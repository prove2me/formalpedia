-- Prove2me | solution 1 for ModularCurve.Period.heckeOperatorHom_preserves_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cbb697ee-d092-5749-905c-394984d404bc

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic

set_option autoImplicit false

open CongruenceSubgroup Matrix MulAction Subgroup
open scoped MatrixGroups

namespace ModularCurve
namespace Period
p2m_export "ModularCurve.Period" "IsParabolicHom"
namespace SolPreservesParabolic
p2m_open "ModularCurve.Period ModularCurve"

open HeckeEis

private theorem fin_two_sq_eq_trace_smul_sub_one
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) :
    A ^ 2 = A.trace • A - 1 := by
  have hadj : A.adjugate = A.trace • 1 - A := by
    ext i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.trace_fin_two, Matrix.one_fin_two]
  have hAA : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  rw [hadj, mul_sub, Matrix.mul_smul, mul_one, ← sq] at hAA
  have hrearr := sub_sub_cancel (A.trace • A) (A ^ 2)
  rw [hAA] at hrearr; exact hrearr.symm

private theorem trace_sq_pow_of_det_one
    (A : Matrix (Fin 2) (Fin 2) ℤ) (hdet : A.det = 1) (htr : A.trace ^ 2 = 4) (n : ℕ) :
    (A ^ n).trace ^ 2 = 4 := by
  have hrec : ∀ k, (A ^ (k + 2)).trace = A.trace * (A ^ (k + 1)).trace - (A ^ k).trace := by
    intro k
    have hstep : A ^ (k + 2) = A.trace • A ^ (k + 1) - A ^ k := by
      rw [show k + 2 = 2 + k from Nat.add_comm k 2, pow_add,
        fin_two_sq_eq_trace_smul_sub_one A hdet, sub_mul, smul_mul_assoc,
        ← pow_succ', one_mul]
    rw [hstep, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have hinv : ∀ k, ((A ^ k).trace = 2 ∧ (A ^ (k + 1)).trace = A.trace) ∨
      ((A ^ k).trace = A.trace ∧ (A ^ (k + 1)).trace = 2) := by
    intro k
    induction k with
    | zero =>
      refine Or.inl ⟨?_, by rw [zero_add, pow_one]⟩
      rw [pow_zero, Matrix.trace_one, Fintype.card_fin]; rfl
    | succ m ih =>
      rcases ih with ⟨he, ho⟩ | ⟨he, ho⟩
      · exact Or.inr ⟨ho, by rw [hrec m, ho, he, ← sq, htr]; ring⟩
      · exact Or.inl ⟨ho, by rw [hrec m, ho, he]; ring⟩
  rcases hinv n with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; norm_num
  · rw [h]; exact htr

private theorem trace_conj_SL2 (g h : SL(2, ℤ)) :
    ((g⁻¹ * h * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

private theorem trace_heckeConjMat (ℓ : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) :
    (heckeConjMat ℓ g).trace = g.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, heckeConjMat_apply_zero_zero,
    heckeConjMat_apply_one_one]

section Telescope

variable {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [AddCommGroup A]

@[scoped simp] private theorem transferAux_one (q : G ⧸ H) : transferAux H 1 q = 1 := by
  ext; rw [coe_transferAux, one_smul, one_mul, inv_mul_cancel]; rfl

private theorem sum_transferAux_pow (φ : Additive ↥H →+ A) (g : G) (q₀ : G ⧸ H) (m : ℕ) :
    ∑ i ∈ Finset.range m, φ (Additive.ofMul (transferAux H g (g ^ i • q₀)))
      = φ (Additive.ofMul (transferAux H (g ^ m) q₀)) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ' g n, transferAux_mul, ofMul_mul, map_add, add_comm]

private theorem coe_transferAux_pow_of_fixed {g : G} {q₀ : G ⧸ H} {m : ℕ}
    (hq : g ^ m • q₀ = q₀) :
    (transferAux H (g ^ m) q₀ : G) = (Quotient.out q₀)⁻¹ * g ^ m * Quotient.out q₀ := by
  rw [coe_transferAux, hq, mul_assoc]

private lemma sum_zmod_cast {B : Type*} [AddCommMonoid B] (m : ℕ) [NeZero m] (F : ℤ → B) :
    ∑ k : ZMod m, F (ZMod.cast k) = ∑ i ∈ Finset.range m, F (i : ℤ) := by
  refine Finset.sum_nbij' (fun k => k.val) (fun i => (i : ZMod m)) ?_ ?_ ?_ ?_ ?_ <;>
    intro x hx
  · exact Finset.mem_range.mpr (ZMod.val_lt x)
  · exact Finset.mem_univ _
  · simp [ZMod.natCast_val, ZMod.cast_id]
  · exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hx)
  · rw [← ZMod.natCast_val]

private theorem sum_transferAux_eq_orbit_sum {G : Type*} [Group G] {H : Subgroup G}
    {A : Type*} [AddCommGroup A] (φ : Additive ↥H →+ A) (g : G) [Fintype (G ⧸ H)]
    [Fintype (orbitRel.Quotient (zpowers g) (G ⧸ H))] :
    ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q))
      = ∑ ω : orbitRel.Quotient (zpowers g) (G ⧸ H),
          φ (Additive.ofMul
              (⟨(Quotient.out ω.out)⁻¹ * g ^ Function.minimalPeriod (g • ·) ω.out
                  * Quotient.out ω.out,
                QuotientGroup.out_conj_pow_minimalPeriod_mem H g ω.out⟩ : ↥H)) := by
  classical
  calc
    ∑ q : G ⧸ H, φ (Additive.ofMul (transferAux H g q))
        = ∑ x : Σ ω : orbitRel.Quotient (zpowers g) (G ⧸ H),
            ZMod (Function.minimalPeriod (g • ·) ω.out),
            φ (Additive.ofMul (transferAux H g ((quotientEquivSigmaZMod H g).symm x))) :=
      ((quotientEquivSigmaZMod H g).symm.sum_comp _).symm
    _ = ∑ ω : orbitRel.Quotient (zpowers g) (G ⧸ H),
          ∑ k : ZMod (Function.minimalPeriod (g • ·) ω.out),
            φ (Additive.ofMul (transferAux H g ((quotientEquivSigmaZMod H g).symm ⟨ω, k⟩))) :=
      Finset.sum_sigma _ _ _
    _ = _ := Fintype.sum_congr _ _ fun ω => ?_
  simp only [quotientEquivSigmaZMod_symm_apply]
  rw [sum_zmod_cast (Function.minimalPeriod (g • ·) ω.out)
      (fun z => φ (Additive.ofMul (transferAux H g (g ^ z • ω.out))))]
  have hrange : ∀ i ∈ Finset.range (Function.minimalPeriod (g • ·) ω.out),
      φ (Additive.ofMul (transferAux H g (g ^ (i : ℤ) • ω.out)))
        = φ (Additive.ofMul (transferAux H g (g ^ i • ω.out))) := by
    intro i _; rw [zpow_natCast]
  rw [Finset.sum_congr rfl hrange, sum_transferAux_pow]
  congr 1
  refine congrArg Additive.ofMul (Subtype.ext ?_)
  rw [coe_transferAux_pow_of_fixed (pow_smul_eq_iff_minimalPeriod_dvd.mpr dvd_rfl)]

end Telescope

p2m_open "ModularCurve.Period P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve.Period"

end ModularCurve.Period.SolPreservesParabolic
p2m_reactivate "P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve.Period P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve.Period.SolPreservesParabolic"
p2m_reactivate "P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve.Period"
p2m_reactivate "P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve"

p2m_open "ModularCurve.Period P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve.Period P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic.ModularCurve.Period.SolPreservesParabolic HeckeEis"

theorem solution (N ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (φ : Additive (Gamma0 N) →+ A) (hφ : IsParabolicHom (Gamma0 N) φ) :
    IsParabolicHom (Gamma0 N) (heckeOperatorHom N ℓ A φ) := by
  classical
  intro γ hγ

  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  letI : Fintype (MulAction.orbitRel.Quotient (zpowers γ) (Gamma0 N ⧸ heckeUpper N ℓ)) :=
    Quotient.fintype _
  show ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
      (pullbackHom (heckeConj N ℓ) φ) (Additive.ofMul (transferAux (heckeUpper N ℓ) γ q)) = 0

  rw [sum_transferAux_eq_orbit_sum (pullbackHom (heckeConj N ℓ) φ) γ]

  refine Finset.sum_eq_zero fun ω _ => ?_
  rw [pullbackHom_apply]

  refine hφ _ ?_
  set m := Function.minimalPeriod (γ • ·) ω.out with hm
  set r := Quotient.out ω.out with hr

  have hmat :
      (((heckeConj N ℓ ⟨r⁻¹ * γ ^ m * r,
          QuotientGroup.out_conj_pow_minimalPeriod_mem (heckeUpper N ℓ) γ ω.out⟩
        : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = heckeConjMat ℓ
            (((r⁻¹ * γ ^ m * r : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [coe_heckeConj, coe_heckeConjSL]
  rw [hmat, trace_heckeConjMat]

  have hconj :
      ((r⁻¹ * γ ^ m * r : Gamma0 N) : SL(2, ℤ))
        = (r : SL(2, ℤ))⁻¹ * (γ : SL(2, ℤ)) ^ m * (r : SL(2, ℤ)) := by
    push_cast; rfl
  rw [hconj, trace_conj_SL2, Matrix.SpecialLinearGroup.coe_pow]
  exact trace_sq_pow_of_det_one _
    (Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))) hγ m

end S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
end P2MW
export P2MW.S_ModularCurve_Period_heckeOperatorHom_preserves_parabolic (solution)

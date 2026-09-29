-- Prove2me | solution 1 for HeckeEis.exists_coeffH1par_projLineRepSL_equiv_parabolicHoms
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/be27c7ab-3f54-54db-90a0-aae5c30504e0

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_ProjectiveLineMatrixAction
import Definitions.Def_IharaIota
import Theorems.Thm_Int_exists_modEq_and_modEq_and_isCoprime
import Theorems.Thm_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero
import Theorems.Thm_HeckeEis_mem_coeffCoboundaries_of_forall_apply_infty_eq_zero
import Theorems.Thm_HeckeEis_exists_mem_coeffParabolicCocycles_forall_apply_infty_eq
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom
import Theorems.Thm_ModularCurve_Period_heckeOperatorHom_preserves_parabolic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_coeffH1par_projLineRepSL_equiv_parabolicHoms

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "heckeConjMat heckeConjMat_apply_zero_zero heckeConjMat_apply_zero_one heckeConjMat_apply_one_zero heckeConjMat_apply_one_one heckeUpper mem_heckeUpper coe_heckeConjSL heckeConj coe_heckeConj pullbackHom pullbackHom_apply heckeOperatorHom heckeOperatorHom_apply coeffCocycles coeffCoboundaryMap coeffCoboundaryMap_apply coeffCoboundaries IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffHeckeFun redMat projLineAct projLineAct_of_isUnit isUnit_det_redMat_coe projLineAct_one projLineAct_mul projLineAct_coe_mul projLineRepSL projLineAlphaAdj projLineAlphaAdj_apply mem_coeffCoboundaries_of_forall_apply_infty_eq_zero exists_mem_coeffParabolicCocycles_forall_apply_infty_eq coeffHeckeFun_mem_coeffCocycles coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom"
p2m_open "HeckeEis"
namespace Sh1t
open CongruenceSubgroup Matrix ModularCurve
open scoped MatrixGroups

def infty (p : ℕ) : ProjectiveLine (ZMod p) :=
  ⟦⟨((0 : ZMod p), (1 : ZMod p)), isUnimodularRow_one_right (0 : ZMod p)⟩⟧

theorem redMat_apply (p : ℕ) (M : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin 2) :
    redMat p M i j = ((M i j : ℤ) : ZMod p) := rfl

theorem redMat_det_coe (p : ℕ) (g : SL(2, ℤ)) : (redMat p (g : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 := by
  rw [redMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, g.det_coe, map_one]

theorem projLineAct_infty_eq_infty_iff (p : ℕ) (g : SL(2, ℤ)) :
    projLineAct p (g : Matrix (Fin 2) (Fin 2) ℤ) (infty p) = infty p ↔ (p : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  have hu := isUnit_det_redMat_coe p g
  rw [projLineAct_of_isUnit p _ hu, infty, ProjectiveLine.vecMul_mk]
  constructor
  · intro h
    obtain ⟨w, h1, -⟩ := Quotient.exact h
    simp only [ProjectiveLine.vecMulRow_fst, zero_mul, one_mul, zero_add] at h1

    have h0 : redMat p (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
      have := congrArg (fun t => (↑w⁻¹ : ZMod p) * t) h1
      simpa using this
    rw [redMat_apply] at h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
  · intro hdvd
    apply Quotient.sound
    have h10 : redMat p (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
      rw [redMat_apply]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    have hdet := redMat_det_coe p g
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    refine ⟨Units.mkOfMulEqOne _ _ hdet, ?_, ?_⟩
    · simp only [ProjectiveLine.vecMulRow_fst, zero_mul, one_mul, zero_add, h10, mul_zero]
    · simp only [ProjectiveLine.vecMulRow_snd, zero_mul, one_mul, zero_add, Units.val_mkOfMulEqOne, hdet]

theorem projLineAct_infty_eq_infty_iff_mem (N p : ℕ) (hNp : Nat.Coprime N p) (g : Gamma0 N) :
    projLineAct p ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (infty p) = infty p ↔
      (g : SL(2, ℤ)) ∈ Gamma0 (N * p) := by
  rw [projLineAct_infty_eq_infty_iff, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hN : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (Gamma0_mem.mp g.2)
  constructor
  · intro hp
    have := (Nat.isCoprime_iff_coprime.mpr hNp).mul_dvd hN hp
    exact_mod_cast this
  · intro h
    push_cast at h
    exact (dvd_mul_left (p : ℤ) N).trans h

def sl2OfCoprime (m n c d : ℤ) (h : m * c + n * d = 1) : SL(2, ℤ) :=
  ⟨!![n, -m; c, d], by rw [Matrix.det_fin_two_of]; linear_combination h⟩

theorem exists_gamma0_projLineAct_infty_eq (N p : ℕ) [NeZero p] (hNp : Nat.Coprime N p)
    (P : ProjectiveLine (ZMod p)) :
    ∃ g : Gamma0 N, projLineAct p ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (infty p) = P := by
  induction P using Quotient.inductionOn with
  | h xy =>
    obtain ⟨⟨x, y⟩, hxy⟩ := xy
    obtain ⟨s, t, hst⟩ := hxy

    set c0 : ℤ := (x.val : ℤ)
    set d0 : ℤ := (y.val : ℤ)
    set s0 : ℤ := (s.val : ℤ)
    set t0 : ℤ := (t.val : ℤ)
    have hc0 : ((c0 : ℤ) : ZMod p) = x := by simp [c0]
    have hd0 : ((d0 : ℤ) : ZMod p) = y := by simp [d0]
    have hs0 : ((s0 : ℤ) : ZMod p) = s := by simp [s0]
    have ht0 : ((t0 : ℤ) : ZMod p) = t := by simp [t0]

    obtain ⟨w, hw⟩ : (p : ℤ) ∣ (s0 * c0 + t0 * d0) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hc0, hd0, hs0, ht0, hst, sub_self]

    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hNp : IsCoprime (N : ℤ) (p : ℤ))
    set c : ℤ := c0 * u * N with hc
    set d : ℤ := d0 * u * N + v * p with hd
    have h3 : ∃ X Y Z : ℤ, X * c + Y * d + Z * ((N : ℤ) * p) = 1 := by
      refine ⟨s0 * u * N, t0 * u * N + v * p, -(u ^ 2 * N * w + u * v * (t0 + d0) - 2 * u * v), ?_⟩
      rw [hc, hd]
      linear_combination ((N : ℤ) ^ 2 * u ^ 2) * hw + ((N : ℤ) * u + p * v + 1) * huv
    obtain ⟨c', d', hc', hd', hcd⟩ := Int.exists_modEq_and_modEq_and_isCoprime h3
    obtain ⟨m, n, hmn⟩ := hcd

    have hmemN : sl2OfCoprime m n c' d' hmn ∈ Gamma0 N := by
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      show (N : ℤ) ∣ c'
      have h1 : c' ≡ c [ZMOD (N : ℤ)] := hc'.of_mul_right _
      have h2 : (N : ℤ) ∣ c := ⟨c0 * u, by rw [hc]; ring⟩
      have hh : (N : ℤ) ∣ c' - c := Int.ModEq.dvd h1.symm
      have := dvd_add h2 hh
      rwa [add_sub_cancel] at this
    refine ⟨⟨_, hmemN⟩, ?_⟩

    have hu' := isUnit_det_redMat_coe p (sl2OfCoprime m n c' d' hmn)
    rw [show (((⟨_, hmemN⟩ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = (sl2OfCoprime m n c' d' hmn : Matrix (Fin 2) (Fin 2) ℤ) from rfl,
      projLineAct_of_isUnit p _ hu', infty, ProjectiveLine.vecMul_mk]
    apply Quotient.sound

    have hcp : ((c' : ℤ) : ZMod p) = x := by
      have h1 : c' ≡ c [ZMOD (p : ℤ)] := hc'.of_mul_left _
      rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h1, hc]
      push_cast
      rw [hc0]
      have : ((u : ℤ) : ZMod p) * (N : ZMod p) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod p)) huv
        push_cast at this
        rw [ZMod.natCast_self, mul_zero, add_zero] at this
        exact this
      rw [mul_assoc, this, mul_one]
    have hdp : ((d' : ℤ) : ZMod p) = y := by
      have h1 : d' ≡ d [ZMOD (p : ℤ)] := hd'.of_mul_left _
      rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h1, hd]
      push_cast
      rw [hd0, ZMod.natCast_self, mul_zero, add_zero]
      have : ((u : ℤ) : ZMod p) * (N : ZMod p) = 1 := by
        have := congrArg (fun z : ℤ => (z : ZMod p)) huv
        push_cast at this
        rw [ZMod.natCast_self, mul_zero, add_zero] at this
        exact this
      rw [mul_assoc, this, mul_one]
    refine ⟨1, ?_, ?_⟩
    · simp only [ProjectiveLine.vecMulRow_fst, zero_mul, one_mul, zero_add, Units.val_one, redMat_apply]
      show (((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p) = x
      rw [show ((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = c' from rfl, hcp]
    · simp only [ProjectiveLine.vecMulRow_snd, zero_mul, one_mul, zero_add, Units.val_one, redMat_apply]
      show (((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p) = y
      rw [show ((sl2OfCoprime m n c' d' hmn : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d' from rfl, hdp]

end Sh1t
end HeckeEis

namespace HeckeEis
p2m_export "HeckeEis" "heckeConjMat heckeConjMat_apply_zero_zero heckeConjMat_apply_zero_one heckeConjMat_apply_one_zero heckeConjMat_apply_one_one heckeUpper mem_heckeUpper coe_heckeConjSL heckeConj coe_heckeConj pullbackHom pullbackHom_apply heckeOperatorHom heckeOperatorHom_apply coeffCocycles coeffCoboundaryMap coeffCoboundaryMap_apply coeffCoboundaries IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffHeckeFun redMat projLineAct projLineAct_of_isUnit isUnit_det_redMat_coe projLineAct_one projLineAct_mul projLineAct_coe_mul projLineRepSL projLineAlphaAdj projLineAlphaAdj_apply mem_coeffCoboundaries_of_forall_apply_infty_eq_zero exists_mem_coeffParabolicCocycles_forall_apply_infty_eq coeffHeckeFun_mem_coeffCocycles coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom"
p2m_open "HeckeEis"
namespace Sh1
open CongruenceSubgroup Matrix ModularCurve Sh1t Function
open scoped MatrixGroups

variable (N p : ℕ) [NeZero p] (hpN : Nat.Coprime p N) (K : Type*) [CommRing K]

noncomputable abbrev rho : Representation K (Gamma0 N) (ProjectiveLine (ZMod p) → K) :=
  (projLineRepSL p K).comp (Gamma0 N).subtype

noncomputable abbrev act (g : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : (ProjectiveLine (ZMod p)) := projLineAct p ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P

theorem act_mul (g h : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : act N p (g * h) P = act N p h (act N p g P) := by
  show projLineAct p (((g : SL(2, ℤ)) * (h : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P = _
  exact projLineAct_coe_mul p _ _ P

theorem act_one (P : (ProjectiveLine (ZMod p))) : act N p 1 P = P := by
  show projLineAct p ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P = P
  rw [Matrix.SpecialLinearGroup.coe_one, projLineAct_one]

theorem act_inv_act (g : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : act N p g⁻¹ (act N p g P) = P := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_act_inv (g : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : act N p g (act N p g⁻¹ P) = P := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem rho_apply (g : Gamma0 N) (f : (ProjectiveLine (ZMod p)) → K) (P : (ProjectiveLine (ZMod p))) : (rho N p K g) f P = f (act N p g P) := rfl

include hpN in
theorem act_infty_eq_iff (g : Gamma0 N) : act N p g (infty p) = infty p ↔ (g : SL(2, ℤ)) ∈ Gamma0 (N * p) :=
  projLineAct_infty_eq_infty_iff_mem N p hpN.symm g

include hpN in
theorem act_iota0_infty (γ : Gamma0 (N * p)) : act N p (Ihara.ι₀ N p γ) (infty p) = infty p :=
  (act_infty_eq_iff N p hpN _).mpr (by rw [Ihara.coe_iota0]; exact γ.2)

theorem minimalPeriod_act_pos (g : Gamma0 N) (P : (ProjectiveLine (ZMod p))) : 0 < minimalPeriod (act N p g) P := by
  have hinj : Function.Injective (act N p g) := fun P Q h => by
    have := congrArg (act N p g⁻¹) h
    rwa [act_inv_act, act_inv_act] at this

  haveI : Finite (ProjectiveLine (ZMod p)) := inferInstance
  obtain ⟨i, j, hij, hP⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => (act N p g)^[k] P)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have : (act N p g)^[j - i] P = P := by
      have e : (act N p g)^[i] ((act N p g)^[j - i] P) = (act N p g)^[i] P := by
        rw [← iterate_add_apply, Nat.add_sub_cancel' h.le]; exact hP.symm
      exact (hinj.iterate i) e
    exact (IsPeriodicPt.minimalPeriod_pos (Nat.sub_pos_of_lt h) this)
  · have : (act N p g)^[i - j] P = P := by
      have e : (act N p g)^[j] ((act N p g)^[i - j] P) = (act N p g)^[j] P := by
        rw [← iterate_add_apply, Nat.add_sub_cancel' h.le]; exact hP
      exact (hinj.iterate j) e
    exact (IsPeriodicPt.minimalPeriod_pos (Nat.sub_pos_of_lt h) this)

theorem iterate_act (g : Gamma0 N) (k : ℕ) (P : (ProjectiveLine (ZMod p))) : (act N p g)^[k] P = act N p (g ^ k) P := by
  induction k generalizing P with
  | zero => rw [iterate_zero_apply, pow_zero, act_one]
  | succ k ih => rw [iterate_succ_apply, ih, pow_succ', act_mul]

variable (σ : (ProjectiveLine (ZMod p)) → Gamma0 N) (hσ : ∀ P : (ProjectiveLine (ZMod p)), act N p (σ P) (infty p) = P)

include hpN hσ in
theorem kappa_mem (P : (ProjectiveLine (ZMod p))) (g : Gamma0 N) : ((σ P * g * (σ (act N p g P))⁻¹ : Gamma0 N) : SL(2, ℤ)) ∈ Gamma0 (N * p) := by
  rw [← act_infty_eq_iff N p hpN]
  rw [act_mul, act_mul, hσ]
  calc act N p (σ (act N p g P))⁻¹ (act N p g P)
      = act N p (σ (act N p g P))⁻¹ (act N p (σ (act N p g P)) (infty p)) := by rw [hσ]
    _ = infty p := act_inv_act N p _ _

noncomputable def kappa (P : (ProjectiveLine (ZMod p))) (g : Gamma0 N) : Gamma0 (N * p) :=
  ⟨((σ P * g * (σ (act N p g P))⁻¹ : Gamma0 N) : SL(2, ℤ)), kappa_mem N p hpN σ hσ P g⟩

theorem iota0_kappa (P : (ProjectiveLine (ZMod p))) (g : Gamma0 N) : Ihara.ι₀ N p (kappa N p hpN σ hσ P g) = σ P * g * (σ (act N p g P))⁻¹ :=
  rfl

theorem kappa_mul (P : (ProjectiveLine (ZMod p))) (g h : Gamma0 N) :
    kappa N p hpN σ hσ P (g * h) = kappa N p hpN σ hσ P g * kappa N p hpN σ hσ (act N p g P) h := by
  apply Ihara.iota0_injective
  rw [map_mul, iota0_kappa, iota0_kappa, iota0_kappa, act_mul]
  group

include hpN hσ in
theorem mem_coeffCoboundaries_of_forall_eq_zero {z : Gamma0 N → (ProjectiveLine (ZMod p)) → K} (hz : z ∈ coeffCocycles (rho N p K))
    (hz0 : ∀ γ : Gamma0 (N * p), z (Ihara.ι₀ N p γ) (infty p) = 0) : z ∈ coeffCoboundaries (rho N p K) := by
  refine ⟨fun P => z (σ P) (infty p), ?_⟩
  funext g P
  simp only [coeffCoboundaryMap_apply, Pi.sub_apply, LinearMap.sub_apply, rho_apply]

  have h1 : z (σ P * g) (infty p) = z (σ P) (infty p) + z g P := by
    rw [hz (σ P) g, Pi.add_apply, rho_apply, hσ]
  have h2 : z (σ P * g) (infty p) = z (σ (act N p g P)) (infty p) := by
    have e : σ P * g = Ihara.ι₀ N p (kappa N p hpN σ hσ P g) * σ (act N p g P) := by
      rw [iota0_kappa, inv_mul_cancel_right]
    rw [e, hz, Pi.add_apply, rho_apply, hz0, zero_add, act_iota0_infty N p hpN]

  show z (σ (act N p g P)) (infty p) - z (σ P) (infty p) = z g P
  rw [← h2, h1, add_sub_cancel_left]

noncomputable def zOf (φ : Additive (Gamma0 (N * p)) →+ K) : Gamma0 N → (ProjectiveLine (ZMod p)) → K :=
  fun g P => φ (Additive.ofMul (kappa N p hpN σ hσ P g))

theorem zOf_apply (φ : Additive (Gamma0 (N * p)) →+ K) (g : Gamma0 N) (P : (ProjectiveLine (ZMod p))) :
    zOf N p hpN K σ hσ φ g P = φ (Additive.ofMul (kappa N p hpN σ hσ P g)) := rfl

theorem zOf_mem_coeffCocycles (φ : Additive (Gamma0 (N * p)) →+ K) : zOf N p hpN K σ hσ φ ∈ coeffCocycles (rho N p K) := by
  intro g h
  funext P
  rw [Pi.add_apply, rho_apply, zOf_apply, zOf_apply, zOf_apply, kappa_mul, ofMul_mul, map_add]

include hσ in

theorem zOf_iota0_infty (φ : Additive (Gamma0 (N * p)) →+ K) (γ : Gamma0 (N * p)) :
    zOf N p hpN K σ hσ φ (Ihara.ι₀ N p γ) (infty p) = φ (Additive.ofMul γ) := by
  rw [zOf_apply]

  have hk0 : ((σ (infty p) : Gamma0 N) : SL(2, ℤ)) ∈ Gamma0 (N * p) := by
    rw [← act_infty_eq_iff N p hpN]; exact hσ _
  set k0 : Gamma0 (N * p) := ⟨_, hk0⟩
  have e : kappa N p hpN σ hσ (infty p) (Ihara.ι₀ N p γ) = k0 * γ * k0⁻¹ := by
    apply Ihara.iota0_injective
    rw [iota0_kappa, act_iota0_infty N p hpN, map_mul, map_mul, map_inv]
    rfl
  rw [e, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  ring

theorem fin_two_sq_eq_trace_smul_sub_one
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

theorem trace_sq_pow
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

theorem trace_conj (g h : SL(2, ℤ)) :
    ((g * h * g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_comm, ← mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul]

include hσ in

theorem zOf_isParabolic (φ : Additive (Gamma0 (N * p)) →+ K)
    (hφ : ModularCurve.Period.IsParabolicHom (Gamma0 (N * p)) φ) :
    IsParabolicCocycle (rho N p K) (zOf N p hpN K σ hσ φ) := by
  intro γ hγ

  set f : (ProjectiveLine (ZMod p)) → (ProjectiveLine (ZMod p)) := act N p γ with hf
  have hfpos : ∀ P : (ProjectiveLine (ZMod p)), 0 < minimalPeriod f P := minimalPeriod_act_pos N p γ
  have hsum : ∀ (P : (ProjectiveLine (ZMod p))) (n : ℕ), ∑ k ∈ Finset.range n, zOf N p hpN K σ hσ φ γ (f^[k] P)
      = zOf N p hpN K σ hσ φ (γ ^ n) P := by
    intro P n
    induction n with
    | zero =>
      rw [Finset.sum_range_zero, pow_zero, zOf_apply]
      have : kappa N p hpN σ hσ P 1 = 1 := by
        apply Ihara.iota0_injective; rw [iota0_kappa, map_one, act_one]; group
      rw [this, ofMul_one, map_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ, hf, iterate_act]
      have := zOf_mem_coeffCocycles N p hpN K σ hσ φ (γ ^ n) γ
      rw [this, Pi.add_apply, rho_apply]
  have hv : ∀ P : (ProjectiveLine (ZMod p)), ∑ k ∈ Finset.range (minimalPeriod f P), zOf N p hpN K σ hσ φ γ (f^[k] P) = 0 := by
    intro P
    rw [hsum, zOf_apply]
    apply hφ

    have hfix : act N p (γ ^ minimalPeriod f P) P = P := by
      rw [← iterate_act]; exact iterate_minimalPeriod
    have e : ((kappa N p hpN σ hσ P (γ ^ minimalPeriod f P) : Gamma0 (N * p)) : SL(2, ℤ))
        = (σ P : SL(2, ℤ)) * ((γ : SL(2, ℤ)) ^ minimalPeriod f P) * (σ P : SL(2, ℤ))⁻¹ := by
      show ((Ihara.ι₀ N p (kappa N p hpN σ hσ P (γ ^ minimalPeriod f P)) : Gamma0 N) : SL(2, ℤ)) = _
      rw [iota0_kappa, hfix]
      push_cast
      rfl
    rw [e, trace_conj, Matrix.SpecialLinearGroup.coe_pow]
    exact trace_sq_pow _ (γ : SL(2, ℤ)).2 hγ _
  obtain ⟨G, hG⟩ := exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero f hfpos _ hv
  refine ⟨G, ?_⟩
  funext P
  rw [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, rho_apply, hG, hf]

end Sh1
end HeckeEis

namespace HeckeEis
p2m_export "HeckeEis" "heckeConjMat heckeConjMat_apply_zero_zero heckeConjMat_apply_zero_one heckeConjMat_apply_one_zero heckeConjMat_apply_one_one heckeUpper mem_heckeUpper coe_heckeConjSL heckeConj coe_heckeConj pullbackHom pullbackHom_apply heckeOperatorHom heckeOperatorHom_apply coeffCocycles coeffCoboundaryMap coeffCoboundaryMap_apply coeffCoboundaries IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffHeckeFun redMat projLineAct projLineAct_of_isUnit isUnit_det_redMat_coe projLineAct_one projLineAct_mul projLineAct_coe_mul projLineRepSL projLineAlphaAdj projLineAlphaAdj_apply mem_coeffCoboundaries_of_forall_apply_infty_eq_zero exists_mem_coeffParabolicCocycles_forall_apply_infty_eq coeffHeckeFun_mem_coeffCocycles coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom"
p2m_open "HeckeEis"
namespace Sh3
open CongruenceSubgroup Matrix ModularCurve Sh1t Sh1
open scoped MatrixGroups

variable (N p : ℕ) [NeZero p] (hpN : Nat.Coprime p N) (K : Type*) [CommRing K] (ℓ : ℕ) [NeZero ℓ]

theorem projLineAct_alphaAdj_infty : projLineAct p !![(ℓ : ℤ), 0; 0, 1] (infty p) = infty p := by
  classical
  unfold projLineAct
  split_ifs with h
  · rw [infty, ProjectiveLine.vecMul_mk]
    apply Quotient.sound
    refine ⟨1, ?_, ?_⟩
    · simp [ProjectiveLine.vecMulRow_fst, redMat]
    · simp [ProjectiveLine.vecMulRow_snd, redMat]
  · rfl

theorem alphaAdj_mul_heckeConjMat (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : (ℓ : ℤ) ∣ g 0 1) :
    !![(ℓ : ℤ), 0; 0, 1] * heckeConjMat ℓ g = g * !![(ℓ : ℤ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, heckeConjMat_apply_zero_zero, heckeConjMat_apply_zero_one,
      heckeConjMat_apply_one_zero, heckeConjMat_apply_one_one, Int.mul_ediv_cancel' hg, mul_comm]

include hpN in

theorem compat (hℓp : Nat.Coprime ℓ p) (u : ↥(heckeUpper N ℓ)) :
    projLineAlphaAdj p K ℓ ∘ₗ (rho N p K) (heckeConj N ℓ u) = (rho N p K) (u : Gamma0 N) ∘ₗ projLineAlphaAdj p K ℓ := by
  apply LinearMap.ext
  intro f
  funext P
  simp only [LinearMap.comp_apply, projLineAlphaAdj_apply, rho_apply]
  show f (projLineAct p ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ)) (projLineAct p !![(ℓ : ℤ), 0; 0, 1] P))
    = f (projLineAct p !![(ℓ : ℤ), 0; 0, 1] (projLineAct p (((u : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P))
  congr 1
  have hα : IsUnit (redMat p !![(ℓ : ℤ), 0; 0, 1]).det := by
    have : (redMat p !![(ℓ : ℤ), 0; 0, 1]).det = (ℓ : ZMod p) := by
      simp [redMat, Matrix.det_fin_two]
    rw [this]
    exact (ZMod.isUnit_iff_coprime ℓ p).mpr hℓp
  have hc := isUnit_det_redMat_coe p ((heckeConj N ℓ u : Gamma0 N) : SL(2, ℤ))
  have hu := isUnit_det_redMat_coe p ((u : Gamma0 N) : SL(2, ℤ))
  rw [← projLineAct_mul p _ _ hα hc, ← projLineAct_mul p _ _ hu hα]
  congr 1
  rw [coe_heckeConj, coe_heckeConjSL]
  exact alphaAdj_mul_heckeConjMat ℓ _ ((mem_heckeUpper N ℓ).mp u.2)

end Sh3
end HeckeEis

namespace HeckeEis
p2m_export "HeckeEis" "heckeConjMat heckeConjMat_apply_zero_zero heckeConjMat_apply_zero_one heckeConjMat_apply_one_zero heckeConjMat_apply_one_one heckeUpper mem_heckeUpper coe_heckeConjSL heckeConj coe_heckeConj pullbackHom pullbackHom_apply heckeOperatorHom heckeOperatorHom_apply coeffCocycles coeffCoboundaryMap coeffCoboundaryMap_apply coeffCoboundaries IsParabolicCocycle coeffParabolicCocycles coeffCoboundaries_le_coeffParabolicCocycles coeffH1par coeffH1parMk coeffH1parMk_surjective coeffH1parMk_eq_zero_iff coeffHeckeFun redMat projLineAct projLineAct_of_isUnit isUnit_det_redMat_coe projLineAct_one projLineAct_mul projLineAct_coe_mul projLineRepSL projLineAlphaAdj projLineAlphaAdj_apply mem_coeffCoboundaries_of_forall_apply_infty_eq_zero exists_mem_coeffParabolicCocycles_forall_apply_infty_eq coeffHeckeFun_mem_coeffCocycles coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom"
p2m_open "HeckeEis"
namespace C2c
open CongruenceSubgroup Matrix ModularCurve Sh1t Sh1
open scoped MatrixGroups

variable (N : ℕ) [NeZero N] (p : ℕ) [NeZero p] (hpN : Nat.Coprime p N) (K : Type*) [CommRing K]

local notation "Γ" => Gamma0 N
local notation "Γp" => Gamma0 (N * p)

noncomputable def evalHom (z : ↥(coeffParabolicCocycles (rho N p K))) : Additive (Gamma0 (N * p)) →+ K :=
  AddMonoidHom.mk' (fun γ => (z : Gamma0 N → ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p γ.toMul) (infty p))
    (by
      intro γ δ
      have hz := z.2.1 (Ihara.ι₀ N p γ.toMul) (Ihara.ι₀ N p δ.toMul)
      show (z : Gamma0 N → ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p (γ.toMul * δ.toMul)) (infty p) = _
      rw [map_mul, hz, Pi.add_apply, rho_apply, act_iota0_infty N p hpN])

theorem evalHom_apply (z : ↥(coeffParabolicCocycles (rho N p K))) (γ : Gamma0 (N * p)) :
    evalHom N p hpN K z (Additive.ofMul γ) = (z : Gamma0 N → ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p γ) (infty p) := rfl

include hpN in
theorem evalHom_mem (z : ↥(coeffParabolicCocycles (rho N p K))) :
    evalHom N p hpN K z ∈ ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K := by
  rw [ModularCurve.Period.mem_parabolicHoms_iff]
  intro γ hγ
  rw [evalHom_apply]
  have hγ' : ((((Ihara.ι₀ N p γ : Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
    rw [Ihara.coe_iota0]; exact hγ
  obtain ⟨f, hf⟩ := z.2.2 (Ihara.ι₀ N p γ) hγ'
  rw [← hf, LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, rho_apply, act_iota0_infty N p hpN, sub_self]

noncomputable def Phi : ↥(coeffParabolicCocycles (rho N p K)) →ₗ[K] ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K) where
  toFun z := ⟨evalHom N p hpN K z, evalHom_mem N p hpN K z⟩
  map_add' z w := by
    apply Subtype.ext; apply AddMonoidHom.ext; intro x
    rfl
  map_smul' c z := by
    apply Subtype.ext; apply AddMonoidHom.ext; intro x
    rfl

theorem Phi_apply (z : ↥(coeffParabolicCocycles (rho N p K))) (γ : Gamma0 (N * p)) :
    ((Phi N p hpN K z : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K)) : Additive (Gamma0 (N * p)) →+ K)
      (Additive.ofMul γ) = (z : Gamma0 N → ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p γ) (infty p) := rfl

include hpN in
theorem comap_le_ker : (coeffCoboundaries (rho N p K)).comap (coeffParabolicCocycles (rho N p K)).subtype
    ≤ LinearMap.ker (Phi N p hpN K) := by
  intro z hz
  rw [LinearMap.mem_ker]
  apply Subtype.ext; apply AddMonoidHom.ext; intro x
  obtain ⟨v, hv⟩ := (Submodule.mem_comap.mp hz)
  show (z : Gamma0 N → ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p x.toMul) (infty p) = 0
  rw [show (z : Gamma0 N → ProjectiveLine (ZMod p) → K) = coeffCoboundaryMap (rho N p K) v from hv.symm,
    coeffCoboundaryMap_apply, Pi.sub_apply, rho_apply, act_iota0_infty N p hpN, sub_self]

noncomputable def S0 : coeffH1par (rho N p K) →ₗ[K] ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K) :=
  Submodule.liftQ _ (Phi N p hpN K) (comap_le_ker N p hpN K)

theorem S0_mk (z : ↥(coeffParabolicCocycles (rho N p K))) :
    S0 N p hpN K (coeffH1parMk (rho N p K) z) = Phi N p hpN K z := rfl

include hpN in
theorem S0_injective : Function.Injective (S0 N p hpN K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨z, rfl⟩ := coeffH1parMk_surjective (rho N p K) x
  rw [S0_mk] at hx
  rw [coeffH1parMk_eq_zero_iff]
  apply HeckeEis.mem_coeffCoboundaries_of_forall_apply_infty_eq_zero N p hpN K z.2.1
  intro γ
  have := congrArg (fun ψ : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K) =>
    (ψ : Additive (Gamma0 (N * p)) →+ K) (Additive.ofMul γ)) hx
  simp [Phi_apply] at this
  exact this

include hpN in
theorem S0_surjective : Function.Surjective (S0 N p hpN K) := by
  intro φ
  obtain ⟨z, hzpar, hzφ⟩ := HeckeEis.exists_mem_coeffParabolicCocycles_forall_apply_infty_eq N p hpN K φ φ.2
  refine ⟨coeffH1parMk (rho N p K) ⟨z, hzpar⟩, ?_⟩
  rw [S0_mk]
  apply Subtype.ext; apply AddMonoidHom.ext; intro x
  exact hzφ x.toMul

noncomputable def S : coeffH1par (rho N p K) ≃ₗ[K] ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K) :=
  LinearEquiv.ofBijective (S0 N p hpN K) ⟨S0_injective N p hpN K, S0_surjective N p hpN K⟩

theorem S_mk (z : ↥(coeffParabolicCocycles (rho N p K))) (γ : Gamma0 (N * p)) :
    ((S N p hpN K (coeffH1parMk (rho N p K) z) : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K)) :
      Additive (Gamma0 (N * p)) →+ K) (Additive.ofMul γ)
      = (z : Gamma0 N → ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p γ) (infty p) := by
  rw [S, LinearEquiv.ofBijective_apply, S0_mk, Phi_apply]

variable (ℓ : ℕ) [NeZero ℓ]

noncomputable def TNp : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K) →ₗ[K]
    ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K) where
  toFun φ := ⟨heckeOperatorHom (N * p) ℓ K φ,
    ModularCurve.Period.mem_parabolicHoms_iff.mpr
      (ModularCurve.Period.heckeOperatorHom_preserves_parabolic (N * p) ℓ K φ
        (ModularCurve.Period.mem_parabolicHoms_iff.mp φ.2))⟩
  map_add' φ ψ := by
    apply Subtype.ext
    show heckeOperatorHom (N * p) ℓ K (φ + ψ) = heckeOperatorHom (N * p) ℓ K φ + heckeOperatorHom (N * p) ℓ K ψ
    exact map_add _ _ _
  map_smul' c φ := by
    apply Subtype.ext; apply AddMonoidHom.ext; intro x
    show heckeOperatorHom (N * p) ℓ K (c • (φ : Additive (Gamma0 (N * p)) →+ K)) x
      = c • heckeOperatorHom (N * p) ℓ K (φ : Additive (Gamma0 (N * p)) →+ K) x
    rw [show x = Additive.ofMul x.toMul from rfl, heckeOperatorHom_apply, heckeOperatorHom_apply]
    simp only [AddMonoidHom.smul_apply, Finset.smul_sum]

theorem coe_TNp (φ : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K)) :
    ((TNp N p K ℓ φ : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K)) : Additive (Gamma0 (N * p)) →+ K)
      = heckeOperatorHom (N * p) ℓ K φ := rfl

noncomputable def Tprime : coeffH1par (rho N p K) →ₗ[K] coeffH1par (rho N p K) :=
  (S N p hpN K).symm.toLinearMap ∘ₗ TNp N p K ℓ ∘ₗ (S N p hpN K).toLinearMap

theorem S_Tprime (x : coeffH1par (rho N p K)) :
    S N p hpN K (Tprime N p hpN K ℓ x) = TNp N p K ℓ (S N p hpN K x) := by
  rw [Tprime, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]

include hpN in
theorem Tprime_induced (hℓ : Nat.Coprime ℓ (N * p)) (z : ↥(coeffParabolicCocycles (rho N p K))) :
    ∃ w : ↥(coeffParabolicCocycles (rho N p K)),
      (w : Gamma0 N → ProjectiveLine (ZMod p) → K)
        = coeffHeckeFun N ℓ (rho N p K) (projLineAlphaAdj p K ℓ) z ∧
      Tprime N p hpN K ℓ (coeffH1parMk _ z) = coeffH1parMk _ w := by
  have hℓp : Nat.Coprime ℓ p := Nat.Coprime.coprime_dvd_right (dvd_mul_left p N) hℓ
  have ha := Sh3.compat N p hpN K ℓ hℓp
  set wf := coeffHeckeFun N ℓ (rho N p K) (projLineAlphaAdj p K ℓ) z with hwf
  have hwc : wf ∈ coeffCocycles (rho N p K) :=
    HeckeEis.coeffHeckeFun_mem_coeffCocycles N ℓ (rho N p K) (projLineAlphaAdj p K ℓ) ha z.2.1

  set ψ := TNp N p K ℓ (S N p hpN K (coeffH1parMk _ z)) with hψ
  obtain ⟨z₁, hz₁par, hz₁⟩ := HeckeEis.exists_mem_coeffParabolicCocycles_forall_apply_infty_eq N p hpN K ψ ψ.2

  have hwfi : ∀ γ : Gamma0 (N * p), wf (Ihara.ι₀ N p γ) (infty p) = (ψ : Additive (Gamma0 (N * p)) →+ K) (Additive.ofMul γ) := by
    intro γ
    rw [hψ, coe_TNp, hwf]
    exact HeckeEis.coeffHeckeFun_projLineAlphaAdj_apply_iota0_infty_eq_heckeOperatorHom N p hpN K ℓ hℓ z.2.1
      _ (fun δ => S_mk N p hpN K z δ) γ

  have hdiff : wf - z₁ ∈ coeffCoboundaries (rho N p K) := by
    apply HeckeEis.mem_coeffCoboundaries_of_forall_apply_infty_eq_zero N p hpN K (Submodule.sub_mem _ hwc hz₁par.1)
    intro γ
    show wf (Ihara.ι₀ N p γ) (infty p) - z₁ (Ihara.ι₀ N p γ) (infty p) = 0
    rw [hwfi, show z₁ (Ihara.ι₀ N p γ) (infty p) = _ from hz₁ γ, sub_self]
  have hwpar : wf ∈ coeffParabolicCocycles (rho N p K) := by
    have : wf = (wf - z₁) + z₁ := by abel
    rw [this]
    exact Submodule.add_mem _ (coeffCoboundaries_le_coeffParabolicCocycles _ hdiff) hz₁par
  refine ⟨⟨wf, hwpar⟩, rfl, ?_⟩
  apply (S N p hpN K).injective
  rw [S_Tprime]
  apply Subtype.ext; apply AddMonoidHom.ext; intro x
  rw [show x = Additive.ofMul x.toMul from rfl, S_mk]
  exact (hwfi x.toMul).symm

include hpN in
theorem constants (φ : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 N) K)) :
    ∃ z : ↥(coeffParabolicCocycles (rho N p K)),
      (z : Gamma0 N → ProjectiveLine (ZMod p) → K) = (fun g _ => (φ : Additive (Gamma0 N) →+ K) (Additive.ofMul g)) ∧
      ((S N p hpN K (coeffH1parMk _ z) : ↥(ModularCurve.Period.parabolicHoms K (Gamma0 (N * p)) K)) :
          Additive (Gamma0 (N * p)) →+ K)
        = pullbackHom (Ihara.ι₀ N p) (φ : Additive (Gamma0 N) →+ K) := by
  have hmem : (fun (g : Gamma0 N) (_ : ProjectiveLine (ZMod p)) => (φ : Additive (Gamma0 N) →+ K) (Additive.ofMul g))
      ∈ coeffParabolicCocycles (rho N p K) := by
    refine ⟨?_, ?_⟩
    · intro g h
      funext P
      simp only [Pi.add_apply, rho_apply, ofMul_mul, map_add]
    · intro γ hγ
      have h0 : (φ : Additive (Gamma0 N) →+ K) (Additive.ofMul γ) = 0 := (ModularCurve.Period.mem_parabolicHoms_iff.mp φ.2) γ hγ
      have : (fun _ : ProjectiveLine (ZMod p) => (φ : Additive (Gamma0 N) →+ K) (Additive.ofMul γ)) = 0 := by
        funext P; rw [h0]; rfl
      show (fun _ : ProjectiveLine (ZMod p) => (φ : Additive (Gamma0 N) →+ K) (Additive.ofMul γ)) ∈ _
      rw [this]
      exact Submodule.zero_mem _
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩
  apply AddMonoidHom.ext; intro x
  rw [show x = Additive.ofMul x.toMul from rfl, S_mk, pullbackHom_apply]

include hpN in
theorem main :
    ∃ S : HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) ≃ₗ[K]
        ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K),
      (∀ (z : ↥(HeckeEis.coeffParabolicCocycles
              ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)))
          (γ : CongruenceSubgroup.Gamma0 (N * p)),
        ((S (HeckeEis.coeffH1parMk _ z) :
            ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
            Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K) (Additive.ofMul γ)
          = (z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p γ)
              (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧)) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ], Nat.Coprime ℓ (N * p) →
        ∃ T' : HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[K]
            HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles
                ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles
                ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              (w : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K)
                  = HeckeEis.coeffHeckeFun N ℓ
                      ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)
                      (HeckeEis.projLineAlphaAdj p K ℓ) z ∧
              T' (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
          ∀ x, ((S (T' x) : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
                  Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
              = HeckeEis.heckeOperatorHom (N * p) ℓ K
                  ((S x : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
                    Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)) ∧
      (∀ φ : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K),
        ∃ z : ↥(HeckeEis.coeffParabolicCocycles
              ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K)
              = (fun g _ => (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ K) (Additive.ofMul g)) ∧
          ((S (HeckeEis.coeffH1parMk _ z) :
              ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
              Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
            = HeckeEis.pullbackHom (Ihara.ι₀ N p) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ K)) := by
  refine ⟨S N p hpN K, fun z γ => S_mk N p hpN K z γ, ?_, fun φ => constants N p hpN K φ⟩
  intro ℓ _ hℓ
  exact ⟨Tprime N p hpN K ℓ, fun z => Tprime_induced N p hpN K ℓ hℓ z, fun x => by rw [S_Tprime]; rfl⟩

end C2c
end HeckeEis

end

theorem solution
    (N : ℕ) [NeZero N] (p : ℕ) [NeZero p] (hpN : Nat.Coprime p N)
    (K : Type*) [Field K] :
    ∃ S : HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) ≃ₗ[K]
        ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K),

      (∀ (z : ↥(HeckeEis.coeffParabolicCocycles
              ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)))
          (γ : CongruenceSubgroup.Gamma0 (N * p)),
        ((S (HeckeEis.coeffH1parMk _ z) :
            ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
            Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K) (Additive.ofMul γ)
          = (z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K) (Ihara.ι₀ N p γ)
              (⟦⟨((0 : ZMod p), (1 : ZMod p)), ModularCurve.isUnimodularRow_one_right (0 : ZMod p)⟩⟧)) ∧

      (∀ (ℓ : ℕ) [NeZero ℓ], Nat.Coprime ℓ (N * p) →
        ∃ T' : HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype) →ₗ[K]
            HeckeEis.coeffH1par ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype),
          (∀ z : ↥(HeckeEis.coeffParabolicCocycles
                ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
            ∃ w : ↥(HeckeEis.coeffParabolicCocycles
                ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
              (w : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K)
                  = HeckeEis.coeffHeckeFun N ℓ
                      ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)
                      (HeckeEis.projLineAlphaAdj p K ℓ) z ∧
              T' (HeckeEis.coeffH1parMk _ z) = HeckeEis.coeffH1parMk _ w) ∧
          ∀ x, ((S (T' x) : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
                  Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
              = HeckeEis.heckeOperatorHom (N * p) ℓ K
                  ((S x : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
                    Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)) ∧

      (∀ φ : ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K),
        ∃ z : ↥(HeckeEis.coeffParabolicCocycles
              ((HeckeEis.projLineRepSL p K).comp (CongruenceSubgroup.Gamma0 N).subtype)),
          (z : CongruenceSubgroup.Gamma0 N → ModularCurve.ProjectiveLine (ZMod p) → K)
              = (fun g _ => (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ K) (Additive.ofMul g)) ∧
          ((S (HeckeEis.coeffH1parMk _ z) :
              ↥(ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 (N * p)) K)) :
              Additive (CongruenceSubgroup.Gamma0 (N * p)) →+ K)
            = HeckeEis.pullbackHom (Ihara.ι₀ N p) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ K)) :=
  HeckeEis.C2c.main N p hpN K

end S_HeckeEis_exists_coeffH1par_projLineRepSL_equiv_parabolicHoms
end P2MW
export P2MW.S_HeckeEis_exists_coeffH1par_projLineRepSL_equiv_parabolicHoms (solution)

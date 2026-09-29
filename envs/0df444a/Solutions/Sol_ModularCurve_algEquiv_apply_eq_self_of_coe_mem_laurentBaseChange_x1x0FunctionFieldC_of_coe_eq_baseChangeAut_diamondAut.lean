-- Prove2me | solution 1 for ModularCurve.algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_x1x0FunctionFieldC_of_coe_eq_baseChangeAut_diamondAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/33d6c11c-53f1-52f1-a4e0-9ee038f99908

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_x1x0FunctionFieldC_of_coe_eq_baseChangeAut_diamondAut

set_option autoImplicit false

open scoped MatrixGroups

namespace DiamFloor

open ModularCurve CongruenceSubgroup

theorem gamma1_mul_le (M p : ℕ) : Gamma1 (M * p) ≤ Gamma1 M ⊓ Gamma0 p := by
  intro A hA
  refine Subgroup.mem_inf.mpr ⟨Gamma1_le_of_dvd (dvd_mul_right M p) hA, ?_⟩
  rw [Gamma1_mem] at hA
  rw [Gamma0_mem]
  have h := hA.2.2
  have := congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) h
  rwa [map_intCast, map_zero] at this

theorem x1x0FunctionFieldC_le_x1FunctionField (M p : ℕ) :
    x1x0FunctionFieldC ℚ M p ≤ x1FunctionField (M * p) :=
  qExpFunctionFieldC_mono ℚ (gamma1_mul_le M p)

theorem diamondAut_congr (N : ℕ) {d d' : ℕ} (h : (d : ZMod N) = (d' : ZMod N)) :
    diamondAut N d = diamondAut N d' := by
  have hP : IsDiamondAut N d = IsDiamondAut N d' := by
    funext σ
    have hc : Nat.Coprime d N ↔ Nat.Coprime d' N := by
      have hmod : d ≡ d' [MOD N] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      rw [Nat.Coprime, Nat.Coprime, Nat.ModEq.gcd_eq hmod]
    simp only [IsDiamondAut, h, hc]
  have key : ∀ (P Q : (x1FunctionField N ≃ₐ[ℚ] x1FunctionField N) → Prop), P = Q →
      (haveI := Classical.dec (∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, P σ)
       if h : ∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, P σ then h.choose else AlgEquiv.refl) =
      (haveI := Classical.dec (∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, Q σ)
       if h : ∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, Q σ then h.choose else AlgEquiv.refl) := by
    rintro P Q rfl; rfl
  exact key _ _ hP

theorem apply_eq_self_of_coe_mem_laurentBaseChange_x1x0
    (p M : ℕ) [Fact p.Prime] [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (d : ℕ) (hd : d.Coprime (M * p)) (hdM : (d : ZMod M) = 1)
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) :
    ∀ u : ↥K, (u : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p) → θ u = u := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set F₀ := x1FunctionField (M * p) with hF₀
  set F₁ := x1x0FunctionFieldC ℚ M p with hF₁
  have hF₁₀ : F₁ ≤ F₀ := x1x0FunctionFieldC_le_x1FunctionField M p

  have hMp : Nat.Coprime M p := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpM))
  obtain ⟨δ, hδ, hfix⟩ := exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff M p hMp
    (fun d' hd' => exists_isDiamondAut (M * p) hd')

  have hdu : IsUnit (d : ZMod (M * p)) := (ZMod.isUnit_iff_coprime d (M * p)).mpr hd
  set u : (ZMod (M * p))ˣ := hdu.unit with hu
  have huker : u ∈ (ZMod.unitsMap (dvd_mul_right M p)).ker := by
    rw [MonoidHom.mem_ker]
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, Units.val_one]
    show ZMod.castHom (dvd_mul_right M p) (ZMod M) (u : ZMod (M * p)) = 1
    rw [hu, IsUnit.unit_spec, map_natCast, hdM]
  have hδu : δ ⟨u, huker⟩ = diamondAut (M * p) d := by
    rw [hδ]
    apply diamondAut_congr
    show (((u : ZMod (M * p)).val : ℕ) : ZMod (M * p)) = (d : ZMod (M * p))
    rw [ZMod.natCast_zmod_val]
    exact hdu.unit_spec
  have hfix1 : ∀ y : ↥F₀, (y : LaurentSeries ℚ) ∈ F₁ → diamondAut (M * p) d y = y := by
    intro y hy
    rw [← hδu]
    exact (hfix y).mp hy ⟨u, huker⟩

  let P : IntermediateField L (LaurentSeries L) :=
    (IntermediateField.fixedField (Subgroup.zpowers θ)).map K.val
  have hPmem : ∀ x : ↥K, (x : LaurentSeries L) ∈ P ↔ θ x = x := by
    intro x
    constructor
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      subst this
      have hx'' : x' ∈ IntermediateField.fixedField (Subgroup.zpowers θ) := hx'
      rw [IntermediateField.mem_fixedField_iff] at hx''
      exact hx'' θ (Subgroup.mem_zpowers θ)
    · intro hx
      refine ⟨x, ?_, rfl⟩
      show x ∈ IntermediateField.fixedField (Subgroup.zpowers θ)
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have key : ∀ n : ℕ, (θ ^ n) x = x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · exact_mod_cast key m
      · rw [zpow_neg, zpow_natCast]
        have h1 := key m
        conv_lhs => rw [← h1]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

  have hgen : laurentBaseChange L F₁ ≤ P := by
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : z ∈ F₀ := hF₁₀ hz
    have hxK : coeffEmb L z ∈ K := by rw [hK]; exact coeffEmb_mem_laurentBaseChange L hz0
    show coeffEmb L z ∈ P
    rw [show coeffEmb L z = ((⟨coeffEmb L z, hxK⟩ : ↥K) : LaurentSeries L) from rfl, hPmem]
    apply Subtype.ext
    rw [hθ ⟨coeffEmb L z, hxK⟩ ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L hz0⟩ rfl]
    rcases Classical.em (∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀,
        IsBaseChangeAutOf L (diamondAut (M * p) d) σ) with hex | hex
    · have hbc := isBaseChangeAutOf_baseChangeAut hex ⟨z, hz0⟩
      rw [hbc, hfix1 ⟨z, hz0⟩ hz]
    · rw [baseChangeAut_of_not hex]
      rfl

  intro v hv
  exact (hPmem v).mp (hgen hv)

end DiamFloor

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (d : ℕ) (hd : d.Coprime (M * p)) (hdM : (d : ZMod M) = 1)
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L)) :
    ∀ u : ↥K, (u : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p) → θ u = u :=
  DiamFloor.apply_eq_self_of_coe_mem_laurentBaseChange_x1x0 p M hpM L K hK d hd hdM θ hθ

end S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_x1x0FunctionFieldC_of_coe_eq_baseChangeAut_diamondAut
end P2MW
export P2MW.S_ModularCurve_algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_x1x0FunctionFieldC_of_coe_eq_baseChangeAut_diamondAut (solution)

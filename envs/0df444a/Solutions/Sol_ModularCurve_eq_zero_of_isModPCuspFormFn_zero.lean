-- Prove2me | solution 1 for ModularCurve.eq_zero_of_isModPCuspFormFn_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/df7b01bb-9f08-5ca1-a843-201adac3bdcc

import Mathlib
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_forall_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_eq_zero_of_isModPCuspFormFn_zero
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve ModularCurve

namespace WeightZeroCusp

section Transport

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem isIntegral_adjoin_of_coe (S : IntermediateField K L) (y z : ↥S)
    (h : IsIntegral (Algebra.adjoin K ({(y : L)} : Set L)) (z : L)) :
    IsIntegral (Algebra.adjoin K ({y} : Set ↥S)) z := by
  set A := Algebra.adjoin K ({y} : Set ↥S) with hA
  set B := Algebra.adjoin K ({(y : L)} : Set L) with hB
  have hmap : A.map S.val = B := by
    rw [hA, AlgHom.map_adjoin, Set.image_singleton]; rfl
  have hmem : ∀ a : ↥A, ((a : ↥S) : L) ∈ B := fun a => by
    rw [← hmap]; exact ⟨a, a.2, rfl⟩
  let φ : ↥A →+* ↥B :=
    { toFun := fun a => ⟨((a : ↥S) : L), hmem a⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    rw [← hmap] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨⟨a, ha⟩, rfl⟩
  let ψ : ↥A →+* L := (algebraMap ↥S L).comp (algebraMap ↥A ↥S)
  have hcomp : (algebraMap ↥B L).comp φ = ψ := RingHom.ext fun _ => rfl
  obtain ⟨P, hPm, hPz⟩ := h
  have hl : P ∈ Polynomial.lifts φ := by
    rw [Polynomial.mem_lifts]; exact Polynomial.map_surjective φ hφ P
  obtain ⟨Q, hQP, -, hQm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hPm
  have hQz : Polynomial.eval₂ ψ (z : L) Q = 0 := by
    rw [← hcomp, ← Polynomial.eval₂_map, hQP]; exact hPz
  refine ⟨Q, hQm, ?_⟩
  apply (algebraMap ↥S L).injective
  rw [Polynomial.hom_eval₂, map_zero]
  exact hQz

end Transport

section J

variable (K : Type) [Field K] (N : ℕ) [NeZero N]

def jF : ↥(modularFunctionFieldC K N) := ⟨jqModC K, jqModC_mem K N⟩

theorem coe_jF : ((jF K N : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = jqModC K := rfl

theorem jF_ne_algebraMap (c : K) : jF K N ≠ algebraMap K ↥(modularFunctionFieldC K N) c := by
  intro h
  have h1 := congrArg (fun x : ↥(modularFunctionFieldC K N) => (x : LaurentSeries K).coeff (-1)) h
  rw [coe_jF, coeff_jqModC_neg_one] at h1
  have h2 : ((algebraMap K ↥(modularFunctionFieldC K N) c : ↥(modularFunctionFieldC K N)) : LaurentSeries K)
      = algebraMap K (LaurentSeries K) c := rfl
  rw [h2, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by decide)] at h1
  exact one_ne_zero h1

theorem jF_ne_zero : jF K N ≠ 0 := by
  have h := jF_ne_algebraMap K N 0
  rwa [map_zero] at h

end J

theorem main (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (G : ↥(modularFunctionFieldC K N))
    (hG : IsModPCuspFormFn K 0 (G : LaurentSeries K)) : G = 0 := by
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  by_contra hG0
  obtain ⟨h1, M, h2⟩ := hG
  simp only [mul_zero, zero_mul, zero_add, pow_zero, pow_one, mul_one] at h1 h2
  have hj0 := jF_ne_zero K N

  have h1F : IsIntegral (Algebra.adjoin K ({jF K N} : Set ↥(modularFunctionFieldC K N))) (G ^ 6) := by
    apply isIntegral_adjoin_of_coe
    rw [IntermediateField.coe_pow, coe_jF]
    exact h1
  have h2F : IsIntegral (Algebra.adjoin K ({(jF K N)⁻¹} : Set ↥(modularFunctionFieldC K N)))
      (G ^ (2 * M) * jF K N) := by
    apply isIntegral_adjoin_of_coe
    rw [IntermediateField.coe_inv, IntermediateField.coe_mul, IntermediateField.coe_pow, coe_jF]
    exact h2

  have hord : ∀ v : Place K ↥(modularFunctionFieldC K N),
      0 ≤ v.ord G ∧ (v.ord (jF K N) < 0 → 0 < v.ord G) := by
    intro v
    by_cases hvj : 0 ≤ v.ord (jF K N)
    · have h6 := v.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg h1F hvj
      rw [← zpow_natCast, v.ord_zpow] at h6
      push_cast at h6
      exact ⟨by omega, fun h => absurd hvj (not_le.mpr h)⟩
    · push Not at hvj
      have hinv : 0 ≤ v.ord (jF K N)⁻¹ := by rw [v.ord_inv]; omega
      have h := v.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg h2F hinv
      rw [v.ord_mul (pow_ne_zero _ hG0) hj0, ← zpow_natCast, v.ord_zpow] at h
      push_cast at h
      have hpos : 0 < v.ord G := by
        by_contra hle
        push Not at hle
        have : (2 * (M : ℤ)) * v.ord G ≤ 0 := mul_nonpos_iff.mpr (Or.inl ⟨by positivity, hle⟩)
        omega
      exact ⟨hpos.le, fun _ => hpos⟩

  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_ord_nonneg K N hpN G (fun v => (hord v).1)

  obtain ⟨v, hv⟩ : ∃ v : Place K ↥(modularFunctionFieldC K N), v.ord (jF K N) < 0 := by
    by_contra hno
    push Not at hno
    obtain ⟨d, hd⟩ := exists_eq_algebraMap_of_forall_ord_nonneg K N hpN (jF K N) hno
    exact jF_ne_algebraMap K N d hd
  have h := (hord v).2 hv
  rw [hc, v.ord_algebraMap] at h
  exact lt_irrefl _ h

end WeightZeroCusp

end

open AlgebraicCurve ModularCurve in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (G : ↥(modularFunctionFieldC K N)) (hG : ModularCurve.IsModPCuspFormFn K 0 (G : LaurentSeries K)) :
    G = 0 :=
  WeightZeroCusp.main p K N hN G hG

end S_ModularCurve_eq_zero_of_isModPCuspFormFn_zero
end P2MW
export P2MW.S_ModularCurve_eq_zero_of_isModPCuspFormFn_zero (solution)

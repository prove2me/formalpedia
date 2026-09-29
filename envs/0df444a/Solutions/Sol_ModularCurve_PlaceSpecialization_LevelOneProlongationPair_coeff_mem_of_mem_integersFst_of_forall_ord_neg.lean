-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coeff_mem_of_mem_integersFst_of_forall_ord_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/22aba6d9-7fcb-5ad2-962f-e780f3f63ba9

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits_of_forall_ord_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeff_mem_of_mem_integersFst_of_forall_ord_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

open AlgebraicCurve ModularCurve IsLocalRing

noncomputable section

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (hf : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f < 0 →
      W.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : ↥(modularFunctionFieldBar (1 * q))) < 0)
    (h₁ : f ∈ R.R₁.integers) (n : ℤ) :
    (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A := by
  classical
  by_cases hf0 : f = 0
  · subst hf0
    simp

  obtain ⟨c, hc0, hint, k₀, hk₀⟩ :=
    ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits_of_forall_ord_neg (1 * q) f hf0 hf A

  let y : LaurentSeries A :=
    { coeff := fun j => ⟨((c • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)).coeff j, hint j⟩
      isPWO_support' := ((c • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
        (fun _ hn h => hn (Subtype.ext h)) }
  have hy : coeffMap A.subtype y = ((c • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    ext j
    rfl
  have hyF : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q) := by
    rw [hy]; exact SetLike.coe_mem _
  obtain ⟨hint₁, hres₁⟩ := R.residue₁_coeffMap y hyF
  have helt : (⟨coeffMap A.subtype y, hyF⟩ : ↥(modularFunctionFieldBar (1 * q))) = c • f := Subtype.ext hy
  have hcf₁ : c • f ∈ R.R₁.integers := helt ▸ hint₁
  have hres_ne : R.R₁.residue ⟨c • f, hcf₁⟩ ≠ 0 := by
    have hred_ne : coeffMap (IsLocalRing.residue A) y ≠ 0 := by
      intro h0
      have hk : IsLocalRing.residue A (y.coeff k₀) = 0 :=
        congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff k₀) h0
      rw [IsLocalRing.residue_eq_zero_iff] at hk
      exact hk₀ (ValuationSubring.coe_mem_nonunits_iff.mpr hk)
    intro h0
    apply hred_ne
    rw [← hres₁]
    have hsub : (⟨⟨coeffMap A.subtype y, hyF⟩, hint₁⟩ : R.R₁.integers) = ⟨c • f, hcf₁⟩ := Subtype.ext helt
    rw [hsub, h0]
    rfl
  have hunit : IsUnit (⟨c • f, hcf₁⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hres_ne

  have hcinv : c⁻¹ ∈ A := by
    have hv1 : R.R₁.integers.valuation (c • f) = 1 :=
      (ValuationSubring.valuation_eq_one_iff _ ⟨c • f, hcf₁⟩).mp hunit
    have hvf : R.R₁.integers.valuation f ≤ 1 := (R.R₁.integers.valuation_le_one_iff f).mpr h₁
    rw [Algebra.smul_def, map_mul] at hv1
    have hinv : (R.R₁.integers.valuation (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c))⁻¹
        = R.R₁.integers.valuation f := inv_eq_of_mul_eq_one_right hv1
    have hle : R.R₁.integers.valuation (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹) ≤ 1 := by
      rw [map_inv₀, map_inv₀, hinv]
      exact hvf
    exact (R.R₁.algebraMap_mem_iff c⁻¹).mp ((ValuationSubring.valuation_le_one_iff _ _).mp hle)

  have hcoeff : ((c • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)).coeff n
      = c * (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n := by
    rw [IntermediateField.coe_smul, Algebra.smul_def, ModularCurve.algebraMap_laurentSeries_eq_single,
      HahnSeries.coeff_single_zero_mul]
  have hrew : (f : LaurentSeries (AlgebraicClosure ℚ)).coeff n
      = c⁻¹ * ((c • f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)).coeff n := by
    rw [hcoeff, ← mul_assoc, inv_mul_cancel₀ hc0]
    exact (one_mul _).symm
  rw [hrew]
  exact mul_mem hcinv (hint n)

end

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeff_mem_of_mem_integersFst_of_forall_ord_neg
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeff_mem_of_mem_integersFst_of_forall_ord_neg (solution)

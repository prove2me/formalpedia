-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.iota_bijective_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f9ee7429-8da7-5fd9-8712-13a8ced9219f

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective_of_level
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective_of_level
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace IotaBij

theorem coeffMap_algebraMap_of_ringHom {K K' : Type*} [Field K] [Field K'] (σ : K →+* K') (c : K) :
    coeffMap σ (algebraMap K (LaurentSeries K) c) = algebraMap K' (LaurentSeries K') (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_modularFunctionFieldC_of_ringHom {K K' : Type*} [Field K] [Field K'] (σ : K →+* K')
    (N : ℕ) [NeZero N] {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldC K N) :
    coeffMap σ x ∈ modularFunctionFieldC K' N := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪
      {jqModC K, jqNModC K N}) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [coeffMap_algebraMap_of_ringHom]
        exact (modularFunctionFieldC K' N).algebraMap_mem _
      · rcases hy with rfl | hy
        · rw [coeffSemilinearAut.coeffMap_jqModC]
          exact jqModC_mem K' N
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [coeffSemilinearAut.coeffMap_jqNModC]
          exact jqNModC_mem K' N
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end IotaBij

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P) (hqN : ¬ q ∣ N) :
    Function.Bijective R.ι := by
  have hbij : Function.Bijective R.redBar := by
    refine ⟨R.redBar.injective, fun c => ?_⟩
    obtain ⟨a, rfl⟩ := P.red_surjective_of_level c
    exact ⟨IsLocalRing.residue A a, R.redBar_residue a⟩
  haveI : CharP (IsLocalRing.ResidueField A) q := (RingHom.charP_iff_charP R.redBar q).mpr inferInstance
  set e : IsLocalRing.ResidueField A ≃+* k := RingEquiv.ofBijective R.redBar hbij with he
  have he_apply : ∀ c, e c = R.redBar c := fun c => rfl
  refine ⟨R.ι.injective, fun g => ?_⟩
  have hmem : coeffMap (e.symm : k →+* IsLocalRing.ResidueField A) (g : LaurentSeries k) ∈
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) N := by
    rw [← ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (IsLocalRing.ResidueField A) q N hqN]
    exact IotaBij.coeffMap_mem_modularFunctionFieldC_of_ringHom _ N g.2
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [R.ι_coe]
  change coeffMap R.redBar (coeffMap (e.symm : k →+* IsLocalRing.ResidueField A) (g : LaurentSeries k))
      = (g : LaurentSeries k)
  rw [coeffMap_coeffMap,
    coeffMap_congr (g := RingHom.id _) (RingHom.ext fun a => by
      change R.redBar (e.symm a) = a
      rw [← he_apply]; exact e.apply_symm_apply a) _, coeffMap_id]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective_of_level
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective_of_level (solution)

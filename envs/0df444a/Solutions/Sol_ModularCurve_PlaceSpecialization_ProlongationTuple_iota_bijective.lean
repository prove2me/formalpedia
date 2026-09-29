-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.iota_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b6d657ad-0971-5cff-a85f-adcd50628642

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
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
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P) :
    Function.Bijective R.ι := by
  have hbij : Function.Bijective R.redBar := by
    refine ⟨R.redBar.injective, fun c => ?_⟩
    obtain ⟨a, rfl⟩ := P.red_surjective c
    exact ⟨IsLocalRing.residue A a, R.redBar_residue a⟩
  set e : IsLocalRing.ResidueField A ≃+* k := RingEquiv.ofBijective R.redBar hbij with he
  have he_apply : ∀ c, e c = R.redBar c := fun c => rfl
  refine ⟨R.ι.injective, fun g => ?_⟩
  have hmem : coeffMap (e.symm : k →+* IsLocalRing.ResidueField A) (g : LaurentSeries k) ∈
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) 1 := by
    rw [modularFunctionFieldFullC_one]
    exact IotaBij.coeffMap_mem_modularFunctionFieldC_of_ringHom _ 1 g.2
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [R.ι_coe]
  change coeffMap R.redBar (coeffMap (e.symm : k →+* IsLocalRing.ResidueField A) (g : LaurentSeries k))
      = (g : LaurentSeries k)
  rw [coeffMap_coeffMap,
    coeffMap_congr (g := RingHom.id _) (RingHom.ext fun a => by
      change R.redBar (e.symm a) = a
      rw [← he_apply]; exact e.apply_symm_apply a) _, coeffMap_id]

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_iota_bijective (solution)

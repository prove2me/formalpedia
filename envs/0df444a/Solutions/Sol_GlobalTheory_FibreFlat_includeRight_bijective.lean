-- Prove2me | solution 1 for GlobalTheory.FibreFlat.includeRight_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:16.359492+00:00
-- url     : https://prove2.me/submissions/5088bc53-9128-43cf-85a1-bbb880759430

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFlatFibresDvr
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TensorProduct IsLocalRing
open GlobalTheory
open GlobalTheory.FibreFlat
variable {T : Type*} (K : Type*) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
  [Algebra T K] [IsFractionRing T K]
namespace GlobalTheory.FibreFlat
theorem _root_.solution {C : Type*} [CommRing C] [Algebra T C] {π : T} (hπ : Irreducible π)
    (hu : IsUnit (algebraMap T C π)) :
    Function.Bijective (Algebra.TensorProduct.includeRight : C →ₐ[T] K ⊗[T] C) := by
  have h : Algebra.algebraMapSubmonoid C (nonZeroDivisors T) ≤ IsUnit.submonoid C := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero ht) hπ
    change IsUnit _
    rw [map_mul, map_pow]
    exact (u.isUnit.map _).mul (hu.pow n)
  have h2 : Function.Bijective (algebraMap C (C ⊗[T] K)) :=
    (IsLocalization.atUnits C (S := C ⊗[T] K) _ h).bijective
  exact (Algebra.TensorProduct.comm T C K).bijective.comp h2
end GlobalTheory.FibreFlat

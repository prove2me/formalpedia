-- Prove2me | solution 1 for GlobalTheory.BaseRing.aeval_derivative_mul_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:29.239838+00:00
-- url     : https://prove2.me/submissions/b31fea8e-49c9-44d2-9677-981dc80f4c0f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmModelCoefficientSubringDedekindCompatibleEmbed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BaseRing
open Polynomial
namespace GlobalTheory.BaseRing
theorem _root_.solution (A K : Type*) {L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsDomain A] [IsFractionRing A K]
    [IsIntegrallyClosed A] [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L}
    (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) (f : A[X]) (hf : aeval x f = 0)
    {z : L} (hz : IsIntegral A z) : aeval x (derivative f) * z ∈ Algebra.adjoin A {x} := by
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hinj
  have h1 : z ∈ (Algebra.traceForm K L).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin A {x})) := by
    intro y hy
    have hy' : IsIntegral A y :=
      (show Algebra.adjoin A {x} ≤ integralClosure A L from
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr hAx)) hy
    have := Algebra.isIntegral_trace (L := K) (hz.mul hy')
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp this
    rw [Algebra.traceForm_apply, ← ha]
    exact Submodule.mem_one.mpr ⟨a, rfl⟩
  rw [traceForm_dualSubmodule_adjoin A K hx hAx] at h1
  have hne : aeval x (derivative (minpoly K x)) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)
  rw [Submodule.mem_smul_iff_inv_mul_mem (inv_ne_zero hne), inv_inv,
    minpoly.isIntegrallyClosed_eq_field_fractions' K hAx, derivative_map,
    aeval_map_algebraMap] at h1
  obtain ⟨g, hg⟩ := minpoly.isIntegrallyClosed_dvd hAx hf
  have : aeval x (derivative f) * z = aeval x g * (aeval x (derivative (minpoly A x)) * z) := by
    rw [hg, derivative_mul]
    simp only [map_add, map_mul, minpoly.aeval]
    ring
  rw [this]
  exact Subalgebra.mul_mem _ (aeval_mem_adjoin_singleton _ _) h1
end GlobalTheory.BaseRing

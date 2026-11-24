-- Prove2me | solution 1 for GlobalTheory.exists_eigen_element
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:12.189544+00:00
-- url     : https://prove2.me/submissions/1c3c1fb5-71ee-402d-847d-fa0ebaef7f77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnComplexExtend
import Theorems.Thm_GlobalTheory_complexExtend_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] [Module.Finite ℤ O]
    [IsReduced (ℂ ⊗[ℤ] O)] (τ : O →+* ℂ) :
    ∃ e : ℂ ⊗[ℤ] O, complexExtend τ e = 1 ∧ ∀ a : O, ((1 : ℂ) ⊗ₜ[ℤ] a) * e = τ a • e := by
  haveI : IsArtinianRing (ℂ ⊗[ℤ] O) := IsArtinianRing.of_finite ℂ _
  haveI : IsSemisimpleRing (ℂ ⊗[ℤ] O) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨f, hf, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (RingHom.ker (complexExtend τ))
  have hf0 : complexExtend τ f = 0 := by
    have : f ∈ RingHom.ker (complexExtend τ) := hI ▸ Ideal.mem_span_singleton_self f
    exact this
  refine ⟨1 - f, by simp [hf0], fun a => ?_⟩
  have hk : ((1 : ℂ) ⊗ₜ[ℤ] a) - algebraMap ℂ (ℂ ⊗[ℤ] O) (τ a) ∈
      RingHom.ker (complexExtend τ) := by
    rw [RingHom.mem_ker, map_sub, complexExtend_tmul, AlgHom.commutes]
    simp
  rw [hI, Ideal.mem_span_singleton'] at hk
  obtain ⟨y, hy⟩ := hk
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, ← hy, _root_.mul_assoc, mul_sub, _root_.mul_one, hf.eq,
    sub_self, mul_zero]
end GlobalTheory

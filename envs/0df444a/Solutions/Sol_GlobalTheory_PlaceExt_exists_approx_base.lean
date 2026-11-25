-- Prove2me | solution 1 for GlobalTheory.PlaceExt.exists_approx_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:35:59.000685+00:00
-- url     : https://prove2.me/submissions/489969df-b540-4243-a3c2-a0ef8c4d5802

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
import Theorems.Thm_GlobalTheory_PlaceExt_maximalIdeal_eq_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PlaceExt
variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
namespace GlobalTheory.PlaceExt
theorem _root_.solution
    (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')))
    {ϖ : R} (hϖ : Irreducible ϖ) (m : ℕ) (r : R') :
    ∃ (r₀ : R) (r₁ : R'), r = algebraMap R R' r₀ + algebraMap R R' ϖ ^ m * r₁ := by
  induction m with
  | zero => exact ⟨0, r, by simp⟩
  | succ m ih =>
    obtain ⟨r₀, r₁, h⟩ := ih
    obtain ⟨s, hs⟩ := hres (IsLocalRing.residue R' r₁)
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective s
    rw [IsLocalRing.ResidueField.map_residue] at hs
    have hm : r₁ - algebraMap R R' s ∈ IsLocalRing.maximalIdeal R' := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hs, sub_self]
    rw [maximalIdeal_eq_span hmax hϖ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨r₀ + ϖ ^ m * s, c, ?_⟩
    rw [h, map_add, map_mul, map_pow]
    linear_combination (-(algebraMap R R' ϖ) ^ m) * hc
end GlobalTheory.PlaceExt

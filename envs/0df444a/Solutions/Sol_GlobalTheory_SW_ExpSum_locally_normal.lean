-- Prove2me | solution 1 for GlobalTheory.SW.ExpSum.locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:42:52.407354+00:00
-- url     : https://prove2.me/submissions/6a5aead7-9525-4c6f-a224-f4f398d0f02d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsHeatThH
import Theorems.Thm_GlobalTheory_SW_ExpSum_convexOn_norm_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ExpSum
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}
namespace GlobalTheory.SW.ExpSum
theorem _root_.solution (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    ∀ x ∈ U, ∃ W ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ p ∈ W, ‖c i * cexp (L i p)‖ ≤ u i := by
  intro x hx
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  obtain ⟨b, hb, hbU⟩ := exists_mem_interior_convexHull_affineBasis (hU.mem_nhds hx)
  refine ⟨_, mem_interior_iff_mem_nhds.1 hb, fun i => ∑ j, ‖c i * cexp (L i (b j))‖,
    summable_sum fun j _ => hs _ (hbU (subset_convexHull ℝ _ ⟨j, rfl⟩)), fun i p hp => ?_⟩
  obtain ⟨y, ⟨j, rfl⟩, hy⟩ := (convexOn_norm_term (c i) (L i)).exists_ge_of_mem_convexHull
    (Set.subset_univ _) hp
  exact hy.trans (Finset.single_le_sum (f := fun j => ‖c i * cexp (L i (b j))‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j))
end GlobalTheory.SW.ExpSum

-- Prove2me | solution 1 for GlobalTheory.LatBasisAdapted.span_range_smul_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:53.998712+00:00
-- url     : https://prove2.me/submissions/1c08a74b-d9a0-4c8e-9a53-cab84ac5ed60

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedTwoSubspaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.LatBasisAdapted
namespace GlobalTheory.LatBasisAdapted
theorem _root_.solution {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : ι → K) (hc : ∀ i, c i ≠ 0) (w : ι → V) (f : κ → ι) :
    Submodule.span K (Set.range ((fun i => c i • w i) ∘ f)) =
      Submodule.span K (Set.range (w ∘ f)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have h : (w ∘ f) k = (c (f k))⁻¹ • ((fun i => c i • w i) ∘ f) k := by
      simp [smul_smul, inv_mul_cancel₀ (hc (f k))]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
end GlobalTheory.LatBasisAdapted

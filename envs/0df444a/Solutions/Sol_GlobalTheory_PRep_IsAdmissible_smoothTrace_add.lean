-- Prove2me | solution 1 for GlobalTheory.PRep.IsAdmissible.smoothTrace_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:18:22.165844+00:00
-- url     : https://prove2.me/submissions/1cbf9431-de7d-4d12-bb0d-f0c2b95fc32e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Theorems.Thm_GlobalTheory_OpTrace_finRankTrace_add
import Theorems.Thm_GlobalTheory_PRep_IsSmooth_smoothOp_add
import Theorems.Thm_GlobalTheory_PRep_IsAdmissible_finiteDimensional_range_smoothOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace G]
variable [IsTopologicalGroup G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
  {ρ : Representation ℂ G V} {f f' : G → ℂ}
namespace GlobalTheory.OpTrace
namespace _root_.GlobalTheory.PRep.IsAdmissible
theorem _root_.solution [μ.IsMulLeftInvariant] (hρ : IsAdmissible ρ)
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) (hf' : IsLocallyConstant f')
    (hc' : HasCompactSupport f') {K : Subgroup G} (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) :
    smoothTrace ρ μ (f + f') = smoothTrace ρ μ f + smoothTrace ρ μ f' := by
  have := hρ.finiteDimensional_range_smoothOp (μ := μ) hf hc ho hK
  have := hρ.finiteDimensional_range_smoothOp (μ := μ) hf' hc' ho hK
  rw [smoothTrace, hρ.1.smoothOp_add hf hc hf' hc', finRankTrace_add]
  rfl
end _root_.GlobalTheory.PRep.IsAdmissible
end GlobalTheory.OpTrace

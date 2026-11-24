-- Prove2me | solution 1 for GlobalTheory.OpTrace.isUnitaryRep_charRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:42.666369+00:00
-- url     : https://prove2.me/submissions/6d6a7e52-62de-4412-bda7-3955016b9279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional

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
variable {G : Type*} [Group G] [TopologicalSpace G]
  {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace GlobalTheory.OpTrace
theorem _root_.solution {χ : G →* Circle} (hχ : Continuous χ) : IsUnitaryRep (charRep χ) :=
  ⟨fun g v => by simp [charRep, Circle.norm_coe], fun v =>
    ((continuous_subtype_val.comp hχ).mul continuous_const : Continuous fun g => (χ g : ℂ) * v)⟩
end GlobalTheory.OpTrace

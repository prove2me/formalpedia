-- Prove2me | solution 1 for GlobalTheory.SpanIndex.span_le_inf_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:53:34.601251+00:00
-- url     : https://prove2.me/submissions/a3a3b075-2163-4260-a729-aea27a637396

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSupMulRelIndexInfSame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SpanImageInfSpanImageOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicative

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
open GlobalTheory GlobalTheory.SpanIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.SpanIndex
theorem _root_.solution {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {ι : Type}
    (w : ι → Fin r → E) (hw : ∀ a, w a ∈ Λ) :
    (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
  refine le_inf ?_ ?_
  · have : Submodule.span (𝓞 E) (Set.range w) ≤ Λ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hw a)
    exact fun x hx => this hx
  · exact fun x hx => Submodule.span_le_restrictScalars (𝓞 E) E _ hx
end GlobalTheory.SpanIndex

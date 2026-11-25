-- Prove2me | solution 1 for GlobalTheory.SpanIndex.relIndex_mul_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:23.592804+00:00
-- url     : https://prove2.me/submissions/24c7605f-7b74-4ce6-830b-042d48263b93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSupMulRelIndexInfSame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SpanImageInfSpanImageOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicative
import Theorems.Thm_GlobalTheory_relIndex_sup_mul_relIndex_inf


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
namespace GlobalTheory.SpanIndex
theorem _root_.solution {A : Type} [AddCommGroup A] (M₁ M₂ W₁ W₂ Λ : AddSubgroup A)
    (h₁ : M₁ ≤ Λ ⊓ W₁) (h₂ : M₂ ≤ Λ ⊓ W₂)
    (hne : (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) ≠ 0) :
    M₁.relIndex (Λ ⊓ W₁) * M₂.relIndex (Λ ⊓ W₂) ≤
      (M₁ ⊓ M₂).relIndex (Λ ⊓ (W₁ ⊓ W₂)) * (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) := by
  rw [← GlobalTheory.relIndex_sup_mul_relIndex_inf A M₁ _ M₂ _ h₁ h₂, mul_comm, ← inf_inf_distrib_left]
  refine Nat.mul_le_mul_left _ (AddSubgroup.relIndex_le_of_le_right ?_ hne)
  exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)
end GlobalTheory.SpanIndex

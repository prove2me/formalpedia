-- Prove2me | solution 1 for IntractableCoding.Weights.npHard_of_threeDM_reduction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:57:46.03573+00:00
-- url     : https://prove2.me/submissions/beea7cf4-1945-4645-b1c5-b25e2a50caf0

import Mathlib
import Definitions.Def_IntractableCoding_Weights_NPComplete
import Definitions.Def_PricingWithTips3DM_4901b5edb9039a7b71dab674
import Theorems.Thm_PricingWithTips_threeDM_np_hard

open PricingWithTips IntractableCoding.Weights

theorem solution {α : Type} (enc : α → List Bool) (P : α → Prop)
    (g : ThreeDMInstance → α)
    (hg : Nonempty (Turing.TM2ComputableInPolyTime encodeThreeDMInstance enc g))
    (hred : ∀ I : ThreeDMInstance, ThreeDMYes I ↔ P (g I)) :
    NPHardFor enc P := by
  intro Γ L hL
  obtain ⟨f, ⟨hf⟩, hiff⟩ := threeDM_np_hard Γ L hL
  obtain ⟨hg'⟩ := hg
  refine ⟨g ∘ f, Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch hf hg', fun x => ?_⟩
  exact (hiff x).trans (hred (f x))

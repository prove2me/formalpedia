-- Prove2me | solution 1 for GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:06.457225+00:00
-- url     : https://prove2.me/submissions/24ddf667-53f3-4f73-87ed-fb361eeb758f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDifferentiableOnTorsSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionHolomorphic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.TorsionHolomorphic
namespace _root_.GlobalTheory.TorsionHolomorphic
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∏ i ∈ s, f i e) W := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih
end _root_.GlobalTheory.TorsionHolomorphic
end GlobalTheory.TorsionHolomorphic

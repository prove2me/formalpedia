-- Prove2me | solution 1 for GlobalTheory.IntegralMultiple.coe_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:52.490806+00:00
-- url     : https://prove2.me/submissions/7ae0f748-8116-422f-a750-7bd625804561

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoeSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultiple
open NumberField
namespace GlobalTheory.IntegralMultiple
theorem _root_.solution {E : Type} [Field E] [NumberField E] {j : ℕ}
    (Λ : Submodule (𝓞 E) (Fin j → E)) (r : 𝓞 E) {v : Fin j → E} (hv : v ∈ Λ) :
    (r : E) • v ∈ Λ := by
  have := Λ.smul_mem r hv
  rwa [← algebraMap_smul E r v] at this
end GlobalTheory.IntegralMultiple

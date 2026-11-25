-- Prove2me | solution 1 for GlobalTheory.BlockValue.OnlyIn.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:55.331196+00:00
-- url     : https://prove2.me/submissions/c008de94-e69c-47a6-8fa5-174775bee1be

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_one
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}
namespace GlobalTheory.BlockValue
namespace OnlyIn
theorem _root_.solution {S : σ → Prop} {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries σ C}
    (hf : ∀ i ∈ s, OnlyIn S (f i)) : OnlyIn S (∏ i ∈ s, f i) :=
  Finset.prod_induction _ _ (fun _ _ => OnlyIn.mul) (OnlyIn.one S) hf
end OnlyIn
end GlobalTheory.BlockValue

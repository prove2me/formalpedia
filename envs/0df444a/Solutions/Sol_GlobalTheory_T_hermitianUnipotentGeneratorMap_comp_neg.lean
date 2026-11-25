-- Prove2me | solution 1 for GlobalTheory.T.hermitianUnipotentGeneratorMap_comp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:16:02.595735+00:00
-- url     : https://prove2.me/submissions/54dc12cc-79c3-4eb7-a58a-e996166553e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapCompNeg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapCompNegStatement
import Theorems.Thm_GlobalTheory_RowStab_gen_comp_gen_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c c' : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, c a b + c' a b + H.B (ρ b) (ρ a) = 0) → ∀ v : V, GlobalTheory.RowStab.gen H J e ρ c (GlobalTheory.RowStab.gen H J e (-ρ) c' v) = v := by
  first | exact @GlobalTheory.RowStab.gen_comp_gen_neg | exact GlobalTheory.RowStab.gen_comp_gen_neg | (intros; apply GlobalTheory.RowStab.gen_comp_gen_neg <;> assumption)
end _root_.GlobalTheory.T

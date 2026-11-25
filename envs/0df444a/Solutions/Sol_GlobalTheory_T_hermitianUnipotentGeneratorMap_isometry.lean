-- Prove2me | solution 1 for GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:31.883565+00:00
-- url     : https://prove2.me/submissions/bf0eec2f-b17e-4b46-9795-89c2dda31eb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapIsometry
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemIpowSmulOfSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianUnipotentGeneratorMapIsometryStatement
import Theorems.Thm_GlobalTheory_RowStab_gen_isometry


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
theorem _root_.solution : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) → ∀ u v : V, H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  first | exact @GlobalTheory.RowStab.gen_isometry | exact GlobalTheory.RowStab.gen_isometry | (intros; apply GlobalTheory.RowStab.gen_isometry <;> assumption)
end _root_.GlobalTheory.T

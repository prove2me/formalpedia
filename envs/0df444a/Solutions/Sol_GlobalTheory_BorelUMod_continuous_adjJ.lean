-- Prove2me | solution 1 for GlobalTheory.BorelUMod.continuous_adjJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:02:34.397542+00:00
-- url     : https://prove2.me/submissions/56e66ebc-faf5-41e3-8b32-72e188889364

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.BorelUMod
theorem _root_.solution {σ : L →+* L} (hσ : Continuous σ) (n : ℕ) :
    Continuous (adjJ σ : Matrix (Fin n) (Fin n) L → Matrix (Fin n) (Fin n) L) :=
  continuous_matrix fun i j => hσ.comp (continuous_id.matrix_elem j.rev i.rev)
end GlobalTheory.BorelUMod

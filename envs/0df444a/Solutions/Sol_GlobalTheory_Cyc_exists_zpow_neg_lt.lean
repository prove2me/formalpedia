-- Prove2me | solution 1 for GlobalTheory.Cyc.exists_zpow_neg_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:52.604095+00:00
-- url     : https://prove2.me/submissions/2662cfcf-a8fa-4bc4-a2b1-51d62ff239fb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε
end GlobalTheory.Cyc

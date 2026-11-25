-- Prove2me | solution 1 for GlobalTheory.Cyc.padicInt_norm_add_eq_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:55:26.471058+00:00
-- url     : https://prove2.me/submissions/d744fab2-6c22-42d9-bb6a-4459ba2474d7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneOfNotDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution {a b : ℤ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [PadicInt.norm_add_eq_max_of_ne h.ne', max_eq_left h.le]
end GlobalTheory.Cyc

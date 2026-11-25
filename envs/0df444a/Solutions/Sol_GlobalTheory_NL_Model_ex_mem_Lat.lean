-- Prove2me | solution 1 for GlobalTheory.NL.Model.ex_mem_Lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:32.695555+00:00
-- url     : https://prove2.me/submissions/5c82a6b7-d867-4bdc-ac4b-d7f1777942f1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
import Theorems.Thm_GlobalTheory_NL_Model_mem_latSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
  {K : FinExt l} {s : ℕ} {LL : FinExt l}
open TensorProduct
variable {l : ℕ} [Fact l.Prime] {P : _root_.Formalism.BasicNotions.LocPrime l} {AI : _root_.Formalism.BasicNotions.LocAinf l P} {H : _root_.Formalism.BasicNotions.LocHW l P}
  {F : _root_.Formalism.BasicNotions.LocFon l P AI H} {K : _root_.Formalism.BasicNotions.Loc.FinExt l} {s : ℕ} {LL : _root_.Formalism.BasicNotions.Loc.FinExt l}
namespace GlobalTheory.NL.Model
namespace _root_.GlobalTheory.NL.Model
theorem _root_.solution (C : _root_.Formalism.BasicNotions.LocCmpT l P AI H F) (h : _root_.Formalism.BasicNotions.Loc.Good K s LL)
    (T : _root_.GlobalTheory.NL.Lt K LL) (i : _root_.GlobalTheory.NL.Let K) (ζ : ↥LL.1)
    (x : ↥((H.W K s LL h).N T)) :
    _root_.GlobalTheory.NL.ex C h T i ζ x ∈ _root_.GlobalTheory.NL.Lat C h T i ζ :=
  _root_.GlobalTheory.NL.Model.mem_latSpan _ x
end _root_.GlobalTheory.NL.Model
end GlobalTheory.NL.Model

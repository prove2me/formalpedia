-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.chi_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:50.938731+00:00
-- url     : https://prove2.me/submissions/6039c418-0295-4ab9-b48a-ca550d850b74

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.Model
theorem _root_.solution : Continuous fun g : GQ l => (chi g : ℚ_[l]) :=
  (continuous_subtype_val : Continuous fun x : ℤ_[l] => (x : ℚ_[l])).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (cyclotomicCharacter.continuous l ℚ_[l] (Om l)))
end GlobalTheory.Cyc.Model

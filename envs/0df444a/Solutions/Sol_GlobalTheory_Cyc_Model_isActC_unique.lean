-- Prove2me | solution 1 for GlobalTheory.Cyc.Model.isActC_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:37:44.705339+00:00
-- url     : https://prove2.me/submissions/96434d68-b2e6-4306-9cf5-d05fafb19498

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
theorem _root_.solution {a b : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC a)
    (hb : IsActC b) : a = b := by
  ext g y
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (AddMonoidHomClass.isometry_of_norm (a g) (ha.2 g)).continuous
            (AddMonoidHomClass.isometry_of_norm (b g) (hb.2 g)).continuous
  | ih x => rw [ha.1, hb.1]
end GlobalTheory.Cyc.Model

-- Prove2me | solution 1 for GlobalTheory.InertiaEigenvalues.norm_galExtC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:09:21.605805+00:00
-- url     : https://prove2.me/submissions/587bdce6-e815-4fea-94e6-3629a57636bd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GalExtCContinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.InertiaEigenvalues
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.InertiaEigenvalues
theorem _root_.solution (g : GQ l) (y : PadicComplex l) : ‖galExtC g y‖ = ‖y‖ := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (galExtC_continuous g).norm continuous_norm
  | ih x => rw [galExtC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_galAlgCl]
end GlobalTheory.InertiaEigenvalues

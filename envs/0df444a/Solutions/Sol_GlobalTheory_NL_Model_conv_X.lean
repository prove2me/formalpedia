-- Prove2me | solution 1 for GlobalTheory.NL.Model.conv_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:28.286385+00:00
-- url     : https://prove2.me/submissions/78ad1a69-57d8-490a-999e-6d0933dcaf9c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt

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
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.NL.Model
theorem _root_.solution (u : ℤ → M) (k : ℤ) : conv (PowerSeries.X : PowerSeries L) u k = u (k - 1) := by
  unfold conv
  rw [finsum_eq_single _ 1]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_X, hj]
end GlobalTheory.NL.Model

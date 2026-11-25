-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.leviQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:00.225448+00:00
-- url     : https://prove2.me/submissions/8fd88f1b-3f15-40ff-967a-5b019b9ff582

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_levi_pullback_iwasawa_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution : BdetLaw → ExtLaw → GrpTop → LeviQ := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε s hI
  exact levi_pullback_iwasawa_unitary A ε hB hE hT hA hI
end GlobalTheory.CompanionTheory.RgEisLeviQUnit

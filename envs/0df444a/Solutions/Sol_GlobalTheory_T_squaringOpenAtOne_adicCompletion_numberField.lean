-- Prove2me | solution 1 for GlobalTheory.T.squaringOpenAtOne_adicCompletion_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:22:26.704467+00:00
-- url     : https://prove2.me/submissions/05c50c12-a12d-4d8b-bd65-5ff30a02ef2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneAdicCompletionNumberField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneAdicCompletionNumberFieldStatement
import Theorems.Thm_GlobalTheory_QSA_sqOpen_and_nhdsNE_zero_neBot_adicCompletion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  first | exact @GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | exact GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion | (intros; apply GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion <;> assumption)
end _root_.GlobalTheory.T

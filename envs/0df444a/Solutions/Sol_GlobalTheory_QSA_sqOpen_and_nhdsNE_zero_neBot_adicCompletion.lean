-- Prove2me | solution 1 for GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:47:42.818709+00:00
-- url     : https://prove2.me/submissions/706340fd-735e-49b8-b3a3-c423dbeb3ed5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneOfCompleteTwoNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquaringOpenAtOneAdicCompletionNumberField
import Theorems.Thm_GlobalTheory_T_squaringOpenAtOne_of_complete_two_ne_zero


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
noncomputable section
open GlobalTheory GlobalTheory.QSA
namespace GlobalTheory.QSA
theorem _root_.solution :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    intro h
    have h' : algebraMap F (v.adicCompletion F) 2 = algebraMap F (v.adicCompletion F) 0 := by
      rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero ((algebraMap F (v.adicCompletion F)).injective h')
  refine ⟨GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero (v.adicCompletion F) h2, ?_⟩
  infer_instance
end GlobalTheory.QSA

-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.Ks_le_Kinf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:19.74081+00:00
-- url     : https://prove2.me/submissions/443e938c-8fce-4ad6-916d-61b9e4d18fa0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AlmostTrace
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.AlmostTrace
theorem _root_.solution (K : FinExt l) (i : ℕ) : Ks K i ≤ Kinf K := by
  unfold Ks Kinf
  exact sup_le_sup_left (IntermediateField.adjoin.mono _ _ _
    fun (x : Om l) (hx : x ^ l ^ i = 1) => (⟨i, hx⟩ : ∃ j : ℕ, x ^ l ^ j = 1)) _
end GlobalTheory.Cyc.AlmostTrace

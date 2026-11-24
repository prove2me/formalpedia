-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.Kinf_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:30.437523+00:00
-- url     : https://prove2.me/submissions/7d1462b0-c86c-4953-8875-150eb4a53558

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_le_Kinf

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
theorem _root_.solution (K : FinExt l) : Kinf K = ⨆ i, Ks K i := by
  refine le_antisymm ?_ (iSup_le fun i => Ks_le_Kinf K i)
  have h0 : K0 K ≤ Ks K 0 := by
    unfold Ks
    exact le_sup_left
  unfold Kinf
  refine sup_le (h0.trans (le_iSup (Ks K) 0)) ?_
  rw [IntermediateField.adjoin_le_iff]
  rintro x ⟨j, hj⟩
  have hx : x ∈ Ks K j := by
    unfold Ks
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ j = 1} ≤ _)
      (IntermediateField.subset_adjoin _ _ hj)
  exact le_iSup (Ks K) j hx
end GlobalTheory.Cyc.AlmostTrace

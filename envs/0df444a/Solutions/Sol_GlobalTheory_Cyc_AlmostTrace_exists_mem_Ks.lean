-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.exists_mem_Ks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:23:52.743967+00:00
-- url     : https://prove2.me/submissions/12756fb2-fd1c-41e4-9583-1bd7f7ede647

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Ks_mono
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Kinf_eq_iSup

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
theorem _root_.solution (K : FinExt l) {x : Om l} (hx : x ∈ Kinf K) : ∃ i, x ∈ Ks K i := by
  rw [Kinf_eq_iSup] at hx
  have h : x ∈ ((⨆ i, Ks K i : IntermediateField ℚ_[l] (Om l)) : Set (Om l)) := hx
  rw [IntermediateField.coe_iSup_of_directed (Ks_mono K).directed_le, Set.mem_iUnion] at h
  exact h
end GlobalTheory.Cyc.AlmostTrace

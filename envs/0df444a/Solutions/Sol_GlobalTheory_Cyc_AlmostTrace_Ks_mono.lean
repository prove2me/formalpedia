-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.Ks_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:18.928465+00:00
-- url     : https://prove2.me/submissions/86449ca3-99b4-490b-b0ce-2316ad44f821

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
theorem _root_.solution (K : FinExt l) : Monotone (Ks K) := by
  intro i j hij
  unfold Ks
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
  obtain ⟨c, hc⟩ := pow_dvd_pow l hij
  have hx' : x ^ l ^ i = 1 := hx
  show x ^ l ^ j = 1
  rw [hc, pow_mul, hx', one_pow]
end GlobalTheory.Cyc.AlmostTrace

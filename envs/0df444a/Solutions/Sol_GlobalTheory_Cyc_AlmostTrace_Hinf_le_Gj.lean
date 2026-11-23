-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.Hinf_le_Gj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:51.134802+00:00
-- url     : https://prove2.me/submissions/45628aff-dd5c-4c02-9f10-192ae8dc09de

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
theorem _root_.solution (K : FinExt l) (i : ℕ) : Hinf K ≤ Gj K i := by
  unfold Hinf Gj
  exact IntermediateField.fixingSubgroup_antitone (Ks_le_Kinf K i)
end GlobalTheory.Cyc.AlmostTrace

-- Prove2me | solution 1 for GlobalTheory.AnArc.Hw_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:36:21.592687+00:00
-- url     : https://prove2.me/submissions/9dd6a0b8-4086-49c5-bf20-89a1bbc7b45f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_torusProj_def
import Theorems.Thm_GlobalTheory_AnArc_dualForm_pos
import Theorems.Thm_GlobalTheory_AnArc_Hw_apply
import Theorems.Thm_GlobalTheory_AnArc_H_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) {v : A.V} (hv : v ≠ 0) : 0 < (A.Hw w v v).re := by
  rw [Hw_apply, Complex.add_re]
  by_cases h : A.torusProj v = 0
  · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext (by simpa [torusProj_def, h2] using h) h2)
    simpa [h] using A.H_pos h2
  · refine add_pos_of_nonneg_of_pos ?_ (A.dualForm_pos hw h)
    by_cases h2 : v.2 = 0
    · simp [h2]
    · exact (A.H_pos h2).le
end GlobalTheory.AnArc

-- Prove2me | solution 1 for GlobalTheory.AnArc.Bw_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:32:45.406355+00:00
-- url     : https://prove2.me/submissions/3f0930b1-d08c-40a4-8332-e2765f0d6d00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_Bw_symm
import Theorems.Thm_GlobalTheory_AnArc_BwMat_apply
import Theorems.Thm_GlobalTheory_AnArc_map_eq_sum_repr

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
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) {y : A.X} (hy : y ≠ 0) : 0 < A.Bw w y y := by
  have h0 : (fun i => ((Module.Free.chooseBasis ℤ A.X).repr y i : ℝ)) ≠ 0 := fun h => hy <|
    (Module.Free.chooseBasis ℤ A.X).ext_elem fun i => by simpa using congrFun h i
  have := (posDef_iff_dotProduct_mulVec.1 hw).2 h0
  refine this.trans_eq (Eq.symm ?_)
  rw [A.map_eq_sum_repr (A.Bw w y) y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Bw_symm, A.map_eq_sum_repr (A.Bw w _) y]
  simp [mulVec, dotProduct, BwMat_apply, mul_comm]
end GlobalTheory.AnArc

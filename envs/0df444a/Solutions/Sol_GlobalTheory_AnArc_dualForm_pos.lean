-- Prove2me | solution 1 for GlobalTheory.AnArc.dualForm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:19:01.137063+00:00
-- url     : https://prove2.me/submissions/29236b79-185d-44da-9dcd-e20dba20d965

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_dualForm_re_im

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
theorem _root_.solution {w : ℂ} (hw : (A.BwMat w).PosDef) {r : A.X →+ ℂ} (hr : r ≠ 0) : 0 < (A.dualForm w r r).re := by
  classical
  rw [(A.dualForm_re_im w r r _ rfl).1]
  have hp : ∀ x, x ≠ 0 → 0 < x ⬝ᵥ (A.BwMat w)⁻¹ *ᵥ x := fun x hx => by
    simpa using (posDef_iff_dotProduct_mulVec.1 hw.inv).2 hx
  have hn : ∀ x, 0 ≤ x ⬝ᵥ (A.BwMat w)⁻¹ *ᵥ x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  by_cases h : (fun i => (A.coord r i).re) = 0
  · refine add_pos_of_nonneg_of_pos (hn _) (hp _ fun h' => hr (A.coord.map_eq_zero_iff.1 (funext fun i => ?_)))
    exact Complex.ext (congrFun h i) (congrFun h' i)
  · exact add_pos_of_pos_of_nonneg (hp _ h) (hn _)
end GlobalTheory.AnArc

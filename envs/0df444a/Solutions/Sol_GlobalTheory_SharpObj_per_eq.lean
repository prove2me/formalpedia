-- Prove2me | solution 1 for GlobalTheory.SharpObj.per_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:23.491933+00:00
-- url     : https://prove2.me/submissions/db725c5b-5769-4fba-bde4-12287f245a29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
import Theorems.Thm_GlobalTheory_SharpObj_per_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}
namespace GlobalTheory.SharpObj
theorem _root_.solution (x : Fin h ⊕ Fin h → ℤ) :
    per τ x = τ.mulVec (ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inl i) : ℝ)) +
      ReciprocityTheory.PTheta.ofRealVec fun i => (x (.inr i) : ℝ) := by
  funext i
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [per_apply]
end GlobalTheory.SharpObj

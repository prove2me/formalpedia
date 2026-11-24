-- Prove2me | solution 1 for GlobalTheory.SharpObj.imInv_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:01:31.30066+00:00
-- url     : https://prove2.me/submissions/c68d36ec-0bde-4e74-aabe-fde245870b1f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
import Theorems.Thm_GlobalTheory_SharpObj_hermForm_real_re

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
theorem _root_.solution (hp : (τ.map Complex.im).PosDef) (z : Fin h → ℂ) (hz : z ≠ 0) :
    0 < (hermForm (imInv τ) z z).re := by
  have hN := hp.inv
  rw [imInv, hermForm_real_re]
  have key : ∀ v : Fin h → ℝ, 0 ≤ v ⬝ᵥ (τ.map Complex.im)⁻¹.mulVec v := fun v => by
    simpa using hN.posSemidef.dotProduct_mulVec_nonneg v
  by_cases hr : (fun i => (z i).re) = 0
  · have hi : (fun i => (z i).im) ≠ 0 := by
      intro hi
      apply hz
      funext i
      apply Complex.ext
      · simpa using congrFun hr i
      · simpa using congrFun hi i
    have := hN.dotProduct_mulVec_pos hi
    simp only [star_trivial] at this
    linarith [key (fun i => (z i).re)]
  · have := hN.dotProduct_mulVec_pos hr
    simp only [star_trivial] at this
    linarith [key (fun i => (z i).im)]
end GlobalTheory.SharpObj

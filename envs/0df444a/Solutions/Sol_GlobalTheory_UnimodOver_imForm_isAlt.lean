-- Prove2me | solution 1 for GlobalTheory.UnimodOver.imForm_isAlt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:49:51.260153+00:00
-- url     : https://prove2.me/submissions/6ce06aa8-f15e-49fc-9884-a90af7de9694

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
import Theorems.Thm_GlobalTheory_UnimodOver_imForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module
namespace GlobalTheory.UnimodOver
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) :
    (imForm Hm).IsAlt := by
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, h.eq, ← Matrix.dotProduct_mulVec]
  intro z
  rw [imForm_apply]
  have hq := key (star z)
  rw [star_star] at hq
  exact Complex.conj_eq_iff_im.mp hq
end GlobalTheory.UnimodOver

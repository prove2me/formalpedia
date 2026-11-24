-- Prove2me | solution 1 for GlobalTheory.UnimodOver.imForm_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:49:52.16064+00:00
-- url     : https://prove2.me/submissions/aa6c135c-cc85-427a-bcbd-b578f551a03b

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
theorem _root_.solution {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) :
    (imForm Hm).Nondegenerate := by
  have hL : ∀ z : Fin g → ℂ, (∀ w, imForm Hm z w = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz (Complex.I • z)
    rw [imForm_apply, star_smul, Complex.star_def, Complex.conj_I, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul] at h1
    have h2 := hp z hne
    simp [Complex.mul_im] at h1
    linarith
  have hR : ∀ w : Fin g → ℂ, (∀ z, imForm Hm z w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hw (Complex.I • w)
    rw [imForm_apply, smul_dotProduct, smul_eq_mul] at h1
    have h2 := hp w hne
    simp [Complex.mul_im] at h1
    linarith
  first
    | exact ⟨hL, hR⟩
    | exact hL
end GlobalTheory.UnimodOver

-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:20:13.092716+00:00
-- url     : https://prove2.me/submissions/7a4d61ee-c38d-4a10-bc14-969b2ba52b24

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_toGL_val
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_claim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t) {n : ℕ}
    (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, l φ = 0 := by
  classical
  let c : k → ℂ := fun a => if h : a = 0 then 0 else ξ (Units.mk0 a h)
  have hc : ∀ a : kˣ, c a = ξ a := fun a => by simp [c]
  refine claim (c := c) (ϖ := ϖ) (fun a ha => ?_) ϖ.ne_zero (fun h => hξ 1 one_pos ?_) (fun t ht h => hξ t⁻¹ (inv_pos.2 ht) ?_)
    n d l (fun h hh => ⟨1, one_pos, fun φ hφ => ?_⟩) hd
  · simp [c, ha]
  · rw [Units.val_eq_one.1 h]; simp
  · rw [← hc, Complex.ofReal_inv]; exact eq_inv_of_mul_eq_one_left h
  · have := hl φ hφ (toGL h)
    rw [← hc, GeneralLinearGroup.val_det_apply, toGL_val hh] at this
    simpa using this
end GlobalTheory.ThK.Dbl.LD

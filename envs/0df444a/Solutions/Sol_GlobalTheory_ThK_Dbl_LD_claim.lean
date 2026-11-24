-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.LD.claim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:09:25.985994+00:00
-- url     : https://prove2.me/submissions/a5edc693-9750-47f8-83d1-6ffbc57dfbad

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_step_chart
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_step_row
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_step_closed
import Theorems.Thm_GlobalTheory_ThK_Dbl_LD_det_blk


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
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}
namespace GlobalTheory.ThK.Dbl.LD
theorem _root_.solution (hc : ∀ a ≠ 0, c a ≠ 0) (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) (hϖ : ∀ t : ℝ, 0 < t → c ϖ * t ≠ 1) (n : ℕ) :
    ∀ d, Claim c n d := by
  have zero : ∀ n, Claim c n 0 := fun n l _ h φ hφ => h φ hφ fun X ⟨v, hv, _⟩ => absurd (Subsingleton.elim _ _) hv
  induction n with
  | zero =>
    rintro (_ | d)
    · exact zero _
    intro l hl _ φ hφ
    obtain ⟨t, pt, ht⟩ := hl (blk ϖ 0 1) (by simp [det_blk, h0])
    have a := ht φ hφ
    have e : ∀ y : Matrix (Fin 0) (Fin (d + 1)) k, y * blk ϖ (0 : Fin d → k) 1 = y := fun y => by ext i; exact i.elim0
    simp only [e, det_blk, det_one, mul_one] at a
    by_contra h
    exact hϖ t pt (mul_right_cancel₀ h (by rw [← a, one_mul]))
  | succ n ih =>
    rintro (_ | d)
    · exact zero _
    exact fun l hl hd => step_closed (ih _) hl hd (step_row hc hl (step_chart hc h0 h1 (ih d) hl hd))
end GlobalTheory.ThK.Dbl.LD

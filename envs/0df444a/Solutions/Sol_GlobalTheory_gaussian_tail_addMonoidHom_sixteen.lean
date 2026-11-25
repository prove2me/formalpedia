-- Prove2me | solution 1 for GlobalTheory.gaussian_tail_addMonoidHom_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:38:55.182803+00:00
-- url     : https://prove2.me/submissions/050dcb0f-c73a-4609-aa4c-a66b67ff0f1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_GaussianSumOfOneSeparatedOfLe
import Theorems.Thm_GlobalTheory_gaussian_tail_addMonoidHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric MeasureTheory Module Set Real
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace GlobalTheory
theorem _root_.solution {A : Type*} [AddGroup A] (u : A →+ E) {g : ℕ}
    (hg : finrank ℝ E = 2 * g) {R : ℝ} (hR0 : 0 ≤ R) (hR : 16 * (2 * (g : ℝ) + 1) ≤ R ^ 2)
    (hu : ∀ y, y ≠ 0 → R ≤ ‖u y‖) :
    Summable (fun y : {y : A // y ≠ 0} => exp (-‖u y‖ ^ 2 / 16)) ∧
      ∑' y : {y : A // y ≠ 0}, exp (-‖u y‖ ^ 2 / 16) ≤ 2 * 9 ^ g * exp (-R ^ 2 / 16) := by
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have h := gaussian_tail_addMonoidHom u (b := R ^ 2) (q := 1 / 16) (by linarith)
    (by rw [hg]; push_cast; linarith) (fun y hy => by have := hu y hy; gcongr)
  have e : ∀ x : ℝ, -(1 / 16 * x) = -x / 16 := fun x => by ring
  simp only [e] at h
  rw [hg, pow_mul] at h
  norm_num at h ⊢
  exact h
end GlobalTheory

-- Prove2me | solution 1 for MonoInclCLC.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:23:04.784259+00:00
-- url     : https://prove2.me/submissions/9a9ea00e-0a68-4249-aac5-c153cafff27a

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoInclCLC_IsClosedLoopSolution

open InnerProductSpace ThreeOpSplitting.Convergence

open MonoInclCLC in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H → Set H) (hA : IsMaximalMonotone A) (hzer : (zer A).Nonempty)
    (J : ℝ → H → H) (hJ : ∀ l : ℝ, 0 < l → IsResolvent l A (J l))
    (p : ℕ) (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ)
    (x : ℝ → H) (lam : ℝ → ℝ)
    (hsol : IsClosedLoopSolution J p θ (Set.Ici 0) x lam) (hx0 : x 0 ∉ zer A)
    (z : H) (hz : z ∈ zer A) (t : ℝ) (ht : 0 ≤ t) :
    ∃ e : ℝ, HasDerivWithinAt (fun s : ℝ => (1 / 2 : ℝ) * ‖x s - z‖ ^ 2) e (Set.Ici 0) t ∧
      e ≤ -‖x t - J (lam t) (x t)‖ ^ 2 := by
  obtain ⟨hl, hd, _⟩ := hsol t (Set.mem_Ici.mpr ht)
  have hD := ((hd.sub_const z).norm_sq).const_mul (1 / 2 : ℝ)
  refine ⟨_, hD, ?_⟩
  set y := J (lam t) (x t) with hy
  have hm := hA.1 y z ((lam t)⁻¹ • (x t - y)) 0 (hJ (lam t) hl (x t)) hz
  rw [sub_zero, real_inner_smul_right] at hm
  have hm' : 0 ≤ ⟪y - z, x t - y⟫_ℝ := (mul_nonneg_iff_of_pos_left (inv_pos.mpr hl)).mp hm
  have e1 : ⟪x t - z, y - x t⟫_ℝ = -‖x t - y‖ ^ 2 - ⟪y - z, x t - y⟫_ℝ := by
    have : x t - z = (x t - y) + (y - z) := by abel
    rw [this, inner_add_left, ← neg_sub (x t) y, inner_neg_right, inner_neg_right,
      real_inner_self_eq_norm_sq]
    ring
  linarith

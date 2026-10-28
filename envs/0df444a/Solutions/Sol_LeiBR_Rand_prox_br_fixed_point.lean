-- Prove2me | solution 1 for LeiBR.Rand.prox_br_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:33:11.845716+00:00
-- url     : https://prove2.me/submissions/5e58da98-a36f-4f90-8269-094c42dc9240

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_ProxBR
import Definitions.Def_LeiBR_Rand_Assumption1

open MeasureTheory ProbabilityTheory

open LeiBR.Rand in
theorem solution {N : ℕ} {n : Fin N → ℕ} {d : ℕ} (G : Game N n)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 G μξ ψ gψ M) (mu : ℝ) (hmu : 0 < mu)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : IsProxBR G mu xhat)
    (xstar : LeiBR.Sync.Profile n) (hNE : G.IsNE xstar) (i : Fin N) :
    xhat xstar i = xstar i := by
  obtain ⟨hmem, hmin⟩ := hxhat xstar hNE.1 i
  have h1 := isMinOn_iff.mp hmin (xstar i) (hNE.1 i)
  have h2 := hNE.2 i _ hmem
  rw [Function.update_eq_self, sub_self, norm_zero] at h1
  have h3 : ‖xhat xstar i - xstar i‖ ^ 2 ≤ 0 := by
    have : mu / 2 * ‖xhat xstar i - xstar i‖ ^ 2 ≤ 0 := by
      have : (0:ℝ) ^ 2 = 0 := by norm_num
      nlinarith
    have hm : 0 < mu / 2 := by linarith
    nlinarith [sq_nonneg ‖xhat xstar i - xstar i‖]
  have h4 : ‖xhat xstar i - xstar i‖ = 0 := by
    nlinarith [norm_nonneg (xhat xstar i - xstar i)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

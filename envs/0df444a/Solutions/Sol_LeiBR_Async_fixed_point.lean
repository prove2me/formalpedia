-- Prove2me | solution 1 for LeiBR.Async.fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:58:02.01301+00:00
-- url     : https://prove2.me/submissions/39ac5ef4-0fe1-4e5f-9f1b-804fee769975

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model

open LeiBR.Async in
theorem solution {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (xs : LeiBR.Sync.Profile n)
    (hNE : LeiBR.Sync.IsNashEq X f xs) :
    ∀ i : Fin N, xhat xs i = xs i := by
  intro i
  obtain ⟨hX, hmin⟩ := hxhat xs hNE.1 i
  have hxi : xs i ∈ X i := hNE.1 i (Set.mem_univ i)
  have h1 := isMinOn_iff.mp hmin (xs i) hxi
  have h2 := hNE.2 i _ hX
  simp only [Function.update_eq_self, sub_self, norm_zero] at h1
  have h3 : ‖xhat xs i - xs i‖ ^ 2 ≤ 0 := by nlinarith
  have h4 : ‖xhat xs i - xs i‖ = 0 := by nlinarith [norm_nonneg (xhat xs i - xs i)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

-- Prove2me | solution 1 for KumarSeidman.CAF.clearing_run_length
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:25:44.323791+00:00
-- url     : https://prove2.me/submissions/96821a45-320e-4482-9234-26b9d2d5b3f0

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov
open KumarSeidman.CAF MeasureTheory
set_option autoImplicit false

private theorem start_nonneg {P M : ℕ} {S : System P M} (T : Trajectory S)
    (m : Fin M) (k : ℕ) (hk : (k : ℕ∞) < T.N m) : 0 ≤ T.s m k := by
  induction k with
  | zero => simp [T.s_zero]
  | succ k ih =>
    have hk' : (k : ℕ∞) < T.N m := lt_of_le_of_lt (by exact_mod_cast Nat.le_succ k) hk
    have hδ : 0 ≤ runSetup S (T.β m) k := by
      cases k <;> simp [runSetup, S.δ_nonneg]
    have := T.setup_not_cut m k hk
    linarith [ih hk']

theorem solution {P M : ℕ} (S : System P M) (T : Trajectory S)
    (hT : T.IsClearing) (m : Fin M) (hρ : S.rhoPrime m < 1) (k : ℕ) (hk : 1 ≤ k)
    (hnext : T.HasNext m k)
    (hx : 2 * S.deltaBar m / ((1 - S.rhoPrime m) * S.tau (T.β m k)) ≤ T.x (T.β m k) (T.s m k)) :
    2 * S.deltaBar m / (1 - S.rhoPrime m) ≤ T.s m (k + 1) - T.s m k := by
  have hn : (k : ℕ∞) < T.N m := lt_of_le_of_lt (by exact_mod_cast Nat.le_succ k) hnext
  have hs := start_nonneg T m k hn
  have hδ : 0 ≤ runSetup S (T.β m) k := by
    cases k <;> simp [runSetup, S.δ_nonneg]
  have ht : T.s m k ≤ T.s m (k + 1) := by linarith [T.setup_not_cut m k hnext]
  have hempty := (hT m k hn).2 hnext
  let b := T.β m k
  have hτ : 0 < S.tau b := S.τ_pos b.1 b.2
  have hu : inflow S T.y b (T.s m k) ≤ inflow S T.y b (T.s m (k + 1)) := by
    unfold inflow
    cases S.prev b with
    | none => exact mul_le_mul_of_nonneg_left ht (S.d_pos b.1).le
    | some b' => exact T.y_mono b' hs (le_trans hs ht) ht
  have hbal₁ := T.balance b (T.s m k) hs
  have hbal₂ := T.balance b (T.s m (k + 1)) (by linarith)
  have hr := T.rate_cap b (T.s m k) (T.s m (k + 1)) hs ht
  have hvol : (volume (Set.Icc (T.s m k) (T.s m (k + 1)) ∩
      {σ | ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ})).toReal ≤
      T.s m (k + 1) - T.s m k := by
    have hm := measure_mono (μ := (volume : Measure ℝ)) (Set.inter_subset_left :
      Set.Icc (T.s m k) (T.s m (k + 1)) ∩
      {σ | ProcessesAt S (T.N (S.mach b)) (T.β (S.mach b)) (T.s (S.mach b)) b σ} ⊆
      Set.Icc (T.s m k) (T.s m (k + 1)))
    have := ENNReal.toReal_mono (by simp) hm
    simpa [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr ht)] using this
  have hr' : T.x b (T.s m k) ≤ (T.s m (k + 1) - T.s m k) / S.tau b := by
    have he : T.x b (T.s m (k + 1)) = 0 := hempty.1
    have hv := div_le_div_of_nonneg_right hvol hτ.le
    linarith
  have hh := le_trans hx hr'
  have heq : 2 * S.deltaBar m / ((1 - S.rhoPrime m) * S.tau b) =
      (2 * S.deltaBar m / (1 - S.rhoPrime m)) / S.tau b := by rw [div_div]
  rw [heq] at hh
  exact (div_le_div_iff_of_pos_right hτ).mp hh

#print axioms solution

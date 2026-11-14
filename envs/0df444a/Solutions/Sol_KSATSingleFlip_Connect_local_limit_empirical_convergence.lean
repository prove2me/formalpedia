-- Prove2me | solution 1 for KSATSingleFlip.Connect.local_limit_empirical_convergence
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:07:39.151208+00:00
-- url     : https://prove2.me/submissions/1b891ca5-c296-4fde-88ca-8807500787a1

import Theorems.Thm_KSATSingleFlip_Connect_local_limit_empirical_second_moment
import Mathlib
set_option autoImplicit false
open Filter
open scoped BigOperators Topology

theorem solution (Ω : ℕ → Type) [∀ n, Fintype (Ω n)]
    (p : ∀ n, Ω n → ℝ) (hp : ∀ n ω, 0 ≤ p n ω)
    (X : ∀ n, Fin n → Ω n → ℝ) (C : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hdiag : ∀ n i, (∑ ω, p n ω * (X n i ω)^2) ≤ C)
    (hoff : ∀ n (i j : Fin n), i ≠ j → (∑ ω, p n ω * X n i ω * X n j ω) ≤ ε n)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n => ∑ ω, if t ≤ |(∑ i : Fin n, X n i ω)/(n:ℝ)| then p n ω else 0)
      atTop (𝓝 0) := by
  have hr : Tendsto (fun n : ℕ => C/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun n : ℕ => (C/(n:ℝ)+ε n)/t^2) atTop (𝓝 0) := by
    simpa using (hr.add hε0).div_const (t^2)
  apply squeeze_zero' _ _ hbound
  · exact Filter.Eventually.of_forall (fun n => Finset.sum_nonneg (fun ω hω => by split_ifs <;> simp [hp]))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact KSATSingleFlip.Connect.local_limit_empirical_second_moment n hn (p n) (hp n) (X n) C (ε n) t (hε n) ht (hdiag n) (hoff n)

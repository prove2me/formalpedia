-- Prove2me | solution 1 for MasulloRH.bernstein_bilateral_prime_interpolation_cost
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T10:39:27.86218+00:00
-- url     : https://prove2.me/submissions/2516c7a6-d5c7-4f3e-9db2-3b5c44f8a8a0

import Mathlib
import Theorems.Thm_MetodosNumericos_lagrange_error_bound
open Set
theorem solution (n : ℕ) (p : Fin (n+1) → ℕ) (P : ℕ)
    (hp : ∀ i, (p i).Prime) (hinc : StrictMono p) (hP : ∀ i, p i ≤ P)
    (H : ℝ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : ContDiff ℝ (n+1 : ℕ) H)
    (hzero : ∀ i, H (Real.log (p i : ℝ)) = 0)
    (hder : ∀ y ∈ Ioo (-Real.log 2-1) (Real.log (P:ℝ)+1),
      |iteratedDerivWithin (n+1) H (Ioo (-Real.log 2-1) (Real.log (P:ℝ)+1)) y| ≤ A * B^(n+1)) :
    |H (-Real.log 2)| * ((n+1).factorial : ℝ) ≤
      A * (B * (Real.log (P:ℝ)+Real.log 2))^(n+1) := by
  classical
  let xs := fun i : Fin (n+1) => Real.log (p i : ℝ)
  have hpos (i) : 0 < (p i : ℝ) := by exact_mod_cast (hp i).pos
  have hlog (i) : 0 < xs i := Real.log_pos (by exact_mod_cast (hp i).one_lt)
  have hub (i) : xs i ≤ Real.log (P:ℝ) :=
    Real.log_le_log (hpos i) (by exact_mod_cast hP i)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPlog := (hlog 0).trans_le (hub 0)
  have monot : StrictMono xs := by
    intro i j hij
    apply Real.log_lt_log (hpos i)
    exact_mod_cast hinc hij
  have h := MetodosNumericos.lagrange_error_bound H (-Real.log 2-1)
    (Real.log (P:ℝ)+1) (A*B^(n+1)) xs monot
    (fun i => ⟨by linarith [hlog i],by linarith [hub i]⟩)
    hc.contDiffOn hder (-Real.log 2) ⟨by linarith,by linarith⟩
    (fun i => by linarith [hlog i])
  have hsimp : MetodosNumericos.lagrangeInterp xs (fun i => H (xs i)) (-Real.log 2) = 0 := by
    simp [MetodosNumericos.lagrangeInterp,xs,hzero]
  rw [hsimp, sub_zero] at h
  have hpbd : (∏ k : Fin (n+1), |-Real.log 2-xs k|) ≤
      (Real.log (P:ℝ)+Real.log 2)^(n+1) := by
    calc
      _ ≤ ∏ _k : Fin (n+1), (Real.log (P:ℝ)+Real.log 2) := by
        apply Finset.prod_le_prod
        · intro i hi; exact abs_nonneg _
        · intro i hi
          rw [abs_of_nonpos (by linarith [hlog i] : -Real.log 2-xs i ≤ 0)]
          linarith [hub i]
      _ = _ := by simp
  have hfact : 0 < ((n+1).factorial : ℝ) := by positivity
  have hh := h.trans (mul_le_mul_of_nonneg_left hpbd (by positivity))
  rw [mul_pow]
  apply (le_div_iff₀ hfact).mp
  calc
    _ ≤ _ := hh
    _ = _ := by ring

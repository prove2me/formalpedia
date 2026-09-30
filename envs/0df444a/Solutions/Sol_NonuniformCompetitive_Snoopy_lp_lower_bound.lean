-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.lp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:04:22.210482+00:00
-- url     : https://prove2.me/submissions/4744e7b2-0a92-4c8e-83f2-56dedebb6451

import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Mathlib.Tactic
open NonuniformCompetitive.Snoopy
open scoped BigOperators

theorem solution (p : ℕ) (hp : 1 ≤ p) (π : ℕ → ℝ) (α : ℝ)
    (hπ : π (p + 1) = 1)
    (hcon : ∀ k ≤ p, π (k + 1) * p + ∑ i ∈ Finset.Icc 1 k, (1 - π i) ≤ α * k) :
    ep p / (ep p - 1) ≤ α := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  let r : ℝ := ((p:ℝ)+1)/p
  let S (k : ℕ) : ℝ := ∑ i∈Finset.Icc 1 k, π i
  have hr : 1 < r := by dsimp [r]; apply (lt_div_iff₀ hpR).mpr; linarith
  have hep : ep p=r^p := by unfold ep; congr 1; dsimp [r]; field_simp [ne_of_gt hpR]
  have he : 1 < ep p := by rw [hep]; exact one_lt_pow₀ hr (by omega)
  have hcon' (k : ℕ) (hk : k ≤ p) : π (k+1)*(p:ℝ) + k - S k ≤ α*k := by
    have h := hcon k hk
    simp [Finset.sum_sub_distrib] at h
    dsimp [S]
    linarith
  have hb : ∀ k ≤ p, S k ≤ (α-1)*((p:ℝ)*(r^k-1)-k) := by
    intro k
    induction k with
    | zero => intro hk; simp [S]
    | succ k ih =>
      intro hk
      have hki : k ≤ p := by omega
      have ih' := ih hki
      have hstep : π (k+1) ≤ (α-1)*(r^k-1) := by
        apply (mul_le_mul_iff_right₀ hpR).mp
        nlinarith [hcon' k hki]
      have halg : (α-1)*((p:ℝ)*(r^(k+1)-1)-(k+1)) =
          (α-1)*((p:ℝ)*(r^k-1)-k)+(α-1)*(r^k-1) := by
        rw [pow_succ]
        dsimp [r]
        field_simp [ne_of_gt hpR]
        ring
      have hS : S (k+1)=S k+π (k+1) := by
        exact Finset.sum_Icc_succ_top (by omega : 1 ≤ k+1) π
      rw [hS]
      push_cast
      rw [halg]
      exact add_le_add ih' hstep
  have hlast := hcon' p le_rfl
  rw [hπ] at hlast
  have hb' := hb p le_rfl
  rw [← hep] at hb'
  have hfinal : 1 ≤ (α-1)*(ep p-1) := by
    apply (mul_le_mul_iff_right₀ hpR).mp
    nlinarith
  apply (div_le_iff₀ (by linarith : 0 < ep p-1)).mpr
  nlinarith

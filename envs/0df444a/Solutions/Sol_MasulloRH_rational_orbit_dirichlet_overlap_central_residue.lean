-- Prove2me | solution 1 for MasulloRH.rational_orbit_dirichlet_overlap_central_residue
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T02:25:20.905023+00:00
-- url     : https://prove2.me/submissions/e16166b7-fb09-4e06-97d6-39738491979b

import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two
import Mathlib.Tactic.Positivity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.LinearCombination

open Filter Complex
open scoped Topology

private theorem orbit_dirichlet_sum (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j : ℕ => 1/((j:ℂ)+1)^s) (riemannZeta s) := by
  have h0 := Complex.summable_one_div_nat_cpow.mpr hs
  have hs' : Summable (fun j : ℕ => 1/((j:ℂ)+1)^s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h0
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  exact hs'.hasSum

private theorem rational_overlap_series (m n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    let w (k : ℕ) := (1 / (k:ℂ)^s) / riemannZeta s
    HasSum (fun j : ℕ => w (j+1)) 1 ∧
    HasSum (fun j : ℕ => w (m*(j+1)) * w (n*(j+1)))
      (((m*n : ℕ):ℂ)^(-s) * riemannZeta (2*s) / (riemannZeta s)^2) := by
  dsimp only
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  constructor
  · simpa only [Nat.cast_add_one, div_self hz] using (orbit_dirichlet_sum s hs).div_const (riemannZeta s)
  · have h2 : 1 < (2*s).re := by rw [two_mul, Complex.add_re]; linarith
    have H := ((orbit_dirichlet_sum (2*s) h2).mul_left (((m*n:ℕ):ℂ)^(-s))).div_const ((riemannZeta s)^2)
    apply H.congr_fun
    intro j
    simp only [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.cpow_neg]
    simp only [Nat.cast_add_one,
      div_eq_mul_inv, one_mul, mul_inv_rev]
    have hbase : ((j:ℂ)+1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
    rw [two_mul, Complex.cpow_add _ _ hbase]
    ring


open Filter Set
open scoped Topology

namespace MasulloRH

theorem shifted_orbit_zeta_half_residue (A : ℝ) (hA : 0 < A)
    (hz : riemannZeta (1/2:ℂ) ≠ 0) :
    let o (s : ℂ) := (A:ℂ)^(-s) * riemannZeta (2*s) / (riemannZeta s)^2
    let c := (A:ℂ)^(-(1/2:ℂ)) / (riemannZeta (1/2:ℂ))^2
    c ≠ 0 ∧
      Tendsto (fun s : ℂ => (2*s-1) * o s) (𝓝[≠] (1/2:ℂ)) (𝓝 c) ∧
      Tendsto (fun s : ℂ => (s-1/2) * o s) (𝓝[≠] (1/2:ℂ)) (𝓝 (c/2)) := by
  let b : ℂ := 1/2
  have hb : b ≠ 1 := by norm_num [b]
  have hA' : (A:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hd : Tendsto (fun s : ℂ => 2*s) (𝓝[≠] b) (𝓝[≠] (1:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto (fun s : ℂ => 2*s) (𝓝 b) (𝓝 (2*b)) := (continuous_const.mul continuous_id).continuousAt
      simpa [b] using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s ≠ b at hs
      change 2*s ≠ 1
      intro h
      apply hs
      dsimp [b]
      linear_combination h/2
  have hz2 : Tendsto (fun s : ℂ => (2*s-1)*riemannZeta (2*s)) (𝓝[≠] b) (𝓝 1) :=
    riemannZeta_residue_one.comp hd
  have hζ : Tendsto riemannZeta (𝓝[≠] b) (𝓝 (riemannZeta b)) :=
    (differentiableAt_riemannZeta hb).continuousAt.continuousWithinAt
  have hk : Tendsto (fun s : ℂ => (A:ℂ)^(-s)) (𝓝[≠] b) (𝓝 ((A:ℂ)^(-b))) :=
    (continuousAt_const_cpow hA').comp continuous_neg.continuousAt |>.continuousWithinAt
  have hfull := (hk.mul hz2).div (hζ.pow 2) (pow_ne_zero 2 hz)
  have hlim : Tendsto (fun s : ℂ => (2*s-1)*((A:ℂ)^(-s)*riemannZeta (2*s)/(riemannZeta s)^2))
      (𝓝[≠] b) (𝓝 ((A:ℂ)^(-b)/(riemannZeta b)^2)) := by
    simpa only [mul_one, Pi.div_def, Pi.mul_def, mul_div_assoc', mul_left_comm, mul_assoc] using hfull
  refine ⟨div_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hA')) (pow_ne_zero 2 hz),hlim,?_⟩
  convert hlim.div_const (2:ℂ) using 2 with s
  ring

end MasulloRH

theorem solution (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    let o (s : ℂ) := ((m*n : ℕ):ℂ)^(-s) * riemannZeta (2*s) / (riemannZeta s)^2
    let c := ((m*n : ℕ):ℂ)^(-(1/2:ℂ)) / (riemannZeta (1/2:ℂ))^2
    (∀ s : ℂ, 1 < s.re →
      let w (k : ℕ) := (1 / (k:ℂ)^s) / riemannZeta s
      HasSum (fun j : ℕ => w (j+1)) 1 ∧
      HasSum (fun j : ℕ => w (m*(j+1)) * w (n*(j+1))) (o s)) ∧
      c ≠ 0 ∧
      Tendsto (fun s : ℂ => (2*s-1) * o s) (𝓝[≠] (1/2:ℂ)) (𝓝 c) ∧
      Tendsto (fun s : ℂ => (s-1/2) * o s) (𝓝[≠] (1/2:ℂ)) (𝓝 (c/2)) := by
  dsimp only
  refine ⟨fun s hs => rational_overlap_series m n s hs, ?_⟩
  have hhalf : riemannZeta (1/2:ℂ) ≠ 0 := by
    apply zeta_ne_zero_of_mem_strip_of_abs_im_le_two <;> norm_num
  simpa only [Complex.ofReal_natCast] using
    MasulloRH.shifted_orbit_zeta_half_residue ((m*n:ℕ):ℝ) (by positivity) hhalf
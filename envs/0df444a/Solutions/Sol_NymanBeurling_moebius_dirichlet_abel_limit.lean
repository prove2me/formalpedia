-- Prove2me | solution 1 for NymanBeurling.moebius_dirichlet_abel_limit
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T01:08:11.055179+00:00
-- url     : https://prove2.me/submissions/d04d216d-1c45-42e2-a850-73c2660a1301

import Mathlib

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

theorem solution :
    Tendsto (fun ε : ℝ =>
      LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
  have he : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun ε : ℝ => 1 + (ε : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using tendsto_const_nhds.add he, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (ε : ℂ) = 0 := by linear_combination h
    exact (ne_of_gt hε) (Complex.ofReal_eq_zero.mp this)
  have hr := riemannZeta_residue_one.comp hs
  have hq := he.div hr (one_ne_zero : (1 : ℂ) ≠ 0)
  simp only [zero_div] at hq
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hp : 1 < (1 + (ε : ℂ)).re := by simpa using hε
  have hm := LSeries_one_mul_Lseries_moebius hp
  rw [LSeries_one_eq_riemannZeta hp] at hm
  have hz := riemannZeta_ne_zero_of_one_lt_re hp
  have hn : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
  dsimp only [Function.comp_def]
  simp only [add_sub_cancel_left]
  apply (div_eq_iff (mul_ne_zero hn hz)).mpr
  symm
  calc
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 + (ε : ℂ)) *
        ((ε : ℂ) * riemannZeta (1 + (ε : ℂ))) =
        (ε : ℂ) * (riemannZeta (1 + (ε : ℂ)) *
          LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 + (ε : ℂ))) := by ring
    _ = (ε : ℂ) := by rw [hm, mul_one]

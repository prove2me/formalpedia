-- Prove2me | solution 1 for Lean4LPD.entryFactor_le_geom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:05:53.074209+00:00
-- url     : https://prove2.me/submissions/9741c65c-42eb-4e67-bf98-e1617dc2a656

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Theorems.Thm_Lean4LPD_rungW_nonneg
public import Theorems.Thm_Lean4LPD_epsJump_nonneg
public import Theorems.Thm_Lean4LPD_epsJump_ratio

set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset
namespace Lean4LPD
theorem _root_.solution {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {nu : ℕ} (hnu : 1 ≤ nu) (hb1 : betaOf kh1 c a < 1) :
    entryFactor kh1 c a nu ≤ epsJump kh1 c a nu nu / (1 - betaOf kh1 c a) := by
  set b := betaOf kh1 c a with hbdef
  have hb0 : 0 ≤ b := by
    rw [hbdef]; unfold betaOf
    have hw2 : 0 ≤ rungW kh1 c 2 := rungW_nonneg hkh hc (by omega)
    have := Real.exp_pos 1
    positivity
  set u : ℕ → ℝ := fun i => epsJump kh1 c a (nu + i) nu with hudef
  have hu0 : ∀ i, 0 ≤ u i := fun i =>
    epsJump_nonneg hkh hc ha (nu + i) nu (by omega)
  have hstep : ∀ i, u (i + 1) ≤ b * u i := by
    intro i
    have h := epsJump_ratio hkh hc ha (j := nu + i) (nu := nu) hnu (by omega)
    have hidx : nu + i + 1 = nu + (i + 1) := by omega
    rw [hidx] at h
    exact h
  have hgeom : ∀ i, u i ≤ b ^ i * u 0 := fun i => le_geom hb0 i fun k _ => hstep k
  have hsummable : Summable (fun i : ℕ => b ^ i) := summable_geometric_of_lt_one hb0 hb1
  have hpartial : ∀ n : ℕ, ∑ i ∈ range n, u i ≤ u 0 / (1 - b) := by
    intro n
    have h1 : ∑ i ∈ range n, u i ≤ ∑ i ∈ range n, b ^ i * u 0 :=
      Finset.sum_le_sum fun i _ => hgeom i
    have h2 : ∑ i ∈ range n, b ^ i * u 0 = (∑ i ∈ range n, b ^ i) * u 0 := by
      rw [Finset.sum_mul]
    have h3 : ∑ i ∈ range n, b ^ i ≤ ∑' i : ℕ, b ^ i :=
      hsummable.sum_le_tsum _ (fun i _ => pow_nonneg hb0 i)
    have h4 : ∑' i : ℕ, b ^ i = (1 - b)⁻¹ := tsum_geometric_of_lt_one hb0 hb1
    have h5 : (0 : ℝ) < 1 - b := by linarith
    calc ∑ i ∈ range n, u i ≤ (∑ i ∈ range n, b ^ i) * u 0 := by rw [← h2]; exact h1
      _ ≤ (1 - b)⁻¹ * u 0 := by
          exact mul_le_mul_of_nonneg_right (by rw [← h4]; exact h3) (hu0 0)
      _ = u 0 / (1 - b) := by rw [inv_mul_eq_div]
  have hzero : u 0 = epsJump kh1 c a nu nu := by simp [hudef]
  have := Real.tsum_le_of_sum_range_le hu0 hpartial
  rw [← hzero]
  exact this
end Lean4LPD

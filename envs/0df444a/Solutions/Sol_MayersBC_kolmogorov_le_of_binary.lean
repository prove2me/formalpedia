-- Prove2me | solution 1 for MayersBC.kolmogorov_le_of_binary
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:23:31.716086+00:00
-- url     : https://prove2.me/submissions/dda6e1fe-e3f9-4acb-84af-70eeef1e13a8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_MayersBC_outcomeDist
import Definitions.Def_MayersBC_binaryPOVM
import Definitions.Def_MayersBC_kolmogorov
open QAlgorithms
open scoped ComplexOrder

/-- `Tr((Σ_j M_j) ρ) = Σ_j Tr(M_j ρ)` for the real parts. -/
private lemma effectProb_sum {ι J : Type} [Fintype ι] (s : Finset J) (M : J → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) : effectProb (∑ j ∈ s, M j) ρ = ∑ j ∈ s, effectProb (M j) ρ := by
  simp only [effectProb, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

private lemma effectProb_one_sub {ι : Type} [Fintype ι] [DecidableEq ι] (Q ρ : Matrix ι ι ℂ)
    (hρ : IsDensityMatrix ρ) : effectProb (1 - Q) ρ = 1 - effectProb Q ρ := by
  simp only [effectProb, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    hρ.2, Complex.one_re]

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ)
    (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) (ε : ℝ)
    (hbin : ∀ Q : Matrix ι ι ℂ, IsEffect Q →
      MayersBC.kolmogorov (MayersBC.outcomeDist (MayersBC.binaryPOVM Q) ρ0)
        (MayersBC.outcomeDist (MayersBC.binaryPOVM Q) ρ1) ≤ 4 * ε)
    {J : Type} [Fintype J] (M : J → Matrix ι ι ℂ) (hM : IsPOVM M) :
    MayersBC.kolmogorov (MayersBC.outcomeDist M ρ0) (MayersBC.outcomeDist M ρ1) ≤ 4 * ε := by
  classical
  -- differences of the outcome probabilities
  set d : J → ℝ := fun j => effectProb (M j) ρ0 - effectProb (M j) ρ1 with hd
  have htot : ∑ j, d j = 0 := by
    have e0 := effectProb_sum Finset.univ M ρ0
    have e1 := effectProb_sum Finset.univ M ρ1
    rw [hM.2] at e0 e1
    have t0 : effectProb (1 : Matrix ι ι ℂ) ρ0 = 1 := by simp [effectProb, h0.2]
    have t1 : effectProb (1 : Matrix ι ι ℂ) ρ1 = 1 := by simp [effectProb, h1.2]
    simp only [hd, Finset.sum_sub_distrib]
    linarith
  -- the outcomes where `ρ0` is at least as likely as `ρ1`
  set S := Finset.univ.filter fun j => 0 ≤ d j with hS
  set Q : Matrix ι ι ℂ := ∑ j ∈ S, M j with hQ
  have hcompl : 1 - Q = ∑ j ∈ Finset.univ.filter (fun j => ¬ 0 ≤ d j), M j := by
    rw [← hM.2, hQ, hS, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 ≤ d j) M,
      add_sub_cancel_left]
  have hQeff : IsEffect Q := by
    refine ⟨Matrix.posSemidef_sum _ fun j _ => hM.1 j, ?_⟩
    rw [hcompl]
    exact Matrix.posSemidef_sum _ fun j _ => hM.1 j
  have hb := hbin Q hQeff
  -- the binary measurement `{Q, I - Q}` has Kolmogorov distance `2 Σ_S d`
  set D := ∑ j ∈ S, d j with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun j hj => (Finset.mem_filter.mp hj).2
  have hQd : effectProb Q ρ0 - effectProb Q ρ1 = D := by
    rw [hQ, effectProb_sum, effectProb_sum, hD, ← Finset.sum_sub_distrib]
  have hbinK : MayersBC.kolmogorov (MayersBC.outcomeDist (MayersBC.binaryPOVM Q) ρ0)
      (MayersBC.outcomeDist (MayersBC.binaryPOVM Q) ρ1) = 2 * D := by
    simp only [MayersBC.kolmogorov, MayersBC.outcomeDist, MayersBC.binaryPOVM, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, effectProb_one_sub Q ρ0 h0,
      effectProb_one_sub Q ρ1 h1]
    have : 1 - effectProb Q ρ0 - (1 - effectProb Q ρ1) = -(effectProb Q ρ0 - effectProb Q ρ1) := by
      ring
    rw [this, abs_neg, hQd, abs_of_nonneg hD0]
    ring
  -- the general measurement has the same Kolmogorov distance
  have hK : MayersBC.kolmogorov (MayersBC.outcomeDist M ρ0) (MayersBC.outcomeDist M ρ1) =
      2 * D := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 ≤ d j)
      (fun j => |d j|)
    have hsplit' := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 ≤ d j) d
    have hpos : ∑ j ∈ Finset.univ.filter (fun j => 0 ≤ d j), |d j| = D := by
      rw [hD, hS]
      exact Finset.sum_congr rfl fun j hj => abs_of_nonneg (Finset.mem_filter.mp hj).2
    have hneg : ∑ j ∈ Finset.univ.filter (fun j => ¬ 0 ≤ d j), |d j| =
        -∑ j ∈ Finset.univ.filter (fun j => ¬ 0 ≤ d j), d j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j hj =>
        abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hj).2)
    simp only [MayersBC.kolmogorov, MayersBC.outcomeDist]
    change ∑ j, |d j| = 2 * D
    rw [← hsplit, hpos, hneg]
    rw [htot, ← hS, ← hD] at hsplit'
    linarith
  rw [hK, ← hbinK]
  exact hb

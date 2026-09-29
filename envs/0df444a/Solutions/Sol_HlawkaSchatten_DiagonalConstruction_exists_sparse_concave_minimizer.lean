-- Prove2me | solution 1 for HlawkaSchatten.DiagonalConstruction.exists_sparse_concave_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-29T00:53:20.383527+00:00
-- url     : https://prove2.me/submissions/052fb66a-fadb-47ca-b4a5-2959b6f11203

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Sparsification
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Three constraints admit a sparse concave minimizer

For nonnegative coordinate weights, fixing three positive linear moments
gives a compact feasible set. Minimize the concave objective, then maximize
the sum of squared weights among its minimizers. A supported kernel
direction would produce two feasible perturbations whose average squared
size is strictly larger. Thus at most three weights are positive.
-/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten.DiagonalConstruction

private theorem isClosed_momentFiber (A : ι → Fin 3 → ℝ) (b : Fin 3 → ℝ) :
    IsClosed (momentFiber A b) := by
  simp only [momentFiber, Set.ofPred_and, Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_iInter fun k ↦ isClosed_eq
      (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul continuous_const)
      continuous_const

private theorem isCompact_momentFiber (A : ι → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (hA : ∀ i k, 0 ≤ A i k) (hpos : ∀ i, 0 < ∑ k, A i k) :
    IsCompact (momentFiber A b) := by
  have hbox : IsCompact (Set.Icc (0 : ι → ℝ) (fun i ↦ (∑ k, b k) / (∑ k, A i k))) :=
    isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_momentFiber A b)
  intro w hw
  refine ⟨hw.1, fun i ↦ ?_⟩
  change w i ≤ (∑ k, b k) / (∑ k, A i k)
  apply (le_div_iff₀ (hpos i)).mpr
  have hsum : (∑ j, w j * ∑ k, A j k) = ∑ k, b k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ hw.2 k
  rw [← hsum]
  exact Finset.single_le_sum
    (fun j _ ↦ mul_nonneg (hw.1 j) (Finset.sum_nonneg fun k _ ↦ hA j k))
    (Finset.mem_univ i)

theorem solution
    (A : ι → Fin 3 → ℝ) (b : Fin 3 → ℝ)
    (hA : ∀ i k, 0 ≤ A i k) (hpos : ∀ i, 0 < ∑ k, A i k)
    (F : (ι → ℝ) → ℝ) (hF : Continuous F)
    (hconc : ConcaveOn ℝ {w : ι → ℝ | ∀ i, 0 ≤ w i} F)
    (w₀ : ι → ℝ) (hw₀ : w₀ ∈ momentFiber A b) :
    ∃ w ∈ momentFiber A b, F w ≤ F w₀ ∧ Fintype.card {i // w i ≠ 0} ≤ 3 := by
  classical
  have hcompact := isCompact_momentFiber A b hA hpos
  obtain ⟨v, hv, hvmin⟩ := hcompact.exists_isMinOn ⟨w₀, hw₀⟩ hF.continuousOn
  let D := momentFiber A b ∩ {w | F w ≤ F v}
  have hDcompact : IsCompact D :=
    hcompact.inter_right (isClosed_le hF continuous_const)
  have hvD : v ∈ D := ⟨hv, by change F v ≤ F v; rfl⟩
  let G := fun w : ι → ℝ ↦ ∑ i, (w i) ^ 2
  have hG : Continuous G := continuous_finsetSum _ fun i _ ↦ (continuous_apply i).pow 2
  obtain ⟨w, hw, hwmax⟩ := hDcompact.exists_isMaxOn ⟨v, hvD⟩ hG.continuousOn
  have hwmin : ∀ u ∈ momentFiber A b, F w ≤ F u :=
    fun u hu ↦ hw.2.trans (hvmin hu)
  refine ⟨w, hw.1, hwmin w₀ hw₀, ?_⟩
  by_contra hcard
  let J := {i : ι // w i ≠ 0}
  have hdep : ¬LinearIndependent ℝ (fun j : J ↦ A j.1) := by
    intro hlin
    exact hcard (by simpa [J] using hlin.fintype_card_le_finrank)
  obtain ⟨g, hg, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have : Nonempty J := ⟨j₀⟩
  have hwpos (j : J) : 0 < w j.1 :=
    lt_of_le_of_ne (hw.1.1 j.1) (Ne.symm j.2)
  obtain ⟨jmin, _, hjmin⟩ := Finset.univ.exists_min_image
    (fun j : J ↦ w j.1 / (|g j| + 1)) Finset.univ_nonempty
  let ε := w jmin.1 / (|g jmin| + 1)
  have hε : 0 < ε := div_pos (hwpos jmin) (by positivity)
  have hεbound (j : J) : ε * |g j| ≤ w j.1 := by
    have hh := (le_div_iff₀ (show 0 < |g j| + 1 by positivity)).mp
      (hjmin j (Finset.mem_univ j))
    change ε * (|g j| + 1) ≤ w j.1 at hh
    nlinarith
  let d : ι → ℝ := fun i ↦ if h : w i ≠ 0 then ε * g ⟨i, h⟩ else 0
  have hdbound (i : ι) : |d i| ≤ w i := by
    by_cases hi : w i ≠ 0
    · simpa only [d, dif_pos hi, abs_mul, abs_of_pos hε] using hεbound ⟨i, hi⟩
    · simp [d, not_ne_iff.mp hi]
  have hdcoeff (k : Fin 3) : ∑ i, d i * A i k = 0 := by
    have hgk := congrArg (fun v : Fin 3 → ℝ ↦ v k) hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hgk
    have hleft : (∑ j : J, d j.1 * A j.1 k) = ε * ∑ j : J, g j * A j.1 k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [d]
      rw [dif_pos j.2]
      ring
    have hright : (∑ j : {i : ι // ¬w i ≠ 0}, d j.1 * A j.1 k) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [d, dif_neg j.2, zero_mul]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i ↦ w i ≠ 0),
      hleft, hright, hgk, mul_zero, add_zero]
  have hdne : d j₀.1 ≠ 0 := by
    simp only [d, dif_pos j₀.2]
    exact mul_ne_zero hε.ne' hj₀
  let u : ι → ℝ := w + d
  let z : ι → ℝ := w - d
  have hu : u ∈ momentFiber A b := by
    constructor
    · intro i
      have hh := (abs_le.mp (hdbound i)).1
      change 0 ≤ w i + d i
      linarith
    · intro k
      simp only [u, Pi.add_apply, add_mul, Finset.sum_add_distrib, hdcoeff,
        hw.1.2 k, add_zero]
  have hz : z ∈ momentFiber A b := by
    constructor
    · intro i
      have hh := (abs_le.mp (hdbound i)).2
      change 0 ≤ w i - d i
      linarith
    · intro k
      simp only [z, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hdcoeff,
        hw.1.2 k, sub_zero]
  have havg : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • z = w := by
    ext i
    simp only [u, z, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hmid := hconc.2 hu.1 hz.1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [havg] at hmid
  simp only [smul_eq_mul] at hmid
  have hwv : F w ≤ F v := hw.2
  have huD : u ∈ D := ⟨hu, by change F u ≤ F v; linarith [hwmin u hu, hwmin z hz]⟩
  have hzD : z ∈ D := ⟨hz, by change F z ≤ F v; linarith [hwmin u hu, hwmin z hz]⟩
  have huG := hwmax huD
  have hzG := hwmax hzD
  change G u ≤ G w at huG
  change G z ≤ G w at hzG
  have hsum : G u + G z = 2 * G w + 2 * ∑ i, (d i) ^ 2 := by
    dsimp only [G]
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [u, z, Pi.add_apply, Pi.sub_apply]
    ring
  have hdpos : 0 < ∑ i, (d i) ^ 2 := Finset.sum_pos'
    (fun i _ ↦ sq_nonneg (d i)) ⟨j₀.1, Finset.mem_univ _, sq_pos_of_ne_zero hdne⟩
  linarith

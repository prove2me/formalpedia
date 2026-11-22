-- Prove2me | solution 1 for MasulloGRH.directSum_normed_exists_rescale_nhds
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:05:09.514952+00:00
-- url     : https://prove2.me/submissions/e0b4590f-afe9-4358-95e7-d9582375999a

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology
open scoped Pointwise DirectSum

set_option autoImplicit false

namespace Sol_MasulloGRH_directSum_normed_exists_rescale_nhds

open Set Filter

section DirectSumSeminorm

variable {𝕜 ι : Type*} {X : ι → Type*}
  [NormedField 𝕜] [∀ i, AddCommGroup (X i)] [∀ i, Module 𝕜 (X i)]
  [DecidableEq ι] [∀ (i : ι) (z : X i), Decidable (z ≠ 0)]

/-- The sum of the coordinate seminorms on an algebraic direct sum. -/
noncomputable def dsSeminorm (p : ∀ i, Seminorm 𝕜 (X i)) : Seminorm 𝕜 (⨁ i, X i) := by
  refine Seminorm.of (fun x ↦ x.sum fun i ↦ p i) (fun x y ↦ ?_) (fun a x ↦ ?_)
  · rw [DFinsupp.sum_of_support_subset DFinsupp.support_add (fun i _ ↦ map_zero (p i)),
      DFinsupp.sum_of_support_subset Finset.subset_union_left (fun i _ ↦ map_zero (p i)),
      DFinsupp.sum_of_support_subset Finset.subset_union_right (fun i _ ↦ map_zero (p i)),
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ ↦ map_add_le_add (p i) (x i) (y i)
  · rw [DFinsupp.sum_of_support_subset (DFinsupp.support_smul a x) (fun i _ ↦ map_zero (p i))]
    simp only [DFinsupp.smul_apply, map_smul_eq_mul, Finset.mul_sum, DFinsupp.sum]

/-- The seminorm sum can be evaluated over any finite set containing the support. -/
theorem dsSeminorm_apply (p : ∀ i, Seminorm 𝕜 (X i)) (x : ⨁ i, X i) (s : Finset ι)
    (hs : x.support ⊆ s) :
    dsSeminorm p x = ∑ i ∈ s, p i (x i) :=
  DFinsupp.sum_of_support_subset hs fun i _ ↦ map_zero (p i)

/-- On a single summand the seminorm sum restricts to the corresponding seminorm. -/
theorem dsSeminorm_lof (p : ∀ i, Seminorm 𝕜 (X i)) (i : ι) (x : X i) :
    dsSeminorm p (DirectSum.lof 𝕜 ι X i x) = p i x :=
  DFinsupp.sum_single_index (h := fun i ↦ p i) (map_zero (p i))

end DirectSumSeminorm

/-- In a space whose topology is given by a family of seminorms, every neighbourhood of `0`
contains the open unit ball of a single continuous seminorm. -/
theorem exists_continuous_seminorm_ball_subset {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] {P : SeminormFamily ℂ E ι} (hP : WithSeminorms P) {V : Set E}
    (hV : V ∈ 𝓝 (0 : E)) :
    ∃ p : Seminorm ℂ E, Continuous p ∧ p.ball 0 1 ⊆ V := by
  have : IsTopologicalAddGroup E := hP.topologicalAddGroup
  obtain ⟨⟨s, r⟩, hr, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.mp hV
  have hr' : (0 : ℝ) < r := hr
  have hc : (0 : NNReal) < Real.toNNReal r⁻¹ := Real.toNNReal_pos.mpr (inv_pos.mpr hr')
  refine ⟨Real.toNNReal r⁻¹ • s.sup P, ?_, ?_⟩
  · exact (Seminorm.continuous_finsetSup fun i _ ↦ hP.continuous_seminorm i).const_smul _
  · rw [Seminorm.ball_smul _ hc, Real.coe_toNNReal _ (inv_pos.mpr hr').le, one_div, inv_inv]
    exact hsub

end Sol_MasulloGRH_directSum_normed_exists_rescale_nhds

open Sol_MasulloGRH_directSum_normed_exists_rescale_nhds in
theorem solution (Y : ℕ → Type*) [∀ k, NormedAddCommGroup (Y k)]
    [∀ k, NormedSpace ℂ (Y k)] :
    letI := RiemannMasullo.locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
    ∀ V : ℕ → Set (⨁ k, Y k), (∀ k, V k ∈ 𝓝 0) →
      ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧ (⋂ k, (ρ k : ℂ) • V k) ∈ 𝓝 0 := by
  classical
  let D := ⨁ k, Y k
  let lof := DirectSum.lof ℂ ℕ Y
  let : TopologicalSpace D := RiemannMasullo.locallyConvexFinalTopology lof
  intro V hV
  let P : SeminormFamily ℂ D {p : Seminorm ℂ D // ∀ k, Continuous (p ∘ lof k)} := Subtype.val
  have hP : WithSeminorms P := ⟨rfl⟩
  have : IsTopologicalAddGroup D := hP.topologicalAddGroup
  have hlof (k : ℕ) : Continuous (lof k) :=
    hP.continuous_of_continuous_comp _ fun s ↦ s.property k
  -- Each neighbourhood contains the unit ball of a continuous seminorm `p i`.
  choose p hp hball using fun i ↦ exists_continuous_seminorm_ball_subset hP (hV i)
  -- On the normed summand `Y k` the seminorm `p i` is bounded by `a i k` times the norm.
  choose a ha hbound using fun i k ↦
    ((p i).comp (lof k)).bound_of_continuous_normedSpace ((hp i).comp (hlof k))
  -- Each scale bounds its row through the diagonal. Each weight bounds its column above it.
  let ρ (i : ℕ) : ℝ := 1 + ∑ k ∈ Finset.range (i + 1), a i k
  let w (k : ℕ) : ℝ := 1 + ∑ i ∈ Finset.range k, a i k
  have hρ (i : ℕ) : 1 ≤ ρ i := le_add_of_nonneg_right (Finset.sum_nonneg fun k _ ↦ (ha i k).le)
  have hw (k : ℕ) : 1 ≤ w k := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (ha i k).le)
  have hρpos (i : ℕ) : 0 < ρ i := zero_lt_one.trans_le (hρ i)
  have hdom (i k : ℕ) : a i k ≤ ρ i * w k := by
    by_cases h : k ≤ i
    · have hsum : a i k ≤ ∑ j ∈ Finset.range (i + 1), a i j :=
        Finset.single_le_sum (fun j _ ↦ (ha i j).le) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      calc
        a i k ≤ ρ i := hsum.trans (le_add_of_nonneg_left zero_le_one)
        _ ≤ ρ i * w k := le_mul_of_one_le_right (hρpos i).le (hw k)
    · have hsum : a i k ≤ ∑ j ∈ Finset.range k, a j k :=
        Finset.single_le_sum (fun j _ ↦ (ha j k).le) (Finset.mem_range.mpr (Nat.lt_of_not_ge h))
      calc
        a i k ≤ w k := hsum.trans (le_add_of_nonneg_left zero_le_one)
        _ ≤ ρ i * w k := le_mul_of_one_le_left (zero_le_one.trans (hw k)) (hρ i)
  -- The weighted sum of the norms of the components is a continuous seminorm on the direct sum.
  let s (k : ℕ) : Seminorm ℂ (Y k) :=
    (w k).toNNReal • normSeminorm ℂ (Y k)
  have hs (k : ℕ) (z : Y k) : s k z = w k * ‖z‖ := by
    change ((w k).toNNReal : ℝ) * ‖z‖ = w k * ‖z‖
    rw [Real.coe_toNNReal _ (zero_le_one.trans (hw k))]
  let q : Seminorm ℂ D := dsSeminorm s
  have hqlof (k : ℕ) : Continuous (q ∘ lof k) := by
    have h : (q ∘ lof k) = fun z : Y k ↦ w k * ‖z‖ := by
      funext z
      change dsSeminorm s (DirectSum.lof ℂ ℕ Y k z) = w k * ‖z‖
      rw [dsSeminorm_lof, hs]
    rw [h]
    exact continuous_norm.const_mul _
  have hq : Continuous q := hP.continuous_seminorm ⟨q, hqlof⟩
  have hpq (i : ℕ) (x : D) : p i x ≤ ρ i * q x := by
    have hsum := Finset.le_sum_of_subadditive (p i) (map_zero (p i)).le
      (map_add_le_add (p i)) x.support (fun k ↦ lof k (x k))
    rw [show (∑ k ∈ x.support, lof k (x k)) = x from DirectSum.sum_support_of x] at hsum
    refine hsum.trans ?_
    rw [show q x = ∑ k ∈ x.support, s k (x k) from dsSeminorm_apply s x _ Finset.Subset.rfl,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [hs, ← mul_assoc]
    exact (hbound i k (x k)).trans (mul_le_mul_of_nonneg_right (hdom i k) (norm_nonneg _))
  have hqball : q.ball 0 1 ∈ 𝓝 (0 : D) := by
    have hopen : IsOpen {x : D | q x < 1} := isOpen_lt hq continuous_const
    refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
    · change q 0 < 1
      rw [map_zero]
      exact zero_lt_one
    · intro x hx
      rw [Seminorm.mem_ball_zero]
      exact hx
  refine ⟨ρ, hρpos, Filter.mem_of_superset hqball ?_⟩
  intro x hx
  rw [Seminorm.mem_ball_zero] at hx
  refine Set.mem_iInter.mpr fun i ↦ Set.smul_set_mono (hball i) ?_
  have hne : (ρ i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hρpos i).ne'
  rw [Seminorm.smul_ball_zero hne, Complex.norm_of_nonneg (hρpos i).le, mul_one,
    Seminorm.mem_ball_zero]
  exact (hpq i x).trans_lt (by simpa only [mul_one] using mul_lt_mul_of_pos_left hx (hρpos i))

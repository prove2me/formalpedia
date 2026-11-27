-- Prove2me | solution 1 for MaxCutSample2027.Coreset.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:13:05.451115+00:00
-- url     : https://prove2.me/submissions/5c9431e2-e49e-4d22-83f8-17b5a8616652

import Theorems.Thm_MaxCutSample2027_Coreset_equation_2_6
import Mathlib.Topology.Sion
import Definitions.Def_MaxCutSample2027_Coreset_fractional
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

open scoped Pointwise

private theorem box_eq_Icc {V : Type*} (q : V → ℝ) : Z q = Set.Icc 0 q := by
  ext a
  exact forall_and

private theorem box_compact {V : Type*} (q : V → ℝ) : IsCompact (Z q) := by
  rw [box_eq_Icc]
  exact isCompact_Icc

private theorem box_nonempty {V : Type*} {q : V → ℝ} (hq : ∀ v, 0 ≤ q v) : (Z q).Nonempty :=
  ⟨0, fun v => ⟨le_rfl, hq v⟩⟩

private theorem box_hull {V : Type*} [Fintype V] {q : V → ℝ} (hq : ∀ v, 0 ≤ q v) :
    Z q = convexHull ℝ (Set.univ.pi fun v => ({0, q v} : Set ℝ)) := by
  rw [convexHull_pi]
  simp only [convexHull_pair, segment_eq_Icc (hq _)]
  ext a
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  rfl

private theorem hull_union {E : Type*} [AddCommGroup E] [Module ℝ E] (s t : Set E) :
    convexHull ℝ (convexHull ℝ s ∪ convexHull ℝ t) = convexHull ℝ (s ∪ t) := by
  rw [convexHull_convexHull_union_left, convexHull_convexHull_union_right]

private theorem comparison_compact {V : Type*} [Fintype V] {r s : V → ℝ}
    (hr : ∀ v, 0 ≤ r v) (hs : ∀ v, 0 ≤ s v) : IsCompact (Ccal r s) := by
  let corners (q : V → ℝ) := Set.univ.pi fun v => ({0, q v} : Set ℝ)
  have fin (q : V → ℝ) : (corners q).Finite :=
    Set.Finite.pi fun v => (Set.finite_singleton (q v)).insert 0
  have negfin (q : V → ℝ) : (-corners q).Finite := by
    rw [← Set.image_neg_eq_neg]
    exact (fin q).image _
  unfold Ccal
  simp only [box_hull hr, box_hull hs, Set.image_neg_eq_neg, ← convexHull_neg]
  change IsCompact (convexHull ℝ
    (convexHull ℝ (corners r) ∪ convexHull ℝ (-corners r) ∪
      convexHull ℝ (corners s) ∪ convexHull ℝ (-corners s)))
  rw [← convexHull_convexHull_union_left
    (convexHull ℝ (corners r) ∪ convexHull ℝ (-corners r) ∪ convexHull ℝ (corners s))
    (convexHull ℝ (-corners s)),
    ← convexHull_convexHull_union_left (convexHull ℝ (corners r) ∪ convexHull ℝ (-corners r))
      (convexHull ℝ (corners s)),
    hull_union (corners r) (-corners r), hull_union (corners r ∪ -corners r) (corners s), hull_union]
  exact ((((fin r).union (negfin r)).union (fin s)).union (negfin s)).isCompact_convexHull ℝ

private theorem comparison_neg {V : Type*} {r s : V → ℝ} {c : V → ℝ}
    (hc : c ∈ Ccal r s) : -c ∈ Ccal r s := by
  let U := Z r ∪ -Z r ∪ Z s ∪ -Z s
  have hneg : -U = U := by
    ext x
    change -x ∈ U ↔ x ∈ U
    simp only [U, Set.mem_union, Set.mem_neg, neg_neg]
    tauto
  have heq : -(convexHull ℝ U) = convexHull ℝ U := by rw [← convexHull_neg, hneg]
  have hc' : c ∈ convexHull ℝ U := by simpa only [Ccal, Set.image_neg_eq_neg, U] using hc
  have hr : -c ∈ convexHull ℝ U := heq ▸ Set.neg_mem_neg.mpr hc'
  simpa only [Ccal, Set.image_neg_eq_neg, U] using hr

private theorem box_subset_comparison_left {V : Type*} (r s : V → ℝ) : Z r ⊆ Ccal r s :=
  fun _ ha => subset_convexHull ℝ _ (Or.inl (Or.inl (Or.inl ha)))

private theorem box_subset_comparison_right {V : Type*} (r s : V → ℝ) : Z s ⊆ Ccal r s :=
  fun _ ha => subset_convexHull ℝ _ (Or.inl (Or.inr ha))

private noncomputable def linearLeft {V : Type*} [Fintype V] (L : V → V → ℝ) (c : V → ℝ) :
    (V → ℝ) →ₗ[ℝ] ℝ where
  toFun a := bilinear L a c
  map_add' a b := by
    simp only [bilinear, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' t a := by
    simp [bilinear, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem bilinear_swap {V : Type*} [Fintype V] (L : V → V → ℝ) (a c : V → ℝ) :
    bilinear L a c = bilinear (fun i j => L j i) c a := by
  unfold bilinear
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private noncomputable def linearRight {V : Type*} [Fintype V] (L : V → V → ℝ) (a : V → ℝ) :
    (V → ℝ) →ₗ[ℝ] ℝ := linearLeft (fun i j => L j i) a

private theorem linearLeft_apply {V : Type*} [Fintype V] (L : V → V → ℝ) (c a : V → ℝ) :
    linearLeft L c a = bilinear L a c := rfl

private theorem linearRight_apply {V : Type*} [Fintype V] (L : V → V → ℝ) (a c : V → ℝ) :
    linearRight L a c = bilinear L a c := (bilinear_swap L a c).symm

private theorem max_linear {V : Type*} [Fintype V] (L : V → V → ℝ) (q c : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) :
    (∃ a ∈ Z q, bilinear L a c = M L q c) ∧ ∀ a ∈ Z q, bilinear L a c ≤ M L q c := by
  have cont : Continuous (fun a => bilinear L a c) := by unfold bilinear; fun_prop
  have bounds := ((box_compact q).image cont).bddAbove
  have lower (a : V → ℝ) (ha : a ∈ Z q) : bilinear L a c ≤ M L q c :=
    le_csSup bounds ⟨a, ha, rfl⟩
  obtain ⟨a, ha, ha'⟩ := (box_compact q).exists_isMaxOn (box_nonempty hq) cont.continuousOn
  refine ⟨⟨a, ha, le_antisymm (lower a ha) ?_⟩, lower⟩
  exact csSup_le ((box_nonempty hq).image _) (by rintro _ ⟨b, hb, rfl⟩; exact ha' hb)

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r s : V → ℝ) (hr : IsProbabilityVector r) (hs : IsProbabilityVector s) :
    (∀ a ∈ Z r, ∃ b ∈ Z s,
      maxAbsLinear (K A p) (a - b) (Ccal r s) ≤ DeltaK (K A p) r s) ∧
    maxAbsLinear (K A p) (r - s) (Ccal r s) ≤ 2 * DeltaK (K A p) r s := by
  classical
  let L := K A p
  let D := Ccal r s
  let Δ := DeltaK L r s
  have compact := comparison_compact hr.1 hs.1
  have nonempty : D.Nonempty := (box_nonempty hr.1).mono (box_subset_comparison_left r s)
  have convex : Convex ℝ D := convex_convexHull _ _
  have hM (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) : Continuous (M L q) := by
    have h : M L q = fun c => ∑ v, q v * max (∑ u, L v u * c u) 0 :=
      funext fun c => equation_2_6 A p hA hp q c hq
    rw [h]
    fun_prop
  have hΔ (c : V → ℝ) (hc : c ∈ D) : |M L r c - M L s c| ≤ Δ :=
    le_csSup (compact.image ((hM r hr.1).sub (hM s hs.1)).abs).bddAbove ⟨c, hc, rfl⟩
  have sup_bound (v : V → ℝ) (b : ℝ) (h : ∀ c ∈ D, |bilinear L v c| ≤ b) :
      maxAbsLinear L v D ≤ b :=
    csSup_le (nonempty.image _) (by rintro _ ⟨c, hc, rfl⟩; exact h c hc)
  constructor
  · intro a ha
    let f (b c : V → ℝ) := bilinear L (a - b) c
    have fb (c : V → ℝ) : (fun b => f b c) =
        fun b => linearLeft L c a - linearLeft L c b := by
      funext b
      rw [← map_sub, linearLeft_apply]
    have fc (b : V → ℝ) : (fun c => f b c) = linearRight L (a - b) := by
      funext c
      rw [linearRight_apply]
    have continuous_b (c : V → ℝ) : Continuous (fun b => f b c) := by
      unfold f bilinear
      simp only [Pi.sub_apply]
      fun_prop
    have continuous_c (b : V → ℝ) : Continuous (fun c => f b c) := by
      unfold f bilinear
      fun_prop
    have cvx : Convex ℝ (Z s) := by rw [box_eq_Icc]; exact convex_Icc _ _
    obtain ⟨b, hb, c₀, hc₀, saddle⟩ := Sion.exists_isSaddlePointOn (f := f)
      (box_nonempty hs.1) cvx (box_compact s)
      (fun c _ => (continuous_b c).continuousOn.lowerSemicontinuousOn)
      (fun c _ => by rw [fb]; exact ((convexOn_const _ cvx).sub ((linearLeft L c).concaveOn cvx)).quasiconvexOn)
      convex nonempty compact
      (fun b _ => (continuous_c b).continuousOn.upperSemicontinuousOn)
      (fun b _ => by rw [fc]; exact ((linearRight L (a - b)).concaveOn convex).quasiconcaveOn)
    obtain ⟨z, hz, hzmax⟩ := (max_linear L s c₀ hs.1).1
    have hupper : f z c₀ ≤ Δ := by
      have hbound := (max_linear L r c₀ hr.1).2 a ha
      change bilinear L (a - z) c₀ ≤ Δ
      rw [← linearLeft_apply, map_sub, linearLeft_apply, linearLeft_apply, hzmax]
      exact (sub_le_sub_right hbound _).trans ((le_abs_self _).trans (hΔ c₀ hc₀))
    refine ⟨b, hb, sup_bound (a - b) Δ ?_⟩
    intro c hc
    apply abs_le.mpr
    have h₁ := (saddle z hz c hc).trans hupper
    have h₂ := (saddle z hz (-c) (comparison_neg hc)).trans hupper
    change bilinear L (a - b) c ≤ Δ at h₁
    change bilinear L (a - b) (-c) ≤ Δ at h₂
    rw [← linearRight_apply, map_neg, linearRight_apply] at h₂
    exact ⟨neg_le.mp h₂, h₁⟩
  · refine sup_bound (r - s) (2 * Δ) ?_
    intro c hc
    have support_diff (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
        M L q c - M L q (-c) = bilinear L q c := by
      rw [equation_2_6 A p hA hp q c hq, equation_2_6 A p hA hp q (-c) hq]
      unfold bilinear
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← mul_sub]
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      simp only [mul_assoc, ← Finset.mul_sum]
      change q v * (max (∑ u, L v u * c u) 0 - max (-(∑ u, L v u * c u)) 0) = _
      congr 1
      generalize ∑ u, L v u * c u = x
      by_cases h : 0 ≤ x
      · rw [max_eq_left h, max_eq_right (by linarith : -x ≤ 0), sub_zero]
      · have h' : x ≤ 0 := le_of_not_ge h
        rw [max_eq_right h', max_eq_left (by linarith : 0 ≤ -x)]
        ring
    have decompose : bilinear L (r - s) c = (M L r c - M L s c) - (M L r (-c) - M L s (-c)) := by
      rw [← linearLeft_apply, map_sub, linearLeft_apply, linearLeft_apply, ← support_diff r hr.1, ← support_diff s hs.1]
      ring
    rw [decompose]
    calc
      _ ≤ |M L r c - M L s c| + |M L r (-c) - M L s (-c)| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (M L r c - M L s c) (-(M L r (-c) - M L s (-c)))
      _ ≤ Δ + Δ := add_le_add (hΔ c hc) (hΔ (-c) (comparison_neg hc))
      _ = _ := by ring

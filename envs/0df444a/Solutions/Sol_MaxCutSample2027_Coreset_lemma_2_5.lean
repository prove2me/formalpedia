-- Prove2me | solution 1 for MaxCutSample2027.Coreset.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:14:48.746862+00:00
-- url     : https://prove2.me/submissions/870a6118-0ba5-413c-b121-c389a2d6d85e

import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_6
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

private theorem bilinear_sub_left {V : Type*} [Fintype V] (L : V → V → ℝ)
    (a b c : V → ℝ) : bilinear L (a - b) c = bilinear L a c - bilinear L b c := by
  rw [← linearLeft_apply, map_sub, linearLeft_apply, linearLeft_apply]

private theorem bilinear_sub_right {V : Type*} [Fintype V] (L : V → V → ℝ)
    (a b c : V → ℝ) : bilinear L a (b - c) = bilinear L a b - bilinear L a c := by
  rw [← linearRight_apply, map_sub, linearRight_apply, linearRight_apply]

private theorem max_cut_fractional {V : Type*} [Fintype V] (L : V → V → ℝ) (q : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) :
    (∃ a ∈ Z q, bilinear L a (q - a) = FK L q) ∧ ∀ a ∈ Z q, bilinear L a (q - a) ≤ FK L q := by
  have cont : Continuous (fun a => bilinear L a (q - a)) := by
    unfold bilinear
    simp only [Pi.sub_apply]
    fun_prop
  have bounds := ((box_compact q).image cont).bddAbove
  have lower (a : V → ℝ) (ha : a ∈ Z q) : bilinear L a (q - a) ≤ FK L q :=
    le_csSup bounds ⟨a, ha, rfl⟩
  obtain ⟨a, ha, ha'⟩ := (box_compact q).exists_isMaxOn (box_nonempty hq) cont.continuousOn
  refine ⟨⟨a, ha, le_antisymm (lower a ha) ?_⟩, lower⟩
  exact csSup_le ((box_nonempty hq).image _) (by rintro _ ⟨b, hb, rfl⟩; exact ha' hb)

private theorem comparison_swap {V : Type*} (r s : V → ℝ) : Ccal r s = Ccal s r := by
  unfold Ccal
  congr 1
  ext c
  simp only [Set.mem_union]
  tauto

private theorem delta_swap {V : Type*} [Fintype V] (L : V → V → ℝ) (r s : V → ℝ) :
    DeltaK L r s = DeltaK L s r := by
  unfold DeltaK
  rw [comparison_swap r s]
  conv_lhs => enter [1, 1, c]; rw [abs_sub_comm]

private theorem comparison_value_le {V : Type*} [Fintype V] {L : V → V → ℝ}
    {r s v c : V → ℝ} (hc : c ∈ Ccal r s) (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i) :
    |bilinear L v c| ≤ maxAbsLinear L v (Ccal r s) := by
  have cont : Continuous (fun c => |bilinear L v c|) := by unfold bilinear; fun_prop
  exact le_csSup ((comparison_compact hr hs).image cont).bddAbove ⟨c, hc, rfl⟩

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r s : V → ℝ) (hr : IsProbabilityVector r) (hs : IsProbabilityVector s) :
    |FK (K A p) r - FK (K A p) s| ≤ 4 * DeltaK (K A p) r s := by
  let L := K A p
  have symm (a b : V → ℝ) : bilinear L a b = bilinear L b a := by
    have hsym (u v : V) : L u v = L v u := by
      dsimp [L, K]
      rw [hA.1 u v]
      congr 1
      ring
    have ht : (fun u v => L v u) = L := funext fun u => funext fun v => hsym v u
    rw [bilinear_swap L a b, ht]
  have one_direction (r s : V → ℝ) (hr : IsProbabilityVector r) (hs : IsProbabilityVector s) :
      FK L r - FK L s ≤ 4 * DeltaK L r s := by
    let Δ := DeltaK L r s
    obtain ⟨a, ha, hmax⟩ := (max_cut_fractional L r hr.1).1
    obtain ⟨matchCut, fullBound⟩ := lemma_2_6 A p hA hp r s hr hs
    obtain ⟨b, hb, matched⟩ := matchCut a ha
    have hbval := (max_cut_fractional L s hs.1).2 b hb
    have hnotin : r - a ∈ Z r := by
      intro v
      simp only [Pi.sub_apply]
      exact ⟨sub_nonneg.mpr (ha v).2, sub_le_self _ (ha v).1⟩
    have h₁ := (comparison_value_le (box_subset_comparison_left r s hnotin) hr.1 hs.1).trans matched
    have h₂ := (comparison_value_le (box_subset_comparison_right r s hb) hr.1 hs.1).trans fullBound
    have h₃ := (comparison_value_le (box_subset_comparison_right r s hb) hr.1 hs.1).trans matched
    have decompose : bilinear L a (r - a) - bilinear L b (s - b) =
        bilinear L (a - b) (r - a) + bilinear L (r - s) b - bilinear L (a - b) b := by
      simp only [bilinear_sub_left, bilinear_sub_right]
      rw [symm b r, symm b s, symm b a]
      ring
    rw [← hmax]
    calc
      _ ≤ bilinear L a (r - a) - bilinear L b (s - b) := sub_le_sub_left hbval _
      _ = _ := decompose
      _ ≤ 4 * Δ := by
        have t₁ := (le_abs_self _).trans h₁
        have t₂ := (le_abs_self _).trans h₂
        have t₃ := (neg_le_abs _).trans h₃
        change bilinear L (a - b) (r - a) ≤ Δ at t₁
        change bilinear L (r - s) b ≤ 2 * Δ at t₂
        change -bilinear L (a - b) b ≤ Δ at t₃
        linarith
  have forward := one_direction r s hr hs
  have backward := one_direction s r hs hr
  rw [delta_swap L s r] at backward
  change |FK L r - FK L s| ≤ 4 * DeltaK L r s
  exact abs_le.mpr ⟨by linarith, forward⟩

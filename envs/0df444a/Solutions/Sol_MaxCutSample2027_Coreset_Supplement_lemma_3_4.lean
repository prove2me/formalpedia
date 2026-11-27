-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:22:26.441953+00:00
-- url     : https://prove2.me/submissions/f1fa3399-eabd-4dfb-a1dd-bb5a1286b46e

import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_6
import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_5
import Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_3_3
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_recovery
open scoped BigOperators
noncomputable section

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

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
private theorem empirical_sum {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (x : Fin k → V) (f : V → ℝ) : ∑ v, empirical x v * f v = (∑ i, f (x i)) / (k : ℝ) := by
  calc
    _ = (∑ v, ((Finset.univ.filter (fun i => x i = v)).card : ℝ) * f v) / (k : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ => by simp only [empirical]; ring
    _ = _ := by
      congr 1
      rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x) (fun _ _ => Finset.mem_univ _) (fun i => f (x i))]
      apply Finset.sum_congr rfl
      intro v _
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

private theorem empirical_probability {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 1 ≤ k) (x : Fin k → V) : IsProbabilityVector (empirical x) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨fun v => div_nonneg (Nat.cast_nonneg _) hk'.le, ?_⟩
  simpa [hk'.ne'] using empirical_sum x (fun _ => 1)

private theorem sample_le {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (f g : (Fin k → V) → ℝ) (h : ∀ x, f x ≤ g x) :
    sampleAverage p k f ≤ sampleAverage p k g := by
  unfold sampleAverage
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x)
    (Finset.prod_nonneg fun i _ => hp (x i))

private theorem sample_smul {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (a : ℝ) (f : (Fin k → V) → ℝ) : sampleAverage p k (fun x => a * f x) = a * sampleAverage p k f := by
  unfold sampleAverage
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring
private theorem kernel_symmetric {V : Type*} [Fintype V] {A : V → V → ℝ} (p : V → ℝ)
    (hA : IsWeightMatrix A) (a b : V → ℝ) : bilinear (K A p) a b = bilinear (K A p) b a := by
  have hsym (u v : V) : K A p u v = K A p v u := by
    unfold K
    rw [hA.1 u v]
    congr 1
    ring
  have ht : (fun u v => K A p v u) = K A p := funext fun u => funext fun v => hsym v u
  rw [bilinear_swap (K A p) a b, ht]

private theorem bilinear_matVec {V : Type*} [Fintype V] (L : V → V → ℝ) (a b : V → ℝ) :
    bilinear L a b = ∑ v, a v * matVec L b v := by
  simp only [matVec, bilinear, Finset.mul_sum, mul_assoc]

private theorem matVec_subtract {V : Type*} [Fintype V] (L : V → V → ℝ) (a b : V → ℝ) (u : V) :
    matVec L (a - b) u = matVec L a u - matVec L b u := by
  simp only [matVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (x : Fin k → V) (a : V → ℝ) (ha : a ∈ Z (empirical x))
    (hopt : bilinear (K A p) a (empirical x - a) = FK (K A p) (empirical x))
    (b : V → ℝ) (hb : b ∈ Z p)
    (hmin : ∀ c ∈ Z p, recoveryError (K A p) x a b ≤ recoveryError (K A p) x a c) :
    FK (K A p) p - 10 * DeltaK (K A p) p (empirical x) ≤ bilinear (K A p) b (p - b) := by
  classical
  let q := empirical x
  let L := K A p
  let Δ := DeltaK L p q
  have hq : IsProbabilityVector q := empirical_probability hk x
  have hpp : IsProbabilityVector p := ⟨fun v => (hp.1 v).le, hp.2⟩
  obtain ⟨matching, _⟩ := lemma_2_6 A p hA hp q p hq hpp
  obtain ⟨c, hc, matched⟩ := matching a ha
  rw [delta_swap L q p, comparison_swap q p] at matched
  let v := a - c
  let pos (u : V) := if 0 ≤ matVec L v u then q u else 0
  let neg (u : V) := if 0 ≤ matVec L v u then 0 else q u
  have hpos : pos ∈ Z q := by
    intro u
    dsimp [pos]
    split_ifs
    · exact ⟨hq.1 u, le_rfl⟩
    · exact ⟨le_rfl, hq.1 u⟩
  have hneg : neg ∈ Z q := by
    intro u
    dsimp [neg]
    split_ifs
    · exact ⟨le_rfl, hq.1 u⟩
    · exact ⟨hq.1 u, le_rfl⟩
  have bound (z : V → ℝ) (hz : z ∈ Z q) : |bilinear L z v| ≤ Δ := by
    rw [show bilinear L z v = bilinear L v z from kernel_symmetric p hA _ _]
    exact (comparison_value_le (box_subset_comparison_right p q hz) hpp.1 hq.1).trans matched
  have eq : recoveryError L x a c = bilinear L pos v - bilinear L neg v := by
    unfold recoveryError
    rw [← empirical_sum x (fun u => |matVec L a u - matVec L c u|)]
    simp_rw [← matVec_subtract L a c]
    rw [bilinear_matVec, bilinear_matVec, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u _
    change q u * |matVec L v u| = _
    by_cases h : 0 ≤ matVec L v u
    · simp [pos, neg, h, abs_of_nonneg h]
    · simp [pos, neg, h, abs_of_nonpos (le_of_not_ge h)]
  have err : recoveryError L x a b ≤ 2 * Δ := by
    apply (hmin c hc).trans
    rw [eq]
    have hp := (le_abs_self _).trans (bound pos hpos)
    have hn := (neg_le_abs _).trans (bound neg hneg)
    linarith
  have comparison := lemma_2_5 A p hA hp p q hpp hq
  have recovery := lemma_3_3 A p hA hp k hk x a ha hopt b hb
  change |FK L p - FK L q| ≤ 4 * Δ at comparison
  change FK L q - 4 * Δ - recoveryError L x a b ≤ bilinear L b (p - b) at recovery
  change FK L p - 10 * Δ ≤ bilinear L b (p - b)
  have comparison' := (le_abs_self _).trans comparison
  linarith

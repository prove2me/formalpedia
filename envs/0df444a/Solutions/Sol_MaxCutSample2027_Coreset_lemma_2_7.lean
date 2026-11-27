-- Prove2me | solution 1 for MaxCutSample2027.Coreset.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:33:59.576154+00:00
-- url     : https://prove2.me/submissions/96afaf5d-4a87-4b3a-aafd-6b00ba924658

import Theorems.Thm_MaxCutSample2027_Coreset_equation_2_6
import Theorems.Thm_MaxCutSample2027_Coreset_lemma_A_1
import Definitions.Def_MaxCutSample2027_Coreset_signed
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

private noncomputable def opt {E : Type*} (T : Set E) (f : E → ℝ) : ℝ := sSup (f '' T)

private theorem opt_spec {E : Type*} [TopologicalSpace E] {T : Set E} (hne : T.Nonempty)
    (hT : IsCompact T) {f : E → ℝ} (hf : Continuous f) :
    (∃ t ∈ T, f t = opt T f) ∧ ∀ t ∈ T, f t ≤ opt T f := by
  have upper (t : E) (ht : t ∈ T) : f t ≤ opt T f :=
    le_csSup (hT.image hf).bddAbove ⟨t, ht, rfl⟩
  obtain ⟨t, ht, hm⟩ := hT.exists_isMaxOn hne hf.continuousOn
  exact ⟨⟨t, ht, le_antisymm (upper t ht) (csSup_le (hne.image _) (by
    rintro _ ⟨z, hz, rfl⟩; exact hm hz))⟩, upper⟩

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
private theorem sample_product {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ) (f : Fin k → V → ℝ) :
    sampleAverage p k (fun x => ∏ i, f i (x i)) = ∏ i, ∑ v, p v * f i v := by
  unfold sampleAverage sampleWeight
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => p v * f i v)).symm

private theorem sample_one {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ} (hp : IsProbabilityVector p)
    (i : Fin k) (f : V → ℝ) : sampleAverage p k (fun x => f (x i)) = ∑ v, p v * f v := by
  let h : Fin k → V → ℝ := Function.update (fun _ _ => 1) i f
  have prod (x : Fin k → V) : (∏ j, h j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i]
    · simp [h]
    · intro j _ hji
      simp [h, hji]
    · simp
  have e := sample_product p h
  simp_rw [prod] at e
  rw [e, Finset.prod_eq_single i]
  · simp [h]
  · intro j _ hji
    simp [h, hji, hp.2]
  · simp

private theorem sample_two {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ} (hp : IsProbabilityVector p)
    (i j : Fin k) (hij : i ≠ j) (f g : V → ℝ) :
    sampleAverage p k (fun x => f (x i) * g (x j)) = (∑ v, p v * f v) * ∑ v, p v * g v := by
  let h : Fin k → V → ℝ := Function.update (Function.update (fun _ _ => 1) i f) j g
  have prod (x : Fin k → V) : (∏ l, h l (x l)) = f (x i) * g (x j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Finset.prod_eq_single i]
    · simp [h, hij]
    · intro l hl hli
      simp [h, hli, (Finset.mem_erase.mp hl).1]
    · simp [hij]
  have e := sample_product p h
  simp_rw [prod] at e
  rw [e, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), Finset.prod_eq_single i]
  · simp [h, hij]
  · intro l hl hli
    simp [h, hli, (Finset.mem_erase.mp hl).1, hp.2]
  · simp [hij]

private theorem sample_const {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (a : ℝ) : sampleAverage p k (fun _ => a) = a := by
  have h := sample_product (k := k) p (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, hp.2] at h
  change (∑ x : Fin k → V, sampleWeight p x * 1) = 1 at h
  simp only [mul_one] at h
  unfold sampleAverage
  rw [← Finset.sum_mul, h, one_mul]

private theorem sample_sum {V I : Type*} [Fintype V] [Fintype I] {k : ℕ} (p : V → ℝ)
    (f : I → (Fin k → V) → ℝ) : sampleAverage p k (fun x => ∑ i, f i x) = ∑ i, sampleAverage p k (f i) := by
  simp only [sampleAverage, Finset.mul_sum]
  exact Finset.sum_comm

private theorem sample_empirical {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (hk : 1 ≤ k) (v : V) : sampleAverage p k (fun x => empirical x v) = p v := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have empirical_indicator (x : Fin k → V) : empirical x v = ((∑ i, if x i = v then 1 else 0) : ℝ) / (k : ℝ) := by
    rw [empirical, Finset.sum_boole]
  have h (i : Fin k) : sampleAverage p k (fun x => if x i = v then 1 else 0) = p v := by
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using
      sample_one hp i (fun u => if u = v then 1 else 0)
  simp only [empirical_indicator, div_eq_inv_mul, sample_smul, sample_sum, h, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hk'.ne']

private theorem sample_add {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (f g : (Fin k → V) → ℝ) : sampleAverage p k (fun x => f x + g x) = sampleAverage p k f + sampleAverage p k g := by
  simp only [sampleAverage, mul_add, Finset.sum_add_distrib]

private theorem sample_sub {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (f g : (Fin k → V) → ℝ) : sampleAverage p k (fun x => f x - g x) = sampleAverage p k f - sampleAverage p k g := by
  simp only [sampleAverage, mul_sub, Finset.sum_sub_distrib]

private theorem sample_abs {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (f : (Fin k → V) → ℝ) :
    |sampleAverage p k f| ≤ sampleAverage p k (fun x => |f x|) := by
  unfold sampleAverage
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro x _
  have h : 0 ≤ sampleWeight p x := Finset.prod_nonneg fun i _ => hp (x i)
  rw [abs_mul, abs_of_nonneg h]

private theorem sample_mean {V : Type*} [Fintype V] {k : ℕ} {p : V → ℝ}
    (hp : IsProbabilityVector p) (hk : 1 ≤ k) (f : V → ℝ) :
    sampleAverage p k (fun x => (∑ i, f (x i)) / (k : ℝ)) = ∑ v, p v * f v := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have h (i : Fin k) : sampleAverage p k (fun x => f (x i)) = ∑ v, p v * f v := sample_one hp i f
  simp only [div_eq_inv_mul, sample_smul, sample_sum, h, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hk'.ne', one_mul]

private theorem sample_pair_permute {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (swap : ((Fin k → V) × (Fin k → V)) ≃ ((Fin k → V) × (Fin k → V)))
    (h : ∀ x y, sampleWeight p (swap (x, y)).1 * sampleWeight p (swap (x, y)).2 =
      sampleWeight p x * sampleWeight p y)
    (f : (Fin k → V) → (Fin k → V) → ℝ) :
    sampleAverage p k (fun x => sampleAverage p k (fun y => f (swap (x, y)).1 (swap (x, y)).2)) =
      sampleAverage p k (fun x => sampleAverage p k (f x)) := by
  unfold sampleAverage
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [← Fintype.sum_prod_type (fun z : (Fin k → V) × (Fin k → V) =>
        (sampleWeight p z.1 * sampleWeight p z.2) * f (swap z).1 (swap z).2),
    ← Fintype.sum_prod_type (fun z : (Fin k → V) × (Fin k → V) => (sampleWeight p z.1 * sampleWeight p z.2) * f z.1 z.2)]
  refine Fintype.sum_equiv swap _ _ ?_
  rintro ⟨x, y⟩
  simp only
  rw [h x y]
private theorem boxB_interval {V : Type*} [DecidableEq V] {k : ℕ} (p : V → ℝ) (x y : Fin k → V) :
    boxB p x y = Set.Icc (-(p + empirical x + empirical y)) (p + empirical x + empirical y) := by
  ext c
  change (∀ v, |c v| ≤ p v + empirical x v + empirical y v) ↔
    (∀ v, -(p v + empirical x v + empirical y v) ≤ c v) ∧ ∀ v, c v ≤ p v + empirical x v + empirical y v
  simp only [abs_le, forall_and]

private theorem boxB_nonempty {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hk : 1 ≤ k) (x y : Fin k → V) : (boxB p x y).Nonempty := by
  refine ⟨0, ?_⟩
  intro v
  simpa using add_nonneg (add_nonneg (hp v) ((empirical_probability hk x).1 v)) ((empirical_probability hk y).1 v)

private theorem comparison_in_boxB {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hk : 1 ≤ k) (x y : Fin k → V) : Ccal p (empirical x) ⊆ boxB p x y := by
  unfold Ccal
  apply convexHull_min _ (by rw [boxB_interval]; exact convex_Icc _ _)
  have hqx := (empirical_probability hk x).1
  have hqy := (empirical_probability hk y).1
  have pside (c : V → ℝ) (hc : c ∈ Z p) : c ∈ boxB p x y := by
    intro v
    rw [abs_of_nonneg (hc v).1]
    linarith [(hc v).2, hqx v, hqy v]
  have xside (c : V → ℝ) (hc : c ∈ Z (empirical x)) : c ∈ boxB p x y := by
    intro v
    rw [abs_of_nonneg (hc v).1]
    linarith [(hc v).2, hp v, hqy v]
  have neg (c : V → ℝ) (hc : c ∈ boxB p x y) : -c ∈ boxB p x y := by
    intro v
    simpa only [Pi.neg_apply, abs_neg] using hc v
  intro c hc
  rcases hc with (((hc | hc) | hc) | hc)
  · exact pside c hc
  · obtain ⟨a, ha, rfl⟩ := hc
    exact neg a (pside a ha)
  · exact xside c hc
  · obtain ⟨a, ha, rfl⟩ := hc
    exact neg a (xside a ha)

private def swapSamples {V : Type*} {k : ℕ} (σ : Fin k → Bool)
    (z : (Fin k → V) × (Fin k → V)) : (Fin k → V) × (Fin k → V) :=
  (fun i => if σ i then z.2 i else z.1 i, fun i => if σ i then z.1 i else z.2 i)

private theorem swapSamples_involutive {V : Type*} {k : ℕ} (σ : Fin k → Bool) :
    Function.Involutive (swapSamples (V := V) σ) := by
  rintro ⟨x, y⟩
  apply Prod.ext <;> funext i <;> cases hi : σ i <;> simp [swapSamples, hi]

private theorem swapSamples_weight {V : Type*} {k : ℕ} (p : V → ℝ) (σ : Fin k → Bool) (x y : Fin k → V) :
    sampleWeight p (swapSamples σ (x, y)).1 * sampleWeight p (swapSamples σ (x, y)).2 =
      sampleWeight p x * sampleWeight p y := by
  unfold sampleWeight
  simp only [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases hi : σ i <;> simp [swapSamples, hi, mul_comm]

private theorem swapSamples_box {V : Type*} [DecidableEq V] {k : ℕ} (p : V → ℝ) (σ : Fin k → Bool)
    (x y : Fin k → V) : boxB p (swapSamples σ (x, y)).1 (swapSamples σ (x, y)).2 = boxB p x y := by
  have empirical_indicator (x : Fin k → V) (v : V) : empirical x v = ((∑ i, if x i = v then 1 else 0) : ℝ) / (k : ℝ) := by
    rw [empirical, Finset.sum_boole]
  have both (v : V) : empirical (swapSamples σ (x, y)).1 v + empirical (swapSamples σ (x, y)).2 v =
      empirical x v + empirical y v := by
    simp only [empirical_indicator, ← add_div, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases hi : σ i <;> simp [swapSamples, hi, add_comm]
  ext c
  change (∀ v, |c v| ≤ p v + empirical (swapSamples σ (x, y)).1 v + empirical (swapSamples σ (x, y)).2 v) ↔
    ∀ v, |c v| ≤ p v + empirical x v + empirical y v
  simp only [add_assoc, both]

private theorem sign_sample_comm {V : Type*} [Fintype V] {k : ℕ} (p : V → ℝ)
    (f : (Fin k → Bool) → (Fin k → V) → ℝ) :
    signAverage k (fun σ => sampleAverage p k (f σ)) =
      sampleAverage p k (fun x => signAverage k (fun σ => f σ x)) := by
  simp only [signAverage, sampleAverage, ← mul_div_assoc, Finset.sum_div, Finset.mul_sum]
  exact Finset.sum_comm
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
private theorem sign_flip_value (b : Bool) : signValue (!b) = -signValue b := by cases b <;> norm_num [signValue]
private theorem abs_sign_value (b : Bool) : |signValue b| = 1 := by cases b <;> norm_num [signValue]

private def flipCoord {k : ℕ} (i : Fin k) (σ : Fin k → Bool) : Fin k → Bool :=
  Function.update σ i (!σ i)

private theorem flipCoord_involutive {k : ℕ} (i : Fin k) : Function.Involutive (flipCoord i) := by
  intro σ
  funext j
  by_cases h : j = i
  · subst j; simp [flipCoord]
  · simp [flipCoord, Function.update_of_ne h]

private theorem sign_card (k : ℕ) : (Fintype.card (Fin k → Bool) : ℝ) = (2 : ℝ) ^ k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow]
  norm_num

private theorem sign_product_sum {k : ℕ} (i j : Fin k) :
    (∑ σ : Fin k → Bool, signValue (σ i) * signValue (σ j)) = if i = j then (2 : ℝ) ^ k else 0 := by
  classical
  by_cases h : i = j
  · subst j
    have value (b : Bool) : signValue b * signValue b = 1 := by cases b <;> norm_num [signValue]
    simp only [ite_true, value, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sign_card]
  · rw [if_neg h]
    let perm : (Fin k → Bool) ≃ (Fin k → Bool) :=
      ⟨flipCoord i, flipCoord i, flipCoord_involutive i, flipCoord_involutive i⟩
    let f (σ : Fin k → Bool) := signValue (σ i) * signValue (σ j)
    have hsum : (∑ σ, f (flipCoord i σ)) = ∑ σ, f σ := Fintype.sum_equiv perm _ _ (fun _ => rfl)
    have neg (σ : Fin k → Bool) : f (flipCoord i σ) = -f σ := by
      simp [f, flipCoord, Function.update_of_ne (Ne.symm h), sign_flip_value]
    simp only [neg, Finset.sum_neg_distrib] at hsum
    change (∑ σ, f σ) = 0
    linarith

private theorem sign_squared {k : ℕ} (a : Fin k → ℝ) :
    (∑ σ : Fin k → Bool, (∑ i, signValue (σ i) * a i) ^ 2) = (2 : ℝ) ^ k * ∑ i, a i ^ 2 := by
  classical
  calc
    _ = ∑ σ : Fin k → Bool, ∑ i, ∑ j,
          (signValue (σ i) * signValue (σ j)) * (a i * a j) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ j, (∑ σ : Fin k → Bool, signValue (σ i) * signValue (σ j)) * (a i * a j) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
      simp only [sign_product_sum, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, pow_two]

private theorem sqrt_average_le {I : Type*} [Fintype I] (w b : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, w i * Real.sqrt (b i)) ≤ Real.sqrt ((∑ i, w i) * ∑ i, w i * b i) := by
  have h : (∑ i, w i * Real.sqrt (b i)) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * b i := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (hb i))
    intro i _
    rw [mul_pow, Real.sq_sqrt (hb i)]
    ring_nf
    exact le_rfl
  have hnonneg : 0 ≤ (∑ i, w i) * ∑ i, w i * b i :=
    mul_nonneg (Finset.sum_nonneg fun i _ => hw i) (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hb i))
  exact (sq_le_sq₀ (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)).mp (by simpa only [Real.sq_sqrt hnonneg] using h)

private theorem sign_absolute {k : ℕ} (a : Fin k → ℝ) :
    signAverage k (fun σ => |∑ i, signValue (σ i) * a i|) ≤ Real.sqrt (∑ i, a i ^ 2) := by
  let c : ℝ := (2 : ℝ) ^ k
  have hc : 0 < c := by dsimp [c]; positivity
  have hb := sqrt_average_le (fun _ : Fin k → Bool => 1 / c)
    (fun σ => (∑ i, signValue (σ i) * a i) ^ 2) (fun _ => by positivity) (fun _ => sq_nonneg _)
  simp only [Real.sqrt_sq_eq_abs, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, sign_card, sign_squared] at hb
  have hden : (2 : ℝ) ^ k * (1 / c) = 1 := mul_div_cancel₀ _ hc.ne'
  have hden' : (1 / c) * (2 : ℝ) ^ k = 1 := by rw [mul_comm]; exact hden
  rw [hden, one_mul, ← mul_assoc (1 / c) ((2 : ℝ) ^ k), hden', one_mul] at hb
  change (∑ σ : Fin k → Bool, |∑ i, signValue (σ i) * a i|) / c ≤ _
  convert hb using 1 <;> first | rfl | ring

private theorem signAverage_sum' {k : ℕ} {I : Type*} [Fintype I] (f : I → (Fin k → Bool) → ℝ) :
    signAverage k (fun σ => ∑ i, f i σ) = ∑ i, signAverage k (f i) := by
  unfold signAverage
  rw [← Finset.sum_div, Finset.sum_comm]

private theorem sign_smul {k : ℕ} (c : ℝ) (f : (Fin k → Bool) → ℝ) :
    signAverage k (fun σ => c * f σ) = c * signAverage k f := by
  unfold signAverage
  rw [← Finset.mul_sum]
  ring

private theorem sign_le {k : ℕ} {f g : (Fin k → Bool) → ℝ} (h : ∀ σ, f σ ≤ g σ) :
    signAverage k f ≤ signAverage k g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun σ _ => h σ) (by positivity)

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x => DeltaK (K A p) p (empirical x)) ≤
      4 * jointAverage p k (signedMaximum (K A p) p) := by
  classical
  let L := K A p
  let S (v : V) (c : V → ℝ) := ∑ u, L v u * c u
  let G (v : V) (c : V → ℝ) := max (S v c) 0
  let mean (x : Fin k → V) (c : V → ℝ) := (∑ i, G (x i) c) / (k : ℝ)
  let U (x y : Fin k → V) := opt (boxB p x y) (fun c => |mean x c - mean y c|)
  let D (x y : Fin k → V) (σ : Fin k → Bool) := opt (boxB p x y)
    (fun c => |(∑ i, signValue (σ i) * (G (x i) c - G (y i) c)) / (k : ℝ)|)
  have hpp : IsProbabilityVector p := ⟨fun v => (hp.1 v).le, hp.2⟩
  have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have boxCompact (x y : Fin k → V) : IsCompact (boxB p x y) := by rw [boxB_interval]; exact isCompact_Icc
  have delta_bound (x : Fin k → V) : DeltaK L p (empirical x) ≤ sampleAverage p k (U x) := by
    unfold DeltaK
    have hne : (Ccal p (empirical x)).Nonempty := (box_nonempty hpp.1).mono (box_subset_comparison_left p _)
    apply csSup_le (hne.image _)
    rintro _ ⟨c, hc, rfl⟩
    change |M L p c - M L (empirical x) c| ≤ _
    have exact_mean : M L p c = sampleAverage p k (fun y => mean y c) := by
      rw [equation_2_6 A p hA hp p c hpp.1]
      exact (sample_mean hpp hk (fun v => G v c)).symm
    have empirical_mean : M L (empirical x) c = mean x c := by
      rw [equation_2_6 A p hA hp (empirical x) c ((empirical_probability hk x).1)]
      exact empirical_sum x (fun v => G v c)
    have fo : |sampleAverage p k (fun y => mean y c - mean x c)| ≤ sampleAverage p k (U x) := by
      refine (sample_abs hpp.1 _).trans (sample_le hpp.1 _ _ ?_)
      intro y
      rw [abs_sub_comm]
      have cont : Continuous (fun c => |mean x c - mean y c|) := by dsimp [mean, G, S]; fun_prop
      exact (opt_spec (boxB_nonempty hpp.1 hk x y) (boxCompact x y) cont).2 c
        (comparison_in_boxB hpp.1 hk x y hc)
    rw [sample_sub, sample_const hpp] at fo
    rwa [exact_mean, empirical_mean]
  have swapped (x y : Fin k → V) (σ : Fin k → Bool) :
      U (swapSamples σ (x, y)).1 (swapSamples σ (x, y)).2 = D x y σ := by
    dsimp only [U, D]
    rw [swapSamples_box]
    congr 1
    funext c
    dsimp [mean]
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    cases hi : σ i <;> simp [swapSamples, hi, signValue] <;> ring
  have double_to_signed : sampleAverage p k (fun x => sampleAverage p k (U x)) = jointAverage p k D := by
    have each (σ : Fin k → Bool) :
        sampleAverage p k (fun x => sampleAverage p k (fun y => D x y σ)) =
          sampleAverage p k (fun x => sampleAverage p k (U x)) := by
      let e : ((Fin k → V) × (Fin k → V)) ≃ ((Fin k → V) × (Fin k → V)) :=
        ⟨swapSamples σ, swapSamples σ, swapSamples_involutive σ, swapSamples_involutive σ⟩
      simp_rw [← swapped]
      exact sample_pair_permute p e (swapSamples_weight p σ) U
    calc
      _ = signAverage k (fun σ => sampleAverage p k (fun x => sampleAverage p k (fun y => D x y σ))) := by
        simp only [signAverage, each, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sign_card]
        field_simp
      _ = _ := by
        rw [sign_sample_comm p (fun σ x => sampleAverage p k (fun y => D x y σ))]
        unfold jointAverage
        apply congrArg (sampleAverage p k)
        funext x
        exact sign_sample_comm p (fun σ y => D x y σ)
  have contraction (x y : Fin k → V) :
      signAverage k (D x y) ≤ 2 * signAverage k (signedMaximum L p x y) +
        2 * signAverage k (signedMaximum L p y x) := by
    let f (x : Fin k → V) (c : V → ℝ) : Fin k → ℝ := fun i => S (x i) c
    let T (x' : Fin k → V) := f x' '' boxB p x y
    have hT (x' : Fin k → V) : IsCompact (T x') := by
      apply (boxCompact x y).image
      dsimp [f, S]
      fun_prop
    have hTne (x' : Fin k → V) : (T x').Nonempty := (boxB_nonempty hpp.1 hk x y).image _
    have lip : LipschitzWith 1 (fun z : ℝ => max z 0) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      have h : |max a 0 - max b 0| ≤ |a - b| := by
        by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
        · simp [max_eq_left ha, max_eq_left hb]
        · rw [max_eq_left ha, max_eq_right (le_of_not_ge hb), sub_zero, abs_of_nonneg ha]
          exact le_trans (by linarith) (le_abs_self _)
        · rw [max_eq_right (le_of_not_ge ha), max_eq_left hb, zero_sub, abs_neg, abs_of_nonneg hb]
          exact le_trans (by linarith) (neg_le_abs _)
        · simp [max_eq_right (le_of_not_ge ha), max_eq_right (le_of_not_ge hb)]
      simpa [Real.dist_eq] using h
    have value (x' : Fin k → V) (σ : Fin k → Bool) (h : ℝ → ℝ) :
        contractionMaximum (T x') h σ = opt (boxB p x y)
          (fun c => |(∑ i, signValue (σ i) * h (S (x' i) c)) / (k : ℝ)|) := by
      unfold contractionMaximum T opt
      rw [Set.image_image]
    have boxSwap : boxB p x y = boxB p y x := by
      ext c
      change (∀ v, |c v| ≤ p v + empirical x v + empirical y v) ↔
        ∀ v, |c v| ≤ p v + empirical y v + empirical x v
      simp only [add_right_comm]
    have linear_x : contractionMaximum (T x) (fun t : ℝ => t) = signedMaximum L p x y := by
      funext σ
      rw [value]
      rfl
    have linear_y : contractionMaximum (T y) (fun t : ℝ => t) = signedMaximum L p y x := by
      funext σ
      rw [value, boxSwap]
      rfl
    have compare (σ : Fin k → Bool) : D x y σ ≤
        contractionMaximum (T x) (fun z => max z 0) σ + contractionMaximum (T y) (fun z => max z 0) σ := by
      unfold D opt
      apply csSup_le ((boxB_nonempty hpp.1 hk x y).image _)
      rintro _ ⟨c, hc, rfl⟩
      change |(∑ i, signValue (σ i) * (G (x i) c - G (y i) c)) / (k : ℝ)| ≤ _
      simp only [mul_sub, Finset.sum_sub_distrib, sub_div]
      rw [value, value]
      have component (x' : Fin k → V) : |(∑ i, signValue (σ i) * G (x' i) c) / (k : ℝ)| ≤
          opt (boxB p x y) (fun c => |(∑ i, signValue (σ i) * G (x' i) c) / (k : ℝ)|) := by
        have cont : Continuous (fun c => |(∑ i, signValue (σ i) * G (x' i) c) / (k : ℝ)|) := by
          dsimp [G, S]; fun_prop
        exact (opt_spec (boxB_nonempty hpp.1 hk x y) (boxCompact x y) cont).2 c hc
      have triangle (a b : ℝ) : |a - b| ≤ |a| + |b| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
      exact (triangle _ _).trans (add_le_add (component x) (component y))
    have bound := sign_le compare
    have average_add {f g : (Fin k → Bool) → ℝ} : signAverage k (fun σ => f σ + g σ) =
        signAverage k f + signAverage k g := by simp only [signAverage, Finset.sum_add_distrib, add_div]
    rw [average_add] at bound
    refine bound.trans (add_le_add ?_ ?_)
    · have hx := lemma_A_1 k hk (T x) (hTne x) (hT x) (fun z => max z 0) lip (by norm_num)
      simpa only [linear_x] using hx
    · have hy := lemma_A_1 k hk (T y) (hTne y) (hT y) (fun z => max z 0) lip (by norm_num)
      simpa only [linear_y] using hy
  have houter := sample_le hpp.1 _ _ delta_bound
  rw [double_to_signed] at houter
  refine houter.trans ?_
  unfold jointAverage
  have outer := sample_le hpp.1 _ _ (fun x => sample_le hpp.1 _ _ (contraction x))
  refine outer.trans_eq ?_
  simp_rw [sample_add, sample_smul]
  let e : ((Fin k → V) × (Fin k → V)) ≃ ((Fin k → V) × (Fin k → V)) := Equiv.prodComm _ _
  have h := sample_pair_permute p e (fun x y => mul_comm (sampleWeight p y) (sampleWeight p x))
    (fun x y => signAverage k (signedMaximum L p x y))
  change sampleAverage p k (fun x => sampleAverage p k (fun y => signAverage k (signedMaximum L p y x))) = _ at h
  rw [h]
  ring

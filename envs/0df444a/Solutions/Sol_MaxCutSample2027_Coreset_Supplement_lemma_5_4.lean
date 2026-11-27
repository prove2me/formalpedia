-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:52:19.581783+00:00
-- url     : https://prove2.me/submissions/62869b1f-9fb6-46a6-96bb-ecd9b00e5b1b

import Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_5_3
import Definitions.Def_MaxCutSample2027_Coreset_Supplement_rFractional
open scoped BigOperators
noncomputable section

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset
open MaxCutSample2027.Coreset.Supplement

private noncomputable def opt {E : Type*} (T : Set E) (f : E → ℝ) : ℝ := sSup (f '' T)

private theorem opt_spec {E : Type*} [TopologicalSpace E] {T : Set E} (hne : T.Nonempty)
    (hT : IsCompact T) {f : E → ℝ} (hf : Continuous f) :
    (∃ t ∈ T, f t = opt T f) ∧ ∀ t ∈ T, f t ≤ opt T f := by
  have upper (t : E) (ht : t ∈ T) : f t ≤ opt T f :=
    le_csSup (hT.image hf).bddAbove ⟨t, ht, rfl⟩
  obtain ⟨t, ht, hm⟩ := hT.exists_isMaxOn hne hf.continuousOn
  exact ⟨⟨t, ht, le_antisymm (upper t ht) (csSup_le (hne.image _) (by
    rintro _ ⟨z, hz, rfl⟩; exact hm hz))⟩, upper⟩

open scoped Pointwise
private theorem hull_union {E : Type*} [AddCommGroup E] [Module ℝ E] (s t : Set E) :
    convexHull ℝ (convexHull ℝ s ∪ convexHull ℝ t) = convexHull ℝ (s ∪ t) := by
  rw [convexHull_convexHull_union_left, convexHull_convexHull_union_right]

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

private def scaledSimplex (r : ℕ) (q : ℝ) : Set (Fin r → ℝ) :=
  {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = q}

private theorem scaledSimplex_convex (r : ℕ) (q : ℝ) : Convex ℝ (scaledSimplex r q) := by
  intro a ha b hb α β hα hβ hab
  refine ⟨fun i => add_nonneg (mul_nonneg hα (ha.1 i)) (mul_nonneg hβ (hb.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ha.2, hb.2, ← add_mul, hab, one_mul]

private theorem scaledSimplex_hull (r : ℕ) [Nonempty (Fin r)] {q : ℝ} (hq : 0 ≤ q) :
    scaledSimplex r q = convexHull ℝ (Set.range fun i : Fin r => Pi.single i q) := by
  classical
  apply subset_antisymm
  · intro a ha
    rcases hq.eq_or_lt with hzero | hpos
    · have ha0 : a = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha.1 i)).1 (ha.2.trans hzero.symm) i (Finset.mem_univ i)
      apply subset_convexHull ℝ _
      refine ⟨Classical.choice inferInstance, ?_⟩
      rw [ha0, ← hzero]
      simp
    · have center : (Finset.univ : Finset (Fin r)).centerMass a (fun i => Pi.single i q) = a := by
        funext i
        simp only [Finset.centerMass, ha.2, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
          Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        field_simp [hpos.ne']
      rw [← center]
      exact Finset.univ.centerMass_mem_convexHull (fun i _ => ha.1 i) (ha.2.symm ▸ hpos)
        (fun i _ => ⟨i, rfl⟩)
  · refine convexHull_min ?_ (scaledSimplex_convex r q)
    rintro _ ⟨i, rfl⟩
    refine ⟨?_, by simp⟩
    intro j
    by_cases h : j = i <;> simp [h, hq]

private def flipMatrix {V : Type*} (r : ℕ) : (V → Fin r → ℝ) →ₗ[ℝ] (Fin r → V → ℝ) where
  toFun a := fun j v => a v j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem Zr_hull {V : Type*} [Fintype V] (r : ℕ) [Nonempty (Fin r)] (q : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) : ∃ U : Set (Fin r → V → ℝ), U.Finite ∧ Zr r q = convexHull ℝ U := by
  let U := Set.univ.pi (fun v : V => Set.range fun i : Fin r => Pi.single i (q v))
  refine ⟨flipMatrix r '' U, (Set.Finite.pi (fun _ => Set.finite_range _)).image _, ?_⟩
  rw [← (flipMatrix r).image_convexHull, convexHull_pi]
  ext a
  constructor
  · intro ha
    refine ⟨fun v j => a j v, ?_, rfl⟩
    intro v _
    change (fun j => a j v) ∈ convexHull ℝ (Set.range fun j : Fin r => Pi.single j (q v))
    rw [← scaledSimplex_hull r (hq v)]
    exact ⟨fun j => ha.1 j v, ha.2 v⟩
  · rintro ⟨b, hb, rfl⟩
    have h (v : V) : b v ∈ scaledSimplex r (q v) := by
      rw [scaledSimplex_hull r (hq v)]
      exact hb v (Set.mem_univ _)
    exact ⟨fun j v => (h v).1 j, fun v => (h v).2⟩

private theorem Zr_nonempty {V : Type*} (r : ℕ) [Nonempty (Fin r)] {q : V → ℝ} (hq : ∀ v, 0 ≤ q v) :
    (Zr r q).Nonempty := by
  classical
  let j : Fin r := Classical.choice inferInstance
  refine ⟨fun i v => if i = j then q v else 0, fun i v => ?_, fun v => ?_⟩
  · change 0 ≤ if i = j then q v else 0
    split_ifs <;> first | exact hq v | exact le_rfl
  · simp

private theorem Zr_compact {V : Type*} [Fintype V] (r : ℕ) [Nonempty (Fin r)] {q : V → ℝ}
    (hq : ∀ v, 0 ≤ q v) : IsCompact (Zr r q) := by
  obtain ⟨U, hU, h⟩ := Zr_hull r q hq
  rw [h]
  exact hU.isCompact_convexHull ℝ
open scoped Pointwise

private theorem Cr_swap {V : Type*} (r : ℕ) (q s : V → ℝ) : Cr r q s = Cr r s q := by
  unfold Cr
  congr 1
  ext c
  simp only [Set.mem_union]
  tauto

private theorem Cr_compact {V : Type*} [Fintype V] (r : ℕ) [Nonempty (Fin r)] {q s : V → ℝ}
    (hq : ∀ v, 0 ≤ q v) (hs : ∀ v, 0 ≤ s v) : IsCompact (Cr r q s) := by
  obtain ⟨A, hA, ea⟩ := Zr_hull r q hq
  obtain ⟨B, hB, eb⟩ := Zr_hull r s hs
  unfold Cr
  simp only [ea, eb, Set.image_neg_eq_neg, ← convexHull_neg]
  rw [← convexHull_convexHull_union_left
    (convexHull ℝ A ∪ convexHull ℝ (-A) ∪ convexHull ℝ B) (convexHull ℝ (-B)),
    ← convexHull_convexHull_union_left (convexHull ℝ A ∪ convexHull ℝ (-A)) (convexHull ℝ B),
    hull_union A (-A), hull_union (A ∪ -A) B, hull_union]
  have negA : (-A).Finite := by rw [← Set.image_neg_eq_neg]; exact hA.image _
  have negB : (-B).Finite := by rw [← Set.image_neg_eq_neg]; exact hB.image _
  exact (((hA.union negA).union hB).union negB).isCompact_convexHull ℝ

private theorem Cr_neg {V : Type*} {r : ℕ} {q s : V → ℝ} {c : Fin r → V → ℝ}
    (hc : c ∈ Cr r q s) : -c ∈ Cr r q s := by
  let U := Zr r q ∪ -Zr r q ∪ Zr r s ∪ -Zr r s
  have hneg : -U = U := by
    ext x
    change -x ∈ U ↔ x ∈ U
    simp only [U, Set.mem_union, Set.mem_neg, neg_neg]
    tauto
  have heq : -(convexHull ℝ U) = convexHull ℝ U := by rw [← convexHull_neg, hneg]
  have hc' : c ∈ convexHull ℝ U := by simpa only [Cr, Set.image_neg_eq_neg, U] using hc
  have hn : -c ∈ convexHull ℝ U := heq ▸ Set.neg_mem_neg.mpr hc'
  simpa only [Cr, Set.image_neg_eq_neg, U] using hn

private theorem part_subset_left {V : Type*} (r : ℕ) (q s : V → ℝ) : Zr r q ⊆ Cr r q s :=
  fun _ ha => subset_convexHull ℝ _ (Or.inl (Or.inl (Or.inl ha)))

private theorem part_subset_right {V : Type*} (r : ℕ) (q s : V → ℝ) : Zr r s ⊆ Cr r q s :=
  fun _ ha => subset_convexHull ℝ _ (Or.inl (Or.inr ha))

private theorem cross_continuous {V E : Type*} [Fintype V] [TopologicalSpace E] {r : ℕ}
    (L : V → V → ℝ) {a c : E → Fin r → V → ℝ} (ha : Continuous a) (hc : Continuous c) :
    Continuous (fun x => crossLinearR L (a x) (c x)) := by
  unfold crossLinearR bilinear
  apply continuous_finset_sum _
  intro i _
  apply continuous_finset_sum _
  intro j _
  by_cases h : i = j <;> simp [h] <;> fun_prop

private noncomputable def linearLeftR {V : Type*} [Fintype V] {r : ℕ}
    (L : V → V → ℝ) (c : Fin r → V → ℝ) : (Fin r → V → ℝ) →ₗ[ℝ] ℝ where
  toFun a := crossLinearR L a c
  map_add' a b := by
    unfold crossLinearR
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · simp [h]
    · simpa only [if_pos h, linearLeft_apply, Pi.add_apply] using (linearLeft L (c j)).map_add (a i) (b i)
  map_smul' t a := by
    unfold crossLinearR
    simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · simp [h]
    · simpa only [if_pos h, smul_eq_mul, linearLeft_apply, Pi.smul_apply] using
        (linearLeft L (c j)).map_smul t (a i)

private theorem cross_swap {V : Type*} [Fintype V] {r : ℕ} (L : V → V → ℝ) (a c : Fin r → V → ℝ) :
    crossLinearR L a c = crossLinearR (fun i j => L j i) c a := by
  unfold crossLinearR
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i = j
  · simp [h]
  · simp only [if_pos h, if_pos (Ne.symm h), bilinear_swap L (a i) (c j)]

private noncomputable def linearRightR {V : Type*} [Fintype V] {r : ℕ}
    (L : V → V → ℝ) (a : Fin r → V → ℝ) : (Fin r → V → ℝ) →ₗ[ℝ] ℝ :=
  linearLeftR (fun u v => L v u) a

private theorem linearLeftR_apply {V : Type*} [Fintype V] {r : ℕ} (L : V → V → ℝ) (a c : Fin r → V → ℝ) :
    linearLeftR L c a = crossLinearR L a c := rfl

private theorem linearRightR_apply {V : Type*} [Fintype V] {r : ℕ} (L : V → V → ℝ) (a c : Fin r → V → ℝ) :
    linearRightR L a c = crossLinearR L a c := (cross_swap L a c).symm

private theorem Mr_opt {V : Type*} [Fintype V] {r : ℕ} [Nonempty (Fin r)] (L : V → V → ℝ)
    {q : V → ℝ} (hq : ∀ v, 0 ≤ q v) (c : Fin r → V → ℝ) :
    (∃ a ∈ Zr r q, crossLinearR L a c = Mr r L q c) ∧ ∀ a ∈ Zr r q, crossLinearR L a c ≤ Mr r L q c :=
  opt_spec (Zr_nonempty r hq) (Zr_compact r hq) (cross_continuous L continuous_id continuous_const)

private theorem Mr_bounded_on {V : Type*} [Fintype V] {r : ℕ} [Nonempty (Fin r)] (L : V → V → ℝ)
    {q : V → ℝ} (hq : ∀ v, 0 ≤ q v) {C : Set (Fin r → V → ℝ)} (hc : IsCompact C) :
    ∃ B : ℝ, ∀ c ∈ C, |Mr r L q c| ≤ B := by
  have cont : Continuous (fun s : (Fin r → V → ℝ) × (Fin r → V → ℝ) => |crossLinearR L s.1 s.2|) :=
    (cross_continuous L continuous_fst continuous_snd).abs
  obtain ⟨B, hB⟩ := ((Zr_compact r hq).prod hc |>.image cont).bddAbove
  refine ⟨B, fun c hc' => ?_⟩
  obtain ⟨a, ha, he⟩ := (Mr_opt L hq c).1
  rw [← he]
  exact hB ⟨(a, c), ⟨ha, hc'⟩, rfl⟩

private theorem DeltaKr_swap {V : Type*} [Fintype V] (r : ℕ) (L : V → V → ℝ) (q s : V → ℝ) :
    DeltaKr r L q s = DeltaKr r L s q := by
  unfold DeltaKr
  rw [Cr_swap r q s]
  conv_lhs => enter [1, 1, c]; rw [abs_sub_comm]

private theorem multiway_value_le {V : Type*} [Fintype V] {r : ℕ} [Nonempty (Fin r)]
    {L : V → V → ℝ} {q s : V → ℝ} {a b c : Fin r → V → ℝ}
    (hc : c ∈ Cr r q s) (hq : ∀ v, 0 ≤ q v) (hs : ∀ v, 0 ≤ s v) :
    |crossLinearR L (a - b) c| ≤ matchingErrorR L a b (Cr r q s) := by
  have cont := (cross_continuous L (a := fun _ => a - b) (c := id) continuous_const continuous_id).abs
  exact le_csSup ((Cr_compact r hq hs).image cont).bddAbove ⟨c, hc, rfl⟩
private theorem fractional_continuous {V : Type*} [Fintype V] {r : ℕ} (L : V → V → ℝ) :
    Continuous (fun a : Fin r → V → ℝ => fractionalValueR L a) := by
  unfold fractionalValueR bilinear
  apply continuous_finsetSum _
  intro i _
  apply continuous_finsetSum _
  intro j _
  by_cases h : i < j <;> simp only [h, if_true, if_false] <;> fun_prop

private theorem twice_value {V : Type*} [Fintype V] {r : ℕ} (L : V → V → ℝ)
    (symm : ∀ u v, L u v = L v u) (a : Fin r → V → ℝ) :
    2 * fractionalValueR L a = crossLinearR L a a := by
  classical
  have hb (i j : Fin r) : bilinear L (a i) (a j) = bilinear L (a j) (a i) := by
    have h : (fun u v => L v u) = L := funext fun u => funext fun v => symm v u
    rw [bilinear_swap L (a i) (a j), h]
  have split (i j : Fin r) : (if i ≠ j then bilinear L (a i) (a j) else 0) =
      (if i < j then bilinear L (a i) (a j) else 0) + (if j < i then bilinear L (a i) (a j) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, h.ne', not_lt_of_ge h.le]
  unfold crossLinearR fractionalValueR
  simp only [split, Finset.sum_add_distrib]
  have eq : (∑ i, ∑ j, if j < i then bilinear L (a i) (a j) else 0) =
      ∑ i, ∑ j, if i < j then bilinear L (a i) (a j) else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hb j i]
  rw [eq, two_mul]

open scoped BigOperators

private def push_mass {V I : Type*} [DecidableEq V] (x : I → V) (w : I → ℝ)
    (S : Finset I) (v : V) : ℝ := ∑ i ∈ S.filter (fun i => x i = v), w i

private theorem sum_push_mass {V I : Type*} [Fintype V] [DecidableEq V] (x : I → V) (w : I → ℝ)
    (S : Finset I) (f : V → ℝ) :
    ∑ v, push_mass x w S v * f v = ∑ i ∈ S, w i * f (x i) := by
  unfold push_mass
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := x)
    (fun _ _ => Finset.mem_univ _) (fun i => w i * f (x i))]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

private theorem cutValueR_expanded {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}
    (A : V → V → ℝ) (color : V → Fin r) :
    cutValueR A color = (∑ u, ∑ v, if color u ≠ color v then A u v else 0) / 2 := by
  unfold cutValueR Max3CutHard.cutR matrixGraph
  rw [List.map_map]
  change (((Finset.univ : Finset (V × V)).toList.map (fun uv =>
    if color uv.1 ≠ color uv.2 then A uv.1 uv.2 / 2 else 0)).sum) = _
  rw [Finset.sum_map_toList, Fintype.sum_prod_type]
  simp only [Finset.sum_div, ite_div, zero_div]

private theorem maxCutR_expanded {V : Type} [Fintype V] [DecidableEq V] {r : ℕ} [Nonempty (Fin r)]
    (h : r ≠ 0) (A : V → V → ℝ) :
    maxCutR r A = (Finset.univ : Finset (V → Fin r)).sup' Finset.univ_nonempty (cutValueR A) := by
  unfold maxCutR
  rw [dif_neg h]
  rfl

private theorem multiway_scale {V : Type} [Fintype V] [DecidableEq V] {r : ℕ} [Nonempty (Fin r)]
    (hr : r ≠ 0) (A : V → V → ℝ) (c : ℝ) (hc : 0 < c) :
    maxCutR r (fun u v => A u v / c) = maxCutR r A / c := by
  have h (S : V → Fin r) : cutValueR (fun u v => A u v / c) S = cutValueR A S / c := by
    rw [cutValueR_expanded, cutValueR_expanded]
    simp only [Finset.sum_div, ite_div, zero_div]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring
  rw [maxCutR_expanded hr, maxCutR_expanded hr]
  apply le_antisymm
  · apply Finset.sup'_le
    intro S hS
    rw [h]
    exact div_le_div_of_nonneg_right (Finset.le_sup' _ hS) hc.le
  · obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (V → Fin r)).Nonempty)
      (cutValueR A)
    rw [hmax, ← h]
    exact Finset.le_sup' _ hS

private theorem bilateral_mass {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (x : I → V) (w : I → ℝ) (L : V → V → ℝ) (S T : Finset I) :
    bilinear L (push_mass x w S) (push_mass x w T) =
      ∑ i ∈ S, ∑ j ∈ T, w i * L (x i) (x j) * w j := by
  unfold bilinear
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [sum_push_mass]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp_rw [mul_comm (L (x i) _) (push_mass x w T _)]
  rw [sum_push_mass]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem normalized_r_cut {V I : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype I] [DecidableEq I] (A : V → V → ℝ) (p : V → ℝ) (hA : IsWeightMatrix A)
    (hp : IsPositiveProbabilityVector p) (r : ℕ) (hr : 2 ≤ r) (x : I → V) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    FKr r (K A p) (push_mass x w Finset.univ) = maxCutR r (fun i j => w i * K A p (x i) (x j) * w j) := by
  classical
  let _ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  let q := push_mass x w Finset.univ
  let L := K A p
  let G (i j : I) := w i * L (x i) (x j) * w j
  let mass (f : I → Fin r) (j : Fin r) := push_mass x w (Finset.univ.filter (fun i => f i = j))
  have hq (v : V) : 0 ≤ q v := Finset.sum_nonneg fun i _ => hw i
  have symm (u v : V) : L u v = L v u := by
    dsimp [L, K]
    rw [hA.1 u v]
    congr 1
    ring
  have feasible (f : I → Fin r) : mass f ∈ Zr r q := by
    refine ⟨fun j v => Finset.sum_nonneg fun i _ => hw i, ?_⟩
    intro v
    dsimp only [mass, q, push_mass]
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := f) (fun _ _ => Finset.mem_univ _) w]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have cross (f : I → Fin r) : crossLinearR L (mass f) (mass f) =
      ∑ i, ∑ j, if f i ≠ f j then G i j else 0 := by
    let S (j : Fin r) := Finset.univ.filter (fun i => f i = j)
    have h₂ (i : I) : (∑ l, ∑ j ∈ S l, if f i ≠ l then G i j else 0) =
        ∑ j, if f i ≠ f j then G i j else 0 := by
      rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := f) (fun _ _ => Finset.mem_univ _)
        (fun j => if f i ≠ f j then G i j else 0)]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
    calc
      _ = ∑ j, ∑ i ∈ S j, ∑ l, ∑ u ∈ S l, if j ≠ l then G i u else 0 := by
        unfold crossLinearR
        apply Finset.sum_congr rfl
        intro j _
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        by_cases h : j = l
        · subst l; simp
        · simp only [if_pos h]
          exact bilateral_mass x w L (S j) (S l)
      _ = ∑ i, ∑ l, ∑ u ∈ S l, if f i ≠ l then G i u else 0 := by
        rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := f) (fun _ _ => Finset.mem_univ _)
          (fun i => ∑ l, ∑ u ∈ S l, if f i ≠ l then G i u else 0)]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
      _ = _ := Finset.sum_congr rfl fun i _ => h₂ i
  have value (f : I → Fin r) : fractionalValueR L (mass f) = cutValueR G f := by
    rw [cutValueR_expanded, ← cross, ← twice_value L symm]
    ring
  obtain ⟨a, ha, optimal, corners⟩ := lemma_5_3 A p hA hp r hr q hq
  have maxima := (opt_spec (Zr_nonempty r hq) (Zr_compact r hq) (fractional_continuous (r := r) L)).2
  have color_exists (v : V) : ∃ j : Fin r, a j v = q v := by
    by_contra! h
    have hzero (j : Fin r) : a j v = 0 := (corners j v).resolve_right (h j)
    have hqzero : q v = 0 := by rw [← ha.2 v]; simp [hzero]
    exact h (Classical.choice inferInstance) (by simp [hzero, hqzero])
  choose color hcolor using color_exists
  have hzero (v : V) (j : Fin r) (hj : j ≠ color v) : a j v = 0 := by
    have h := ha.2 v
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (color v)), hcolor v] at h
    have hh : (∑ i ∈ Finset.univ.erase (color v), a i v) = 0 := by linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha.1 i v)).1 hh j
      (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)
  have realize : mass (color ∘ x) = a := by
    funext j v
    by_cases h : color v = j
    · have hh : (Finset.univ.filter (fun i => (color ∘ x) i = j)).filter (fun i => x i = v) =
          Finset.univ.filter (fun i => x i = v) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
        constructor
        · exact And.right
        · intro hi
          exact ⟨by rwa [hi], hi⟩
      dsimp only [mass, push_mass]
      rw [hh, ← h]
      exact (hcolor v).symm
    · have hh : (Finset.univ.filter (fun i => (color ∘ x) i = j)).filter (fun i => x i = v) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, Function.comp_apply]
        rintro ⟨hi, hi'⟩
        exact h (hi' ▸ hi)
      dsimp only [mass, push_mass]
      rw [hh, Finset.sum_empty, hzero v j (Ne.symm h)]
  change FKr r L q = maxCutR r G
  rw [maxCutR_expanded (by omega) G]
  apply le_antisymm
  · rw [← optimal, ← realize, value]
    exact Finset.le_sup' _ (Finset.mem_univ (color ∘ x))
  · apply Finset.sup'_le
    intro f _
    rw [← value]
    exact maxima (mass f) (feasible f)

theorem solution {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k)
    (r : ℕ) (hr : 2 ≤ r)
    (x : Fin k → V) :
    FKr r (K A p) p = maxCutR r A / (Fintype.card V : ℝ) ^ 2 ∧
    FKr r (K A p) (empirical x) = maxCutR r (Ahat A p x) / (Fintype.card V : ℝ) ^ 2 := by
  let _ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  let N : ℝ := Fintype.card V
  have hN : 0 < N := by
    change (0 : ℝ) < (Fintype.card V : ℝ)
    exact_mod_cast Fintype.card_pos (α := V)
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hzero : r ≠ 0 := by omega
  have unweighted : push_mass (id : V → V) p Finset.univ = p := by
    funext v
    have hfilter : Finset.univ.filter (fun i : V => id i = v) = {v} := by ext i; simp
    rw [push_mass, hfilter, Finset.sum_singleton]
  have empirical_mass : push_mass x (fun _ => 1 / (k : ℝ)) Finset.univ = empirical x := by
    funext v
    simp only [push_mass, empirical, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  constructor
  · have hpush := normalized_r_cut A p hA hp r hr id p (fun v => (hp.1 v).le)
    rw [unweighted] at hpush
    rw [hpush]
    have scaled : (fun u v => p u * K A p (id u) (id v) * p v) = fun u v => A u v / N ^ 2 := by
      funext u v
      change p u * (A u v / (N ^ 2 * p u * p v)) * p v = _
      field_simp [hN.ne', (hp.1 u).ne', (hp.1 v).ne']
    rw [scaled, multiway_scale hzero A (N ^ 2) (by positivity)]
  · rw [← empirical_mass, normalized_r_cut A p hA hp r hr x (fun _ => 1 / (k : ℝ)) (fun _ => by positivity)]
    have scaled : (fun i j => (1 / (k : ℝ)) * K A p (x i) (x j) * (1 / (k : ℝ))) =
        fun i j => Ahat A p x i j / N ^ 2 := by
      funext i j
      change (1 / (k : ℝ)) * (A (x i) (x j) / (N ^ 2 * p (x i) * p (x j))) * (1 / (k : ℝ)) =
        A (x i) (x j) / ((k : ℝ) ^ 2 * p (x i) * p (x j)) / N ^ 2
      field_simp [hN.ne', hkreal.ne', (hp.1 (x i)).ne', (hp.1 (x j)).ne']
    rw [scaled, multiway_scale hzero (Ahat A p x) (N ^ 2) (by positivity)]

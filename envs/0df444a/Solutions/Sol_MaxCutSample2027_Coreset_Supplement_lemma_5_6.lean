-- Prove2me | solution 1 for MaxCutSample2027.Coreset.Supplement.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:46:56.296332+00:00
-- url     : https://prove2.me/submissions/ab08a965-5070-4c68-9829-b0bcbf211b85

import Mathlib.Topology.Sion
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

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (r : ℕ) (hr : 2 ≤ r)
    (q s : V → ℝ) (hq : IsProbabilityVector q) (hs : IsProbabilityVector s)
    : (∀ a ∈ Zr r q, ∃ b ∈ Zr r s,
        matchingErrorR (K A p) a b (Cr r q s) ≤ DeltaKr r (K A p) q s) ∧
      (∀ b ∈ Zr r s, ∃ a ∈ Zr r q,
        matchingErrorR (K A p) a b (Cr r q s) ≤ DeltaKr r (K A p) q s) := by
  let _ : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  let L := K A p
  have one_way (q s : V → ℝ) (hq : IsProbabilityVector q) (hs : IsProbabilityVector s) :
      ∀ a ∈ Zr r q, ∃ b ∈ Zr r s, matchingErrorR L a b (Cr r q s) ≤ DeltaKr r L q s := by
    intro a ha
    let C := Cr r q s
    have hC : IsCompact C := Cr_compact r hq.1 hs.1
    have hne : C.Nonempty := (Zr_nonempty r hq.1).mono (part_subset_left r q s)
    have hconv : Convex ℝ C := convex_convexHull _ _
    have hconvS : Convex ℝ (Zr r s) := by
      obtain ⟨U, _, hU⟩ := Zr_hull r s hs.1
      rw [hU]
      exact convex_convexHull _ _
    have bound (c : Fin r → V → ℝ) (hc : c ∈ C) : |Mr r L q c - Mr r L s c| ≤ DeltaKr r L q s := by
      obtain ⟨Bq, hBq⟩ := Mr_bounded_on L hq.1 hC
      obtain ⟨Bs, hBs⟩ := Mr_bounded_on L hs.1 hC
      have bdd : BddAbove ((fun c => |Mr r L q c - Mr r L s c|) '' C) := by
        refine ⟨Bq + Bs, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        have h := abs_add_le (Mr r L q x) (-Mr r L s x)
        exact (by simpa only [sub_eq_add_neg, abs_neg] using h :
          |Mr r L q x - Mr r L s x| ≤ |Mr r L q x| + |Mr r L s x|).trans
            (add_le_add (hBq x hx) (hBs x hx))
      exact le_csSup bdd ⟨c, hc, rfl⟩
    let f (b c : Fin r → V → ℝ) := crossLinearR L (a - b) c
    have fb (c) : (fun b => f b c) = fun b => linearLeftR L c a - linearLeftR L c b := by
      funext b
      rw [← map_sub, linearLeftR_apply]
    have fc (b) : (fun c => f b c) = linearRightR L (a - b) := by
      funext c
      rw [linearRightR_apply]
    have contB (c) : Continuous (fun b => f b c) := cross_continuous L (continuous_const.sub continuous_id) continuous_const
    have contC (b) : Continuous (fun c => f b c) := cross_continuous L continuous_const continuous_id
    obtain ⟨b, hb, c₀, hc₀, saddle⟩ := Sion.exists_isSaddlePointOn (f := f)
      (Zr_nonempty r hs.1) hconvS (Zr_compact r hs.1)
      (fun c _ => (contB c).continuousOn.lowerSemicontinuousOn)
      (fun c _ => by rw [fb]; exact ((convexOn_const _ hconvS).sub ((linearLeftR L c).concaveOn hconvS)).quasiconvexOn)
      hconv hne hC (fun b _ => (contC b).continuousOn.upperSemicontinuousOn)
      (fun b _ => by rw [fc]; exact ((linearRightR L (a - b)).concaveOn hconv).quasiconcaveOn)
    obtain ⟨z, hz, hzmax⟩ := (Mr_opt L hs.1 c₀).1
    have hupper : f z c₀ ≤ DeltaKr r L q s := by
      have hbound := (Mr_opt L hq.1 c₀).2 a ha
      change crossLinearR L (a - z) c₀ ≤ _
      rw [← linearLeftR_apply, map_sub, linearLeftR_apply, linearLeftR_apply, hzmax]
      exact (sub_le_sub_right hbound _).trans ((le_abs_self _).trans (bound c₀ hc₀))
    refine ⟨b, hb, csSup_le (hne.image _) ?_⟩
    rintro _ ⟨c, hc, rfl⟩
    apply abs_le.mpr
    have h₁ := (saddle z hz c hc).trans hupper
    have h₂ := (saddle z hz (-c) (Cr_neg hc)).trans hupper
    change crossLinearR L (a - b) c ≤ _ at h₁
    change crossLinearR L (a - b) (-c) ≤ _ at h₂
    rw [← linearRightR_apply, map_neg, linearRightR_apply] at h₂
    exact ⟨neg_le.mp h₂, h₁⟩
  refine ⟨one_way q s hq hs, ?_⟩
  intro b hb
  obtain ⟨a, ha, hmatch⟩ := one_way s q hs hq b hb
  refine ⟨a, ha, ?_⟩
  rw [DeltaKr_swap r L s q, Cr_swap r s q] at hmatch
  have h : matchingErrorR L a b (Cr r q s) = matchingErrorR L b a (Cr r q s) := by
    have heq : (fun c => |crossLinearR L (a - b) c|) = fun c => |crossLinearR L (b - a) c| := by
      funext c
      rw [show a - b = -(b - a) by abel, ← linearLeftR_apply, map_neg, linearLeftR_apply, abs_neg]
    unfold matchingErrorR
    rw [heq]
  rwa [h]

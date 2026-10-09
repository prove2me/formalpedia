-- Prove2me | solution 1 for MaxPressure.ReversedLeontief.reversed_leontief_separable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:13:42.854374+00:00
-- url     : https://prove2.me/submissions/5e3ad141-901d-4cff-9fc2-a06a7915a884

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

set_option autoImplicit false

namespace RLSep712
open MaxPressure.ReversedLeontief

lemma A_other {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    (hRL : IsReversedLeontief N) {k k' : Fin K} {j : Fin J} (hk : N.A k j = 1) (hne : k' ≠ k) :
    N.A k' j = 0 := by
  rcases h01 k' j with h | h
  · exact h
  · obtain ⟨k0, _, hu⟩ := hRL j
    exact absurd ((hu k' h).trans (hu k hk).symm) hne

lemma colsum {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    (hRL : IsReversedLeontief N) (j : Fin J) : ∑ k, N.A k j = 1 := by
  obtain ⟨k, hk, -⟩ := hRL j
  rw [Finset.sum_eq_single k (fun k' _ hne => A_other N h01 hRL hk hne) (by simp)]
  exact hk

lemma tnn {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    {a : Fin J → ℝ} (ha0 : ∀ j, 0 ≤ a j) (k : Fin K) (j : Fin J) : 0 ≤ N.A k j * a j := by
  rcases h01 k j with h | h <;> simp [h, ha0 j]

lemma coord_le_one {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    (hRL : IsReversedLeontief N) {a : Fin J → ℝ} (ha : a ∈ allocSet N) (j : Fin J) : a j ≤ 1 := by
  obtain ⟨k, hk, -⟩ := hRL j
  have h1 : N.A k j * a j ≤ ∑ i, N.A k i * a i :=
    Finset.single_le_sum (f := fun i => N.A k i * a i) (fun i _ => tnn N h01 ha.1 k i)
      (Finset.mem_univ j)
  rw [hk, one_mul] at h1
  exact h1.trans (ha.2.1 k)

lemma ext_perturb {J : ℕ} {S : Set (Fin J → ℝ)} {a d : Fin J → ℝ}
    (ha : a ∈ Set.extremePoints ℝ S)
    (hp : (fun i => a i + d i) ∈ S) (hm : (fun i => a i + -d i) ∈ S) (i : Fin J) : d i = 0 := by
  rw [mem_extremePoints] at ha
  have hseg : a ∈ openSegment ℝ (fun i => a i + d i) (fun i => a i + -d i) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 := congrFun (ha.2 _ hp _ hm hseg).1 i
  linarith

lemma shift_mem {I J K : ℕ} (N : Network I J K) {x e : Fin J → ℝ} (hx : x ∈ allocSet N)
    (hnn : ∀ i, 0 ≤ x i + e i)
    (hle : ∀ k, ∑ i, N.A k i * x i + ∑ i, N.A k i * e i ≤ 1)
    (heq : ∀ k, N.inputProc k → ∑ i, N.A k i * e i = 0) :
    (fun i => x i + e i) ∈ allocSet N := by
  have key : ∀ k, ∑ i, N.A k i * (x i + e i) = ∑ i, N.A k i * x i + ∑ i, N.A k i * e i := by
    intro k; simp only [mul_add, Finset.sum_add_distrib]
  refine ⟨hnn, fun k => ?_, fun k hk => ?_⟩
  · rw [key]; exact hle k
  · rw [key, heq k hk, add_zero]; exact hx.2.2 k hk

lemma ext_zo {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    (hRL : IsReversedLeontief N) {a : Fin J → ℝ} (ha : a ∈ extremeAllocs N) (j : Fin J) :
    a j = 0 ∨ a j = 1 := by
  have haS : a ∈ allocSet N := extremePoints_subset ha
  have h0 := haS.1 j
  have h1 := coord_le_one N h01 hRL haS j
  by_contra hne
  push_neg at hne
  have hpos : 0 < a j := lt_of_le_of_ne h0 (Ne.symm hne.1)
  have hlt : a j < 1 := lt_of_le_of_ne h1 hne.2
  obtain ⟨k, hk, -⟩ := hRL j
  by_cases hB : ∃ j', j' ≠ j ∧ N.A k j' = 1 ∧ 0 < a j'
  · obtain ⟨j', hj'ne, hkj', hpos'⟩ := hB
    obtain ⟨t, htpos, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ a j ∧ t ≤ a j' :=
      ⟨min (a j) (a j'), lt_min hpos hpos', min_le_left _ _, min_le_right _ _⟩
    obtain ⟨d, hd⟩ : ∃ d : Fin J → ℝ,
        ∀ i, d i = (if i = j then t else 0) - (if i = j' then t else 0) :=
      ⟨_, fun i => rfl⟩
    have hsum : ∀ k', ∑ i, N.A k' i * d i = 0 := by
      intro k'
      simp only [hd, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      by_cases hkk : k' = k
      · subst hkk; simp [hk, hkj']
      · simp [A_other N h01 hRL hk hkk, A_other N h01 hRL hkj' hkk]
    have hnn : ∀ i, 0 ≤ a i + d i ∧ 0 ≤ a i + -d i := by
      intro i
      have hai := haS.1 i
      rw [hd]
      split_ifs with c1 c2 c2
      · exact absurd (c2.symm.trans c1) hj'ne
      · rw [c1]; constructor <;> linarith
      · rw [c2]; constructor <;> linarith
      · constructor <;> linarith
    have hP : (fun i => a i + d i) ∈ allocSet N :=
      shift_mem N haS (fun i => (hnn i).1) (fun k' => by rw [hsum, add_zero]; exact haS.2.1 k')
        (fun k' _ => hsum k')
    have hM : (fun i => a i + -d i) ∈ allocSet N :=
      shift_mem N haS (fun i => (hnn i).2)
        (fun k' => by
          simp only [mul_neg, Finset.sum_neg_distrib, hsum, neg_zero, add_zero]
          exact haS.2.1 k')
        (fun k' _ => by simp only [mul_neg, Finset.sum_neg_distrib, hsum, neg_zero])
    have := ext_perturb (S := allocSet N) ha hP hM j
    rw [hd, if_pos rfl, if_neg (Ne.symm hj'ne)] at this
    linarith
  · push_neg at hB
    have hsumk : ∑ i, N.A k i * a i = a j := by
      rw [Finset.sum_eq_single j]
      · rw [hk, one_mul]
      · intro i _ hi
        rcases h01 k i with h | h
        · rw [h, zero_mul]
        · rw [h, one_mul]; linarith [hB i hi h, haS.1 i]
      · simp
    have hnin : ¬ N.inputProc k := fun hin => by
      have := haS.2.2 k hin; rw [hsumk] at this; linarith
    have hk0 : ∀ k', N.inputProc k' → N.A k' j = 0 := fun k' hin =>
      A_other N h01 hRL hk (fun h => hnin (h ▸ hin))
    obtain ⟨t, htpos, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ a j ∧ t ≤ 1 - a j :=
      ⟨min (a j) (1 - a j), lt_min hpos (by linarith), min_le_left _ _, min_le_right _ _⟩
    obtain ⟨d, hd⟩ : ∃ d : Fin J → ℝ, ∀ i, d i = if i = j then t else 0 := ⟨_, fun i => rfl⟩
    have hsum : ∀ k', ∑ i, N.A k' i * d i = N.A k' j * t := by
      intro k'
      simp only [hd, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hnn : ∀ i, 0 ≤ a i + d i ∧ 0 ≤ a i + -d i := by
      intro i
      have hai := haS.1 i
      rw [hd]
      split_ifs with c1
      · rw [c1]; constructor <;> linarith
      · constructor <;> linarith
    have hle : ∀ k', ∑ i, N.A k' i * a i + N.A k' j * t ≤ 1 ∧
        ∑ i, N.A k' i * a i + -(N.A k' j * t) ≤ 1 := by
      intro k'
      by_cases hkk : k' = k
      · subst hkk; rw [hsumk, hk]; constructor <;> linarith
      · rw [A_other N h01 hRL hk hkk, zero_mul, neg_zero, add_zero]
        exact ⟨haS.2.1 k', haS.2.1 k'⟩
    have hP : (fun i => a i + d i) ∈ allocSet N :=
      shift_mem N haS (fun i => (hnn i).1) (fun k' => by rw [hsum]; exact (hle k').1)
        (fun k' hin => by rw [hsum, hk0 k' hin, zero_mul])
    have hM : (fun i => a i + -d i) ∈ allocSet N :=
      shift_mem N haS (fun i => (hnn i).2)
        (fun k' => by simp only [mul_neg, Finset.sum_neg_distrib, hsum]; exact (hle k').2)
        (fun k' hin => by
          simp only [mul_neg, Finset.sum_neg_distrib, hsum, hk0 k' hin, zero_mul, neg_zero])
    have := ext_perturb (S := allocSet N) ha hP hM j
    rw [hd, if_pos rfl] at this
    linarith

lemma zo_ext {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    (hRL : IsReversedLeontief N) {b : Fin J → ℝ} (hb : b ∈ allocSet N)
    (hzo : ∀ j, b j = 0 ∨ b j = 1) : b ∈ extremeAllocs N := by
  rw [extremeAllocs, mem_extremePoints]
  refine ⟨hb, fun x hx y hy hseg => ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hseg
  have hc : ∀ j, α * x j + β * y j = b j := fun j => by
    have := congrFun hcomb j; simpa using this
  have key : ∀ j, x j = b j ∧ y j = b j := by
    intro j
    have hx0 := hx.1 j
    have hy0 := hy.1 j
    have hx1 := coord_le_one N h01 hRL hx j
    have hy1 := coord_le_one N h01 hRL hy j
    have hcj := hc j
    rcases hzo j with h | h <;> rw [h] at hcj ⊢
    · constructor <;> nlinarith [mul_nonneg hα.le hx0, mul_nonneg hβ.le hy0]
    · constructor <;> nlinarith [mul_nonneg hα.le (sub_nonneg.2 hx1),
        mul_nonneg hβ.le (sub_nonneg.2 hy1)]
  exact ⟨funext fun j => (key j).1, funext fun j => (key j).2⟩

lemma block_unique {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    {a : Fin J → ℝ} (ha : a ∈ allocSet N) {k : Fin K} {j j' : Fin J}
    (hj : N.A k j = 1) (haj : a j = 1) (hj' : N.A k j' = 1) (haj' : a j' = 1) : j = j' := by
  by_contra hne
  have hsub : ∑ i ∈ {j, j'}, N.A k i * a i ≤ ∑ i, N.A k i * a i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => tnn N h01 ha.1 k i)
  rw [Finset.sum_pair hne, hj, haj, hj', haj'] at hsub
  linarith [ha.2.1 k]

lemma block_term {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    {a : Fin J → ℝ} (ha : a ∈ allocSet N) (hzo : ∀ j, a j = 0 ∨ a j = 1) (k : Fin K)
    (z : Fin I → ℝ) :
    ∑ j, N.A k j * a j * actPressure N j z = actPressure' N (activityOf N a k) z := by
  unfold activityOf
  split_ifs with h
  · have hs := h.choose_spec
    rw [Finset.sum_eq_single h.choose]
    · simp [actPressure', hs.1, hs.2]
    · intro j _ hne
      rcases h01 k j with h0 | h1
      · simp [h0]
      · rcases hzo j with h2 | h2
        · simp [h2]
        · exact absurd (block_unique N h01 ha h1 h2 hs.1 hs.2) hne
    · simp
  · push_neg at h
    simp only [actPressure']
    apply Finset.sum_eq_zero
    intro j _
    rcases h01 k j with h0 | h1
    · simp [h0]
    · rcases hzo j with h2 | h2
      · simp [h2]
      · exact absurd h2 (h j h1)

lemma act_mem {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    {a : Fin J → ℝ} (ha : a ∈ allocSet N) (hzo : ∀ j, a j = 0 ∨ a j = 1) (k : Fin K) :
    activityOf N a k ∈ procActs N k := by
  unfold activityOf
  split_ifs with h
  · exact Or.inr ⟨_, rfl, h.choose_spec.1⟩
  · refine Or.inl ⟨rfl, fun hin => ?_⟩
    push_neg at h
    have h1 := ha.2.2 k hin
    have hz : ∑ j, N.A k j * a j = 0 := Finset.sum_eq_zero fun j _ => by
      rcases h01 k j with h0 | h0
      · simp [h0]
      · rcases hzo j with h2 | h2
        · simp [h2]
        · exact absurd h2 (h j h0)
    rw [hz] at h1
    norm_num at h1

lemma psum {I J K : ℕ} (N : Network I J K) (a : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N a z = ∑ j, a j * actPressure N j z := by
  simp only [pressure, actPressure, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma pressure_split {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    (hRL : IsReversedLeontief N) {a : Fin J → ℝ} (ha : a ∈ allocSet N)
    (hzo : ∀ j, a j = 0 ∨ a j = 1) (z : Fin I → ℝ) :
    pressure N a z = ∑ k, actPressure' N (activityOf N a k) z := by
  rw [psum, Finset.sum_congr rfl (fun k _ => (block_term N h01 ha hzo k z).symm),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, colsum N h01 hRL j, one_mul]

lemma sum_o {I J K : ℕ} (N : Network I J K) {k : Fin K} {o : Option (Fin J)}
    (ho : o ∈ procActs N k) (f : Fin J → ℝ) :
    ∑ i, N.A k i * (if o = some i then 1 else 0) * f i = Option.elim o 0 f := by
  rcases ho with ⟨rfl, -⟩ | ⟨j1, rfl, hj1⟩
  · simp
  · simp [hj1]

lemma act'_elim {I J K : ℕ} (N : Network I J K) (o : Option (Fin J)) (z : Fin I → ℝ) :
    actPressure' N o z = Option.elim o 0 (fun j => actPressure N j z) := by
  cases o <;> rfl

lemma split_props {I J K : ℕ} (N : Network I J K) (h01 : ∀ k j, N.A k j = 0 ∨ N.A k j = 1)
    (hRL : IsReversedLeontief N) {a : Fin J → ℝ} (ha : a ∈ allocSet N)
    (hzo : ∀ j, a j = 0 ∨ a j = 1) (k : Fin K) (o : Option (Fin J)) (ho : o ∈ procActs N k) :
    splitAlloc N a k o ∈ allocSet N ∧
    (∀ j, splitAlloc N a k o j = 0 ∨ splitAlloc N a k o j = 1) ∧
    ∀ z, pressure N (splitAlloc N a k o) z =
      pressure N a z - actPressure' N (activityOf N a k) z + actPressure' N o z := by
  have hs : ∀ j, splitAlloc N a k o j =
      a j - N.A k j * a j + N.A k j * (if o = some j then 1 else 0) := by
    intro j
    simp only [splitAlloc]
    rcases h01 k j with h | h <;> simp [h]
  have hzo' : ∀ j, splitAlloc N a k o j = 0 ∨ splitAlloc N a k o j = 1 := by
    intro j
    simp only [splitAlloc]
    split_ifs
    · right; rfl
    · left; rfl
    · exact hzo j
  have hblk : ∑ i, N.A k i * splitAlloc N a k o i = Option.elim o 0 (fun _ => (1:ℝ)) := by
    rw [← sum_o N ho (fun _ => (1:ℝ))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases h01 k i with h | h
    · simp [h]
    · rw [hs i, h]; simp
  have hoth : ∀ k', k' ≠ k → ∑ i, N.A k' i * splitAlloc N a k o i = ∑ i, N.A k' i * a i := by
    intro k' hne
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases h01 k' i with h | h
    · simp [h]
    · rw [hs i, A_other N h01 hRL h (Ne.symm hne)]; ring
  refine ⟨⟨fun j => ?_, fun k' => ?_, fun k' hin => ?_⟩, hzo', fun z => ?_⟩
  · rcases hzo' j with h | h <;> rw [h] <;> norm_num
  · by_cases hkk : k' = k
    · subst hkk; rw [hblk]; rcases ho with ⟨rfl, -⟩ | ⟨j1, rfl, -⟩ <;> simp
    · rw [hoth k' hkk]; exact ha.2.1 k'
  · by_cases hkk : k' = k
    · subst hkk; rw [hblk]
      rcases ho with ⟨rfl, hni⟩ | ⟨j1, rfl, -⟩
      · exact absurd hin hni
      · simp
    · rw [hoth k' hkk]; exact ha.2.2 k' hin
  · rw [psum, psum, ← block_term N h01 ha hzo k z, act'_elim N o z, ← sum_o N ho,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs j]
    ring

end RLSep712

open MaxPressure.ReversedLeontief in
theorem solution {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (hRL : IsReversedLeontief N) (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i)
    (a : Fin J → ℝ) (ha : a ∈ extremeAllocs N) :
    (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ↔
      ∀ k, ∀ o ∈ procActs N k, actPressure' N o z ≤ actPressure' N (activityOf N a k) z := by
  have h01 := hN.1
  have haS : a ∈ allocSet N := extremePoints_subset ha
  have hzo := RLSep712.ext_zo N h01 hRL ha
  constructor
  · intro h k o ho
    by_contra hlt
    push_neg at hlt
    obtain ⟨hm, hz', hp⟩ := RLSep712.split_props N h01 hRL haS hzo k o ho
    have := h _ (RLSep712.zo_ext N h01 hRL hm hz')
    rw [hp z] at this
    linarith
  · intro h a' ha'
    have ha'S : a' ∈ allocSet N := extremePoints_subset ha'
    have hzo' := RLSep712.ext_zo N h01 hRL ha'
    rw [RLSep712.pressure_split N h01 hRL ha'S hzo' z, RLSep712.pressure_split N h01 hRL haS hzo z]
    exact Finset.sum_le_sum fun k _ => h k _ (RLSep712.act_mem N h01 ha'S hzo' k)

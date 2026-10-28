-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.exists_sparse_near_optimal_lp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:05:15.042423+00:00
-- url     : https://prove2.me/submissions/299267c3-34a6-4cd4-ad64-7d3225e13645

import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared
open KKBinPacking.GeometricGrouping

theorem KKs_sum_superset (x : Multiset ℝ →₀ ℝ) (T : Finset (Multiset ℝ)) (hT : x.support ⊆ T)
    (f : Multiset ℝ → ℝ) : ∑ c ∈ x.support, x c * f c = ∑ c ∈ T, x c * f c := by
  apply Finset.sum_subset hT
  intro c _ hc; rw [Finsupp.notMem_support_iff.mp hc, zero_mul]

theorem KKs_step (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible I x)
    (hcard : numSizes I < x.support.card) :
    ∃ x' : Multiset ℝ →₀ ℝ, IsLPFeasible I x' ∧ lpCost x' ≤ lpCost x ∧
      x'.support.card < x.support.card := by
  classical
  obtain ⟨hconf, hnn, hcov⟩ := hx
  set S := x.support with hS
  let v : S → (I.toFinset → ℝ) := fun c t => ((c : Multiset ℝ).count (t : ℝ) : ℝ)
  have hnli : ¬ LinearIndependent ℝ v := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at this
    simp only [Fintype.card_coe] at this
    unfold numSizes at hcard
    omega
  obtain ⟨g0, hg0, i0, hi0⟩ := Fintype.not_linearIndependent_iff.mp hnli
  obtain ⟨g, hg, i1, hi1, hgs⟩ : ∃ g : S → ℝ, ∑ i, g i • v i = 0 ∧
      ∃ i, g i ≠ 0 ∧ 0 ≤ ∑ i, g i := by
    by_cases h : 0 ≤ ∑ i, g0 i
    · exact ⟨g0, hg0, i0, hi0, h⟩
    · refine ⟨fun i => - g0 i, ?_, i0, neg_ne_zero.mpr hi0, ?_⟩
      · simp only [neg_smul, Finset.sum_neg_distrib, hg0, neg_zero]
      · simp only [Finset.sum_neg_distrib]; linarith
  let G : Multiset ℝ → ℝ := fun c => if h : c ∈ S then g ⟨c, h⟩ else 0
  have hGsum : ∀ f : Multiset ℝ → ℝ, ∑ c ∈ S, G c * f c = ∑ i : S, g i * f i := by
    intro f
    rw [← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl; intro i _; simp [G, i.2]
  have hrel : ∀ t ∈ I.toFinset, ∑ c ∈ S, G c * (c.count t : ℝ) = 0 := by
    intro t ht
    rw [hGsum]
    have := congrFun hg ⟨t, ht⟩
    simpa [Finset.sum_apply, v] using this
  have hGS : 0 ≤ ∑ c ∈ S, G c := by
    have := hGsum (fun _ => 1); simp only [mul_one] at this; rw [this]; exact hgs
  have hposex : ∃ c ∈ S, 0 < G c := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ c ∈ S, -G c = 0 := by
      rw [Finset.sum_neg_distrib]
      have : ∑ c ∈ S, G c ≤ 0 := Finset.sum_nonpos hcon
      linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun c hc => neg_nonneg.mpr (hcon c hc))] at h0
    have := h0 i1 i1.2
    apply hi1
    have : G i1 = g i1 := by simp [G, i1.2]
    linarith
  obtain ⟨c1, hc1S, hc1⟩ := hposex
  set T := S.filter (fun c => 0 < G c) with hT
  have hTne : T.Nonempty := ⟨c1, Finset.mem_filter.mpr ⟨hc1S, hc1⟩⟩
  set θ := T.inf' hTne (fun c => x c / G c) with hθ
  obtain ⟨c0, hc0T, hθc0⟩ := Finset.exists_mem_eq_inf' hTne (fun c => x c / G c)
  rw [← hθ] at hθc0
  have hc0S : c0 ∈ S := (Finset.mem_filter.mp hc0T).1
  have hGc0 : 0 < G c0 := (Finset.mem_filter.mp hc0T).2
  have hθnn : 0 ≤ θ := by rw [hθc0]; exact div_nonneg (hnn c0) hGc0.le
  have hGout : ∀ c, c ∉ S → G c = 0 := by intro c hc; simp [G, hc]
  let x' : Multiset ℝ →₀ ℝ := Finsupp.onFinset S (fun c => x c - θ * G c) (by
    intro c hc
    by_contra hcS
    apply hc
    rw [hGout c hcS, Finsupp.notMem_support_iff.mp hcS]; ring)
  have hx'c : ∀ c, x' c = x c - θ * G c := fun c => Finsupp.onFinset_apply
  have hx'S : x'.support ⊆ S := Finsupp.support_onFinset_subset
  have hx'0 : x' c0 = 0 := by
    rw [hx'c, hθc0]; field_simp; ring
  have hx'E : x'.support ⊆ S.erase c0 := by
    intro c hc
    rw [Finset.mem_erase]
    refine ⟨?_, hx'S hc⟩
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hc) hx'0
  refine ⟨x', ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro c hc; exact hconf c (hx'S hc)
  · intro c
    rw [hx'c]
    by_cases hG : 0 < G c
    · have hcS : c ∈ S := by by_contra h; rw [hGout c h] at hG; exact lt_irrefl _ hG
      have : θ ≤ x c / G c := Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hcS, hG⟩)
      rw [le_div_iff₀ hG] at this
      linarith
    · push_neg at hG
      have := mul_nonpos_of_nonneg_of_nonpos hθnn hG
      linarith [hnn c]
  · intro t ht
    rw [KKs_sum_superset x' S hx'S]
    have := hcov t ht
    simp only [hx'c, sub_mul, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum, hrel t ht, mul_zero, sub_zero]
    exact this
  · unfold lpCost
    have e1 := KKs_sum_superset x' S hx'S (fun _ => 1)
    simp only [mul_one] at e1
    rw [e1]
    simp only [hx'c, Finset.sum_sub_distrib, ← Finset.mul_sum]
    nlinarith [mul_nonneg hθnn hGS]
  · exact lt_of_le_of_lt (Finset.card_le_card hx'E) (Finset.card_erase_lt_of_mem hc0S)

theorem KKs_reduce (I : Multiset ℝ) : ∀ n : ℕ, ∀ x : Multiset ℝ →₀ ℝ, IsLPFeasible I x →
    x.support.card = n → ∃ x' : Multiset ℝ →₀ ℝ, IsLPFeasible I x' ∧
      lpCost x' ≤ lpCost x ∧ x'.support.card ≤ numSizes I := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx hn
    by_cases h : x.support.card ≤ numSizes I
    · exact ⟨x, hx, le_rfl, h⟩
    · obtain ⟨x', hx', hc, hlt⟩ := KKs_step I x hx (by omega)
      obtain ⟨x'', h1, h2, h3⟩ := ih _ (hn ▸ hlt) x' hx' rfl
      exact ⟨x'', h1, h2.trans hc, h3⟩

theorem KKs_nonempty (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ x : Multiset ℝ →₀ ℝ, IsLPFeasible I x := by
  classical
  have key : ∀ c : Multiset ℝ,
      (if Multiset.card c = 1 then (I.count c.sum : ℝ) else 0) ≠ 0 →
        ∃ a ∈ I, c = {a} := by
    intro c hc
    split_ifs at hc with h1
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
      refine ⟨a, ?_, rfl⟩
      simp only [Multiset.sum_singleton, Nat.cast_ne_zero] at hc
      exact Multiset.count_ne_zero.mp hc
    · exact absurd rfl hc
  let x : Multiset ℝ →₀ ℝ := Finsupp.onFinset (I.toFinset.image (fun t => ({t} : Multiset ℝ)))
    (fun c => if Multiset.card c = 1 then (I.count c.sum : ℝ) else 0) (by
      intro c hc
      obtain ⟨a, ha, rfl⟩ := key c hc
      exact Finset.mem_image.mpr ⟨a, Multiset.mem_toFinset.mpr ha, rfl⟩)
  have hxc : ∀ c, x c = if Multiset.card c = 1 then (I.count c.sum : ℝ) else 0 :=
    fun c => Finsupp.onFinset_apply
  refine ⟨x, ?_, ?_, ?_⟩
  · intro c hc
    rw [Finsupp.mem_support_iff, hxc] at hc
    obtain ⟨a, ha, rfl⟩ := key c hc
    refine ⟨by simp, ?_, ?_⟩
    · intro t ht; rw [Multiset.mem_singleton] at ht; rw [ht]; exact ha
    · simp only [Multiset.sum_singleton]; exact (hI a ha).2.le
  · intro c; rw [hxc]; split_ifs <;> positivity
  · intro t ht
    have hmem : ({t} : Multiset ℝ) ∈ x.support := by
      rw [Finsupp.mem_support_iff, hxc]
      simp only [Multiset.card_singleton, Multiset.sum_singleton, if_true, ne_eq,
        Nat.cast_eq_zero]
      exact Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp ht)
    have hle := Finset.single_le_sum (f := fun c => x c * (c.count t : ℝ))
      (fun c _ => mul_nonneg (by rw [hxc]; split_ifs <;> positivity) (by positivity)) hmem
    simp only [hxc, Multiset.card_singleton, Multiset.sum_singleton, if_true,
      Multiset.count_singleton_self, Nat.cast_one, mul_one] at hle
    exact hle

theorem solution
    (I : Multiset ℝ) (hI : IsInstance I) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Multiset ℝ →₀ ℝ,
      IsLPFeasible I x ∧ lpCost x < LIN I + ε ∧
      x.support.card ≤ numSizes I := by
  obtain ⟨x0, hx0⟩ := KKs_nonempty I hI
  have hne : {z : ℝ | ∃ x : Multiset ℝ →₀ ℝ, IsLPFeasible I x ∧ lpCost x = z}.Nonempty :=
    ⟨_, x0, hx0, rfl⟩
  obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := Real.lt_sInf_add_pos hne hε
  obtain ⟨x', h1, h2, h3⟩ := KKs_reduce I _ x hx rfl
  exact ⟨x', h1, lt_of_le_of_lt h2 hz, h3⟩

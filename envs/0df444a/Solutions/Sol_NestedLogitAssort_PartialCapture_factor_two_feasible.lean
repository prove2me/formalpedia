-- Prove2me | solution 1 for NestedLogitAssort.PartialCapture.factor_two_feasible
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T10:01:07.040454+00:00
-- url     : https://prove2.me/submissions/e615d3d4-2948-41f8-aaaf-e7db6e83232c

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Feas3
import Definitions.Def_NestedLogitAssort_PartialCapture_IsOpt4
import Definitions.Def_NestedLogitAssort_PartialCapture_Cand

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NLPCAux

open NestedLogitAssort.PartialCapture

/-- `V ↦ V^γ (P/V - x)` is nonincreasing for `0 ≤ γ ≤ 1`, `P, x ≥ 0`. -/
lemma mono {γ x P V1 V2 : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hx : 0 ≤ x) (hP : 0 ≤ P)
    (hV1 : 0 ≤ V1) (h12 : V1 ≤ V2) (hz : V1 = 0 → P = 0) :
    V2 ^ γ * (P / V2 - x) ≤ V1 ^ γ * (P / V1 - x) := by
  have hpow : V1 ^ γ ≤ V2 ^ γ := Real.rpow_le_rpow hV1 h12 hγ0
  have h1 : V2 ^ γ * (P / V2) ≤ V1 ^ γ * (P / V1) := by
    rcases hV1.eq_or_lt with h0 | hpos
    · have hP0 : P = 0 := hz h0.symm
      simp [hP0]
    · have hV2 : 0 < V2 := lt_of_lt_of_le hpos h12
      have e2 : V2 ^ γ * (P / V2) = P * V2 ^ (γ - 1) := by
        rw [Real.rpow_sub_one hV2.ne']; ring
      have e1 : V1 ^ γ * (P / V1) = P * V1 ^ (γ - 1) := by
        rw [Real.rpow_sub_one hpos.ne']; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hpos h12 (by linarith)) hP
  have h2 : x * V1 ^ γ ≤ x * V2 ^ γ := mul_le_mul_of_nonneg_left hpow hx
  have e : ∀ W : ℝ, W ^ γ * (P / W - x) = W ^ γ * (P / W) - x * W ^ γ := fun W => by ring
  rw [e V2, e V1]
  linarith

/-- Splitting `2x` over two numerators. -/
lemma split {γ x P P1 P2 V : ℝ} (hV : 0 ≤ V) (hP : P ≤ P1 + P2) :
    V ^ γ * (P / V - 2 * x) ≤ V ^ γ * (P1 / V - x) + V ^ γ * (P2 / V - x) := by
  have hd : P / V ≤ (P1 + P2) / V := div_le_div_of_nonneg_right hP hV
  have hpos : 0 ≤ V ^ γ := Real.rpow_nonneg hV γ
  have h := mul_le_mul_of_nonneg_left hd hpos
  rw [add_div] at h
  calc V ^ γ * (P / V - 2 * x) = V ^ γ * (P / V) - 2 * x * V ^ γ := by ring
    _ ≤ V ^ γ * (P1 / V + P2 / V) - 2 * x * V ^ γ := by linarith
    _ = V ^ γ * (P1 / V - x) + V ^ γ * (P2 / V - x) := by ring

variable {M : Type*} {n : ℕ}

/-- Revenue numerator `∑_{j∈S} r_{ij} v_{ij}`. -/
noncomputable def Pn (I : Instance M n) (i : M) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, I.r i j * I.v i j

/-- Weight of the eligible products before `j` (the `pre` of `zhat`). -/
noncomputable def pre (I : Instance M n) (i : M) (ε : ℝ) (j : Fin n) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => k < j ∧ I.v i k ≤ ε), I.v i k

lemma T_eq (I : Instance M n) (i : M) (S : Finset (Fin n)) (x : ℝ) :
    T I i S x = V I i S ^ I.γ i * (Pn I i S / V I i S - x) := rfl

lemma Pn_nonneg (I : Instance M n) (i : M) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (S : Finset (Fin n)) : 0 ≤ Pn I i S :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hv j))

lemma V_nonneg (I : Instance M n) (i : M) (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j)
    (S : Finset (Fin n)) : 0 ≤ V I i S :=
  add_nonneg hw0 (Finset.sum_nonneg (fun j _ => hv j))

lemma Pn_zero (I : Instance M n) (i : M) (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j)
    (S : Finset (Fin n)) (h : V I i S = 0) : Pn I i S = 0 := by
  unfold V at h
  have hs0 : 0 ≤ ∑ j ∈ S, I.v i j := Finset.sum_nonneg (fun j _ => hv j)
  have hs : ∑ j ∈ S, I.v i j = 0 := le_antisymm (by linarith) hs0
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hv j)).1 hs
  unfold Pn
  exact Finset.sum_eq_zero (fun j hj => by rw [hz j hj, mul_zero])

lemma mem_Shat (I : Instance M n) (i : M) (ε : ℝ) (j : Fin n) (hvj : 0 ≤ I.v i j) :
    j ∈ Shat I i ε ↔ I.v i j ≤ ε ∧ (I.v i j = 0 ∨ pre I i ε j + I.v i j ≤ ε) := by
  unfold Shat
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold zhat
  dsimp only
  unfold pre
  by_cases he : I.v i j ≤ ε
  · rw [if_pos he]
    by_cases h0 : I.v i j = 0
    · rw [if_pos h0]
      exact ⟨fun _ => ⟨he, Or.inl h0⟩, fun _ => rfl⟩
    · rw [if_neg h0]
      have hpos : 0 < I.v i j := lt_of_le_of_ne hvj (Ne.symm h0)
      rw [min_eq_left_iff, le_max_iff, le_div_iff₀ hpos]
      constructor
      · rintro (h | h)
        · norm_num at h
        · exact ⟨he, Or.inr (by linarith)⟩
      · rintro ⟨_, h | h⟩
        · exact absurd h h0
        · right
          linarith
  · rw [if_neg he]
    simp [he]

lemma Shat_cand (I : Instance M n) (i : M) (ε : ℝ) (hε : 0 ≤ ε) : Shat I i ε ∈ Cand I i := by
  simp only [Cand, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact Or.inl (Or.inl ⟨ε, hε, rfl⟩)

lemma univ_cand (I : Instance M n) (i : M) : (Finset.univ : Finset (Fin n)) ∈ Cand I i := by
  simp only [Cand, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact Or.inl (Or.inr trivial)

lemma single_cand (I : Instance M n) (i : M) (k : Fin n) : ({k} : Finset (Fin n)) ∈ Cand I i := by
  simp only [Cand, Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact Or.inr ⟨k, rfl⟩

/-- The greedy assortment fits in the capacity. -/
lemma W_Shat_le (I : Instance M n) (i : M) (ε : ℝ) (hv : ∀ j, 0 ≤ I.v i j) (hε : 0 ≤ ε) :
    ∑ j ∈ Shat I i ε, I.v i j ≤ ε := by
  have hsplit : ∑ j ∈ Shat I i ε, I.v i j
      = ∑ j ∈ (Shat I i ε).filter (fun j => 0 < I.v i j), I.v i j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · rfl
    · exact le_antisymm (not_lt.1 h) (hv j)
  rw [hsplit]
  rcases ((Shat I i ε).filter (fun j => 0 < I.v i j)).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact hε
  · obtain ⟨m, hmdef⟩ : ∃ m, m = ((Shat I i ε).filter (fun j => 0 < I.v i j)).max' hne :=
      ⟨_, rfl⟩
    have hm : m ∈ (Shat I i ε).filter (fun j => 0 < I.v i j) := hmdef ▸ Finset.max'_mem _ hne
    have hmA : m ∈ Shat I i ε := (Finset.mem_filter.1 hm).1
    have hmpos : 0 < I.v i m := (Finset.mem_filter.1 hm).2
    have hmem := (mem_Shat I i ε m (hv m)).1 hmA
    have hmle : pre I i ε m + I.v i m ≤ ε := hmem.2.resolve_left hmpos.ne'
    have hsub : (Shat I i ε).filter (fun j => 0 < I.v i j)
        ⊆ insert m (Finset.univ.filter (fun k => k < m ∧ I.v i k ≤ ε)) := by
      intro j hj
      rw [Finset.mem_insert, Finset.mem_filter]
      rcases eq_or_ne j m with h | h
      · exact Or.inl h
      · right
        have hjm : j ≤ m := hmdef ▸ Finset.le_max' _ j hj
        exact ⟨Finset.mem_univ _, lt_of_le_of_ne hjm h,
          ((mem_Shat I i ε j (hv j)).1 (Finset.mem_filter.1 hj).1).1⟩
    have hnot : m ∉ Finset.univ.filter (fun k => k < m ∧ I.v i k ≤ ε) := by
      simp
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hv j)
    rw [Finset.sum_insert hnot] at hle
    have hpre : pre I i ε m = ∑ k ∈ Finset.univ.filter (fun k => k < m ∧ I.v i k ≤ ε), I.v i k :=
      rfl
    linarith

/-- Knapsack exchange: the numerator of `S` is at most that of the greedy `Ŝ(ε)` plus that of one
more candidate of weight at most `ε`, where `ε` is the weight of `S`. -/
lemma knap (I : Instance M n) (i : M) (hv : ∀ j, 0 ≤ I.v i j) (hr : ∀ j, 0 ≤ I.r i j)
    (hanti : Antitone (I.r i)) (S : Finset (Fin n)) (ε : ℝ) (hε : ε = ∑ j ∈ S, I.v i j) :
    ∃ C : Finset (Fin n), C ∈ Cand I i ∧ ∑ j ∈ C, I.v i j ≤ ε ∧
      Pn I i S ≤ Pn I i (Shat I i ε) + Pn I i C := by
  have hε0 : 0 ≤ ε := by rw [hε]; exact Finset.sum_nonneg (fun j _ => hv j)
  have hSel : ∀ j ∈ S, I.v i j ≤ ε := fun j hj => by
    rw [hε]; exact Finset.single_le_sum (fun k _ => hv k) hj
  by_cases hall : ∀ j, I.v i j ≤ ε → j ∈ Shat I i ε
  · refine ⟨Shat I i ε, Shat_cand I i ε hε0, W_Shat_le I i ε hv hε0, ?_⟩
    have hsub : S ⊆ Shat I i ε := fun j hj => hall j (hSel j hj)
    have h1 : Pn I i S ≤ Pn I i (Shat I i ε) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => mul_nonneg (hr j) (hv j))
    have h2 : 0 ≤ Pn I i (Shat I i ε) := Pn_nonneg I i hv hr _
    linarith
  · obtain ⟨j0, hj0e, hj0n⟩ : ∃ j, I.v i j ≤ ε ∧ j ∉ Shat I i ε := by
      by_contra hc
      exact hall (fun j hj => by
        by_contra hn
        exact hc ⟨j, hj, hn⟩)
    have hne : (Finset.univ.filter (fun j => I.v i j ≤ ε ∧ j ∉ Shat I i ε)).Nonempty :=
      ⟨j0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj0e, hj0n⟩⟩
    obtain ⟨k, hkdef⟩ : ∃ k, k = (Finset.univ.filter (fun j => I.v i j ≤ ε ∧ j ∉ Shat I i ε)).min' hne :=
      ⟨_, rfl⟩
    have hkmem : k ∈ Finset.univ.filter (fun j => I.v i j ≤ ε ∧ j ∉ Shat I i ε) :=
      hkdef ▸ Finset.min'_mem _ hne
    have hke : I.v i k ≤ ε := (Finset.mem_filter.1 hkmem).2.1
    have hkn : k ∉ Shat I i ε := (Finset.mem_filter.1 hkmem).2.2
    have hmin : ∀ j, I.v i j ≤ ε → j ∉ Shat I i ε → k ≤ j := fun j h1 h2 =>
      hkdef ▸ Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1, h2⟩)
    have hbelow : ∀ j, I.v i j ≤ ε → j < k → j ∈ Shat I i ε := fun j h1 h2 => by
      by_contra hn
      exact absurd (hmin j h1 hn) (not_le.2 h2)
    have hkpre : ε < pre I i ε k + I.v i k := by
      by_contra hc
      exact hkn ((mem_Shat I i ε k (hv k)).2 ⟨hke, Or.inr (not_lt.1 hc)⟩)
    have habove : ∀ j ∈ Shat I i ε, 0 < I.v i j → j < k := by
      intro j hj hjpos
      have hm := (mem_Shat I i ε j (hv j)).1 hj
      have hjle : pre I i ε j + I.v i j ≤ ε := hm.2.resolve_left hjpos.ne'
      by_contra hc
      have hkj : k < j := lt_of_le_of_ne (not_lt.1 hc) (fun h => hkn (h ▸ hj))
      have hsub : insert k (Finset.univ.filter (fun l => l < k ∧ I.v i l ≤ ε))
          ⊆ Finset.univ.filter (fun l => l < j ∧ I.v i l ≤ ε) := by
        intro l hl
        rw [Finset.mem_insert] at hl
        rw [Finset.mem_filter]
        rcases hl with hl | hl
        · rw [hl]
          exact ⟨Finset.mem_univ _, hkj, hke⟩
        · have h3 := (Finset.mem_filter.1 hl).2
          exact ⟨Finset.mem_univ _, lt_trans h3.1 hkj, h3.2⟩
      have hnot : k ∉ Finset.univ.filter (fun l => l < k ∧ I.v i l ≤ ε) := by
        simp
      have h4 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hv l)
      rw [Finset.sum_insert hnot] at h4
      have hpk : pre I i ε k = ∑ l ∈ Finset.univ.filter (fun l => l < k ∧ I.v i l ≤ ε), I.v i l :=
        rfl
      have hpj : pre I i ε j = ∑ l ∈ Finset.univ.filter (fun l => l < j ∧ I.v i l ≤ ε), I.v i l :=
        rfl
      linarith [hv j]
    have hpreW : pre I i ε k ≤ ∑ j ∈ Shat I i ε, I.v i j := by
      unfold pre
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun l hl => hbelow l (Finset.mem_filter.1 hl).2.2 (Finset.mem_filter.1 hl).2.1)
        (fun l _ _ => hv l)
    have e : ∀ U : Finset (Fin n), ∑ j ∈ U, (I.r i j - I.r i k) * I.v i j
        = Pn I i U - I.r i k * ∑ j ∈ U, I.v i j := fun U => by
      unfold Pn
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hfS : ∑ j ∈ S, (I.r i j - I.r i k) * I.v i j
        ≤ ∑ j ∈ Shat I i ε, (I.r i j - I.r i k) * I.v i j := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun j => j ∈ Shat I i ε)]
      have h1 : ∑ j ∈ S.filter (fun j => j ∉ Shat I i ε), (I.r i j - I.r i k) * I.v i j ≤ 0 := by
        apply Finset.sum_nonpos
        intro j hj
        have hjS := (Finset.mem_filter.1 hj).1
        have hjn := (Finset.mem_filter.1 hj).2
        have hkj : k ≤ j := hmin j (hSel j hjS) hjn
        have hrj : I.r i j ≤ I.r i k := hanti hkj
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hv j)
      have h2 : ∑ j ∈ S.filter (fun j => j ∈ Shat I i ε), (I.r i j - I.r i k) * I.v i j
          ≤ ∑ j ∈ Shat I i ε, (I.r i j - I.r i k) * I.v i j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact (Finset.mem_filter.1 hj).2
        · intro j hjA _
          rcases (hv j).eq_or_lt with h0 | hpos
          · rw [← h0, mul_zero]
          · have hjk : j < k := habove j hjA hpos
            have hrk : I.r i k ≤ I.r i j := hanti hjk.le
            exact mul_nonneg (by linarith) (hv j)
      linarith
    rw [e, e] at hfS
    refine ⟨{k}, single_cand I i k, by rw [Finset.sum_singleton]; exact hke, ?_⟩
    have hPk : Pn I i {k} = I.r i k * I.v i k := by
      unfold Pn
      rw [Finset.sum_singleton]
    rw [hPk]
    have hWS : ∑ j ∈ S, I.v i j = ε := hε.symm
    rw [hWS] at hfS
    have h5 : I.r i k * (ε - ∑ j ∈ Shat I i ε, I.v i j) ≤ I.r i k * I.v i k :=
      mul_le_mul_of_nonneg_left (by linarith) (hr k)
    linarith

/-- Per-nest bound: `T(S, 2x) ≤ T(C₁, x) + T(C₂, x)` for two candidates. -/
lemma per_nest (I : Instance M n) (i : M) (hw0 : 0 ≤ I.w0 i) (hv : ∀ j, 0 ≤ I.v i j)
    (hr : ∀ j, 0 ≤ I.r i j) (hanti : Antitone (I.r i)) (hγ0 : 0 ≤ I.γ i) (hγ1 : I.γ i ≤ 1)
    (x : ℝ) (hx : 0 ≤ x) (S : Finset (Fin n)) :
    ∃ C1 ∈ Cand I i, ∃ C2 ∈ Cand I i, T I i S (2 * x) ≤ T I i C1 x + T I i C2 x := by
  have hε0 : 0 ≤ ∑ j ∈ S, I.v i j := Finset.sum_nonneg (fun j _ => hv j)
  obtain ⟨C, hC, hCW, hP⟩ := knap I i hv hr hanti S (∑ j ∈ S, I.v i j) rfl
  refine ⟨Shat I i (∑ j ∈ S, I.v i j), Shat_cand I i _ hε0, C, hC, ?_⟩
  have hVS : 0 ≤ V I i S := V_nonneg I i hw0 hv S
  rw [T_eq, T_eq, T_eq]
  refine le_trans (split hVS hP) (add_le_add ?_ ?_)
  · have hW := W_Shat_le I i (∑ j ∈ S, I.v i j) hv hε0
    exact mono hγ0 hγ1 hx (Pn_nonneg I i hv hr _) (V_nonneg I i hw0 hv _)
      (by unfold V; linarith) (Pn_zero I i hw0 hv _)
  · exact mono hγ0 hγ1 hx (Pn_nonneg I i hv hr _) (V_nonneg I i hw0 hv _)
      (by unfold V; linarith) (Pn_zero I i hw0 hv _)

theorem main {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (Cand I) x y) :
    Feas3 I (2 * x) (fun i => 2 * y i) := by
  obtain ⟨⟨hsum, hcand⟩, hmin⟩ := hopt
  have hT0 : x < 0 → ∀ i S, 0 ≤ T I i S x := by
    intro hneg i S
    rw [T_eq]
    have hR : 0 ≤ Pn I i S / V I i S :=
      div_nonneg (Pn_nonneg I i (hv i) (hr i) S) (V_nonneg I i (hw0 i) (hv i) S)
    exact mul_nonneg (Real.rpow_nonneg (V_nonneg I i (hw0 i) (hv i) S) _) (by linarith)
  have hx : 0 ≤ x := by
    by_contra hneg
    have hneg : x < 0 := not_le.1 hneg
    have hy0 : ∀ i, 0 ≤ y i := fun i =>
      le_trans (hT0 hneg i Finset.univ) (hcand i _ (univ_cand I i))
    have hs0 : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy0 i)
    have hv0x : I.v0 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv0 hneg.le
    have hsumeq : ∑ i, y i = 0 := by linarith
    have hyz : ∀ i, y i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hy0 i)).1 hsumeq i (Finset.mem_univ _)
    have hv0z : I.v0 = 0 := by
      have : I.v0 * x = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hneg.ne
    have hfeas : Feas4 I (Cand I) (x - 1) y := by
      refine ⟨?_, ?_⟩
      · rw [hsumeq, hv0z, zero_mul]
      · intro i S hS
        have hTS := hcand i S hS
        rw [hyz i] at hTS ⊢
        have hTS0 : T I i S x = 0 := le_antisymm hTS (hT0 hneg i S)
        rw [T_eq] at hTS0 ⊢
        have hR : 0 ≤ Pn I i S / V I i S :=
          div_nonneg (Pn_nonneg I i (hv i) (hr i) S) (V_nonneg I i (hw0 i) (hv i) S)
        have hRx : 0 < Pn I i S / V I i S - x := by linarith
        have hVg : V I i S ^ I.γ i = 0 := (mul_eq_zero.1 hTS0).resolve_right hRx.ne'
        rw [hVg, zero_mul]
    have := hmin _ _ hfeas
    linarith
  refine ⟨?_, ?_⟩
  · show ∑ i, 2 * y i ≤ I.v0 * (2 * x)
    rw [← Finset.mul_sum]
    have e : I.v0 * (2 * x) = 2 * (I.v0 * x) := by ring
    rw [e]
    linarith
  · intro i S
    show T I i S (2 * x) ≤ 2 * y i
    obtain ⟨C1, h1, C2, h2, hle⟩ :=
      per_nest I i (hw0 i) (hv i) (hr i) (hanti i) (hγ0 i) (hγ1 i) x hx S
    have := hcand i C1 h1
    have := hcand i C2 h2
    linarith

end NLPCAux

open NestedLogitAssort.PartialCapture in
theorem solution {M : Type*} [Fintype M] {n : ℕ}
    (I : Instance M n)
    (hv0 : 0 ≤ I.v0) (hw0 : ∀ i, 0 ≤ I.w0 i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hanti : ∀ i, Antitone (I.r i))
    (hγ0 : ∀ i, 0 ≤ I.γ i) (hγ1 : ∀ i, I.γ i ≤ 1)
    (x : ℝ) (y : M → ℝ) (hopt : IsOpt4 I (Cand I) x y) :
    Feas3 I (2 * x) (fun i => 2 * y i) := by
  exact NLPCAux.main I hv0 hw0 hv hr hanti hγ0 hγ1 x y hopt

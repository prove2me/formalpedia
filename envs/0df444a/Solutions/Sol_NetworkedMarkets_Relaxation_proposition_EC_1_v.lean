-- Prove2me | solution 1 for NetworkedMarkets.Relaxation.proposition_EC_1_v
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:58:41.980189+00:00
-- url     : https://prove2.me/submissions/e8b39e44-8db0-4b03-be3b-297c44737807

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NMAuxV
open NetworkedMarkets.Relaxation

variable (D : ValueDist)

lemma F_nonneg (hD : D.Assumption1) (v : ℝ) : 0 ≤ D.F v := (hD.2.1 v).1
lemma F_le_one (hD : D.Assumption1) (v : ℝ) : D.F v ≤ 1 := (hD.2.1 v).2
lemma F_of_nonpos (hD : D.Assumption1) {v : ℝ} (hv : v ≤ 0) : D.F v = 0 := hD.2.2.1 v hv
lemma F_of_ge (hD : D.Assumption1) {v : ℝ} (hv : D.vbar ≤ (v : WithTop ℝ)) : D.F v = 1 :=
  hD.2.2.2.1 v hv

lemma F_pos (hD : D.Assumption1) {v : ℝ} (hv : 0 < v) : 0 < D.F v := by
  by_cases h : D.vbar ≤ (v : WithTop ℝ)
  · rw [F_of_ge D hD h]; norm_num
  · push Not at h
    have hsm := hD.2.2.2.2.2.2.2.1
    have h1 : v / 2 ∈ D.Interior := ⟨by linarith, lt_trans (by exact_mod_cast (by linarith : v/2 < v)) h⟩
    have h2 : v ∈ D.Interior := ⟨hv, h⟩
    have := hsm h1 h2 (by linarith)
    linarith [F_nonneg D hD (v/2)]

lemma F_lt_one_of_top (hD : D.Assumption1) (htop : D.vbar = ⊤) (v : ℝ) : D.F v < 1 := by
  have hsm := hD.2.2.2.2.2.2.2.1
  rcases le_or_gt v 0 with hv | hv
  · rw [F_of_nonpos D hD hv]; norm_num
  · have h1 : v ∈ D.Interior := ⟨hv, by rw [htop]; exact WithTop.coe_lt_top v⟩
    have h2 : v + 1 ∈ D.Interior := ⟨by linarith, by rw [htop]; exact WithTop.coe_lt_top _⟩
    have := hsm h1 h2 (by linarith)
    linarith [F_le_one D hD (v+1)]

lemma Finv_le (w : ℝ) (hw : 0 ≤ w) : D.Finv (D.F w) ≤ w := by
  unfold ValueDist.Finv
  apply csInf_le ⟨0, fun v hv => hv.1⟩
  exact ⟨hw, le_refl _⟩

lemma Finv_nonneg (u : ℝ) : 0 ≤ D.Finv u := by
  unfold ValueDist.Finv
  by_cases hne : ({v : ℝ | 0 ≤ v ∧ u ≤ D.F v}).Nonempty
  · exact le_csInf hne (fun v hv => hv.1)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sInf_empty]

lemma Finv_ge (hD : D.Assumption1) (w : ℝ) (hw : 0 ≤ w) (h1 : D.F w < 1) :
    w ≤ D.Finv (D.F w) := by
  unfold ValueDist.Finv
  refine le_csInf ⟨w, ?_⟩ ?_
  · exact ⟨hw, le_refl _⟩
  rintro v ⟨hv0, hv⟩
  by_contra hlt
  push Not at hlt
  have hwv : (w : WithTop ℝ) < D.vbar := by
    by_contra hc; push Not at hc; rw [F_of_ge D hD hc] at h1; exact lt_irrefl _ h1
  have hw0 : 0 < w := lt_of_le_of_lt hv0 hlt
  have hsm := hD.2.2.2.2.2.2.2.1
  rcases eq_or_lt_of_le hv0 with h0 | h0
  · subst h0
    rw [F_of_nonpos D hD (le_refl _)] at hv
    have := F_pos D hD hw0
    linarith
  · have hvI : v ∈ D.Interior := ⟨h0, lt_trans (by exact_mod_cast hlt) hwv⟩
    have hwI : w ∈ D.Interior := ⟨hw0, hwv⟩
    have := hsm hvI hwI hlt
    linarith

end NMAuxV

namespace NMAuxV
open NetworkedMarkets.Relaxation

lemma Finv_mono (D : ValueDist) {u u' : ℝ} (h : u ≤ u')
    (hne : ({v : ℝ | 0 ≤ v ∧ u' ≤ D.F v}).Nonempty) : D.Finv u ≤ D.Finv u' := by
  unfold ValueDist.Finv
  exact csInf_le_csInf ⟨0, fun v hv => hv.1⟩ hne (fun v hv => ⟨hv.1, le_trans h hv.2⟩)

lemma Finv_set_nonempty (D : ValueDist) (hD : D.Assumption1) (u : ℝ) (hu : u < 1) :
    ({v : ℝ | 0 ≤ v ∧ u ≤ D.F v}).Nonempty := by
  have hT := hD.2.2.2.2.2.2.1
  obtain ⟨v, hv1, hv2⟩ := ((hT.eventually (lt_mem_nhds hu)).and (eventually_ge_atTop 0)).exists
  exact ⟨v, hv2, hv1.le⟩

lemma Finv_set_nonempty' (D : ValueDist) (hD : D.Assumption1) (u : ℝ) (hu1 : u ≤ 1)
    (hu : u < 1 ∨ D.vbar ≠ ⊤) : ({v : ℝ | 0 ≤ v ∧ u ≤ D.F v}).Nonempty := by
  rcases hu with hu | hu
  · exact Finv_set_nonempty D hD u hu
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu
    have hpos := hD.1
    rw [← hr] at hpos
    have hr0 : 0 < r := by exact_mod_cast hpos
    refine ⟨r, hr0.le, ?_⟩
    rw [F_of_ge D hD (by rw [← hr])]; exact hu1

lemma Finv_zero (D : ValueDist) (hD : D.Assumption1) : D.Finv 0 = 0 := by
  apply le_antisymm _ (Finv_nonneg D 0)
  unfold ValueDist.Finv
  exact csInf_le ⟨0, fun v hv => hv.1⟩ ⟨le_rfl, F_nonneg D hD 0⟩

lemma Finv_pos (D : ValueDist) (hD : D.Assumption1) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < D.Finv u := by
  have hcont := hD.2.2.2.2.2.1
  have hF0 : D.F 0 = 0 := F_of_nonpos D hD le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hcont.tendsto 0).eventually (gt_mem_nhds (by rw [hF0]; exact hu0)))
  have : δ / 2 ≤ D.Finv u := by
    unfold ValueDist.Finv
    refine le_csInf (Finv_set_nonempty D hD u hu1) ?_
    rintro v ⟨hv0, hv⟩
    by_contra hlt; push Not at hlt
    have : dist v 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_nonneg hv0]; linarith
    have := hball this
    linarith
  linarith

end NMAuxV

namespace NMAuxV
open NetworkedMarkets.Relaxation
variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma feas_nonneg_qs (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (h : M.Feas7 x qs qb) (i : S) : 0 ≤ qs i := by
  have := h.2.1 i
  have : qs i = ∑ j ∈ M.nbrS i, x i j := by linarith
  rw [this]; exact Finset.sum_nonneg (fun j hj => h.2.2.2.2.1 i j (by simpa [Market.nbrS] using hj))

lemma feas_nonneg_qb (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (h : M.Feas7 x qs qb) (j : B) : 0 ≤ qb j := by
  have := h.1 j
  have : qb j = ∑ i ∈ M.nbrB j, x i j := by linarith
  rw [this]; exact Finset.sum_nonneg (fun i hi => h.2.2.2.2.1 i j (by simpa [Market.nbrB] using hi))

/-- Proposition EC.1(v) at problem (7). -/
lemma qb_lt (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : M.IsOpt7 x qs qb) :
    ∀ j, qb j < M.b j := by
  intro j
  have hF := hopt.1
  by_contra hcon; push Not at hcon
  have hqb : qb j = M.b j := le_antisymm (hF.2.2.1 j) hcon
  have hb := hM.1.2.1 j
  obtain ⟨i, hi, hx⟩ : ∃ i ∈ M.nbrB j, 0 < x i j := by
    by_contra hc; push Not at hc
    have : ∑ i ∈ M.nbrB j, x i j ≤ 0 := Finset.sum_nonpos hc
    linarith [hF.1 j]
  have hiE : (i, j) ∈ M.E := by simpa [Market.nbrB] using hi
  have hjS : j ∈ M.nbrS i := by simp [Market.nbrS, hiE]
  set ε := min (x i j) (M.b j / 2) with hε
  have hε0 : 0 < ε := lt_min hx (by linarith)
  have hεx : ε ≤ x i j := min_le_left _ _
  have hεb : ε ≤ M.b j / 2 := min_le_right _ _
  have hxle : x i j ≤ qs i := by
    have := hF.2.1 i
    have e : qs i = ∑ j ∈ M.nbrS i, x i j := by linarith
    rw [e]
    exact Finset.single_le_sum (fun k hk => hF.2.2.2.2.1 i k (by simpa [Market.nbrS] using hk)) hjS
  set x' : S → B → ℝ := fun i' j' => x i' j' - if i' = i ∧ j' = j then ε else 0
  set qs' : S → ℝ := fun i' => qs i' - if i' = i then ε else 0
  set qb' : B → ℝ := fun j' => qb j' - if j' = j then ε else 0
  have hF' : M.Feas7 x' qs' qb' := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hF
    refine ⟨fun j' => ?_, fun i' => ?_, fun j' => ?_, fun i' => ?_, fun i' j' he => ?_,
      fun i' ht => ?_⟩
    · simp only [x', qb', Finset.sum_sub_distrib]
      by_cases hj' : j' = j
      · subst hj'; simp [Finset.sum_ite_eq', hi]; linarith [a1 j']
      · simp [hj']; linarith [a1 j']
    · simp only [x', qs', Finset.sum_sub_distrib]
      by_cases hi' : i' = i
      · subst hi'; simp [Finset.sum_ite_eq', hjS]; linarith [a2 i']
      · simp [hi']; linarith [a2 i']
    · simp only [qb']; split_ifs <;> linarith [a3 j']
    · simp only [qs']; split_ifs <;> linarith [a4 i']
    · simp only [x']; split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; linarith
      · linarith [a5 i' j' he]
    · simp only [qs']; split_ifs <;> linarith [a6 i' ht]
  have hle := hopt.2 x' qs' qb' hF'
  -- compute the change of h
  have hg : ∑ k, M.gB k (qb' k) - ∑ k, M.gB k (qb k) = M.gB j (qb j - ε) - M.gB j (qb j) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp [qb']
    · intro k _ hk; simp [qb', hk]
    · simp
  have hs : ∑ k, M.hS k (qs' k) - ∑ k, M.hS k (qs k) = M.hS i (qs i - ε) - M.hS i (qs i) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp [qs']
    · intro k _ hk; simp [qs', hk]
    · simp
  have hc : ∑ k, M.c k * qs' k - ∑ k, M.c k * qs k = - (M.c i * ε) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp [qs']; ring
    · intro k _ hk; simp [qs', hk]
    · simp
  have hFb := hM.1.2.2.2.2.2.2 j
  have hFs := hM.1.2.2.2.2.2.1 i
  have hgb : M.gB j (qb j) = 0 := by
    simp only [Market.gB]; rw [hqb, div_self hb.ne', sub_self, Finv_zero _ hFb]; ring
  have hgpos : 0 < M.gB j (qb j - ε) := by
    simp only [Market.gB]
    rw [hqb]
    have e : 1 - (M.b j - ε) / M.b j = ε / M.b j := by field_simp; ring
    rw [e]
    have h1 : 0 < ε / M.b j := div_pos hε0 hb
    have h2 : ε / M.b j < 1 := by rw [div_lt_one hb]; linarith
    exact mul_pos (Finv_pos _ hFb h1 h2) (by linarith)
  have hsle : M.hS i (qs i - ε) ≤ M.hS i (qs i) := by
    simp only [Market.hS]
    have hs0 := hM.1.1 i
    have hq0 : 0 ≤ qs i - ε := by linarith
    have hu1 : qs i / M.s i ≤ 1 := (div_le_one hs0).mpr (hF.2.2.2.1 i)
    have hne := Finv_set_nonempty' _ hFs (qs i / M.s i) hu1 (by
      by_cases ht : (M.Fs i).vbar = ⊤
      · exact Or.inl ((div_lt_one hs0).mpr (hF.2.2.2.2.2 i ht))
      · exact Or.inr ht)
    have hmono : (M.Fs i).Finv ((qs i - ε) / M.s i) ≤ (M.Fs i).Finv (qs i / M.s i) :=
      Finv_mono _ (div_le_div_of_nonneg_right (by linarith) hs0.le) hne
    have hn := Finv_nonneg (M.Fs i) (qs i / M.s i)
    calc (M.Fs i).Finv ((qs i - ε) / M.s i) * (qs i - ε)
        ≤ (M.Fs i).Finv (qs i / M.s i) * (qs i - ε) := mul_le_mul_of_nonneg_right hmono hq0
      _ ≤ (M.Fs i).Finv (qs i / M.s i) * qs i := mul_le_mul_of_nonneg_left (by linarith) hn
  have hc0 := hM.1.2.2.1 i
  simp only [Market.h] at hle
  have : 0 ≤ M.c i * ε := mul_nonneg hc0 hε0.le
  linarith

end NMAuxV

open NetworkedMarkets.Relaxation NMAuxV in
theorem solution {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : M.IsOpt7 x qs qb) :
    ∀ j, qb j < M.b j :=
  qb_lt M hM x qs qb hopt

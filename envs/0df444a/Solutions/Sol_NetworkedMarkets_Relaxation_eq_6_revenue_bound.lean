-- Prove2me | solution 1 for NetworkedMarkets.Relaxation.eq_6_revenue_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:44:24.250963+00:00
-- url     : https://prove2.me/submissions/33e42ec4-bbfa-4e25-a449-9a04bf3d67e3

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NMAux
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

end NMAux

namespace NMAux
open NetworkedMarkets.Relaxation
variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma sumE_S (M : Market S B) (φ : S → B → ℝ) :
    ∑ e ∈ M.E, φ e.1 e.2 = ∑ i, ∑ j ∈ M.nbrS i, φ i j := by
  have : M.E = Finset.univ.filter (fun e => e ∈ M.E) := by ext; simp
  rw [this, Finset.sum_filter, Fintype.sum_prod_type]
  simp [Market.nbrS, Finset.sum_filter]

lemma sumE_B (M : Market S B) (φ : S → B → ℝ) :
    ∑ e ∈ M.E, φ e.1 e.2 = ∑ j, ∑ i ∈ M.nbrB j, φ i j := by
  have : M.E = Finset.univ.filter (fun e => e ∈ M.E) := by ext; simp
  rw [this, Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Market.nbrB, Finset.sum_filter]

lemma conv_S (M : Market S B) (x : S → B → ℝ) (qs : S → ℝ)
    (hs : ∀ i, qs i = ∑ j ∈ M.nbrS i, x i j) (a : S → ℝ) :
    ∑ i, qs i * a i = ∑ e ∈ M.E, x e.1 e.2 * a e.1 := by
  rw [sumE_S M (fun i j => x i j * a i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hs i, Finset.sum_mul]

lemma conv_B (M : Market S B) (x : S → B → ℝ) (qb : B → ℝ)
    (hb : ∀ j, qb j = ∑ i ∈ M.nbrB j, x i j) (a : B → ℝ) :
    ∑ j, qb j * a j = ∑ e ∈ M.E, x e.1 e.2 * a e.2 := by
  rw [sumE_B M (fun i j => x i j * a j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hb j, Finset.sum_mul]

/-- seller bracket -/
noncomputable def Aterm (M : Market S B) (f : Fees S B) (p : S → ℝ) (qs : S → ℝ) (i : S) : ℝ :=
  (1 - f.γs i) * p i - f.μs i - (M.Fs i).Finv (qs i / M.s i)

/-- buyer bracket -/
noncomputable def Bterm (M : Market S B) (f : Fees S B) (p : S → ℝ) (qb : B → ℝ) (i : S) (j : B) : ℝ :=
  (M.Fb j).Finv (1 - qb j / M.b j) - M.cost f p i j - f.μb j

lemma identity (M : Market S B) (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ)
    (qb : B → ℝ) (hs : ∀ i, qs i = ∑ j ∈ M.nbrS i, x i j)
    (hb : ∀ j, qb j = ∑ i ∈ M.nbrB j, x i j) :
    M.h qs qb - M.rev f p x =
      ∑ i, qs i * Aterm M f p qs i + ∑ e ∈ M.E, x e.1 e.2 * Bterm M f p qb e.1 e.2 := by
  have e1 := conv_S M x qs hs (fun i => (1 - f.γs i) * p i - f.μs i)
  have e2 := conv_S M x qs hs (fun i => M.c i)
  have e3 := conv_B M x qb hb (fun j => (M.Fb j).Finv (1 - qb j / M.b j))
  have hA : ∑ i, qs i * Aterm M f p qs i =
      ∑ i, qs i * ((1 - f.γs i) * p i - f.μs i) - ∑ i, M.hS i (qs i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Aterm, Market.hS]; ring
  have hB : ∑ e ∈ M.E, x e.1 e.2 * Bterm M f p qb e.1 e.2 =
      ∑ e ∈ M.E, x e.1 e.2 * (M.Fb e.2).Finv (1 - qb e.2 / M.b e.2)
        - ∑ e ∈ M.E, x e.1 e.2 * ((1 + f.γb e.2) * p e.1 + M.c e.1 + f.μb e.2) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [Bterm, Market.cost]; ring
  have hgB : ∑ j, M.gB j (qb j) = ∑ j, qb j * (M.Fb j).Finv (1 - qb j / M.b j) := by
    refine Finset.sum_congr rfl (fun j _ => ?_); simp only [Market.gB]; ring
  have hc : ∑ i, M.c i * qs i = ∑ i, qs i * M.c i := by
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  have key : ∑ e ∈ M.E, (x e.1 e.2 * ((1 - f.γs e.1) * p e.1 - f.μs e.1)
      - x e.1 e.2 * ((1 + f.γb e.2) * p e.1 + M.c e.1 + f.μb e.2) + x e.1 e.2 * M.c e.1
      + ((f.γs e.1 + f.γb e.2) * p e.1 * x e.1 e.2 + (f.μs e.1 + f.μb e.2) * x e.1 e.2)) = 0 := by
    apply Finset.sum_eq_zero; intro e _; ring
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at key
  rw [hA, hB]
  simp only [Market.h, Market.rev]
  rw [hgB, hc, e1, e2, e3]
  simp only [Finset.sum_add_distrib]
  linarith

end NMAux

open NetworkedMarkets.Relaxation NMAux in
theorem solution {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing1)
    (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (h3 : M.Feas3 f p x qs qb) :
    M.Feas7 x qs qb ∧ M.rev f p x ≤ M.h qs qb := by
  obtain ⟨hs0, hb0, hc0, -, -, hFs, hFb⟩ := hM
  obtain ⟨⟨hγs, hγb, hμs, hμb⟩, hp, h2a, h2b, h2cs, h2cb, h2dx, h2d⟩ := h3
  have hqs0 : ∀ i, 0 ≤ qs i := fun i => by
    rw [h2a i]; exact mul_nonneg (hs0 i).le (F_nonneg _ (hFs i) _)
  refine ⟨⟨fun j => by rw [h2cb j]; ring, fun i => by rw [h2cs i]; ring, ?_, ?_, h2dx, ?_⟩, ?_⟩
  · intro j
    obtain ⟨m, -, hm⟩ := h2b j
    rw [hm]; have := F_nonneg _ (hFb j) (m + f.μb j)
    nlinarith [hb0 j]
  · intro i
    rw [h2a i]; have := F_le_one _ (hFs i) ((1 - f.γs i) * p i - f.μs i)
    nlinarith [hs0 i]
  · intro i htop
    rw [h2a i]; have := F_lt_one_of_top _ (hFs i) htop ((1 - f.γs i) * p i - f.μs i)
    nlinarith [hs0 i]
  · have hid := identity M f p x qs qb h2cs h2cb
    have hA : ∀ i, 0 ≤ qs i * Aterm M f p qs i := by
      intro i
      rcases eq_or_lt_of_le (hqs0 i) with h0 | h0
      · rw [← h0]; simp
      · apply mul_nonneg h0.le
        set v := (1 - f.γs i) * p i - f.μs i with hv
        have hq : qs i / M.s i = (M.Fs i).F v := by
          rw [h2a i, ← hv]; field_simp [(hs0 i).ne']
        have hvpos : 0 < v := by
          by_contra hc; push Not at hc
          have := F_of_nonpos _ (hFs i) hc
          rw [h2a i, ← hv, this] at h0; simp at h0
        simp only [Aterm]; rw [hq, ← hv]
        linarith [Finv_le (M.Fs i) v hvpos.le]
    have hB : ∀ e ∈ M.E, 0 ≤ x e.1 e.2 * Bterm M f p qb e.1 e.2 := by
      rintro ⟨i, j⟩ he
      rcases eq_or_lt_of_le (h2dx i j he) with h0 | h0
      · simp only; rw [← h0]; simp
      · simp only
        apply mul_nonneg h0.le
        obtain ⟨m, ⟨⟨i', hi'E, hi'm⟩, hmle⟩, hm⟩ := h2b j
        have hcost : M.cost f p i j = m := by
          apply le_antisymm _ (hmle ⟨i, he, rfl⟩)
          by_contra hlt; push Not at hlt
          have := h2d i j he ⟨i', hi'E, by rw [← hi'm]; exact hlt⟩
          linarith
        have hqbpos : 0 < qb j := by
          rw [h2cb j]
          have hi : i ∈ M.nbrB j := by simp [Market.nbrB, he]
          calc 0 < x i j := h0
            _ ≤ ∑ i ∈ M.nbrB j, x i j := Finset.single_le_sum
                (fun k hk => h2dx k j (by simpa [Market.nbrB] using hk)) hi
        have hw0 : 0 ≤ m + f.μb j := by
          rw [← hcost]; simp only [Market.cost]
          have := hγb j; have := hp i; have := hc0 i; have := hμb j
          nlinarith
        have hq : 1 - qb j / M.b j = (M.Fb j).F (m + f.μb j) := by
          rw [hm]; field_simp [(hb0 j).ne']; ring
        have hlt1 : (M.Fb j).F (m + f.μb j) < 1 := by
          by_contra hc; push Not at hc
          have h1 := F_le_one _ (hFb j) (m + f.μb j)
          have : (M.Fb j).F (m + f.μb j) = 1 := le_antisymm h1 hc
          rw [hm, this] at hqbpos; simp at hqbpos
        simp only [Bterm]; rw [hq, hcost]
        linarith [Finv_ge (M.Fb j) (hFb j) _ hw0 hlt1]
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hA i)
    have := Finset.sum_nonneg hB
    linarith

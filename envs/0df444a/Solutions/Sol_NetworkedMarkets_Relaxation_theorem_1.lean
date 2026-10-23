-- Prove2me | solution 1 for NetworkedMarkets.Relaxation.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:55:15.176892+00:00
-- url     : https://prove2.me/submissions/2b34bcdc-ebea-436d-8acb-4543047fa160

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting
import Theorems.Thm_NetworkedMarkets_Relaxation_theorem_1_i
import Theorems.Thm_NetworkedMarkets_Relaxation_eq_6_revenue_bound
import Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_iv

open Filter Topology

namespace NMAuxT
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

end NMAuxT

namespace NMAuxT
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

end NMAuxT


namespace NMAuxT
open NetworkedMarkets.Relaxation

lemma Finv_set_closed (D : ValueDist) (hD : D.Assumption1) (u : ℝ) :
    IsClosed {v : ℝ | 0 ≤ v ∧ u ≤ D.F v} :=
  IsClosed.inter (isClosed_le continuous_const continuous_id)
    (isClosed_le continuous_const hD.2.2.2.2.2.1)

lemma Finv_set_nonempty (D : ValueDist) (hD : D.Assumption1) (u : ℝ) (hu : u < 1) :
    ({v : ℝ | 0 ≤ v ∧ u ≤ D.F v}).Nonempty := by
  have hT := hD.2.2.2.2.2.2.1
  obtain ⟨v, hv1, hv2⟩ := ((hT.eventually (lt_mem_nhds hu)).and (eventually_ge_atTop 0)).exists
  exact ⟨v, hv2, hv1.le⟩

lemma F_Finv (D : ValueDist) (hD : D.Assumption1) (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hu : u < 1 ∨ D.vbar ≠ ⊤) : D.F (D.Finv u) = u := by
  have hne : ({v : ℝ | 0 ≤ v ∧ u ≤ D.F v}).Nonempty := by
    rcases hu with hu | hu
    · exact Finv_set_nonempty D hD u hu
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hu
      have hpos := hD.1
      rw [← hr] at hpos
      have hr0 : 0 < r := by exact_mod_cast hpos
      refine ⟨r, hr0.le, ?_⟩
      rw [F_of_ge D hD (by rw [← hr])]; exact hu1
  have hbdd : BddBelow {v : ℝ | 0 ≤ v ∧ u ≤ D.F v} := ⟨0, fun v hv => hv.1⟩
  have hmem := (Finv_set_closed D hD u).csInf_mem hne hbdd
  unfold ValueDist.Finv
  set v := sInf {v : ℝ | 0 ≤ v ∧ u ≤ D.F v} with hvdef
  apply le_antisymm _ hmem.2
  by_contra hc; push Not at hc
  rcases eq_or_lt_of_le hmem.1 with h0 | h0
  · rw [← h0, F_of_nonpos D hD (le_refl _)] at hc; linarith
  · have hcont := hD.2.2.2.2.2.1
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
      ((hcont.tendsto v).eventually (lt_mem_nhds hc))
    set w := v - min ε v / 2 with hw
    have hmin1 : min ε v ≤ ε := min_le_left _ _
    have hmin2 : min ε v ≤ v := min_le_right _ _
    have hmin0 : 0 < min ε v := lt_min hε h0
    have hw0 : 0 ≤ w := by rw [hw]; linarith
    have hwd : dist w v < ε := by
      rw [Real.dist_eq, hw]; rw [abs_lt]; constructor <;> linarith
    have hFw := hball hwd
    have : v ≤ w := csInf_le hbdd ⟨hw0, hFw.le⟩
    rw [hw] at this; linarith

lemma Finv_unbounded (D : ValueDist) (hD : D.Assumption1) (htop : D.vbar = ⊤) (K : ℝ) :
    ∃ u0 < 1, ∀ u, u0 < u → u < 1 → K ≤ D.Finv u := by
  set K' := max K 1
  refine ⟨D.F K', F_lt_one_of_top D hD htop K', fun u hu0 hu1 => ?_⟩
  have hne := Finv_set_nonempty D hD u hu1
  unfold ValueDist.Finv
  refine le_trans (le_max_left K 1) (le_csInf hne ?_)
  rintro v ⟨hv0, hv⟩
  by_contra hlt; push Not at hlt
  have := hD.2.2.2.2.1 hlt.le
  linarith

end NMAuxT

namespace NMAuxT
open NetworkedMarkets.Relaxation
variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma terms_nonneg (M : Market S B) (hM : M.Standing1)
    (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (h3 : M.Feas3 f p x qs qb) :
    (∀ i, 0 ≤ qs i * Aterm M f p qs i) ∧ (∀ e ∈ M.E, 0 ≤ x e.1 e.2 * Bterm M f p qb e.1 e.2) := by
  obtain ⟨hs0, hb0, hc0, -, -, hFs, hFb⟩ := hM
  obtain ⟨⟨hγs, hγb, hμs, hμb⟩, hp, h2a, h2b, h2cs, h2cb, h2dx, h2d⟩ := h3
  have hqs0 : ∀ i, 0 ≤ qs i := fun i => by
    rw [h2a i]; exact mul_nonneg (hs0 i).le (F_nonneg _ (hFs i) _)
  constructor
  · intro i
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
  · rintro ⟨i, j⟩ he
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

lemma gB_eq (M : Market S B) (j : B) (hb : 0 < M.b j) (q : ℝ) :
    M.gB j q = M.b j * ((q / M.b j) * (M.Fb j).Finv (1 - q / M.b j)) := by
  simp only [Market.gB]; field_simp

lemma hS_eq (M : Market S B) (i : S) (hs : 0 < M.s i) (q : ℝ) :
    M.hS i q = M.s i * ((q / M.s i) * (M.Fs i).Finv (q / M.s i)) := by
  simp only [Market.hS]; field_simp

lemma mix_gB (M : Market S B) (hM : M.Standing) (j : B) (a c t : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ M.b j) (hc : 0 ≤ c) (hc' : c ≤ M.b j) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * M.gB j a + t * M.gB j c ≤ M.gB j ((1 - t) * a + t * c) := by
  have hb := hM.1.2.1 j
  have hcc := (hM.2.1 j).concaveOn
  have hu : a / M.b j ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg ha hb.le, (div_le_one hb).mpr ha'⟩
  have hv : c / M.b j ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg hc hb.le, (div_le_one hb).mpr hc'⟩
  have := hcc.2 hu hv (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at this
  rw [gB_eq M j hb a, gB_eq M j hb c, gB_eq M j hb ((1 - t) * a + t * c)]
  have e : ((1 - t) * a + t * c) / M.b j = (1 - t) * (a / M.b j) + t * (c / M.b j) := by ring
  rw [e]
  nlinarith

lemma mix_hS (M : Market S B) (hM : M.Standing) (i : S) (a c t : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ M.s i) (hat : (M.Fs i).vbar = ⊤ → a < M.s i)
    (hc : 0 ≤ c) (hc' : c ≤ M.s i) (hct : (M.Fs i).vbar = ⊤ → c < M.s i)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    M.hS i ((1 - t) * a + t * c) ≤ (1 - t) * M.hS i a + t * M.hS i c := by
  have hs := hM.1.1 i
  have hcc := (hM.2.2 i).concaveOn
  have hu : a / M.s i ∈ (M.Fs i).sellerUnitDom :=
    ⟨div_nonneg ha hs.le, (div_le_one hs).mpr ha', fun ht => (div_lt_one hs).mpr (hat ht)⟩
  have hv : c / M.s i ∈ (M.Fs i).sellerUnitDom :=
    ⟨div_nonneg hc hs.le, (div_le_one hs).mpr hc', fun ht => (div_lt_one hs).mpr (hct ht)⟩
  have := hcc.2 hu hv (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [smul_eq_mul] at this
  rw [hS_eq M i hs a, hS_eq M i hs c, hS_eq M i hs ((1 - t) * a + t * c)]
  have e : ((1 - t) * a + t * c) / M.s i = (1 - t) * (a / M.s i) + t * (c / M.s i) := by ring
  rw [e]
  nlinarith

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

lemma feas_mix (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    {x' : S → B → ℝ} {qs' : S → ℝ} {qb' : B → ℝ}
    (h : M.Feas7 x qs qb) (h' : M.Feas7 x' qs' qb') (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    M.Feas7 (fun i j => (1 - t) * x i j + t * x' i j) (fun i => (1 - t) * qs i + t * qs' i)
      (fun j => (1 - t) * qb j + t * qb' j) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h'
  have ht1' : 0 ≤ 1 - t := by linarith
  refine ⟨fun j => ?_, fun i => ?_, fun j => ?_, fun i => ?_, fun i j he => ?_, fun i ht => ?_⟩
  · simp only; rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := a1 j; have := b1 j
    have e1 : ∑ i ∈ M.nbrB j, x i j = qb j := by linarith
    have e2 : ∑ i ∈ M.nbrB j, x' i j = qb' j := by linarith
    rw [e1, e2]; ring
  · simp only; rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := a2 i; have := b2 i
    have e1 : ∑ j ∈ M.nbrS i, x i j = qs i := by linarith
    have e2 : ∑ j ∈ M.nbrS i, x' i j = qs' i := by linarith
    rw [e1, e2]; ring
  · simp only; nlinarith [a3 j, b3 j]
  · simp only; nlinarith [a4 i, b4 i]
  · simp only; nlinarith [a5 i j he, b5 i j he]
  · simp only
    have := a6 i ht; have := b6 i ht
    rcases eq_or_lt_of_le ht0 with h0 | h0
    · subst h0; simp; exact this.trans_le' le_rfl |>.trans_le' (by linarith) |> fun _ => by linarith
    · nlinarith

/-- At an optimum of (7), a buyer type with unbounded support trades a positive quantity. -/
lemma qb_pos_of_top (M : Market S B) (hM : M.Standing) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (hopt : M.IsOpt7 x qs qb) (j : B) (htop : (M.Fb j).vbar = ⊤) : 0 < qb j := by
  have hF := hopt.1
  rcases eq_or_lt_of_le (feas_nonneg_qb M hF j) with h0 | h0
  swap; · exact h0
  exfalso
  obtain ⟨i, hi⟩ := hM.1.2.2.2.2.1 j
  have hiE : (i, j) ∈ M.E := by simpa [Market.nbrB] using hi
  have hjS : j ∈ M.nbrS i := by simp [Market.nbrS, hiE]
  have hs := hM.1.1 i
  have hb := hM.1.2.1 j
  set δ := min (M.s i) (M.b j) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hs hb)
  have hδs : δ < M.s i := by rw [hδ]; linarith [min_le_left (M.s i) (M.b j), lt_min hs hb]
  have hδb : δ ≤ M.b j := by rw [hδ]; linarith [min_le_right (M.s i) (M.b j), lt_min hs hb]
  set y : S → B → ℝ := fun i' j' => if i' = i ∧ j' = j then δ else 0 with hy
  set ys : S → ℝ := fun i' => if i' = i then δ else 0 with hys
  set yb : B → ℝ := fun j' => if j' = j then δ else 0 with hyb
  have hyF : M.Feas7 y ys yb := by
    refine ⟨fun j' => ?_, fun i' => ?_, fun j' => ?_, fun i' => ?_, fun i' j' _ => ?_, fun i' _ => ?_⟩
    · simp only [hy, hyb]
      by_cases hj' : j' = j
      · subst hj'; simp [Finset.sum_ite, hi]
      · simp [hj']
    · simp only [hy, hys]
      by_cases hi' : i' = i
      · subst hi'; simp [Finset.sum_ite, hjS]
      · simp [hi']
    · simp only [hyb]; split_ifs with h
      · rw [h]; exact hδb
      · exact (hM.1.2.1 j').le
    · simp only [hys]; split_ifs with h
      · rw [h]; exact hδs.le
      · exact (hM.1.1 i').le
    · simp only [hy]; split_ifs <;> [exact hδ0.le; exact le_rfl]
    · simp only [hys]; split_ifs with h
      · rw [h]; exact hδs
      · exact hM.1.1 i'
  have hFj := hM.1.2.2.2.2.2.2 j
  set K := (M.h qs qb - M.h ys yb + M.gB j δ) / δ + 1
  obtain ⟨u0, hu0, hK⟩ := Finv_unbounded (M.Fb j) hFj htop K
  set t := min 1 ((1 - u0) * M.b j / (2 * δ)) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ (1 - u0) * M.b j / (2 * δ) := min_le_right _ _
  have hmixF := feas_mix M hF hyF t ht0.le ht1
  have hle := hopt.2 _ _ _ hmixF
  -- concavity deficits
  set Dg : B → ℝ := fun k => M.gB k ((1 - t) * qb k + t * yb k) - ((1 - t) * M.gB k (qb k) + t * M.gB k (yb k))
  set Dh : S → ℝ := fun k => (1 - t) * M.hS k (qs k) + t * M.hS k (ys k) - M.hS k ((1 - t) * qs k + t * ys k)
  have hDg : ∀ k, 0 ≤ Dg k := fun k => by
    have := mix_gB M hM k (qb k) (yb k) t (feas_nonneg_qb M hF k) (hF.2.2.1 k)
      (feas_nonneg_qb M hyF k) (hyF.2.2.1 k) ht0.le ht1
    simp only [Dg]; linarith
  have hDh : ∀ k, 0 ≤ Dh k := fun k => by
    have := mix_hS M hM k (qs k) (ys k) t (feas_nonneg_qs M hF k) (hF.2.2.2.1 k) (hF.2.2.2.2.2 k)
      (feas_nonneg_qs M hyF k) (hyF.2.2.2.1 k) (hyF.2.2.2.2.2 k) ht0.le ht1
    simp only [Dh]; linarith
  have hexp : M.h (fun i => (1 - t) * qs i + t * ys i) (fun j => (1 - t) * qb j + t * yb j) =
      (1 - t) * M.h qs qb + t * M.h ys yb + ∑ k, Dg k + ∑ k, Dh k := by
    have e1 : ∑ k, Dg k = ∑ k, M.gB k ((1 - t) * qb k + t * yb k) -
        ((1 - t) * ∑ k, M.gB k (qb k) + t * ∑ k, M.gB k (yb k)) := by
      simp only [Dg]; rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have e2 : ∑ k, Dh k = ((1 - t) * ∑ k, M.hS k (qs k) + t * ∑ k, M.hS k (ys k)) -
        ∑ k, M.hS k ((1 - t) * qs k + t * ys k) := by
      simp only [Dh]; rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    have e3 : ∑ i, M.c i * ((1 - t) * qs i + t * ys i) =
        (1 - t) * ∑ i, M.c i * qs i + t * ∑ i, M.c i * ys i := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_); ring
    simp only [Market.h]
    rw [e1, e2, e3]; ring
  have hSg : Dg j ≤ ∑ k, Dg k := Finset.single_le_sum (fun k _ => hDg k) (Finset.mem_univ j)
  have hSh : 0 ≤ ∑ k, Dh k := Finset.sum_nonneg (fun k _ => hDh k)
  -- compute Dg j
  have hgB0 : M.gB j 0 = 0 := by simp [Market.gB]
  have hDgj : Dg j = M.gB j (t * δ) - t * M.gB j δ := by
    simp only [Dg, hyb, if_pos rfl, ← h0, mul_zero, zero_add, hgB0, ite_true]
  have hu1 : u0 < 1 - t * δ / M.b j := by
    have : t * δ ≤ (1 - u0) * M.b j / 2 := by
      have := mul_le_mul_of_nonneg_right ht2 hδ0.le
      rw [div_mul_eq_mul_div, mul_div_assoc] at this
      calc t * δ ≤ (1 - u0) * M.b j * (δ / (2 * δ)) := this
        _ = (1 - u0) * M.b j / 2 := by field_simp
    have : t * δ / M.b j ≤ (1 - u0) / 2 := by
      rw [div_le_iff₀ hb]; linarith
    linarith
  have hu2 : 1 - t * δ / M.b j < 1 := by
    have : 0 < t * δ / M.b j := by positivity
    linarith
  have hKv := hK _ hu1 hu2
  have hgt : M.gB j (t * δ) = (M.Fb j).Finv (1 - t * δ / M.b j) * (t * δ) := rfl
  -- combine
  have : (1 - t) * M.h qs qb + t * M.h ys yb + (M.gB j (t * δ) - t * M.gB j δ) ≤ M.h qs qb := by
    linarith
  rw [hgt] at this
  have h2 : t * (δ * (M.Fb j).Finv (1 - t * δ / M.b j)) ≤ t * (M.h qs qb - M.h ys yb + M.gB j δ) := by
    nlinarith
  have h3 : δ * (M.Fb j).Finv (1 - t * δ / M.b j) ≤ M.h qs qb - M.h ys yb + M.gB j δ :=
    le_of_mul_le_mul_left h2 ht0
  have h4 : δ * K ≤ δ * (M.Fb j).Finv (1 - t * δ / M.b j) := mul_le_mul_of_nonneg_left hKv hδ0.le
  have h5 : δ * K = M.h qs qb - M.h ys yb + M.gB j δ + δ := by
    simp only [K]; field_simp
  linarith

end NMAuxT

open NetworkedMarkets.Relaxation NMAuxT in
theorem solution {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (xbar : S → B → ℝ) (qsbar : S → ℝ) (qbbar : B → ℝ) (hopt : M.IsOpt7 xbar qsbar qbbar) :
    IsGreatest M.Value3 (M.h qsbar qbbar) ∧
    (∀ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
      M.Feas3 f p x qs qb → M.rev f p x = M.h qsbar qbbar → qs = qsbar ∧ qb = qbbar) ∧
    (∀ f : Fees S B, f.InGammaU → (∀ i, f.γs i < 1) →
      (M.IsOptimalFees f ↔
        ∃ (p : S → ℝ) (x : S → B → ℝ), M.IsOpt7 x qsbar qbbar ∧ M.Sys8 f p x qsbar qbbar)) := by
  obtain ⟨hG, huniq⟩ := theorem_1_i M hM xbar qsbar qbbar hopt
  refine ⟨hG, huniq, ?_⟩
  intro f hf hγ1
  have hM1 := hM.1
  obtain ⟨hs0, hb0, hc0, hnS, hnB, hFs, hFb⟩ := hM1
  obtain ⟨hγs, hγb, hμs, hμb⟩ := hf
  have hd : ∀ i, 0 < 1 - f.γs i := fun i => by linarith [hγ1 i]
  have he : ∀ j, 0 < 1 + f.γb j := fun j => by linarith [hγb j]
  constructor
  · -- (→)
    rintro ⟨p, x, qs, qb, h3, hGr⟩
    have hrev : M.rev f p x = M.h qsbar qbbar := hGr.unique hG
    obtain ⟨rfl, rfl⟩ := huniq f p x qs qb h3 hrev
    obtain ⟨h7, -⟩ := eq_6_revenue_bound M hM.1 f p x qs qb h3
    have hopt' : M.IsOpt7 x qs qb := ⟨h7, fun x' qs' qb' h7' => hopt.2 x' qs' qb' h7'⟩
    refine ⟨p, x, hopt', ?_⟩
    obtain ⟨hTA, hTB⟩ := terms_nonneg M hM.1 f p x qs qb h3
    have hid := identity M f p x qs qb h3.2.2.2.2.1 h3.2.2.2.2.2.1
    rw [hrev, sub_self] at hid
    have hsA := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hTA i)
    have hsB := Finset.sum_nonneg hTB
    have hA0 : ∀ i, qs i * Aterm M f p qs i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hTA i)).mp
        (by linarith) i (Finset.mem_univ i)
      exact this
    have hB0 : ∀ e ∈ M.E, x e.1 e.2 * Bterm M f p qb e.1 e.2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hTB).mp (by linarith)
    obtain ⟨-, hp, h2a, h2b, h2cs, h2cb, h2dx, h2d⟩ := h3
    refine ⟨fun i hqi => ?_, fun i hqi => ?_, fun i j he' hx => ?_, fun i j he' hx => ?_,
      fun i => ⟨?_, ?_, hp i⟩, fun j => ⟨?_, ?_, ?_⟩⟩
    · have hA := (mul_eq_zero.mp (hA0 i)).resolve_left hqi.ne'
      simp only [Aterm] at hA
      simp only [Fees.γts, Fees.μts]
      have := hd i
      field_simp
      linarith
    · have : (M.Fs i).F ((1 - f.γs i) * p i - f.μs i) = 0 := by
        have := h2a i; rw [hqi] at this
        rcases mul_eq_zero.mp this.symm with h | h
        · exact absurd h (hs0 i).ne'
        · exact h
      have hle : (1 - f.γs i) * p i - f.μs i ≤ 0 := by
        by_contra hc; push Not at hc
        have := F_pos _ (hFs i) hc; linarith
      simp only [Fees.μts]
      have := hd i
      rw [sub_nonpos, le_div_iff₀ this]; linarith
    · have hB := (mul_eq_zero.mp (hB0 (i, j) he')).resolve_left hx.ne'
      simp only [Bterm, Market.cost] at hB
      simp only [Fees.γtb, Fees.μtb]
      have := he j
      field_simp
      linarith
    · obtain ⟨m, ⟨⟨i', hi'E, hi'm⟩, hmle⟩, hm⟩ := h2b j
      have hcm : m ≤ M.cost f p i j := hmle ⟨i, he', rfl⟩
      have hw0 : 0 ≤ m + f.μb j := by
        rw [hi'm]; simp only [Market.cost]
        have := hγb j; have := hp i'; have := hc0 i'; have := hμb j
        nlinarith
      have hq : 1 - qb j / M.b j = (M.Fb j).F (m + f.μb j) := by
        rw [hm]; field_simp [(hb0 j).ne']; ring
      have hFl := Finv_le (M.Fb j) (m + f.μb j) hw0
      rw [← hq] at hFl
      simp only [Market.cost] at hcm
      simp only [Fees.γtb, Fees.μtb]
      have := he j
      rw [ge_iff_le, show p i + f.μb j / (1 + f.γb j) + M.c i * (1 / (1 + f.γb j)) -
          (M.Fb j).Finv (1 - qb j / M.b j) * (1 / (1 + f.γb j)) =
          ((1 + f.γb j) * p i + M.c i + f.μb j - (M.Fb j).Finv (1 - qb j / M.b j)) / (1 + f.γb j) by
          field_simp; ring]
      apply div_nonneg _ this.le
      linarith
    · simp only [Fees.γts]; rw [ge_iff_le, le_div_iff₀ (hd i)]; linarith [hγs i]
    · simp only [Fees.μts]; exact div_nonneg (hμs i) (hd i).le
    · simp only [Fees.γtb]; exact div_nonneg zero_le_one (he j).le
    · simp only [Fees.γtb]; rw [div_le_iff₀ (he j)]; linarith [hγb j]
    · simp only [Fees.μtb]; exact div_nonneg (hμb j) (he j).le
  · -- (←)
    rintro ⟨p, x, hopt7, h8a, h8b, h8c, h8d, h8e, h8f⟩
    have h7 := hopt7.1
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := h7
    have hcs : ∀ i, qsbar i = ∑ j ∈ M.nbrS i, x i j := fun i => by linarith [f2 i]
    have hcb : ∀ j, qbbar j = ∑ i ∈ M.nbrB j, x i j := fun j => by linarith [f1 j]
    have hp : ∀ i, 0 ≤ p i := fun i => (h8e i).2.2
    -- (8a) rearranged
    have hA : ∀ i, 0 < qsbar i → (1 - f.γs i) * p i - f.μs i = (M.Fs i).Finv (qsbar i / M.s i) := by
      intro i hq
      have h1 := h8a i hq
      simp only [Fees.γts, Fees.μts] at h1
      have := hd i
      have h2 : (1 - f.γs i) * p i - f.μs i - (M.Fs i).Finv (qsbar i / M.s i) =
          (1 - f.γs i) * (p i - f.μs i / (1 - f.γs i) -
            (M.Fs i).Finv (qsbar i / M.s i) * (1 / (1 - f.γs i))) := by
        field_simp
      rw [h1, mul_zero] at h2
      linarith
    -- buyer side: V_j and the cost relation
    have hBle : ∀ i j, (i, j) ∈ M.E →
        (M.Fb j).Finv (1 - qbbar j / M.b j) ≤ M.cost f p i j + f.μb j := by
      intro i j hE
      have key : 0 ≤ p i + f.μtb j + M.c i * f.γtb j - (M.Fb j).Finv (1 - qbbar j / M.b j) * f.γtb j := by
        rcases eq_or_lt_of_le (f5 i j hE) with h0 | h0
        · exact h8d i j hE h0.symm
        · exact (h8c i j hE h0).ge
      simp only [Fees.γtb, Fees.μtb] at key
      have := he j
      have key2 : 0 ≤ ((1 + f.γb j) * p i + M.c i + f.μb j - (M.Fb j).Finv (1 - qbbar j / M.b j)) /
          (1 + f.γb j) := by
        rw [show ((1 + f.γb j) * p i + M.c i + f.μb j - (M.Fb j).Finv (1 - qbbar j / M.b j)) /
          (1 + f.γb j) = p i + f.μb j / (1 + f.γb j) + M.c i * (1 / (1 + f.γb j)) -
          (M.Fb j).Finv (1 - qbbar j / M.b j) * (1 / (1 + f.γb j)) by field_simp; ring]
        exact key
      have := (div_nonneg_iff.mp key2)
      simp only [Market.cost]
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · linarith
      · linarith
    have hBeq : ∀ i j, (i, j) ∈ M.E → 0 < x i j →
        M.cost f p i j + f.μb j = (M.Fb j).Finv (1 - qbbar j / M.b j) := by
      intro i j hE hx
      have key := h8c i j hE hx
      simp only [Fees.γtb, Fees.μtb] at key
      have := he j
      field_simp at key
      simp only [Market.cost]
      linarith
    have hCE : M.IsCE f p x qsbar qbbar := by
      refine ⟨hp, fun i => ?_, fun j => ?_, hcs, hcb, f5, fun i j hE ⟨i', hi'E, hlt⟩ => ?_⟩
      · rcases eq_or_lt_of_le (feas_nonneg_qs M hopt7.1 i) with h0 | h0
        · rw [← h0]
          have hle : (1 - f.γs i) * p i - f.μs i ≤ 0 := by
            have h1 := h8b i h0.symm
            simp only [Fees.μts] at h1
            have := hd i
            have h2 : (1 - f.γs i) * p i - f.μs i = (1 - f.γs i) * (p i - f.μs i / (1 - f.γs i)) := by
              field_simp
            rw [h2]; exact mul_nonpos_of_nonneg_of_nonpos this.le h1
          rw [F_of_nonpos _ (hFs i) hle]; ring
        · rw [hA i h0]
          have hu0 : 0 ≤ qsbar i / M.s i := div_nonneg h0.le (hs0 i).le
          have hu1 : qsbar i / M.s i ≤ 1 := (div_le_one (hs0 i)).mpr (f4 i)
          have hu : qsbar i / M.s i < 1 ∨ (M.Fs i).vbar ≠ ⊤ := by
            by_cases ht : (M.Fs i).vbar = ⊤
            · exact Or.inl ((div_lt_one (hs0 i)).mpr (f6 i ht))
            · exact Or.inr ht
          rw [F_Finv _ (hFs i) _ hu0 hu1 hu]
          field_simp [(hs0 i).ne']
      · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (M.nbrB j) (fun i => M.cost f p i j) (hnB j)
        have hi0E : (i0, j) ∈ M.E := by simpa [Market.nbrB] using hi0
        refine ⟨M.cost f p i0 j, ⟨⟨i0, hi0E, rfl⟩, ?_⟩, ?_⟩
        · rintro v ⟨i, hiE, rfl⟩
          exact hmin i (by simp [Market.nbrB, hiE])
        · have hV := hBle i0 j hi0E
          rcases eq_or_lt_of_le (feas_nonneg_qb M hopt7.1 j) with h0 | h0
          · -- qbbar j = 0
            rw [← h0]
            by_cases ht : (M.Fb j).vbar = ⊤
            · have := qb_pos_of_top M hM x qsbar qbbar hopt7 j ht; linarith
            · rw [← h0] at hV; simp only [zero_div, sub_zero] at hV
              have hF1 := F_Finv _ (hFb j) 1 zero_le_one le_rfl (Or.inr ht)
              have hmono := (hFb j).2.2.2.2.1 hV
              rw [hF1] at hmono
              have := F_le_one _ (hFb j) (M.cost f p i0 j + f.μb j)
              have : (M.Fb j).F (M.cost f p i0 j + f.μb j) = 1 := le_antisymm this hmono
              rw [this]; ring
          · -- qbbar j > 0 : some flow is positive
            obtain ⟨i, hi, hx⟩ : ∃ i ∈ M.nbrB j, 0 < x i j := by
              by_contra hc; push Not at hc
              have : ∑ i ∈ M.nbrB j, x i j ≤ 0 := Finset.sum_nonpos hc
              linarith [hcb j]
            have hiE : (i, j) ∈ M.E := by simpa [Market.nbrB] using hi
            have heq := hBeq i j hiE hx
            have hle2 : M.cost f p i0 j ≤ M.cost f p i j := hmin i hi
            have hmeq : M.cost f p i0 j + f.μb j = (M.Fb j).Finv (1 - qbbar j / M.b j) := by linarith
            rw [hmeq]
            have hu0 : 0 ≤ 1 - qbbar j / M.b j := by
              have := (div_le_one (hb0 j)).mpr (f3 j); linarith
            have hu1 : 1 - qbbar j / M.b j < 1 := by
              have : 0 < qbbar j / M.b j := div_pos h0 (hb0 j); linarith
            rw [F_Finv _ (hFb j) _ hu0 hu1.le (Or.inl hu1)]
            field_simp [(hb0 j).ne']; ring
      · by_contra hx
        have hx' : 0 < x i j := lt_of_le_of_ne (f5 i j hE) (Ne.symm hx)
        have := hBeq i j hE hx'
        have := hBle i' j hi'E
        linarith
    have hrev : M.rev f p x = M.h qsbar qbbar := by
      have hid := identity M f p x qsbar qbbar hcs hcb
      have hs1 : ∑ i, qsbar i * Aterm M f p qsbar i = 0 := by
        apply Finset.sum_eq_zero; intro i _
        rcases eq_or_lt_of_le (feas_nonneg_qs M hopt7.1 i) with h0 | h0
        · rw [← h0]; ring
        · simp only [Aterm]; rw [hA i h0]; ring
      have hs2 : ∑ e ∈ M.E, x e.1 e.2 * Bterm M f p qbbar e.1 e.2 = 0 := by
        apply Finset.sum_eq_zero; rintro ⟨i, j⟩ hE
        rcases eq_or_lt_of_le (f5 i j hE) with h0 | h0
        · simp only; rw [← h0]; ring
        · simp only [Bterm]; have := hBeq i j hE h0; rw [← this]; ring
      linarith
    refine ⟨p, x, qsbar, qbbar, ⟨⟨hγs, hγb, hμs, hμb⟩, hCE⟩, ?_⟩
    rw [hrev]; exact hG

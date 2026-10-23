-- Prove2me | solution 1 for NetworkedMarkets.Relaxation.proposition_EC_1_iii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T08:27:13.093705+00:00
-- url     : https://prove2.me/submissions/dfb663ea-82f9-432b-8f35-d6fa37600058

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting
import Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_v

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


namespace NMAuxT
open NetworkedMarkets.Relaxation

lemma Finv_mono (D : ValueDist) {u u' : ℝ} (h : u ≤ u')
    (hne : ({v : ℝ | 0 ≤ v ∧ u' ≤ D.F v}).Nonempty) : D.Finv u ≤ D.Finv u' := by
  unfold ValueDist.Finv
  exact csInf_le_csInf ⟨0, fun v hv => hv.1⟩ hne (fun v hv => ⟨hv.1, le_trans h hv.2⟩)

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

lemma Finv_lower (D : ValueDist) (hD : D.Assumption1) (V : ℝ) :
    ∀ u, D.F V < u → u < 1 → V ≤ D.Finv u := by
  intro u hu0 hu1
  have hne := Finv_set_nonempty D hD u hu1
  unfold ValueDist.Finv
  refine le_csInf hne ?_
  rintro v ⟨hv0, hv⟩
  by_contra hlt; push Not at hlt
  have := hD.2.2.2.2.1 hlt.le
  linarith

lemma F_lt_one_of_lt (D : ValueDist) (hD : D.Assumption1) (R : ℝ) (hR : D.vbar = (R : WithTop ℝ))
    (V : ℝ) (hV : V < R) : D.F V < 1 := by
  rcases le_or_gt V 0 with h0 | h0
  · rw [F_of_nonpos D hD h0]; norm_num
  · have hsm := hD.2.2.2.2.2.2.2.1
    have h1 : V ∈ D.Interior := ⟨h0, by rw [hR]; exact_mod_cast hV⟩
    have h2 : (V + R) / 2 ∈ D.Interior := ⟨by linarith, by rw [hR]; exact_mod_cast (by linarith : (V + R) / 2 < R)⟩
    have := hsm h1 h2 (by linarith)
    linarith [F_le_one D hD ((V + R) / 2)]

lemma exists_diff_of_monotoneOn {G : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hG : MonotoneOn G (Set.Ioo a b)) :
    ∃ r ∈ Set.Ioo a b, DifferentiableAt ℝ G r := by
  have h1 := hG.ae_differentiableWithinAt measurableSet_Ioo
  have h2 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioo a b)), x ∈ Set.Ioo a b :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioo
  haveI : (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioo a b))).NeBot := by
    rw [MeasureTheory.ae_restrict_neBot, Real.volume_Ioo]
    simp [hab]
  obtain ⟨r, hr1, hr2⟩ := (h1.and h2).exists
  exact ⟨r, hr2, hr1.differentiableAt (Ioo_mem_nhds hr2.1 hr2.2)⟩

lemma deriv_ge_of_left {φ : ℝ → ℝ} {r c δ : ℝ} (hδ : 0 < δ) (hd : DifferentiableAt ℝ φ r)
    (h : ∀ r', r - δ < r' → r' < r → (r - r') * c ≤ φ r - φ r') : c ≤ deriv φ r := by
  have ht := hd.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at ht
  have ht' : Tendsto (slope φ r) (𝓝[<] r) (𝓝 (deriv φ r)) :=
    ht.mono_left (nhdsWithin_mono r (fun y hy => ne_of_lt (Set.mem_Iio.mp hy)))
  apply ge_of_tendsto ht'
  have : Set.Ioo (r - δ) r ∈ 𝓝[<] r := Ioo_mem_nhdsLT (by linarith)
  filter_upwards [this] with r' hr'
  rw [slope_def_field]
  have h1 := h r' hr'.1 hr'.2
  have h2 : r' - r < 0 := by linarith [hr'.2]
  rw [le_div_iff_of_neg h2]
  linarith

lemma deriv_le_of_right {φ : ℝ → ℝ} {r c δ : ℝ} (hδ : 0 < δ) (hd : DifferentiableAt ℝ φ r)
    (h : ∀ r', r < r' → r' < r + δ → φ r' - φ r ≤ (r' - r) * c) : deriv φ r ≤ c := by
  have ht := hd.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at ht
  have ht' : Tendsto (slope φ r) (𝓝[>] r) (𝓝 (deriv φ r)) :=
    ht.mono_left (nhdsWithin_mono r (fun y hy => ne_of_gt (Set.mem_Ioi.mp hy)))
  apply le_of_tendsto ht'
  have : Set.Ioo r (r + δ) ∈ 𝓝[>] r := Ioo_mem_nhdsGT (by linarith)
  filter_upwards [this] with r' hr'
  rw [slope_def_field]
  have h1 := h r' hr'.1 hr'.2
  have h2 : 0 < r' - r := by linarith [hr'.1]
  rw [div_le_iff₀ h2]
  linarith

end NMAuxT

namespace NMAuxT
open NetworkedMarkets.Relaxation
variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- At differentiability points of `h_i` inside `(0, s_i)`, `h_i'(r) ≥ F⁻¹(r/s_i)`; and such points
are dense. -/
lemma seller_point (M : Market S B) (hM : M.Standing) (i : S) {a c : ℝ} (ha : 0 ≤ a) (hac : a < c)
    (hc : c ≤ M.s i) : ∃ r ∈ Set.Ioo a c, (M.Fs i).Finv (r / M.s i) ≤ deriv (M.hS i) r := by
  have hs := hM.1.1 i
  have hFs := hM.1.2.2.2.2.2.1 i
  have hmono : MonotoneOn (fun r => (M.Fs i).Finv (r / M.s i)) (Set.Ioo a c) := by
    intro r hr r' hr' hle
    apply Finv_mono _ (div_le_div_of_nonneg_right hle hs.le)
    exact Finv_set_nonempty _ hFs _ ((div_lt_one hs).mpr (lt_of_lt_of_le hr'.2 hc))
  obtain ⟨r, hr, hdG⟩ := exists_diff_of_monotoneOn hac hmono
  have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
  have hd : DifferentiableAt ℝ (M.hS i) r := by
    have : M.hS i = fun q => (M.Fs i).Finv (q / M.s i) * q := rfl
    rw [this]; exact hdG.mul differentiableAt_id
  refine ⟨r, hr, deriv_ge_of_left hr0 hd (fun r' h1 h2 => ?_)⟩
  have hr'0 : 0 ≤ r' := by linarith
  have hm : (M.Fs i).Finv (r' / M.s i) ≤ (M.Fs i).Finv (r / M.s i) :=
    Finv_mono _ (div_le_div_of_nonneg_right h2.le hs.le)
      (Finv_set_nonempty _ hFs _ ((div_lt_one hs).mpr (lt_of_lt_of_le hr.2 hc)))
  simp only [Market.hS]
  nlinarith [mul_le_mul_of_nonneg_left hm hr'0]

lemma buyer_point (M : Market S B) (hM : M.Standing) (j : B) {a c : ℝ} (ha : 0 ≤ a) (hac : a < c)
    (hc : c ≤ M.b j) : ∃ r ∈ Set.Ioo a c, deriv (M.gB j) r ≤ (M.Fb j).Finv (1 - r / M.b j) := by
  have hb := hM.1.2.1 j
  have hFb := hM.1.2.2.2.2.2.2 j
  have hmono : MonotoneOn (fun r => -(M.Fb j).Finv (1 - r / M.b j)) (Set.Ioo a c) := by
    intro r hr r' hr' hle
    simp only [neg_le_neg_iff]
    apply Finv_mono _ (by have := div_le_div_of_nonneg_right hle hb.le; linarith)
    apply Finv_set_nonempty _ hFb
    have : 0 < r / M.b j := div_pos (lt_of_le_of_lt ha hr.1) hb
    linarith
  obtain ⟨r, hr, hdG⟩ := exists_diff_of_monotoneOn hac hmono
  have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
  have hd : DifferentiableAt ℝ (M.gB j) r := by
    have : M.gB j = fun q => (-(-(M.Fb j).Finv (1 - q / M.b j))) * q := by
      funext q; simp [Market.gB]
    rw [this]; exact hdG.neg.mul differentiableAt_id
  refine ⟨r, hr, deriv_le_of_right hr0 hd (fun r' h1 h2 => ?_)⟩
  have hm : (M.Fb j).Finv (1 - r' / M.b j) ≤ (M.Fb j).Finv (1 - r / M.b j) := by
    apply Finv_mono _ (by have := div_le_div_of_nonneg_right h1.le hb.le; linarith)
    apply Finv_set_nonempty _ hFb
    have : 0 < r / M.b j := div_pos hr0 hb
    linarith
  simp only [Market.gB]
  have hr'0 : 0 ≤ r' := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hm hr'0]

lemma seller_slope (M : Market S B) (hM : M.Standing) (i : S) (q L : ℝ) (hq0 : 0 ≤ q)
    (hqs : q ≤ M.s i) (htop : (M.Fs i).vbar = ⊤ → q < M.s i)
    (hT : Tendsto (deriv (M.hS i)) (𝓝[Set.Ioo 0 (M.s i)] q) (𝓝 L)) :
    (M.Fs i).Finv (q / M.s i) ≤ L := by
  have hs := hM.1.1 i
  have hFs := hM.1.2.2.2.2.2.1 i
  by_contra hcon; push Not at hcon
  rcases lt_or_eq_of_le hqs with hlt | heq
  · set V := (M.Fs i).Finv (q / M.s i)
    have hev := hT.eventually (gt_mem_nhds hcon)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    obtain ⟨r, hr, hder⟩ := seller_point M hM i hq0 (lt_min (by linarith : q < q + δ) hlt)
      (min_le_right _ _)
    have hrI : r ∈ Set.Ioo 0 (M.s i) :=
      ⟨lt_of_le_of_lt hq0 hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
    have hdist : dist r q < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2, min_le_left (q + δ) (M.s i)]
    have h1 := hball hdist hrI
    have h2 : V ≤ (M.Fs i).Finv (r / M.s i) :=
      Finv_mono _ (div_le_div_of_nonneg_right hr.1.le hs.le)
        (Finv_set_nonempty _ hFs _ ((div_lt_one hs).mpr hrI.2))
    linarith
  · -- q = s_i, so the support is bounded
    have hntop : (M.Fs i).vbar ≠ ⊤ := fun ht => by have := htop ht; linarith
    obtain ⟨R, hR⟩ := WithTop.ne_top_iff_exists.mp hntop
    have hR0 : 0 < R := by have := hFs.1; rw [← hR] at this; exact_mod_cast this
    have hFR : (M.Fs i).F R = 1 := F_of_ge _ hFs (by rw [← hR])
    have hF1R : (M.Fs i).Finv 1 ≤ R := by
      unfold ValueDist.Finv; exact csInf_le ⟨0, fun v hv => hv.1⟩ ⟨hR0.le, hFR.ge⟩
    rw [heq, div_self hs.ne'] at hcon
    set V := (L + (M.Fs i).Finv 1) / 2 with hVdef
    have hVR : V < R := by rw [hVdef]; linarith
    have hFV : (M.Fs i).F V < 1 := F_lt_one_of_lt _ hFs R hR.symm V hVR
    have hev := hT.eventually (gt_mem_nhds (by rw [hVdef]; linarith : L < V))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hball⟩ := hev
    set a := max (max (q - δ / 2) (M.s i * (M.Fs i).F V)) (M.s i / 2)
    have ha0 : 0 ≤ a := le_trans (by linarith) (le_max_right _ _)
    have has : a < M.s i := by
      apply max_lt (max_lt (by linarith) ?_) (by linarith)
      nlinarith
    obtain ⟨r, hr, hder⟩ := seller_point M hM i ha0 has le_rfl
    have hrI : r ∈ Set.Ioo 0 (M.s i) := ⟨lt_of_le_of_lt ha0 hr.1, hr.2⟩
    have hdist : dist r q < δ := by
      have : q - δ / 2 ≤ a := le_trans (le_max_left _ _) (le_max_left _ _)
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2]
    have h1 := hball hdist hrI
    have hu : (M.Fs i).F V < r / M.s i := by
      rw [lt_div_iff₀ hs]
      have : M.s i * (M.Fs i).F V ≤ a := le_trans (le_max_right _ _) (le_max_left _ _)
      linarith [hr.1]
    have h2 := Finv_lower _ hFs V (r / M.s i) hu ((div_lt_one hs).mpr hr.2)
    linarith

lemma buyer_slope (M : Market S B) (hM : M.Standing) (j : B) (q L : ℝ) (hq0 : 0 ≤ q)
    (hqb : q < M.b j) (hpos : 0 < q ∨ (M.Fb j).vbar ≠ ⊤)
    (hT : Tendsto (deriv (M.gB j)) (𝓝[Set.Ioo 0 (M.b j)] q) (𝓝 L)) :
    L ≤ (M.Fb j).Finv (1 - q / M.b j) := by
  have hb := hM.1.2.1 j
  have hFb := hM.1.2.2.2.2.2.2 j
  by_contra hcon; push Not at hcon
  set V := (M.Fb j).Finv (1 - q / M.b j)
  have hev := hT.eventually (lt_mem_nhds hcon)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  obtain ⟨r, hr, hder⟩ := buyer_point M hM j hq0 (lt_min (by linarith : q < q + δ) hqb)
    (min_le_right _ _)
  have hrI : r ∈ Set.Ioo 0 (M.b j) :=
    ⟨lt_of_le_of_lt hq0 hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
  have hdist : dist r q < δ := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.1, hr.2, min_le_left (q + δ) (M.b j)]
  have h1 := hball hdist hrI
  have h2 : (M.Fb j).Finv (1 - r / M.b j) ≤ V := by
    apply Finv_mono _ (by have := div_le_div_of_nonneg_right hr.1.le hb.le; linarith)
    apply Finv_set_nonempty' _ hFb
    · have : 0 ≤ q / M.b j := div_nonneg hq0 hb.le; linarith
    · rcases hpos with hp | hp
      · left; have : 0 < q / M.b j := div_pos hp hb; linarith
      · right; exact hp
  linarith

end NMAuxT




namespace NMAuxT
open NetworkedMarkets.Relaxation

section Dist
variable (D : ValueDist)

lemma Finv_zero' (hD : D.Assumption1) : D.Finv 0 = 0 := by
  apply le_antisymm _ (Finv_nonneg D 0)
  unfold ValueDist.Finv
  exact csInf_le ⟨0, fun v hv => hv.1⟩ ⟨le_rfl, F_nonneg D hD 0⟩

lemma Finv_pos' (hD : D.Assumption1) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
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

lemma interior_open (hD : D.Assumption1) : IsOpen D.Interior := by
  by_cases h : D.vbar = ⊤
  · have : D.Interior = Set.Ioi 0 := by
      ext v; simp [ValueDist.Interior, h]
    rw [this]; exact isOpen_Ioi
  · obtain ⟨R, hR⟩ := WithTop.ne_top_iff_exists.mp h
    have : D.Interior = Set.Ioo 0 R := by
      ext v; simp [ValueDist.Interior, ← hR]
    rw [this]; exact isOpen_Ioo

lemma F_lt_one_of_lt_vbar (hD : D.Assumption1) {v : ℝ} (hv : (v : WithTop ℝ) < D.vbar) :
    D.F v < 1 := by
  by_cases h : D.vbar = ⊤
  · exact F_lt_one_of_top D hD h v
  · obtain ⟨R, hR⟩ := WithTop.ne_top_iff_exists.mp h
    rw [← hR] at hv
    exact F_lt_one_of_lt D hD R hR.symm v (by exact_mod_cast hv)

lemma Finv_F (hD : D.Assumption1) {v : ℝ} (hv0 : 0 ≤ v) (hv : (v : WithTop ℝ) < D.vbar) :
    D.Finv (D.F v) = v :=
  le_antisymm (Finv_le D v hv0) (Finv_ge D hD v hv0 (F_lt_one_of_lt_vbar D hD hv))

lemma F_lt_of_lt (hD : D.Assumption1) {v w : ℝ} (hv : v ∈ D.Interior) (hw : w < v) :
    D.F w < D.F v := by
  rcases le_or_gt w 0 with h | h
  · rw [F_of_nonpos D hD h]; exact F_pos D hD hv.1
  · have hwI : w ∈ D.Interior := ⟨h, lt_trans (by exact_mod_cast hw) hv.2⟩
    exact hD.2.2.2.2.2.2.2.1 hwI hv hw

lemma F_gt_of_gt (hD : D.Assumption1) {v w : ℝ} (hv : v ∈ D.Interior) (hw : v < w) :
    D.F v < D.F w := by
  by_cases h : D.vbar ≤ (w : WithTop ℝ)
  · rw [F_of_ge D hD h]; exact F_lt_one_of_lt_vbar D hD hv.2
  · push Not at h
    have hwI : w ∈ D.Interior := ⟨lt_trans hv.1 hw, h⟩
    exact hD.2.2.2.2.2.2.2.1 hv hwI hw

lemma Finv_mem_interior (hD : D.Assumption1) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    D.Finv u ∈ D.Interior := by
  refine ⟨Finv_pos' D hD hu0 hu1, ?_⟩
  by_contra h; push Not at h
  have h1 := F_of_ge D hD h
  rw [F_Finv D hD u hu0.le hu1.le (Or.inl hu1)] at h1
  linarith


lemma Finv_continuousAt (hD : D.Assumption1) {u0 : ℝ} (h0 : 0 < u0) (h1 : u0 < 1) :
    ContinuousAt D.Finv u0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  set v0 := D.Finv u0
  have hv0 : v0 ∈ D.Interior := Finv_mem_interior D hD h0 h1
  have hFv0 : D.F v0 = u0 := F_Finv D hD u0 h0.le h1.le (Or.inl h1)
  set e := ε / 2 with he_def
  have he : 0 < e := half_pos hε
  have hlo : D.F (v0 - e) < u0 := by rw [← hFv0]; exact F_lt_of_lt D hD hv0 (by linarith)
  have hhi : u0 < D.F (v0 + e) := by rw [← hFv0]; exact F_gt_of_gt D hD hv0 (by linarith)
  refine ⟨min (u0 - D.F (v0 - e)) (D.F (v0 + e) - u0), lt_min (by linarith) (by linarith), ?_⟩
  intro u hu
  rw [Real.dist_eq, abs_lt] at hu
  have hm1 := min_le_left (u0 - D.F (v0 - e)) (D.F (v0 + e) - u0)
  have hm2 := min_le_right (u0 - D.F (v0 - e)) (D.F (v0 + e) - u0)
  have hu_lo : D.F (v0 - e) < u := by linarith
  have hu_hi : u < D.F (v0 + e) := by linarith
  have hu1 : u < 1 := lt_of_lt_of_le hu_hi (F_le_one D hD _)
  have hA := Finv_lower D hD (v0 - e) u hu_lo hu1
  have hB : D.Finv u ≤ v0 + e := by
    unfold ValueDist.Finv
    exact csInf_le ⟨0, fun v hv => hv.1⟩ ⟨by linarith [hv0.1], hu_hi.le⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith [he_def]

lemma F_hasDerivAt (hD : D.Assumption1) {v : ℝ} (hv : v ∈ D.Interior) :
    HasDerivAt D.F (deriv D.F v) v := by
  have hcd := hD.2.2.2.2.2.2.2.2.1
  have hdo : DifferentiableOn ℝ D.F D.Interior := hcd.differentiableOn (by norm_num)
  exact (hdo.differentiableAt ((interior_open D hD).mem_nhds hv)).hasDerivAt

lemma F_deriv_contOn (hD : D.Assumption1) : ContinuousOn (deriv D.F) D.Interior :=
  hD.2.2.2.2.2.2.2.2.1.continuousOn_deriv_of_isOpen (interior_open D hD) le_rfl

/-- If `v - v₀ ≤ C (F v - F v₀)` to the right of `v₀`, then `F'(v₀) > 0`. -/
lemma Fderiv_pos_of_right (hD : D.Assumption1) {v0 v1 C : ℝ} (hv0 : v0 ∈ D.Interior) (h01 : v0 < v1)
    (hC : 0 < C) (h : ∀ v, v0 < v → v < v1 → v - v0 ≤ C * (D.F v - D.F v0)) :
    0 < deriv D.F v0 := by
  have ht := (F_hasDerivAt D hD hv0)
  rw [hasDerivAt_iff_tendsto_slope] at ht
  have ht' : Tendsto (slope D.F v0) (𝓝[>] v0) (𝓝 (deriv D.F v0)) :=
    ht.mono_left (nhdsWithin_mono v0 (fun y hy => ne_of_gt (Set.mem_Ioi.mp hy)))
  have : 1 / C ≤ deriv D.F v0 := by
    apply ge_of_tendsto ht'
    filter_upwards [Ioo_mem_nhdsGT h01] with v hv
    rw [slope_def_field]
    have h1 := h v hv.1 hv.2
    have h2 : 0 < v - v0 := by linarith [hv.1]
    rw [div_le_div_iff₀ hC h2]
    linarith
  exact lt_of_lt_of_le (by positivity) this

lemma Fderiv_pos_of_left (hD : D.Assumption1) {v0 v1 C : ℝ} (hv0 : v0 ∈ D.Interior) (h01 : v1 < v0)
    (hC : 0 < C) (h : ∀ v, v1 < v → v < v0 → v0 - v ≤ C * (D.F v0 - D.F v)) :
    0 < deriv D.F v0 := by
  have ht := (F_hasDerivAt D hD hv0)
  rw [hasDerivAt_iff_tendsto_slope] at ht
  have ht' : Tendsto (slope D.F v0) (𝓝[<] v0) (𝓝 (deriv D.F v0)) :=
    ht.mono_left (nhdsWithin_mono v0 (fun y hy => ne_of_lt (Set.mem_Iio.mp hy)))
  have : 1 / C ≤ deriv D.F v0 := by
    apply ge_of_tendsto ht'
    filter_upwards [Ioo_mem_nhdsLT h01] with v hv
    rw [slope_def_field]
    have h1 := h v hv.1 hv.2
    have h2 : v - v0 < 0 := by linarith [hv.2]
    rw [le_div_iff_of_neg h2]
    have : 1 / C * (v - v0) = -(1 / C * (v0 - v)) := by ring
    rw [this]
    have h3 : 1 / C * (v0 - v) ≤ D.F v0 - D.F v := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hC]; linarith
    linarith
  exact lt_of_lt_of_le (by positivity) this

lemma Finv_hasDerivAt (hD : D.Assumption1) (hpos : ∀ v ∈ D.Interior, 0 < deriv D.F v)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt D.Finv (deriv D.F (D.Finv u))⁻¹ u := by
  have hI := Finv_mem_interior D hD hu0 hu1
  apply HasDerivAt.of_local_left_inverse (Finv_continuousAt D hD hu0 hu1) (F_hasDerivAt D hD hI)
    (hpos _ hI).ne'
  filter_upwards [Ioo_mem_nhds hu0 hu1] with y hy
  exact F_Finv D hD y hy.1.le hy.2.le (Or.inl hy.2)

lemma Finv_deriv_continuousAt (hD : D.Assumption1) (hpos : ∀ v ∈ D.Interior, 0 < deriv D.F v)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ContinuousAt (fun u => (deriv D.F (D.Finv u))⁻¹) u := by
  have hI := Finv_mem_interior D hD hu0 hu1
  have h1 : ContinuousAt (deriv D.F) (D.Finv u) :=
    (F_deriv_contOn D hD).continuousAt ((interior_open D hD).mem_nhds hI)
  exact (h1.comp (Finv_continuousAt D hD hu0 hu1)).inv₀ (hpos _ hI).ne'

end Dist
end NMAuxT



namespace NMAuxT
open NetworkedMarkets.Relaxation

lemma concave_secant {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {x y z : ℝ} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y ≤ z) :
    f x + (y - x) / (z - x) * (f z - f x) ≤ f y := by
  have hzx : 0 < z - x := by linarith
  have ha : 0 ≤ (z - y) / (z - x) := div_nonneg (by linarith) hzx.le
  have hb : 0 ≤ (y - x) / (z - x) := div_nonneg (by linarith) hzx.le
  have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by field_simp; ring
  have := hf.2 hx hz ha hb hab
  simp only [smul_eq_mul] at this
  have e : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by field_simp; ring
  rw [e] at this
  have e2 : (z - y) / (z - x) = 1 - (y - x) / (z - x) := by linarith
  rw [e2] at this
  linarith

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma seller_Fderiv_pos (M : Market S B) (hM : M.Standing) (i : S) :
    ∀ v ∈ (M.Fs i).Interior, 0 < deriv (M.Fs i).F v := by
  intro v0 hv0
  set D := M.Fs i with hDdef
  have hD : D.Assumption1 := hM.1.2.2.2.2.2.1 i
  have hcc : ConcaveOn ℝ D.sellerUnitDom (fun u => -(u * D.Finv u)) := (hM.2.2 i).concaveOn
  set u0 := D.F v0 with hu0def
  have hu0 : 0 < u0 := F_pos D hD hv0.1
  have hu01 : u0 < 1 := F_lt_one_of_lt_vbar D hD hv0.2
  have hFinv0 : D.Finv u0 = v0 := Finv_F D hD hv0.1.le hv0.2
  set u1 := (u0 + 1) / 2 with hu1def
  have hu01' : u0 < u1 := by rw [hu1def]; linarith
  have hu11 : u1 < 1 := by rw [hu1def]; linarith
  set v1 := D.Finv u1 with hv1def
  have hFv1 : D.F v1 = u1 := F_Finv D hD u1 (by linarith) hu11.le (Or.inl hu11)
  have hv1I : v1 ∈ D.Interior := Finv_mem_interior D hD (by linarith) hu11
  have hv01 : v0 < v1 := by
    by_contra h; push Not at h
    have := hD.2.2.2.2.1 h
    linarith
  have hdom : ∀ u, 0 ≤ u → u < 1 → u ∈ D.sellerUnitDom := fun u h0 h1 => ⟨h0, h1.le, fun _ => h1⟩
  set K := (u1 * D.Finv u1 - u0 * v0) / (u1 - u0)
  apply Fderiv_pos_of_right D hD hv0 hv01 (lt_of_lt_of_le one_pos (le_max_right (K / u0) 1))
  intro v hv hvv1
  have hvI : v ∈ D.Interior := ⟨lt_trans hv0.1 hv, lt_trans (by exact_mod_cast hvv1) hv1I.2⟩
  set u := D.F v
  have hu_gt : u0 < u := F_gt_of_gt D hD hv0 hv
  have hu_le : u ≤ u1 := by rw [← hFv1]; exact hD.2.2.2.2.1 hvv1.le
  have hFinv : D.Finv u = v := Finv_F D hD hvI.1.le hvI.2
  have hsec := concave_secant hcc (hdom u0 hu0.le hu01) (hdom u1 (by linarith) hu11) hu_gt hu_le
  simp only [hFinv, hFinv0] at hsec
  -- hsec : -(u0*v0) + (u-u0)/(u1-u0) * (-(u1*Finv u1) - -(u0*v0)) ≤ -(u*v)
  have hK : u * v - u0 * v0 ≤ (u - u0) * K := by
    have e : (u - u0) / (u1 - u0) * (-(u1 * D.Finv u1) - -(u0 * v0)) = -((u - u0) * K) := by
      simp only [K]; field_simp; ring
    rw [e] at hsec; linarith
  have h1 : u0 * (v - v0) ≤ (u - u0) * K := by nlinarith [hvI.1]
  have h2 : v - v0 ≤ K / u0 * (u - u0) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hu0]; linarith
  have h3 : K / u0 * (u - u0) ≤ max (K / u0) 1 * (u - u0) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  linarith

lemma buyer_Fderiv_pos (M : Market S B) (hM : M.Standing) (j : B) :
    ∀ v ∈ (M.Fb j).Interior, 0 < deriv (M.Fb j).F v := by
  intro v0 hv0
  set D := M.Fb j with hDdef
  have hD : D.Assumption1 := hM.1.2.2.2.2.2.2 j
  have hcc : ConcaveOn ℝ (Set.Icc 0 1) (fun u => u * D.Finv (1 - u)) := (hM.2.1 j).concaveOn
  set w0 := D.F v0 with hw0def
  have hw0 : 0 < w0 := F_pos D hD hv0.1
  have hw01 : w0 < 1 := F_lt_one_of_lt_vbar D hD hv0.2
  have hFinv0 : D.Finv w0 = v0 := Finv_F D hD hv0.1.le hv0.2
  set u0 := 1 - w0 with hu0def
  set u1 := (u0 + 1) / 2 with hu1def
  have hu0 : 0 < u0 := by rw [hu0def]; linarith
  have hu01' : u0 < u1 := by rw [hu1def, hu0def]; linarith
  have hu11 : u1 < 1 := by rw [hu1def, hu0def]; linarith
  set w1 := 1 - u1 with hw1def
  have hw1 : 0 < w1 := by rw [hw1def]; linarith
  have hw10 : w1 < w0 := by rw [hw1def, hu1def, hu0def]; linarith
  set v1 := D.Finv w1 with hv1def
  have hFv1 : D.F v1 = w1 := F_Finv D hD w1 hw1.le (by linarith) (Or.inl (by linarith))
  have hv1I : v1 ∈ D.Interior := Finv_mem_interior D hD hw1 (by linarith)
  have hv10 : v1 < v0 := by
    by_contra h; push Not at h
    have := hD.2.2.2.2.1 h
    linarith
  set K := (u1 * D.Finv (1 - u1) - u0 * v0) / (u1 - u0)
  apply Fderiv_pos_of_left D hD hv0 hv10 (lt_of_lt_of_le one_pos (le_max_right ((v0 - K) / u0) 1))
  intro v hv hvv0
  have hvI : v ∈ D.Interior := ⟨lt_trans hv1I.1 hv, lt_trans (by exact_mod_cast hvv0) hv0.2⟩
  set w := D.F v
  have hw_lt : w < w0 := F_lt_of_lt D hD hv0 hvv0
  have hw_ge : w1 ≤ w := by rw [← hFv1]; exact hD.2.2.2.2.1 hv.le
  have hFinv : D.Finv w = v := Finv_F D hD hvI.1.le hvI.2
  set u := 1 - w with hudef
  have hu_gt : u0 < u := by rw [hudef, hu0def]; linarith
  have hu_le : u ≤ u1 := by rw [hudef]; linarith
  have hsec := concave_secant hcc ⟨hu0.le, by linarith⟩ ⟨by linarith, hu11.le⟩ hu_gt hu_le
  have e0 : 1 - u0 = w0 := by rw [hu0def]; ring
  have e1 : 1 - u = w := by rw [hudef]; ring
  simp only [e0, e1, hFinv, hFinv0] at hsec
  have hK : u0 * v0 + (u - u0) * K ≤ u * v := by
    have e : (u - u0) / (u1 - u0) * (u1 * D.Finv (1 - u1) - u0 * v0) = (u - u0) * K := by
      simp only [K]; field_simp
    rw [e] at hsec; linarith
  have h1 : u0 * (v0 - v) ≤ (u - u0) * (v0 - K) := by nlinarith
  have h2 : v0 - v ≤ (v0 - K) / u0 * (u - u0) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hu0]; linarith
  have h3 : (v0 - K) / u0 * (u - u0) ≤ max ((v0 - K) / u0) 1 * (u - u0) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have e4 : u - u0 = w0 - w := by rw [hudef, hu0def]; ring
  rw [e4] at h3
  linarith

end NMAuxT



namespace NMAuxT
open NetworkedMarkets.Relaxation

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- explicit derivative of `g_j` on `(0, b_j)` -/
noncomputable def gBd (M : Market S B) (j : B) (q : ℝ) : ℝ :=
  (deriv (M.Fb j).F ((M.Fb j).Finv (1 - q / M.b j)))⁻¹ * (-(1 / M.b j)) * q +
    (M.Fb j).Finv (1 - q / M.b j)

/-- explicit derivative of `h_i` on `(0, s_i)` -/
noncomputable def hSd (M : Market S B) (i : S) (q : ℝ) : ℝ :=
  (deriv (M.Fs i).F ((M.Fs i).Finv (q / M.s i)))⁻¹ * (1 / M.s i) * q +
    (M.Fs i).Finv (q / M.s i)

lemma gB_hasDerivAt (M : Market S B) (hM : M.Standing) (j : B) {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (M.b j)) : HasDerivAt (M.gB j) (gBd M j q) q := by
  have hb := hM.1.2.1 j
  have hD := hM.1.2.2.2.2.2.2 j
  have hu0 : 0 < 1 - q / M.b j := by have := (div_lt_one hb).mpr hq.2; linarith
  have hu1 : 1 - q / M.b j < 1 := by have := div_pos hq.1 hb; linarith
  have hlin : HasDerivAt (fun x => 1 - x / M.b j) (-(1 / M.b j)) q :=
    ((hasDerivAt_id q).div_const (M.b j)).const_sub 1
  have h1 := (Finv_hasDerivAt (M.Fb j) hD (buyer_Fderiv_pos M hM j) hu0 hu1).comp q hlin
  have h2 := h1.mul (hasDerivAt_id q)
  have h3 : HasDerivAt (M.gB j) ((deriv (M.Fb j).F ((M.Fb j).Finv (1 - q / M.b j)))⁻¹ *
      -(1 / M.b j) * id q + ((M.Fb j).Finv ∘ fun x => 1 - x / M.b j) q * 1) q := h2
  convert h3 using 1
  simp only [gBd, Function.comp_apply, id_eq, mul_one]

lemma hS_hasDerivAt (M : Market S B) (hM : M.Standing) (i : S) {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (M.s i)) : HasDerivAt (M.hS i) (hSd M i q) q := by
  have hs := hM.1.1 i
  have hD := hM.1.2.2.2.2.2.1 i
  have hu0 : 0 < q / M.s i := div_pos hq.1 hs
  have hu1 : q / M.s i < 1 := (div_lt_one hs).mpr hq.2
  have hlin : HasDerivAt (fun x => x / M.s i) (1 / M.s i) q := (hasDerivAt_id q).div_const (M.s i)
  have h1 := (Finv_hasDerivAt (M.Fs i) hD (seller_Fderiv_pos M hM i) hu0 hu1).comp q hlin
  have h2 := h1.mul (hasDerivAt_id q)
  have h3 : HasDerivAt (M.hS i) ((deriv (M.Fs i).F ((M.Fs i).Finv (q / M.s i)))⁻¹ *
      (1 / M.s i) * id q + ((M.Fs i).Finv ∘ fun x => x / M.s i) q * 1) q := h2
  convert h3 using 1
  simp only [hSd, Function.comp_apply, id_eq, mul_one]

lemma gBd_continuousAt (M : Market S B) (hM : M.Standing) (j : B) {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (M.b j)) : ContinuousAt (gBd M j) q := by
  have hb := hM.1.2.1 j
  have hD := hM.1.2.2.2.2.2.2 j
  have hu0 : 0 < 1 - q / M.b j := by have := (div_lt_one hb).mpr hq.2; linarith
  have hu1 : 1 - q / M.b j < 1 := by have := div_pos hq.1 hb; linarith
  have hl : ContinuousAt (fun x => 1 - x / M.b j) q := by fun_prop
  have c1 : ContinuousAt (fun x => (deriv (M.Fb j).F ((M.Fb j).Finv (1 - x / M.b j)))⁻¹) q :=
    ContinuousAt.comp (g := fun u => (deriv (M.Fb j).F ((M.Fb j).Finv u))⁻¹)
      (f := fun x => 1 - x / M.b j)
      (Finv_deriv_continuousAt (M.Fb j) hD (buyer_Fderiv_pos M hM j) hu0 hu1) hl
  have c2 : ContinuousAt (fun x => (M.Fb j).Finv (1 - x / M.b j)) q :=
    ContinuousAt.comp (g := (M.Fb j).Finv) (f := fun x => 1 - x / M.b j)
      (Finv_continuousAt (M.Fb j) hD hu0 hu1) hl
  have e : gBd M j = fun x => (deriv (M.Fb j).F ((M.Fb j).Finv (1 - x / M.b j)))⁻¹ *
      (-(1 / M.b j)) * x + (M.Fb j).Finv (1 - x / M.b j) := rfl
  rw [e]
  exact ((c1.mul continuousAt_const).mul continuousAt_id).add c2

lemma hSd_continuousAt (M : Market S B) (hM : M.Standing) (i : S) {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (M.s i)) : ContinuousAt (hSd M i) q := by
  have hs := hM.1.1 i
  have hD := hM.1.2.2.2.2.2.1 i
  have hu0 : 0 < q / M.s i := div_pos hq.1 hs
  have hu1 : q / M.s i < 1 := (div_lt_one hs).mpr hq.2
  have hl : ContinuousAt (fun x => x / M.s i) q := by fun_prop
  have c1 : ContinuousAt (fun x => (deriv (M.Fs i).F ((M.Fs i).Finv (x / M.s i)))⁻¹) q :=
    ContinuousAt.comp (g := fun u => (deriv (M.Fs i).F ((M.Fs i).Finv u))⁻¹)
      (f := fun x => x / M.s i)
      (Finv_deriv_continuousAt (M.Fs i) hD (seller_Fderiv_pos M hM i) hu0 hu1) hl
  have c2 : ContinuousAt (fun x => (M.Fs i).Finv (x / M.s i)) q :=
    ContinuousAt.comp (g := (M.Fs i).Finv) (f := fun x => x / M.s i)
      (Finv_continuousAt (M.Fs i) hD hu0 hu1) hl
  have e : hSd M i = fun x => (deriv (M.Fs i).F ((M.Fs i).Finv (x / M.s i)))⁻¹ *
      (1 / M.s i) * x + (M.Fs i).Finv (x / M.s i) := rfl
  rw [e]
  exact ((c1.mul continuousAt_const).mul continuousAt_id).add c2

lemma gB_deriv_continuousAt (M : Market S B) (hM : M.Standing) (j : B) {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (M.b j)) : ContinuousAt (deriv (M.gB j)) q := by
  apply (gBd_continuousAt M hM j hq).congr
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with y hy
  exact (gB_hasDerivAt M hM j hy).deriv.symm

lemma hS_deriv_continuousAt (M : Market S B) (hM : M.Standing) (i : S) {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (M.s i)) : ContinuousAt (deriv (M.hS i)) q := by
  apply (hSd_continuousAt M hM i hq).congr
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with y hy
  exact (hS_hasDerivAt M hM i hy).deriv.symm

lemma gB_concaveOn (M : Market S B) (hM : M.Standing) (j : B) {T : Set ℝ} (hT : Convex ℝ T)
    (hsub : ∀ q ∈ T, 0 ≤ q ∧ q ≤ M.b j) : ConcaveOn ℝ T (M.gB j) := by
  refine ⟨hT, fun x hx y hy a c ha hc hac => ?_⟩
  have := mix_gB M hM j x y c (hsub x hx).1 (hsub x hx).2 (hsub y hy).1 (hsub y hy).2 hc
    (by linarith)
  simp only [smul_eq_mul]
  have e : a = 1 - c := by linarith
  rw [e]; exact this

lemma hS_convexOn (M : Market S B) (hM : M.Standing) (i : S) {T : Set ℝ} (hT : Convex ℝ T)
    (hsub : ∀ q ∈ T, 0 ≤ q ∧ q ≤ M.s i ∧ ((M.Fs i).vbar = ⊤ → q < M.s i)) :
    ConvexOn ℝ T (M.hS i) := by
  refine ⟨hT, fun x hx y hy a c ha hc hac => ?_⟩
  have := mix_hS M hM i x y c (hsub x hx).1 (hsub x hx).2.1 (hsub x hx).2.2 (hsub y hy).1
    (hsub y hy).2.1 (hsub y hy).2.2 hc (by linarith)
  simp only [smul_eq_mul]
  have e : a = 1 - c := by linarith
  rw [e]; exact this

lemma gB_deriv_antitoneOn (M : Market S B) (hM : M.Standing) (j : B) :
    AntitoneOn (deriv (M.gB j)) (Set.Ioo 0 (M.b j)) :=
  (gB_concaveOn M hM j (convex_Ioo 0 (M.b j)) (fun q hq => ⟨hq.1.le, hq.2.le⟩)).antitoneOn_deriv
    (fun q hq => (gB_hasDerivAt M hM j hq).differentiableAt)

lemma hS_deriv_monotoneOn (M : Market S B) (hM : M.Standing) (i : S) :
    MonotoneOn (deriv (M.hS i)) (Set.Ioo 0 (M.s i)) :=
  (hS_convexOn M hM i (convex_Ioo 0 (M.s i)) (fun q hq => ⟨hq.1.le, hq.2.le, fun _ => hq.2⟩)).monotoneOn_deriv
    (fun q hq => (hS_hasDerivAt M hM i hq).differentiableAt)

end NMAuxT



namespace NMAuxT
open NetworkedMarkets.Relaxation

section Dist
variable (D : ValueDist)

lemma Finv_one (hD : D.Assumption1) {R : ℝ} (hR : D.vbar = (R : WithTop ℝ)) : D.Finv 1 = R := by
  have hR0 : 0 < R := by have := hD.1; rw [hR] at this; exact_mod_cast this
  have hFR : D.F R = 1 := F_of_ge D hD (by rw [hR])
  apply le_antisymm
  · unfold ValueDist.Finv; exact csInf_le ⟨0, fun v hv => hv.1⟩ ⟨hR0.le, hFR.ge⟩
  · unfold ValueDist.Finv
    refine le_csInf ⟨R, hR0.le, hFR.ge⟩ ?_
    rintro v ⟨hv0, hv⟩
    by_contra hlt; push Not at hlt
    have := F_lt_one_of_lt D hD R hR v hlt
    linarith

lemma Finv_le_vbar (hD : D.Assumption1) {R : ℝ} (hR : D.vbar = (R : WithTop ℝ)) {u : ℝ}
    (hu : u ≤ 1) : D.Finv u ≤ R := by
  have hR0 : 0 < R := by have := hD.1; rw [hR] at this; exact_mod_cast this
  have hFR : D.F R = 1 := F_of_ge D hD (by rw [hR])
  unfold ValueDist.Finv; exact csInf_le ⟨0, fun v hv => hv.1⟩ ⟨hR0.le, by rw [hFR]; exact hu⟩

lemma Finv_tendsto_one (hD : D.Assumption1) {R : ℝ} (hR : D.vbar = (R : WithTop ℝ)) :
    Tendsto D.Finv (𝓝[<] 1) (𝓝 R) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · set V := (a + R) / 2 with hV
    have hFV : D.F V < 1 := F_lt_one_of_lt D hD R hR V (by rw [hV]; linarith)
    filter_upwards [Ioo_mem_nhdsLT hFV] with u hu
    have := Finv_lower D hD V u hu.1 hu.2
    rw [hV] at this; linarith
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact lt_of_le_of_lt (Finv_le_vbar D hD hR (le_of_lt hu)) ha

end Dist

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma gB_zero (M : Market S B) (j : B) : M.gB j 0 = 0 := by simp [Market.gB]
lemma hS_zero (M : Market S B) (i : S) : M.hS i 0 = 0 := by simp [Market.hS]

lemma gB_contWithin0 (M : Market S B) (hM : M.Standing) (j : B) (ht : (M.Fb j).vbar ≠ ⊤) :
    ContinuousWithinAt (M.gB j) (Set.Ioo 0 (M.b j)) 0 := by
  have hb := hM.1.2.1 j
  have hD := hM.1.2.2.2.2.2.2 j
  have hne := Finv_set_nonempty' (M.Fb j) hD 1 le_rfl (Or.inr ht)
  unfold ContinuousWithinAt
  rw [gB_zero]
  have hup : Tendsto (fun q => (M.Fb j).Finv 1 * q) (𝓝[Set.Ioo 0 (M.b j)] 0) (𝓝 0) := by
    have : Tendsto (fun q => (M.Fb j).Finv 1 * q) (𝓝 0) (𝓝 ((M.Fb j).Finv 1 * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this; exact this.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [Market.gB]; exact mul_nonneg (Finv_nonneg _ _) hq.1.le
  · filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [Market.gB]
    apply mul_le_mul_of_nonneg_right _ hq.1.le
    exact Finv_mono _ (by have := div_pos hq.1 hb; linarith) hne

lemma hS_contWithin0 (M : Market S B) (hM : M.Standing) (i : S) :
    ContinuousWithinAt (M.hS i) (Set.Ioo 0 (M.s i)) 0 := by
  have hs := hM.1.1 i
  have hD := hM.1.2.2.2.2.2.1 i
  have hne := Finv_set_nonempty (M.Fs i) hD (1/2) (by norm_num)
  unfold ContinuousWithinAt
  rw [hS_zero]
  have hup : Tendsto (fun q => (M.Fs i).Finv (1/2) * q) (𝓝[Set.Ioo 0 (M.s i)] 0) (𝓝 0) := by
    have : Tendsto (fun q => (M.Fs i).Finv (1/2) * q) (𝓝 0) (𝓝 ((M.Fs i).Finv (1/2) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this; exact this.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ q in 𝓝[Set.Ioo 0 (M.s i)] (0:ℝ), q < M.s i / 2 :=
    (eventually_lt_nhds (by linarith : (0:ℝ) < M.s i / 2)).filter_mono nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [Market.hS]; exact mul_nonneg (Finv_nonneg _ _) hq.1.le
  · filter_upwards [self_mem_nhdsWithin, hsmall] with q hq hq2
    simp only [Market.hS]
    apply mul_le_mul_of_nonneg_right _ hq.1.le
    apply Finv_mono _ _ hne
    rw [div_le_iff₀ hs]; linarith

lemma hS_contWithinS (M : Market S B) (hM : M.Standing) (i : S) (ht : (M.Fs i).vbar ≠ ⊤) :
    ContinuousWithinAt (M.hS i) (Set.Ioo 0 (M.s i)) (M.s i) := by
  have hs := hM.1.1 i
  have hD := hM.1.2.2.2.2.2.1 i
  obtain ⟨R, hR⟩ := WithTop.ne_top_iff_exists.mp ht
  unfold ContinuousWithinAt
  have hval : M.hS i (M.s i) = R * M.s i := by
    simp only [Market.hS]; rw [div_self hs.ne', Finv_one _ hD hR.symm]
  rw [hval]
  have h1 : Tendsto (fun q => q / M.s i) (𝓝[Set.Ioo 0 (M.s i)] (M.s i)) (𝓝[<] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun q => q / M.s i) (𝓝 (M.s i)) (𝓝 (M.s i / M.s i)) :=
        (continuous_id.div_const _).tendsto _
      rw [div_self hs.ne'] at this; exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (div_lt_one hs).mpr hq.2
  have h2 := (Finv_tendsto_one _ hD hR.symm).comp h1
  have h3 : Tendsto (fun q : ℝ => q) (𝓝[Set.Ioo 0 (M.s i)] (M.s i)) (𝓝 (M.s i)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  exact h2.mul h3

lemma gB_deriv_le (M : Market S B) (hM : M.Standing) (j : B) (ht : (M.Fb j).vbar ≠ ⊤) :
    ∀ q ∈ Set.Ioo 0 (M.b j), deriv (M.gB j) q ≤ (M.Fb j).Finv 1 := by
  intro q hq
  have hb := hM.1.2.1 j
  have hD := hM.1.2.2.2.2.2.2 j
  have hcc := gB_concaveOn M hM j (convex_Icc 0 q) (fun x hx => ⟨hx.1, hx.2.trans hq.2.le⟩)
  have := hcc.deriv_le_slope (Set.left_mem_Icc.mpr hq.1.le) (Set.right_mem_Icc.mpr hq.1.le) hq.1
    (gB_hasDerivAt M hM j hq).differentiableAt
  rw [slope_def_field, gB_zero, sub_zero, sub_zero] at this
  have e : M.gB j q / q = (M.Fb j).Finv (1 - q / M.b j) := by
    simp only [Market.gB]; field_simp [hq.1.ne']
  rw [e] at this
  refine this.trans (Finv_mono _ (by have := div_pos hq.1 hb; linarith)
    (Finv_set_nonempty' _ hD 1 le_rfl (Or.inr ht)))

lemma hS_deriv_nonneg (M : Market S B) (hM : M.Standing) (i : S) :
    ∀ q ∈ Set.Ioo 0 (M.s i), 0 ≤ deriv (M.hS i) q := by
  intro q hq
  have hcc := hS_convexOn M hM i (convex_Icc 0 q)
    (fun x hx => ⟨hx.1, hx.2.trans hq.2.le, fun _ => lt_of_le_of_lt hx.2 hq.2⟩)
  have := hcc.slope_le_deriv (Set.left_mem_Icc.mpr hq.1.le) (Set.right_mem_Icc.mpr hq.1.le) hq.1
    (hS_hasDerivAt M hM i hq).differentiableAt
  rw [slope_def_field, hS_zero, sub_zero, sub_zero] at this
  refine le_trans ?_ this
  simp only [Market.hS]
  exact div_nonneg (mul_nonneg (Finv_nonneg _ _) hq.1.le) hq.1.le

/-- one-sided data at the buyer's quantity -/
lemma buyer_data (M : Market S B) (hM : M.Standing) (j : B) (q : ℝ) (hq0 : 0 ≤ q)
    (hqb : q < M.b j) (hpos : 0 < q ∨ (M.Fb j).vbar ≠ ⊤) :
    ∃ a, Tendsto (deriv (M.gB j)) (𝓝[Set.Ioo 0 (M.b j)] q) (𝓝 a) ∧
      HasDerivWithinAt (M.gB j) a (Set.Ici q) q ∧ (0 < q → HasDerivAt (M.gB j) a q) := by
  have hb := hM.1.2.1 j
  rcases eq_or_lt_of_le hq0 with h0 | h0
  · subst h0
    have ht : (M.Fb j).vbar ≠ ⊤ := by
      rcases hpos with h | h
      · exact absurd h (lt_irrefl _)
      · exact h
    have hbdd : BddAbove (deriv (M.gB j) '' Set.Ioo 0 (M.b j)) :=
      ⟨(M.Fb j).Finv 1, by rintro _ ⟨q, hq, rfl⟩; exact gB_deriv_le M hM j ht q hq⟩
    have hlim := (gB_deriv_antitoneOn M hM j).tendsto_nhdsWithin_Ioo_right
      (Set.nonempty_Ioo.mpr hb) hbdd
    refine ⟨_, hlim.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Ioi_self), ?_,
      fun h => absurd h (lt_irrefl _)⟩
    exact hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun x hx => (gB_hasDerivAt M hM j hx).differentiableAt.differentiableWithinAt)
      (gB_contWithin0 M hM j ht) (Ioo_mem_nhdsGT hb) hlim
  · have hqI : q ∈ Set.Ioo 0 (M.b j) := ⟨h0, hqb⟩
    have hd := gB_hasDerivAt M hM j hqI
    refine ⟨deriv (M.gB j) q, ?_, ?_, fun _ => ?_⟩
    · exact ((gB_deriv_continuousAt M hM j hqI).tendsto).mono_left nhdsWithin_le_nhds
    · rw [hd.deriv]; exact hd.hasDerivWithinAt
    · rw [hd.deriv]; exact hd

lemma seller_data_lt (M : Market S B) (hM : M.Standing) (i : S) (q : ℝ) (hq0 : 0 ≤ q)
    (hqs : q < M.s i) :
    ∃ d, Tendsto (deriv (M.hS i)) (𝓝[Set.Ioo 0 (M.s i)] q) (𝓝 d) ∧
      HasDerivWithinAt (M.hS i) d (Set.Ici q) q ∧ (0 < q → HasDerivAt (M.hS i) d q) := by
  have hs := hM.1.1 i
  rcases eq_or_lt_of_le hq0 with h0 | h0
  · subst h0
    have hbdd : BddBelow (deriv (M.hS i) '' Set.Ioo 0 (M.s i)) :=
      ⟨0, by rintro _ ⟨q, hq, rfl⟩; exact hS_deriv_nonneg M hM i q hq⟩
    have hlim := (hS_deriv_monotoneOn M hM i).tendsto_nhdsWithin_Ioo_right
      (Set.nonempty_Ioo.mpr hs) hbdd
    refine ⟨_, hlim.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Ioi_self), ?_,
      fun h => absurd h (lt_irrefl _)⟩
    exact hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun x hx => (hS_hasDerivAt M hM i hx).differentiableAt.differentiableWithinAt)
      (hS_contWithin0 M hM i) (Ioo_mem_nhdsGT hs) hlim
  · have hqI : q ∈ Set.Ioo 0 (M.s i) := ⟨h0, hqs⟩
    have hd := hS_hasDerivAt M hM i hqI
    refine ⟨deriv (M.hS i) q, ?_, ?_, fun _ => ?_⟩
    · exact ((hS_deriv_continuousAt M hM i hqI).tendsto).mono_left nhdsWithin_le_nhds
    · rw [hd.deriv]; exact hd.hasDerivWithinAt
    · rw [hd.deriv]; exact hd

lemma seller_data_eq (M : Market S B) (hM : M.Standing) (i : S) (ht : (M.Fs i).vbar ≠ ⊤)
    (K : ℝ) (hK : ∀ q ∈ Set.Ioo 0 (M.s i), deriv (M.hS i) q ≤ K) :
    ∃ d, Tendsto (deriv (M.hS i)) (𝓝[Set.Ioo 0 (M.s i)] (M.s i)) (𝓝 d) ∧
      HasDerivWithinAt (M.hS i) d (Set.Iic (M.s i)) (M.s i) := by
  have hs := hM.1.1 i
  have hbdd : BddAbove (deriv (M.hS i) '' Set.Ioo 0 (M.s i)) :=
    ⟨K, by rintro _ ⟨q, hq, rfl⟩; exact hK q hq⟩
  have hlim := (hS_deriv_monotoneOn M hM i).tendsto_nhdsWithin_Ioo_left
    (Set.nonempty_Ioo.mpr hs) hbdd
  refine ⟨_, hlim.mono_left (nhdsWithin_mono _ Set.Ioo_subset_Iio_self), ?_⟩
  exact hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun x hx => (hS_hasDerivAt M hM i hx).differentiableAt.differentiableWithinAt)
    (hS_contWithinS M hM i ht) (Ioo_mem_nhdsLT hs) hlim

end NMAuxT



namespace NMAuxT
open NetworkedMarkets.Relaxation

lemma quot_of {f : ℝ → ℝ} {x a δ : ℝ} {T : Set ℝ} (h : HasDerivWithinAt f a T x) (hδ : δ ≠ 0)
    (hmaps : ∀ t : ℝ, 0 < t → x + t * δ ∈ T) :
    Tendsto (fun t => (f (x + t * δ) - f x) / t) (𝓝[>] 0) (𝓝 (a * δ)) := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at h
  have hl : Tendsto (fun t : ℝ => x + t * δ) (𝓝[>] 0) (𝓝[T \ {x}] x) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun t : ℝ => x + t * δ) (𝓝 0) (𝓝 (x + 0 * δ)) :=
        (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
      rw [zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine ⟨hmaps t ht, ?_⟩
      simp only [Set.mem_singleton_iff, add_eq_left]
      exact mul_ne_zero (ne_of_gt ht) hδ
  have h2 := (h.comp hl).mul_const δ
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp_apply, slope_def_field]
  have ht0 : t ≠ 0 := ne_of_gt ht
  rw [show x + t * δ - x = t * δ by ring]
  field_simp

lemma quot_zero {f : ℝ → ℝ} {x a : ℝ} :
    Tendsto (fun t => (f (x + t * 0) - f x) / t) (𝓝[>] 0) (𝓝 (a * 0)) := by
  simp

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma feas_dir (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hF : M.Feas7 x qs qb) (Δx : S → B → ℝ) (Δs : S → ℝ) (Δb : B → ℝ)
    (hbs : ∀ i, ∑ j ∈ M.nbrS i, Δx i j = Δs i) (hbb : ∀ j, ∑ i ∈ M.nbrB j, Δx i j = Δb j)
    (t : ℝ) (hx : ∀ i j, (i, j) ∈ M.E → 0 ≤ x i j + t * Δx i j)
    (hqb : ∀ j, qb j + t * Δb j ≤ M.b j) (hqs : ∀ i, qs i + t * Δs i ≤ M.s i)
    (htop : ∀ i, (M.Fs i).vbar = ⊤ → qs i + t * Δs i < M.s i) :
    M.Feas7 (fun i j => x i j + t * Δx i j) (fun i => qs i + t * Δs i)
      (fun j => qb j + t * Δb j) := by
  obtain ⟨a1, a2, -, -, -, -⟩ := hF
  refine ⟨fun j => ?_, fun i => ?_, hqb, hqs, hx, htop⟩
  · simp only; rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbb j]; linarith [a1 j]
  · simp only; rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbs i]; linarith [a2 i]

/-- First-order optimality condition along a feasible direction. -/
lemma first_order (M : Market S B) {x : S → B → ℝ} {qs : S → ℝ} {qb : B → ℝ}
    (hopt : M.IsOpt7 x qs qb) (a : B → ℝ) (d : S → ℝ)
    (Δx : S → B → ℝ) (Δs : S → ℝ) (Δb : B → ℝ)
    (hqB : ∀ j, Tendsto (fun t => (M.gB j (qb j + t * Δb j) - M.gB j (qb j)) / t) (𝓝[>] 0)
      (𝓝 (a j * Δb j)))
    (hqS : ∀ i, Tendsto (fun t => (M.hS i (qs i + t * Δs i) - M.hS i (qs i)) / t) (𝓝[>] 0)
      (𝓝 (d i * Δs i)))
    (t0 : ℝ) (ht0 : 0 < t0)
    (hfeas : ∀ t, 0 < t → t < t0 → M.Feas7 (fun i j => x i j + t * Δx i j)
      (fun i => qs i + t * Δs i) (fun j => qb j + t * Δb j)) :
    ∑ j, a j * Δb j - ∑ i, d i * Δs i - ∑ i, M.c i * Δs i ≤ 0 := by
  have hT : Tendsto (fun t => ∑ j, (M.gB j (qb j + t * Δb j) - M.gB j (qb j)) / t
      - ∑ i, (M.hS i (qs i + t * Δs i) - M.hS i (qs i)) / t - ∑ i, M.c i * Δs i) (𝓝[>] 0)
      (𝓝 (∑ j, a j * Δb j - ∑ i, d i * Δs i - ∑ i, M.c i * Δs i)) :=
    ((tendsto_finset_sum _ (fun j _ => hqB j)).sub (tendsto_finset_sum _ (fun i _ => hqS i))).sub
      tendsto_const_nhds
  apply le_of_tendsto hT
  filter_upwards [Ioo_mem_nhdsGT ht0] with t ht
  have hle := hopt.2 _ _ _ (hfeas t ht.1 ht.2)
  simp only [Market.h] at hle
  have e1 : ∑ j, (M.gB j (qb j + t * Δb j) - M.gB j (qb j)) / t =
      (∑ j, M.gB j (qb j + t * Δb j) - ∑ j, M.gB j (qb j)) / t := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
  have e2 : ∑ i, (M.hS i (qs i + t * Δs i) - M.hS i (qs i)) / t =
      (∑ i, M.hS i (qs i + t * Δs i) - ∑ i, M.hS i (qs i)) / t := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
  have e3 : ∑ i, M.c i * (qs i + t * Δs i) = ∑ i, M.c i * qs i + t * ∑ i, M.c i * Δs i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [e1, e2]
  rw [e3] at hle
  have htp := ht.1
  rw [div_sub_div_same, sub_nonpos, div_le_iff₀ htp]
  linarith

/-- edge directions -/
def edx (i0 : S) (j0 : B) : S → B → ℝ := fun i j => if i = i0 ∧ j = j0 then 1 else 0
def eds (i0 : S) : S → ℝ := fun i => if i = i0 then 1 else 0
def edb (j0 : B) : B → ℝ := fun j => if j = j0 then 1 else 0

lemma edx_bal_S (M : Market S B) {i0 : S} {j0 : B} (he : (i0, j0) ∈ M.E) (i : S) :
    ∑ j ∈ M.nbrS i, edx i0 j0 i j = eds i0 i := by
  have hj : j0 ∈ M.nbrS i0 := by simp [Market.nbrS, he]
  by_cases hi : i = i0
  · subst hi; simp [edx, eds, hj]
  · simp [edx, eds, hi]

lemma edx_bal_B (M : Market S B) {i0 : S} {j0 : B} (he : (i0, j0) ∈ M.E) (j : B) :
    ∑ i ∈ M.nbrB j, edx i0 j0 i j = edb j0 j := by
  have hi : i0 ∈ M.nbrB j0 := by simp [Market.nbrB, he]
  by_cases hj : j = j0
  · subst hj; simp [edx, edb, hi]
  · simp [edx, edb, hj]

end NMAuxT



namespace NMAuxT
open NetworkedMarkets.Relaxation
variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

lemma sum_edb (a : B → ℝ) (j : B) (σ : ℝ) : ∑ j', a j' * (σ * edb j j') = a j * σ := by
  simp [edb]

lemma sum_eds (a : S → ℝ) (i : S) (σ : ℝ) : ∑ i', a i' * (σ * eds i i') = a i * σ := by
  simp [eds]

theorem ec1iii (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : M.IsOpt7 x qs qb) :
    ∃ (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ),
      M.IsSpecialDual x qs qb θb θs ηb ηs π := by
  have hF := hopt.1
  obtain ⟨hs0, hb0, hc0, hnS, hnB, hFs, hFb⟩ := hM.1
  have hqblt := NetworkedMarkets.Relaxation.proposition_EC_1_v M hM x qs qb hopt
  have hqbpos : ∀ j, 0 < qb j ∨ (M.Fb j).vbar ≠ ⊤ := by
    intro j
    by_cases ht : (M.Fb j).vbar = ⊤
    · exact Or.inl (qb_pos_of_top M hM x qs qb hopt j ht)
    · exact Or.inr ht
  have hqb0 := feas_nonneg_qb M hF
  have hqs0 := feas_nonneg_qs M hF
  have hx0 : ∀ i j, (i, j) ∈ M.E → 0 ≤ x i j := hF.2.2.2.2.1
  have hsumS : ∀ i, qs i = ∑ j ∈ M.nbrS i, x i j := fun i => by linarith [hF.2.1 i]
  have hsumB : ∀ j, qb j = ∑ i ∈ M.nbrB j, x i j := fun j => by linarith [hF.1 j]
  have hxle_s : ∀ i j, (i, j) ∈ M.E → x i j ≤ qs i := fun i j he => by
    rw [hsumS i]
    exact Finset.single_le_sum (fun k hk => hx0 i k (by simpa [Market.nbrS] using hk))
      (by simp [Market.nbrS, he])
  have hxle_b : ∀ i j, (i, j) ∈ M.E → x i j ≤ qb j := fun i j he => by
    rw [hsumB j]
    exact Finset.single_le_sum (fun k hk => hx0 k j (by simpa [Market.nbrB] using hk))
      (by simp [Market.nbrB, he])
  -- buyer data
  choose a ha_T ha_R ha_L using fun j => buyer_data M hM j (qb j) (hqb0 j) (hqblt j) (hqbpos j)
  have qB : ∀ j δ, (δ < 0 → 0 < qb j) →
      Tendsto (fun t => (M.gB j (qb j + t * δ) - M.gB j (qb j)) / t) (𝓝[>] 0) (𝓝 (a j * δ)) := by
    intro j δ hδ
    rcases lt_trichotomy δ 0 with h | h | h
    · exact quot_of ((ha_L j (hδ h)).hasDerivWithinAt (s := Set.Iic (qb j))) h.ne
        (fun t ht => Set.mem_Iic.mpr (by nlinarith))
    · subst h; exact quot_zero
    · exact quot_of (ha_R j) h.ne' (fun t ht => Set.mem_Ici.mpr (by nlinarith))
  -- seller bound at full capacity
  have hbound : ∀ i, qs i = M.s i → ∃ K, ∀ q ∈ Set.Ioo 0 (M.s i), deriv (M.hS i) q ≤ K := by
    intro i hfull
    have ht : (M.Fs i).vbar ≠ ⊤ := fun ht => by have := hF.2.2.2.2.2 i ht; linarith
    obtain ⟨j, hj, hxj⟩ : ∃ j ∈ M.nbrS i, 0 < x i j := by
      by_contra hc; push Not at hc
      have : ∑ j ∈ M.nbrS i, x i j ≤ 0 := Finset.sum_nonpos hc
      linarith [hsumS i, hs0 i]
    have hjE : (i, j) ∈ M.E := by simpa [Market.nbrS] using hj
    have hqbj : 0 < qb j := lt_of_lt_of_le hxj (hxle_b i j hjE)
    refine ⟨a j - M.c i + 1, fun q0 hq0 => ?_⟩
    by_contra hcon; push Not at hcon
    have hq := qB j (-1) (fun _ => hqbj)
    have hev1 := hq.eventually (lt_mem_nhds (by linarith : a j * -1 - 1 < a j * -1))
    have hev2 : Set.Ioo (0:ℝ) (min (x i j) (M.s i - q0)) ∈ 𝓝[>] (0:ℝ) :=
      Ioo_mem_nhdsGT (lt_min hxj (by linarith [hq0.2]))
    obtain ⟨t, ht1, ht2⟩ := (hev1.and hev2).exists
    have htx : t < x i j := lt_of_lt_of_le ht2.2 (min_le_left _ _)
    have hts : t < M.s i - q0 := lt_of_lt_of_le ht2.2 (min_le_right _ _)
    have htp := ht2.1
    -- feasibility of the decrease
    have hfe := feas_dir M hF (fun i' j' => (-1) * edx i j i' j') (fun i' => (-1) * eds i i')
      (fun j' => (-1) * edb j j')
      (fun i' => by rw [← Finset.mul_sum, edx_bal_S M hjE])
      (fun j' => by rw [← Finset.mul_sum, edx_bal_B M hjE]) t
      (fun i' j' he => by
        simp only [edx]; split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; linarith
        · linarith [hx0 i' j' he])
      (fun j' => by simp only [edb]; split_ifs <;> linarith [hF.2.2.1 j'])
      (fun i' => by simp only [eds]; split_ifs <;> linarith [hF.2.2.2.1 i'])
      (fun i' hti => by simp only [eds]; split_ifs <;> linarith [hF.2.2.2.2.2 i' hti])
    have hle := hopt.2 _ _ _ hfe
    simp only [Market.h] at hle
    have hg : ∑ k, M.gB k (qb k + t * ((-1) * edb j k)) - ∑ k, M.gB k (qb k) =
        M.gB j (qb j + t * (-1)) - M.gB j (qb j) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
      · simp [edb]
      · intro k _ hk; simp [edb, hk]
      · simp
    have hs : ∑ k, M.hS k (qs k + t * ((-1) * eds i k)) - ∑ k, M.hS k (qs k) =
        M.hS i (qs i + t * (-1)) - M.hS i (qs i) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · simp [eds]
      · intro k _ hk; simp [eds, hk]
      · simp
    have hc : ∑ k, M.c k * (qs k + t * ((-1) * eds i k)) - ∑ k, M.c k * qs k = -(M.c i * t) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · simp [eds]; ring
      · intro k _ hk; simp [eds, hk]
      · simp
    -- convexity of h_i near s_i
    have hcv := hS_convexOn M hM i (convex_Icc 0 (M.s i))
      (fun q hq => ⟨hq.1, hq.2, fun h => absurd h ht⟩)
    have hst : M.s i - t ∈ Set.Ioo 0 (M.s i) := ⟨by linarith [hq0.1], by linarith⟩
    have hd1 := hcv.deriv_le_slope (x := M.s i - t) (y := M.s i) ⟨hst.1.le, hst.2.le⟩
      ⟨(hs0 i).le, le_rfl⟩ hst.2 (hS_hasDerivAt M hM i hst).differentiableAt
    rw [slope_def_field, show M.s i - (M.s i - t) = t by ring] at hd1
    have hd2 := hS_deriv_monotoneOn M hM i hq0 hst (by linarith)
    have hd3 : t * (a j - M.c i + 1) < M.hS i (M.s i) - M.hS i (M.s i - t) := by
      rw [le_div_iff₀ htp] at hd1
      nlinarith
    have hq1 : (M.gB j (qb j + t * -1) - M.gB j (qb j)) / t > a j * -1 - 1 := ht1
    rw [gt_iff_lt, lt_div_iff₀ htp] at hq1
    rw [hfull] at hs
    have e1 : M.s i + t * (-1) = M.s i - t := by ring
    rw [e1] at hs
    linarith
  -- seller data
  have hsd : ∀ i, ∃ d, Tendsto (deriv (M.hS i)) (𝓝[Set.Ioo 0 (M.s i)] (qs i)) (𝓝 d) ∧
      (qs i < M.s i → HasDerivWithinAt (M.hS i) d (Set.Ici (qs i)) (qs i)) ∧
      (0 < qs i → HasDerivWithinAt (M.hS i) d (Set.Iic (qs i)) (qs i)) := by
    intro i
    rcases lt_or_eq_of_le (hF.2.2.2.1 i) with hlt | heq
    · obtain ⟨d, h1, h2, h3⟩ := seller_data_lt M hM i (qs i) (hqs0 i) hlt
      exact ⟨d, h1, fun _ => h2, fun h => (h3 h).hasDerivWithinAt⟩
    · have ht : (M.Fs i).vbar ≠ ⊤ := fun ht => by have := hF.2.2.2.2.2 i ht; linarith
      obtain ⟨K, hK⟩ := hbound i heq
      obtain ⟨d, h1, h2⟩ := seller_data_eq M hM i ht K hK
      rw [heq]
      exact ⟨d, h1, fun h => absurd h (lt_irrefl _), fun _ => h2⟩
  choose d hd_T hd_R hd_L using hsd
  have qS : ∀ i δ, (0 < δ → qs i < M.s i) → (δ < 0 → 0 < qs i) →
      Tendsto (fun t => (M.hS i (qs i + t * δ) - M.hS i (qs i)) / t) (𝓝[>] 0) (𝓝 (d i * δ)) := by
    intro i δ hδ1 hδ2
    rcases lt_trichotomy δ 0 with h | h | h
    · exact quot_of (hd_L i (hδ2 h)) h.ne (fun t ht => Set.mem_Iic.mpr (by nlinarith))
    · subst h; exact quot_zero
    · exact quot_of (hd_R i (hδ1 h)) h.ne' (fun t ht => Set.mem_Ici.mpr (by nlinarith))
  -- (F1) increasing an edge out of a non-saturated seller
  have F1 : ∀ i j, (i, j) ∈ M.E → qs i < M.s i → a j ≤ d i + M.c i := by
    intro i j hE hlt
    have hfo := first_order M hopt a d (fun i' j' => 1 * edx i j i' j') (fun i' => 1 * eds i i')
      (fun j' => 1 * edb j j')
      (fun j' => qB j' _ (fun h => by simp [edb] at h; split_ifs at h <;> linarith))
      (fun i' => qS i' _ (fun h => by
          simp only [eds] at h; split_ifs at h with hi
          · subst hi; exact hlt
          · linarith)
        (fun h => by simp [eds] at h; split_ifs at h <;> linarith))
      (min (M.s i - qs i) (M.b j - qb j)) (lt_min (by linarith) (by linarith [hqblt j]))
      (fun t ht ht' => feas_dir M hF _ _ _
        (fun i' => by rw [← Finset.mul_sum, edx_bal_S M hE])
        (fun j' => by rw [← Finset.mul_sum, edx_bal_B M hE]) t
        (fun i' j' he => by simp only [edx]; split_ifs <;> nlinarith [hx0 i' j' he])
        (fun j' => by
          have := min_le_right (M.s i - qs i) (M.b j - qb j)
          simp only [edb]; split_ifs with h
          · subst h; linarith
          · linarith [hF.2.2.1 j'])
        (fun i' => by
          have := min_le_left (M.s i - qs i) (M.b j - qb j)
          simp only [eds]; split_ifs with h
          · subst h; linarith
          · linarith [hF.2.2.2.1 i'])
        (fun i' hti => by
          have := min_le_left (M.s i - qs i) (M.b j - qb j)
          simp only [eds]; split_ifs with h
          · subst h; linarith
          · linarith [hF.2.2.2.2.2 i' hti]))
    rw [sum_edb, sum_eds, sum_eds] at hfo
    linarith
  -- (F2) decreasing an edge carrying flow
  have F2 : ∀ i j, (i, j) ∈ M.E → 0 < x i j → d i + M.c i ≤ a j := by
    intro i j hE hx
    have hqbj : 0 < qb j := lt_of_lt_of_le hx (hxle_b i j hE)
    have hqsi : 0 < qs i := lt_of_lt_of_le hx (hxle_s i j hE)
    have hfo := first_order M hopt a d (fun i' j' => (-1) * edx i j i' j')
      (fun i' => (-1) * eds i i') (fun j' => (-1) * edb j j')
      (fun j' => qB j' _ (fun h => by
          simp only [edb] at h; split_ifs at h with hj
          · subst hj; exact hqbj
          · linarith))
      (fun i' => qS i' _ (fun h => by simp [eds] at h; split_ifs at h <;> linarith)
        (fun h => by
          simp only [eds] at h; split_ifs at h with hi
          · subst hi; exact hqsi
          · linarith))
      (x i j) hx
      (fun t ht ht' => feas_dir M hF _ _ _
        (fun i' => by rw [← Finset.mul_sum, edx_bal_S M hE])
        (fun j' => by rw [← Finset.mul_sum, edx_bal_B M hE]) t
        (fun i' j' he => by
          simp only [edx]; split_ifs with h
          · obtain ⟨rfl, rfl⟩ := h; linarith
          · linarith [hx0 i' j' he])
        (fun j' => by simp only [edb]; split_ifs <;> linarith [hF.2.2.1 j'])
        (fun i' => by simp only [eds]; split_ifs <;> linarith [hF.2.2.2.1 i'])
        (fun i' hti => by simp only [eds]; split_ifs <;> linarith [hF.2.2.2.2.2 i' hti]))
    rw [sum_edb, sum_eds, sum_eds] at hfo
    linarith
  -- (F3) exchange at a seller
  have F3 : ∀ i j j', (i, j) ∈ M.E → (i, j') ∈ M.E → 0 < x i j → a j' ≤ a j := by
    intro i j j' hE hE' hx
    by_cases hjj : j' = j
    · rw [hjj]
    have hqbj : 0 < qb j := lt_of_lt_of_le hx (hxle_b i j hE)
    have hfo := first_order M hopt a d (fun i' k => edx i j' i' k - edx i j i' k)
      (fun i' => eds i i' - eds i i') (fun k => edb j' k - edb j k)
      (fun k => qB k _ (fun h => by
          simp only [edb] at h; split_ifs at h with h1 h2 h2
          · exact absurd (h1.symm.trans h2) hjj
          · linarith
          · subst h2; exact hqbj
          · linarith))
      (fun i' => qS i' _ (fun h => by simp at h) (fun h => by simp at h))
      (min (x i j) (M.b j' - qb j')) (lt_min hx (by linarith [hqblt j']))
      (fun t ht ht' => feas_dir M hF _ _ _
        (fun i' => by rw [Finset.sum_sub_distrib, edx_bal_S M hE', edx_bal_S M hE])
        (fun k => by rw [Finset.sum_sub_distrib, edx_bal_B M hE', edx_bal_B M hE]) t
        (fun i' k he => by
          have h1 := min_le_left (x i j) (M.b j' - qb j')
          simp only [edx]; split_ifs with ha hb hb
          · exact absurd (ha.2.symm.trans hb.2) hjj
          · linarith [hx0 i' k he]
          · obtain ⟨rfl, rfl⟩ := hb; linarith
          · linarith [hx0 i' k he])
        (fun k => by
          have h1 := min_le_right (x i j) (M.b j' - qb j')
          simp only [edb]; split_ifs with ha hb hb
          · exact absurd (ha.symm.trans hb) hjj
          · subst ha; linarith
          · linarith [hF.2.2.1 k]
          · linarith [hF.2.2.1 k])
        (fun i' => by simp; exact hF.2.2.2.1 i')
        (fun i' hti => by simp; exact hF.2.2.2.2.2 i' hti))
    simp only [mul_sub, Finset.sum_sub_distrib, sub_self, mul_zero, Finset.sum_const_zero] at hfo
    have e1 : ∑ k, a k * edb j' k = a j' := by simp [edb]
    have e2 : ∑ k, a k * edb j k = a j := by simp [edb]
    rw [e1, e2] at hfo
    linarith
  -- the dual vector
  classical
  set A : S → ℝ := fun i => (M.nbrS i).sup' (hnS i) a with hA
  set θs : S → ℝ := fun i => if qs i < M.s i then d i else A i - M.c i with hθs
  refine ⟨a, θs, fun _ => 0, fun i => θs i - d i, fun i j => θs i + M.c i - a j, ?_⟩
  have hAge : ∀ i j, (i, j) ∈ M.E → a j ≤ A i := fun i j hE =>
    Finset.le_sup' a (by simp [Market.nbrS, hE])
  refine ⟨fun j => by simpa using ha_T j, fun i => by simpa using hd_T i,
    fun i j hE => by ring, fun j => ⟨hF.2.2.1 j, le_rfl, by ring⟩, fun i => ?_, fun i j hE => ?_,
    fun j => (hsumB j).symm, fun i => (hsumS i).symm⟩
  · refine ⟨hF.2.2.2.1 i, ?_, ?_⟩
    · simp only [hθs]
      split_ifs with h
      · simp
      · have heq : qs i = M.s i := le_antisymm (hF.2.2.2.1 i) (not_lt.mp h)
        obtain ⟨j, hj, hxj⟩ : ∃ j ∈ M.nbrS i, 0 < x i j := by
          by_contra hc; push Not at hc
          have : ∑ j ∈ M.nbrS i, x i j ≤ 0 := Finset.sum_nonpos hc
          linarith [hsumS i, hs0 i]
        have hjE : (i, j) ∈ M.E := by simpa [Market.nbrS] using hj
        linarith [F2 i j hjE hxj, hAge i j hjE]
    · simp only [hθs]
      split_ifs with h
      · simp
      · have heq : qs i = M.s i := le_antisymm (hF.2.2.2.1 i) (not_lt.mp h)
        rw [heq]; ring
  · refine ⟨hx0 i j hE, ?_, ?_⟩
    · simp only [hθs]
      split_ifs with h
      · linarith [F1 i j hE h]
      · linarith [hAge i j hE]
    · rcases eq_or_lt_of_le (hx0 i j hE) with h0 | h0
      · rw [← h0]; ring
      · have : θs i + M.c i - a j = 0 := by
          simp only [hθs]
          split_ifs with h
          · linarith [F1 i j hE h, F2 i j hE h0]
          · have : A i ≤ a j := Finset.sup'_le _ _ (fun j' hj' =>
              F3 i j j' hE (by simpa [Market.nbrS] using hj') h0)
            linarith [hAge i j hE]
        show (θs i + M.c i - a j) * x i j = 0
        rw [this]; ring

end NMAuxT

open NetworkedMarkets.Relaxation NMAuxT in
theorem solution {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : M.IsOpt7 x qs qb) :
    ∃ (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ),
      M.IsSpecialDual x qs qb θb θs ηb ηs π :=
  ec1iii M hM x qs qb hopt

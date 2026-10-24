-- Prove2me | solution 1 for LPCommunity.SBMDense.theorem_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T09:38:11.37542+00:00
-- url     : https://prove2.me/submissions/94992ed8-54ea-40a8-9e91-ad26c3384491
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs
import Definitions.Def_LPCommunity_SBMDense_Thresholds
import Theorems.Thm_LPCommunity_LPFail_theorem_5
import Theorems.Thm_LPCommunity_SBMDense_display_26
import Theorems.Thm_LPCommunity_SBMDense_proposition_16
import Theorems.Thm_LPCommunity_SBMDense_proposition_17
import Theorems.Thm_LPCommunity_SBMDense_proposition_18

open Finset
open scoped Classical

namespace LPC7Aux

open LPCommunity.SBMRecovery

/-- graphs on `Fin n` are the same as Boolean functions on the pairs `i < j`. -/
noncomputable def graphEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ pairs n} → Bool) where
  toFun G := fun p => decide (G.Adj p.1.1 p.1.2)
  invFun g :=
    { Adj := fun i j => (∃ h : (i, j) ∈ pairs n, g ⟨(i, j), h⟩ = true) ∨
          (∃ h : (j, i) ∈ pairs n, g ⟨(j, i), h⟩ = true)
      symm := ⟨fun _ _ h => Or.symm h⟩
      loopless := ⟨fun i h => by
        rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [pairs] at h⟩ }
  left_inv G := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · have h1 : (i, j) ∈ pairs n := by simp [pairs, hij]
      have h2 : (j, i) ∉ pairs n := by simp [pairs, hij.le]
      constructor
      · rintro (⟨h, hg⟩ | ⟨h, hg⟩)
        · simpa using hg
        · exact absurd h h2
      · intro hG; exact Or.inl ⟨h1, by simpa using hG⟩
    · simp [pairs]
    · have h1 : (j, i) ∈ pairs n := by simp [pairs, hij]
      have h2 : (i, j) ∉ pairs n := by simp [pairs, hij.le]
      constructor
      · rintro (⟨h, hg⟩ | ⟨h, hg⟩)
        · exact absurd h h2
        · simpa [G.adj_comm] using hg
      · intro hG; exact Or.inr ⟨h1, by simpa [G.adj_comm] using hG⟩
  right_inv g := by
    funext ⟨⟨i, j⟩, h⟩
    have hij : i < j := by simpa [pairs] using h
    have h2 : (j, i) ∉ pairs n := by simp [pairs, hij.le]
    simp only
    cases hg : g ⟨(i, j), h⟩
    · simp only [decide_eq_false_iff_not]
      rintro (⟨h', hg'⟩ | ⟨h', _⟩)
      · rw [hg] at hg'; exact Bool.false_ne_true hg'
      · exact h2 h'
    · simp only [decide_eq_true_eq]
      exact Or.inl ⟨h, hg⟩

lemma edgeWeight_sum {n : ℕ} (r : Fin n → Fin n → ℝ) :
    ∑ G : SimpleGraph (Fin n), edgeWeight G r = 1 := by
  set f : {p : Fin n × Fin n // p ∈ pairs n} → Bool → ℝ :=
    fun p b => if b then clamp01 (r p.1.1 p.1.2) else 1 - clamp01 (r p.1.1 p.1.2) with hf
  have h1 : ∏ i, ∑ b ∈ (univ : Finset Bool), f i b = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp [hf]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ] at h1
  rw [← h1]
  refine Fintype.sum_equiv (graphEquiv n) _ _ (fun G => ?_)
  unfold edgeWeight
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp [hf, graphEquiv]

lemma edgeWeight_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n → Fin n → ℝ) :
    0 ≤ edgeWeight G r := by
  unfold edgeWeight
  apply Finset.prod_nonneg
  intro p _
  have h0 : 0 ≤ clamp01 (r p.1 p.2) := le_max_left _ _
  have h1 : clamp01 (r p.1 p.2) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  split_ifs <;> linarith

lemma bisections_nonempty (m : ℕ) : (bisections (2 * m)).Nonempty := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (univ : Finset (Fin (2 * m))))
    (n := m) (by simp; omega)
  exact ⟨S, by simp [bisections, LPCommunity.MinBisect.IsBisection, hS]⟩

lemma sbmProb_true (m : ℕ) (p q : ℝ) :
    sbmProb (2 * m) p q (fun _ _ => True) = 1 := by
  unfold sbmProb
  simp only [if_true, mul_one, edgeWeight_sum, Finset.sum_const, nsmul_eq_mul]
  have : ((bisections (2 * m)).card : ℝ) ≠ 0 := by
    exact_mod_cast (bisections_nonempty m).card_pos.ne'
  field_simp

lemma sbmProb_mono {n : ℕ} (p q : ℝ) (E F : Finset (Fin n) → SimpleGraph (Fin n) → Prop)
    (h : ∀ V1 ∈ bisections n, ∀ G, E V1 G → F V1 G) :
    sbmProb n p q E ≤ sbmProb n p q F := by
  unfold sbmProb
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro V1 hV1
  apply Finset.sum_le_sum
  intro G _
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  by_cases hE : E V1 G
  · simp [hE, h V1 hV1 G hE]
  · simp only [hE, if_false]; split_ifs <;> norm_num

lemma sbmProb_le_one (m : ℕ) (p q : ℝ) (E : Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop) :
    sbmProb (2 * m) p q E ≤ 1 := by
  rw [← sbmProb_true m p q]
  exact sbmProb_mono p q _ _ (fun _ _ _ _ => trivial)

lemma sbmProb_or_le {n : ℕ} (p q : ℝ) (E F : Finset (Fin n) → SimpleGraph (Fin n) → Prop) :
    sbmProb n p q (fun V G => E V G ∨ F V G) ≤ sbmProb n p q E + sbmProb n p q F := by
  unfold sbmProb
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro V1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro G _
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (edgeWeight_nonneg _ _)
  split_ifs <;> simp_all

lemma sbmProb_compl {n : ℕ} (p q : ℝ) (E : Finset (Fin n) → SimpleGraph (Fin n) → Prop) :
    sbmProb n p q E + sbmProb n p q (fun V G => ¬ E V G) = sbmProb n p q (fun _ _ => True) := by
  unfold sbmProb
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun V1 _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun G _ => ?_)
  by_cases h : E V1 G <;> simp [h]

lemma tendsto_and {p q : ℕ → ℝ}
    (E F : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop)
    (hE : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m)) Filter.atTop (nhds 1))
    (hF : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (F m)) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (fun V G => E m V G ∧ F m V G))
      Filter.atTop (nhds 1) := by
  have key : ∀ m, sbmProb (2 * m) (p m) (q m) (E m) + sbmProb (2 * m) (p m) (q m) (F m) - 1 ≤
      sbmProb (2 * m) (p m) (q m) (fun V G => E m V G ∧ F m V G) := by
    intro m
    have h1 := sbmProb_compl (p m) (q m) (E m)
    have h2 := sbmProb_compl (p m) (q m) (F m)
    have h3 := sbmProb_compl (p m) (q m) (fun V G => E m V G ∧ F m V G)
    have h4 := sbmProb_or_le (p m) (q m) (fun V G => ¬ E m V G) (fun V G => ¬ F m V G)
    have h5 : sbmProb (2 * m) (p m) (q m) (fun V G => ¬ (E m V G ∧ F m V G)) ≤
        sbmProb (2 * m) (p m) (q m) (fun V G => ¬ E m V G ∨ ¬ F m V G) :=
      sbmProb_mono _ _ _ _ (fun V _ G h => by tauto)
    rw [sbmProb_true] at h1 h2 h3
    linarith
  have hlow : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m) +
      sbmProb (2 * m) (p m) (q m) (F m) - 1) Filter.atTop (nhds 1) := by
    have := (hE.add hF).sub_const 1
    norm_num at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds key
    (fun m => sbmProb_le_one m _ _ _)

lemma tendsto_of_imp {p q : ℕ → ℝ}
    (E F : (m : ℕ) → Finset (Fin (2 * m)) → SimpleGraph (Fin (2 * m)) → Prop)
    (hE : Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (E m)) Filter.atTop (nhds 1))
    (hEF : ∀ᶠ m in Filter.atTop, ∀ V1 ∈ bisections (2 * m), ∀ G, E m V1 G → F m V1 G) :
    Filter.Tendsto (fun m => sbmProb (2 * m) (p m) (q m) (F m)) Filter.atTop (nhds 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hE tendsto_const_nhds ?_
    (Filter.Eventually.of_forall (fun m => sbmProb_le_one m _ _ _))
  filter_upwards [hEF] with m hm
  exact sbmProb_mono _ _ _ _ hm

end LPC7Aux

open Finset
open scoped Classical ENNReal

namespace LPC7Aux

lemma b_bound (n R a aL t : ℝ) (hn : 5 ≤ n) (hR1 : 1 ≤ R) (haL : 0 < aL) (ha : aL ≤ a)
    (h1 : 1 / (2 * aL) < t)
    (h2 : 3 * R ≤ 4 * aL ∨ ((1 - 4 / n) + 3 * R - 4 * aL) / (6 * ((1 - 1 / n) * R - aL)) < t) :
    (1 + max 0 ((3 * R - 4 * a) / (1 - 4 / n))) /
      (2 * a + 2 * max 0 ((3 * R - 4 * a) / (1 - 4 / n)) * (1 - 1 / n)) < t := by
  have hn0 : 0 < n := by linarith
  set u := 1 / n with hu
  have h4 : 4 / n = 4 * u := by rw [hu]; ring
  rw [h4] at h2 ⊢
  have hu0 : 0 < u := by positivity
  have hu5 : u ≤ 1 / 5 := by rw [hu]; exact one_div_le_one_div_of_le (by norm_num) hn
  have hd : 0 < 1 - 4 * u := by linarith
  have ha0 : 0 < a := by linarith
  rcases le_or_gt (3 * R - 4 * a) 0 with hc | hc
  · have : max 0 ((3 * R - 4 * a) / (1 - 4 * u)) = 0 :=
      max_eq_left (div_nonpos_of_nonpos_of_nonneg hc hd.le)
    rw [this]
    simp only [add_zero, mul_zero, zero_mul]
    calc (1 : ℝ) / (2 * a) ≤ 1 / (2 * aL) := by gcongr
      _ < t := h1
  · have hpos : 0 < (3 * R - 4 * a) / (1 - 4 * u) := div_pos hc hd
    rw [max_eq_right hpos.le]
    have h2' : ((1 - 4 * u) + 3 * R - 4 * aL) / (6 * ((1 - u) * R - aL)) < t := by
      rcases h2 with h2 | h2
      · exfalso; linarith
      · exact h2
    refine lt_of_le_of_lt ?_ h2'
    have hka : 0 < (1 - u) * R - a := by nlinarith
    have hkaL : 0 < (1 - u) * R - aL := by linarith
    have heq : (1 + (3 * R - 4 * a) / (1 - 4 * u)) /
        (2 * a + 2 * ((3 * R - 4 * a) / (1 - 4 * u)) * (1 - u)) =
        ((1 - 4 * u) + 3 * R - 4 * a) / (6 * ((1 - u) * R - a)) := by
      have hd' : (1 - 4 * u) ≠ 0 := hd.ne'
      have e1 : 1 + (3 * R - 4 * a) / (1 - 4 * u) = ((1 - 4 * u) + 3 * R - 4 * a) / (1 - 4 * u) := by
        field_simp; ring
      have e2 : 2 * a + 2 * ((3 * R - 4 * a) / (1 - 4 * u)) * (1 - u) =
          6 * ((1 - u) * R - a) / (1 - 4 * u) := by
        field_simp; ring
      rw [e1, e2, div_div_div_cancel_right₀ hd']
    rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hR1)) hd.le]

open LPCommunity.LPFail in
lemma det_not_recovers {n : ℕ} (hn : 5 ≤ n) (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (R aL t : ℝ) (hR1 : 1 ≤ R) (haL : 0 < aL)
    (ht : 0 < t)
    (hmax : ((rhoMax G : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal R)
    (havg1 : ENNReal.ofReal aL ≤ rhoAvg G) (havg2 : rhoAvg G ≤ ((rhoMax G : ℕ∞) : ℝ≥0∞))
    (hcut : t ≤ (LPCommunity.MinBisect.cutCost G V1 : ℝ) / (G.edgeFinset.card : ℝ))
    (h1 : 1 / (2 * aL) < t)
    (h2 : 3 * R ≤ 4 * aL ∨
      ((1 - 4 / (n : ℝ)) + 3 * R - 4 * aL) / (6 * ((1 - 1 / (n : ℝ)) * R - aL)) < t) :
    ¬ LPCommunity.LPRecovery.LPRecovers G V1 := by
  have hne : ((rhoMax G : ℕ∞) : ℝ≥0∞) ≠ ⊤ := by rw [hmax]; exact ENNReal.ofReal_ne_top
  have hne' : G.ediam ≠ ⊤ := by
    intro h; apply hne; simp [rhoMax, h]
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hconn : G.Connected := G.connected_of_ediam_ne_top hne'
  have hRv : ((rhoMax G : ℕ∞) : ℝ≥0∞).toReal = R := by
    rw [hmax, ENNReal.toReal_ofReal (by linarith)]
  have hane : rhoAvg G ≠ ⊤ := ne_top_of_le_ne_top hne havg2
  have haL' : aL ≤ (rhoAvg G).toReal := (ENNReal.ofReal_le_iff_le_toReal hane).1 havg1
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := b_bound n R (rhoAvg G).toReal aL t hn' hR1 haL haL' h1 h2
  apply theorem_5 G V1 hV1 hconn hn
  have hcG : cG G = max 0 ((3 * R - 4 * (rhoAvg G).toReal) / (1 - 4 / (n : ℝ))) := by
    rw [cG, hRv]
  rw [hcG]
  have hE : (0 : ℝ) < (G.edgeFinset.card : ℝ) := by
    by_contra hc
    have h0 : (G.edgeFinset.card : ℝ) = 0 := le_antisymm (not_lt.1 hc) (Nat.cast_nonneg _)
    rw [h0, div_zero] at hcut
    linarith
  rw [le_div_iff₀ hE] at hcut
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hb hE) hcut

end LPC7Aux

open Filter Topology

namespace LPC7Aux

lemma exists_eps (L R t0 : ℝ) (hL : 0 < L) (hR : 1 ≤ R) (ht0 : 0 < t0)
    (hb1 : 1 / (2 * L) < t0)
    (hb2 : 3 * R < 4 * L ∨ (L < R ∧ (1 + 3 * R - 4 * L) / (6 * (R - L)) < t0)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n : ℕ in atTop,
      1 / (2 * ((1 - ε) * L)) < (1 - ε) * t0 ∧
      (3 * R ≤ 4 * ((1 - ε) * L) ∨
        ((1 - 4 / (n : ℝ)) + 3 * R - 4 * ((1 - ε) * L)) /
          (6 * ((1 - 1 / (n : ℝ)) * R - (1 - ε) * L)) < (1 - ε) * t0) := by
  have c1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 / (2 * ((1 - ε) * L)) < (1 - ε) * t0 := by
    apply ContinuousAt.eventually_lt
    · apply ContinuousAt.div continuousAt_const (by fun_prop) (by simp; exact hL.ne')
    · fun_prop
    · simpa using hb1
  have c2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 :=
    eventually_lt_nhds (by norm_num)
  have pick : ∀ P : ℝ → Prop, (∀ᶠ ε in 𝓝 (0 : ℝ), P ε) → ∃ ε, 0 < ε ∧ P ε := by
    intro P hP
    exact ((hP.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi 0))).exists
      |>.imp fun ε h => ⟨h.2, h.1⟩
  rcases hb2 with hA | ⟨hLR, hB⟩
  · have c3 : ∀ᶠ ε in 𝓝 (0 : ℝ), 3 * R < 4 * ((1 - ε) * L) := by
      apply ContinuousAt.eventually_lt continuousAt_const (by fun_prop)
      simpa using hA
    obtain ⟨ε, hε, h1, h2, h3⟩ := pick _ (c1.and (c2.and c3))
    exact ⟨ε, hε, h2, Eventually.of_forall fun _ => ⟨h1, Or.inl h3.le⟩⟩
  · have c3 : ∀ᶠ ε in 𝓝 (0 : ℝ),
        (1 + 3 * R - 4 * ((1 - ε) * L)) / (6 * (R - (1 - ε) * L)) < (1 - ε) * t0 := by
      apply ContinuousAt.eventually_lt
      · apply ContinuousAt.div (by fun_prop) (by fun_prop)
        simp; linarith
      · fun_prop
      · simpa using hB
    obtain ⟨ε, hε, h1, h2, h3⟩ := pick _ (c1.and (c2.and c3))
    refine ⟨ε, hε, h2, ?_⟩
    have hpos : R - (1 - ε) * L ≠ 0 := by nlinarith
    have hlim : Tendsto (fun n : ℕ => ((1 - 4 / (n : ℝ)) + 3 * R - 4 * ((1 - ε) * L)) /
        (6 * ((1 - 1 / (n : ℝ)) * R - (1 - ε) * L))) atTop
        (𝓝 ((1 + 3 * R - 4 * ((1 - ε) * L)) / (6 * (R - (1 - ε) * L)))) := by
      have hu := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
      have e : (fun n : ℕ => ((1 - 4 / (n : ℝ)) + 3 * R - 4 * ((1 - ε) * L)) /
          (6 * ((1 - 1 / (n : ℝ)) * R - (1 - ε) * L))) =
          (fun n : ℕ => ((1 - 4 * (1 / (n : ℝ))) + 3 * R - 4 * ((1 - ε) * L)) /
          (6 * ((1 - 1 / (n : ℝ)) * R - (1 - ε) * L))) := by
        funext n; ring
      rw [e]
      have := ((((tendsto_const_nhds (x := (1:ℝ))).sub (hu.const_mul 4)).add_const (3 * R)).sub_const
        (4 * ((1 - ε) * L))).div
        (Tendsto.const_mul 6 ((((tendsto_const_nhds (x := (1:ℝ))).sub hu).mul_const R).sub_const ((1 - ε) * L)))
        (by simpa using mul_ne_zero (by norm_num : (6:ℝ) ≠ 0) hpos)
      simp only [mul_zero, sub_zero, one_mul] at this
      exact this
    filter_upwards [hlim.eventually_lt_const h3] with n hn
    exact ⟨h1, Or.inr hn⟩

end LPC7Aux

open Finset Filter Topology
open scoped Classical ENNReal

namespace LPC7Aux

open LPCommunity.SBMDense LPCommunity.SBMRecovery LPCommunity.LPFail

lemma dense_hyps (α β ω : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α) (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (hdense : ω = 0 → α < 1 ∧ β < 1) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * Real.log n / n ≤ denseRegime α ω n ∧ c * Real.log n / n ≤ denseRegime β ω n) ∧
    (∀ᶠ n : ℕ in atTop, denseRegime α ω n ≤ 1 ∧ denseRegime β ω n ≤ 1) ∧
    Tendsto (fun n : ℕ => denseRegime β ω n / denseRegime α ω n) atTop (𝓝 (β / α)) := by
  have hev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ n :=
    (eventually_ge_atTop 1).mono fun n hn => by exact_mod_cast hn
  refine ⟨⟨β, hβ, ?_⟩, ?_, ?_⟩
  · have hlo := (isLittleO_log_rpow_atTop (sub_pos.2 hω1)).bound (c := 1) one_pos
    have hlo' := tendsto_natCast_atTop_atTop.eventually hlo
    filter_upwards [hlo', hev1] with n hn hn1
    have hx : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≤ (n : ℝ) ^ (1 - ω) := by
      have h0 : 0 ≤ Real.log n := Real.log_nonneg hn1
      have h1 : 0 ≤ (n : ℝ) ^ (1 - ω) := Real.rpow_nonneg hx.le _
      simpa [Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg h1] using hn
    have hpow : (n : ℝ) ^ (-ω) = (n : ℝ) ^ (1 - ω) / n := by
      rw [show -ω = (1 - ω) - 1 by ring, Real.rpow_sub_one hx.ne']
    have key : β * Real.log n / n ≤ β * (n : ℝ) ^ (-ω) := by
      rw [hpow, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hx.le) hβ.le
    have hp0 : 0 ≤ (n : ℝ) ^ (-ω) := Real.rpow_nonneg hx.le _
    refine ⟨?_, key⟩
    unfold denseRegime
    nlinarith
  · rcases hω0.lt_or_eq with hω | hω
    · have ht := (tendsto_rpow_neg_atTop hω).comp tendsto_natCast_atTop_atTop
      have ht' := ht.const_mul α
      rw [mul_zero] at ht'
      filter_upwards [ht'.eventually_lt_const (show (0:ℝ) < 1 by norm_num), hev1] with n hn hn1
      have hp0 : 0 ≤ (n : ℝ) ^ (-ω) := Real.rpow_nonneg (by linarith) _
      simp only [Function.comp] at hn
      unfold denseRegime
      constructor <;> nlinarith
    · subst hω
      obtain ⟨ha1, hb1⟩ := hdense rfl
      exact Eventually.of_forall fun n => by simp [denseRegime]; constructor <;> linarith
  · apply tendsto_const_nhds.congr'
    filter_upwards [hev1] with n hn1
    have hp : 0 < (n : ℝ) ^ (-ω) := Real.rpow_pos_of_pos (by linarith) _
    unfold denseRegime
    rw [mul_div_mul_right _ _ hp.ne']

lemma assemble (α β ω : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α) (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (hdense : ω = 0 → α < 1 ∧ β < 1)
    (L R : ℝ) (hR : 1 ≤ R) (hL : 0 < L)
    (hb1 : 1 / (2 * L) < β / (α + β))
    (hb2 : 3 * R < 4 * L ∨ (L < R ∧ (1 + 3 * R - 4 * L) / (6 * (R - L)) < β / (α + β)))
    (hdist : ∀ ε : ℝ, 0 < ε → Tendsto (fun m : ℕ => sbmProb (2 * m) (denseRegime α ω (2 * m))
      (denseRegime β ω (2 * m)) (fun _ G => ENNReal.ofReal ((1 - ε) * L) ≤ rhoAvg G ∧
        rhoAvg G ≤ ((rhoMax G : ℕ∞) : ℝ≥0∞) ∧ ((rhoMax G : ℕ∞) : ℝ≥0∞) = ENNReal.ofReal R))
      atTop (𝓝 1)) :
    Tendsto (fun m : ℕ => sbmProb (2 * m) (denseRegime α ω (2 * m)) (denseRegime β ω (2 * m))
      (fun V1 G => ¬ LPCommunity.LPRecovery.LPRecovers G V1)) atTop (𝓝 1) := by
  have ht0 : 0 < β / (α + β) := by positivity
  obtain ⟨ε, hε, hε1, hev⟩ := exists_eps L R (β / (α + β)) hL hR ht0 hb1 hb2
  obtain ⟨hpq, hpq1, hlim⟩ := dense_hyps α β ω hα hβ hαβ hω0 hω1 hdense
  have h26 := display_26 (fun n => denseRegime α ω n) (fun n => denseRegime β ω n) hpq hpq1
    (β / α) (by positivity) ((div_le_one hα).2 hαβ.le) hlim ε hε
  have hd := hdist ε hε
  have hand := tendsto_and (p := fun m => denseRegime α ω (2 * m))
    (q := fun m => denseRegime β ω (2 * m)) _ _ h26 hd
  refine tendsto_of_imp _ _ hand ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop (max N 3)] with m hm
  rintro V1 hV1 G ⟨⟨hcut, -⟩, hrA, hrM, hR'⟩
  have hn5 : 5 ≤ 2 * m := by have := le_of_max_le_right hm; omega
  obtain ⟨h1, h2⟩ := hN (2 * m) (by have := le_of_max_le_left hm; omega)
  have hbis : LPCommunity.MinBisect.IsBisection (2 * m) V1 := by
    simpa [bisections] using hV1
  have hx : 0 < ((2 * m : ℕ) : ℝ) ^ (-ω) := Real.rpow_pos_of_pos (by
    have : (5 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hn5
    linarith) _
  have hq : denseRegime β ω (2 * m) / (denseRegime α ω (2 * m) + denseRegime β ω (2 * m)) =
      β / (α + β) := by
    unfold denseRegime
    rw [show α * ((2 * m : ℕ) : ℝ) ^ (-ω) + β * ((2 * m : ℕ) : ℝ) ^ (-ω) =
      (α + β) * ((2 * m : ℕ) : ℝ) ^ (-ω) by ring, mul_div_mul_right _ _ hx.ne']
  rw [hq] at hcut
  exact det_not_recovers hn5 G V1 hbis R ((1 - ε) * L) ((1 - ε) * (β / (α + β))) hR
    (by nlinarith) (by nlinarith) hR' hrA hrM hcut h1 h2

end LPC7Aux

open Finset Filter Topology
open scoped Classical ENNReal

open LPCommunity.SBMDense LPCommunity.SBMRecovery LPCommunity.LPFail

theorem solution (α β ω : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α) (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (hdense : ω = 0 → α < 1 ∧ β < 1)
    (hcond : Cond22 α β ω ∨ Cond23 α β ω ∨ Cond24 α β ω ∨ Cond25 α β ω) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (denseRegime α ω (2 * m)) (denseRegime β ω (2 * m))
        (fun V1 G => ¬ LPCommunity.LPRecovery.LPRecovers G V1))
      Filter.atTop (nhds 1) := by
  have hs : 0 < α + β := by linarith
  rcases hcond with ⟨hω, hβ'⟩ | ⟨hωp, -, hk, hβ'⟩ | ⟨hω, hβ'⟩ | ⟨hωp, -, ⟨k, hk2, hk⟩, hβ'⟩
  · -- Condition (22): ω = 0
    subst hω
    obtain ⟨ha1, hb1⟩ := hdense rfl
    have hD : 0 ≤ (3 - α) ^ 2 - 4 * α := by nlinarith
    set S := Real.sqrt ((3 - α) ^ 2 - 4 * α) with hS
    have hS2 : S ^ 2 = (3 - α) ^ 2 - 4 * α := Real.sq_sqrt hD
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    obtain ⟨hr1, hr2⟩ := max_lt_iff.1 hβ'
    have hquad : β ^ 2 + (α - 3) * β + α < 0 := by
      nlinarith [mul_pos (show 0 < 2 * β - (3 - α) + S by linarith)
        (show 0 < S - (2 * β - (3 - α)) by linarith)]
    have e0 : ∀ γ : ℝ, ∀ n : ℕ, denseRegime γ 0 n = γ := fun γ n => by simp [denseRegime]
    refine LPC7Aux.assemble α β 0 hα hβ hαβ le_rfl hω1 (fun _ => ⟨ha1, hb1⟩)
      (2 - (α + β) / 2) 2 (by norm_num) (by linarith) ?_ ?_ ?_
    · rw [div_lt_div_iff₀ (by linarith) hs]; nlinarith
    · right
      refine ⟨by linarith, ?_⟩
      rw [div_lt_div_iff₀ (by linarith) hs]; nlinarith
    · intro ε hε
      simp only [e0]
      refine LPC7Aux.tendsto_of_imp (p := fun _ => α) (q := fun _ => β) _ _
        (proposition_16 α β hβ hαβ ha1 ε hε) (Eventually.of_forall fun m V1 _ G h => ?_)
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1, h2, ?_⟩
      rw [h3]; simp
  · -- Condition (23)
    set K := ⌈1 / (1 - ω)⌉₊ with hK
    have hx : 0 < 1 / (1 - ω) := by apply div_pos one_pos; linarith
    have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hx).ne'
    have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    refine LPC7Aux.assemble α β ω hα hβ hαβ hω0 hω1 hdense (K : ℝ) (K : ℝ) hK1' (by linarith)
      ?_ (Or.inl (by linarith)) ?_
    · have h2K : 0 < 2 * (K : ℝ) - 1 := by linarith
      rw [one_div_mul_eq_div, gt_iff_lt, div_lt_iff₀ h2K] at hβ'
      rw [div_lt_div_iff₀ (by linarith) hs]; nlinarith
    · intro ε hε
      refine LPC7Aux.tendsto_of_imp _ _
        (proposition_17 α β ω hα hβ hωp hω1 hk ε hε) (Eventually.of_forall fun m V1 _ G h => ?_)
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1, h2, ?_⟩
      rw [h3, ENNReal.ofReal_natCast]
      exact ENat.toENNReal_coe _
  · -- Condition (24): ω = 1/2
    subst hω
    have hx2 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
    set e := Real.exp (-(α ^ 2)) with he
    have he0 : 0 < e := Real.exp_pos _
    have he1 : e < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    have hr1 : (1 - 2 * e) / (2 - e) * α < β :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left _ _) hα.le) hβ'
    have hr2 : 1 / (3 + 2 * e) * α < β :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_right _ _) hα.le) hβ'
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)] at hr1
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)] at hr2
    refine LPC7Aux.assemble α β (1 / 2) hα hβ hαβ (by norm_num) (by norm_num) (by norm_num)
      (2 + e) 3 (by norm_num) (by linarith) ?_ ?_ ?_
    · rw [div_lt_div_iff₀ (by linarith) hs]; nlinarith
    · right
      refine ⟨by linarith, ?_⟩
      rw [div_lt_div_iff₀ (by nlinarith) hs]; nlinarith
    · intro ε hε
      have h18 := proposition_18 α β (1 / 2) hβ hαβ (by norm_num) (by norm_num) ⟨2, by norm_num⟩ ε hε
      simp only [hx2, Real.rpow_two] at h18
      refine LPC7Aux.tendsto_of_imp _ _ h18 (Eventually.of_forall fun m V1 _ G h => ?_)
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨h1, h2, ?_⟩
      rw [h3]; norm_num
  · -- Condition (25)
    set x := 1 / (1 - ω) with hxdef
    have h1ω : 0 < 1 - ω := by linarith
    have hx1 : 1 < x := by rw [hxdef, lt_div_iff₀ h1ω]; linarith
    have hk3 : (3 : ℝ) ≤ x := by
      rw [hk] at hx1 ⊢
      have : 1 < k := by exact_mod_cast hx1
      have : 3 ≤ k := by omega
      exact_mod_cast this
    set e := Real.exp (-(α ^ x)) with he
    have he0 : 0 < e := Real.exp_pos _
    have hden : 0 < 2 * x - 1 + 2 * e := by linarith
    rw [one_div_mul_eq_div, gt_iff_lt, div_lt_iff₀ hden] at hβ'
    refine LPC7Aux.assemble α β ω hα hβ hαβ hω0 hω1 hdense (x + e) (x + 1) (by linarith)
      (by linarith) ?_ (Or.inl (by linarith)) ?_
    · rw [div_lt_div_iff₀ (by linarith) hs]; nlinarith
    · intro ε hε
      exact proposition_18 α β ω hβ hαβ hωp hω1 ⟨k, hk⟩ ε hε

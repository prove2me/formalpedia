-- Prove2me | solution 1 for OAI.PlanarHalving.Boundary.enhanced_boundary_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:52:51.975209+00:00
-- url     : https://prove2.me/submissions/b4b2e037-4abb-4bf5-9ba6-5bd39f92f1dd

import Mathlib
import Definitions.Def_HalvingLines
import Definitions.Def_OAIQWPHL000
import Theorems.Thm_OAI_PlanarHalving_PlaneGraph_designated_crossing_bound

section
-- module Solutions.OAIQW_PlanarHalving.Activity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Sweep

theorem distance_of_outside_visitors {n k c : ℕ} (P : Fin n → Point)
    (s₀ t : ℝ) (E E' U : Finset (Fin n))
    (hE : E.card = k + c) (hE' : E'.card = k + c)
    (hsep : Separates P s₀ E) (hsep' : Separates P t E')
    (hU : c ≤ U.card)
    (hvisit : ∀ u ∈ U, u ∉ E ∧ ∃ (s : ℝ) (M : Finset (Fin n)),
      s₀ ≤ s ∧ s ≤ t ∧ M.card = k ∧ Separates P s M ∧ u ∈ M) :
    c ≤ (E \ E').card := by
  classical
  by_cases hh : ∃ u ∈ U, u ∉ E'
  · obtain ⟨u, hu, hu'⟩ := hh
    obtain ⟨huE, s, M, h₀, ht, hcard, hM, huM⟩ := hvisit u hu
    have hsub : E \ M ⊆ E \ E' := by
      intro v hv
      obtain ⟨hvE, hvM⟩ := Finset.mem_sdiff.mp hv
      refine Finset.mem_sdiff.mpr ⟨hvE, ?_⟩
      intro hv'
      have hvt := (comparison_persists (P u) (P v) h₀ ht
        (hsep v hvE u huE) (hM u huM v hvM)).2
      exact (not_lt_of_gt hvt) (hsep' v hv' u hu')
    have hcount := Finset.card_sdiff_add_card_inter E M
    have hinter : (E ∩ M).card ≤ M.card := Finset.card_le_card Finset.inter_subset_right
    have hc : c ≤ (E \ M).card := by omega
    exact hc.trans (Finset.card_le_card hsub)
  · have hsub : U ⊆ E' \ E := by
      intro u hu
      refine Finset.mem_sdiff.mpr ⟨?_, (hvisit u hu).1⟩
      by_contra hnot
      exact hh ⟨u, hu, hnot⟩
    have hc := hU.trans (Finset.card_le_card hsub)
    have hc₁ := Finset.card_sdiff_add_card_inter E E'
    have hc₂ := Finset.card_sdiff_add_card_inter E' E
    rw [Finset.inter_comm E' E] at hc₂
    omega

lemma states_nested {n : ℕ} {P : Fin n → Point} {s : ℝ} {M E : Finset (Fin n)}
    (hM : Separates P s M) (hE : Separates P s E) (hcard : M.card ≤ E.card) : M ⊆ E := by
  classical
  intro i hi
  by_contra hiE
  have hsub : E ⊆ M := by
    intro j hj
    by_contra hjM
    exact (not_lt_of_gt (hM i hi j hjM)) (hE j hj i hiE)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  exact hiE (heq.symm ▸ hi)

theorem outside_class_distance {n k c : ℕ} (P : Fin n → Point)
    (s₀ t : ℝ) (M₀ E E' V : Finset (Fin n))
    (hM₀ : M₀.card = k) (hE : E.card = k + c) (hE' : E'.card = k + c)
    (hsep₀ : Separates P s₀ M₀) (hsep : Separates P s₀ E)
    (hsep' : Separates P t E') (hV : 2 * c ≤ V.card)
    (hvisit : ∀ u ∈ V, u ∉ M₀ ∧ ∃ (s : ℝ) (M : Finset (Fin n)),
      s₀ ≤ s ∧ s ≤ t ∧ M.card = k ∧ Separates P s M ∧ u ∈ M) :
    c ≤ (E \ E').card := by
  classical
  have hsubset : M₀ ⊆ E := states_nested hsep₀ hsep (by omega)
  have hdiff : (E \ M₀).card = c := by
    have hh := Finset.card_sdiff_add_card_inter E M₀
    rw [Finset.inter_eq_right.mpr hsubset, hM₀, hE] at hh
    omega
  have hinter : V ∩ E ⊆ E \ M₀ := by
    intro u hu
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hu).2,
      (hvisit u (Finset.mem_inter.mp hu).1).1⟩
  have hU : c ≤ (V \ E).card := by
    have hh := Finset.card_sdiff_add_card_inter V E
    have hle := Finset.card_le_card hinter
    omega
  apply distance_of_outside_visitors P s₀ t E E' (V \ E) hE hE' hsep hsep' hU
  intro u hu
  exact ⟨(Finset.mem_sdiff.mp hu).2, (hvisit u (Finset.mem_sdiff.mp hu).1).2⟩

end Sweep

namespace Sweep

lemma separates_neg_compl {n : ℕ} {P : Fin n → Point} {s : ℝ}
    {M : Finset (Fin n)} (hM : Separates P s M) :
    Separates (fun i => -P i) s Mᶜ := by
  classical
  intro i hi j hj
  have hi' : i ∉ M := Finset.mem_compl.mp hi
  have hj' : j ∈ M := by simpa using hj
  have h := hM j hj' i hi'
  simp only [projection, Prod.fst_neg, Prod.snd_neg] at *
  linarith

theorem activity_distance {n k c : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin n → Point) (s : ι → ℝ) (M : ι → Finset (Fin n)) (i₀ i₁ : ι)
    (hsize : ∀ i, (M i).card = k) (hsep : ∀ i, Separates P (s i) (M i))
    (hlo : ∀ i, s i₀ ≤ s i) (hhi : ∀ i, s i ≤ s i₁)
    (hinj₀ : Function.Injective (fun u => projection (s i₀) (P u)))
    (hinj₁ : Function.Injective (fun u => projection (s i₁) (P u)))
    (hc : 4 * c ≤ (activity M i₀).card) :
    (k + c ≤ n ∧ ∃ E E' : Finset (Fin n),
      E.card = k + c ∧ E'.card = k + c ∧
      Separates P (s i₀) E ∧ Separates P (s i₁) E' ∧ c ≤ (E \ E').card) ∨
    (c ≤ k ∧ ∃ E E' : Finset (Fin n),
      E.card = k - c ∧ E'.card = k - c ∧
      Separates P (s i₀) E ∧ Separates P (s i₁) E' ∧ c ≤ (E \ E').card) := by
  classical
  let A := activity M i₀
  let V := A \ M i₀
  let W := A ∩ M i₀
  have hpart : V.card + W.card = A.card := Finset.card_sdiff_add_card_inter A (M i₀)
  have hk : k ≤ n := by
    simpa only [hsize i₀, Fintype.card_fin] using (M i₀).card_le_univ
  by_cases hV : 2 * c ≤ V.card
  · have hVsub : V ⊆ (M i₀)ᶜ := by
      intro u hu
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hu).2
    have hfeas : k + c ≤ n := by
      have hle := Finset.card_le_card hVsub
      simp only [Finset.card_compl, Fintype.card_fin, hsize] at hle
      omega
    obtain ⟨E, hE, hsepE⟩ := exists_state P (s i₀) hfeas hinj₀
    obtain ⟨E', hE', hsepE'⟩ := exists_state P (s i₁) hfeas hinj₁
    refine Or.inl ⟨hfeas, E, E', hE, hE', hsepE, hsepE', ?_⟩
    apply outside_class_distance P (s i₀) (s i₁) (M i₀) E E' V
      (hsize i₀) hE hE' (hsep i₀) hsepE hsepE' hV
    intro u hu
    obtain ⟨huA, huM⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨i, hi | hi⟩ := mem_activity.mp huA
    · exact ⟨huM, s i, M i, hlo i, hhi i, hsize i, hsep i, hi.1⟩
    · exact False.elim (huM hi.2)
  · have hW : 2 * c ≤ W.card := by change 4 * c ≤ A.card at hc; omega
    have hfeas : c ≤ k := by
      have hle : W.card ≤ (M i₀).card := Finset.card_le_card Finset.inter_subset_right
      rw [hsize] at hle
      omega
    obtain ⟨E, hE, hsepE⟩ := exists_state P (s i₀) (show k-c ≤ n by omega) hinj₀
    obtain ⟨E', hE', hsepE'⟩ := exists_state P (s i₁) (show k-c ≤ n by omega) hinj₁
    refine Or.inr ⟨hfeas, E, E', hE, hE', hsepE, hsepE', ?_⟩
    have hbound : c ≤ (Eᶜ \ E'ᶜ).card := by
      apply outside_class_distance (fun u => -P u) (s i₀) (s i₁) (M i₀)ᶜ Eᶜ E'ᶜ W
        (k := n-k) (c := c)
      · simp only [Finset.card_compl, Fintype.card_fin, hsize]
      · simp only [Finset.card_compl, Fintype.card_fin, hE]
        omega
      · simp only [Finset.card_compl, Fintype.card_fin, hE']
        omega
      · exact separates_neg_compl (hsep i₀)
      · exact separates_neg_compl hsepE
      · exact separates_neg_compl hsepE'
      · exact hW
      · intro u hu
        obtain ⟨huA, huM⟩ := Finset.mem_inter.mp hu
        obtain ⟨i, hi | hi⟩ := mem_activity.mp huA
        · exact False.elim (hi.2 huM)
        · refine ⟨by simpa using huM, s i, (M i)ᶜ, hlo i, hhi i, ?_,
            separates_neg_compl (hsep i), Finset.mem_compl.mpr hi.1⟩
          simp only [Finset.card_compl, Fintype.card_fin, hsize]
    have heq : Eᶜ \ E'ᶜ = E' \ E := by ext u; simp; tauto
    rw [heq] at hbound
    have he := Finset.card_sdiff_add_card_inter E E'
    have he' := Finset.card_sdiff_add_card_inter E' E
    rw [Finset.inter_comm E' E] at he'
    omega

lemma projection_lt_between (p q : Point) {s₀ s₁ t : ℝ}
    (h₀ : s₀ ≤ t) (h₁ : t ≤ s₁)
    (hp₀ : projection s₀ p < projection s₀ q)
    (hp₁ : projection s₁ p < projection s₁ q) : projection t p < projection t q := by
  unfold projection at *
  by_cases hx : p.1 ≤ q.1
  · have hprod := mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr hx)
    nlinarith only [hp₁, hprod]
  · have hprod := mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr (le_of_not_ge hx))
    nlinarith only [hp₀, hprod]

lemma separates_between {n : ℕ} {P : Fin n → Point} {s₀ s₁ t : ℝ}
    {M : Finset (Fin n)} (h₀ : s₀ ≤ t) (h₁ : t ≤ s₁)
    (hM₀ : Separates P s₀ M) (hM₁ : Separates P s₁ M) : Separates P t M := by
  intro u hu v hv
  exact projection_lt_between (P u) (P v) h₀ h₁ (hM₀ u hu v hv) (hM₁ u hu v hv)

lemma states_unique {n : ℕ} {P : Fin n → Point} {s : ℝ} {M E : Finset (Fin n)}
    (hM : Separates P s M) (hE : Separates P s E) (hcard : M.card = E.card) : M = E :=
  Finset.eq_of_subset_of_card_le (states_nested hM hE hcard.le) hcard.ge

theorem activity_pos_distance {n k : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin n → Point) (s : ι → ℝ) (M : ι → Finset (Fin n)) (i₀ i₁ : ι)
    (hsize : ∀ i, (M i).card = k) (hsep : ∀ i, Separates P (s i) (M i))
    (hlo : ∀ i, s i₀ ≤ s i) (hhi : ∀ i, s i ≤ s i₁)
    (hactivity : 0 < (activity M i₀).card) : 1 ≤ (M i₀ \ M i₁).card := by
  classical
  by_contra hn
  have hempty : M i₀ \ M i₁ = ∅ := Finset.card_eq_zero.mp (by omega)
  have hsub : M i₀ ⊆ M i₁ := Finset.sdiff_eq_empty_iff_subset.mp hempty
  have heq : M i₀ = M i₁ := Finset.eq_of_subset_of_card_le hsub (by rw [hsize, hsize])
  have hconstant (i : ι) : M i = M i₀ := by
    apply states_unique (hsep i)
      (separates_between (hlo i) (hhi i) (hsep i₀) (by rw [heq]; exact hsep i₁))
    rw [hsize, hsize]
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hactivity
  obtain ⟨i, hi | hi⟩ := mem_activity.mp hu
  · rw [hconstant i] at hi
    exact hi.2 hi.1
  · rw [hconstant i] at hi
    exact hi.1 hi.2

end Sweep

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Boundary

lemma outside_strip {t c ρ : ℝ} (h : ¬ |t - c| ≤ 3 * ρ) :
    t < c - 3 * ρ ∨ c + 3 * ρ < t := by
  have h' : 3 * ρ < |t - c| := lt_of_not_ge h
  rcases lt_abs.mp h' with h' | h'
  · right
    linarith
  · left
    linarith

lemma initially_marked_loss {t c₀ cmin ρ : ℝ}
    (hρ : 0 ≤ ρ) (hmark : t < c₀)
    (hactive : cmin - ρ ≤ t)
    (hstrip₀ : ¬ |t - c₀| ≤ 3 * ρ)
    (hstripmin : ¬ |t - cmin| ≤ 3 * ρ) :
    cmin + 3 * ρ < t ∧ t < c₀ - 3 * ρ ∧ cmin + 6 * ρ < c₀ := by
  rcases outside_strip hstrip₀ with h₀ | h₀
  · rcases outside_strip hstripmin with hm | hm
    · linarith
    · exact ⟨hm, h₀, by linarith⟩
  · linarith

lemma initially_unmarked_gain {t c₀ cmax ρ : ℝ}
    (hρ : 0 ≤ ρ) (hunmark : c₀ ≤ t)
    (hactive : t ≤ cmax + ρ)
    (hstrip₀ : ¬ |t - c₀| ≤ 3 * ρ)
    (hstripmax : ¬ |t - cmax| ≤ 3 * ρ) :
    c₀ + 3 * ρ < t ∧ t < cmax - 3 * ρ ∧ c₀ + 6 * ρ < cmax := by
  rcases outside_strip hstrip₀ with h₀ | h₀
  · linarith
  · rcases outside_strip hstripmax with hm | hm
    · exact ⟨h₀, hm, by linarith⟩
    · linarith

theorem three_strips_core {α ι : Type*} [DecidableEq α]
    (M : ι → Finset α) (A B : Finset α) (t : α → ℝ)
    (c : ι → ℝ) (e : ι → α → ℝ) (i₀ imin imax : ι) (ρ : ℝ) (C : ℕ)
    (hρ : 0 ≤ ρ)
    (hmin : ∀ i, c imin ≤ c i) (hmax : ∀ i, c i ≤ c imax)
    (herr : ∀ i x, x ∈ B → |e i x| ≤ ρ)
    (hzero : ∀ x ∈ B, e i₀ x = 0)
    (hcut : ∀ i x, x ∈ B → (x ∈ M i ↔ t x + e i x < c i))
    (hactive : ∀ x ∈ A,
      (x ∈ M i₀ → ∃ i, x ∉ M i) ∧ (x ∉ M i₀ → ∃ i, x ∈ M i))
    (hbudget : ∀ i,
      (M i₀ ∩ B).card ≤ (M i ∩ B).card + C ∧
      (M i ∩ B).card ≤ (M i₀ ∩ B).card + C) :
    ((A ∩ B).filter fun x =>
      ¬ (|t x - c i₀| ≤ 3 * ρ ∨ |t x - c imin| ≤ 3 * ρ ∨
        |t x - c imax| ≤ 3 * ρ)).card ≤ 2 * C := by
  classical
  let H := (A ∩ B).filter fun x =>
    ¬ (|t x - c i₀| ≤ 3 * ρ ∨ |t x - c imin| ≤ 3 * ρ ∨
      |t x - c imax| ≤ 3 * ρ)
  let L := H.filter fun x => x ∈ M i₀
  let G := H.filter fun x => x ∉ M i₀
  have hH (x : α) (hx : x ∈ H) :
      x ∈ A ∧ x ∈ B ∧ ¬ |t x - c i₀| ≤ 3 * ρ ∧
        ¬ |t x - c imin| ≤ 3 * ρ ∧ ¬ |t x - c imax| ≤ 3 * ρ := by
    simpa only [H, Finset.mem_filter, Finset.mem_inter, not_or, and_assoc] using hx
  have hL (x : α) (hx : x ∈ L) :
      c imin + 3 * ρ < t x ∧ t x < c i₀ - 3 * ρ ∧ c imin + 6 * ρ < c i₀ := by
    obtain ⟨hxH, hxM⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hxB, hx₀, hxm, _⟩ := hH x hxH
    have hmarked : t x < c i₀ := by
      simpa only [hzero x hxB, add_zero] using (hcut i₀ x hxB).mp hxM
    obtain ⟨i, hi⟩ := (hactive x hxA).1 hxM
    have hi' : c i ≤ t x + e i x := not_lt.mp fun h => hi ((hcut i x hxB).mpr h)
    have he := (abs_le.mp (herr i x hxB)).2
    have ht : c imin - ρ ≤ t x := by linarith [hmin i]
    exact initially_marked_loss hρ hmarked ht hx₀ hxm
  have hG (x : α) (hx : x ∈ G) :
      c i₀ + 3 * ρ < t x ∧ t x < c imax - 3 * ρ ∧ c i₀ + 6 * ρ < c imax := by
    obtain ⟨hxH, hxM⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxA, hxB, hx₀, _, hxmax⟩ := hH x hxH
    have hunmarked : c i₀ ≤ t x := by
      apply not_lt.mp
      intro h
      exact hxM ((hcut i₀ x hxB).mpr (by simpa only [hzero x hxB, add_zero] using h))
    obtain ⟨i, hi⟩ := (hactive x hxA).2 hxM
    have hi' := (hcut i x hxB).mp hi
    have he := (abs_le.mp (herr i x hxB)).1
    have ht : t x ≤ c imax + ρ := by linarith [hmax i]
    exact initially_unmarked_gain hρ hunmarked ht hx₀ hxmax
  have hLcard : L.card ≤ C := by
    by_cases hn : L.Nonempty
    · obtain ⟨x, hx⟩ := hn
      have hgap := (hL x hx).2.2
      have hsub : M imin ∩ B ⊆ M i₀ ∩ B := by
        intro y hy
        obtain ⟨hyM, hyB⟩ := Finset.mem_inter.mp hy
        refine Finset.mem_inter.mpr ⟨?_, hyB⟩
        by_contra hnM
        have hy₀ : c i₀ ≤ t y := by
          apply not_lt.mp
          intro h
          exact hnM ((hcut i₀ y hyB).mpr (by simpa only [hzero y hyB, add_zero] using h))
        have hymin := (hcut imin y hyB).mp hyM
        have he := (abs_le.mp (herr imin y hyB)).1
        linarith
      have hsubL : L ⊆ (M i₀ ∩ B) \ (M imin ∩ B) := by
        intro y hy
        obtain ⟨hyH, hyM⟩ := Finset.mem_filter.mp hy
        have hyB := (hH y hyH).2.1
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hyM, hyB⟩, ?_⟩
        intro hymin
        have hc := (hcut imin y hyB).mp (Finset.mem_inter.mp hymin).1
        have he := (abs_le.mp (herr imin y hyB)).1
        have ht := (hL y hy).1
        linarith
      have hcount := Finset.card_sdiff_add_card_eq_card hsub
      have hle := Finset.card_le_card hsubL
      have hb := (hbudget imin).1
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.zero_le]
  have hGcard : G.card ≤ C := by
    by_cases hn : G.Nonempty
    · obtain ⟨x, hx⟩ := hn
      have hgap := (hG x hx).2.2
      have hsub : M i₀ ∩ B ⊆ M imax ∩ B := by
        intro y hy
        obtain ⟨hyM, hyB⟩ := Finset.mem_inter.mp hy
        refine Finset.mem_inter.mpr ⟨(hcut imax y hyB).mpr ?_, hyB⟩
        have hy₀ : t y < c i₀ := by
          simpa only [hzero y hyB, add_zero] using (hcut i₀ y hyB).mp hyM
        have he := (abs_le.mp (herr imax y hyB)).2
        linarith
      have hsubG : G ⊆ (M imax ∩ B) \ (M i₀ ∩ B) := by
        intro y hy
        obtain ⟨hyH, hyM⟩ := Finset.mem_filter.mp hy
        have hyB := (hH y hyH).2.1
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨?_, hyB⟩, ?_⟩
        · apply (hcut imax y hyB).mpr
          have he := (abs_le.mp (herr imax y hyB)).2
          have ht := (hG y hy).2.1
          linarith
        · exact fun hi => hyM (Finset.mem_inter.mp hi).1
      have hcount := Finset.card_sdiff_add_card_eq_card hsub
      have hle := Finset.card_le_card hsubG
      have hb := (hbudget imax).2
      omega
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.zero_le]
  have hsplit : L.card + G.card = H.card := Finset.card_filter_add_card_filter_not (s := H) (fun x => x ∈ M i₀)
  change H.card ≤ 2 * C
  omega

lemma token_population {α τ : Type*} [DecidableEq α] [Fintype τ]
    (f : τ → α) (hf : Function.Injective f) (B : Finset α) :
    ((Finset.univ.image f) ∩ B).card =
      (Finset.univ.filter fun u => f u ∈ B).card := by
  classical
  rw [← Finset.filter_mem_eq_inter, Finset.filter_image,
    Finset.card_image_of_injective _ hf]

lemma filter_population_change {τ : Type*} [Fintype τ]
    (p q : τ → Prop) [DecidablePred p] [DecidablePred q] :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card +
      (Finset.univ.filter fun u => ¬ (p u ↔ q u)).card ∧
    (Finset.univ.filter q).card ≤ (Finset.univ.filter p).card +
      (Finset.univ.filter fun u => ¬ (p u ↔ q u)).card := by
  classical
  have h₁ : Finset.univ.filter p ⊆
      (Finset.univ.filter q) ∪ (Finset.univ.filter fun u => ¬ (p u ↔ q u)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hq : q u
    · exact Or.inl hq
    · exact Or.inr fun h => hq (h.mp hu)
  have h₂ : Finset.univ.filter q ⊆
      (Finset.univ.filter p) ∪ (Finset.univ.filter fun u => ¬ (p u ↔ q u)) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hp : p u
    · exact Or.inl hp
    · exact Or.inr fun h => hp (h.mpr hu)
  exact ⟨(Finset.card_le_card h₁).trans (Finset.card_union_le _ _),
    (Finset.card_le_card h₂).trans (Finset.card_union_le _ _)⟩

theorem token_population_budget {τ : Type*} [Fintype τ]
    (inside : ℕ → τ → Prop) [∀ i, DecidablePred (inside i)] (m i : ℕ) (hi : i ≤ m) :
    let pop := fun j => (Finset.univ.filter (inside j)).card
    let cost := fun j => (Finset.univ.filter fun u =>
      ¬ (inside j u ↔ inside (j + 1) u)).card
    pop 0 ≤ pop i + ∑ j ∈ Finset.range m, cost j ∧
    pop i ≤ pop 0 + ∑ j ∈ Finset.range m, cost j := by
  classical
  dsimp only
  let pop := fun j => (Finset.univ.filter (inside j)).card
  let cost := fun j => (Finset.univ.filter fun u =>
    ¬ (inside j u ↔ inside (j + 1) u)).card
  change pop 0 ≤ pop i + ∑ j ∈ Finset.range m, cost j ∧
    pop i ≤ pop 0 + ∑ j ∈ Finset.range m, cost j
  have hpref (i : ℕ) :
      pop 0 ≤ pop i + ∑ j ∈ Finset.range i, cost j ∧
      pop i ≤ pop 0 + ∑ j ∈ Finset.range i, cost j := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hstep := filter_population_change (inside i) (inside (i + 1))
      change pop i ≤ pop (i+1) + cost i ∧ pop (i+1) ≤ pop i + cost i at hstep
      rw [Finset.sum_range_succ]
      omega
  have hsum : ∑ j ∈ Finset.range i, cost j ≤ ∑ j ∈ Finset.range m, cost j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (by intros; omega)
  have hp := hpref i
  omega

theorem three_strips_tokens {α τ : Type*} [DecidableEq α] [Fintype τ]
    (m : ℕ) (f : ℕ → τ → α) (hf : ∀ i ≤ m, Function.Injective (f i))
    (A B : Finset α) (t : α → ℝ) (c : Fin (m + 1) → ℝ)
    (e : Fin (m + 1) → α → ℝ) (imin imax : Fin (m + 1)) (ρ : ℝ)
    (hρ : 0 ≤ ρ)
    (hmin : ∀ i, c imin ≤ c i) (hmax : ∀ i, c i ≤ c imax)
    (herr : ∀ i x, x ∈ B → |e i x| ≤ ρ)
    (hzero : ∀ x ∈ B, e 0 x = 0)
    (hcut : ∀ (i : Fin (m + 1)) (x : α), x ∈ B →
      (x ∈ Finset.univ.image (f i) ↔ t x + e i x < c i))
    (hactive : ∀ x ∈ A,
      (x ∈ Finset.univ.image (f 0) → ∃ i : Fin (m + 1),
        x ∉ Finset.univ.image (f i)) ∧
      (x ∉ Finset.univ.image (f 0) → ∃ i : Fin (m + 1),
        x ∈ Finset.univ.image (f i))) :
    ((A ∩ B).filter fun x =>
      ¬ (|t x - c 0| ≤ 3 * ρ ∨ |t x - c imin| ≤ 3 * ρ ∨
        |t x - c imax| ≤ 3 * ρ)).card ≤
      2 * ∑ j ∈ Finset.range m, (Finset.univ.filter fun u =>
        ¬ (f j u ∈ B ↔ f (j + 1) u ∈ B)).card := by
  classical
  apply three_strips_core (fun i : Fin (m + 1) => Finset.univ.image (f i))
    A B t c e 0 imin imax ρ _ hρ hmin hmax herr hzero hcut hactive
  intro i
  simp only [Fin.val_zero]
  rw [token_population _ (hf 0 (Nat.zero_le _)),
    token_population _ (hf i (by omega))]
  exact token_population_budget (fun j u => f j u ∈ B) m i (by omega)

lemma changes_initial {ι : Type*} (p : ι → Prop) (i₀ : ι)
    (hp : ∃ i j, ¬ (p i ↔ p j)) :
    (p i₀ → ∃ i, ¬ p i) ∧ (¬ p i₀ → ∃ i, p i) := by
  classical
  obtain ⟨i, j, h⟩ := hp
  constructor
  · intro _
    by_cases hi : p i
    · exact ⟨j, fun hj => h ⟨fun _ => hj, fun _ => hi⟩⟩
    · exact ⟨i, hi⟩
  · intro _
    by_cases hi : p i
    · exact ⟨i, hi⟩
    · refine ⟨j, ?_⟩
      by_contra hj
      exact h ⟨fun hpi => (hi hpi).elim, fun hpj => (hj hpj).elim⟩

lemma dot_sq_le (u v : Point) : dot u v ^ 2 ≤ sqNorm u * sqNorm v := by
  unfold dot sqNorm
  nlinarith [sq_nonneg (u.1 * v.2 - u.2 * v.1)]

lemma abs_dot_le {u v : Point} {D θ : ℝ} (hD : 0 ≤ D) (hθ : 0 ≤ θ)
    (hu : sqNorm u ≤ θ ^ 2) (hv : sqNorm v ≤ D ^ 2) :
    |dot u v| ≤ D * θ := by
  have hs : 0 ≤ sqNorm v := by unfold sqNorm; positivity
  have hsq := (dot_sq_le u v).trans (mul_le_mul hu hv hs (sq_nonneg θ))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD hθ)).mp
  rw [sq_abs]
  nlinarith

end Boundary

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.PlaneGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
namespace PlaneGraph

variable {V : Type*} [Fintype V] {P : V → Point}

omit [Fintype V] in
lemma incident_disjoint (hP : Position P) (hx : Function.Injective (fun v => (P v).1))
    {v u w : V} (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w) :
    Disjoint (openSegment ℝ (P v) (P u)) (openSegment ℝ (P v) (P w)) := by
  apply Set.disjoint_left.mpr
  intro z hzu hzw
  have hu := height_of_mem_openSegment (fun h => hvu (hx h)) hzu
  have hw := height_of_mem_openSegment (fun h => hvw (hx h)) hzw
  have he : PlanarHalving.slope (P v) (P u) = PlanarHalving.slope (P v) (P w) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hu.1)
    dsimp only [height] at hu hw
    linarith only [hu.2, hw.2]
  exact huw (slope_eq_implies_eq_ne hP (fun h => hvu (hx h)) (fun h => hvw (hx h)) he)

omit [Fintype V] in
lemma Drawing.crossing_endpoints (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges) (hne : e ≠ f)
    (hc : Crosses P e f) :
    e.1 ≠ e.2 ∧ f.1 ≠ f.2 ∧ e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  have hev : e.1 ≠ e.2 := by intro h; have := D.right _ he; rw [h] at this; exact lt_irrefl _ this
  have hfv : f.1 ≠ f.2 := by intro h; have := D.right _ hf; rw [h] at this; exact lt_irrefl _ this
  have h11 : e.1 ≠ f.1 := by
    intro h
    apply hc
    rw [h]
    exact incident_disjoint hP hx (by simpa only [← h] using hev) hfv
      (fun h' => hne (Prod.ext h h'))
  have h22 : e.2 ≠ f.2 := by
    intro h
    apply hc
    rw [openSegment_symm ℝ (P e.1), openSegment_symm ℝ (P f.1), h]
    exact incident_disjoint hP hx (by simpa only [← h] using hev.symm) hfv.symm
      (fun h' => hne (Prod.ext h' h))
  obtain ⟨z, hze, hzf⟩ := Set.not_disjoint_iff.mp hc
  have hxe := openSegment_horizontal_bounds (D.right _ he) hze
  have hxf := openSegment_horizontal_bounds (D.right _ hf) hzf
  refine ⟨hev, hfv, h11, ?_, ?_, h22⟩
  · intro h
    rw [h] at hxe
    exact lt_irrefl _ (hxe.1.trans hxf.2)
  · intro h
    rw [h] at hxe
    exact lt_irrefl _ (hxf.1.trans hxe.2)

end PlaneGraph
end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.CrossingEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.PlaneGraph
open scoped BigOperators
open FiniteSampling
variable {V : Type*} [Fintype V] {P : V → Point}

lemma Drawing.crossings_card_eq (D : Drawing P) :
    D.crossings.card = ((↑(D.edges ×ˢ D.edges) : Set ((V × V) × (V × V))) ∩
      {ef | Fintype.equivFin (V × V) ef.1 < Fintype.equivFin (V × V) ef.2 ∧
        ¬ Disjoint (openSegment ℝ (P ef.1.1) (P ef.1.2)) (openSegment ℝ (P ef.2.1) (P ef.2.2))}).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  unfold Drawing.crossings
  rw [Finset.coe_filter]
  ext ef
  simp [Crosses, edgeIndex]

theorem Drawing.designated_crossing (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    (F : Finset V) (hFv : F ⊆ D.vertices)
    (hF : ∀ e ∈ D.edges, e.1 ∈ F ∨ e.2 ∈ F) :
    (D.edges.card : ℝ) ^ 3 ≤ 2304 * F.card * D.vertices.card * D.crossings.card +
      13824 * (D.vertices.card : ℝ) ^ 3 := by
  have h := designated_crossing_bound P hP hx D.vertices D.edges D.right D.ends F hFv hF
  rw [← Drawing.crossings_card_eq] at h
  exact h

end PlanarHalving.PlaneGraph

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Chains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.PlaneGraph

variable {V : Type*} [Fintype V] {P : V → Point}

lemma Drawing.crossingPoint_injective (D : Drawing P) (hD : D.NoMultiple) :
    Function.Injective D.crossingPoint := by
  intro w v hpoint
  have hw := D.crossing_props w
  have hv := D.crossing_props v
  have hwm := D.crossingPoint_mem w
  have hvm := D.crossingPoint_mem v
  have hne : w.val.1 ≠ w.val.2 := fun h => hw.2.2.1.ne (congrArg edgeIndex h)
  have he (g : V × V) (hg : g ∈ D.edges)
      (hgm : D.crossingPoint w ∈ segment ℝ (P g.1) (P g.2)) :
      g = w.val.1 ∨ g = w.val.2 := by
    by_contra hh
    push Not at hh
    exact hD _ hw.1 _ hw.2.1 hne _ hg hh.1 hh.2 _ hwm.1 hwm.2 hgm
  have h₁ := he v.val.1 hv.1 (by rw [hpoint]; exact openSegment_subset_segment ℝ _ _ hvm.1)
  have h₂ := he v.val.2 hv.2.1 (by rw [hpoint]; exact openSegment_subset_segment ℝ _ _ hvm.2)
  apply Subtype.ext
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · have := hv.2.2.1
    rw [h₁, h₂] at this
    exact False.elim (lt_irrefl _ this)
  · exact Prod.ext h₁.symm h₂.symm
  · have := hv.2.2.1
    rw [h₁, h₂] at this
    exact False.elim (lt_asymm hw.2.2.1 this)
  · have := hv.2.2.1
    rw [h₁, h₂] at this
    exact False.elim (lt_irrefl _ this)

lemma Drawing.crossing_slopes_ne (D : Drawing P) (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (w : ↥D.crossings) :
    slope (P w.val.1.1) (P w.val.1.2) ≠ slope (P w.val.2.1) (P w.val.2.2) := by
  have hw := D.crossing_props w
  have he := D.crossing_endpoints hP hx hw.1 hw.2.1
    (fun h => hw.2.2.1.ne (congrArg edgeIndex h)) hw.2.2.2
  have hm := D.crossingPoint_mem w
  have h₁ := (height_of_mem_openSegment (D.right _ hw.1).ne hm.1).2
  have h₂ := (height_of_mem_openSegment (D.right _ hw.2.1).ne hm.2).2
  intro hs
  have h₃ := height_right (P w.val.1.1) (P w.val.1.2) (D.right _ hw.1).ne
  apply hP.2 w.val.1.1 w.val.1.2 w.val.2.1 he.1 he.2.2.2.2.1 he.2.2.1
  unfold height at h₁ h₂ h₃
  rw [← hs] at h₂
  unfold orient
  have ha : (P w.val.1.2).2 - (P w.val.1.1).2 =
      ((P w.val.1.2).1 - (P w.val.1.1).1) * slope (P w.val.1.1) (P w.val.1.2) := by linarith only [h₃]
  have hb : (P w.val.2.1).2 - (P w.val.1.1).2 =
      ((P w.val.2.1).1 - (P w.val.1.1).1) * slope (P w.val.1.1) (P w.val.1.2) := by linarith only [h₁, h₂]
  rw [ha, hb]
  ring

variable {I J : Type*} {D : Drawing P}

lemma height_difference (p q r s : Point) (x y : ℝ) :
    height p q x - height r s x = height p q y - height r s y +
      (x-y) * (slope p q - slope r s) := by unfold height; ring

lemma ConvexCover.crossing_support (C : ConvexCover D I) (A : ConcaveCover D J)
    (w v : ↥D.crossings) (hc : C.owner w.val.1 = C.owner v.val.1)
    (ha : A.owner w.val.2 = A.owner v.val.2) :
    ((D.crossingPoint v).1 - (D.crossingPoint w).1) *
      (slope (P w.val.1.1) (P w.val.1.2) - slope (P w.val.2.1) (P w.val.2.2)) ≤ 0 := by
  have hw := D.crossing_props w
  have hv := D.crossing_props v
  have hvm := D.crossingPoint_mem v
  have hwm := D.crossingPoint_mem w
  have h₀ := C.support _ hw.1 _ hv.1 hc _ (openSegment_subset_segment ℝ _ _ hvm.1)
  have h₁ := A.support _ hw.2.1 _ hv.2.1 ha _ (openSegment_subset_segment ℝ _ _ hvm.2)
  have h₂ := (height_of_mem_openSegment (D.right _ hw.1).ne hwm.1).2
  have h₃ := (height_of_mem_openSegment (D.right _ hw.2.1).ne hwm.2).2
  have h₄ := height_difference (P w.val.1.1) (P w.val.1.2) (P w.val.2.1) (P w.val.2.2)
    (D.crossingPoint v).1 (D.crossingPoint w).1
  linarith only [h₀, h₁, h₂, h₃, h₄]

lemma ConvexCover.crossing_eq_of_x (C : ConvexCover D I) (hD : D.NoMultiple)
    (w v : ↥D.crossings) (hc : C.owner w.val.1 = C.owner v.val.1)
    (h : (D.crossingPoint w).1 = (D.crossingPoint v).1) : w = v := by
  have hw := D.crossing_props w
  have hv := D.crossing_props v
  have hvm := D.crossingPoint_mem v
  have hwm := D.crossingPoint_mem w
  have h₀ := C.support _ hw.1 _ hv.1 hc _ (openSegment_subset_segment ℝ _ _ hvm.1)
  have h₁ := C.support _ hv.1 _ hw.1 hc.symm _ (openSegment_subset_segment ℝ _ _ hwm.1)
  have h₂ := (height_of_mem_openSegment (D.right _ hw.1).ne hwm.1).2
  have h₃ := (height_of_mem_openSegment (D.right _ hv.1).ne hvm.1).2
  apply D.crossingPoint_injective hD
  apply Prod.ext h
  rw [h] at h₁ h₂
  linarith only [h₀, h₁, h₂, h₃]

lemma ConvexCover.crossing_sign_injective (C : ConvexCover D I) (A : ConcaveCover D J)
    (hP : Position P) (hx : Function.Injective (fun v => (P v).1)) (hD : D.NoMultiple) :
    Function.Injective (fun w : ↥D.crossings =>
      (C.owner w.val.1, A.owner w.val.2,
        decide (slope (P w.val.1.1) (P w.val.1.2) < slope (P w.val.2.1) (P w.val.2.2)))) := by
  intro w v hh
  have hc := congrArg Prod.fst hh
  have ha := congrArg (fun p => p.2.1) hh
  have hs : (slope (P w.val.1.1) (P w.val.1.2) < slope (P w.val.2.1) (P w.val.2.2)) ↔
      (slope (P v.val.1.1) (P v.val.1.2) < slope (P v.val.2.1) (P v.val.2.2)) :=
    by simpa only [decide_eq_decide] using (congrArg (fun p => p.2.2) hh)
  have hw := C.crossing_support A w v hc ha
  have hv := C.crossing_support A v w hc.symm ha.symm
  apply C.crossing_eq_of_x hD w v hc
  have hnw := D.crossing_slopes_ne hP hx w
  have hnv := D.crossing_slopes_ne hP hx v
  by_cases h : slope (P w.val.1.1) (P w.val.1.2) < slope (P w.val.2.1) (P w.val.2.2)
  · have h' := hs.mp h
    have hxw : (D.crossingPoint w).1 ≤ (D.crossingPoint v).1 := by nlinarith only [hw, h]
    have hxv : (D.crossingPoint v).1 ≤ (D.crossingPoint w).1 := by nlinarith only [hv, h']
    exact le_antisymm hxw hxv
  · have h' := mt hs.mpr h
    have hnw' := lt_of_le_of_ne (le_of_not_gt h) hnw.symm
    have hnv' := lt_of_le_of_ne (le_of_not_gt h') hnv.symm
    have hxw : (D.crossingPoint w).1 ≤ (D.crossingPoint v).1 := by nlinarith only [hv, hnv']
    have hxv : (D.crossingPoint v).1 ≤ (D.crossingPoint w).1 := by nlinarith only [hw, hnw']
    exact le_antisymm hxw hxv

end PlanarHalving.PlaneGraph

namespace PlanarHalving.Batches
open PlaneGraph

variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.card_edges (S : @System n R k a P) : S.edges.card = R * a ^ 2 := by
  classical
  rw [System.edges, Finset.card_biUnion]
  · simp [Finset.card_product, S.card_loss, S.card_gain, pow_two]
  · intro b _ c _ hbc
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact hbc (S.batch_unique (Finset.mem_product.mp he) (Finset.mem_product.mp hf))

lemma System.token_fixed_of_outside (S : @System n R k a P) [NeZero a]
    (j : Fin a) (u : ↥(S.marks 0)) (hu : u.val ∉ S.vertices) (b : Fin (R + 1)) :
    (S.tokenState j b u : Fin n) = u.val := by
  induction b using Fin.induction with
  | zero => simp
  | succ b ih =>
    rcases S.token_step j u b with h | ⟨hl,hg⟩
    · exact h.symm.trans ih
    · have he : ((S.tokenState j b.castSucc u : Fin n), (S.tokenState j b.succ u : Fin n)) ∈ S.edges :=
        (S.mem_edges _).mpr ⟨b,hl,hg⟩
      have hv := (S.edge_ends he).1
      rw [ih] at hv
      exact False.elim (hu hv)

lemma System.trace_token_mem (S : @System n R k a P) [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) : (S.trace he).token.val ∈ S.vertices := by
  by_contra hn
  have hh := S.token_fixed_of_outside (S.trace he).number (S.trace he).token hn (S.trace he).batch.castSucc
  rw [(S.trace he).source] at hh
  exact hn (hh ▸ (S.edge_ends he).1)

lemma System.convexOwner_mem (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) :
    S.convexOwner e ∈ Finset.univ ×ˢ S.vertices := by
  rw [S.convexOwner_eq he]
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, S.trace_token_mem he⟩

end PlanarHalving.Batches

namespace PlanarHalving.PlaneGraph
variable {V : Type*} [Fintype V] {P : V → Point} {I J : Type*} {D : Drawing P}

theorem ConvexCover.crossing_bound_finset [DecidableEq I] [DecidableEq J]
    (C : ConvexCover D I) (A : ConcaveCover D J) (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (hD : D.NoMultiple)
    (ci : Finset I) (cj : Finset J)
    (hci : ∀ e ∈ D.edges, C.owner e ∈ ci) (hcj : ∀ e ∈ D.edges, A.owner e ∈ cj) :
    D.crossings.card ≤ 2 * ci.card * cj.card := by
  classical
  let f := fun w : (V × V) × (V × V) =>
    (C.owner w.1, A.owner w.2,
      decide (slope (P w.1.1) (P w.1.2) < slope (P w.2.1) (P w.2.2)))
  have hm : Set.MapsTo f (D.crossings : Set _) (↑(ci ×ˢ (cj ×ˢ (Finset.univ : Finset Bool))) : Set _) := by
    intro w hw
    have hp := D.crossing_props ⟨w,hw⟩
    exact Finset.mem_product.mpr ⟨hci _ hp.1,
      Finset.mem_product.mpr ⟨hcj _ hp.2.1, Finset.mem_univ _⟩⟩
  have hi : (D.crossings : Set _).InjOn f := by
    intro w hw v hv hh
    exact congrArg Subtype.val (C.crossing_sign_injective A hP hx hD (a₁ := ⟨w,hw⟩) (a₂ := ⟨v,hv⟩) hh)
  have hc := Finset.card_le_card_of_injOn f hm hi
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_bool,
    mul_comm, mul_left_comm, mul_assoc] using hc

end PlanarHalving.PlaneGraph

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ChainDrawing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open PlaneGraph
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.flip_vertices (S : @System n R k a P) : S.flip.vertices = S.vertices := by
  classical
  ext u
  simp only [System.vertices, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨e,he,hu⟩ | ⟨e,he,hu⟩)
    · exact Or.inr ⟨e.swap, (S.flip_edge e.swap).mp (by simpa using he), hu⟩
    · exact Or.inl ⟨e.swap, (S.flip_edge e.swap).mp (by simpa using he), hu⟩
  · rintro (⟨e,he,hu⟩ | ⟨e,he,hu⟩)
    · exact Or.inr ⟨e.swap, (S.flip_edge e).mpr he, hu⟩
    · exact Or.inl ⟨e.swap, (S.flip_edge e).mpr he, hu⟩

lemma System.concaveOwner_mem (S : @System n R k a P) [NeZero n] [NeZero a]
    {e : Fin n × Fin n} (he : e ∈ S.edges) :
    S.concaveCover.owner e ∈ Finset.univ ×ˢ S.vertices := by
  have h := S.flip.convexOwner_mem ((S.flip_edge e).mpr he)
  rwa [S.flip_vertices] at h

theorem System.crossing_cap (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Position P) (hx : Function.Injective (fun v => (P v).1))
    (hD : S.drawing.NoMultiple) :
    S.drawing.crossings.card ≤ 2 * a^2 * S.vertices.card^2 := by
  have h := S.convexCover.crossing_bound_finset S.concaveCover hP hx hD
    (Finset.univ ×ˢ S.vertices) (Finset.univ ×ˢ S.vertices)
    (fun _ he => S.convexOwner_mem he) (fun _ he => S.concaveOwner_mem he)
  simpa [Finset.card_product, pow_two, mul_assoc, mul_left_comm, mul_comm] using h

end PlanarHalving.Batches

namespace PlanarHalving.PlaneGraph
variable {V : Type*} [Fintype V] {P : V → Point}

lemma Drawing.restrict_crossings (D : Drawing P) (E : Finset (V × V)) :
    (D.restrictEdges E).crossings ⊆ D.crossings := by
  classical
  intro w hw
  simp only [Drawing.crossings, Drawing.restrictEdges, Finset.mem_filter,
    Finset.mem_product, Finset.mem_inter] at hw ⊢
  exact ⟨⟨hw.1.1.1,hw.1.2.1⟩,hw.2⟩

end PlanarHalving.PlaneGraph

namespace PlanarHalving.Batches
open PlaneGraph
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertices_le (S : @System n R k a P) : S.vertices.card ≤ n := by
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

theorem System.localized_crossing (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) (F : Finset (Fin n)) (hF : F ⊆ S.vertices) :
    ((S.edges.filter fun e => e.1 ∈ F).card : ℝ)^3 ≤
      4608 * (a : ℝ)^2 * F.card * (S.vertices.card : ℝ)^3 +
        13824 * (S.vertices.card : ℝ)^3 := by
  classical
  let D := S.drawing.restrictEdges (S.edges.filter fun e => e.1 ∈ F)
  have hv : D.vertices = S.vertices := rfl
  have he : D.edges = S.edges.filter (fun e => e.1 ∈ F) := by
    ext e
    simp [D, Drawing.restrictEdges, System.drawing]
  have hc := D.designated_crossing hP.1 (PlaneGraph.Generic.x_injective hP) F hF (by
    intro e he'
    rw [he] at he'
    exact Or.inl (Finset.mem_filter.mp he').2)
  rw [he,hv] at hc
  have hcr : (D.crossings.card : ℝ) ≤ 2 * (a : ℝ)^2 * (S.vertices.card : ℝ)^2 := by
    exact_mod_cast (Finset.card_le_card (S.drawing.restrict_crossings _)).trans
      (S.crossing_cap hP.1 (PlaneGraph.Generic.x_injective hP) (S.drawing.noMultiple_of_generic hP))
  apply hc.trans
  calc 2304 * (F.card : ℝ) * S.vertices.card * D.crossings.card +
        13824 * (S.vertices.card : ℝ)^3 ≤
      2304 * (F.card : ℝ) * S.vertices.card * (2 * (a : ℝ)^2 * (S.vertices.card : ℝ)^2) +
        13824 * (S.vertices.card : ℝ)^3 := by gcongr
    _ = _ := by ring

theorem System.cubed_bound (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) :
    (R : ℝ)^3 * (a : ℝ)^4 ≤ 18432 * (n : ℝ)^4 := by
  classical
  have hc := S.localized_crossing hP S.vertices (by rfl)
  have he : S.edges.filter (fun e => e.1 ∈ S.vertices) = S.edges := by
    exact Finset.filter_eq_self.mpr (fun e he => (S.edge_ends he).1)
  rw [he, S.card_edges] at hc
  push_cast at hc
  have hs : (S.vertices.card : ℝ) ≤ n := by exact_mod_cast S.vertices_le
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast (NeZero.one_le : 1 ≤ a)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (NeZero.one_le : 1 ≤ n)
  have hs₁ : 4608 * (a : ℝ)^2 * S.vertices.card * (S.vertices.card : ℝ)^3 ≤
      4608 * (a : ℝ)^2 * (n : ℝ)^4 := by
    calc _ ≤ 4608 * (a : ℝ)^2 * n * (n : ℝ)^3 := by gcongr
      _ = _ := by ring
  have hs₂ : 13824 * (S.vertices.card : ℝ)^3 ≤ 13824 * (a : ℝ)^2 * (n : ℝ)^4 := by
    calc _ ≤ 13824 * (n : ℝ)^3 := by gcongr
      _ = 13824 * (1 : ℝ)^2 * (1 * (n : ℝ)^3) := by ring
      _ ≤ 13824 * (a : ℝ)^2 * (n * (n : ℝ)^3) := by gcongr
      _ = _ := by ring
  have hh : (a : ℝ)^2 * ((R : ℝ)^3 * (a : ℝ)^4) ≤
      (a : ℝ)^2 * (18432 * (n : ℝ)^4) := by
    nlinarith only [hc, hs₁, hs₂]
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < (a : ℝ)^2)).mp hh

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Tokens
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology

lemma sum_cube_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i)^3 ≤ (s.card : ℝ)^2 * ∑ i ∈ s, (f i)^3 := by
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s (f := f) (p := 3) (by norm_num) hf
  norm_num only [show (3 : ℝ)-1=2 by norm_num, Real.rpow_ofNat] at hh
  exact hh

lemma sum_angular_power_le {ι : Type*} (s : Finset ι) (θ : ι → ℝ)
    (hθ : ∀ i ∈ s, 0 ≤ θ i) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∑ i ∈ s, θ i ^ α) ≤ (s.card : ℝ)^(1-α) * (∑ i ∈ s, θ i)^α := by
  by_cases hs : s.Nonempty
  · have hc : 0 < (s.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
    have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
      (f := fun i => θ i^α) (p := α⁻¹) ((one_le_inv₀ hα).mpr hα1)
      (fun i hi => Real.rpow_nonneg (hθ i hi) α)
    have hsum : 0 ≤ ∑ i ∈ s, θ i^α := Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hθ i hi) α)
    have hsum' : 0 ≤ ∑ i ∈ s, θ i := Finset.sum_nonneg hθ
    have hev (i : ι) (hi : i ∈ s) : (θ i^α)^α⁻¹ = θ i := Real.rpow_rpow_inv (hθ i hi) hα.ne'
    simp_rw [Finset.sum_congr rfl hev] at hh
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hsum _) hh hα.le
    rw [← Real.rpow_mul hsum,inv_mul_cancel₀ hα.ne',Real.rpow_one,
      Real.mul_rpow (Real.rpow_nonneg hc.le _) hsum',← Real.rpow_mul hc.le] at hp
    have he : (α⁻¹-1)*α = 1-α := by
      calc
        (α⁻¹-1)*α = α⁻¹*α - α := by ring
        _ = 1-α := by rw [inv_mul_cancel₀ hα.ne']
    rwa [he] at hp
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [he,Finset.sum_empty,Finset.card_empty,Nat.cast_zero]
    rw [Real.zero_rpow hα.ne',mul_zero]

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology

lemma high_mass_bound {ι : Type*} (S : Finset ι) (lam s : ι → ℝ)
    {q M H : ℝ} (hq : 0 < q) (hM : 0 < M)
    (hlam : ∀ i ∈ S, lam i ≤ q⁻¹)
    (htail : ∀ u > 0, ((S.filter fun i => u < s i).card : ℝ) ≤ H * u^(-(4:ℝ)/3)) :
    ∑ i ∈ S with M*q^(-(3:ℝ)/4) < s i, lam i ≤ H*M^(-(4:ℝ)/3) := by
  classical
  let t := M*q^(-(3:ℝ)/4)
  have ht : 0 < t := mul_pos hM (Real.rpow_pos_of_pos hq _)
  have hpow : t^(-(4:ℝ)/3) = M^(-(4:ℝ)/3)*q := by
    dsimp [t]
    rw [Real.mul_rpow hM.le (Real.rpow_nonneg hq.le _),← Real.rpow_mul hq.le]
    norm_num
  have hp := mul_le_mul_of_nonneg_right (htail t ht) (inv_nonneg.mpr hq.le)
  rw [hpow] at hp
  have hbound := Finset.sum_le_sum (s := S.filter (fun i => t < s i))
    (f := lam) (g := fun _ => q⁻¹) (fun i hi => hlam i (Finset.mem_filter.mp hi).1)
  simp only [Finset.sum_const, nsmul_eq_mul] at hbound
  apply hbound.trans
  convert hp using 1; field_simp

lemma activity_sum_bound {ι : Type*} (S : Finset ι) (μ b θ : ι → ℝ)
    {q B B₀ T α : ℝ} (hq : 0 ≤ q) (hB : 0 ≤ B) (_hT : 0 ≤ T)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hcard : (S.card : ℝ) ≤ q) (hb : ∑ i ∈ S, b i ≤ B₀)
    (hθ : ∀ i ∈ S, 0 ≤ θ i) (hθsum : ∑ i ∈ S, θ i ≤ T)
    (hμ : ∀ i ∈ S, μ i ≤ 2*b i+B*θ i^α) :
    ∑ i ∈ S, μ i ≤ 2*B₀+B*q^(1-α)*T^α := by
  have hsum0 : 0 ≤ ∑ i ∈ S, θ i := Finset.sum_nonneg hθ
  have hc := Real.rpow_le_rpow (Nat.cast_nonneg S.card) hcard (sub_nonneg.mpr hα1)
  have hθp := Real.rpow_le_rpow hsum0 hθsum hα.le
  have hpow := (sum_angular_power_le S θ hθ hα hα1).trans
    (mul_le_mul hc hθp (Real.rpow_nonneg hsum0 _) (Real.rpow_nonneg hq _))
  have hsum := Finset.sum_le_sum hμ
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hm := mul_le_mul_of_nonneg_left hpow hB
  nlinarith only [hsum,hb,hm]

lemma low_cube_bound {ι : Type*} (S : Finset ι) (lam μ s : ι → ℝ)
    {q M A U : ℝ} (hq : 0 < q) (hM : 0 < M) (hA : 0 ≤ A)
    (hcard : (S.card : ℝ) ≤ q)
    (hlam : ∀ i ∈ S, 0 ≤ lam i) (hμ : ∀ i ∈ S, 0 ≤ μ i) (hs : ∀ i ∈ S, 0 ≤ s i)
    (hmass : ∀ i ∈ S, (lam i)^3 ≤ A*(s i)^3*μ i)
    (hμsum : ∑ i ∈ S, μ i ≤ U) :
    (∑ i ∈ S with s i ≤ M*q^(-(3:ℝ)/4), lam i)^3 ≤
      A*M^3*q^(-(1:ℝ)/4)*U := by
  classical
  let t := M*q^(-(3:ℝ)/4)
  let L := S.filter (fun i => s i ≤ t)
  have ht : 0 < t := mul_pos hM (Real.rpow_pos_of_pos hq _)
  have hL (i : ι) (hi : i ∈ L) : i ∈ S ∧ s i ≤ t := Finset.mem_filter.mp hi
  have hμsumL : ∑ i ∈ L, μ i ≤ U :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun i hi _ => hμ i hi)).trans hμsum
  have hmassL : ∑ i ∈ L, (lam i)^3 ≤ A*t^3*U := by
    calc
      _ ≤ ∑ i ∈ L, A*t^3*μ i := by
        apply Finset.sum_le_sum
        intro i hi
        apply (hmass i (hL i hi).1).trans
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hs i (hL i hi).1) (hL i hi).2 3) hA)
          (hμ i (hL i hi).1)
      _ = A*t^3 * ∑ i ∈ L, μ i := by rw [Finset.mul_sum]
      _ ≤ A*t^3*U := mul_le_mul_of_nonneg_left hμsumL (by positivity)
  have hc : (L.card : ℝ) ≤ q := (Nat.cast_le.mpr (Finset.card_filter_le ..)).trans hcard
  have hcube := sum_cube_le L lam (fun i hi => hlam i (hL i hi).1)
  have hsumlam : 0 ≤ ∑ i ∈ L, (lam i)^3 := by
    exact Finset.sum_nonneg (fun i hi => pow_nonneg (hlam i (hL i hi).1) _)
  have hc2 : (L.card : ℝ)^2 ≤ q^2 := by nlinarith [show (0:ℝ) ≤ L.card from Nat.cast_nonneg _]
  have hbound := hcube.trans ((mul_le_mul_of_nonneg_right hc2 hsumlam).trans
    (mul_le_mul_of_nonneg_left hmassL (sq_nonneg q)))
  have he : q^2*t^3 = M^3*q^(-(1:ℝ)/4) := by
    dsimp [t]
    rw [mul_pow,← Real.rpow_mul_natCast hq.le]
    simp only [Nat.cast_ofNat]
    rw [← Real.rpow_ofNat q 2]
    calc
      q^(2:ℝ) * (M^3 * q^((-(3:ℝ)/4)*3)) =
        M^3*(q^(2:ℝ)*q^((-(3:ℝ)/4)*3)) := by ring
      _ = M^3*q^(-(1:ℝ)/4) := by rw [← Real.rpow_add hq]; congr 2; norm_num
  change (∑ i ∈ L, lam i)^3 ≤ _
  calc
    _ ≤ q^2*(A*t^3*U) := hbound
    _ = A*(q^2*t^3)*U := by ring
    _ = A*(M^3*q^(-(1:ℝ)/4))*U := by rw [he]
    _ = A*M^3*q^(-(1:ℝ)/4)*U := by ring

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology

lemma low_bound_tendsto_zero {q : ℕ → ℝ} (hq : ∀ n, 0 < q n)
    (hqtop : Tendsto q atTop atTop) {α : ℝ} (hα : (3:ℝ)/4 < α)
    (A M B₀ B T : ℝ) :
    Tendsto (fun n => A*M^3*(q n)^(-(1:ℝ)/4)*
      (2*B₀+B*(q n)^(1-α)*T^α)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => (q n)^(-(1:ℝ)/4)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (show (0:ℝ)<1/4 by norm_num)).comp hqtop
    convert hh using 1
    funext n
    rw [Function.comp_apply,neg_div]
  have h2 : Tendsto (fun n => (q n)^((3:ℝ)/4-α)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp hqtop
    convert hh using 1
    funext n
    rw [Function.comp_apply,neg_sub]
  have ht := (h1.const_mul (A*M^3*(2*B₀))).add
    (h2.const_mul (A*M^3*B*T^α))
  simp only [mul_zero,add_zero] at ht
  apply ht.congr
  intro n
  have he : (q n)^(-(1:ℝ)/4)*(q n)^(1-α) = (q n)^((3:ℝ)/4-α) := by
    rw [← Real.rpow_add (hq n)]
    congr 1
    ring
  calc
    _ = A*M^3*(2*B₀)*(q n)^(-(1:ℝ)/4) +
      A*M^3*B*T^α*((q n)^(-(1:ℝ)/4)*(q n)^(1-α)) := by rw [he]
    _ = _ := by ring

theorem mass_eq_zero {ι : Type*} (S : ℕ → Finset ι)
    (lam μ s b θ : ℕ → ι → ℝ) (q : ℕ → ℝ)
    {L A H B B₀ T α : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hα : (3:ℝ)/4 < α) (hα1 : α ≤ 1)
    (hq : ∀ n, 0 < q n) (hqtop : Tendsto q atTop atTop)
    (hcard : ∀ n, ((S n).card : ℝ) ≤ q n)
    (hlam0 : ∀ n i, i ∈ S n → 0 ≤ lam n i)
    (hlam1 : ∀ n i, i ∈ S n → lam n i ≤ (q n)⁻¹)
    (hμ0 : ∀ n i, i ∈ S n → 0 ≤ μ n i)
    (hs0 : ∀ n i, i ∈ S n → 0 ≤ s n i)
    (hθ0 : ∀ n i, i ∈ S n → 0 ≤ θ n i)
    (hmass : ∀ n i, i ∈ S n → (lam n i)^3 ≤ A*(s n i)^3*μ n i)
    (hactivity : ∀ n i, i ∈ S n → μ n i ≤ 2*b n i+B*(θ n i)^α)
    (hbsum : ∀ n, ∑ i ∈ S n, b n i ≤ B₀)
    (hθsum : ∀ n, ∑ i ∈ S n, θ n i ≤ T)
    (htail : ∀ n u, 0 < u → ((S n |>.filter fun i => u < s n i).card : ℝ) ≤
      H*u^(-(4:ℝ)/3))
    (hpartition : ∀ n, L ≤ ∑ i ∈ S n, lam n i) : L = 0 := by
  classical
  by_contra hne
  have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hne)
  have hdecay : Tendsto (fun M : ℝ => H*M^(-(4:ℝ)/3)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (show (0:ℝ)<4/3 by norm_num)).const_mul H
  obtain ⟨M,hM,hMH⟩ : ∃ M : ℝ, 0 < M ∧ H*M^(-(4:ℝ)/3) < L/2 := by
    have hev := (hdecay.eventually (eventually_lt_nhds (half_pos hLp))).and
      (eventually_gt_atTop (0:ℝ))
    obtain ⟨M,h1,h2⟩ := hev.exists
    exact ⟨M,h2,h1⟩
  have hμsum (n : ℕ) : ∑ i ∈ S n, μ n i ≤
      2*B₀+B*(q n)^(1-α)*T^α :=
    activity_sum_bound (S n) (μ n) (b n) (θ n) (hq n).le hB hT
      (by linarith) hα1 (hcard n) (hbsum n) (hθ0 n) (hθsum n) (hactivity n)
  have hdecay2 := low_bound_tendsto_zero hq hqtop hα A M B₀ B T
  have hthr : 0 < (L/2)^3 := pow_pos (half_pos hLp) _
  obtain ⟨n,hn⟩ := (hdecay2.eventually (eventually_lt_nhds hthr)).exists
  have hhigh := high_mass_bound (S n) (lam n) (s n) (hq n) hM (hlam1 n) (htail n)
  have hlow := low_cube_bound (S n) (lam n) (μ n) (s n) (hq n) hM hA
    (hcard n) (hlam0 n) (hμ0 n) (hs0 n) (hmass n) (hμsum n)
  have hlow' : (∑ i ∈ S n with s n i ≤ M*(q n)^(-(3:ℝ)/4), lam n i) < L/2 := by
    by_contra hnot
    have hlole : L/2 ≤ ∑ i ∈ S n with s n i ≤ M*(q n)^(-(3:ℝ)/4), lam n i := le_of_not_gt hnot
    have hp := pow_le_pow_left₀ (half_pos hLp).le hlole 3
    exact (not_lt_of_ge (hp.trans hlow)) hn
  have hsplit := Finset.sum_filter_add_sum_filter_not (S n)
    (fun i => s n i ≤ M*(q n)^(-(3:ℝ)/4)) (lam n)
  simp only [not_le] at hsplit
  have htotal := hpartition n
  linarith only [hhigh,hMH,hlow',hsplit,htotal]

end PlanarHalving.Boundary

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.AtomicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal
variable {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]

lemma finiteMeasure_tendsto_apply {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {E : Set X} (hE : (μ : Measure X) (frontier E) = 0) :
    Tendsto (fun n => μs n E) atTop (𝓝 (μ E)) := by
  by_cases hμ : μ = 0
  · subst μ
    have hmass := h.mass
    have hb (n : ℕ) : μs n E ≤ (μs n).mass := (μs n).apply_mono (subset_univ E)
    simpa using
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass (fun _ => zero_le) hb
  · have hn := FiniteMeasure.tendsto_normalize_of_tendsto h hμ
    have hE' : (μ.normalize : Measure X) (frontier E) = 0 := by
      rw [μ.toMeasure_normalize_eq_of_nonzero hμ,Measure.smul_apply,hE]
      simp
    have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn (by simpa only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_eq_zero] using hE')
    have hh := h.mass.mul ht
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using hh

omit [Nonempty X] in
lemma finiteMeasure_tendsto_thickening (μ : FiniteMeasure X) {F : Set X} (hF : IsClosed F)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (hp : ∀ n, 0 < r n) :
    Tendsto (fun n => μ (Metric.thickening (r n) F)) atTop (𝓝 (μ F)) := by
  have ht := tendsto_measure_thickening_of_isClosed (μ := (μ : Measure X)) ⟨1,by norm_num,measure_ne_top _ _⟩ hF
  have hr' : Tendsto r atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hr,Filter.Eventually.of_forall hp⟩
  have hh := (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure X) F)).comp (ht.comp hr')
  exact hh

lemma cubed_bound_limit_closed
    {μ lam : FiniteMeasure X} {μs lams : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hlam : Tendsto lams atTop (𝓝 lam))
    {c d : ℕ → ℝ} {C : ℝ} (hc : Tendsto c atTop (𝓝 C)) (hd : Tendsto d atTop (𝓝 0))
    (hbound : ∀ n U, MeasurableSet U → (lams n U : ℝ)^3 ≤ c n*(μs n U : ℝ)+d n)
    {F : Set X} (hF : IsClosed F) : (lam F : ℝ)^3 ≤ C*(μ F : ℝ) := by
  obtain ⟨r,hr,hnull⟩ := exists_null_frontiers_thickening ((μ : Measure X)+(lam : Measure X)) F
  have hb (j : ℕ) : (lam (Metric.thickening (r j) F) : ℝ)^3 ≤ C*(μ (Metric.thickening (r j) F) : ℝ) := by
    have hh := (hnull j).2
    rw [Measure.add_apply] at hh
    have hμ' := finiteMeasure_tendsto_apply hμ (add_eq_zero.mp hh).1
    have hlam' := finiteMeasure_tendsto_apply hlam (add_eq_zero.mp hh).2
    have hμR := NNReal.continuous_coe.tendsto _ |>.comp hμ'
    have hlamR := NNReal.continuous_coe.tendsto _ |>.comp hlam'
    have ht := le_of_tendsto_of_tendsto (hlamR.pow 3) ((hc.mul hμR).add hd)
      (Filter.Eventually.of_forall (fun n => hbound n _ Metric.isOpen_thickening.measurableSet))
    simpa only [add_zero] using ht
  have hp : ∀ j, 0 < r j := fun j => (hnull j).1
  have hμR := NNReal.continuous_coe.tendsto _ |>.comp (finiteMeasure_tendsto_thickening μ hF hr hp)
  have hlamR := NNReal.continuous_coe.tendsto _ |>.comp (finiteMeasure_tendsto_thickening lam hF hr hp)
  exact le_of_tendsto_of_tendsto (hlamR.pow 3) (hμR.const_mul C) (Filter.Eventually.of_forall hb)

omit [Nonempty X] in
lemma cubed_bound_of_compact [CompactSpace X]
    (μ lam : FiniteMeasure X) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ K : Set X, IsCompact K → (lam K : ℝ)^3 ≤ C*(μ K : ℝ))
    {F : Set X} (hF : MeasurableSet F) : (lam F : ℝ)^3 ≤ C*(μ F : ℝ) := by
  have hh (t : ℝ) (ht : t < (lam F : ℝ)) : t^3 ≤ C*(μ F : ℝ) := by
    by_cases ht0 : t < 0
    · exact (show t^3 ≤ 0 by have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) ht0.le; nlinarith).trans (mul_nonneg hC (NNReal.coe_nonneg _))
    · have ht0' : 0 ≤ t := le_of_not_gt ht0
      have ht' : ENNReal.ofReal t < (lam : Measure X) F := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal ht0' (measure_ne_top (lam : Measure X) F)]
        exact ht
      obtain ⟨K,hKF,hK,htK⟩ := hF.exists_lt_isCompact ht'
      have htK' : t < (lam K : ℝ) := by
        rwa [ENNReal.ofReal_lt_iff_lt_toReal ht0' (measure_ne_top (lam : Measure X) K)] at htK
      exact (pow_le_pow_left₀ ht0' htK'.le 3).trans ((hbound K hK).trans
        (mul_le_mul_of_nonneg_left (show (μ K : ℝ) ≤ μ F from (NNReal.coe_le_coe.mpr (μ.apply_mono hKF))) hC))
  have ht : Tendsto (fun t : ℝ => t^3) (𝓝[<] (lam F : ℝ)) (𝓝 ((lam F : ℝ)^3)) :=
    ((continuous_pow 3).tendsto _).mono_left inf_le_left
  exact le_of_tendsto ht (Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => hh t ht))

lemma cubed_bound_limit [CompactSpace X]
    {μ lam : FiniteMeasure X} {μs lams : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hlam : Tendsto lams atTop (𝓝 lam))
    {c d : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hc : Tendsto c atTop (𝓝 C)) (hd : Tendsto d atTop (𝓝 0))
    (hbound : ∀ n U, MeasurableSet U → (lams n U : ℝ)^3 ≤ c n*(μs n U : ℝ)+d n)
    {F : Set X} (hF : MeasurableSet F) : (lam F : ℝ)^3 ≤ C*(μ F : ℝ) :=
  cubed_bound_of_compact μ lam hC (fun _ hK => cubed_bound_limit_closed hμ hlam hc hd hbound hK.isClosed) hF

end PlanarHalving.Limits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Partition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.UniformPartition
open MeasureTheory Set
open scoped unitInterval

lemma cell_measurable (m : ℕ) [NeZero m] (i : Fin m) : MeasurableSet (cell m i) := by
  unfold cell
  split_ifs <;> measurability

lemma cell_lower (m : ℕ) [NeZero m] (i : Fin m) {t : I} (ht : t ∈ cell m i) :
    (i : ℝ)/(m : ℝ) ≤ (t : ℝ) := by
  unfold cell at ht
  split_ifs at ht <;> exact ht.1

lemma cell_upper (m : ℕ) [NeZero m] (i : Fin m) {t : I} (ht : t ∈ cell m i) :
    (t : ℝ) ≤ ((i : ℝ)+1)/(m : ℝ) := by
  unfold cell at ht
  split_ifs at ht
  · simpa [boundary] using (show (t : ℝ) ≤ (boundary m i.succ : ℝ) from ht.2)
  · simpa [boundary] using (show (t : ℝ) ≤ (boundary m i.succ : ℝ) from ht.2.le)

lemma cell_upper_lt (m : ℕ) [NeZero m] (i : Fin m) (hi : i.val+1≠m)
    {t : I} (ht : t ∈ cell m i) : (t : ℝ) < ((i : ℝ)+1)/(m : ℝ) := by
  rw [cell,ite_eq_right hi] at ht
  simpa [boundary] using (show (t : ℝ) < (boundary m i.succ : ℝ) from ht.2)

lemma cells_disjoint (m : ℕ) [NeZero m] : Pairwise (fun i j : Fin m => Disjoint (cell m i) (cell m j)) := by
  have hh (i j : Fin m) (hlt : i.val < j.val) : Disjoint (cell m i) (cell m j) := by
    apply Set.disjoint_left.mpr
    intro t hti htj
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    have hu := cell_upper_lt m i (by omega) hti
    have hl := cell_lower m j htj
    have hij' : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast hlt
    have hc := div_le_div_of_nonneg_right hij' hm.le
    linarith
  intro i j hij
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact hh i j h
  · exact (hh j i h).symm

lemma cells_cover (m : ℕ) [NeZero m] : (⋃ i : Fin m, cell m i) = univ := by
  ext t
  simp only [mem_iUnion,mem_univ,iff_true]
  exact mem_some_cell m t

lemma cell_volume (m : ℕ) [NeZero m] (i : Fin m) :
    volume (cell m i) = ENNReal.ofReal (1/(m : ℝ)) := by
  have he : ((boundary m i.succ : I) : ℝ) - ((boundary m i.castSucc : I) : ℝ) =
      1/(m : ℝ) := by simp [boundary]; ring
  unfold cell
  split_ifs
  · rw [unitInterval.volume_Icc,he]
  · rw [unitInterval.volume_Ico,he]

lemma cell_diameter_bound (m : ℕ) [NeZero m] (i : Fin m) {s t : I}
    (hs : s ∈ cell m i) (ht : t ∈ cell m i) : dist s t ≤ 1/(m : ℝ) := by
  rw [Subtype.dist_eq,Real.dist_eq]
  apply abs_le.mpr
  have hs0 := cell_lower m i hs
  have hs1 := cell_upper m i hs
  have ht0 := cell_lower m i ht
  have ht1 := cell_upper m i ht
  have he : ((i : ℝ)+1)/(m : ℝ) = (i : ℝ)/(m : ℝ)+1/(m : ℝ) := by ring
  rw [he] at hs1 ht1
  constructor <;> linarith

end PlanarHalving.UniformPartition

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter
open scoped unitInterval Topology

lemma mem_cell_index (m : ℕ) [NeZero m] (t : I) : t ∈ cell m (index m t) :=
  (mem_some_cell m t).choose_spec

lemma index_eq (m : ℕ) [NeZero m] (t : I) (i : Fin m) : index m t = i ↔ t ∈ cell m i := by
  constructor
  · intro h; rw [← h]; exact mem_cell_index m t
  · intro ht
    by_contra hne
    exact Set.disjoint_left.mp (cells_disjoint m hne) (mem_cell_index m t) ht

lemma index_measurable (m : ℕ) [NeZero m] : Measurable (index m) := by
  apply measurable_to_countable'
  intro i
  have he : (index m) ⁻¹' {i} = cell m i := by ext t; exact index_eq m t i
  rw [he]
  exact cell_measurable m i

lemma integral_partition {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ] (C : ι → Set X)
    (hC : ∀ i, MeasurableSet (C i))
    (idx : X → ι) (hi : ∀ x i, idx x = i ↔ x ∈ C i) (v : ι → ℝ) :
    ∫ x, v (idx x) ∂μ = ∑ i, μ.real (C i)*v i := by
  classical
  have he : (fun x => v (idx x)) = fun x => ∑ i, (C i).indicator (fun _ => v i) x := by
    funext x
    symm
    rw [Finset.sum_eq_single (idx x)]
    · exact Set.indicator_of_mem ((hi x (idx x)).mp rfl) _
    · intro j _ hj
      rw [Set.indicator_of_notMem]
      intro hx
      exact hj ((hi x j).mpr hx).symm
    · simp
  rw [he,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ (hC i)]
    simp only [smul_eq_mul]
  · intro i _
    exact (integrable_const (v i)).indicator (hC i)

end PlanarHalving.UniformPartition

namespace PlanarHalving.Limits
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology

lemma measure_le_of_test {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ ν : FiniteMeasure X)
    (h : ∀ f : BoundedContinuousFunction X ℝ, (∀ x, 0 ≤ f x) → ∫ x, f x ∂(μ : Measure X) ≤ ∫ x, f x ∂(ν : Measure X)) :
    (μ : Measure X) ≤ (ν : Measure X) := by
  have hn (f : BoundedContinuousFunction X NNReal) : ∫⁻ x, f x ∂(μ : Measure X) ≤ ∫⁻ x, f x ∂(ν : Measure X) := by
    let g : BoundedContinuousFunction X ℝ := ⟨⟨fun x => (f x : ℝ), continuous_subtype_val.comp f.continuous⟩,f.map_bounded'⟩
    apply (ENNReal.toReal_le_toReal (f.lintegral_lt_top_of_nnreal _).ne
      (f.lintegral_lt_top_of_nnreal _).ne).mp
    rw [toReal_lintegral_coe_eq_integral f μ,toReal_lintegral_coe_eq_integral f ν]
    exact h g (fun x => NNReal.coe_nonneg _)
  have hclosed (F : Set X) (hF : IsClosed F) : (μ : Measure X) F ≤ (ν : Measure X) F := by
    exact le_of_tendsto_of_tendsto (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (μ : Measure X))
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (ν : Measure X)) (Filter.Eventually.of_forall (fun n => hn (hF.apprSeq n)))
  apply Measure.le_iff.mpr
  intro F hF
  rw [hF.measure_eq_iSup_isCompact (μ : Measure X)]
  exact iSup_le (fun K => iSup_le (fun hKF => iSup_le (fun hK =>
    (hclosed K hK.isClosed).trans (measure_mono hKF))))

end PlanarHalving.Limits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology unitInterval NNReal ENNReal

lemma integral_weightedAtoms {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {α : Type*} [Fintype α] (w : ℝ≥0) (x : α → X) (f : X → ℝ) :
    ∫ t, f t ∂(weightedAtoms w x : Measure X) = (w : ℝ) * ∑ i, f (x i) := by
  classical
  change ∫ t, f t ∂((w : ℝ≥0∞) • ∑ i, Measure.dirac (x i)) = _
  rw [integral_smul_measure,integral_finsetSum_measure]
  · simp only [integral_dirac,ENNReal.coe_toReal,smul_eq_mul]
  · intro i _
    exact integrable_dirac (by simp)

lemma mass_weightedAtoms {X : Type*} [MeasurableSpace X] {α : Type*} [Fintype α]
    (w : ℝ≥0) (x : α → X) :
    (weightedAtoms w x).mass = w * Fintype.card α := by
  classical
  simp [weightedAtoms,FiniteMeasure.mass,FiniteMeasure.mk_apply,Measure.smul_apply,
    Measure.finsetSum_apply]

end PlanarHalving.Limits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Windows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval Classical

lemma measurable_carrier (J : Window) : MeasurableSet (carrier J) :=
  UniformPartition.cell_measurable _ _

lemma time_lt_one (R : ℕ) [NeZero R] (b : Fin R) : (time R b : ℝ)<1 := by
  apply (div_lt_one (Nat.cast_pos.mpr (NeZero.pos R))).mpr
  have hb : (b : ℝ)+1 ≤ R := by exact_mod_cast b.isLt
  linarith

lemma time_strictMono (R : ℕ) [NeZero R] : StrictMono (time R) := by
  intro b c hbc
  change ((b : ℝ)+1/2)/(R : ℝ)<((c : ℝ)+1/2)/(R : ℝ)
  have hh : (b : ℝ)<(c : ℝ) := by exact_mod_cast hbc
  exact div_lt_div_of_pos_right (by linarith only [hh])
    (Nat.cast_pos.mpr (NeZero.pos R))

lemma lt_cut_iff {α : Type*} [LinearOrder α] {R : ℕ} {t : Fin R → α}
    (ht : StrictMono t) (b : Fin R) (x : α) : b.val < cut t x ↔ t b < x := by
  constructor
  · intro h
    by_contra hbx
    have hsub : (Finset.univ.filter fun c => t c<x) ⊆ Finset.Iio b := by
      intro c hc
      apply Finset.mem_Iio.mpr
      apply ht.lt_iff_lt.mp
      exact ((Finset.mem_filter.mp hc).2).trans_le (le_of_not_gt hbx)
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hh
    exact (not_lt_of_ge hh) h
  · intro hb
    have hsub : Finset.Iic b ⊆ (Finset.univ.filter fun c => t c<x) := by
      intro c hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ht.monotone (Finset.mem_Iic.mp hc)).trans_lt hb⟩
    have hh := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hh
    exact hh

lemma mem_carrier_iff (R : ℕ) [NeZero R] (J : Window) (b : Fin R) :
    time R b ∈ carrier J ↔ start R J ≤ b.val ∧ b.val < stop R J := by
  have hlo := lt_cut_iff (time_strictMono R) b (UniformPartition.boundary (2^J.1) J.2.castSucc)
  have hhi := lt_cut_iff (time_strictMono R) b (UniformPartition.boundary (2^J.1) J.2.succ)
  have hl : UniformPartition.boundary (2^J.1) J.2.castSucc ≤ time R b ↔ start R J ≤ b.val := by
    simpa only [not_lt,start] using (not_congr hlo).symm
  change time R b ∈ UniformPartition.cell (2^J.1) J.2 ↔ _
  rw [UniformPartition.cell]
  split_ifs with hj
  · have hu : UniformPartition.boundary (2^J.1) J.2.succ = (1 : I) := by
      apply Subtype.ext
      change ((J.2.val+1 : ℕ) : ℝ)/(2^J.1 : ℕ)=1
      rw [hj,div_self (by positivity : ((2^J.1 : ℕ) : ℝ)≠0)]
    have hb : time R b < UniformPartition.boundary (2^J.1) J.2.succ := by
      rw [hu]; exact time_lt_one R b
    simp only [mem_Icc,hl,hb.le,and_true]
    exact (and_iff_left (hhi.mpr hb)).symm
  · exact and_congr hl hhi.symm

end PlanarHalving.TimeWindows

namespace PlanarHalving.Limits
open MeasureTheory Set
open scoped NNReal ENNReal Classical

lemma weightedAtoms_apply_finset {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {α : Type*} [Fintype α] (w : ℝ≥0) (x : α → X) {U : Set X} (hU : MeasurableSet U) :
    (weightedAtoms w x U : ℝ) = (w : ℝ) * ((Finset.univ.filter fun i => x i ∈ U).card : ℝ) := by
  classical
  have h := integral_weightedAtoms w x (U.indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const 1 hU] at h
  simpa only [smul_eq_mul,mul_one,measureReal_def,← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ENNReal.coe_toReal,Set.indicator_apply,Finset.sum_boole] using h

end PlanarHalving.Limits

namespace PlanarHalving.Batches
open MeasureTheory Set Limits
open scoped NNReal ENNReal Classical
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertexMeasure_apply (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (z : Fin n → X)
    {U : Set X} (hU : MeasurableSet U) :
    (S.vertexMeasure z U : ℝ) = ((S.vertices.filter fun v => z v ∈ U).card : ℝ)/(n : ℝ) := by
  classical
  rw [System.vertexMeasure,weightedAtoms_apply_finset _ _ hU]
  have he : (Finset.univ.filter fun v : ↥S.vertices => z v.val ∈ U).card =
      (S.vertices.filter fun v => z v ∈ U).card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      exact Finset.mem_filter.mpr ⟨v.property,(Finset.mem_filter.mp hv).2⟩
    · intro v _ w _ h; exact Subtype.ext h
    · intro v hv
      exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,by simpa using (Finset.mem_filter.mp hv).2,rfl⟩
  rw [he]
  simp only [NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]

lemma System.endpointMeasure_apply (S : @System n R k a P)
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (z : Fin n → X)
    (E : ℝ≥0) {U : Set X} (hU : MeasurableSet U) :
    (S.endpointMeasure z E U : ℝ) = ((S.edges.filter fun e => z e.1 ∈ U).card : ℝ)/(E : ℝ) := by
  classical
  rw [System.endpointMeasure,weightedAtoms_apply_finset _ _ hU]
  have he : (Finset.univ.filter fun e : ↥S.edges => z e.val.1 ∈ U).card =
      (S.edges.filter fun e => z e.1 ∈ U).card := by
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      exact Finset.mem_filter.mpr ⟨e.property,(Finset.mem_filter.mp he).2⟩
    · intro e _ f _ h; exact Subtype.ext h
    · intro e he
      exact ⟨⟨e,(Finset.mem_filter.mp he).1⟩,by simpa using (Finset.mem_filter.mp he).2,rfl⟩
  rw [he]
  simp only [NNReal.coe_inv,div_eq_inv_mul]

theorem System.atomic_cubed_bound (S : @System n R k a P) [NeZero n] [NeZero a]
    (hP : Generic P) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Fin n → X) {E : ℝ≥0} (hE : 0 < E) {U : Set X} (hU : MeasurableSet U) :
    (S.endpointMeasure z E U : ℝ)^3 ≤
      (4608 * (a : ℝ)^2 * n^4 / (E : ℝ)^3) *
        ((S.vertices.card : ℝ)/(n : ℝ))^3 * (S.vertexMeasure z U : ℝ) +
      13824 * (S.vertices.card : ℝ)^3 / (E : ℝ)^3 := by
  classical
  let F := S.vertices.filter fun v => z v ∈ U
  have hF : F ⊆ S.vertices := Finset.filter_subset _ _
  have hc := S.localized_crossing hP F hF
  have he : S.edges.filter (fun e => e.1 ∈ F) = S.edges.filter (fun e => z e.1 ∈ U) := by
    ext e
    simp only [Finset.mem_filter,F]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,(S.edge_ends h.1).1,h.2⟩⟩
  rw [he] at hc
  rw [S.endpointMeasure_apply z E hU,S.vertexMeasure_apply z hU]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hER : 0 < (E : ℝ) := hE
  have hc' := div_le_div_of_nonneg_right hc (le_of_lt (pow_pos hER 3))
  convert hc' using 1
  all_goals
    try dsimp only [F]
    try field_simp [hn,ne_of_gt hER]
    try ring
    try rfl

end PlanarHalving.Batches

namespace PlanarHalving.Batches
open Set TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.timeWindow_edges (S : @System n R k a P) [NeZero R] (J : Window) :
    (S.timeWindow J).edges ⊆ S.edges := S.window_edges _ _ _

lemma System.timeWindow_mem (S : @System n R k a P) [NeZero R] [NeZero a]
    (J : Window) (e : ↥S.edges) : e.val ∈ (S.timeWindow J).edges ↔ S.edgeTime e ∈ carrier J := by
  classical
  rw [System.edgeTime,mem_carrier_iff]
  constructor
  · intro he
    obtain ⟨b,hl,hg⟩ := ((S.timeWindow J).mem_edges e.val).mp he
    have hb := S.batch_unique (b := ⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩)
      ⟨hl,hg⟩ ⟨(S.trace e.property).loss,(S.trace e.property).gain⟩
    have heq := congrArg Fin.val hb
    have hbl := b.isLt
    have hs := start_add_length R J
    dsimp at heq
    omega
  · intro h
    let b : Fin (length R J) := ⟨(S.trace e.property).batch.val-start R J,by
      have := start_add_length R J
      omega⟩
    apply ((S.timeWindow J).mem_edges e.val).mpr
    refine ⟨b,?_,?_⟩
    all_goals
      have heq : (⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩ : Fin R) =
          (S.trace e.property).batch := by
        apply Fin.ext
        dsimp [b]
        omega
    · change e.val.1 ∈ S.loss ⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩
      rw [heq]
      exact (S.trace e.property).loss
    · change e.val.2 ∈ S.gain ⟨start R J+b.val,by have := start_add_length R J; have := stop_le R J; omega⟩
      rw [heq]
      exact (S.trace e.property).gain

lemma System.edgeTime_distribution (S : @System n R k a P) [NeZero R] [NeZero a]
    (b : Fin R) :
    (Finset.univ.filter fun e : ↥S.edges => (S.trace e.property).batch=b).card=a^2 := by
  classical
  have he : (Finset.univ.filter fun e : ↥S.edges => (S.trace e.property).batch=b).card =
      ((S.loss b).product (S.gain b)).card := by
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      have hh := (Finset.mem_filter.mp he).2
      exact Finset.mem_product.mpr (hh ▸ ⟨(S.trace e.property).loss,(S.trace e.property).gain⟩)
    · intro e _ f _ h; exact Subtype.ext h
    · intro e he
      have hm : e∈S.edges := (S.mem_edges e).mpr ⟨b,Finset.mem_product.mp he⟩
      refine ⟨⟨e,hm⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
      exact S.batch_unique ⟨(S.trace hm).loss,(S.trace hm).gain⟩ (Finset.mem_product.mp he)
  rw [he]
  calc
    _ = (S.loss b).card * (S.gain b).card := Finset.card_product _ _
    _ = a^2 := by rw [S.card_loss,S.card_gain,pow_two]

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Directions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter UniformPartition Limits
open scoped Topology unitInterval NNReal

lemma time_mem_cell (m : ℕ) [NeZero m] (i : Fin m) : time m i∈cell m i := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have h₁ : (i : ℝ)/(m : ℝ)≤((i : ℝ)+1/2)/(m : ℝ) := by gcongr; norm_num
  have h₂ : ((i : ℝ)+1/2)/(m : ℝ)<((i : ℝ)+1)/(m : ℝ) := by gcongr; norm_num
  unfold cell
  split_ifs
  · constructor
    · exact h₁
    · change ((i : ℝ)+1/2)/(m : ℝ)≤((i.val+1 : ℕ):ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using h₂.le
  · constructor
    · exact h₁
    · change ((i : ℝ)+1/2)/(m : ℝ)<((i.val+1 : ℕ):ℝ)/(m : ℝ)
      simpa only [Nat.cast_add,Nat.cast_one] using h₂

lemma midpointGrid_measurable (m : ℕ) [NeZero m] : Measurable (midpointGrid m) :=
  (measurable_of_finite (time m)).comp (index_measurable m)

lemma midpointGrid_dist (m : ℕ) [NeZero m] (t : I) : dist (midpointGrid m t) t≤1/(m : ℝ) :=
  cell_diameter_bound m (index m t) (time_mem_cell m _) (mem_cell_index m t)

lemma midpointGrid_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)]
    (hm : Tendsto m atTop atTop) (t : I) :
    Tendsto (fun n => midpointGrid (m n) t) atTop (𝓝 t) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => midpointGrid_dist (m n) t)
  have hnat : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hnat

lemma integral_midpointGrid (m : ℕ) [NeZero m] (f : I → ℝ) :
    ∫ t, f (midpointGrid m t) = (∑ i : Fin m, f (time m i))/(m : ℝ) := by
  change ∫ t, (fun i : Fin m => f (time m i)) (index m t) = _
  rw [integral_partition volume (cell m) (cell_measurable m) (index m) (index_eq m) (fun i : Fin m => f (time m i))]
  simp only [measureReal_def,cell_volume,ENNReal.toReal_ofReal (by positivity : 0≤1/(m : ℝ))]
  rw [← Finset.mul_sum]
  ring

lemma midpoint_riemann_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop)
    (f : BoundedContinuousFunction I ℝ) :
    Tendsto (fun n => (∑ i : Fin (m n), f (time (m n) i))/(m n : ℝ)) atTop
      (𝓝 (∫ t : I, f t)) := by
  simp_rw [← integral_midpointGrid]
  apply tendsto_integral_of_dominated_convergence (fun _ : I => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (midpointGrid_measurable (m n))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall (fun _ => f.norm_coe_le_norm _)
  · exact Eventually.of_forall (fun t => (f.continuous.tendsto t).comp (midpointGrid_tendsto m hm t))

lemma timeMeasure_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => weightedAtoms (m n : ℝ≥0)⁻¹ (time (m n))) atTop
      (𝓝 (⟨volume,inferInstance⟩ : FiniteMeasure I)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun n => ∫ x, f x ∂(weightedAtoms (m n : ℝ≥0)⁻¹ (time (m n)) : Measure I))
    atTop (𝓝 (∫ t : I, f t))
  simpa only [integral_weightedAtoms,NNReal.coe_inv,NNReal.coe_natCast,
    ← div_eq_inv_mul] using midpoint_riemann_tendsto m hm f

end PlanarHalving.TimeWindows

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]

lemma restriction_limit_eq {μ lam : FiniteMeasure X} {μs lams : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hlam : Tendsto lams atTop (𝓝 lam))
    {S : Set X} (_hS : MeasurableSet S) (hbd : (μ : Measure X) (frontier S)=0)
    (he : ∀ n, (lams n : Measure X)=(μs n : Measure X).restrict S) :
    (lam : Measure X)=(μ : Measure X).restrict S := by
  let ν : FiniteMeasure X := ⟨(μ : Measure X).restrict S,inferInstance⟩
  have hclosed (F : Set X) (hF : IsClosed F) : lam F=ν F := by
    obtain ⟨r,hr,hnull⟩ := exists_null_frontiers_thickening ((μ : Measure X)+(lam : Measure X)) F
    have hval (j : ℕ) : lam (Metric.thickening (r j) F)=ν (Metric.thickening (r j) F) := by
      let U := Metric.thickening (r j) F
      have hU : MeasurableSet U := Metric.isOpen_thickening.measurableSet
      have hnullμ : (μ : Measure X) (frontier U)=0 := by
        have hh := (hnull j).2
        rw [Measure.add_apply] at hh
        exact (add_eq_zero.mp hh).1
      have hnullLam : (lam : Measure X) (frontier U)=0 := by
        have hh := (hnull j).2
        rw [Measure.add_apply] at hh
        exact (add_eq_zero.mp hh).2
      have hnullUS : (μ : Measure X) (frontier (U∩S))=0 :=
        measure_mono_null ((frontier_inter_subset U S).trans
          (union_subset_union inter_subset_left inter_subset_right)) (measure_union_null hnullμ hbd)
      have h₁ := finiteMeasure_tendsto_apply hlam hnullLam
      have h₂ := finiteMeasure_tendsto_apply hμ hnullUS
      have h₂' : Tendsto (fun n => lams n U) atTop (𝓝 (ν U)) := by
        convert h₂ using 1
        · funext n
          change ((lams n : Measure X) U).toNNReal = _
          rw [he n,Measure.restrict_apply hU]
          rfl
        · change 𝓝 (((μ : Measure X).restrict S U).toNNReal) = _
          rw [Measure.restrict_apply hU]
          rfl
      exact tendsto_nhds_unique h₁ h₂'
    have h₁ := finiteMeasure_tendsto_thickening lam hF hr (fun j => (hnull j).1)
    have h₂ := finiteMeasure_tendsto_thickening ν hF hr (fun j => (hnull j).1)
    exact tendsto_nhds_unique (h₁.congr (fun j => hval j)) h₂
  have heF (F : Set X) (hF : IsClosed F) : (lam : Measure X) F=(ν : Measure X) F := by
    simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) (hclosed F hF)
  change (lam : Measure X)=(ν : Measure X)
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  rw [← compl_compl U,measure_compl hU.isClosed_compl.measurableSet (measure_ne_top _ _),
    measure_compl hU.isClosed_compl.measurableSet (measure_ne_top _ _),
    heF univ isClosed_univ,heF Uᶜ hU.isClosed_compl]

end PlanarHalving.Limits
namespace PlanarHalving.Limits
open MeasureTheory
open scoped NNReal

lemma map_weightedAtoms {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    {α : Type*} [Fintype α] (w : ℝ≥0) (x : α → X) {f : X → Y} (hf : Measurable f) :
    (weightedAtoms w x).map f=weightedAtoms w (f∘x) := by
  classical
  apply FiniteMeasure.toMeasure_injective
  change Measure.map f (w • (∑ i, Measure.dirac (x i) : Measure X))=
    w • (∑ i, Measure.dirac (f (x i)) : Measure Y)
  rw [Measure.map_smul,Measure.map_finset_sum hf.aemeasurable]
  simp only [Measure.map_dirac]

end PlanarHalving.Limits
namespace PlanarHalving.Batches
open MeasureTheory Set Filter Limits TimeWindows
open scoped Topology NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.sum_edgeTime (S : @System n R k a P) [NeZero R] [NeZero a] (f : I → ℝ) :
    ∑ e : ↥S.edges, f (S.edgeTime e) = (a : ℝ)^2 * ∑ b : Fin R, f (time R b) := by
  classical
  change ∑ e : ↥S.edges, f (time R (S.trace e.property).batch)=_
  rw [← Finset.sum_fiberwise' Finset.univ (fun e : ↥S.edges => (S.trace e.property).batch)
    (fun b => f (time R b))]
  simp only [Finset.sum_const,S.edgeTime_distribution,nsmul_eq_mul,Nat.cast_pow]
  exact (Finset.mul_sum ..).symm

lemma System.edgeTime_atoms (S : @System n R k a P) [NeZero R] [NeZero a] :
    weightedAtoms ((R : ℝ≥0)*(a : ℝ≥0)^2)⁻¹ S.edgeTime=
      weightedAtoms (R : ℝ≥0)⁻¹ (time R) := by
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  simp only [integral_weightedAtoms,S.sum_edgeTime,NNReal.coe_inv,NNReal.coe_mul,
    NNReal.coe_pow,NNReal.coe_natCast]
  have hR : (R : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne R)
  have ha : (a : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
  field_simp

lemma System.labelTimeMeasure_time (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (z : Fin n → X) :
    (S.labelTimeMeasure z).map Prod.snd=weightedAtoms (R : ℝ≥0)⁻¹ (time R) := by
  rw [System.labelTimeMeasure,map_weightedAtoms _ _ measurable_snd]
  exact S.edgeTime_atoms

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.RankMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.time_marginal {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) :
    L.edgeTime.map Prod.snd=⟨volume,inferInstance⟩ := by
  have hm := (FiniteMeasure.continuous_map continuous_snd).tendsto L.edgeTime |>.comp h.edgeTime
  have ht := timeMeasure_tendsto (fun n => (F n).R) hR
  apply tendsto_nhds_unique hm
  convert ht using 1
  funext n
  exact (F n).system.labelTimeMeasure_time _

end PlanarHalving.RankLimits
namespace PlanarHalving.UniformPartition
open MeasureTheory Set
open scoped unitInterval

lemma volume_frontier_cell (m : ℕ) [NeZero m] (i : Fin m) :
    volume (frontier (cell m i))=0 := by
  let a := boundary m i.castSucc
  let b := boundary m i.succ
  have hab : (a : ℝ)<(b : ℝ) := by
    apply div_lt_div_of_pos_right _ (Nat.cast_pos.mpr (NeZero.pos m))
    simp only [Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    linarith
  have hpair : (Subtype.val : I → ℝ) ⁻¹' {(a : ℝ),(b : ℝ)}={a,b} := by
    ext t
    simp only [mem_preimage,mem_insert_iff,mem_singleton_iff,Subtype.coe_inj]
  unfold cell
  split_ifs
  · change volume (frontier ((Subtype.val : I → ℝ) ⁻¹' Icc (a : ℝ) (b : ℝ)))=0
    apply measure_mono_null (continuous_subtype_val.frontier_preimage_subset _)
    rw [frontier_Icc hab.le,hpair]
    exact Set.Finite.measure_zero ((Set.finite_singleton b).insert a) _
  · change volume (frontier ((Subtype.val : I → ℝ) ⁻¹' Ico (a : ℝ) (b : ℝ)))=0
    apply measure_mono_null (continuous_subtype_val.frontier_preimage_subset _)
    rw [frontier_Ico hab,hpair]
    exact Set.Finite.measure_zero ((Set.finite_singleton b).insert a) _

end PlanarHalving.UniformPartition
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.null_time_boundary {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.edgeTime : Measure (Labels×I)) (frontier (Prod.snd ⁻¹' carrier J))=0 := by
  apply measure_mono_null (continuous_snd.frontier_preimage_subset _)
  rw [← Measure.map_apply measurable_snd isClosed_frontier.measurableSet]
  have he : (Measure.map Prod.snd (L.edgeTime : Measure (Labels×I)))=volume :=
    congrArg (fun m : FiniteMeasure I => (m : Measure I)) (h.time_marginal hR)
  rw [he]
  exact UniformPartition.volume_frontier_cell _ _

lemma Converges.restriction_eq {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.timeRestrict J : Measure (Labels×I))=(L.edgeTime : Measure (Labels×I)).restrict (Prod.snd ⁻¹' carrier J) :=
  restriction_limit_eq h.edgeTime (h.timeRestrict J)
    ((measurable_carrier J).preimage measurable_snd) (h.null_time_boundary hR J) (fun _ => rfl)

lemma Converges.restriction_mass {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    ((L.timeRestrict J).mass : ℝ≥0∞)=(2^J.1 : ℝ≥0∞)⁻¹ := by
  rw [FiniteMeasure.ennreal_mass,h.restriction_eq hR,Measure.restrict_apply MeasurableSet.univ,univ_inter]
  rw [← Measure.map_apply measurable_snd (measurable_carrier J)]
  have he : (Measure.map Prod.snd (L.edgeTime : Measure (Labels×I)))=volume :=
    congrArg (fun m : FiniteMeasure I => (m : Measure I)) (h.time_marginal hR)
  rw [he]
  rw [TimeWindows.carrier,UniformPartition.cell_volume]
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast,one_div]
  norm_cast

end PlanarHalving.RankLimits
namespace PlanarHalving.Batches
open MeasureTheory Set Limits TimeWindows
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.window_endpoint_eq (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Fin n → X) (J : Window) :
    ((S.labelTimeMeasure z).restrict (Prod.snd ⁻¹' carrier J)).map Prod.fst=
      (S.timeWindow J).endpointMeasure z ((R : ℝ≥0)*(a : ℝ≥0)^2) := by
  classical
  apply FiniteMeasure.eq_of_forall_toMeasure_apply_eq
  intro U hU
  have he : ((((S.labelTimeMeasure z).restrict (Prod.snd ⁻¹' carrier J)).map Prod.fst) U : ℝ)=
      ((S.timeWindow J).endpointMeasure z ((R : ℝ≥0)*(a : ℝ≥0)^2) U : ℝ) := by
    rw [FiniteMeasure.map_apply _ measurable_fst hU,
      FiniteMeasure.restrict_apply _ _ (hU.preimage measurable_fst),
      System.labelTimeMeasure,weightedAtoms_apply_finset _ _
        ((hU.preimage measurable_fst).inter ((measurable_carrier J).preimage measurable_snd)),
      System.endpointMeasure,weightedAtoms_apply_finset _ _ hU]
    congr 2
    apply Finset.card_bij (fun e he =>
      (⟨e.val,(S.timeWindow_mem J e).mpr (by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_inter_iff,Set.mem_preimage] at he
        exact he.2)⟩ : ↥(S.timeWindow J).edges))
    · intro e he
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,
        Set.mem_inter_iff,Set.mem_preimage] at he ⊢
      exact he.1
    · intro e _ f _ hef
      exact Subtype.ext (congrArg (fun x : ↥(S.timeWindow J).edges => x.val) hef)
    · intro e he
      let f : ↥S.edges := ⟨e.val,S.timeWindow_edges J e.property⟩
      refine ⟨f,?_,rfl⟩
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,
        Set.mem_inter_iff,Set.mem_preimage] at he ⊢
      exact ⟨he,(S.timeWindow_mem J f).mp e.property⟩
  have he' := NNReal.coe_injective he
  simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) he'

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Configuration.edgeWindow_eq (F : Configuration) (J : Window) :
    F.edgeWindow J=(F.system.timeWindow J).endpointMeasure (F.label ∘ F.point)
      ((F.R : ℝ≥0)*(F.a : ℝ≥0)^2) := F.system.window_endpoint_eq _ J

lemma Configuration.vertices_mass_ratio (F : Configuration) (J : Window) :
    ((F.vertices J).mass : ℝ)=((F.system.timeWindow J).vertices.card : ℝ)/(F.n : ℝ) := by
  rw [Configuration.vertices,System.vertexMeasure,mass_weightedAtoms,Fintype.card_coe]
  simp only [NNReal.coe_mul,NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]

end PlanarHalving.RankLimits
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology

lemma measure_le_of_weak_limits {X : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {μ ν : FiniteMeasure X} {μs νs : ℕ → FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hν : Tendsto νs atTop (𝓝 ν))
    (h : ∀ n, (μs n : Measure X) ≤ (νs n : Measure X)) :
    (μ : Measure X) ≤ (ν : Measure X) := by
  apply measure_le_of_test
  intro f hf
  exact le_of_tendsto_of_tendsto
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f)
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν f)
    (Eventually.of_forall (fun n => integral_mono_measure (h n)
      (Eventually.of_forall hf) (BoundedContinuousFunction.integrable (νs n : Measure X) f)))

end PlanarHalving.Limits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Sweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

lemma States.Greedy.packing (S : @States n T k P) {a : ℕ}
    (Q : S.Greedy 0 a) (C : Finset (Fin (T+1) × Fin (T+1)))
    (hC : StepDisjoint C) (horder : ∀ p∈C, p.1≤p.2)
    (hd : ∀ p∈C, 2*a-1≤S.distance p.1 p.2) : C.card≤Q.count := by
  classical
  have hex (p : ↥C) : ∃ j : Fin Q.count, p.val.1 < Q.index j.succ ∧ Q.index j.succ≤p.val.2 :=
    Q.hit _ _ (Fin.zero_le _) (horder _ p.property) (hd _ p.property)
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro p q he
    by_contra hpq
    have hdis := hC _ p.property _ q.property (fun h => hpq (Subtype.ext h))
    exact Set.disjoint_left.mp hdis (hf p) (by simpa only [Set.mem_Ioc,he] using hf q)
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hinj

lemma States.greedy_packing (S : @States n T k P) {d : ℕ} (hd : 0 < d)
    (C : Finset (Fin (T+1) × Fin (T+1))) (hC : StepDisjoint C)
    (horder : ∀ p∈C, p.1≤p.2) (hdist : ∀ p∈C, d≤S.distance p.1 p.2) :
    C.card≤(S.greedy 0 ((d+1)/2) (by omega)).count := by
  apply (S.greedy 0 ((d+1)/2) (by omega)).packing S C hC horder
  intro p hp
  exact (show 2*((d+1)/2)-1≤d by omega).trans (hdist p hp)

lemma States.distance_packing_cubic (S : @States n T k P) (hP : Generic P) [NeZero n]
    {d : ℕ} (hd : 0 < d) (C : Finset (Fin (T+1) × Fin (T+1)))
    (hC : StepDisjoint C) (horder : ∀ p∈C, p.1≤p.2)
    (hdist : ∀ p∈C, d≤S.distance p.1 p.2) :
    (C.card : ℝ)^3*(d : ℝ)^4≤294912*(n : ℝ)^4 := by
  let a := (d+1)/2
  have ha : 0 < a := by dsimp [a]; omega
  let : NeZero a := ⟨ne_of_gt ha⟩
  let Q := S.greedy 0 a ha
  have hcount : C.card≤Q.count := S.greedy_packing hd C hC horder hdist
  have hbound := (S.greedySystem a ha).cubed_bound hP
  have hda : (d : ℝ)≤2*(a : ℝ) := by exact_mod_cast (show d≤2*a by dsimp [a]; omega)
  calc
    _ ≤ (Q.count : ℝ)^3*(2*(a : ℝ))^4 := by gcongr
    _ = 16*((Q.count : ℝ)^3*(a : ℝ)^4) := by ring
    _ ≤ 16*(18432*(n : ℝ)^4) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = _ := by ring

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

lemma States.intervalActivity_pos_distance (S : @States n T k P)
    {u v : Fin (T+1)} (h : u≤v) (ha : 0<(S.intervalActivity u v h).card) :
    1≤S.distance u v := by
  exact activity_pos_distance P (fun i : ↥(Finset.Icc u v) => S.slope i)
    (fun i => S.marks i) ⟨u,Finset.mem_Icc.mpr ⟨le_rfl,h⟩⟩
    ⟨v,Finset.mem_Icc.mpr ⟨h,le_rfl⟩⟩ (fun i => S.card_marks i)
    (fun i => S.separates i) (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).1)
    (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).2) ha

lemma states_intervalActivity_distance {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n)
    {c : ℕ} {u v : Fin ((traversal (criticalSlopes P)).size+1)} (huv : u≤v)
    (hc : 4*c≤((states P hP hk).intervalActivity u v huv).card) :
    (∃ hk' : k+c≤n, c≤(states P hP hk').distance u v) ∨
    (∃ hk' : k-c≤n, c≤k ∧ c≤(states P hP hk').distance u v) := by
  let S := states P hP hk
  have hi (i) : Function.Injective (fun x => projection (S.slope i) (P x)) :=
    projection_injective (PlaneGraph.Generic.x_injective hP) ((traversal _).sample_not_mem i)
  have hd := activity_distance P (fun i : ↥(Finset.Icc u v) => S.slope i)
    (fun i => S.marks i) ⟨u,Finset.mem_Icc.mpr ⟨le_rfl,huv⟩⟩
    ⟨v,Finset.mem_Icc.mpr ⟨huv,le_rfl⟩⟩ (fun i => S.card_marks i)
    (fun i => S.separates i) (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).1)
    (fun i => S.increasing.monotone (Finset.mem_Icc.mp i.property).2) (hi u) (hi v) hc
  rcases hd with ⟨hk',E,E',hE,hE',hs,hs',hd⟩ | ⟨hck,E,E',hE,hE',hs,hs',hd⟩
  · left
    refine ⟨hk',?_⟩
    have he : E=(states P hP hk').marks u := states_unique hs (states P hP hk' |>.separates u) (hE.trans (states P hP hk' |>.card_marks u).symm)
    have he' : E'=(states P hP hk').marks v := states_unique hs' (states P hP hk' |>.separates v) (hE'.trans (states P hP hk' |>.card_marks v).symm)
    simpa only [he,he',States.distance,setDistance] using hd
  · right
    have hk' : k-c≤n := (Nat.sub_le _ _).trans hk
    refine ⟨hk',hck,?_⟩
    have he : E=(states P hP hk').marks u := states_unique hs (states P hP hk' |>.separates u) (hE.trans (states P hP hk' |>.card_marks u).symm)
    have he' : E'=(states P hP hk').marks v := states_unique hs' (states P hP hk' |>.separates v) (hE'.trans (states P hP hk' |>.card_marks v).symm)
    simpa only [he,he',States.distance,setDistance] using hd

lemma cube_add_le {x y : ℝ} (hx : 0≤x) (hy : 0≤y) : (x+y)^3≤4*(x^3+y^3) := by
  nlinarith [mul_nonneg (sq_nonneg (x-y)) (add_nonneg hx hy)]

lemma activity_packing_cubic {n k : ℕ} (P : Fin n → Point) (hP : Generic P)
    [NeZero n] (hk : k≤n) {b : ℕ} (hb : 0<b)
    (C : Finset (Fin ((traversal (criticalSlopes P)).size+1) × Fin ((traversal (criticalSlopes P)).size+1)))
    (hC : StepDisjoint C) (horder : ∀ p∈C, p.1≤p.2)
    (hactivity : ∀ p, ∀ hp : p∈C, b≤((states P hP hk).intervalActivity p.1 p.2 (horder p hp)).card) :
    (C.card : ℝ)^3*(b : ℝ)^4≤10000000000*(n : ℝ)^4 := by
  classical
  let S := states P hP hk
  by_cases hb4 : 4≤b
  · let c := b/4
    have hc : 0<c := by dsimp [c]; omega
    have hbLe : (b : ℝ)≤8*(c : ℝ) := by exact_mod_cast (show b≤8*c by dsimp [c]; omega)
    let A := C.filter (fun p => ∃ hk' : k+c≤n, c≤(states P hP hk').distance p.1 p.2)
    let B := C\A
    have hA : A⊆C := Finset.filter_subset _ _
    have hB : B⊆C := Finset.sdiff_subset
    have hbound (D : Finset _) (hD : D⊆C) (r : ℕ)
        (hd : ∀ p∈D, ∃ hr : r≤n, c≤(states P hP hr).distance p.1 p.2) :
        (D.card : ℝ)^3*(c : ℝ)^4≤294912*(n : ℝ)^4 := by
      by_cases hne : D.Nonempty
      · obtain ⟨p,hp⟩ := hne
        obtain ⟨hr,_⟩ := hd p hp
        apply (states P hP hr).distance_packing_cubic hP hc D
        · exact fun p hp q hq hpq => hC p (hD hp) q (hD hq) hpq
        · exact fun p hp => horder p (hD hp)
        · intro p hp
          obtain ⟨hr',hh⟩ := hd p hp
          exact hh
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero,zero_pow (by omega : (3:ℕ)≠0),zero_mul]
        positivity
    have hAb := hbound A hA (k+c) (fun p hp => (Finset.mem_filter.mp hp).2)
    have hBb := hbound B hB (k-c) (fun p hp => by
      have hpC := hB hp
      have hh := states_intervalActivity_distance P hP hk (horder p hpC)
        ((show 4*c≤b from Nat.mul_div_le b 4).trans (hactivity p hpC))
      rcases hh with hh | ⟨hr,_,hh⟩
      · exact False.elim ((Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hpC,hh⟩))
      · exact ⟨hr,hh⟩)
    have hcard : (C.card : ℝ)=(A.card : ℝ)+(B.card : ℝ) := by
      exact_mod_cast (by simpa only [B,Nat.add_comm] using (Finset.card_sdiff_add_card_eq_card hA).symm : C.card=A.card+B.card)
    have hsum := mul_le_mul_of_nonneg_right (cube_add_le (show (0:ℝ)≤A.card by positivity) (show (0:ℝ)≤B.card by positivity)) (show (0:ℝ)≤(c : ℝ)^4 by positivity)
    rw [← hcard] at hsum
    have hcub : (C.card : ℝ)^3*(c : ℝ)^4≤2359296*(n : ℝ)^4 := by nlinarith [hAb,hBb]
    calc
      _ ≤ (C.card : ℝ)^3*(8*(c : ℝ))^4 := by gcongr
      _ = 4096*((C.card : ℝ)^3*(c : ℝ)^4) := by ring
      _ ≤ 4096*(2359296*(n : ℝ)^4) := mul_le_mul_of_nonneg_left hcub (by norm_num)
      _ ≤ _ := by nlinarith [sq_nonneg ((n : ℝ)^2)]
  · have hd := S.distance_packing_cubic hP (by omega : 0<1) C hC horder
      (fun p hp => S.intervalActivity_pos_distance (horder p hp) (lt_of_lt_of_le hb (hactivity p hp)))
    norm_num at hd
    have hbLe : (b : ℝ)≤3 := by exact_mod_cast (by omega : b≤3)
    calc
      _ ≤ (C.card : ℝ)^3*3^4 := by gcongr
      _ ≤ 294912*(n : ℝ)^4*3^4 := mul_le_mul_of_nonneg_right hd (by norm_num)
      _ ≤ _ := by nlinarith [sq_nonneg ((n : ℝ)^2)]

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.WindowMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.edgeWindow_mass {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    ((L.edgeWindow J).mass : ℝ)=((2^J.1 : ℕ) : ℝ)⁻¹ := by
  have he := h.restriction_mass hR J
  have hm : (L.edgeWindow J).mass=(L.timeRestrict J).mass := by
    change (L.timeRestrict J).map Prod.fst univ=(L.timeRestrict J) univ
    rw [FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ,preimage_univ]
  rw [hm]
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.coe_toReal,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    Nat.cast_pow,Nat.cast_ofNat] using hh

end PlanarHalving.RankLimits

namespace PlanarHalving.Sweep
open Set

lemma activity_family_cubic {n k : ℕ} (P : Fin n → Point) (hP : Generic P)
    [NeZero n] (hk : k≤n) {b : ℕ} (hb : 0<b)
    {ι : Type*} [DecidableEq ι] (D : Finset ι)
    (u v : ι → Fin ((traversal (criticalSlopes P)).size+1))
    (huv : ∀ i∈D, u i≤v i)
    (hdisjoint : ∀ i∈D, ∀ j∈D, i≠j → Disjoint (Ioc (u i) (v i)) (Ioc (u j) (v j)))
    (hactivity : ∀ i, ∀ hi : i∈D, b≤((states P hP hk).intervalActivity (u i) (v i) (huv i hi)).card) :
    (D.card : ℝ)^3*(b : ℝ)^4≤10000000000*(n : ℝ)^4 := by
  classical
  let f := fun i => (u i,v i)
  have hlt (i) (hi : i∈D) : u i<v i := by
    apply lt_of_le_of_ne (huv i hi)
    intro he
    have ha := (states P hP hk).intervalActivity_pos_distance (huv i hi) (hb.trans_le (hactivity i hi))
    rw [he,States.distance_self] at ha
    omega
  have hinj : Set.InjOn f D := by
    intro i hi j hj he
    by_contra hne
    have hu : u i=u j := congrArg Prod.fst he
    have hv : v i=v j := congrArg Prod.snd he
    exact Set.disjoint_left.mp (hdisjoint i hi j hj hne)
      (show v i∈Ioc (u i) (v i) from ⟨hlt i hi,le_rfl⟩)
      (by rw [hv,hu] at *; exact ⟨hlt j hj,le_rfl⟩)
  have hh := activity_packing_cubic P hP hk hb (D.image f) ?_ ?_ ?_
  · rwa [Finset.card_image_iff.mpr hinj] at hh
  · intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    exact hdisjoint i hi j hj (fun he => hpq (congrArg f he))
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact huv i hi
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hactivity i hi

lemma cubic_to_tail {x u : ℝ} (hx : 0≤x) (hu : 0<u)
    (h : x^3*u^4≤10000000000) : x≤10000*u^(-(4:ℝ)/3) := by
  have hp : (u^(-(4:ℝ)/3))^3=u^(-(4:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hu.le]
    norm_num
  have he : u^(-(4:ℝ))=(u^4)⁻¹ := by rw [Real.rpow_neg hu.le]; norm_num
  have hpos : 0≤10000*u^(-(4:ℝ)/3) := by positivity
  apply (pow_le_pow_iff_left₀ hx hpos (by omega : (3:ℕ)≠0)).mp
  rw [mul_pow,hp,he]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hu 4)).mpr (h.trans (by norm_num : (10000000000:ℝ)≤10000^3))

end PlanarHalving.Sweep

namespace PlanarHalving.Batches
open Set Sweep
variable {n R k a T : ℕ} {P : Fin n → Point}

lemma System.vertices_subset_activity (S : @System n R k a P) (H : @States n T k P)
    (index : Fin (R+1) → Fin (T+1)) (hm : Monotone index)
    (hmarks : ∀ j, S.marks j=H.marks (index j)) :
    S.vertices ⊆ H.intervalActivity (index 0) (index (Fin.last R))
      (hm (Fin.zero_le _)) := by
  classical
  have he (b : Fin R) (x : Fin n)
      (hx : (x∈S.marks b.castSucc ∧ x∉S.marks b.succ) ∨
            (x∉S.marks b.castSucc ∧ x∈S.marks b.succ)) :
      x∈H.intervalActivity (index 0) (index (Fin.last R)) (hm (Fin.zero_le _)) := by
    rw [States.mem_intervalActivity]
    rw [hmarks,hmarks] at hx
    by_cases hx0 : x∈H.marks (index 0)
    · rcases hx with hx | hx
      · exact ⟨index b.succ,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inr ⟨hx.2,hx0⟩⟩
      · exact ⟨index b.castSucc,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inr ⟨hx.1,hx0⟩⟩
    · rcases hx with hx | hx
      · exact ⟨index b.castSucc,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inl ⟨hx.1,hx0⟩⟩
      · exact ⟨index b.succ,hm (Fin.zero_le _),hm (Fin.le_last _),Or.inl ⟨hx.2,hx0⟩⟩
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨e,he',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,_⟩ := (S.mem_edges e).mp he'
    exact he b e.1 (Or.inl (Finset.mem_sdiff.mp hb))
  · obtain ⟨e,he',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,_,hb⟩ := (S.mem_edges e).mp he'
    exact he b e.2 (Or.inr (And.symm (Finset.mem_sdiff.mp hb)))

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Sweep Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Configuration.SweepEmbedding.stop_le_start {F : Configuration} (E : F.SweepEmbedding)
    {A B : Window} (hAB : Before A B) : E.stop A≤E.start B :=
  E.increasing.monotone (TimeWindows.stop_le_start F.R hAB)

lemma Configuration.SweepEmbedding.vertices_subset {F : Configuration} (E : F.SweepEmbedding) (J : Window) :
    (F.system.timeWindow J).vertices ⊆ (states F.point F.generic E.rank_le).intervalActivity
      (E.start J) (E.stop J) (E.start_le_stop J) := by
  let index : Fin (length F.R J+1) → Fin ((traversal (criticalSlopes F.point)).size+1) :=
    fun j => E.index ⟨TimeWindows.start F.R J+j.val,by have:=start_add_length F.R J;have:=stop_le F.R J;have:=j.isLt;omega⟩
  have hmono : Monotone index := by
    intro i j hij
    apply E.increasing.monotone
    exact Nat.add_le_add_left hij _
  have he := (F.system.timeWindow J).vertices_subset_activity
    (states F.point F.generic E.rank_le) index hmono (fun j => E.marks _)
  have hstart : index 0=E.start J := by congr 1
  have hstop : index (Fin.last (length F.R J))=E.stop J := by
    apply congrArg E.index
    apply Fin.ext
    exact start_add_length F.R J
  simpa only [hstart,hstop] using he

lemma before_of_same_depth {m : ℕ} {i j : Fin (2^m)} (hij : i<j) : Before ⟨m,i⟩ ⟨m,j⟩ := by
  change ((i.val+1 : ℕ) : ℝ)/(2^m : ℕ)≤(j : ℝ)/(2^m : ℕ)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (show i.val+1≤j.val from hij)

lemma Configuration.SweepEmbedding.windows_disjoint {F : Configuration} (E : F.SweepEmbedding)
    {m : ℕ} {i j : Fin (2^m)} (hij : i≠j) :
    Disjoint (Ioc (E.start ⟨m,i⟩) (E.stop ⟨m,i⟩)) (Ioc (E.start ⟨m,j⟩) (E.stop ⟨m,j⟩)) := by
  rcases lt_or_gt_of_ne hij with hh | hh
  · exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hi.2.trans (E.stop_le_start (before_of_same_depth hh))) hj.1)
  · exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hj.2.trans (E.stop_le_start (before_of_same_depth hh))) hi.1)

lemma Configuration.SweepEmbedding.activity_tail {F : Configuration} (E : F.SweepEmbedding)
    (m : ℕ) {u : ℝ} (hu : 0<u) :
    (((Finset.univ.filter fun i : Fin (2^m) => u<((F.vertices ⟨m,i⟩).mass : ℝ)).card : ℝ))≤
      10000*u^(-(4:ℝ)/3) := by
  classical
  let D := Finset.univ.filter fun i : Fin (2^m) => u<((F.vertices ⟨m,i⟩).mass : ℝ)
  let b := ⌊u*(F.n : ℝ)⌋₊+1
  have hb : 0<b := by dsimp [b];omega
  have hn : (0:ℝ)<F.n := Nat.cast_pos.mpr F.n_pos
  have hcard (i) (hi : i∈D) : b≤(F.system.timeWindow ⟨m,i⟩).vertices.card := by
    have hi' := (Finset.mem_filter.mp hi).2
    rw [F.vertices_mass_ratio] at hi'
    have hlt := (lt_div_iff₀ hn).mp hi'
    change ⌊u*(F.n : ℝ)⌋₊+1≤_
    exact Nat.succ_le_of_lt ((Nat.floor_lt (mul_nonneg hu.le hn.le)).mpr hlt)
  have hh := activity_family_cubic F.point F.generic E.rank_le hb D
    (fun i => E.start ⟨m,i⟩) (fun i => E.stop ⟨m,i⟩)
    (fun i _hi => E.start_le_stop ⟨m,i⟩)
    (fun _i _hi _j _hj hij => E.windows_disjoint hij)
    (fun i hi => (hcard i hi).trans (Finset.card_le_card (E.vertices_subset ⟨m,i⟩)))
  have hb' : u*(F.n : ℝ)≤(b : ℝ) := by
    dsimp [b]
    rw [Nat.cast_add,Nat.cast_one]
    exact (Nat.lt_floor_add_one _).le
  have hh' : (D.card : ℝ)^3*(u*(F.n : ℝ))^4≤10000000000*(F.n : ℝ)^4 := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hu.le hn.le) hb' 4) (by positivity)).trans hh
  have hcub : (D.card : ℝ)^3*u^4≤10000000000 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hn 4)).mp
    nlinarith [hh']
  exact cubic_to_tail (by positivity) hu hcub

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.activity_tail {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (m : ℕ) {u : ℝ} (hu : 0<u) :
    (((Finset.univ.filter fun i : Fin (2^m) => u<((L.vertices ⟨m,i⟩).mass : ℝ)).card : ℝ))≤
      10000*u^(-(4:ℝ)/3) := by
  classical
  have hh : ∀ᶠ j in atTop, ∀ i : Fin (2^m), u<((L.vertices ⟨m,i⟩).mass : ℝ) →
      u<(((F j).vertices ⟨m,i⟩).mass : ℝ) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : u<((L.vertices ⟨m,i⟩).mass : ℝ)
    · have hm := NNReal.continuous_coe.tendsto _ |>.comp
        (FiniteMeasure.continuous_mass.tendsto _ |>.comp (h.vertices ⟨m,i⟩))
      exact ((tendsto_order.mp hm).1 u hi).mono (fun j hj _ => hj)
    · exact Eventually.of_forall (fun _ => fun hh => (hi hh).elim)
  obtain ⟨j,hj⟩ := hh.exists
  apply le_trans _ ((E j).activity_tail m hu)
  have hs : (Finset.univ.filter fun i : Fin (2^m) => u<((L.vertices ⟨m,i⟩).mass : ℝ)) ⊆
      (Finset.univ.filter fun i : Fin (2^m) => u<(((F j).vertices ⟨m,i⟩).mass : ℝ)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj i (Finset.mem_filter.mp hi).2⟩
  exact Nat.cast_le.mpr (Finset.card_le_card hs)

lemma timePartition_cover (m : ℕ) (t : I) : ∃ J∈timePartition m, t∈carrier J := by
  have ht : t∈⋃ i : Fin (2^m),carrier ⟨m,i⟩ := by
    change t∈⋃ i : Fin (2^m), UniformPartition.cell (2^m) i
    rw [UniformPartition.cells_cover];trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp ht
  exact ⟨⟨m,i⟩,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩

lemma filter_timePartition (m : ℕ) (p : Window → Prop) [DecidablePred p] :
    (timePartition m |>.filter p).card = (Finset.univ.filter fun i : Fin (2^m) => p ⟨m,i⟩).card := by
  classical
  rw [timePartition,Finset.filter_image,Finset.card_image_of_injective _ (fun _ _ he => eq_of_heq (Sigma.mk.inj he).2)]

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.MeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
lemma card_filter_attached {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x : ↥s => p x.val)).card = (s.filter p).card := by
  classical
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext x
  simp [and_comm]
end PlanarHalving
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma eventually_lt_closed {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {F : Set X} (hF : IsClosed F)
    {q : ℝ} (hq : (μ F : ℝ)<q) : ∀ᶠ n in atTop, (μs n F : ℝ)<q := by
  have hq0 : 0<q := lt_of_le_of_lt (NNReal.coe_nonneg _) hq
  have hq' : (μ : Measure X) F<ENNReal.ofReal q := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hq0).mpr hq
  have ht := (FiniteMeasure.limsup_measure_closed_le_of_tendsto h hF).trans_lt hq'
  have he := eventually_lt_of_limsup_lt ht
  filter_upwards [he] with n hn
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff hq0).mp (by simpa only [ENNReal.ofReal_coe_nnreal] using hn)

end PlanarHalving.Limits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter PlaneGraph
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Configuration.edgeWindow_apply (F : Configuration) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (F.edgeWindow J U : ℝ)=
      (((F.system.timeWindow J).edges.filter (fun e : Fin F.n×Fin F.n => F.label (F.point e.1)∈U)).card : ℝ)/
        ((F.R : ℝ)*F.a^2) := by
  classical
  rw [F.edgeWindow_eq,System.endpointMeasure,weightedAtoms_apply_finset _ _ hU]
  simp only [Function.comp_apply]
  rw [card_filter_attached _ (fun e : Fin F.n×Fin F.n => F.label (F.point e.1)∈U)]
  simp only [NNReal.coe_inv,NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast,
    div_eq_inv_mul]

end PlanarHalving.RankLimits
namespace PlanarHalving.UniformPartition
open Set
open scoped unitInterval

lemma cell_refinement (m d : ℕ) [NeZero m] [NeZero d] (i : Fin (m*d)) :
    cell (m*d) i ⊆ cell m ⟨i.val/d,(Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr i.isLt⟩ := by
  intro t ht
  let j : Fin m := ⟨i.val/d,(Nat.div_lt_iff_lt_mul (NeZero.pos d)).mpr i.isLt⟩
  have hm : (0:ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hd : (0:ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hlo : (j:ℝ)*d ≤ (i:ℝ) := by
    exact_mod_cast Nat.div_mul_le_self i.val d
  have hhi : (i:ℝ)+1 ≤ ((j:ℝ)+1)*d := by
    have hr := Nat.mod_lt i.val (NeZero.pos d)
    have he := Nat.mod_add_div i.val d
    have hh : i.val+1 ≤ (i.val/d+1)*d := by nlinarith
    exact_mod_cast hh
  have hlow : (j:ℝ)/(m:ℝ) ≤ (t:ℝ) := by
    apply le_trans _ (cell_lower (m*d) i ht)
    rw [Nat.cast_mul]
    apply (div_le_div_iff₀ hm (mul_pos hm hd)).mpr
    nlinarith
  have hup : ((i:ℝ)+1)/((m*d:ℕ):ℝ) ≤ ((j:ℝ)+1)/(m:ℝ) := by
    rw [Nat.cast_mul]
    apply (div_le_div_iff₀ (mul_pos hm hd) hm).mpr
    nlinarith
  change t∈cell m j
  unfold cell
  split_ifs with hj
  · refine ⟨hlow,?_⟩
    change (t:ℝ) ≤ _
    simpa only [boundary,Fin.val_succ,Nat.cast_add,Nat.cast_one] using (cell_upper (m*d) i ht).trans hup
  · have hi : i.val+1≠m*d := by
      intro hi
      have hsur : i.val+1 ≤ (j.val+1)*d := by exact_mod_cast hhi
      have hjlt : j.val+1 < m := by omega
      have hh := Nat.mul_lt_mul_of_pos_right hjlt (NeZero.pos d)
      omega
    refine ⟨hlow,?_⟩
    change (t:ℝ) < _
    simpa only [boundary,Fin.val_succ,Nat.cast_add,Nat.cast_one] using (cell_upper_lt (m*d) i hi ht).trans_le hup

lemma exists_cell_refinement (m d N : ℕ) [NeZero m] [NeZero d] [NeZero N]
    (hN : N=m*d) (i : Fin N) : ∃ j : Fin m, cell N i⊆cell m j := by
  subst N
  exact ⟨_,cell_refinement m d i⟩

end PlanarHalving.UniformPartition
namespace PlanarHalving.TimeWindows
open Set
open scoped unitInterval

lemma carrier_refinement (d m : ℕ) (i : Fin (2^(d+m))) :
    ∃ j : Fin (2^d), carrier ⟨d+m,i⟩⊆carrier ⟨d,j⟩ := by
  exact UniformPartition.exists_cell_refinement (2^d) (2^m) (2^(d+m)) (pow_add 2 d m) i

lemma same_depth_disjoint {d : ℕ} {i j : Fin (2^d)} (hij : i≠j) :
    Disjoint (carrier ⟨d,i⟩) (carrier ⟨d,j⟩) := UniformPartition.cells_disjoint _ hij

lemma refining_cell_subset {K J : Window} {m : ℕ} (hdepth : J.1=K.1+m)
    {t : I} (htK : t∈carrier K) (htJ : t∈carrier J) : carrier J⊆carrier K := by
  obtain ⟨d,i⟩ := K
  obtain ⟨e,j⟩ := J
  dsimp only at hdepth
  subst e
  obtain ⟨k,hk⟩ := carrier_refinement d m j
  by_cases hki : k=i
  · simpa only [hki] using hk
  · exact False.elim (Set.disjoint_left.mp (same_depth_disjoint hki) (hk htJ) htK)

end PlanarHalving.TimeWindows
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma mem_timePartition {J : Window} {m : ℕ} : J∈timePartition m ↔ J.1=m := by
  obtain ⟨d,i⟩ := J
  constructor
  · intro h
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp h
    exact (congrArg Sigma.fst he).symm
  · intro h
    dsimp only at h
    subst d
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

lemma timePartition_disjoint (m : ℕ) {J K : Window} (hJ : J∈timePartition m) (hK : K∈timePartition m)
    (hJK : J≠K) : Disjoint (carrier J) (carrier K) := by
  obtain ⟨d,i⟩ := J
  obtain ⟨e,j⟩ := K
  have hd := mem_timePartition.mp hJ
  have he := mem_timePartition.mp hK
  dsimp only at hd he
  subst d; subst e
  exact same_depth_disjoint (fun hij => hJK (congrArg (Sigma.mk m) hij))

lemma localPartition_cover (K : Window) (m : ℕ) {t : I} (ht : t∈carrier K) :
    ∃ J∈localPartition K m, t∈carrier J := by
  obtain ⟨J,hJ,htJ⟩ := timePartition_cover (K.1+m) t
  exact ⟨J,Finset.mem_filter.mpr ⟨hJ,refining_cell_subset (mem_timePartition.mp hJ) ht htJ⟩,htJ⟩

lemma localPartition_disjoint (K : Window) (m : ℕ) {J H : Window}
    (hJ : J∈localPartition K m) (hH : H∈localPartition K m) (hJH : J≠H) :
    Disjoint (carrier J) (carrier H) :=
  timePartition_disjoint _ (Finset.mem_filter.mp hJ).1 (Finset.mem_filter.mp hH).1 hJH

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Converges.edgeWindow_apply {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (L.edgeWindow J U : ℝ)=(L.edgeTime : Measure (Labels×I)).real (U×ˢcarrier J) := by
  change ((L.edgeWindow J : Measure Labels) U).toReal= _
  rw [Data.edgeWindow,FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hU,
    h.restriction_eq hR,Measure.restrict_apply (hU.preimage measurable_fst)]
  rfl

lemma Converges.localPartition_sum {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (K : Window) (m : ℕ)
    {U : Set Labels} (hU : MeasurableSet U) :
    ∑ J∈localPartition K m, (L.edgeWindow J U : ℝ)=(L.edgeWindow K U : ℝ) := by
  simp_rw [h.edgeWindow_apply hR _ hU]
  have hd : Set.PairwiseDisjoint (↑(localPartition K m) : Set Window) (fun J => U×ˢcarrier J) := by
    intro J hJ H hH hJH
    exact Set.disjoint_left.mpr (fun t htJ htH =>
      Set.disjoint_left.mp (localPartition_disjoint K m hJ hH hJH) htJ.2 htH.2)
  rw [← measureReal_biUnion_finset hd (fun J _ => hU.prod (measurable_carrier J))]
  congr 1
  ext t
  constructor
  · intro ht
    obtain ⟨J,hJ,htJ⟩ := mem_iUnion₂.mp ht
    exact ⟨htJ.1,(Finset.mem_filter.mp hJ).2 htJ.2⟩
  · intro ht
    obtain ⟨J,hJ,htJ⟩ := localPartition_cover K m ht.2
    exact mem_iUnion₂.mpr ⟨J,hJ,ht.1,htJ⟩

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.MassEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal unitInterval

lemma measurable_decode : Measurable decode := by
  exact ((Real.measurable_log.comp ((measurable_subtype_coe.comp measurable_fst).inv.sub measurable_const)).neg).prodMk
    ((Real.measurable_log.comp ((measurable_subtype_coe.comp measurable_snd).inv.sub measurable_const)).neg)

lemma encode_injective : Function.Injective encode := by
  intro p q he
  simpa only [decode_encode] using congrArg decode he

end PlanarHalving.Spatial

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Enhancement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Enhancement
open RankLimits Batches TimeWindows Limits Spatial MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma vertices_mass (F : Configuration) (ψ : Point → Point) (J : Window) :
    (vertices F ψ J).mass=(F.vertices J).mass := by
  simp only [vertices,Configuration.vertices,System.vertexMeasure,mass_weightedAtoms]

lemma vertices_le_points (F : Configuration) (ψ : Point → Point) (J : Window) :
    (vertices F ψ J : Measure Space)≤(points F ψ : Measure Space) := by
  apply Measure.le_iff.mpr
  intro U hU
  have he : (vertices F ψ J U:ℝ)≤(points F ψ U:ℝ) := by
    rw [vertices,System.vertexMeasure_apply _ _ hU,points,weightedAtoms_apply_finset _ _ hU]
    simp only [NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    (ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp he))

lemma local_cubic {F : ℕ → Configuration} {ψ : ℕ → Point → Point}
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (ψ n) i) atTop (𝓝 (M i)))
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 /
      (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 /
      (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) {U : Set Space} (hU : MeasurableSet U) :
    (M (.edge J) U:ℝ)^3≤C*((M (.vertex J)).mass:ℝ)^3*(M (.vertex J) U:ℝ) := by
  have hm := NNReal.continuous_coe.tendsto _ |>.comp
    (FiniteMeasure.continuous_mass.tendsto _ |>.comp (hM (.vertex J)))
  apply cubed_bound_limit (hM (.vertex J)) (hM (.edge J))
    (mul_nonneg hC (pow_nonneg (NNReal.coe_nonneg _) _)) ((hm.pow 3).const_mul C) herror
  · intro n V hV
    have hR : 0<((F n).R:ℝ≥0) := Nat.cast_pos.mpr (F n).R_pos
    have ha : 0<((F n).a:ℝ≥0) := Nat.cast_pos.mpr (F n).a_pos
    have hh := ((F n).system.timeWindow J).atomic_cubed_bound (F n).generic
      (fun v => label (F n) (ψ n) ((F n).point v)) (show 0<((F n).R:ℝ≥0)*(F n).a^2 by positivity) hV
    change (edges (F n) (ψ n) J V:ℝ)^3≤_
    apply hh.trans
    apply add_le_add
    · dsimp only [Function.comp_apply]
      push_cast
      rw [show ((measures (F n) (ψ n) (.vertex J)).mass:ℝ)=
        (((F n).system.timeWindow J).vertices.card:ℝ)/(F n).n from by
          change ((vertices (F n) (ψ n) J).mass:ℝ)=_
          rw [vertices_mass,(F n).vertices_mass_ratio]]
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
      exact mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (by positivity) _)
    · apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 3
      exact_mod_cast (show ((F n).system.timeWindow J).vertices.card≤(F n).n by
        simpa only [Fintype.card_fin] using ((F n).system.timeWindow J).vertices.card_le_univ)
  · exact hU

end PlanarHalving.Enhancement

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

lemma support_lift_restrict {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [HereditarilyLindelofSpace X]
    (μ ρ : Measure X) (hac : ρ ≪ μ) (A : Set X) :
    ρ.restrict (A∩μ.support)=ρ.restrict A := by
  apply Measure.restrict_congr_set
  filter_upwards [hac.ae_le μ.support_mem_ae] with x hx
  exact propext ⟨fun h => h.1,fun ha => ⟨ha,hx⟩⟩

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Metric Boundary

lemma unit_sqNorm_coordinate_bounds {v : Point} (hv : sqNorm v=1) :
    |v.1|≤1 ∧ |v.2|≤1 := by
  dsimp [sqNorm] at hv
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
    rw [sq_abs]; nlinarith [sq_nonneg v.2]
  · apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
    rw [sq_abs]; nlinarith [sq_nonneg v.1]

lemma unit_sqNorm_norm {v : Point} (hv : sqNorm v=1) : ‖v‖≤1 := by
  rw [Prod.norm_def]
  exact max_le (unit_sqNorm_coordinate_bounds hv).1 (unit_sqNorm_coordinate_bounds hv).2

lemma transverse_decomposition {ν : Point} (hν : sqNorm ν=1) (w : Point) :
    w=(dot (-ν.2,ν.1) w) • (-ν.2,ν.1)+(dot ν w) • ν := by
  dsimp [sqNorm] at hν
  ext <;> dsimp [dot] <;> nlinarith [congrArg (fun t : ℝ => t*w.1) hν,
    congrArg (fun t : ℝ => t*w.2) hν]

lemma bounded_strip_cover (ν : Point) (hν : sqNorm ν=1) (c : ℝ)
    {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    ∃ (S : Finset ℤ) (a : ℤ → Point), (S.card:ℝ)≤13/r ∧
      closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r} ⊆
        ⋃ j∈S, closedBall (a j) (3*r) := by
  classical
  let A : Set Point := closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r}
  by_cases hA : A.Nonempty
  swap
  · refine ⟨∅,fun _ => 0,by simp; positivity,?_⟩
    intro x hx
    exact (hA ⟨x,hx⟩).elim
  obtain ⟨a,ha⟩ := hA
  let v : Point := (-ν.2,ν.1)
  have hv : sqNorm v=1 := by dsimp [v,sqNorm]; simpa only [sqNorm,neg_sq,add_comm] using hν
  have hnν := unit_sqNorm_norm hν
  have hnv := unit_sqNorm_norm hv
  let k : ℤ := ⌈4/r⌉+1
  let S : Finset ℤ := Finset.Icc (-k) k
  have hkpos : 0≤k := by
    have hh := Int.le_ceil (4/r)
    have : (0:ℝ)≤(k:ℝ) := by dsimp [k]; push_cast; linarith [div_pos (by norm_num : (0:ℝ)<4) hr]
    exact_mod_cast this
  have hkbound : (k:ℝ)≤4/r+2 := by
    have hh := Int.ceil_lt_add_one (4/r)
    dsimp [k]; push_cast; linarith
  have hcard : (S.card:ℝ)=2*(k:ℝ)+1 := by
    dsimp [S]
    rw [Int.card_Icc]
    rw [show ((k+1- -k).toNat:ℝ)=((k+1- -k):ℝ) by
      exact_mod_cast (Int.toNat_of_nonneg (by omega : 0≤k+1- -k))]
    ring
  refine ⟨S,fun j => a+(r*(j:ℝ)) • v,?_,?_⟩
  · rw [hcard]
    apply (le_div_iff₀ hr).mpr
    have hh := mul_le_mul_of_nonneg_right hkbound hr.le
    rw [add_mul,div_mul_cancel₀ _ hr.ne'] at hh
    nlinarith
  · intro x hx
    have hdiff : ‖x-a‖≤2 := by
      have hx' : ‖x‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
      have ha' : ‖a‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using ha.1
      exact (norm_sub_le _ _).trans (by linarith)
    let t : ℝ := dot v (x-a)
    let δ : ℝ := dot ν (x-a)
    have hδ : |δ|≤2*r := by
      have he : δ=(dot ν x-c)-(dot ν a-c) := by dsimp [δ,dot]; ring
      rw [he]
      have hx2 : |dot ν x-c|≤r := hx.2
      have ha2 : |dot ν a-c|≤r := ha.2
      exact (abs_sub _ _).trans (by linarith)
    have ht : |t|≤4 := by
      have h1 : |(x-a).1|≤2 := (le_max_left _ _).trans hdiff
      have h2 : |(x-a).2|≤2 := (le_max_right _ _).trans hdiff
      have hv' := unit_sqNorm_coordinate_bounds hv
      dsimp [t,dot]
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul]
      have hh1 := mul_le_mul hv'.1 h1 (abs_nonneg _) zero_le_one
      have hh2 := mul_le_mul hv'.2 h2 (abs_nonneg _) zero_le_one
      dsimp only [Prod.fst_sub,Prod.snd_sub] at hh1 hh2
      linarith
    let j : ℤ := ⌊t/r⌋
    have hjlo : (j:ℝ)≤t/r := Int.floor_le _
    have hjhi : t/r<(j:ℝ)+1 := Int.lt_floor_add_one _
    have hceil : 4/r≤(⌈4/r⌉:ℤ) := Int.le_ceil _
    have htlo : -(4/r)≤t/r := by
      apply (le_div_iff₀ hr).mpr
      have ht' := (abs_le.mp ht).1
      rw [neg_mul,div_mul_cancel₀ _ hr.ne']
      exact ht'
    have hthi : t/r≤4/r := (div_le_div_iff_of_pos_right hr).mpr (abs_le.mp ht).2
    have hjmem : j∈S := by
      apply Finset.mem_Icc.mpr
      constructor
      · have : -(k:ℝ)≤(j:ℝ) := by dsimp [k]; push_cast; linarith
        exact_mod_cast this
      · have : (j:ℝ)≤(k:ℝ) := by dsimp [k]; push_cast; linarith
        exact_mod_cast this
    refine mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hjmem,?_⟩⟩
    have he : x-(a+(r*(j:ℝ)) • v)=(t-r*(j:ℝ)) • v+δ • ν := by
      have hw := transverse_decomposition hν (x-a)
      change x-a=t • v+δ • ν at hw
      calc
        x-(a+(r*(j:ℝ)) • v) = (x-a)-(r*(j:ℝ)) • v := by abel
        _ = _ := by rw [hw]; module
    rw [mem_closedBall,dist_eq_norm,he]
    have htr0 : 0≤t-r*(j:ℝ) := by
      have hh := (le_div_iff₀ hr).mp hjlo
      nlinarith
    have htr1 : t-r*(j:ℝ)≤r := by
      have hh := (div_lt_iff₀ hr).mp hjhi
      nlinarith
    apply (norm_add_le _ _).trans
    rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg htr0]
    have hh1 := mul_le_mul htr1 hnv (norm_nonneg _) hr.le
    have hh2 := mul_le_mul hδ hnν (norm_nonneg _) (by positivity : 0≤2*r)
    linarith

open MeasureTheory Filter
open scoped ENNReal Topology
lemma strip_bound_of_disk (μ : Measure Point) {C d : ℝ} (_hC : 0≤C)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0<r → μ (closedBall x r)≤ENNReal.ofReal (C*r^d))
    (ν : Point) (hν : sqNorm ν=1) (c : ℝ) {r : ℝ} (hr : 0<r) (hr1 : r≤1) :
    μ (closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r}) ≤
      ENNReal.ofReal (13*C*3^d*r^(d-1)) := by
  obtain ⟨S,a,hcard,hcover⟩ := bounded_strip_cover ν hν c hr hr1
  have hcast : (S.card:ℝ≥0∞)≤ENNReal.ofReal (13/r) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  calc
    _ ≤ μ (⋃ j∈S,closedBall (a j) (3*r)) := measure_mono hcover
    _ ≤ ∑ j∈S,μ (closedBall (a j) (3*r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j∈S,ENNReal.ofReal (C*(3*r)^d) := Finset.sum_le_sum (fun j _ => hbound (a j) (3*r) (by positivity))
    _ = (S.card:ℝ≥0∞)*ENNReal.ofReal (C*(3*r)^d) := by simp
    _ ≤ ENNReal.ofReal (13/r)*ENNReal.ofReal (C*(3*r)^d) := mul_le_mul' hcast le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) hr.le,Real.rpow_sub hr]
      simp only [Real.rpow_one]
      ring

lemma line_null_of_disk (μ : Measure Point) {C d : ℝ} (hC : 0≤C) (hd : 1<d)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0<r → μ (closedBall x r)≤ENNReal.ofReal (C*r^d))
    (ν : Point) (hν : sqNorm ν=1) (c : ℝ) :
    μ (closedBall (0:Point) 1 ∩ {x | dot ν x=c})=0 := by
  let a := μ (closedBall (0:Point) 1 ∩ {x | dot ν x=c})
  have hb : ∀ᶠ r in 𝓝[>] (0:ℝ), a≤ENNReal.ofReal (13*C*3^d*r^(d-1)) := by
    have hu : ∀ᶠ r in 𝓝[>] (0:ℝ), r<1 := (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin,hu] with r hr hr1
    have hr : (0:ℝ)<r := hr
    apply le_trans (b:=μ (closedBall (0:Point) 1 ∩ {x | |dot ν x-c|≤r})) ?_
      (strip_bound_of_disk μ hC hbound ν hν c hr hr1.le)
    apply measure_mono
    intro x hx
    have hxe : dot ν x=c := hx.2
    exact ⟨hx.1,show |dot ν x-c|≤r by simpa only [hxe,sub_self,abs_zero] using hr.le⟩
  have ht : Tendsto (fun r : ℝ => ENNReal.ofReal (13*C*3^d*r^(d-1))) (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun r : ℝ => r^(d-1)) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
      convert (Real.continuous_rpow_const (sub_nonneg.mpr hd.le)).tendsto (0:ℝ) using 1
      exact (Real.zero_rpow (sub_ne_zero.mpr hd.ne')).symm ▸ rfl
    have hh' : Tendsto (fun r : ℝ => r^(d-1)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) :=
      hh.mono_left nhdsWithin_le_nhds
    have hc : Tendsto (fun r : ℝ => 13*C*3^d*r^(d-1)) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using hh'.const_mul (13*C*3^d)
    convert (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp hc using 1
    · rfl
    · rw [ENNReal.ofReal_zero]
  exact le_antisymm (ge_of_tendsto ht hb) zero_le

end PlanarHalving.Spatial

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.BoundaryTokens
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Boundary
open Set
open scoped Classical

lemma monotone_pred_changes {m : ℕ} (p : Fin (m+1) → Prop)
    (hp : ∀ i j, i≤j → p i → p j) :
    (Finset.univ.filter fun i : Fin m => ¬ (p i.castSucc ↔ p i.succ)).card≤1 := by
  classical
  have hstep {i : Fin m} (hi : ¬ (p i.castSucc ↔ p i.succ)) : ¬p i.castSucc ∧ p i.succ := by
    have hf := hp i.castSucc i.succ (by simp [Fin.le_def])
    tauto
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' := hstep (Finset.mem_filter.mp hi).2
  have hj' := hstep (Finset.mem_filter.mp hj).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hj'.1 (hp i.succ j.castSucc (by simp only [Fin.le_def,Fin.lt_def,Fin.val_succ,Fin.val_castSucc] at *; omega) hi'.2)
  · exact hi'.1 (hp j.succ i.castSucc (by simp only [Fin.le_def,Fin.lt_def,Fin.val_succ,Fin.val_castSucc] at *; omega) hj'.2)

lemma monotone_square_changes {m : ℕ} (f : Fin (m+1) → Point)
    (h1 : Monotone (fun i => (f i).1)) (h2 : Monotone (fun i => (f i).2))
    (a b : ℝ) :
    (Finset.univ.filter fun i : Fin m => ¬ (InSquare a b (f i.castSucc) ↔ InSquare a b (f i.succ))).card≤4 := by
  classical
  let A := Finset.univ.filter fun i : Fin m => ¬ (a<(f i.castSucc).1 ↔ a<(f i.succ).1)
  let B := Finset.univ.filter fun i : Fin m => ¬ (b≤(f i.castSucc).1 ↔ b≤(f i.succ).1)
  let C := Finset.univ.filter fun i : Fin m => ¬ (a<(f i.castSucc).2 ↔ a<(f i.succ).2)
  let D := Finset.univ.filter fun i : Fin m => ¬ (b≤(f i.castSucc).2 ↔ b≤(f i.succ).2)
  have hA : A.card≤1 := monotone_pred_changes (fun i => a<(f i).1) (fun i j hij ha => ha.trans_le (h1 hij))
  have hB : B.card≤1 := monotone_pred_changes (fun i => b≤(f i).1) (fun i j hij ha => ha.trans (h1 hij))
  have hC : C.card≤1 := monotone_pred_changes (fun i => a<(f i).2) (fun i j hij ha => ha.trans_le (h2 hij))
  have hD : D.card≤1 := monotone_pred_changes (fun i => b≤(f i).2) (fun i j hij ha => ha.trans (h2 hij))
  have hs : (Finset.univ.filter fun i : Fin m =>
      ¬ (InSquare a b (f i.castSucc) ↔ InSquare a b (f i.succ)))⊆ A∪B∪C∪D := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [A,B,C,D,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    dsimp only [InSquare] at hi'
    simp only [lt_iff_not_ge] at *
    tauto
  have ht := Finset.card_le_card hs
  have h4 := Finset.card_union_le (A∪B∪C) D
  have h3 := Finset.card_union_le (A∪B) C
  have h2 := Finset.card_union_le A B
  omega

lemma square_token_budget {τ : Type*} [Fintype τ] {m : ℕ}
    (f : Fin (m+1) → τ → Point)
    (h1 : ∀ u, Monotone (fun i => (f i u).1))
    (h2 : ∀ u, Monotone (fun i => (f i u).2)) (a b : ℝ) :
    (∑ i : Fin m, (Finset.univ.filter fun u : τ =>
      ¬ (InSquare a b (f i.castSucc u) ↔ InSquare a b (f i.succ u))).card)≤4*Fintype.card τ := by
  classical
  have he : (∑ i : Fin m, (Finset.univ.filter fun u : τ =>
      ¬ (InSquare a b (f i.castSucc u) ↔ InSquare a b (f i.succ u))).card)=
      ∑ u : τ, (Finset.univ.filter fun i : Fin m =>
      ¬ (InSquare a b (f i.castSucc u) ↔ InSquare a b (f i.succ u))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [he]
  calc
    _ ≤ ∑ _u : τ, 4 := Finset.sum_le_sum (fun u _ => monotone_square_changes (fun i => f i u) (h1 u) (h2 u) a b)
    _ = _ := by simp [Nat.mul_comm]

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

lemma frameWeight_pos {a b l u s : ℝ} (ha : 0<a) (hb : 0<b)
    (hlu : l<u) (hs : s∈Icc l u) : 0<frameWeight a b l u s := by
  have h1 := mul_nonneg ha.le (sub_nonneg.mpr hs.1)
  have h2 := mul_nonneg hb.le (sub_nonneg.mpr hs.2)
  rcases lt_or_eq_of_le hs.1 with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos ha (sub_pos.mpr h)) h2
  · subst s; simpa [frameWeight] using mul_pos hb (sub_pos.mpr hlu)

lemma frameParameter_mem {a b l u s : ℝ} (ha : 0<a) (hb : 0<b)
    (hlu : l<u) (hs : s∈Icc l u) : frameParameter a b l u s∈Icc (0:ℝ) 1 := by
  have hd := frameWeight_pos ha hb hlu hs
  constructor
  · exact div_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hs.1)) hd.le
  · apply (div_le_one hd).mpr
    dsimp [frameWeight]
    linarith [mul_nonneg hb.le (sub_nonneg.mpr hs.2)]

lemma frameParameter_monotone {a b l u : ℝ} (ha : 0<a) (hb : 0<b) (hlu : l<u) :
    MonotoneOn (frameParameter a b l u) (Icc l u) := by
  intro s hs t ht hst
  apply (div_le_div_iff₀ (frameWeight_pos ha hb hlu hs) (frameWeight_pos ha hb hlu ht)).mpr
  dsimp [frameWeight]
  have hp := mul_nonneg (mul_nonneg ha.le hb.le) (mul_nonneg (sub_nonneg.mpr hlu.le) (sub_nonneg.mpr hst))
  nlinarith only [hp]

lemma frame_apply (E : Point ≃L[ℝ] Point) {a b l u : ℝ}
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u)) (x : Point) :
    E x=(a*x.1+b*x.2,a*l*x.1+b*u*x.2) := by
  have hx : x=x.1 • ((1,0):Point)+x.2 • ((0,1):Point) := by ext <;> simp
  conv_lhs => rw [hx,map_add,map_smul,map_smul,h1,h2]
  ext <;> dsimp <;> ring

lemma frame_projection (E : Point ≃L[ℝ] Point) {a b l u s : ℝ}
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hd : frameWeight a b l u s≠0) (x : Point) :
    Sweep.projection s (E x)=frameWeight a b l u s * dot (rawNormal (frameParameter a b l u s)) x := by
  rw [frame_apply E h1 h2]
  dsimp [Sweep.projection,dot,rawNormal,frameParameter]
  field_simp
  dsimp [frameWeight]
  ring

lemma frame_inverse_nonneg (E : Point ≃L[ℝ] Point) {a b l u : ℝ}
    (ha : 0<a) (hb : 0<b) (hlu : l<u)
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (v : Point) (hlo : l*v.1≤v.2) (hhi : v.2≤u*v.1) :
    0≤(E.symm v).1 ∧ 0≤(E.symm v).2 := by
  have he := frame_apply E h1 h2 (E.symm v)
  rw [E.apply_symm_apply] at he
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change v.1=a*(E.symm v).1+b*(E.symm v).2 at he1
  change v.2=a*l*(E.symm v).1+b*u*(E.symm v).2 at he2
  rw [he1,he2] at hlo hhi
  constructor
  · have hp : 0<a*(u-l) := mul_pos ha (sub_pos.mpr hlu)
    have hh : 0≤a*(u-l)*(E.symm v).1 := by nlinarith [hhi]
    exact (mul_nonneg_iff_of_pos_left hp).mp hh
  · have hp : 0<b*(u-l) := mul_pos hb (sub_pos.mpr hlu)
    have hh : 0≤b*(u-l)*(E.symm v).2 := by nlinarith [hlo]
    exact (mul_nonneg_iff_of_pos_left hp).mp hh

lemma rawNormal_bounds (t : ℝ) : (1:ℝ)/2 ≤ sqNorm (rawNormal t) := by
  dsimp [sqNorm,rawNormal]
  nlinarith [sq_nonneg (t-1/2)]
lemma rawNormal_difference (s t : ℝ) : sqNorm (rawNormal s-rawNormal t)=2*(s-t)^2 := by
  dsimp [sqNorm,rawNormal]; ring

lemma separating_threshold {V : Type*} [Fintype V] (f : V → ℝ) (M : Finset V)
    (hsep : ∀ i∈M, ∀ j∉M, f i<f j) : ∃ c : ℝ, ∀ i, i∈M ↔ f i<c := by
  classical
  by_cases hM : M.Nonempty
  · obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image M f hM
    by_cases hN : (Finset.univ\M).Nonempty
    · obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.univ\M) f hN
      have hn := (Finset.mem_sdiff.mp hj).2
      obtain ⟨c,hc,hd⟩ := exists_between (hsep i hi j hn)
      refine ⟨c,fun v => ⟨fun hv => (hmax v hv).trans_lt hc,fun hv => ?_⟩⟩
      by_contra hvM
      exact (not_lt_of_ge ((hmin v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hvM⟩)).trans' hd.le)) hv
    · refine ⟨f i+1,fun v => ⟨fun hv => by linarith [hmax v hv],fun _ => ?_⟩⟩
      by_contra hv
      exact hN ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩
  · have he : M=∅ := Finset.not_nonempty_iff_eq_empty.mp hM
    subst M
    by_cases hn : Nonempty V
    · let := hn
      obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
      refine ⟨f j-1,fun v => ?_⟩
      simp only [Finset.notMem_empty,false_iff,not_lt]
      linarith [hmin v (Finset.mem_univ _)]
    · exact ⟨0,fun v => (hn ⟨v⟩).elim⟩

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

lemma physical_sub (E : Point ≃L[ℝ] Point) (o : Point) (r : ℝ) (p q : Point) :
    physical E o r q - physical E o r p=r • E.symm (q-p) := by
  rw [physical,physical,← smul_sub,← map_sub]
  congr 2
  abel

lemma projection_physical (E : Point ≃L[ℝ] Point) {a b l u s : ℝ}
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hd : frameWeight a b l u s≠0) (o : Point) (r : ℝ) (p : Point) :
    dot (rawNormal (frameParameter a b l u s)) (physical E o r p)=
      r/frameWeight a b l u s*(Sweep.projection s p-Sweep.projection s o) := by
  have he := frame_projection E h1 h2 hd (E.symm (p-o))
  rw [E.apply_symm_apply] at he
  calc
    _ = r*dot (rawNormal (frameParameter a b l u s)) (E.symm (p-o)) := by dsimp [physical,dot]; ring
    _ = r/frameWeight a b l u s*(frameWeight a b l u s*dot (rawNormal (frameParameter a b l u s)) (E.symm (p-o))) := by field_simp
    _ = _ := by rw [← he]; dsimp [Sweep.projection]; congr 1; ring

lemma actual_transformed_cuts {n R k a₀ : ℕ} {P : Fin n → Point}
    (S : @Batches.System n R k a₀ P) (E : Point ≃L[ℝ] Point)
    {a b l u : ℝ} (ha : 0<a) (hb : 0<b) (hlu : l<u)
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hspan : ∀ i, S.slope i∈Icc l u) (o : Point) {r : ℝ} (hr : 0<r) :
    ∃ c : Fin (R+1) → ℝ, ∀ i v,
      v∈S.marks i ↔ dot (rawNormal (frameParameter a b l u (S.slope i))) (physical E o r (P v))<c i := by
  choose c hc using fun i => separating_threshold
    (fun v => dot (rawNormal (frameParameter a b l u (S.slope i))) (physical E o r (P v)))
    (S.marks i) (by
      intro v hv w hw
      rw [projection_physical E h1 h2 (frameWeight_pos ha hb hlu (hspan i)).ne' o r,
        projection_physical E h1 h2 (frameWeight_pos ha hb hlu (hspan i)).ne' o r]
      exact mul_lt_mul_of_pos_left (sub_lt_sub_right (S.separates i v hv w hw) _)
        (div_pos hr (frameWeight_pos ha hb hlu (hspan i))))
  exact ⟨c,hc⟩

lemma actual_tokens_monotone {n R k a₀ : ℕ} {P : Fin n → Point} [NeZero a₀]
    (S : @Batches.System n R k a₀ P) (E : Point ≃L[ℝ] Point)
    {a b l u : ℝ} (ha : 0<a) (hb : 0<b) (hlu : l<u)
    (h1 : E (1,0)=a • (1,l)) (h2 : E (0,1)=b • (1,u))
    (hspan : ∀ i, S.slope i∈Icc l u) (o : Point) {r : ℝ} (hr : 0<r)
    (j : Fin a₀) (v : ↥(S.marks 0)) :
    Monotone (fun i => (physical E o r (P (S.tokenState j i v))).1) ∧
      Monotone (fun i => (physical E o r (P (S.tokenState j i v))).2) := by
  have hstep (i : Fin R) :
      0 ≤ (physical E o r (P (S.tokenState j i.succ v))-
        physical E o r (P (S.tokenState j i.castSucc v))).1 ∧
      0 ≤ (physical E o r (P (S.tokenState j i.succ v))-
        physical E o r (P (S.tokenState j i.castSucc v))).2 := by
    rcases S.token_step j v i with he | ⟨hl,hg⟩
    · rw [he,sub_self]; exact ⟨le_rfl,le_rfl⟩
    · have hx := sub_pos.mpr (S.edge_right i hl hg)
      have hs := S.edge_slope i hl hg
      have hlo : l*(P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).1 ≤
          (P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).2 :=
        (le_div_iff₀ hx).mp ((hspan i.castSucc).1.trans hs.1.le)
      have hhi : (P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).2 ≤
          u*(P (S.tokenState j i.succ v)-P (S.tokenState j i.castSucc v)).1 :=
        (div_le_iff₀ hx).mp (hs.2.le.trans (hspan i.succ).2)
      have hh := frame_inverse_nonneg E ha hb hlu h1 h2 _ hlo hhi
      rw [physical_sub]
      exact ⟨mul_nonneg hr.le hh.1,mul_nonneg hr.le hh.2⟩
  constructor
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact sub_nonneg.mp (hstep i).1
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact sub_nonneg.mp (hstep i).2

end PlanarHalving.Boundary

namespace PlanarHalving.Boundary
open Set
open scoped Classical

lemma clipCut_mem (c : ℝ) : clipCut c∈Icc (-4:ℝ) 4 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
lemma clipCut_distance {t : ℝ} (ht : t∈Icc (-4:ℝ) 4) (c : ℝ) :
    |t-clipCut c|≤|t-c| := by
  obtain ⟨htlo,hthi⟩ := ht
  by_cases hc : c≤-4
  · rw [clipCut,min_eq_right (hc.trans (by norm_num)),max_eq_left hc,
      abs_of_nonneg (by linarith : 0≤t-(-4)),abs_of_nonneg (by linarith : 0≤t-c)]
    linarith
  · by_cases hd : 4≤c
    · rw [clipCut,min_eq_left hd,max_eq_right (by norm_num : (-4:ℝ)≤4),
        abs_of_nonpos (by linarith : t-4≤0),abs_of_nonpos (by linarith : t-c≤0)]
      linarith
    · rw [clipCut,min_eq_right (le_of_not_ge hd),max_eq_right (le_of_not_ge hc)]

lemma rawNormal_dot_bound {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {x : Point}
    (hx : InSquare (-2) 2 x) : |dot (rawNormal t) x|≤2 := by
  have htlo := ht.1
  have hthi := ht.2
  have h1 : |x.1|≤2 := abs_le.mpr ⟨hx.1.le,hx.2.1.le⟩
  have h2 : |x.2|≤2 := abs_le.mpr ⟨hx.2.2.1.le,hx.2.2.2.le⟩
  calc
    _ ≤ |(-t)*x.1|+|(1-t)*x.2| := abs_add_le _ _
    _ = t*|x.1|+(1-t)*|x.2| := by rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg ht.1,abs_of_nonneg (by linarith : 0≤1-t)]
    _ ≤ t*2+(1-t)*2 := add_le_add (mul_le_mul_of_nonneg_left h1 ht.1) (mul_le_mul_of_nonneg_left h2 (by linarith))
    _ = 2 := by ring

lemma finite_raw_bound {V τ : Type*} [Fintype V] [Fintype τ]
    {m : ℕ} (p : V → Point) (f : Fin (m+1) → τ → V)
    (hf : ∀ i, Function.Injective (f i)) (A : Finset V)
    (t c : Fin (m+1) → ℝ) (ht : Monotone t) (htI : ∀ i, t i∈Icc (0:ℝ) 1)
    (hcut : ∀ i v, v∈Finset.univ.image (f i) ↔ dot (rawNormal (t i)) (p v)<c i)
    (hactive : ∀ v∈A, ∃ i j : Fin (m+1), ¬(v∈Finset.univ.image (f i) ↔ v∈Finset.univ.image (f j))) :
    ∃ d : Fin 3 → ℝ, (∀ j, d j∈Icc (-4:ℝ) 4) ∧
      (A.filter fun v => InSquare (-2) 2 (p v) ∧
        ∀ j, 18*(t (Fin.last m)-t 0)< |dot (rawNormal (t 0)) (p v)-d j|).card≤
      2*∑ i : Fin m, (Finset.univ.filter fun u : τ =>
        ¬(InSquare (-2) 2 (p (f i.castSucc u)) ↔ InSquare (-2) 2 (p (f i.succ u)))).card := by
  classical
  obtain ⟨imin,hmin⟩ := Finite.exists_min c
  obtain ⟨imax,hmax⟩ := Finite.exists_max c
  let d : Fin 3 → ℝ := ![clipCut (c 0),clipCut (c imin),clipCut (c imax)]
  refine ⟨d,fun j => by fin_cases j <;> exact clipCut_mem _,?_⟩
  let B := Finset.univ.filter fun v => InSquare (-2) 2 (p v)
  let θ := t (Fin.last m)-t 0
  have hθ : 0≤θ := sub_nonneg.mpr (ht (Fin.zero_le _))
  let g : ℕ → τ → V := fun i => f ⟨min i m,by omega⟩
  have hg (i : Fin (m+1)) : g i=f i := by
    have he : (⟨min i.val m,by omega⟩ : Fin (m+1))=i := Fin.ext (min_eq_left (by omega))
    exact congrArg f he
  have hgzero : g 0=f 0 := hg 0
  have hnormal (i : Fin (m+1)) : sqNorm (rawNormal (t i)-rawNormal (t 0))≤(2*θ)^2 := by
    rw [rawNormal_difference]
    have h0 := ht (Fin.zero_le i)
    have h1 := ht (Fin.le_last i)
    have hh : (t i-t 0)^2≤θ^2 := pow_le_pow_left₀ (sub_nonneg.mpr h0) (by dsimp [θ]; linarith) 2
    nlinarith [sq_nonneg θ]
  have herr (i : Fin (m+1)) (v : V) (hv : v∈B) :
      |dot (rawNormal (t i)-rawNormal (t 0)) (p v)|≤3*(2*θ) := by
    apply abs_dot_le (by norm_num) (by positivity) (hnormal i)
    have hv' := (Finset.mem_filter.mp hv).2
    have h1 : |(p v).1|≤2 := abs_le.mpr ⟨hv'.1.le,hv'.2.1.le⟩
    have h2 : |(p v).2|≤2 := abs_le.mpr ⟨hv'.2.2.1.le,hv'.2.2.2.le⟩
    have h1' := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).mpr h1
    have h2' := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤2)).mpr h2
    simp only [sq_abs] at h1' h2'
    dsimp [sqNorm]; nlinarith
  have hmain := three_strips_tokens m g (fun i hi => hf _) A B
    (fun v => dot (rawNormal (t 0)) (p v)) c
    (fun i v => dot (rawNormal (t i)-rawNormal (t 0)) (p v)) imin imax (3*(2*θ))
    (by positivity) hmin hmax herr (fun v _ => by simp [dot])
    (by
      intro i v _
      rw [hg]
      have he : dot (rawNormal (t 0)) (p v)+dot (rawNormal (t i)-rawNormal (t 0)) (p v)=dot (rawNormal (t i)) (p v) := by dsimp [dot]; ring
      rw [he]
      exact hcut i v)
    (by
      intro v hv
      have hh := changes_initial (fun i : Fin (m+1) => v∈Finset.univ.image (f i)) 0 (hactive v hv)
      simpa only [hgzero,hg] using hh)
  have hs : (A.filter fun v => InSquare (-2) 2 (p v) ∧
      ∀ j,18*θ< |dot (rawNormal (t 0)) (p v)-d j|)⊆
      ((A∩B).filter fun v => ¬(|dot (rawNormal (t 0)) (p v)-c 0|≤3*(3*(2*θ)) ∨
        |dot (rawNormal (t 0)) (p v)-c imin|≤3*(3*(2*θ)) ∨
        |dot (rawNormal (t 0)) (p v)-c imax|≤3*(3*(2*θ)))) := by
    intro v hv
    obtain ⟨hvA,hvB,hvD⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hvA,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvB⟩⟩,?_⟩
    have hvdot := abs_le.mp (rawNormal_dot_bound (htI 0) hvB)
    have hd (c : ℝ) := clipCut_distance (show dot (rawNormal (t 0)) (p v)∈Icc (-4:ℝ) 4 by constructor <;> linarith) c
    have h0 := (hvD 0).trans_le (hd (c 0))
    have h1 := (hvD 1).trans_le (hd (c imin))
    have h2 := (hvD 2).trans_le (hd (c imax))
    change 18*θ< |dot (rawNormal (t 0)) (p v)-c 0| at h0
    change 18*θ< |dot (rawNormal (t 0)) (p v)-c imin| at h1
    change 18*θ< |dot (rawNormal (t 0)) (p v)-c imax| at h2
    rintro (hh|hh|hh) <;> linarith
  apply (Finset.card_le_card hs).trans
  convert hmain using 1
  all_goals try rfl
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext u
  have hgi := hg i.castSucc
  have hgj := hg i.succ
  simp only [Fin.val_castSucc,Fin.val_succ] at hgi hgj
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,hgi,hgj,B]

end PlanarHalving.Boundary

namespace PlanarHalving.Spatial
open Set Metric MeasureTheory Boundary
open scoped ENNReal

lemma strip_bound_of_disk_nonneg (μ : Measure Point) {C d : ℝ} (hC : 0 ≤ C) (hd : 1 < d)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0 < r → μ (closedBall x r) ≤ ENNReal.ofReal (C*r^d))
    (ν : Point) (hν : sqNorm ν=1) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    μ (closedBall (0:Point) 1 ∩ {x | |dot ν x-c| ≤ r}) ≤
      ENNReal.ofReal (13*C*(1+3^d)*r^(d-1)) := by
  rcases hr.eq_or_lt with he | hr
  · subst r
    have hz := line_null_of_disk μ hC hd hbound ν hν c
    have heq : {x : Point | |dot ν x-c| ≤ 0}={x | dot ν x=c} := by ext x; simp [sub_eq_zero]
    rw [heq,hz]
    exact zero_le
  · by_cases h1 : r ≤ 1
    · apply (strip_bound_of_disk μ hC hbound ν hν c hr h1).trans
      apply ENNReal.ofReal_le_ofReal
      gcongr
      linarith
    · have h1' : 1 ≤ r := (not_le.mp h1).le
      have hp : 1 ≤ r^(d-1) := Real.one_le_rpow h1' (by linarith)
      calc
        _  ≤  μ (closedBall (0:Point) 1) := measure_mono inter_subset_left
        _  ≤  ENNReal.ofReal C := by simpa using hbound 0 1 (by norm_num)
        _  ≤  _ := by
          apply ENNReal.ofReal_le_ofReal
          have h3 : 0 ≤ (3:ℝ)^d := Real.rpow_nonneg (by norm_num) _
          have hh : C ≤ 13*C*(1+3^d) := by nlinarith
          exact hh.trans (le_mul_of_one_le_right (by positivity) hp)

lemma normalize_sqNorm (ν : Point) (hν : 0 < sqNorm ν) :
    sqNorm ((Real.sqrt (sqNorm ν))⁻¹ • ν)=1 := by
  have hs := Real.sq_sqrt hν.le
  have hn := (Real.sqrt_pos.mpr hν).ne'
  dsimp [sqNorm] at *
  field_simp
  nlinarith only [hs]

lemma raw_strip_bound (μ : Measure Point) {C d : ℝ} (hC : 0 ≤ C) (hd : 1 < d)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0 < r → μ (closedBall x r) ≤ ENNReal.ofReal (C*r^d))
    (t c : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    μ (closedBall (0:Point) 1 ∩ {x | |dot (Boundary.rawNormal t) x-c| ≤ 18*θ}) ≤
      ENNReal.ofReal (13*C*(1+3^d)*36^(d-1)*θ^(d-1)) := by
  let ν := Boundary.rawNormal t
  let a := Real.sqrt (sqNorm ν)
  have ha : 0 < a := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (Boundary.rawNormal_bounds t))
  have ha2 : (1:ℝ)/2 ≤ a := by
    have hs := Real.sq_sqrt (show 0 ≤ sqNorm ν from (by norm_num : (0:ℝ) ≤ 1/2).trans (Boundary.rawNormal_bounds t))
    change a^2=sqNorm ν at hs
    have hb := Boundary.rawNormal_bounds t
    change 1/2 ≤ sqNorm ν at hb
    nlinarith
  have hn : sqNorm (a⁻¹ • ν)=1 := normalize_sqNorm ν (by have := Boundary.rawNormal_bounds t; change 1/2 ≤ sqNorm ν at this; linarith)
  have hs : {x : Point | |dot ν x-c| ≤ 18*θ}⊆{x | |dot (a⁻¹ • ν) x-c/a| ≤ 36*θ} := by
    intro x hx
    have he : dot (a⁻¹ • ν) x-c/a=(dot ν x-c)/a := by dsimp [dot]; ring
    change |dot (a⁻¹ • ν) x-c/a| ≤ 36*θ
    rw [he,abs_div,abs_of_pos ha]
    apply (div_le_iff₀ ha).mpr
    change |dot ν x-c| ≤ 18*θ at hx
    have hh := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ 36*θ by positivity)
    nlinarith only [hx,hh]
  apply (measure_mono (inter_subset_inter_right _ hs)).trans
  have hh := strip_bound_of_disk_nonneg μ hC hd hbound (a⁻¹ • ν) hn (c/a) (show 0 ≤ 36*θ by positivity)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 36) hθ] at hh
  simpa only [mul_assoc] using hh

end PlanarHalving.Spatial

namespace PlanarHalving.Limits
open Set Filter MeasureTheory
open scoped Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma eventually_gt_open {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {O : Set X} (hO : IsOpen O)
    {q : ℝ} (hq : q < (μ O : ℝ)) : ∀ᶠ n in atTop, q < (μs n O : ℝ) := by
  let ε := ((μ O:ℝ)-q)/3
  have hε : 0<ε := by dsimp [ε]; linarith
  have hadd (ν : FiniteMeasure X) : (ν O:ℝ)+(ν Oᶜ:ℝ)=(ν.mass:ℝ) :=
    measureReal_add_measureReal_compl (μ:=(ν:Measure X)) hO.measurableSet
  have hcomp := eventually_lt_closed h hO.isClosed_compl
    (show (μ Oᶜ:ℝ)<(μ Oᶜ:ℝ)+ε by linarith)
  have hmass := (NNReal.continuous_coe.tendsto _ |>.comp h.mass).eventually
    (eventually_gt_nhds (show (μ.mass:ℝ)-ε<(μ.mass:ℝ) by linarith))
  filter_upwards [hcomp,hmass] with n hn hm
  have hsum := hadd (μs n)
  have hsum' := hadd μ
  dsimp [ε] at hn hm
  linarith

lemma open_le_of_eventually_le {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) {O : Set X} (hO : IsOpen O)
    {b : ℕ → ℝ} {B : ℝ} (hb : Tendsto b atTop (𝓝 B))
    (hbound : ∀ᶠ n in atTop, (μs n O:ℝ) ≤ b n) : (μ O:ℝ) ≤ B := by
  by_contra hh
  obtain ⟨q,hqB,hqμ⟩ := exists_between (lt_of_not_ge hh)
  obtain ⟨n,hn,hn',hn''⟩ := ((eventually_gt_open h hO hqμ).and
    ((hb.eventually (eventually_lt_nhds hqB)).and hbound)).exists
  exact (not_lt_of_ge hn'') (hn'.trans hn)

end PlanarHalving.Limits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ThinStrips
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Boundary
open scoped Topology unitInterval

lemma isOpenMap_encode : IsOpenMap encode := by
  have h : IsOpenMap unitInterval.sigmoid :=
    Topology.isEmbedding_sigmoid.isInducing.isOpenMap (by rw [unitInterval.range_sigmoid]; exact isOpen_Ioo)
  exact h.prodMap h

lemma isOpen_square (a b : ℝ) : IsOpen {x : Point | InSquare a b x} := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)))

lemma continuous_dot (ν : Point) : Continuous (dot ν) := by
  exact (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)

lemma isOpen_awayStrips (t θ : ℝ) (c : Fin 3 → ℝ) : IsOpen (awayStrips t θ c) := by
  have he : awayStrips t θ c={x : Point | InSquare (-2) 2 x} ∩ ⋂ j : Fin 3, {x | 18*θ < |dot (rawNormal t) x-c j|} := by
    ext x; simp [awayStrips]
  rw [he]
  apply (isOpen_square (-2) 2).inter
  exact isOpen_iInter_of_finite (fun j : Fin 3 => isOpen_lt continuous_const ((continuous_dot _).sub continuous_const).abs)

lemma awayStrips_stable {ts θs : ℕ → ℝ} {cs : ℕ → Fin 3 → ℝ}
    {t θ : ℝ} {c : Fin 3 → ℝ}
    (ht : Tendsto ts atTop (𝓝 t)) (hθ : Tendsto θs atTop (𝓝 θ))
    (hc : Tendsto cs atTop (𝓝 c)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in atTop, awayStrips t (θ+ε) c ⊆ awayStrips (ts n) (θs n) (cs n) := by
  have ht' := (tendsto_order.mp ((tendsto_sub_nhds_zero_iff.mpr ht).abs)).2 ε (by simpa using hε)
  have hθ' := (tendsto_order.mp ((tendsto_sub_nhds_zero_iff.mpr hθ).abs)).2 (ε/2) (by simpa using half_pos hε)
  have hc' : ∀ᶠ n in atTop, ∀ j, |cs n j-c j|<ε := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_order.mp ((tendsto_sub_nhds_zero_iff.mpr (tendsto_pi_nhds.mp hc j)).abs)).2 ε (by simpa using hε)
  filter_upwards [ht',hθ',hc'] with n hn hnθ hnc x hx
  refine ⟨hx.1,fun j => ?_⟩
  have h1 : |x.1|≤2 := abs_le.mpr ⟨hx.1.1.le,hx.1.2.1.le⟩
  have h2 : |x.2|≤2 := abs_le.mpr ⟨hx.1.2.2.1.le,hx.1.2.2.2.le⟩
  have hdiff : |dot (rawNormal (ts n)) x-dot (rawNormal t) x|≤4*|ts n-t| := by
    have he : dot (rawNormal (ts n)) x-dot (rawNormal t) x=-(ts n-t)*(x.1+x.2) := by dsimp [dot,rawNormal]; ring
    rw [he,abs_mul,abs_neg]
    have hh : |x.1+x.2|≤4 := (abs_add_le _ _).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (ts n-t))]
  have htotal : |(dot (rawNormal (ts n)) x-cs n j)-(dot (rawNormal t) x-c j)|<5*ε := by
    have he : (dot (rawNormal (ts n)) x-cs n j)-(dot (rawNormal t) x-c j)=
        (dot (rawNormal (ts n)) x-dot (rawNormal t) x)-(cs n j-c j) := by ring
    rw [he]
    have hh := abs_sub (dot (rawNormal (ts n)) x-dot (rawNormal t) x) (cs n j-c j)
    have hncj := hnc j
    linarith
  have hh := abs_abs_sub_abs_le_abs_sub (dot (rawNormal (ts n)) x-cs n j) (dot (rawNormal t) x-c j)
  have hh' := (abs_le.mp hh).1
  have hlow := hx.2 j
  have hup := (abs_lt.mp hnθ).2
  linarith

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Boundary Limits
open scoped Topology unitInterval ENNReal

lemma awayStrips_antitone (t : ℝ) (c : Fin 3 → ℝ) : Antitone (fun θ => awayStrips t θ c) := by
  intro θ θ' hθ x hx
  exact ⟨hx.1,fun j => (mul_le_mul_of_nonneg_left hθ (by norm_num)).trans_lt (hx.2 j)⟩

lemma awayStrips_iUnion (t θ : ℝ) (c : Fin 3 → ℝ) :
    (⋃ m : ℕ, awayStrips t (θ+1/((m:ℝ)+1)) c)=awayStrips t θ c := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨m,hm⟩ := mem_iUnion.mp hx
    exact awayStrips_antitone t c (le_add_of_nonneg_right (by positivity)) hm
  · intro x hx
    have hh : ∀ᶠ m : ℕ in atTop, ∀ j, 18*(θ+1/((m:ℝ)+1)) < |dot (rawNormal t) x-c j| := by
      apply Filter.eventually_all.mpr
      intro j
      have hl : Tendsto (fun m : ℕ => 18*(θ+1/((m:ℝ)+1))) atTop (𝓝 (18*θ)) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_add θ |>.const_mul 18
      exact hl.eventually (eventually_lt_nhds (hx.2 j))
    obtain ⟨m,hm⟩ := hh.exists
    exact mem_iUnion.mpr ⟨m,hx.1,hm⟩

lemma moving_strips_limit {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μs : ℕ → FiniteMeasure (X × Cube)} {μ : FiniteMeasure (X × Cube)}
    (hμ : Tendsto μs atTop (𝓝 μ))
    {ts θs bs : ℕ → ℝ} {cs : ℕ → Fin 3 → ℝ} {t θ b : ℝ} {c : Fin 3 → ℝ}
    (ht : Tendsto ts atTop (𝓝 t)) (hθ : Tendsto θs atTop (𝓝 θ))
    (hc : Tendsto cs atTop (𝓝 c)) (hb : Tendsto bs atTop (𝓝 b))
    (hfinite : ∀ᶠ n in atTop,
      (μs n (Prod.snd ⁻¹' (encode '' awayStrips (ts n) (θs n) (cs n))):ℝ) ≤ 2*bs n) :
    (μ (Prod.snd ⁻¹' (encode '' awayStrips t θ c)):ℝ) ≤ 2*b := by
  let O (m : ℕ) : Set (X × Cube) := Prod.snd ⁻¹' (encode '' awayStrips t (θ+1/((m:ℝ)+1)) c)
  have hO (m : ℕ) : IsOpen (O m) :=
    (isOpenMap_encode _ (isOpen_awayStrips ..)).preimage continuous_snd
  have hbound (m : ℕ) : (μ (O m):ℝ) ≤ 2*b := by
    apply open_le_of_eventually_le hμ (hO m) (hb.const_mul 2)
    have he := awayStrips_stable ht hθ hc (show 0<1/((m:ℝ)+1) by positivity)
    filter_upwards [he,hfinite] with n hn hnf
    exact (show (μs n (O m):ℝ) ≤ μs n (Prod.snd ⁻¹' (encode '' awayStrips (ts n) (θs n) (cs n))) from
      NNReal.coe_le_coe.mpr ((μs n).apply_mono (preimage_mono (image_mono hn)))).trans hnf
  have hmono : Monotone O := by
    intro m n hmn
    apply preimage_mono
    apply image_mono
    apply awayStrips_antitone
    have hm : (0:ℝ) < m+1 := by positivity
    have hn : (0:ℝ) < n+1 := by positivity
    have hmn' : (m:ℝ)+1 ≤ n+1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    exact add_le_add_right ((one_div_le_one_div hn hm).mpr hmn') θ
  have hunion : (⋃ m, O m)=Prod.snd ⁻¹' (encode '' awayStrips t θ c) := by
    rw [← awayStrips_iUnion t θ c,image_iUnion,preimage_iUnion]
  have hbound' (m : ℕ) : (μ : Measure (X × Cube)) (O m) ≤ ENNReal.ofReal (2*b) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hbound m)
  have he : (μ : Measure (X × Cube)) (Prod.snd ⁻¹' (encode '' awayStrips t θ c)) ≤ ENNReal.ofReal (2*b) := by
    rw [← hunion,hmono.measure_iUnion]
    exact iSup_le hbound'
  have hb0 : 0≤2*b := (NNReal.coe_nonneg (μ (O 0))).trans (hbound 0)
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal] at he
  exact (ENNReal.ofReal_le_ofReal_iff hb0).mp he

end PlanarHalving.Spatial
namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory Boundary Limits
open scoped Topology unitInterval ENNReal

lemma limiting_activity_bound {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : FiniteMeasure (X × Cube)) (H : Set (X × Cube)) (_hH : MeasurableSet H)
    (hν : (ν : Measure (X × Cube))≤μ)
    (hpos : ∀ z∈H, ‖decode z.2‖≤1 ∧ encode (decode z.2)=z.2)
    {C d t θ b : ℝ} (hC : 0≤C) (hd : 1<d) (hθ : 0≤θ) (hb : 0≤b)
    (c : Fin 3 → ℝ)
    (hbound : ∀ x : Point, ∀ r : ℝ, 0<r →
      ((μ : Measure (X × Cube)).restrict H).map (decode ∘ Prod.snd) (closedBall x r) ≤ ENNReal.ofReal (C*r^d))
    (haway : (ν (Prod.snd ⁻¹' (encode '' awayStrips t θ c)):ℝ)≤2*b) :
    (ν H:ℝ)≤2*b+3*(13*C*(1+3^d)*36^(d-1))*θ^(d-1) := by
  let ψ : X × Cube → Point := decode ∘ Prod.snd
  let β := ((μ : Measure (X × Cube)).restrict H).map ψ
  let D : Fin 3 → Set Point := fun j => closedBall (0:Point) 1 ∩ {x | |dot (rawNormal t) x-c j|≤18*θ}
  let A : Fin 3 → Set (X × Cube) := fun j => ψ ⁻¹' D j ∩ H
  let O : Set (X × Cube) := Prod.snd ⁻¹' (encode '' awayStrips t θ c)
  have hD (j : Fin 3) : MeasurableSet (D j) := measurableSet_closedBall.inter
    (isClosed_le (((continuous_dot _).sub continuous_const).abs) continuous_const).measurableSet
  have hψ : Measurable ψ := measurable_decode.comp measurable_snd
  have hsub : H ⊆ O ∪ ⋃ j : Fin 3, A j := by
    intro z hz
    have hp := hpos z hz
    by_cases hstrip : ∃ j, |dot (rawNormal t) (ψ z)-c j|≤18*θ
    · obtain ⟨j,hj⟩ := hstrip
      refine Or.inr (mem_iUnion.mpr ⟨j,⟨?_,hj⟩,hz⟩)
      simpa only [mem_closedBall,dist_zero_right,ψ,Function.comp_apply] using hp.1
    · apply Or.inl
      refine ⟨ψ z,⟨?_,fun j => lt_of_not_ge (fun hj => hstrip ⟨j,hj⟩)⟩,hp.2⟩
      have hx := (norm_fst_le (ψ z)).trans hp.1
      have hy := (norm_snd_le (ψ z)).trans hp.1
      rw [Real.norm_eq_abs] at hx hy
      have hx' := abs_le.mp hx
      have hy' := abs_le.mp hy
      change -2<(ψ z).1 ∧ (ψ z).1<2 ∧ -2<(ψ z).2 ∧ (ψ z).2<2
      constructor
      · linarith
      constructor
      · linarith
      constructor <;> linarith
  have hA (j : Fin 3) : (μ : Measure (X × Cube)) (A j)=β (D j) := by
    rw [Measure.map_apply hψ (hD j),Measure.restrict_apply ((hD j).preimage hψ)]
  have hstrip (j : Fin 3) : (ν : Measure (X × Cube)) (A j)≤
      ENNReal.ofReal (13*C*(1+3^d)*36^(d-1)*θ^(d-1)) := by
    exact (hν (A j)).trans ((hA j) ▸ raw_strip_bound β hC hd hbound t (c j) hθ)
  have haway' : (ν : Measure (X × Cube)) O≤ENNReal.ofReal (2*b) := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal haway
  have htotal : (ν : Measure (X × Cube)) H≤
      ENNReal.ofReal (2*b+3*(13*C*(1+3^d)*36^(d-1))*θ^(d-1)) := by
    calc
      _ ≤ (ν : Measure (X × Cube)) (O ∪ ⋃ j : Fin 3, A j) := measure_mono hsub
      _ ≤ (ν : Measure (X × Cube)) O + (ν : Measure (X × Cube)) (⋃ j : Fin 3, A j) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2*b)+∑ j : Fin 3, ENNReal.ofReal (13*C*(1+3^d)*36^(d-1)*θ^(d-1)) := by
        apply add_le_add haway'
        exact (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum (fun j _ => hstrip j))
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast 3,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← ENNReal.ofReal_coe_nnreal] at htotal
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htotal

end PlanarHalving.Spatial

namespace PlanarHalving.Boundary
open Set
open scoped Classical

lemma sum_batchRange {M : Type*} [AddCommMonoid M] {R s m : ℕ} (h : s+m≤R) (w : Fin R → M) :
    ∑ i∈batchRange R s m, w i=∑ i : Fin m, w ⟨s+i.val,by omega⟩ := by
  classical
  symm
  apply Finset.sum_bij (fun i _ => (⟨s+i.val,by omega⟩ : Fin R))
  · intro i _
    simp only [batchRange,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor <;> omega
  · intro i _ j _ hij
    have hh := congrArg Fin.val hij
    apply Fin.ext
    simpa using hh
  · intro i hi
    obtain ⟨hil,hir⟩ := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val-s,by omega⟩,Finset.mem_univ _,?_⟩
    apply Fin.ext
    simp only
    omega
  · intro i _; rfl

lemma sum_disjoint_ranges {ι : Type*} (F : Finset ι) {R : ℕ} (s m : ι → ℕ)
    (hd : Set.PairwiseDisjoint (↑F:Set ι) (fun j => batchRange R (s j) (m j)))
    (w : Fin R → ℝ) (hw : ∀ i, 0≤w i) :
    ∑ j∈F, ∑ i∈batchRange R (s j) (m j), w i ≤ ∑ i : Fin R, w i := by
  classical
  rw [← Finset.sum_biUnion hd]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)

lemma parameter_telescope {R : ℕ} (t : Fin (R+1) → ℝ) :
    ∑ i : Fin R, (t i.succ-t i.castSucc)=t (Fin.last R)-t 0 := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ t
  have h₂ := Fin.sum_univ_castSucc t
  linarith

lemma parameter_range_sum {R s m : ℕ} (h : s+m≤R) (t : Fin (R+1) → ℝ) :
    ∑ i∈batchRange R s m, (t i.succ-t i.castSucc)=
      t ⟨s+m,by omega⟩-t ⟨s,by omega⟩ := by
  rw [sum_batchRange h]
  convert parameter_telescope (fun i : Fin (m+1) => t ⟨s+i.val,by omega⟩) using 1 <;> simp [Nat.add_assoc]

lemma parameter_budget {ι : Type*} (F : Finset ι) {R : ℕ} (s m : ι → ℕ)
    (hd : Set.PairwiseDisjoint (↑F:Set ι) (fun j => batchRange R (s j) (m j)))
    (t : Fin (R+1) → ℝ) (ht : Monotone t) (htI : ∀ i,t i∈Icc (0:ℝ) 1) :
    ∑ j∈F, ∑ i∈batchRange R (s j) (m j), (t i.succ-t i.castSucc) ≤ 1 := by
  have hh := sum_disjoint_ranges F s m hd (fun i => t i.succ-t i.castSucc)
    (fun i => sub_nonneg.mpr (ht (by simp [Fin.le_def])))
  rw [parameter_telescope] at hh
  have hlo := (htI 0).1
  have hhi := (htI (Fin.last R)).2
  linarith

end PlanarHalving.Boundary

namespace PlanarHalving.Batches
open Set TimeWindows
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertices_eq_of_marks (S T : @System n R k a P) (h : S.marks=T.marks) :
    S.vertices=T.vertices := by
  classical
  unfold System.vertices System.edges System.loss System.gain
  rw [h]

lemma System.relative_vertices (S : @System n R k a P) [NeZero R]
    {K J : Window} (h : carrier J⊆carrier K) :
    ((S.timeWindow K).window (start R J-start R K) (length R J) (relative_end_le R h)).vertices=
      (S.timeWindow J).vertices := by
  apply System.vertices_eq_of_marks
  funext i
  dsimp [System.timeWindow,System.window]
  congr 1
  apply Fin.ext
  simp only
  have hc := (cuts_of_subset R h).1
  omega

end PlanarHalving.Batches

namespace PlanarHalving.Boundary
open Set Filter
open scoped Topology unitInterval PiCountable

lemma params_subsequence {J : Type*} [Countable J] (p : ℕ → J → CompactParams) :
    ∃ (φ : ℕ → ℕ) (b t θ : J → ℝ) (c : J → Fin 3 → ℝ), StrictMono φ ∧
      (∀ j, b j∈Icc (0:ℝ) 4 ∧ t j∈Icc (0:ℝ) 1 ∧ θ j∈Icc (0:ℝ) 1 ∧
        ∀ i, c j i∈Icc (-4:ℝ) 4) ∧
      (∀ j, Tendsto (fun n => (p (φ n) j).1.val) atTop (𝓝 (b j))) ∧
      (∀ j, Tendsto (fun n => (p (φ n) j).2.1.val) atTop (𝓝 (t j))) ∧
      (∀ j, Tendsto (fun n => (p (φ n) j).2.2.1.val) atTop (𝓝 (θ j))) ∧
      (∀ j, Tendsto (fun n i => ((p (φ n) j).2.2.2 i).val) atTop (𝓝 (c j))) := by
  obtain ⟨q,φ,hφ,hq⟩ := CompactSpace.tendsto_subseq p
  refine ⟨φ,fun j => (q j).1.val,fun j => (q j).2.1.val,fun j => (q j).2.2.1.val,
    fun j i => ((q j).2.2.2 i).val,hφ,?_,?_,?_,?_,?_⟩
  · intro j
    exact ⟨(q j).1.property,(q j).2.1.property,(q j).2.2.1.property,
      fun i => ((q j).2.2.2 i).property⟩
  · intro j
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp hq j).fst_nhds
  · intro j
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp hq j).snd_nhds.fst_nhds
  · intro j
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp hq j).snd_nhds.snd_nhds.fst_nhds
  · intro j
    apply tendsto_pi_nhds.mpr
    intro i
    exact continuous_subtype_val.tendsto _ |>.comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hq j).snd_nhds.snd_nhds.snd_nhds i)

lemma finite_budget_limit {J : Type*} (F : Finset J) (f : ℕ → J → ℝ) (g : J → ℝ) {B : ℝ}
    (h : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (g j)))
    (hf : ∀ᶠ n in atTop, ∑ j∈F, f n j ≤ B) : ∑ j∈F, g j≤B := by
  apply le_of_tendsto (tendsto_finsetSum F (fun j _ => h j)) hf

end PlanarHalving.Boundary

namespace PlanarHalving.Batches
open Set Boundary
open scoped Classical
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertices_changes (S : @System n R k a P) {v : Fin n} (hv : v∈S.vertices) :
    ∃ i j : Fin (R+1), ¬(v∈S.marks i ↔ v∈S.marks j) := by
  classical
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b,hb,_⟩ := (S.mem_edges e).mp he
    obtain ⟨hl,hr⟩ := Finset.mem_sdiff.mp hb
    exact ⟨b.castSucc,b.succ,fun h => hr (h.mp hl)⟩
  · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b,_,hb⟩ := (S.mem_edges e).mp he
    obtain ⟨hl,hr⟩ := Finset.mem_sdiff.mp hb
    exact ⟨b.castSucc,b.succ,fun h => hr (h.mpr hl)⟩

lemma System.boundary_budget (S : @System n R k a P) [NeZero a]
    (p : Fin n → Point) (j : Fin a)
    (h1 : ∀ u, Monotone (fun i => (p (S.tokenState j i u)).1))
    (h2 : ∀ u, Monotone (fun i => (p (S.tokenState j i u)).2)) :
    ∑ i : Fin R, S.boundaryCount p j i ≤ 4*n := by
  have hh := square_token_budget (fun i u => p (S.tokenState j i u)) h1 h2 (-2) 2
  apply hh.trans
  rw [Fintype.card_coe]
  exact Nat.mul_le_mul_left _ (by simpa using Finset.card_le_univ (S.marks 0))

lemma System.window_boundary (S : @System n R k a P) [NeZero a]
    (E : Point ≃L[ℝ] Point) {A B l u : ℝ} (hA : 0<A) (hB : 0<B) (hlu : l<u)
    (h1 : E (1,0)=A • (1,l)) (h2 : E (0,1)=B • (1,u))
    (hspan : ∀ i, S.slope i∈Icc l u) (o : Point) {r : ℝ} (hr : 0<r)
    (j : Fin a) (s m : ℕ) (hsm : s+m ≤ R) :
    let T := fun i : Fin (R+1) => frameParameter A B l u (S.slope i)
    let i₀ : Fin (R+1) := ⟨s,by omega⟩
    let i₁ : Fin (R+1) := ⟨s+m,by omega⟩
    ∃ c : Fin 3 → ℝ, (∀ h, c h∈Icc (-4:ℝ) 4) ∧
      (((S.window s m hsm).vertices.filter fun v =>
        InSquare (-2) 2 (physical E o r (P v)) ∧
          ∀ h, 18*(T i₁-T i₀) < |dot (rawNormal (T i₀)) (physical E o r (P v))-c h|).card) ≤
        2*∑ i : Fin m, S.boundaryCount (fun v => physical E o r (P v)) j ⟨s+i.val,by omega⟩ := by
  classical
  dsimp only
  obtain ⟨c,hc⟩ := actual_transformed_cuts S E hA hB hlu h1 h2 hspan o hr
  let idx : Fin (m+1) → Fin (R+1) := fun i => ⟨s+i.val,by omega⟩
  let f : Fin (m+1) → ↥(S.marks 0) → Fin n := fun i t => S.tokenState j (idx i) t
  have hf : ∀ i, Function.Injective (f i) := fun i => Subtype.val_injective.comp (S.tokenState j (idx i)).injective
  have himg (i : Fin (m+1)) (v : Fin n) : v∈Finset.univ.image (f i) ↔ v∈S.marks (idx i) := by
    constructor
    · intro hv
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
      exact (S.tokenState j (idx i) u).property
    · intro hv
      exact Finset.mem_image.mpr ⟨(S.tokenState j (idx i)).symm ⟨v,hv⟩,Finset.mem_univ _,
        congrArg Subtype.val ((S.tokenState j (idx i)).apply_symm_apply _)⟩
  have ht : Monotone (fun i : Fin (m+1) => frameParameter A B l u (S.slope (idx i))) := by
    intro v w hvw
    apply frameParameter_monotone hA hB hlu (hspan _) (hspan _)
    apply S.increasing.monotone
    simp only [idx,Fin.le_def]
    exact Nat.add_le_add_left hvw s
  have htI (i : Fin (m+1)) : frameParameter A B l u (S.slope (idx i))∈Icc (0:ℝ) 1 :=
    frameParameter_mem hA hB hlu (hspan _)
  have hh := finite_raw_bound (fun v => physical E o r (P v)) f hf
    (S.window s m hsm).vertices (fun i => frameParameter A B l u (S.slope (idx i))) (fun i => c (idx i)) ht htI
    (by
      intro i v
      simpa only [Finset.mem_image,Finset.mem_univ,true_and] using (himg i v).trans (hc (idx i) v))
    (by
      intro v hv
      obtain ⟨i,j,hij⟩ := (S.window s m hsm).vertices_changes hv
      refine ⟨i,j,?_⟩
      intro he
      apply hij
      have hi := himg i v
      have hj := himg j v
      simp only [Finset.mem_image,Finset.mem_univ,true_and] at he hi hj
      exact hi.symm.trans (he.trans hj))
  obtain ⟨d,hd,hbound⟩ := hh
  refine ⟨d,hd,?_⟩
  have hsum : (∑ i : Fin m, (Finset.univ.filter fun u : ↥(S.marks 0) =>
      ¬(InSquare (-2) 2 (physical E o r (P (f i.castSucc u))) ↔
        InSquare (-2) 2 (physical E o r (P (f i.succ u))))).card)=
      ∑ i : Fin m, S.boundaryCount (fun v => physical E o r (P v)) j ⟨s+i.val,by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
  rw [hsum] at hbound
  convert hbound using 1; congr 1

end PlanarHalving.Batches

namespace PlanarHalving.TimeWindows
open Set Boundary
open scoped Classical

lemma relative_range_disjoint (R : ℕ) [NeZero R] {K : Window} (J H : Subwindow K)
    (h : Disjoint (carrier J.val) (carrier H.val)) :
    Disjoint (batchRange (length R K) (start R J.val-start R K) (length R J.val))
      (batchRange (length R K) (start R H.val-start R K) (length R H.val)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  have hJ := (cuts_of_subset R J.property).1
  have hH := (cuts_of_subset R H.property).1
  have hK := start_add_length R K
  have hK' := stop_le R K
  have heJ := start_add_length R J.val
  have heH := start_add_length R H.val
  let b : Fin R := ⟨start R K+i.val,by omega⟩
  have hbJ : time R b∈carrier J.val := by
    apply (mem_carrier_iff R J.val b).mpr
    dsimp [b]
    constructor <;> omega
  have hbH : time R b∈carrier H.val := by
    apply (mem_carrier_iff R H.val b).mpr
    dsimp [b]
    constructor <;> omega
  exact Set.disjoint_left.mp h hbJ hbH

end PlanarHalving.TimeWindows

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.ActivityRetention
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Boundary
open Set Filter MeasureTheory Batches TimeWindows RankLimits Enhancement Spatial
open scoped Topology unitInterval NNReal ENNReal Classical

lemma finite_window_params (F : Configuration) (K : Window) (E : Point ≃L[ℝ] Point)
    {A B l u : ℝ} (hA : 0 < A) (hB : 0 < B) (hlu : l < u)
    (h1 : E (1,0)=A • (1,l)) (h2 : E (0,1)=B • (1,u))
    (hspan : ∀ i, (F.system.timeWindow K).slope i ∈ Icc l u)
    (o : Point) {r : ℝ} (hr : 0 < r) :
    ∃ p : Subwindow K → CompactParams,
      (∀ J, (vertices F (physical E o r) J.val
        (Prod.snd ⁻¹' (encode '' awayStrips (p J).2.1.val (p J).2.2.1.val
          (fun i => ((p J).2.2.2 i).val))):ℝ) ≤ 2*(p J).1.val) ∧
      (∀ D : Finset (Subwindow K), Set.PairwiseDisjoint (↑D : Set (Subwindow K)) (fun J => carrier J.val) →
        (∑ J∈D, (p J).1.val) ≤ 4 ∧ (∑ J∈D, (p J).2.2.1.val) ≤ 1) := by
  classical
  let S := F.system.timeWindow K
  let pnt := fun v => physical E o r (F.point v)
  let j : Fin F.a := ⟨0,F.a_pos⟩
  let w : Fin (length F.R K) → ℝ := fun i => S.boundaryCount pnt j i
  let t : Fin (length F.R K+1) → ℝ := fun i => frameParameter A B l u (S.slope i)
  let s : Subwindow K → ℕ := fun J => start F.R J.val-start F.R K
  let m : Subwindow K → ℕ := fun J => length F.R J.val
  have hsm (J : Subwindow K) : s J+m J ≤ length F.R K := relative_end_le F.R J.property
  let b : Subwindow K → ℝ := fun J => (∑ i∈batchRange _ (s J) (m J), w i)/F.n
  let ti : Subwindow K → ℝ := fun J => t ⟨s J,by have := hsm J; omega⟩
  let theta : Subwindow K → ℝ := fun J => t ⟨s J+m J,by have := hsm J; omega⟩-ti J
  have hw (i) : 0 ≤ w i := Nat.cast_nonneg _
  have ht : Monotone t := by
    intro i i' hii'
    apply frameParameter_monotone hA hB hlu (hspan _) (hspan _)
    exact S.increasing.monotone hii'
  have htI (i) : t i ∈ Icc (0:ℝ) 1 := frameParameter_mem hA hB hlu (hspan _)
  have hcost : (∑ i, w i) ≤ 4*(F.n:ℝ) := by
    have hh := S.boundary_budget pnt j
      (fun v => (actual_tokens_monotone S E hA hB hlu h1 h2 hspan o hr j v).1)
      (fun v => (actual_tokens_monotone S E hA hB hlu h1 h2 hspan o hr j v).2)
    dsimp only [w]
    exact_mod_cast hh
  have hpos : 0 < (F.n:ℝ) := Nat.cast_pos.mpr F.n_pos
  have hb (J) : b J ∈ Icc (0:ℝ) 4 := by
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun i _ => hw i)) hpos.le
    · apply (div_le_iff₀ hpos).mpr
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hw i)).trans hcost
  have hti (J) : ti J ∈ Icc (0:ℝ) 1 := htI _
  have htheta (J) : theta J ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (ht (by simp [Fin.le_def]))
    · have hh := (htI (⟨s J+m J,by have := hsm J; omega⟩)).2
      have hh' := (hti J).1
      dsimp [theta]; linarith
  obtain ⟨c,hc,hfinite⟩ : ∃ c : Subwindow K → Fin 3 → ℝ,
      (∀ J h, c J h ∈ Icc (-4:ℝ) 4) ∧
      ∀ J, (((S.window (s J) (m J) (hsm J)).vertices.filter fun v =>
        pnt v∈awayStrips (ti J) (theta J) (c J)).card) ≤
          2*∑ i : Fin (m J), S.boundaryCount pnt j ⟨s J+i.val,by have := hsm J; omega⟩ := by
    choose c hc hb using fun J => S.window_boundary E hA hB hlu h1 h2 hspan o hr j (s J) (m J) (hsm J)
    refine ⟨c,hc,fun J => ?_⟩
    convert hb J using 1
    congr 1
    apply Finset.filter_congr
    intro v _
    rfl
  let p : Subwindow K → CompactParams := fun J =>
    (⟨b J,hb J⟩,⟨ti J,hti J⟩,⟨theta J,htheta J⟩,fun i => ⟨c J i,hc J i⟩)
  refine ⟨p,?_,?_⟩
  · intro J
    change (vertices F (physical E o r) J.val (Prod.snd ⁻¹' (encode '' awayStrips (ti J) (theta J) (c J))):ℝ) ≤ 2*b J
    rw [vertices,System.vertexMeasure_apply _ _ ((isOpenMap_encode _ (isOpen_awayStrips _ _ _)).measurableSet.preimage measurable_snd)]
    have he : ((F.system.timeWindow J.val).vertices.filter fun v =>
        label F (physical E o r) (F.point v)∈Prod.snd ⁻¹' (encode '' awayStrips (ti J) (theta J) (c J))) =
      ((S.window (s J) (m J) (hsm J)).vertices.filter fun v => pnt v∈awayStrips (ti J) (theta J) (c J)) := by
      rw [show (S.window (s J) (m J) (hsm J)).vertices=(F.system.timeWindow J.val).vertices from
        F.system.relative_vertices J.property]
      apply Finset.filter_congr
      intro v _
      exact encode_injective.mem_set_image
    rw [he]
    apply (div_le_iff₀ hpos).mpr
    have hh : (((S.window (s J) (m J) (hsm J)).vertices.filter fun v => pnt v∈awayStrips (ti J) (theta J) (c J)).card:ℝ) ≤
        2*∑ i∈batchRange _ (s J) (m J), w i := by
      rw [sum_batchRange (hsm J)]
      dsimp only [w]
      exact_mod_cast hfinite J
    calc
      _ ≤ 2*∑ i∈batchRange _ (s J) (m J), w i := hh
      _ = 2*b J*(F.n:ℝ) := by
        dsimp [b]
        field_simp
  · intro D hD
    have hd : Set.PairwiseDisjoint (↑D : Set (Subwindow K)) (fun J => batchRange (length F.R K) (s J) (m J)) := by
      intro J hJ H hH hJH
      exact relative_range_disjoint F.R J H (hD hJ hH hJH)
    constructor
    · change (∑ J∈D, b J) ≤ 4
      simp only [b,← Finset.sum_div]
      apply (div_le_iff₀ hpos).mpr
      exact (sum_disjoint_ranges D s m hd w hw).trans hcost
    · change (∑ J∈D, theta J) ≤ 1
      have he (J : Subwindow K) : theta J=∑ i∈batchRange _ (s J) (m J), (t i.succ-t i.castSucc) :=
        (parameter_range_sum (hsm J) t).symm
      simp_rw [he]
      exact parameter_budget D s m hd t ht htI

end PlanarHalving.Boundary

namespace PlanarHalving.RankLimits
open Set TimeWindows Boundary
open scoped Classical

lemma mem_subPartition {K : Window} {m : ℕ} {J : Subwindow K} :
    J∈subPartition K m ↔ J.val∈localPartition K m := by
  unfold subPartition
  constructor
  · intro h
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
    exact j.property
  · intro h
    exact Finset.mem_image.mpr ⟨⟨J.val,h⟩,Finset.mem_attach _ _,Subtype.ext rfl⟩

lemma subPartition_map_val (K : Window) (m : ℕ) :
    (subPartition K m).image Subtype.val=localPartition K m := by
  ext J
  constructor
  · intro h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    exact mem_subPartition.mp hj
  · intro h
    exact Finset.mem_image.mpr ⟨⟨J,localPartition_subset h⟩,mem_subPartition.mpr h,rfl⟩

lemma subPartition_sum {M : Type*} [AddCommMonoid M] (K : Window) (m : ℕ) (f : Window → M) :
    ∑ J∈subPartition K m, f J.val=∑ J∈localPartition K m, f J := by
  rw [← subPartition_map_val K m]
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]

lemma subPartition_disjoint (K : Window) (m : ℕ) :
    Set.PairwiseDisjoint (↑(subPartition K m):Set (Subwindow K)) (fun J => carrier J.val) := by
  intro J hJ H hH hJH
  exact localPartition_disjoint K m (mem_subPartition.mp hJ) (mem_subPartition.mp hH)
    (fun he => hJH (Subtype.ext he))

lemma subPartition_card (K : Window) (m : ℕ) : (subPartition K m).card ≤ 2^(K.1+m) := by
  have he : (subPartition K m).card=(localPartition K m).card := by
    rw [← subPartition_map_val K m,Finset.card_image_of_injective _ Subtype.val_injective]
  rw [he]
  apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
  exact (Finset.card_image_le).trans (by simp)

lemma subPartition_tail {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (K : Window) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    (((subPartition K m).filter fun J => u < ((L.vertices J.val).mass:ℝ)).card:ℝ) ≤
      10000*u^(-(4:ℝ)/3) := by
  have hh := h.activity_tail E (K.1+m) hu
  rw [← filter_timePartition (K.1+m) (fun J => u < ((L.vertices J).mass:ℝ))] at hh
  apply hh.trans'
  apply Nat.cast_le.mpr
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro J hJ
    obtain ⟨hJ,hJu⟩ := Finset.mem_filter.mp hJ
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (mem_subPartition.mp hJ)).1,hJu⟩
  · exact Subtype.val_injective.injOn

end PlanarHalving.RankLimits

namespace PlanarHalving.Enhancement
open Set Filter MeasureTheory Batches TimeWindows RankLimits Limits Spatial
open scoped Topology unitInterval NNReal ENNReal Classical

lemma limit_vertices_le {F : ℕ → Configuration} {ψ : ℕ → Point → Point}
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (ψ n) i) atTop (𝓝 (M i))) (J : Window) :
    (M (.vertex J) : Measure Space) ≤ (M .point : Measure Space) :=
  measure_le_of_weak_limits (hM (.vertex J)) (hM .point) (fun n => vertices_le_points (F n) (ψ n) J)

lemma limit_edge_ac {F : ℕ → Configuration} {ψ : ℕ → Point → Point}
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (ψ n) i) atTop (𝓝 (M i)))
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) : (M (.edge J) : Measure Space) ≪ (M .point : Measure Space) := by
  apply Measure.AbsolutelyContinuous.trans (μ₂ := (M (.vertex J) : Measure Space))
    _ (Measure.absolutelyContinuous_of_le (limit_vertices_le hM J))
  intro U hU
  let V := toMeasurable (M (.vertex J) : Measure Space) U
  have hc := local_cubic hM hC hcoeff herror J (measurableSet_toMeasurable (M (.vertex J) : Measure Space) U)
  have hV : M (.vertex J) V=0 := by
    apply ENNReal.coe_eq_zero.mp
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,measure_toMeasurable]
    exact hU
  change (M (.edge J) V:ℝ)^3 ≤ C*((M (.vertex J)).mass:ℝ)^3*(M (.vertex J) V:ℝ) at hc
  rw [hV,NNReal.coe_zero,mul_zero] at hc
  have hz : M (.edge J) V=0 := by
    apply NNReal.coe_injective
    exact (pow_eq_zero_iff (by norm_num : (3:ℕ)≠0)).mp
      (le_antisymm hc (pow_nonneg (NNReal.coe_nonneg _) _))
  apply measure_mono_null (subset_toMeasurable _ _)
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hz,ENNReal.coe_zero]

lemma lifted_mass (μ ν : FiniteMeasure Space) (ρ : FiniteMeasure Labels)
    (hac : (ν : Measure Space) ≪ (μ : Measure Space)) (hmap : ν.map Prod.fst=ρ)
    {G : Set Labels} (hG : MeasurableSet G) :
    (ν (Prod.fst ⁻¹' G ∩ (μ : Measure Space).support):ℝ)=(ρ G:ℝ) := by
  have hr := congrArg (fun m : Measure Space => m univ)
    (support_lift_restrict (μ:Measure Space) (ν:Measure Space) hac (Prod.fst ⁻¹' G))
  simp only [Measure.restrict_apply_univ] at hr
  have he := congrArg (fun m : FiniteMeasure Labels => (m:Measure Labels) G) hmap
  rw [FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hG] at he
  change ((ν:Measure Space) _).toReal=((ρ:Measure Labels) G).toReal
  rw [hr,he]

lemma projected_mass (ν : FiniteMeasure Space) (ρ : FiniteMeasure Labels)
    (hmap : ν.map Prod.fst=ρ) : ν.mass=ρ.mass := by
  rw [← hmap]
  change ν univ=(ν.map Prod.fst) univ
  rw [FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ,preimage_univ]

end PlanarHalving.Enhancement

namespace PlanarHalving.Boundary
open Set Filter Metric MeasureTheory Batches TimeWindows RankLimits Enhancement Spatial
open scoped Topology unitInterval NNReal ENNReal Classical

lemma enhanced_boundary_zero_oai {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (emb : ∀ n, (F n).SweepEmbedding)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (K : Window) (E : ℕ → Point ≃L[ℝ] Point) (o : ℕ → Point) (r : ℕ → ℝ)
    (hr : ∀ n, 0<r n)
    (hframe : ∀ n, ∃ A B l u : ℝ, 0<A ∧ 0<B ∧ l<u ∧
      E n (1,0)=A • (1,l) ∧ E n (0,1)=B • (1,u) ∧
      ∀ i, ((F n).system.timeWindow K).slope i∈Icc l u)
    {M : Index → FiniteMeasure Space}
    (hM : ∀ i, Tendsto (fun n => measures (F n) (physical (E n) (o n) (r n)) i) atTop (𝓝 (M i)))
    (hprojection : ∀ i, (M i).map Prod.fst=old L i)
    (G : Set Labels) (hG : MeasurableSet G)
    (hpos : ∀ z∈Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support,
      ‖decode z.2‖≤1 ∧ encode (decode z.2)=z.2)
    {D : ℝ} (hD : 0≤D)
    (hdisk : ∀ x : Point, ∀ t : ℝ, 0<t →
      (((M .point : Measure Space).restrict (Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support)).map
        (decode ∘ Prod.snd)) (closedBall x t)≤ENNReal.ofReal (D*t^((32:ℝ)/17))) :
    (L.edgeWindow K G:ℝ)=0 := by
  classical
  let H := Prod.fst ⁻¹' G ∩ (M .point : Measure Space).support
  have hH : MeasurableSet H := (hG.preimage measurable_fst).inter (M .point : Measure Space).isClosed_support.measurableSet
  choose A B lo up ha hb hlu h1 h2 hspan using hframe
  have hparams := fun n => finite_window_params (F n) K (E n)
    (ha n) (hb n) (hlu n) (h1 n) (h2 n) (hspan n) (o n) (hr n)
  choose p hp hbudget using hparams
  obtain ⟨φ,b,t,θ,c,hφ,hbounds,hb,ht,hθ,hc⟩ := params_subsequence p
  have haway (J : Subwindow K) :
      (M (.vertex J.val) (Prod.snd ⁻¹' (encode '' awayStrips (t J) (θ J) (c J))):ℝ)≤2*b J := by
    apply moving_strips_limit ((hM (.vertex J.val)).comp hφ.tendsto_atTop)
      (ht J) (hθ J) (hc J) (hb J)
    exact Filter.Eventually.of_forall (fun n => hp (φ n) J)
  have hactivity (J : Subwindow K) : (M (.vertex J.val) H:ℝ)≤
      2*b J+3*(13*D*(1+3^((32:ℝ)/17))*36^((32:ℝ)/17-1))*θ J^((32:ℝ)/17-1) := by
    exact limiting_activity_bound (M .point) (M (.vertex J.val)) H hH
      (limit_vertices_le hM J.val) hpos hD (by norm_num) (hbounds J).2.2.1.1
      (hbounds J).1.1 (c J) hdisk (haway J)
  have hbudgets (m : ℕ) : (∑ J∈subPartition K m, b J)≤4 ∧ (∑ J∈subPartition K m, θ J)≤1 := by
    constructor
    · exact finite_budget_limit (subPartition K m) _ b hb
        (Filter.Eventually.of_forall (fun n => (hbudget (φ n) (subPartition K m) (subPartition_disjoint K m)).1))
    · exact finite_budget_limit (subPartition K m) _ θ hθ
        (Filter.Eventually.of_forall (fun n => (hbudget (φ n) (subPartition K m) (subPartition_disjoint K m)).2))
  have hlam (J : Window) : (M (.edge J) H:ℝ)=(L.edgeWindow J G:ℝ) :=
    lifted_mass (M .point) (M (.edge J)) (L.edgeWindow J)
      (limit_edge_ac hM hC hcoeff herror J) (hprojection (.edge J)) hG
  have hvertex (J : Window) : (M (.vertex J)).mass=(L.vertices J).mass :=
    projected_mass _ _ (hprojection (.vertex J))
  let q : ℕ → ℝ := fun m => (2:ℝ)^(K.1+m)
  have hq : ∀ m, 0<q m := fun _ => by positivity
  have hqtop : Tendsto q atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp (tendsto_atTop_mono (fun n => Nat.le_add_left n K.1) tendsto_id)
  apply mass_eq_zero (subPartition K) (fun _ J => (M (.edge J.val) H:ℝ))
    (fun _ J => (M (.vertex J.val) H:ℝ)) (fun _ J => ((L.vertices J.val).mass:ℝ))
    (fun _ J => b J) (fun _ J => θ J) q (A:=C)
    (H:=10000) (B:=3*(13*D*(1+3^((32:ℝ)/17))*36^((32:ℝ)/17-1))) (B₀:=4) (T:=1)
    (α:=(32:ℝ)/17-1) (NNReal.coe_nonneg _) hC (by positivity) (by norm_num)
    (by norm_num) (by norm_num) hq hqtop
  · intro m
    simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using
      (Nat.cast_le (α:=ℝ).mpr (subPartition_card K m))
  · intro m J _
    exact NNReal.coe_nonneg _
  · intro m J hJ
    rw [hlam]
    have hd := mem_timePartition.mp (Finset.mem_filter.mp (mem_subPartition.mp hJ)).1
    apply (NNReal.coe_le_coe.mpr ((L.edgeWindow J.val).apply_le_mass G)).trans_eq
    rw [hF.edgeWindow_mass hR,hd]
    simp only [q,Nat.cast_pow,Nat.cast_ofNat]
  · intro m J _; exact NNReal.coe_nonneg _
  · intro m J _; exact NNReal.coe_nonneg _
  · intro m J _; exact (hbounds J).2.2.1.1
  · intro m J _
    have hh := Enhancement.local_cubic hM hC hcoeff herror J.val hH
    rwa [hvertex] at hh
  · intro m J _; exact hactivity J
  · intro m; exact (hbudgets m).1
  · intro m; exact (hbudgets m).2
  · intro m u hu; exact subPartition_tail hF emb K m hu
  · intro m
    simp_rw [hlam]
    rw [subPartition_sum K m (fun J => (L.edgeWindow J G:ℝ)),hF.localPartition_sum hR K m hG]

end PlanarHalving.Boundary

end OAI
end

theorem solution : type_of% @OAI.PlanarHalving.Boundary.enhanced_boundary_zero_oai := @OAI.PlanarHalving.Boundary.enhanced_boundary_zero_oai

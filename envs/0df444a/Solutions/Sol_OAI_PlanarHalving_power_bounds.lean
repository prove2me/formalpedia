-- Prove2me | solution 1 for OAI.PlanarHalving.power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:56:43.050743+00:00
-- url     : https://prove2.me/submissions/57545e63-ac1b-4585-88b6-d9de75448a9e

import Mathlib
import Definitions.Def_HalvingLines
import Definitions.Def_OAIQWPHL000
import Theorems.Thm_OAI_PlanarHalving_RankLimits_Converges_impossible

section
-- module Solutions.OAIQW_PlanarHalving.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

theorem orient_swap (p q r : Point) : orient q p r = -orient p q r := by
  unfold orient
  ring

lemma sideCount_add_reverse {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {i j : Fin n} (hij : i ≠ j) : sideCount P i j + sideCount P j i = n - 2 := by
  classical
  let A := Finset.univ.filter (fun l => 0 < orient (P i) (P j) (P l))
  let B := Finset.univ.filter (fun l => 0 < orient (P j) (P i) (P l))
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro l hlA hlB
    have ha : 0 < orient (P i) (P j) (P l) := (Finset.mem_filter.mp hlA).2
    have hb : 0 < orient (P j) (P i) (P l) := (Finset.mem_filter.mp hlB).2
    rw [orient_swap] at hb
    linarith only [ha, hb]
  have hu : A ∪ B = (Finset.univ.erase i).erase j := by
    ext l
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase]
    rw [orient_swap (P i) (P j) (P l)]
    have hz := orient_zero_iff hP hij l
    constructor
    · intro hl
      have hn : orient (P i) (P j) (P l) ≠ 0 := by
        rcases hl with hl | hl <;> linarith only [hl]
      have hn' : ¬ (l = i ∨ l = j) := fun he => hn (hz.mpr he)
      exact ⟨fun h => hn' (Or.inr h), fun h => hn' (Or.inl h), trivial⟩
    · rintro ⟨hlj, hli, _⟩
      have hn : orient (P i) (P j) (P l) ≠ 0 := by
        intro hh
        rcases hz.mp hh with hh | hh
        · exact hli hh
        · exact hlj hh
      rcases lt_or_gt_of_ne hn with hl | hl
      · right; linarith only [hl]
      · exact Or.inl hl
  change A.card + B.card = n - 2
  rw [← Finset.card_union_of_disjoint hd, hu,
    Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

lemma belowCount_eq_sideCount_of_x_lt {n : ℕ} (P : Fin n → Point) (i j : Fin n)
    (hx : (P i).1 < (P j).1) : belowCount P i j = sideCount P j i := by
  classical
  unfold belowCount sideCount
  dsimp only
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro l _
  rw [orient_swap, orient_eq_proj_diff _ _ _ hx.ne']
  have hx' : 0 < (P j).1 - (P i).1 := sub_pos.mpr hx
  rw [neg_pos]
  simp only [mul_neg_iff, hx', hx'.not_gt, true_and, false_and,
    or_false, sub_neg]

lemma belowCount_eq_sideCount_of_x_gt {n : ℕ} (P : Fin n → Point) (i j : Fin n)
    (hx : (P j).1 < (P i).1) : belowCount P i j = sideCount P i j := by
  classical
  unfold belowCount sideCount
  dsimp only
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro l _
  rw [orient_eq_proj_diff _ _ _ hx.ne]
  have hx' : (P j).1 - (P i).1 < 0 := sub_neg.mpr hx
  simp only [mul_pos_iff, hx', hx'.not_gt, true_and, false_and,
    false_or, sub_neg]

theorem halvingCount_eq_middle_switchCount {m : ℕ} (hm : 0 < m)
    (P : Fin (2 * m) → Point) (hP : Generic P) :
    halvingCount P = switchCount P m := by
  classical
  unfold halvingCount switchCount
  congr 1
  apply Finset.filter_congr
  intro ij _
  have hm' : m < 2 * m := by omega
  simp only [hm, hm', true_and]
  by_cases hij : ij.1 < ij.2
  · simp only [hij, true_and]
    have hs := sideCount_add_reverse hP.1 hij.ne
    have hdiv : (2 * m - 2) / 2 = m - 1 := by omega
    rw [hdiv]
    rcases lt_or_gt_of_ne (hP.2.1 ij.1 ij.2 hij.ne) with hx | hx
    · rw [belowCount_eq_sideCount_of_x_lt P _ _ hx]
      omega
    · rw [belowCount_eq_sideCount_of_x_gt P _ _ hx]
      omega
  · simp only [hij, false_and]

end PlanarHalving

end OAI
end

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

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology unitInterval NNReal ENNReal

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
-- module Solutions.OAIQW_PlanarHalving.Directions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Batches
open MeasureTheory Set Filter Limits TimeWindows
open scoped Topology NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.labelTimeMeasure_mass (S : @System n R k a P) [NeZero R] [NeZero a]
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) :
    (S.labelTimeMeasure z).mass=1 := by
  rw [System.labelTimeMeasure,mass_weightedAtoms]
  simp only [Fintype.card_coe,S.card_edges,Nat.cast_mul,Nat.cast_pow]
  exact inv_mul_cancel₀ (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne R))
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne a))))

end PlanarHalving.Batches

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal

theorem finiteMeasure_subsequence_dependent
    {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, MetricSpace (X i)] [∀ i, CompactSpace (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)]
    (μ : ℕ → ∀ i, FiniteMeasure (X i)) (C : ι → ℝ≥0)
    (hbound : ∀ n i, (μ n i).mass ≤ C i) :
    ∃ (φ : ℕ → ℕ) (ν : ∀ i, FiniteMeasure (X i)), StrictMono φ ∧
      ∀ i, Tendsto (fun n => μ (φ n) i) atTop (𝓝 (ν i)) := by
  let F : ℕ → ∀ i : ι, (Icc (0 : ℝ≥0) (C i)) × ProbabilityMeasure (X i) :=
    fun n i => (⟨(μ n i).mass,zero_le,hbound n i⟩,(μ n i).normalize)
  obtain ⟨g,φ,hφ,hg⟩ := CompactSpace.tendsto_subseq F
  refine ⟨φ,fun i => (g i).1.val • (g i).2.toFiniteMeasure,hφ,?_⟩
  intro i
  have hi := (tendsto_pi_nhds.mp hg) i
  have hm := continuous_subtype_val.tendsto _ |>.comp ((continuous_fst.tendsto (g i)).comp hi)
  have hn := (ProbabilityMeasure.toFiniteMeasure_isEmbedding (X i)).continuous.tendsto _ |>.comp
    ((continuous_snd.tendsto (g i)).comp hi)
  have ht := hm.smul hn
  convert ht using 1
  funext n
  exact (μ (φ n) i).self_eq_mass_smul_normalize

end PlanarHalving.Limits
namespace PlanarHalving.Batches
open MeasureTheory Set Limits TimeWindows PlaneGraph
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.vertexMeasure_mass_le (S : @System n R k a P) [NeZero n]
    {X : Type*} [MeasurableSpace X] (z : Fin n → X) : (S.vertexMeasure z).mass ≤ 1 := by
  rw [System.vertexMeasure,mass_weightedAtoms]
  have hcard : Fintype.card ↥S.vertices ≤ n := by simpa using S.vertices.card_le_univ
  calc
    _ ≤ (n : ℝ≥0)⁻¹ * n := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) zero_le
    _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n))

lemma System.windowCrossMeasure_mass_le (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    (hP : Generic P) (A B : Window) {X : Type*} [MeasurableSpace X] (z : Point → X) :
    (S.windowCrossMeasure A B z).mass ≤ 2 := by
  rw [System.windowCrossMeasure,mass_weightedAtoms,Fintype.card_coe]
  have hc : (S.windowCrossings A B).card ≤ 2*(a*n)^2 := by
    calc
      _ ≤ S.drawing.crossings.card := Finset.card_le_card (S.windowCrossings_sub A B)
      _ ≤ 2*a^2*S.vertices.card^2 := S.crossing_cap hP.1 (Generic.x_injective hP)
          (S.drawing.noMultiple_of_generic hP)
      _ ≤ 2*a^2*n^2 := by gcongr; exact S.vertices.card_le_univ.trans (by simp)
      _ = 2*(a*n)^2 := by ring
  have hM : (((a*n : ℕ) : ℝ≥0)^2) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne n)))
  calc
    _ ≤ (((a*n : ℕ) : ℝ≥0)^2)⁻¹ * (2*((a*n : ℕ) : ℝ≥0)^2) := by
      gcongr
      exact_mod_cast hc
    _ = 2 := by rw [mul_left_comm,inv_mul_cancel₀ hM,mul_one]

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Configuration.points_mass (F : Configuration) : F.points.mass=1 := by
  rw [Configuration.points,mass_weightedAtoms,Fintype.card_fin]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne F.n))
lemma Configuration.vertices_mass_le (F : Configuration) (J : Window) : (F.vertices J).mass ≤ 1 :=
  (F.system.timeWindow J).vertexMeasure_mass_le _
lemma Configuration.edgeTime_mass (F : Configuration) : F.edgeTime.mass=1 := F.system.labelTimeMeasure_mass _
lemma Configuration.crossings_mass_le (F : Configuration) (A B : Window) : (F.crossings A B).mass ≤ 2 :=
  F.system.windowCrossMeasure_mass_le F.generic A B _
lemma Configuration.timeRestrict_mass_le (F : Configuration) (J : Window) : (F.timeRestrict J).mass ≤ 1 := by
  rw [← F.edgeTime_mass]
  apply ENNReal.coe_le_coe.mp
  simp only [FiniteMeasure.ennreal_mass]
  change (F.edgeTime : Measure (Labels×I)).restrict (Prod.snd ⁻¹' carrier J) univ ≤
    (F.edgeTime : Measure (Labels×I)) univ
  exact Measure.restrict_le_self _

end PlanarHalving.RankLimits

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

lemma Configuration.measures_mass_le (F : Configuration) (i : MeasureIndex) :
    (F.measures i).mass ≤ 2 := by
  cases i with
  | point => exact F.points_mass.le.trans (by norm_num)
  | vertices J => exact (F.vertices_mass_le J).trans (by norm_num)
  | time => exact F.edgeTime_mass.le.trans (by norm_num)
  | restrict J => exact (F.timeRestrict_mass_le J).trans (by norm_num)
  | cross A B => exact F.crossings_mass_le A B

theorem subsequence (F : ℕ → Configuration) :
    ∃ (φ : ℕ → ℕ) (L : Data), StrictMono φ ∧ Converges (F ∘ φ) L := by
  obtain ⟨φ,f,hφ,hf⟩ := finiteMeasure_subsequence_dependent
    (fun n => (F n).measures) (fun _ => 2) (fun n i => (F n).measures_mass_le i)
  exact ⟨φ,Data.ofFamily f,hφ,⟨hf .point,fun J => hf (.vertices J),hf .time,
    fun J => hf (.restrict J),fun A B => hf (.cross A B)⟩⟩

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches Filter
open scoped Topology

lemma Configuration.normalization_coefficient (F : Configuration) {c : ℝ} (hc : 0<c)
    (hnear : c*(F.n : ℝ)^4≤(F.R : ℝ)^3*(F.a : ℝ)^4) :
    4608*(F.a : ℝ)^2*(F.n : ℝ)^4/((F.R : ℝ)*(F.a : ℝ)^2)^3≤4608/c := by
  have ha : (0:ℝ)<F.a := Nat.cast_pos.mpr F.a_pos
  have hR : (0:ℝ)<F.R := Nat.cast_pos.mpr F.R_pos
  apply (div_le_div_iff₀ (pow_pos (mul_pos hR (pow_pos ha _)) _) hc).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnear (by positivity : (0:ℝ)≤4608*(F.a : ℝ)^2)]

lemma Configuration.short_ratio_cube (F : Configuration) {c : ℝ} (hc : 0<c)
    (hnear : c*(F.n : ℝ)^4≤(F.R : ℝ)^3*(F.a : ℝ)^4) :
    ((F.n : ℝ)/((F.R : ℝ)*(F.a : ℝ)))^3≤1/(c*((F.n : ℝ)/(F.a : ℝ))) := by
  have ha : (0:ℝ)<F.a := Nat.cast_pos.mpr F.a_pos
  have hR : (0:ℝ)<F.R := Nat.cast_pos.mpr F.R_pos
  have hn : (0:ℝ)<F.n := Nat.cast_pos.mpr F.n_pos
  rw [div_pow]
  apply (div_le_div_iff₀ (pow_pos (mul_pos hR ha) _) (mul_pos hc (div_pos hn ha))).mpr
  apply (mul_le_mul_iff_left₀ ha).mp
  field_simp
  nlinarith [hnear]

lemma short_ratio_tendsto_zero {F : ℕ → Configuration} {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n : ℝ)^4≤((F n).R : ℝ)^3*((F n).a : ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n : ℝ)/(F n).a) atTop atTop) :
    Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => 1/(c*(((F n).n : ℝ)/(F n).a))) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp (hq.const_mul_atTop hc)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hi (ε^3) (pow_pos hε _)
  refine ⟨N,fun n hn => ?_⟩
  have hb := (F n).short_ratio_cube hc (hnear n)
  have hp : (0:ℝ)≤((F n).n : ℝ)/((F n).R*(F n).a) := by positivity
  have hv := hN n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)] at hv
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hp]
  exact (pow_lt_pow_iff_left₀ hp hε.le (by omega : (3:ℕ)≠0)).mp (hb.trans_lt hv)

lemma sparse_error_tendsto_zero {F : ℕ → Configuration} {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n : ℝ)^4≤((F n).R : ℝ)^3*((F n).a : ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n : ℝ)/(F n).a) atTop atTop) :
    Tendsto (fun n => 13824*((F n).n : ℝ)^3/((F n).R*(F n).a^2)^3) atTop (𝓝 0) := by
  have hsmall := (short_ratio_tendsto_zero hc hnear hq).pow 3 |>.const_mul 13824
  simp only [zero_pow (by omega : (3:ℕ)≠0),mul_zero] at hsmall
  apply squeeze_zero (fun n => by positivity) (fun n => ?_) hsmall
  have ha : (1:ℝ)≤(F n).a := by exact_mod_cast (F n).a_pos
  have hR : (0:ℝ)<(F n).R := Nat.cast_pos.mpr (F n).R_pos
  rw [div_pow,mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr
  nlinarith

lemma normalization_sizes_atTop {F : ℕ → Configuration} {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n : ℝ)^4≤((F n).R : ℝ)^3*((F n).a : ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n : ℝ)/(F n).a) atTop atTop) :
    Tendsto (fun n => (F n).n) atTop atTop ∧
    Tendsto (fun n => (F n).a*(F n).n) atTop atTop ∧
    Tendsto (fun n => (F n).R) atTop atTop := by
  have hn : Tendsto (fun n => ((F n).n : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) hq
    exact div_le_self (by positivity) (by exact_mod_cast (F n).a_pos)
  have hn' : Tendsto (fun n => (F n).n) atTop atTop := tendsto_natCast_atTop_iff.mp hn
  refine ⟨hn',tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left _ (F n).a_pos) hn',?_⟩
  apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp
  apply tendsto_atTop_mono' atTop ?_ hq
  have hs := (short_ratio_tendsto_zero hc hnear hq).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hs] with n hn
  have ha : (0:ℝ)<(F n).a := Nat.cast_pos.mpr (F n).a_pos
  have hR : (0:ℝ)<(F n).R := Nat.cast_pos.mpr (F n).R_pos
  apply (div_le_iff₀ ha).mpr
  have := (div_lt_iff₀ (mul_pos hR ha)).mp hn
  linarith

end PlanarHalving.RankLimits

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

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Packing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Filter
open scoped Topology

lemma normalized_sequence_impossible (F : ℕ → Configuration)
    (emb : ∀ n, (F n).SweepEmbedding) {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n:ℝ)^4≤((F n).R:ℝ)^3*((F n).a:ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n:ℝ)/(F n).a) atTop atTop) : False := by
  obtain ⟨φ,L,hφ,hF⟩ := subsequence F
  have hnear' : ∀ n, c*((F (φ n)).n:ℝ)^4≤((F (φ n)).R:ℝ)^3*((F (φ n)).a:ℝ)^4 :=
    fun n => hnear (φ n)
  have hq' := hq.comp hφ.tendsto_atTop
  have hs := normalization_sizes_atTop hc hnear' hq'
  exact hF.impossible (fun n => emb (φ n)) hs.2.2 hs.2.1 (by positivity : 0≤4608/c)
    (fun n => (F (φ n)).normalization_coefficient hc (hnear' n))
    (sparse_error_tendsto_zero hc hnear' hq') (short_ratio_tendsto_zero hc hnear' hq')

theorem uniform_batch_saving {c : ℝ} (hc : 0<c) :
    ∃ Q : ℝ, 0<Q ∧ ∀ F : Configuration, F.SweepEmbedding → Q≤(F.n:ℝ)/F.a →
      (F.R:ℝ)^3*(F.a:ℝ)^4≤c*(F.n:ℝ)^4 := by
  by_contra h
  push Not at h
  have hex (m : ℕ) : ∃ F : Configuration, Nonempty F.SweepEmbedding ∧
      (m:ℝ)+1≤(F.n:ℝ)/F.a ∧ c*(F.n:ℝ)^4≤(F.R:ℝ)^3*(F.a:ℝ)^4 := by
    obtain ⟨F,emb,hq,hnear⟩ := h ((m:ℝ)+1) (by positivity)
    exact ⟨F,⟨emb⟩,hq,hnear.le⟩
  choose F he hq hn using hex
  have hlim : Tendsto (fun m => ((F m).n:ℝ)/(F m).a) atTop atTop := by
    apply tendsto_atTop_mono hq
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact normalized_sequence_impossible F (fun n => (he n).some) hc hn hlim

end PlanarHalving.RankLimits
namespace PlanarHalving.Sweep
open Set RankLimits

lemma distance_saving {c : ℝ} (hc : 0<c) :
    ∃ Q : ℝ, 0<Q ∧ ∀ {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n),
      ∀ {d : ℕ}, 0<d → Q≤(n:ℝ)/d →
      ∀ C : Finset (Fin ((traversal (criticalSlopes P)).size+1) × Fin ((traversal (criticalSlopes P)).size+1)),
      StepDisjoint C → (∀ p∈C, p.1≤p.2) →
      (∀ p∈C, d≤(states P hP hk).distance p.1 p.2) →
      (C.card:ℝ)^3*(d:ℝ)^4≤16*c*(n:ℝ)^4 := by
  obtain ⟨Q,hQ,hbatch⟩ := uniform_batch_saving hc
  refine ⟨Q,hQ,?_⟩
  intro n k P hP hk d hd hq C hC hord hdist
  let S := states P hP hk
  let a := (d+1)/2
  have ha : 0<a := by dsimp [a];omega
  have had : a≤d := by dsimp [a];omega
  let R := (S.greedy 0 a ha).count
  have hcount : C.card≤R := S.greedy_packing hd C hC hord hdist
  by_cases hR : 0<R
  · have hn : 0<n := by
      by_contra hn
      have hn0 : n=0 := by omega
      have hq0 : (n:ℝ)/d=0 := by simp [hn0]
      rw [hq0] at hq
      exact (not_le_of_gt hQ) hq
    let F := greedyConfiguration hP hk a ha hn hR
    have hbd : (R:ℝ)^3*(a:ℝ)^4≤c*(n:ℝ)^4 :=
      hbatch F (greedyConfiguration_embedding hP hk a ha hn hR)
        (hq.trans (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast ha) (by exact_mod_cast had)))
    have hda : (d:ℝ)≤2*(a:ℝ) := by exact_mod_cast (show d≤2*a by dsimp [a];omega)
    calc
      _ ≤ (R:ℝ)^3*(2*(a:ℝ))^4 := by gcongr
      _ = 16*((R:ℝ)^3*(a:ℝ)^4) := by ring
      _ ≤ 16*(c*(n:ℝ)^4) := mul_le_mul_of_nonneg_left hbd (by norm_num)
      _ = _ := by ring
  · have hz : C.card=0 := by omega
    simp only [hz,Nat.cast_zero,zero_pow (by omega : (3:ℕ)≠0),zero_mul]
    positivity

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set

theorem activity_saving_cubic {δ : ℝ} (hδ : 0<δ) :
    ∃ Q : ℝ, 0<Q ∧ ∀ {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n),
      ∀ {b : ℕ}, 0<b → Q≤(n:ℝ)/b →
      ∀ C : Finset (Fin ((traversal (criticalSlopes P)).size+1) × Fin ((traversal (criticalSlopes P)).size+1)),
      StepDisjoint C → (horder : ∀ p∈C, p.1≤p.2) →
      (∀ p, ∀ hp : p∈C, b≤((states P hP hk).intervalActivity p.1 p.2 (horder p hp)).card) →
      (C.card:ℝ)^3*(b:ℝ)^4≤524288*δ*(n:ℝ)^4 := by
  obtain ⟨Q,hQ,hdist⟩ := distance_saving hδ
  refine ⟨Q,hQ,?_⟩
  intro n k P hP hk b hb hq C hC horder hactivity
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
        (D.card : ℝ)^3*(c : ℝ)^4≤16*δ*(n : ℝ)^4 := by
      by_cases hne : D.Nonempty
      · obtain ⟨p,hp⟩ := hne
        obtain ⟨hr,_⟩ := hd p hp
        apply hdist P hP hr hc (hq.trans (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hc) (by exact_mod_cast (show c≤b by dsimp [c];omega)))) D
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
    have hcub : (C.card : ℝ)^3*(c : ℝ)^4≤128*δ*(n : ℝ)^4 := by nlinarith [hAb,hBb]
    calc
      _ ≤ (C.card : ℝ)^3*(8*(c : ℝ))^4 := by gcongr
      _ = 4096*((C.card : ℝ)^3*(c : ℝ)^4) := by ring
      _ ≤ 4096*(128*δ*(n : ℝ)^4) := mul_le_mul_of_nonneg_left hcub (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hδ.le (sq_nonneg ((n : ℝ)^2))]
  · have hd := hdist P hP hk (by omega : 0<1) (by simpa using hq.trans (div_le_self (by positivity) (by exact_mod_cast hb))) C hC horder
      (fun p hp => S.intervalActivity_pos_distance (horder p hp) (lt_of_lt_of_le hb (hactivity p hp)))
    norm_num at hd
    have hbLe : (b : ℝ)≤3 := by exact_mod_cast (by omega : b≤3)
    calc
      _ ≤ (C.card : ℝ)^3*3^4 := by gcongr
      _ ≤ 16*δ*(n : ℝ)^4*3^4 := mul_le_mul_of_nonneg_right hd (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hδ.le (sq_nonneg ((n : ℝ)^2))]

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Greedy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving
open Set

lemma Generic.comp_strictMono {n m : ℕ} {P : Fin n → Point} (hP : Generic P)
    {f : Fin m → Fin n} (hf : StrictMono f) : Generic (P∘f) := by
  refine ⟨⟨hP.1.1.comp hf.injective,?_⟩,?_,?_,?_⟩
  · intro i j l hij hjl hil
    exact hP.1.2 _ _ _ (hf.injective.ne hij) (hf.injective.ne hjl) (hf.injective.ne hil)
  · intro i j hij
    exact hP.2.1 _ _ (hf.injective.ne hij)
  · intro i j a b hij hab he
    obtain ⟨hi,hj⟩ := hP.2.2.1 _ _ _ _ (hf hij) (hf hab) he
    exact ⟨hf.injective hi,hf.injective hj⟩
  · intro i j a b c d hij hab hcd hne hci hca z hzij hzab hzcd
    have hinj : Function.Injective (Prod.map f f) := hf.injective.prodMap hf.injective
    exact hP.2.2.2 _ _ _ _ _ _ (hf hij) (hf hab) (hf hcd)
      (hinj.ne hne) (hinj.ne hci) (hinj.ne hca) z hzij hzab hzcd

end PlanarHalving
namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

lemma States.ActivityGreedy.intervals_card (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (Q : S.ActivityGreedy s b) : (Q.intervals S).card=Q.count := by
  classical
  rw [States.ActivityGreedy.intervals,Finset.card_image_of_injective,Finset.card_univ,Fintype.card_fin]
  intro i j he
  exact Fin.castSucc_inj.mp (Q.increasing.injective (congrArg Prod.fst he))

lemma States.ActivityGreedy.intervals_data (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (Q : S.ActivityGreedy s b) : StepDisjoint (Q.intervals S) ∧
      ∀ p ∈ Q.intervals S, p.1 ≤ p.2 ∧ b ≤ S.activitySize p.1 p.2 := by
  constructor
  · intro p hp q hq hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    have hij : i≠j := by intro h;subst j;exact hne rfl
    rcases lt_or_gt_of_ne hij with h | h
    · have he : Q.index i.succ ≤ Q.index j.castSucc := Q.increasing.monotone (by change i.val+1 ≤ j.val;omega)
      exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hi.2.trans he) hj.1)
    · have he : Q.index j.succ ≤ Q.index i.castSucc := Q.increasing.monotone (by change j.val+1 ≤ i.val;omega)
      exact Set.disjoint_left.mpr (fun _ hi hj => not_lt_of_ge (hj.2.trans he) hi.1)
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨Q.increasing.monotone (Fin.castSucc_le_succ i),Q.lower i⟩

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

lemma continuous_lt_iff_of_no_eq {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {s t : ℝ} (hst : s≤t) (hne : ∀ u∈Icc s t, f u≠g u) : f s<g s ↔ f t<g t := by
  constructor
  · intro hs
    by_contra ht
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc hst (hf.sub hg).continuousOn
      (show (0:ℝ)∈Icc (f s-g s) (f t-g t) from ⟨sub_nonpos.mpr hs.le,sub_nonneg.mpr (le_of_not_gt ht)⟩)
    exact hne u hu (sub_eq_zero.mp he)
  · intro ht
    by_contra hs
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hst (hf.sub hg).continuousOn
      (show (0:ℝ)∈Icc (f t-g t) (f s-g s) from ⟨sub_nonpos.mpr ht.le,sub_nonneg.mpr (le_of_not_gt hs)⟩)
    exact hne u hu (sub_eq_zero.mp he)

lemma projection_eq_iff_slope {p q : Point} (hx : p.1≠q.1) {s : ℝ} :
    projection s p=projection s q ↔ s=slope p q := by
  rw [slope,eq_div_iff (sub_ne_zero.mpr hx.symm)]
  unfold projection
  constructor <;> intro h <;> linarith

lemma tied_projection (p q : Point) (hx : p.1≠q.1) :
    projection (slope p q) p=projection (slope p q) q :=
  (projection_eq_iff_slope hx).mpr rfl

variable {n : ℕ} {P : Fin n → Point}

lemma Traversal.cut_bounds (T : Traversal (criticalSlopes P)) (i : Fin T.size) :
    T.sample i.castSucc<T.cut i.succ.castSucc ∧ T.cut i.succ.castSucc<T.sample i.succ := by
  exact ⟨by simpa only [Fin.castSucc_succ] using (T.sample_bounds i.castSucc).2,
    (T.sample_bounds i.succ).1⟩

lemma Traversal.projection_ne_between (T : Traversal (criticalSlopes P)) (hP : Generic P)
    (i : Fin T.size) {a b : Fin n}
    (hne : projection (T.cut i.succ.castSucc) (P a)≠projection (T.cut i.succ.castSucc) (P b)) :
    ∀ u∈Icc (T.sample i.castSucc) (T.sample i.succ), projection u (P a)≠projection u (P b) := by
  have hab : a≠b := fun h => hne (by rw [h])
  intro u hu he
  have hs := (projection_eq_iff_slope (hP.2.1 a b hab)).mp he
  have hmem : u∈criticalSlopes P := hs ▸ mem_criticalSlopes P hab
  have hl : T.sample i.castSucc<u := lt_of_le_of_ne hu.1 (fun h => T.sample_not_mem _ (h ▸ hmem))
  have hr : u<T.sample i.succ := lt_of_le_of_ne hu.2 (fun h => T.sample_not_mem _ (h ▸ hmem))
  have hc := T.unique_critical i hmem hl hr
  exact hne (hc ▸ he)

lemma Traversal.comparison_cut (T : Traversal (criticalSlopes P)) (hP : Generic P)
    (i : Fin T.size) {a b : Fin n}
    (hne : projection (T.cut i.succ.castSucc) (P a)≠projection (T.cut i.succ.castSucc) (P b)) :
    (projection (T.sample i.castSucc) (P a)<projection (T.sample i.castSucc) (P b) ↔
      projection (T.cut i.succ.castSucc) (P a)<projection (T.cut i.succ.castSucc) (P b)) ∧
    (projection (T.sample i.succ) (P a)<projection (T.sample i.succ) (P b) ↔
      projection (T.cut i.succ.castSucc) (P a)<projection (T.cut i.succ.castSucc) (P b)) := by
  have ha : Continuous (fun s => projection s (P a)) := by unfold projection;fun_prop
  have hb : Continuous (fun s => projection s (P b)) := by unfold projection;fun_prop
  have hc := T.cut_bounds i
  have hn := T.projection_ne_between hP i hne
  exact ⟨continuous_lt_iff_of_no_eq ha hb hc.1.le
    (fun u hu => hn u ⟨hu.1,hu.2.trans hc.2.le⟩),
    (continuous_lt_iff_of_no_eq ha hb hc.2.le
      (fun u hu => hn u ⟨hc.1.le.trans hu.1,hu.2⟩)).symm⟩

lemma projection_ne_at_pair (hP : GeneralPosition P) {a b l : Fin n}
    (hab : a≠b) (hla : l≠a) (hlb : l≠b) (hxa : (P a).1≠(P b).1) :
    projection (slope (P a) (P b)) (P l)≠projection (slope (P a) (P b)) (P a) := by
  intro h
  apply hP.2 a b l hab hlb.symm hla.symm
  have he := (div_mul_cancel₀ ((P b).2-(P a).2) (sub_ne_zero.mpr hxa.symm))
  change slope (P a) (P b)*((P b).1-(P a).1)=(P b).2-(P a).2 at he
  unfold projection at h
  have hl : (P l).2-(P a).2=slope (P a) (P b)*((P l).1-(P a).1) := by linarith
  unfold orient
  rw [hl,← he]
  ring

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

lemma Traversal.sample_refines {n : ℕ} {P : Fin n → Point}
    (T : Traversal (criticalSlopes P)) (hP : Generic P) (i : Fin T.size) :
    Refines P (T.cut i.succ.castSucc) (T.sample i.castSucc) ∧
    Refines P (T.cut i.succ.castSucc) (T.sample i.succ) := by
  constructor <;> intro a b hab
  · exact (T.comparison_cut hP i (ne_of_lt hab)).1.mpr hab
  · exact (T.comparison_cut hP i (ne_of_lt hab)).2.mpr hab

lemma mem_belowSet {n : ℕ} (P : Fin n → Point) (a b l : Fin n) :
    l∈belowSet P a b ↔ projection (slope (P a) (P b)) (P l)<projection (slope (P a) (P b)) (P a) := by
  classical
  simp only [belowSet,Finset.mem_filter,Finset.mem_univ,true_and]

lemma card_belowSet {n : ℕ} (P : Fin n → Point) (a b : Fin n) :
    (belowSet P a b).card=belowCount P a b := rfl

lemma belowSet_eq_erase {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {s : ℝ} {M : Finset (Fin n)} (hM : Separates P s M) {a b : Fin n}
    (ha : a∈M) (hb : b∉M) (hx : (P a).1≠(P b).1)
    (hR : Refines P (slope (P a) (P b)) s) : belowSet P a b=M.erase a := by
  classical
  have hab : a≠b := fun h => hb (h ▸ ha)
  have ht := tied_projection (P a) (P b) hx
  ext l
  rw [mem_belowSet,Finset.mem_erase]
  constructor
  · intro hl
    have hla : l≠a := by intro he;subst l;exact lt_irrefl _ hl
    refine ⟨hla,?_⟩
    by_contra hn
    exact not_lt_of_gt (hM a ha l hn) (hR l a hl)
  · rintro ⟨hla,hl⟩
    have hlb : l≠b := fun he => hb (he ▸ hl)
    have hne := projection_ne_at_pair hP hab hla hlb hx
    by_contra hn
    have hgt := lt_of_le_of_ne (le_of_not_gt hn) hne.symm
    rw [ht] at hgt
    exact not_lt_of_gt (hM l hl b hb) (hR b l hgt)

lemma below_insert_separates {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {s : ℝ} {a b : Fin n} (hab : a≠b) (hx : (P a).1≠(P b).1)
    (hR : Refines P (slope (P a) (P b)) s)
    (hs : projection s (P a)<projection s (P b)) :
    Separates P s (insert a (belowSet P a b)) := by
  classical
  intro l hl m hm
  have hma : m≠a := by intro he;subst m;exact hm (Finset.mem_insert_self _ _)
  have hmB : m∉belowSet P a b := fun hh => hm (Finset.mem_insert_of_mem hh)
  have hcm : projection (slope (P a) (P b)) (P a)≤projection (slope (P a) (P b)) (P m) :=
    le_of_not_gt (fun hh => hmB ((mem_belowSet P a b m).mpr hh))
  rcases Finset.mem_insert.mp hl with he | hl
  · subst l
    by_cases hmb : m=b
    · simpa only [hmb] using hs
    · exact hR a m (lt_of_le_of_ne hcm (projection_ne_at_pair hP hab hma hmb hx).symm)
  · exact hR l m (((mem_belowSet P a b l).mp hl).trans_le hcm)

lemma projection_order_at_slope {p q : Point} (hx : p.1<q.1) {s t : ℝ}
    (hs : s<slope p q) (ht : slope p q<t) :
    projection s p<projection s q ∧ projection t q<projection t p := by
  have hdx : 0<q.1-p.1 := sub_pos.mpr hx
  have hs' := (lt_div_iff₀ hdx).mp hs
  have ht' := (div_lt_iff₀ hdx).mp ht
  unfold projection
  constructor <;> nlinarith

lemma belowSet_symm {n : ℕ} {P : Fin n → Point} {a b : Fin n} (hx : (P a).1≠(P b).1) :
    belowSet P b a=belowSet P a b := by
  classical
  ext l
  simp only [mem_belowSet,slope_symm (P b) (P a),tied_projection (P a) (P b) hx]

lemma belowCount_symm {n : ℕ} {P : Fin n → Point} {a b : Fin n} (hx : (P a).1≠(P b).1) :
    belowCount P b a=belowCount P a b := congrArg Finset.card (belowSet_symm hx)

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep
open Set

lemma state_eq_insert_below {n k : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {s : ℝ} {M : Finset (Fin n)} (hM : Separates P s M) (hcard : M.card=k)
    {a b : Fin n} (hab : a≠b) (hx : (P a).1≠(P b).1)
    (hR : Refines P (slope (P a) (P b)) s)
    (hs : projection s (P a)<projection s (P b)) (hk : 0<k)
    (hbelow : belowCount P a b=k-1) : M=insert a (belowSet P a b) := by
  classical
  apply states_unique hM (below_insert_separates hP hab hx hR hs)
  have hna : a∉belowSet P a b := by simp only [mem_belowSet,lt_self_iff_false,not_false_eq_true]
  rw [hcard,Finset.card_insert_of_notMem hna,card_belowSet,hbelow]
  omega

lemma states_change_of_pair {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    (i : Fin (traversal (criticalSlopes P)).size) {a b : Fin n} (hab : a≠b)
    (hc : (traversal (criticalSlopes P)).cut i.succ.castSucc=slope (P a) (P b))
    (hkpos : 0<k) (hbelow : belowCount P a b=k-1) :
    (states P hP hk).marks i.castSucc≠(states P hP hk).marks i.succ := by
  classical
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  have aux (a b : Fin n) (hx : (P a).1<(P b).1)
      (hc : T.cut i.succ.castSucc=slope (P a) (P b))
      (hb : belowCount P a b=k-1) : S.marks i.castSucc≠S.marks i.succ := by
    have hbounds := T.cut_bounds i
    rw [hc] at hbounds
    have ho := projection_order_at_slope hx hbounds.1 hbounds.2
    have hR := (T.sample_refines hP i).1
    rw [hc] at hR
    have hab' : a≠b := fun he => ne_of_lt hx (congrArg (fun x => (P x).1) he)
    have he := state_eq_insert_below hP.1 (S.separates i.castSucc) (S.card_marks i.castSucc)
      hab' hx.ne hR ho.1 hkpos hb
    intro hsame
    have ha : a∈S.marks i.succ := by rw [← hsame,he];exact Finset.mem_insert_self _ _
    have hb' : b∉S.marks i.succ := by
      rw [← hsame,he,Finset.mem_insert]
      simp only [mem_belowSet,tied_projection (P a) (P b) hx.ne,lt_self_iff_false,or_false]
      exact hab'.symm
    exact not_lt_of_gt ho.2 (S.separates i.succ a ha b hb')
  rcases lt_or_gt_of_ne (hP.2.1 a b hab) with hx | hx
  · exact aux a b hx hc hbelow
  · apply aux b a hx
    · simpa only [slope_symm (P b) (P a)] using hc
    · simpa only [belowCount_symm (hP.2.1 a b hab)] using hbelow

lemma mem_switchPairs {n : ℕ} (P : Fin n → Point) (k : ℕ) (p : Fin n × Fin n) :
    p∈switchPairs P k ↔ p.1<p.2 ∧ 0<k ∧ k<n ∧ belowCount P p.1 p.2=k-1 := by
  classical
  simp only [switchPairs,Finset.mem_filter,Finset.mem_univ,true_and]

lemma States.mem_changeSteps {n T k : ℕ} {P : Fin n → Point} (S : @States n T k P) (i : Fin T) :
    i∈S.changeSteps ↔ S.marks i.castSucc≠S.marks i.succ := by
  classical
  simp only [States.changeSteps,Finset.mem_filter,Finset.mem_univ,true_and]

lemma switchCount_le_changes {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n) :
    switchCount P k≤(states P hP hk).changeSteps.card := by
  classical
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  have hex (p : ↥(switchPairs P k)) : ∃ i : Fin T.size, i∈S.changeSteps ∧
      T.cut i.succ.castSucc=slope (P p.val.1) (P p.val.2) := by
    have hp := (mem_switchPairs P k p.val).mp p.property
    obtain ⟨i,hi⟩ := (T.critical _).mp (mem_criticalSlopes P hp.1.ne)
    exact ⟨i,(S.mem_changeSteps i).mpr (states_change_of_pair hP hk i hp.1.ne hi hp.2.1 hp.2.2.2),hi⟩
  choose f hf hs using hex
  let g : ↥(switchPairs P k) → ↥S.changeSteps := fun p => ⟨f p,hf p⟩
  have hg : Function.Injective g := by
    intro p q h
    have he : f p=f q := congrArg Subtype.val h
    have heq := (hs p).symm.trans ((congrArg (fun j => T.cut j.succ.castSucc) he).trans (hs q))
    have hp := (mem_switchPairs P k p.val).mp p.property
    have hq := (mem_switchPairs P k q.val).mp q.property
    obtain ⟨h1,h2⟩ := hP.2.2.1 _ _ _ _ hp.1 hq.1 heq
    exact Subtype.ext (Prod.ext h1 h2)
  change (switchPairs P k).card≤S.changeSteps.card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

lemma local_change_event {n k : ℕ} {P : Fin n → Point} (hP : Generic P)
    {s t c : ℝ} {M N : Finset (Fin n)}
    (hM : Separates P s M) (hN : Separates P t N) (hcardM : M.card=k) (hcardN : N.card=k)
    (hRs : Refines P c s) (hRt : Refines P c t) (hne : M≠N) :
    ∃ p∈switchPairs P k, slope (P p.1) (P p.2)=c := by
  classical
  have hneM : (M\N).Nonempty := by
    by_contra hh
    have hsub : M⊆N := Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp hh)
    exact hne (Finset.eq_of_subset_of_card_le hsub (hcardN.trans hcardM.symm).le)
  obtain ⟨a,ha⟩ := hneM
  have hneN : (N\M).Nonempty := by
    rw [← Finset.card_pos,← Finset.card_sdiff_comm (hcardM.trans hcardN.symm)]
    exact Finset.card_pos.mpr ⟨a,ha⟩
  obtain ⟨b,hb⟩ := hneN
  have haM := (Finset.mem_sdiff.mp ha).1
  have haN := (Finset.mem_sdiff.mp ha).2
  have hbN := (Finset.mem_sdiff.mp hb).1
  have hbM := (Finset.mem_sdiff.mp hb).2
  have hab : a≠b := fun he => hbM (he ▸ haM)
  have hc : projection c (P a)=projection c (P b) := by
    apply le_antisymm
    · by_contra h
      exact not_lt_of_gt (hM a haM b hbM) (hRs b a (lt_of_not_ge h))
    · by_contra h
      exact not_lt_of_gt (hN b hbN a haN) (hRt a b (lt_of_not_ge h))
  have hsc : c=slope (P a) (P b) := (projection_eq_iff_slope (hP.2.1 a b hab)).mp hc
  have hbelow : belowCount P a b=k-1 := by
    rw [← card_belowSet,belowSet_eq_erase hP.1 hM haM hbM (hP.2.1 a b hab) (hsc ▸ hRs),
      Finset.card_erase_of_mem haM,hcardM]
  have hkpos : 0<k := hcardM ▸ Finset.card_pos.mpr ⟨a,haM⟩
  have hkn : k<n := by
    have he : M⊂Finset.univ := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,by intro h;apply hbM;rw [h];exact Finset.mem_univ _⟩
    simpa only [hcardM,Finset.card_univ,Fintype.card_fin] using Finset.card_lt_card he
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨(a,b),(mem_switchPairs P k _).mpr ⟨hab,hkpos,hkn,hbelow⟩,hsc.symm⟩
  · exact ⟨(b,a),(mem_switchPairs P k _).mpr ⟨hba,hkpos,hkn,by rw [belowCount_symm (hP.2.1 a b (ne_of_gt hba)),hbelow]⟩,
      (slope_symm (P b) (P a)).trans hsc.symm⟩

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set

lemma subsetIndex_strictMono {n : ℕ} (A : Finset (Fin n)) : StrictMono (subsetIndex A) :=
  fun _ _ h => (A.orderIsoOfFin rfl).strictMono h

lemma subsetIndex_mem {n : ℕ} (A : Finset (Fin n)) (i : Fin A.card) : subsetIndex A i∈A :=
  (A.orderIsoOfFin rfl i).property

lemma subsetIndex_surj {n : ℕ} (A : Finset (Fin n)) {x : Fin n} (hx : x∈A) :
    ∃ i, subsetIndex A i=x := by
  exact ⟨(A.orderIsoOfFin rfl).symm ⟨x,hx⟩,congrArg Subtype.val ((A.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩)⟩

lemma subsetPoints_generic {n : ℕ} {P : Fin n → Point} (hP : Generic P) (A : Finset (Fin n)) :
    Generic (subsetPoints P A) := hP.comp_strictMono (subsetIndex_strictMono A)

lemma mem_restrictMarks {n : ℕ} (A M : Finset (Fin n)) (i : Fin A.card) :
    i∈restrictMarks A M ↔ subsetIndex A i∈M := by
  classical
  simp only [restrictMarks,Finset.mem_filter,Finset.mem_univ,true_and]

lemma card_restrictMarks {n : ℕ} (A M : Finset (Fin n)) :
    (restrictMarks A M).card=(M∩A).card := by
  classical
  have he : (restrictMarks A M).image (subsetIndex A)=M∩A := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨(mem_restrictMarks A M i).mp hi,subsetIndex_mem A i⟩
    · intro hx
      obtain ⟨i,rfl⟩ := subsetIndex_surj A (Finset.mem_inter.mp hx).2
      exact Finset.mem_image.mpr ⟨i,(mem_restrictMarks A M i).mpr (Finset.mem_inter.mp hx).1,rfl⟩
  rw [← he,Finset.card_image_of_injective _ (subsetIndex_strictMono A).injective]

lemma restrictMarks_separates {n : ℕ} {P : Fin n → Point} {s : ℝ} {M : Finset (Fin n)}
    (hM : Separates P s M) (A : Finset (Fin n)) :
    Separates (subsetPoints P A) s (restrictMarks A M) := by
  intro i hi j hj
  exact hM _ ((mem_restrictMarks A M i).mp hi) _ (fun h => hj ((mem_restrictMarks A M j).mpr h))

lemma Refines.subset {n : ℕ} {P : Fin n → Point} {c s : ℝ} (hR : Refines P c s)
    (A : Finset (Fin n)) : Refines (subsetPoints P A) c s := fun _ _ h => hR _ _ h

variable {n T k : ℕ} {P : Fin n → Point}

lemma States.restrict_activity_card (S : @States n T k P)
    {u v : Fin (T+1)} (huv : u ≤ v) {i : Fin (T+1)} (hui : u ≤ i) (hiv : i ≤ v) :
    (restrictMarks (S.intervalActivity u v huv) (S.marks i)).card=
      ((S.marks u)∩S.intervalActivity u v huv).card := by
  classical
  let A := S.intervalActivity u v huv
  have he : S.marks i\A=S.marks u\A := by
    ext x
    simp only [Finset.mem_sdiff]
    by_cases hx : x∈A
    · simp [hx]
    · rw [S.outside_activity_constant huv hx hui hiv]
  have h1 := Finset.card_inter_add_card_sdiff (S.marks i) A
  have h2 := Finset.card_inter_add_card_sdiff (S.marks u) A
  rw [S.card_marks] at h1 h2
  rw [he] at h1
  rw [card_restrictMarks]
  change (S.marks i∩A).card=(S.marks u∩A).card
  omega

lemma States.restrict_activity_change (S : @States n T k P)
    {u v : Fin (T+1)} (huv : u ≤ v) {i j : Fin (T+1)}
    (hui : u ≤ i) (hiv : i ≤ v) (huj : u ≤ j) (hjv : j ≤ v)
    (hne : S.marks i≠S.marks j) :
    restrictMarks (S.intervalActivity u v huv) (S.marks i)≠
      restrictMarks (S.intervalActivity u v huv) (S.marks j) := by
  classical
  intro he
  apply hne
  ext x
  by_cases hx : x∈S.intervalActivity u v huv
  · obtain ⟨a,rfl⟩ := subsetIndex_surj _ hx
    exact (mem_restrictMarks _ _ a).symm.trans ((congrArg (fun M => a∈M) he).to_iff.trans (mem_restrictMarks _ _ a))
  · exact (S.outside_activity_constant huv hx hui hiv).trans (S.outside_activity_constant huv hx huj hjv).symm

lemma States.mem_blockSteps (S : @States n T k P) (u v : Fin (T+1)) (i : Fin T) :
    i∈S.blockSteps u v ↔ i∈S.changeSteps ∧ u ≤ i.castSucc ∧ i.succ ≤ v := by
  classical
  simp only [States.blockSteps,Finset.mem_filter]

lemma card_le_of_injective_labels {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (f : α → γ) (g : β → γ)
    (hf : Set.InjOn f A) (hex : ∀ a∈A, ∃ b∈B, g b=f a) : A.card≤B.card := by
  classical
  choose h hh he using (fun a : ↥A => hex a a.property)
  let F : ↥A → ↥B := fun a => ⟨h a,hh a⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hh' : h a=h b := congrArg Subtype.val hab
    exact Subtype.ext (hf a.property b.property ((he a).symm.trans ((congrArg g hh').trans (he b))))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hF

lemma block_step_event {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    {u v : Fin ((traversal (criticalSlopes P)).size+1)} (huv : u ≤ v)
    {i : Fin (traversal (criticalSlopes P)).size} (hi : i∈(states P hP hk).blockSteps u v) :
    let A := (states P hP hk).intervalActivity u v huv
    let r := ((states P hP hk).marks u∩A).card
    ∃ p∈switchPairs (subsetPoints P A) r,
      slope (subsetPoints P A p.1) (subsetPoints P A p.2)=(traversal (criticalSlopes P)).cut i.succ.castSucc := by
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  let A := S.intervalActivity u v huv
  have hi' := (S.mem_blockSteps u v i).mp hi
  have hs := T.sample_refines hP i
  exact local_change_event (subsetPoints_generic hP A)
    (restrictMarks_separates (S.separates i.castSucc) A)
    (restrictMarks_separates (S.separates i.succ) A)
    (S.restrict_activity_card huv hi'.2.1 ((Fin.castSucc_le_succ _).trans hi'.2.2))
    (S.restrict_activity_card huv (hi'.2.1.trans (Fin.castSucc_le_succ _)) hi'.2.2)
    (hs.1.subset A) (hs.2.subset A)
    (S.restrict_activity_change huv hi'.2.1 ((Fin.castSucc_le_succ _).trans hi'.2.2)
      (hi'.2.1.trans (Fin.castSucc_le_succ _)) hi'.2.2 ((S.mem_changeSteps _).mp hi'.1))

lemma block_count_le {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    {u v : Fin ((traversal (criticalSlopes P)).size+1)} (huv : u ≤ v) :
    ∃ r : ℕ, r≤((states P hP hk).intervalActivity u v huv).card ∧
      ((states P hP hk).blockSteps u v).card≤
        switchCount (subsetPoints P ((states P hP hk).intervalActivity u v huv)) r := by
  classical
  let T := traversal (criticalSlopes P)
  let S := states P hP hk
  let A := S.intervalActivity u v huv
  let r := (S.marks u∩A).card
  refine ⟨r,(Finset.card_le_card (Finset.inter_subset_right)),?_⟩
  change (S.blockSteps u v).card≤(switchPairs (subsetPoints P A) r).card
  apply card_le_of_injective_labels _ _ (fun i => T.cut i.succ.castSucc)
    (fun p => slope (subsetPoints P A p.1) (subsetPoints P A p.2))
  · intro i _ j _ he
    exact Fin.succ_inj.mp (Fin.castSucc_inj.mp (T.increasing.injective he))
  · exact fun i hi => block_step_event hP hk huv hi

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep
open Set
variable {n T k : ℕ} {P : Fin n → Point}

lemma States.blockSteps_self (S : @States n T k P) (u : Fin (T+1)) : S.blockSteps u u=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h := (S.mem_blockSteps u u i).mp hi
  exact not_lt_of_ge (h.2.2.trans h.2.1) (Fin.castSucc_lt_succ (i:=i))

lemma States.blockSteps_all (S : @States n T k P) : S.blockSteps 0 (Fin.last T)=S.changeSteps := by
  classical
  ext i
  simp only [S.mem_blockSteps,Fin.zero_le,Fin.le_last,and_true]

lemma States.blockSteps_card_add (S : @States n T k P) {u v w : Fin (T+1)}
    (huv : u ≤ v) (hvw : v ≤ w) :
    (S.blockSteps u v).card+(S.blockSteps v w).card=(S.blockSteps u w).card := by
  classical
  have hdis : Disjoint (S.blockSteps u v) (S.blockSteps v w) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hi' := (S.mem_blockSteps u v i).mp hi
    have hj' := (S.mem_blockSteps v w i).mp hj
    exact not_lt_of_ge (hi'.2.2.trans hj'.2.1) (Fin.castSucc_lt_succ (i:=i))
  have he : S.blockSteps u v ∪ S.blockSteps v w=S.blockSteps u w := by
    ext i
    simp only [Finset.mem_union,S.mem_blockSteps]
    constructor
    · rintro (⟨hi,hu,hv⟩ | ⟨hi,hv,hw⟩)
      · exact ⟨hi,hu,hv.trans hvw⟩
      · exact ⟨hi,huv.trans hv,hw⟩
    · rintro ⟨hi,hu,hw⟩
      by_cases h : i.succ ≤ v
      · exact Or.inl ⟨hi,hu,h⟩
      · exact Or.inr ⟨hi,(by change v.val ≤ i.val;change ¬i.val+1 ≤ v.val at h;omega),hw⟩
  rw [← he,Finset.card_union_of_disjoint hdis]

lemma States.sum_blockSteps (S : @States n T k P) (m : ℕ)
    (f : Fin (m+1) → Fin (T+1)) (hf : Monotone f) :
    ∑ j : Fin m, (S.blockSteps (f j.castSucc) (f j.succ)).card=
      (S.blockSteps (f 0) (f (Fin.last m))).card := by
  induction m with
  | zero => simp [S.blockSteps_self]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hh := ih (fun j : Fin (m+1) => f j.castSucc) (fun _ _ h => hf (Fin.castSucc_le_castSucc_iff.mpr h))
    simp only [Fin.castSucc_succ] at hh
    rw [hh]
    exact S.blockSteps_card_add (hf (Fin.zero_le _)) (hf (Fin.castSucc_le_succ _))

lemma States.ActivityGreedy.fullIndex_mono (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : Monotone (G.fullIndex S) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun j => ?_) j
  · intro _
    simpa only [States.ActivityGreedy.fullIndex,Fin.snoc_last] using (Fin.le_last (G.fullIndex S i))
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hij
      exact False.elim (not_le_of_gt (Fin.castSucc_lt_last j) hij)
    · intro hij
      simpa only [States.ActivityGreedy.fullIndex,Fin.snoc_castSucc] using G.increasing.monotone (Fin.castSucc_le_castSucc_iff.mp hij)

lemma States.ActivityGreedy.fullIndex_first (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : G.fullIndex S 0=s := by
  simpa only [States.ActivityGreedy.fullIndex,←Fin.castSucc_zero,Fin.snoc_castSucc] using G.first

lemma States.ActivityGreedy.fullIndex_last (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) : G.fullIndex S (Fin.last (G.count+1))=Fin.last T := Fin.snoc_last _ _

lemma States.ActivityGreedy.fullIndex_activity (S : @States n T k P) {s : Fin (T+1)} {b : ℕ}
    (G : S.ActivityGreedy s b) (j : Fin (G.count+1)) :
    S.activitySize (G.fullIndex S j.castSucc) (G.fullIndex S j.succ)≤b+1 := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [States.ActivityGreedy.fullIndex,Fin.snoc_castSucc,Fin.succ_last,Fin.snoc_last] using G.tail.le.trans (Nat.le_succ b)
  · simpa only [States.ActivityGreedy.fullIndex,←Fin.castSucc_succ,Fin.snoc_castSucc] using G.upper i

lemma activity_decomposition {n k : ℕ} {P : Fin n → Point} (hP : Generic P) (hk : k≤n)
    {b : ℕ} (hb : 0<b) :
    ∃ (A : Fin (((states P hP hk).activityGreedy 0 b hb).count+1) → Finset (Fin n))
      (r : Fin (((states P hP hk).activityGreedy 0 b hb).count+1) → ℕ),
      (∀ j, (A j).card≤b+1) ∧ (∀ j, r j≤(A j).card) ∧
      switchCount P k ≤ ∑ j, switchCount (subsetPoints P (A j)) (r j) := by
  classical
  let S := states P hP hk
  let G := S.activityGreedy 0 b hb
  let f := G.fullIndex S
  have hf : Monotone f := G.fullIndex_mono S
  let A (j : Fin (G.count+1)) := S.intervalActivity (f j.castSucc) (f j.succ) (hf (Fin.castSucc_le_succ j))
  have hex (j : Fin (G.count+1)) : ∃ r : ℕ, r≤(A j).card ∧
      (S.blockSteps (f j.castSucc) (f j.succ)).card ≤ switchCount (subsetPoints P (A j)) r :=
    block_count_le hP hk (hf (Fin.castSucc_le_succ j))
  choose r hr hcount using hex
  refine ⟨A,r,?_,hr,?_⟩
  · intro j
    rw [← S.activitySize_eq]
    exact G.fullIndex_activity S j
  · have hsum := S.sum_blockSteps (G.count+1) f hf
    dsimp only [f] at hsum
    rw [G.fullIndex_first S,G.fullIndex_last S,S.blockSteps_all] at hsum
    calc
      switchCount P k ≤ S.changeSteps.card := switchCount_le_changes hP hk
      _ = ∑ j : Fin (G.count+1), (S.blockSteps (f j.castSucc) (f j.succ)).card := hsum.symm
      _ ≤ _ := Finset.sum_le_sum (fun j _ => hcount j)

end PlanarHalving.Sweep

namespace PlanarHalving.Sweep

lemma division_scale {n q : ℕ} (hq : 4≤q) (hn : 4*q≤n) :
    let b := n/q-1
    0<b ∧ b+1=n/q ∧ (b+1:ℝ)≤(n:ℝ)/q ∧ n≤2*q*b ∧ (b+1)<n := by
  have hq0 : 0<q := by omega
  have hd : 4≤n/q := (Nat.le_div_iff_mul_le hq0).mpr hn
  have hbd : n/q-1+1=n/q := by omega
  refine ⟨by omega,hbd,?_,?_,?_⟩
  · have he : ((n/q-1:ℕ):ℝ)+1=(n/q:ℕ) := by exact_mod_cast hbd
    rw [he]
    exact (le_div_iff₀ (by exact_mod_cast hq0)).mpr (by exact_mod_cast Nat.div_mul_le_self n q)
  · have he := Nat.mod_add_div n q
    have hm := Nat.mod_lt n hq0
    nlinarith
  · rw [hbd]
    exact Nat.div_lt_self (by omega) (by omega)

lemma greedy_count_bound {q : ℕ} (hq : 4≤q) {m n b : ℕ} (hb : 0<b)
    (hn : n≤2*q*b) (hp : (m:ℝ)^3*(b:ℝ)^4≤(n:ℝ)^4/1024) :
    (m:ℝ)+1≤(q:ℝ)^((4:ℝ)/3)/2 := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hbr : (0:ℝ)<b := by exact_mod_cast hb
  have hnr : (n:ℝ)≤2*(q:ℝ)*b := by exact_mod_cast hn
  have hpow : ((q:ℝ)^((4:ℝ)/3))^3=(q:ℝ)^4 := by
    rw [←Real.rpow_mul_natCast hq0.le]
    norm_num
  have hm : (m:ℝ)≤(q:ℝ)^((4:ℝ)/3)/4 := by
    apply le_of_pow_le_pow_left₀ (by decide : (3:ℕ)≠0) (by positivity)
    have hn4 := pow_le_pow_left₀ (show (0:ℝ)≤n by positivity) hnr 4
    have ht : (m:ℝ)^3*(b:ℝ)^4≤((q:ℝ)^((4:ℝ)/3)/4)^3*(b:ℝ)^4 := by
      rw [div_pow,hpow]
      nlinarith
    exact (mul_le_mul_iff_left₀ (pow_pos hbr 4)).mp ht
  have hqpow : (4:ℝ)≤(q:ℝ)^((4:ℝ)/3) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤q by exact_mod_cast (show 1≤q by omega)) (by norm_num : (1:ℝ)≤4/3)
    rw [Real.rpow_one] at h1
    exact (show (4:ℝ)≤q by exact_mod_cast hq).trans h1
  linarith

lemma recurrence_exponent {q : ℕ} (hq : 4≤q) :
    ∃ ε : ℝ, 0<ε ∧ 0<(4:ℝ)/3-ε ∧
      (q:ℝ)^((4:ℝ)/3)/2≤(q:ℝ)^((4:ℝ)/3-ε) := by
  have hq2 : (2:ℝ)≤q := by exact_mod_cast (show 2≤q by omega)
  have hq0 : (0:ℝ)<q := lt_of_lt_of_le (by norm_num) hq2
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlq : 0<Real.log (q:ℝ) := Real.log_pos (by linarith)
  have hlog : Real.log 2≤Real.log (q:ℝ) := Real.log_le_log (by norm_num) hq2
  let ε : ℝ := Real.log 2/(2*Real.log (q:ℝ))
  have he : 0<ε := div_pos hl2 (by positivity)
  have hehalf : ε≤1/2 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0<2*Real.log (q:ℝ))).mpr
    nlinarith
  refine ⟨ε,he,by linarith,?_⟩
  rw [Real.rpow_sub hq0]
  apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hq0 ε)
  rw [Real.rpow_def_of_pos hq0]
  calc
    Real.exp (Real.log (q:ℝ)*ε) ≤ Real.exp (Real.log 2) := by
      apply Real.exp_le_exp.mpr
      dsimp [ε]
      have hl0 := ne_of_gt hlq
      field_simp
      nlinarith
    _ = 2 := Real.exp_log (by norm_num)

end PlanarHalving.Sweep

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Recurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Sweep

lemma switchCount_le_sq {n : ℕ} (P : Fin n → Point) (k : ℕ) : switchCount P k≤n*n := by
  classical
  simpa only [switchCount,Finset.card_univ,Fintype.card_prod,Fintype.card_fin] using
    (Finset.card_le_card (Finset.filter_subset (fun ij : Fin n × Fin n =>
      ij.1 < ij.2 ∧ 0<k ∧ k<n ∧ belowCount P ij.1 ij.2=k-1) Finset.univ))

lemma packing_scale : ∃ q : ℕ, 4≤q ∧ ∀ {n k : ℕ} (P : Fin n → Point)
    (hP : Generic P) (hk : k≤n) (_hn : 4*q≤n),
    let b := n/q-1
    ∀ hb : 0<b, (((states P hP hk).activityGreedy 0 b hb).count:ℝ)+1≤(q:ℝ)^((4:ℝ)/3)/2 := by
  obtain ⟨Q,_,hpack⟩ := activity_saving_cubic (δ := (1:ℝ)/(524288*1024)) (by norm_num)
  obtain ⟨q,hq⟩ := exists_nat_gt (max (4:ℝ) Q)
  have hq4 : 4≤q := by exact_mod_cast (le_max_left (4:ℝ) Q).trans hq.le
  have hqQ : Q≤q := (le_max_right (4:ℝ) Q).trans hq.le
  refine ⟨q,hq4,?_⟩
  intro n k P hP hk hn b hb
  let S := states P hP hk
  let G := S.activityGreedy 0 b hb
  have hscale := division_scale hq4 hn
  change 0<b ∧ b+1=n/q ∧ (b+1:ℝ)≤(n:ℝ)/q ∧ n≤2*q*b ∧ b+1<n at hscale
  have hqb : q*b≤n := (Nat.mul_le_mul_left q (Nat.sub_le (n/q) 1)).trans (Nat.mul_div_le n q)
  have hratio : Q≤(n:ℝ)/b := hqQ.trans ((le_div_iff₀ (by exact_mod_cast hb)).mpr (by exact_mod_cast hqb))
  have hdata := G.intervals_data S
  have hh := hpack P hP hk hb hratio (G.intervals S) hdata.1
    (fun p hp => (hdata.2 p hp).1) (fun p hp => by
      rw [← S.activitySize_eq]
      exact (hdata.2 p hp).2)
  rw [G.intervals_card S] at hh
  apply greedy_count_bound hq4 hb hscale.2.2.2.1
  norm_num at hh
  nlinarith

lemma count_bound_induction {q : ℕ} (hq : 4≤q) {β : ℝ} (hβ : 0<β)
    (hpacking : ∀ {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n)
      (_hn : 4*q≤n), let b := n/q-1
      ∀ hb : 0<b, (((states P hP hk).activityGreedy 0 b hb).count:ℝ)+1≤(q:ℝ)^β) :
    ∀ n : ℕ, ∀ P : Fin n → Point, Generic P → ∀ k : ℕ, k≤n →
      (switchCount P k:ℝ)≤(4*(q:ℝ))^2*(n:ℝ)^β := by
  let C : ℝ := (4*(q:ℝ))^2
  have hC : 0≤C := sq_nonneg _
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hP k hk
    by_cases hn : 4*q≤n
    · let b := n/q-1
      have hscale := division_scale hq hn
      change 0<b ∧ b+1=n/q ∧ (b+1:ℝ)≤(n:ℝ)/q ∧ n≤2*q*b ∧ b+1<n at hscale
      let hb := hscale.1
      let G := (states P hP hk).activityGreedy 0 b hb
      obtain ⟨A,r,hA,hr,hcount⟩ := activity_decomposition hP hk hb
      have hg : (G.count:ℝ)+1≤(q:ℝ)^β := hpacking P hP hk hn hb
      have hAreal (j : Fin (G.count+1)) : ((A j).card:ℝ)≤(n:ℝ)/q :=
        (by exact_mod_cast hA j : ((A j).card:ℝ)≤b+1).trans hscale.2.2.1
      have hind (j : Fin (G.count+1)) :
          (switchCount (subsetPoints P (A j)) (r j):ℝ)≤C*((A j).card:ℝ)^β :=
        ih (A j).card ((hA j).trans_lt hscale.2.2.2.2) (subsetPoints P (A j))
          (subsetPoints_generic hP (A j)) (r j) (hr j)
      change (switchCount P k:ℝ)≤C*(n:ℝ)^β
      calc
        (switchCount P k:ℝ) ≤ ∑ j : Fin (G.count+1), (switchCount (subsetPoints P (A j)) (r j):ℝ) := by exact_mod_cast hcount
        _ ≤ ∑ j : Fin (G.count+1), C*((A j).card:ℝ)^β := Finset.sum_le_sum (fun j _ => hind j)
        _ ≤ ∑ _j : Fin (G.count+1), C*((n:ℝ)/q)^β := Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (hAreal j) hβ.le) hC)
        _ = C*((n:ℝ)/q)^β*((G.count:ℝ)+1) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring
        _ ≤ C*((n:ℝ)/q)^β*(q:ℝ)^β := mul_le_mul_of_nonneg_left hg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
        _ = C*(n:ℝ)^β := by rw [Real.div_rpow (by positivity) hq0.le];field_simp
    · have hs : (switchCount P k:ℝ)≤(n:ℝ)^2 := by exact_mod_cast (by simpa only [pow_two] using switchCount_le_sq P k : switchCount P k≤n^2)
      by_cases hz : n=0
      · subst n
        simpa only [Nat.cast_zero,zero_pow (by decide : (2:ℕ)≠0),Real.zero_rpow hβ.ne',mul_zero] using hs
      · have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
        have hnr : (n:ℝ)≤4*(q:ℝ) := by exact_mod_cast (le_of_lt (lt_of_not_ge hn))
        have hpow : 1≤(n:ℝ)^β := by
          simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1) hn1 hβ.le
        exact (hs.trans (pow_le_pow_left₀ (by positivity) hnr 2)).trans (le_mul_of_one_le_right hC hpow)

end PlanarHalving.Sweep

namespace PlanarHalving

theorem all_ranks_power :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ P : Fin n → Point, Generic P →
        ∀ k : ℕ, k ≤ n → (switchCount P k : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε) := by
  obtain ⟨q,hq,hpack⟩ := Sweep.packing_scale
  obtain ⟨ε,he,hβ,hpow⟩ := Sweep.recurrence_exponent hq
  refine ⟨ε,he,(4*(q:ℝ))^2,?_⟩
  intro n _ P hP k hk
  apply Sweep.count_bound_induction hq hβ _ n P hP k hk
  intro n k P hP hk hn b hb
  exact (hpack P hP hk hn hb).trans hpow
end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Perturbation
open Set

lemma orient_cycle (p q r : Point) : orient q r p=orient p q r := by unfold orient;ring

lemma orient_segment {p q z : Point} (hz : z∈segment ℝ p q) : orient p q z=0 := by
  rw [segment_eq_image] at hz
  obtain ⟨t,_,rfl⟩ := hz
  simp only [orient,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma no_vertex_openSegment {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P)
    {i j : Fin n} (hij : i≠j) (v : Fin n) : P v∉openSegment ℝ (P i) (P j) := by
  intro hv
  have ho := orient_segment (openSegment_subset_segment ℝ _ _ hv)
  rcases (orient_zero_iff hP hij v).mp ho with rfl | rfl
  · exact hij (hP.1 (left_mem_openSegment_iff.mp hv))
  · exact hij (hP.1 (right_mem_openSegment_iff.mp hv))

lemma two_lines_intersection {p q r z : Point} (hd : orient p q r≠0)
    (hq : orient p q z=0) (hr : orient p r z=0) : z=p := by
  have hx : orient p q r*(z.1-p.1)=0 := by
    unfold orient at *
    linear_combination (r.1-p.1)*hq-(q.1-p.1)*hr
  have hy : orient p q r*(z.2-p.2)=0 := by
    unfold orient at *
    linear_combination (r.2-p.2)*hq-(q.2-p.2)*hr
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hd))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hd))

lemma slope_eq_orient_zero {p q r : Point} (hxq : p.1≠q.1) (hxr : p.1≠r.1)
    (hs : slope p q=slope p r) : orient p q r=0 := by
  rw [orient_eq_proj_diff _ _ _ hxq.symm]
  have he := Sweep.tied_projection p r hxr
  rw [← hs] at he
  change _*(Sweep.projection (slope p q) r-Sweep.projection (slope p q) p)=0
  rw [← he,sub_self,mul_zero]

lemma orient_line_eq {p q z : Point} (hx : p.1≠q.1) (hz : orient p q z=0) :
    z.2=slope p q*z.1+intercept p q := by
  rw [orient_eq_proj_diff _ _ _ hx.symm] at hz
  have hh := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hx.symm)
  dsimp [intercept]
  linarith

lemma intersectionPoint_eq {p q r s z : Point} (hpq : p.1≠q.1) (hrs : r.1≠s.1)
    (hs : slope p q≠slope r s) (hzp : orient p q z=0) (hzr : orient r s z=0) :
    z=intersectionPoint p q r s := by
  have hp := orient_line_eq hpq hzp
  have hr := orient_line_eq hrs hzr
  have hx : z.1=(intercept r s-intercept p q)/(slope p q-slope r s) := by
    apply (eq_div_iff (sub_ne_zero.mpr hs)).mpr
    nlinarith only [hp,hr]
  apply Prod.ext
  · exact hx
  · change z.2=slope p q*((intercept r s-intercept p q)/(slope p q-slope r s))+intercept p q
    rw [← hx]
    exact hp

lemma Regular.generic {n : ℕ} {P : Fin n → Point} (hP : Regular P) : Generic P := by
  refine ⟨hP.general,hP.xdistinct,?_,?_⟩
  · intro i j a b hij hab hs
    have he : (⟨(i,j),hij⟩ : Edge n)=⟨(a,b),hab⟩ := hP.slopes hs
    exact Prod.mk.inj (congrArg Subtype.val he)
  · intro i j a b c d hij hab hcd hef hge hgf z hz₁ hz₂ hz₃
    obtain ⟨v,hv⟩ := hP.concurrent ⟨(i,j),hij⟩ ⟨(a,b),hab⟩ ⟨(c,d),hcd⟩
      (fun h => hef (congrArg Subtype.val h)) (fun h => hge (congrArg Subtype.val h))
      (fun h => hgf (congrArg Subtype.val h)) z
      (orient_segment (openSegment_subset_segment ℝ _ _ hz₁))
      (orient_segment (openSegment_subset_segment ℝ _ _ hz₂)) (orient_segment hz₃)
    rw [← hv] at hz₁
    exact no_vertex_openSegment hP.general hij.ne v hz₁

lemma edge_cases {n : ℕ} (e : Edge (n+1)) :
    (∃ i, e=newEdge i) ∨ ∃ f, e=oldEdge f := by
  rcases e with ⟨⟨i,j⟩,hij⟩
  have hj : j≠0 := by intro h;subst j;exact (Fin.not_lt_zero i) hij
  obtain ⟨j,rfl⟩ := Fin.exists_succ_eq.mpr hj
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
  · exact Or.inl ⟨j,rfl⟩
  · exact Or.inr ⟨⟨(i,j),Fin.succ_lt_succ_iff.mp hij⟩,rfl⟩

end PlanarHalving.Perturbation
namespace PlanarHalving.Perturbation
open Set

lemma open_dense_affine (a b c : ℝ) (hab : a≠0 ∨ b≠0) :
    IsOpen {p : Point | a*p.1+b*p.2≠c} ∧ Dense {p : Point | a*p.1+b*p.2≠c} := by
  let L : Point →L[ℝ] ℝ := a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hL : L≠0 := by
    intro h
    have ha := congrArg (fun f : Point →L[ℝ] ℝ => f (1,0)) h
    have hb := congrArg (fun f : Point →L[ℝ] ℝ => f (0,1)) h
    change a*1+b*0=0 at ha
    change a*0+b*1=0 at hb
    norm_num at ha hb
    exact hab.elim (fun h => h ha) (fun h => h hb)
  have hd := (dense_compl_singleton c).preimage (L.isOpenMap_of_ne_zero hL)
  refine ⟨?_,?_⟩
  · exact isOpen_ne.preimage (by fun_prop : Continuous (fun p : Point => a*p.1+b*p.2))
  · change Dense {p : Point | a*p.1+b*p.2≠c} at hd
    exact hd

lemma open_dense_orient {p q : Point} (hpq : p≠q) :
    IsOpen {z : Point | orient p q z≠0} ∧ Dense {z : Point | orient p q z≠0} := by
  have hab : -(q.2-p.2)≠0 ∨ q.1-p.1≠0 := by
    by_contra! h
    apply hpq
    apply Prod.ext <;> linarith
  have he : {z : Point | orient p q z≠0}=
      {z : Point | -(q.2-p.2)*z.1+(q.1-p.1)*z.2≠(q.1-p.1)*p.2-(q.2-p.2)*p.1} := by
    ext z
    simp only [Set.mem_ofPred_eq,orient]
    constructor <;> intro hn he <;> apply hn <;> nlinarith only [he]
  rw [he]
  exact open_dense_affine _ _ _ hab

lemma open_dense_forall {ι : Sort*} [Finite ι] (p : ι → Point → Prop)
    (hU : ∀ i, IsOpen {x | p i x} ∧ Dense {x | p i x}) :
    IsOpen {x : Point | ∀ i, p i x} ∧ Dense {x : Point | ∀ i, p i x} := by
  simpa only [Set.ofPred_forall] using
    (show IsOpen (⋂ i, {x | p i x}) ∧ Dense (⋂ i, {x | p i x}) from
      ⟨isOpen_iInter_of_finite (fun i => (hU i).1),dense_iInter_of_isOpen (fun i => (hU i).1) (fun i => (hU i).2)⟩)

lemma open_dense_and {p q : Point → Prop}
    (hp : IsOpen {x | p x} ∧ Dense {x | p x}) (hq : IsOpen {x | q x} ∧ Dense {x | q x}) :
    IsOpen {x | p x ∧ q x} ∧ Dense {x | p x ∧ q x} :=
  ⟨hp.1.inter hq.1,hp.2.inter_of_isOpen_left hq.2 hp.1⟩

lemma fresh_open_dense {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P) :
    IsOpen {p | Fresh P p} ∧ Dense {p | Fresh P p} := by
  unfold Fresh
  apply open_dense_and
  · apply open_dense_forall
    intro i
    simpa only [one_mul,zero_mul,add_zero] using open_dense_affine 1 0 (P i).1 (Or.inl one_ne_zero)
  · apply open_dense_and
    · apply open_dense_forall
      intro i
      apply open_dense_forall
      intro j
      apply open_dense_forall
      intro hij
      exact open_dense_orient (fun h => hij (hP.1 h))
    · apply open_dense_and
      · apply open_dense_forall
        intro i
        apply open_dense_forall
        intro e
        simpa only [Sweep.projection,one_mul,sub_eq_add_neg,neg_mul,add_comm] using
          open_dense_affine (-(edgeSlope P e)) 1 ((P i).2-edgeSlope P e*(P i).1) (Or.inr one_ne_zero)
      · apply open_dense_forall
        intro i
        apply open_dense_forall
        intro e
        apply open_dense_forall
        intro f
        apply open_dense_forall
        intro hi
        exact open_dense_orient hi.symm

end PlanarHalving.Perturbation
namespace PlanarHalving.Perturbation
open Set
variable {n : ℕ} {P : Fin n → Point} {p : Point}

lemma Fresh.xdistinct (hP : Regular P) (hp : Fresh P p) :
    ∀ i j : Fin (n+1), i≠j → (Fin.cons (α := fun _ => Point) p P i).1≠(Fin.cons (α := fun _ => Point) p P j).1 := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
  · exact False.elim (hij rfl)
  · simpa only [Fin.cons_zero,Fin.cons_succ] using hp.1 j
  · simpa only [Fin.cons_zero,Fin.cons_succ] using (hp.1 i).symm
  · simpa only [Fin.cons_succ] using hP.xdistinct i j (fun h => hij (congrArg Fin.succ h))

lemma Fresh.general (hP : Regular P) (hp : Fresh P p) : GeneralPosition (Fin.cons (α := fun _ => Point) p P) := by
  refine ⟨?_,?_⟩
  · intro i j he
    by_contra hn
    exact hp.xdistinct hP i j hn (congrArg Prod.fst he)
  · intro i j l hij hjl hil
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · exact False.elim (hij rfl)
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l,rfl⟩
        · exact False.elim (hil rfl)
        · simp only [Fin.cons_zero,Fin.cons_succ]
          rw [← orient_cycle p (P j) (P l)]
          exact hp.2.1 j l (fun h => hjl (congrArg Fin.succ h))
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l,rfl⟩
        · exact False.elim (hjl rfl)
        · simp only [Fin.cons_zero,Fin.cons_succ]
          have he : orient (P i) p (P l)=-orient (P i) (P l) p := by unfold orient;ring
          rw [he]
          exact neg_ne_zero.mpr (hp.2.1 i l (fun h => hil (congrArg Fin.succ h)))
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l,rfl⟩
        · simpa only [Fin.cons_zero,Fin.cons_succ] using hp.2.1 i j (fun h => hij (congrArg Fin.succ h))
        · simpa only [Fin.cons_succ] using hP.general.2 i j l
            (fun h => hij (congrArg Fin.succ h)) (fun h => hjl (congrArg Fin.succ h))
            (fun h => hil (congrArg Fin.succ h))

lemma Fresh.slopes (hP : Regular P) (hp : Fresh P p) :
    Function.Injective (edgeSlope (Fin.cons (α := fun _ => Point) p P)) := by
  intro e f hs
  rcases edge_cases e with ⟨i,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases edge_cases f with ⟨j,rfl⟩ | ⟨f,rfl⟩
  · simp only [edgeSlope_new] at hs
    apply congrArg newEdge
    by_contra hij
    have ho : orient p (P i) (P j)≠0 := by
      rw [← orient_cycle p (P i) (P j)]
      exact hp.2.1 i j hij
    exact ho (slope_eq_orient_zero (hp.1 i) (hp.1 j) hs)
  · simp only [edgeSlope_new,edgeSlope_old] at hs
    have ht := Sweep.tied_projection p (P i) (hp.1 i)
    rw [hs] at ht
    exact False.elim (hp.2.2.1 i f ht)
  · simp only [edgeSlope_new,edgeSlope_old] at hs
    have ht := Sweep.tied_projection p (P j) (hp.1 j)
    rw [← hs] at ht
    exact False.elim (hp.2.2.1 j e ht)
  · simp only [edgeSlope_old] at hs
    exact congrArg oldEdge (hP.slopes hs)

lemma Fresh.two_new {i j : Fin n} (hp : Fresh P p) (hij : i≠j) {z : Point}
    (hi : orient p (P i) z=0) (hj : orient p (P j) z=0) :
    ∃ v : Fin (n+1), Fin.cons (α := fun _ => Point) p P v=z := by
  have ho : orient p (P i) (P j)≠0 := by
    rw [← orient_cycle p (P i) (P j)]
    exact hp.2.1 i j hij
  exact ⟨0,(two_lines_intersection ho hi hj).symm⟩

lemma Fresh.one_new (hP : Regular P) (hp : Fresh P p) (i : Fin n) {e f : Edge n}
    (hef : e≠f) {z : Point} (hi : orient p (P i) z=0) (he : onLine P e z) (hf : onLine P f z) :
    ∃ v : Fin (n+1), Fin.cons (α := fun _ => Point) p P v=z := by
  have hz : z=edgeMeet P e f := intersectionPoint_eq
    (hP.xdistinct _ _ e.property.ne) (hP.xdistinct _ _ f.property.ne)
    (fun h => hef (hP.slopes h)) he hf
  by_cases hzi : z=P i
  · exact ⟨i.succ,hzi.symm⟩
  · have hn := hp.2.2.2 i e f (by rw [← hz];exact hzi)
    rw [← hz,orient_cycle p (P i) z] at hn
    exact False.elim (hn hi)

lemma Fresh.regular (hP : Regular P) (hp : Fresh P p) : Regular (Fin.cons (α := fun _ => Point) p P) := by
  refine ⟨hp.general hP,hp.xdistinct hP,hp.slopes hP,?_⟩
  intro e f g hef hge hgf z he hf hg
  rcases edge_cases e with ⟨i,rfl⟩ | ⟨e,rfl⟩
  · rcases edge_cases f with ⟨j,rfl⟩ | ⟨f,rfl⟩
    · exact hp.two_new (fun h => hef (congrArg newEdge h)) ((onLine_new P p z i).mp he) ((onLine_new P p z j).mp hf)
    · rcases edge_cases g with ⟨l,rfl⟩ | ⟨g,rfl⟩
      · exact hp.two_new (fun h => hge (congrArg newEdge h.symm)) ((onLine_new P p z i).mp he) ((onLine_new P p z l).mp hg)
      · exact hp.one_new hP i (fun h => hgf (congrArg oldEdge h.symm))
          ((onLine_new P p z i).mp he) ((onLine_old P p z f).mp hf) ((onLine_old P p z g).mp hg)
  · rcases edge_cases f with ⟨j,rfl⟩ | ⟨f,rfl⟩
    · rcases edge_cases g with ⟨l,rfl⟩ | ⟨g,rfl⟩
      · exact hp.two_new (fun h => hgf (congrArg newEdge h.symm)) ((onLine_new P p z j).mp hf) ((onLine_new P p z l).mp hg)
      · exact hp.one_new hP j (fun h => hge (congrArg oldEdge h.symm))
          ((onLine_new P p z j).mp hf) ((onLine_old P p z e).mp he) ((onLine_old P p z g).mp hg)
    · rcases edge_cases g with ⟨l,rfl⟩ | ⟨g,rfl⟩
      · exact hp.one_new hP l (fun h => hef (congrArg oldEdge h))
          ((onLine_new P p z l).mp hg) ((onLine_old P p z e).mp he) ((onLine_old P p z f).mp hf)
      · obtain ⟨v,hv⟩ := hP.concurrent e f g (fun h => hef (congrArg oldEdge h))
          (fun h => hge (congrArg oldEdge h)) (fun h => hgf (congrArg oldEdge h)) z
          ((onLine_old P p z e).mp he) ((onLine_old P p z f).mp hf) ((onLine_old P p z g).mp hg)
        exact ⟨v.succ,hv⟩

end PlanarHalving.Perturbation
namespace PlanarHalving.Perturbation
open Set

lemma regular_empty (P : Fin 0 → Point) : Regular P := by
  constructor
  · constructor
    · intro i;exact Fin.elim0 i
    · intro i;exact Fin.elim0 i
  · intro i;exact Fin.elim0 i
  · intro e;exact Fin.elim0 e.val.1
  · intro e;exact Fin.elim0 e.val.1

lemma regular_approx (n : ℕ) {ε : ℝ} (hε : 0<ε) : ∀ P : Fin n → Point,
    ∃ Q : Fin n → Point, Regular Q ∧ ∀ i, dist (Q i) (P i)<ε := by
  induction n with
  | zero =>
    intro P
    exact ⟨P,regular_empty P,fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro P
    obtain ⟨Q,hQ,hclose⟩ := ih (fun i => P i.succ)
    obtain ⟨p,hp,hpclose⟩ := (fresh_open_dense hQ.general).2.exists_mem_open Metric.isOpen_ball
      (show (Metric.ball (P 0) ε).Nonempty from ⟨P 0,Metric.mem_ball_self hε⟩)
    refine ⟨Fin.cons p Q,hp.regular hQ,?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hpclose
    · exact hclose j

lemma dense_regular (n : ℕ) : Dense {P : Fin n → Point | Regular P} := by
  apply Metric.dense_iff.mpr
  intro P ε hε
  obtain ⟨Q,hQ,hclose⟩ := regular_approx n hε P
  exact ⟨Q,(dist_pi_lt_iff hε).mpr hclose,hQ⟩

lemma dense_generic (n : ℕ) : Dense {P : Fin n → Point | Generic P} :=
  (dense_regular n).mono (fun _ hp => hp.generic)

lemma generic_same_sides {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P) :
    ∃ Q : Fin n → Point, Generic Q ∧ ∀ i j l,
      (0<orient (P i) (P j) (P l) ↔ 0<orient (Q i) (Q j) (Q l)) := by
  let U : Set (Fin n → Point) := {Q | ∀ i j l, orient (P i) (P j) (P l)≠0 →
    0<orient (P i) (P j) (P l)*orient (Q i) (Q j) (Q l)}
  have hU : IsOpen U := by
    dsimp only [U]
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro l
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt continuous_const (by unfold orient;fun_prop)
  have hPU : P∈U := by
    intro i j l hn
    exact mul_self_pos.mpr hn
  obtain ⟨Q,hQ,hQU⟩ := (dense_generic n).exists_mem_open hU ⟨P,hPU⟩
  refine ⟨Q,hQ,?_⟩
  intro i j l
  by_cases hij : i=j
  · subst j;simp [orient]
  by_cases hjl : j=l
  · subst l;simp
  by_cases hil : i=l
  · subst l;simp
  have hprod := hQU i j l (hP.2 i j l hij hjl hil)
  rcases mul_pos_iff.mp hprod with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · exact iff_of_true hp hq
  · exact iff_of_false (not_lt_of_ge hp.le) (not_lt_of_ge hq.le)

lemma generic_same_halvingCount {n : ℕ} {P : Fin n → Point} (hP : GeneralPosition P) :
    ∃ Q : Fin n → Point, Generic Q ∧ halvingCount P=halvingCount Q := by
  classical
  obtain ⟨Q,hQ,hsides⟩ := generic_same_sides hP
  have hcount (i j : Fin n) : sideCount P i j=sideCount Q i j := by
    unfold sideCount
    apply congrArg Finset.card
    exact Finset.filter_congr (fun l _ => hsides i j l)
  refine ⟨Q,hQ,?_⟩
  unfold halvingCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro ij _
  rw [hcount,hcount]

end PlanarHalving.Perturbation

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving

theorem halving_power :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → Point,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε) := by
  obtain ⟨ε,hε,C,hbound⟩ := all_ranks_power
  refine ⟨ε,hε,C,2,?_⟩
  intro n heven hn P hP
  obtain ⟨m,hm⟩ := heven
  have hn' : n=2*m := by omega
  clear hm
  subst n
  obtain ⟨Q,hQ,hcount⟩ := Perturbation.generic_same_halvingCount hP
  rw [hcount,halvingCount_eq_middle_switchCount (by omega : 0 < m) Q hQ]
  exact hbound (2*m) (by omega) Q hQ m (by omega)
end PlanarHalving

namespace PlanarHalving

theorem power_bounds_oai :
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → Point,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ P : Fin n → Point, Generic P →
        ∀ k : ℕ, k ≤ n → (switchCount P k : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) :=
  ⟨halving_power, all_ranks_power⟩

end PlanarHalving

end OAI
end

theorem solution : type_of% @OAI.PlanarHalving.power_bounds_oai := @OAI.PlanarHalving.power_bounds_oai

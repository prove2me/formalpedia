-- Prove2me | solution 1 for OAI.PlanarHalving.RankLimits.Converges.radial_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:54:04.88311+00:00
-- url     : https://prove2.me/submissions/1e709e83-2eb6-4c66-9ea4-34f822b77ebd

import Mathlib
import Definitions.Def_HalvingLines
import Definitions.Def_OAIQWPHL000
import Theorems.Thm_OAI_PlanarHalving_PlaneGraph_designated_crossing_bound
import Theorems.Thm_OAI_PlanarHalving_RankLimits_pointwise_radial

section
-- module Solutions.OAIQW_PlanarHalving.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

theorem critical_image_null (f : Point → Point) :
    MeasureTheory.volume (f '' {p | DifferentiableAt ℝ f p ∧
      (fderiv ℝ f p).det = 0}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    MeasureTheory.volume
  · intro p hp
    exact hp.1.hasFDerivAt.hasFDerivWithinAt
  · intro p hp
    exact hp.2

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
-- module Solutions.OAIQW_PlanarHalving.Compactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Transversality

open MeasureTheory Set
open scoped MeasureTheory ENNReal

theorem critical_projection_null {Z : Type*} [MeasurableSpace Z]
    (σ : Measure Z) (coordinate : Z → Point) (hcoordinate : Measurable coordinate)
    (hdom : σ.map coordinate ≪ volume) (p : Z → Point) (F : Point → Point)
    (S : Set Z) (hidentity : ∀ z ∈ S, coordinate z = F (p z))
    (hdiff : ∀ z ∈ S, DifferentiableAt ℝ F (p z))
    (hsing : ∀ z ∈ S, (fderiv ℝ F (p z)).det = 0) : σ S = 0 := by
  obtain ⟨N, hsub, hN, hnull⟩ := exists_measurable_superset_of_null (critical_image_null F)
  apply measure_mono_null (t := coordinate ⁻¹' N)
  · intro z hz
    change coordinate z ∈ N
    rw [hidentity z hz]
    exact hsub ⟨p z, ⟨hdiff z hz, hsing z hz⟩, rfl⟩
  · rw [← Measure.map_apply hcoordinate hN]
    exact hdom hnull

theorem independent_gradients_ae {Z ι : Type*} [MeasurableSpace Z] [Countable ι]
    (ν : Measure Z) (h : Z → ℝ≥0∞) (hh : Measurable h)
    (σ : ι → Measure Z) (hν : ν.withDensity h ≪ Measure.sum σ)
    (coordinate : ι → Z → Point) (hcoordinate : ∀ i, Measurable (coordinate i))
    (hdom : ∀ i, (σ i).map (coordinate i) ≪ volume)
    (p : Z → Point) (F : ι → Point → Point) (S : Set Z)
    (hidentity : ∀ i z, z ∈ S → coordinate i z = F i (p z))
    (hdiff : ∀ i z, z ∈ S → DifferentiableAt ℝ (F i) (p z)) :
    ∀ᵐ z ∂ν, z ∈ S → h z ≠ 0 → ∃ i, (fderiv ℝ (F i) (p z)).det ≠ 0 := by
  have hbad : (ν.withDensity h) {z | z ∈ S ∧ ∀ i, (fderiv ℝ (F i) (p z)).det = 0} = 0 := by
    apply hν
    rw [Measure.sum_apply_eq_zero]
    intro i
    apply critical_projection_null (σ i) (coordinate i) (hcoordinate i) (hdom i) p
      (F i) _
    · intro z hz
      exact hidentity i z hz.1
    · intro z hz
      exact hdiff i z hz.1
    · intro z hz
      exact hz.2 i
  have hgood : ∀ᵐ z ∂ν.withDensity h,
      z ∈ S → ∃ i, (fderiv ℝ (F i) (p z)).det ≠ 0 := by
    apply ae_iff.mpr
    simpa only [Classical.not_imp, not_exists, not_not] using hbad
  have hg := (ae_withDensity_iff hh).mp hgood
  filter_upwards [hg] with z hz hzS hzh
  exact hz hzh hzS

end Transversality

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
-- module Solutions.OAIQW_PlanarHalving.PathLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankCoordinates
open Set

lemma variation_le_two {f : ℕ → ℝ} {n : ℕ}
    (hf : ∀ i ≤ n, 0 ≤ f i ∧ f i ≤ 1)
    (hqc : ∀ i j k, i ≤ j → j ≤ k → k ≤ n → min (f i) (f k) ≤ f j) :
    ∑ i ∈ Finset.range n, |f (i+1)-f i| ≤ 2 := by
  classical
  obtain ⟨k,hk,hmax⟩ := (Finset.range (n+1)).exists_max_image f (by simp)
  have hkn : k ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk
  have hleft : ∑ i ∈ Finset.range k, |f (i+1)-f i| = f k-f 0 := by
    rw [← Finset.sum_range_sub f k]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    apply abs_of_nonneg
    apply sub_nonneg.mpr
    have hq := hqc i (i+1) k (by omega) (by omega) hkn
    rw [min_eq_left (hmax i (by simp; omega))] at hq
    exact hq
  have hright : ∑ i ∈ Finset.Ico k n, |f (i+1)-f i| = f k-f n := by
    calc
      _ = - ∑ i ∈ Finset.Ico k n, (f (i+1)-f i) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨hki,hin⟩ := Finset.mem_Ico.mp hi
        apply abs_of_nonpos
        apply sub_nonpos.mpr
        have hq := hqc k i (i+1) hki (by omega) (by omega)
        rw [min_eq_right (hmax (i+1) (by simp; omega))] at hq
        exact hq
      _ = _ := by rw [Finset.sum_Ico_sub f hkn]; ring
  rw [← Finset.sum_range_add_sum_Ico (fun i => |f (i+1)-f i|) hkn,hleft,hright]
  have h0 := (hf 0 (Nat.zero_le n)).1
  have hn := (hf n le_rfl).1
  have hk1 := (hf k hkn).2
  linarith only [h0,hn,hk1]

lemma min_le_of_quasiconcave {f : ℝ → ℝ} (hf : QuasiconcaveOn ℝ univ f)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) : min (f x) (f z) ≤ f y := by
  have hc := (hf (min (f x) (f z))).ordConnected
  have hx : x ∈ univ ∩ {u | min (f x) (f z) ≤ f u} := by
    refine ⟨mem_univ _,?_⟩
    change min (f x) (f z) ≤ f x
    exact min_le_left _ _
  have hz : z ∈ univ ∩ {u | min (f x) (f z) ≤ f u} := by
    refine ⟨mem_univ _,?_⟩
    change min (f x) (f z) ≤ f z
    exact min_le_right _ _
  exact (hc.out hx hz ⟨hxy,hyz⟩).2

lemma concave_cdf_variation {f F : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    (hF : Monotone F) (hFrange : ∀ x, F x ∈ Icc 0 1)
    (x : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n, |F (f (x (i+1)))-F (f (x i))| ≤ 2 := by
  apply variation_le_two (fun i _ => hFrange (f (x i)))
  intro i j k hij hjk _
  rw [← hF.map_min]
  exact hF (min_le_of_quasiconcave hf.quasiconcaveOn (hx hij) (hx hjk))

lemma sigmoid_variation {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    {ε : ℝ} (hε : 0 < ε) (x : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n,
      |Real.sigmoid (f (x (i+1))/ε)-Real.sigmoid (f (x i)/ε)| ≤ 2 := by
  apply concave_cdf_variation hf
    (fun _ _ h => Real.sigmoid_strictMono.monotone (div_le_div_of_nonneg_right h hε.le))
    (fun _ => ⟨(Real.sigmoid_pos _).le,(Real.sigmoid_lt_one _).le⟩) x hx n

lemma smoothed_variation {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    {ε : ℝ} (hε : 0 < ε) (x : ℕ → ℝ) (hx : Monotone x) (n : ℕ) :
    ∑ i ∈ Finset.range n,
      |smoothed g ε (x (i+1),f (x (i+1)))-smoothed g ε (x i,f (x i))| ≤ 2 := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hterm (i : ℕ) :
      |smoothed g ε (x (i+1),f (x (i+1)))-smoothed g ε (x i,f (x i))| ≤
        (∑ j, |Real.sigmoid ((f (x (i+1))-g j (x (i+1)))/ε) -
                Real.sigmoid ((f (x i)-g j (x i))/ε)|) / m := by
    unfold smoothed
    rw [← sub_div,abs_div,abs_of_pos hmR,← Finset.sum_sub_distrib]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hmR.le
  calc
    _ ≤ ∑ i ∈ Finset.range n, (∑ j, |Real.sigmoid ((f (x (i+1))-g j (x (i+1)))/ε) -
        Real.sigmoid ((f (x i)-g j (x i))/ε)|) / m := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (∑ j : Fin m, ∑ i ∈ Finset.range n,
        |Real.sigmoid ((f (x (i+1))-g j (x (i+1)))/ε) -
          Real.sigmoid ((f (x i)-g j (x i))/ε)|) / m := by
      rw [← Finset.sum_div,Finset.sum_comm]
    _ ≤ (∑ _j : Fin m, (2 : ℝ))/m := by
      apply div_le_div_of_nonneg_right _ hmR.le
      exact Finset.sum_le_sum (fun j _ => sigmoid_variation (hf.sub (hg j)) hε x hx n)
    _ = 2 := by simp; field_simp

end PlanarHalving.RankCoordinates

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

namespace PlanarHalving.RankCoordinates
open Set

lemma slot_lt_of_le_imp_lt {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    {p q : Point} (h : ∀ i, g i p.1 ≤ p.2 → g i q.1 < q.2)
    (hp : ∃ i, g i p.1 = p.2) : slot g p < slot g q := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h i (Finset.mem_filter.mp hi).2.le⟩
  · obtain ⟨i,hi⟩ := hp
    intro he
    have hiq : i ∈ Finset.univ.filter (fun i => g i q.1 < q.2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,h i hi.le⟩
    rw [← he] at hiq
    exact (lt_irrefl (p.2)) (hi ▸ (Finset.mem_filter.mp hiq).2)

lemma slot_chord_bounds {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ)
    {l u : ℝ}
    (hs : ∀ i x y, x ≤ y → l*(y-x) ≤ g i y-g i x ∧ g i y-g i x ≤ u*(y-x))
    {p q : Point} (hx : p.1 ≤ q.1) (hp : ∃ i, g i p.1 = p.2)
    (hq : ∃ i, g i q.1 = q.2) (he : slot g p = slot g q) :
    l*(q.1-p.1) ≤ q.2-p.2 ∧ q.2-p.2 ≤ u*(q.1-p.1) := by
  constructor
  · by_contra hn
    have ht := slot_lt_of_le_imp_lt g (p := q) (q := p) (fun i hi => by
      have hh := (hs i p.1 q.1 hx).1
      linarith only [hh,hi,lt_of_not_ge hn]) hq
    exact (ne_of_lt ht) he.symm
  · by_contra hn
    have ht := slot_lt_of_le_imp_lt g (p := p) (q := q) (fun i hi => by
      have hh := (hs i p.1 q.1 hx).2
      linarith only [hh,hi,lt_of_not_ge hn]) hp
    exact (ne_of_lt ht) he

theorem pair_slots_injOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : ι → ℝ → ℝ) (h : κ → ℝ → ℝ) {l u l' u' : ℝ}
    (hg : ∀ i x y, x ≤ y → l*(y-x) ≤ g i y-g i x ∧ g i y-g i x ≤ u*(y-x))
    (hh : ∀ i x y, x ≤ y → l'*(y-x) ≤ h i y-h i x ∧ h i y-h i x ≤ u'*(y-x))
    (hgap : u < l') (S : Set Point)
    (hS : ∀ p ∈ S, (∃ i, g i p.1 = p.2) ∧ ∃ j, h j p.1 = p.2) :
    Set.InjOn (fun p => (slot g p,slot h p)) S := by
  have horder {p q : Point} (hp : p ∈ S) (hq : q ∈ S)
      (he : (slot g p,slot h p) = (slot g q,slot h q)) : ¬ p.1 < q.1 := by
    intro hx
    have hg' := (slot_chord_bounds g hg hx.le (hS p hp).1 (hS q hq).1 (congrArg Prod.fst he)).2
    have hh' := (slot_chord_bounds h hh hx.le (hS p hp).2 (hS q hq).2 (congrArg Prod.snd he)).1
    have hstrict := mul_lt_mul_of_pos_right hgap (sub_pos.mpr hx)
    linarith only [hg',hh',hstrict]
  intro p hp q hq he
  have hx : p.1 = q.1 := le_antisymm (le_of_not_gt (horder hq hp he.symm)) (le_of_not_gt (horder hp hq he))
  have hy := slot_chord_bounds g hg hx.le (hS p hp).1 (hS q hq).1 (congrArg Prod.fst he)
  rw [hx,sub_self,mul_zero,mul_zero] at hy
  exact Prod.ext hx (by linarith only [hy.1,hy.2])

lemma slot_lt_card {ι : Type*} [Fintype ι] (g : ι → ℝ → ℝ) {p : Point}
    (hp : ∃ i, g i p.1 = p.2) : slot g p < Fintype.card ι := by
  classical
  apply lt_of_lt_of_eq (Finset.card_lt_card ?_) (Finset.card_univ : _ = Fintype.card ι)
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset ..,?_⟩
  obtain ⟨i,hi⟩ := hp
  intro he
  have hmem := Finset.mem_univ i
  rw [← he] at hmem
  exact (lt_irrefl (p.2)) (hi ▸ (Finset.mem_filter.mp hmem).2)

end PlanarHalving.RankCoordinates

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

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology

theorem persistent_mass_zero {ι : Type*} (S : ℕ → Finset ι)
    (lam μ s : ℕ → ι → ℝ) (q : ℕ → ℝ) {L A H U : ℝ}
    (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hq : ∀ n, 0 < q n) (hqtop : Tendsto q atTop atTop)
    (hcard : ∀ n, ((S n).card : ℝ) ≤ q n)
    (hlam0 : ∀ n i, i ∈ S n → 0 ≤ lam n i)
    (hlam1 : ∀ n i, i ∈ S n → lam n i ≤ (q n)⁻¹)
    (hμ0 : ∀ n i, i ∈ S n → 0 ≤ μ n i)
    (hs0 : ∀ n i, i ∈ S n → 0 ≤ s n i)
    (hmass : ∀ n i, i ∈ S n → (lam n i)^3 ≤ A*(s n i)^3*μ n i)
    (hμsum : ∀ n, ∑ i ∈ S n, μ n i ≤ U)
    (htail : ∀ n u, 0 < u → ((S n |>.filter fun i => u < s n i).card : ℝ) ≤
      H*u^(-(4:ℝ)/3))
    (hpartition : ∀ n, L ≤ ∑ i ∈ S n, lam n i) : L = 0 := by
  apply Boundary.mass_eq_zero S lam μ s (fun n i => μ n i/2) (fun _ _ => 0) q
    (L := L) (A := A) (H := H) (B := 0) (B₀ := U/2) (T := 0) (α := 1)
    hL hA (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hq hqtop hcard hlam0 hlam1 hμ0 hs0 (by intros; norm_num) hmass
    (by intros; linarith) ?_ (by intros; simp) htail hpartition
  intro n
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (hμsum n) (by norm_num)

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

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology
variable {X ι : Type*} [MeasurableSpace X]

lemma probability_overlap_bound (μ : FiniteMeasure X) (S : Finset ι) (p : ι → X → ℝ)
    (hp : ∀ i ∈ S, Measurable (p i)) (hp0 : ∀ i ∈ S, ∀ z, 0 ≤ p i z)
    (hsum : ∀ z, ∑ i ∈ S, p i z ≤ 1) {β : ℝ} (hβ : 0 < β) :
    ∑ i ∈ S, (μ {z | β < p i z} : ℝ) ≤ (μ.mass : ℝ)/β := by
  classical
  let A : ι → Set X := fun i => {z | β < p i z}
  have hm i (hi : i ∈ S) : MeasurableSet (A i) := measurableSet_lt measurable_const (hp i hi)
  have hInt i (hi : i ∈ S) : Integrable ((A i).indicator (fun _ : X => (1 : ℝ))) (μ : Measure X) :=
    (integrable_const 1).indicator (hm i hi)
  have he i (hi : i ∈ S) : ∫ z, (A i).indicator (fun _ : X => (1 : ℝ)) z ∂(μ : Measure X) =
      (μ (A i) : ℝ) := by
    rw [integral_indicator_const 1 (hm i hi)]
    simp
  have hbound (z : X) : (∑ i ∈ S, (A i).indicator (fun _ : X => (1 : ℝ)) z) ≤ 1/β := by
    have hh : β*(∑ i ∈ S, (A i).indicator (fun _ : X => (1 : ℝ)) z) ≤ 1 := by
      calc
        _ = ∑ i ∈ S, β*(A i).indicator (fun _ : X => (1 : ℝ)) z := Finset.mul_sum ..
        _ ≤ ∑ i ∈ S, p i z := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hz : z ∈ A i
          · simpa only [Set.indicator_of_mem hz,mul_one] using (show β < p i z from hz).le
          · simpa only [Set.indicator_of_notMem hz,mul_zero] using hp0 i hi z
        _ ≤ 1 := hsum z
    exact (le_div_iff₀ hβ).mpr (by simpa only [mul_comm] using hh)
  have hh := integral_mono (integrable_finsetSum S hInt) (integrable_const (1/β)) hbound
  rw [integral_finsetSum S hInt] at hh
  rw [Finset.sum_congr rfl he] at hh
  simpa [integral_const,div_eq_mul_inv,FiniteMeasure.mass] using hh

lemma finite_bad_cover_mass (μ : FiniteMeasure X) (S : Finset ι) (p : ι → X → ℝ)
    (hp : ∀ i ∈ S, Measurable (p i)) (hp0 : ∀ i ∈ S, ∀ z, 0 ≤ p i z)
    (hp1 : ∀ i ∈ S, ∀ z, p i z ≤ 1) {β : ℝ}
    {B : Set X} (hB : MeasurableSet B)
    (hcover : ∀ z ∈ B, ∃ i ∈ S, β < p i z) :
    β*(μ B : ℝ) ≤ ∑ i ∈ S, ∫ z in {z | β < p i z}, p i z ∂(μ : Measure X) := by
  classical
  let A : ι → Set X := fun i => {z | β < p i z}
  have hm i (hi : i ∈ S) : MeasurableSet (A i) := measurableSet_lt measurable_const (hp i hi)
  have hInt i (hi : i ∈ S) : Integrable (p i) (μ : Measure X) :=
    (integrable_const (1 : ℝ)).mono' (hp i hi).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hp0 i hi z)] using hp1 i hi z))
  have hInd i (hi : i ∈ S) := (hInt i hi).indicator (hm i hi)
  have hpoint (z : X) : B.indicator (fun _ : X => β) z ≤ ∑ i ∈ S, (A i).indicator (p i) z := by
    have hnn i (hi : i ∈ S) : 0 ≤ (A i).indicator (p i) z := by
      exact Set.indicator_nonneg (fun x _ => hp0 i hi x) z
    by_cases hz : z ∈ B
    · obtain ⟨i,hi,hip⟩ := hcover z hz
      rw [Set.indicator_of_mem hz]
      calc
        β ≤ (A i).indicator (p i) z := by rw [Set.indicator_of_mem (show z ∈ A i from hip)]; exact hip.le
        _ ≤ ∑ i ∈ S, (A i).indicator (p i) z := Finset.single_le_sum hnn hi
    · rw [Set.indicator_of_notMem hz]
      exact Finset.sum_nonneg hnn
  have hh := integral_mono ((integrable_const β).indicator hB) (integrable_finsetSum S hInd) hpoint
  rw [integral_indicator_const β hB,integral_finsetSum S hInd] at hh
  rw [Finset.sum_congr rfl (fun i hi => integral_indicator (hm i hi))] at hh
  simpa [mul_comm] using hh

end PlanarHalving.Limits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology

theorem ae_exists_partition_small {X ι : Type*} [MeasurableSpace X]
    (lam μ : FiniteMeasure X) (S : ℕ → Finset ι) (p : ℕ → ι → X → ℝ)
    (mu nu : ℕ → ι → FiniteMeasure X) (s : ℕ → ι → ℝ) (q : ℕ → ℝ)
    {A H : ℝ} (hA : 0 ≤ A)
    (hq : ∀ n, 0 < q n) (hqtop : Tendsto q atTop atTop)
    (hcard : ∀ n, ((S n).card : ℝ) ≤ q n)
    (hp : ∀ n i, i ∈ S n → Measurable (p n i))
    (hp0 : ∀ n i, i ∈ S n → ∀ z, 0 ≤ p n i z)
    (hp1 : ∀ n i, i ∈ S n → ∀ z, p n i z ≤ 1)
    (hsum : ∀ n z, ∑ i ∈ S n, p n i z ≤ 1)
    (hs0 : ∀ n i, i ∈ S n → 0 ≤ s n i)
    (hmu : ∀ n i, i ∈ S n → ∀ B, mu n i B ≤ μ B)
    (hnu : ∀ n i, i ∈ S n → ∀ B, MeasurableSet B →
      (nu n i B : ℝ) = ∫ z in B, p n i z ∂(lam : Measure X))
    (hnuMass : ∀ n i, i ∈ S n → ((nu n i).mass : ℝ) ≤ (q n)⁻¹)
    (hmass : ∀ n i, i ∈ S n → ∀ B, MeasurableSet B →
      (nu n i B : ℝ)^3 ≤ A*(s n i)^3*(mu n i B : ℝ))
    (htail : ∀ n u, 0 < u → ((S n |>.filter fun i => u < s n i).card : ℝ) ≤
      H*u^(-(4:ℝ)/3)) {β : ℝ} (hβ : 0 < β) :
    ∀ᵐ z ∂(lam : Measure X), ∃ n, ∀ i ∈ S n, p n i z ≤ β := by
  classical
  let B : Set X := ⋂ n, ⋃ i ∈ S n, {z | β < p n i z}
  have hm n i (hi : i ∈ S n) : MeasurableSet {z | β < p n i z} :=
    measurableSet_lt measurable_const (hp n i hi)
  have hB : MeasurableSet B := by
    apply MeasurableSet.iInter
    intro n
    exact (S n).finite_toSet.measurableSet_biUnion (fun i hi => hm n i hi)
  have hcover n z (hz : z ∈ B) : ∃ i ∈ S n, β < p n i z := by
    have hz' := mem_iInter.mp hz n
    simpa only [mem_iUnion,mem_ofPred_eq,exists_prop] using hz'
  have hz := persistent_mass_zero S
    (fun n i => (nu n i {z | β < p n i z} : ℝ))
    (fun n i => (mu n i {z | β < p n i z} : ℝ)) s q
    (L := β*(lam B : ℝ)) (A := A) (H := H) (U := (μ.mass : ℝ)/β)
    (mul_nonneg hβ.le (NNReal.coe_nonneg _)) hA hq hqtop hcard
    (fun _ _ _ => NNReal.coe_nonneg _) ?_
    (fun _ _ _ => NNReal.coe_nonneg _) hs0 ?_ ?_ htail ?_
  · have hzero : (lam B : ℝ) = 0 := (mul_eq_zero.mp hz).resolve_left hβ.ne'
    have hzero' : (lam : Measure X) B = 0 := by
      apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
      simpa using hzero
    rw [ae_iff]
    have he : {z | ¬ ∃ n, ∀ i ∈ S n, p n i z ≤ β} = B := by
      ext z
      simp only [mem_ofPred_eq,not_exists,not_forall,not_le,B,mem_iInter,mem_iUnion,
        exists_prop]
    rw [he]
    exact hzero'
  · intro n i hi
    exact (show (nu n i {z | β < p n i z} : ℝ) ≤ ((nu n i).mass : ℝ) from
      NNReal.coe_le_coe.mpr ((nu n i).apply_le_mass _)).trans (hnuMass n i hi)
  · intro n i hi
    exact hmass n i hi _ (hm n i hi)
  · intro n
    exact (Finset.sum_le_sum (fun i hi => NNReal.coe_le_coe.mpr (hmu n i hi _))).trans
      (probability_overlap_bound μ (S n) (p n) (hp n) (hp0 n) (hsum n) hβ)
  · intro n
    have hc := finite_bad_cover_mass lam (S n) (p n) (hp n) (hp0 n) (hp1 n) hB (hcover n)
    simpa only [Finset.sum_congr rfl (fun i hi => hnu n i hi _ (hm n i hi))] using hc

end PlanarHalving.Limits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter ProbabilityTheory

lemma kernel_nullSingleton_of_cells {X T ι : Type*} [MeasurableSpace X]
    [MeasurableSpace T] (lam : Measure X) (h : Kernel X T) [IsMarkovKernel h]
    (S : ℕ → Finset ι) (cell : ℕ → ι → Set T)
    (hcover : ∀ n t, ∃ i ∈ S n, t ∈ cell n i)
    (hsmall : ∀ m : ℕ, ∀ᵐ z ∂lam, ∃ n, ∀ i ∈ S n,
      (h z).real (cell n i) ≤ 1/((m : ℝ)+1)) :
    ∀ᵐ z ∂lam, NullSingletonClass (h z) := by
  have hh := (ae_all_iff.mpr hsmall)
  filter_upwards [hh] with z hz
  constructor
  intro t
  apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
  by_contra hpos
  have htpos : 0 < (h z).real {t} := lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hpos)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt htpos
  obtain ⟨n, hn⟩ := hz m
  obtain ⟨i, hi, hit⟩ := hcover n t
  have hh : (h z).real {t} ≤ (h z).real (cell n i) :=
    measureReal_mono (singleton_subset_iff.mpr hit)
  linarith [hn i hi]

end PlanarHalving.Limits
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

lemma grid_measurable (m : ℕ) [NeZero m] : Measurable (grid m) :=
  (measurable_of_finite (fun i : Fin m => boundary m i.castSucc)).comp (index_measurable m)

lemma dist_grid (m : ℕ) [NeZero m] (t : I) : dist (grid m t) t ≤ 1/(m : ℝ) := by
  have ht := mem_cell_index m t
  have hl := cell_lower m (index m t) ht
  have hu := cell_upper m (index m t) ht
  rw [Subtype.dist_eq,Real.dist_eq,abs_sub_comm]
  change |(t : ℝ)-(index m t : ℝ)/(m : ℝ)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  change (t : ℝ)-(index m t : ℝ)/(m : ℝ) ≤ 1/(m : ℝ)
  have he : ((index m t : ℝ)+1)/(m : ℝ) = (index m t : ℝ)/(m : ℝ)+1/(m : ℝ) := by ring
  rw [he] at hu
  linarith

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

lemma integral_grid_pair (m : ℕ) [NeZero m] (f : I × I → ℝ) :
    ∫ t : I × I, f (grid m t.1,grid m t.2) =
      (∑ i : Fin m × Fin m, f (boundary m i.1.castSucc,boundary m i.2.castSucc))/(m : ℝ)^2 := by
  let C : Fin m × Fin m → Set (I × I) := fun i => cell m i.1 ×ˢ cell m i.2
  have hC i : MeasurableSet (C i) := (cell_measurable m i.1).prod (cell_measurable m i.2)
  let idx : I × I → Fin m × Fin m := fun t => (index m t.1,index m t.2)
  have hi t i : idx t = i ↔ t ∈ C i := by
    rcases i with ⟨i,j⟩
    simp only [idx,C,Prod.mk.injEq,index_eq,mem_prod]
  change ∫ t, (fun i : Fin m × Fin m => f (boundary m i.1.castSucc,boundary m i.2.castSucc)) (idx t) = _
  rw [integral_partition volume C hC idx hi (fun i => f (boundary m i.1.castSucc,boundary m i.2.castSucc))]
  have hv i : volume.real (C i) = 1/(m : ℝ)^2 := by
    rw [measureReal_def]
    change ((volume.prod volume) (cell m i.1 ×ˢ cell m i.2)).toReal = _
    rw [Measure.prod_prod,cell_volume,cell_volume,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(m : ℝ))]
    ring
  simp_rw [hv]
  rw [← Finset.mul_sum]
  ring

end PlanarHalving.UniformPartition

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped unitInterval Topology

lemma grid_tendsto_seq (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop) (t : I) :
    Tendsto (fun n => grid (m n) t) atTop (𝓝 t) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => dist_grid (m n) t)
  have hnat : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hnat

lemma riemann_tendsto (m : ℕ → ℕ) [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop)
    (f : BoundedContinuousFunction (I × I) ℝ) :
    Tendsto (fun n => (∑ i : Fin (m n) × Fin (m n),
      f (boundary (m n) i.1.castSucc,boundary (m n) i.2.castSucc))/(m n : ℝ)^2)
      atTop (𝓝 (∫ t : I × I, f t)) := by
  simp_rw [← integral_grid_pair]
  apply tendsto_integral_of_dominated_convergence (fun _ : I × I => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp
      (((grid_measurable (m n)).comp measurable_fst).prodMk
        ((grid_measurable (m n)).comp measurable_snd))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (fun _ => f.norm_coe_le_norm _)
  · exact Filter.Eventually.of_forall (fun t => (f.continuous.tendsto t).comp
      ((grid_tendsto_seq m hm t.1).prodMk_nhds (grid_tendsto_seq m hm t.2)))

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

namespace PlanarHalving.UniformPartition
open MeasureTheory Set Filter PlanarHalving.Limits
open scoped Topology unitInterval NNReal ENNReal

lemma grid_sum_le {m c : ℕ} [NeZero m] (slots : Fin c → Fin m × Fin m)
    (hs : Function.Injective slots) (f : I × I → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (∑ i, f (gridPoint m (slots i))) ≤ ∑ j, f (gridPoint m j) := by
  classical
  rw [← Finset.sum_image (f := fun j => f (gridPoint m j)) hs.injOn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hf _)

lemma normalized_perturbed_sum_le {m c : ℕ} [NeZero m]
    (slots : Fin c → Fin m × Fin m) (hs : Function.Injective slots)
    (x : Fin c → I × I) (f : I × I → ℝ) (hf : ∀ t, 0 ≤ f t)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ i, f (x i) ≤ f (gridPoint m (slots i)) + ε) :
    (∑ i, f (x i))/(m : ℝ)^2 ≤
      (∑ j : Fin m × Fin m, f (gridPoint m j))/(m : ℝ)^2 + ε := by
  have hm : 0 < (m : ℝ) := by exact_mod_cast NeZero.pos m
  have hc : (c : ℝ) ≤ (m : ℝ)^2 := by
    have h := Fintype.card_le_of_injective slots hs
    simp only [Fintype.card_fin,Fintype.card_prod] at h
    simpa only [pow_two] using (show (c : ℝ) ≤ (m : ℝ)*(m : ℝ) by exact_mod_cast h)
  have hsum : (∑ i, f (x i)) ≤ (∑ j : Fin m × Fin m, f (gridPoint m j)) + (c : ℝ)*ε := by
    calc
      _ ≤ ∑ i, (f (gridPoint m (slots i)) + ε) := Finset.sum_le_sum (fun i _ => hclose i)
      _ = (∑ i, f (gridPoint m (slots i))) + (c : ℝ)*ε := by simp [Finset.sum_add_distrib]
      _ ≤ _ := add_le_add (grid_sum_le slots hs f hf) le_rfl
  have hεc : (c : ℝ)*ε ≤ (m : ℝ)^2*ε := mul_le_mul_of_nonneg_right hc hε
  apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
  nlinarith [div_mul_cancel₀ (∑ j : Fin m × Fin m, f (gridPoint m j)) (ne_of_gt (sq_pos_of_pos hm))]

end PlanarHalving.UniformPartition

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

namespace PlanarHalving.TimeWindows
open Set Filter
open scoped unitInterval Topology

lemma cut_time_error (R : ℕ) [NeZero R] (x : I) :
    |(cut (time R) x : ℝ)-(R : ℝ)*(x : ℝ)| ≤ 1 := by
  have hR : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
  have hc := cut_le (time R) x
  apply abs_le.mpr
  constructor
  · by_cases h : cut (time R) x=R
    · rw [h]
      have hx := mul_le_mul_of_nonneg_left x.property.2 hR.le
      linarith
    · have hc' : cut (time R) x<R := lt_of_le_of_ne hc h
      let b : Fin R := ⟨cut (time R) x,hc'⟩
      have hb : ¬ time R b<x := by
        rw [← lt_cut_iff (time_strictMono R)]
        exact Nat.lt_irrefl _
      have hx : (x : ℝ)≤((b : ℝ)+1/2)/(R : ℝ) := le_of_not_gt hb
      have hh := (le_div_iff₀ hR).mp hx
      change (x : ℝ)*(R : ℝ) ≤ (cut (time R) x : ℝ)+1/2 at hh
      nlinarith
  · by_cases h : cut (time R) x=0
    · rw [h,Nat.cast_zero,zero_sub]
      have hx := mul_nonneg hR.le x.property.1
      linarith
    · have hc0 : 0<cut (time R) x := Nat.pos_of_ne_zero h
      let b : Fin R := ⟨cut (time R) x-1,by omega⟩
      have hb : time R b<x := (lt_cut_iff (time_strictMono R) b x).mp (by dsimp [b]; omega)
      have hx : ((b : ℝ)+1/2)/(R : ℝ)<(x : ℝ) := hb
      have hh := (div_lt_iff₀ hR).mp hx
      have hv : (b : ℝ)+1=(cut (time R) x : ℝ) := by
        exact_mod_cast (show b.val+1=cut (time R) x by dsimp [b]; omega)
      nlinarith

lemma length_error (R : ℕ) [NeZero R] (J : Window) :
    |(length R J : ℝ)/(R : ℝ)-1/(2^J.1 : ℕ)| ≤ 2/(R : ℝ) := by
  have hlo := cut_time_error R (UniformPartition.boundary (2^J.1) J.2.castSucc)
  have hhi := cut_time_error R (UniformPartition.boundary (2^J.1) J.2.succ)
  have hn : (0 : ℝ)<R := Nat.cast_pos.mpr (NeZero.pos R)
  have he : (length R J : ℝ)=(stop R J : ℝ)-(start R J : ℝ) :=
    Nat.cast_sub (start_le_stop R J)
  have hbound : |(length R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ)|≤2 := by
    rw [he]
    have hid : (stop R J : ℝ)-(start R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ) =
        ((stop R J : ℝ)-(R : ℝ)*(UniformPartition.boundary (2^J.1) J.2.succ : ℝ)) -
        ((start R J : ℝ)-(R : ℝ)*(UniformPartition.boundary (2^J.1) J.2.castSucc : ℝ)) := by
      simp only [UniformPartition.boundary,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
      ring
    rw [hid]
    exact (abs_sub _ _).trans (by simpa only [start,stop,one_add_one_eq_two] using add_le_add hhi hlo)
  have hid : (length R J : ℝ)/(R : ℝ)-1/(2^J.1 : ℕ)=
      ((length R J : ℝ)-(R : ℝ)/(2^J.1 : ℕ))/(R : ℝ) := by field_simp
  rw [hid,abs_div,abs_of_pos hn]
  exact div_le_div_of_nonneg_right hbound hn.le

lemma length_tendsto (R : ℕ → ℕ) [∀ n, NeZero (R n)] (hR : Tendsto R atTop atTop) (J : Window) :
    Tendsto (fun n => (length (R n) J : ℝ)/(R n : ℝ)) atTop (𝓝 (1/(2^J.1 : ℕ) : ℝ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using length_error (R n) J)
  have hn : Tendsto (fun n => (R n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  simpa only [div_eq_mul_inv,Function.comp_def,mul_zero] using (tendsto_inv_atTop_zero.comp hn).const_mul 2

lemma eventually_length_pos (R : ℕ → ℕ) [∀ n, NeZero (R n)] (hR : Tendsto R atTop atTop) (J : Window) :
    ∀ᶠ n in atTop, 0<length (R n) J := by
  have ht := (tendsto_order.mp (length_tendsto R hR J)).1 (0 : ℝ) (by positivity)
  filter_upwards [ht] with n hn
  have hh := (div_pos_iff.mp hn)
  rcases hh with hh|hh
  · exact_mod_cast hh.1
  · exact False.elim (not_lt_of_ge (Nat.cast_nonneg (length (R n) J)) hh.1)

end PlanarHalving.TimeWindows

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
namespace PlanarHalving.RankCoordinates
open Set
open scoped ENNReal

lemma smoothed_eVariation {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    {ε : ℝ} (hε : 0 < ε) :
    eVariationOn (fun x => smoothed g ε (x,f x)) univ ≤ 2 := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n,x,hx,_⟩
  have h := smoothed_variation hm g hg hf hε x hx n
  simpa only [edist_dist,Real.dist_eq,ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _),
    ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h

lemma sum_interval_eVariation {N : ℕ} {f : ℝ → ℝ}
    (x : Fin (N+1) → ℝ) (hx : Monotone x) :
    ∑ i : Fin N, eVariationOn f (Icc (x i.castSucc) (x i.succ)) ≤ eVariationOn f univ := by
  let y : ℕ → ℝ := fun n => x ⟨min n N,by omega⟩
  have hy : Monotone y := fun i j hij => hx (by
    show min i N ≤ min j N
    exact min_le_min_right N hij)
  have he : ∑ i : Fin N, eVariationOn f (Icc (x i.castSucc) (x i.succ)) =
      ∑ i ∈ Finset.range N, eVariationOn f (Icc (y i) (y (i+1))) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hi := i.isLt
    congr 3 <;> apply Fin.ext <;> dsimp [y] <;> omega
  rw [he,eVariationOn.sum' f hy]
  exact eVariationOn.mono f (subset_univ _)

end PlanarHalving.RankCoordinates
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
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates
open scoped ENNReal
variable {R n k a : ℕ} {P : Fin n → Point}

lemma ConvexPath.x_monotone (C : ConvexPath R) : Monotone (fun i => (C.point i).1) := by
  intro i j hij
  apply fin_between_le i j hij
  intro b _ _
  rcases C.right b with he | he
  · exact le_of_eq (congrArg Prod.fst he)
  · exact he.le

lemma segment_fst_mem {p q z : Point} (hpq : p.1 ≤ q.1)
    (hz : z∈segment ℝ p q) : z.1∈Icc p.1 q.1 := by
  rw [segment_eq_image] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  simp only [Prod.fst_add,Prod.smul_fst,smul_eq_mul,mem_Icc]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hpq) ht.1,
    mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr ht.2)]

lemma ConvexPath.sum_rank_oscillation (C : ConvexPath R) {l u : ℝ}
    (hsl : ∀ b : Fin R, C.point b.castSucc ≠ C.point b.succ →
      l ≤ slope (C.point b.castSucc) (C.point b.succ) ∧
      slope (C.point b.castSucc) (C.point b.succ) ≤ u)
    {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {ε : ℝ} (hε : 0 < ε) :
    ∑ b : Fin R, Metric.ediam ((fun z => smoothed g ε (-z)) ''
      segment ℝ (C.point b.castSucc) (C.point b.succ))  ≤  2 := by
  let f := C.extension l u
  let g' : Fin m → ℝ → ℝ := fun j x => g j (-x)
  let F : ℝ → ℝ := fun x => smoothed g' ε (x,-f x)
  have hg' (j : Fin m) : ConvexOn ℝ univ (g' j) := by
    simpa only [Set.preimage_univ,Function.comp_def,LinearMap.neg_apply,LinearMap.id_apply]
      using (hg j).comp_linearMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hf : ConcaveOn ℝ univ (fun x => -f x) :=
    (convexOn_envelope (C.extensionSlopes l u) (C.extensionIntercepts l u)).neg
  have hF : eVariationOn F univ ≤ 2 := smoothed_eVariation hm g' hg' hf hε
  have hpiece (b : Fin R) :
      Metric.ediam ((fun z => smoothed g ε (-z)) ''
        segment ℝ (C.point b.castSucc) (C.point b.succ))  ≤
      eVariationOn F (Icc (C.point b.castSucc).1 (C.point b.succ).1) := by
    by_cases hb : C.point b.castSucc=C.point b.succ
    · simp only [hb,segment_same,image_singleton,Metric.ediam_singleton]
      exact zero_le
    · apply Metric.ediam_image_le_iff.mpr
      intro z hz w hw
      have hz' := C.extension_edge hsl b hb hz
      have hw' := C.extension_edge hsl b hb hw
      have hze : smoothed g ε (-z)=F z.1 := by
        dsimp [F,f,g',smoothed]
        rw [hz']
      have hwe : smoothed g ε (-w)=F w.1 := by
        dsimp [F,f,g',smoothed]
        rw [hw']
      rw [hze,hwe]
      exact eVariationOn.edist_le F (segment_fst_mem (C.x_monotone (Fin.castSucc_le_succ b)) hz)
        (segment_fst_mem (C.x_monotone (Fin.castSucc_le_succ b)) hw)
  exact (Finset.sum_le_sum (fun b _ => hpiece b)).trans
    ((sum_interval_eVariation (fun i => (C.point i).1) C.x_monotone).trans hF)

lemma System.sum_edges_le_paths (S : @System n R k a P) [NeZero a]
    (W : Point → Point → ℝ≥0∞) (hpath : ∀ j : Fin a, ∀ u : ↥(S.marks 0),
      ∑ b : Fin R, W ((S.tokenPath j u).point b.castSucc)
        ((S.tokenPath j u).point b.succ) ≤ 2) :
    ∑ e : ↥S.edges, W (P e.val.1) (P e.val.2)  ≤  2*a*n := by
  classical
  let ι := Fin a × (↥(S.marks 0) × Fin R)
  let T (e : ↥S.edges) := S.trace e.property
  let tag : ↥S.edges → ι := fun e => ((T e).number,((T e).token,(T e).batch))
  let w : ι → ℝ≥0∞ := fun i => W ((S.tokenPath i.1 i.2.1).point i.2.2.castSucc)
    ((S.tokenPath i.1 i.2.1).point i.2.2.succ)
  have ht : Function.Injective tag := by
    intro e f h
    have hn := congrArg Prod.fst h
    have hu := congrArg (fun i : ι => i.2.1) h
    have hb := congrArg (fun i : ι => i.2.2) h
    dsimp only [tag] at hn hu hb
    apply Subtype.ext
    apply Prod.ext
    · rw [← (T e).source,←(T f).source]
      rw [hn,hu,hb]
    · rw [← (T e).target,←(T f).target]
      rw [hn,hu,hb]
  have hw (e : ↥S.edges) : W (P e.val.1) (P e.val.2)=w (tag e) := by
    dsimp [w,tag,System.tokenPath]
    rw [(T e).source,(T e).target]
  calc
    _ = ∑ e : ↥S.edges, w (tag e) := Fintype.sum_congr _ _ hw
    _ = ∑ i ∈ Finset.univ.image tag, w i := (Finset.sum_image (fun _ _ _ _ h => ht h)).symm
    _  ≤  ∑ i : ι, w i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ j : Fin a, ∑ u : ↥(S.marks 0), ∑ b : Fin R,
        W ((S.tokenPath j u).point b.castSucc) ((S.tokenPath j u).point b.succ) := by
      dsimp only [ι]
      simp only [Fintype.sum_prod_type,w]
    _  ≤  ∑ _j : Fin a, ∑ _u : ↥(S.marks 0), (2 : ℝ≥0∞) := by
      gcongr with j u
      exact hpath j u
    _ = 2*a*(S.marks 0).card := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Fintype.card_coe,nsmul_eq_mul]
      ring
    _  ≤  2*a*n := by
      have hc : (S.marks 0).card ≤ n := (S.marks 0).card_le_univ.trans (by simp)
      gcongr

theorem System.rank_oscillation (S : @System n R k a P) [NeZero a]
    {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ → ℝ)
    (hg : ∀ j, ConvexOn ℝ univ (g j)) {ε : ℝ} (hε : 0 < ε) :
    ∑ e : ↥S.edges, Metric.ediam (smoothed g ε '' segment ℝ (P e.val.1) (P e.val.2))  ≤  2*a*n := by
  classical
  let W : Point → Point → ℝ≥0∞ := fun p q =>
    Metric.ediam ((fun z => smoothed g ε (-z)) '' segment ℝ p q)
  have hp (j : Fin a) (v : ↥(S.flip.marks 0)) :
      ∑ b : Fin R, W ((S.flip.tokenPath j v).point b.castSucc)
        ((S.flip.tokenPath j v).point b.succ) ≤ 2 := by
    apply (S.flip.tokenPath j v).sum_rank_oscillation
      (l := S.slope 0) (u := S.slope (Fin.last R)) _ hm g hg hε
    intro b hb
    exact ⟨(S.flip.tokenPath_bounds j v b hb).1.le,(S.flip.tokenPath_bounds j v b hb).2.le⟩
  have hb := S.flip.sum_edges_le_paths W hp
  let e : ↥S.edges ≃ ↥S.flip.edges :=
    { toFun := fun e => ⟨e.val.swap,(S.flip_edge _).mpr e.property⟩
      invFun := fun e => ⟨e.val.swap,(S.flip_edge _).mp (by simp only [Prod.swap_swap]; exact e.property)⟩
      left_inv := by intro x; apply Subtype.ext; exact Prod.swap_swap _
      right_inv := by intro x; apply Subtype.ext; exact Prod.swap_swap _ }
  have hsum : (∑ v : ↥S.edges, Metric.ediam (smoothed g ε '' segment ℝ (P v.val.1) (P v.val.2))) =
      ∑ v : ↥S.flip.edges, W (-P v.val.1) (-P v.val.2) := by
    apply Fintype.sum_equiv e
    intro v
    change Metric.ediam (smoothed g ε '' segment ℝ (P v.val.1) (P v.val.2)) =
      Metric.ediam ((fun z => smoothed g ε (-z)) '' segment ℝ (-P v.val.2) (-P v.val.1))
    have hseg : (fun z : Point => -z) '' segment ℝ (-P v.val.2) (-P v.val.1) =
        segment ℝ (P v.val.2) (P v.val.1) := by
      simpa using image_segment ℝ ((-LinearMap.id : Point →ₗ[ℝ] Point).toAffineMap)
        (-P v.val.2) (-P v.val.1)
    congr 1
    calc
      _ = smoothed g ε '' ((fun z : Point => -z) '' segment ℝ (-P v.val.2) (-P v.val.1)) := by
        rw [hseg,segment_symm]
      _ = _ := Set.image_image _ _ _
  rw [hsum]
  exact hb

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

namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.coordinate_oscillation (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) :
    ∑ e : ↥S.edges, Metric.ediam ((fun p => S.labels hP p J) '' segment ℝ (P e.val.1) (P e.val.2))
      ≤ 2*a*n := by
  have hh := S.rank_oscillation (Nat.mul_pos (NeZero.pos a) (NeZero.pos n))
    (S.rankFamily hP J).graph (S.rankFamily hP J).convex (S.rankFamily hP J).scale_pos
  convert hh using 1
  apply Finset.sum_congr rfl
  intro e _
  exact (Isometry.ediam_image (isometry_subtype_coe : Isometry (Subtype.val : I → ℝ)) _).symm.trans
    (by rw [Set.image_image]; rfl)

end PlanarHalving.Batches
namespace PlanarHalving.CompactLabels
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal PiCountable unitInterval
variable {ι : Type*} [Encodable ι]

lemma ediam_le_finite {X : Type*} (z : X → (ι → I)) (A : Set X) (K : Finset ι) :
    Metric.ediam (z '' A) ≤ (∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A))+
      ∑' i : {j // j ∉ K}, (2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι) := by
  apply Metric.ediam_le
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  calc
    edist (z x) (z y) = ∑' i : ι, min ((2 : ℝ≥0∞)⁻¹ ^ Encodable.encode i) (edist (z x i) (z y i)) := rfl
    _ = (∑ i ∈ K, min ((2 : ℝ≥0∞)⁻¹ ^ Encodable.encode i) (edist (z x i) (z y i)))+
        ∑' i : {j // j ∉ K}, min ((2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι)) (edist (z x i) (z y i)) :=
      (ENNReal.sum_add_tsum_compl ..).symm
    _ ≤ _ := by
      gcongr
      · exact (min_le_right ..).trans (Metric.edist_le_ediam_of_mem ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩)
      · exact min_le_left ..

lemma finite_tail {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ K : Finset ι, ∑' i : {j // j ∉ K}, (2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι) < ρ/2 := by
  exact ((tendsto_order.1 <| ENNReal.tendsto_tsum_compl_atTop_zero
    (tsum_geometric_encode_lt_top ENNReal.one_half_lt_one).ne).2 _
      <| by simpa using hρ.ne').exists

lemma long_count_bound {X α : Type*} [Fintype α] (z : X → (ι → I)) (A : α → Set X)
    {ρ : ℝ≥0∞} (_hρ : 0 < ρ) (K : Finset ι)
    (hK : ∑' i : {j // j ∉ K}, (2 : ℝ≥0∞)⁻¹ ^ Encodable.encode (i : ι) < ρ/2)
    {B : ℝ≥0∞} (hB : ∀ i, ∑ e : α, Metric.ediam ((fun x => z x i) '' A e) ≤ B) :
    (ρ/2) * ((Finset.univ.filter (fun e : α => ρ ≤ Metric.ediam (z '' A e))).card : ℝ≥0∞)
      ≤ K.card*B := by
  classical
  let E := Finset.univ.filter (fun e : α => ρ ≤ Metric.ediam (z '' A e))
  have he (e : α) (he : e ∈ E) : ρ/2 ≤ ∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A e) := by
    by_contra hh
    have hh' := lt_of_not_ge hh
    have hlt := ENNReal.add_lt_add hh' hK
    rw [ENNReal.add_halves] at hlt
    exact not_lt_of_ge (Finset.mem_filter.mp he).2
      ((ediam_le_finite z (A e) K).trans_lt hlt)
  calc
    _ = ∑ _e ∈ E, ρ/2 := by simp only [Finset.sum_const,nsmul_eq_mul]; rw [mul_comm]
    _ ≤ ∑ e ∈ E, ∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A e) := Finset.sum_le_sum he
    _ ≤ ∑ e : α, ∑ i ∈ K, Metric.ediam ((fun x => z x i) '' A e) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset ..)
    _ = ∑ i ∈ K, ∑ e : α, Metric.ediam ((fun x => z x i) '' A e) := Finset.sum_comm
    _ ≤ ∑ _i ∈ K, B := Finset.sum_le_sum (fun i _ => hB i)
    _ = K.card*B := by simp

end PlanarHalving.CompactLabels
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows MeasureTheory Limits
open scoped unitInterval NNReal ENNReal
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.timeWindow_disjoint (S : @System n R k a P) [NeZero R] [NeZero a]
    {A B : Window} (hAB : Before A B) :
    Disjoint (S.timeWindow A).edges (S.timeWindow B).edges := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heA heB
  let v : ↥S.edges := ⟨e,S.timeWindow_edges A heA⟩
  have hA := (mem_carrier_iff R A (S.trace v.property).batch).mp ((S.timeWindow_mem A v).mp heA)
  have hB := (mem_carrier_iff R B (S.trace v.property).batch).mp ((S.timeWindow_mem B v).mp heB)
  have hh := stop_le_start R hAB
  omega

lemma System.windowCrossPoint_injective (S : @System n R k a P) [NeZero R]
    (hP : Generic P) (A B : Window) : Function.Injective (S.windowCrossPoint A B) := by
  intro w v h
  apply Subtype.ext
  exact congrArg (fun v : ↥S.drawing.crossings => v.val)
    (S.drawing.crossingPoint_injective (S.drawing.noMultiple_of_generic hP) h)

lemma System.windowCrossPoint_exterior (S : @System n R k a P) [NeZero R] [NeZero a]
    {A B : Window} (hAB : Before A B) (w : ↥(S.windowCrossings A B)) :
    S.windowCrossPoint A B w ∈ S.drawing.exteriorCrossings (S.timeWindow A).edges ∧
    S.windowCrossPoint A B w ∈ S.drawing.exteriorCrossings (S.timeWindow B).edges := by
  classical
  let v : ↥S.drawing.crossings := ⟨w.val,S.windowCrossings_sub A B w.property⟩
  have hw := (Finset.mem_filter.mp w.property).2
  have hd := Finset.disjoint_left.mp (S.timeWindow_disjoint hAB)
  have hA : (v.val.1 ∈ (S.timeWindow A).edges ∧ v.val.2 ∉ (S.timeWindow A).edges) ∨
      (v.val.2 ∈ (S.timeWindow A).edges ∧ v.val.1 ∉ (S.timeWindow A).edges) := by
    rcases hw with hw | hw
    · exact Or.inl ⟨hw.1,fun hh => hd hh hw.2⟩
    · exact Or.inr ⟨hw.1,fun hh => hd hh hw.2⟩
  have hB : (v.val.1 ∈ (S.timeWindow B).edges ∧ v.val.2 ∉ (S.timeWindow B).edges) ∨
      (v.val.2 ∈ (S.timeWindow B).edges ∧ v.val.1 ∉ (S.timeWindow B).edges) := by
    rcases hw with hw | hw
    · exact Or.inr ⟨hw.2,hd hw.1⟩
    · exact Or.inl ⟨hw.2,hd hw.1⟩
  exact ⟨Finset.mem_image.mpr ⟨v,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hA,rfl⟩,
    Finset.mem_image.mpr ⟨v,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hB,rfl⟩⟩

lemma System.windowCrossPoint_graph (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    {A B : Window} (w : ↥(S.windowCrossings A B))
    {F H : Finset Point} (G : (S.timeWindow A).FullGraphs F) (G' : (S.timeWindow B).FullGraphs H) :
    (∃ i, G.graph i (S.windowCrossPoint A B w).1 = (S.windowCrossPoint A B w).2) ∧
    ∃ j, G'.graph j (S.windowCrossPoint A B w).1 = (S.windowCrossPoint A B w).2 := by
  classical
  let v : ↥S.drawing.crossings := ⟨w.val,S.windowCrossings_sub A B w.property⟩
  have hm := S.drawing.crossingPoint_mem v
  have hw := (Finset.mem_filter.mp w.property).2
  rcases hw with hw | hw
  · exact ⟨⟨_,G.edge _ hw.1 _ (openSegment_subset_segment ℝ _ _ hm.1)⟩,
      ⟨_,G'.edge _ hw.2 _ (openSegment_subset_segment ℝ _ _ hm.2)⟩⟩
  · exact ⟨⟨_,G.edge _ hw.1 _ (openSegment_subset_segment ℝ _ _ hm.2)⟩,
      ⟨_,G'.edge _ hw.2 _ (openSegment_subset_segment ℝ _ _ hm.1)⟩⟩

theorem System.window_crossing_slots (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) :
    ∃ slots : ↥(S.windowCrossings A B) → Fin (a*n) × Fin (a*n),
      Function.Injective slots ∧ ∀ w,
        dist (S.labels hP (S.windowCrossPoint A B w) A,S.labels hP (S.windowCrossPoint A B w) B)
          (UniformPartition.gridPoint (a*n) (slots w)) ≤ 2/(a*n : ℕ) := by
  classical
  obtain ⟨G,hG,hGE⟩ := S.rankFamily_spec hP A hA
  obtain ⟨H,hH,hHE⟩ := S.rankFamily_spec hP B hB
  let pt := S.windowCrossPoint A B
  have hinc (w : ↥(S.windowCrossings A B)) := S.windowCrossPoint_graph w G H
  let slots : ↥(S.windowCrossings A B) → Fin (a*n) × Fin (a*n) := fun w =>
    (⟨slot G.graph (pt w),by simpa using slot_lt_card G.graph (hinc w).1⟩,
      ⟨slot H.graph (pt w),by simpa using slot_lt_card H.graph (hinc w).2⟩)
  refine ⟨slots,?_,?_⟩
  · intro u v huv
    apply S.windowCrossPoint_injective hP A B
    apply pair_slots_injOn G.graph H.graph G.slopes H.slopes (S.timeWindow_graph_gap hAB G H)
      (range pt) (by rintro _ ⟨w,rfl⟩; exact hinc w) (mem_range_self u) (mem_range_self v)
    exact congrArg (fun p : Fin (a*n) × Fin (a*n) => (p.1.val,p.2.val)) huv
  · intro w
    rw [Prod.dist_eq,max_le_iff]
    have hext := S.windowCrossPoint_exterior hAB w
    constructor
    · change |(S.rankFamily hP A).value (pt w)-(slot G.graph (pt w) : ℝ)/(a*n : ℕ)| ≤ _
      simpa only [Nat.cast_mul] using hGE _ hext.1
    · change |(S.rankFamily hP B).value (pt w)-(slot H.graph (pt w) : ℝ)/(a*n : ℕ)| ≤ _
      simpa only [Nat.cast_mul] using hHE _ hext.2

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
open MeasureTheory Set Filter Limits
open scoped Topology NNReal ENNReal unitInterval

lemma normalized_perturbed_fintype_sum_le {m : ℕ} [NeZero m] {α : Type*} [Fintype α]
    (slots : α → Fin m × Fin m) (hs : Function.Injective slots)
    (x : α → I × I) (f : I × I → ℝ) (hf : ∀ t, 0 ≤ f t)
    {ε : ℝ} (hε : 0 ≤ ε) (hclose : ∀ i, f (x i) ≤ f (gridPoint m (slots i)) + ε) :
    (∑ i, f (x i))/(m : ℝ)^2 ≤
      (∑ j : Fin m × Fin m, f (gridPoint m j))/(m : ℝ)^2 + ε := by
  let e := (Fintype.equivFin α).symm
  have hh := normalized_perturbed_sum_le (slots ∘ e) (hs.comp e.injective)
    (x ∘ e) f hf hε (fun i => hclose (e i))
  have he : (∑ i, f (x (e i)))=∑ i, f (x i) := Equiv.sum_comp e (fun i => f (x i))
  simpa only [Function.comp_apply,he] using hh

lemma perturbed_fintype_grid_limit (m : ℕ → ℕ) [∀ n, NeZero (m n)]
    (hm : Tendsto m atTop atTop) {α : ℕ → Type*} [∀ n, Fintype (α n)]
    (x : ∀ n, α n → I × I) (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0))
    (hslots : ∀ᶠ n in atTop, ∃ slots : α n → Fin (m n) × Fin (m n),
      Function.Injective slots ∧ ∀ i, dist (x n i) (gridPoint (m n) (slots i)) ≤ d n)
    (μ : FiniteMeasure (I × I))
    (hμ : Tendsto (fun n => weightedAtoms ((m n : ℝ≥0)^2)⁻¹ (x n)) atTop (𝓝 μ)) :
    (μ : Measure (I × I)) ≤ volume := by
  let ν : FiniteMeasure (I × I) := ⟨volume,inferInstance⟩
  apply measure_le_of_test μ ν
  intro f hf
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ,hδ,hfδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  have hdδ : ∀ᶠ n in atTop, d n < δ := (tendsto_order.mp hd).2 δ hδ
  have hineq : ∀ᶠ n in atTop,
      ∫ t, f t ∂(weightedAtoms ((m n : ℝ≥0)^2)⁻¹ (x n) : Measure (I × I)) ≤
        (∑ j : Fin (m n) × Fin (m n), f (gridPoint (m n) j))/(m n : ℝ)^2 + ε := by
    filter_upwards [hdδ,hslots] with n hn hs
    obtain ⟨slots,hs,hclose⟩ := hs
    rw [integral_weightedAtoms]
    simp only [NNReal.coe_inv,NNReal.coe_pow,NNReal.coe_natCast]
    rw [← div_eq_inv_mul]
    apply normalized_perturbed_fintype_sum_le slots hs (x n) f hf hε.le
    intro i
    have h := hfδ ((hclose i).trans_lt hn)
    rw [Real.dist_eq,abs_lt] at h
    linarith [h.2]
  have hlim := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) f
  have hgrid := (riemann_tendsto m hm f).add_const ε
  exact le_of_tendsto_of_tendsto hlim hgrid hineq

end PlanarHalving.UniformPartition
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Converges.crossing_projection {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {A B : Window} (hAB : Before A B) :
    ((L.crossings A B).map (fun z => (z A,z B)) : Measure (I × I)) ≤ volume := by
  let m := fun n => (F n).a*(F n).n
  let x := fun n w => ((F n).label ((F n).system.windowCrossPoint A B w) A,
    (F n).label ((F n).system.windowCrossPoint A B w) B)
  have hd : Tendsto (fun n => 2/(m n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hM)
  have hs : ∀ᶠ n in atTop, ∃ slots : _ → Fin (m n) × Fin (m n),
      Function.Injective slots ∧ ∀ w, dist (x n w) (UniformPartition.gridPoint (m n) (slots w)) ≤ 2/(m n : ℝ) := by
    filter_upwards [eventually_length_pos _ hR A,eventually_length_pos _ hR B] with n hA hB
    exact (F n).system.window_crossing_slots (F n).generic hAB hA hB
  apply UniformPartition.perturbed_fintype_grid_limit m hM x _ hd hs
  have hc : Continuous (fun z : Labels => (z A,z B)) :=
    (continuous_apply A).prodMk (continuous_apply B)
  have hh := (FiniteMeasure.continuous_map hc).tendsto (L.crossings A B) |>.comp (h.crossings A B)
  convert hh using 1
  funext n
  exact (map_weightedAtoms _ _ hc.measurable).symm

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

lemma Configuration.window_cubed_bound (F : Configuration) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (F.edgeWindow J U : ℝ)^3 ≤
      (4608 * (F.a : ℝ)^2 * F.n^4 / ((F.R : ℝ)*F.a^2)^3) *
        ((F.vertices J).mass : ℝ)^3 * (F.vertices J U : ℝ) +
      13824 * ((F.system.timeWindow J).vertices.card : ℝ)^3 / ((F.R : ℝ)*F.a^2)^3 := by
  rw [F.edgeWindow_eq,F.vertices_mass_ratio]
  have hR : 0 < (F.R : ℝ≥0) := Nat.cast_pos.mpr F.R_pos
  have ha : 0 < (F.a : ℝ≥0) := Nat.cast_pos.mpr F.a_pos
  exact (F.system.timeWindow J).atomic_cubed_bound F.generic _ (by positivity) hU

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
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Configuration.vertices_le_points (F : Configuration) (J : Window) :
    (F.vertices J : Measure Labels) ≤ (F.points : Measure Labels) := by
  classical
  apply Measure.le_iff.mpr
  intro U hU
  have he : (F.vertices J U : ℝ) ≤ (F.points U : ℝ) := by
    rw [Configuration.vertices,System.vertexMeasure_apply _ _ hU,
      Configuration.points,weightedAtoms_apply_finset _ _ hU]
    simp only [NNReal.coe_inv,NNReal.coe_natCast,div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
  simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    (ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp he))

lemma Converges.vertices_le_points {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (J : Window) : (L.vertices J : Measure Labels) ≤ (L.points : Measure Labels) :=
  measure_le_of_weak_limits (h.vertices J) h.points (fun n => (F n).vertices_le_points J)

lemma Converges.edgeWindow {F : ℕ → Configuration} {L : Data} (h : Converges F L) (J : Window) :
    Tendsto (fun n => (F n).edgeWindow J) atTop (𝓝 (L.edgeWindow J)) :=
  (FiniteMeasure.continuous_map continuous_fst).tendsto _ |>.comp (h.timeRestrict J)

lemma Converges.local_cubic {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4 /
      (((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3 /
      (((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) {U : Set Labels} (hU : MeasurableSet U) :
    (L.edgeWindow J U : ℝ)^3 ≤ C*((L.vertices J).mass : ℝ)^3*(L.vertices J U : ℝ) := by
  have hm : Tendsto (fun n => ((F n).vertices J).mass) atTop (𝓝 ((L.vertices J).mass)) :=
    FiniteMeasure.continuous_mass.tendsto _ |>.comp (h.vertices J)
  have hmR := NNReal.continuous_coe.tendsto _ |>.comp hm
  apply cubed_bound_limit (h.vertices J) (h.edgeWindow J)
    (mul_nonneg hC (pow_nonneg (NNReal.coe_nonneg _) _))
    ((hmR.pow 3).const_mul C) herror
  intro n V hV
  apply ((F n).window_cubed_bound J hV).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcoeff n) (pow_nonneg (NNReal.coe_nonneg _) _))
      (NNReal.coe_nonneg _)
  · apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 3
    exact_mod_cast (show ((F n).system.timeWindow J).vertices.card ≤ (F n).n by
      simpa only [Fintype.card_fin] using ((F n).system.timeWindow J).vertices.card_le_univ)
  exact hU

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

lemma Data.edge_toMeasure (L : Data) : (L.edge : Measure Labels)=(L.edgeTime : Measure (Labels×I)).fst := by
  rw [Data.edge,FiniteMeasure.toMeasure_map]
  rfl

lemma Data.conditional_measurable (L : Data) (J : Window) :
    Measurable (fun z => (L.conditional z).real (carrier J)) :=
  (L.conditional.measurable_coe (measurable_carrier J)).ennreal_toReal

lemma Converges.conditional_integral {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window)
    {U : Set Labels} (hU : MeasurableSet U) :
    (L.edgeWindow J U : ℝ)=∫ z in U, (L.conditional z).real (carrier J) ∂(L.edge : Measure Labels) := by
  have hi := Measure.setIntegral_condKernel (ρ:=(L.edgeTime : Measure (Labels×I)))
    (f:=fun _ => (1:ℝ)) hU (measurable_carrier J) (integrable_const 1)
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul,mul_one] at hi
  rw [L.edge_toMeasure]
  change (L.edgeWindow J U : ℝ)=∫ z in U, ((L.edgeTime : Measure (Labels×I)).condKernel z).real (carrier J)
    ∂(L.edgeTime : Measure (Labels×I)).fst
  rw [hi]
  change ((L.edgeWindow J : Measure Labels) U).toReal= _
  rw [Data.edgeWindow,FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hU,
    h.restriction_eq hR,Measure.restrict_apply (hU.preimage measurable_fst)]
  rfl

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

lemma Data.conditional_le_one (L : Data) (J : Window) (z : Labels) :
    (L.conditional z).real (carrier J)≤1 := by
  exact (measureReal_mono (subset_univ _)).trans_eq (by simp)

lemma Data.conditional_sum (L : Data) (m : ℕ) (z : Labels) :
    ∑ i : Fin (2^m), (L.conditional z).real (carrier ⟨m,i⟩)=1 := by
  have he : (⋃ i : Fin (2^m),carrier ⟨m,i⟩)=univ := UniformPartition.cells_cover (2^m)
  have hd : Pairwise (fun (i j : Fin (2^m)) => Disjoint (carrier ⟨m,i⟩) (carrier ⟨m,j⟩)) :=
    UniformPartition.cells_disjoint (2^m)
  rw [← measureReal_iUnion_fintype hd (fun i => measurable_carrier ⟨m,i⟩),he]
  simp

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

lemma timePartition_card (m : ℕ) : (timePartition m).card=2^m := by
  classical
  rw [timePartition,Finset.card_image_of_injective _ (fun _ _ he => eq_of_heq (Sigma.mk.inj he).2),Finset.card_univ,Fintype.card_fin]

lemma timePartition_cover (m : ℕ) (t : I) : ∃ J∈timePartition m, t∈carrier J := by
  have ht : t∈⋃ i : Fin (2^m),carrier ⟨m,i⟩ := by
    change t∈⋃ i : Fin (2^m), UniformPartition.cell (2^m) i
    rw [UniformPartition.cells_cover];trivial
  obtain ⟨i,hi⟩ := mem_iUnion.mp ht
  exact ⟨⟨m,i⟩,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩

lemma sum_timePartition {M : Type*} [AddCommMonoid M] (m : ℕ) (f : Window → M) :
    ∑ J∈timePartition m, f J = ∑ i : Fin (2^m), f ⟨m,i⟩ := by
  classical
  exact Finset.sum_image (fun _ _ _ _ he => eq_of_heq (Sigma.mk.inj he).2)

lemma filter_timePartition (m : ℕ) (p : Window → Prop) [DecidablePred p] :
    (timePartition m |>.filter p).card = (Finset.univ.filter fun i : Fin (2^m) => p ⟨m,i⟩).card := by
  classical
  rw [timePartition,Finset.filter_image,Finset.card_image_of_injective _ (fun _ _ he => eq_of_heq (Sigma.mk.inj he).2)]

lemma Converges.conditional_nullSingleton {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4 /
      (((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3 /
      (((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0)) :
    ∀ᵐ z ∂(L.edge : Measure Labels), NullSingletonClass (L.conditional z) := by
  classical
  apply kernel_nullSingleton_of_cells (L.edge : Measure Labels) L.conditional timePartition
    (fun _ J => carrier J) timePartition_cover
  intro b
  apply ae_exists_partition_small L.edge L.points timePartition
    (fun _ J z => (L.conditional z).real (carrier J)) (fun _ => L.vertices) (fun _ => L.edgeWindow)
    (fun _ J => ((L.vertices J).mass : ℝ)) (fun m => (2:ℝ)^m) hC
    (fun _ => by positivity) (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  · intro m
    rw [timePartition_card,Nat.cast_pow,Nat.cast_ofNat]
  · exact fun _ J _ => L.conditional_measurable J
  · exact fun _ _ _ _ => measureReal_nonneg
  · exact fun _ J _ => L.conditional_le_one J
  · intro m z
    rw [sum_timePartition,L.conditional_sum]
  · exact fun _ _ _ => NNReal.coe_nonneg _
  · intro _ J _ U
    have hh := (h.vertices_le_points J) U
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
    exact ENNReal.coe_le_coe.mp hh
  · exact fun _ J _ U hU => h.conditional_integral hR J hU
  · intro m J hJ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hJ
    rw [h.edgeWindow_mass hR,Nat.cast_pow,Nat.cast_ofNat]
  · exact fun _ J _ U hU => h.local_cubic hC hcoeff herror J hU
  · intro m u hu
    rw [filter_timePartition]
    exact h.activity_tail E m hu
  · positivity

end PlanarHalving.RankLimits
namespace PlanarHalving.PlaneGraph
open Set
variable {V : Type*} [Fintype V] {P : V → Point}

lemma Drawing.pointOfPair_eq (D : Drawing P) (w : ↥D.crossings) :
    D.pointOfPair w.val=D.crossingPoint w := by
  classical
  simp only [Drawing.pointOfPair,dite_eq_left w.property]

end PlanarHalving.PlaneGraph
namespace PlanarHalving.Batches
open Set PlaneGraph TimeWindows MeasureTheory Limits
open scoped NNReal ENNReal unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.restricted_crossing (S : @System n R k a P) (hP : Generic P)
    (E : Finset (Fin n×Fin n)) (hE : E⊆S.edges) :
    (E.card : ℝ)^3 ≤ 2304*(n : ℝ)^2*((S.drawing.restrictEdges E).crossings.card : ℝ)+13824*(n : ℝ)^3 := by
  classical
  let D := S.drawing.restrictEdges E
  have he : D.edges=E := by
    ext e
    simp only [D, Drawing.restrictEdges, Finset.mem_inter]
    exact ⟨And.right, fun h => ⟨hE h, h⟩⟩
  have hc := D.designated_crossing hP.1 (Generic.x_injective hP) D.vertices (by rfl)
    (fun e he => Or.inl (D.ends e he).1)
  have hv : (D.vertices.card : ℝ) ≤ n := Nat.cast_le.mpr S.vertices_le
  rw [he] at hc
  apply hc.trans
  nlinarith [mul_le_mul_of_nonneg_right (sq_le_sq₀ (by positivity) (by positivity) |>.mpr hv)
    (by positivity : (0:ℝ) ≤ 2304*((D.crossings.card : ℝ))),
    pow_le_pow_left₀ (by positivity) hv 3]

lemma System.windowCrossMeasure_apply (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Point → X) {U : Set X} (hU : MeasurableSet U) :
    (S.windowCrossMeasure A B z U : ℝ)=(S.crossingsIn A B z U).card/((a*n : ℕ) : ℝ)^2 := by
  classical
  rw [System.windowCrossMeasure,weightedAtoms_apply_finset _ _ hU]
  have he : (Finset.univ.filter (fun w : ↥(S.windowCrossings A B) => z (S.windowCrossPoint A B w)∈U)).card=
      (S.crossingsIn A B z U).card := by
    rw [← Finset.card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext w
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,System.crossingsIn]
    constructor
    · rintro ⟨v,hv,rfl⟩
      refine ⟨v.property,?_⟩
      simpa only [System.windowCrossPoint,Drawing.pointOfPair,
        dite_eq_left (S.windowCrossings_sub A B v.property)] using hv
    · rintro ⟨hw,hz⟩
      refine ⟨⟨w,hw⟩,?_,rfl⟩
      simpa only [System.windowCrossPoint,Drawing.pointOfPair,
        dite_eq_left (S.windowCrossings_sub A B hw)] using hz
  rw [he]
  simp only [NNReal.coe_inv,NNReal.coe_pow,NNReal.coe_natCast,div_eq_inv_mul]

lemma System.retained_crossing_cover (S : @System n R k a P) [NeZero R]
    {X : Type*} (z : Point → X) (U : Set X) (W : Finset Window)
    (E : Finset (Fin n×Fin n)) (_hE : E⊆S.edges)
    (hcover : ∀ e∈E, ∃ J∈W, e∈(S.timeWindow J).edges)
    (hnear : ∀ e∈E, ∀ p∈segment ℝ (P e.1) (P e.2), z p∈U) :
    (S.drawing.restrictEdges E).crossings ⊆ (W×ˢ W).biUnion
      (fun ij => if ij.1=ij.2 then (S.timeWindow ij.1).drawing.crossings
        else S.crossingsIn ij.1 ij.2 z U) := by
  classical
  intro w hw
  have hp := (S.drawing.restrictEdges E).crossing_props ⟨w,hw⟩
  have hep := hp
  simp only [Drawing.restrictEdges, Finset.mem_inter] at hep
  have he₁ := hep.1.2
  have he₂ := hep.2.1.2
  obtain ⟨J,hJ,heJ⟩ := hcover w.1 he₁
  obtain ⟨K,hK,heK⟩ := hcover w.2 he₂
  apply Finset.mem_biUnion.mpr
  refine ⟨(J,K),Finset.mem_product.mpr ⟨hJ,hK⟩,?_⟩
  dsimp only
  by_cases hJK : J=K
  · rw [ite_eq_left hJK]
    rw [← hJK] at heK
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heJ,heK⟩,hp.2.2⟩
  · rw [ite_eq_right hJK]
    have hc : w∈S.drawing.crossings := S.drawing.restrict_crossings E hw
    have hz : z (S.drawing.pointOfPair w)∈U := by
      rw [show S.drawing.pointOfPair w=S.drawing.crossingPoint ⟨w,hc⟩ from S.drawing.pointOfPair_eq ⟨w,hc⟩]
      exact hnear _ he₁ _ ((openSegment_subset_segment ℝ _ _) (S.drawing.crossingPoint_mem ⟨w,hc⟩).1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hc,Or.inl ⟨heJ,heK⟩⟩,hz⟩

lemma System.retained_crossing_bound (S : @System n R k a P) [NeZero R] [NeZero n] [NeZero a]
    (hP : Generic P) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Point → X) {U : Set X} (hU : MeasurableSet U) (W : Finset Window)
    (E : Finset (Fin n×Fin n)) (hE : E⊆S.edges)
    (hcover : ∀ e∈E, ∃ J∈W, e∈(S.timeWindow J).edges)
    (hnear : ∀ e∈E, ∀ p∈segment ℝ (P e.1) (P e.2), z p∈U) :
    (((S.drawing.restrictEdges E).crossings.card : ℝ)/((a*n : ℕ) : ℝ)^2)  ≤
      ∑ J∈W, ∑ K∈W, if J=K then 2*((S.timeWindow J).vertices.card : ℝ)^2/(n : ℝ)^2
        else (S.windowCrossMeasure J K z U : ℝ) := by
  classical
  have hc := (Finset.card_le_card (S.retained_crossing_cover z U W E hE hcover hnear)).trans
    (Finset.card_biUnion_le)
  have hh : ((S.drawing.restrictEdges E).crossings.card : ℝ) ≤
      ∑ ij∈W×ˢ W, if ij.1=ij.2 then 2*(a : ℝ)^2*((S.timeWindow ij.1).vertices.card : ℝ)^2
        else ((S.crossingsIn ij.1 ij.2 z U).card : ℝ) := by
    apply (Nat.cast_le.mpr hc).trans
    push_cast
    apply Finset.sum_le_sum
    intro ij _hij
    split_ifs with he
    · exact_mod_cast (S.timeWindow ij.1).crossing_cap hP.1 (Generic.x_injective hP)
        ((S.timeWindow ij.1).drawing.noMultiple_of_generic hP)
    · rfl
  apply (div_le_div_of_nonneg_right hh (sq_nonneg _)).trans_eq
  rw [Finset.sum_div,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro J _hJ
  apply Finset.sum_congr rfl
  intro K _hK
  split_ifs
  · have ha : (a : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne a)
    push_cast
    field_simp
  · exact (S.windowCrossMeasure_apply J K z hU).symm

end PlanarHalving.Batches

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
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Configuration.longEdges_bound {ρ : ℝ} (hρ : 0<ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Configuration, ((F.longEdges ρ).card : ℝ) ≤ C*(F.a : ℝ)*F.n := by
  classical
  obtain ⟨K,hK⟩ := CompactLabels.finite_tail (ι:=Window) (ENNReal.ofReal_pos.mpr hρ)
  refine ⟨4*K.card/ρ,by positivity,fun F => ?_⟩
  have hh := CompactLabels.long_count_bound F.label
    (fun e : ↥F.system.edges => segment ℝ (F.point e.val.1) (F.point e.val.2))
    (ENNReal.ofReal_pos.mpr hρ) K hK (fun J => F.system.coordinate_oscillation F.generic J)
  have hh' := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_ofReal hρ.le,
    ENNReal.toReal_ofNat,ENNReal.toReal_natCast] at hh'
  have hc : (Finset.univ.filter (fun e : ↥F.system.edges => ENNReal.ofReal ρ ≤ Metric.ediam
      (F.label '' segment ℝ (F.point e.val.1) (F.point e.val.2)))).card=(F.longEdges ρ).card :=
    by
      simpa only [Configuration.longEdges] using (card_filter_attached F.system.edges
        (fun e => ENNReal.ofReal ρ ≤ Metric.ediam (F.label '' segment ℝ (F.point e.1) (F.point e.2))))
  rw [hc] at hh'
  change ρ/2*((F.longEdges ρ).card : ℝ) ≤ (K.card : ℝ)*(2*(F.a : ℝ)*F.n) at hh'
  calc
    _  ≤  4*(K.card : ℝ)*F.a*F.n/ρ := (le_div_iff₀ hρ).mpr (by nlinarith [hh'])
    _ = _ := by ring

lemma longEdges_ratio_zero {F : ℕ → Configuration}
    (hratio : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    {ρ : ℝ} (hρ : 0<ρ) :
    Tendsto (fun n => (((F n).longEdges ρ).card : ℝ)/((F n).R*(F n).a^2)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := Configuration.longEdges_bound hρ
  have ht := hratio.const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro n
  have ha : (0:ℝ)<(F n).a := Nat.cast_pos.mpr (F n).a_pos
  have hR : (0:ℝ)<(F n).R := Nat.cast_pos.mpr (F n).R_pos
  apply (div_le_iff₀ (mul_pos hR (pow_pos ha 2))).mpr
  have hh := hbound (F n)
  calc
    _  ≤  C*(F n).a*(F n).n := hh
    _ = _ := by field_simp

lemma Configuration.short_edge_label {F : Configuration} {ρ : ℝ}
    {e : Fin F.n×Fin F.n} (he : e∈F.system.edges) (hshort : e∉F.longEdges ρ)
    {p : Point} (hp : p∈segment ℝ (F.point e.1) (F.point e.2)) :
    dist (F.label p) (F.label (F.point e.1))<ρ := by
  classical
  have hdiam : Metric.ediam (F.label '' segment ℝ (F.point e.1) (F.point e.2))<ENNReal.ofReal ρ := by
    have hh : ¬ ENNReal.ofReal ρ ≤ Metric.ediam (F.label '' segment ℝ (F.point e.1) (F.point e.2)) := by
      intro hh
      exact hshort (Finset.mem_filter.mpr ⟨he,hh⟩)
    exact lt_of_not_ge hh
  have hh : edist (F.label p) (F.label (F.point e.1))<ENNReal.ofReal ρ :=
    (Metric.edist_le_ediam_of_mem (s := F.label '' segment ℝ (F.point e.1) (F.point e.2))
      ⟨p,hp,rfl⟩ ⟨F.point e.1,left_mem_segment ℝ _ _,rfl⟩).trans_lt hdiam
  rw [edist_dist] at hh
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hh).1

end PlanarHalving.RankLimits
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

lemma eventually_thickening_lower [Nonempty X]
    {μ : FiniteMeasure X} {μs : ℕ → FiniteMeasure X}
    (h : Tendsto μs atTop (𝓝 μ)) (F : Set X) {r : ℝ} (hr : 0<r)
    {q : ℝ} (hq : q<(μ F : ℝ)) :
    ∀ᶠ n in atTop, q<(μs n (Metric.thickening r F) : ℝ) := by
  obtain ⟨s,hs,hnull⟩ := exists_null_frontiers_thickening (μ : Measure X) F
  obtain ⟨j,hj⟩ := ((tendsto_order.mp hs).2 r hr).exists
  have hlim := NNReal.continuous_coe.tendsto _ |>.comp
    (finiteMeasure_tendsto_apply h (hnull j).2)
  have hb : q<(μ (Metric.thickening (s j) F) : ℝ) :=
    hq.trans_le (NNReal.coe_le_coe.mpr (μ.apply_mono (Metric.self_subset_thickening (hnull j).1 _)))
  filter_upwards [(tendsto_order.mp hlim).1 q hb] with n hn
  exact hn.trans_le (NNReal.coe_le_coe.mpr (μs n |>.apply_mono (Metric.thickening_mono hj.le _)))

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

lemma Configuration.windows_edges_disjoint (F : Configuration) {A B : Window}
    (hAB : Disjoint (carrier A) (carrier B)) :
    Disjoint (F.system.timeWindow A).edges (F.system.timeWindow B).edges := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heA heB
  let v : ↥F.system.edges := ⟨e,F.system.timeWindow_edges A heA⟩
  exact Set.disjoint_left.mp hAB ((F.system.timeWindow_mem A v).mp heA)
    ((F.system.timeWindow_mem B v).mp heB)

lemma Configuration.selectedEdges_mass (F : Configuration) (W : Finset Window)
    (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    {U : Set Labels} (hU : MeasurableSet U) :
    ∑ J∈W, (F.edgeWindow J U : ℝ) =
      ((F.selectedEdges W U).card : ℝ)/((F.R : ℝ)*F.a^2) := by
  classical
  simp_rw [F.edgeWindow_apply _ hU]
  rw [← Finset.sum_div,Configuration.selectedEdges,Finset.card_biUnion]
  · push_cast; rfl
  · intro J hJ K hK hJK
    exact (F.windows_edges_disjoint (hW J hJ K hK hJK)).mono
      (Finset.filter_subset ..) (Finset.filter_subset ..)

lemma Configuration.selectedEdges_subset (F : Configuration) (W : Finset Window)
    (U : Set Labels) : F.selectedEdges W U⊆F.system.edges := by
  classical
  intro e he
  obtain ⟨J,_hJ,heJ⟩ := Finset.mem_biUnion.mp he
  exact F.system.timeWindow_edges J (Finset.mem_filter.mp heJ).1

lemma Configuration.retained_near (F : Configuration) (W : Finset Window)
    (A : Set Labels) {ρ : ℝ} (e : Fin F.n×Fin F.n)
    (he : e∈F.selectedEdges W (Metric.thickening ρ A) \ F.longEdges ρ)
    (p : Point) (hp : p∈segment ℝ (F.point e.1) (F.point e.2)) :
    F.label p∈Metric.cthickening (2*ρ) A := by
  classical
  obtain ⟨hes,hel⟩ := Finset.mem_sdiff.mp he
  obtain ⟨J,_hJ,heJ⟩ := Finset.mem_biUnion.mp hes
  obtain ⟨z,hz,hd⟩ := Metric.mem_thickening_iff.mp (Finset.mem_filter.mp heJ).2
  have hp' := F.short_edge_label (F.selectedEdges_subset W _ hes) hel hp
  exact Metric.mem_cthickening_of_dist_le _ z _ A hz
    (le_of_lt ((dist_triangle _ _ _).trans_lt (by linarith)))

lemma Configuration.retained_mass_lower (F : Configuration) (W : Finset Window)
    (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    {U : Set Labels} (hU : MeasurableSet U) (ρ : ℝ) :
    (∑ J∈W, (F.edgeWindow J U : ℝ)) -
        ((F.longEdges ρ).card : ℝ)/((F.R : ℝ)*F.a^2)  ≤
      ((F.selectedEdges W U \ F.longEdges ρ).card : ℝ)/((F.R : ℝ)*F.a^2) := by
  classical
  rw [F.selectedEdges_mass W hW hU,← sub_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh := Finset.card_le_card (show F.selectedEdges W U⊆
      (F.selectedEdges W U \ F.longEdges ρ)∪F.longEdges ρ from by
        intro e he; by_cases h : e∈F.longEdges ρ <;> simp [he,h])
  have hh' := hh.trans (Finset.card_union_le _ _)
  have hh'' : ((F.selectedEdges W U).card : ℝ) ≤
      ((F.selectedEdges W U \ F.longEdges ρ).card : ℝ)+(F.longEdges ρ).card := by
    exact_mod_cast hh'
  linarith

end PlanarHalving.RankLimits
namespace PlanarHalving.Limits
open Filter
open scoped Topology

lemma eventually_sum_lower {ι : Type*} (W : Finset ι) {f : ℕ → ι → ℝ} {a : ι → ℝ}
    (h : ∀ i∈W, ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, a i-ε ≤ f n i)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ n in atTop, (∑ i∈W, a i)-ε ≤ ∑ i∈W, f n i := by
  classical
  induction W using Finset.induction_on generalizing ε with
  | empty => exact Eventually.of_forall (fun _ => by simpa using hε.le)
  | @insert i W hi ih =>
    have h₁ := h i (Finset.mem_insert_self _ _) (ε/2) (by positivity)
    have h₂ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) (ε := ε/2) (half_pos hε)
    filter_upwards [h₁,h₂] with n hn hn'
    simp only [Finset.sum_insert hi]
    linarith

lemma eventually_sum_upper {ι : Type*} (W : Finset ι) {f : ℕ → ι → ℝ} {a : ι → ℝ}
    (h : ∀ i∈W, ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, f n i ≤ a i+ε)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ n in atTop, (∑ i∈W, f n i) ≤ (∑ i∈W, a i)+ε := by
  have hh := eventually_sum_lower W (f:=fun n i => -f n i) (a:=fun i => -a i)
    (fun i hi δ hδ => (h i hi δ hδ).mono (fun n hn => by linarith)) hε
  filter_upwards [hh] with n hn
  simp only [Finset.sum_neg_distrib] at hn
  linarith

lemma cubic_of_eventual_bounds {x b e : ℕ → ℝ} {s B C : ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hx : ∀ n, 0 ≤ x n)
    (hb : ∀ n, (x n)^3 ≤ C*b n+e n)
    (hlower : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, s-ε ≤ x n)
    (hupper : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop, b n ≤ B+ε)
    (he : Tendsto e atTop (𝓝 0)) : s^3 ≤ C*B := by
  have hineq (ε : ℝ) (hε : 0<ε) : (max (s-ε) 0)^3 ≤ C*(B+ε)+ε := by
    have hev := ((tendsto_order.mp he).2 ε hε).mono (fun n hn => hn.le)
    obtain ⟨n,hn,hn',hen⟩ := ((hlower ε hε).and ((hupper ε hε).and hev)).exists
    have hl : max (s-ε) 0 ≤ x n := max_le hn (hx n)
    exact (pow_le_pow_left₀ (le_max_right _ _) hl 3).trans
      ((hb n).trans (add_le_add (mul_le_mul_of_nonneg_left hn' hC) hen))
  have hlim₁ : Tendsto (fun ε : ℝ => (max (s-ε) 0)^3) (𝓝[>] 0) (𝓝 (s^3)) := by
    have hc : Continuous (fun ε : ℝ => (max (s-ε) 0)^3) := by fun_prop
    simpa only [sub_zero,max_eq_left hs] using (hc.continuousWithinAt (s:=Set.Ioi (0:ℝ)) (x:=0)).tendsto
  have hlim₂ : Tendsto (fun ε : ℝ => C*(B+ε)+ε) (𝓝[>] 0) (𝓝 (C*B)) := by
    have hc : Continuous (fun ε : ℝ => C*(B+ε)+ε) := by fun_prop
    simpa only [add_zero] using (hc.continuousWithinAt (s:=Set.Ioi (0:ℝ)) (x:=0)).tendsto
  exact le_of_tendsto_of_tendsto hlim₁ hlim₂
    (Filter.mem_of_superset self_mem_nhdsWithin (fun ε hε => hineq ε hε))

end PlanarHalving.Limits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter PlaneGraph
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Configuration.retained_cubic (F : Configuration) {C : ℝ}
    (hcoeff : 4608*(F.a : ℝ)^2*F.n^4/((F.R : ℝ)*F.a^2)^3 ≤ C)
    (W : Finset Window) (E : Finset (Fin F.n×Fin F.n)) (hE : E⊆F.system.edges)
    (hcover : ∀ e∈E, ∃ J∈W, e∈(F.system.timeWindow J).edges)
    {U : Set Labels} (hU : MeasurableSet U)
    (hnear : ∀ e∈E, ∀ p∈segment ℝ (F.point e.1) (F.point e.2), F.label p∈U) :
    ((E.card : ℝ)/((F.R : ℝ)*F.a^2))^3 ≤
      C*(∑ J∈W, ∑ K∈W, if J=K then 2*((F.vertices J).mass : ℝ)^2
        else (F.crossings J K U : ℝ))+
      13824*(F.n : ℝ)^3/((F.R : ℝ)*F.a^2)^3 := by
  classical
  let cr : ℝ := ((F.system.drawing.restrictEdges E).crossings.card : ℝ)
  let coeff : ℝ := 4608*(F.a : ℝ)^2*F.n^4/((F.R : ℝ)*F.a^2)^3
  have hc := F.system.restricted_crossing F.generic E hE
  have hc' : (E.card : ℝ)^3 ≤ 4608*(F.n : ℝ)^2*cr+13824*(F.n : ℝ)^3 := by
    dsimp [cr]; nlinarith [mul_nonneg (sq_nonneg (F.n : ℝ))
      (show (0:ℝ) ≤ ((F.system.drawing.restrictEdges E).crossings.card : ℝ) by positivity)]
  have hn : (F.n : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne F.n)
  have ha : (F.a : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne F.a)
  have hR : (F.R : ℝ)≠0 := Nat.cast_ne_zero.mpr (NeZero.ne F.R)
  have heq : (4608*(F.n : ℝ)^2*cr+13824*(F.n : ℝ)^3)/((F.R : ℝ)*F.a^2)^3 =
      coeff*(cr/((F.a : ℝ)*F.n)^2)+13824*(F.n : ℝ)^3/((F.R : ℝ)*F.a^2)^3 := by
    dsimp [coeff]; field_simp
  have hb := F.system.retained_crossing_bound F.generic F.label hU W E hE hcover hnear
  have hb' : cr/((F.a : ℝ)*F.n)^2 ≤
      ∑ J∈W, ∑ K∈W, if J=K then 2*((F.vertices J).mass : ℝ)^2 else (F.crossings J K U : ℝ) := by
    simpa only [F.vertices_mass_ratio,div_pow,mul_div_assoc,Configuration.crossings,Nat.cast_mul] using hb
  rw [div_pow]
  apply (div_le_div_of_nonneg_right hc' (by positivity)).trans
  rw [heq]
  apply add_le_add _ le_rfl
  exact (mul_le_mul_of_nonneg_right hcoeff (by dsimp [cr]; positivity)).trans
    (mul_le_mul_of_nonneg_left hb' ((show (0:ℝ) ≤ coeff by dsimp [coeff]; positivity).trans hcoeff))

lemma Converges.partition_cubic_thickening {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (W : Finset Window) (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    (A : Set Labels) {ρ : ℝ} (hρ : 0<ρ) :
    (∑ J∈W, (L.edgeWindow J A : ℝ))^3 ≤
      C*(∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2
        else (L.crossings J K (Metric.cthickening (2*ρ) A) : ℝ)) := by
  classical
  let U := Metric.thickening ρ A
  let V := Metric.cthickening (2*ρ) A
  let E (n : ℕ) := (F n).selectedEdges W U \ (F n).longEdges ρ
  apply cubic_of_eventual_bounds (x:=fun n => ((E n).card : ℝ)/((F n).R*(F n).a^2))
    (b:=fun n => ∑ J∈W, ∑ K∈W, if J=K then 2*(((F n).vertices J).mass : ℝ)^2
      else ((F n).crossings J K V : ℝ))
    (by positivity) hC (fun n => by positivity)
  · intro n
    apply (F n).retained_cubic (hcoeff n) W (E n)
      ((Finset.sdiff_subset).trans ((F n).selectedEdges_subset W U))
    · intro e he
      obtain ⟨J,hJ,heJ⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp he).1
      exact ⟨J,hJ,(Finset.mem_filter.mp heJ).1⟩
    · exact Metric.isClosed_cthickening.measurableSet
    · exact fun e he p hp => (F n).retained_near W A e he p hp
  · intro ε hε
    have h₁ := eventually_sum_lower W (fun J _ δ hδ =>
      (eventually_thickening_lower (h.edgeWindow J) A hρ (by linarith : (L.edgeWindow J A : ℝ)-δ<_)).mono
        (fun _ hn => hn.le)) (half_pos hε)
    have h₂ := (tendsto_order.mp (longEdges_ratio_zero hshort hρ)).2 (ε/2) (half_pos hε)
    filter_upwards [h₁,h₂] with n hn hn'
    have hb := (F n).retained_mass_lower W hW (U:=U) Metric.isOpen_thickening.measurableSet ρ
    dsimp only [E,U] at *
    linarith
  · intro ε hε
    apply eventually_sum_upper W _ hε
    intro J _ δ hδ
    apply eventually_sum_upper W _ hδ
    intro K _ τ hτ
    by_cases hJK : J=K
    · simp only [ite_eq_left hJK]
      have ht := NNReal.continuous_coe.tendsto _ |>.comp (FiniteMeasure.continuous_mass.tendsto _ |>.comp (h.vertices J))
      exact ((tendsto_order.mp (ht.pow 2 |>.const_mul 2)).2 _ (lt_add_of_pos_right _ hτ)).mono (fun _ hn => hn.le)
    · simp only [ite_eq_right hJK]
      exact (eventually_lt_closed (h.crossings J K) Metric.isClosed_cthickening
        (lt_add_of_pos_right _ hτ)).mono (fun _ hn => hn.le)
  · exact herror

end PlanarHalving.RankLimits
namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma finiteMeasure_tendsto_cthickening (μ : FiniteMeasure X) {A : Set X} (hA : IsClosed A)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => (μ (Metric.cthickening (r n) A) : ℝ)) atTop (𝓝 (μ A : ℝ)) := by
  have ht := tendsto_measure_cthickening_of_isClosed (μ:=(μ : Measure X))
    ⟨1,by norm_num,measure_ne_top _ _⟩ hA
  exact ENNReal.tendsto_toReal (measure_ne_top (μ : Measure X) A) |>.comp (ht.comp hr)

end PlanarHalving.Limits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter PlaneGraph
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Data.partitionQuantity_tendsto (L : Data) (W : Finset Window)
    {A : Set Labels} (hA : IsClosed A) {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2
        else (L.crossings J K (Metric.cthickening (r n) A) : ℝ)) atTop
      (𝓝 (∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J K A : ℝ))) := by
  classical
  apply tendsto_finsetSum
  intro J hJ
  apply tendsto_finsetSum
  intro K hK
  by_cases hJK : J=K
  · simp only [ite_eq_left hJK]; exact tendsto_const_nhds
  · simp only [ite_eq_right hJK]; exact finiteMeasure_tendsto_cthickening _ hA hr

lemma Converges.partition_cubic_closed {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (W : Finset Window) (hW : ∀ J∈W, ∀ K∈W, J≠K → Disjoint (carrier J) (carrier K))
    {A : Set Labels} (hA : IsClosed A) :
    (∑ J∈W, (L.edgeWindow J A : ℝ))^3 ≤
      C*(∑ J∈W, ∑ K∈W, if J=K then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J K A : ℝ)) := by
  classical
  have hr : Tendsto (fun n : ℕ => 2*(1/((n:ℝ)+1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
  have hlim := L.partitionQuantity_tendsto W hA hr |>.const_mul C
  apply ge_of_tendsto hlim
  exact Eventually.of_forall (fun n =>
    h.partition_cubic_thickening hC hcoeff herror hshort W hW A (by positivity : 0 < (1/((n:ℝ)+1))))

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
-- module Solutions.OAIQW_PlanarHalving.Derivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma inv_cube_rpow {q : ℝ} (hq : 0 < q) : (1/q^3)^(-(4:ℝ)/3)=q^4 := by
  have he : 1/q^3=q^(-(3:ℝ)) := by rw [Real.rpow_neg hq.le]; norm_num [one_div]
  rw [he,← Real.rpow_mul hq.le]
  norm_num

lemma goodPartition_subset (L : Data) (K : Window) (m : ℕ) :
    goodPartition L K m ⊆ localPartition K (5*m) := Finset.filter_subset _ _

lemma goodPartition_disjoint (L : Data) (K : Window) (m : ℕ) :
    ∀ J∈goodPartition L K m, ∀ H∈goodPartition L K m, J≠H → Disjoint (carrier J) (carrier H) := by
  intro J hJ H hH hJH
  exact localPartition_disjoint K (5*m) (goodPartition_subset L K m hJ) (goodPartition_subset L K m hH) hJH

lemma pow_depth (K m : ℕ) : (2:ℝ)^(K+5*m)=(2:ℝ)^K*((2:ℝ)^m)^5 := by
  rw [pow_add,Nat.mul_comm 5 m,pow_mul]

lemma Converges.goodPartition_loss {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (K : Window) (m : ℕ) {A : Set Labels} (hA : MeasurableSet A) :
    (L.edgeWindow K A : ℝ)-10000/(2:ℝ)^m ≤ ∑ J∈goodPartition L K m, (L.edgeWindow J A : ℝ) := by
  classical
  let W := localPartition K (5*m)
  let u : ℝ := 1/((2:ℝ)^m)^3
  let B := W.filter (fun J => ¬ ((L.vertices J).mass : ℝ) ≤ u)
  have hu : 0 < u := by dsimp [u]; positivity
  have hcard : (B.card : ℝ) ≤ 10000*((2:ℝ)^m)^4 := by
    have hb : B ⊆ (timePartition (K.1+5*m)).filter (fun J => u < ((L.vertices J).mass : ℝ)) := by
      intro J hJ
      obtain ⟨hJ,hb⟩ := Finset.mem_filter.mp hJ
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hJ).1,lt_of_not_ge hb⟩
    have ht := h.activity_tail E (K.1+5*m) hu
    rw [← filter_timePartition (K.1+5*m) (fun J => u < ((L.vertices J).mass : ℝ))] at ht
    have hi := (Nat.cast_le.mpr (Finset.card_le_card hb) : (B.card : ℝ) ≤ _)
    exact hi.trans (by simpa only [u,inv_cube_rpow (by positivity : (0:ℝ) < (2:ℝ)^m)] using ht)
  have hmass (J : Window) (hJ : J∈B) : (L.edgeWindow J A : ℝ) ≤ 1/((2:ℝ)^m)^5 := by
    have hd : J.1=K.1+5*m := mem_timePartition.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
    have hh := NNReal.coe_le_coe.mpr ((L.edgeWindow J).apply_le_mass A)
    rw [h.edgeWindow_mass hR,Nat.cast_pow,Nat.cast_ofNat,hd,pow_depth] at hh
    have he : (1:ℝ) ≤ (2:ℝ)^K.1 := one_le_pow₀ (by norm_num)
    have hp : ((2:ℝ)^m)^5 ≤ (2:ℝ)^K.1*((2:ℝ)^m)^5 :=
      le_mul_of_one_le_left (by positivity) he
    exact hh.trans (by simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : (0:ℝ) < ((2:ℝ)^m)^5) hp)
  have hloss : ∑ J∈B, (L.edgeWindow J A : ℝ) ≤ 10000/(2:ℝ)^m := by
    apply (Finset.sum_le_sum hmass).trans
    simp only [Finset.sum_const,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right hcard (by positivity)).trans
    have hn : ((2:ℝ)^m)≠0 := by positivity
    exact le_of_eq (by field_simp)
  have he : (∑ J∈goodPartition L K m, (L.edgeWindow J A : ℝ))+
      (∑ J∈B, (L.edgeWindow J A : ℝ))=(L.edgeWindow K A : ℝ) := by
    rw [← h.localPartition_sum hR K (5*m) hA]
    exact Finset.sum_filter_add_sum_filter_not W _ _
  linarith

lemma Data.goodPartition_diagonal (L : Data) (K : Window) (m : ℕ) :
    ∑ J∈goodPartition L K m, 2*((L.vertices J).mass : ℝ)^2 ≤ 2*(2:ℝ)^K.1/(2:ℝ)^m := by
  classical
  let W := goodPartition L K m
  have hs : W ⊆ timePartition (K.1+5*m) := fun J hJ =>
    (Finset.mem_filter.mp (goodPartition_subset L K m hJ)).1
  have hc : (W.card : ℝ) ≤ (2:ℝ)^(K.1+5*m) := by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (timePartition_card _)
  have hsum : ∑ J∈W, 2*((L.vertices J).mass : ℝ)^2 ≤ (W.card : ℝ)*(2*(1/((2:ℝ)^m)^3)^2) := by
    have hh := Finset.sum_le_sum (s:=W) (fun J hJ => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (Finset.mem_filter.mp hJ).2 2) (by norm_num : (0:ℝ)≤2))
    simpa only [Finset.sum_const,nsmul_eq_mul] using hh
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans
  rw [pow_depth]
  have hn : ((2:ℝ)^m)≠0 := by positivity
  exact le_of_eq (by field_simp)

lemma Data.goodPartition_crossings (L : Data) (K : Window) (m : ℕ) {A : Set Labels}
    (hnull : ∀ J H : Window, carrier J⊆carrier K → carrier H⊆carrier K →
      Disjoint (carrier J) (carrier H) → L.crossings J H A=0) :
    (∑ J∈goodPartition L K m, ∑ H∈goodPartition L K m,
      if J=H then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J H A : ℝ)) ≤
      2*(2:ℝ)^K.1/(2:ℝ)^m := by
  classical
  apply le_trans _ (L.goodPartition_diagonal K m)
  apply Finset.sum_le_sum
  intro J hJ
  have he : (∑ H∈goodPartition L K m,
      if J=H then 2*((L.vertices J).mass : ℝ)^2 else (L.crossings J H A : ℝ))=
      2*((L.vertices J).mass : ℝ)^2 := by
    rw [Finset.sum_eq_single J]
    · simp
    · intro H hH hHJ
      rw [ite_eq_right (Ne.symm hHJ),hnull J H
        (Finset.mem_filter.mp (goodPartition_subset L K m hJ)).2
        (Finset.mem_filter.mp (goodPartition_subset L K m hH)).2
        (goodPartition_disjoint L K m J hJ H hH (Ne.symm hHJ))]
      rfl
    · exact fun hn => (hn hJ).elim
  exact he.le

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable Classical

lemma Converges.edge_crossing_null_closed {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (K : Window) {A : Set Labels} (hA : IsClosed A)
    (hnull : ∀ J H : Window, carrier J⊆carrier K → carrier H⊆carrier K →
      Disjoint (carrier J) (carrier H) → L.crossings J H A=0) : L.edgeWindow K A=0 := by
  have ht : Tendsto (fun m : ℕ => ((2:ℝ)^m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlo : Tendsto (fun m : ℕ => 10000/(2:ℝ)^m) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ht.const_mul (10000:ℝ)
  have hup : Tendsto (fun m : ℕ => 2*(2:ℝ)^K.1/(2:ℝ)^m) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ht.const_mul (2*(2:ℝ)^K.1)
  have hcub : (L.edgeWindow K A : ℝ)^3 ≤ C*0 := by
    apply Limits.cubic_of_eventual_bounds (x:=fun m => ∑ J∈goodPartition L K m, (L.edgeWindow J A : ℝ))
      (b:=fun m => 2*(2:ℝ)^K.1/(2:ℝ)^m) (e:=fun _ => 0) (by positivity) hC
    · intro m; positivity
    · intro m
      simpa only [add_zero] using
        (h.partition_cubic_closed hC hcoeff herror hshort _ (goodPartition_disjoint L K m) hA).trans
          (mul_le_mul_of_nonneg_left (L.goodPartition_crossings K m hnull) hC)
    · intro ε hε
      filter_upwards [(tendsto_order.mp hlo).2 ε hε] with m hm
      have hh := h.goodPartition_loss E hR K m hA.measurableSet
      linarith
    · intro ε hε
      exact ((tendsto_order.mp hup).2 ε hε).mono (fun _ hh => by simpa only [zero_add] using hh.le)
    · exact tendsto_const_nhds
  apply NNReal.coe_injective
  change (L.edgeWindow K A : ℝ)=0
  have hp : 0 ≤ (L.edgeWindow K A : ℝ) := by positivity
  have he : (L.edgeWindow K A : ℝ)^3=0 :=
    le_antisymm (by simpa only [mul_zero] using hcub) (pow_nonneg hp _)
  exact (pow_eq_zero_iff (by decide : (3:ℕ)≠0)).mp he

lemma Converges.edge_crossing_null {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (K : Window) {A : Set Labels} (hA : MeasurableSet A)
    (hnull : ∀ J H : Window, carrier J⊆carrier K → carrier H⊆carrier K →
      Disjoint (carrier J) (carrier H) → L.crossings J H A=0) : L.edgeWindow K A=0 := by
  by_contra hn
  have hp : 0 < (L.edgeWindow K : Measure Labels) A := by
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ENNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hn)
  obtain ⟨T,hTA,hT,hpos⟩ := hA.exists_lt_isCompact hp
  have hz := h.edge_crossing_null_closed E hR hC hcoeff herror hshort K hT.isClosed
    (fun J H hJ hH hd => le_antisymm (((L.crossings J H).apply_mono hTA).trans_eq (hnull J H hJ hH hd)) (by positivity))
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hz,ENNReal.coe_zero] at hpos
  exact lt_irrefl _ hpos

lemma Converges.edge_crossing_ac {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    (K : Window) : (L.edgeWindow K : Measure Labels) ≪
      Measure.sum (fun JH : CrossingPairs K => (L.crossings JH.val.1 JH.val.2 : Measure Labels)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hn
  have hz (J H : Window) (hJ : carrier J⊆carrier K) (hH : carrier H⊆carrier K)
      (hd : Disjoint (carrier J) (carrier H)) : L.crossings J H A=0 := by
    have hh := Measure.sum_apply_eq_zero.mp hn (⟨(J,H),hJ,hH,hd⟩ : CrossingPairs K)
    simpa only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,ENNReal.coe_eq_zero] using hh
  have hh := h.edge_crossing_null E hR hC hcoeff herror hshort K hA hz
  simpa only [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,ENNReal.coe_eq_zero] using hh

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows
open scoped Topology unitInterval

lemma continuous_signedPair (b : Bool) : Continuous (signedPair b) := by
  cases b
  · exact continuous_fst.neg.prodMk continuous_snd
  · exact continuous_fst.prodMk continuous_snd.neg

lemma continuous_pairCoordinates (b : Bool) (A B : Window) :
    Continuous (pairCoordinates b A B) :=
  (continuous_signedPair b).comp ((continuous_subtype_val.comp (continuous_apply A)).prodMk
    (continuous_subtype_val.comp (continuous_apply B)))

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Continuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped unitInterval Topology

lemma Ioo_subset_carrier (J : Window) : Ioo (lower J) (upper J) ⊆ carrier J := by
  intro t ht
  unfold carrier UniformPartition.cell
  split_ifs
  · exact ⟨ht.1.le, ht.2.le⟩
  · exact ⟨ht.1.le, ht.2⟩

lemma carrier_subset_Icc (J : Window) : carrier J ⊆ Icc (lower J) (upper J) := by
  intro t ht
  unfold carrier UniformPartition.cell at ht
  split_ifs at ht
  · exact ht
  · exact ⟨ht.1, ht.2.le⟩

lemma before_or_before {A B : Window} (h : Disjoint (carrier A) (carrier B)) :
    Before A B ∨ Before B A := by
  by_contra hn
  have hn' : upper B > lower A ∧ upper A > lower B := by
    simpa only [Before, lower, upper, not_or, not_le, and_comm] using hn
  have hlt : max (lower A) (lower B) < min (upper A) (upper B) := by
    exact max_lt_iff.mpr ⟨lt_min (lower_lt_upper A) hn'.1,
      lt_min hn'.2 (lower_lt_upper B)⟩
  obtain ⟨t,ht1,ht2⟩ := exists_between hlt
  exact Set.disjoint_left.mp h (Ioo_subset_carrier A ⟨(le_max_left _ _).trans_lt ht1,
      ht2.trans_le (min_le_left _ _)⟩)
    (Ioo_subset_carrier B ⟨(le_max_right _ _).trans_lt ht1,ht2.trans_le (min_le_right _ _)⟩)

end PlanarHalving.TimeWindows
namespace PlanarHalving.Batches
open Set MeasureTheory TimeWindows Limits
variable {n R k a : ℕ} {P : Fin n → Point}
lemma System.windowCrossings_comm (S : @System n R k a P) [NeZero R] (A B : Window) :
    S.windowCrossings A B = S.windowCrossings B A := by
  classical
  unfold System.windowCrossings
  congr 1
  funext w
  apply propext
  tauto

lemma System.windowCrossMeasure_comm (S : @System n R k a P) [NeZero R]
    (A B : Window) {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (z : Point → X) : S.windowCrossMeasure A B z = S.windowCrossMeasure B A z := by
  apply FiniteMeasure.eq_of_forall_apply_eq
  intro U hU
  apply NNReal.coe_injective
  rw [S.windowCrossMeasure_apply A B z hU,S.windowCrossMeasure_apply B A z hU]
  rw [System.crossingsIn,System.crossingsIn,S.windowCrossings_comm A B]
end PlanarHalving.Batches

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped unitInterval Topology

lemma Converges.crossings_comm {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (A B : Window) : L.crossings A B = L.crossings B A := by
  apply tendsto_nhds_unique (h.crossings A B)
  convert h.crossings B A using 1
  funext n
  exact (F n).system.windowCrossMeasure_comm A B _

lemma unitPair_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun p : I × I => ((p.1 : ℝ),(p.2 : ℝ))) volume volume := by
  have hi : Measure.QuasiMeasurePreserving ((↑) : I → ℝ) volume volume :=
    unitInterval.measurePreserving_coe.quasiMeasurePreserving.mono_right (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self))
  exact QuasiMeasurePreserving.prodMap hi hi

lemma Converges.crossing_real_projection {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {A B : Window} (hAB : Before A B) :
    (L.crossings A B : Measure Labels).map (fun z => ((z A : ℝ),(z B : ℝ))) ≪ volume := by
  have hp : Measure.QuasiMeasurePreserving (fun z : Labels => (z A,z B))
      (L.crossings A B : Measure Labels) volume :=
    ⟨(continuous_apply A |>.prodMk (continuous_apply B)).measurable,
      Measure.absolutelyContinuous_of_le (h.crossing_projection hR hM hAB)⟩
  exact (unitPair_quasiMeasurePreserving.comp hp).absolutelyContinuous

lemma Converges.window_withDensity {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.edgeWindow J : Measure Labels) = (L.edge : Measure Labels).withDensity
      (fun z => L.conditional z (carrier J)) := by
  ext U hU
  rw [withDensity_apply _ hU, Data.edge_toMeasure, Data.conditional,
    Measure.setLIntegral_condKernel_eq_measure_prod hU (measurable_carrier J)]
  rw [Data.edgeWindow,FiniteMeasure.toMeasure_map,Measure.map_apply measurable_fst hU,
    h.restriction_eq hR,Measure.restrict_apply (hU.preimage measurable_fst)]
  rfl

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Densities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval

lemma Converges.crossing_real_projection_disjoint {F : ℕ → Configuration} {L : Data}
    (h : Converges F L) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {A B : Window} (hAB : Disjoint (carrier A) (carrier B)) :
    (L.crossings A B : Measure Labels).map (fun z => ((z A : ℝ),(z B : ℝ))) ≪ volume := by
  rcases before_or_before hAB with hab | hba
  · exact h.crossing_real_projection hR hM hab
  · have hp : Measure.QuasiMeasurePreserving (fun z : Labels => ((z B : ℝ),(z A : ℝ)))
        (L.crossings B A : Measure Labels) volume :=
      ⟨by fun_prop,h.crossing_real_projection hR hM hba⟩
    have hswap : Measure.QuasiMeasurePreserving (Prod.swap : Point → Point) volume volume :=
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).quasiMeasurePreserving
    have hh := (hswap.comp hp).absolutelyContinuous
    simpa only [Function.comp_def, Prod.swap_prod_mk, ← h.crossings_comm A B] using hh

lemma Converges.rank_regular_ae {F : ℕ → Configuration} {L : Data} (_h : Converges F L)
    {K A B : Window} (ν : Measure Labels) (hp : ν ≪ (L.points : Measure Labels))
    (hproj : ν.map (pairCoordinates true A B) ≪ volume)
    (G : Subwindows K → Point → I)
    (hd : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p)
    (hid : ∀ i z, z ∈ (L.points : Measure Labels).support →
      ContinuousAt (G i) (pairCoordinates true A B z) →
      z i.val = G i (pairCoordinates true A B z)) :
    ∀ᵐ z ∂ν, ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) (pairCoordinates true A B z) ∧
      z i.val = G i (pairCoordinates true A B z) := by
  have hq : Measure.QuasiMeasurePreserving (pairCoordinates true A B) ν volume :=
    ⟨(continuous_pairCoordinates true A B).measurable,hproj⟩
  have hda := hq.ae ((ae_all_iff).mpr hd)
  have hs : ∀ᵐ z ∂ν, z ∈ (L.points : Measure Labels).support := hp.ae_le Measure.support_mem_ae
  filter_upwards [hda,hs] with z hz hzs i
  refine ⟨hz i,hid i z hzs ?_⟩
  exact ((hz i).continuousAt).codRestrict (fun x => (G i x).property)

lemma Converges.rank_independent_ae {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (E : ∀ n, (F n).SweepEmbedding)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0 ≤ C)
    (hcoeff : ∀ n, 4608*((F n).a : ℝ)^2*(F n).n^4/(((F n).R : ℝ)*(F n).a^2)^3 ≤ C)
    (herror : Tendsto (fun n => 13824*((F n).n : ℝ)^3/(((F n).R : ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n : ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    {K A B : Window} (G : Subwindows K → Point → I) :
    ∀ᵐ z ∂(L.edge : Measure Labels),
      (∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) (pairCoordinates true A B z) ∧
        z i.val = G i (pairCoordinates true A B z)) →
      ∀ J : Subwindows K, L.conditional z (carrier J.val) ≠ 0 →
        ∃ i j : Subwindows K, carrier i.val ⊆ carrier J.val ∧
          carrier j.val ⊆ carrier J.val ∧ Disjoint (carrier i.val) (carrier j.val) ∧
          Function.Injective (fun v : Point =>
            ((fderiv ℝ (fun x => (G i x : ℝ)) (pairCoordinates true A B z)) v,
             (fderiv ℝ (fun x => (G j x : ℝ)) (pairCoordinates true A B z)) v)) := by
  let p := pairCoordinates true A B
  let S : Set Labels := {z | ∀ i, DifferentiableAt ℝ (fun x => (G i x : ℝ)) (p z) ∧
    z i.val = G i (p z)}
  have he : ∀ J : Subwindows K, ∀ᵐ z ∂(L.edge : Measure Labels), z ∈ S →
      L.conditional z (carrier J.val) ≠ 0 →
      ∃ q : CrossingPairs J.val,
        (fderiv ℝ (fun x => ((G ⟨q.val.1,q.property.1.trans J.property⟩ x : ℝ),
          (G ⟨q.val.2,q.property.2.1.trans J.property⟩ x : ℝ))) (p z)).det ≠ 0 := by
    intro J
    apply Transversality.independent_gradients_ae (L.edge : Measure Labels)
      (fun z => L.conditional z (carrier J.val)) (L.conditional.measurable_coe (measurable_carrier J.val))
      (fun q : CrossingPairs J.val => (L.crossings q.val.1 q.val.2 : Measure Labels))
      (by rw [← h.window_withDensity hR]; exact h.edge_crossing_ac E hR hC hcoeff herror hshort J.val)
      (fun q z => ((z q.val.1 : ℝ),(z q.val.2 : ℝ)))
      (fun _ => by fun_prop)
      (fun q => h.crossing_real_projection_disjoint hR hM q.property.2.2) p
      (fun q x => ((G ⟨q.val.1,q.property.1.trans J.property⟩ x : ℝ),
        (G ⟨q.val.2,q.property.2.1.trans J.property⟩ x : ℝ))) S
    · intro q z hz
      exact Prod.ext (congrArg Subtype.val (hz ⟨q.val.1,q.property.1.trans J.property⟩).2)
        (congrArg Subtype.val (hz ⟨q.val.2,q.property.2.1.trans J.property⟩).2)
    · intro q z hz
      exact ((hz _).1).prodMk ((hz _).1)
  filter_upwards [(ae_all_iff).mpr he] with z hz hreg J hJ
  obtain ⟨q,hq⟩ := hz J hreg hJ
  let i : Subwindows K := ⟨q.val.1,q.property.1.trans J.property⟩
  let j : Subwindows K := ⟨q.val.2,q.property.2.1.trans J.property⟩
  refine ⟨i,j,q.property.1,q.property.2.1,q.property.2.2,?_⟩
  have hder : fderiv ℝ (fun x => ((G i x : ℝ),(G j x : ℝ))) (p z) =
      (fderiv ℝ (fun x => (G i x : ℝ)) (p z)).prod (fderiv ℝ (fun x => (G j x : ℝ)) (p z)) :=
    ((hreg i).1.hasFDerivAt.prodMk (hreg j).1.hasFDerivAt).fderiv
  rw [hder] at hq
  let D := (fderiv ℝ (fun x => (G i x : ℝ)) (p z)).prod
    (fderiv ℝ (fun x => (G j x : ℝ)) (p z))
  change Function.Injective D
  apply (LinearMap.ker_eq_bot (f := D.toLinearMap)).mp
  by_contra hn
  exact hq (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hn)

end PlanarHalving.RankLimits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.SeparatedWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open MeasureTheory Set Filter
open scoped Topology unitInterval

lemma measure_interior_eq (μ : Measure I) [NullSingletonClass μ] (K : Window) :
    μ (Ioo (lower K) (upper K)) = μ (carrier K) := by
  apply le_antisymm (measure_mono (Ioo_subset_carrier K))
  calc
    μ (carrier K) ≤ μ (Icc (lower K) (upper K)) := measure_mono (carrier_subset_Icc K)
    _ = μ (Ioo (lower K) (upper K)) := measure_congr Ioo_ae_eq_Icc.symm

end PlanarHalving.TimeWindows

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.Noncollapse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped Topology unitInterval

lemma CommonChoice.time_mem {K : Window} (q : CommonChoice K) (i : Fin 3) :
    q.time i∈Ioo (lower K) (upper K) := by
  have h := q.property
  fin_cases i <;> dsimp [CommonChoice.time]
  · exact ⟨h.1,(lower_lt_upper q.val.1).trans (h.2.1.trans ((lower_lt_upper q.val.2.1).trans h.2.2.1))⟩
  · exact ⟨h.1.trans (lower_lt_upper q.val.1),h.2.1.trans ((lower_lt_upper q.val.2.1).trans h.2.2.1)⟩
  · exact ⟨h.1.trans ((lower_lt_upper q.val.1).trans (h.2.1.trans (lower_lt_upper q.val.2.1))),h.2.2.1⟩

lemma CommonChoice.positive_gaps {K : Window} (q : CommonChoice K)
    (μ : Measure I) [NullSingletonClass μ]
    (hJ : μ (carrier q.val.1)≠0) (hH : μ (carrier q.val.2.1)≠0) :
    ∀ i j, i<j → μ (Ioo (q.time i) (q.time j))≠0 := by
  have hj : μ (Ioo (lower q.val.1) (upper q.val.1))≠0 := by rwa [measure_interior_eq]
  have hh : μ (Ioo (lower q.val.2.1) (upper q.val.2.1))≠0 := by rwa [measure_interior_eq]
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try (norm_num at hij)
  all_goals dsimp [CommonChoice.time]
  · exact hj
  · apply ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hj) (measure_mono ?_))
    exact Ioo_subset_Ioo_right ((q.property.2.1.trans (lower_lt_upper q.val.2.1)).le)
  · apply ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hh) (measure_mono ?_))
    exact Ioo_subset_Ioo_left q.property.2.1.le

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

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows
open scoped Topology unitInterval ENNReal

lemma coordinate_lines_null (x : ℝ) :
    (volume : Measure Point) {p | p.1=x}=0 ∧ (volume : Measure Point) {p | p.2=x}=0 := by
  have h1 : {p : Point | p.1=x}=({x}:Set ℝ)×ˢuniv := by ext p; simp
  have h2 : {p : Point | p.2=x}=(univ:Set ℝ)×ˢ{x} := by ext p; simp
  rw [h1,h2,Measure.volume_eq_prod,Measure.prod_prod,Measure.prod_prod]
  simp

lemma pairCoordinates_interior_ae {ν : Measure Labels} {A B : Window}
    (hproj : ν.map (pairCoordinates true A B) ≪ volume) :
    ∀ᵐ z ∂ν, pairCoordinates true A B z∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  have hq : Measure.QuasiMeasurePreserving (pairCoordinates true A B) ν volume :=
    ⟨(continuous_pairCoordinates true A B).measurable,hproj⟩
  have ha (x : ℝ) : ∀ᵐ p ∂(volume : Measure Point), p.1≠x := by
    simpa only [ae_iff,not_not] using (coordinate_lines_null x).1
  have hb (x : ℝ) : ∀ᵐ p ∂(volume : Measure Point), p.2≠x := by
    simpa only [ae_iff,not_not] using (coordinate_lines_null x).2
  filter_upwards [hq.ae (ha 0),hq.ae (ha 1),hq.ae (hb (-1)),hq.ae (hb 0)] with z h1 h2 h3 h4
  dsimp [pairCoordinates,signedPair] at h1 h2 h3 h4 ⊢
  have hzA := (z A).property
  have hzB := (z B).property
  exact ⟨⟨lt_of_le_of_ne hzA.1 (Ne.symm h1),lt_of_le_of_ne hzA.2 h2⟩,
    ⟨lt_of_le_of_ne (by linarith [hzB.2]) (Ne.symm h3),lt_of_le_of_ne (by linarith [hzB.1]) h4⟩⟩

end PlanarHalving.RankLimits

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
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom
open scoped Topology unitInterval

lemma commonDirection_independent (i j : Fin 3) (h : i≠j) :
    detPair (commonDirection i) (commonDirection j)≠0 := by
  fin_cases i <;> fin_cases j <;> norm_num [commonDirection,detPair] at *

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom
open scoped Topology unitInterval

lemma Converges.radial_ae_oai {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (emb : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n:ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (hA : ∀ n, 0<length (F n).R A) (hB : ∀ n, 0<length (F n).R B)
    (G : Subwindows K → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B i.val q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x:ℝ)) p)
    (hid : ∀ i z, z∈(L.points:Measure Labels).support →
      ContinuousAt (G i) (pairCoordinates true A B z) → z i.val=G i (pairCoordinates true A B z))
    (ν : Measure Labels) (he : ν≪(L.edge:Measure Labels)) (hp : ν≪(L.points:Measure Labels))
    (hproj : ν.map (pairCoordinates true A B)≪volume)
    (q : CommonChoice K)
    (hpos : ∀ᵐ z ∂ν, L.conditional z (carrier K)≠0 ∧ z∈commonSet L q)
    (E : ℕ → Point ≃L[ℝ] Point)
    (hE : ∀ n i, detPair ((E n).symm (1,(F n).timeSlope (q.time i))) (commonDirection i)=0) :
    ∀ᵐ z ∂ν, pairCoordinates true A B z∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C₀ : ℝ, 0<C₀ ∧ ∀ T : ℝ, 1≤T → ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
        RadialCompare (commonChart (F n) hAB (hA n) (hB n) (E n)).symm
          (pairCoordinates true A B z) r C₀ T := by
  have hreg := h.rank_regular_ae ν hp hproj G hGaed hid
  have hind := he.ae_le (h.rank_independent_ae (A:=A) (B:=B) emb hR hM hC hcoeff herror hshort G)
  have hna := he.ae_le (h.conditional_nullSingleton emb hR hC hcoeff herror)
  filter_upwards [hreg,hind,hna,hpos,pairCoordinates_interior_ae hproj] with z hz hi hn hpos hzp
  let := hn
  refine ⟨hzp,?_⟩
  have h := pointwise_radial F hR hAB hKA hKB hA hB G hjoint hGaed hzp
    (fun i => (hz i).1) (L.conditional z) hpos.1 (fun J hJ => by
      obtain ⟨i,j,hi,hj,_,hij⟩ := hi hz J hJ
      exact ⟨i,j,hi,hj,hij⟩) q.time q.time_mem
    (q.positive_gaps (L.conditional z) hpos.2.1 hpos.2.2.1)
    (fun n => (E n).symm) commonDirection commonDirection_independent hE
  exact h

end PlanarHalving.RankLimits

end OAI
end

theorem solution : type_of% @OAI.PlanarHalving.RankLimits.Converges.radial_ae_oai := @OAI.PlanarHalving.RankLimits.Converges.radial_ae_oai

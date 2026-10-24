-- Prove2me | solution 1 for OAI.PlanarHalving.RankLimits.Converges.impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:52:53.701989+00:00
-- url     : https://prove2.me/submissions/b667cfdf-ea5f-46e5-8166-4ab0253a3d89

import Mathlib
import Definitions.Def_HalvingLines
import Definitions.Def_OAIQWPHL000
import Theorems.Thm_OAI_PlanarHalving_Boundary_enhanced_boundary_zero
import Theorems.Thm_OAI_PlanarHalving_PlaneGraph_designated_crossing_bound
import Theorems.Thm_OAI_PlanarHalving_RankLimits_Converges_positive_part
import Theorems.Thm_OAI_PlanarHalving_RankLimits_Converges_radial_ae

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
-- module Solutions.OAIQW_PlanarHalving.Calculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarHalving

namespace Calculus

open Filter MeasureTheory Set Metric Asymptotics
open scoped Topology ENNReal NNReal

theorem ae_near_set (S : Set Point) (hS : MeasurableSet S) :
    ∀ᵐ x ∂(volume : Measure Point), x ∈ S →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x,
        ∃ z ∈ S, dist z y ≤ ε * dist y x := by
  have hd : ∀ᵐ x ∂(volume : Measure Point).restrict S, ∀ n : ℕ,
      ∀ {ι : Type} {l : Filter ι} (w : ι → Point) (δ : ι → ℝ),
      Tendsto δ l (𝓝[>] 0) →
      (∀ᶠ j in l, x ∈ closedBall (w j) ((n + 1 : ℝ) * δ j)) →
      Tendsto (fun j => volume (S ∩ closedBall (w j) (δ j)) /
        volume (closedBall (w j) (δ j))) l (𝓝 (1 : ℝ≥0∞)) := by
    rw [ae_all_iff]
    intro n
    exact IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume S (n + 1)
  rw [ae_restrict_iff' hS] at hd
  filter_upwards [hd] with x hx hxs
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (ε⁻¹)
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hnε : (n + 1 : ℝ)⁻¹ ≤ ε := by
    apply (inv_le_iff_one_le_mul₀ hn0).mpr
    have hh := (inv_lt_iff_one_lt_mul₀ hε).mp hn
    nlinarith
  have hδ : Tendsto (fun y : Point => (n + 1 : ℝ)⁻¹ * dist y x)
      (𝓝[≠] x) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hh : Tendsto (fun y : Point => (n + 1 : ℝ)⁻¹ * dist y x)
          (𝓝 x) (𝓝 ((n + 1 : ℝ)⁻¹ * dist x x)) :=
        (continuousAt_id.dist continuousAt_const).const_mul _
      simpa using hh.mono_left (nhdsWithin_le_nhds (s := {x}ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact mul_pos (inv_pos.mpr hn0) (dist_pos.mpr hy)
  have hcover : ∀ᶠ y : Point in 𝓝[≠] x,
      x ∈ closedBall y ((n + 1 : ℝ) * ((n + 1 : ℝ)⁻¹ * dist y x)) := by
    filter_upwards with y
    simp [Metric.mem_closedBall, mul_inv_cancel_left₀ hn0.ne', dist_comm]
  have hlim := hx hxs n (fun y : Point => y)
    (fun y => (n + 1 : ℝ)⁻¹ * dist y x) hδ hcover
  have he : ∀ᶠ y : Point in 𝓝[≠] x,
      ∃ z ∈ S, dist z y ≤ ε * dist y x := by
    have hh := hlim.eventually (Ioi_mem_nhds (show (0 : ℝ≥0∞) < 1 by simp))
    filter_upwards [hh] with y hy
    have hne : volume (S ∩ closedBall y ((n + 1 : ℝ)⁻¹ * dist y x)) ≠ 0 := by
      intro hz
      simp [hz] at hy
    obtain ⟨z, hzS, hzB⟩ := nonempty_of_measure_ne_zero hne
    exact ⟨z, hzS, (Metric.mem_closedBall.mp hzB).trans
      (mul_le_mul_of_nonneg_right hnε dist_nonneg)⟩
  rw [← nhdsNE_sup_pure x, Filter.eventually_sup]
  exact ⟨he, by simp only [Filter.eventually_pure]; exact ⟨x, hxs, by simp⟩⟩

theorem hasFDerivAt_of_within_near_set {f : Point → ℝ} {S : Set Point}
    {x : Point} {f' : Point →L[ℝ] ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hLip : ∀ z ∈ S, ∀ y, ‖f y - f z‖ ≤ C * ‖y - z‖)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x,
      ∃ z ∈ S, dist z y ≤ ε * dist y x)
    (hf : HasFDerivWithinAt f f' S x) : HasFDerivAt f f' x := by
  rw [hasFDerivAt_iff_isLittleO]
  apply IsLittleO.of_bound
  intro ε hε
  let η := min 1 (ε / (2 * (C + ‖f'‖ + 1)))
  have hden : 0 < 2 * (C + ‖f'‖ + 1) := by positivity
  have hη : 0 < η := lt_min zero_lt_one (div_pos hε hden)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hsmall : (C + ‖f'‖) * η ≤ ε / 2 := by
    have hh := (le_div_iff₀ hden).mp (min_le_right 1 (ε / (2 * (C + ‖f'‖ + 1))))
    nlinarith only [hh, hη]
  have hlin := hf.isLittleO.def (show 0 < ε / 4 by positivity)
  obtain ⟨r, hr, hrlin⟩ := Metric.mem_nhdsWithin_iff.mp hlin
  filter_upwards [hnear η hη, Metric.ball_mem_nhds x (show 0 < r / 2 by positivity)] with y hy hyr
  obtain ⟨z, hzS, hzy⟩ := hy
  have hyz : ‖y - z‖ ≤ η * ‖y - x‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hzy
  have hzx : ‖z - x‖ ≤ 2 * ‖y - x‖ := by
    have hh := dist_triangle z y x
    simp only [dist_eq_norm] at hh
    have hzy' : ‖z - y‖ ≤ ‖y - x‖ := by
      have hzyη : ‖z - y‖ ≤ η * ‖y - x‖ := by
        rw [norm_sub_rev]
        exact hyz
      exact hzyη.trans (mul_le_of_le_one_left (norm_nonneg _) hη1)
    linarith only [hh, hzy']
  have hzr : dist z x < r := by
    rw [Metric.mem_ball, dist_eq_norm] at hyr
    rw [dist_eq_norm]
    linarith only [hzx, hyr]
  have hzlin := hrlin ⟨hzr, hzS⟩
  have hdecomp : f y - f x - f' (y - x) =
      (f y - f z - f' (y - z)) + (f z - f x - f' (z - x)) := by
    rw [show y - x = (y - z) + (z - x) by abel, map_add]
    ring
  calc
    ‖f y - f x - f' (y - x)‖ ≤
        ‖f y - f z‖ + ‖f' (y - z)‖ + ‖f z - f x - f' (z - x)‖ := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ C * ‖y - z‖ + ‖f'‖ * ‖y - z‖ + (ε / 4) * ‖z - x‖ := by
      gcongr
      · exact hLip z hzS y
      · exact f'.le_opNorm _
      · exact hzlin
    _ ≤ (C + ‖f'‖) * (η * ‖y - x‖) + (ε / 4) * (2 * ‖y - x‖) := by
      rw [← add_mul]
      gcongr
    _ ≤ ε * ‖y - x‖ := by
      nlinarith only [mul_le_mul_of_nonneg_right hsmall (norm_nonneg (y - x))]

theorem ae_differentiable_of_pointwise_lipschitz_pieces {f : Point → ℝ}
    (S : ℕ → Set Point) (hS : ∀ n, MeasurableSet (S n))
    (hLip : ∀ n, ∀ z ∈ S n, ∀ y, ‖f y - f z‖ ≤ (n : ℝ) * ‖y - z‖)
    (hcover : ∀ᵐ x ∂(volume : Measure Point), ∃ n, x ∈ S n) :
    ∀ᵐ x ∂(volume : Measure Point), DifferentiableAt ℝ f x := by
  have hd : ∀ n, ∀ᵐ x ∂(volume : Measure Point), x ∈ S n → DifferentiableAt ℝ f x := by
    intro n
    have hl : LipschitzOnWith (n : ℝ≥0) f (S n) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simpa only [dist_eq_norm, NNReal.coe_natCast] using hLip n y hy x
    filter_upwards [hl.ae_differentiableWithinAt_of_mem, ae_near_set (S n) (hS n)] with x hx hn hxs
    obtain ⟨f', hf'⟩ := hx hxs
    exact (hasFDerivAt_of_within_near_set (by positivity) (hLip n) (hn hxs) hf').differentiableAt
  filter_upwards [ae_all_iff.mpr hd, hcover] with x hx hc
  obtain ⟨n, hn⟩ := hc
  exact hx n hn

theorem measurableSet_slopePiece {f : Point → ℝ} (hf : Measurable f) (m : ℕ) :
    MeasurableSet (slopePiece f m) := by
  simp only [slopePiece, ofPred_forall]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le ((hf.comp (measurable_id.add_const _)).sub
    (hf.comp (measurable_id.sub_const _))) measurable_const

theorem monotone_chord_bound {f : Point → ℝ} (hf : Monotone f)
    (x y : Point) (q : ℝ) (hq : ‖y - x‖ ≤ q) :
    ‖f y - f x‖ ≤ f (x + (q, q)) - f (x - (q, q)) := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hq
  have hxy := norm_prod_le_iff.mp hq
  change |y.1 - x.1| ≤ q ∧ |y.2 - x.2| ≤ q at hxy
  rw [abs_le, abs_le] at hxy
  have hlow : x - (q, q) ≤ y := by
    constructor <;> dsimp <;> linarith only [hxy.1.1, hxy.2.1]
  have hup : y ≤ x + (q, q) := by
    constructor <;> dsimp <;> linarith only [hxy.1.2, hxy.2.2]
  have hlowx : x - (q, q) ≤ x := by constructor <;> dsimp <;> linarith
  have hupx : x ≤ x + (q, q) := by constructor <;> dsimp <;> linarith
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith only [hf hlow, hf hup, hf hlowx, hf hupx]

theorem slopePiece_bound {f : Point → ℝ} (hf : Monotone f) (m : ℕ)
    {x : Point} (hx : x ∈ slopePiece f m) (y : Point) :
    ‖f y - f x‖ ≤ (m : ℝ) * ‖y - x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hm : 0 < (m : ℝ) + 1 := by positivity
  obtain ⟨q, hq, hq'⟩ := exists_rat_btwn
    (show ‖y - x‖ < ‖y - x‖ + ε / (m + 1 : ℝ) by linarith only [div_pos hε hm])
  have hq0 : 0 < q := by exact_mod_cast (lt_of_le_of_lt (norm_nonneg _) hq)
  have hh := (monotone_chord_bound hf x y q hq.le).trans (hx q hq0)
  have hq'' : (q : ℝ) - ‖y - x‖ < ε / (m + 1 : ℝ) := by linarith only [hq']
  have hmul := (lt_div_iff₀ hm).mp hq''
  nlinarith only [hh, hmul, hq]

theorem mem_slopePiece_of_diagonal_differentiable {f : Point → ℝ} {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B) {x : Point}
    (hd : DifferentiableAt ℝ (fun t : ℝ => f (x + (t, t))) 0) :
    ∃ m, x ∈ slopePiece f m := by
  obtain ⟨C, hC, hc⟩ := hd.hasFDerivAt.isBigO_sub.exists_pos
  obtain ⟨δ, hδ, hδC⟩ := Metric.eventually_nhds_iff.mp hc.bound
  obtain ⟨m, hm⟩ := exists_nat_ge (max (2 * C) (2 * B / δ))
  have hmC := (le_max_left (2 * C) (2 * B / δ)).trans hm
  have hmB := (le_max_right (2 * C) (2 * B / δ)).trans hm
  refine ⟨m, ?_⟩
  intro q hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  by_cases hqd : (q : ℝ) < δ
  · have hp := hδC (y := (q : ℝ)) (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos hq0] using hqd)
    have hn := hδC (y := -(q : ℝ)) (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos hq0] using hqd)
    simp only [sub_zero, Real.norm_eq_abs, abs_of_pos hq0, abs_neg] at hp hn
    have he : x + (-(q : ℝ), -(q : ℝ)) = x - ((q : ℝ), (q : ℝ)) := by ext <;> simp [sub_eq_add_neg]
    rw [he] at hn
    have hpu := (abs_le.mp hp).2
    have hnl := (abs_le.mp hn).1
    nlinarith only [hpu, hnl, mul_le_mul_of_nonneg_right hmC hq0.le]
  · have hb1 := (abs_le.mp (show |f (x + ((q : ℝ), (q : ℝ)))| ≤ B by simpa using hb _)).2
    have hb2 := (abs_le.mp (show |f (x - ((q : ℝ), (q : ℝ)))| ≤ B by simpa using hb _)).1
    have hB := (div_le_iff₀ hδ).mp hmB
    have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt hqd) (show 0 ≤ (m : ℝ) by positivity)
    nlinarith only [hb1, hb2, hB, hmul]

theorem bounded_monotone_ae_differentiable {f : Point → ℝ} (hf : Monotone f)
    (hfmeas : Measurable f) {B : ℝ} (hb : ∀ x, ‖f x‖ ≤ B) :
    ∀ᵐ x ∂(volume : Measure Point), DifferentiableAt ℝ f x := by
  apply ae_differentiable_of_pointwise_lipschitz_pieces (slopePiece f)
    (measurableSet_slopePiece hfmeas) (fun n z hz y => slopePiece_bound hf n hz y)
  let L : ℝ →ₗ[ℝ] Point := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).prod LinearMap.id
  have hS : MeasurableSet {x | ∃ n, x ∈ slopePiece f n} := by
    simpa only [ofPred_exists, Set.ofPred_mem_eq] using
      MeasurableSet.iUnion (measurableSet_slopePiece hfmeas)
  apply ae_mem_of_ae_add_linearMap_mem L volume volume hS
  intro p
  have hg : Monotone (fun t : ℝ => f (p + (t, t))) := by
    intro s t hst
    apply hf
    constructor <;> dsimp <;> linarith only [hst]
  filter_upwards [hg.ae_differentiableAt] with s hs
  apply mem_slopePiece_of_diagonal_differentiable hb
  have hs' : DifferentiableAt ℝ (fun t => f (p + (t, t))) (s + (0 : ℝ)) := by simpa using hs
  have hh := hs'.comp 0 ((differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ => t) 0).const_add s)
  have he : (fun t : ℝ => f (p + L s + (t, t))) =
      (fun t : ℝ => f (p + (t, t))) ∘ (fun t : ℝ => s + t) := by
    funext t
    congr 1
    ext <;> simp [L] <;> ring
  rw [he]
  exact hh

end Calculus

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

namespace RankLimit

open Filter MeasureTheory Set Metric
open scoped Topology

lemma lowerGrid_monotone (g : RatPoint → unitInterval) : Monotone (lowerGrid g) := by
  intro x y hxy
  apply iSup_le
  intro q
  by_cases hq : (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2
  · have hqy : (q.1 : ℝ) < y.1 ∧ (q.2 : ℝ) < y.2 :=
      ⟨hq.1.trans_le hxy.1, hq.2.trans_le hxy.2⟩
    simpa only [lowerGrid, ite_eq_left hq, ite_eq_left hqy] using
      (le_iSup (fun r : RatPoint =>
        if (r.1 : ℝ) < y.1 ∧ (r.2 : ℝ) < y.2 then g r else ⊥) q)
  · simp only [ite_eq_right hq, bot_le]

lemma lowerGrid_measurable (g : RatPoint → unitInterval) : Measurable (lowerGrid g) := by
  apply Measurable.iSup
  intro q
  exact Measurable.ite
    ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_const continuous_snd)).measurableSet
    measurable_const measurable_const

lemma grid_le_lowerGrid {g : RatPoint → unitInterval} {q : RatPoint} {x : Point}
    (hq : (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2) : g q ≤ lowerGrid g x := by
  simpa only [lowerGrid, ite_eq_left hq] using
    (le_iSup (fun r : RatPoint =>
      if (r.1 : ℝ) < x.1 ∧ (r.2 : ℝ) < x.2 then g r else ⊥) q)

end RankLimit

end PlanarHalving

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.RankCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
namespace PlanarHalving.RankCoordinates

variable {lA uA lB uB : ℝ} (A : Coordinate lA uA) (B : Coordinate lB uB)

namespace Coordinate
variable {lR uR lS uS : ℝ} (R : Coordinate lR uR) (S : Coordinate lS uS)

lemma strictMono_along_level (hgap : uR < lS) (v : UnitOpen) :
    StrictMono (fun x => R.value (x,S.level x v)) := by
  intro x x' h
  have hh := R.translate_upper x (S.level x v) (x'-x) (sub_nonneg.mpr h.le)
  rw [show x+(x'-x) = x' by ring] at hh
  have hprod : uR*(x'-x) < lS*(x'-x) := mul_lt_mul_of_pos_right hgap (sub_pos.mpr h)
  have hs := (S.level_slope h.le v).1
  exact hh.trans_lt (R.strict_vertical x' (by linarith :
    S.level x v+uR*(x'-x) < S.level x' v))

lemma strictAnti_along_level (hgap : uS < lR) (v : UnitOpen) :
    StrictAnti (fun x => R.value (x,S.level x v)) := by
  intro x x' h
  have hh := R.translate_lower x (S.level x v) (x'-x) (sub_nonneg.mpr h.le)
  rw [show x+(x'-x) = x' by ring] at hh
  have hprod : uS*(x'-x) < lR*(x'-x) := mul_lt_mul_of_pos_right hgap (sub_pos.mpr h)
  have hs := (S.level_slope h.le v).2
  exact (R.strict_vertical x' (by linarith :
    S.level x' v < S.level x v+lR*(x'-x))).trans_le hh

end Coordinate

lemma value_pair_inverse_fst (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    A.value ((pairHomeomorph A B hgap).symm v) = v.1 :=
  congrArg (fun w : UnitOpen × UnitOpen => (w.1:ℝ)) ((pairHomeomorph A B hgap).apply_symm_apply v)

lemma value_pair_inverse_snd (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    B.value ((pairHomeomorph A B hgap).symm v) = v.2 :=
  congrArg (fun w : UnitOpen × UnitOpen => (w.2:ℝ)) ((pairHomeomorph A B hgap).apply_symm_apply v)

lemma pair_inverse_snd_levelA (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ((pairHomeomorph A B hgap).symm v).2 = A.level ((pairHomeomorph A B hgap).symm v).1 v.1 := rfl

lemma pair_inverse_snd_levelB (hgap : uA < lB) (v : UnitOpen × UnitOpen) :
    ((pairHomeomorph A B hgap).symm v).2 = B.level ((pairHomeomorph A B hgap).symm v).1 v.2 := by
  apply (B.strict_vertical ((pairHomeomorph A B hgap).symm v).1).injective
  dsimp only
  rw [B.value_level]
  exact value_pair_inverse_snd A B hgap v

lemma inverseX_mono_left (hgap : uA < lB) (v : UnitOpen) :
    Monotone (fun u : UnitOpen => ((pairHomeomorph A B hgap).symm (u,v)).1) := by
  intro u u' huu
  apply (A.strictMono_along_level B hgap v).le_iff_le.mp
  have h₁ := value_pair_inverse_fst A B hgap (u,v)
  have h₂ := value_pair_inverse_fst A B hgap (u',v)
  conv_lhs at h₁ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v))]
  conv_lhs at h₂ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u',v))]
  rw [pair_inverse_snd_levelB] at h₁ h₂
  change A.value (_, B.level _ v) = (u:ℝ) at h₁
  change A.value (_, B.level _ v) = (u':ℝ) at h₂
  rw [h₁,h₂]
  exact huu

lemma inverseX_anti_right (hgap : uA < lB) (u : UnitOpen) :
    Antitone (fun v : UnitOpen => ((pairHomeomorph A B hgap).symm (u,v)).1) := by
  intro v v' hvv
  apply (B.strictAnti_along_level A hgap u).le_iff_ge.mp
  have h₁ := value_pair_inverse_snd A B hgap (u,v)
  have h₂ := value_pair_inverse_snd A B hgap (u,v')
  conv_lhs at h₁ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v))]
  conv_lhs at h₂ => rw [← Prod.eta ((pairHomeomorph A B hgap).symm (u,v'))]
  rw [pair_inverse_snd_levelA] at h₁ h₂
  change B.value (_, A.level _ u) = (v:ℝ) at h₁
  change B.value (_, A.level _ u) = (v':ℝ) at h₂
  rw [h₁,h₂]
  exact hvv

lemma inCoordinates_eq_levelA {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) :
    inCoordinates A B hgap C v = C.value
      (((pairHomeomorph A B hgap).symm v).1,
       A.level ((pairHomeomorph A B hgap).symm v).1 v.1) := rfl

lemma inCoordinates_eq_levelB {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (v : UnitOpen × UnitOpen) :
    inCoordinates A B hgap C v = C.value
      (((pairHomeomorph A B hgap).symm v).1,
       B.level ((pairHomeomorph A B hgap).symm v).1 v.2) := by
  unfold inCoordinates
  conv_lhs => rw [← Prod.eta ((pairHomeomorph A B hgap).symm v)]
  rw [pair_inverse_snd_levelB]

lemma inCoordinates_monotone_left {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hCB : uC < lB) (v : UnitOpen) :
    Monotone (fun u : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro u u' h
  dsimp only
  rw [inCoordinates_eq_levelB, inCoordinates_eq_levelB]
  exact (C.strictMono_along_level B hCB v).monotone (inverseX_mono_left A B hgap v h)

lemma inCoordinates_antitone_left {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hBC : uB < lC) (v : UnitOpen) :
    Antitone (fun u : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro u u' h
  dsimp only
  rw [inCoordinates_eq_levelB, inCoordinates_eq_levelB]
  exact (C.strictAnti_along_level B hBC v).antitone (inverseX_mono_left A B hgap v h)

lemma inCoordinates_antitone_right {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hCA : uC < lA) (u : UnitOpen) :
    Antitone (fun v : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro v v' h
  dsimp only
  rw [inCoordinates_eq_levelA, inCoordinates_eq_levelA]
  exact (C.strictMono_along_level A hCA u).monotone (inverseX_anti_right A B hgap u h)

lemma inCoordinates_monotone_right {lC uC : ℝ} (hgap : uA < lB)
    (C : Coordinate lC uC) (hAC : uA < lC) (u : UnitOpen) :
    Monotone (fun v : UnitOpen => inCoordinates A B hgap C (u,v)) := by
  intro v v' h
  dsimp only
  rw [inCoordinates_eq_levelA, inCoordinates_eq_levelA]
  exact (C.strictAnti_along_level A hAC u).antitone (inverseX_anti_right A B hgap u h)

end PlanarHalving.RankCoordinates

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

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

theorem subsequence_of_asymptotic_continuity
    {X Y : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MetricSpace Y] [CompleteSpace Y]
    (f : ℕ → X → Y) (G : Set X) (hG : G.Nonempty) (K : Set Y) (hK : IsCompact K)
    (hbounded : ∀ n p, p ∈ G → f n p ∈ K)
    (hcont : ∀ p ∈ G, ∀ ε > 0, ∃ r > 0,
      ∀ᶠ n in atTop, ∀ q, dist q p < r → dist (f n q) (f n p) ≤ ε) :
    ∃ (φ : ℕ → ℕ) (l : G → Y), StrictMono φ ∧
      (∀ p, l p ∈ K) ∧
      (∀ p : G, ∀ u : ℕ → X, Tendsto u atTop (𝓝 (p : X)) →
        Tendsto (fun n => f (φ n) (u n)) atTop (𝓝 (l p))) := by
  classical
  let : Nonempty G := hG.to_subtype
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq G
  let F : ℕ → ℕ → K := fun n j => ⟨f n (q j), hbounded n (q j) (q j).property⟩
  obtain ⟨g,φ,hφ,hg⟩ := CompactSpace.tendsto_subseq F
  have hgrid (j : ℕ) : Tendsto (fun n => f (φ n) (q j)) atTop (𝓝 (g j : Y)) :=
    continuous_subtype_val.tendsto _ |>.comp ((tendsto_pi_nhds.mp hg) j)
  have hcauchy (p : G) : CauchySeq (fun n => f (φ n) p) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨r,hr,hrf⟩ := hcont p p.property (ε/4) (by positivity)
    obtain ⟨j,hj⟩ := hq.exists_dist_lt p hr
    have hj' : dist (q j : X) p < r := by simpa only [Subtype.dist_eq, dist_comm] using hj
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hφ.tendsto_atTop.eventually hrf)
    obtain ⟨N',hN'⟩ := Metric.cauchySeq_iff.mp (hgrid j).cauchySeq (ε/4) (by positivity)
    refine ⟨max N N',fun m hm n hn => ?_⟩
    have hm' := hN m (le_trans (le_max_left _ _) hm) (q j) hj'
    have hn' := hN n (le_trans (le_max_left _ _) hn) (q j) hj'
    have hmn := hN' m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
    have htri := dist_triangle4 (f (φ m) p) (f (φ m) (q j)) (f (φ n) (q j)) (f (φ n) p)
    rw [dist_comm (f (φ m) p) (f (φ m) (q j))] at htri
    linarith only [htri,hm',hn',hmn,hε]
  choose l hl using fun p => cauchySeq_tendsto_of_complete (hcauchy p)
  refine ⟨φ,l,hφ,?_,?_⟩
  · intro p
    exact hK.isClosed.mem_of_tendsto (hl p) (Eventually.of_forall (fun n => hbounded (φ n) p p.property))
  · intro p u hu
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨r,hr,hrf⟩ := hcont p p.property (ε/3) (by positivity)
    have hu' : ∀ᶠ n in atTop, dist (u n) (p : X) < r := (Metric.tendsto_nhds.mp hu) r hr
    have hl' : ∀ᶠ n in atTop, dist (f (φ n) p) (l p) < ε/3 :=
      (Metric.tendsto_nhds.mp (hl p)) (ε/3) (by positivity)
    apply eventually_atTop.mp
    filter_upwards [hφ.tendsto_atTop.eventually hrf,hu',hl'] with n hn hnu hnl
    have hh := hn (u n) hnu
    have ht := dist_triangle (f (φ n) (u n)) (f (φ n) p) (l p)
    linarith only [hh,ht,hnl,hε]

lemma asymptotic_continuity_of_radial
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (G : Set X) (r e : ℕ → ℝ)
    (hr : ∀ j, 0 < r j) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ p ∈ G, ∀ j, ∀ᶠ n in atTop,
      ∀ q, dist q p < r j → dist (f n q) (f n p) ≤ e j) :
    ∀ p ∈ G, ∀ ε > 0, ∃ δ > 0,
      ∀ᶠ n in atTop, ∀ q, dist q p < δ → dist (f n q) (f n p) ≤ ε := by
  intro p hp ε hε
  obtain ⟨j,hj⟩ := ((tendsto_order.mp he).2 ε hε).exists
  refine ⟨r j,hr j,?_⟩
  filter_upwards [hb p hp j] with n hn q hq
  exact (hn q hq).trans hj.le

lemma lower_distance_of_limit
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {p q : X} {x y : Y} (hp : Tendsto (fun n => f (φ n) p) atTop (𝓝 x))
    (hq : Tendsto (fun n => f (φ n) q) atTop (𝓝 y))
    {a : ℝ} (ha : ∀ᶠ n in atTop, a ≤ dist (f n p) (f n q)) : a ≤ dist x y := by
  exact ge_of_tendsto (hp.dist hq) (hφ.tendsto_atTop.eventually ha)

end PlanarHalving.Spatial
namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma geometric_scale {q h d : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (_hh : 0 < h) (hd : 0 < d) (hdh : d ≤ h) :
    ∃ j : ℕ, 1 ≤ j ∧ h*q^j < d ∧ q*d ≤ h*q^j := by
  have ht : Tendsto (fun j : ℕ => h*q^j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul h
  have hex : ∃ j : ℕ, h*q^j < d := ((tendsto_order.mp ht).2 d hd).exists
  let j := Nat.find hex
  have hj : h*q^j < d := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h
    simp only [h,pow_zero,mul_one] at hj
    exact (not_lt_of_ge hdh) hj
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
  have hprev : d ≤ h*q^(j-1) := by
    exact le_of_not_gt (Nat.find_min hex (show j-1 < j by omega))
  refine ⟨j,hj1,hj,?_⟩
  have hp : q^j = q^(j-1)*q := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hp]
  nlinarith only [mul_le_mul_of_nonneg_left hprev hq.le]

lemma geometric_lower_power {q h d s : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hh : 0 < h) (hd : 0 < d) (hdh : d ≤ h) (hs : 0 ≤ s) :
    ∃ j : ℕ, 1 ≤ j ∧ h*q^j < d ∧
      q^s * (q/h)^s * d^s ≤ (q^s)^(j+1) := by
  obtain ⟨j,hj,hjd,hdj⟩ := geometric_scale hq hq1 hh hd hdh
  refine ⟨j,hj,hjd,?_⟩
  have hdiv : q/h*d ≤ q^j := by
    have hv : q*d/h ≤ q^j := (div_le_iff₀ hh).mpr (by nlinarith only [hdj])
    convert hv using 1
    ring
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ q/h*d) hdiv hs
  rw [Real.mul_rpow (by positivity) hd.le] at hp
  rw [pow_succ, Real.rpow_pow_comm hq.le]
  have ht := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hq.le s)
  nlinarith only [ht]

lemma inverse_holder_of_radial_limits
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (G : Set X) (l : G → Y)
    (hl : ∀ p : G, Tendsto (fun n => f (φ n) p) atTop (𝓝 (l p)))
    {q h s : ℝ} (hq : 0 < q) (hq1 : q < 1) (hh : 0 < h) (hs : 0 < s)
    (hdiam : ∀ p p' : G, dist (p : X) p' ≤ h)
    (hlower : ∀ p : G, ∀ j : ℕ, 1 ≤ j → ∀ᶠ n in atTop,
      ∀ p' : G, h*q^j < dist (p : X) p' → (q^s)^(j+1) ≤ dist (f n p) (f n p')) :
    ∀ p p' : G, (q^s * (q/h)^s) * dist (p : X) p' ^ s ≤ dist (l p) (l p') := by
  intro p p'
  by_cases hpp : p = p'
  · subst p'
    simp [Real.zero_rpow hs.ne']
  · have hd : 0 < dist (p : X) p' := dist_pos.mpr (Subtype.coe_ne_coe.mpr hpp)
    obtain ⟨j,hj,hjd,hdj⟩ := geometric_lower_power hq hq1 hh hd (hdiam p p') hs.le
    apply hdj.trans
    apply lower_distance_of_limit f φ hφ (hl p) (hl p')
    filter_upwards [hlower p j hj] with n hn
    exact hn p' hjd

end PlanarHalving.Spatial

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

end PlanarHalving.Batches
namespace PlanarHalving.RankLimits
open Batches TimeWindows Limits MeasureTheory Set Filter
open scoped Topology NNReal ENNReal unitInterval PiCountable

lemma Configuration.vertices_mass_le (F : Configuration) (J : Window) : (F.vertices J).mass ≤ 1 :=
  (F.system.timeWindow J).vertexMeasure_mass_le _
lemma Configuration.edgeTime_mass (F : Configuration) : F.edgeTime.mass=1 := F.system.labelTimeMeasure_mass _
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
namespace PlanarHalving.Batches
open Set PlaneGraph RankCoordinates TimeWindows
open scoped unitInterval
variable {n R k a : ℕ} {P : Fin n → Point}

lemma System.rankGraphs_eq (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) :
    (S.rankGraphs hP J hJ).graph=(S.rankFamily hP J).graph :=
  (S.rankFamily_spec hP J hJ).choose_spec.1.symm

lemma System.rankCoordinate_value (S : @System n R k a P) [NeZero n] [NeZero a] [NeZero R]
    (hP : Generic P) (J : Window) (hJ : 0 < length R J) (p : Point) :
    (S.rankCoordinate hP J hJ).value p=(S.labels hP p J : ℝ) := by
  change smoothed (S.rankGraphs hP J hJ).graph _ p=smoothed (S.rankFamily hP J).graph _ p
  rw [S.rankGraphs_eq]

lemma System.rankHomeomorph_coordinates (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (p : Point) :
    (((S.rankHomeomorph hP hAB hA hB) p).1 : ℝ)=(S.labels hP p A : ℝ) ∧
    (((S.rankHomeomorph hP hAB hA hB) p).2 : ℝ)=(S.labels hP p B : ℝ) :=
  ⟨S.rankCoordinate_value hP A hA p,S.rankCoordinate_value hP B hB p⟩

lemma System.rankInCoordinates_eq (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B : Window} (hAB : Before A B)
    (hA : 0 < length R A) (hB : 0 < length R B) (C : Window) (hC : 0 < length R C) :
    S.rankInCoordinates hP hAB hA hB C=
      inCoordinates (S.rankCoordinate hP A hA) (S.rankCoordinate hP B hB)
        (S.timeWindow_graph_gap hAB _ _) (S.rankCoordinate hP C hC) := by
  funext p
  exact (S.rankCoordinate_value hP C hC _).symm

lemma System.rankInCoordinates_before (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B C : Window}
    (hAB : Before A B) (hCA : Before C A) (hCB : Before C B)
    (hA : 0 < length R A) (hB : 0 < length R B) (hC : 0 < length R C) :
    (∀ v, Monotone (fun u => S.rankInCoordinates hP hAB hA hB C (u,v))) ∧
    (∀ u, Antitone (fun v => S.rankInCoordinates hP hAB hA hB C (u,v))) := by
  rw [S.rankInCoordinates_eq hP hAB hA hB C hC]
  exact ⟨fun v => inCoordinates_monotone_left _ _ _ _ (S.timeWindow_graph_gap hCB _ _) v,
    fun u => inCoordinates_antitone_right _ _ _ _ (S.timeWindow_graph_gap hCA _ _) u⟩

lemma System.rankInCoordinates_after (S : @System n R k a P)
    [NeZero n] [NeZero a] [NeZero R] (hP : Generic P) {A B C : Window}
    (hAB : Before A B) (hAC : Before A C) (hBC : Before B C)
    (hA : 0 < length R A) (hB : 0 < length R B) (hC : 0 < length R C) :
    (∀ v, Antitone (fun u => S.rankInCoordinates hP hAB hA hB C (u,v))) ∧
    (∀ u, Monotone (fun v => S.rankInCoordinates hP hAB hA hB C (u,v))) := by
  rw [S.rankInCoordinates_eq hP hAB hA hB C hC]
  exact ⟨fun v => inCoordinates_antitone_left _ _ _ _ (S.timeWindow_graph_gap hBC _ _) v,
    fun u => inCoordinates_monotone_right _ _ _ _ (S.timeWindow_graph_gap hAC _ _) u⟩

end PlanarHalving.Batches
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

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

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

namespace PlanarHalving.RankLimit
open Filter Set MeasureTheory Metric
open scoped Topology unitInterval

lemma extendRank_monotone {X : Type*} (p : X → Point) (c : X → I) :
    Monotone (extendRank p c) := by
  intro x y hxy
  apply iSup_le
  intro a
  by_cases ha : p a ≤ x
  · simpa only [extendRank, ite_eq_left ha, ite_eq_left (ha.trans hxy)] using
      (le_iSup (fun b : X => if p b ≤ y then c b else ⊥) a)
  · simp only [ite_eq_right ha, bot_le]

lemma extendRank_eq {X : Type*} (p : X → Point) (c : X → I)
    (hc : ∀ a b, p a ≤ p b → c a ≤ c b) (a : X) : extendRank p c (p a) = c a := by
  apply le_antisymm
  · apply iSup_le
    intro b
    split_ifs with hb
    · exact hc b a hb
    · exact bot_le
  · simpa only [extendRank, ite_eq_left le_rfl] using
      (le_iSup (fun b : X => if p b ≤ p a then c b else ⊥) a)

theorem joint_tendsto_of_grid {f : ℕ → Point → I}
    (hf : ∀ n, Monotone (f n)) {g : RatPoint → I}
    (hg : ∀ q, Tendsto (fun n => f n (ratPoint q)) atTop (𝓝 (g q)))
    {x : Point} (hc : ContinuousAt (lowerGrid g) x) :
    Tendsto (fun q : ℕ × Point => f q.1 q.2) (atTop ×ˢ 𝓝 x) (𝓝 (lowerGrid g x)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp ha
    by_cases hqx : (q.1 : ℝ) < x.1 ∧ (q.2 : ℝ) < x.2
    · simp only [ite_eq_left hqx] at hq
      filter_upwards [(tendsto_order.mp ((hg q).comp tendsto_fst)).1 a hq,
        (tendsto_order.mp ((continuous_fst.tendsto x).comp tendsto_snd)).1 _ hqx.1,
        (tendsto_order.mp ((continuous_snd.tendsto x).comp tendsto_snd)).1 _ hqx.2]
        with n hn hn₁ hn₂
      exact hn.trans_le (hf n.1 ⟨hn₁.le, hn₂.le⟩)
    · simp only [ite_eq_right hqx, not_lt_bot] at hq
  · intro a ha
    have hn := hc.preimage_mem_nhds (isOpen_Iio.mem_nhds ha)
    obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hn
    let b : Point := x + (δ / 2, δ / 2)
    have hb : b ∈ ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [b, add_sub_cancel_left, Prod.norm_def, Real.norm_eq_abs,
        abs_of_pos (half_pos hδ), max_self]
      linarith only [hδ]
    have hba : lowerGrid g b < a := hδU hb
    obtain ⟨r₁, hxr₁, hr₁b⟩ := exists_rat_btwn
      (show x.1 < b.1 by dsimp [b]; linarith only [hδ])
    obtain ⟨r₂, hxr₂, hr₂b⟩ := exists_rat_btwn
      (show x.2 < b.2 by dsimp [b]; linarith only [hδ])
    let r : RatPoint := (r₁, r₂)
    have hra : g r < a := (grid_le_lowerGrid ⟨hr₁b, hr₂b⟩).trans_lt hba
    filter_upwards [(tendsto_order.mp ((hg r).comp tendsto_fst)).2 a hra,
      (tendsto_order.mp ((continuous_fst.tendsto x).comp tendsto_snd)).2 _ hxr₁,
      (tendsto_order.mp ((continuous_snd.tendsto x).comp tendsto_snd)).2 _ hxr₂]
      with n hn hn₁ hn₂
    exact (hf n.1 ⟨hn₁.le, hn₂.le⟩).trans_lt hn

theorem monotone_joint_subsequence {ι : Type*} [Countable ι]
    (f : ℕ → ι → Point → I) (hf : ∀ n i, Monotone (f n i)) :
    ∃ (φ : ℕ → ℕ) (F : ι → Point → I), StrictMono φ ∧
      (∀ i, Monotone (F i) ∧ Measurable (F i)) ∧
      (∀ i x, ContinuousAt (F i) x →
        Tendsto (fun q : ℕ × Point => f (φ q.1) i q.2)
          (atTop ×ˢ 𝓝 x) (𝓝 (F i x))) := by
  obtain ⟨g, φ, hφ, hg⟩ := CompactSpace.tendsto_subseq
    (fun n i q => f n i (ratPoint q))
  refine ⟨φ, fun i => lowerGrid (g i), hφ,
    fun i => ⟨lowerGrid_monotone _, lowerGrid_measurable _⟩, ?_⟩
  intro i x hx
  apply joint_tendsto_of_grid (fun n => hf (φ n) i) _ hx
  intro q
  exact ((tendsto_pi_nhds.mp hg) i).apply_nhds q

end PlanarHalving.RankLimit

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

lemma Configuration.extendedRank_monotone (F : Configuration) (b : Bool) (A B C : Window) :
    Monotone (F.extendedRank b A B C) := RankLimit.extendRank_monotone _ _

lemma Configuration.extendedRank_eq (F : Configuration) (b : Bool) {A B C : Window}
    (hAB : Before A B)
    (hC : if b then Before C A ∧ Before C B else Before A C ∧ Before B C)
    (hA : 0 < length F.R A) (hB : 0 < length F.R B) (hCl : 0 < length F.R C)
    (p : Point) :
    F.extendedRank b A B C (pairCoordinates b A B (F.system.labels F.generic p)) =
      F.system.labels F.generic p C := by
  apply RankLimit.extendRank_eq
  intro x y hxy
  let H := F.system.rankHomeomorph F.generic hAB hA hB
  have hx := F.system.rankHomeomorph_coordinates F.generic hAB hA hB x
  have hy := F.system.rankHomeomorph_coordinates F.generic hAB hA hB y
  change ((F.system.labels F.generic x C : I) : ℝ) ≤ (F.system.labels F.generic y C : ℝ)
  have he (q : Point) : F.system.rankInCoordinates F.generic hAB hA hB C (H q) =
      (F.system.labels F.generic q C : ℝ) := by
    simp only [Batches.System.rankInCoordinates, H, Homeomorph.symm_apply_apply]
  rw [← he x, ← he y]
  cases b
  · simp only [Bool.false_eq_true, ite_false] at hC
    have hm := F.system.rankInCoordinates_after F.generic hAB hC.1 hC.2 hA hB hCl
    have hh : (H y).1 ≤ (H x).1 ∧ (H x).2 ≤ (H y).2 := by
      change ((H y).1 : ℝ) ≤ ((H x).1 : ℝ) ∧ ((H x).2 : ℝ) ≤ ((H y).2 : ℝ)
      rw [hy.1,hx.1,hx.2,hy.2]
      simpa only [pairCoordinates, signedPair, Bool.false_eq_true, ite_false, Prod.mk_le_mk,
        neg_le_neg_iff] using hxy
    exact ((hm.1 (H x).2) hh.1).trans ((hm.2 (H y).1) hh.2)
  · simp only [ite_true] at hC
    have hm := F.system.rankInCoordinates_before F.generic hAB hC.1 hC.2 hA hB hCl
    have hh : (H x).1 ≤ (H y).1 ∧ (H y).2 ≤ (H x).2 := by
      change ((H x).1 : ℝ) ≤ ((H y).1 : ℝ) ∧ ((H y).2 : ℝ) ≤ ((H x).2 : ℝ)
      rw [hx.1,hy.1,hy.2,hx.2]
      simpa only [pairCoordinates, signedPair, ite_true, Prod.mk_le_mk,neg_le_neg_iff] using hxy
    exact ((hm.1 (H x).2) hh.1).trans ((hm.2 (H y).1) hh.2)

end PlanarHalving.RankLimits

namespace PlanarHalving.Limits
open Set Filter MeasureTheory Metric
open scoped Topology

lemma support_coordinate_identity {X Y T : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [TopologicalSpace Y] [MetricSpace T]
    {μs : ℕ → FiniteMeasure X} {μ : FiniteMeasure X}
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : X → Y) (hp : Continuous p)
    (c : X → T) (hc : Continuous c) (f : ℕ → Y → T)
    (hid : ∀ᶠ n in atTop, ∀ᵐ z ∂(μs n : Measure X), c z = f n (p z))
    {z : X} (hz : z ∈ (μ : Measure X).support) {v : T}
    (hf : Tendsto (fun q : ℕ × Y => f q.1 q.2) (atTop ×ˢ 𝓝 (p z)) (𝓝 v)) :
    c z = v := by
  by_contra hne
  have hd : 0 < dist (c z) v := dist_pos.mpr hne
  have hp' : Tendsto (fun q : ℕ × X => (q.1,p q.2)) (atTop ×ˢ 𝓝 z)
      (atTop ×ˢ 𝓝 (p z)) := tendsto_fst.prodMk ((hp.tendsto z).comp tendsto_snd)
  have hdlim := ((hc.tendsto z).comp tendsto_snd).dist (hf.comp hp')
  have he := (tendsto_order.mp hdlim).1 0 hd
  obtain ⟨pa,hpa,pb,hpb,hbad⟩ := Filter.eventually_prod_iff.mp he
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hpb
  let : Nonempty X := ⟨z⟩
  have hpos : 0 < (μ (ball z (r/2)) : ℝ) := by
    have hh := (Measure.mem_support_iff_forall z).mp hz _ (ball_mem_nhds _ (half_pos hr))
    rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
    exact_mod_cast hh
  have helow := eventually_thickening_lower hμ (ball z (r/2)) (half_pos hr) hpos
  obtain ⟨n,hn,hni,hnlow⟩ := (hpa.and (hid.and helow)).exists
  have hzero : (μs n : Measure X) (ball z r) = 0 := by
    apply measure_mono_null (t := {w | c w ≠ f n (p w)})
    · intro w hw
      exact dist_pos.mp (hbad hn (hball hw))
    · exact ae_iff.mp hni
  have hsub : thickening (r/2) (ball z (r/2)) ⊆ ball z r := by
    simpa only [add_halves] using thickening_ball z (r/2) (r/2)
  have hzero' := measure_mono_null hsub hzero
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ENNReal.coe_eq_zero] at hzero'
  rw [hzero'] at hnlow
  exact (lt_irrefl (0 : ℝ)) hnlow

end PlanarHalving.Limits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Limits
open scoped Topology unitInterval

lemma Configuration.points_ae (F : Configuration) (H : Labels → Prop)
    (hH : ∀ p, H (F.label p)) : ∀ᵐ z ∂(F.points : Measure Labels), H z := by
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  simpa only [ae_dirac_eq,Filter.eventually_pure,Function.comp_apply] using hH (F.point i)

lemma Converges.subseq {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : Converges (F ∘ φ) L :=
  ⟨h.points.comp hφ.tendsto_atTop,fun J => (h.vertices J).comp hφ.tendsto_atTop,
    h.edgeTime.comp hφ.tendsto_atTop,fun J => (h.timeRestrict J).comp hφ.tendsto_atTop,
    fun A B => (h.crossings A B).comp hφ.tendsto_atTop⟩

theorem Converges.rank_analytic {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (b : Bool) {A B : Window} (hAB : Before A B)
    {ι : Type*} [Countable ι] (C : ι → Window)
    (hC : ∀ i, if b then Before (C i) A ∧ Before (C i) B else Before A (C i) ∧ Before B (C i)) :
    ∃ (φ : ℕ → ℕ) (G : ι → Point → I), StrictMono φ ∧
      (∀ i, Monotone (G i) ∧ Measurable (G i)) ∧
      (∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x : ℝ)) p) ∧
      (∀ i z, z ∈ (L.points : Measure Labels).support →
        ContinuousAt (G i) (pairCoordinates b A B z) →
        z (C i) = G i (pairCoordinates b A B z)) ∧
      (∀ i p, ContinuousAt (G i) p →
        Tendsto (fun q : ℕ × Point => (F (φ q.1)).extendedRank b A B (C i) q.2)
          (atTop ×ˢ 𝓝 p) (𝓝 (G i p))) := by
  obtain ⟨φ,G,hφ,hG,hlim⟩ := RankLimit.monotone_joint_subsequence
    (fun n i => (F n).extendedRank b A B (C i)) (fun n i => (F n).extendedRank_monotone b A B (C i))
  refine ⟨φ,G,hφ,hG,?_,?_,hlim⟩
  · intro i
    apply Calculus.bounded_monotone_ae_differentiable (fun x y hxy => (hG i).1 hxy)
      (measurable_subtype_coe.comp (hG i).2) (B:=1)
    intro x
    simpa only [Real.norm_eq_abs,abs_of_nonneg (G i x).property.1] using (G i x).property.2
  · intro i z hz hcont
    apply support_coordinate_identity (h.subseq hφ).points (pairCoordinates b A B)
      (continuous_pairCoordinates b A B) (fun z => z (C i)) (continuous_apply (C i))
      (fun n => (F (φ n)).extendedRank b A B (C i)) _ hz (hlim i _ hcont)
    have hR' : Tendsto (fun n => (F (φ n)).R) atTop atTop := hR.comp hφ.tendsto_atTop
    filter_upwards [eventually_length_pos _ hR' A,eventually_length_pos _ hR' B,
      eventually_length_pos _ hR' (C i)] with n hnA hnB hnC
    apply Configuration.points_ae
    intro p
    exact ((F (φ n)).extendedRank_eq b hAB (hC i) hnA hnB hnC p).symm

end PlanarHalving.RankLimits

namespace PlanarHalving.Limits
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma restrict_ac_withDensity {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ≥0∞) (hf : Measurable f) {A : Set X} (_hA : MeasurableSet A)
    (hpos : ∀ x ∈ A, f x ≠ 0) : μ.restrict A ≪ μ.withDensity f := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hB hzero
  rw [Measure.restrict_apply hB]
  have hh := (withDensity_apply_eq_zero hf).mp hzero
  apply measure_mono_null (t := {x | f x ≠ 0} ∩ B)
  · intro x hx
    exact ⟨hpos x hx.2,hx.1⟩
  · exact hh

end PlanarHalving.Limits

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

lemma upper_sub_lower (J : Window) : (upper J : ℝ) - (lower J : ℝ) = 1/(2:ℝ)^J.1 := by
  simp only [upper, lower, UniformPartition.boundary, Fin.val_succ, Fin.val_castSucc,
    Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  ring

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

lemma ae_avoid_boundaries (μ : Measure I) [NullSingletonClass μ] :
    ∀ᵐ t ∂μ, ∀ m (i : Fin (2^m+1)), t ≠ UniformPartition.boundary (2^m) i := by
  rw [ae_all_iff]
  intro m
  rw [ae_all_iff]
  intro i
  exact μ.ae_ne _

end PlanarHalving.TimeWindows

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped unitInterval Topology

lemma unitPair_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving (fun p : I × I => ((p.1 : ℝ),(p.2 : ℝ))) volume volume := by
  have hi : Measure.QuasiMeasurePreserving ((↑) : I → ℝ) volume volume :=
    unitInterval.measurePreserving_coe.quasiMeasurePreserving.mono_right (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self))
  exact QuasiMeasurePreserving.prodMap hi hi

lemma signedPair_measurePreserving (b : Bool) : MeasurePreserving (signedPair b) volume volume := by
  cases b
  · exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  · exact (MeasurePreserving.id _).prod (Measure.measurePreserving_neg (volume : Measure ℝ))

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

lemma Converges.crossing_signed_projection {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    (b : Bool) {A B : Window} (hAB : Before A B) :
    (L.crossings A B : Measure Labels).map (pairCoordinates b A B) ≪ volume := by
  have hp : Measure.QuasiMeasurePreserving (fun z : Labels => ((z A : ℝ),(z B : ℝ)))
      (L.crossings A B : Measure Labels) volume :=
    ⟨by fun_prop,h.crossing_real_projection hR hM hAB⟩
  exact ((signedPair_measurePreserving b).quasiMeasurePreserving.comp hp).absolutelyContinuous

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
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates
open scoped Topology unitInterval

lemma Configuration.rankChart_apply (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) (p : Point) :
    F.rankChart hAB hA hB p = pairCoordinates true A B (F.system.labels F.generic p) := by
  change reflectSecond (((F.system.rankHomeomorph F.generic hAB hA hB) p).1,
    ((F.system.rankHomeomorph F.generic hAB hA hB) p).2) = _
  obtain ⟨he1,he2⟩ := F.system.rankHomeomorph_coordinates F.generic hAB hA hB p
  rw [he1,he2]
  rfl

lemma Configuration.rankChart_source (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    (F.rankChart hAB hA hB).source = univ := rfl

lemma Configuration.rankChart_target (F : Configuration) {A B : Window}
    (hAB : Before A B) (hA : 0 < length F.R A) (hB : 0 < length F.R B) :
    (F.rankChart hAB hA hB).target = Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  unfold Configuration.rankChart
  rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  change Set.range (fun x : Point => reflectSecond
    (((F.system.rankHomeomorph F.generic hAB hA hB) x).1,
     ((F.system.rankHomeomorph F.generic hAB hA hB) x).2)) = _
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨((F.system.rankHomeomorph F.generic hAB hA hB) x).1.property,
      by dsimp; constructor <;> linarith [((F.system.rankHomeomorph F.generic hAB hA hB) x).2.property.1,
        ((F.system.rankHomeomorph F.generic hAB hA hB) x).2.property.2]⟩
  · intro hp
    let q : UnitOpen × UnitOpen := (⟨p.1,hp.1⟩,⟨-p.2,by constructor <;> linarith [hp.2.1,hp.2.2]⟩)
    refine ⟨(F.system.rankHomeomorph F.generic hAB hA hB).symm q,?_⟩
    dsimp only
    rw [Homeomorph.apply_symm_apply]
    simp [q]

lemma Configuration.timeSlope_before (F : Configuration) {J : Window} {t : I}
    (h : t ≤ lower J) : F.timeSlope t ≤ (F.system.timeWindow J).slope 0 := by
  apply F.system.increasing.monotone
  change cut (time F.R) t ≤ start F.R J+0
  simpa only [Nat.add_zero, start, TimeWindows.lower] using cut_mono (time F.R) h

lemma Configuration.timeSlope_after (F : Configuration) {J : Window} {t : I}
    (h : upper J ≤ t) : (F.system.timeWindow J).slope (Fin.last (length F.R J)) ≤ F.timeSlope t := by
  apply F.system.increasing.monotone
  change start F.R J+length F.R J ≤ cut (time F.R) t
  rw [start_add_length]
  exact cut_mono (time F.R) h

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

lemma exists_positive_inside (μ : Measure I) [NullSingletonClass μ]
    {s t : I} (hpos : μ (Ioo s t) ≠ 0) :
    ∃ J : Window, s < lower J ∧ upper J < t ∧ μ (carrier J) ≠ 0 := by
  have hsupp : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  obtain ⟨x,hx,hxs,hxb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    ((hsupp.and (ae_avoid_boundaries μ)).filter_mono ae_restrict_le)
  have hmesh : Tendsto (fun m : ℕ => 1/(2:ℝ)^m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hsx : (s : ℝ) < x := hx.1
  have hxt : (x : ℝ) < t := hx.2
  obtain ⟨m,hm⟩ := (hmesh.eventually (gt_mem_nhds
    (show 0 < min ((x:ℝ)-s) ((t:ℝ)-x) by positivity))).exists
  obtain ⟨i,hi⟩ := UniformPartition.mem_some_cell (2^m) x
  let J : Window := ⟨m,i⟩
  have hJ := carrier_subset_Icc J hi
  have hxi : x ∈ Ioo (lower J) (upper J) :=
    ⟨lt_of_le_of_ne hJ.1 (Ne.symm (hxb m i.castSucc)),
      lt_of_le_of_ne hJ.2 (hxb m i.succ)⟩
  have hw := upper_sub_lower J
  have hj1 : (lower J : ℝ) ≤ x := hJ.1
  have hj2 : (x : ℝ) ≤ upper J := hJ.2
  have hm1 := (lt_min_iff.mp hm).1
  have hm2 := (lt_min_iff.mp hm).2
  dsimp [J] at hw
  refine ⟨J,?_,?_,?_⟩
  · change (s : ℝ) < lower J
    linarith
  · change (upper J : ℝ) < t
    linarith
  · exact ne_of_gt ((measure_mono (Ioo_subset_carrier J)).trans_lt'
      ((Measure.mem_support_iff_forall x).mp hxs _ (Ioo_mem_nhds hxi.1 hxi.2)))

end PlanarHalving.TimeWindows
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
-- module Solutions.OAIQW_PlanarHalving.LocalZoom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Zoom
open Set

lemma detPair_smul (u v : Point) (a b : ℝ) :
    detPair (a • u) (b • v)=a*b*detPair u v := by
  dsimp [detPair]; ring

lemma slope_frame {s₁ s₂ s₃ : ℝ} (h12 : s₁<s₂) (h23 : s₂<s₃) :
    ∃ (E : Point ≃L[ℝ] Point) (a b : ℝ), 0<a ∧ 0<b ∧
      E (1,0)=a • (1,s₁) ∧ E (0,1)=b • (1,s₃) ∧ E (1,1)=(1,s₂) := by
  let a := (s₃-s₂)/(s₃-s₁)
  let b := (s₂-s₁)/(s₃-s₁)
  have hden : 0<s₃-s₁ := sub_pos.mpr (h12.trans h23)
  have ha : 0<a := div_pos (sub_pos.mpr h23) hden
  have hb : 0<b := div_pos (sub_pos.mpr h12) hden
  have he : a • ((1,s₁) : Point)+b • ((1,s₃) : Point)=((1,s₂) : Point) := by
    ext <;> dsimp [a,b] <;> field_simp [hden.ne'] <;> ring
  have hdet : detPair (a • (1,s₁)) (b • (1,s₃)) ≠ 0 := by
    rw [detPair_smul]
    exact mul_ne_zero (mul_ne_zero ha.ne' hb.ne') (by simpa [detPair] using hden.ne')
  refine ⟨columnEquiv _ _ hdet,a,b,ha,hb,?_,?_,?_⟩
  · simp
  · simp
  · simpa using he

end PlanarHalving.Zoom

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows RankCoordinates Zoom
open scoped Topology unitInterval

lemma timeSlope_eventually_lt (F : ℕ → Configuration)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) {s t : I} (hst : s<t) :
    ∀ᶠ n in atTop, (F n).timeSlope s < (F n).timeSlope t := by
  have hst' : 0<(t:ℝ)-s := sub_pos.mpr hst
  have htR : Tendsto (fun n => ((F n).R:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hR
  filter_upwards [htR.eventually_gt_atTop (2/((t:ℝ)-s))] with n hn
  apply (F n).system.increasing
  have hs := (abs_le.mp (cut_time_error (F n).R s)).2
  have ht := (abs_le.mp (cut_time_error (F n).R t)).1
  have hp := (div_lt_iff₀ hst').mp hn
  have hc : (cut (time (F n).R) s : ℝ)<(cut (time (F n).R) t : ℝ) := by nlinarith
  exact_mod_cast hc

end PlanarHalving.RankLimits

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

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma ray_image_leaves_compact (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) (K : Set Point) (hK : IsCompact K) (hKt : K ⊆ f.target)
    (x v : Point) (hv : v≠0) : ∃ t : ℝ, 0≤t ∧ f (x+t • v) ∉ K := by
  have hc := hK.image_of_continuousOn (f.continuousOn_symm.mono hKt)
  obtain ⟨C,hC,hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hvp := norm_pos_iff.mpr hv
  let t : ℝ := (C+‖x‖+1)/‖v‖
  have ht : 0≤t := by dsimp [t]; positivity
  refine ⟨t,ht,?_⟩
  intro hmem
  have hx : x+t • v ∈ f.symm '' K := ⟨f (x+t • v),hmem,f.left_inv (by rw [hs]; trivial)⟩
  have hb := hbound _ hx
  have hh : ‖t • v‖ ≤ ‖x+t • v‖+‖x‖ := by
    calc
      _ = ‖(x+t • v)-x‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] at hh
  have he : t*‖v‖=C+‖x‖+1 := div_mul_cancel₀ _ hvp.ne'
  rw [he] at hh
  linarith

lemma radial_upper_enclosure (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p : Point} {h U : ℝ} (hU : 0≤U)
    (hball : closedBall p h ⊆ f.target)
    (hb : ∀ x ∈ sphere p h, dist (f.symm x) (f.symm p) ≤ U) :
    ∀ x ∈ closedBall p h, dist (f.symm x) (f.symm p) ≤ U := by
  intro x hx
  by_cases he : f.symm x=f.symm p
  · simpa only [he,dist_self] using hU
  let v := f.symm x-f.symm p
  have hv : v≠0 := sub_ne_zero.mpr he
  obtain ⟨t,ht,hexit⟩ := ray_image_leaves_compact f hs (closedBall p h)
    (isCompact_closedBall _ _) hball (f.symm x) v hv
  have hf : Continuous f := continuousOn_univ.mp (by simpa only [hs] using f.continuousOn)
  have hcont : Continuous (fun s : ℝ => dist (f (f.symm x+s • v)) p) :=
    (hf.comp
      (continuous_const.add (continuous_id.smul continuous_const))).dist continuous_const
  have h0 : dist (f (f.symm x+(0:ℝ) • v)) p ≤ h := by
    simpa only [zero_smul,add_zero,f.right_inv (hball hx)] using (Metric.mem_closedBall.mp hx)
  have h1 : h ≤ dist (f (f.symm x+t • v)) p := (not_le.mp hexit).le
  obtain ⟨s,hs',heq⟩ := intermediate_value_Icc ht hcont.continuousOn ⟨h0,h1⟩
  have hh := hb (f (f.symm x+s • v)) heq
  rw [f.left_inv (by rw [hs]; trivial)] at hh
  have hn : dist (f.symm x+s • v) (f.symm p)=(1+s)*dist (f.symm x) (f.symm p) := by
    rw [dist_eq_norm,show f.symm x+s • v-f.symm p=(1+s) • v by dsimp [v]; module]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [hs'.1])]
    rfl
  rw [hn] at hh
  nlinarith [dist_nonneg (x:=f.symm x) (y:=f.symm p),hs'.1]

lemma radial_lower_exterior (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p : Point} (hp : p∈f.target) {h V : ℝ} (hh : 0≤h)
    (hb : ∀ x ∈ sphere p h, V ≤ dist (f.symm x) (f.symm p)) :
    ∀ x ∈ f.target, h ≤ dist x p → V ≤ dist (f.symm x) (f.symm p) := by
  intro x hx hxp
  let v := f.symm x-f.symm p
  have hf : Continuous f := continuousOn_univ.mp (by simpa only [hs] using f.continuousOn)
  have hcont : Continuous (fun s : ℝ => dist (f (f.symm p+s • v)) p) :=
    (hf.comp
      (continuous_const.add (continuous_id.smul continuous_const))).dist continuous_const
  have h0 : dist (f (f.symm p+(0:ℝ) • v)) p ≤ h := by simpa [f.right_inv hp] using hh
  have h1 : h ≤ dist (f (f.symm p+(1:ℝ) • v)) p := by simpa [v,f.right_inv hx] using hxp
  obtain ⟨s,hs',heq⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) hcont.continuousOn ⟨h0,h1⟩
  have hb' := hb (f (f.symm p+s • v)) heq
  rw [f.left_inv (by rw [hs]; trivial),dist_eq_norm,add_sub_cancel_left,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg hs'.1] at hb'
  change V ≤ dist (f.symm x) (f.symm p)
  rw [dist_eq_norm]
  exact hb'.trans (mul_le_of_le_one_left (norm_nonneg v) hs'.2)

lemma radial_inner_enclosure (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p : Point} (hp : p∈f.target) {h V : ℝ} (hh : 0≤h)
    (hb : ∀ x ∈ sphere p h, V ≤ dist (f.symm x) (f.symm p)) :
    ball (f.symm p) V ⊆ f.symm '' ball p h := by
  intro y hy
  have hyt : f y∈f.target := f.map_source (by rw [hs]; trivial)
  have he : f.symm (f y)=y := f.left_inv (by rw [hs]; trivial)
  refine ⟨f y,?_,he⟩
  by_contra hn
  have hd := radial_lower_exterior f hs hp hh hb (f y) hyt (not_lt.mp hn)
  rw [he] at hd
  exact (not_lt_of_ge hd) hy

end PlanarHalving.Spatial

namespace PlanarHalving.TimeWindows
open Set Filter MeasureTheory
open scoped Topology unitInterval

lemma exists_two_positive_inside (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (hpos : μ (carrier K)≠0) :
    ∃ J H : Window, lower K<lower J ∧ upper J<lower H ∧ upper H<upper K ∧
      μ (carrier J)≠0 ∧ μ (carrier H)≠0 := by
  have hpos' : μ (Ioo (lower K) (upper K))≠0 := by rwa [measure_interior_eq μ K]
  have hsupp : ∀ᵐ x ∂μ, x∈μ.support := μ.support_mem_ae
  obtain ⟨x,hx,hxs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos'
    (hsupp.filter_mono ae_restrict_le)
  obtain ⟨y,hy,hys,hyx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos'
    ((hsupp.and (μ.ae_ne x)).filter_mono ae_restrict_le)
  have hpair : ∃ a b : I, a∈Ioo (lower K) (upper K) ∧ b∈Ioo (lower K) (upper K) ∧
      a∈μ.support ∧ b∈μ.support ∧ a<b := by
    rcases lt_or_gt_of_ne hyx with h | h
    · exact ⟨y,x,hy,hx,hys,hxs,h⟩
    · exact ⟨x,y,hx,hy,hxs,hys,h⟩
  obtain ⟨a,b,ha,hb,has,hbs,hab⟩ := hpair
  obtain ⟨c,hac,hcb⟩ := exists_between hab
  have hleft : μ (Ioo (lower K) c)≠0 := ne_of_gt
    ((Measure.mem_support_iff_forall a).mp has _ (Ioo_mem_nhds ha.1 hac))
  have hright : μ (Ioo c (upper K))≠0 := ne_of_gt
    ((Measure.mem_support_iff_forall b).mp hbs _ (Ioo_mem_nhds hcb hb.2))
  obtain ⟨J,hJ1,hJ2,hJ⟩ := exists_positive_inside μ hleft
  obtain ⟨H,hH1,hH2,hH⟩ := exists_positive_inside μ hright
  exact ⟨J,H,hJ1,hJ2.trans hH1,hH2,hJ,hH⟩

lemma CommonChoice.time_strictMono {K : Window} (q : CommonChoice K) : StrictMono q.time := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i <;> dsimp [CommonChoice.time]
  · exact lower_lt_upper q.val.1
  · exact q.property.2.1.trans (lower_lt_upper q.val.2.1)

lemma exists_commonChoice (μ : Measure I) [NullSingletonClass μ]
    (K : Window) (hpos : μ (carrier K)≠0) :
    ∃ q : CommonChoice K, μ (carrier q.val.1)≠0 ∧
      μ (carrier q.val.2.1)≠0 ∧ μ (carrier q.val.2.2)≠0 := by
  obtain ⟨J,H,hJ1,hJH,hH2,hJ,hH⟩ := exists_two_positive_inside μ K hpos
  have hJi : μ (Ioo (lower J) (upper J))≠0 := by rwa [measure_interior_eq]
  obtain ⟨K₀,hK1,hK2,hK⟩ := exists_positive_inside μ hJi
  exact ⟨⟨(J,H,K₀),hJ1,hJH,hH2,hK1,hK2⟩,hJ,hH,hK⟩

end PlanarHalving.TimeWindows

namespace PlanarHalving.Limits
open Set MeasureTheory

lemma positive_countable_selection {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (T : Set X) (hTm : MeasurableSet T) (hT : μ T≠0) (E : ι → Set X)
    (hcover : ∀ᵐ x ∂μ.restrict T, ∃ i, x∈E i) :
    ∃ i, μ (T∩E i)≠0 := by
  by_contra hn
  have hn' : ∀ i, μ (T∩E i)=0 := by simpa only [not_exists,not_not] using hn
  have hzero : μ (⋃ i, T∩E i)=0 := measure_iUnion_null hn'
  have hnull : ∀ᵐ x ∂μ.restrict T, x∉⋃ i, E i := by
    apply (ae_restrict_iff' hTm).mpr
    rw [ae_iff]
    convert hzero using 1
    congr 1
    ext x
    simp only [mem_ofPred_eq,Classical.not_imp,not_not,mem_iUnion,mem_inter_iff]
    aesop
  have he : ∀ᵐ x ∂μ.restrict T, False := by
    filter_upwards [hcover,hnull] with x hx hn
    exact hn (mem_iUnion.mpr hx)
  have hh : μ.restrict T univ=0 := by simpa only [ae_iff,not_false_eq_true,ofPred_true] using he
  exact hT (by simpa only [Measure.restrict_apply_univ] using hh)

end PlanarHalving.Limits

end OAI
end

section
-- module Solutions.OAIQW_PlanarHalving.SpatialMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma unitSphere_param {p : Point} {h : ℝ} (hh : 0≤h) (u : UnitSphere) :
    p+h • (u:Point)∈sphere p h := by
  simp only [mem_sphere,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg hh,u.property,mul_one]

lemma sphere_representation {p x : Point} {h : ℝ} (hh : 0<h) (hx : x∈sphere p h) :
    ∃ u : UnitSphere, x=p+h • (u:Point) := by
  have hn : ‖x-p‖=h := hx
  refine ⟨⟨h⁻¹ • (x-p),?_⟩,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),hn,inv_mul_cancel₀ hh.ne']
  · simp only [smul_smul,mul_inv_cancel₀ hh.ne',one_smul,add_sub_cancel]

lemma continuous_sphereValue {f : Point → Point} {p : Point} {h : ℝ} (hh : 0≤h)
    (hf : ContinuousOn f (closedBall p h)) :
    Continuous (fun u : UnitSphere => dist (f (p+h • (u:Point))) (f p)) := by
  have hc : Continuous (fun u : UnitSphere => p+h • (u:Point)) := by fun_prop
  exact (hf.comp_continuous hc
    (fun u => sphere_subset_closedBall (unitSphere_param (p:=p) hh u))).dist continuous_const

lemma radialU_attained {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) :
    ∃ x ∈ sphere p h, dist (f x) (f p)=radialU f p h ∧
      ∀ y∈sphere p h, dist (f y) (f p)≤radialU f p h := by
  obtain ⟨u,_,he,hu⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    (Set.univ_nonempty : (univ:Set UnitSphere).Nonempty) (continuous_sphereValue hh.le hf).continuousOn
  have he' : radialU f p h=dist (f (p+h • (u:Point))) (f p) := by
    simpa only [image_univ,radialU] using he
  refine ⟨_,unitSphere_param hh.le u,he'.symm,?_⟩
  intro y hy
  obtain ⟨v,rfl⟩ := sphere_representation hh hy
  rw [he']
  exact hu v (mem_univ _)

lemma radialV_attained {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) :
    ∃ x ∈ sphere p h, dist (f x) (f p)=radialV f p h ∧
      ∀ y∈sphere p h, radialV f p h≤dist (f y) (f p) := by
  obtain ⟨u,_,he,hu⟩ := isCompact_univ.exists_sInf_image_eq_and_le
    (Set.univ_nonempty : (univ:Set UnitSphere).Nonempty) (continuous_sphereValue hh.le hf).continuousOn
  have he' : radialV f p h=dist (f (p+h • (u:Point))) (f p) := by
    simpa only [image_univ,radialV] using he
  refine ⟨_,unitSphere_param hh.le u,he'.symm,?_⟩
  intro y hy
  obtain ⟨v,rfl⟩ := sphere_representation hh hy
  rw [he']
  exact hu v (mem_univ _)

lemma radial_extrema_bounds {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) :
    0≤radialV f p h ∧ radialV f p h≤radialU f p h ∧
      ∀ x∈sphere p h, radialV f p h≤dist (f x) (f p) ∧ dist (f x) (f p)≤radialU f p h := by
  obtain ⟨x,hx,he,hlo⟩ := radialV_attained hh hf
  obtain ⟨y,hy,he',hup⟩ := radialU_attained hh hf
  refine ⟨he ▸ dist_nonneg,?_,fun z hz => ⟨hlo z hz,hup z hz⟩⟩
  rw [← he']; exact hlo y hy

lemma radialV_pos {f : Point → Point} {p : Point} {h : ℝ} (hh : 0<h)
    (hf : ContinuousOn f (closedBall p h)) (hinj : InjOn f (closedBall p h)) :
    0<radialV f p h := by
  obtain ⟨x,hx,he,_⟩ := radialV_attained hh hf
  rw [← he,dist_pos]
  intro hf'
  have hxp := hinj (sphere_subset_closedBall hx) (mem_closedBall_self hh.le) hf'
  have hh' : h=0 := by simpa only [hxp,dist_self,eq_comm,mem_sphere] using hx
  exact hh.ne' hh'

lemma continuousOn_radialU {f : Point → Point} {D P : Set Point} {h : ℝ} (hh : 0≤h)
    (hf : ContinuousOn f D) (hP : ∀ p∈P, closedBall p h ⊆ D) :
    ContinuousOn (fun p => radialU f p h) P := by
  rw [continuousOn_iff_continuous_domRestrict]
  let a : P × UnitSphere → Point := fun q => (q.1:Point)+h • (q.2:Point)
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hfa : Continuous (f ∘ a) := hf.comp_continuous ha
    (fun q => hP q.1 q.1.property (sphere_subset_closedBall (unitSphere_param hh q.2)))
  have hfb : Continuous (fun q : P × UnitSphere => f q.1) := hf.comp_continuous
    (continuous_subtype_val.comp continuous_fst) (fun q => hP q.1 q.1.property (mem_closedBall_self hh))
  have ht := isCompact_univ.continuous_sSup
    (f:=fun p : P => fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)) (hfa.dist hfb)
  change Continuous (fun p : P => sSup (range fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)))
  simpa only [image_univ] using ht

lemma continuousOn_radialV {f : Point → Point} {D P : Set Point} {h : ℝ} (hh : 0≤h)
    (hf : ContinuousOn f D) (hP : ∀ p∈P, closedBall p h ⊆ D) :
    ContinuousOn (fun p => radialV f p h) P := by
  rw [continuousOn_iff_continuous_domRestrict]
  let a : P × UnitSphere → Point := fun q => (q.1:Point)+h • (q.2:Point)
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hfa : Continuous (f ∘ a) := hf.comp_continuous ha
    (fun q => hP q.1 q.1.property (sphere_subset_closedBall (unitSphere_param hh q.2)))
  have hfb : Continuous (fun q : P × UnitSphere => f q.1) := hf.comp_continuous
    (continuous_subtype_val.comp continuous_fst) (fun q => hP q.1 q.1.property (mem_closedBall_self hh))
  have ht := isCompact_univ.continuous_sInf
    (f:=fun p : P => fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)) (hfa.dist hfb)
  change Continuous (fun p : P => sInf (range fun u : UnitSphere => dist (f ((p:Point)+h • (u:Point))) (f p)))
  simpa only [image_univ] using ht

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Metric Zoom
open scoped Topology

lemma rankCore_closed (h : ℝ) : IsClosed (rankCore h) := isClosed_Icc.prod isClosed_Icc

lemma rankCore_ball {h : ℝ} (hh : 0<h) {p : Point} (hp : p∈rankCore h) :
    closedBall p h ⊆ Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  intro x hx
  rw [mem_closedBall,Prod.dist_eq] at hx
  have hx1 : |x.1-p.1|≤h := (le_max_left _ _).trans hx
  have hx2 : |x.2-p.2|≤h := (le_max_right _ _).trans hx
  rcases abs_le.mp hx1 with ⟨hx11,hx12⟩
  rcases abs_le.mp hx2 with ⟨hx21,hx22⟩
  rcases hp with ⟨⟨hp11,hp12⟩,⟨hp21,hp22⟩⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma rankCore_small {p : Point} (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0) :
    ∃ δ>0, ∀ h, h≤δ → p∈rankCore h := by
  let d := min p.1 (min (1-p.1) (min (p.2+1) (-p.2)))
  have hd : 0<d := by dsimp [d]; exact lt_min hp.1.1 (lt_min (by linarith [hp.1.2]) (lt_min (by linarith [hp.2.1]) (by linarith [hp.2.2])))
  have h1 : d≤p.1 := min_le_left _ _
  have h2 : d≤1-p.1 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : d≤p.2+1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : d≤-p.2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨d/4,by positivity,fun h hh => ?_⟩
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

lemma radialCompare_extrema {f : Point → Point} {p : Point} {h C M T : ℝ}
    (hh : 0<h) (hT : 1≤T) (hM : 0<M) (hCM : C≤M)
    (hf : ContinuousOn f (closedBall p h)) (hc : RadialCompare f p h C T) :
    (1/(M*T))*radialU f p h ≤ radialV f p (h/T) ∧
      radialU f p (h/T)≤(M/T)*radialV f p h := by
  have hTp : 0<T := lt_of_lt_of_le zero_lt_one hT
  have hhT : 0<h/T := div_pos hh hTp
  have hsmall : h/T≤h := (div_le_iff₀ hTp).mpr (by nlinarith)
  have hf' := hf.mono (closedBall_subset_closedBall hsmall)
  obtain ⟨u,hu,heu,_⟩ := radialV_attained hhT hf'
  obtain ⟨v,hv,hev,_⟩ := radialU_attained hh hf
  have h1 := hc.1 u v hu hv
  change dist (f v) (f p) ≤ C*T*dist (f u) (f p) at h1
  rw [heu,hev] at h1
  have hlow : 0≤radialV f p (h/T) := (radial_extrema_bounds hhT hf').1
  have h1' : radialU f p h ≤ M*T*radialV f p (h/T) :=
    h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM hTp.le) hlow)
  obtain ⟨u',hu',heu',_⟩ := radialU_attained hhT hf'
  obtain ⟨v',hv',hev',_⟩ := radialV_attained hh hf
  have h2 := hc.2 u' v' hu' hv'
  change T*dist (f u') (f p) ≤ C*dist (f v') (f p) at h2
  rw [heu',hev'] at h2
  have hv0 := (radial_extrema_bounds hh hf).1
  constructor
  · rw [one_div,inv_mul_eq_div]
    exact (div_le_iff₀ (mul_pos hM hTp)).mpr (by nlinarith [h1'])
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hTp).mpr
    have h2' := h2.trans (mul_le_mul_of_nonneg_right hCM hv0)
    convert h2' using 1; ring

lemma scaleGood_measurable (f : ℕ → Point → Point) {h q α β : ℝ}
    (hh : 0<h) (hq : 0≤q) (hq1 : q≤1)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)) :
    MeasurableSet (ScaleGood f h q α β) := by
  let P := rankCore h
  have hcU (n j : ℕ) : Continuous (fun p : P => radialU (f n) p (h*q^j)) := by
    have hc : ContinuousOn (fun p => radialU (f n) p (h*q^j)) P := by
      apply continuousOn_radialU (by positivity) (hf n)
      intro p hp
      exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq hq1))).trans
        (rankCore_ball hh hp)
    exact hc.domRestrict
  have hcV (n j : ℕ) : Continuous (fun p : P => radialV (f n) p (h*q^j)) := by
    have hc : ContinuousOn (fun p => radialV (f n) p (h*q^j)) P := by
      apply continuousOn_radialV (by positivity) (hf n)
      intro p hp
      exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq hq1))).trans
        (rankCore_ball hh hp)
    exact hc.domRestrict
  have hm : MeasurableSet {p : P | ∀ j : ℕ, ∀ᶠ n in atTop,
      α*radialU (f n) p (h*q^j)≤radialV (f n) p (h*q^(j+1)) ∧
      radialU (f n) p (h*q^(j+1))≤β*radialV (f n) p (h*q^j)} := by
    simp only [eventually_atTop]
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    rw [ofPred_exists]
    apply MeasurableSet.iUnion
    intro N
    rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    by_cases hn : N≤n
    · simp only [hn,true_implies]
      exact (measurableSet_le ((hcU n j).measurable.const_mul α) (hcV n (j+1)).measurable).inter
        (measurableSet_le (hcU n (j+1)).measurable ((hcV n j).measurable.const_mul β))
    · simp only [hn,false_implies,ofPred_true]; exact MeasurableSet.univ
  have hi := (MeasurableEmbedding.subtype_coe (rankCore_closed h).measurableSet).measurableSet_image.mpr hm
  convert hi using 1
  ext p
  simp only [ScaleGood,mem_ofPred_eq,mem_image,Subtype.exists]
  aesop

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter MeasureTheory Metric Zoom
open scoped Topology

lemma exists_scaleGood (f : ℕ → Point → Point) {p : Point}
    (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0))
    {C M T : ℝ} (hCM : C≤M) (hM : 0<M) (hT : 1<T)
    (hc : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop, RadialCompare (f n) p h C T) :
    ∃ m : ℕ, p∈ScaleGood f ((1/T)^m) (1/T) (1/(M*T)) (M/T) := by
  obtain ⟨δ,hδ,hδc⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hc
  obtain ⟨d,hd,hcore⟩ := rankCore_small hp
  have hTp : 0<T := lt_trans zero_lt_one hT
  have hq : 0<1/T := div_pos zero_lt_one hTp
  have hq1 : 1/T<1 := (div_lt_one hTp).mpr hT
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1
  obtain ⟨m,hm⟩ := ((tendsto_order.mp hlim).2 (min δ d) (lt_min hδ hd)).exists
  have hmd : (1/T)^m<d := hm.trans_le (min_le_right _ _)
  have hmδ : (1/T)^m<δ := hm.trans_le (min_le_left _ _)
  have hmc := hcore _ hmd.le
  refine ⟨m,hmc,fun j => ?_⟩
  have hr : 0<(1/T)^m*(1/T)^j := mul_pos (pow_pos hq _) (pow_pos hq _)
  have hrm : (1/T)^m*(1/T)^j≤(1/T)^m := mul_le_of_le_one_right
    (pow_nonneg hq.le _) (pow_le_one₀ hq.le hq1.le)
  have hrc := hδc ⟨hr,hrm.trans_lt hmδ⟩
  filter_upwards [hrc] with n hn
  have hball := (closedBall_subset_closedBall hrm (x:=p)).trans
    (rankCore_ball (pow_pos hq _) hmc)
  have hb := radialCompare_extrema hr hT.le hM hCM ((hf n).mono hball) hn
  have he : (1/T)^m*(1/T)^j/T=(1/T)^m*(1/T)^(j+1) := by rw [pow_succ]; ring
  rwa [he] at hb

lemma exists_dyadicExponent_scaleGood (f : ℕ → Point → Point) {p : Point}
    (hp : p∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0))
    (hc : ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ),
      ∀ᶠ n in atTop, RadialCompare (f n) p h C T) :
    ∃ M m : ℕ, 2≤M ∧ p∈ScaleGood f ((1/(M:ℝ)^16)^m) (1/(M:ℝ)^16)
      (1/((M:ℝ)*(M:ℝ)^16)) ((M:ℝ)/(M:ℝ)^16) := by
  obtain ⟨C,_,hC⟩ := hc
  obtain ⟨N,hN⟩ := exists_nat_gt C
  let M := max N 2
  have hM2 : 2≤M := le_max_right _ _
  have hMp : 0<(M:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hM2)
  have hM1 : 1<(M:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hM2)
  have hCM : C≤(M:ℝ) := hN.le.trans (by exact_mod_cast le_max_left N 2)
  have hT : 1<(M:ℝ)^16 := one_lt_pow₀ hM1 (by decide)
  obtain ⟨m,hm⟩ := exists_scaleGood f hp hf hCM hMp hT (hC _ hT.le)
  exact ⟨M,m,hM2,hm⟩

lemma positive_scaleGood {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) (hpos : μ E≠0)
    (π : X → Point) (hπ : Measurable π) (f : ℕ → Point → Point)
    (hf : ∀ n, ContinuousOn (f n) (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0))
    (hc : ∀ᵐ x ∂μ.restrict E, π x∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ),
        ∀ᶠ n in atTop, RadialCompare (f n) (π x) h C T) :
    ∃ M m : ℕ, 2≤M ∧ MeasurableSet (E∩π ⁻¹' ScaleGood f ((1/(M:ℝ)^16)^m)
      (1/(M:ℝ)^16) (1/((M:ℝ)*(M:ℝ)^16)) ((M:ℝ)/(M:ℝ)^16)) ∧
      μ (E∩π ⁻¹' ScaleGood f ((1/(M:ℝ)^16)^m)
      (1/(M:ℝ)^16) (1/((M:ℝ)*(M:ℝ)^16)) ((M:ℝ)/(M:ℝ)^16))≠0 := by
  let A := fun q : ℕ×ℕ => {x | 2≤q.1 ∧ π x∈ScaleGood f ((1/(q.1:ℝ)^16)^q.2)
      (1/(q.1:ℝ)^16) (1/((q.1:ℝ)*(q.1:ℝ)^16)) ((q.1:ℝ)/(q.1:ℝ)^16)}
  obtain ⟨q,hq⟩ := Limits.positive_countable_selection μ E hE hpos A (by
    filter_upwards [hc] with x hx
    obtain ⟨M,m,hM,hm⟩ := exists_dyadicExponent_scaleGood f hx.1 hf hx.2
    exact ⟨(M,m),hM,hm⟩)
  obtain ⟨x,_,hM,_⟩ := nonempty_of_measure_ne_zero hq
  have hM2 : 2≤q.1 := hM
  have hMp : 0<(q.1:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hM2)
  have hM1 : 1≤(q.1:ℝ) := by exact_mod_cast (le_trans (by decide : 1≤2) hM2)
  have hT : 1≤(q.1:ℝ)^16 := one_le_pow₀ hM1
  have hTp : 0<(q.1:ℝ)^16 := pow_pos hMp _
  have hm := scaleGood_measurable f (h:=(1/(q.1:ℝ)^16)^q.2)
    (α:=1/((q.1:ℝ)*(q.1:ℝ)^16)) (β:=(q.1:ℝ)/(q.1:ℝ)^16)
    (pow_pos (div_pos zero_lt_one hTp) q.2)
    (div_nonneg zero_le_one hTp.le) ((div_le_one hTp).mpr hT) hf
  refine ⟨q.1,q.2,hM2,hE.inter (hm.preimage hπ),?_⟩
  exact ne_of_gt ((pos_iff_ne_zero.mpr hq).trans_le (measure_mono (by
    intro x hx
    exact ⟨hx.1,hx.2.2⟩)))

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma radius_le_of_ball_subset_closedBall {a b : Point} {r R : ℝ}
    (hr : 0≤r) (hR : 0≤R) (hb : ball a r ⊆ closedBall b R) : r≤R := by
  have hh := diam_mono hb isBounded_closedBall
  rw [diam_ball_eq a hr,diam_closedBall_eq b hR] at hh
  linarith

lemma normalized_local_bounds (f : OpenPartialHomeomorph Point Point)
    (hs : f.source=univ) {p₀ p : Point} {h q : ℝ}
    (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2)
    (hb₀ : closedBall p₀ h ⊆ f.target) (hb : closedBall p h ⊆ f.target)
    (hp : dist p p₀<h/4) (hz : f.symm p₀=0) (hU : radialU f.symm p₀ h=1) :
    ‖f.symm p‖≤1 ∧ radialU f.symm p (h*q)≤2 ∧
      ∀ α : ℝ, 0≤α → α≤radialV f.symm p₀ (h*q) → α≤radialU f.symm p h := by
  have hqh : h*q≤h := mul_le_of_le_one_right hh.le (by linarith)
  have hqhp : 0<h*q := mul_pos hh hq
  have hcont₀ := f.continuousOn_symm.mono hb₀
  have hcont := f.continuousOn_symm.mono hb
  have hcont₁ := hcont.mono (closedBall_subset_closedBall hqh)
  have hcont₀₁ := hcont₀.mono (closedBall_subset_closedBall hqh)
  have hby : closedBall p (h*q) ⊆ closedBall p₀ h := by
    intro x hx
    have ht := dist_triangle x p p₀
    have hx' : dist x p≤h*q := hx
    have hm : h*q≤h/2 := by nlinarith
    change dist x p₀≤h
    linarith
  have hby' : ball p₀ (h*q) ⊆ closedBall p h := by
    intro x hx
    have ht := dist_triangle x p₀ p
    have hx' : dist x p₀<h*q := hx
    rw [dist_comm p₀ p] at ht
    have hm : h*q≤h/2 := by nlinarith
    change dist x p≤h
    linarith
  have hupper : ∀ x∈closedBall p₀ h, ‖f.symm x‖≤1 := by
    have hr := radial_upper_enclosure f hs (hU:=zero_le_one) hb₀ (fun x hx => by
      have hhx := (radial_extrema_bounds hh hcont₀).2.2 x hx
      simpa only [hU] using hhx.2)
    simpa only [hz,dist_zero_right] using hr
  have hnp : ‖f.symm p‖≤1 := hupper p (by change dist p p₀≤h; linarith)
  refine ⟨hnp,?_,?_⟩
  · obtain ⟨x,hx,he,_⟩ := radialU_attained hqhp hcont₁
    have hnx := hupper x (hby (sphere_subset_closedBall hx))
    rw [← he]
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  · intro α hα hαV
    have hinner := radial_inner_enclosure f hs (hb₀ (mem_closedBall_self hh.le))
      hqhp.le (fun x hx => hαV.trans ((radial_extrema_bounds hqhp hcont₀₁).2.2 x hx).1)
    rw [hz] at hinner
    have hu0 := (radial_extrema_bounds hh hcont).1.trans (radial_extrema_bounds hh hcont).2.1
    apply radius_le_of_ball_subset_closedBall hα hu0
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hinner hy
    exact radial_upper_enclosure f hs hu0 hb
      (fun x hx => ((radial_extrema_bounds hh hcont).2.2 x hx).2) x (hby' hx)

lemma scaleGood_iteration (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    {p₀ p : Point} {h q α β : ℝ} (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2)
    (hα : 0≤α) (hβ : 0≤β)
    (h₀ : p₀∈ScaleGood (fun n => (f n).symm) h q α β)
    (hp : p∈ScaleGood (fun n => (f n).symm) h q α β) (hd : dist p p₀<h/4)
    (hz : ∀ n, (f n).symm p₀=0) (hU : ∀ n, radialU (f n).symm p₀ h=1) :
    (∀ n, ‖(f n).symm p‖≤1) ∧ ∀ j : ℕ, ∀ᶠ n in atTop,
      α^(j+2)≤radialV (f n).symm p (h*q^(j+1)) ∧
      radialU (f n).symm p (h*q^(j+1))≤2*β^j := by
  have hb (n : ℕ) : closedBall p h ⊆ (f n).target := by rw [ht n]; exact rankCore_ball hh hp.1
  have hb₀ (n : ℕ) : closedBall p₀ h ⊆ (f n).target := by rw [ht n]; exact rankCore_ball hh h₀.1
  have hlocal := fun n => normalized_local_bounds (f n) (hs n) hh hq hq2 (hb₀ n) (hb n) hd (hz n) (hU n)
  refine ⟨fun n => (hlocal n).1,?_⟩
  have hlow : ∀ᶠ n in atTop, α≤radialU (f n).symm p h := by
    filter_upwards [h₀.2 0] with n hn
    apply (hlocal n).2.2 α hα
    simpa only [Nat.zero_add,pow_zero,pow_one,mul_one,hU n] using hn.1
  intro j
  induction j with
  | zero =>
    filter_upwards [hlow,hp.2 0] with n hn hn'
    constructor
    · have hh' := mul_le_mul_of_nonneg_left hn hα
      simp only [Nat.zero_add,pow_zero,pow_one,mul_one] at hn'
      simpa only [Nat.zero_add,pow_one,pow_two] using hh'.trans hn'.1
    · simpa only [Nat.zero_add,pow_zero,pow_one,mul_one] using (hlocal n).2.1
  | succ j ih =>
    filter_upwards [ih,hp.2 (j+1)] with n hn hn'
    have hjh : h*q^(j+1)≤h := mul_le_of_le_one_right hh.le (pow_le_one₀ hq.le (by linarith))
    have hc := (f n).continuousOn_symm.mono ((closedBall_subset_closedBall hjh).trans (hb n))
    have hvu := (radial_extrema_bounds (mul_pos hh (pow_pos hq _)) hc).2.1
    constructor
    · have he := (mul_le_mul_of_nonneg_left (hn.1.trans hvu) hα).trans hn'.1
      calc
        α^(j.succ+2) = α*α^(j+2) := by
          rw [show j.succ+2=j+2+1 by omega,pow_succ,mul_comm]
        _ ≤ _ := he
    · have he := hn'.2.trans (mul_le_mul_of_nonneg_left (hvu.trans hn.2) hβ)
      calc
        _ ≤ β*(2*β^j) := he
        _ = 2*β^j.succ := by rw [pow_succ]; ring

end PlanarHalving.Spatial

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
open Set Filter Metric Zoom
open scoped Topology

lemma radial_extrema_scale {f g : Point → Point} {p : Point} {h c : ℝ}
    (hh : 0<h) (hc : 0≤c)
    (hf : ContinuousOn f (closedBall p h)) (hg : ContinuousOn g (closedBall p h))
    (he : ∀ x∈sphere p h, dist (g x) (g p)=c*dist (f x) (f p)) :
    radialU g p h=c*radialU f p h ∧ radialV g p h=c*radialV f p h := by
  obtain ⟨x,hx,hex,hfx⟩ := radialU_attained hh hf
  obtain ⟨y,hy,hey,hgy⟩ := radialU_attained hh hg
  have hU : radialU g p h=c*radialU f p h := by
    apply le_antisymm
    · rw [← hey,he y hy]
      exact mul_le_mul_of_nonneg_left (hfx y hy) hc
    · rw [← hex,← he x hx]
      exact hgy x hx
  obtain ⟨x,hx,hex,hfx⟩ := radialV_attained hh hf
  obtain ⟨y,hy,hey,hgy⟩ := radialV_attained hh hg
  refine ⟨hU,le_antisymm ?_ ?_⟩
  · rw [← hex,← he x hx]
    exact hgy x hx
  · rw [← hey,he y hy]
    exact mul_le_mul_of_nonneg_left (hfx y hy) hc

lemma normalizeChart_source (f : OpenPartialHomeomorph Point Point) (hs : f.source=univ)
    (p : Point) (U : ℝ) (hU : U≠0) : (normalizeChart f p U hU).source=univ := by
  ext x
  change (f.symm p+U • x∈f.source) ↔ x∈univ
  rw [hs]; simp

lemma normalizeChart_radial (f : OpenPartialHomeomorph Point Point)
    (p₀ : Point) {U : ℝ} (hU : 0<U) {p : Point} {h : ℝ} (hh : 0<h)
    (hb : closedBall p h ⊆ f.target) :
    radialU (normalizeChart f p₀ U hU.ne').symm p h=U⁻¹*radialU f.symm p h ∧
    radialV (normalizeChart f p₀ U hU.ne').symm p h=U⁻¹*radialV f.symm p h := by
  apply radial_extrema_scale hh (inv_nonneg.mpr hU.le)
    (f.continuousOn_symm.mono hb) ((normalizeChart f p₀ U hU.ne').continuousOn_symm.mono hb)
  intro x _
  rw [normalizeChart_symm,normalizeChart_symm,dist_eq_norm,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hU)]
  congr 1
  rw [dist_eq_norm]
  congr 1
  abel

lemma normalizeChart_scaleGood (f : ℕ → OpenPartialHomeomorph Point Point)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (p₀ : Point) (U : ℕ → ℝ) (hU : ∀ n, 0<U n)
    {p : Point} {h q α β : ℝ} (hh : 0<h) (hq : 0<q) (hq1 : q≤1)
    (hp : p∈ScaleGood (fun n => (f n).symm) h q α β) :
    p∈ScaleGood (fun n => (normalizeChart (f n) p₀ (U n) (hU n).ne').symm) h q α β := by
  refine ⟨hp.1,fun j => ?_⟩
  have hb (n j : ℕ) : closedBall p (h*q^j) ⊆ (f n).target := by
    rw [ht n]
    exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq.le hq1))).trans
      (rankCore_ball hh hp.1)
  filter_upwards [hp.2 j] with n hn
  have he := normalizeChart_radial (f n) p₀ (hU n) (mul_pos hh (pow_pos hq j)) (hb n j)
  have he' := normalizeChart_radial (f n) p₀ (hU n) (mul_pos hh (pow_pos hq (j+1))) (hb n (j+1))
  rw [he.1,he.2,he'.1,he'.2]
  constructor
  · calc
      _ = (U n)⁻¹*(α*radialU (f n).symm p (h*q^j)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn.1 (inv_nonneg.mpr (hU n).le)
  · calc
      _ ≤ (U n)⁻¹*(β*radialV (f n).symm p (h*q^j)) :=
        mul_le_mul_of_nonneg_left hn.2 (inv_nonneg.mpr (hU n).le)
      _ = _ := by ring

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma normalized_spatial_limit (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (G : Set Point) (p₀ : Point) (hp₀ : p₀∈G)
    {h q s β : ℝ} (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2) (hspos : 0<s)
    (hβ : 0≤β) (hβ1 : β<1)
    (hgood : G ⊆ ScaleGood (fun n => (f n).symm) h q (q^s) β)
    (hlocal : ∀ p∈G, dist p p₀<h/4)
    (hz : ∀ n, (f n).symm p₀=0) (hU : ∀ n, radialU (f n).symm p₀ h=1) :
    ∃ (φ : ℕ → ℕ) (l : G → Point), StrictMono φ ∧ (∀ p, ‖l p‖≤1) ∧
      (∀ p : G, ∀ u : ℕ → Point, Tendsto u atTop (𝓝 (p:Point)) →
        Tendsto (fun n => (f (φ n)).symm (u n)) atTop (𝓝 (l p))) ∧
      ∀ p p' : G, (q^s*(q/h)^s)*dist (p:Point) p'^s ≤ dist (l p) (l p') := by
  have hq1 : q<1 := by linarith
  have hiter := fun p hp => scaleGood_iteration f hs ht hh hq hq2
    (Real.rpow_nonneg hq.le s) hβ (hgood hp₀) (hgood hp) (hlocal p hp) hz hU
  have hball (n : ℕ) (p : Point) (hp : p∈G) (j : ℕ) :
      closedBall p (h*q^j) ⊆ (f n).target := by
    rw [ht n]
    exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le (pow_le_one₀ hq.le hq1.le))).trans
      (rankCore_ball hh (hgood hp).1)
  have hcont : ∀ p∈G, ∀ ε>0, ∃ r>0, ∀ᶠ n in atTop, ∀ x,
      dist x p<r → dist ((f n).symm x) ((f n).symm p)≤ε := by
    apply asymptotic_continuity_of_radial (fun n => (f n).symm) G
      (fun j => h*q^(j+1)) (fun j => 2*β^j)
      (fun j => mul_pos hh (pow_pos hq _))
    · simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).const_mul 2
    · intro p hp j
      filter_upwards [(hiter p hp).2 j] with n hn x hx
      have hc := (f n).continuousOn_symm.mono (hball n p hp (j+1))
      have he := radial_extrema_bounds (mul_pos hh (pow_pos hq (j+1))) hc
      apply le_trans (b:=radialU (f n).symm p (h*q^(j+1))) ?_ hn.2
      exact radial_upper_enclosure (f n) (hs n) (he.1.trans he.2.1) (hball n p hp (j+1))
        (fun x hx => (he.2.2 x hx).2) x hx.le
  obtain ⟨φ,l,hφ,hl,hmoving⟩ := subsequence_of_asymptotic_continuity
    (fun n => (f n).symm) G ⟨p₀,hp₀⟩ (closedBall (0:Point) 1) (isCompact_closedBall _ _)
    (fun n p hp => by simpa only [mem_closedBall,dist_zero_right] using (hiter p hp).1 n) hcont
  refine ⟨φ,l,hφ,fun p => by simpa only [mem_closedBall,dist_zero_right] using hl p,hmoving,?_⟩
  apply inverse_holder_of_radial_limits (fun n => (f n).symm) φ hφ G l
    (fun p => hmoving p (fun _ => p) tendsto_const_nhds) hq hq1 hh hspos
  · intro p p'
    have hd := dist_triangle (p:Point) p₀ (p':Point)
    rw [dist_comm p₀ (p':Point)] at hd
    have h1 := hlocal p p.property
    have h2 := hlocal p' p'.property
    linarith
  · intro p j hj
    cases j with
    | zero => omega
    | succ j =>
      filter_upwards [(hiter p p.property).2 j] with n hn p' hdist
      have hc := (f n).continuousOn_symm.mono (hball n p p.property (j+1))
      apply hn.1.trans
      rw [dist_comm ((f n).symm p) ((f n).symm p')]
      apply radial_lower_exterior (f n) (hs n)
        (hball n p p.property 0 (by simpa only [pow_zero,mul_one] using mem_closedBall_self hh.le))
        (mul_nonneg hh.le (pow_nonneg hq.le _))
        (fun x hx => ((radial_extrema_bounds (mul_pos hh (pow_pos hq _)) hc).2.2 x hx).1)
        p' (hball n p' p'.property 0 (by simpa only [pow_zero,mul_one] using mem_closedBall_self hh.le))
      simpa only [dist_comm] using hdist.le

end PlanarHalving.Spatial

namespace PlanarHalving.Limits
open Set Filter MeasureTheory
open scoped ENNReal

lemma exists_bounded_density_piece {X : Type*} [MeasurableSpace X]
    (ν β γ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure γ] [SigmaFinite β]
    (hac : γ ≪ β) (hpos : γ univ≠0) :
    ∃ (m : ℕ) (A : Set X), MeasurableSet A ∧ γ A≠0 ∧ ν.restrict A≤(m:ℝ≥0∞) • β := by
  obtain ⟨S,hS,hνS,hβS⟩ := Measure.mutuallySingular_singularPart ν β
  let A : ℕ → Set X := fun m => S∩{x | ν.rnDeriv β x≤(m:ℝ≥0∞)}
  have hA (m : ℕ) : MeasurableSet (A m) := hS.inter
    (measurableSet_le (Measure.measurable_rnDeriv ν β) measurable_const)
  have hSae : ∀ᵐ x ∂β, x∈S := by exact hβS
  have hcover : ∀ᵐ x ∂γ, ∃ m : ℕ, x∈A m := by
    filter_upwards [hac.ae_le hSae,hac.ae_le (Measure.rnDeriv_lt_top ν β)] with x hx hf
    obtain ⟨m,hm⟩ := exists_nat_gt (ν.rnDeriv β x).toReal
    refine ⟨m,hx,?_⟩
    apply (ENNReal.toReal_le_toReal hf.ne (by simp)).mp
    simpa only [ENNReal.toReal_natCast] using hm.le
  obtain ⟨m,hm⟩ := positive_countable_selection γ univ MeasurableSet.univ hpos A
    (by simpa only [Measure.restrict_univ] using hcover)
  have hm' : γ (A m)≠0 := by simpa only [univ_inter] using hm
  refine ⟨m,A m,hA m,hm',?_⟩
  have hsing : (ν.singularPart β).restrict (A m)=0 := by
    apply Measure.restrict_eq_zero.mpr
    exact measure_mono_null inter_subset_left hνS
  rw [ν.haveLebesgueDecomposition_add β,Measure.restrict_add,hsing,zero_add,
    restrict_withDensity (hA m)]
  have hd : (ν.rnDeriv β)≤ᵐ[β.restrict (A m)] fun _ => (m:ℝ≥0∞) := by
    filter_upwards [ae_restrict_mem (hA m)] with x hx
    exact hx.2
  exact (withDensity_mono hd).trans (by
    rw [withDensity_const]
    apply Measure.le_iff.mpr
    intro B hB
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.restrict_le_self B))

lemma positive_bounded_projection {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ θ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure θ]
    (β : Measure Y) [SigmaFinite β] (π : X → Y) (hπ : Measurable π)
    (E : Set X) (hE : MeasurableSet E) (hpos : θ E≠0)
    (hac : (θ.restrict E).map π ≪ β) :
    ∃ (m : ℕ) (G : Set X), MeasurableSet G ∧ G⊆E ∧ θ G≠0 ∧
      (μ.restrict G).map π≤(m:ℝ≥0∞) • β := by
  obtain ⟨m,A,hA,hm,hb⟩ := exists_bounded_density_piece (μ.map π) β ((θ.restrict E).map π) hac (by
    simpa only [Measure.map_apply hπ MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ] using hpos)
  let G := π ⁻¹' A ∩ E
  have hG : MeasurableSet G := (hA.preimage hπ).inter hE
  refine ⟨m,G,hG,inter_subset_right,?_,?_⟩
  · simpa only [Measure.map_apply hπ hA,Measure.restrict_apply (hA.preimage hπ)] using hm
  · apply le_trans (b:= (μ.map π).restrict A) ?_ hb
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.map_apply hπ hB,Measure.restrict_apply (hB.preimage hπ),
      Measure.restrict_apply hB,Measure.map_apply hπ (hB.inter hA)]
    apply measure_mono
    intro x hx
    exact ⟨hx.1,hx.2.1⟩

end PlanarHalving.Limits

namespace PlanarHalving.Spatial
open Set Filter Metric
open scoped Topology

lemma joint_of_asymptotic_continuity {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : ℕ → X → Y) {p : X} {v : Y}
    (hl : Tendsto (fun n => f n p) atTop (𝓝 v))
    (hc : ∀ ε>0, ∃ r>0, ∀ᶠ n in atTop, ∀ x, dist x p<r → dist (f n x) (f n p)≤ε) :
    Tendsto (fun q : ℕ × X => f q.1 q.2) (atTop ×ˢ 𝓝 p) (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r,hr,hrc⟩ := hc (ε/2) (half_pos hε)
  have hl' := (Metric.tendsto_nhds.mp hl) (ε/2) (half_pos hε)
  have hp : ∀ᶠ x in 𝓝 p, dist x p<r := ball_mem_nhds p hr
  filter_upwards [hrc.prod_inl (𝓝 p),hl'.prod_inl (𝓝 p),hp.prod_inr atTop] with q hq hq' hqp
  have hh := hq q.2 hqp
  have ht := dist_triangle (f q.1 q.2) (f q.1 p) v
  linarith

lemma scaleGood_joint (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    {p₀ p : Point} {h q α β : ℝ} (hh : 0<h) (hq : 0<q) (hq2 : q≤1/2)
    (hα : 0≤α) (hβ : 0≤β) (hβ1 : β<1)
    (h₀ : p₀∈ScaleGood (fun n => (f n).symm) h q α β)
    (hp : p∈ScaleGood (fun n => (f n).symm) h q α β) (hd : dist p p₀<h/4)
    (hz : ∀ n, (f n).symm p₀=0) (hU : ∀ n, radialU (f n).symm p₀ h=1)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (v : Point)
    (hl : Tendsto (fun n => (f (φ n)).symm p) atTop (𝓝 v)) :
    Tendsto (fun z : ℕ × Point => (f (φ z.1)).symm z.2) (atTop ×ˢ 𝓝 p) (𝓝 v) := by
  apply joint_of_asymptotic_continuity _ hl
  have hi := scaleGood_iteration f hs ht hh hq hq2 hα hβ h₀ hp hd hz hU
  have hb (n j : ℕ) : closedBall p (h*q^j) ⊆ (f n).target := by
    rw [ht n]
    exact (closedBall_subset_closedBall (mul_le_of_le_one_right hh.le
      (pow_le_one₀ hq.le (by linarith)))).trans (rankCore_ball hh hp.1)
  intro ε hε
  have he : Tendsto (fun j : ℕ => 2*β^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).const_mul 2
  obtain ⟨j,hj⟩ := ((tendsto_order.mp he).2 ε hε).exists
  refine ⟨h*q^(j+1),mul_pos hh (pow_pos hq _),?_⟩
  filter_upwards [hφ.tendsto_atTop.eventually (hi.2 j)] with n hn x hx
  have hdisk := radial_upper_enclosure (f (φ n)) (hs (φ n))
    (by positivity : 0≤2*β^j) (hb (φ n) (j+1)) (fun y hy =>
      ((radial_extrema_bounds (mul_pos hh (pow_pos hq _))
        ((f (φ n)).continuousOn_symm.mono (hb (φ n) (j+1)))).2.2 y hy).2.trans hn.2)
  exact (hdisk x hx.le).trans hj.le

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

lemma positive_localization {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) (hpos : μ E≠0)
    (π : X → Point) (hπ : Measurable π) {r : ℝ} (hr : 0<r) :
    ∃ (G : Set X) (x₀ : X), MeasurableSet G ∧ G⊆E ∧ μ G≠0 ∧ x₀∈G ∧
      ∀ x∈G, dist (π x) (π x₀)<r := by
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq Point
  let A : ℕ → Set X := fun j => π ⁻¹' ball (a j) (r/2)
  obtain ⟨j,hj⟩ := Limits.positive_countable_selection μ E hE hpos A (by
    apply Eventually.of_forall
    intro x
    obtain ⟨j,hj⟩ := ha.exists_dist_lt (π x) (half_pos hr)
    exact ⟨j,by simpa only [A,mem_preimage,mem_ball,dist_comm] using hj⟩)
  let G := E∩A j
  obtain ⟨x₀,hx₀⟩ := nonempty_of_measure_ne_zero hj
  refine ⟨G,x₀,hE.inter (measurableSet_ball.preimage hπ),inter_subset_left,hj,hx₀,?_⟩
  intro x hx
  have h1 : dist (π x) (a j)<r/2 := hx.2
  have h2 : dist (π x₀) (a j)<r/2 := hx₀.2
  have ht := dist_triangle (π x) (a j) (π x₀)
  rw [dist_comm (a j) (π x₀)] at ht
  linarith

lemma integer_scale_parameters {M : ℕ} (hM : 2≤M) :
    0<1/(M:ℝ)^16 ∧ 1/(M:ℝ)^16≤1/2 ∧
      0≤(M:ℝ)/(M:ℝ)^16 ∧ (M:ℝ)/(M:ℝ)^16<1 ∧
      (1/(M:ℝ)^16)^((17:ℝ)/16)=1/((M:ℝ)*(M:ℝ)^16) := by
  have hMp : 0<(M:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) hM)
  have hM2 : (2:ℝ)≤M := by exact_mod_cast hM
  have hM1 : 1<(M:ℝ) := by linarith
  have hp : 0<(M:ℝ)^16 := pow_pos hMp _
  have hpow : (M:ℝ)<(M:ℝ)^16 := lt_self_pow₀ hM1 (by decide)
  refine ⟨by positivity,?_,by positivity,(div_lt_one hp).mpr hpow,?_⟩
  · apply (div_le_iff₀ hp).mpr
    linarith
  · calc
      (1/(M:ℝ)^16)^((17:ℝ)/16) = (((M:ℝ)⁻¹)^16)^((17:ℝ)/16) := by rw [inv_pow,one_div]
      _ = ((M:ℝ)⁻¹)^(17:ℝ) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (inv_nonneg.mpr hMp.le)]
        norm_num
      _ = 1/((M:ℝ)*(M:ℝ)^16) := by
        rw [show (17:ℝ)=(17:ℕ) by norm_num,Real.rpow_natCast,pow_succ,inv_pow]
        field_simp

lemma positive_spatial_witness {X : Type*} [MeasurableSpace X]
    (μ θ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure θ]
    (E : Set X) (hE : MeasurableSet E) (hpos : θ E≠0)
    (π : X → Point) (hπ : Measurable π)
    (hac : (θ.restrict E).map π ≪ volume)
    (f : ℕ → OpenPartialHomeomorph Point Point)
    (hs : ∀ n, (f n).source=univ)
    (ht : ∀ n, (f n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0)
    (hc : ∀ᵐ x ∂θ.restrict E, π x∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C : ℝ, 0<C ∧ ∀ T : ℝ, 1≤T → ∀ᶠ h in 𝓝[>] (0:ℝ),
        ∀ᶠ n in atTop, Zoom.RadialCompare (f n).symm (π x) h C T) :
    ∃ (G : Set X), MeasurableSet G ∧ G⊆E ∧ θ G≠0 ∧
      ∃ (m : ℕ), (μ.restrict G).map π≤(m:ℝ≥0∞) • volume ∧
        ∃ (p₀ : Point) (U : ℕ → ℝ) (hU : ∀ n, 0<U n)
          (φ : ℕ → ℕ) (l : (π '' G) → Point) (c : ℝ),
          0<c ∧ StrictMono φ ∧ (∀ p, ‖l p‖≤1) ∧
          (∀ p : (π '' G), Tendsto (fun z : ℕ × Point =>
            (normalizeChart (f (φ z.1)) p₀ (U (φ z.1)) (hU (φ z.1)).ne').symm z.2)
              (atTop ×ˢ 𝓝 (p:Point)) (𝓝 (l p))) ∧
          ∀ p p' : (π '' G), c*dist (p:Point) p'^((17:ℝ)/16)≤dist (l p) (l p') := by
  have hcont (n : ℕ) : ContinuousOn (f n).symm (Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0) := by
    rw [← ht n]; exact (f n).continuousOn_symm
  obtain ⟨M,k,hM,hAmeas,hApos⟩ := positive_scaleGood θ E hE hpos π hπ
    (fun n => (f n).symm) hcont hc
  obtain ⟨hq,hq2,hβ,hβ1,hα⟩ := integer_scale_parameters hM
  let q : ℝ := 1/(M:ℝ)^16
  let h : ℝ := q^k
  let β : ℝ := (M:ℝ)/(M:ℝ)^16
  have hh : 0<h := pow_pos hq k
  let A : Set X := E ∩ π ⁻¹' ScaleGood (fun n => (f n).symm) h q (q^((17:ℝ)/16)) β
  have hAm : MeasurableSet A := by simpa only [A,h,q,β,hα] using hAmeas
  have hAp : θ A≠0 := by simpa only [A,h,q,β,hα] using hApos
  have hAE : A⊆E := inter_subset_left
  have hacA : (θ.restrict A).map π ≪ volume := by
    exact (Measure.absolutelyContinuous_of_le (Measure.map_mono (Measure.restrict_mono_set θ hAE) hπ)).trans hac
  obtain ⟨m,B,hBm,hBA,hBp,hBd⟩ := Limits.positive_bounded_projection μ θ volume π hπ A hAm hAp hacA
  obtain ⟨G,x₀,hGm,hGB,hGp,hx₀,hloc⟩ := positive_localization θ B hBm hBp π hπ (by positivity : 0<h/4)
  have hGA : G⊆A := hGB.trans hBA
  have hgood : π '' G ⊆ ScaleGood (fun n => (f n).symm) h q (q^((17:ℝ)/16)) β := by
    rintro p ⟨x,hx,rfl⟩; exact (hGA hx).2
  let p₀ := π x₀
  have hp₀ : p₀∈π '' G := mem_image_of_mem π hx₀
  have hb₀ (n : ℕ) : closedBall p₀ h ⊆ (f n).target := by
    rw [ht n]; exact rankCore_ball hh (hgood hp₀).1
  let U : ℕ → ℝ := fun n => radialU (f n).symm p₀ h
  have hU (n : ℕ) : 0<U n := by
    have hv := radialV_pos hh ((f n).continuousOn_symm.mono (hb₀ n))
      ((f n).symm.injOn.mono (hb₀ n))
    exact hv.trans_le (radial_extrema_bounds hh ((f n).continuousOn_symm.mono (hb₀ n))).2.1
  let g : ℕ → OpenPartialHomeomorph Point Point := fun n => normalizeChart (f n) p₀ (U n) (hU n).ne'
  have hgs (n : ℕ) : (g n).source=univ := normalizeChart_source _ (hs n) _ _ _
  have hgt (n : ℕ) : (g n).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := ht n
  have hg : π '' G ⊆ ScaleGood (fun n => (g n).symm) h q (q^((17:ℝ)/16)) β := by
    intro p hp
    exact normalizeChart_scaleGood f ht p₀ U hU hh hq (by linarith) (hgood hp)
  have hz (n : ℕ) : (g n).symm p₀=0 := by simp [g]
  have hgU (n : ℕ) : radialU (g n).symm p₀ h=1 := by
    rw [(normalizeChart_radial (f n) p₀ (hU n) hh (hb₀ n)).1]
    exact inv_mul_cancel₀ (hU n).ne'
  obtain ⟨φ,l,hφ,hl,hmov,hsep⟩ := normalized_spatial_limit g hgs hgt (π '' G) p₀ hp₀
    hh hq hq2 (by norm_num : (0:ℝ)<17/16) hβ hβ1 hg
    (by rintro p ⟨x,hx,rfl⟩; exact hloc x hx) hz hgU
  refine ⟨G,hGm,hGA.trans hAE,hGp,m,?_,p₀,U,hU,φ,l,q^((17:ℝ)/16)*(q/h)^((17:ℝ)/16),
    by positivity,hφ,hl,?_,hsep⟩
  · exact (Measure.map_mono (Measure.restrict_mono_set μ hGB) hπ).trans hBd
  · intro p
    apply scaleGood_joint g hgs hgt hh hq hq2 (by positivity) hβ hβ1
      (hg hp₀) (hg p.property) _ hz hgU φ hφ (l p)
    · exact hmov p (fun _ => (p:Point)) tendsto_const_nhds
    · obtain ⟨x,hx,he⟩ := p.property
      rw [← he]; exact hloc x hx

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal unitInterval

lemma continuous_encode : Continuous encode := by
  exact (unitInterval.continuous_sigmoid.comp continuous_fst).prodMk
    (unitInterval.continuous_sigmoid.comp continuous_snd)

lemma measurable_decode : Measurable decode := by
  exact ((Real.measurable_log.comp ((measurable_subtype_coe.comp measurable_fst).inv.sub measurable_const)).neg).prodMk
    ((Real.measurable_log.comp ((measurable_subtype_coe.comp measurable_snd).inv.sub measurable_const)).neg)

lemma support_spatial_graph {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μs : ℕ → FiniteMeasure (X × Cube)} {μ : FiniteMeasure (X × Cube)}
    (hμ : Tendsto μs atTop (𝓝 μ)) (π : X → Point) (hπ : Continuous π)
    (f : ℕ → Point → Point)
    (hid : ∀ᶠ n in atTop, ∀ᵐ z ∂(μs n : Measure (X × Cube)), z.2=encode (f n (π z.1)))
    (G : Set X) (l : (π '' G) → Point)
    (hjoint : ∀ p : (π '' G), Tendsto (fun q : ℕ × Point => f q.1 q.2)
      (atTop ×ˢ 𝓝 (p:Point)) (𝓝 (l p)))
    {z : X × Cube} (hz : z∈(μ : Measure (X × Cube)).support) (hG : z.1∈G) :
    z.2=encode (l ⟨π z.1,mem_image_of_mem π hG⟩) := by
  exact Limits.support_coordinate_identity hμ (fun z => π z.1) (hπ.comp continuous_fst)
    Prod.snd continuous_snd (fun n p => encode (f n p)) hid hz
    ((continuous_encode.tendsto _).comp (hjoint ⟨π z.1,mem_image_of_mem π hG⟩))

end PlanarHalving.Spatial

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped ENNReal

lemma volume_closedBall_point (p : Point) {r : ℝ} (hr : 0≤r) :
    volume (closedBall p r)=ENNReal.ofReal (4*r^2) := by
  rw [← closedBall_prod_same]
  change (volume.prod volume) (closedBall p.1 r ×ˢ closedBall p.2 r)=_
  rw [Measure.prod_prod,Real.volume_closedBall,Real.volume_closedBall,← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma disk_bound_of_inverse_holder {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : Set X) (hG : MeasurableSet G)
    (π ψ : X → Point) (hπ : Measurable π) (hψ : Measurable ψ)
    {M : ℝ≥0∞} {c s : ℝ} (hc : 0<c) (hs : 0<s)
    (hdensity : (μ.restrict G).map π≤M • volume)
    (hsep : ∀ x∈G, ∀ y∈G, c*dist (π x) (π y)^s≤dist (ψ x) (ψ y))
    (x : Point) {r : ℝ} (hr : 0<r) :
    (μ.restrict G).map ψ (closedBall x r) ≤
      M*ENNReal.ofReal (4*(2/c)^(2/s))*ENNReal.ofReal (r^(2/s)) := by
  let A := ψ ⁻¹' closedBall x r ∩ G
  have hA : MeasurableSet A := (measurableSet_closedBall.preimage hψ).inter hG
  rw [Measure.map_apply hψ measurableSet_closedBall,Measure.restrict_apply (measurableSet_closedBall.preimage hψ)]
  change μ A≤_
  by_cases hzero : μ A=0
  · rw [hzero]; exact zero_le
  obtain ⟨a,ha⟩ := nonempty_of_measure_ne_zero hzero
  let R : ℝ := (2*r/c)^(s⁻¹)
  have hR : 0≤R := Real.rpow_nonneg (by positivity) _
  have hsub : A ⊆ π ⁻¹' closedBall (π a) R ∩ G := by
    intro b hb
    refine ⟨?_,hb.2⟩
    change dist (π b) (π a)≤(2*r/c)^(s⁻¹)
    apply (Real.le_rpow_inv_iff_of_pos dist_nonneg (by positivity) hs).mpr
    apply (le_div_iff₀ hc).mpr
    have he := hsep b hb.2 a ha.2
    have ht := dist_triangle (ψ b) x (ψ a)
    have hb' : dist (ψ b) x≤r := hb.1
    have ha' : dist (ψ a) x≤r := ha.1
    rw [dist_comm x (ψ a)] at ht
    linarith
  calc
    μ A ≤ μ (π ⁻¹' closedBall (π a) R ∩ G) := measure_mono hsub
    _ = (μ.restrict G).map π (closedBall (π a) R) := by
      rw [Measure.map_apply hπ measurableSet_closedBall,Measure.restrict_apply (measurableSet_closedBall.preimage hπ)]
    _ ≤ (M • volume) (closedBall (π a) R) := hdensity _
    _ = M*ENNReal.ofReal (4*R^2) := by rw [Measure.smul_apply,smul_eq_mul,volume_closedBall_point _ hR]
    _ = M*ENNReal.ofReal (4*(2/c)^(2/s))*ENNReal.ofReal (r^(2/s)) := by
      have hpow : R^2=(2/c)^(2/s)*r^(2/s) := by
        dsimp [R]
        rw [← Real.rpow_mul_natCast (by positivity : 0≤2*r/c)]
        rw [show s⁻¹*(2:ℕ)=2/s by simp only [Nat.cast_ofNat]; ring]
        rw [show 2*r/c=(2/c)*r by ring,Real.mul_rpow (by positivity) hr.le]
      rw [hpow,← mul_assoc (4:ℝ),ENNReal.ofReal_mul (by positivity),mul_assoc]

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

lemma points_map (F : Configuration) (ψ : Point → Point) : (points F ψ).map Prod.fst=F.points := by
  rw [points,map_weightedAtoms _ _ measurable_fst]
  rfl
lemma vertices_map (F : Configuration) (ψ : Point → Point) (J : Window) :
    (vertices F ψ J).map Prod.fst=F.vertices J := by
  rw [vertices,System.vertexMeasure,map_weightedAtoms _ _ measurable_fst]
  rfl
lemma edges_map (F : Configuration) (ψ : Point → Point) (J : Window) :
    (edges F ψ J).map Prod.fst=F.edgeWindow J := by
  rw [F.edgeWindow_eq,edges,System.endpointMeasure,map_weightedAtoms _ _ measurable_fst]
  rfl

lemma points_mass (F : Configuration) (ψ : Point → Point) : (points F ψ).mass=1 := by
  rw [points,mass_weightedAtoms,Fintype.card_fin]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne F.n))
lemma vertices_mass (F : Configuration) (ψ : Point → Point) (J : Window) :
    (vertices F ψ J).mass=(F.vertices J).mass := by
  simp only [vertices,Configuration.vertices,System.vertexMeasure,mass_weightedAtoms]
lemma edges_mass (F : Configuration) (ψ : Point → Point) (J : Window) :
    (edges F ψ J).mass=(F.edgeWindow J).mass := by
  rw [F.edgeWindow_eq,edges]
  simp only [System.endpointMeasure,mass_weightedAtoms]

lemma measures_mass_le (F : Configuration) (ψ : Point → Point) (i : Index) :
    (measures F ψ i).mass≤1 := by
  cases i with
  | point => exact (points_mass F ψ).le
  | vertex J => exact (vertices_mass F ψ J).le.trans (F.vertices_mass_le J)
  | edge J =>
    change (edges F ψ J).mass≤1
    rw [edges_mass]
    exact (FiniteMeasure.mass_map_le _ (F.timeRestrict J)).trans (F.timeRestrict_mass_le J)

theorem subsequence {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (ψ : ℕ → Point → Point) :
    ∃ (φ : ℕ → ℕ) (M : Index → FiniteMeasure Space), StrictMono φ ∧
      (∀ i, Tendsto (fun n => measures (F (φ n)) (ψ (φ n)) i) atTop (𝓝 (M i))) ∧
      ∀ i, (M i).map Prod.fst=old L i := by
  obtain ⟨φ,M,hφ,hM⟩ := finiteMeasure_subsequence_dependent (X:=fun _ : Index => Space)
    (fun n i => measures (F n) (ψ n) i) (fun _ => 1) (fun n i => measures_mass_le (F n) (ψ n) i)
  refine ⟨φ,M,hφ,hM,?_⟩
  intro i
  have hm := (FiniteMeasure.continuous_map continuous_fst).tendsto (M i) |>.comp (hM i)
  apply tendsto_nhds_unique hm
  cases i with
  | point =>
    change Tendsto (fun n => (points (F (φ n)) (ψ (φ n))).map Prod.fst) atTop (𝓝 L.points)
    simp_rw [points_map]
    exact hF.points.comp hφ.tendsto_atTop
  | vertex J =>
    change Tendsto (fun n => (vertices (F (φ n)) (ψ (φ n)) J).map Prod.fst) atTop (𝓝 (L.vertices J))
    simp_rw [vertices_map]
    exact (hF.vertices J).comp hφ.tendsto_atTop
  | edge J =>
    change Tendsto (fun n => (edges (F (φ n)) (ψ (φ n)) J).map Prod.fst) atTop (𝓝 (L.edgeWindow J))
    simp_rw [edges_map]
    exact (hF.edgeWindow J).comp hφ.tendsto_atTop

end PlanarHalving.Enhancement

namespace PlanarHalving.Spatial
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

lemma support_lift_disk {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure (X × Cube)) (G : Set X) (hG : MeasurableSet G)
    (π : X → Point) (hπ : Measurable π) (l : (π '' G) → Point)
    {m : ℕ} {c : ℝ} (hc : 0<c)
    (hdensity : (((μ.map Prod.fst).restrict G).map π)≤(m:ℝ≥0∞) • volume)
    (hgraph : ∀ z∈μ.support, ∀ hz : z.1∈G, z.2=encode (l ⟨π z.1,mem_image_of_mem π hz⟩))
    (hl : ∀ p, ‖l p‖≤1)
    (hsep : ∀ p p' : (π '' G), c*dist (p:Point) p'^((17:ℝ)/16)≤dist (l p) (l p')) :
    let H := Prod.fst ⁻¹' G ∩ μ.support
    let β := (μ.restrict H).map (decode ∘ Prod.snd)
    MeasurableSet H ∧
      (∀ z∈H, ‖decode z.2‖≤1) ∧
      ∃ C : ℝ, 0≤C ∧ ∀ x : Point, ∀ r : ℝ, 0<r →
        β (closedBall x r)≤ENNReal.ofReal (C*r^((32:ℝ)/17)) := by
  dsimp only
  let H := Prod.fst ⁻¹' G ∩ μ.support
  have hH : MeasurableSet H := (hG.preimage measurable_fst).inter μ.isClosed_support.measurableSet
  have hmap : ((μ.restrict (Prod.fst ⁻¹' G)).map (π∘Prod.fst))=
      ((μ.map Prod.fst).restrict G).map π := by
    rw [Measure.restrict_map measurable_fst hG,Measure.map_map hπ measurable_fst]
  have hd : (μ.restrict H).map (π∘Prod.fst)≤(m:ℝ≥0∞) • volume :=
    (Measure.map_mono (Measure.restrict_mono_set μ inter_subset_left) (hπ.comp measurable_fst)).trans
      (hmap ▸ hdensity)
  have hg (z : X × Cube) (hz : z∈H) : decode z.2=l ⟨π z.1,mem_image_of_mem π hz.1⟩ := by
    rw [hgraph z hz.2 hz.1,decode_encode]
  refine ⟨hH,fun z hz => by rw [hg z hz]; exact hl _,
    (m:ℝ)*(4*(2/c)^((32:ℝ)/17)),by positivity,?_⟩
  intro x r hr
  have hh := disk_bound_of_inverse_holder μ H hH (π∘Prod.fst) (decode∘Prod.snd)
    (hπ.comp measurable_fst) (measurable_decode.comp measurable_snd)
    hc (by norm_num : (0:ℝ)<17/16) hd (by
      intro z hz w hw
      simpa only [Function.comp_apply,hg z hz,hg w hw] using
        hsep ⟨π z.1,mem_image_of_mem π hz.1⟩ ⟨π w.1,mem_image_of_mem π hw.1⟩) x hr
  convert hh using 1
  norm_num only [show (2:ℝ)/(17/16)=32/17 by norm_num,
      ENNReal.ofReal_mul (Nat.cast_nonneg m),ENNReal.ofReal_natCast,
      ENNReal.ofReal_mul (by positivity : 0≤(4:ℝ)*(2/c)^((32:ℝ)/17)),mul_assoc]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

end PlanarHalving.Spatial

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
open Set Filter MeasureTheory Batches TimeWindows Limits
open scoped Topology unitInterval ENNReal

lemma Converges.window_le_edge {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (J : Window) :
    (L.edgeWindow J : Measure Labels)≤(L.edge : Measure Labels) := by
  rw [Data.edgeWindow,Data.edge,FiniteMeasure.toMeasure_map,FiniteMeasure.toMeasure_map,
    h.restriction_eq hR]
  exact Measure.map_mono Measure.restrict_le_self measurable_fst

lemma commonSet_measurable (L : Data) {K : Window} (q : CommonChoice K) :
    MeasurableSet (commonSet L q) := by
  have hm (J : Window) : MeasurableSet {z | L.conditional z (carrier J)≠0} :=
    ((L.conditional.measurable_coe (measurable_carrier J)) (measurableSet_singleton 0)).compl
  exact (hm q.val.1).inter ((hm q.val.2.1).inter (hm q.val.2.2))

lemma Converges.common_positive {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (K : Window)
    (hna : ∀ᵐ z ∂(L.edge : Measure Labels), NullSingletonClass (L.conditional z))
    {T : Set Labels} (hT : MeasurableSet T) (hTp : (L.edge : Measure Labels) T≠0)
    (hK : ∀ z∈T, L.conditional z (carrier K)≠0) :
    ∃ (q : CommonChoice K) (E : Set Labels), MeasurableSet E ∧ E⊆T ∧
      (∀ z∈E, z∈commonSet L q) ∧ (L.edgeWindow q.val.2.2 : Measure Labels) E≠0 ∧
      (L.edgeWindow q.val.2.2 : Measure Labels).restrict E ≤ (L.edge : Measure Labels).restrict T := by
  have hcover : ∀ᵐ z ∂(L.edge : Measure Labels).restrict T, ∃ q : CommonChoice K, z∈commonSet L q := by
    filter_upwards [ae_restrict_of_ae hna,ae_restrict_mem hT] with z hz hzt
    let := hz
    exact exists_commonChoice (L.conditional z) K (hK z hzt)
  obtain ⟨q,hq⟩ := positive_countable_selection (L.edge : Measure Labels) T hT hTp (commonSet L) hcover
  let E := T∩commonSet L q
  have hE : MeasurableSet E := hT.inter (commonSet_measurable L q)
  have hac : (L.edge : Measure Labels).restrict E ≪ (L.edgeWindow q.val.2.2 : Measure Labels) := by
    rw [h.window_withDensity hR]
    exact restrict_ac_withDensity _ _ (L.conditional.measurable_coe (measurable_carrier _)) hE
      (fun z hz => hz.2.2.2)
  refine ⟨q,E,hE,inter_subset_left,fun _ hz => hz.2,?_,?_⟩
  · intro he
    have hzero := hac he
    rw [Measure.restrict_apply hE,inter_self] at hzero
    exact hq hzero
  · exact Measure.restrict_mono inter_subset_left (h.window_le_edge hR _)

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

lemma common_frame (F : ℕ → Configuration) {K : Window} (q : CommonChoice K)
    (h12 : ∀ n, (F n).timeSlope (q.time 0)<(F n).timeSlope (q.time 1))
    (h23 : ∀ n, (F n).timeSlope (q.time 1)<(F n).timeSlope (q.time 2)) :
    ∃ E : ℕ → Point ≃L[ℝ] Point,
      (∀ n i, detPair ((E n).symm (1,(F n).timeSlope (q.time i))) (commonDirection i)=0) ∧
      ∀ n, ∃ a b l u : ℝ, 0<a ∧ 0<b ∧ l<u ∧
        E n (1,0)=a • (1,l) ∧ E n (0,1)=b • (1,u) ∧
        ∀ i, ((F n).system.timeWindow q.val.2.2).slope i∈Icc l u := by
  choose E a b ha hb h1 h2 h3 using fun n => slope_frame (h12 n) (h23 n)
  refine ⟨E,?_,?_⟩
  · intro n i
    have h1' : (E n).symm (1,(F n).timeSlope (q.time 0))=(a n)⁻¹ • (1,0) := by
      apply (E n).injective
      rw [(E n).apply_symm_apply,map_smul,h1,smul_smul,inv_mul_cancel₀ (ha n).ne',one_smul]
    have h2' : (E n).symm (1,(F n).timeSlope (q.time 2))=(b n)⁻¹ • (0,1) := by
      apply (E n).injective
      rw [(E n).apply_symm_apply,map_smul,h2,smul_smul,inv_mul_cancel₀ (hb n).ne',one_smul]
    have h3' : (E n).symm (1,(F n).timeSlope (q.time 1))=(1,1) := by
      rw [←h3,(E n).symm_apply_apply]
    fin_cases i
    · change detPair ((E n).symm (1,(F n).timeSlope (q.time 0))) (1,0)=0
      rw [h1']; simp [detPair]
    · change detPair ((E n).symm (1,(F n).timeSlope (q.time 1))) (1,1)=0
      rw [h3']; simp [detPair]
    · change detPair ((E n).symm (1,(F n).timeSlope (q.time 2))) (0,1)=0
      rw [h2']; simp [detPair]
  · intro n
    refine ⟨a n,b n,_,_,ha n,hb n,(h12 n).trans (h23 n),h1 n,h2 n,?_⟩
    intro i
    constructor
    · exact ((F n).timeSlope_before (J:=q.val.2.2) q.property.2.2.2.1.le).trans
        (((F n).system.timeWindow q.val.2.2).increasing.monotone (Fin.zero_le i))
    · apply (((F n).system.timeWindow q.val.2.2).increasing.monotone (Fin.le_last i)).trans
      exact (F n).timeSlope_after (J:=q.val.2.2)
        (q.property.2.2.2.2.trans (q.property.2.1.trans (lower_lt_upper q.val.2.1))).le

lemma commonChart_source (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) :
    (commonChart F hAB hA hB E).source=univ := by
  simp [commonChart,F.rankChart_source]

lemma commonChart_target (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) :
    (commonChart F hAB hA hB E).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  simp [commonChart,F.rankChart_target]

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary
open scoped Topology unitInterval

lemma normalized_commonChart (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point)
    (p : Point) {U : ℝ} (hU : U≠0) (x : Point) :
    (normalizeChart (commonChart F hAB hA hB E) p U hU).symm x=
      physical E ((F.rankChart hAB hA hB).symm p) U⁻¹ ((F.rankChart hAB hA hB).symm x) := by
  simp only [normalizeChart_symm,commonChart_symm,physical,map_sub]

lemma enhancement_points_ae (F : Configuration) (ψ : Point → Point) (H : Space → Prop)
    (hH : ∀ p, H (Enhancement.label F ψ p)) :
    ∀ᵐ z ∂(Enhancement.points F ψ : Measure Space), H z := by
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  simpa only [ae_dirac_eq,Filter.eventually_pure,Function.comp_apply] using hH (F.point i)

lemma normalized_points_graph (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point)
    (p₀ : Point) {U : ℝ} (hU : U≠0) :
    let o := (F.rankChart hAB hA hB).symm p₀
    let ψ := physical E o U⁻¹
    ∀ᵐ z ∂(Enhancement.points F ψ : Measure Space), z.2=encode
      ((normalizeChart (commonChart F hAB hA hB E) p₀ U hU).symm
        (pairCoordinates true A B z.1)) := by
  dsimp only
  apply enhancement_points_ae
  intro p
  change encode (physical E _ _ p)=encode ((normalizeChart (commonChart F hAB hA hB E) p₀ U hU).symm
      (pairCoordinates true A B (F.system.labels F.generic p)))
  rw [normalized_commonChart,←F.rankChart_apply hAB hA hB p]
  rw [(F.rankChart hAB hA hB).left_inv (mem_univ p)]

lemma support_graph_subseq {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μs : ℕ → FiniteMeasure (X × Cube)} {μ : FiniteMeasure (X × Cube)}
    {τ : ℕ → ℕ} (hτ : StrictMono τ) (hμ : Tendsto (μs∘τ) atTop (𝓝 μ))
    (π : X → Point) (hπ : Continuous π) (f : ℕ → Point → Point)
    (hid : ∀ n, ∀ᵐ z ∂(μs n:Measure (X×Cube)), z.2=encode (f n (π z.1)))
    (G : Set X) (l : (π '' G) → Point)
    (hjoint : ∀ p : (π '' G), Tendsto (fun q : ℕ × Point => f q.1 q.2)
      (atTop ×ˢ 𝓝 (p:Point)) (𝓝 (l p))) :
    ∀ z∈(μ:Measure (X×Cube)).support, ∀ hz : z.1∈G,
      z.2=encode (l ⟨π z.1,mem_image_of_mem π hz⟩) := by
  intro z hz hG
  apply support_spatial_graph hμ π hπ (f∘τ)
    (Filter.Eventually.of_forall (fun n => hid (τ n))) G l _ hz hG
  intro p
  exact (hjoint p).comp (hτ.tendsto_atTop.prodMap tendsto_id)

lemma Converges.spatial_impossible {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (emb : ∀ n, (F n).SweepEmbedding)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) {A B : Window} (hAB : Before A B)
    (hA : ∀ n, 0<length (F n).R A) (hB : ∀ n, 0<length (F n).R B)
    (E : ℕ → Point ≃L[ℝ] Point)
    (hframe : ∀ n, ∃ a b l u : ℝ, 0<a ∧ 0<b ∧ l<u ∧
      E n (1,0)=a • (1,l) ∧ E n (0,1)=b • (1,u) ∧
      ∀ i, ((F n).system.timeWindow J).slope i∈Icc l u)
    (T : Set Labels) (hT : MeasurableSet T) (hTp : (L.edgeWindow J:Measure Labels) T≠0)
    (hac : ((L.edgeWindow J:Measure Labels).restrict T).map (pairCoordinates true A B)≪volume)
    (hrad : ∀ᵐ z ∂(L.edgeWindow J:Measure Labels).restrict T,
      pairCoordinates true A B z∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C₀ : ℝ, 0<C₀ ∧ ∀ Q : ℝ, 1≤Q → ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
        RadialCompare (commonChart (F n) hAB (hA n) (hB n) (E n)).symm
          (pairCoordinates true A B z) r C₀ Q) : False := by
  let π := pairCoordinates true A B
  let f := fun n => commonChart (F n) hAB (hA n) (hB n) (E n)
  obtain ⟨G,hG,hGT,hGp,m,hdensity,p₀,U,hU,φ,l,c,hc,hφ,hl,hjoint,hsep⟩ :=
    positive_spatial_witness (L.points:Measure Labels) (L.edgeWindow J:Measure Labels)
      T hT hTp π (continuous_pairCoordinates true A B).measurable hac f
      (fun n => commonChart_source _ _ _ _ _) (fun n => commonChart_target _ _ _ _ _) hrad
  let o := fun n => ((F n).rankChart hAB (hA n) (hB n)).symm p₀
  let ψ := fun n => physical (E n) (o n) (U n)⁻¹
  obtain ⟨ρ,M,hρ,hM,hprojection⟩ := Enhancement.subsequence (hF.subseq hφ) (fun n => ψ (φ n))
  have hgraph : ∀ z∈(M .point:Measure Space).support, ∀ hz : z.1∈G,
      z.2=encode (l ⟨π z.1,mem_image_of_mem π hz⟩) :=
    support_graph_subseq (μs:=fun n => Enhancement.points (F (φ n)) (ψ (φ n))) hρ
      (hM .point) π (continuous_pairCoordinates true A B)
      (fun n => (normalizeChart (f (φ n)) p₀ (U (φ n)) (hU (φ n)).ne').symm)
      (fun n => normalized_points_graph (F (φ n)) hAB (hA _) (hB _) (E _) p₀ (hU _).ne')
      G l hjoint
  have hmap : (M .point:Measure Space).map Prod.fst=(L.points:Measure Labels) := by
    rw [← FiniteMeasure.toMeasure_map]
    exact congrArg FiniteMeasure.toMeasure (hprojection .point)
  obtain ⟨hH,hbounded,D,hD,hdisk⟩ := support_lift_disk (M .point:Measure Space) G hG π
    (continuous_pairCoordinates true A B).measurable l hc (by rwa [hmap]) hgraph hl hsep
  have hz := enhanced_boundary_zero ((hF.subseq hφ).subseq hρ)
    ((hR.comp hφ.tendsto_atTop).comp hρ.tendsto_atTop) (fun n => emb (φ (ρ n)))
    hC (fun n => hcoeff (φ (ρ n))) ((herror.comp hφ.tendsto_atTop).comp hρ.tendsto_atTop)
    J (fun n => E (φ (ρ n))) (fun n => o (φ (ρ n))) (fun n => (U (φ (ρ n)))⁻¹)
    (fun n => inv_pos.mpr (hU _)) (fun n => hframe (φ (ρ n))) hM hprojection G hG
    (fun z hz => ⟨hbounded z hz,by rw [hgraph z hz.2 hz.1,decode_encode]⟩) hD hdisk
  have hz' : L.edgeWindow J G=0 := NNReal.coe_injective hz
  apply hGp
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hz',ENNReal.coe_zero]

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary
open scoped Topology unitInterval

lemma common_finite_eventually (F : ℕ → Configuration)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (A B : Window) {K : Window} (q : CommonChoice K) :
    ∀ᶠ n in atTop, 0<length (F n).R A ∧ 0<length (F n).R B ∧
      (F n).timeSlope (q.time 0)<(F n).timeSlope (q.time 1) ∧
      (F n).timeSlope (q.time 1)<(F n).timeSlope (q.time 2) := by
  filter_upwards [eventually_length_pos _ hR A,eventually_length_pos _ hR B,
    timeSlope_eventually_lt F hR (q.time_strictMono (by decide : (0:Fin 3)<1)),
    timeSlope_eventually_lt F hR (q.time_strictMono (by decide : (1:Fin 3)<2))]
    with n hA hB h12 h23
  exact ⟨hA,hB,h12,h23⟩

lemma joint_shift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ℕ → X → Y) {p : X} {y : Y}
    (h : Tendsto (fun z : ℕ × X => f z.1 z.2) (atTop ×ˢ 𝓝 p) (𝓝 y)) (N : ℕ) :
    Tendsto (fun z : ℕ × X => f (z.1+N) z.2) (atTop ×ˢ 𝓝 p) (𝓝 y) :=
  h.comp ((tendsto_add_atTop_nat N).prodMap tendsto_id)

lemma Converges.analytic_ready {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (q : CommonChoice K) :
    ∃ (φ : ℕ → ℕ) (G : Subwindows K → Point → I), StrictMono φ ∧
      (∀ n, 0<length (F (φ n)).R A ∧ 0<length (F (φ n)).R B ∧
        (F (φ n)).timeSlope (q.time 0)<(F (φ n)).timeSlope (q.time 1) ∧
        (F (φ n)).timeSlope (q.time 1)<(F (φ n)).timeSlope (q.time 2)) ∧
      (∀ i, ∀ᵐ p ∂(volume:Measure Point), DifferentiableAt ℝ (fun x => (G i x:ℝ)) p) ∧
      (∀ i z, z∈(L.points:Measure Labels).support →
        ContinuousAt (G i) (pairCoordinates true A B z) → z i.val=G i (pairCoordinates true A B z)) ∧
      ∀ i p, ContinuousAt (G i) p → Tendsto
        (fun z : ℕ × Point => (F (φ z.1)).extendedRank true A B i.val z.2)
        (atTop ×ˢ 𝓝 p) (𝓝 (G i p)) := by
  have hC (i : Subwindows K) : Before i.val A ∧ Before i.val B :=
    ⟨(endpoints_of_subset i.property).2.trans hKA,(endpoints_of_subset i.property).2.trans hKB⟩
  obtain ⟨φ,G,hφ,_,hGaed,hid,hjoint⟩ := hF.rank_analytic hR true hAB
    (fun i : Subwindows K => i.val) (fun i => hC i)
  have hR' : Tendsto (fun n => (F (φ n)).R) atTop atTop := hR.comp hφ.tendsto_atTop
  have he := common_finite_eventually (F∘φ) hR' A B q
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨fun n => φ (n+N),G,(fun _ _ h => hφ (Nat.add_lt_add_right h N)),
    (fun n => hN (n+N) (Nat.le_add_left N n)),hGaed,hid,?_⟩
  intro i p hp
  exact joint_shift (fun n => (F (φ n)).extendedRank true A B i.val) (hjoint i p hp) N

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary
open scoped Topology unitInterval

lemma Converges.impossible_oai {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (emb : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n:ℝ)/((F n).R*(F n).a)) atTop (𝓝 0)) : False := by
  obtain ⟨K,H,A,B,T,hKH,hAH,hBH,hAB,hT,hTp,hpos,hcross,hpts⟩ :=
    hF.positive_part emb hR hC hcoeff herror hshort
  obtain ⟨q,V,hV,hVT,hcommon,hVp,hVle⟩ := hF.common_positive hR K
    (hF.conditional_nullSingleton emb hR hC hcoeff herror) hT hTp (fun z hz => (hpos z hz).1)
  let ν := (L.edgeWindow q.val.2.2:Measure Labels).restrict V
  have he : ν≪(L.edge:Measure Labels) :=
    Measure.absolutelyContinuous_of_le (hVle.trans Measure.restrict_le_self)
  have hp : ν≪(L.points:Measure Labels) := (Measure.absolutelyContinuous_of_le hVle).trans hpts
  have hproj : ν.map (pairCoordinates true A B)≪volume :=
    (((Measure.absolutelyContinuous_of_le hVle).trans hcross).map
      (continuous_pairCoordinates true A B).measurable).trans (hF.crossing_signed_projection hR hM true hAB)
  have hgood : ∀ᵐ z ∂ν, L.conditional z (carrier K)≠0 ∧ z∈commonSet L q := by
    filter_upwards [ae_restrict_mem hV] with z hz
    exact ⟨(hpos z (hVT hz)).1,hcommon z hz⟩
  have hKA : Before K A := hKH.2.1.le.trans (endpoints_of_subset hAH).1
  have hKB : Before K B := hKH.2.1.le.trans (endpoints_of_subset hBH).1
  obtain ⟨φ,G,hφ,hfinite,hGaed,hid,hjoint⟩ := hF.analytic_ready hR hAB hKA hKB q
  have hF' : Converges (F∘φ) L := hF.subseq hφ
  have hR' : Tendsto (fun n => (F (φ n)).R) atTop atTop := hR.comp hφ.tendsto_atTop
  obtain ⟨E,hE,hframe⟩ := common_frame (F∘φ) q
    (fun n => (hfinite n).2.2.1) (fun n => (hfinite n).2.2.2)
  exact hF'.spatial_impossible hR' (fun n => emb (φ n)) hC (fun n => hcoeff (φ n))
    (herror.comp hφ.tendsto_atTop) q.val.2.2 hAB (fun n => (hfinite n).1)
    (fun n => (hfinite n).2.1) E hframe V hV hVp hproj
    (hF'.radial_ae (fun n => emb (φ n)) hR' (hM.comp hφ.tendsto_atTop) hC
      (fun n => hcoeff (φ n)) (herror.comp hφ.tendsto_atTop) (hshort.comp hφ.tendsto_atTop)
      hAB hKA hKB (fun n => (hfinite n).1) (fun n => (hfinite n).2.1)
      G hjoint hGaed hid ν he hp hproj q hgood E hE)

end PlanarHalving.RankLimits

end OAI
end

theorem solution : type_of% @OAI.PlanarHalving.RankLimits.Converges.impossible_oai := @OAI.PlanarHalving.RankLimits.Converges.impossible_oai

-- Prove2me | solution 1 for MinBuying.affiliated_coordinate_threshold
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:09:40.358498+00:00
-- url     : https://prove2.me/submissions/7228cb6d-1045-4836-950e-31e1cd5d8d05

import Theorems.Thm_MinBuying_integrable_four_functions

open MeasureTheory Set MinBuying
open scoped BigOperators FinsetFamily
noncomputable section

private lemma four_functions_summable {α : Type*} [DistribLattice α]
    (a b c d : α → ℝ)
    (ha : ∀ x,0 ≤ a x) (hb : ∀ x,0 ≤ b x) (hc : ∀ x,0 ≤ c x) (hd : ∀ x,0 ≤ d x)
    (h : ∀ x y,a x*b y ≤ c (x ⊓ y)*d (x ⊔ y))
    (sa : Summable a) (sb : Summable b) (sc : Summable c) (sd : Summable d) :
    (∑' x,a x)*(∑' x,b x) ≤ (∑' x,c x)*(∑' x,d x) := by
  classical
  apply le_of_tendsto' (Filter.Tendsto.mul sa.hasSum sb.hasSum)
  intro s
  have hfour := four_functions_theorem a b c d ha hb hc hd h s s
  have hsc : (∑ x ∈ s ⊼ s,c x) ≤ ∑' x,c x :=
    Summable.sum_le_tsum _ (fun x _ => hc x) sc
  have hsd : (∑ x ∈ s ⊻ s,d x) ≤ ∑' x,d x :=
    Summable.sum_le_tsum _ (fun x _ => hd x) sd
  exact hfour.trans (mul_le_mul hsc hsd (Finset.sum_nonneg (fun x _ => hd x)) (tsum_nonneg hc))

private lemma indicator_nonnegative {α : Type*} (w : α → ℝ) (hw : ∀ x,0 ≤ w x)
    (s : Set α) (x : α) : 0 ≤ s.indicator w x := by
  classical
  by_cases hx : x ∈ s <;> simp [hx,hw]

private lemma event_four_functions {n : ℕ} (w : Valuations n → ℝ)
    (hw : ∀ v,0 ≤ w v) (hmtp : MTP2 w) (i j : Fin n) (a s t : ℝ) (hst : s ≤ t) :
    ∀ v z : Valuations n,
      ({v | v i < a ∧ t ≤ v j}.indicator w v) * ({v | s ≤ v j}.indicator w z) ≤
        ({v | v i < a ∧ s ≤ v j}.indicator w (fun k => min (v k) (z k))) *
          ({v | t ≤ v j}.indicator w (fun k => max (v k) (z k))) := by
  classical
  intro v z
  by_cases hv : v i < a ∧ t ≤ v j
  · by_cases hz : s ≤ z j
    · have hmin : min (v i) (z i) < a ∧ s ≤ min (v j) (z j) :=
        ⟨(min_le_left _ _).trans_lt hv.1,le_min (hst.trans hv.2) hz⟩
      have hmax : t ≤ max (v j) (z j) := hv.2.trans (le_max_left _ _)
      simpa [Set.indicator,hv,hz,hmin,hmax,mul_comm] using hmtp v z
    · simp only [Set.indicator,Set.mem_setOf_eq,if_neg hz,mul_zero]
      apply mul_nonneg <;> split_ifs <;> first | exact hw _ | exact le_rfl
  · simp only [Set.indicator,Set.mem_setOf_eq,if_neg hv,zero_mul]
    apply mul_nonneg <;> split_ifs <;> first | exact hw _ | exact le_rfl

private lemma density_integrable {n : ℕ} (w : Valuations n → ℝ)
    (hw : Measurable w) (hw0 : ∀ v,0 ≤ w v)
    [IsFiniteMeasure (volume.withDensity (fun v => ENNReal.ofReal (w v)))] :
    Integrable w volume := by
  have h1 : Integrable (fun _ : Valuations n => (1:ℝ))
      (volume.withDensity (fun v => ENNReal.ofReal (w v))) := integrable_const 1
  have hh := (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp h1
  simpa only [smul_eq_mul,mul_one,ENNReal.toReal_ofReal (hw0 _)] using hh

private lemma density_event {n : ℕ} (w : Valuations n → ℝ)
    (hw : Measurable w) (hw0 : ∀ v,0 ≤ w v) (s : Set (Valuations n)) (hs : MeasurableSet s) :
    ((volume.withDensity (fun v => ENNReal.ofReal (w v))) s).toReal =
      ∫ v, s.indicator w v := by
  have he := integral_indicator_const (μ := volume.withDensity (fun v => ENNReal.ofReal (w v)))
    (1:ℝ) hs
  simp only [smul_eq_mul,mul_one,Measure.real] at he
  rw [← he,integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  by_cases hv : v ∈ s <;> simp [Set.indicator,hv,hw0]

private lemma pmf_event {n : ℕ} (w : PMF (Valuations n)) (s : Set (Valuations n))
    (hs : MeasurableSet s) :
    (w.toMeasure s).toReal = ∑' v, s.indicator (fun z => (w z).toReal) v := by
  classical
  rw [w.toMeasure_apply hs,ENNReal.tsum_toReal_eq (fun v => ?_)]
  · apply tsum_congr
    intro v
    by_cases hv : v ∈ s <;> simp [hv]
  · by_cases hv : v ∈ s <;> simp [hv,w.apply_ne_top]

theorem solution (n : ℕ) (μ : JointLaw n)
    (hμ : ValidLaw μ) (haff : Affiliated μ) (i j : Fin n)
    (a s t : ℝ) (hst : s ≤ t) :
    (μ {v | v i < a ∧ t ≤ v j}).toReal * (μ {v | s ≤ v j}).toReal ≤
      (μ {v | v i < a ∧ s ≤ v j}).toReal * (μ {v | t ≤ v j}).toReal := by
  classical
  let A : Set (Valuations n) := {v | v i < a ∧ t ≤ v j}
  let B : Set (Valuations n) := {v | s ≤ v j}
  let C : Set (Valuations n) := {v | v i < a ∧ s ≤ v j}
  let D : Set (Valuations n) := {v | t ≤ v j}
  have hA : MeasurableSet A :=
    (measurableSet_lt (measurable_pi_apply i) measurable_const).inter
      (measurableSet_le measurable_const (measurable_pi_apply j))
  have hB : MeasurableSet B := measurableSet_le measurable_const (measurable_pi_apply j)
  have hC : MeasurableSet C :=
    (measurableSet_lt (measurable_pi_apply i) measurable_const).inter hB
  have hD : MeasurableSet D := measurableSet_le measurable_const (measurable_pi_apply j)
  change (μ A).toReal * (μ B).toReal ≤ (μ C).toReal * (μ D).toReal
  rcases haff with ⟨w,hw,hw0,hmtp,rfl⟩ | ⟨w,rfl,hmtp⟩
  · letI : IsProbabilityMeasure (volume.withDensity (fun v => ENNReal.ofReal (w v))) := hμ.1
    have hi := density_integrable w hw hw0
    rw [density_event w hw hw0 A hA,density_event w hw hw0 B hB,
      density_event w hw hw0 C hC,density_event w hw hw0 D hD]
    exact integrable_four_functions n (A.indicator w) (B.indicator w)
      (C.indicator w) (D.indicator w)
      (indicator_nonnegative w hw0 A) (indicator_nonnegative w hw0 B)
      (indicator_nonnegative w hw0 C) (indicator_nonnegative w hw0 D)
      (event_four_functions w hw0 hmtp i j a s t hst)
      (hi.indicator hA) (hi.indicator hB) (hi.indicator hC) (hi.indicator hD)
  · let W : Valuations n → ℝ := fun v => (w v).toReal
    have hw0 : ∀ v,0 ≤ W v := fun _ => ENNReal.toReal_nonneg
    have hw : Summable W := ENNReal.summable_toReal w.tsum_coe_ne_top
    rw [pmf_event w A hA,pmf_event w B hB,pmf_event w C hC,pmf_event w D hD]
    apply four_functions_summable (A.indicator W) (B.indicator W) (C.indicator W) (D.indicator W)
      (indicator_nonnegative W hw0 A) (indicator_nonnegative W hw0 B)
      (indicator_nonnegative W hw0 C) (indicator_nonnegative W hw0 D)
      ?_ (hw.indicator A) (hw.indicator B) (hw.indicator C) (hw.indicator D)
    intro v z
    exact event_four_functions W hw0 hmtp i j a s t hst v z

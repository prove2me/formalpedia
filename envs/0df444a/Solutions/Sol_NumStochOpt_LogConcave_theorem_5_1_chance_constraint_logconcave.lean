-- Prove2me | solution 1 for NumStochOpt.LogConcave.theorem_5_1_chance_constraint_logconcave
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:41:34.19817+00:00
-- url     : https://prove2.me/submissions/2f282218-f86d-4e85-98d8-ad62bcea76ca

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_NumStochOpt_LogConcave_chanceProb
import Theorems.Thm_ConvexOptimization_prekopa_marginal_log_concave

set_option autoImplicit false

open MeasureTheory

namespace NumStochOpt.LogConcave.Glue8a1dca99

/-- Statement of the PROVED platform theorem fd4b27a3
(ConvexOptimization.prekopa_marginal_log_concave), taken as a hypothesis. -/
def PrekopaMarginal : Prop :=
  ∀ {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ),
    Measurable f → ConvexOptimization.LogConcaveOn Set.univ f →
    (∀ x : EuclideanSpace ℝ (Fin n), Integrable (fun y : EuclideanSpace ℝ (Fin m) => f (x, y))) →
    ConvexOptimization.LogConcaveOn Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) => ∫ y : EuclideanSpace ℝ (Fin m), f (x, y))

/-- G1: the joint integrand `1_C(x,y) f(y)` is log-concave. -/
theorem joint_logConcave {n q r : ℕ}
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) :
    ConvexOptimization.LogConcaveOn Set.univ
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) =>
        Set.indicator {p | ∀ i, 0 ≤ g i p} (fun p => f p.2) p) := by
  have hnn : ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q),
      0 ≤ Set.indicator {p | ∀ i, 0 ≤ g i p} (fun p => f p.2) p := fun p =>
    Set.indicator_nonneg (fun p _ => hf_lc.1 _ (Set.mem_univ _)) p
  refine ⟨fun p _ => hnn p, ?_⟩
  intro p _ s _ a b ha hb hab
  beta_reduce
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · have ha1 : a = 1 := by linarith
    subst ha1
    simp
  by_cases hp : p ∈ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) | ∀ i, 0 ≤ g i p}
  · by_cases hs : s ∈ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) | ∀ i, 0 ≤ g i p}
    · have hmem : a • p + b • s ∈
          {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) | ∀ i, 0 ≤ g i p} := by
        intro i
        have h1 := (hg i).2 (Set.mem_univ p) (Set.mem_univ s) ha hb hab
        have h2 : 0 ≤ g i p := hp i
        have h3 : 0 ≤ g i s := hs i
        simp only [smul_eq_mul] at h1
        nlinarith [mul_nonneg ha h2, mul_nonneg hb h3]
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hs, Set.indicator_of_mem hmem]
      have := hf_lc.2 p.2 (Set.mem_univ _) s.2 (Set.mem_univ _) a b ha hb hab
      simpa using this
    · rw [Set.indicator_of_notMem hs, Real.zero_rpow hb'.ne', mul_zero]
      exact hnn _
  · rw [Set.indicator_of_notMem hp, Real.zero_rpow ha'.ne', zero_mul]
    exact hnn _

/-- the constraint set is measurable (concave on univ in finite dimension ⇒ continuous). -/
theorem C_measurable {n q r : ℕ}
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) :
    MeasurableSet {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) | ∀ i, 0 ≤ g i p} := by
  have hc : ∀ i, Continuous (g i) := fun i =>
    continuousOn_univ.mp ((hg i).continuousOn isOpen_univ)
  have hcl : IsClosed
      {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) | ∀ i, 0 ≤ g i p} := by
    have : {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) | ∀ i, 0 ≤ g i p}
        = ⋂ i, {p | 0 ≤ g i p} := by ext p; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (hc i)
  exact hcl.measurableSet

/-- G2: measurability of the joint integrand. -/
theorem joint_measurable {n q r : ℕ}
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) =>
        Set.indicator {p | ∀ i, 0 ≤ g i p} (fun p => f p.2) p) :=
  (hf_meas.comp measurable_snd).indicator (C_measurable g hg)

/-- f is integrable (it is a probability density). -/
theorem f_integrable {Ω : Type*} [MeasurableSpace Ω] {q : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin q)) (hξ : Measurable ξ)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hlaw : P.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y))) :
    Integrable f := by
  have hl : ∫⁻ y, ENNReal.ofReal (f y) = 1 := by
    have h1 : (P.map ξ) Set.univ = 1 := by
      rw [Measure.map_apply hξ MeasurableSet.univ]; simp
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
    exact h1
  have hi := integrable_toReal_of_lintegral_ne_top
    (hf_meas.ennreal_ofReal).aemeasurable (by rw [hl]; exact ENNReal.one_ne_top)
  refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
  exact ENNReal.toReal_ofReal (hf_lc.1 y (Set.mem_univ _))

/-- G3: sections are integrable. -/
theorem section_integrable {Ω : Type*} [MeasurableSpace Ω] {n q r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin q)) (hξ : Measurable ξ)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hlaw : P.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => Set.indicator {p | ∀ i, 0 ≤ g i p} (fun p => f p.2) (x, y)) := by
  have hfi := f_integrable P ξ hξ f hf_meas hf_lc hlaw
  refine hfi.mono' (((joint_measurable f hf_meas g hg).comp
    measurable_prodMk_left).aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ f y := hf_lc.1 y (Set.mem_univ _)
  by_cases hm : (x, y) ∈ {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) | ∀ i, 0 ≤ g i p}
  · simp only [Set.indicator_of_mem hm, Real.norm_eq_abs, abs_of_nonneg h0, le_refl]
  · simp only [Set.indicator_of_notMem hm, norm_zero]
    exact h0

/-- G4: `h₀(x)` is the section integral. -/
theorem chanceProb_eq_integral {Ω : Type*} [MeasurableSpace Ω] {n q r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin q)) (hξ : Measurable ξ)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hlaw : P.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) (x : EuclideanSpace ℝ (Fin n)) :
    chanceProb P ξ g x =
      ∫ y, Set.indicator {p | ∀ i, 0 ≤ g i p} (fun p => f p.2) (x, y) := by
  set Cx : Set (EuclideanSpace ℝ (Fin q)) := {y | ∀ i, 0 ≤ g i (x, y)} with hCx_def
  have hCx : MeasurableSet Cx :=
    measurable_prodMk_left (C_measurable g hg)
  have hfun : (fun y => Set.indicator {p | ∀ i, 0 ≤ g i p} (fun p => f p.2) (x, y))
      = Cx.indicator f := by
    funext y
    by_cases hm : ∀ i, 0 ≤ g i (x, y)
    · rw [Set.indicator_of_mem (s := {p | ∀ i, 0 ≤ g i p}) hm,
        Set.indicator_of_mem (s := Cx) hm]
    · rw [Set.indicator_of_notMem (s := {p | ∀ i, 0 ≤ g i p}) hm,
        Set.indicator_of_notMem (s := Cx) hm]
  rw [hfun, integral_indicator hCx]
  have hpre : {ω | ∀ i, 0 ≤ g i (x, ξ ω)} = ξ ⁻¹' Cx := rfl
  unfold chanceProb
  rw [hpre, ← Measure.map_apply hξ hCx, hlaw, withDensity_apply _ hCx]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => hf_lc.1 y (Set.mem_univ _))
    hf_meas.aestronglyMeasurable]

/-- Assembly: the target, given the Prékopa marginal theorem as a hypothesis. -/
theorem theorem_5_1_of_marginal (hPM : PrekopaMarginal)
    {Ω : Type*} [MeasurableSpace Ω] {n q r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin q)) (hξ : Measurable ξ)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hlaw : P.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) :
    ConvexOptimization.LogConcaveOn Set.univ (chanceProb P ξ g) := by
  have key := hPM _ (joint_measurable f hf_meas g hg) (joint_logConcave f hf_lc g hg)
    (section_integrable P ξ hξ f hf_meas hf_lc hlaw g hg)
  have hfun : chanceProb P ξ g = fun x =>
      ∫ y, Set.indicator {p | ∀ i, 0 ≤ g i p} (fun p => f p.2) (x, y) := by
    funext x; exact chanceProb_eq_integral P ξ hξ f hf_meas hf_lc hlaw g hg x
  rw [hfun]; exact key

end NumStochOpt.LogConcave.Glue8a1dca99

open MeasureTheory NumStochOpt.LogConcave in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {n q r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin q)) (hξ : Measurable ξ)
    (f : EuclideanSpace ℝ (Fin q) → ℝ) (hf_meas : Measurable f)
    (hf_lc : ConvexOptimization.LogConcaveOn Set.univ f)
    (hlaw : P.map ξ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (g : Fin r → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin q) → ℝ)
    (hg : ∀ i, ConcaveOn ℝ Set.univ (g i)) :
    ConvexOptimization.LogConcaveOn Set.univ (chanceProb P ξ g) := by
  exact Glue8a1dca99.theorem_5_1_of_marginal
    (fun f hm hl hi => ConvexOptimization.prekopa_marginal_log_concave f hm hl hi)
    P ξ hξ f hf_meas hf_lc hlaw g hg

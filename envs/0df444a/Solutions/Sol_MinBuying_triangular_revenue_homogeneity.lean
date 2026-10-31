-- Prove2me | solution 1 for MinBuying.triangular_revenue_homogeneity
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:12:10.789442+00:00
-- url     : https://prove2.me/submissions/c1b4b9ce-5002-41cf-98b3-dba3d68a3298

import Definitions.Def_MinBuying_Triangular

open MeasureTheory Set MinBuying

private lemma payment_measurable {n : ℕ} (p : Prices n) : Measurable (payment p) := by
  have ha : Measurable (affordable p) := by
    apply measurable_finset_iff.mpr
    intro i
    apply measurableSet_setOfPred.mp
    simpa [affordable] using
      (measurableSet_le measurable_const (measurable_pi_apply i) :
        MeasurableSet {v : Valuations n | p i ≤ v i})
  have hf : Measurable (fun A : Finset (Fin n) => if h : A.Nonempty then A.inf' h p else 0) :=
    measurable_of_countable _
  exact hf.comp ha

private lemma payment_scale {n : ℕ} (p : Prices n) (v : Valuations n)
    (s : ℝ) (hs : 0 < s) :
    payment (fun i => s * p i) (fun i => s * v i) = s * payment p v := by
  have ha : affordable (fun i => s * p i) (fun i => s * v i) = affordable p v := by
    ext i
    simp [affordable, mul_le_mul_iff_right₀ hs]
  unfold payment
  simp only [ha]
  split_ifs with h
  · exact (Finset.apply_inf'_eq_inf'_comp h (fun x : ℝ => s * x)
      (fun x y => mul_min_of_nonneg x y hs.le)).symm
  · simp

private lemma revenue_scale {n : ℕ} (μ : JointLaw n) (p : Prices n)
    (s : ℝ) (hs : 0 < s) :
    Revenue (Measure.map (fun v : Valuations n => fun i => s * v i) μ)
      (fun i => s * p i) = s * Revenue μ p := by
  unfold Revenue
  rw [integral_map (show AEMeasurable (fun v : Valuations n => fun i => s * v i) μ from
    (show Measurable (fun v : Valuations n => fun i => s * v i) by fun_prop).aemeasurable)
    (payment_measurable _).aestronglyMeasurable]
  simp_rw [payment_scale p _ s hs]
  exact integral_const_mul s (payment p)

private lemma triangular_scale (a v s : ℝ) (hs : 0 < s) :
    triangularLaw (s * a) (s * v) = Measure.map (fun x : ℝ => s * x) (triangularLaw a v) := by
  unfold triangularLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  dsimp [Function.comp_def]
  rw [mul_min_of_nonneg _ _ hs.le]
  congr 1
  ring

private lemma triangular_finite (a v : ℝ) : IsFiniteMeasure (triangularLaw a v) := by
  have : IsFiniteMeasure unitIntervalLaw := by
    unfold unitIntervalLaw
    infer_instance
  unfold triangularLaw
  infer_instance

private lemma triangular_joint_scale {n : ℕ} (I J : TriangularInstance n)
    (s : ℝ) (hs : 0 < s) (ha : ∀ i, J.a i = s * I.a i) (hv : ∀ i, J.cap i = s * I.cap i) :
    triangularJoint J = Measure.map (fun v : Valuations n => fun i => s * v i) (triangularJoint I) := by
  haveI : ∀ i, IsFiniteMeasure (triangularLaw (I.a i) (I.cap i)) :=
    fun i => triangular_finite (I.a i) (I.cap i)
  change Measure.pi (fun i => triangularLaw (J.a i) (J.cap i)) =
    Measure.map (fun v : Valuations n => fun i => s * v i)
      (Measure.pi (fun i => triangularLaw (I.a i) (I.cap i)))
  rw [Measure.pi_map_pi (fun i => (show Measurable (fun x : ℝ => s * x) by fun_prop).aemeasurable)]
  congr 1
  funext i
  rw [ha, hv]
  exact triangular_scale _ _ _ hs

private lemma revenue_unscale {n : ℕ} (μ : JointLaw n) (p : Prices n)
    (s : ℝ) (hs : 0 < s) :
    Revenue (Measure.map (fun v : Valuations n => fun i => s * v i) μ) p =
      s * Revenue μ (fun i => p i / s) := by
  have heq : (fun i => s * (p i / s)) = p := by
    funext i
    field_simp
  simpa only [heq] using revenue_scale μ (fun i => p i / s) s hs

private lemma wellposed_scale {n : ℕ} (μ : JointLaw n) (hμ : WellPosed μ)
    (s : ℝ) (hs : 0 < s) :
    let ν := Measure.map (fun v : Valuations n => fun i => s * v i) μ
    WellPosed ν ∧ DPRevenue ν = s * DPRevenue μ ∧ UPRevenue ν = s * UPRevenue μ := by
  let ν := Measure.map (fun v : Valuations n => fun i => s * v i) μ
  change WellPosed ν ∧ DPRevenue ν = s * DPRevenue μ ∧ UPRevenue ν = s * UPRevenue μ
  have hDupper : ∀ r ∈ differentiatedValues ν, r ≤ s * DPRevenue μ := by
    rintro r ⟨p, hp, rfl⟩
    rw [revenue_unscale μ p s hs]
    apply mul_le_mul_of_nonneg_left _ hs.le
    exact le_csSup hμ.1 ⟨fun i => p i / s, fun i => div_nonneg (hp i) hs.le, rfl⟩
  have hUupper : ∀ r ∈ uniformValues ν, r ≤ s * UPRevenue μ := by
    rintro r ⟨p, hp, rfl⟩
    unfold uniformRevenue
    rw [revenue_unscale μ (fun _ => p) s hs]
    apply mul_le_mul_of_nonneg_left _ hs.le
    exact le_csSup hμ.2.1 ⟨p / s, div_nonneg hp hs.le, rfl⟩
  have hDbdd : BddAbove (differentiatedValues ν) := ⟨s * DPRevenue μ, hDupper⟩
  have hUbdd : BddAbove (uniformValues ν) := ⟨s * UPRevenue μ, hUupper⟩
  obtain ⟨p, hp, hpopt⟩ := hμ.2.2.1
  obtain ⟨q, hq, hqopt⟩ := hμ.2.2.2.1
  have hsp : FeasiblePrices (fun i => s * p i) := fun i => mul_nonneg hs.le (hp i)
  have hsq : 0 ≤ s * q := mul_nonneg hs.le hq
  have hsprev : Revenue ν (fun i => s * p i) = s * DPRevenue μ := by
    rw [revenue_scale μ p s hs, hpopt]
  have hsqrev : uniformRevenue ν (s * q) = s * UPRevenue μ := by
    change Revenue ν (fun _ => s * q) = s * UPRevenue μ
    rw [revenue_scale μ (fun _ => q) s hs]
    exact congrArg (s * ·) hqopt
  have hDne : (differentiatedValues ν).Nonempty :=
    ⟨Revenue ν (fun i => s * p i), ⟨_, hsp, rfl⟩⟩
  have hUne : (uniformValues ν).Nonempty := ⟨uniformRevenue ν (s * q), ⟨_, hsq, rfl⟩⟩
  have hD : DPRevenue ν = s * DPRevenue μ := by
    apply le_antisymm (csSup_le hDne hDupper)
    rw [← hsprev]
    exact le_csSup hDbdd ⟨_, hsp, rfl⟩
  have hU : UPRevenue ν = s * UPRevenue μ := by
    apply le_antisymm (csSup_le hUne hUupper)
    rw [← hsqrev]
    exact le_csSup hUbdd ⟨_, hsq, rfl⟩
  refine ⟨⟨hDbdd, hUbdd, ⟨_, hsp, hsprev.trans hD.symm⟩,
    ⟨_, hsq, hsqrev.trans hU.symm⟩, ?_⟩, hD, hU⟩
  rw [hU]
  exact mul_pos hs hμ.2.2.2.2

theorem solution (n : ℕ) (I : TriangularInstance n)
    (hI : WellPosed (triangularJoint I)) (s : ℝ) (hs : 0 < s) :
    ∃ J : TriangularInstance n,
      (∀ i, J.a i = s * I.a i) ∧
      (∀ i, J.cap i = s * I.cap i) ∧
      WellPosed (triangularJoint J) ∧
      DPRevenue (triangularJoint J) = s * DPRevenue (triangularJoint I) ∧
      UPRevenue (triangularJoint J) = s * UPRevenue (triangularJoint I) := by
  let J : TriangularInstance n := {
    a := fun i => s * I.a i
    cap := fun i => s * I.cap i
    a_pos := fun i => mul_pos hs (I.a_pos i)
    cap_pos := fun i => mul_pos hs (I.cap_pos i) }
  have hJ := triangular_joint_scale I J s hs (fun _ => rfl) (fun _ => rfl)
  have hw := wellposed_scale (triangularJoint I) hI s hs
  refine ⟨J, fun _ => rfl, fun _ => rfl, ?_⟩
  rw [hJ]
  exact hw

-- Prove2me | solution 1 for MartOT.Opt.optimizer_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T07:39:48.960005+00:00
-- url     : https://prove2.me/submissions/e8d4d62d-cc1d-4c45-b802-b7641dc9bdb4

import Mathlib
import Definitions.Def_MartOT_Var_Setting

set_option autoImplicit false

namespace MartOTExist

open MeasureTheory Filter Topology MartOT.Var
open scoped ENNReal NNReal BoundedContinuousFunction

/-! ### Fatou for lower semicontinuous integrands under weak convergence -/

lemma lintegral_le_liminf_of_lsc {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {f : Ω → ℝ} (hf : LowerSemicontinuous f) (f_nn : 0 ≤ f)
    {P : ProbabilityMeasure Ω} {Ps : ℕ → ProbabilityMeasure Ω} (h : Tendsto Ps atTop (𝓝 P)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(P : Measure Ω) ≤
      atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂(Ps i : Measure Ω)) := by
  have hmeas : Measurable f := hf.measurable
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall f_nn) hmeas.aemeasurable]
  calc ∫⁻ (t : ℝ) in Set.Ioi 0, (P : Measure Ω) {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (Ps i : Measure Ω) {a | t < f a}) :=
        lintegral_mono (fun t ↦
          ProbabilityMeasure.le_liminf_measure_open_of_tendsto h (hf.isOpen_preimage t))
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (Ps i : Measure Ω) {a | t < f a}) :=
        lintegral_liminf_le (fun n ↦ Antitone.measurable (fun s t hst ↦
            measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))

lemma lintegral_le_of_lsc_eventually {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {f : Ω → ℝ} (hf : LowerSemicontinuous f) (f_nn : 0 ≤ f)
    {P : ProbabilityMeasure Ω} {Ps : ℕ → ProbabilityMeasure Ω} (h : Tendsto Ps atTop (𝓝 P))
    {X : ℝ≥0∞} (hX : ∀ᶠ i in atTop, ∫⁻ x, ENNReal.ofReal (f x) ∂(Ps i : Measure Ω) ≤ X) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(P : Measure Ω) ≤ X :=
  (lintegral_le_liminf_of_lsc hf f_nn h).trans (liminf_le_of_frequently_le' hX.frequently)

/-! ### Marginal helpers -/

lemma lint_fst {μ : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.fst = μ) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g μ) : ∫⁻ p, g p.1 ∂Q = ∫⁻ x, g x ∂μ := by
  subst hQ; exact (lintegral_map' hg measurable_fst.aemeasurable).symm

lemma lint_snd {ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.snd = ν) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g ν) : ∫⁻ p, g p.2 ∂Q = ∫⁻ x, g x ∂ν := by
  subst hQ; exact (lintegral_map' hg measurable_snd.aemeasurable).symm

lemma aem_fst {μ : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.fst = μ) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g μ) : AEMeasurable (fun p : ℝ × ℝ => g p.1) Q := by
  subst hQ; exact hg.comp_aemeasurable measurable_fst.aemeasurable

lemma aem_snd {ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.snd = ν) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g ν) : AEMeasurable (fun p : ℝ × ℝ => g p.2) Q := by
  subst hQ; exact hg.comp_aemeasurable measurable_snd.aemeasurable

lemma int_fst {μ : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.fst = μ) {g : ℝ → ℝ}
    (hg : Integrable g μ) : Integrable (fun p : ℝ × ℝ => g p.1) Q := by
  subst hQ; exact hg.comp_measurable measurable_fst

lemma int_snd {ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.snd = ν) {g : ℝ → ℝ}
    (hg : Integrable g ν) : Integrable (fun p : ℝ × ℝ => g p.2) Q := by
  subst hQ; exact hg.comp_measurable measurable_snd

lemma integral_fst' {μ : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.fst = μ) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g μ) : ∫ p, g p.1 ∂Q = ∫ x, g x ∂μ := by
  subst hQ; exact (integral_map measurable_fst.aemeasurable hg).symm

lemma integral_snd' {ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : Q.map Prod.snd = ν) {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g ν) : ∫ p, g p.2 ∂Q = ∫ x, g x ∂ν := by
  subst hQ; exact (integral_map measurable_snd.aemeasurable hg).symm

lemma integrable_diff {μ ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : IsPlan μ ν Q)
    (hμ : InM μ) (hν : InM ν) : Integrable (fun p : ℝ × ℝ => p.2 - p.1) Q :=
  (int_snd hQ.2 hν.2).sub (int_fst hQ.1 hμ.2)

lemma integrable_diff' {μ ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : IsPlan μ ν Q)
    (hμ : InM μ) (hν : InM ν) : Integrable (fun p : ℝ × ℝ => p.1 - p.2) Q :=
  (int_fst hQ.1 hμ.2).sub (int_snd hQ.2 hν.2)

lemma isProb_of_map {μ : Measure ℝ} [IsProbabilityMeasure μ] {Q : Measure (ℝ × ℝ)}
    (hQ : Q.map Prod.fst = μ) : IsProbabilityMeasure Q := by
  constructor
  have h := congrArg (fun m : Measure ℝ => m Set.univ) hQ
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    measure_univ] at h
  exact h

lemma lint_ofReal_ne_top {m : Measure ℝ} {g : ℝ → ℝ} (hg : Integrable g m) :
    ∫⁻ x, ENNReal.ofReal (g x) ∂m ≠ ⊤ :=
  (lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (le_abs_self _))
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => abs_nonneg _)).mp
      hg.abs.2)).ne

/-! ### Tails and truncation -/

noncomputable def tailF (R u : ℝ) : ℝ := max (2 * |u| - R) 0

noncomputable def clampR (R z : ℝ) : ℝ := max (-R) (min R z)

lemma continuous_tailF (R : ℝ) : Continuous (tailF R) := by
  unfold tailF
  exact ((continuous_const.mul continuous_abs).sub continuous_const).max continuous_const

lemma continuous_clampR (R : ℝ) : Continuous (clampR R) := by
  unfold clampR
  exact continuous_const.max (continuous_const.min continuous_id)

lemma norm_clampR_le {R : ℝ} (hR : 0 ≤ R) (z : ℝ) : ‖clampR R z‖ ≤ R := by
  unfold clampR
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma abs_sub_clamp_le (R z : ℝ) (hR : 0 ≤ R) : |z - clampR R z| ≤ max (|z| - R) 0 := by
  unfold clampR
  rcases le_total z (-R) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h, abs_of_nonpos (show z - -R ≤ 0 by linarith),
      abs_of_nonpos (show z ≤ 0 by linarith)]
    exact le_max_of_le_left (by linarith)
  · rcases le_total z R with h' | h'
    · rw [min_eq_right h', max_eq_right h, sub_self, abs_zero]; exact le_max_right _ _
    · rw [min_eq_left h', max_eq_right (by linarith), abs_of_nonneg (show 0 ≤ z - R by linarith),
        abs_of_nonneg (show 0 ≤ z by linarith)]
      exact le_max_of_le_left (by linarith)

lemma pw_clamp (R x y : ℝ) (hR : 0 ≤ R) :
    |(y - x) - clampR R (y - x)| ≤ tailF R x + tailF R y := by
  refine (abs_sub_clamp_le R (y - x) hR).trans ?_
  unfold tailF
  have h1 : |y - x| ≤ |y| + |x| := abs_sub y x
  have a1 := le_max_left (2 * |x| - R) 0
  have a2 := le_max_right (2 * |x| - R) 0
  have b1 := le_max_left (2 * |y| - R) 0
  have b2 := le_max_right (2 * |y| - R) 0
  apply max_le _ (by linarith)
  rcases le_total |x| |y| with h | h <;> linarith

lemma integrable_tailF {m : Measure ℝ} (hm : Integrable (fun x : ℝ => x) m) {R : ℝ} (hR : 0 ≤ R) :
    Integrable (tailF R) m :=
  (hm.norm.const_mul 2).mono' (continuous_tailF R).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      unfold tailF
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
      exact max_le (by linarith) (by positivity))

lemma tendsto_tail {m : Measure ℝ} (hm : Integrable (fun x : ℝ => x) m) :
    Tendsto (fun n : ℕ => ∫ u, tailF n u ∂m) atTop (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _u, (0 : ℝ) ∂m := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun u => 2 * ‖u‖)
    (fun n => (continuous_tailF n).aestronglyMeasurable) (hm.norm.const_mul 2)
    (fun n => Eventually.of_forall fun u => ?_) (Eventually.of_forall fun u => ?_)
  · unfold tailF
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (by positivity)
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ⌈2 * |u|⌉₊] with n hn
    have h1 : 2 * |u| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    unfold tailF
    rw [max_eq_right (by linarith)]

lemma approx_bound {μ ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} [IsFiniteMeasure Q]
    (hQ : IsPlan μ ν Q) (hμ : InM μ) (hν : InM ν)
    {ρ : ℝ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ x, |ρ x| ≤ C) {R : ℝ} (hR0 : 0 ≤ R) :
    |∫ p, ρ p.1 * (p.2 - p.1) ∂Q - ∫ p, ρ p.1 * clampR R (p.2 - p.1) ∂Q| ≤
      C * (∫ u, tailF R u ∂μ + ∫ u, tailF R u ∂ν) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hI : Integrable (fun p : ℝ × ℝ => p.2 - p.1) Q := integrable_diff hQ hμ hν
  have hm1 : Measurable (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1)) :=
    (hρ.comp measurable_fst).mul (measurable_snd.sub measurable_fst)
  have hm2 : Measurable (fun p : ℝ × ℝ => ρ p.1 * clampR R (p.2 - p.1)) :=
    (hρ.comp measurable_fst).mul
      ((continuous_clampR R).measurable.comp (measurable_snd.sub measurable_fst))
  have i1 : Integrable (fun p : ℝ × ℝ => ρ p.1 * (p.2 - p.1)) Q :=
    (hI.norm.const_mul C).mono' hm1.aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hC _) (norm_nonneg _))
  have i2 : Integrable (fun p : ℝ × ℝ => ρ p.1 * clampR R (p.2 - p.1)) Q :=
    (integrable_const (C * R)).mono' hm2.aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [norm_mul]
      exact mul_le_mul (by rw [Real.norm_eq_abs]; exact hC _) (norm_clampR_le hR0 _)
        (norm_nonneg _) hC0)
  have it1 := integrable_tailF hμ.2 hR0
  have it2 := integrable_tailF hν.2 hR0
  have hg : Integrable (fun p : ℝ × ℝ => C * (tailF R p.1 + tailF R p.2)) Q :=
    ((int_fst hQ.1 it1).add (int_snd hQ.2 it2)).const_mul C
  rw [← integral_sub i1 i2, ← Real.norm_eq_abs]
  calc ‖∫ p, (ρ p.1 * (p.2 - p.1) - ρ p.1 * clampR R (p.2 - p.1)) ∂Q‖
      ≤ ∫ p, C * (tailF R p.1 + tailF R p.2) ∂Q :=
        norm_integral_le_of_norm_le hg (Eventually.of_forall fun p => by
          rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul (hC _) (pw_clamp R p.1 p.2 hR0) (abs_nonneg _) hC0)
    _ = C * (∫ u, tailF R u ∂μ + ∫ u, tailF R u ∂ν) := by
        rw [integral_const_mul, integral_add (int_fst hQ.1 it1) (int_snd hQ.2 it2),
          integral_fst' hQ.1 it1.1, integral_snd' hQ.2 it2.1]

/-! ### Positive / negative displacement measures -/

noncomputable def mPos (Q : Measure (ℝ × ℝ)) : Measure ℝ :=
  (Q.withDensity fun p => ((Real.toNNReal (p.2 - p.1) : ℝ≥0) : ℝ≥0∞)).map Prod.fst

noncomputable def mNeg (Q : Measure (ℝ × ℝ)) : Measure ℝ :=
  (Q.withDensity fun p => ((Real.toNNReal (p.1 - p.2) : ℝ≥0) : ℝ≥0∞)).map Prod.fst

lemma isFinite_mPos {Q : Measure (ℝ × ℝ)} (hI : Integrable (fun p : ℝ × ℝ => p.2 - p.1) Q) :
    IsFiniteMeasure (mPos Q) := by
  unfold mPos
  have : IsFiniteMeasure (Q.withDensity fun p => ((Real.toNNReal (p.2 - p.1) : ℝ≥0) : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hI.2
  infer_instance

lemma isFinite_mNeg {Q : Measure (ℝ × ℝ)} (hI : Integrable (fun p : ℝ × ℝ => p.1 - p.2) Q) :
    IsFiniteMeasure (mNeg Q) := by
  unfold mNeg
  have : IsFiniteMeasure (Q.withDensity fun p => ((Real.toNNReal (p.1 - p.2) : ℝ≥0) : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_ofReal hI.2
  infer_instance

lemma integral_mPos {Q : Measure (ℝ × ℝ)} {ρ : ℝ → ℝ} (hρ : Measurable ρ) :
    ∫ x, ρ x ∂(mPos Q) = ∫ p, ρ p.1 * max (p.2 - p.1) 0 ∂Q := by
  unfold mPos
  rw [integral_map measurable_fst.aemeasurable hρ.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (show Measurable (fun p : ℝ × ℝ => Real.toNNReal (p.2 - p.1)) from
      (measurable_snd.sub measurable_fst).real_toNNReal)]
  congr 1; ext p
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal', mul_comm]

lemma integral_mNeg {Q : Measure (ℝ × ℝ)} {ρ : ℝ → ℝ} (hρ : Measurable ρ) :
    ∫ x, ρ x ∂(mNeg Q) = ∫ p, ρ p.1 * max (p.1 - p.2) 0 ∂Q := by
  unfold mNeg
  rw [integral_map measurable_fst.aemeasurable hρ.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (show Measurable (fun p : ℝ × ℝ => Real.toNNReal (p.1 - p.2)) from
      (measurable_fst.sub measurable_snd).real_toNNReal)]
  congr 1; ext p
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal', mul_comm]

lemma split_integral {Q : Measure (ℝ × ℝ)}
    (hI : Integrable (fun p : ℝ × ℝ => p.2 - p.1) Q)
    {ρ : ℝ → ℝ} (hρ : Measurable ρ) {C : ℝ} (hC : ∀ x, |ρ x| ≤ C) :
    ∫ p, ρ p.1 * (p.2 - p.1) ∂Q = ∫ x, ρ x ∂(mPos Q) - ∫ x, ρ x ∂(mNeg Q) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have j1 : Integrable (fun p : ℝ × ℝ => ρ p.1 * max (p.2 - p.1) 0) Q :=
    (hI.norm.const_mul C).mono'
      ((hρ.comp measurable_fst).mul ((measurable_snd.sub measurable_fst).max
        measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [norm_mul]
        refine mul_le_mul (by rw [Real.norm_eq_abs]; exact hC _) ?_ (norm_nonneg _) hC0
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _))
  have j2 : Integrable (fun p : ℝ × ℝ => ρ p.1 * max (p.1 - p.2) 0) Q :=
    (hI.norm.const_mul C).mono'
      ((hρ.comp measurable_fst).mul ((measurable_fst.sub measurable_snd).max
        measurable_const)).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [norm_mul]
        refine mul_le_mul (by rw [Real.norm_eq_abs]; exact hC _) ?_ (norm_nonneg _) hC0
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by rw [abs_sub_comm]; exact le_abs_self _) (abs_nonneg _))
  rw [integral_mPos hρ, integral_mNeg hρ, ← integral_sub j1 j2]
  congr 1; ext p
  rw [← mul_sub]; congr 1
  rcases le_total p.1 p.2 with h | h
  · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h), sub_zero]
  · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]; ring

/-! ### The martingale property passes to weak limits -/

lemma martingale_limit {μ ν : Measure ℝ} (hμ : InM μ) (hν : InM ν)
    {P : ProbabilityMeasure (ℝ × ℝ)} {Ps : ℕ → ProbabilityMeasure (ℝ × ℝ)}
    (h : Tendsto Ps atTop (𝓝 P)) (hPs : ∀ k, IsMartingalePlan μ ν (Ps k))
    (hP : IsPlan μ ν P) : IsMartingalePlan μ ν P := by
  have hI := integrable_diff hP hμ hν
  have hI' := integrable_diff' hP hμ hν
  have step1 : ∀ ρ : ℝ →ᵇ ℝ, ∫ p, ρ p.1 * (p.2 - p.1) ∂(P : Measure (ℝ × ℝ)) = 0 := by
    intro ρ
    have hρm : Measurable ρ := ρ.continuous.measurable
    have hC : ∀ x, |ρ x| ≤ ‖ρ‖ := fun x => by rw [← Real.norm_eq_abs]; exact ρ.norm_coe_le_norm x
    have key : ∀ n : ℕ, |∫ p, ρ p.1 * (p.2 - p.1) ∂(P : Measure (ℝ × ℝ))| ≤
        2 * (‖ρ‖ * (∫ u, tailF n u ∂μ + ∫ u, tailF n u ∂ν)) := by
      intro n
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hb : ∀ r : ℝ × ℝ, ‖ρ r.1 * clampR n (r.2 - r.1)‖ ≤ ‖ρ‖ * n := fun r => by
        rw [norm_mul]
        exact mul_le_mul (ρ.norm_coe_le_norm _) (norm_clampR_le hn0 _) (norm_nonneg _)
          (norm_nonneg _)
      let F : (ℝ × ℝ) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
        ⟨fun p => ρ p.1 * clampR n (p.2 - p.1),
          (ρ.continuous.comp continuous_fst).mul
            ((continuous_clampR n).comp (continuous_snd.sub continuous_fst))⟩
        (2 * (‖ρ‖ * n)) (by
          intro p q
          rw [dist_eq_norm]
          refine (norm_sub_le _ _).trans ?_
          have h1 := hb p
          have h2 := hb q
          simp only [ContinuousMap.coe_mk]
          linarith)
      have hF : ∀ Q : Measure (ℝ × ℝ), ∫ p, F p ∂Q = ∫ p, ρ p.1 * clampR n (p.2 - p.1) ∂Q :=
        fun Q => rfl
      have hlim := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h F
      have hk : ∀ k, |∫ p, F p ∂(Ps k : Measure (ℝ × ℝ))| ≤
          ‖ρ‖ * (∫ u, tailF n u ∂μ + ∫ u, tailF n u ∂ν) := by
        intro k
        have h0 := (hPs k).2.2 ρ hρm ⟨‖ρ‖, hC⟩
        have := approx_bound (hPs k).1 hμ hν hρm hC hn0
        rw [h0, zero_sub, abs_neg] at this
        rw [hF]; exact this
      have hPF := le_of_tendsto' hlim.abs hk
      rw [hF] at hPF
      have hA := approx_bound hP hμ hν hρm hC hn0
      have htri := abs_sub_le (∫ p, ρ p.1 * (p.2 - p.1) ∂(P : Measure (ℝ × ℝ)))
        (∫ p, ρ p.1 * clampR n (p.2 - p.1) ∂(P : Measure (ℝ × ℝ))) 0
      simp only [sub_zero] at htri
      linarith
    have hT : Tendsto (fun n : ℕ => 2 * (‖ρ‖ * (∫ u, tailF n u ∂μ + ∫ u, tailF n u ∂ν)))
        atTop (𝓝 0) := by
      have := (((tendsto_tail hμ.2).add (tendsto_tail hν.2)).const_mul ‖ρ‖).const_mul 2
      simpa using this
    exact abs_nonpos_iff.mp (ge_of_tendsto' hT key)
  haveI := isFinite_mPos hI
  haveI := isFinite_mNeg hI'
  have step2 : mPos (P : Measure (ℝ × ℝ)) = mNeg P := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have h1 := step1 f
    have hC : ∀ x, |f x| ≤ ‖f‖ := fun x => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
    rw [split_integral hI f.continuous.measurable hC] at h1
    linarith
  refine ⟨hP, hI, fun ρ hρ hbd => ?_⟩
  obtain ⟨C, hC⟩ := hbd
  rw [split_integral hI hρ hC, step2, sub_self]

/-! ### Plans: tightness and closedness of the marginal constraint -/

lemma tight_plans {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (S : Set (ProbabilityMeasure (ℝ × ℝ))) (hS : ∀ P ∈ S, IsPlan μ ν P) :
    IsTightMeasureSet {((P : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) | P ∈ S} := by
  apply IsTightMeasureSet.prodMk
  · apply (isTightMeasureSet_singleton (μ := μ)).subset
    rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    exact (hS P hP).1
  · apply (isTightMeasureSet_singleton (μ := ν)).subset
    rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    exact (hS P hP).2

lemma plan_limit {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {P : ProbabilityMeasure (ℝ × ℝ)} {Ps : ℕ → ProbabilityMeasure (ℝ × ℝ)}
    (h : Tendsto Ps atTop (𝓝 P)) (hPs : ∀ k, IsPlan μ ν (Ps k)) : IsPlan μ ν P := by
  constructor
  · have h1 : Tendsto (fun k => (Ps k).map continuous_fst.measurable.aemeasurable) atTop
        (𝓝 (P.map continuous_fst.measurable.aemeasurable)) :=
      ((ProbabilityMeasure.continuous_map continuous_fst).tendsto P).comp h
    let μP : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩
    have hc' : ∀ k, (Ps k).map continuous_fst.measurable.aemeasurable = μP :=
      fun k => Subtype.ext (hPs k).1
    have h2 : Tendsto (fun _ : ℕ => μP) atTop (𝓝 (P.map continuous_fst.measurable.aemeasurable)) :=
      h1.congr hc'
    have h3 : P.map continuous_fst.measurable.aemeasurable = μP := tendsto_nhds_unique h2 tendsto_const_nhds
    exact congrArg ProbabilityMeasure.toMeasure h3
  · have h1 : Tendsto (fun k => (Ps k).map continuous_snd.measurable.aemeasurable) atTop
        (𝓝 (P.map continuous_snd.measurable.aemeasurable)) :=
      ((ProbabilityMeasure.continuous_map continuous_snd).tendsto P).comp h
    let νP : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
    have hc' : ∀ k, (Ps k).map continuous_snd.measurable.aemeasurable = νP :=
      fun k => Subtype.ext (hPs k).2
    have h2 : Tendsto (fun _ : ℕ => νP) atTop (𝓝 (P.map continuous_snd.measurable.aemeasurable)) :=
      h1.congr hc'
    have h3 : P.map continuous_snd.measurable.aemeasurable = νP := tendsto_nhds_unique h2 tendsto_const_nhds
    exact congrArg ProbabilityMeasure.toMeasure h3

/-! ### The cost functional -/

noncomputable def Acost (c : ℝ → ℝ → ℝ) (Q : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂Q

noncomputable def Bcost (c : ℝ → ℝ → ℝ) (Q : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (-c p.1 p.2) ∂Q

noncomputable def Bn (c : ℝ → ℝ → ℝ) (N : ℝ) (Q : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p, min (ENNReal.ofReal (-c p.1 p.2)) (ENNReal.ofReal N) ∂Q

noncomputable def Gn (c : ℝ → ℝ → ℝ) (N : ℝ) (Q : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (max (c p.1 p.2) (-N) + N) ∂Q

noncomputable def Vobj (c : ℝ → ℝ → ℝ) (W : ℝ≥0∞) (Q : Measure (ℝ × ℝ)) : ℝ≥0∞ :=
  Acost c Q + (W - Bcost c Q)

noncomputable def Wof (a b : ℝ → ℝ) (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-a x) ∂μ + ∫⁻ y, ENNReal.ofReal (-b y) ∂ν

noncomputable def δof (a b : ℝ → ℝ) (μ ν : Measure ℝ) (N : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (-a x - N / 2) ∂μ + ∫⁻ y, ENNReal.ofReal (-b y - N / 2) ∂ν

lemma cost_eq (c : ℝ → ℝ → ℝ) (Q : Measure (ℝ × ℝ)) :
    cost c Q = (Acost c Q : EReal) - (Bcost c Q : EReal) := by
  simp only [cost, integralE, ModelRiskOT.Duality.extIntegral, Acost, Bcost, ← EReal.coe_neg,
    EReal.real_coe_toENNReal]

lemma pw1 (x N : ℝ) (hN : 0 ≤ N) :
    ENNReal.ofReal (max x (-N) + N) + min (ENNReal.ofReal (-x)) (ENNReal.ofReal N) =
      ENNReal.ofReal x + ENNReal.ofReal N := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left (by linarith), ENNReal.ofReal_of_nonpos (show -x ≤ 0 by linarith),
      min_eq_left (by simp), add_zero, ENNReal.ofReal_add h hN]
  · rcases le_total (-N) x with h' | h'
    · rw [max_eq_left h', ENNReal.ofReal_of_nonpos h, zero_add,
        min_eq_left (ENNReal.ofReal_le_ofReal (by linarith)),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
    · rw [max_eq_right h', min_eq_right (ENNReal.ofReal_le_ofReal (by linarith)),
        ENNReal.ofReal_of_nonpos h]
      simp

lemma pw3 (x N : ℝ) (hN : 0 ≤ N) :
    ENNReal.ofReal (-x) ≤ min (ENNReal.ofReal (-x)) (ENNReal.ofReal N) + ENNReal.ofReal (-x - N) := by
  rcases le_total (-x) N with h | h
  · rw [min_eq_left (ENNReal.ofReal_le_ofReal h)]; exact le_self_add
  · rw [min_eq_right (ENNReal.ofReal_le_ofReal h), ← ENNReal.ofReal_add hN (by linarith)]
    apply le_of_eq; congr 1; ring

lemma G_add_Bn {c : ℝ → ℝ → ℝ} (hcm : Measurable fun p : ℝ × ℝ => c p.1 p.2) {N : ℝ}
    (hN : 0 ≤ N) (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] :
    Gn c N Q + Bn c N Q = Acost c Q + ENNReal.ofReal N := by
  unfold Gn Bn Acost
  rw [← lintegral_add_left ((hcm.max measurable_const).add_const _).ennreal_ofReal]
  rw [show (fun p : ℝ × ℝ => ENNReal.ofReal (max (c p.1 p.2) (-N) + N) +
      min (ENNReal.ofReal (-c p.1 p.2)) (ENNReal.ofReal N)) =
      fun p => ENNReal.ofReal (c p.1 p.2) + ENNReal.ofReal N from funext fun p => pw1 _ N hN]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

lemma Bn_le_B (c : ℝ → ℝ → ℝ) (N : ℝ) (Q : Measure (ℝ × ℝ)) : Bn c N Q ≤ Bcost c Q :=
  lintegral_mono fun _ => min_le_left _ _

lemma B_le_W {μ ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : IsPlan μ ν Q)
    {c : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} (ha : Integrable a μ) (hb : Integrable b ν)
    (hab : ∀ x y, a x + b y ≤ c x y) : Bcost c Q ≤ Wof a b μ ν := by
  unfold Bcost Wof
  have hA : AEMeasurable (fun x => ENNReal.ofReal (-a x)) μ := ha.aemeasurable.neg.ennreal_ofReal
  have hB : AEMeasurable (fun y => ENNReal.ofReal (-b y)) ν := hb.aemeasurable.neg.ennreal_ofReal
  calc ∫⁻ p, ENNReal.ofReal (-c p.1 p.2) ∂Q
      ≤ ∫⁻ p, (ENNReal.ofReal (-a p.1) + ENNReal.ofReal (-b p.2)) ∂Q :=
        lintegral_mono fun p => (ENNReal.ofReal_le_ofReal (by linarith [hab p.1 p.2])).trans
          ENNReal.ofReal_add_le
    _ = ∫⁻ p, ENNReal.ofReal (-a p.1) ∂Q + ∫⁻ p, ENNReal.ofReal (-b p.2) ∂Q :=
        lintegral_add_left' (aem_fst hQ.1 hA) _
    _ = _ := by rw [lint_fst hQ.1 hA, lint_snd hQ.2 hB]

lemma B_le_Bn_add {μ ν : Measure ℝ} {Q : Measure (ℝ × ℝ)} (hQ : IsPlan μ ν Q)
    {c : ℝ → ℝ → ℝ} (hcm : Measurable fun p : ℝ × ℝ => c p.1 p.2)
    {a b : ℝ → ℝ} (ha : Integrable a μ) (hb : Integrable b ν)
    (hab : ∀ x y, a x + b y ≤ c x y) {N : ℝ} (hN : 0 ≤ N) :
    Bcost c Q ≤ Bn c N Q + δof a b μ ν N := by
  unfold Bcost Bn δof
  have hA : AEMeasurable (fun x => ENNReal.ofReal (-a x - N / 2)) μ :=
    (ha.aemeasurable.neg.sub_const _).ennreal_ofReal
  have hB : AEMeasurable (fun y => ENNReal.ofReal (-b y - N / 2)) ν :=
    (hb.aemeasurable.neg.sub_const _).ennreal_ofReal
  calc ∫⁻ p, ENNReal.ofReal (-c p.1 p.2) ∂Q
      ≤ ∫⁻ p, (min (ENNReal.ofReal (-c p.1 p.2)) (ENNReal.ofReal N) +
          (ENNReal.ofReal (-a p.1 - N / 2) + ENNReal.ofReal (-b p.2 - N / 2))) ∂Q :=
        lintegral_mono fun p => by
          refine (pw3 _ N hN).trans ?_
          gcongr
          exact (ENNReal.ofReal_le_ofReal (by linarith [hab p.1 p.2])).trans ENNReal.ofReal_add_le
    _ = ∫⁻ p, min (ENNReal.ofReal (-c p.1 p.2)) (ENNReal.ofReal N) ∂Q +
          (∫⁻ p, ENNReal.ofReal (-a p.1 - N / 2) ∂Q + ∫⁻ p, ENNReal.ofReal (-b p.2 - N / 2) ∂Q) := by
        have hmin : Measurable (fun p : ℝ × ℝ => min (ENNReal.ofReal (-c p.1 p.2)) (ENNReal.ofReal N)) :=
          hcm.neg.ennreal_ofReal.min measurable_const
        rw [lintegral_add_left' hmin.aemeasurable,
          lintegral_add_left' (aem_fst hQ.1 hA)]
    _ = _ := by rw [lint_fst hQ.1 hA, lint_snd hQ.2 hB]

lemma V_add_B {c : ℝ → ℝ → ℝ} {W : ℝ≥0∞} {Q : Measure (ℝ × ℝ)} (hBW : Bcost c Q ≤ W) :
    Vobj c W Q + Bcost c Q = Acost c Q + W := by
  unfold Vobj; rw [add_assoc, tsub_add_cancel_of_le hBW]

lemma tendsto_shift {m : Measure ℝ} {g : ℝ → ℝ} (hg : Integrable g m) :
    Tendsto (fun n : ℕ => ∫⁻ x, ENNReal.ofReal (-g x - (n : ℝ) / 2) ∂m) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence' (μ := m)
    (F := fun (n : ℕ) x => ENNReal.ofReal (-g x - (n : ℝ) / 2)) (f := fun _ => 0)
    (fun x => ENNReal.ofReal (-g x))
    (fun n => (hg.aemeasurable.neg.sub_const _).ennreal_ofReal)
    (fun n => Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (by
      have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
      linarith))
    (lint_ofReal_ne_top (g := fun x => -g x) hg.neg)
    (Eventually.of_forall fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈2 * |g x|⌉₊] with n hn
      have h1 : 2 * |g x| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      exact (ENNReal.ofReal_of_nonpos (by linarith [neg_le_abs (g x)])).symm)
  simpa using h

lemma compare {A1 B1 A2 B2 W : ℝ≥0∞} (hB1 : B1 ≤ W) (hB2 : B2 ≤ W) (hW : W ≠ ⊤)
    (h : A1 + (W - B1) ≤ A2 + (W - B2)) : (A1 : EReal) - B1 ≤ (A2 : EReal) - B2 := by
  have hB1t : B1 ≠ ⊤ := ne_top_of_le_ne_top hW hB1
  have hB2t : B2 ≠ ⊤ := ne_top_of_le_ne_top hW hB2
  by_cases hA2 : A2 = ⊤
  · rw [hA2, EReal.coe_ennreal_top, EReal.top_sub (by simpa using hB2t)]
    exact le_top
  · have hfin : A2 + (W - B2) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hA2, ENNReal.sub_ne_top hW⟩
    have hA1 : A1 ≠ ⊤ := by
      intro h1
      rw [h1, top_add] at h
      exact hfin (top_le_iff.mp h)
    rw [← EReal.coe_ennreal_toReal hA1, ← EReal.coe_ennreal_toReal hB1t,
      ← EReal.coe_ennreal_toReal hA2, ← EReal.coe_ennreal_toReal hB2t, ← EReal.coe_sub,
      ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_add hA1 (ENNReal.sub_ne_top hW), ENNReal.toReal_add hA2
      (ENNReal.sub_ne_top hW), ENNReal.toReal_sub_of_le hB1 hW,
      ENNReal.toReal_sub_of_le hB2 hW] at this
    linarith

/-- The lower semicontinuity step along a weakly convergent sequence of plans. -/
lemma core {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ → ℝ → ℝ} (hc : LowerSemicontinuous (Function.uncurry c))
    {a b : ℝ → ℝ} (ha : Integrable a μ) (hb : Integrable b ν) (hab : ∀ x y, a x + b y ≤ c x y)
    {P : ProbabilityMeasure (ℝ × ℝ)} {Ps : ℕ → ProbabilityMeasure (ℝ × ℝ)}
    (h : Tendsto Ps atTop (𝓝 P)) (hPs : ∀ k, IsPlan μ ν (Ps k)) (hP : IsPlan μ ν P)
    (n : ℕ) {X : ℝ≥0∞} (hX : ∀ᶠ k in atTop, Vobj c (Wof a b μ ν) (Ps k) ≤ X) :
    Vobj c (Wof a b μ ν) P ≤ X + δof a b μ ν n := by
  have hcm : Measurable fun p : ℝ × ℝ => c p.1 p.2 := hc.measurable
  set N : ℝ := (n : ℝ) with hNdef
  have hN : 0 ≤ N := Nat.cast_nonneg n
  set W := Wof a b μ ν with hWdef
  set δ := δof a b μ ν N with hδdef
  have hW : W ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨lint_ofReal_ne_top (g := fun x => -a x) ha.neg, lint_ofReal_ne_top (g := fun x => -b x) hb.neg⟩
  have hk : ∀ᶠ k in atTop, Gn c N (Ps k) + W ≤ X + δ + ENNReal.ofReal N := hX.mono fun k hk => by
    have e1 := G_add_Bn hcm hN (Ps k : Measure (ℝ × ℝ))
    have e2 := V_add_B (c := c) (B_le_W (hPs k) ha hb hab)
    have e3 := B_le_Bn_add (hPs k) hcm ha hb hab hN
    have hBn : Bn c N (Ps k) ≠ ⊤ :=
      ne_top_of_le_ne_top hW ((Bn_le_B c N _).trans (B_le_W (hPs k) ha hb hab))
    have key : Gn c N (Ps k) + W + Bn c N (Ps k) ≤ X + δ + ENNReal.ofReal N + Bn c N (Ps k) := by
      calc Gn c N (Ps k) + W + Bn c N (Ps k)
          = (Gn c N (Ps k) + Bn c N (Ps k)) + W := by ring
        _ = (Acost c (Ps k) + ENNReal.ofReal N) + W := by rw [e1]
        _ = (Acost c (Ps k) + W) + ENNReal.ofReal N := by ring
        _ = (Vobj c W (Ps k) + Bcost c (Ps k)) + ENNReal.ofReal N := by rw [e2]
        _ ≤ (X + (Bn c N (Ps k) + δ)) + ENNReal.ofReal N := by gcongr
        _ = X + δ + ENNReal.ofReal N + Bn c N (Ps k) := by ring
    exact (ENNReal.add_le_add_iff_right hBn).mp key
  have hGP : Gn c N P ≤ X + δ + ENNReal.ofReal N - W := by
    unfold Gn
    refine lintegral_le_of_lsc_eventually (f := fun p : ℝ × ℝ => max (c p.1 p.2) (-N) + N)
      ((hc.sup lowerSemicontinuous_const).add lowerSemicontinuous_const)
      (fun p => by have := le_max_right (c p.1 p.2) (-N); simp only [Pi.zero_apply]; linarith)
      h ?_
    exact hk.mono fun k hk => ENNReal.le_sub_of_add_le_right hW hk
  have hWle : W ≤ X + δ + ENNReal.ofReal N := by
    obtain ⟨k, hk⟩ := hk.exists
    exact le_trans le_add_self hk
  have hGW : Gn c N P + W ≤ X + δ + ENNReal.ofReal N := by
    calc Gn c N P + W ≤ (X + δ + ENNReal.ofReal N - W) + W := by gcongr
      _ = _ := tsub_add_cancel_of_le hWle
  have e1 := G_add_Bn hcm hN (P : Measure (ℝ × ℝ))
  have e2 := V_add_B (c := c) (B_le_W hP ha hb hab)
  have hBnB := Bn_le_B c N (P : Measure (ℝ × ℝ))
  have hB : Bcost c P ≠ ⊤ := ne_top_of_le_ne_top hW (B_le_W hP ha hb hab)
  have key : Vobj c W P + ENNReal.ofReal N + Bcost c P ≤ X + δ + ENNReal.ofReal N + Bcost c P := by
    calc Vobj c W P + ENNReal.ofReal N + Bcost c P
        = (Vobj c W P + Bcost c P) + ENNReal.ofReal N := by ring
      _ = (Acost c P + W) + ENNReal.ofReal N := by rw [e2]
      _ = (Acost c P + ENNReal.ofReal N) + W := by ring
      _ = (Gn c N P + Bn c N P) + W := by rw [e1]
      _ ≤ (Gn c N P + Bcost c P) + W := by gcongr
      _ = (Gn c N P + W) + Bcost c P := by ring
      _ ≤ (X + δ + ENNReal.ofReal N) + Bcost c P := by gcongr
  have key2 := (ENNReal.add_le_add_iff_right hB).mp key
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp key2

theorem main (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (c : ℝ → ℝ → ℝ) (hc : LowerSemicontinuous (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hne : ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsOptimal c μ ν π := by
  classical
  obtain ⟨a, b, ha, hb, hab⟩ := hint
  set W := Wof a b μ ν with hWdef
  have hW : W ≠ ⊤ := ENNReal.add_ne_top.mpr
    ⟨lint_ofReal_ne_top (g := fun x => -a x) ha.neg, lint_ofReal_ne_top (g := fun x => -b x) hb.neg⟩
  let V : Measure (ℝ × ℝ) → ENNReal := Vobj c W
  let Sm : Set (Measure (ℝ × ℝ)) := {π | MartOT.Var.IsMartingalePlan μ ν π}
  obtain ⟨π0, hπ0⟩ := hne
  obtain ⟨u, -, hu, hu_mem⟩ :=
    exists_seq_tendsto_sInf (S := V '' Sm) ⟨V π0, π0, hπ0, rfl⟩ (OrderBot.bddBelow _)
  choose π hπS hπV using hu_mem
  have hprob : ∀ k, IsProbabilityMeasure (π k) := fun k => isProb_of_map (hπS k).1.1
  let Ps : ℕ → ProbabilityMeasure (ℝ × ℝ) := fun k => ⟨π k, hprob k⟩
  let T : Set (ProbabilityMeasure (ℝ × ℝ)) := {P | MartOT.Var.IsPlan μ ν P}
  have hT : IsCompact (closure T) :=
    isCompact_closure_of_isTightMeasureSet (tight_plans T fun P hP => hP)
  obtain ⟨P, -, φ, hφ, hlim⟩ :=
    hT.isSeqCompact (fun k => subset_closure (show Ps k ∈ T from (hπS k).1))
  have hPplan : MartOT.Var.IsPlan μ ν P := plan_limit hlim (fun k => (hπS (φ k)).1)
  have hPm : MartOT.Var.IsMartingalePlan μ ν P :=
    martingale_limit hμ hν hlim (fun k => hπS (φ k)) hPplan
  set m := sInf (V '' Sm) with hmdef
  have hlimV : Tendsto (fun k => V (Ps (φ k))) atTop (𝓝 m) :=
    (hu.comp hφ.tendsto_atTop).congr fun k => (hπV (φ k)).symm
  have hVP : V P ≤ m := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hm => ?_
    have hX : ∀ᶠ k in atTop, V ((Ps ∘ φ) k) ≤ m + ε :=
      (hlimV.eventually (Iio_mem_nhds (ENNReal.lt_add_right hm.ne
        (ENNReal.coe_ne_zero.mpr hε.ne')))).mono fun k hk => le_of_lt hk
    have hn : ∀ n : ℕ, V P ≤ (m + ε) + δof a b μ ν n := fun n =>
      core hc ha hb hab hlim (fun k => (hπS (φ k)).1) hPplan n hX
    have hδ : Tendsto (fun n : ℕ => (m + ε) + δof a b μ ν n) atTop (𝓝 ((m + ε) + 0)) := by
      refine tendsto_const_nhds.add ?_
      have := (tendsto_shift ha).add (tendsto_shift hb)
      simpa [δof] using this
    simpa using ge_of_tendsto' hδ hn
  refine ⟨P, hPm, fun π' h' => ?_⟩
  have hle : V P ≤ V π' := hVP.trans (csInf_le (OrderBot.bddBelow _) ⟨π', h', rfl⟩)
  rw [cost_eq, cost_eq]
  exact compare (B_le_W hPplan ha hb hab) (B_le_W h'.1 ha hb hab) hW hle

end MartOTExist

open MeasureTheory in
theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (c : ℝ → ℝ → ℝ) (hc : LowerSemicontinuous (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (hne : ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsOptimal c μ ν π := by
  exact MartOTExist.main μ ν hμ hν c hc hint hne

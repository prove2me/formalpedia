-- Prove2me | solution 1 for KarimiPL.SGD.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T06:10:36.019343+00:00
-- url     : https://prove2.me/submissions/e00f9412-188c-4aef-b56e-bd63e7219543

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_SGD_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace KPL4SGD

theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫_ℝ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫_ℝ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫_ℝ - ⟪G x, w⟫_ℝ
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫_ℝ) ⟪G x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫_ℝ
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫_ℝ - ⟪G x, w⟫_ℝ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫_ℝ - ⟪G x, w⟫_ℝ = ⟪G (x + c • w) - G x, w⟫_ℝ := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

theorem ofReal_lin_le (c a b : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (c * a + b) ≤ ENNReal.ofReal c * ENNReal.ofReal a + ENNReal.ofReal b := by
  refine ENNReal.ofReal_add_le.trans ?_
  gcongr
  rcases le_total 0 c with hc | hc
  · rw [ENNReal.ofReal_mul hc]
  · have : c * a ≤ 0 := by nlinarith
    rw [ENNReal.ofReal_of_nonpos this]
    positivity

/-- One SG step from a fixed point `x`, averaged over the index. -/
theorem one_step_point {d : ℕ} {I : Type*} [MeasurableSpace I]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (fs : ℝ) (hfs : ∀ y, fs ≤ f y)
    (μ : ℝ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ fs)
    (hunb : KarimiPL.SGD.IsUnbiasedGradient F ν f)
    (hmeas : Measurable (fun p : I × EuclideanSpace ℝ (Fin d) => gradient (F p.1) p.2))
    (C α : ℝ) (hα : 0 ≤ α) (x : EuclideanSpace ℝ (Fin d))
    (hC : ∫⁻ i, ‖gradient (F i) x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (C ^ 2)) :
    ∫⁻ i, ENNReal.ofReal (f (x - α • gradient (F i) x) - fs) ∂ν
      ≤ ENNReal.ofReal (1 - 2 * μ * α) * ENNReal.ofReal (f x - fs)
        + ENNReal.ofReal (L * α ^ 2 * C ^ 2 / 2) := by
  have hgm : Measurable (fun i => gradient (F i) x) :=
    hmeas.comp (measurable_id.prodMk measurable_const)
  have hgi : Integrable (fun i => gradient (F i) x) ν := (hunb x).1
  have hsqm : AEStronglyMeasurable (fun i => ‖gradient (F i) x‖ ^ 2) ν :=
    (hgm.norm.pow_const 2).aestronglyMeasurable
  have hsq_lint : ∫⁻ i, ‖gradient (F i) x‖ₑ ^ 2 ∂ν < ∞ :=
    lt_of_le_of_lt hC ENNReal.ofReal_lt_top
  have hsqi : Integrable (fun i => ‖gradient (F i) x‖ ^ 2) ν := by
    refine ⟨hsqm, ?_⟩
    show ∫⁻ i, ‖‖gradient (F i) x‖ ^ 2‖ₑ ∂ν < ∞
    simpa [enorm_pow, enorm_norm] using hsq_lint
  have hdesc : ∀ i, f (x - α • gradient (F i) x) - fs ≤ (f x - fs)
      - α * ⟪gradient f x, gradient (F i) x⟫_ℝ + L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2 := by
    intro i
    have h := descent (F := f) (G := gradient f) (L := L) (fun z => (hdiff z).hasGradientAt)
      hLip x (x - α • gradient (F i) x)
    have e1 : x - α • gradient (F i) x - x = -(α • gradient (F i) x) := by abel
    rw [e1, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hα] at h
    have e2 : (α * ‖gradient (F i) x‖) ^ 2 = α ^ 2 * ‖gradient (F i) x‖ ^ 2 := by ring
    rw [e2] at h
    linarith
  have hui : Integrable (fun i => (f x - fs) - α * ⟪gradient f x, gradient (F i) x⟫_ℝ
      + L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2) ν :=
    ((integrable_const _).sub ((hgi.const_inner (gradient f x)).const_mul α)).add
      (hsqi.const_mul (L / 2 * α ^ 2))
  have hu_nonneg : ∀ i, 0 ≤ (f x - fs) - α * ⟪gradient f x, gradient (F i) x⟫_ℝ
      + L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2 :=
    fun i => le_trans (sub_nonneg.2 (hfs _)) (hdesc i)
  have hS : ∫ i, ‖gradient (F i) x‖ ^ 2 ∂ν ≤ C ^ 2 := by
    have : ∫ i, ‖gradient (F i) x‖ ^ 2 ∂ν = (∫⁻ i, ‖gradient (F i) x‖ₑ ^ 2 ∂ν).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun i => by positivity)) hsqm]
      congr 1
      apply lintegral_congr
      intro i
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [this]
    exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg C) hC
  have hint : ∫ i, ((f x - fs) - α * ⟪gradient f x, gradient (F i) x⟫_ℝ
      + L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2) ∂ν
      = (f x - fs) - α * ‖gradient f x‖ ^ 2 + L / 2 * α ^ 2 * ∫ i, ‖gradient (F i) x‖ ^ 2 ∂ν := by
    have hA1 : Integrable (fun i => α * ⟪gradient f x, gradient (F i) x⟫_ℝ) ν :=
      (hgi.const_inner (gradient f x)).const_mul α
    have hA : Integrable (fun i => (f x - fs) - α * ⟪gradient f x, gradient (F i) x⟫_ℝ) ν :=
      (integrable_const _).sub hA1
    have hB : Integrable (fun i => L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2) ν :=
      hsqi.const_mul (L / 2 * α ^ 2)
    rw [integral_add hA hB, integral_sub (integrable_const _) hA1,
      integral_const, integral_const_mul, integral_const_mul, integral_inner hgi, (hunb x).2,
      real_inner_self_eq_norm_sq]
    simp
  have hP := hPL x
  have hreal : ∫ i, ((f x - fs) - α * ⟪gradient f x, gradient (F i) x⟫_ℝ
      + L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2) ∂ν
      ≤ (1 - 2 * μ * α) * (f x - fs) + L * α ^ 2 * C ^ 2 / 2 := by
    rw [hint]
    have h1 : α * (2 * μ * (f x - fs)) ≤ α * ‖gradient f x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hP hα
    have h2 : L / 2 * α ^ 2 * ∫ i, ‖gradient (F i) x‖ ^ 2 ∂ν ≤ L / 2 * α ^ 2 * C ^ 2 :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    nlinarith
  calc ∫⁻ i, ENNReal.ofReal (f (x - α • gradient (F i) x) - fs) ∂ν
      ≤ ∫⁻ i, ENNReal.ofReal ((f x - fs) - α * ⟪gradient f x, gradient (F i) x⟫_ℝ
          + L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2) ∂ν :=
        lintegral_mono (fun i => ENNReal.ofReal_le_ofReal (hdesc i))
    _ = ENNReal.ofReal (∫ i, ((f x - fs) - α * ⟪gradient f x, gradient (F i) x⟫_ℝ
          + L / 2 * α ^ 2 * ‖gradient (F i) x‖ ^ 2) ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hui (ae_of_all _ hu_nonneg)).symm
    _ ≤ ENNReal.ofReal ((1 - 2 * μ * α) * (f x - fs) + L * α ^ 2 * C ^ 2 / 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ ≤ _ := ofReal_lin_le _ _ _ (sub_nonneg.2 (hfs x))

/-- The `k`-th iterate is measurable with respect to the first `k` coordinates. -/
theorem run_meas {d : ℕ} {I : Type*} [mI : MeasurableSpace I]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ)
    (hmeas : Measurable (fun p : I × EuclideanSpace ℝ (Fin d) => gradient (F p.1) p.2))
    (α : ℕ → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    Measurable[⨆ j ∈ Set.Iio k, MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI]
      (fun ω => KarimiPL.SGD.sgRun F α x0 ω k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hle : (⨆ j ∈ Set.Iio k, MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI)
        ≤ ⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI :=
      biSup_mono (fun j (hj : j < k) => (lt_trans hj (Nat.lt_succ_self k) : j < k + 1))
    have h1 : Measurable[⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI]
        (fun ω => KarimiPL.SGD.sgRun F α x0 ω k) := ih.mono hle le_rfl
    have h2 : Measurable[⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI]
        (fun ω : ℕ → I => ω k) := by
      have : MeasurableSpace.comap (fun ω : ℕ → I => ω k) mI
          ≤ ⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI :=
        le_iSup₂ (f := fun j (_ : j ∈ Set.Iio (k + 1)) =>
          MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI) k (Nat.lt_succ_self k)
      exact (comap_measurable _).mono this le_rfl
    have h3 : Measurable[⨆ j ∈ Set.Iio (k + 1), MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI]
        (fun ω => gradient (F (ω k)) (KarimiPL.SGD.sgRun F α x0 ω k)) :=
      hmeas.comp (h2.prodMk h1)
    exact h1.sub (h3.const_smul (α k))

/-- Independence of the next index from the current iterate turns the expected gap at
step `k+1` into an iterated integral. -/
theorem step_lintegral {d : ℕ} {I : Type*} [mI : MeasurableSpace I]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hfc : Continuous f) (fs : ℝ)
    (hmeas : Measurable (fun p : I × EuclideanSpace ℝ (Fin d) => gradient (F p.1) p.2))
    (α : ℕ → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    KarimiPL.SGD.expectedGap F ν α x0 f fs (k + 1)
      = ∫⁻ ω, (∫⁻ i, ENNReal.ofReal (f (KarimiPL.SGD.sgRun F α x0 ω k
          - α k • gradient (F i) (KarimiPL.SGD.sgRun F α x0 ω k)) - fs) ∂ν)
          ∂(KarimiPL.SGD.pathLaw ν) := by
  have hPdef : KarimiPL.SGD.pathLaw ν = Measure.infinitePi (fun _ : ℕ => ν) := rfl
  haveI : IsProbabilityMeasure (KarimiPL.SGD.pathLaw ν) := by rw [hPdef]; infer_instance
  have hH : Measurable (fun p : EuclideanSpace ℝ (Fin d) × I =>
      ENNReal.ofReal (f (p.1 - α k • gradient (F p.2) p.1) - fs)) :=
    ENNReal.measurable_ofReal.comp ((hfc.measurable.comp (measurable_fst.sub
      ((hmeas.comp (measurable_snd.prodMk measurable_fst)).const_smul (α k)))).sub_const fs)
  have hXm' := run_meas F hmeas α x0 k
  have hle : (⨆ j ∈ Set.Iio k, MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI)
      ≤ MeasurableSpace.pi :=
    iSup₂_le (fun j _ => (measurable_pi_apply j).comap_le)
  have hXm : Measurable (fun ω => KarimiPL.SGD.sgRun F α x0 ω k) := hXm'.mono hle le_rfl
  have hYm : Measurable (fun ω : ℕ → I => ω k) := measurable_pi_apply k
  have hind : IndepFun (fun ω => KarimiPL.SGD.sgRun F α x0 ω k) (fun ω : ℕ → I => ω k)
      (KarimiPL.SGD.pathLaw ν) := by
    rw [IndepFun_iff_Indep]
    have hi : iIndep (fun j => MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI)
        (KarimiPL.SGD.pathLaw ν) := by
      have := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ (x : I) => x)
        (fun _ => measurable_id)
      rw [hPdef]
      exact (iIndepFun_iff_iIndep (fun _ => mI) (fun j (ω : ℕ → I) => ω j) _).1 this
    have h2 := indep_iSup_of_disjoint (fun j => (measurable_pi_apply j).comap_le) hi
      (S := Set.Iio k) (T := {k}) (by simp)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h2 hXm'.comap_le) ?_
    exact le_iSup₂ (f := fun j (_ : j ∈ ({k} : Set ℕ)) =>
      MeasurableSpace.comap (fun ω : ℕ → I => ω j) mI) k rfl
  have hmap : (KarimiPL.SGD.pathLaw ν).map
      (fun ω => (KarimiPL.SGD.sgRun F α x0 ω k, ω k))
      = ((KarimiPL.SGD.pathLaw ν).map (fun ω => KarimiPL.SGD.sgRun F α x0 ω k)).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hYm.aemeasurable).1 hind]
    congr 1
    rw [hPdef]
    exact Measure.infinitePi_map_eval _ k
  calc KarimiPL.SGD.expectedGap F ν α x0 f fs (k + 1)
      = ∫⁻ ω, (fun p : EuclideanSpace ℝ (Fin d) × I =>
          ENNReal.ofReal (f (p.1 - α k • gradient (F p.2) p.1) - fs))
            (KarimiPL.SGD.sgRun F α x0 ω k, ω k) ∂(KarimiPL.SGD.pathLaw ν) := rfl
    _ = ∫⁻ p, ENNReal.ofReal (f (p.1 - α k • gradient (F p.2) p.1) - fs)
          ∂((KarimiPL.SGD.pathLaw ν).map (fun ω => (KarimiPL.SGD.sgRun F α x0 ω k, ω k))) :=
        (lintegral_map hH (hXm.prodMk hYm)).symm
    _ = ∫⁻ p, ENNReal.ofReal (f (p.1 - α k • gradient (F p.2) p.1) - fs)
          ∂(((KarimiPL.SGD.pathLaw ν).map (fun ω => KarimiPL.SGD.sgRun F α x0 ω k)).prod ν) := by
        rw [hmap]
    _ = ∫⁻ y, ∫⁻ i, ENNReal.ofReal (f (y - α k • gradient (F i) y) - fs) ∂ν
          ∂((KarimiPL.SGD.pathLaw ν).map (fun ω => KarimiPL.SGD.sgRun F α x0 ω k)) :=
        lintegral_prod _ hH.aemeasurable
    _ = _ := lintegral_map hH.lintegral_prod_right' hXm

/-- The one-step recursion for the expected gap. -/
theorem step_bound {d : ℕ} {I : Type*} [MeasurableSpace I]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (fs : ℝ) (hfs : ∀ y, fs ≤ f y)
    (μ : ℝ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ fs)
    (hunb : KarimiPL.SGD.IsUnbiasedGradient F ν f)
    (hmeas : Measurable (fun p : I × EuclideanSpace ℝ (Fin d) => gradient (F p.1) p.2))
    (x0 : EuclideanSpace ℝ (Fin d)) (C : ℝ) (α : ℕ → ℝ) (hα : ∀ k, 0 ≤ α k)
    (hSM : KarimiPL.SGD.SecondMomentAlongRun F ν α x0 C) (k : ℕ) :
    KarimiPL.SGD.expectedGap F ν α x0 f fs (k + 1)
      ≤ ENNReal.ofReal (1 - 2 * μ * α k) * KarimiPL.SGD.expectedGap F ν α x0 f fs k
        + ENNReal.ofReal (L * α k ^ 2 * C ^ 2 / 2) := by
  have hPdef : KarimiPL.SGD.pathLaw ν = Measure.infinitePi (fun _ : ℕ => ν) := rfl
  haveI : IsProbabilityMeasure (KarimiPL.SGD.pathLaw ν) := by rw [hPdef]; infer_instance
  rw [step_lintegral ν F f hdiff.continuous fs hmeas α x0 k]
  calc ∫⁻ ω, (∫⁻ i, ENNReal.ofReal (f (KarimiPL.SGD.sgRun F α x0 ω k
          - α k • gradient (F i) (KarimiPL.SGD.sgRun F α x0 ω k)) - fs) ∂ν)
          ∂(KarimiPL.SGD.pathLaw ν)
      ≤ ∫⁻ ω, (ENNReal.ofReal (1 - 2 * μ * α k)
          * ENNReal.ofReal (f (KarimiPL.SGD.sgRun F α x0 ω k) - fs)
          + ENNReal.ofReal (L * α k ^ 2 * C ^ 2 / 2)) ∂(KarimiPL.SGD.pathLaw ν) := by
        apply lintegral_mono_ae
        filter_upwards [hSM] with ω hω
        exact one_step_point ν F f hdiff L hL hLip fs hfs μ hPL hunb hmeas C (α k) (hα k)
          (KarimiPL.SGD.sgRun F α x0 ω k) (hω k)
    _ = ENNReal.ofReal (1 - 2 * μ * α k) * KarimiPL.SGD.expectedGap F ν α x0 f fs k
        + ENNReal.ofReal (L * α k ^ 2 * C ^ 2 / 2) := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ,
          mul_one]
        rfl

theorem dec_ineq (K μ t : ℝ) (hK : 0 ≤ K) (hμ : 0 < μ) (ht : 1 ≤ t) :
    (1 - 2 * μ * ((2 * t + 1) / (2 * μ * (t + 1) ^ 2))) * (K / (2 * t * μ ^ 2))
      + K / (2 * μ ^ 2) * ((2 * t + 1) / (2 * μ * (t + 1) ^ 2)) ^ 2 * μ ^ 2
      ≤ K / (2 * (t + 1) * μ ^ 2) := by
  have ht0 : 0 < t := by linarith
  have h : K / (2 * (t + 1) * μ ^ 2)
      - ((1 - 2 * μ * ((2 * t + 1) / (2 * μ * (t + 1) ^ 2))) * (K / (2 * t * μ ^ 2))
      + K / (2 * μ ^ 2) * ((2 * t + 1) / (2 * μ * (t + 1) ^ 2)) ^ 2 * μ ^ 2)
      = K * (4 * t + 3) / (8 * μ ^ 2 * (t + 1) ^ 4) := by
    field_simp
    ring
  have : 0 ≤ K * (4 * t + 3) / (8 * μ ^ 2 * (t + 1) ^ 4) := by positivity
  linarith

end KPL4SGD

theorem solution {d : ℕ} {I : Type*} [MeasurableSpace I]
    (ν : MeasureTheory.Measure I) [MeasureTheory.IsProbabilityMeasure ν]
    (F : I → EuclideanSpace ℝ (Fin d) → ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hdiff : Differentiable ℝ f) (L : ℝ) (hL : 0 < L)
    (hLip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ y, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 < μ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar))
    (hf : KarimiPL.SGD.IsStochObjective F ν f)
    (hFdiff : ∀ i, Differentiable ℝ (F i))
    (hunb : KarimiPL.SGD.IsUnbiasedGradient F ν f)
    (hmeas : Measurable (fun p : I × EuclideanSpace ℝ (Fin d) => gradient (F p.1) p.2))
    (x0 : EuclideanSpace ℝ (Fin d)) (C : ℝ) :
    (KarimiPL.SGD.SecondMomentAlongRun F ν (KarimiPL.SGD.decStep μ) x0 C →
      ∀ k : ℕ, 1 ≤ k →
        KarimiPL.SGD.expectedGap F ν (KarimiPL.SGD.decStep μ) x0 f (f xstar) k
          ≤ ENNReal.ofReal (L * C ^ 2 / (2 * k * μ ^ 2))) ∧
    (∀ α₀ : ℝ, 0 < α₀ → α₀ < 1 / (2 * μ) →
      KarimiPL.SGD.SecondMomentAlongRun F ν (fun _ => α₀) x0 C →
      ∀ k : ℕ,
        KarimiPL.SGD.expectedGap F ν (fun _ => α₀) x0 f (f xstar) k
          ≤ ENNReal.ofReal ((1 - 2 * μ * α₀) ^ k * (f x0 - f xstar)
              + L * C ^ 2 * α₀ / (4 * μ))) := by
  have hPdef : KarimiPL.SGD.pathLaw ν = MeasureTheory.Measure.infinitePi (fun _ : ℕ => ν) := rfl
  haveI : MeasureTheory.IsProbabilityMeasure (KarimiPL.SGD.pathLaw ν) := by
    rw [hPdef]; infer_instance
  constructor
  · intro hSM k hk
    have hαnn : ∀ k, 0 ≤ KarimiPL.SGD.decStep μ k := fun k => by
      unfold KarimiPL.SGD.decStep; positivity
    have hrec := fun k => KPL4SGD.step_bound ν F f hdiff L hL hLip (f xstar) hxstar μ hPL hunb hmeas
      x0 C (KarimiPL.SGD.decStep μ) hαnn hSM k
    have key : ∀ n : ℕ, KarimiPL.SGD.expectedGap F ν (KarimiPL.SGD.decStep μ) x0 f (f xstar)
        (n + 1) ≤ ENNReal.ofReal (L * C ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * μ ^ 2)) := by
      intro n
      induction n with
      | zero =>
        refine (hrec 0).trans ?_
        have h0 : 1 - 2 * μ * KarimiPL.SGD.decStep μ 0 = 0 := by
          unfold KarimiPL.SGD.decStep
          field_simp
          push_cast
          ring
        rw [h0, ENNReal.ofReal_zero, zero_mul, zero_add]
        apply ENNReal.ofReal_le_ofReal
        unfold KarimiPL.SGD.decStep
        have h : L * C ^ 2 / (2 * ((0 + 1 : ℕ) : ℝ) * μ ^ 2)
            - L * ((2 * ((0 : ℕ) : ℝ) + 1) / (2 * μ * (((0 : ℕ) : ℝ) + 1) ^ 2)) ^ 2 * C ^ 2 / 2
            = 3 * (L * C ^ 2) / (8 * μ ^ 2) := by
          push_cast
          field_simp
          ring
        have : 0 ≤ 3 * (L * C ^ 2) / (8 * μ ^ 2) := by positivity
        linarith
      | succ n ih =>
        refine (hrec (n + 1)).trans ?_
        have hc : 0 ≤ 1 - 2 * μ * KarimiPL.SGD.decStep μ (n + 1) := by
          unfold KarimiPL.SGD.decStep
          rw [sub_nonneg, mul_div_assoc', div_le_one (by positivity)]
          push_cast
          have hn : (2 * ((n : ℝ) + 1) + 1) ≤ ((n : ℝ) + 1 + 1) ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 2 * μ)]
        have hD : 0 ≤ L * C ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * μ ^ 2) := by positivity
        calc ENNReal.ofReal (1 - 2 * μ * KarimiPL.SGD.decStep μ (n + 1))
              * KarimiPL.SGD.expectedGap F ν (KarimiPL.SGD.decStep μ) x0 f (f xstar) (n + 1)
              + ENNReal.ofReal (L * KarimiPL.SGD.decStep μ (n + 1) ^ 2 * C ^ 2 / 2)
            ≤ ENNReal.ofReal (1 - 2 * μ * KarimiPL.SGD.decStep μ (n + 1))
              * ENNReal.ofReal (L * C ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * μ ^ 2))
              + ENNReal.ofReal (L * KarimiPL.SGD.decStep μ (n + 1) ^ 2 * C ^ 2 / 2) := by
              gcongr
          _ = ENNReal.ofReal ((1 - 2 * μ * KarimiPL.SGD.decStep μ (n + 1))
              * (L * C ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * μ ^ 2))
              + L * KarimiPL.SGD.decStep μ (n + 1) ^ 2 * C ^ 2 / 2) := by
              rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (mul_nonneg hc hD)
                (by positivity)]
          _ ≤ ENNReal.ofReal (L * C ^ 2 / (2 * ((n + 1 + 1 : ℕ) : ℝ) * μ ^ 2)) := by
              apply ENNReal.ofReal_le_ofReal
              have := KPL4SGD.dec_ineq (L * C ^ 2) μ ((n + 1 : ℕ) : ℝ) (by positivity) hμ
                (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
              unfold KarimiPL.SGD.decStep
              have e : L * ((2 * ((n + 1 : ℕ) : ℝ) + 1)
                  / (2 * μ * (((n + 1 : ℕ) : ℝ) + 1) ^ 2)) ^ 2 * C ^ 2 / 2
                  = L * C ^ 2 / (2 * μ ^ 2) * ((2 * ((n + 1 : ℕ) : ℝ) + 1)
                  / (2 * μ * (((n + 1 : ℕ) : ℝ) + 1) ^ 2)) ^ 2 * μ ^ 2 := by
                field_simp
              rw [e]
              have e2 : ((n + 1 + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
              rw [e2]
              exact this
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact key n
  · intro α₀ hα0 hα1 hSM k
    have hc : 0 ≤ 1 - 2 * μ * α₀ := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ)).1 hα1
      linarith
    have hrec := fun k => KPL4SGD.step_bound ν F f hdiff L hL hLip (f xstar) hxstar μ hPL hunb hmeas
      x0 C (fun _ => α₀) (fun _ => hα0.le) hSM k
    have ha : 0 ≤ f x0 - f xstar := sub_nonneg.2 (hxstar x0)
    have hB : 0 ≤ L * C ^ 2 * α₀ / (4 * μ) := by positivity
    induction k with
    | zero =>
      have e0 : KarimiPL.SGD.expectedGap F ν (fun _ => α₀) x0 f (f xstar) 0
          = ENNReal.ofReal (f x0 - f xstar) := by
        show ∫⁻ _ω, ENNReal.ofReal (f x0 - f xstar) ∂(KarimiPL.SGD.pathLaw ν) = _
        rw [MeasureTheory.lintegral_const, MeasureTheory.measure_univ, mul_one]
      rw [e0]
      apply ENNReal.ofReal_le_ofReal
      simp only [pow_zero, one_mul]
      linarith
    | succ k ih =>
      refine (hrec k).trans ?_
      calc ENNReal.ofReal (1 - 2 * μ * α₀)
            * KarimiPL.SGD.expectedGap F ν (fun _ => α₀) x0 f (f xstar) k
            + ENNReal.ofReal (L * α₀ ^ 2 * C ^ 2 / 2)
          ≤ ENNReal.ofReal (1 - 2 * μ * α₀)
            * ENNReal.ofReal ((1 - 2 * μ * α₀) ^ k * (f x0 - f xstar)
              + L * C ^ 2 * α₀ / (4 * μ))
            + ENNReal.ofReal (L * α₀ ^ 2 * C ^ 2 / 2) := by gcongr
        _ = ENNReal.ofReal ((1 - 2 * μ * α₀) * ((1 - 2 * μ * α₀) ^ k * (f x0 - f xstar)
              + L * C ^ 2 * α₀ / (4 * μ)) + L * α₀ ^ 2 * C ^ 2 / 2) := by
            rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ = ENNReal.ofReal ((1 - 2 * μ * α₀) ^ (k + 1) * (f x0 - f xstar)
              + L * C ^ 2 * α₀ / (4 * μ)) := by
            congr 1
            field_simp
            ring

-- Prove2me | solution 1 for JHolomorphic.ae_sub_eq_integral_segment
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:20:47.317199+00:00
-- url     : https://prove2.me/submissions/67d7b434-45e0-4184-a974-a78e61168eb0

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_JHolomorphic_ae_eq_of_forall_integral_smul_eq
import Theorems.Thm_JHolomorphic_integrable_smul_of_integrableOn_compact
import Theorems.Thm_JHolomorphic_fderiv_apply_isTestFunction
import Theorems.Thm_JHolomorphic_lintegral_ball_segment_le
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.FDeriv.Comp



namespace JHolomorphic

open MeasureTheory Metric Filter
open scoped ContDiff ENNReal

/-- If `G` is the weak derivative of `f` in the direction `a` on `W` and `B(c, r + ‖a‖) ⊆ W`, then
`f (z + a) - f z = ∫₀¹ G (z + t a) dt` for almost every `z ∈ B(c, r)`. -/
theorem ae_sub_eq_integral_segment_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {W : Set ℂ} {f G : ℂ → E} (a : ℂ)
    (hd : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ z, fderiv ℝ φ z a • f z = -∫ z, φ z • G z)
    (hf : ∀ K ⊆ W, IsCompact K → IntegrableOn f K) (hG : StronglyMeasurable G)
    (hGi : ∀ K ⊆ W, IsCompact K → IntegrableOn G K) (c : ℂ) (r : ℝ)
    (hb : ball c (r + ‖a‖) ⊆ W) :
    ∀ᵐ z ∂(volume.restrict (ball c r)), f (z + a) - f z = ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a) := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hν
  haveI : IsProbabilityMeasure ν := ⟨by simp [hν]⟩
  have hseg : ∀ {t : ℝ}, t ∈ Set.Icc (0:ℝ) 1 → ‖(t:ℂ) * a‖ ≤ ‖a‖ := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have hball : ∀ {x : ℂ} {s : ℝ} (b : ℂ), x ∈ ball c s → ‖b‖ ≤ ‖a‖ → x + b ∈ ball c (s + ‖a‖) := by
    intro x s b hx hb'
    rw [mem_ball] at hx ⊢
    calc dist (x + b) c ≤ dist x c + ‖b‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
      _ < s + ‖a‖ := by linarith
  have hGm : Measurable fun x => ‖G x‖ₑ := hG.enorm
  have hGseg : StronglyMeasurable (Function.uncurry fun z (t : ℝ) => G (z + (t:ℂ) * a)) :=
    hG.comp_measurable (measurable_fst.add
      ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const))
  -- finiteness of `∫⁻ ‖G‖ₑ` on the enlarged discs
  have hfin : ∀ s < r, ∫⁻ w in ball c (s + ‖a‖), ‖G w‖ₑ < ⊤ := by
    intro s hs
    have hK : closedBall c (s + ‖a‖) ⊆ W :=
      (closedBall_subset_ball (by linarith)).trans hb
    exact lt_of_le_of_lt (lintegral_mono_set ball_subset_closedBall)
      (hGi _ hK (isCompact_closedBall _ _)).2
  -- integrability of `G (z + t a)` on `B(c, s) × (0, 1]`
  have hIG : ∀ s < r, Integrable (Function.uncurry fun z (t : ℝ) => G (z + (t:ℂ) * a))
      ((volume.restrict (ball c s)).prod ν) := by
    intro s hs
    refine ⟨hGseg.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ (hGseg.enorm.aemeasurable)]
    exact lt_of_le_of_lt (lintegral_ball_segment_le _ hGm a c s) (hfin s hs)
  have hF2 : ∀ K ⊆ ball c r, IsCompact K →
      IntegrableOn (fun z => ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)) K := by
    intro K hK hKc
    obtain ⟨s, hs, hKs⟩ := exists_lt_subset_ball hKc.isClosed hK
    have h := (hIG s hs).integral_prod_left
    have he : (fun z => ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a)) =
        fun z => ∫ t, G (z + (t:ℂ) * a) ∂ν := by
      funext z; exact intervalIntegral.integral_of_le zero_le_one
    rw [he]
    exact IntegrableOn.mono_set (t := ball c s) h hKs
  have hF1 : ∀ K ⊆ ball c r, IsCompact K → IntegrableOn (fun z => f (z + a) - f z) K := by
    intro K hK hKc
    refine IntegrableOn.sub ?_ (hf K (hK.trans ((ball_subset_ball (by
      linarith [norm_nonneg a])).trans hb)) hKc)
    set S := (fun x => x - a) ⁻¹' K
    have hSc : IsCompact S := (Homeomorph.subRight a).isCompact_preimage.2 hKc
    have hSW : S ⊆ W := by
      intro x hx
      have := hball (b := a) (hK hx) le_rfl
      simpa using hb this
    have hpre : (fun z => z + a) ⁻¹' S = K := by ext z; simp [S]
    have := ((measurePreserving_add_right volume a).integrableOn_comp_preimage
      (MeasurableEquiv.addRight a).measurableEmbedding (f := f) (s := S)).2 (hf S hSW hSc)
    rwa [hpre] at this
  refine ae_eq_of_forall_integral_smul_eq isOpen_ball hF1 hF2 ?_
  intro φ hφ hφc hφU
  obtain ⟨s, hs, hφs⟩ := exists_lt_subset_ball (isClosed_tsupport φ) hφU
  set K' := closedBall c (s + ‖a‖) with hK'
  have hK'W : K' ⊆ W := (closedBall_subset_ball (by linarith)).trans hb
  set f' := K'.indicator f with hf'
  have hf'i : Integrable f' :=
    (hf K' hK'W (isCompact_closedBall _ _)).integrable_indicator measurableSet_closedBall
  have hφ0 : ∀ x, φ x ≠ 0 → x ∈ ball c s := fun x hx => hφs (subset_tsupport _ hx)
  set κ : ℂ → ℝ := fun x => fderiv ℝ φ x a with hκ
  obtain ⟨hκs, hκc, -⟩ := fderiv_apply_isTestFunction (U := W) hφ hφc
    (hφs.trans ((ball_subset_ball (by linarith [norm_nonneg a])).trans hb)) a
  have hκ0 : ∀ x, κ x ≠ 0 → x ∈ ball c s := by
    intro x hx
    apply hφs
    apply support_fderiv_subset ℝ
    intro h0
    apply hx
    simp [hκ, h0]
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  obtain ⟨C', hC'⟩ := hκs.continuous.bounded_above_of_compact_support hκc
  have hmem : ∀ {x : ℂ} {t : ℝ}, t ∈ Set.Icc (0:ℝ) 1 → x - (t:ℂ) * a ∈ ball c s → x ∈ K' := by
    intro x t ht hx
    have := hball ((t:ℂ) * a) hx (hseg ht)
    rw [sub_add_cancel] at this
    exact ball_subset_closedBall this
  -- E1: move the translation onto `φ`
  have E1 : ∫ z, φ z • (f (z + a) - f z) = ∫ w, (φ (w - a) - φ w) • f' w := by
    have h1 : ∀ z, φ z • (f (z + a) - f z) = φ z • f' (z + a) - φ z • f' z := by
      intro z
      by_cases hz : φ z = 0
      · simp [hz]
      have hz' := hφ0 z hz
      have ha : z + a ∈ K' := by
        have := hmem (t := 1) ⟨zero_le_one, le_rfl⟩ (x := z + a) (by simpa using hz')
        exact this
      have hz'' : z ∈ K' := by
        have := hmem (t := 0) ⟨le_rfl, zero_le_one⟩ (x := z) (by simpa using hz')
        exact this
      rw [hf', Set.indicator_of_mem ha, Set.indicator_of_mem hz'', smul_sub]
    have hi1 : Integrable fun w => φ (w - a) • f' w := by
      refine Integrable.mono' (hf'i.norm.const_mul C)
        ((hφ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable.smul
          hf'i.aestronglyMeasurable) (Eventually.of_forall fun w => ?_)
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    have hi0 : Integrable fun w => φ w • f' w := by
      refine Integrable.mono' (hf'i.norm.const_mul C)
        (hφ.continuous.aestronglyMeasurable.smul hf'i.aestronglyMeasurable)
        (Eventually.of_forall fun w => ?_)
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    have htr : ∫ z, φ z • f' (z + a) = ∫ w, φ (w - a) • f' w := by
      have := integral_add_right_eq_self (μ := volume) (fun w => φ (w - a) • f' w) a
      simpa using this
    rw [integral_congr_ae (Eventually.of_forall h1)]
    have hi1' : Integrable fun z => φ z • f' (z + a) := by
      have := hi1.comp_add_right a
      simpa using this
    rw [integral_sub hi1' hi0, htr, ← integral_sub hi1 hi0]
    congr 1; funext w; rw [sub_smul]
  -- E2: fundamental theorem of calculus along the segment
  have E2 : ∀ w, φ (w - a) - φ w = -∫ t, κ (w - (t:ℂ) * a) ∂ν := by
    intro w
    have hder : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (w - (t:ℂ) * a)) (-κ (w - (t:ℂ) * a)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => w - (t:ℂ) * a) (-a) t := by
        have := ((hasDerivAt_id t).ofReal_comp.mul_const a).const_sub w
        simpa using this
      have h2 := ((hφ.differentiable (by simp)).differentiableAt (x := w - (t:ℂ) * a)).hasFDerivAt
      exact (h2.comp_hasDerivAt t h1).congr_deriv (by simp [hκ])
    have hcont : Continuous fun t : ℝ => -κ (w - (t:ℂ) * a) :=
      (hκs.continuous.comp (continuous_const.sub
        (Complex.continuous_ofReal.mul continuous_const))).neg
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (fun t _ => hder t) (hcont.intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le zero_le_one] at this
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, sub_zero] at this
    rw [← this]
    exact integral_neg _
  -- integrability for the first exchange of integrals
  have hIf : Integrable (Function.uncurry fun w (t : ℝ) => κ (w - (t:ℂ) * a) • f' w)
      (volume.prod ν) := by
    have hm : AEStronglyMeasurable (Function.uncurry fun w (t : ℝ) => κ (w - (t:ℂ) * a) • f' w)
        (volume.prod ν) :=
      ((hκs.continuous.comp (continuous_fst.sub
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))).aestronglyMeasurable).smul
        hf'i.aestronglyMeasurable.comp_fst
    refine Integrable.mono' ((hf'i.norm.const_mul C').comp_fst ν) hm
      (Eventually.of_forall fun p => ?_)
    obtain ⟨w, t⟩ := p
    simp only [Function.uncurry_apply_pair, norm_smul]
    exact mul_le_mul_of_nonneg_right (hC' _) (norm_nonneg _)
  -- E4: the weak derivative on each translate of `φ`
  have E4 : ∀ t ∈ Set.Ioc (0:ℝ) 1,
      ∫ w, κ (w - (t:ℂ) * a) • f' w = -∫ z, φ z • G (z + (t:ℂ) * a) := by
    intro t ht
    have ht' : t ∈ Set.Icc (0:ℝ) 1 := Set.Ioc_subset_Icc_self ht
    set ψ : ℂ → ℝ := fun w => φ (w - (t:ℂ) * a) with hψ
    have hψs : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.sub contDiff_const)
    have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.subRight _)
    have hψU : tsupport ψ ⊆ W := by
      intro x hx
      have hx' : x - (t:ℂ) * a ∈ tsupport φ :=
        tsupport_comp_subset_preimage φ (f := fun z => z - (t:ℂ) * a)
          (continuous_sub_right _) hx
      exact hK'W (hmem ht' (hφs hx'))
    have hdψ : ∀ w, fderiv ℝ ψ w = fderiv ℝ φ (w - (t:ℂ) * a) := fun w =>
      fderiv_comp_sub (f := φ) _
    have h1 : ∫ w, κ (w - (t:ℂ) * a) • f' w = ∫ w, fderiv ℝ ψ w a • f w := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [hdψ]
      show κ (w - (t:ℂ) * a) • f' w = κ (w - (t:ℂ) * a) • f w
      by_cases hw : κ (w - (t:ℂ) * a) = 0
      · rw [hw, zero_smul, zero_smul]
      · have hwK : w ∈ K' := hmem ht' (hκ0 _ hw)
        rw [hf', Set.indicator_of_mem hwK]
    rw [h1, hd ψ hψs hψc hψU]
    congr 1
    have := integral_add_right_eq_self (μ := volume) (fun w => ψ w • G w) ((t:ℂ) * a)
    simpa [hψ] using this.symm
  -- integrability for the second exchange of integrals
  have hIG' : Integrable (Function.uncurry fun z (t : ℝ) => φ z • G (z + (t:ℂ) * a))
      ((volume.restrict (ball c s)).prod ν) := by
    refine Integrable.mono' ((hIG s hs).norm.const_mul C)
      ((hφ.continuous.comp continuous_fst).aestronglyMeasurable.smul
        hGseg.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    obtain ⟨z, t⟩ := p
    simp only [Function.uncurry_apply_pair, norm_smul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  have hoff : ∀ g : ℂ → E, ∫ z, φ z • g z = ∫ z in ball c s, φ z • g z := by
    intro g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    have : φ z = 0 := by
      by_contra h; exact hz (hφ0 z h)
    simp [this]
  calc ∫ z, φ z • (f (z + a) - f z)
      = ∫ w, (φ (w - a) - φ w) • f' w := E1
    _ = -∫ w, ∫ t, κ (w - (t:ℂ) * a) • f' w ∂ν := by
        rw [← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [E2 w, neg_smul, integral_smul_const]
    _ = -∫ t, ∫ w, κ (w - (t:ℂ) * a) • f' w ∂volume ∂ν := by
        rw [integral_integral_swap hIf]
    _ = ∫ t, (∫ z in ball c s, φ z • G (z + (t:ℂ) * a)) ∂ν := by
        rw [← integral_neg]
        refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
        simp only [E4 t ht, neg_neg, hoff]
    _ = ∫ z in ball c s, ∫ t, φ z • G (z + (t:ℂ) * a) ∂ν := by
        rw [integral_integral_swap hIG']
    _ = ∫ z, φ z • ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a) := by
        rw [hoff]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [intervalIntegral.integral_of_le zero_le_one, integral_smul, hν]

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {W : Set ℂ} {f G : ℂ → E} (a : ℂ)
    (hd : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W →
      ∫ z, fderiv ℝ φ z a • f z = -∫ z, φ z • G z)
    (hf : ∀ K ⊆ W, IsCompact K → IntegrableOn f K) (hG : StronglyMeasurable G)
    (hGi : ∀ K ⊆ W, IsCompact K → IntegrableOn G K) (c : ℂ) (r : ℝ)
    (hb : ball c (r + ‖a‖) ⊆ W) :
    ∀ᵐ z ∂(volume.restrict (ball c r)), f (z + a) - f z = ∫ t in (0:ℝ)..1, G (z + (t:ℂ) * a) :=
  ae_sub_eq_integral_segment_aux a hd hf hG hGi c r hb

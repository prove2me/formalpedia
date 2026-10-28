-- Prove2me | solution 1 for OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:08:47.962207+00:00
-- url     : https://prove2.me/submissions/3bf35f2b-77b6-478f-8ed9-194997437d9e

import Mathlib
import Definitions.Def_OAIQ087A027
import Definitions.Def_OAIQ087A028

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Density
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman

open scoped Real Topology NNReal ContDiff
open Set Filter MeasureTheory
open ProbabilityTheory

 theorem density_pos (x : ℝ) : 0 < density x := gaussianPDFReal_pos 0 1 x (by norm_num)
 theorem density_nonneg (x : ℝ) : 0 ≤ density x := (density_pos x).le
 theorem density_continuous : Continuous density := by
  unfold density gaussianPDFReal
  fun_prop

 theorem density_integrable : Integrable density := integrable_gaussianPDFReal 0 1

 theorem density_neg (x : ℝ) : density (-x) = density x := by
  simp [density, gaussianPDFReal]

 theorem density_deriv (x : ℝ) : HasDerivAt density (-x * density x) x := by
  unfold density gaussianPDFReal
  convert (HasDerivAt.const_mul (√(2 * Real.pi * (1 : ℝ≥0) : ℝ))⁻¹
    (((hasDerivAt_id x).pow 2).neg.div_const (2 * (1 : ℝ≥0))).exp) using 1 <;>
    norm_num
  all_goals first | rfl | ring

 theorem cdf_deriv (x : ℝ) : HasDerivAt cdf (density x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (density_continuous.intervalIntegrable 0 x)
    density_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    density_continuous.continuousAt
  convert h.const_add (1 / 2 : ℝ) using 1
  all_goals try with_reducible_and_instances rfl
  rfl

 theorem cdf_continuous : Continuous cdf := continuous_iff_continuousAt.mpr
  (fun x => (cdf_deriv x).continuousAt)

 theorem cdf_strictMono : StrictMono cdf := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(cdf_deriv x).deriv]
  exact density_pos x

 theorem integral_density : ∫ x, density x = 1 :=
  integral_gaussianPDFReal_eq_one 0 (by norm_num : (1 : ℝ≥0) ≠ 0)

 theorem half_integral : ∫ x in Iic (0 : ℝ), density x = 1 / 2 := by
  have he : (∫ x in Iic (0 : ℝ), density x) = ∫ x in Ioi (0 : ℝ), density x := by
    simpa only [density_neg, neg_zero] using integral_comp_neg_Iic 0 density
  have h := intervalIntegral.integral_Iic_add_Ioi (b := 0)
    density_integrable.integrableOn density_integrable.integrableOn
  rw [integral_density, ← he] at h
  linarith

 theorem cdf_eq_integral (x : ℝ) : cdf x = ∫ t in Iic x, density t := by
  have h := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x)
    density_integrable.integrableOn density_integrable.integrableOn
  rw [half_integral] at h
  unfold cdf
  linarith

 theorem cdf_mem_Ioo (x : ℝ) : cdf x ∈ Ioo (0 : ℝ) 1 := by
  have h0 (y : ℝ) : 0 ≤ cdf y := by
    rw [cdf_eq_integral]
    exact integral_nonneg density_nonneg
  have h1 (y : ℝ) : cdf y ≤ 1 := by
    rw [cdf_eq_integral]
    have h := intervalIntegral.integral_Iic_add_Ioi (b := y)
      density_integrable.integrableOn density_integrable.integrableOn
    rw [integral_density] at h
    have hn : 0 ≤ ∫ t in Ioi y, density t := integral_nonneg density_nonneg
    linarith
  exact ⟨(h0 (x - 1)).trans_lt (cdf_strictMono (by linarith)),
    (cdf_strictMono (show x < x + 1 by linarith)).trans_le (h1 (x + 1))⟩

 theorem cdf_neg (x : ℝ) : cdf (-x) = 1 - cdf x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) density
  simp only [density_neg, neg_zero] at h
  have h' : (∫ t in (0 : ℝ)..-x, density t) = -(∫ t in (0 : ℝ)..x, density t) := by
    rw [intervalIntegral.integral_symm, ← h]
  dsimp [cdf]
  rw [h']
  ring

 theorem cdf_tendsto_atBot : Tendsto cdf atBot (𝓝 0) := by
  convert (tendsto_integral_Iic_zero (f := density) (μ := volume) tendsto_id) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  exact cdf_eq_integral x

 theorem cdf_tendsto_atTop : Tendsto cdf atTop (𝓝 1) := by
  have h := cdf_tendsto_atBot.comp tendsto_neg_atTop_atBot
  have h' := h.const_sub 1
  simpa only [Function.comp_def, cdf_neg, sub_sub_cancel, sub_zero] using h'

 theorem cdf_range : range cdf = Ioo (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩; exact cdf_mem_Ioo x
  · have h := isPreconnected_univ.intermediate_value_Ioo
      (l₁ := atBot) (l₂ := atTop) (by simp) (by simp)
      cdf_continuous.continuousOn cdf_tendsto_atBot cdf_tendsto_atTop
    simpa only [image_univ] using h

@[simp] theorem quantile_cdf (x : ℝ) : quantile (cdf x) = x :=
  Function.leftInverse_invFun cdf_strictMono.injective x

 theorem cdf_quantile {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : cdf (quantile x) = x := by
  obtain ⟨y, rfl⟩ : x ∈ range cdf := cdf_range.symm ▸ hx
  exact congrArg cdf (quantile_cdf y)

 theorem quantile_strictMonoOn : StrictMonoOn quantile (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  apply cdf_strictMono.lt_iff_lt.mp
  rwa [cdf_quantile ha, cdf_quantile hb]

 theorem quantile_image : quantile '' Ioo (0 : ℝ) 1 = univ := by
  apply eq_univ_of_forall
  intro x
  exact ⟨cdf x, cdf_mem_Ioo x, quantile_cdf x⟩

 theorem quantile_continuousAt {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt quantile x := by
  apply quantile_strictMonoOn.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds hx)
  rw [quantile_image]
  exact univ_mem

 theorem quantile_deriv {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt quantile (density (quantile x))⁻¹ x := by
  apply HasDerivAt.of_local_left_inverse (quantile_continuousAt hx)
    (cdf_deriv (quantile x)) (ne_of_gt (density_pos _))
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact cdf_quantile hy

@[simp] theorem quantile_half : quantile (1 / 2) = 0 := by
  simpa only [cdf_zero] using quantile_cdf 0

/-- Differentiation under a finite integral using the actual compact uniform
bound, to be applied to the Plackett integrand below. -/
 theorem integral_hasDerivAt_compact {F F' : ℝ → ℝ → ℝ} {a b u v x : ℝ}
    (hx : x ∈ Ioo u v) (hab : a ≤ b)
    (hc : ContinuousOn (Function.uncurry F) (Icc u v ×ˢ Icc a b))
    (hc' : ContinuousOn (Function.uncurry F') (Icc u v ×ˢ Icc a b))
    (hd : ∀ z ∈ Icc u v, ∀ t ∈ Icc a b, HasDerivAt (F · t) (F' z t) z) :
    HasDerivAt (fun z => ∫ t in a..b, F z t) (∫ t in a..b, F' x t) x := by
  have section_cont {H : ℝ → ℝ → ℝ}
      (hh : ContinuousOn (Function.uncurry H) (Icc u v ×ˢ Icc a b))
      {z : ℝ} (hz : z ∈ Icc u v) : ContinuousOn (H z) (Icc a b) := by
    exact hh.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hz, ht⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc'
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a b)) (F := F) (F' := F') (bound := fun _ => C)
    (Icc_mem_nhds hx.1 hx.2)
    (show ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) (volume.restrict (Ioc a b)) from by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with z hz
      exact ((section_cont hc hz).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
    (((section_cont hc ⟨hx.1.le, hx.2.le⟩).integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    (((section_cont hc' ⟨hx.1.le, hx.2.le⟩).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc)
    (show ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ z ∈ Icc u v, ‖F' z t‖ ≤ C from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht z hz
      exact hC (z, t) ⟨hz, Ioc_subset_Icc_self ht⟩)
    (integrable_const C)
    (show ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ z ∈ Icc u v,
      HasDerivAt (F · t) (F' z t) z from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht z hz
      exact hd z hz t (Ioc_subset_Icc_self ht))
  simpa only [intervalIntegral.integral_of_le hab] using h.2

 theorem sigma_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < sigma t := by
  apply Real.sqrt_pos.mpr
  nlinarith [ht.1, ht.2]

 theorem sigma_sq {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : (sigma t) ^ 2 = 1 - t ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [ht.1, ht.2]

 theorem sigma_continuous : Continuous sigma := by unfold sigma; fun_prop

 theorem sigma_deriv {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt sigma (-t / sigma t) t := by
  have h := ((hasDerivAt_id t).pow 2).const_sub 1
  convert h.sqrt (ne_of_gt (show 0 < 1 - t ^ 2 by nlinarith [ht.1, ht.2])) using 1 <;>
    first | rfl | (dsimp [sigma]; ring)

 theorem plackett_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    0 < plackett t u v := div_pos (mul_pos (density_pos _) (density_pos _)) (sigma_pos ht)

 theorem conditionalArg_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => conditionalArg p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Ioo (-1 : ℝ) 1} := by
  unfold conditionalArg
  exact ((continuous_snd.snd.sub (continuous_fst.mul continuous_snd.fst)).continuousOn).div
    (sigma_continuous.comp continuous_fst).continuousOn (fun p hp => ne_of_gt (sigma_pos hp))

 theorem plackett_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => plackett p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Ioo (-1 : ℝ) 1} := by
  unfold plackett
  exact ((density_continuous.comp continuous_snd.fst).continuousOn.mul
    (density_continuous.comp_continuousOn conditionalArg_continuousOn)).div
    (sigma_continuous.comp continuous_fst).continuousOn (fun p hp => ne_of_gt (sigma_pos hp))

 theorem kernel_ge_product {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y : ℝ) :
    x * y ≤ kernel t x y := by
  have h : 0 ≤ ∫ r in (0 : ℝ)..t, plackett r (quantile x) (quantile y) := by
    apply intervalIntegral.integral_nonneg ht.1
    intro r hr
    exact (plackett_pos ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩ _ _).le
  exact le_add_of_nonneg_right h

 theorem density_mul (u v : ℝ) : density u * density v =
    density 0 ^ 2 * Real.exp (-u ^ 2 / 2 + -v ^ 2 / 2) := by
  simp only [density, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
    zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero, zero_div, Real.exp_zero, Real.exp_add]
  ring

 theorem density_zero_sq : density 0 ^ 2 = (2 * Real.pi)⁻¹ := by
  have h : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  simp only [density, gaussianPDFReal, NNReal.coe_one, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
    neg_zero, zero_div, Real.exp_zero, mul_one, inv_pow, h]

 theorem plackett_symm {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    plackett t u v = plackett t v u := by
  have hn := ne_of_gt (sigma_pos ht)
  have he : -u ^ 2 / 2 + -(conditionalArg t u v) ^ 2 / 2 =
      -v ^ 2 / 2 + -(conditionalArg t v u) ^ 2 / 2 := by
    unfold conditionalArg
    calc
      _ = -(u ^ 2 * sigma t ^ 2 + (v - t * u) ^ 2) / (2 * sigma t ^ 2) := by
        field_simp; ring
      _ = -(v ^ 2 * sigma t ^ 2 + (u - t * v) ^ 2) / (2 * sigma t ^ 2) := by
        rw [sigma_sq ht]; ring
      _ = _ := by field_simp; ring
  unfold plackett
  rw [density_mul, density_mul, he]

 theorem kernel_symm {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y : ℝ) :
    kernel t x y = kernel t y x := by
  unfold kernel
  rw [mul_comm x y]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  exact plackett_symm ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩ _ _

 theorem kernel_half {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    kernel t (1 / 2) (1 / 2) = 1 / 4 + Real.arcsin t / (2 * Real.pi) := by
  have hi : IntervalIntegrable (fun r => 1 / sigma r) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.div sigma_continuous.continuousOn (fun r hr => by
      rw [uIcc_of_le ht.1] at hr
      exact ne_of_gt (sigma_pos ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f := Real.arcsin) (f' := fun r => 1 / sigma r)
    (fun r hr => by
      rw [uIcc_of_le ht.1] at hr
      exact Real.hasDerivAt_arcsin (by linarith [hr.1]) (ne_of_lt (hr.2.trans_lt ht.2))) hi
  simp only [kernel, quantile_half, plackett, conditionalArg, mul_zero, sub_zero, zero_div,
    ← pow_two, density_zero_sq]
  simp only [div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul] at h ⊢
  rw [h, Real.arcsin_zero, sub_zero]
  ring

 theorem conditionalArg_deriv_u (t u v : ℝ) :
    HasDerivAt (fun z => conditionalArg t z v) (-t / sigma t) u := by
  convert (((hasDerivAt_id u).const_mul t).const_sub v).div_const (sigma t) using 1 <;>
    first | rfl | simp

 theorem conditionalArg_deriv_t {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    HasDerivAt (fun r => conditionalArg r u v) ((t * v - u) / sigma t ^ 3) t := by
  have hn := ne_of_gt (sigma_pos ht)
  have he : ((-u) * sigma t - (v - t * u) * (-t / sigma t)) / sigma t ^ 2 =
      (t * v - u) / sigma t ^ 3 := by
    field_simp
    rw [sigma_sq ht]
    ring
  convert (((hasDerivAt_id t).mul_const u).const_sub v).div (sigma_deriv ht) hn using 1 <;> try rfl
  simpa only [id_eq, one_mul] using he.symm

 theorem plackett_deriv_u {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    HasDerivAt (fun z => plackett t z v)
      (density u * density (conditionalArg t u v) * (t * v - u) / sigma t ^ 3) u := by
  have hn := ne_of_gt (sigma_pos ht)
  have hd := ((density_deriv u).mul
    ((density_deriv (conditionalArg t u v)).comp u (conditionalArg_deriv_u t u v))).div_const
      (sigma t)
  convert hd using 1 <;> try rfl
  dsimp only [Function.comp_apply]
  unfold conditionalArg
  field_simp
  rw [sigma_sq ht]
  ring

 theorem plackett_quantile_deriv_x {t x : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (y : ℝ) :
    HasDerivAt (fun z => plackett t (quantile z) (quantile y))
      (density (conditionalArg t (quantile x) (quantile y)) *
        (t * quantile y - quantile x) / sigma t ^ 3) x := by
  convert (plackett_deriv_u ht (quantile x) (quantile y)).comp x (quantile_deriv hx) using 1 <;> try rfl
  field_simp [ne_of_gt (density_pos (quantile x))]

 theorem conditionalCDF_deriv_t {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (u v : ℝ) :
    HasDerivAt (fun r => cdf (conditionalArg r u v))
      (density (conditionalArg t u v) * (t * v - u) / sigma t ^ 3) t := by
  convert (cdf_deriv (conditionalArg t u v)).comp t (conditionalArg_deriv_t ht u v) using 1 <;> try rfl
  ring

 theorem flux_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => flux p.1 p.2.1 p.2.2)
      {p | p.1 ∈ Ioo (-1 : ℝ) 1} := by
  unfold flux
  exact ((density_continuous.comp_continuousOn conditionalArg_continuousOn).mul
    ((continuous_fst.mul continuous_snd.snd).sub continuous_snd.fst).continuousOn).div
    ((sigma_continuous.comp continuous_fst).pow 3).continuousOn
    (fun p hp => pow_ne_zero _ (ne_of_gt (sigma_pos hp)))

 theorem quantile_continuousOn : ContinuousOn quantile (Ioo (0 : ℝ) 1) :=
  fun _ hx => (quantile_continuousAt hx).continuousWithinAt

 theorem kernel_deriv_x {t x y : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => kernel t z y) (cdf (conditionalArg t (quantile x) (quantile y))) x := by
  let u := x / 2
  let v := (x + 1) / 2
  have huxv : x ∈ Ioo u v := by dsimp [u, v]; constructor <;> linarith [hx.1, hx.2]
  have huv : Icc u v ⊆ Ioo (0 : ℝ) 1 := by
    intro z hz; dsimp [u, v] at hz; constructor <;> linarith [hx.1, hx.2, hz.1, hz.2]
  have hrt : Icc (0 : ℝ) t ⊆ Ioo (-1 : ℝ) 1 := by
    intro r hr; exact ⟨by linarith [hr.1], hr.2.trans_lt ht.2⟩
  have hm : ContinuousOn (fun p : ℝ × ℝ => (p.2, quantile p.1, quantile y))
      (Icc u v ×ˢ Icc (0 : ℝ) t) := by
    apply continuous_snd.continuousOn.prodMk
    exact (quantile_continuousOn.comp continuous_fst.continuousOn
      (fun p hp => huv hp.1)).prodMk continuousOn_const
  have hc := plackett_continuousOn.comp hm (fun p hp => hrt hp.2)
  have hc' := flux_continuousOn.comp hm (fun p hp => hrt hp.2)
  have hd := integral_hasDerivAt_compact (F := fun z r => plackett r (quantile z) (quantile y))
    (F' := fun z r => flux r (quantile z) (quantile y)) huxv ht.1 hc hc'
    (fun z hz r hr => plackett_quantile_deriv_x (hrt hr) (huv hz) y)
  have hint : (∫ r in (0 : ℝ)..t, flux r (quantile x) (quantile y)) =
      cdf (conditionalArg t (quantile x) (quantile y)) - y := by
    have hfc : ContinuousOn (fun r => flux r (quantile x) (quantile y)) (uIcc 0 t) := by
      apply flux_continuousOn.comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const)).continuousOn
      intro r hr
      rw [uIcc_of_le ht.1] at hr
      exact hrt hr
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun r hr => conditionalCDF_deriv_t (hrt (by rwa [uIcc_of_le ht.1] at hr))
        (quantile x) (quantile y)) hfc.intervalIntegrable
    simpa only [flux, conditionalArg, sigma, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
      Real.sqrt_one, zero_mul, div_one, cdf_quantile hy] using hh
  convert ((hasDerivAt_id x).mul_const y).add hd using 1 <;> try rfl
  simp only [one_mul]
  rw [hint]
  ring

 theorem kernel_deriv_y {t x y : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (kernel t x) (cdf (conditionalArg t (quantile y) (quantile x))) y := by
  have h := kernel_deriv_x ht hy hx
  have he : (fun z => kernel t z x) = kernel t x := by
    funext z; exact kernel_symm ht z x
  rwa [he] at h

 theorem kernel_weighted_hessian {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y a b : ℝ) :
    kernelXX t x y * a ^ 2 + 2 * t * kernelXY t x y * a * b + kernelXX t y x * b ^ 2 =
      -t * plackett t (quantile x) (quantile y) *
        (a / density (quantile x) - b / density (quantile y)) ^ 2 := by
  have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  unfold kernelXX kernelXY
  rw [plackett_symm ht' (quantile y) (quantile x)]
  field_simp [ne_of_gt (density_pos (quantile x)), ne_of_gt (density_pos (quantile y))]
  ring

 theorem kernel_weighted_hessian_nonpos {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (x y a b : ℝ) :
    kernelXX t x y * a ^ 2 + 2 * t * kernelXY t x y * a * b + kernelXX t y x * b ^ 2 ≤ 0 := by
  rw [kernel_weighted_hessian ht]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [ht.1])
      (plackett_pos ⟨by linarith [ht.1], ht.2⟩ _ _).le
  · exact sq_nonneg _

 theorem density_contDiff (n : ℕ∞ω) : ContDiff ℝ n density := by
  unfold density gaussianPDFReal
  fun_prop

 theorem cdf_contDiff (n : ℕ) : ContDiff ℝ n cdf := by
  cases n with
  | zero => exact contDiff_zero.mpr cdf_continuous
  | succ n =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp, contDiff_succ_iff_deriv]
    refine ⟨fun x => (cdf_deriv x).differentiableAt, by simp, ?_⟩
    have he : deriv cdf = density := funext (fun x => (cdf_deriv x).deriv)
    rw [he]
    exact density_contDiff n

 theorem quantile_contDiffOn (n : ℕ) : ContDiffOn ℝ n quantile (Ioo (0 : ℝ) 1) := by
  induction n with
  | zero => exact contDiffOn_zero.mpr quantile_continuousOn
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun x hx => (quantile_deriv hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have h : ContDiffOn ℝ n (fun x => (density (quantile x))⁻¹) (Ioo (0 : ℝ) 1) := by
      exact ((density_contDiff n).comp_contDiffOn ih).inv (fun _ _ => ne_of_gt (density_pos _))
    apply h.congr
    intro x hx
    exact (quantile_deriv hx).deriv

 theorem kernelX_contDiffOn {t : ℝ} (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (kernelX t)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hx : ContDiffOn ℝ n (fun p : ℝ × ℝ => quantile p.1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (quantile_contDiffOn n).comp contDiffOn_fst (fun _ hp => hp.1)
  have hy : ContDiffOn ℝ n (fun p : ℝ × ℝ => quantile p.2)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (quantile_contDiffOn n).comp contDiffOn_snd (fun _ hp => hp.2)
  exact (cdf_contDiff n).comp_contDiffOn ((hy.sub (contDiffOn_const.mul hx)).div_const (sigma t))

 theorem kernelD_contDiffOn (t : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (kernelD t) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  have hswap : ContDiffOn ℝ n (fun p : ℝ × ℝ => kernelX t p.2 p.1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (kernelX_contDiffOn n).comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)
  exact ((kernelX_contDiffOn n).smul_const _).add (hswap.smul_const _)

 theorem kernel_fderiv {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :
    HasFDerivAt (Function.uncurry (kernel t)) (kernelD t p) p := by
  have hn := (isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp
  have hc : ContinuousAt (Function.uncurry (kernelX t)) p :=
    (kernelX_contDiffOn 0).continuousOn.continuousAt hn
  have hswap : ContDiffOn ℝ 0 (fun q : ℝ × ℝ => kernelX t q.2 q.1)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) :=
    (kernelX_contDiffOn 0).comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hq => ⟨hq.2, hq.1⟩)
  have hcs : ContinuousAt (fun q : ℝ × ℝ => kernelX t q.2 q.1) p :=
    hswap.continuousOn.continuousAt hn
  have hf := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (f := kernel t)
    (f₁ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (kernelX t x y))
    (f₂ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (kernelX t y x))
    (Filter.mem_of_superset hn (fun q hq => (kernel_deriv_x ht hq.1 hq.2).hasFDerivAt))
    (Filter.mem_of_superset hn (fun q hq => (kernel_deriv_y ht hq.1 hq.2).hasFDerivAt))
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hc)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.continuousAt.comp hcs)
  convert hf.hasFDerivAt using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro q
  change kernelX t p.1 p.2 * q.1 + kernelX t p.2 p.1 * q.2 =
    q.1 * kernelX t p.1 p.2 + q.2 * kernelX t p.2 p.1
  ring

 theorem kernel_contDiffOn {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (kernel t)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
  cases n with
  | zero =>
    apply contDiffOn_zero.mpr
    intro p hp
    exact (kernel_fderiv ht hp).continuousAt.continuousWithinAt
  | succ n =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_Ioo)]
    refine ⟨fun p hp => (kernel_fderiv ht hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    apply (kernelD_contDiffOn t n).congr
    intro p hp
    exact (kernel_fderiv ht hp).fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem affinePath_deriv (p d : E) (u : ℝ) :
    HasDerivAt (fun v : ℝ => p + v • d) d u := by
  simpa using ((hasDerivAt_id u).smul_const d).const_add p

 theorem affinePath_iterated_two (p d : E) (u : ℝ) :
    iteratedDeriv 2 (fun v : ℝ => p + v • d) u = 0 := by
  rw [iteratedDeriv_const_add (by norm_num),
    iteratedDeriv_smul_const (f := fun v : ℝ => v) (contDiffAt_id : ContDiffAt ℝ 2 _ _)]
  simp [iteratedDeriv_fun_id]

 theorem affinePath_iterated_three (p d : E) (u : ℝ) :
    iteratedDeriv 3 (fun v : ℝ => p + v • d) u = 0 := by
  rw [iteratedDeriv_const_add (by norm_num),
    iteratedDeriv_smul_const (f := fun v : ℝ => v) (contDiffAt_id : ContDiffAt ℝ 3 _ _)]
  simp [iteratedDeriv_fun_id]

 theorem iteratedDeriv_affinePath_two {F : E → ℝ} {p d : E} {u : ℝ}
    (hf : ContDiffAt ℝ 2 F (p + u • d)) :
    iteratedDeriv 2 (fun v : ℝ => F (p + v • d)) u =
      iteratedFDeriv ℝ 2 F (p + u • d) (fun _ => d) := by
  have h := iteratedDeriv_vcomp_two hf
    (show ContDiffAt ℝ 2 (fun v : ℝ => p + v • d) u by fun_prop)
  simpa [Function.comp_def, (affinePath_deriv p d u).deriv,
    affinePath_iterated_two] using h

 theorem iteratedDeriv_affinePath_three {F : E → ℝ} {p d : E} {u : ℝ}
    (hf : ContDiffAt ℝ 3 F (p + u • d)) :
    iteratedDeriv 3 (fun v : ℝ => F (p + v • d)) u =
      iteratedFDeriv ℝ 3 F (p + u • d) (fun _ => d) := by
  have h := iteratedDeriv_vcomp_three hf
    (show ContDiffAt ℝ 3 (fun v : ℝ => p + v • d) u by fun_prop)
  have hz₀ := (iteratedFDeriv ℝ 2 F (p + u • d)).map_coord_zero
    (m := ![0, d]) 0 (by simp)
  have hz₁ := (iteratedFDeriv ℝ 2 F (p + u • d)).map_coord_zero
    (m := ![d, 0]) 1 (by simp)
  simpa [Function.comp_def, (affinePath_deriv p d u).deriv,
    affinePath_iterated_two, affinePath_iterated_three, hz₀, hz₁] using h

 theorem compact_third_derivative_bound {O K : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) {F : E → ℝ} (hf : ContDiffOn ℝ 3 F O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ‖iteratedFDeriv ℝ 3 F p‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ 3 F) O := by
    apply (hf.continuousOn_iteratedFDerivWithin (by norm_num) hO.uniqueDiffOn).congr
    intro p hp
    exact (iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
      (hf.contDiffAt (hO.mem_nhds hp)) hp).symm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKO)
  refine ⟨max 0 C, le_max_left _ _, fun p hp => (hC p hp).trans (le_max_right _ _)⟩

 theorem compact_cubic_taylor_bound {O K : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hcv : Convex ℝ K) (hKO : K ⊆ O)
    {F : E → ℝ} (hf : ContDiffOn ℝ 3 F O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ q ∈ K,
      |F q - F p - fderiv ℝ F p (q - p) -
        (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F p (fun _ => q - p)| ≤ C * ‖q - p‖ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := compact_third_derivative_bound hO hK hKO hf
  refine ⟨C, hC0, ?_⟩
  intro p hp q hq
  let d := q - p
  let g : ℝ → ℝ := fun u => F (p + u • d)
  have hpath (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : p + u • d ∈ K :=
    hcv.add_smul_sub_mem hp hq hu
  have hF (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 3 F (p + u • d) :=
    hf.contDiffAt (hO.mem_nhds (hKO (hpath u hu)))
  have hg (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 3 g u :=
    (hF u hu).comp u (by fun_prop)
  have hthird (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin 3 g (Icc 0 1) u‖ ≤ C * ‖d‖ ^ 3 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num)) (hg u hu) hu]
    change ‖iteratedDeriv 3 (fun v => F (p + v • d)) u‖ ≤ _
    rw [iteratedDeriv_affinePath_three (hF u hu)]
    simpa using (iteratedFDeriv ℝ 3 F (p + u • d)).le_of_opNorm_le
      (hC _ (hpath u hu)) (fun _ => d)
  have hb := taylor_mean_remainder_bound (n := 2) (a := (0 : ℝ)) (b := 1)
    (x := 1) (by norm_num) (fun u hu => (hg u hu).contDiffWithinAt)
    (by constructor <;> norm_num) hthird
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hg0 : ContDiffAt ℝ 3 g 0 := hg 0 h0
  have hg1 : deriv g 0 = fderiv ℝ F p d := by
    have hh := (hf.contDiffAt (hO.mem_nhds (hKO hp))).differentiableAt (by norm_num)
    have hh' : HasFDerivAt F (fderiv ℝ F p) (p + (0 : ℝ) • d) := by simpa using hh.hasFDerivAt
    simpa [g, Function.comp_def] using (hh'.comp_hasDerivAt 0 (affinePath_deriv p d 0)).deriv
  have hg2 : iteratedDeriv 2 g 0 = iteratedFDeriv ℝ 2 F p (fun _ => d) := by
    simpa [g] using iteratedDeriv_affinePath_two ((hF 0 h0).of_le (by norm_num))
  have ht : taylorWithinEval g 2 (Icc 0 1) 0 1 =
      F p + fderiv ℝ F p d + (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F p (fun _ => d) := by
    rw [taylorWithinEval_succ g 1, taylorWithinEval_succ g 0, taylor_within_zero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
        (hg0.of_le (by norm_num)) h0,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
        (hg0.of_le (by norm_num)) h0]
    simp only [hg2]
    norm_num [g]
    exact hg1
  rw [ht] at hb
  have hg_end : g 1 = F q := by simp [g, d]
  rw [hg_end] at hb
  norm_num at hb
  calc
    _ = |F q - (F p + fderiv ℝ F p d +
        (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 F p (fun _ => d))| := by congr 1; dsimp [d]; ring
    _ ≤ C * ‖d‖ ^ 3 / 2 := hb
    _ ≤ C * ‖q - p‖ ^ 3 := div_le_self (by positivity) (by norm_num)

 theorem kernelX_line_deriv {t x y a b u : ℝ} (_ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x + u * a ∈ Ioo (0 : ℝ) 1) (hy : y + u * b ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v : ℝ => kernelX t (x + v * a) (y + v * b))
      (kernelXX t (x + u * a) (y + u * b) * a +
        kernelXY t (x + u * a) (y + u * b) * b) u := by
  have hqx := (quantile_deriv hx).comp u (((hasDerivAt_id u).mul_const a).const_add x)
  have hqy := (quantile_deriv hy).comp u (((hasDerivAt_id u).mul_const b).const_add y)
  have h := (cdf_deriv (conditionalArg t (quantile (x + u * a)) (quantile (y + u * b)))).comp u
    ((hqy.sub (hqx.const_mul t)).div_const (sigma t))
  convert h using 1 <;> try rfl
  unfold kernelXX kernelXY plackett
  field_simp [ne_of_gt (density_pos (quantile (x + u * a))),
    ne_of_gt (density_pos (quantile (y + u * b)))]
  ring

 theorem kernel_line_deriv {t x y a b u : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x + u * a ∈ Ioo (0 : ℝ) 1) (hy : y + u * b ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun v : ℝ => kernel t (x + v * a) (y + v * b))
      (kernelX t (x + u * a) (y + u * b) * a +
        kernelX t (y + u * b) (x + u * a) * b) u := by
  have hline : HasDerivAt (fun v : ℝ => (x + v * a, y + v * b)) (a, b) u :=
    by simpa using ((((hasDerivAt_id u).mul_const a).const_add x).prodMk
      (((hasDerivAt_id u).mul_const b).const_add y))
  simpa [Function.comp_def, kernelD] using (kernel_fderiv ht ⟨hx, hy⟩).comp_hasDerivAt u hline

 theorem kernel_line_second {t x y a b : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    iteratedDeriv 2 (fun v : ℝ => kernel t (x + v * a) (y + v * b)) 0 =
      kernelXX t x y * a ^ 2 + 2 * kernelXY t x y * a * b + kernelXX t y x * b ^ 2 := by
  have hx' : x + (0 : ℝ) * a ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  have hy' : y + (0 : ℝ) * b ∈ Ioo (0 : ℝ) 1 := by simpa using hy
  have hne : ∀ᶠ v : ℝ in 𝓝 0, x + v * a ∈ Ioo (0 : ℝ) 1 ∧
      y + v * b ∈ Ioo (0 : ℝ) 1 := by
    have hc : ContinuousAt (fun v : ℝ => (x + v * a, y + v * b)) 0 := by fun_prop
    exact hc.preimage_mem_nhds ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hx', hy'⟩)
  have he : deriv (fun v : ℝ => kernel t (x + v * a) (y + v * b)) =ᶠ[𝓝 0]
      (fun v => kernelX t (x + v * a) (y + v * b) * a +
        kernelX t (y + v * b) (x + v * a) * b) := by
    filter_upwards [hne] with v hv
    exact (kernel_line_deriv ht hv.1 hv.2).deriv
  have hd := ((kernelX_line_deriv ht hx' hy').mul_const a).add
    ((kernelX_line_deriv ht hy' hx').mul_const b)
  have heq : kernelXY t y x = kernelXY t x y := by
    unfold kernelXY
    rw [plackett_symm ⟨by linarith [ht.1], ht.2⟩ (quantile y) (quantile x), mul_comm]
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, he.deriv_eq]
  have hdd := hd.deriv
  simp only [zero_mul, add_zero, heq] at hdd
  convert hdd using 1
  all_goals try with_reducible_and_instances rfl
  ring

 theorem kernel_second_diagonal {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (d : ℝ × ℝ) :
    iteratedFDeriv ℝ 2 (Function.uncurry (kernel t)) p (fun _ => d) =
      kernelXX t p.1 p.2 * d.1 ^ 2 + 2 * kernelXY t p.1 p.2 * d.1 * d.2 +
        kernelXX t p.2 p.1 * d.2 ^ 2 := by
  have hf : ContDiffAt ℝ 2 (Function.uncurry (kernel t)) (p + (0 : ℝ) • d) := by
    simpa using (kernel_contDiffOn ht 2).contDiffAt
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp)
  have he := iteratedDeriv_affinePath_two hf
  simp only [zero_smul, add_zero] at he
  rw [← he]
  exact kernel_line_second ht hp.1 hp.2

 theorem norm_pair_cube_le (a b : ℝ) : ‖(a, b)‖ ^ 3 ≤ |a| ^ 3 + |b| ^ 3 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total |a| |b| with h | h
  · rw [max_eq_right h]; exact le_add_of_nonneg_left (by positivity)
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (by positivity)

 theorem kernel_uniform_cubic {t η : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hη : 0 < η) (_hη' : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Icc η (1 - η) ×ˢ Icc η (1 - η),
      ∀ q ∈ Icc η (1 - η) ×ˢ Icc η (1 - η),
      |kernel t q.1 q.2 - kernel t p.1 p.2 -
        (kernelX t p.1 p.2 * (q.1 - p.1) + kernelX t p.2 p.1 * (q.2 - p.2)) -
        (1 / 2 : ℝ) * (kernelXX t p.1 p.2 * (q.1 - p.1) ^ 2 +
          2 * kernelXY t p.1 p.2 * (q.1 - p.1) * (q.2 - p.2) +
          kernelXX t p.2 p.1 * (q.2 - p.2) ^ 2)| ≤
      C * (|q.1 - p.1| ^ 3 + |q.2 - p.2| ^ 3) := by
  have hsub : Icc η (1 - η) ×ˢ Icc η (1 - η) ⊆
      Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 := by
    intro p hp
    exact ⟨⟨hη.trans_le hp.1.1, by linarith [hp.1.2]⟩,
      ⟨hη.trans_le hp.2.1, by linarith [hp.2.2]⟩⟩
  obtain ⟨C, hC0, hC⟩ := compact_cubic_taylor_bound (isOpen_Ioo.prod isOpen_Ioo)
    (isCompact_Icc.prod isCompact_Icc) ((convex_Icc η (1 - η)).prod (convex_Icc η (1 - η)))
    hsub (kernel_contDiffOn ht 3)
  refine ⟨C, hC0, ?_⟩
  intro p hp q hq
  have hb := hC p hp q hq
  rw [(kernel_fderiv ht (hsub hp)).fderiv, kernel_second_diagonal ht (hsub hp)] at hb
  change |kernel t q.1 q.2 - kernel t p.1 p.2 -
    (kernelX t p.1 p.2 * (q.1 - p.1) + kernelX t p.2 p.1 * (q.2 - p.2)) -
    (1 / 2 : ℝ) * (kernelXX t p.1 p.2 * (q.1 - p.1) ^ 2 +
      2 * kernelXY t p.1 p.2 * (q.1 - p.1) * (q.2 - p.2) +
      kernelXX t p.2 p.1 * (q.2 - p.2) ^ 2)| ≤ C * ‖q - p‖ ^ 3 at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (norm_pair_cube_le (q.1 - p.1) (q.2 - p.2)) hC0)

 theorem kernel_one_bit {t η : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y a b : ℝ,
      (∀ e : Bool, x + sign e * a ∈ Icc η (1 - η)) →
      (∀ e : Bool, y + sign e * b ∈ Icc η (1 - η)) →
      (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f *
        kernel t (x + sign e * a) (y + sign f * b)) ≤
      kernel t x y + C * (|a| ^ 3 + |b| ^ 3) := by
  obtain ⟨C, hC0, hC⟩ := kernel_uniform_cubic ht hη hη'
  refine ⟨C, hC0, ?_⟩
  intro x y a b hx hy
  have hxp : x ∈ Icc η (1 - η) := by
    have hx0 := hx false; have hx1 := hx true
    simp [sign] at hx0 hx1
    constructor <;> linarith [hx0.1, hx0.2, hx1.1, hx1.2]
  have hyp : y ∈ Icc η (1 - η) := by
    have hy0 := hy false; have hy1 := hy true
    simp [sign] at hy0 hy1
    constructor <;> linarith [hy0.1, hy0.2, hy1.1, hy1.2]
  let Q : Bool → Bool → ℝ := fun e f => kernel t x y +
    (kernelX t x y * (sign e * a) + kernelX t y x * (sign f * b)) +
    (1 / 2 : ℝ) * (kernelXX t x y * (sign e * a) ^ 2 +
      2 * kernelXY t x y * (sign e * a) * (sign f * b) +
      kernelXX t y x * (sign f * b) ^ 2) + C * (|a| ^ 3 + |b| ^ 3)
  have hpoint (e f : Bool) : kernel t (x + sign e * a) (y + sign f * b) ≤ Q e f := by
    have hb := (hC (x, y) ⟨hxp, hyp⟩ (x + sign e * a, y + sign f * b) ⟨hx e, hy f⟩)
    simp only [add_sub_cancel_left] at hb
    have he : |sign e * a| = |a| := by cases e <;> simp [sign]
    have hf : |sign f * b| = |b| := by cases f <;> simp [sign]
    rw [he, hf] at hb
    have hb' := (abs_le.mp hb).2
    dsimp [Q]
    linarith
  have hsum : (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f *
      kernel t (x + sign e * a) (y + sign f * b)) ≤
      ∑ e : Bool, ∑ f : Bool, bitPairWeight t e f * Q e f := by
    apply Finset.sum_le_sum
    intro e _
    apply Finset.sum_le_sum
    intro f _
    exact mul_le_mul_of_nonneg_left (hpoint e f)
      (bitPairWeight_nonneg ⟨by linarith [ht.1], ht.2.le⟩ e f)
  have halg : (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f * Q e f) =
      kernel t x y + (1 / 2 : ℝ) *
        (kernelXX t x y * a ^ 2 + 2 * t * kernelXY t x y * a * b + kernelXX t y x * b ^ 2) +
      C * (|a| ^ 3 + |b| ^ 3) := by
    simp only [Fintype.sum_bool, Q, bitPairWeight, sign, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [halg] at hsum
  linarith [kernel_weighted_hessian_nonpos ht x y a b]

 theorem kernel_lipschitz_x {t x x' y : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hx' : x' ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |kernel t x' y - kernel t x y| ≤ |x' - x| := by
  have hb := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z => kernel t z y) (C := 1)
    (fun z hz => (kernel_deriv_x ht hz hy).differentiableAt)
    (fun z hz => by
      rw [(kernel_deriv_x ht hz hy).deriv, Real.norm_eq_abs,
        abs_of_pos (cdf_mem_Ioo _).1]
      exact (cdf_mem_Ioo _).2.le)
    (convex_Ioo (0 : ℝ) 1) hx hx'
  simpa only [Real.norm_eq_abs, one_mul] using hb

 theorem kernel_lipschitz {t x x' y y' : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hx' : x' ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) (hy' : y' ∈ Ioo (0 : ℝ) 1) :
    |kernel t x' y' - kernel t x y| ≤ |x' - x| + |y' - y| := by
  have h1 := kernel_lipschitz_x ht hx hx' hy'
  have h2 := kernel_lipschitz_x ht hy hy' hx
  rw [kernel_symm ht y' x, kernel_symm ht y x] at h2
  calc
    _ = |(kernel t x' y' - kernel t x y') + (kernel t x y' - kernel t x y)| := by congr 1; ring
    _ ≤ |kernel t x' y' - kernel t x y'| + |kernel t x y' - kernel t x y| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitCube
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman
open scoped BigOperators
open Set Finset

 theorem section_decomposition {n : ℕ} (f : BitCube (n + 1) → ℝ) (x : BitCube n) (a : Bool) :
    f (Fin.cons a x) = midpointSection f x + sign a * slopeSection f x := by
  cases a <;> simp only [midpointSection, slopeSection, sign, Bool.false_eq_true, ↓reduceIte] <;> ring

 theorem midpointSection_mem {n : ℕ} {f : BitCube (n + 1) → ℝ} {l u : ℝ}
    (hf : ∀ x, f x ∈ Icc l u) (x : BitCube n) : midpointSection f x ∈ Icc l u := by
  have h0 := hf (Fin.cons false x)
  have h1 := hf (Fin.cons true x)
  dsimp [midpointSection]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

 theorem corrAverage_mul_const (t c : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y * c) = corrAverage t n F * c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverage, ← mul_assoc, ← Finset.sum_mul, ih]

 theorem corrAverage_const_mul (t c : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => c * F x y) = c * corrAverage t n F := by
  simpa only [mul_comm] using corrAverage_mul_const t c n F

 theorem corrAverage_snd (t : ℝ) (n : ℕ) (f : BitCube n → ℝ) :
    corrAverage t n (fun _ y => f y) = 𝔼 y, f y := by
  induction n with
  | zero => exact (expect_zero_cube f).symm
  | succ n ih =>
    have hp (y : BitCube n) :
        (∑ a : Bool, ∑ b : Bool, bitPairWeight t a b * f (Fin.cons b y)) = midpointSection f y := by
      simp only [Fintype.sum_bool, bitPairWeight, sign, Bool.false_eq_true, ↓reduceIte, midpointSection]
      ring
    simp only [corrAverage, hp]
    rw [ih, expect_section]

 theorem finite_bellman_tensorization {t C l u : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (J : ℝ → ℝ → ℝ)
    (hJ : ∀ x y a b : ℝ,
      (∀ e : Bool, x + sign e * a ∈ Icc l u) →
      (∀ e : Bool, y + sign e * b ∈ Icc l u) →
      (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f * J (x + sign e * a) (y + sign f * b)) ≤
      J x y + C * (|a| ^ 3 + |b| ^ 3))
    (n : ℕ) (f g : BitCube n → ℝ) (hf : ∀ x, f x ∈ Icc l u) (hg : ∀ x, g x ∈ Icc l u) :
    corrAverage t n (fun x y => J (f x) (g y)) ≤
      J (𝔼 x, f x) (𝔼 y, g y) + C * (cubicCost n f + cubicCost n g) := by
  induction n with
  | zero => simp only [corrAverage, cubicCost, expect_zero_cube, add_zero, mul_zero, le_refl]
  | succ n ih =>
    have hlocal (x y : BitCube n) :
        (∑ a : Bool, ∑ b : Bool, bitPairWeight t a b * J (f (Fin.cons a x)) (g (Fin.cons b y))) ≤
        J (midpointSection f x) (midpointSection g y) +
          C * (|slopeSection f x| ^ 3 + |slopeSection g y| ^ 3) := by
      simpa only [← section_decomposition] using hJ (midpointSection f x) (midpointSection g y)
        (slopeSection f x) (slopeSection g y)
        (fun e => by rw [← section_decomposition]; exact hf _)
        (fun e => by rw [← section_decomposition]; exact hg _)
    have hb := corrAverage_mono ht n hlocal
    rw [corrAverage_add, corrAverage_const_mul, corrAverage_add, corrAverage_fst, corrAverage_snd] at hb
    have hi := ih (midpointSection f) (midpointSection g) (midpointSection_mem hf) (midpointSection_mem hg)
    rw [expect_section f, expect_section g]
    simp only [corrAverage, cubicCost]
    linarith

 theorem gradient_cons_zero {n : ℕ} (f : BitCube (n + 1) → ℝ) (a : Bool) (x : BitCube n) :
    gradient f 0 (Fin.cons a x) = sign a * slopeSection f x := by
  cases a <;> simp [gradient, sign, slopeSection] ; ring

 theorem gradient_midpoint {n : ℕ} (f : BitCube (n + 1) → ℝ) (i : Fin n) (x : BitCube n) :
    gradient (midpointSection f) i x = midpointSection (gradient f i.succ) x := by
  simp only [gradient, midpointSection, Fin.cons_succ, ← Fin.cons_update]
  ring

 theorem abs_midpoint_cube_le (a b : ℝ) :
    |(a + b) / 2| ^ 3 ≤ (|a| ^ 3 + |b| ^ 3) / 2 := by
  have h := abs_add_le a b
  have hpow : |a + b| ^ 3 ≤ (|a| + |b|) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h 3
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_pow]
  have hm := mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) (sq_nonneg (|a| - |b|))
  nlinarith

 theorem midpoint_cubic_contract {n : ℕ} (f : BitCube (n + 1) → ℝ) :
    (𝔼 x, |midpointSection f x| ^ 3) ≤ 𝔼 x, |f x| ^ 3 := by
  rw [expect_section (fun x => |f x| ^ 3)]
  apply Finset.expect_le_expect
  intro x _
  exact abs_midpoint_cube_le _ _

 theorem gradient_zero_cubic {n : ℕ} (f : BitCube (n + 1) → ℝ) :
    (𝔼 x, |gradient f 0 x| ^ 3) = 𝔼 x, |slopeSection f x| ^ 3 := by
  rw [expect_section]
  apply Finset.expect_congr rfl
  intro x _
  simp [midpointSection, gradient_cons_zero, sign]

 theorem cubicCost_le_gradients (n : ℕ) (f : BitCube n → ℝ) :
    cubicCost n f ≤ ∑ i, 𝔼 x, |gradient f i x| ^ 3 := by
  induction n with
  | zero => simp [cubicCost]
  | succ n ih =>
    rw [cubicCost, Fin.sum_univ_succ, gradient_zero_cubic]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ i, 𝔼 x, |gradient (midpointSection f) i x| ^ 3 := ih _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        simp only [gradient_midpoint]
        exact midpoint_cubic_contract _

 theorem gradient_lipschitz {n : ℕ} (F : ℝ → ℝ)
    (hF : ∀ a b, |F a - F b| ≤ |a - b|) (f : BitCube n → ℝ) (i : Fin n) (x : BitCube n) :
    |gradient (fun x => F (f x)) i x| ≤ |gradient f i x| := by
  simp only [gradient, abs_div]
  exact div_le_div_of_nonneg_right (hF _ _) (abs_nonneg _)

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Degree
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real Walsh analysis on finite Boolean cubes. The basis and inversion
identities are proved from the explicit coordinate characters. -/

noncomputable section

namespace OptimalMaxCut.Analytic

open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad

section NoiseIdentities

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact diagonalization of ordinary bit noise. -/
theorem coefficient_noise (u : ℝ) (f : Cube I → ℝ) (a : Cube I) :
    coefficient (noise u f) a = u ^ degree a * coefficient f a := by
  classical
  unfold coefficient noise
  simp only [Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_expect, walsh_orthogonality]
  simp [coefficient]

/-- The finite energy bound used for the dimension-independent cutoff step. -/
theorem spectral_energy_le_one (f : Cube I → ℝ)
    (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) :
    (∑ s, coefficient f s ^ 2) ≤ 1 := by
  rw [walsh_parseval]
  apply Finset.expect_le Finset.univ_nonempty
  intro x _
  obtain ⟨hl, hu⟩ := hf x
  nlinarith

theorem stability_noise (t u : ℝ) (f : Cube I → ℝ) :
    stability t (noise u f) =
      ∑ s, t ^ degree s * u ^ (2 * degree s) * coefficient f s ^ 2 := by
  classical
  unfold stability
  simp_rw [coefficient_noise, mul_pow, pow_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The exact error integrand, before replacing it by any uniform bound. -/
theorem stability_sub_noise (t u : ℝ) (f : Cube I → ℝ) :
    stability t f - stability t (noise u f) =
      ∑ s, (t ^ degree s * (1 - u ^ (2 * degree s))) * coefficient f s ^ 2 := by
  classical
  rw [stability_noise, stability, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- A uniform multiplier bound gives a dimension-independent stability error. -/
theorem stability_sub_noise_le (t u η : ℝ) (f : Cube I → ℝ)
    (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) (hη : 0 ≤ η)
    (h : ∀ j : ℕ, t ^ j * (1 - u ^ (2 * j)) ≤ η) :
    stability t f - stability t (noise u f) ≤ η := by
  rw [stability_sub_noise]
  calc
    _ ≤ ∑ s, η * coefficient f s ^ 2 :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (h _) (sq_nonneg _)
    _ = η * ∑ s, coefficient f s ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left (spectral_energy_le_one f hf) hη
    _ = η := mul_one _

/-- Exactly preservation of the probability-normalized mean. -/
theorem noise_mean (u : ℝ) (f : Cube I → ℝ) :
    (𝔼 x, noise u f x) = 𝔼 x, f x := by
  simpa [coefficient] using coefficient_noise u f (fun _ => false)

omit [DecidableEq I] in
lemma pow_degree (u : ℝ) (s : Cube I) :
    u ^ degree s = ∏ i, if s i = true then u else 1 := by
  classical
  simp [Finset.prod_ite, degree]

/-- The product kernel of independent bit noise, not an assumed operator. -/
theorem walsh_noise_kernel (u : ℝ) (x y : Cube I) :
    (∑ s, u ^ degree s * walsh s x * walsh s y) =
      ∏ i, (1 + u * bitSign (x i) * bitSign (y i)) := by
  classical
  have hs (s : Cube I) : u ^ degree s * walsh s x * walsh s y =
      ∏ i, if s i = true then u * bitSign (x i) * bitSign (y i) else 1 := by
    rw [pow_degree, walsh, walsh, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases h : s i <;> simp [bitSign]
  simp_rw [hs]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) =>
    if b = true then u * bitSign (x i) * bitSign (y i) else 1)]
  apply Finset.prod_congr rfl
  intro i _
  simp [add_comm]

theorem noise_kernel (u : ℝ) (f : Cube I → ℝ) (x : Cube I) :
    noise u f x =
      𝔼 y, f y * ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) := by
  classical
  unfold noise coefficient
  simp_rw [Finset.mul_expect, Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro y _
  calc
    _ = f y * (∑ s, u ^ degree s * walsh s y * walsh s x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by rw [walsh_noise_kernel]

/-- Normalization of the actual bit-noise kernel, for every real multiplier. -/
theorem noise_kernel_mass (u : ℝ) (x : Cube I) :
    (𝔼 y : Cube I, ∏ i, (1 + u * bitSign (y i) * bitSign (x i))) = 1 := by
  have h := noise_kernel u (fun _ : Cube I => (1 : ℝ)) x
  simpa using h.symm

omit [DecidableEq I] in
/-- The positivity restriction needed to make the kernel a probability law. -/
theorem noise_kernel_nonneg (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (x y : Cube I) : 0 ≤ ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) := by
  apply Finset.prod_nonneg
  intro i _
  cases hx : x i <;> cases hy : y i <;> simp [bitSign] <;> linarith

theorem noise_bounded (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (f : Cube I → ℝ) (hf : ∀ x, -1 ≤ f x ∧ f x ≤ 1) :
    ∀ x, -1 ≤ noise u f x ∧ noise u f x ≤ 1 := by
  intro x
  rw [noise_kernel]
  have hmass := noise_kernel_mass u x
  constructor
  · calc
      -1 = 𝔼 y, (-1 : ℝ) * ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) := by
        rw [← Finset.mul_expect, hmass, mul_one]
      _ ≤ _ := Finset.expect_le_expect fun y _ =>
        mul_le_mul_of_nonneg_right (hf y).1 (noise_kernel_nonneg u hu hu1 x y)
  · calc
      _ ≤ 𝔼 y, (1 : ℝ) * ∏ i, (1 + u * bitSign (y i) * bitSign (x i)) :=
        Finset.expect_le_expect fun y _ =>
          mul_le_mul_of_nonneg_right (hf y).2 (noise_kernel_nonneg u hu hu1 x y)
      _ = 1 := by simpa using hmass

end NoiseIdentities

theorem nat_mul_pow_mul_one_sub_le_one (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (j : ℕ) : (j : ℝ) * t ^ j * (1 - t) ≤ 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp : t ^ (j + 1) ≤ 1 := pow_le_one₀ ht ht1
    calc
      ((j + 1 : ℕ) : ℝ) * t ^ (j + 1) * (1 - t) =
          t * ((j : ℝ) * t ^ j * (1 - t)) + t ^ (j + 1) * (1 - t) := by
            push_cast
            rw [pow_succ]
            ring
      _ ≤ t * 1 + 1 * (1 - t) := add_le_add
        (mul_le_mul_of_nonneg_left ih ht)
        (mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr ht1))
      _ = 1 := by ring

/-- Explicit control of the entire noise-stability multiplier sequence. -/
theorem multiplier_le (t u : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (j : ℕ) :
    t ^ j * (1 - u ^ (2 * j)) ≤ 2 * (1 - u) / (1 - t) := by
  have hber := one_add_mul_sub_le_pow (show -1 ≤ u by linarith) (2 * j)
  have hbern : 1 - u ^ (2 * j) ≤ (2 * (j : ℝ)) * (1 - u) := by
    push_cast at hber
    nlinarith
  have htp : 0 ≤ t ^ j := pow_nonneg ht j
  have hju := nat_mul_pow_mul_one_sub_le_one t ht ht1.le j
  have htm : 0 < 1 - t := sub_pos.mpr ht1
  apply (le_div_iff₀ htm).mpr
  calc
    t ^ j * (1 - u ^ (2 * j)) * (1 - t) ≤
        t ^ j * (2 * (j : ℝ) * (1 - u)) * (1 - t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbern htp) htm.le
    _ = (2 * (1 - u)) * ((j : ℝ) * t ^ j * (1 - t)) := by ring
    _ ≤ (2 * (1 - u)) * 1 := mul_le_mul_of_nonneg_left hju (by linarith)
    _ = 2 * (1 - u) := by ring

theorem exists_uniform_noise_error (t ξ : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hξ : 0 < ξ) : ∃ u : ℝ, 0 < u ∧ u < 1 ∧
      ∀ j : ℕ, t ^ j * (1 - u ^ (2 * j)) ≤ ξ / 2 := by
  let e : ℝ := min (1 / 2) (ξ * (1 - t) / 4)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have hehalf : e ≤ 1 / 2 := min_le_left _ _
  have heξ : e ≤ ξ * (1 - t) / 4 := min_le_right _ _
  refine ⟨1 - e, by linarith, by linarith, ?_⟩
  intro j
  calc
    _ ≤ 2 * (1 - (1 - e)) / (1 - t) :=
      multiplier_le t (1 - e) ht ht1 (by linarith) (by linarith) j
    _ ≤ ξ / 2 := by
      apply (div_le_iff₀ (sub_pos.mpr ht1)).mpr
      linarith

/-- Degree cutoff for the influence tail, with no dimension dependence. -/
theorem exists_influence_tail_cutoff (u δ : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hδ : 0 < δ) : ∃ K : ℕ, 1 ≤ K ∧ u ^ (2 * (K + 1)) ≤ δ / 2 := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity) hu1
  refine ⟨N + 1, by omega, ?_⟩
  exact le_trans (pow_le_pow_of_le_one hu hu1.le (by omega : N ≤ 2 * (N + 1 + 1)))
    hN.le

end OptimalMaxCut.Analytic

end -- noncomputable Walsh/analytic section

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Gadgets_Polynomial
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.BooleanFourthMoment
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad

 theorem sum_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    ∑ x, F x = ∑ b : Bool, ∑ y : Cube (Fin n), F (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  exact Fintype.sum_prod_type _

 theorem expect_cube_succ {n : ℕ} (F : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, F x) = 𝔼 b : Bool, 𝔼 y : Cube (Fin n), F (Fin.cons b y) := by
  calc
    _ = 𝔼 p : Bool × Cube (Fin n), F (Fin.cons p.1 p.2) :=
      (Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) _ F (fun _ => rfl)).symm
    _ = _ := by rw [← Finset.univ_product_univ, Finset.expect_product]

 theorem expect_bool (F : Bool → ℝ) : (𝔼 b, F b) = (F false + F true) / 2 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [add_comm]

 theorem energy_nonneg {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    0 ≤ energy c := by
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg _ (sq_nonneg _)
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> norm_num

 theorem walsh_cons {n : ℕ} (s x : Cube (Fin n)) (a b : Bool) :
    walsh (Fin.cons a s) (Fin.cons b x) = (if a then bitSign b else 1) * walsh s x := by
  cases a <;> simp [walsh, Fin.prod_univ_succ, bitSign]

 theorem polynomial_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) (x : Cube (Fin n)) (b : Bool) :
    polynomial c (Fin.cons b x) = polynomial (fun s => c (Fin.cons false s)) x +
      bitSign b * polynomial (fun s => c (Fin.cons true s)) x := by
  unfold polynomial
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [walsh_cons, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

 theorem energy_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    energy c = energy (fun s => c (Fin.cons false s)) +
      3 * energy (fun s => c (Fin.cons true s)) := by
  unfold energy
  rw [sum_cube_succ, Fintype.sum_bool]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, ↓reduceIte,
    one_mul, mul_assoc]
  rw [← Finset.mul_sum]
  ring

 theorem fourth_moment_cons {n : ℕ} (c : Cube (Fin (n + 1)) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) =
      (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 4) +
      6 * (𝔼 x, polynomial (fun s => c (Fin.cons false s)) x ^ 2 *
        polynomial (fun s => c (Fin.cons true s)) x ^ 2) +
      (𝔼 x, polynomial (fun s => c (Fin.cons true s)) x ^ 4) := by
  rw [expect_cube_succ, Finset.expect_comm]
  simp_rw [expect_bool]
  simp only [polynomial_cons, bitSign, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul]
  simp_rw [show ∀ a b : ℝ, ((a + b) ^ 4 + (a + -b) ^ 4) / 2 = a ^ 4 + 6 * (a ^ 2 * b ^ 2) + b ^ 4 by
    intro a b; ring]
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect]

 theorem fourth_moment_bound (n : ℕ) (c : Cube (Fin n) → ℝ) :
    (𝔼 x, polynomial c x ^ 4) ≤ energy c ^ 2 := by
  induction n with
  | zero => simp [polynomial, energy, walsh]; exact le_of_eq (by ring)
  | succ n ih =>
    let c₀ : Cube (Fin n) → ℝ := fun s => c (Fin.cons false s)
    let c₁ : Cube (Fin n) → ℝ := fun s => c (Fin.cons true s)
    have h₀ := ih c₀
    have h₁ := ih c₁
    have he₀ := energy_nonneg c₀
    have he₁ := energy_nonneg c₁
    have hm₀ : 0 ≤ 𝔼 x, polynomial c₀ x ^ 4 := by positivity
    have hm₁ : 0 ≤ 𝔼 x, polynomial c₁ x ^ 4 := by positivity
    have hc := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
      (fun x => polynomial c₀ x ^ 2) (fun x => polynomial c₁ x ^ 2)
    simp only [← pow_mul, Nat.reduceMul] at hc
    have hc' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ^ 2 ≤
        (energy c₀ * energy c₁) ^ 2 := by
      calc _ ≤ _ := hc
           _ ≤ energy c₀ ^ 2 * energy c₁ ^ 2 := mul_le_mul h₀ h₁ hm₁ (sq_nonneg _)
           _ = _ := by ring
    have hc'' : (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) ≤ energy c₀ * energy c₁ :=
      (sq_le_sq₀ (by positivity) (mul_nonneg he₀ he₁)).mp hc'
    rw [fourth_moment_cons, energy_cons]
    change (𝔼 x, polynomial c₀ x ^ 4) +
      6 * (𝔼 x, polynomial c₀ x ^ 2 * polynomial c₁ x ^ 2) +
      (𝔼 x, polynomial c₁ x ^ 4) ≤ (energy c₀ + 3 * energy c₁) ^ 2
    nlinarith [sq_nonneg (energy c₁)]

 theorem weight_eq_degree {I : Type*} [Fintype I] [DecidableEq I] (s : Cube I) :
    (∏ i, if s i then (3 : ℝ) else 1) = 3 ^ Analytic.degree s := by
  simp [Finset.prod_ite, Analytic.degree]

 theorem energy_truncated {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (c : Cube I → ℝ) (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    energy c ≤ 3 ^ K * ∑ s, c s ^ 2 := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [weight_eq_degree]
  by_cases hs : Analytic.degree s ≤ K
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hs) (sq_nonneg _)
  · rw [hc s (lt_of_not_ge hs)]; simp

 theorem coefficient_polynomial {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (a : Cube I) : coefficient (polynomial c) a = c a := by
  unfold coefficient polynomial
  simp only [Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_expect, walsh_orthogonality]
  simp

 theorem polynomial_second_moment {I : Type*} [Fintype I] [DecidableEq I] (c : Cube I → ℝ) :
    (𝔼 x, polynomial c x ^ 2) = ∑ s, c s ^ 2 := by
  rw [← walsh_parseval]
  simp only [coefficient_polynomial]

 theorem degree_fourth_moment_bound {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    (𝔼 x, polynomial c x ^ 4) ≤ (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 := by
  rw [polynomial_second_moment]
  exact (fourth_moment_bound n c).trans
    ((sq_le_sq₀ (energy_nonneg c) (by positivity)).mpr (energy_truncated K c hc))

 theorem degree_third_moment_bound {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsmall : (𝔼 x, polynomial c x ^ 2) ≤ τ ^ 2) :
    (𝔼 x, |polynomial c x| ^ 3) ≤ 3 ^ K * τ * (𝔼 x, polynomial c x ^ 2) := by
  have hsecond : 0 ≤ 𝔼 x, polynomial c x ^ 2 := by positivity
  have hfourth := degree_fourth_moment_bound c hc
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => |polynomial c x|) (fun x => polynomial c x ^ 2)
  have hp (a : ℝ) : |a| * a ^ 2 = |a| ^ 3 := by rw [← sq_abs]; ring
  simp_rw [hp, sq_abs, ← pow_mul, Nat.reduceMul] at hCS
  have hbound : (𝔼 x, |polynomial c x| ^ 3) ^ 2 ≤
      (3 ^ K * τ * (𝔼 x, polynomial c x ^ 2)) ^ 2 := by
    calc
      _ ≤ (𝔼 x, polynomial c x ^ 2) * (𝔼 x, polynomial c x ^ 4) := hCS
      _ ≤ (𝔼 x, polynomial c x ^ 2) * (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourth hsecond
      _ = (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 * (𝔼 x, polynomial c x ^ 2) := by ring
      _ ≤ (3 ^ K * (𝔼 x, polynomial c x ^ 2)) ^ 2 * τ ^ 2 :=
        mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hbound

 theorem walsh_flip {I : Type*} [Fintype I] [DecidableEq I]
    (s x : Cube I) (i : I) :
    walsh s (Function.update x i (!x i)) = (if s i then -1 else 1) * walsh s x := by
  classical
  have hp (j : I) : bitSign (s j && Function.update x i (!x i) j) =
      (if j = i then (if s i then (-1 : ℝ) else 1) else 1) * bitSign (s j && x j) := by
    by_cases h : j = i
    · subst j; cases s i <;> cases x i <;> simp [bitSign]
    · simp [h]
  simp only [walsh, hp, Finset.prod_mul_distrib]
  simp

 theorem polynomial_diff {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) (i : I) :
    discreteDiff (polynomial c) i = polynomial (fun s => if s i then c s else 0) := by
  funext x
  simp only [discreteDiff, polynomial, walsh_flip, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  cases s i <;> simp

 theorem total_diff_second {I : Type*} [Fintype I] [DecidableEq I]
    (c : Cube I → ℝ) :
    (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) =
      ∑ s, (Analytic.degree s : ℝ) * c s ^ 2 := by
  simp only [polynomial_diff, polynomial_second_moment]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [ite_pow, zero_pow (by omega : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp [Analytic.degree]

 theorem total_diff_second_truncated {I : Type*} [Fintype I] [DecidableEq I]
    (K : ℕ) (c : Cube I → ℝ) (hc : ∀ s, K < Analytic.degree s → c s = 0) :
    (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤
      K * (𝔼 x, polynomial c x ^ 2) := by
  rw [total_diff_second, polynomial_second_moment, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : Analytic.degree s ≤ K
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg _)
  · rw [hc s (lt_of_not_ge hs)]; simp

 theorem total_diff_third_truncated {n K : ℕ} (c : Cube (Fin n) → ℝ)
    (hc : ∀ s, K < Analytic.degree s → c s = 0) {τ : ℝ} (hτ : 0 ≤ τ)
    (hsmall : ∀ i, (𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤ τ ^ 2) :
    (∑ i, 𝔼 x, |discreteDiff (polynomial c) i x| ^ 3) ≤
      3 ^ K * τ * K * (𝔼 x, polynomial c x ^ 2) := by
  calc
    _ ≤ ∑ i, 3 ^ K * τ * (𝔼 x, discreteDiff (polynomial c) i x ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hsmall i
      rw [polynomial_diff] at hi ⊢
      exact degree_third_moment_bound _ (fun s hs => by rw [hc s hs]; split_ifs <;> rfl)
        hτ hi
    _ = 3 ^ K * τ * (∑ i, 𝔼 x, discreteDiff (polynomial c) i x ^ 2) := by rw [Finset.mul_sum]
    _ ≤ 3 ^ K * τ * (K * (𝔼 x, polynomial c x ^ 2)) :=
      mul_le_mul_of_nonneg_left (total_diff_second_truncated K c hc) (by positivity)
    _ = _ := by ring

end OptimalMaxCut.BooleanFourthMoment

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Clip
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.MISProof
open scoped BigOperators
open Finset Set MaxCutGames.Foundations.Hastad Analytic BooleanFourthMoment GaussianBellman

 theorem degree_cons {n : ℕ} (a : Bool) (s : Cube (Fin n)) :
    degree (Fin.cons a s) = degree s + if a then 1 else 0 := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  cases a <;> simp [Nat.add_comm]

 theorem corrAverage_walsh (t : ℝ) (n : ℕ) (s r : Cube (Fin n)) :
    corrAverage t n (fun x y => walsh s x * walsh r y) =
      if s = r then t ^ degree s else 0 := by
  induction n with
  | zero => simp [corrAverage, walsh, degree, Subsingleton.elim s r]
  | succ n ih =>
    obtain ⟨⟨a, s⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective s
    obtain ⟨⟨b, r⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).surjective r
    change corrAverage t (n + 1) (fun x y => walsh (Fin.cons a s) x * walsh (Fin.cons b r) y) =
      if (Fin.cons a s : Cube (Fin (n + 1))) = Fin.cons b r then t ^ degree (Fin.cons a s) else 0
    have hp (x y : Cube (Fin n)) :
        (∑ e : Bool, ∑ f : Bool, bitPairWeight t e f *
          (walsh (Fin.cons a s) (Fin.cons e x) * walsh (Fin.cons b r) (Fin.cons f y))) =
        (if a = b then (if a then t else 1) else 0) * (walsh s x * walsh r y) := by
      cases a <;> cases b <;>
        simp only [Fintype.sum_bool, bitPairWeight, sign, walsh_cons, bitSign,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
    simp only [corrAverage, hp, corrAverage_const_mul, ih, Fin.cons_inj, degree_cons]
    cases a <;> cases b <;> by_cases h : s = r <;> simp [h, pow_succ, mul_comm]

 theorem corrAverage_polynomial (t : ℝ) (n : ℕ) (c d : Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => polynomial c x * polynomial d y) =
      ∑ s, t ^ degree s * c s * d s := by
  have hp (x y : Cube (Fin n)) : polynomial c x * polynomial d y =
      ∑ s, ∑ r, (c s * d r) * (walsh s x * walsh r y) := by
    simp only [polynomial]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [hp, corrAverage_sum, corrAverage_const_mul, corrAverage_walsh]
  apply Finset.sum_congr rfl
  intro s _
  simp [mul_ite]
  ring

 theorem corrAverage_stability (t : ℝ) (n : ℕ) (f : Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => f x * f y) = stability t f := by
  have hf : polynomial (coefficient f) = f := funext (walsh_inversion f)
  rw [← hf, corrAverage_polynomial]
  simp only [stability, coefficient_polynomial]
  apply Finset.sum_congr rfl
  intro s _
  ring

 theorem clip_mem (x : ℝ) : clip x ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

 theorem clip_eq {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : clip x = x := by
  rw [clip, min_eq_right hx.2, max_eq_right hx.1]

 theorem clip_lipschitz (a b : ℝ) : |clip a - clip b| ≤ |a - b| := by
  have h1 := le_abs_self (a - b)
  have h2 := neg_le_abs (a - b)
  unfold clip
  simp only [max_def, min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

 theorem interiorClip_mem {η : ℝ} (_hη : 0 ≤ η) (hη' : η ≤ 1 / 2) (x : ℝ) :
    interiorClip η x ∈ Icc η (1 - η) := by
  have hx := clip_mem x
  have hl := mul_nonneg (by linarith : 0 ≤ 1 - 2 * η) (by linarith [hx.1] : 0 ≤ clip x + 1)
  have hu := mul_le_mul_of_nonneg_left (by linarith [hx.2] : clip x + 1 ≤ 2)
    (by linarith : 0 ≤ 1 - 2 * η)
  unfold interiorClip
  constructor <;> linarith

 theorem interiorClip_lipschitz {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2) (a b : ℝ) :
    |interiorClip η a - interiorClip η b| ≤ |a - b| := by
  have hc : 0 ≤ (1 - 2 * η) / 2 := by linarith
  have hc' : (1 - 2 * η) / 2 ≤ 1 := by linarith
  have he : interiorClip η a - interiorClip η b = (1 - 2 * η) / 2 * (clip a - clip b) := by
    unfold interiorClip; ring
  rw [he, abs_mul, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left (clip_lipschitz a b) hc).trans
    (by simpa using mul_le_mul_of_nonneg_right hc' (abs_nonneg (a - b)))

 theorem interiorClip_approx {η b : ℝ} (hη : 0 ≤ η) (hb : b ∈ Icc (-1 : ℝ) 1) (a : ℝ) :
    |interiorClip η a - (b + 1) / 2| ≤ |a - b| + η := by
  have he : interiorClip η a - (b + 1) / 2 = (clip a - b) / 2 + (-η * clip a) := by
    unfold interiorClip; ring
  have hc : |clip a| ≤ 1 := abs_le.mpr (clip_mem a)
  have hab : |clip a - b| ≤ |a - b| := by
    simpa only [clip_eq hb] using clip_lipschitz a b
  rw [he]
  calc
    _ ≤ |(clip a - b) / 2| + |-η * clip a| := abs_add_le _ _
    _ = |clip a - b| / 2 + η * |clip a| := by
      rw [abs_div, abs_mul, abs_neg, abs_of_nonneg hη]; norm_num
    _ ≤ |a - b| / 2 + η * 1 := add_le_add (by linarith) (mul_le_mul_of_nonneg_left hc hη)
    _ ≤ _ := by linarith [abs_nonneg (a - b)]

 theorem mean_abs_diff_le {n : ℕ} (f g : BitCube n → ℝ) :
    |(𝔼 x, f x) - (𝔼 x, g x)| ≤ 𝔼 x, |f x - g x| := by
  rw [← Finset.expect_sub_distrib]
  apply abs_le.mpr
  constructor
  · rw [← Finset.expect_neg_distrib]
    exact Finset.expect_le_expect (fun x _ => neg_le_of_abs_le (le_refl |f x - g x|))
  · exact Finset.expect_le_expect (fun x _ => le_abs_self _)

 theorem correlation_diff_le {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {n : ℕ}
    (f g : BitCube n → ℝ) (hf : ∀ x, f x ∈ Icc (0 : ℝ) 1) (hg : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    corrAverage t n (fun x y => f x * f y) ≤
      corrAverage t n (fun x y => g x * g y) + 2 * (𝔼 x, |f x - g x|) := by
  have hp (x y : BitCube n) : f x * f y ≤ g x * g y + |f x - g x| + |f y - g y| := by
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (f x - g x)) (hf y).1
    have h2 := mul_le_mul_of_nonneg_left (hf y).2 (abs_nonneg (f x - g x))
    have h3 := mul_le_mul_of_nonneg_left (le_abs_self (f y - g y)) (hg x).1
    have h4 := mul_le_mul_of_nonneg_right (hg x).2 (abs_nonneg (f y - g y))
    nlinarith
  have hh := corrAverage_mono ht n hp
  rw [corrAverage_add, corrAverage_add, corrAverage_fst, corrAverage_snd] at hh
  linarith

 theorem centered_half_correlation (t : ℝ) (n : ℕ) (h : BitCube n → ℝ) (hm : (𝔼 x, h x) = 0) :
    4 * corrAverage t n (fun x y => ((h x + 1) / 2) * ((h y + 1) / 2)) - 1 = stability t h := by
  have hp (x y : BitCube n) : ((h x + 1) / 2) * ((h y + 1) / 2) =
      (h x * h y + h x + h y + 1) * (1 / 4) := by ring
  simp_rw [hp]
  rw [corrAverage_mul_const, corrAverage_add, corrAverage_add, corrAverage_add,
    corrAverage_fst, corrAverage_fst, corrAverage_snd, corrAverage_stability, hm,
    Fintype.expect_const]
  ring

 theorem smoothedTrunc_high {n K : ℕ} (u : ℝ) (h : BitCube n → ℝ)
    (s : BitCube n) (hs : K < degree s) : smoothedTruncCoeff K u h s = 0 := by
  simp [smoothedTruncCoeff, not_le.mpr hs]

 theorem smoothedTrunc_sq_le {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (s : BitCube n) : smoothedTruncCoeff K u h s ^ 2 ≤ coefficient h s ^ 2 := by
  unfold smoothedTruncCoeff
  split_ifs
  · rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (pow_nonneg hu.1 _) (pow_le_one₀ hu.1 hu.2))
      (sq_nonneg _)).trans_eq (one_mul _)
  · simpa only [zero_pow (by omega : 2 ≠ 0)] using sq_nonneg (coefficient h s)

 theorem smoothedTrunc_second_le {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) :
    (𝔼 x, polynomial (smoothedTruncCoeff K u h) x ^ 2) ≤ 1 := by
  rw [polynomial_second_moment]
  exact (Finset.sum_le_sum (fun s _ => smoothedTrunc_sq_le hu h s)).trans (spectral_energy_le_one h hh)

 theorem smoothedTrunc_diff_second {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (i : Fin n) :
    (𝔼 x, discreteDiff (polynomial (smoothedTruncCoeff K u h)) i x ^ 2) ≤ cutoffInfluence K i h := by
  rw [polynomial_diff, polynomial_second_moment]
  unfold cutoffInfluence
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro s _
  by_cases hi : s i = true
  · simp only [hi, ↓reduceIte, true_and]
    by_cases hs : degree s ≤ K
    · rw [ite_eq_left hs]; exact smoothedTrunc_sq_le hu h s
    · simp [smoothedTruncCoeff, hs]
  · simp [hi]

 theorem coefficient_sub {n : ℕ} (f g : BitCube n → ℝ) (s : BitCube n) :
    coefficient (fun x => f x - g x) s = coefficient f s - coefficient g s := by
  simp only [coefficient, sub_mul, Finset.expect_sub_distrib]

 theorem smoothedTrunc_tail_second {n K : ℕ} {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) :
    (𝔼 x, (polynomial (smoothedTruncCoeff K u h) x - noise u h x) ^ 2) ≤ u ^ (2 * (K + 1)) := by
  rw [← walsh_parseval]
  simp only [coefficient_sub, coefficient_polynomial, coefficient_noise]
  calc
    _ ≤ ∑ s, u ^ (2 * (K + 1)) * coefficient h s ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : degree s ≤ K
      · simp only [smoothedTruncCoeff, ite_eq_left hs, sub_self, zero_pow (by omega : 2 ≠ 0)]
        exact mul_nonneg (pow_nonneg hu.1 _) (sq_nonneg _)
      · have hd : 2 * (K + 1) ≤ degree s * 2 := by omega
        have hp := pow_le_pow_of_le_one hu.1 hu.2 hd
        simp only [smoothedTruncCoeff, ite_eq_right hs, zero_sub, neg_sq, mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = u ^ (2 * (K + 1)) * ∑ s, coefficient h s ^ 2 := (Finset.mul_sum ..).symm
    _ ≤ u ^ (2 * (K + 1)) * 1 := mul_le_mul_of_nonneg_left (spectral_energy_le_one h hh) (pow_nonneg hu.1 _)
    _ = _ := mul_one _

 theorem mean_abs_le_of_second {n : ℕ} (f : BitCube n → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : (𝔼 x, f x ^ 2) ≤ ε ^ 2) : (𝔼 x, |f x|) ≤ ε := by
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ (fun x => |f x|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs, Fintype.expect_const] at hCS
  exact (sq_le_sq₀ (by positivity) hε).mp (hCS.trans hf)

 theorem smoothedTrunc_tail_first {n K : ℕ} {u ε : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hε : 0 ≤ ε) (htail : u ^ (2 * (K + 1)) ≤ ε ^ 2)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) :
    (𝔼 x, |polynomial (smoothedTruncCoeff K u h) x - noise u h x|) ≤ ε :=
  mean_abs_le_of_second _ hε ((smoothedTrunc_tail_second hu h hh).trans htail)

 theorem clipped_polynomial_bellman {t η : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (hη : 0 < η) (hη' : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n K : ℕ) (c : BitCube n → ℝ) (τ : ℝ), 0 ≤ τ →
      (∀ s, K < degree s → c s = 0) →
      (𝔼 x, polynomial c x ^ 2) ≤ 1 →
      (∀ i, (𝔼 x, discreteDiff (polynomial c) i x ^ 2) ≤ τ ^ 2) →
      corrAverage t n (fun x y => interiorClip η (polynomial c x) * interiorClip η (polynomial c y)) ≤
        kernel t (𝔼 x, interiorClip η (polynomial c x)) (𝔼 x, interiorClip η (polynomial c x)) +
          2 * C * (3 ^ K * τ * K) := by
  obtain ⟨C, hC0, hC⟩ := kernel_one_bit ht hη hη'
  refine ⟨C, hC0, ?_⟩
  intro n K c τ hτ hc hsecond hsmall
  let F : BitCube n → ℝ := fun x => interiorClip η (polynomial c x)
  have hcost : cubicCost n F ≤ 3 ^ K * τ * K := by
    calc
      _ ≤ ∑ i, 𝔼 x, |gradient F i x| ^ 3 := cubicCost_le_gradients n F
      _ ≤ ∑ i, 𝔼 x, |discreteDiff (polynomial c) i x| ^ 3 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.expect_le_expect
        intro x _
        exact pow_le_pow_left₀ (abs_nonneg _)
          (gradient_lipschitz (interiorClip η) (interiorClip_lipschitz hη.le hη') (polynomial c) i x) 3
      _ ≤ 3 ^ K * τ * K * (𝔼 x, polynomial c x ^ 2) := total_diff_third_truncated c hc hτ hsmall
      _ ≤ 3 ^ K * τ * K * 1 := mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ = _ := mul_one _
  have hF (x : BitCube n) : F x ∈ Icc η (1 - η) := interiorClip_mem hη.le hη' _
  have htt : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.le⟩
  have hb := finite_bellman_tensorization htt (kernel t) hC n F F hF hF
  have hm := corrAverage_mono htt n (fun x y => kernel_ge_product ht (F x) (F y))
  have he := mul_le_mul_of_nonneg_left hcost hC0
  change corrAverage t n (fun x y => F x * F y) ≤
    kernel t (𝔼 x, F x) (𝔼 x, F x) + 2 * C * (3 ^ K * τ * K)
  linarith

 theorem mean_mem_Icc {n : ℕ} {l u : ℝ} (f : BitCube n → ℝ) (hf : ∀ x, f x ∈ Icc l u) :
    (𝔼 x, f x) ∈ Icc l u :=
  ⟨Finset.le_expect Finset.univ_nonempty (fun x _ => (hf x).1),
    Finset.expect_le Finset.univ_nonempty (fun x _ => (hf x).2)⟩

 theorem smoothed_stability_bellman {t η u τ C : ℝ} {n K : ℕ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hη : 0 < η) (hη' : η ≤ 1 / 2)
    (hu : u ∈ Icc (0 : ℝ) 1)
    (h : BitCube n → ℝ) (hh : ∀ x, h x ∈ Icc (-1 : ℝ) 1) (hm : (𝔼 x, h x) = 0)
    (htail : u ^ (2 * (K + 1)) ≤ η ^ 2)
    (hb : corrAverage t n (fun x y =>
        interiorClip η (polynomial (smoothedTruncCoeff K u h) x) *
          interiorClip η (polynomial (smoothedTruncCoeff K u h) y)) ≤
      kernel t (𝔼 x, interiorClip η (polynomial (smoothedTruncCoeff K u h) x))
        (𝔼 x, interiorClip η (polynomial (smoothedTruncCoeff K u h) x)) + 2 * C * (3 ^ K * τ * K)) :
    stability t (noise u h) ≤ 2 / Real.pi * Real.arcsin t + 32 * η + 8 * C * (3 ^ K * τ * K) := by
  let P := polynomial (smoothedTruncCoeff K u h)
  let F : BitCube n → ℝ := fun x => interiorClip η (P x)
  let G : BitCube n → ℝ := fun x => (noise u h x + 1) / 2
  have hnoise := noise_bounded u hu.1 hu.2 h hh
  have hmean : (𝔼 x, G x) = 1 / 2 := by
    change (𝔼 x, ((noise u h x + 1) / 2)) = 1 / 2
    rw [← Finset.expect_div, Finset.expect_add_distrib, noise_mean, hm, Fintype.expect_const]
    ring
  have hF (x : BitCube n) : F x ∈ Icc η (1 - η) := interiorClip_mem hη.le hη' _
  have hF01 (x : BitCube n) : F x ∈ Icc (0 : ℝ) 1 := by
    have hhx := hF x
    constructor <;> linarith [hhx.1, hhx.2]
  have hG01 (x : BitCube n) : G x ∈ Icc (0 : ℝ) 1 := by
    dsimp [G]
    constructor <;> linarith [(hnoise x).1, (hnoise x).2]
  have hdiff : (𝔼 x, |F x - G x|) ≤ 2 * η := by
    calc
      _ ≤ 𝔼 x, (|P x - noise u h x| + η) :=
        Finset.expect_le_expect (fun x _ => interiorClip_approx hη.le (hnoise x) (P x))
      _ = (𝔼 x, |P x - noise u h x|) + η := by rw [Finset.expect_add_distrib, Fintype.expect_const]
      _ ≤ 2 * η := by linarith [smoothedTrunc_tail_first hu hη.le htail h hh]
  have hmeanF : (𝔼 x, F x) ∈ Ioo (0 : ℝ) 1 := by
    have hhF := mean_mem_Icc F hF
    constructor <;> linarith [hhF.1, hhF.2]
  have hmeanDiff : |(𝔼 x, F x) - (1 / 2 : ℝ)| ≤ 2 * η := by
    have hbnd := (mean_abs_diff_le F G).trans hdiff
    rwa [hmean] at hbnd
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hk := kernel_lipschitz ht hhalf hmeanF hhalf hmeanF
  have hk' := (abs_le.mp hk).2
  rw [kernel_half ht] at hk'
  have hcorr := correlation_diff_le ⟨by linarith [ht.1], ht.2.le⟩ G F hG01 hF01
  have heq : (𝔼 x, |G x - F x|) = 𝔼 x, |F x - G x| := by simp only [abs_sub_comm]
  rw [heq] at hcorr
  have hnmean : (𝔼 x, noise u h x) = 0 := (noise_mean u h).trans hm
  have hid := centered_half_correlation t n (noise u h) hnmean
  change 4 * corrAverage t n (fun x y => G x * G y) - 1 = stability t (noise u h) at hid
  change corrAverage t n (fun x y => F x * F y) ≤
    kernel t (𝔼 x, F x) (𝔼 x, F x) + 2 * C * (3 ^ K * τ * K) at hb
  have halg : 4 * (Real.arcsin t / (2 * Real.pi)) = 2 / Real.pi * Real.arcsin t := by ring
  linarith

 theorem majority_is_stablest : MajorityIsStablest := by
  intro t ht ht1 ξ hξ
  obtain ⟨u, hu, hu1, huerr⟩ := exists_uniform_noise_error t ξ ht.le ht1 hξ
  let η : ℝ := min (1 / 4) (ξ / 128)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηsmall : η ≤ 1 / 4 := min_le_left _ _
  have hηξ : η ≤ ξ / 128 := min_le_right _ _
  have hηhalf : η ≤ 1 / 2 := by linarith
  obtain ⟨C, hC0, hC⟩ := clipped_polynomial_bellman ⟨ht.le, ht1⟩ hη hηhalf
  obtain ⟨K, hK, htail⟩ := exists_influence_tail_cutoff u (2 * η ^ 2) hu.le hu1 (by positivity)
  have htail' : u ^ (2 * (K + 1)) ≤ η ^ 2 := by linarith
  let D : ℝ := 8 * C * 3 ^ K * K
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let r : ℝ := (ξ / 4) / (D + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrEq : (D + 1) * r = ξ / 4 := by
    dsimp [r]
    field_simp
  have herr : D * r ≤ ξ / 4 := by nlinarith
  refine ⟨K, hK, r ^ 2, sq_pos_of_pos hr, ?_⟩
  intro n h hh hm hi
  have hsmall (i : Fin n) :
      (𝔼 x, discreteDiff (polynomial (smoothedTruncCoeff K u h)) i x ^ 2) ≤ r ^ 2 :=
    (smoothedTrunc_diff_second ⟨hu.le, hu1.le⟩ h i).trans (hi i).le
  have hb := hC n K (smoothedTruncCoeff K u h) r hr.le
    (smoothedTrunc_high u h) (smoothedTrunc_second_le ⟨hu.le, hu1.le⟩ h hh) hsmall
  have hst := smoothed_stability_bellman ⟨ht.le, ht1⟩ hη hηhalf ⟨hu.le, hu1.le⟩ h hh hm htail' hb
  have hsmooth := stability_sub_noise_le t u (ξ / 2) h hh (by positivity) huerr
  have halg : 8 * C * (3 ^ K * r * K) = D * r := by dsimp [D]; ring
  rw [halg] at hst
  linarith

end OptimalMaxCut.MISProof

namespace OptimalMaxCut.LongCode

open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

theorem weight_nonneg (p : Law I) (i : I) : 0 ≤ (p.weight i : ℝ) := by
  exact_mod_cast p.nonneg i

theorem total_real (p : Law I) : ∑ i, (p.weight i : ℝ) = 1 := by
  exact_mod_cast p.total

@[simp] theorem avg_const (p : Law I) (a : ℝ) : p.avg (fun _ => a) = a := by
  simp [avg, ← sum_mul, total_real]

theorem avg_mono (p : Law I) {f g : I → ℝ} (h : ∀ i, f i ≤ g i) : p.avg f ≤ p.avg g :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (p.weight_nonneg i)

theorem avg_nonneg (p : Law I) {f : I → ℝ} (h : ∀ i, 0 ≤ f i) : 0 ≤ p.avg f := by
  simpa using p.avg_mono h

theorem avg_sum (p : Law I) (f : J → I → ℝ) :
    p.avg (fun i => ∑ j, f j i) = ∑ j, p.avg (f j) := by
  simp_rw [avg, mul_sum]
  rw [sum_comm]

theorem avg_sq_le (p : Law I) (f : I → ℝ) : p.avg f ^ 2 ≤ p.avg (fun i => f i ^ 2) := by
  have h := p.avg_nonneg (fun i => sq_nonneg (f i - p.avg f))
  have he : p.avg (fun i => (f i - p.avg f) ^ 2) = p.avg (fun i => f i ^ 2) - p.avg f ^ 2 := by
    simp_rw [sub_sq]
    rw [avg_add, avg_sub, avg_mul, avg_smul, avg_const]
    ring
  rw [he] at h
  linarith

theorem avg_mem (p : Law I) {f : I → ℝ} {a b : ℝ} (h : ∀ i, f i ∈ Set.Icc a b) :
    p.avg f ∈ Set.Icc a b := by
  constructor
  · simpa using p.avg_mono (fun i => (h i).1)
  · simpa using p.avg_mono (fun i => (h i).2)

 theorem avg_expect {n : ℕ} (p : Law I) (f : I → Cube (Fin n) → ℝ) :
    (𝔼 x, p.avg (fun i => f i x)) = p.avg (fun i => 𝔼 x, f i x) := by
  simp_rw [avg, Finset.expect_sum_comm, ← Finset.mul_expect]

 theorem coefficient_avg {n : ℕ} (p : Law I) (f : I → Cube (Fin n) → ℝ)
    (s : Cube (Fin n)) :
    coefficient (fun x => p.avg (fun i => f i x)) s = p.avg (fun i => coefficient (f i) s) := by
  simp_rw [coefficient, avg, sum_mul, mul_assoc, Finset.expect_sum_comm, ← Finset.mul_expect]

 theorem cutoffInfluence_avg {n : ℕ} (p : Law I) (f : I → Cube (Fin n) → ℝ)
    (K : ℕ) (a : Fin n) :
    cutoffInfluence K a (fun x => p.avg (fun i => f i x)) ≤
      p.avg (fun i => cutoffInfluence K a (f i)) := by
  unfold cutoffInfluence
  simp_rw [coefficient_avg]
  calc
    _ ≤ ∑ s ∈ univ.filter (fun s : Cube (Fin n) => s a = true ∧ degree s ≤ K),
        p.avg (fun i => coefficient (f i) s ^ 2) := sum_le_sum fun s _ => p.avg_sq_le _
    _ = _ := by simp_rw [avg, mul_sum]; rw [sum_comm]

end Law

 theorem antipode_involutive {n : ℕ} : Function.Involutive (@antipode n) := by
  intro x
  funext i
  simp [antipode]

 theorem oddPart_bounded {n : ℕ} (f : Cube (Fin n) → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (x : Cube (Fin n)) :
    oddPart f x ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 := hf x
  have h2 := hf (antipode x)
  constructor <;> dsimp [oddPart] <;> linarith [h1.1,h1.2,h2.1,h2.2]

 theorem oddPart_mean {n : ℕ} (f : Cube (Fin n) → ℝ) : (𝔼 x, oddPart f x) = 0 := by
  have he : (𝔼 x, f (antipode x)) = 𝔼 x, f x := by
    exact Fintype.expect_equiv antipode_involutive.toPerm _ _ (fun _ => rfl)
  simp_rw [oddPart]
  rw [← Finset.expect_div, Finset.expect_sub_distrib, he]
  ring

 theorem sum_cutoffInfluences {n : ℕ} (K : ℕ) (f : Cube (Fin n) → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    (∑ i, cutoffInfluence K i f) ≤ K := by
  classical
  have hiden : (∑ i, cutoffInfluence K i f) =
      ∑ s : Cube (Fin n), if degree s ≤ K then (degree s : ℝ) * coefficient f s ^ 2 else 0 := by
    unfold cutoffInfluence
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro s _
    by_cases hs : degree s ≤ K
    · simp only [hs, and_true, ↓reduceIte]
      rw [← sum_filter]
      simp [degree, sum_const, nsmul_eq_mul]
    · simp [hs]
  rw [hiden]
  calc
    _ ≤ ∑ s : Cube (Fin n), (K : ℝ) * coefficient f s ^ 2 := by
      apply sum_le_sum
      intro s _
      split_ifs with hs
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sq_nonneg _)
      · positivity
    _ = (K : ℝ) * ∑ s, coefficient f s ^ 2 := (mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * 1 := mul_le_mul_of_nonneg_left (spectral_energy_le_one f hf) (Nat.cast_nonneg _)
    _ = _ := mul_one _

end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Analysis_CubePerm
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic

 theorem degree_cubePerm {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Cube (Fin n)) :
    degree (cubePerm π s) = degree s := by
  unfold degree
  simp only [card_eq_sum_ones, sum_filter]
  exact Fintype.sum_equiv π _ _ (fun _ => rfl)

 theorem walsh_cubePerm {n : ℕ} (π : Equiv.Perm (Fin n)) (s x : Cube (Fin n)) :
    walsh (cubePerm π s) (cubePerm π x) = walsh s x := by
  unfold walsh
  exact Fintype.prod_equiv π _ _ (fun _ => rfl)

 theorem coefficient_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Cube (Fin n) → ℝ)
    (s : Cube (Fin n)) : coefficient (reindex π f) s = coefficient f (cubePerm π s) := by
  unfold coefficient reindex
  apply Fintype.expect_equiv (cubePerm π)
  intro x
  rw [walsh_cubePerm]

 theorem mean_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Cube (Fin n) → ℝ) :
    (𝔼 x, reindex π f x) = 𝔼 x, f x :=
  Fintype.expect_equiv (cubePerm π) _ _ (fun _ => rfl)

 theorem cutoffInfluence_reindex {n : ℕ} (π : Equiv.Perm (Fin n)) (f : Cube (Fin n) → ℝ)
    (K : ℕ) (i : Fin n) :
    cutoffInfluence K i (reindex π f) = cutoffInfluence K (π.symm i) f := by
  classical
  unfold cutoffInfluence
  simp only [sum_filter, coefficient_reindex]
  apply Fintype.sum_equiv (cubePerm π)
  intro s
  simp [degree_cubePerm]

 theorem cutoffInfluence_nonneg {n : ℕ} (K : ℕ) (i : Fin n) (f : Cube (Fin n) → ℝ) :
    0 ≤ cutoffInfluence K i f :=
  sum_nonneg (fun _ _ => sq_nonneg _)

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

 theorem averageCode_bounded (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ)
    (hf : ∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1) (y : Y) (z : Cube (Fin q)) :
    G.averageCode f y z ∈ Set.Icc (-1 : ℝ) 1 :=
  (G.edgeLaw y).avg_mem (fun e => hf (G.source e) _)

 theorem averageCode_mean (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ)
    (hf : ∀ x, (𝔼 z, f x z) = 0) (y : Y) : (𝔼 z, G.averageCode f y z) = 0 := by
  unfold averageCode
  rw [Law.avg_expect]
  simp_rw [mean_reindex, hf]
  exact Law.avg_const _ _

 theorem averageCode_influence (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ)
    (K : ℕ) (y : Y) (i : Fin q) :
    cutoffInfluence K i (G.averageCode f y) ≤ (G.edgeLaw y).avg (fun e =>
      cutoffInfluence K ((G.permutation e).symm i) (f (G.source e))) := by
  apply (Law.cutoffInfluence_avg (G.edgeLaw y) _ K i).trans_eq
  simp_rw [cutoffInfluence_reindex]

/-- Low-degree Fourier influence decodes an actual labeling. There is no
assumed decoder or hardness assertion in this inequality. -/
 theorem decoding_bound (G : Game X Y E q) (hq : 0 < q) (K : ℕ)
    (f : X → Cube (Fin q) → ℝ) (hf : ∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1)
    (δ : ℝ) (hsound : G.Sound δ) (ly : Y → Fin q) :
    G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
      cutoffInfluence K ((G.permutation e).symm (ly y)) (f (G.source e)))) ≤ (K : ℝ) * δ := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let P (x : X) (i : Fin q) : ℝ := cutoffInfluence K i (f x)
  let score (x : X) (i : Fin q) : ℝ := G.rightLaw.avg (fun y =>
    (G.edgeLaw y).avg (fun e => if G.source e = x then
      (if G.permutation e i = ly y then 1 else 0) else 0))
  have hP (x : X) (i : Fin q) : 0 ≤ P x i := cutoffInfluence_nonneg _ _ _
  have hPsum (x : X) : (∑ i, P x i) ≤ (K : ℝ) := sum_cutoffInfluences K (f x) (hf x)
  have hscore (x : X) (i : Fin q) : 0 ≤ score x i := by
    apply Law.avg_nonneg
    intro y
    apply Law.avg_nonneg
    intro e
    split_ifs <;> norm_num
  have hmax (x : X) : ∃ i : Fin q, ∀ j, score x j ≤ score x i := by
    obtain ⟨i, _, hi⟩ := exists_max_image univ (score x) univ_nonempty
    exact ⟨i, fun j => hi j (mem_univ _)⟩
  choose lx hlx using hmax
  have hweighted (x : X) : (∑ i, P x i * score x i) ≤ (K : ℝ) * score x (lx x) := by
    calc
      _ ≤ ∑ i, P x i * score x (lx x) :=
        sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlx x i) (hP x i))
      _ = (∑ i, P x i) * score x (lx x) := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hPsum x) (hscore x (lx x))
  have htotal : (∑ x, score x (lx x)) = G.satisfied lx ly := by
    dsimp [score, satisfied]
    simp_rw [← Law.avg_sum]
    congr 1
    funext y
    congr 1
    funext e
    simp
  have hinfluence : (∑ x, ∑ i, P x i * score x i) =
      G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
        P (G.source e) ((G.permutation e).symm (ly y)))) := by
    calc
      _ = ∑ x, ∑ i, G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
          P x i * (if G.source e = x then (if G.permutation e i = ly y then 1 else 0) else 0))) := by
        simp only [Law.avg_smul, score]
      _ = G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
          ∑ x, ∑ i, P x i * (if G.source e = x then (if G.permutation e i = ly y then 1 else 0) else 0))) := by
        simp_rw [Law.avg_sum]
      _ = _ := by
        congr 1
        funext y
        congr 1
        funext e
        simp only [← Equiv.eq_symm_apply, mul_ite, mul_one, mul_zero]
        simp
  change G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
    P (G.source e) ((G.permutation e).symm (ly y)))) ≤ _
  rw [← hinfluence]
  calc
    _ ≤ ∑ x, (K : ℝ) * score x (lx x) := sum_le_sum (fun x _ => hweighted x)
    _ = (K : ℝ) * G.satisfied lx ly := by rw [← mul_sum, htotal]
    _ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_left (hsound lx ly) (Nat.cast_nonneg _)

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Graphs_TestCut
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad OptimalMaxCut.Analytic
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem stability_nonneg {n : ℕ} (t : ℝ) (ht : 0 ≤ t) (f : Cube (Fin n) → ℝ) :
    0 ≤ stability t f := by
  exact sum_nonneg (fun s _ => mul_nonneg (pow_nonneg ht _) (sq_nonneg _))

 theorem stability_le_one {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (f : Cube (Fin n) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    stability t f ≤ 1 := by
  apply le_trans _ (spectral_energy_le_one f hf)
  apply sum_le_sum
  intro s _
  exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ ht.1 ht.2)

 theorem corrAverage_sub (t : ℝ) (n : ℕ) (F G : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F x y - G x y) = corrAverage t n F - corrAverage t n G := by
  have he (x y : BitCube n) : F x y - G x y = F x y + G x y * (-1) := by ring
  simp_rw [he, corrAverage_add, corrAverage_mul_const]
  ring

 theorem corrAverage_swap (t : ℝ) (n : ℕ) (F : BitCube n → BitCube n → ℝ) :
    corrAverage t n (fun x y => F y x) = corrAverage t n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [corrAverage]
    rw [ih]
    congr 1
    funext x y
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    congr 1
    simp only [bitPairWeight]
    ring

 theorem correlation_antipode (t : ℝ) {n : ℕ} (f : Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => f x * f (antipode y)) =
      stability t (evenPart f) - stability t (oddPart f) := by
  have hp (x y : Cube (Fin n)) : f x * f (antipode y) =
      (evenPart f x * evenPart f y - oddPart f x * oddPart f y) +
        (oddPart f x * evenPart f y - evenPart f x * oddPart f y) := by
    unfold evenPart oddPart
    ring
  have hs : corrAverage t n (fun x y => oddPart f x * evenPart f y) =
      corrAverage t n (fun x y => evenPart f x * oddPart f y) := by
    simpa only [mul_comm] using corrAverage_swap t n (fun x y => evenPart f x * oddPart f y)
  simp_rw [hp]
  rw [corrAverage_add, corrAverage_sub, corrAverage_sub, hs,
    corrAverage_stability, corrAverage_stability]
  ring

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

 theorem oddPart_averageCode (G : Game X Y E q) (f : X → Cube (Fin q) → ℝ) (y : Y) :
    oddPart (G.averageCode f y) = G.averageCode (fun x => oddPart (f x)) y := by
  funext z
  simp only [oddPart, averageCode, reindex, Law.avg_div, Law.avg_sub]
  rfl

 theorem testCut_stability (G : Game X Y E q) (t : ℝ) (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = 1 / 2 +
      G.rightLaw.avg (fun y => stability t (G.averageCode (fun x => oddPart (f x)) y)) / 2 -
      G.rightLaw.avg (fun y => stability t (evenPart (G.averageCode f y))) / 2 := by
  unfold testCut
  simp_rw [correlation_antipode, oddPart_averageCode]
  simp only [Law.avg_div, Law.avg_sub, Law.avg_const]
  ring

 theorem testCut_le_stability (G : Game X Y E q) (t : ℝ) (ht : 0 ≤ t)
    (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f ≤ (1 +
      G.rightLaw.avg (fun y => stability t (G.averageCode (fun x => oddPart (f x)) y))) / 2 := by
  rw [testCut_stability]
  have h : 0 ≤ G.rightLaw.avg (fun y => stability t (evenPart (G.averageCode f y))) :=
    G.rightLaw.avg_nonneg (fun _ => stability_nonneg t ht _)
  linarith

/-- Dimension-uniform soundness, with an actual Fourier-influence decoding
proof. Every input game soundness bound feeds the finite long-code cut test. -/
 theorem stability_soundness (G : Game X Y E q) (hq : 0 < q)
    {t ξ τ : ℝ} {K : ℕ} (ht : 0 < t) (ht1 : t < 1) (hξ : 0 < ξ) (hτ : 0 < τ)
    (hMIS : ∀ (n : ℕ) (h : Cube (Fin n) → ℝ),
      (∀ x, -1 ≤ h x ∧ h x ≤ 1) → (𝔼 x, h x) = 0 →
      (∀ i, cutoffInfluence K i h < τ) → stability t h ≤ 2 / Real.pi * Real.arcsin t + ξ)
    (f : X → Cube (Fin q) → ℝ) (hf : ∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1)
    (hm : ∀ x, (𝔼 z, f x z) = 0) (δ : ℝ) (hsound : G.Sound δ) :
    G.rightLaw.avg (fun y => stability t (G.averageCode f y)) ≤
      2 / Real.pi * Real.arcsin t + ξ + (K : ℝ) * δ / τ := by
  classical
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hp (y : Y) : ∃ i : Fin q, ∀ j,
      cutoffInfluence K j (G.averageCode f y) ≤ cutoffInfluence K i (G.averageCode f y) := by
    obtain ⟨i, _, hi⟩ := exists_max_image univ (fun i => cutoffInfluence K i (G.averageCode f y)) univ_nonempty
    exact ⟨i, fun j => hi j (mem_univ _)⟩
  choose ly hly using hp
  have hB : 0 ≤ 2 / Real.pi * Real.arcsin t + ξ := by
    have h := Real.arcsin_nonneg.mpr ht.le
    positivity
  have hy (y : Y) : stability t (G.averageCode f y) ≤ 2 / Real.pi * Real.arcsin t + ξ +
      cutoffInfluence K (ly y) (G.averageCode f y) / τ := by
    by_cases h : ∀ i, cutoffInfluence K i (G.averageCode f y) < τ
    · have hmis := hMIS q (G.averageCode f y) (G.averageCode_bounded f hf y)
        (G.averageCode_mean f hm y) h
      have hnon : 0 ≤ cutoffInfluence K (ly y) (G.averageCode f y) / τ :=
        div_nonneg (cutoffInfluence_nonneg _ _ _) hτ.le
      linarith
    · push Not at h
      obtain ⟨i, hi⟩ := h
      have hmτ := hi.trans (hly y i)
      have hratio : 1 ≤ cutoffInfluence K (ly y) (G.averageCode f y) / τ :=
        (le_div_iff₀ hτ).mpr (by simpa using hmτ)
      have hstab := stability_le_one t ⟨ht.le, ht1.le⟩ (G.averageCode f y) (G.averageCode_bounded f hf y)
      linarith
  calc
    _ ≤ G.rightLaw.avg (fun y => 2 / Real.pi * Real.arcsin t + ξ +
        cutoffInfluence K (ly y) (G.averageCode f y) / τ) := G.rightLaw.avg_mono hy
    _ = 2 / Real.pi * Real.arcsin t + ξ +
        G.rightLaw.avg (fun y => cutoffInfluence K (ly y) (G.averageCode f y)) / τ := by
      rw [Law.avg_add, Law.avg_const, Law.avg_div]
    _ ≤ 2 / Real.pi * Real.arcsin t + ξ +
        G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
          cutoffInfluence K ((G.permutation e).symm (ly y)) (f (G.source e)))) / τ := by
      gcongr
      exact G.rightLaw.avg_mono (fun y => G.averageCode_influence f K y (ly y))
    _ ≤ _ := by
      gcongr
      exact G.decoding_bound hq K f hf δ hsound ly

/-- The MIS threshold and low-degree cutoff are actually proved, not supplied
as assumptions. This theorem is the soundness component of the main reduction. -/
 theorem exists_test_soundness (t ξ : ℝ) (ht : 0 < t) (ht1 : t < 1) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
      (q : ℕ) (_hq : 0 < q) (G : Game X Y E q), G.Sound δ →
      ∀ f : X → Cube (Fin q) → ℝ, (∀ x z, f x z ∈ Set.Icc (-1 : ℝ) 1) →
        G.testCut t f ≤ (1 + 2 / Real.pi * Real.arcsin t) / 2 + ξ := by
  obtain ⟨K, hK, τ, hτ, hMIS⟩ := majority_is_stablest t ht ht1 ξ hξ
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  refine ⟨ξ * τ / K, by positivity, ?_⟩
  intro X Y E _ _ _ q hq G hs f hf
  have ho (x : X) (z : Cube (Fin q)) := oddPart_bounded (f x) (hf x) z
  have hb := G.stability_soundness hq ht ht1 hξ hτ hMIS (fun x => oddPart (f x)) ho
    (fun x => oddPart_mean (f x)) (ξ * τ / K) hs
  have he : (K : ℝ) * (ξ * τ / K) / τ = ξ := by field_simp
  rw [he] at hb
  have hc := G.testCut_le_stability t ht.le f
  linarith

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitPairWeightQ
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.GaussianBellman OptimalMaxCut.MISProof

 theorem jointLaw_average (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1) (n : ℕ)
    (F : Cube (Fin n) → Cube (Fin n) → ℝ) :
    (jointLaw t ht n).avg (fun p => F p.1 p.2) = corrAverage t n F := by
  unfold Law.avg jointLaw
  simp only [corrAverageQ_cast, apply_ite Rat.cast, Rat.cast_one, Rat.cast_zero]
  calc
    _ = ∑ p : Cube (Fin n) × Cube (Fin n), corrAverage t n (fun x y =>
        (if (x, y) = p then (1 : ℝ) else 0) * F p.1 p.2) := by
      simp only [corrAverage_mul_const]
    _ = corrAverage t n (fun x y => ∑ p : Cube (Fin n) × Cube (Fin n),
        (if (x, y) = p then (1 : ℝ) else 0) * F p.1 p.2) := (corrAverage_sum _ _ _ _).symm
    _ = _ := by simp

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J]

 theorem bind_average (p : Law I) (q : I → Law J) (F : I × J → ℝ) :
    (p.bind q).avg F = p.avg (fun i => (q i).avg (fun j => F (i,j))) := by
  simp only [avg, bind, Rat.cast_mul, Fintype.sum_prod_type, mul_sum, mul_assoc]

 theorem corrAverage_avg (p : Law I) (t : ℝ) (n : ℕ)
    (F : I → Cube (Fin n) → Cube (Fin n) → ℝ) :
    corrAverage t n (fun x y => p.avg (fun i => F i x y)) = p.avg (fun i => corrAverage t n (F i)) := by
  simp only [avg, corrAverage_sum, corrAverage_const_mul]

end Law

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q : ℕ}

 theorem testCut_expanded (G : Game X Y E q) (t : ℝ) (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = G.rightLaw.avg (fun y => (G.edgeLaw y).avg (fun e =>
      (G.edgeLaw y).avg (fun e' => corrAverage t q (fun z z' =>
        (1 - f (G.source e) (cubePerm (G.permutation e) z) *
          f (G.source e') (cubePerm (G.permutation e') (antipode z'))) / 2)))) := by
  have hp : ∀ y z z', G.averageCode f y z * G.averageCode f y (antipode z') =
      (G.edgeLaw y).avg (fun e => (G.edgeLaw y).avg (fun e' =>
      f (G.source e) (cubePerm (G.permutation e) z) *
        f (G.source e') (cubePerm (G.permutation e') (antipode z')))) := by
    intro y z z'
    simp only [averageCode, reindex, Law.avg_mul, Law.avg_smul]
  unfold testCut
  simp_rw [hp, Law.corrAverage_avg]
  simp_rw [div_eq_mul_inv, corrAverage_mul_const, corrAverage_sub,
    corrAverage_fst, Fintype.expect_const, Law.avg_mul, Law.avg_sub, Law.avg_const]

/-- The analytic test value is exactly the expectation over explicit rational
atoms. This identity will be used to aggregate a genuine finite graph. -/
 theorem testCut_sampleLaw (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (f : X → Cube (Fin q) → ℝ) :
    G.testCut t f = (G.sampleLaw t ht).avg (fun a =>
      (1 - f (G.queries a).1.1 (G.queries a).1.2 *
        f (G.queries a).2.1 (G.queries a).2.2) / 2) := by
  rw [testCut_expanded]
  simp only [sampleLaw, Law.bind_average, queries]
  congr 1; funext y
  congr 1; funext e
  congr 1; funext e'
  exact (jointLaw_average t ht q _).symm

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Vec
attribute [-instance] _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.MaxCutGames.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace OptimalMaxCut.Unweighted

open Finset
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

theorem weightedMax_attained {N : ℕ} (w : Fin N → Fin N → ℝ) :
    ∃ σ : Fin N → Bool, weightedCut w σ = weightedMax w := by
  have hm := (univ.image (weightedCut w)).max'_mem (univ_nonempty.image _)
  obtain ⟨σ, hσ, he⟩ := mem_image.mp hm
  exact ⟨σ, he⟩

end OptimalMaxCut.Unweighted

/-! Exact tree gate and slice symmetry. Sign values are encoded in ZMod 2:
b encodes (-1)^b. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Dictator
attribute [-instance] _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.rawObservationFibreFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.LongCode
open scoped BigOperators
open Finset MaxCutGames.Foundations.Hastad
open OptimalMaxCut.Unweighted

namespace Law
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

 theorem push_average (p : Law I) (f : I → J) (g : J → ℝ) :
    (p.push f).avg g = p.avg (fun i => g (f i)) := by
  simp only [avg, push, Rat.cast_sum, apply_ite Rat.cast, Rat.cast_zero, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul]

end Law

 theorem upper_triangle_symmetrize {N : ℕ} (a : Fin N → Fin N → ℝ) :
    (∑ u, ∑ v, if u < v then a u v + a v u else 0) =
      ∑ u, ∑ v, if u ≠ v then a u v else 0 := by
  have he (u v : Fin N) : (if u ≠ v then a u v else 0) =
      (if u < v then a u v else 0) + (if v < u then a u v else 0) := by
    rcases lt_trichotomy u v with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hs (u v : Fin N) : (if u < v then a u v + a v u else 0) =
      (if u < v then a u v else 0) + (if u < v then a v u else 0) := by
    split_ifs <;> ring
  conv_lhs => simp only [hs, sum_add_distrib]
  conv_rhs => simp only [he, sum_add_distrib]
  congr 1
  rw [sum_comm]

 theorem aggregate_cut {N : ℕ} (p : Law (Fin N × Fin N)) (σ : Fin N → Bool) :
    weightedCut (fun u v => (aggregate p u v : ℝ)) σ =
      p.avg (fun e => if σ e.1 ≠ σ e.2 then 1 else 0) := by
  have h (u v : Fin N) :
      (if u < v ∧ σ u ≠ σ v then (aggregate p u v : ℝ) else 0) =
      (if u < v then (if σ u ≠ σ v then (p.weight (u,v) : ℝ) else 0) +
        (if σ v ≠ σ u then (p.weight (v,u) : ℝ) else 0) else 0) := by
    by_cases hlt : u < v <;> by_cases hs : σ u = σ v <;>
      simp [aggregate, hlt, hs, eq_comm, ne_of_lt, Rat.cast_add]
  simp only [weightedCut, h, upper_triangle_symmetrize, Law.avg, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases huv : u = v <;> by_cases hs : σ u = σ v <;> simp [huv, hs]

namespace Game
variable {X Y E : Type*} [Fintype X] [Fintype Y] [Fintype E] {q N : ℕ}

 theorem weightedCut_testCut (G : Game X Y E q) (t : ℚ) (ht : t ∈ Set.Icc (-1 : ℚ) 1)
    (enum : X × Cube (Fin q) ≃ Fin N) (σ : Fin N → Bool) :
    weightedCut (fun u v => (G.weights t ht enum u v : ℝ)) σ =
      G.testCut t (fun x z => bitSign (σ (enum (x,z)))) := by
  rw [weights, aggregate_cut, edgeDistribution, Law.push_average, G.testCut_sampleLaw t ht]
  congr 1
  funext a
  cases h : σ (enum (G.queries a).1) <;> cases h' : σ (enum (G.queries a).2) <;>
    norm_num [bitSign, h, h']

 theorem exists_weighted_soundness_oai (t : ℚ) (ht : 0 < t) (ht1 : t < 1) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]
      {q N : ℕ} (_hq : 0 < q) (G : Game X Y E q)
      (enum : X × Cube (Fin q) ≃ Fin N), G.Sound δ →
      weightedMax (fun u v => (G.weights t ⟨by linarith, ht1.le⟩ enum u v : ℝ)) ≤
        (1 + 2 / Real.pi * Real.arcsin t) / 2 + ξ := by
  obtain ⟨δ, hδ, hbound⟩ := exists_test_soundness (t : ℝ) ξ
    (by exact_mod_cast ht) (by exact_mod_cast ht1) hξ
  refine ⟨δ, hδ, ?_⟩
  intro X Y E _ _ _ q N hq G enum hsound
  obtain ⟨σ, hσ⟩ := weightedMax_attained (fun u v => (G.weights t ⟨by linarith, ht1.le⟩ enum u v : ℝ))
  have hm : t ∈ Set.Icc (-1 : ℚ) 1 := ⟨by linarith, ht1.le⟩
  have hb := hbound q hq G hsound (fun x z => bitSign (σ (enum (x,z)))) (by
    intro x z
    cases σ (enum (x,z)) <;> norm_num [bitSign])
  exact hσ.symm.trans_le ((G.weightedCut_testCut t hm enum σ).trans_le hb)

end Game
end OptimalMaxCut.LongCode

end

end OAI
end

theorem solution : type_of% @OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness_oai := @OAI.OptimalMaxCut.LongCode.Game.exists_weighted_soundness_oai

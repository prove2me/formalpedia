-- Prove2me | solution 1 for OAI.LogBrunnMinkowski.softVariance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:18:09.250413+00:00
-- url     : https://prove2.me/submissions/b97a08f8-1ae9-403c-9b0a-664d957bb390

import Mathlib
import Definitions.Def_OAIW2LB000
import Theorems.Thm_OAI_C11InteriorRegularity_continuous_hessian_rep
import Theorems.Thm_OAI_C11InteriorRegularity_holder_hessian
import Theorems.Thm_OAI_CompactMomentVariational_exists_C11_truncated
import Theorems.Thm_OAI_MomentQuotient_C3_local
import Theorems.Thm_OAI_MomentSchauder_smooth_of_regular_three
import Theorems.Thm_OAI_MomentSlab_variance_from_moment

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology NNReal

namespace CompactMomentVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma values_nonempty {K : Set E} (hK : K.Nonempty) (u : E → ℝ) (z : E) :
    ((fun x => ⟪x,z⟫_ℝ-u x) '' K).Nonempty := hK.image _

lemma conjugate_le {K : Set E} (hK : K.Nonempty) {u : E → ℝ} {z : E} {b : ℝ}
    (h : ∀ x ∈ K, ⟪x,z⟫_ℝ-u x ≤ b) : conjugate K u z ≤ b := by
  apply csSup_le (values_nonempty hK u z)
  rintro _ ⟨x,hx,rfl⟩
  exact h x hx

section Partition
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma integrable_exp_neg_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E => Real.exp (-c*‖x‖)) μ := by
  let r : ℝ := Module.finrank ℝ E + 1
  have hr : (Module.finrank ℝ E : ℝ) < r := by dsimp [r]; linarith
  have hi : Integrable (fun x : E => (1+‖x‖)^(-r)) μ := integrable_one_add_norm hr
  have hl : LocallyIntegrable (fun x : E => Real.exp (-c*‖x‖)) μ :=
    (show Continuous (fun x : E => Real.exp (-c*‖x‖)) by fun_prop).locallyIntegrable
  have ht : Tendsto (fun x : E => (1:ℝ)+‖x‖) (cocompact E) atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop
  have hO := (isLittleO_exp_neg_mul_rpow_atTop hc (-r)).isBigO.comp_tendsto ht
  have hO' := hO.const_mul_left (Real.exp c)
  have hfn : (fun x : E => Real.exp c * Real.exp (-c * (1+‖x‖))) =
      (fun x : E => Real.exp (-c*‖x‖)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Function.comp_apply] at hO'
  rw [hfn] at hO'
  exact hl.integrable_of_isBigO_cocompact hO' (hi.integrableAtFilter (cocompact E))

lemma tail_integrable {φ : E → ℝ} (hφ : Continuous φ) {c b : ℝ}
    (hc : 0 < c) (hl : ∀ z, c*‖z‖-b ≤ φ z) :
    Integrable (fun z => Real.exp (-φ z)) μ := by
  refine ((integrable_exp_neg_norm μ hc).const_mul (Real.exp b)).mono'
    (Real.continuous_exp.comp hφ.neg).aestronglyMeasurable ?_
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hl z])

end Partition


end
end CompactMomentVariational

open Set Filter
open scoped Topology NNReal

noncomputable section

namespace CompactMomentVariational

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexOn_conjugate_of_bdd {K D : Set E} (hK : K.Nonempty) (hD : Convex ℝ D)
    {u : E → ℝ} (hb : ∀ z ∈ D, BddAbove ((fun x => ⟪x,z⟫_ℝ-u x) '' K)) :
    ConvexOn ℝ D (conjugate K u) := by
  refine ⟨hD, ?_⟩
  intro z hz w hw a b ha hb' hab
  apply conjugate_le hK
  intro x hx
  have hz' := le_csSup (hb z hz) (mem_image_of_mem (fun x => ⟪x,z⟫_ℝ-u x) hx)
  have hw' := le_csSup (hb w hw) (mem_image_of_mem (fun x => ⟪x,w⟫_ℝ-u x) hx)
  change ⟪x,z⟫_ℝ-u x ≤ conjugate K u z at hz'
  change ⟪x,w⟫_ℝ-u x ≤ conjugate K u w at hw'
  simp only [smul_eq_mul]
  rw [inner_add_right,inner_smul_right,inner_smul_right]
  have habu : (a+b)*u x=u x := by rw [hab,one_mul]
  nlinarith [mul_le_mul_of_nonneg_left hz' ha,mul_le_mul_of_nonneg_left hw' hb']

lemma dualOn_eq {K : Set E} {φ : E → ℝ} {x : E} (hx : x ∈ K) :
    dualOn K φ x=conjugate univ φ x := indicator_of_mem hx _

lemma convexOn_dualOn {K : Set E} (hK : Convex ℝ K) {φ : E → ℝ}
    (hb : ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) :
    ConvexOn ℝ K (dualOn K φ) :=
  (convexOn_conjugate_of_bdd (univ_nonempty) hK hb).congr (fun _ hx => (dualOn_eq hx).symm)

lemma fenchel_dualOn {K : Set E} {φ : E → ℝ}
    (hb : ∀ x ∈ K, BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ)) {x : E} (hx : x ∈ K) (z : E) :
    ⟪x,z⟫_ℝ-dualOn K φ x ≤ φ z := by
  rw [dualOn_eq hx]
  have h := le_csSup (hb x hx) (mem_image_of_mem (fun z => ⟪z,x⟫_ℝ-φ z) (mem_univ z))
  change ⟪z,x⟫_ℝ-φ z ≤ conjugate univ φ x at h
  rw [real_inner_comm x z] at h
  linarith

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma normalizedSource_probability {φ : E → ℝ}
    (hI : Integrable (fun z => Real.exp (-φ z)) μ) :
    IsProbabilityMeasure (normalizedSource μ φ) := by
  have hIp := integral_exp_pos hI
  apply isProbabilityMeasure_iff.mpr
  rw [normalizedSource,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · simp only [integral_div,div_self hIp.ne',ENNReal.ofReal_one]
  · exact hI.div_const _
  · exact Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hIp.le

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma integral_normalizedSource {φ : E → ℝ} (hφ : Measurable φ)
    (hI : Integrable (fun z => Real.exp (-φ z)) μ) (f : E → ℝ) :
    (∫ z,f z ∂normalizedSource μ φ) =
      (∫ z,f z*Real.exp (-φ z) ∂μ)/(∫ z,Real.exp (-φ z) ∂μ) := by
  have hIp := integral_exp_pos hI
  have hd : Measurable (fun z => ENNReal.ofReal (Real.exp (-φ z)/(∫ y,Real.exp (-φ y) ∂μ))) :=
    (hφ.neg.exp.div_const _).ennreal_ofReal
  rw [normalizedSource,integral_withDensity_eq_integral_toReal_smul hd
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hIp.le),smul_eq_mul]
  rw [← integral_div]
  congr 1
  funext z
  ring

end CompactMomentVariational
end

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

noncomputable section
namespace TruncatedMoment
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma integrable_density {V : E → ℝ} (hV : Continuous V) (R : ℝ) :
    IntegrableOn (fun x => Real.exp (-V x)) (Metric.ball (0:E) R) μ :=
  ((hV.neg.rexp.continuousOn).integrableOn_compact (isCompact_closedBall (0:E) R)).mono_set
    Metric.ball_subset_closedBall

lemma partition_pos {V : E → ℝ} (hV : Continuous V) {R : ℝ} (hR : 0 < R) :
    0 < partition μ R V := by
  let : NeZero (μ.restrict (Metric.ball (0:E) R)) := ⟨by
    intro he
    have hh := congrArg (fun m : Measure E => m univ) he
    simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter,Measure.coe_zero,Pi.zero_apply] at hh
    exact (Metric.measure_ball_pos μ 0 hR).ne' hh⟩
  exact integral_exp_pos (integrable_density μ hV R)

lemma probability {V : E → ℝ} (hV : Continuous V) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (target μ R V) := by
  have hZ := partition_pos μ hV hR
  apply isProbabilityMeasure_iff.mpr
  rw [target,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div]
    change ENNReal.ofReal (partition μ R V / partition μ R V) = 1
    rw [div_self hZ.ne',ENNReal.ofReal_one]
  · exact (integrable_density μ hV R).div_const _
  · exact Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hZ.le

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma ae_mem_ball (V : E → ℝ) (R : ℝ) :
    ∀ᵐ x ∂target μ R V, x ∈ Metric.ball (0:E) R :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_ball)

end TruncatedMoment

end

open scoped ENNReal

noncomputable section
namespace CompactMomentVariational
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma fenchel_eq_at_gradient {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) {z : E}
    (hd : DifferentiableAt ℝ φ z) :
    conjugate univ φ (gradient φ z) = ⟪gradient φ z,z⟫_ℝ-φ z := by
  have hb : BddAbove ((fun w => ⟪w,gradient φ z⟫_ℝ-φ w) '' univ) := by
    refine ⟨⟪gradient φ z,z⟫_ℝ-φ z,?_⟩
    rintro _ ⟨w,_,rfl⟩
    have hh := convex_supporting_gradient hc hd w
    rw [inner_sub_right] at hh
    dsimp only
    rw [real_inner_comm (gradient φ z) w]
    linarith
  apply le_antisymm
  · apply conjugate_le (Set.univ_nonempty)
    intro w _
    have hh := convex_supporting_gradient hc hd w
    rw [inner_sub_right] at hh
    rw [real_inner_comm (gradient φ z) w]
    linarith
  · simpa only [conjugate,real_inner_comm (gradient φ z) z] using
      (le_csSup hb (mem_image_of_mem (fun w => ⟪w,gradient φ z⟫_ℝ-φ w) (mem_univ z)))

lemma inverse_gradient {φ : E → ℝ} {K : Set E} (hK : IsOpen K)
    (hc : ConvexOn ℝ univ φ) {z : E} (hd : DifferentiableAt ℝ φ z)
    (hg : gradient φ z ∈ K)
    (hb : ∀ x ∈ K, BddAbove ((fun w => ⟪w,x⟫_ℝ-φ w) '' univ))
    (hu : DifferentiableAt ℝ (dualOn K φ) (gradient φ z)) :
    gradient (dualOn K φ) (gradient φ z) = z := by
  let x := gradient φ z
  have he : dualOn K φ x = ⟪z,x⟫_ℝ-φ z := by
    rw [dualOn_eq hg,fenchel_eq_at_gradient hc hd,real_inner_comm]
  have hmin : IsLocalMin (fun y => dualOn K φ y-⟪z,y⟫_ℝ) x := by
    filter_upwards [hK.mem_nhds hg] with y hy
    have hh := fenchel_dualOn hb hy z
    rw [he,real_inner_comm y z] at *
    linarith
  have hz := hmin.hasFDerivAt_eq_zero
    (hu.hasFDerivAt.sub (innerSL ℝ z).hasFDerivAt)
  have hz' : fderiv ℝ (dualOn K φ) x = innerSL ℝ z := sub_eq_zero.mp hz
  rw [gradient,hz']
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply z

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma locallyLipschitz_ae_differentiable {μ : Measure E} [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsOpen K) {f : E → ℝ} (hf : LocallyLipschitzOn K f) :
    ∀ᵐ x ∂μ, x ∈ K → DifferentiableAt ℝ f x := by
  have hloc : ∀ x ∈ K, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ≥0, LipschitzOnWith C f U := by
    intro x hx
    obtain ⟨C,t,ht,hft⟩ := hf hx
    rw [hK.nhdsWithin_eq hx] at ht
    exact ⟨interior t,isOpen_interior,mem_interior_iff_mem_nhds.mpr ht,C,
      hft.mono interior_subset⟩
  choose U hUo hUx C hC using hloc
  obtain ⟨t,ht,hcover⟩ := (HereditarilyLindelofSpace.isLindelof K).elim_nhds_subcover' U
    (fun x hx => (hUo x hx).mem_nhds (hUx x hx))
  have hh : ∀ᵐ x ∂μ.restrict (⋃ z ∈ t, U z.val z.property), DifferentiableAt ℝ f x := by
    rw [ae_restrict_biUnion_iff _ ht]
    intro z _
    rw [ae_restrict_iff' (hUo z.val z.property).measurableSet]
    filter_upwards [(hC z.val z.property).ae_differentiableWithinAt_of_mem (μ:=μ)] with x hx
    intro hxU
    exact (hx hxU).differentiableAt ((hUo z.val z.property).mem_nhds hxU)
  rw [← ae_restrict_iff' hK.measurableSet]
  exact (ae_mono (Measure.restrict_mono hcover le_rfl)) hh

lemma convex_ae_differentiable {μ : Measure E} [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsOpen K) {f : E → ℝ} (hf : ConvexOn ℝ K f) :
    ∀ᵐ x ∂μ, x ∈ K → DifferentiableAt ℝ f x :=
  locallyLipschitz_ae_differentiable hK (hf.locallyLipschitzOn hK)


lemma gradient_measurable (φ : E → ℝ) : Measurable (gradient φ) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ φ)

end

section

lemma map_density_pullback {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (σ : Measure α) {g : α → β} (hg : Measurable g) {w : β → ℝ≥0∞} (hw : Measurable w) :
    Measure.map g (σ.withDensity (w ∘ g)) = (Measure.map g σ).withDensity w := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hg hs,withDensity_apply _ (hs.preimage hg),withDensity_apply _ hs,
    ← lintegral_indicator (hs.preimage hg),← lintegral_indicator hs,
    lintegral_map (hw.indicator hs) hg]
  congr 1

lemma reverse_weighted {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {σ : Measure α} {ν : Measure β} {g : α → β} {f : β → α}
    (hg : Measurable g) (hf : Measurable f)
    (hm : Measure.map g σ = ν) (hi : ∀ᵐ z ∂σ, f (g z)=z)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    Measure.map f (ν.withDensity w) = σ.withDensity (w ∘ g) := by
  rw [← hm,← map_density_pullback σ hg hw,Measure.map_map hf hg]
  exact (Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le hi)).trans Measure.map_id

end

end CompactMomentVariational
end

open scoped InnerProductSpace ContDiff Topology
noncomputable section
namespace CompactMomentVariational

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma supporting_monotone {φ : E → ℝ} {z w p q : E}
    (hsz : SupportingSlope φ z p) (hsw : SupportingSlope φ w q) :
    0 ≤ ⟪p-q,z-w⟫_ℝ := by
  have hz := hsz w
  have hw := hsw z
  simp only [inner_sub_left,inner_sub_right] at *
  linarith

end CompactMomentVariational
end
open scoped ENNReal

open Set MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace MomentJacobian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem jacobian_of_ae_inverse_within {σ ν : Measure E} {K D : Set E}
    (_hK : MeasurableSet K) {g f : E → E} {g' : E → E →L[ℝ] E}
    (hgm : Measurable g) (hf : Measurable f)
    (hg : ∀ᵐ z ∂μ, z ∈ D ∧ HasFDerivWithinAt g (g' z) D z)
    (hm : Measure.map g σ = ν) (hμσ : μ ≪ σ) (hσμ : σ ≪ μ)
    (hKν : μ.restrict K ≪ ν)
    (hi : ∀ᵐ z ∂σ, f (g z)=z) (hk : ∀ᵐ z ∂σ, g z ∈ K) :
    μ.withDensity (fun z => ENNReal.ofReal |(g' z).det|) = Measure.map f (μ.restrict K) := by
  let s := {z | z ∈ D ∧ HasFDerivWithinAt g (g' z) D z ∧ f (g z)=z ∧ g z ∈ K}
  have hfull : ∀ᵐ z ∂μ, z ∈ s := by
    filter_upwards [hg,hμσ.ae_le hi,hμσ.ae_le hk] with z hz hi hk
    exact ⟨hz.1,hz.2,hi,hk⟩
  have hsn : NullMeasurableSet s μ := by
    apply NullMeasurableSet.of_compl
    exact NullMeasurableSet.of_null (ae_iff.mp hfull)
  obtain ⟨t,hts,ht,heq⟩ := hsn.exists_measurable_subset_ae_eq
  have htfull : ∀ᵐ z ∂μ, z ∈ t := by
    filter_upwards [hfull,heq] with z hz he
    exact he.mpr hz
  have hsinj : InjOn g t := by
    intro z hz w hw he
    exact (hts hz).2.2.1.symm.trans ((congrArg f he).trans (hts hw).2.2.1)
  have hder (z) (hz : z ∈ t) : HasFDerivWithinAt g (g' z) t z :=
    ((hts hz).2.1).mono (fun w hw => (hts hw).1)
  have him : MeasurableSet (g '' t) := measurable_image_of_fderivWithin ht hder hsinj
  have htfullσ : ∀ᵐ z ∂σ, z ∈ t := hσμ.ae_le htfull
  have himfullν : ∀ᵐ x ∂ν, x ∈ g '' t := by
    rw [← hm]
    exact (ae_map_iff hgm.aemeasurable him).mpr
      (htfullσ.mono (fun z hz => mem_image_of_mem g hz))
  have himless : g '' t ⊆ K := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hts hz).2.2.2
  have himrestrict : μ.restrict (g '' t)=μ.restrict K := by
    rw [← Measure.restrict_eq_self_of_ae_mem (hKν.ae_le himfullν),
      Measure.restrict_restrict him,inter_eq_left.mpr himless]
  have hj := map_withDensity_abs_det_fderiv_eq_addHaar μ ht.nullMeasurableSet hder hsinj
  rw [Measure.restrict_eq_self_of_ae_mem htfull,himrestrict] at hj
  rw [← hj,Measure.map_map hf hgm]
  have hie : ∀ᵐ z ∂μ.withDensity (fun z => ENNReal.ofReal |(g' z).det|), f (g z)=z :=
    (withDensity_absolutelyContinuous _ _).ae_le (hμσ.ae_le hi)
  exact ((Measure.map_congr hie).trans Measure.map_id).symm

end MomentJacobian
namespace CompactMomentVariational

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma supporting_selection_monotone_line {φ : E → ℝ} {P : E → E}
    (hs : ∀ x, SupportingSlope φ x (P x)) (x v : E) :
    Monotone (fun t : ℝ => ⟪P (x+t • v),v⟫_ℝ) := by
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  have hm := supporting_monotone (hs (x+b • v)) (hs (x+a • v))
  have he : (x+b • v)-(x+a • v)=(b-a) • v := by module
  rw [he,real_inner_smul_right] at hm
  have hi := nonneg_of_mul_nonneg_right hm (sub_pos.mpr hab)
  simpa only [inner_sub_left,sub_nonneg] using hi

omit [FiniteDimensional ℝ E] in
lemma supporting_derivative_nonneg {φ : E → ℝ} {P : E → E}
    (hs : ∀ x, SupportingSlope φ x (P x)) {x : E} {H : E →L[ℝ] E}
    (hH : HasFDerivAt P H x) (v : E) : 0 ≤ ⟪H v,v⟫_ℝ := by
  have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
    simpa only [one_smul,id_eq] using
      ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hP : HasDerivAt (fun t : ℝ => P (x+t • v)) (H v) 0 := by
    have hh : HasFDerivAt P H (x+(0:ℝ) • v) := by simpa only [zero_smul,add_zero] using hH
    exact hh.comp_hasDerivAt (0:ℝ) hline
  have hh := hP.inner ℝ (hasDerivAt_const (0:ℝ) v)
  simp only [inner_zero_right,zero_add] at hh
  have hm := (supporting_selection_monotone_line hs x v).deriv_nonneg (x:=0)
  rwa [hh.deriv] at hm

end

end CompactMomentVariational

namespace LogDetConcavity
open Matrix
open scoped MatrixOrder BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma logdet_le_trace {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card ι := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [Real.log_prod (fun i _ => ne_of_gt (hA.eigenvalues_pos i))]
  calc
    _ ≤ ∑ i, (hA.isHermitian.eigenvalues i - 1) :=
      Finset.sum_le_sum (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
    _ = _ := by simp [Finset.sum_sub_distrib]

theorem tangent {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    Real.log B.det - Real.log A.det ≤ (A⁻¹ * (B-A)).trace := by
  obtain ⟨Q,hQ⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.inv.posSemidef.nonneg
  have hQ' : A⁻¹ = Qᴴ * Q := hQ
  have hdQ : Q.det ≠ 0 := by
    have hd := congrArg Matrix.det hQ'
    rw [Matrix.det_mul, Matrix.det_conjTranspose] at hd
    intro hz
    simp only [hz, mul_zero] at hd
    exact ne_of_gt hA.inv.det_pos hd
  have hunit : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hdQ)
  have hK : (Q * B * Qᴴ).PosDef := hB.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_iff_isUnit.mpr hunit)
  have ht := logdet_le_trace hK
  have htrace : (Q * B * Qᴴ).trace = (A⁻¹ * B).trace := by
    rw [hQ', Matrix.trace_mul_cycle]
  have hdet : (Q * B * Qᴴ).det = B.det / A.det := by
    have hd := congrArg Matrix.det hQ'
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, Matrix.det_nonsing_inv, Ring.inverse_eq_inv] at hd ⊢
    rw [div_eq_mul_inv, hd]
    ring
  rw [htrace, hdet, Real.log_div (ne_of_gt hB.det_pos) (ne_of_gt hA.det_pos)] at ht
  simpa only [Matrix.mul_sub, Matrix.trace_sub,
    Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)), Matrix.trace_one] using ht

end LogDetConcavity
end

noncomputable section
namespace SourceIdentity
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma norm_exp_bound {c : ℝ} (hc : 0<c) (r : ℝ) :
    r*Real.exp (-c*r) ≤ (2/c)*Real.exp (-(c/2)*r) := by
  have hh : c/2*r ≤ Real.exp (c/2*r) := (by linarith : c/2*r ≤ c/2*r+1).trans (Real.add_one_le_exp _)
  have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-c*r)).le
  rw [← Real.exp_add] at hm
  have he : c/2*r+-c*r=-(c/2)*r := by ring
  rw [he] at hm
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0≤2/c)
  have he' : (2/c)*(c/2*r*Real.exp (-c*r))=r*Real.exp (-c*r) := by field_simp
  rw [he'] at hm'
  exact hm'

omit [μ.IsAddHaarMeasure] in
lemma integrable_norm_density {φ : E → ℝ} (hφ : Continuous φ) {c d : ℝ}
    (hc : 0<c) (ht : ∀ x, c*‖x‖-d≤φ x)
    (he : Integrable (fun x : E => Real.exp (-(c/2)*‖x‖)) μ) :
    Integrable (fun x => ‖x‖*Real.exp (-φ x)) μ := by
  apply (he.const_mul (Real.exp d*(2/c))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  calc
    ‖x‖*Real.exp (-φ x) ≤ ‖x‖*(Real.exp d*Real.exp (-c*‖x‖)) := by
      gcongr
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [ht x]
    _ = Real.exp d*(‖x‖*Real.exp (-c*‖x‖)) := by ring
    _ ≤ Real.exp d*((2/c)*Real.exp (-(c/2)*‖x‖)) :=
      mul_le_mul_of_nonneg_left (norm_exp_bound hc ‖x‖) (Real.exp_pos _).le
    _ = _ := by ring

omit [μ.IsAddHaarMeasure] in
lemma gradient_moment_integrable {φ : E → ℝ} {P : E → E} (hφ : Continuous φ)
    (hP : Continuous P) {R : ℝ} (hR : ∀ x, ‖P x‖≤R)
    (hi : Integrable (fun x => ‖x‖*Real.exp (-φ x)) μ) :
    Integrable (fun x => ⟪P x,x⟫_ℝ * Real.exp (-φ x)) μ := by
  apply (hi.const_mul R).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    |⟪P x,x⟫_ℝ| * Real.exp (-φ x) ≤ (‖P x‖*‖x‖)*Real.exp (-φ x) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ ≤ (R*‖x‖)*Real.exp (-φ x) := by gcongr; exact hR x
    _ = _ := by ring

lemma coordinate_identity {φ : E → ℝ} {P : E → E}
    (hφ : ∀ x, HasFDerivAt φ (innerSL ℝ (P x)) x) (hP : Continuous P)
    {R : ℝ} (hR : ∀ x, ‖P x‖≤R)
    (hI : Integrable (fun x => Real.exp (-φ x)) μ)
    (hi : Integrable (fun x => ‖x‖*Real.exp (-φ x)) μ) (v : E) :
    (∫ x, ⟪v,x⟫_ℝ * ⟪P x,v⟫_ℝ * Real.exp (-φ x) ∂μ) =
      ‖v‖^2*(∫ x, Real.exp (-φ x) ∂μ) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  let ρ := fun x => Real.exp (-φ x)
  have hd (x w : E) : fderiv ℝ ρ x w = -⟪P x,w⟫_ℝ * ρ x := by
    have hh : HasFDerivAt ρ (Real.exp (-φ x) • -(innerSL ℝ (P x))) x := (hφ x).neg.exp
    rw [hh.fderiv]
    simp only [smul_apply,neg_apply,
      innerSL_apply_apply,smul_eq_mul,ρ]
    ring
  have hv (x w : E) : fderiv ℝ (fun y => ⟪v,y⟫_ℝ) x w= ⟪v,w⟫_ℝ :=
    congrArg (fun f : E →L[ℝ] ℝ => f w) (innerSL ℝ v).hasFDerivAt.fderiv
  have hfg : Integrable (fun x => ⟪v,x⟫_ℝ * ρ x) μ := by
    apply (hi.const_mul ‖v‖).mono' (by dsimp [ρ]; fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hh := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm v x) (Real.exp_pos (-φ x)).le
    simpa only [ρ,mul_assoc] using hh
  have hfg' : Integrable (fun x => ⟪v,x⟫_ℝ * fderiv ℝ ρ x v) μ := by
    apply (hi.const_mul (R*‖v‖^2)).mono' (by simp_rw [hd]; dsimp [ρ]; fun_prop)
    filter_upwards [] with x
    rw [hd,Real.norm_eq_abs,abs_mul,abs_mul,abs_neg,abs_of_pos (Real.exp_pos _)]
    have hvx := abs_real_inner_le_norm v x
    have hpx : |⟪P x,v⟫_ℝ|≤R*‖v‖ := (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hR x) (norm_nonneg _))
    calc
      |⟪v,x⟫_ℝ| * (|⟪P x,v⟫_ℝ| * Real.exp (-φ x)) ≤
          (‖v‖*‖x‖)*((R*‖v‖)*Real.exp (-φ x)) := by gcongr
      _ = _ := by ring
  have hf'g : Integrable (fun x => fderiv ℝ (fun y => ⟪v,y⟫_ℝ) x v*ρ x) μ := by
    simp_rw [hv]
    exact hI.const_mul _
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun x _ => (innerSL ℝ v).differentiableAt)
    (fun x _ => ((hφ x).neg.exp).differentiableAt)
  simp_rw [hd,hv,real_inner_self_eq_norm_sq] at hh
  have he : (fun x => ⟪v,x⟫_ℝ * (-⟪P x,v⟫_ℝ * ρ x)) =
      (fun x => -(⟪v,x⟫_ℝ * ⟪P x,v⟫_ℝ * ρ x)) := by funext x;ring
  rw [he,integral_neg,integral_const_mul,neg_inj] at hh
  exact hh

omit [μ.IsAddHaarMeasure] in
lemma coordinate_moment_integrable {φ : E → ℝ} {P : E → E}
    (hφ : Continuous φ) (hP : Continuous P) {R : ℝ} (hR : ∀ x, ‖P x‖≤R)
    (hi : Integrable (fun x => ‖x‖*Real.exp (-φ x)) μ) (v : E) :
    Integrable (fun x => ⟪v,x⟫_ℝ * ⟪P x,v⟫_ℝ * Real.exp (-φ x)) μ := by
  apply (hi.const_mul (R*‖v‖^2)).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hvx := abs_real_inner_le_norm v x
  have hpx : |⟪P x,v⟫_ℝ|≤R*‖v‖ := (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hR x) (norm_nonneg _))
  calc
    |⟪v,x⟫_ℝ| * |⟪P x,v⟫_ℝ| * Real.exp (-φ x) ≤
        (‖v‖*‖x‖)*(R*‖v‖)*Real.exp (-φ x) := by gcongr
    _ = _ := by ring

variable {ι : Type*} [Fintype ι]

lemma euclidean_identity (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} {P : E → E}
    (hφ : ∀ x, HasFDerivAt φ (innerSL ℝ (P x)) x) (hP : Continuous P)
    {R : ℝ} (hR : ∀ x, ‖P x‖≤R)
    (hI : Integrable (fun x => Real.exp (-φ x)) μ)
    (hi : Integrable (fun x => ‖x‖*Real.exp (-φ x)) μ) :
    (∫ x, ⟪P x,x⟫_ℝ * Real.exp (-φ x) ∂μ) =
      Fintype.card ι*(∫ x, Real.exp (-φ x) ∂μ) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have he : (fun x => ⟪P x,x⟫_ℝ * Real.exp (-φ x)) =
      (fun x => ∑ i, ⟪b i,x⟫_ℝ * ⟪P x,b i⟫_ℝ * Real.exp (-φ x)) := by
    funext x
    rw [← b.sum_inner_mul_inner (P x) x,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,integral_finsetSum _ (fun i _ => coordinate_moment_integrable μ hφc hP hR hi (b i))]
  simp_rw [coordinate_identity μ hφ hP hR hI hi,b.norm_eq_one]
  simp

lemma weighted_identity (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} {P : E → E}
    (hφ : ∀ x, HasFDerivAt φ (innerSL ℝ (P x)) x) (hP : Continuous P)
    {R : ℝ} (hR : ∀ x, ‖P x‖≤R)
    (hI : Integrable (fun x => Real.exp (-φ x)) μ)
    (hi : Integrable (fun x => ‖x‖*Real.exp (-φ x)) μ)
    (hn : (∫ x, Real.exp (-φ x) ∂μ)=1) :
    (∫ x, ⟪P x,x⟫_ℝ ∂μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) =
      Fintype.card ι := by
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hφ x).continuousAt
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ x))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul]
  simp_rw [mul_comm (Real.exp _) _]
  rw [euclidean_identity μ b hφ hP hR hI hi,hn,mul_one]

end SourceIdentity
end

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace UniformMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma supporting_plane {φ : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ Set.univ φ) (hG : ∀ x, HasGradientAt φ (G x) x) (z x : E) :
    φ z + ⟪G z, x-z⟫_ℝ ≤ φ x := by
  let a : ℝ →ᵃ[ℝ] E := AffineMap.lineMap z x
  have hc' : ConvexOn ℝ Set.univ (φ ∘ a) := by
    simpa only [Set.preimage_univ] using hc.comp_affineMap a
  have hd : HasDerivAt (φ ∘ a) ⟪G z, x-z⟫_ℝ 0 := by
    have hz : HasFDerivAt φ ((InnerProductSpace.toDual ℝ E) (G z)) (a 0) := by
      simpa [a] using (hG z).hasFDerivAt
    exact hz.comp_hasDerivAt 0 AffineMap.hasDerivAt_lineMap
  have hh := hc'.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num) hd
  simp [slope, a] at hh
  linarith

omit [FiniteDimensional ℝ E] in
lemma even_convex_min {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (he : Function.Even φ) (z : E) : φ 0 ≤ φ z := by
  have h := hc.2 (mem_univ z) (mem_univ (-z)) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1:ℝ)/2+1/2=1 by norm_num)
  rw [smul_neg, add_neg_cancel, he, smul_eq_mul, ← add_mul] at h
  norm_num at h
  exact h

lemma abs_inner_le {φ : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ φ) (he : Function.Even φ)
    (hG : ∀ x, HasGradientAt φ (G x) x) (z y : E) :
    |⟪G z,y⟫_ℝ| ≤ φ y - φ 0 + ⟪G z,z⟫_ℝ := by
  have h₁ := supporting_plane hc hG z y
  have h₂ := supporting_plane hc hG z (-y)
  have h₀ := even_convex_min hc he z
  rw [he] at h₂
  simp only [inner_sub_right, inner_neg_right] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

section Measure
variable [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [IsProbabilityMeasure ν]

lemma first_moment_bound {φ : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ φ) (he : Function.Even φ)
    (hG : ∀ x, HasGradientAt φ (G x) x) (hGc : Continuous G)
    (hi : Integrable (fun z => ⟪G z,z⟫_ℝ) ν) (y : E) :
    (∫ z, |⟪G z,y⟫_ℝ| ∂ν) ≤ φ y-φ 0 + ∫ z, ⟪G z,z⟫_ℝ ∂ν := by
  have hir : Integrable (fun z => φ y-φ 0 + ⟪G z,z⟫_ℝ) ν :=
    (integrable_const _).add hi
  have hil : Integrable (fun z => |⟪G z,y⟫_ℝ|) ν :=
    hir.mono' (hGc.inner continuous_const).abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_abs] using
          (abs_inner_le hc he hG z y))
  have h := integral_mono hil hir (abs_inner_le hc he hG · y)
  simpa [integral_add (integrable_const _) hi, integral_const, Measure.real] using h

lemma uniform_coercivity {φ : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ φ) (he : Function.Even φ)
    (hG : ∀ x, HasGradientAt φ (G x) x) (hGc : Continuous G)
    (hi : Integrable (fun z => ⟪G z,z⟫_ℝ) ν) {c d : ℝ}
    (hd : (∫ z, ⟪G z,z⟫_ℝ ∂ν) = d)
    (hm : ∀ y, c*‖y‖ ≤ ∫ z, |⟪G z,y⟫_ℝ| ∂ν) (y : E) :
    c*‖y‖-d ≤ φ y-φ 0 := by
  have h := first_moment_bound ν hc he hG hGc hi y
  rw [hd] at h
  have := hm y
  linarith

end Measure

section Ball
variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

lemma ballMoment_integrable (y : E) :
    IntegrableOn (fun x : E => |⟪x,y⟫_ℝ|) (Metric.closedBall 0 1) μ :=
  ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
    (continuous_id.inner continuous_const).abs.continuousOn

lemma continuous_ballMoment : Continuous (ballMoment μ) := by
  have hn : IntegrableOn (fun x : E => ‖x‖) (Metric.closedBall 0 1) μ :=
    ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) continuous_norm.continuousOn
  apply continuous_iff_continuousAt.mpr
  intro y₀
  apply continuousAt_of_dominated (bound := fun x : E => (‖y₀‖+1)*‖x‖)
  · exact Eventually.of_forall fun y => (ballMoment_integrable μ y).aestronglyMeasurable
  · have hy : ∀ᶠ y : E in nhds y₀, ‖y‖ < ‖y₀‖+1 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds
        (show ‖y₀‖ < ‖y₀‖ + 1 by linarith)
    filter_upwards [hy] with y hy
    exact Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs, abs_abs]
      calc
        |⟪x,y⟫_ℝ| ≤ ‖x‖*‖y‖ := abs_real_inner_le_norm x y
        _ ≤ (‖y₀‖+1)*‖x‖ := by nlinarith [norm_nonneg x]
  · exact hn.const_mul _
  · exact Eventually.of_forall fun x =>
      (continuous_const.inner continuous_id).abs.continuousAt

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsFiniteMeasureOnCompacts μ] in
lemma ballMoment_smul (a : ℝ) (y : E) :
    ballMoment μ (a • y) = |a| * ballMoment μ y := by
  simp only [ballMoment, inner_smul_right, abs_mul, integral_const_mul]

lemma ballMoment_pos_of_norm_one [μ.IsOpenPosMeasure] {y : E} (hy : ‖y‖=1) :
    0 < ballMoment μ y := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun x => abs_nonneg ⟪x,y⟫_ℝ)
    (ballMoment_integrable μ y)).mpr
  let U := {x : E | ⟪x,y⟫_ℝ ≠ 0} ∩ Metric.ball (0:E) 1
  have hU : IsOpen U :=
    (isOpen_ne.preimage (continuous_id.inner continuous_const)).inter Metric.isOpen_ball
  have hne : U.Nonempty := by
    refine ⟨(1/2:ℝ) • y, ?_, ?_⟩
    · change ⟪(1/2:ℝ) • y,y⟫_ℝ ≠ 0
      simp [real_inner_smul_left, hy]
    · simp [Metric.mem_ball, dist_zero_right, norm_smul, hy]
      norm_num
  have hm := hU.measure_pos μ hne
  exact lt_of_lt_of_le hm (measure_mono (by
    intro x hx
    exact ⟨by simpa only [Function.mem_support, abs_ne_zero, Set.mem_ofPred_eq] using hx.1,
      Metric.ball_subset_closedBall hx.2⟩))

lemma exists_ballMoment_lower [μ.IsOpenPosMeasure] [Nontrivial E] :
    ∃ c : ℝ, 0 < c ∧ ∀ y : E, c*‖y‖ ≤ ballMoment μ y := by
  have hne : (Metric.sphere (0:E) 1).Nonempty := by
    obtain ⟨y,hy⟩ := exists_norm_eq E (show (0:ℝ) ≤ 1 by norm_num)
    exact ⟨y, by simpa [Metric.mem_sphere, dist_zero_right] using hy⟩
  obtain ⟨y,hy,hm⟩ := (isCompact_sphere (0:E) 1).exists_isMinOn hne
    (continuous_ballMoment μ).continuousOn
  have hyn : ‖y‖=1 := by simpa [Metric.mem_sphere, dist_zero_right] using hy
  refine ⟨ballMoment μ y, ballMoment_pos_of_norm_one μ hyn, ?_⟩
  intro z
  by_cases hz : z=0
  · simp [hz, ballMoment]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let w : E := ‖z‖⁻¹ • z
  have hwn : ‖w‖=1 := by simp [w, norm_smul, hnz]
  have hw : w ∈ Metric.sphere (0:E) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hwn
  have hh : ballMoment μ y ≤ ballMoment μ w := hm hw
  have hz' : ‖z‖ • w = z := by simp [w, smul_smul, hnz]
  calc
    ballMoment μ y*‖z‖ ≤ ‖z‖*ballMoment μ w := by nlinarith [norm_nonneg z]
    _ = ballMoment μ (‖z‖ • w) := by
      rw [ballMoment_smul μ ‖z‖ w, abs_of_nonneg (norm_nonneg z)]
    _ = ballMoment μ z := by rw [hz']

lemma exists_first_moment_lower [μ.IsOpenPosMeasure] [Nontrivial E]
    {d : ℝ} (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : Measure E),
      ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) 1) ≤ ρ →
      (∀ y : E, Integrable (fun x => |⟪x,y⟫_ℝ|) ρ) →
      ∀ y : E, c*‖y‖ ≤ ∫ x, |⟪x,y⟫_ℝ| ∂ρ := by
  obtain ⟨a,ha,ha'⟩ := exists_ballMoment_lower μ
  refine ⟨d*a, mul_pos hd ha, ?_⟩
  intro ρ hρ hi y
  calc
    d*a*‖y‖ = d*(a*‖y‖) := by ring
    _ ≤ d*ballMoment μ y := mul_le_mul_of_nonneg_left (ha' y) hd.le
    _ = ∫ x, |⟪x,y⟫_ℝ| ∂(ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) 1)) := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hd.le]
      rfl
    _ ≤ ∫ x, |⟪x,y⟫_ℝ| ∂ρ :=
      integral_mono_measure hρ (Eventually.of_forall fun x => abs_nonneg _) (hi y)
end Ball

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma integrable_exp_neg_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E => Real.exp (-c*‖x‖)) μ := by
  let r : ℝ := Module.finrank ℝ E + 1
  have hr : (Module.finrank ℝ E : ℝ) < r := by dsimp [r]; linarith
  have hi : Integrable (fun x : E => (1+‖x‖)^(-r)) μ := integrable_one_add_norm hr
  have hl : LocallyIntegrable (fun x : E => Real.exp (-c*‖x‖)) μ :=
    (show Continuous (fun x : E => Real.exp (-c*‖x‖)) by fun_prop).locallyIntegrable
  have ht : Tendsto (fun x : E => (1:ℝ)+‖x‖) (cocompact E) atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop
  have hO := (isLittleO_exp_neg_mul_rpow_atTop hc (-r)).isBigO.comp_tendsto ht
  have hO' := hO.const_mul_left (Real.exp c)
  have hfn : (fun x : E => Real.exp c * Real.exp (-c * (1+‖x‖))) =
      (fun x : E => Real.exp (-c*‖x‖)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Function.comp_apply] at hO'
  rw [hfn] at hO'
  exact hl.integrable_of_isBigO_cocompact hO' (hi.integrableAtFilter (cocompact E))
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in

lemma centered_mass {φ : E → ℝ} (hn : (∫ x, Real.exp (-φ x) ∂μ)=1) :
    (∫ x, Real.exp (-(φ x-φ 0)) ∂μ) = Real.exp (φ 0) := by
  have he : (fun x => Real.exp (-(φ x-φ 0))) =
      (fun x => Real.exp (φ 0)*Real.exp (-φ x)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_const_mul, hn, mul_one]

lemma centered_integrable {φ : E → ℝ} (hφ : Continuous φ)
    {c d : ℝ} (hc : 0<c) (hl : ∀ y, c*‖y‖-d ≤ φ y-φ 0) :
    Integrable (fun x => Real.exp (-(φ x-φ 0))) μ := by
  refine ((integrable_exp_neg_norm μ hc).const_mul (Real.exp d)).mono'
    (Real.continuous_exp.comp (hφ.sub continuous_const).neg).aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := hl x
    linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in

lemma centered_mass_lower {φ : E → ℝ} {S : Set E} (hS : MeasurableSet S)
    (hfin : μ S ≠ ⊤) {a : ℝ} (hu : ∀ x∈S, φ x-φ 0 ≤ a)
    (hi : Integrable (fun x => Real.exp (-(φ x-φ 0))) μ) :
    Real.exp (-a)*μ.real S ≤ ∫ x, Real.exp (-(φ x-φ 0)) ∂μ := by
  let : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using lt_top_iff_ne_top.mpr hfin⟩
  have h₁ : (∫ x in S, Real.exp (-a) ∂μ) ≤
      ∫ x in S, Real.exp (-(φ x-φ 0)) ∂μ := by
    apply integral_mono_ae (integrable_const _) hi.restrict
    filter_upwards [ae_restrict_mem hS] with x hx
    exact Real.exp_le_exp.mpr (by linarith [hu x hx])
  have h₂ : (∫ x in S, Real.exp (-(φ x-φ 0)) ∂μ) ≤
      ∫ x, Real.exp (-(φ x-φ 0)) ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun x => (Real.exp_pos _).le) hi
  simpa [setIntegral_const, mul_comm] using h₁.trans h₂

lemma uniform_density_majorant {φ : E → ℝ} (hφ : Continuous φ)
    (hn : (∫ x, Real.exp (-φ x) ∂μ)=1)
    {S : Set E} (hS : MeasurableSet S) (hfin : μ S ≠ ⊤) (hpos : 0<μ.real S)
    {a c d : ℝ} (hc : 0<c) (hl : ∀ y, c*‖y‖-d ≤ φ y-φ 0)
    (hu : ∀ x∈S, φ x-φ 0 ≤ a) (y : E) :
    Real.exp (-φ y) ≤ (Real.exp d/(Real.exp (-a)*μ.real S))*
      Real.exp (-c*‖y‖) := by
  have hi := centered_integrable μ hφ hc hl
  have hm := centered_mass_lower μ hS hfin hu hi
  rw [centered_mass μ hn] at hm
  have hA : 0<Real.exp (-a)*μ.real S := mul_pos (Real.exp_pos _) hpos
  have he : Real.exp (-φ y) = Real.exp (-(φ y-φ 0))/Real.exp (φ 0) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [he]
  calc
    Real.exp (-(φ y-φ 0))/Real.exp (φ 0) ≤
        Real.exp (-(φ y-φ 0))/(Real.exp (-a)*μ.real S) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hA hm
    _ ≤ (Real.exp d*Real.exp (-c*‖y‖))/(Real.exp (-a)*μ.real S) := by
      gcongr
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hl y
      linarith
    _ = _ := by ring
end UniformMoment
namespace TruncatedMoment
open MeasureTheory Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma uniform_density_lower {V : E → ℝ} (hV : Continuous V)
    (hI : Integrable (fun x => Real.exp (-V x)) μ) :
    ∃ d > 0, ∀ R : ℝ, 2 ≤ R →
      ENNReal.ofReal d • μ.restrict (Metric.closedBall (0:E) 1) ≤ target μ R V := by
  let Z := ∫ x, Real.exp (-V x) ∂μ
  have hZ : 0<Z := integral_exp_pos hI
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:E) 1).bddAbove_image hV.continuousOn
  refine ⟨Real.exp (-M)/Z,div_pos (Real.exp_pos _) hZ,fun R hR => ?_⟩
  have hRp : 0<R := by linarith
  have hZR := partition_pos μ hV hRp
  have hpart : partition μ R V ≤ Z := integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun x => (Real.exp_pos (-V x)).le) hI
  rw [target,← withDensity_const,← withDensity_indicator measurableSet_closedBall,
    ← withDensity_indicator measurableSet_ball]
  apply withDensity_mono
  filter_upwards [] with x
  by_cases hx : x ∈ Metric.closedBall (0:E) 1
  · have hxb : x ∈ Metric.ball (0:E) R :=
      Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt (by linarith))
    rw [indicator_of_mem hx,indicator_of_mem hxb]
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr
      (neg_le_neg (hM (mem_image_of_mem _ hx)))) hZ.le).trans
        (div_le_div_of_nonneg_left (Real.exp_pos _).le hZR hpart)
  · rw [indicator_of_notMem hx]
    exact bot_le

end TruncatedMoment

namespace CompactMomentVariational
open MeasureTheory Set Filter
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma integral_density_one {φ : E → ℝ}
    (hI : Integrable (fun x => Real.exp (-φ x)) μ)
    [hp : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))))] :
    (∫ x, Real.exp (-φ x) ∂μ)=1 := by
  have he := measure_univ (μ:=μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))))
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => (Real.exp_pos (-φ x)).le)] at he
  exact ENNReal.ofReal_eq_one.mp he

lemma weighted_gradient_moment_integrable {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) {R : ℝ≥0} (hl : LipschitzWith R φ)
    (hcont : Continuous (gradient φ)) (hc : ∃ c > 0, ∃ d : ℝ, ∀ x, c*‖x‖-d ≤ φ x) :
    Integrable (fun x => ⟪gradient φ x,x⟫_ℝ)
      (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) := by
  obtain ⟨c,hc,d,ht⟩ := hc
  have hφc := hφ.continuous
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-φ x))) := by fun_prop
  rw [integrable_withDensity_iff hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact SourceIdentity.gradient_moment_integrable μ hφ.continuous hcont
    (norm_gradient_le_lipschitz hl) (SourceIdentity.integrable_norm_density μ hφ.continuous hc ht
      (integrable_exp_neg_norm μ (by positivity)))

lemma weighted_gradient_identity (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 1 φ) {R : ℝ≥0} (hl : LipschitzWith R φ)
    (hcont : Continuous (gradient φ)) (hc : ∃ c > 0, ∃ d : ℝ, ∀ x, c*‖x‖-d ≤ φ x)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))))] :
    (∫ x, ⟪gradient φ x,x⟫_ℝ ∂μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x))))
      = Fintype.card ι := by
  obtain ⟨c,hc,d,ht⟩ := hc
  have hI := tail_integrable μ hφ.continuous hc ht
  exact SourceIdentity.weighted_identity μ b
    (fun x => (hφ.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
    hcont (norm_gradient_le_lipschitz hl) hI
    (SourceIdentity.integrable_norm_density μ hφ.continuous hc ht
      (integrable_exp_neg_norm μ (by positivity))) (integral_density_one μ hI)

lemma target_first_moment_integrable {V : E → ℝ} (hV : Continuous V) {R : ℝ} (hR : 0<R)
    (y : E) : Integrable (fun x => |⟪x,y⟫_ℝ|) (TruncatedMoment.target μ R V) := by
  let : IsProbabilityMeasure (TruncatedMoment.target μ R V) := TruncatedMoment.probability μ hV hR
  apply (integrable_const (R*‖y‖)).mono' (by fun_prop)
  filter_upwards [TruncatedMoment.ae_mem_ball μ V R] with x hx
  simp only [Real.norm_eq_abs,abs_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (by simpa [dist_zero_right] using (Metric.mem_ball.mp hx).le) (norm_nonneg _))

lemma uniform_centered_coercivity [Nontrivial E] (b : OrthonormalBasis ι ℝ E)
    {V : E → ℝ} (hV : Continuous V) (hI : Integrable (fun x => Real.exp (-V x)) μ) :
    ∃ c > 0, ∀ (R : ℝ≥0), 2 ≤ R → ∀ (φ : E → ℝ),
      ConvexOn ℝ univ φ → Function.Even φ → LipschitzWith R φ → ContDiff ℝ 1 φ →
      Continuous (gradient φ) → (∃ a > 0, ∃ d : ℝ, ∀ x, a*‖x‖-d ≤ φ x) →
      IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) →
      Measure.map (gradient φ) (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (-φ x)))) =
        TruncatedMoment.target μ R V →
      ∀ y, c*‖y‖-Fintype.card ι ≤ φ y-φ 0 := by
  obtain ⟨d,hd,hlow⟩ := TruncatedMoment.uniform_density_lower μ hV hI
  obtain ⟨c,hc,hc'⟩ := UniformMoment.exists_first_moment_lower μ hd
  refine ⟨c,hc,fun R hR φ hcv hev hl hφ hcont htail hp hm y => ?_⟩
  let := hp
  apply UniformMoment.uniform_coercivity _ hcv hev
    (fun x => (hφ.differentiable (by norm_num) x).hasGradientAt) hcont
    (weighted_gradient_moment_integrable μ hφ hl hcont htail)
    (weighted_gradient_identity μ b hφ hl hcont htail) _ y
  intro z
  specialize hc' (TruncatedMoment.target μ R V) (hlow R hR)
    (target_first_moment_integrable μ hV (by positivity)) z
  rw [← hm,integral_map hcont.aemeasurable (by fun_prop)] at hc'
  exact hc'

end CompactMomentVariational

namespace UniformMoment
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma centered_upper_of_secondDiff {φ : E → ℝ} (he : Function.Even φ) {C : ℝ}
    (hd : ∀ h z, φ (z+h)+φ (z-h)-2*φ z ≤ C*‖h‖^2) (x : E) :
    φ x-φ 0 ≤ C/2*‖x‖^2 := by
  have hh := hd x 0
  simp only [zero_add,zero_sub,he x] at hh
  linarith

variable [FiniteDimensional ℝ E]

lemma gradient_zero_at_origin {φ : E → ℝ} (hc : ConvexOn ℝ univ φ) (he : Function.Even φ) :
    gradient φ 0=0 := by
  have hm : IsLocalMin φ 0 := Filter.Eventually.of_forall (even_convex_min hc he)
  simp only [gradient,hm.fderiv_eq_zero,map_zero]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma centered_normalization_bounds {c d C : ℝ} (hc : 0<c) (hC : 0≤C) :
    ∃ a b D : ℝ, 0<D ∧ ∀ φ : E → ℝ, Continuous φ →
      (∫ x, Real.exp (-φ x) ∂μ)=1 →
      (∀ x, c*‖x‖-d ≤ φ x-φ 0) →
      (∀ x, φ x-φ 0 ≤ C/2*‖x‖^2) →
      φ 0 ∈ Icc a b ∧ ∀ x, Real.exp (-φ x) ≤ D*Real.exp (-c*‖x‖) := by
  let S := Metric.closedBall (0:E) 1
  have hS : MeasurableSet S := measurableSet_closedBall
  have hf : μ S ≠ ⊤ := (isCompact_closedBall (0:E) 1).measure_ne_top
  have hp : 0<μ.real S := ENNReal.toReal_pos (Metric.measure_closedBall_pos μ 0 (by norm_num)).ne' hf
  let A := Real.exp (-(C/2))*μ.real S
  let B := Real.exp d*(∫ x : E, Real.exp (-c*‖x‖) ∂μ)
  have hA : 0<A := mul_pos (Real.exp_pos _) hp
  refine ⟨Real.log A,Real.log B,Real.exp d/A,div_pos (Real.exp_pos _) hA,?_⟩
  intro φ hφ hn hl hu
  have hi := centered_integrable μ hφ hc hl
  have hus : ∀ x ∈ S, φ x-φ 0 ≤ C/2 := by
    intro x hx
    have hnx : ‖x‖≤1 := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hx
    have hs : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
    exact (hu x).trans (by nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ C/2 by positivity)])
  have hlow : A ≤ Real.exp (φ 0) := by
    rw [← centered_mass μ hn]
    exact centered_mass_lower μ hS hf hus hi
  have hupp : Real.exp (φ 0) ≤ B := by
    rw [← centered_mass μ hn]
    calc
      _ ≤ ∫ x, Real.exp d*Real.exp (-c*‖x‖) ∂μ := by
        apply integral_mono hi ((integrable_exp_neg_norm μ hc).const_mul _)
        intro x
        change Real.exp (-(φ x-φ 0)) ≤ Real.exp d*Real.exp (-c*‖x‖)
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith [hl x]
      _ = B := by rw [integral_const_mul]
  refine ⟨⟨?_,?_⟩,fun x => uniform_density_majorant μ hφ hn hS hf hp hc hl hus x⟩
  · simpa only [Real.log_exp] using Real.log_le_log hA hlow
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hupp

end UniformMoment

namespace C11Compactness
open Set Filter
open scoped Topology NNReal InnerProductSpace
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [ProperSpace F]

omit [ProperSpace F] in
lemma normalizedLipschitz_pointwise (R : ℝ≥0) :
    ContinuousMap.toFun '' (normalizedLipschitz (E:=E) (F:=F) R) =
      {f : E → F | LipschitzWith R f ∧ f 0=0} := by
  ext f
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact hg
  · intro hf
    exact ⟨⟨f,hf.1.continuous⟩,hf,rfl⟩

lemma normalizedLipschitz_compact (R : ℝ≥0) :
    IsCompact (normalizedLipschitz (E:=E) (F:=F) R) := by
  apply ArzelaAscoli.isCompact_of_equicontinuous
  · rw [normalizedLipschitz_pointwise]
    apply (isCompact_pi_infinite (fun x : E =>
      isCompact_closedBall (0:F) ((R:ℝ)*‖x‖))).of_isClosed_subset
    · exact (isClosed_setOfPred_lipschitzWith R).inter
        (isClosed_eq (continuous_apply 0) continuous_const)
    · intro f hf x
      have h := hf.1.dist_le_mul x 0
      simpa only [hf.2,Metric.mem_closedBall,dist_zero_right] using h
  · exact Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (R:ℝ)*r)
      (by simpa using (show Continuous (fun r : ℝ => (R:ℝ)*r) by fun_prop).tendsto 0) _
      (fun x y f => f.property.1.dist_le_mul x y)

section Normed
variable [NormedSpace ℝ E]

lemma normalizedLipschitz_subsequence [FiniteDimensional ℝ E]
    {R : ℝ≥0} {f : ℕ → E → F} (hl : ∀ k, LipschitzWith R (f k))
    (h0 : ∀ k, f k 0=0) :
    ∃ (g : E → F) (s : ℕ → ℕ), LipschitzWith R g ∧ g 0=0 ∧ StrictMono s ∧
      TendstoLocallyUniformly (fun k => f (s k)) g atTop := by
  let Fs : ℕ → C(E,F) := fun k => ⟨f k,(hl k).continuous⟩
  have hm : ∀ k, Fs k ∈ normalizedLipschitz R := fun k => ⟨hl k,h0 k⟩
  obtain ⟨g,hg,s,hs,ht⟩ := (normalizedLipschitz_compact (E:=E) (F:=F) R).tendsto_subseq hm
  refine ⟨g,s,hg.1,hg.2,hs,?_⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht

end Normed

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup F] [ProperSpace F] in
lemma pointwise_cauchy_of_gradient {fs : ℕ → E → ℝ} {Gs : ℕ → E → E} {G : E → E}
    (hd : ∀ n x, HasFDerivAt (fs n) (innerSL ℝ (Gs n x)) x)
    (ht : TendstoLocallyUniformly Gs G atTop)
    (h0 : CauchySeq (fun n => fs n 0)) (x : E) :
    CauchySeq (fun n => fs n x) := by
  have ht' := (innerSL ℝ (E:=E)).uniformContinuous.comp_tendstoLocallyUniformly ht
  have hh : TendstoUniformlyOn (fun n z => innerSL ℝ (Gs n z)) (fun z => innerSL ℝ (G z))
      atTop (Metric.closedBall (0:E) (‖x‖+1)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall _ _)).mp
      ht'.tendstoLocallyUniformlyOn
  exact cauchy_map_of_uniformCauchySeqOn_fderiv Metric.isOpen_ball (convex_ball 0 (‖x‖+1)).isPreconnected
    (hh.uniformCauchySeqOn.mono Metric.ball_subset_closedBall) (fun n z _ => hd n z)
    (by simp [Metric.mem_ball]; positivity)
    (by simp [Metric.mem_ball,dist_zero_right]) h0

omit [NormedAddCommGroup F] [ProperSpace F] in

lemma subsequence {fs : ℕ → E → ℝ} {Gs : ℕ → E → E} {L : ℝ≥0} {a b : ℝ}
    (hd : ∀ n x, HasFDerivAt (fs n) (innerSL ℝ (Gs n x)) x)
    (hl : ∀ n, LipschitzWith L (Gs n)) (h0 : ∀ n, Gs n 0=0)
    (hb : ∀ n, fs n 0 ∈ Icc a b) :
    ∃ (f : E → ℝ) (G : E → E) (s : ℕ → ℕ), StrictMono s ∧
      LipschitzWith L G ∧ G 0=0 ∧ f 0 ∈ Icc a b ∧
      (∀ x, HasFDerivAt f (innerSL ℝ (G x)) x) ∧
      ContDiff ℝ 1 f ∧
      (∀ x, Tendsto (fun n => fs (s n) x) atTop (𝓝 (f x))) ∧
      TendstoLocallyUniformly (fun n => Gs (s n)) G atTop := by
  obtain ⟨m,hm,s₀,hs₀,ht₀⟩ := isCompact_Icc.tendsto_subseq hb
  obtain ⟨G,s₁,hG,hG0,hs₁,htG⟩ := normalizedLipschitz_subsequence
    (fun n => hl (s₀ n)) (fun n => h0 (s₀ n))
  let s := s₀ ∘ s₁
  have h0t : Tendsto (fun n => fs (s n) 0) atTop (𝓝 m) := ht₀.comp hs₁.tendsto_atTop
  have hf : ∀ x, ∃ y, Tendsto (fun n => fs (s n) x) atTop (𝓝 y) := fun x =>
    cauchySeq_tendsto_of_complete (pointwise_cauchy_of_gradient
      (fun n z => hd (s n) z) htG h0t.cauchy_map x)
  choose f hft using hf
  have hdf : ∀ x, HasFDerivAt f (innerSL ℝ (G x)) x := by
    intro x
    exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      ((innerSL ℝ (E:=E)).uniformContinuous.comp_tendstoLocallyUniformly htG).tendstoLocallyUniformlyOn
      (fun n z _ => hd (s n) z) (fun z _ => hft z) (mem_univ x)
  refine ⟨f,G,s,hs₀.comp hs₁,hG,hG0,?_,hdf,?_,hft,htG⟩
  · have he : f 0=m := tendsto_nhds_unique (hft 0) h0t
    simpa [he] using hm
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hdf x).differentiableAt,?_⟩
    have he : fderiv ℝ f = fun x => innerSL ℝ (G x) := funext fun x => (hdf x).fderiv
    rw [he]
    exact (innerSL ℝ (E:=E)).continuous.comp hG.continuous

end C11Compactness
end

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace MomentLimits
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E)

omit [MeasurableSpace E] [BorelSpace E] in
lemma continuous_density {φ : E → ℝ} (hφ : Continuous φ) : Continuous (density φ) :=
  Real.continuous_exp.comp hφ.neg

lemma integral_source {φ : E → ℝ} (hφ : Continuous φ) (f : E → ℝ) :
    (∫ x, f x ∂source μ φ) = ∫ x, density φ x*f x ∂μ := by
  rw [source, integral_withDensity_eq_integral_toReal_smul
    (continuous_density hφ).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [density, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]

omit [NormedAddCommGroup E] [BorelSpace E] in
lemma source_finite {φ : E → ℝ} (hi : Integrable (density φ) μ) :
    IsFiniteMeasure (source μ φ) := isFiniteMeasure_withDensity_ofReal hi.2

lemma integral_density_tendsto {φs : ℕ → E → ℝ} {φ : E → ℝ} {M : E → ℝ}
    (hc : ∀ n, Continuous (φs n)) (hi : Integrable M μ)
    (hb : ∀ n x, density (φs n) x ≤ M x)
    (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    Tendsto (fun n => ∫ x, density (φs n) x ∂μ) atTop
      (𝓝 (∫ x, density φ x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence M
    (fun n => (continuous_density (hc n)).aestronglyMeasurable) hi
  · intro n
    exact Eventually.of_forall fun x => by
      simpa [density, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb n x
  · exact Eventually.of_forall fun x => Real.continuous_exp.continuousAt.tendsto.comp (ht x).neg

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] in
lemma density_le_limit_bound {φs : ℕ → E → ℝ} {φ : E → ℝ} {M : E → ℝ}
    (hb : ∀ n x, density (φs n) x ≤ M x)
    (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) (x : E) :
    density φ x ≤ M x := by
  apply le_of_tendsto' (Real.continuous_exp.continuousAt.tendsto.comp (ht x).neg)
  exact fun n => hb n x

lemma density_integrable_limit {φs : ℕ → E → ℝ} {φ : E → ℝ} {M : E → ℝ}
    (hφ : Continuous φ) (hi : Integrable M μ)
    (hb : ∀ n x, density (φs n) x ≤ M x)
    (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    Integrable (density φ) μ := by
  apply hi.mono' (continuous_density hφ).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa [density, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      density_le_limit_bound hb ht x

lemma density_integral_one {φs : ℕ → E → ℝ} {φ : E → ℝ} {M : E → ℝ}
    (hc : ∀ n, Continuous (φs n)) (hi : Integrable M μ)
    (hb : ∀ n x, density (φs n) x ≤ M x)
    (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hn : ∀ n, (∫ x, density (φs n) x ∂μ)=1) :
    (∫ x, density φ x ∂μ)=1 := by
  have h := integral_density_tendsto μ hc hi hb ht
  simp only [hn] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

omit [NormedAddCommGroup E] [BorelSpace E] in
lemma source_probability {φ : E → ℝ}
    (hi : Integrable (density φ) μ) (hn : (∫ x, density φ x ∂μ)=1) :
    IsProbabilityMeasure (source μ φ) := by
  constructor
  rw [source, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x =>
    (Real.exp_pos (-φ x)).le), hn]
  simp

lemma integral_composed_tendsto {φs : ℕ → E → ℝ} {φ : E → ℝ}
    {Gs : ℕ → E → E} {G : E → E} {M : E → ℝ}
    (hc : ∀ n, Continuous (φs n)) (hGs : ∀ n, Continuous (Gs n))
    (hi : Integrable M μ) (hb : ∀ n x, density (φs n) x ≤ M x)
    (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hGt : ∀ x, Tendsto (fun n => Gs n x) atTop (𝓝 (G x))) (f : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, density (φs n) x*f (Gs n x) ∂μ) atTop
      (𝓝 (∫ x, density φ x*f (G x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => M x*‖f‖)
    (fun n => ((continuous_density (hc n)).mul (f.continuous.comp (hGs n))).aestronglyMeasurable)
    (hi.mul_const ‖f‖)
  · intro n
    exact Eventually.of_forall fun x => by
      change ‖density (φs n) x * f (Gs n x)‖ ≤ M x * ‖f‖
      rw [norm_mul, Real.norm_eq_abs]
      rw [abs_of_pos (show 0 < density (φs n) x from Real.exp_pos _)]
      exact mul_le_mul (hb n x) (f.norm_coe_le_norm _) (norm_nonneg _)
        ((Real.exp_pos _).le.trans (hb n x))
  · exact Eventually.of_forall fun x =>
      (Real.continuous_exp.continuousAt.tendsto.comp (ht x).neg).mul
        (f.continuous.continuousAt.tendsto.comp (hGt x))

theorem map_source_limit {φs : ℕ → E → ℝ} {φ : E → ℝ}
    {Gs : ℕ → E → E} {G : E → E} {M : E → ℝ}
    (hc : ∀ n, Continuous (φs n)) (hφ : Continuous φ)
    (hGs : ∀ n, Continuous (Gs n)) (hG : Continuous G)
    (hi : Integrable M μ) (hb : ∀ n x, density (φs n) x ≤ M x)
    (ht : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x)))
    (hGt : ∀ x, Tendsto (fun n => Gs n x) atTop (𝓝 (G x)))
    (νs : ℕ → Measure E) (ν : Measure E) [IsFiniteMeasure ν]
    (hm : ∀ n, Measure.map (Gs n) (source μ (φs n))=νs n)
    (hw : ∀ f : E →ᵇ ℝ, Tendsto (fun n => ∫ x, f x ∂νs n) atTop
      (𝓝 (∫ x, f x ∂ν))) :
    Measure.map G (source μ φ)=ν := by
  have hif := density_integrable_limit μ hφ hi hb ht
  let : IsFiniteMeasure (source μ φ) := source_finite μ hif
  have his n : Integrable (density (φs n)) μ := by
    apply hi.mono' (continuous_density (hc n)).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simpa [density, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb n x
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hln := integral_composed_tendsto μ hc hGs hi hb ht hGt f
  have hneq (n : ℕ) : (∫ x, density (φs n) x*f (Gs n x) ∂μ) =
      ∫ x, f x ∂νs n := by
    let : IsFiniteMeasure (source μ (φs n)) := source_finite μ (his n)
    rw [← hm n, integral_map (hGs n).aemeasurable f.continuous.aestronglyMeasurable,
      integral_source μ (hc n)]
  have heq : (∫ x, density φ x*f (G x) ∂μ) = ∫ x, f x ∂ν := by
    simp only [hneq] at hln
    exact tendsto_nhds_unique hln (hw f)
  rw [integral_map hG.aemeasurable f.continuous.aestronglyMeasurable,
    integral_source μ hφ, heq]

lemma normalized_exhaustion {w : E → ℝ} (hi : Integrable w μ)
    (hne : (∫ x, w x ∂μ) ≠ 0) (S : ℕ → Set E)
    (hS : ∀ n, MeasurableSet (S n)) (hinc : Monotone S) (hexh : (⋃ n, S n)=univ)
    (f : E →ᵇ ℝ) :
    Tendsto (fun n => (∫ x in S n, w x*f x ∂μ)/(∫ x in S n, w x ∂μ)) atTop
      (𝓝 ((∫ x, w x*f x ∂μ)/(∫ x, w x ∂μ))) := by
  have hif : Integrable (fun x => w x*f x) μ := by
    apply (hi.norm.mul_const ‖f‖).mono'
      (hi.aestronglyMeasurable.mul f.continuous.aestronglyMeasurable)
    exact Eventually.of_forall fun x => by
      change ‖w x * f x‖ ≤ ‖w x‖ * ‖f‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)
  have h₁ := tendsto_setIntegral_of_monotone hS hinc (hif.integrableOn (s:=⋃ n, S n))
  have h₂ := tendsto_setIntegral_of_monotone hS hinc (hi.integrableOn (s:=⋃ n, S n))
  simp only [hexh, Measure.restrict_univ] at h₁ h₂
  exact h₁.div h₂ hne

end
end MomentLimits

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section
namespace GlobalMoment
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
lemma supporting_plane {φ : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ Set.univ φ) (hG : ∀ x, HasGradientAt φ (G x) x) (z x : E) :
    φ z + ⟪G z, x-z⟫_ℝ ≤ φ x := by
  let a : ℝ →ᵃ[ℝ] E := AffineMap.lineMap z x
  have hc' : ConvexOn ℝ Set.univ (φ ∘ a) := by
    simpa only [Set.preimage_univ] using hc.comp_affineMap a
  have hd : HasDerivAt (φ ∘ a) ⟪G z, x-z⟫_ℝ 0 := by
    have hz : HasFDerivAt φ ((InnerProductSpace.toDual ℝ E) (G z)) (a 0) := by
      simpa [a] using (hG z).hasFDerivAt
    exact hz.comp_hasDerivAt 0 AffineMap.hasDerivAt_lineMap
  have hh := hc'.le_slope_of_hasDerivAt (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num) hd
  simp [slope, a] at hh
  linarith

lemma tilted_potential_coercive {φ : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ φ) (hG : ∀ x, HasGradientAt φ (G x) x)
    (hd : DenseRange G) (x₀ : E) :
    ∃ b : ℝ, ∀ y : E, ‖y‖-b ≤ φ y-⟪x₀,y⟫_ℝ := by
  classical
  let U : E → Set E := fun z => {u | 1 < ⟪G z-x₀,u⟫_ℝ}
  have hU : ∀ z, IsOpen (U z) := fun z =>
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  have hcover : Metric.sphere (0:E) 1 ⊆ ⋃ z, U z := by
    intro u hu
    have hun : ‖u‖=1 := by simpa [Metric.mem_sphere, dist_zero_right] using hu
    obtain ⟨z,hz⟩ := hd.exists_dist_lt (x₀+(2:ℝ) • u) (show (0:ℝ)<1/2 by norm_num)
    rw [dist_comm, dist_eq_norm] at hz
    have hh := abs_real_inner_le_norm (G z-(x₀+(2:ℝ) • u)) u
    rw [hun, mul_one, inner_sub_left, inner_add_left, real_inner_smul_left] at hh
    have huin : ⟪u,u⟫_ℝ=1 := by simp [hun]
    rw [huin] at hh
    refine mem_iUnion.mpr ⟨z, ?_⟩
    change 1 < ⟪G z-x₀,u⟫_ℝ
    rw [inner_sub_left]
    have := (abs_le.mp hh).1
    linarith
  obtain ⟨s,hs⟩ := (isCompact_sphere (0:E) 1).elim_finite_subcover U hU hcover
  let β : E → ℝ := fun z => φ z-⟪G z,z⟫_ℝ
  let b : ℝ := |φ 0| + ∑ z ∈ s, |β z|
  have hsum : 0 ≤ ∑ z ∈ s, |β z| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨b, ?_⟩
  intro y
  by_cases hy : y=0
  · subst y
    simp only [norm_zero, inner_zero_right, sub_zero, zero_sub]
    dsimp [b]
    nlinarith [neg_abs_le (φ 0)]
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  let u : E := ‖y‖⁻¹ • y
  have hun : ‖u‖=1 := by simp [u, norm_smul, hn]
  have hu : u ∈ Metric.sphere (0:E) 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hun
  obtain ⟨z,hz⟩ := mem_iUnion.mp (hs hu)
  obtain ⟨hzs,hzu⟩ := mem_iUnion.mp hz
  have hβ := Finset.single_le_sum (fun z _ => abs_nonneg (β z)) hzs
  have hβ' : -b ≤ β z := by
    dsimp [b]
    nlinarith [neg_abs_le (β z), abs_nonneg (φ 0)]
  have hsupport := supporting_plane hc hG z y
  rw [inner_sub_right] at hsupport
  have hyu : y = ‖y‖ • u := by simp [u, smul_smul, hn]
  have hg : ‖y‖ ≤ ⟪G z-x₀,y⟫_ℝ := by
    conv_rhs => rw [hyu, inner_smul_right]
    have hzu' : 1 < ⟪G z-x₀,u⟫_ℝ := hzu
    nlinarith [norm_nonneg y]
  rw [inner_sub_left] at hg
  dsimp [β] at hβ'
  linarith

theorem gradient_surjective_of_dense {φ : E → ℝ} {G : E → E}
    (hc : ConvexOn ℝ univ φ) (hG : ∀ x, HasGradientAt φ (G x) x)
    (hd : DenseRange G) : Function.Surjective G := by
  intro x₀
  obtain ⟨b,hb⟩ := tilted_potential_coercive hc hG hd x₀
  let f : E → ℝ := fun y => φ y-⟪x₀,y⟫_ℝ
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun x =>
    (hG x).hasFDerivAt.continuousAt
  have hfc : Continuous f := hφc.sub (continuous_const.inner continuous_id)
  have hlarge : ∀ᶠ y : E in cocompact E, f 0 ≤ f y := by
    have hn : ∀ᶠ y : E in cocompact E, f 0+b ≤ ‖y‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (f 0+b))
    filter_upwards [hn] with y hy
    have := hb y
    change f 0 ≤ f y
    change ‖y‖-b ≤ f y at this
    linarith
  obtain ⟨z,hz⟩ := hfc.exists_forall_le' 0 hlarge
  have hmin : IsLocalMin f z :=
    (isMinOn_univ_iff.mpr hz).isLocalMin (by simp)
  have hfder : HasFDerivAt f
      ((InnerProductSpace.toDual ℝ E) (G z) - (InnerProductSpace.toDual ℝ E) x₀) z := by
    exact (hG z).hasFDerivAt.sub ((InnerProductSpace.toDual ℝ E) x₀).hasFDerivAt
  have heq := hmin.hasFDerivAt_eq_zero hfder
  refine ⟨z, ?_⟩
  exact (InnerProductSpace.toDual ℝ E).injective (sub_eq_zero.mp heq)

variable [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma denseRange_of_pushforward (ν μ : Measure E) [μ.IsOpenPosMeasure]
    {G : E → E} (hG : Continuous G) (hm : Measure.map G ν = μ) : DenseRange G := by
  rw [Metric.denseRange_iff]
  intro x r hr
  have hpos : 0 < ν (G ⁻¹' Metric.ball x r) := by
    rw [← Measure.map_apply hG.measurable measurableSet_ball, hm]
    exact Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr hr)
  have hne : (G ⁻¹' Metric.ball x r).Nonempty := nonempty_of_measure_ne_zero hpos.ne'
  obtain ⟨z,hz⟩ := hne
  exact ⟨z, by simpa [Metric.mem_ball, dist_comm] using hz⟩

theorem gradient_surjective_of_pushforward (ν μ : Measure E) [μ.IsOpenPosMeasure]
    {φ : E → ℝ} {G : E → E} (hc : ConvexOn ℝ univ φ)
    (hG : ∀ x, HasGradientAt φ (G x) x) (hGc : Continuous G)
    (hm : Measure.map G ν = μ) : Function.Surjective G :=
  gradient_surjective_of_dense hc hG (denseRange_of_pushforward ν μ hGc hm)
end GlobalMoment

namespace CompactMomentVariational
section
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology BoundedContinuousFunction NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma normalizedSource_openPos {V : E → ℝ} (hV : Continuous V)
    (hI : Integrable (fun x => Real.exp (-V x)) μ) :
    (normalizedSource μ V).IsOpenPosMeasure := by
  have hp := integral_exp_pos hI
  have hm : Measurable (fun x => ENNReal.ofReal (Real.exp (-V x)/(∫ y,Real.exp (-V y) ∂μ))) := by
    fun_prop
  have ha : μ ≪ normalizedSource μ V := withDensity_absolutelyContinuous' hm.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (div_pos (Real.exp_pos _) hp)).ne')
  exact ⟨fun U hU hn hz => hU.measure_ne_zero μ hn (ha hz)⟩

lemma integral_truncated_target {V : E → ℝ} (hV : Continuous V) {R : ℝ} (hR : 0<R)
    (f : E → ℝ) :
    (∫ x, f x ∂TruncatedMoment.target μ R V) =
      (∫ x in Metric.ball (0:E) R, Real.exp (-V x)*f x ∂μ)/TruncatedMoment.partition μ R V := by
  have hZ := TruncatedMoment.partition_pos μ hV hR
  have hm : Measurable (fun x => ENNReal.ofReal
      (Real.exp (-V x)/TruncatedMoment.partition μ R V)) := by fun_prop
  rw [TruncatedMoment.target,integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le),smul_eq_mul]
  rw [← integral_div]
  congr 1
  funext x
  ring

lemma truncated_target_tendsto {V : E → ℝ} (hV : Continuous V)
    (hI : Integrable (fun x => Real.exp (-V x)) μ) (f : E →ᵇ ℝ) :
    Tendsto (fun n : ℕ => ∫ x, f x ∂TruncatedMoment.target μ ((n:ℝ)+2) V) atTop
      (𝓝 (∫ x, f x ∂normalizedSource μ V)) := by
  have ht := MomentLimits.normalized_exhaustion μ hI (integral_exp_pos hI).ne'
    (fun n : ℕ => Metric.ball (0:E) ((n:ℝ)+2)) (fun _ => measurableSet_ball)
    (fun n m hnm => Metric.ball_subset_ball (by exact_mod_cast Nat.add_le_add_right hnm 2))
  have he : (⋃ n : ℕ, Metric.ball (0:E) ((n:ℝ)+2))=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := exists_nat_gt ‖x‖
    apply mem_iUnion.mpr
    exact ⟨n,by simp only [Metric.mem_ball,dist_zero_right]; linarith⟩
  specialize ht he f
  have heq (n : ℕ) := integral_truncated_target μ hV (show 0<(n:ℝ)+2 by positivity) f
  simp_rw [heq]
  rw [integral_normalizedSource μ hV.measurable hI]
  have hn : (∫ x, f x * Real.exp (-V x) ∂μ) = ∫ x, Real.exp (-V x) * f x ∂μ :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [hn]
  exact ht

theorem exists_C11_global [Nontrivial E] (b : OrthonormalBasis ι ℝ E)
    {V : E → ℝ} (hV : Continuous V) (hVe : Function.Even V)
    (hI : Integrable (fun x => Real.exp (-V x)) μ)
    {ε : ℝ} (hε : 0<ε)
    (hcurv : ∀ x y, ε/8*‖x-y‖^2 ≤ (V x+V y)/2-V ((1/2:ℝ) • (x+y))) :
    ∃ φ : E → ℝ, ConvexOn ℝ univ φ ∧ Function.Even φ ∧ ContDiff ℝ 1 φ ∧
      LipschitzWith (Real.toNNReal (16/ε)) (gradient φ) ∧
      (∀ h z, WeakMomentBound.secondDiff φ h z ≤ 4/ε*‖h‖^2) ∧
      (∃ c > 0, ∃ d : ℝ, ∀ z, c*‖z‖-d ≤ φ z) ∧
      IsProbabilityMeasure (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) ∧
      Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
        normalizedSource μ V ∧ Function.Surjective (gradient φ) := by
  classical
  let R : ℕ → ℝ≥0 := fun n => n+2
  have hRp (n) : 0<R n := by dsimp [R]; positivity
  choose fs hcv hev hl hC hg hcap htail hprob hb hm using
    (fun n => exists_C11_truncated μ b hV hVe hε hcurv (hRp n))
  obtain ⟨c,hc,hcoer⟩ := uniform_centered_coercivity μ b hV hI
  have hlow n x : c*‖x‖-Fintype.card ι ≤ fs n x-fs n 0 :=
    hcoer (R n) (by change (2:ℝ) ≤ (n:ℝ)+2; linarith [Nat.cast_nonneg (α:=ℝ) n])
      (fs n) (hcv n) (hev n) (hl n) (hC n) (hg n).continuous (htail n) (hprob n) (hm n) x
  have hup n x : fs n x-fs n 0 ≤ (4/ε)/2*‖x‖^2 :=
    UniformMoment.centered_upper_of_secondDiff (hev n) (hcap n) x
  have hnorm n : (∫ x,Real.exp (-fs n x) ∂μ)=1 := by
    let := hprob n
    obtain ⟨c,hc,d,hd⟩ := htail n
    exact integral_density_one μ (tail_integrable μ (hC n).continuous hc hd)
  obtain ⟨a,a',D,hD,hbound⟩ := UniformMoment.centered_normalization_bounds μ hc
    (show 0≤4/ε by positivity) (d:=(Fintype.card ι:ℝ))
  have hbound' n := hbound (fs n) (hC n).continuous (hnorm n) (hlow n) (hup n)
  obtain ⟨φ,G,s,hs,hG,hG0,hφ0,hdf,hφ,hft,hGt⟩ := C11Compactness.subsequence
    (fun n x => ((hC n).differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
    hg (fun n => UniformMoment.gradient_zero_at_origin (hcv n) (hev n)) (fun n => (hbound' n).1)
  have hge : gradient φ=G := funext fun x =>
    (hasGradientAt_iff_hasFDerivAt.mpr (hdf x)).gradient
  have hφcv : ConvexOn ℝ univ φ := by
    refine ⟨convex_univ,fun x hx y hy a b ha hb hab => ?_⟩
    apply le_of_tendsto_of_tendsto (hft (a • x+b • y))
      (((hft x).const_mul a).add ((hft y).const_mul b))
    exact Eventually.of_forall fun n => (hcv (s n)).2 hx hy ha hb hab
  have hφev : Function.Even φ := fun x => by
    have heq : (fun n => fs (s n) (-x))=(fun n => fs (s n) x) := funext fun n => hev (s n) x
    have ht := hft (-x)
    rw [heq] at ht
    exact tendsto_nhds_unique ht (hft x)
  have hcapφ : ∀ h z, WeakMomentBound.secondDiff φ h z ≤ 4/ε*‖h‖^2 := by
    intro h z
    apply le_of_tendsto' (((hft (z+h)).add (hft (z-h))).sub ((hft z).const_mul 2))
    exact fun n => hcap (s n) h z
  have htailφ : ∀ x, c*‖x‖-((Fintype.card ι:ℝ)-φ 0) ≤ φ x := by
    intro x
    have h := ge_of_tendsto' ((hft x).sub (hft 0)) (fun n => hlow (s n) x)
    linarith
  let M : E → ℝ := fun x => D*Real.exp (-c*‖x‖)
  have hMI : Integrable M μ := (integrable_exp_neg_norm μ hc).const_mul D
  have hMb n x : MomentLimits.density (fs (s n)) x ≤ M x := (hbound' (s n)).2 x
  have hmass := MomentLimits.density_integral_one μ (fun n => (hC (s n)).continuous)
    hMI hMb hft (fun n => hnorm (s n))
  have hφI := MomentLimits.density_integrable_limit μ hφ.continuous hMI hMb hft
  have hp := MomentLimits.source_probability μ hφI hmass
  let : IsProbabilityMeasure (normalizedSource μ V) := normalizedSource_probability μ hI
  have hmap : Measure.map G (MomentLimits.source μ φ)=normalizedSource μ V :=
    MomentLimits.map_source_limit μ (fun n => (hC (s n)).continuous) hφ.continuous
      (fun n => (hg (s n)).continuous) hG.continuous hMI hMb hft
      (fun x => hGt.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)) (fun n => TruncatedMoment.target μ (R (s n)) V) (normalizedSource μ V)
      (fun n => hm (s n)) (fun f => (truncated_target_tendsto μ hV hI f).comp hs.tendsto_atTop)
  have honto : Function.Surjective G := by
    let := normalizedSource_openPos μ hV hI
    exact GlobalMoment.gradient_surjective_of_pushforward (MomentLimits.source μ φ)
      (normalizedSource μ V) hφcv (fun x => hasGradientAt_iff_hasFDerivAt.mpr (hdf x))
      hG.continuous hmap
  refine ⟨φ,hφcv,hφev,hφ,?_,hcapφ,⟨c,hc,_,htailφ⟩,hp,?_,?_⟩
  · rw [hge]; exact hG
  · rw [hge]; exact hmap
  · rw [hge]; exact honto

end

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [MeasurableSpace E] [BorelSpace E] in
lemma finite_dual_of_surjective_gradient {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) (hs : Function.Surjective (gradient φ)) :
    ∀ x ∈ (univ : Set E), BddAbove ((fun z => ⟪z,x⟫_ℝ-φ z) '' univ) := by
  intro x _
  obtain ⟨z,rfl⟩ := hs x
  refine ⟨⟪z,gradient φ z⟫_ℝ-φ z,?_⟩
  rintro _ ⟨w,_,rfl⟩
  have hh := convex_supporting_gradient hc (hd z) w
  dsimp only
  rw [inner_sub_right] at hh
  have hw : ⟪gradient φ z,w⟫_ℝ=⟪w,gradient φ z⟫_ℝ := real_inner_comm _ _
  have hz : ⟪gradient φ z,z⟫_ℝ=⟪z,gradient φ z⟫_ℝ := real_inner_comm _ _
  rw [hw,hz] at hh
  linarith

lemma C1_inverse {φ V : E → ℝ} (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    (hs : Function.Surjective (gradient φ))
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource μ V) :
    ∀ᵐ z ∂μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z))),
      gradient (dualOn univ φ) (gradient φ z)=z := by
  have hb := finite_dual_of_surjective_gradient hc hd hs
  have ha : ∀ᵐ x ∂normalizedSource μ V, DifferentiableAt ℝ (dualOn univ φ) x := by
    filter_upwards [(withDensity_absolutelyContinuous μ _).ae_le
      (convex_ae_differentiable isOpen_univ (convexOn_dualOn convex_univ hb))] with x hx
    exact hx (mem_univ x)
  rw [← hm] at ha
  filter_upwards [ae_of_ae_map (gradient_measurable φ).aemeasurable ha] with z hz
  exact inverse_gradient isOpen_univ hc (hd z) (mem_univ _) hb hz

lemma C1_weak_MA {φ V : E → ℝ} (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    (hs : Function.Surjective (gradient φ)) (hV : Continuous V)
    (hI : Integrable (fun x => Real.exp (-V x)) μ)
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource μ V) :
    Measure.map (gradient (dualOn univ φ)) μ =
      μ.withDensity (fun z => ENNReal.ofReal
        ((∫ x,Real.exp (-V x) ∂μ)*Real.exp (V (gradient φ z)-φ z))) := by
  let Z := ∫ x,Real.exp (-V x) ∂μ
  let w := fun x => ENNReal.ofReal (Real.exp (-V x)/Z)
  let σ := μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))
  let ν := normalizedSource μ V
  have hZ : 0<Z := integral_exp_pos hI
  have hw : Measurable w := (hV.neg.rexp.measurable.div_const Z).ennreal_ofReal
  have hinv : ν.withDensity (fun x => (w x)⁻¹)=μ := withDensity_inv_same₀ hw.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_ne_zero_iff.mpr (div_pos (Real.exp_pos _) hZ))
    (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  conv_lhs => rw [← hinv]
  have hr := reverse_weighted (gradient_measurable _) (gradient_measurable _) hm
    (C1_inverse μ hc hd hs hm) hw.inv
  exact hr.trans (by
    change σ.withDensity (fun z => (w (gradient φ z))⁻¹)=_
    dsimp only [σ]
    refine (withDensity_mul μ hd.continuous.neg.rexp.measurable.ennreal_ofReal
      (hw.inv.comp (gradient_measurable φ))).symm.trans ?_
    congr 1
    funext z
    dsimp only [Pi.mul_apply,Pi.inv_apply,Pi.neg_apply,Function.comp_apply,w]
    rw [← ENNReal.ofReal_inv_of_pos (div_pos (Real.exp_pos _) hZ),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    dsimp only [Z]
    simp only [Real.exp_neg,inv_div,div_inv_eq_mul,Real.exp_sub]
    ring)

omit [MeasurableSpace E] [BorelSpace E] in
lemma convex_gradient_derivative_positive {φ : E → ℝ} (hc : ConvexOn ℝ univ φ)
    (hd : Differentiable ℝ φ) {z : E} (hg : DifferentiableAt ℝ (gradient φ) z) :
    (fderiv ℝ (gradient φ) z).toLinearMap.IsPositive := by
  refine ⟨?_,fun v => supporting_derivative_nonneg
    (fun x w => convex_supporting_gradient hc (hd x) w) hg.hasFDerivAt v⟩
  intro v w
  have hh := second_derivative_symmetric (fun x => (hd x).hasGradientAt.hasFDerivAt)
    ((InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.hasFDerivAt.comp z hg.hasFDerivAt) v w
  change ⟪(fderiv ℝ (gradient φ) z) v,w⟫_ℝ=⟪(fderiv ℝ (gradient φ) z) w,v⟫_ℝ at hh
  exact hh.trans (real_inner_comm _ _)

theorem C11_ae_positive_MA (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    {L : ℝ≥0} (hl : LipschitzWith L (gradient φ))
    (hs : Function.Surjective (gradient φ)) (hV : Continuous V)
    (hI : Integrable (fun x => Real.exp (-V x)) μ)
    (hm : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource μ V) :
    ∀ᵐ z ∂μ, DifferentiableAt ℝ (gradient φ) z ∧
      (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient φ) z).toLinearMap).PosDef ∧
      Real.log (fderiv ℝ (gradient φ) z).det =
        V (gradient φ z)+Real.log (∫ x,Real.exp (-V x) ∂μ)-φ z := by
  let σ := μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))
  let ν := normalizedSource μ V
  let Z := ∫ x,Real.exp (-V x) ∂μ
  have hZ : 0<Z := integral_exp_pos hI
  have hμσ : μ ≪ σ := withDensity_absolutelyContinuous'
    hd.continuous.neg.rexp.measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
  have hμν : μ.restrict univ ≪ ν := by
    rw [Measure.restrict_univ]
    exact withDensity_absolutelyContinuous'
      (hV.neg.rexp.measurable.div_const Z).ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_ne_zero_iff.mpr (div_pos (Real.exp_pos _) hZ))
  have ha : ∀ᵐ z ∂μ, z ∈ (univ : Set E) ∧
      HasFDerivWithinAt (gradient φ) (fderiv ℝ (gradient φ) z) univ z := by
    filter_upwards [hl.ae_differentiableAt (μ:=μ)] with z hz
    exact ⟨mem_univ z,hz.hasFDerivAt.hasFDerivWithinAt⟩
  have hj := MomentJacobian.jacobian_of_ae_inverse_within μ MeasurableSet.univ
    (gradient_measurable _) (gradient_measurable _) ha hm hμσ
    (withDensity_absolutelyContinuous _ _) hμν (C1_inverse μ hc hd hs hm)
    (Eventually.of_forall fun z => mem_univ (gradient φ z))
  rw [Measure.restrict_univ] at hj
  have he := hj.trans (C1_weak_MA μ hc hd hs hV hI hm)
  have hJm : Measurable (fun z => |(fderiv ℝ (gradient φ) z).det|) :=
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ _)).abs
  have hWm : Measurable (fun z => Z*Real.exp (V (gradient φ z)-φ z)) :=
    measurable_const.mul ((hV.measurable.comp (gradient_measurable _)).sub hd.continuous.measurable).exp
  have hae := (withDensity_eq_iff_of_sigmaFinite hJm.ennreal_ofReal.aemeasurable
    hWm.ennreal_ofReal.aemeasurable).mp he
  filter_upwards [hl.ae_differentiableAt (μ:=μ),hae] with z hz hj
  have hps := (LinearMap.posSemidef_toMatrix_iff b).mpr (convex_gradient_derivative_positive hc hd hz)
  have hdeta : (LinearMap.toMatrix b.toBasis b.toBasis
      (fderiv ℝ (gradient φ) z).toLinearMap).det=(fderiv ℝ (gradient φ) z).det :=
    LinearMap.det_toMatrix b.toBasis _
  have hdet0 : 0 ≤ (fderiv ℝ (gradient φ) z).det := hdeta ▸ hps.det_nonneg
  have hdet : (fderiv ℝ (gradient φ) z).det=Z*Real.exp (V (gradient φ z)-φ z) := by
    have hh := (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (mul_nonneg hZ.le (Real.exp_pos _).le)).mp hj
    rwa [abs_of_nonneg hdet0] at hh
  refine ⟨hz,hps.posDef_iff_det_ne_zero.mpr ?_,?_⟩
  · rw [hdeta,hdet]; exact (mul_pos hZ (Real.exp_pos _)).ne'
  · rw [hdet,Real.log_mul hZ.ne' (Real.exp_ne_zero _),Real.log_exp]
    ring

end CompactMomentVariational

namespace LocalEllipticity
open Set Metric
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma positive_closed : IsClosed {A : E →L[ℝ] E | A.toLinearMap.IsPositive} := by
  have hs : IsClosed {A : E →L[ℝ] E | ∀ v w, ⟪A v,w⟫_ℝ=⟪v,A w⟫_ℝ} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_iInter
    intro w
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hp : IsClosed {A : E →L[ℝ] E | ∀ v, 0 ≤ ⟪A v,v⟫_ℝ} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    exact isClosed_le continuous_const (by fun_prop)
  exact hs.inter hp

omit [FiniteDimensional ℝ E] in
lemma positive_inner (b : OrthonormalBasis ι ℝ E) {A : E →L[ℝ] E}
    (hA : A.toLinearMap.IsPositive) (hd : A.det ≠ 0) (v : E) (hv : v ≠ 0) :
    0 < ⟪A v,v⟫_ℝ := by
  have hm := (LinearMap.posSemidef_toMatrix_iff b).mpr hA
  have hpd := hm.posDef_iff_det_ne_zero.mpr ((LinearMap.det_toMatrix b.toBasis _).trans_ne hd)
  have hcoord : (b.toBasis.repr v : ι → ℝ) ≠ 0 := by
    intro he
    have hz : b.toBasis.repr v = 0 := DFunLike.coe_injective he
    exact hv (b.toBasis.repr.injective (by simpa using hz))
  have hh := hpd.dotProduct_mulVec_pos hcoord
  rw [LinearMap.toMatrix_mulVec_repr] at hh
  have he (w : E) : (b.toBasis.repr w : ι → ℝ) = WithLp.ofLp (b.repr w) := by
    ext i
    exact b.coe_toBasis_repr_apply w i
  rw [he v] at hh
  change 0 < star (b.repr v).ofLp ⬝ᵥ (b.toBasis.repr (A v) : ι → ℝ) at hh
  rw [he (A v)] at hh
  have hi := b.repr.inner_map_map v (A v)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
  simp only [star_trivial] at hh hi
  rw [dotProduct_comm] at hi
  rw [hi] at hh
  simpa only [real_inner_comm] using hh

lemma uniform_coercivity (b : OrthonormalBasis ι ℝ E) (C : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ δ > 0, ∀ A : E →L[ℝ] E, A.toLinearMap.IsPositive → ‖A‖ ≤ C → d ≤ A.det →
      ∀ v, δ*‖v‖^2 ≤ ⟪A v,v⟫_ℝ := by
  let K : Set (E →L[ℝ] E) := {A | A.toLinearMap.IsPositive ∧ ‖A‖ ≤ C ∧ d ≤ A.det}
  have hKc : IsClosed K := positive_closed.inter
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const ContinuousLinearMap.continuous_det))
  have hK : IsCompact K := (isCompact_closedBall (0 : E →L[ℝ] E) C).of_isClosed_subset hKc
    (fun A hA => by simpa only [mem_closedBall,dist_zero_right] using hA.2.1)
  have hS := hK.prod (isCompact_sphere (0:E) 1)
  obtain ⟨δ,hδ,hbound⟩ := hS.exists_forall_le'
    (show ContinuousOn (fun p : (E →L[ℝ] E) × E => ⟪p.1 p.2,p.2⟫_ℝ) _ from
      (by fun_prop : Continuous (fun p : (E →L[ℝ] E) × E => ⟪p.1 p.2,p.2⟫_ℝ)).continuousOn)
    (fun p hp => positive_inner b hp.1.1 (hd.trans_le hp.1.2.2).ne' p.2 (by
      intro he
      simpa only [he,mem_sphere_zero_iff_norm,norm_zero,zero_ne_one] using hp.2))
  refine ⟨δ,hδ,fun A hA hC hdA v => ?_⟩
  by_cases hv : v=0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖v‖⁻¹ • v ∈ sphere (0:E) 1 := by
    rw [mem_sphere_zero_iff_norm,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn]
  have hb := hbound (A,‖v‖⁻¹ • v) ⟨⟨hA,hC,hdA⟩,hunit⟩
  have heq : ⟪A (‖v‖⁻¹ • v),‖v‖⁻¹ • v⟫_ℝ=‖v‖⁻¹^2*⟪A v,v⟫_ℝ := by
    simp only [map_smul,real_inner_smul_left,real_inner_smul_right]
    ring
  dsimp only at hb
  rw [heq] at hb
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  have he : (‖v‖⁻¹^2*⟪A v,v⟫_ℝ)*‖v‖^2=⟪A v,v⟫_ℝ := by field_simp [hn]
  rwa [he] at hh

end LocalEllipticity
namespace MomentLinearization
open MeasureTheory Set Filter Matrix CompactMomentVariational
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma discrete_subsolution {V φ : E → ℝ} {X : E → E} {H : E → Matrix ι ι ℝ}
    (hV : ConvexOn ℝ univ V) {h z : E} (hdV : DifferentiableAt ℝ V (X z)) {c : ℝ}
    (h0 : (H z).PosDef) (hp : (H (z+h)).PosDef) (hm : (H (z-h)).PosDef)
    (he0 : Real.log (H z).det=V (X z)+c-φ z)
    (hep : Real.log (H (z+h)).det=V (X (z+h))+c-φ (z+h))
    (hem : Real.log (H (z-h)).det=V (X (z-h))+c-φ (z-h)) :
    ⟪gradient V (X z),vectorDiff X h z⟫_ℝ ≤
      ((H z)⁻¹*matrixDiff H h z).trace+WeakMomentBound.secondDiff φ h z := by
  have ht1 := LogDetConcavity.tangent h0 hp
  have ht2 := LogDetConcavity.tangent h0 hm
  have hv1 := convex_supporting_gradient hV hdV (X (z+h))
  have hv2 := convex_supporting_gradient hV hdV (X (z-h))
  have he : ((H z)⁻¹*matrixDiff H h z).trace =
      ((H z)⁻¹*(H (z+h)-H z)).trace+((H z)⁻¹*(H (z-h)-H z)).trace := by
    have hh : matrixDiff H h z=(H (z+h)-H z)+(H (z-h)-H z) := by
      dsimp only [matrixDiff]
      simp only [two_smul]
      abel
    rw [hh,Matrix.mul_add,Matrix.trace_add]
  rw [he,WeakMomentBound.secondDiff]
  rw [hep,he0] at ht1
  rw [hem,he0] at ht2
  simp only [inner_sub_right] at hv1 hv2
  simp only [vectorDiff,inner_sub_right,inner_add_right,inner_smul_right]
  linarith

variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

theorem C11_ae_subsolution (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hd : Differentiable ℝ φ)
    {L : ℝ≥0} (hl : LipschitzWith L (gradient φ))
    (hs : Function.Surjective (gradient φ)) (hV : ConvexOn ℝ univ V)
    (hVd : Differentiable ℝ V) (hI : Integrable (fun x => Real.exp (-V x)) μ)
    (hmap : Measure.map (gradient φ) (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource μ V) (h : E) :
    ∀ᵐ z ∂μ, ⟪gradient V (gradient φ z),vectorDiff (gradient φ) h z⟫_ℝ ≤
      ((hessian b φ z)⁻¹*matrixDiff (hessian b φ) h z).trace+
        WeakMomentBound.secondDiff φ h z := by
  have ha := C11_ae_positive_MA μ b hc hd hl hs hVd.continuous hI hmap
  have hap := (measurePreserving_add_right μ h).quasiMeasurePreserving.ae ha
  have ham := (measurePreserving_add_right μ (-h)).quasiMeasurePreserving.ae ha
  filter_upwards [ha,hap,ham] with z hz hp hm
  simp only [← sub_eq_add_neg] at hm
  exact discrete_subsolution hV (hVd _) hz.2.1 hp.2.1 hm.2.1
    (by simpa only [hessian,LinearMap.det_toMatrix] using hz.2.2)
    (by simpa only [hessian,LinearMap.det_toMatrix] using hp.2.2)
    (by simpa only [hessian,LinearMap.det_toMatrix] using hm.2.2)

end MomentLinearization

namespace InverseElliptic
open Set Metric Matrix
open scoped InnerProductSpace Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ

lemma toMatrix_fromMatrix (b : OrthonormalBasis ι ℝ E) (M : Mat) :
    LinearMap.toMatrix b.toBasis b.toBasis (fromMatrix b M).toLinearMap=M := by
  change (LinearMap.toMatrix b.toBasis b.toBasis) ((LinearMap.toMatrix b.toBasis b.toBasis).symm M)=M
  exact LinearEquiv.apply_symm_apply _ _

lemma inverse_continuousOn {K : Set Mat} (hK : ∀ M∈K,M.PosDef) :
    ContinuousOn (fun M : Mat => M⁻¹) K := by
  intro M hM
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hK M hM).det_pos.ne'

theorem compact_inverse_bounds (b : OrthonormalBasis ι ℝ E) {K : Set Mat}
    (hK : IsCompact K) (hpos : ∀ M∈K,M.PosDef) :
    ∃ ell T Tm : ℝ,0<ell ∧ 0≤T ∧ ∀ M∈K,
      (M⁻¹-ell • (1:Mat)).PosSemidef ∧ (M⁻¹).trace≤T ∧ ‖M⁻¹‖≤Tm := by
  let J := (fun M : Mat => M⁻¹) '' K
  have hJ : IsCompact J := hK.image_of_continuousOn (inverse_continuousOn hpos)
  have hJp : ∀ M∈J,M.PosDef := by rintro _ ⟨M,hM,rfl⟩; exact (hpos M hM).inv
  let e := fromMatrix b
  obtain ⟨C,hC⟩ := (hJ.image e.continuous).isBounded.exists_norm_le
  obtain ⟨d,hd,hdet⟩ := hJ.exists_forall_le'
    (ContinuousLinearMap.continuous_det.comp e.continuous).continuousOn
    (fun M hM => by
      change 0 < (e M).det
      change 0 < LinearMap.det (fromMatrix b M).toLinearMap
      rw [← LinearMap.det_toMatrix b.toBasis (fromMatrix b M).toLinearMap,toMatrix_fromMatrix]
      exact (hJp M hM).det_pos)
  obtain ⟨ell,hell,hel⟩ := LocalEllipticity.uniform_coercivity b C hd
  obtain ⟨Tm,hTm⟩ := hJ.isBounded.exists_norm_le
  obtain ⟨T,hT⟩ := (hJ.image (show Continuous (fun M : Mat => M.trace) by unfold Matrix.trace; fun_prop)).isBounded.exists_norm_le
  refine ⟨ell,max T 0,Tm,hell,le_max_right _ _,fun M hM => ?_⟩
  have hMin : M⁻¹∈J := ⟨M,hM,rfl⟩
  have hep : (e M⁻¹).toLinearMap.IsPositive := by
    apply (LinearMap.posSemidef_toMatrix_iff b).mp
    dsimp only [e]
    rw [toMatrix_fromMatrix]
    exact (hJp M⁻¹ hMin).posSemidef
  have hec := hC _ (mem_image_of_mem e hMin)
  have hed := hdet _ hMin
  have hb := hel _ hep hec hed
  have heq : LinearMap.toMatrix b.toBasis b.toBasis
      ((e M⁻¹)-(ell • ContinuousLinearMap.id ℝ E)).toLinearMap=M⁻¹-ell • (1:Mat) := by
    dsimp only [e]
    simp only [ContinuousLinearMap.toLinearMap_sub,ContinuousLinearMap.toLinearMap_smul,
      map_sub,map_smul,ContinuousLinearMap.coe_id,LinearMap.toMatrix_id,toMatrix_fromMatrix]
  refine ⟨?_,?_,hTm _ hMin⟩
  · rw [← heq]
    apply (LinearMap.posSemidef_toMatrix_iff b).mpr
    constructor
    · exact hep.isSymmetric.sub (LinearMap.IsSymmetric.smul rfl LinearMap.IsSymmetric.id)
    · intro v
      change 0 ≤ ⟪(e M⁻¹) v-ell • v,v⟫_ℝ
      simpa only [inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq] using sub_nonneg.mpr (hb v)
  · have ht : |(M⁻¹).trace| ≤ T := by simpa only [Real.norm_eq_abs] using hT _ (mem_image_of_mem (fun M : Mat => M.trace) hMin)
    exact (le_abs_self _).trans (ht.trans (le_max_left _ _))

end InverseElliptic

namespace MomentLinearization
open Set Metric Matrix Filter MeasureTheory CompactMomentVariational
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ

omit [DecidableEq ι] in
lemma continuous_gradient_of_C1 {V : E → ℝ} (hV : ContDiff ℝ 1 V) : Continuous (gradient V) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((contDiff_one_iff_fderiv.mp hV).2)

theorem C11_local_coefficients (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient φ))
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)) volume)
    {G : Set E} (hG : ∀ x∈G,DifferentiableAt ℝ (gradient φ) x ∧
      (hessian b φ x).PosDef ∧ Real.log (hessian b φ x).det=
        V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x) :
    ∀ c : E,∃ ell T Tm B K R : ℝ,0<ell ∧ 0≤T ∧ 0≤B ∧ 0≤K ∧ 0<R ∧
      (∀ x∈G,x∈ball c R →
        ((hessian b φ x)⁻¹-ell • (1:Mat)).PosSemidef ∧
          ((hessian b φ x)⁻¹).trace≤T ∧ ‖(hessian b φ x)⁻¹‖≤Tm ∧
          ‖gradient V (gradient φ x)‖≤B) ∧
      (∀ x∈G,x∈ball c R → ∀ y∈G,y∈ball c R →
        ((hessian b φ y)⁻¹*(hessian b φ y-hessian b φ x)).trace≤
          K*(dist x c+dist y c)) := by
  intro c
  let Z := ∫ x,Real.exp (-V x)
  let F := fun z => Z*Real.exp (V (gradient φ z)-φ z)
  have hZ : 0<Z := integral_exp_pos hI
  have hF : Continuous F := continuous_const.mul ((hV.continuous.comp hL.continuous).sub hφ.continuous).rexp
  obtain ⟨d,hd,hdF⟩ := (isCompact_closedBall c 1).exists_forall_le' hF.continuousOn
    (fun z _ => mul_pos hZ (Real.exp_pos _))
  let J : Set (E →L[ℝ] E) := {Q | Q.toLinearMap.IsPositive ∧ ‖Q‖≤(L:ℝ) ∧ d≤Q.det}
  have hJ : IsCompact J := (isCompact_closedBall (0:E →L[ℝ] E) (L:ℝ)).of_isClosed_subset
    (LocalEllipticity.positive_closed.inter ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const ContinuousLinearMap.continuous_det)))
    (fun Q hQ => by simpa only [mem_closedBall,dist_zero_right] using hQ.2.1)
  let toMat : (E →L[ℝ] E) → Mat := fun Q => LinearMap.toMatrix b.toBasis b.toBasis Q.toLinearMap
  have htoMat : Continuous toMat := (InverseElliptic.fromMatrix b).symm.continuous
  have hpos : ∀ M∈toMat '' J,M.PosDef := by
    rintro _ ⟨Q,hQ,rfl⟩
    apply ((LinearMap.posSemidef_toMatrix_iff b).mpr hQ.1).posDef_iff_det_ne_zero.mpr
    rw [LinearMap.det_toMatrix]
    exact (hd.trans_le hQ.2.2).ne'
  obtain ⟨ell,T,Tm,hell,hT,hbounds⟩ := InverseElliptic.compact_inverse_bounds b (hJ.image htoMat) hpos
  have hgradV := continuous_gradient_of_C1 hV
  obtain ⟨B,hB⟩ := ((isCompact_closedBall c 1).image (hgradV.comp hL.continuous)).isBounded.exists_norm_le
  obtain ⟨Kv,U,hU,hKv⟩ := (hV.locallyLipschitz.comp hL.locallyLipschitz) c
  obtain ⟨Kp,W,hW,hKp⟩ := hφ.locallyLipschitz c
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hW)
  let r := min R 1
  have hr : 0<r := lt_min hR zero_lt_one
  have hx1 {x : E} (hx : x∈ball c r) : x∈closedBall c 1 :=
    mem_closedBall.mpr (mem_ball.mp ((ball_subset_ball (min_le_right R 1)) hx)).le
  have hxU {x : E} (hx : x∈ball c r) : x∈U := (hRU (ball_subset_ball (min_le_left _ _) hx)).1
  have hxW {x : E} (hx : x∈ball c r) : x∈W := (hRU (ball_subset_ball (min_le_left _ _) hx)).2
  have hM (x : E) (hx : x∈G) (hxr : x∈ball c r) : hessian b φ x∈toMat '' J := by
    refine ⟨fderiv ℝ (gradient φ) x,⟨?_,norm_fderiv_le_of_lipschitz ℝ hL,?_⟩,rfl⟩
    · exact convex_gradient_derivative_positive hc (hφ.differentiable one_ne_zero) (hG x hx).1
    · have he := congrArg Real.exp (hG x hx).2.2
      rw [Real.exp_log (hG x hx).2.1.det_pos] at he
      have heF : (hessian b φ x).det=F x := by
        rw [he]
        dsimp only [F,Z]
        rw [show V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x=
          Real.log (∫ x,Real.exp (-V x))+(V (gradient φ x)-φ x) by ring,
          Real.exp_add,Real.exp_log hZ]
      have heD : (hessian b φ x).det=(fderiv ℝ (gradient φ) x).det := LinearMap.det_toMatrix b.toBasis _
      rw [← heD,heF]
      exact hdF x (hx1 hxr)
  refine ⟨ell,T,Tm,max B 0,(Kv+Kp:ℝ≥0),r,hell,hT,le_max_right _ _,NNReal.coe_nonneg _,hr,?_,?_⟩
  · intro x hx hxr
    exact ⟨(hbounds _ (hM x hx hxr)).1,(hbounds _ (hM x hx hxr)).2.1,
      (hbounds _ (hM x hx hxr)).2.2,(hB _ (mem_image_of_mem _ (hx1 hxr))).trans (le_max_left _ _)⟩
  · intro x hx hxr y hy hyr
    have ht := LogDetConcavity.tangent (hG y hy).2.1 (hG x hx).2.1
    have he : ((hessian b φ y)⁻¹*(hessian b φ y-hessian b φ x)).trace=
        -((hessian b φ y)⁻¹*(hessian b φ x-hessian b φ y)).trace := by
      rw [← Matrix.trace_neg,← Matrix.mul_neg,neg_sub]
    rw [he]
    rw [(hG x hx).2.2,(hG y hy).2.2] at ht
    have hvb := hKv.dist_le_mul y (hxU hyr) x (hxU hxr)
    have hpb := hKp.dist_le_mul x (hxW hxr) y (hxW hyr)
    change dist (V (gradient φ y)) (V (gradient φ x))≤(Kv:ℝ)*dist y x at hvb
    rw [Real.dist_eq] at hvb hpb
    have hv := (le_abs_self (V (gradient φ y)-V (gradient φ x))).trans hvb
    have hp := (le_abs_self (φ x-φ y)).trans hpb
    have hxy := dist_triangle x c y
    rw [dist_comm c y] at hxy
    have hvp := mul_le_mul_of_nonneg_left hxy (NNReal.coe_nonneg (Kv+Kp))
    rw [NNReal.coe_add] at hvp
    rw [dist_comm y x] at hv
    simp only [NNReal.coe_add]
    nlinarith

end MomentLinearization

namespace AESlice
section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma ae_lines {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) (e : E) :
    ∀ᵐ x ∂μ, ∀ᵐ t ∂(volume : Measure ℝ), P (x+t • e) := by
  obtain ⟨N,hN,hNm,hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hNae : ∀ᵐ x ∂μ, x∉N := by
    rw [ae_iff]
    convert hN0 using 2; ext x; simp
  have hpre : MeasurableSet {p : E×ℝ | p.1+p.2 • e∉N} := by
    exact (hNm.preimage (show Measurable (fun p : E×ℝ => p.1+p.2 • e) by fun_prop)).compl
  have ht : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂μ, x+t • e∉N := by
    exact ae_of_all _ (fun t => (measurePreserving_add_right μ (t • e)).quasiMeasurePreserving.ae hNae)
  have hh := (ae_ae_comm hpre).mpr ht
  filter_upwards [hh] with x hx
  filter_upwards [hx] with t ht
  exact not_not.mp (fun hn => ht (hN hn))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma line_lipschitz (x e : E) : LipschitzWith ‖e‖₊ (fun t : ℝ => x+t • e) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← sub_smul,norm_smul,Real.norm_eq_abs]
  exact le_of_eq (mul_comm _ _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma line_deriv (g : E → ℝ) {x e : E} {t : ℝ} (hg : DifferentiableAt ℝ g (x+t • e)) :
    HasDerivAt (fun s : ℝ => g (x+s • e)) ((fderiv ℝ g (x+t • e)) e) t := by
  simpa only [id_eq,one_smul,Function.comp_def] using hg.hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const e).const_add x)

lemma difference_le_ae {g : E → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) {e : E} {M : ℝ}
    (ha : ∀ᵐ x ∂μ, x∈Ω → DifferentiableAt ℝ g x ∧ fderiv ℝ g x e≤M)
    {x : E} {a : ℝ} (ha0 : 0≤a) (hx : x∈Ω) (hxa : x+a • e∈Ω) :
    g (x+a • e)-g x≤M*a := by
  have hl := ae_lines μ ha e
  let U : Set E := Ω∩(fun y => y+a • e) ⁻¹' Ω
  have hU : IsOpen U := hΩ.inter (hΩ.preimage (by fun_prop))
  have hxU : x∈U := ⟨hx,hxa⟩
  have hgood : ∀ᵐ y ∂μ, y∈U → g (y+a • e)-g y≤M*a := by
    filter_upwards [hl] with y hy hyU
    have hs (t : ℝ) (ht : t∈Icc 0 a) : y+t • e∈Ω := by
      by_cases haZ : a=0
      · have htZ : t=0 := by rw [haZ] at ht; linarith [ht.1,ht.2]
        simpa only [htZ,zero_smul,add_zero] using hyU.1
      have haP : 0<a := lt_of_le_of_ne ha0 (Ne.symm haZ)
      have hh := hc hyU.1 hyU.2 (show 0≤1-t/a by rw [sub_nonneg]; exact (div_le_one haP).mpr ht.2)
        (div_nonneg ht.1 ha0) (by ring : (1-t/a)+t/a=1)
      convert hh using 1
      dsimp only at hh ⊢
      simp only [smul_add,smul_smul,sub_smul,one_smul]
      rw [div_mul_cancel₀ _ haZ]
      abel
    have hline := hg.comp (line_lipschitz y e)
    have hac : AbsolutelyContinuousOnInterval (fun s => g (y+s • e)) 0 a :=
      hline.lipschitzOnWith.absolutelyContinuousOnInterval
    have hi := hac.intervalIntegrable_deriv
    have hd : ∀ᵐ t ∂(volume.restrict (Icc 0 a)), deriv (fun s => g (y+s • e)) t≤M := by
      filter_upwards [ae_restrict_of_ae hy,ae_restrict_mem measurableSet_Icc] with t ht hta
      rw [(line_deriv g (ht (hs t hta)).1).deriv]
      exact (ht (hs t hta)).2
    have hh := intervalIntegral.integral_mono_ae_restrict ha0 hi (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 a) hd
    rw [hac.integral_deriv_eq_sub] at hh
    simpa only [zero_smul,add_zero,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using hh
  have hdense := μ.dense_of_ae hgood
  have hcl := hdense.open_subset_closure_inter hU hxU
  have hclosed : IsClosed {y : E | g (y+a • e)-g y≤M*a} :=
    isClosed_le ((hg.continuous.comp (by fun_prop)).sub hg.continuous) continuous_const
  exact hclosed.closure_subset_iff.mpr (fun y hy => hy.2 hy.1) hcl

end
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped Topology NNReal
open scoped InnerProductSpace


end AESlice

namespace SecondQuotient
open Filter Set Topology Asymptotics
open scoped InnerProductSpace

lemma scalar_limit {f g : ℝ → ℝ} {A : ℝ} (hf : ∀ t, HasDerivAt f (g t) t)
    (hg : HasDerivAt g A 0) :
    Tendsto (fun t => (f t+f (-t)-2*f 0)/t^2) (𝓝[≠] 0) (𝓝 A) := by
  let R : ℝ → ℝ := fun t => f t-f 0-t*g 0-t^2/2*A
  have hR (t : ℝ) : HasDerivAt R (g t-g 0-t*A) t := by
    convert ((hf t).sub_const (f 0) |>.sub ((hasDerivAt_id t).mul_const (g 0))).sub
      (((hasDerivAt_id t).pow 2).div_const 2 |>.mul_const A) using 1 <;> first | rfl | (dsimp only [R,id_eq]; ring)
  have hgo : (fun t => g t-g 0-t*A) =o[𝓝[univ] 0] (fun t : ℝ => (t-0)^1) := by
    simpa only [nhdsWithin_univ,sub_zero,pow_one,smul_eq_mul] using hg.isLittleO
  have hro := Convex.isLittleO_pow_succ_real convex_univ (mem_univ (0:ℝ))
    (fun t (_ : t∈(univ:Set ℝ)) => (hR t).hasDerivWithinAt) hgo
  have hlim : Tendsto (fun t => R t/t^2) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [nhdsWithin_univ,show R 0=0 by simp [R],sub_zero] using hro.tendsto_div_nhds_zero
  have hneg : Tendsto (fun t : ℝ => R (-t)/t^2) (𝓝 (0:ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,neg_sq] using hlim.comp (show Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) from by simpa only [neg_zero] using continuous_neg.tendsto (0:ℝ))
  have hsum := ((hlim.add hneg).add_const A).mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ)≤𝓝 0)
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t≠0 := ht
  dsimp only [R]
  field_simp [ht0]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma gradient_limit {φ : E → ℝ} (hd : Differentiable ℝ φ) {x e : E}
    (hH : DifferentiableAt ℝ (gradient φ) x) :
    Tendsto (fun t : ℝ => (φ (x+t • e)+φ (x-t • e)-2*φ x)/t^2)
      (𝓝[≠] 0) (𝓝 (⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ)) := by
  let f : ℝ → ℝ := fun t => φ (x+t • e)
  let g : ℝ → ℝ := fun t => ⟪gradient φ (x+t • e),e⟫_ℝ
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ => x+s • e) e t := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const e).const_add x
  have hf (t : ℝ) : HasDerivAt f (g t) t := by
    have hh := (hd (x+t • e)).hasFDerivAt.comp_hasDerivAt t (hline t)
    simpa only [f,g,Function.comp_def,← toDual_gradient,InnerProductSpace.toDual_apply_apply] using hh
  have hg : HasDerivAt g (⟪(fderiv ℝ (gradient φ) x) e,e⟫_ℝ) 0 := by
    have h0 : x+(0:ℝ) • e=x := by simp
    have hh := (h0 ▸ hH.hasFDerivAt).comp_hasDerivAt 0 (hline 0)
    have hj := (innerSL ℝ e).hasFDerivAt.comp_hasDerivAt 0 hh
    simpa only [g,Function.comp_def,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
      h0,real_inner_comm] using hj
  simpa only [f,zero_smul,add_zero,neg_smul,← sub_eq_add_neg] using scalar_limit hf hg

end SecondQuotient

namespace HessianCoordinates
open Matrix
open scoped InnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_toMatrix (b : OrthonormalBasis ι ℝ E) (A : E →L[ℝ] E) (e : ι → ℝ) :
    FiniteElliptic.quadratic (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap) e =
      ⟪A (vector b e),vector b e⟫_ℝ := by
  have he : (b.toBasis.repr (vector b e) : ι → ℝ)=e := by
    ext i
    simp only [OrthonormalBasis.coe_toBasis_repr_apply,vector,LinearIsometryEquiv.apply_symm_apply]
  have hm := LinearMap.toMatrix_mulVec_repr b.toBasis b.toBasis A.toLinearMap (vector b e)
  rw [he] at hm
  unfold FiniteElliptic.quadratic
  rw [hm,← b.repr.inner_map_map (A (vector b e)) (vector b e),EuclideanSpace.inner_eq_star_dotProduct]
  simp only [vector,LinearIsometryEquiv.apply_symm_apply,star_trivial]
  rfl

end HessianCoordinates

end

noncomputable section

namespace AEContinuousDerivative
section
open Filter Set Metric MeasureTheory
open scoped InnerProductSpace Topology NNReal
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma increment_bound {g : E → F} {L : ℝ≥0} (hg : LipschitzWith L g)
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω) (A : E →L[ℝ] F) {ε : ℝ}
    (hε : 0 ≤ ε) (ha : ∀ᵐ z ∂μ, z∈Ω → DifferentiableAt ℝ g z ∧ ‖fderiv ℝ g z-A‖≤ε)
    {x h : E} (hx : x∈Ω) (hxh : x+h∈Ω) :
    ‖g (x+h)-g x-A h‖ ≤ ε*‖h‖ := by
  let v := g (x+h)-g x-A h
  let f : E → ℝ := fun z => ⟪v,g z-A z⟫_ℝ
  have hf : LipschitzWith (‖innerSL ℝ v‖₊*(L+‖A‖₊)) f :=
    (innerSL ℝ v).lipschitz.comp (hg.sub A.lipschitz)
  have hfa : ∀ᵐ z ∂μ,z∈Ω → DifferentiableAt ℝ f z ∧ fderiv ℝ f z h≤‖v‖*(ε*‖h‖) := by
    filter_upwards [ha] with z hz hzΩ
    have hh := (innerSL ℝ v).hasFDerivAt.comp z ((hz hzΩ).1.hasFDerivAt.sub A.hasFDerivAt)
    refine ⟨hh.differentiableAt,?_⟩
    have hfd : fderiv ℝ f z=(innerSL ℝ v).comp (fderiv ℝ g z-A) := hh.fderiv
    rw [hfd]
    change ⟪v,(fderiv ℝ g z-A) h⟫_ℝ≤_
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hz hzΩ).2 (norm_nonneg h))) (norm_nonneg v))
  have hh := AESlice.difference_le_ae μ hf hΩ hc hfa (a:=1) (by norm_num) hx
    (by simpa only [one_smul] using hxh)
  have he : f (x+(1:ℝ) • h)-f x=‖v‖^2 := by
    simp only [one_smul,f,← inner_sub_right]
    have hv : g (x+h)-A (x+h)-(g x-A x)=v := by dsimp only [v]; rw [map_add]; abel
    rw [hv,real_inner_self_eq_norm_sq]
  rw [he,mul_one] at hh
  by_cases hv : ‖v‖=0
  · change ‖v‖≤ε*‖h‖
    rw [hv]
    positivity
  · have hv0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    change ‖v‖≤ε*‖h‖
    nlinarith

theorem hasFDerivAt_of_ae {g : E → F} {L : ℝ≥0} (hg : LipschitzWith L g)
    {A : E → E →L[ℝ] F} (hA : Continuous A)
    (ha : ∀ᵐ z ∂μ,HasFDerivAt g (A z) z) (x : E) : HasFDerivAt g (A x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp
    (hA.continuousAt.eventually (Metric.ball_mem_nhds (A x) hε))
  have hh : ∀ᵐ z ∂μ,z∈ball x δ → DifferentiableAt ℝ g z ∧ ‖fderiv ℝ g z-A x‖≤ε := by
    filter_upwards [ha] with z hz hzB
    refine ⟨hz.differentiableAt,?_⟩
    rw [hz.fderiv]
    exact le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hball (mem_ball.mp hzB))
  filter_upwards [Metric.ball_mem_nhds (0:E) hδ] with h hhB
  exact increment_bound μ hg isOpen_ball (convex_ball _ _) (A x) hε.le hh
    (mem_ball_self hδ) (by simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hhB)

end

open MeasureTheory Set Filter Matrix
open scoped InnerProductSpace NNReal Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem contDiff_one_of_matrix_rep (b : OrthonormalBasis ι ℝ E)
    {g : E → E} {L : ℝ≥0} (hg : LipschitzWith L g)
    {M : E → Matrix ι ι ℝ} (hM : Continuous M)
    (hrep : ∀ᵐ x ∂volume,DifferentiableAt ℝ g x ∧
      M x=LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ g x).toLinearMap) :
    ContDiff ℝ 1 g := by
  let e : Matrix ι ι ℝ ≃L[ℝ] E →L[ℝ] E :=
    ((LinearMap.toMatrix b.toBasis b.toBasis).symm.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv
  have hind (A : E →L[ℝ] E) : e (LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap)=A := by
    change LinearMap.toContinuousLinearMap ((LinearMap.toMatrix b.toBasis b.toBasis).symm
      ((LinearMap.toMatrix b.toBasis b.toBasis) A.toLinearMap))=A
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hA : Continuous (fun x => e (M x)) := e.continuous.comp hM
  have ha : ∀ᵐ x ∂volume,HasFDerivAt g (e (M x)) x := by
    filter_upwards [hrep] with x hx
    rw [hx.2,hind]
    exact hx.1.hasFDerivAt
  have hdf (x : E) := hasFDerivAt_of_ae volume hg hA ha x
  apply contDiff_one_iff_fderiv.mpr
  refine ⟨fun x => (hdf x).differentiableAt,?_⟩
  have he : fderiv ℝ g=fun x => e (M x) := funext fun x => (hdf x).fderiv
  rw [he]
  exact hA

omit [MeasurableSpace E] [BorelSpace E] in
lemma contDiff_two_of_gradient {φ : E → ℝ} (hd : Differentiable ℝ φ)
    (hg : ContDiff ℝ 1 (gradient φ)) : ContDiff ℝ 2 φ := by
  have hf : ContDiff ℝ 1 (fderiv ℝ φ) := by
    have he : fderiv ℝ φ=fun x => (InnerProductSpace.toDual ℝ E) (gradient φ x) :=
      funext fun _ => toDual_gradient.symm
    rw [he]
    exact (InnerProductSpace.toDual ℝ E).contDiff.comp hg
  exact contDiff_succ_iff_fderiv.mpr ⟨hd,(by simp),hf⟩

end AEContinuousDerivative

namespace CompactMomentVariational
open Set Metric Matrix Filter MeasureTheory
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

theorem C11_to_C2 (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient φ))
    (hs : Function.Surjective (gradient φ)) (hVc : ConvexOn ℝ univ V)
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)) volume)
    (hm : Measure.map (gradient φ) (volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource volume V) : ContDiff ℝ 2 φ := by
  let G : Set E := {x | DifferentiableAt ℝ (gradient φ) x ∧
    (MomentLinearization.hessian b φ x).PosDef ∧
      Real.log (MomentLinearization.hessian b φ x).det=
        V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x}
  have hd := hφ.differentiable one_ne_zero
  have hG : ∀ᵐ x ∂volume,x∈G := by
    filter_upwards [C11_ae_positive_MA volume b hc hd hL hs hV.continuous hI hm] with x hx
    exact ⟨hx.1,hx.2.1,by simpa only [MomentLinearization.hessian,LinearMap.det_toMatrix] using hx.2.2⟩
  have hlocal := MomentLinearization.C11_local_coefficients b hc hφ hL hV hI (G:=G) (fun _ hx => hx)
  have hP := MomentLinearization.C11_ae_subsolution volume b hc hd hL hs hVc
    (hV.differentiable one_ne_zero) hI hm
  obtain ⟨M,hM,hrep⟩ := C11InteriorRegularity.continuous_hessian_rep b hd hL hG
    (fun _ hx => hx.1) (fun _ hx => hx.2.1.isHermitian) hlocal hP
  have hg : ContDiff ℝ 1 (gradient φ) := AEContinuousDerivative.contDiff_one_of_matrix_rep b hL hM (by
    filter_upwards [hG] with x hx
    exact ⟨hx.1,hrep x hx⟩)
  exact AEContinuousDerivative.contDiff_two_of_gradient hd hg

omit [Nonempty ι] in

theorem C2_positive_MA (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 2 φ)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient φ))
    (hs : Function.Surjective (gradient φ)) (hV : Continuous V)
    (hI : Integrable (fun x => Real.exp (-V x)) volume)
    (hm : Measure.map (gradient φ) (volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource volume V) :
    ∀ x,(MomentLinearization.hessian b φ x).PosDef ∧
      Real.log (fderiv ℝ (gradient φ) x).det=
        V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x := by
  have hd := hφ.differentiable (by norm_num)
  have hg : ContDiff ℝ 1 (gradient φ) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hφ.fderiv_right (by norm_num))
  have hgd := hg.differentiable one_ne_zero
  let Z := ∫ x,Real.exp (-V x)
  have hZ : 0<Z := integral_exp_pos hI
  have hda : (fun x => (fderiv ℝ (gradient φ) x).det)=ᵐ[volume]
      (fun x => Z*Real.exp (V (gradient φ x)-φ x)) := by
    filter_upwards [C11_ae_positive_MA volume b hc hd hL hs hV hI hm] with x hx
    have hdet : 0<(fderiv ℝ (gradient φ) x).det := by
      simpa only [LinearMap.det_toMatrix] using hx.2.1.det_pos
    have he := congrArg Real.exp hx.2.2
    rw [Real.exp_log hdet] at he
    rw [he]
    dsimp only [Z]
    rw [show V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x=
      Real.log (∫ x,Real.exp (-V x))+(V (gradient φ x)-φ x) by ring,
      Real.exp_add,Real.exp_log hZ]
  have heq := Measure.eq_of_ae_eq hda
    (ContinuousLinearMap.continuous_det.comp (contDiff_one_iff_fderiv.mp hg).2)
    (continuous_const.mul ((hV.comp hg.continuous).sub hφ.continuous).rexp)
  intro x
  have he := congrFun heq x
  have hpd : (MomentLinearization.hessian b φ x).PosDef := by
    apply ((LinearMap.posSemidef_toMatrix_iff b).mpr
      (convex_gradient_derivative_positive hc hd (hgd x))).posDef_iff_det_ne_zero.mpr
    change (LinearMap.toMatrix b.toBasis b.toBasis (fderiv ℝ (gradient φ) x).toLinearMap).det ≠ 0
    rw [LinearMap.det_toMatrix]
    change (fderiv ℝ (gradient φ) x).det ≠ 0
    rw [he]
    exact (mul_pos hZ (Real.exp_pos _)).ne'
  refine ⟨hpd,?_⟩
  rw [he,Real.log_mul hZ.ne' (Real.exp_ne_zero _),Real.log_exp]
  dsimp only [Z]
  ring

end CompactMomentVariational
namespace MomentLinearization
open Set Metric Matrix Filter MeasureTheory CompactMomentVariational
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ

omit [DecidableEq ι] in
lemma continuous_gradient_of_C1_pair {V : E → ℝ} (hV : ContDiff ℝ 1 V) : Continuous (gradient V) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    ((contDiff_one_iff_fderiv.mp hV).2)

theorem C11_local_coefficients_pair (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient φ))
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)) volume)
    {G : Set E} (hG : ∀ x∈G,DifferentiableAt ℝ (gradient φ) x ∧
      (hessian b φ x).PosDef ∧ Real.log (hessian b φ x).det=
        V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x) :
    ∀ c : E,∃ ell T Tm B K R : ℝ,0<ell ∧ 0≤T ∧ 0≤B ∧ 0≤K ∧ 0<R ∧
      (∀ x∈G,x∈ball c R →
        ((hessian b φ x)⁻¹-ell • (1:Mat)).PosSemidef ∧
          ((hessian b φ x)⁻¹).trace≤T ∧ ‖(hessian b φ x)⁻¹‖≤Tm ∧
          ‖gradient V (gradient φ x)‖≤B) ∧
      (∀ x∈G,x∈ball c R → ∀ y∈G,y∈ball c R →
        ((hessian b φ y)⁻¹*(hessian b φ y-hessian b φ x)).trace≤
          K*dist x y) := by
  intro c
  let Z := ∫ x,Real.exp (-V x)
  let F := fun z => Z*Real.exp (V (gradient φ z)-φ z)
  have hZ : 0<Z := integral_exp_pos hI
  have hF : Continuous F := continuous_const.mul ((hV.continuous.comp hL.continuous).sub hφ.continuous).rexp
  obtain ⟨d,hd,hdF⟩ := (isCompact_closedBall c 1).exists_forall_le' hF.continuousOn
    (fun z _ => mul_pos hZ (Real.exp_pos _))
  let J : Set (E →L[ℝ] E) := {Q | Q.toLinearMap.IsPositive ∧ ‖Q‖≤(L:ℝ) ∧ d≤Q.det}
  have hJ : IsCompact J := (isCompact_closedBall (0:E →L[ℝ] E) (L:ℝ)).of_isClosed_subset
    (LocalEllipticity.positive_closed.inter ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const ContinuousLinearMap.continuous_det)))
    (fun Q hQ => by simpa only [mem_closedBall,dist_zero_right] using hQ.2.1)
  let toMat : (E →L[ℝ] E) → Mat := fun Q => LinearMap.toMatrix b.toBasis b.toBasis Q.toLinearMap
  have htoMat : Continuous toMat := (InverseElliptic.fromMatrix b).symm.continuous
  have hpos : ∀ M∈toMat '' J,M.PosDef := by
    rintro _ ⟨Q,hQ,rfl⟩
    apply ((LinearMap.posSemidef_toMatrix_iff b).mpr hQ.1).posDef_iff_det_ne_zero.mpr
    rw [LinearMap.det_toMatrix]
    exact (hd.trans_le hQ.2.2).ne'
  obtain ⟨ell,T,Tm,hell,hT,hbounds⟩ := InverseElliptic.compact_inverse_bounds b (hJ.image htoMat) hpos
  have hgradV := continuous_gradient_of_C1_pair hV
  obtain ⟨B,hB⟩ := ((isCompact_closedBall c 1).image (hgradV.comp hL.continuous)).isBounded.exists_norm_le
  obtain ⟨Kv,U,hU,hKv⟩ := (hV.locallyLipschitz.comp hL.locallyLipschitz) c
  obtain ⟨Kp,W,hW,hKp⟩ := hφ.locallyLipschitz c
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hW)
  let r := min R 1
  have hr : 0<r := lt_min hR zero_lt_one
  have hx1 {x : E} (hx : x∈ball c r) : x∈closedBall c 1 :=
    mem_closedBall.mpr (mem_ball.mp ((ball_subset_ball (min_le_right R 1)) hx)).le
  have hxU {x : E} (hx : x∈ball c r) : x∈U := (hRU (ball_subset_ball (min_le_left _ _) hx)).1
  have hxW {x : E} (hx : x∈ball c r) : x∈W := (hRU (ball_subset_ball (min_le_left _ _) hx)).2
  have hM (x : E) (hx : x∈G) (hxr : x∈ball c r) : hessian b φ x∈toMat '' J := by
    refine ⟨fderiv ℝ (gradient φ) x,⟨?_,norm_fderiv_le_of_lipschitz ℝ hL,?_⟩,rfl⟩
    · exact convex_gradient_derivative_positive hc (hφ.differentiable one_ne_zero) (hG x hx).1
    · have he := congrArg Real.exp (hG x hx).2.2
      rw [Real.exp_log (hG x hx).2.1.det_pos] at he
      have heF : (hessian b φ x).det=F x := by
        rw [he]
        dsimp only [F,Z]
        rw [show V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x=
          Real.log (∫ x,Real.exp (-V x))+(V (gradient φ x)-φ x) by ring,
          Real.exp_add,Real.exp_log hZ]
      have heD : (hessian b φ x).det=(fderiv ℝ (gradient φ) x).det := LinearMap.det_toMatrix b.toBasis _
      rw [← heD,heF]
      exact hdF x (hx1 hxr)
  refine ⟨ell,T,Tm,max B 0,(Kv+Kp:ℝ≥0),r,hell,hT,le_max_right _ _,NNReal.coe_nonneg _,hr,?_,?_⟩
  · intro x hx hxr
    exact ⟨(hbounds _ (hM x hx hxr)).1,(hbounds _ (hM x hx hxr)).2.1,
      (hbounds _ (hM x hx hxr)).2.2,(hB _ (mem_image_of_mem _ (hx1 hxr))).trans (le_max_left _ _)⟩
  · intro x hx hxr y hy hyr
    have ht := LogDetConcavity.tangent (hG y hy).2.1 (hG x hx).2.1
    have he : ((hessian b φ y)⁻¹*(hessian b φ y-hessian b φ x)).trace=
        -((hessian b φ y)⁻¹*(hessian b φ x-hessian b φ y)).trace := by
      rw [← Matrix.trace_neg,← Matrix.mul_neg,neg_sub]
    rw [he]
    rw [(hG x hx).2.2,(hG y hy).2.2] at ht
    have hvb := hKv.dist_le_mul y (hxU hyr) x (hxU hxr)
    have hpb := hKp.dist_le_mul x (hxW hxr) y (hxW hyr)
    change dist (V (gradient φ y)) (V (gradient φ x))≤(Kv:ℝ)*dist y x at hvb
    rw [Real.dist_eq] at hvb hpb
    have hv := (le_abs_self (V (gradient φ y)-V (gradient φ x))).trans hvb
    have hp := (le_abs_self (φ x-φ y)).trans hpb
    rw [dist_comm y x] at hv
    simp only [NNReal.coe_add]
    nlinarith

end MomentLinearization
end

noncomputable section
namespace CompactMomentVariational
open Set Metric Matrix Filter MeasureTheory
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

theorem C2_local_holder (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 2 φ)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient φ))
    (hs : Function.Surjective (gradient φ)) (hVc : ConvexOn ℝ univ V)
    (hV : ContDiff ℝ 1 V) (hI : Integrable (fun x => Real.exp (-V x)) volume)
    (hm : Measure.map (gradient φ) (volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource volume V) (c : E) :
    ∃ a C r : ℝ,0<a ∧ a<1 ∧ 0≤C ∧ 0<r ∧
      ∀ x∈ball c r,∀ y∈ball c r,
        dist (MomentLinearization.hessian b φ x) (MomentLinearization.hessian b φ y)≤C*dist x y^a := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hd := hφ1.differentiable one_ne_zero
  have hg : ContDiff ℝ 1 (gradient φ) :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hφ.fderiv_right (by norm_num))
  have hgd := hg.differentiable one_ne_zero
  have hpos := C2_positive_MA b hc hφ hL hs hV.continuous hI hm
  have hG : ∀ x∈(univ : Set E),DifferentiableAt ℝ (gradient φ) x ∧
      (MomentLinearization.hessian b φ x).PosDef ∧
      Real.log (MomentLinearization.hessian b φ x).det=
        V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x := by
    intro x _
    exact ⟨hgd x,(hpos x).1,by simpa only [MomentLinearization.hessian,LinearMap.det_toMatrix] using (hpos x).2⟩
  obtain ⟨ell,T,Tm,B,K,R,hell,hT,hB,hK,hR,hA,htr⟩ :=
    MomentLinearization.C11_local_coefficients_pair b hc hφ1 hL hV hI hG c
  have hP := MomentLinearization.C11_ae_subsolution volume b hc hd hL hs hVc
    (hV.differentiable one_ne_zero) hI hm
  obtain ⟨a,C,r,ha,ha1,hC,hr,hhold⟩ := C11InteriorRegularity.holder_hessian b hd hL
    (G:=univ) (by simp) (fun x _ => hgd x) (fun x _ => (hpos x).1.isHermitian)
    hell hT hB hK hR hA htr hP
  exact ⟨a,C,r,ha,ha1,hC,hr,fun x hx y hy => hhold x (mem_univ x) hx y (mem_univ y) hy⟩
end CompactMomentVariational
end

end

section

open scoped Real

open MeasureTheory
open scoped Topology

open MeasureTheory FourierTransform Convolution
open scoped SchwartzMap

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology

open MeasureTheory TemperedDistribution FourierTransform LineDeriv
open scoped SchwartzMap ContDiff

open Filter Function
open scoped SchwartzMap Topology ContDiff

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology ContDiff

open MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace WeightedCalculus


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_weight {V : E → ℝ} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (weight V) := hV.neg.exp


end WeightedCalculus

namespace MomentCoordinates

open WeightedCalculus Matrix
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma smooth_grad {f : Space ι → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (grad f) := contDiff_pi.mpr (fun i => smooth_pd hf i)

end MomentCoordinates
end

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace TargetCoordinates
open WeightedCalculus MomentCoordinates MomentDifferential MomentEquation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (μ : Measure (Space ι))

omit [DecidableEq ι] in
lemma target_integral {V : Space ι → ℝ} (hV : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z)
    (F : Space ι → ℝ) : (∫ x, F x ∂targetMeasure μ V Z) = normalizedE μ V Z F := by
  rw [targetMeasure, integral_withDensity_eq_integral_toReal_smul
    (((smooth_weight hV).continuous.div_const Z).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  change (∫ x, (ENNReal.ofReal (weight V x / Z)).toReal • F x ∂μ) = _
  have hw (x : Space ι) : 0 ≤ weight V x / Z := div_nonneg (le_of_lt (Real.exp_pos _)) hZ.le
  simp only [ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  have he : (fun x => weight V x / Z * F x) = fun x => (F x * weight V x) / Z := by
    funext x
    ring
  rw [he, integral_div]
  rfl

end TargetCoordinates

end

open scoped ContDiff Topology

open Matrix
open scoped BigOperators Kronecker
noncomputable section

namespace SoftSlab

section
open WeightedCalculus MomentCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma linear_apply (p x : ι → ℝ) : linear p x = ∑ i, p i * x i := by
  simp [linear]

omit [DecidableEq ι] in
omit [DecidableEq ι] in
lemma summand_eq (p : ι → ℝ) (h : ℝ) (q : ℕ) (x : Space ι) :
    summand p h q x = ((∑ i, p i * x i) / h)^q := by rw [summand, linear_apply]

omit [DecidableEq ι] in
lemma smooth_summand (p : ι → ℝ) (h : ℝ) (q : ℕ) : ContDiff ℝ ∞ (summand p h q) :=
  ((linear p).contDiff.div_const h).pow q

omit [DecidableEq ι] in
lemma summand_even {q : ℕ} (hq : Even q) (p : ι → ℝ) (h : ℝ) :
    Function.Even (summand p h q) := by
  intro x
  simp only [summand, map_neg, neg_div, hq.neg_pow]

omit [DecidableEq ι] in
lemma summand_nonneg {q : ℕ} (hq : Even q) (p : ι → ℝ) (h : ℝ) (x : Space ι) :
    0 ≤ summand p h q x := hq.pow_nonneg _

end

open MeasureTheory WeightedCalculus MomentCoordinates
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma smooth_potential (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (q : ℕ) :
    ContDiff ℝ ∞ (potential ε p h q) := by
  apply ContDiff.add
  · exact contDiff_const.mul (ContDiff.sum (fun j _ => (contDiff_apply ℝ ℝ j).pow 2))
  · exact ContDiff.sum (fun i _ => smooth_summand (p i) (h i) q)

omit [DecidableEq ι] in
lemma potential_even {q : ℕ} (hq : Even q) (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) :
    Function.Even (potential ε p h q) := by
  intro x
  simp only [potential, Pi.neg_apply, neg_sq]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => summand_even hq (p i) (h i) x)

omit [DecidableEq ι] in
lemma potential_lower {q : ℕ} (hq : Even q) (ε : ℝ) (p : κ → ι → ℝ) (h : κ → ℝ) (x : Space ι) :
    ε/2*(∑ j, x j^2) ≤ potential ε p h q x := by
  unfold potential
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => summand_nonneg hq (p i) (h i) x))


end SoftSlab
end

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace GaussianPolynomial
section
variable {ι : Type*} [Fintype ι]

lemma gaussian_product (b : ℝ) (x : ι → ℝ) :
    Real.exp (-b * ∑ i, x i ^ 2) = ∏ i, Real.exp (-b * x i ^ 2) := by
  rw [Finset.mul_sum, Real.exp_sum]

lemma monomial_integrable {b : ℝ} (hb : 0 < b) (d : ι → ℕ) :
    Integrable (fun x : ι → ℝ => (∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2)) := by
  have hi (i : ι) : Integrable (fun x : ℝ => x ^ d i * Real.exp (-b * x^2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq hb (by have := Nat.cast_nonneg (α := ℝ) (d i); linarith : (-1:ℝ) < (d i : ℝ))
  have hp := Integrable.fintype_prod hi
  have he : (fun x : ι → ℝ => (∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2)) =
      (fun x : ι → ℝ => ∏ i, x i ^ d i * Real.exp (-b * x i^2)) := by
    funext x
    rw [gaussian_product, Finset.prod_mul_distrib]
  rw [he]
  exact hp

lemma polynomial_integrable {b : ℝ} (hb : 0 < b) (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P * Real.exp (-b * ∑ i, x i^2)) := by
  have hi : Integrable (fun x : ι → ℝ => ∑ d ∈ P.support,
      P.coeff d * ((∏ i, x i ^ d i) * Real.exp (-b * ∑ i, x i^2))) := by
    exact integrable_finsetSum _ (fun d _ => (monomial_integrable hb d).const_mul _)
  convert hi using 1
  funext x
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

lemma dominated_polynomial {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x)
    (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => MvPolynomial.eval x P * Real.exp (-V x)) := by
  have hmaj := (polynomial_integrable hb P).norm.const_mul (Real.exp c)
  apply hmaj.mono' (((MvPolynomial.continuous_eval P).mul (Real.continuous_exp.comp hV.neg)).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  change ‖MvPolynomial.eval x P * Real.exp (-V x)‖ ≤
    Real.exp c * ‖MvPolynomial.eval x P * Real.exp (-b * ∑ i, x i^2)‖
  simp only [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-V x) ≤ Real.exp c * Real.exp (-b * ∑ i, x i^2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hlower x]
  calc
    _ ≤ ‖MvPolynomial.eval x P‖ * (Real.exp c * Real.exp (-b * ∑ i, x i^2)) :=
      mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = _ := by ring

lemma partition_integrable {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x) :
    Integrable (fun x => Real.exp (-V x)) := by
  simpa using dominated_polynomial hV hb hlower (1 : MvPolynomial ι ℝ)

end

open MeasureTheory
variable {ι : Type*} [Fintype ι]

lemma normalized_polynomial {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c Z : ℝ} (hb : 0 < b) (hZ : 0 < Z)
    (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x) (P : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x P)
      (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)/Z))) := by
  have hm : Measurable (fun x : ι → ℝ => ENNReal.ofReal (Real.exp (-V x)/Z)) :=
    ((Real.continuous_exp.comp hV.neg).div_const Z).measurable.ennreal_ofReal
  apply (integrable_withDensity_iff_integrable_smul' (μ:=volume) hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have he (x : ι → ℝ) : (ENNReal.ofReal (Real.exp (-V x)/Z)).toReal • MvPolynomial.eval x P =
      (MvPolynomial.eval x P*Real.exp (-V x))/Z := by
    rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hZ.le), smul_eq_mul]
    ring
  simp_rw [he]
  exact (dominated_polynomial hV hb hlower P).div_const Z

lemma partition_pos {V : (ι → ℝ) → ℝ} (hV : Continuous V)
    {b c : ℝ} (hb : 0 < b) (hlower : ∀ x, b * (∑ i, x i^2) - c ≤ V x) :
    0 < ∫ x, Real.exp (-V x) :=
  integral_exp_pos (partition_integrable hV hb hlower)

end GaussianPolynomial

namespace SoftSlab
open MeasureTheory WeightedCalculus MomentCoordinates
open scoped BigOperators ContDiff
variable {ι : Type*} {κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma eval_linearPolynomial (p : ι → ℝ) (h : ℝ) (x : Space ι) :
    MvPolynomial.eval x (linearPolynomial p h) = linear p x/h := by
  simp [linearPolynomial, linear_apply, map_sum, div_eq_mul_inv]

omit [DecidableEq ι] in
lemma potential_partition_pos {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) : 0 < ∫ x, Real.exp (-potential ε p h q x) :=
  GaussianPolynomial.partition_pos (c:=0) (smooth_potential ε p h q).continuous (half_pos hε)
    (by intro x; simpa using potential_lower hq ε p h x)

omit [DecidableEq ι] in
lemma polynomial_moment {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (P : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x P) (law ε p h q) :=
  GaussianPolynomial.normalized_polynomial (c:=0) (smooth_potential ε p h q).continuous (half_pos hε)
    (potential_partition_pos hq hε p h) (by intro x; simpa using potential_lower hq ε p h x) P

omit [DecidableEq ι] in
lemma integrable_summand {q : ℕ} (hq : Even q) {ε : ℝ} (hε : 0 < ε)
    (p : κ → ι → ℝ) (h : κ → ℝ) (v : ι → ℝ) (r : ℝ) (m : ℕ) :
    Integrable (summand v r m) (law ε p h q) := by
  change Integrable (fun x => (linear v x/r)^m) _
  simpa only [map_pow, eval_linearPolynomial] using
    polynomial_moment hq hε p h ((linearPolynomial v r)^m)

end SoftSlab
end

open scoped BigOperators InnerProductSpace Topology

end
section


open Set MeasureTheory
open scoped ENNReal InnerProductSpace

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace SlabPartition
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
lemma variation_eq (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t : ℝ) (x : ι → ℝ) :
    variation ψ b k t x = ∑ i, b i ^ k * Real.exp (b i * t) * MvPolynomial.eval x (ψ i) := by
  simp [variation, derivativePoly]

omit [Fintype ι] in
lemma variation_continuous (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (k : ℕ) (t : ℝ) :
    Continuous (variation ψ b k t) := MvPolynomial.continuous_eval _

lemma potential_continuous (ε : ℝ) (ψ : κ → MvPolynomial ι ℝ) (b : κ → ℝ) (t : ℝ) :
    Continuous (potential ε ψ b t) := by
  apply Continuous.add
  · exact continuous_const.mul (continuous_finsetSum _ fun j _ => (continuous_apply j).pow 2)
  · exact variation_continuous ψ b 0 t

lemma potential_lower (ε : ℝ) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) (x : ι → ℝ) :
    ε / 2 * (∑ j, x j ^ 2) ≤ potential ε ψ b t x := by
  apply le_add_of_nonneg_right
  rw [variation_eq]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hψ i x))

lemma polynomial_integrable {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ)
    (P : MvPolynomial ι ℝ) : Integrable (fun x => MvPolynomial.eval x P * density ε ψ b t x) := by
  exact GaussianPolynomial.dominated_polynomial (c := 0) (potential_continuous ε ψ b t)
    (half_pos hε) (fun x => by simpa using potential_lower ε hψ b t x) P

lemma density_integrable {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) :
    Integrable (density ε ψ b t) := by
  simpa using polynomial_integrable hε hψ b t (1 : MvPolynomial ι ℝ)

lemma partition_pos {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ) :
    0 < partition ε ψ b t := integral_exp_pos (density_integrable hε hψ b t)

lemma variance_eq {ε : ℝ} (hε : 0 < ε) {ψ : κ → MvPolynomial ι ℝ}
    (hψ : ∀ i x, 0 ≤ MvPolynomial.eval x (ψ i)) (b : κ → ℝ) (t : ℝ)
    (P : MvPolynomial ι ℝ) :
    variance ε ψ b t (fun x => MvPolynomial.eval x P) =
      mean ε ψ b t (fun x => MvPolynomial.eval x P ^ 2) -
        mean ε ψ b t (fun x => MvPolynomial.eval x P) ^ 2 := by
  have hP := polynomial_integrable hε hψ b t P
  have hP₂ : Integrable (fun x => MvPolynomial.eval x P ^ 2 * density ε ψ b t x) := by
    convert! polynomial_integrable hε hψ b t (P^2) using 1
    funext x
    rw [map_pow]
  have hd := density_integrable hε hψ b t
  let m := mean ε ψ b t (fun x => MvPolynomial.eval x P)
  have he : (fun x => (MvPolynomial.eval x P-m)^2 * density ε ψ b t x) =
      (fun x => MvPolynomial.eval x P ^ 2 * density ε ψ b t x -
        2*m*(MvPolynomial.eval x P * density ε ψ b t x) + m^2*density ε ψ b t x) := by
    funext x
    ring
  change (∫ x, (MvPolynomial.eval x P-m)^2 * density ε ψ b t x) / partition ε ψ b t = _
  have hsub : Integrable (fun x => MvPolynomial.eval x P ^ 2 * density ε ψ b t x -
      2*m*(MvPolynomial.eval x P * density ε ψ b t x)) := by
    simpa only [Pi.sub_apply] using! hP₂.sub (hP.const_mul (2*m))
  rw [he, integral_add hsub (hd.const_mul (m^2)),
    integral_sub hP₂ (hP.const_mul (2*m)), integral_const_mul, integral_const_mul]
  have hZ := (partition_pos hε hψ b t).ne'
  dsimp [m, mean, partition] at *
  field_simp
  ring

end SlabPartition

namespace SlabReduction
open MeasureTheory Set Filter
open scoped BigOperators Topology
variable {ι : Type*} {κ : Type*} [Fintype ι] [Fintype κ]

lemma eval_feature (p x : ι → ℝ) (h : ℝ) (q : ℕ) :
    MvPolynomial.eval x (feature p h q) = (p ⬝ᵥ x / h)^q := by
  simp [feature, linearPoly, dotProduct, div_eq_mul_inv, mul_comm]

omit [Fintype κ] in
lemma features_nonneg (p : κ → ι → ℝ) (h : κ → ℝ) {q : ℕ} (hq : Even q) :
    ∀ i x, 0 ≤ MvPolynomial.eval x (features p h q i) := by
  intro i x
  rw [features, eval_feature]
  exact hq.pow_nonneg _

end SlabReduction

end


end



noncomputable section


namespace CompactMomentVariational
open Set Metric Matrix Filter MeasureTheory HolderJets
open scoped InnerProductSpace NNReal ENNReal ContDiff Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

attribute [local instance] OAI.CompactMomentVariational.instNormedAddCommGroupContinuousLinearMapRealIdEuclideanSpace_solutions
attribute [local instance] OAI.CompactMomentVariational.instNormedSpaceRealContinuousLinearMapIdEuclideanSpace_solutions
attribute [local instance] OAI.CompactMomentVariational.instNormedAddCommGroupContinuousLinearMapRealIdEuclideanSpace_solutions_1
attribute [local instance] OAI.CompactMomentVariational.instNormedSpaceRealContinuousLinearMapIdEuclideanSpace_solutions_1
theorem C2_to_smooth (b : OrthonormalBasis ι ℝ E) {φ V : E → ℝ}
    (hc : ConvexOn ℝ univ φ) (hφ : ContDiff ℝ 2 φ)
    {L : ℝ≥0} (hL : LipschitzWith L (gradient φ))
    (hs : Function.Surjective (gradient φ)) (hVc : ConvexOn ℝ univ V)
    (hV : ContDiff ℝ ∞ V) (hI : Integrable (fun x => Real.exp (-V x)) volume)
    (hm : Measure.map (gradient φ) (volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-φ z)))) =
      normalizedSource volume V) : ContDiff ℝ ∞ φ := by
  have hV2:ContDiff ℝ 2 V:=hV.of_le (WithTop.coe_le_coe.mpr le_top)
  have hpos := C2_positive_MA b hc hφ hL hs hV.continuous hI hm
  have hp:∀x,(MomentQuotient.matrixHessian b φ x).PosDef := fun x=>(hpos x).1
  have heq:∀x,Real.log (MomentQuotient.matrixHessian b φ x).det=
      V (gradient φ x)+Real.log (∫ x,Real.exp (-V x))-φ x := by
    intro x
    simpa only [MomentQuotient.matrixHessian,LinearMap.det_toMatrix] using (hpos x).2
  have hgain (c:E) : ∃a r:ℝ,0<a ∧ a<1 ∧ 0<r ∧ ContDiffOn ℝ 3 φ (ball c r) ∧
      ∃U:ℝ,0≤U ∧ ∀x∈ball c r,∀y∈ball c r,
        dist (fderiv ℝ (HessianInterpolation.hessian φ) x)
          (fderiv ℝ (HessianInterpolation.hessian φ) y)≤U*dist x y^a := by
    obtain ⟨a,C,R,ha,ha1,hC,hR,hh⟩ := C2_local_holder b hc hφ hL hs hVc
      (hV.of_le (by simp)) hI hm c
    obtain ⟨r,hr,h3,hhold⟩ := MomentQuotient.C3_local volume b hφ
      hV2 heq hp ha ha1 hC hR hh
    exact ⟨a,r,ha,ha1,hr,h3,hhold⟩
  have h3:ContDiff ℝ 3 φ := contDiff_iff_contDiffAt.mpr (fun c=>by
    obtain ⟨a,r,ha,ha1,hr,hc,hhold⟩:=hgain c
    exact hc.contDiffAt (ball_mem_nhds c hr))
  have hH:ContDiff ℝ 1 (HessianInterpolation.hessian φ) :=
    (h3.fderiv_right (m:=2) (by norm_num)).fderiv_right (by norm_num)
  have hDC:Continuous (fderiv ℝ (HessianInterpolation.hessian φ)) :=
    (contDiff_one_iff_fderiv.mp hH).2
  have hreg:Regular 3 φ := by
    refine ⟨h3.differentiable (by norm_num),
      (h3.fderiv_right (m:=2) (by norm_num)).differentiable (by norm_num),
      hH.differentiable one_ne_zero,hDC,?_⟩
    intro c
    obtain ⟨a,r,ha,ha1,hr,_,C,hC,hh⟩ := hgain c
    obtain ⟨B,hB⟩ := (isCompact_closedBall c (r/2)).exists_bound_of_continuousOn hDC.continuousOn
    have hsub:closedBall c (r/2)⊆ball c r := closedBall_subset_ball (by linarith)
    exact ⟨a,r/2,ha,ha1,by positivity,max 0 B,C,le_max_left _ _,hC,
      fun _ x hx=>(hB x hx).trans (le_max_right _ _),fun _ x hx y hy=>hh x (hsub hx) y (hsub hy)⟩
  exact MomentSchauder.smooth_of_regular_three volume b hreg hV heq hp

end CompactMomentVariational
end



noncomputable section
namespace MomentCoordinatesBridge
open MeasureTheory Set Matrix MomentCoordinates
open scoped InnerProductSpace ContDiff
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => (ι → ℝ)
lemma coord_basis (i:ι) : (coord (ι:=ι)).symm (basis i)=ob i := by
  ext j
  simp [coord,ob,EuclideanSpace.basisFun_apply,basis]
lemma grad_pull {φ:E→ℝ} (hφ:Differentiable ℝ φ) (x:P) :
    grad (fun z=>φ (coord.symm z)) x=coord (gradient φ (coord.symm x)) := by
  ext i
  change fderiv ℝ (fun z=>φ (coord.symm z)) x (basis i)=_
  have hd:=((hφ (coord.symm x)).hasGradientAt.hasFDerivAt.comp x (coord (ι:=ι)).symm.toContinuousLinearMap.hasFDerivAt).fderiv
  dsimp only [Function.comp_def] at hd
  rw [hd,ContinuousLinearMap.comp_apply]
  change ⟪gradient φ (coord.symm x),coord.symm (basis i)⟫_ℝ=_
  rw [coord_basis]
  exact EuclideanSpace.inner_basisFun_real ι _ i
lemma pd_pull {φ:E→ℝ} (hφ:Differentiable ℝ φ) (i:ι) :
    pd i (fun z=>φ (coord.symm z))=fun x=>(coord (gradient φ (coord.symm x))) i := by
  funext x
  exact congrFun (grad_pull hφ x) i
lemma hess_pull {φ:E→ℝ} (hφ:ContDiff ℝ ∞ φ) (x:P) :
    hess (fun z=>φ (coord.symm z)) x=
      MomentLinearization.hessian ob φ (coord.symm x) := by
  have hG:ContDiff ℝ ∞ (gradient φ):=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hφ.fderiv_right (by simp))
  ext i j
  change pd j (pd i (fun z=>φ (coord.symm z))) x=_
  rw [pd_pull (hφ.differentiable (by simp))]
  let ev : E→L[ℝ]ℝ := (ContinuousLinearMap.proj i).comp coord.toContinuousLinearMap
  have hd:=((ev.hasFDerivAt.comp (coord.symm x)
    (hG.differentiable (by simp) (coord.symm x)).hasFDerivAt).comp x (coord (ι:=ι)).symm.toContinuousLinearMap.hasFDerivAt).fderiv
  change fderiv ℝ (fun z=>ev (gradient φ (coord.symm z))) x (basis j)=_
  dsimp only [Function.comp_def] at hd
  rw [hd,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
  simp only [ev,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  change (coord ((fderiv ℝ (gradient φ) (coord.symm x)) (coord.symm (basis j)))) i=_
  rw [coord_basis]
  simp [MomentLinearization.hessian,LinearMap.toMatrix_apply,ob,coord,
    OrthonormalBasis.coe_toBasis_repr_apply]
end MomentCoordinatesBridge


namespace SoftEuclidean
open MeasureTheory Set SoftSlab
open scoped InnerProductSpace ContDiff
variable {ι κ:Type} [Fintype ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "C" => PiLp.continuousLinearEquiv 2 ℝ (fun _:ι=>ℝ)
lemma convex_summand {q:ℕ} (hq:Even q) (p:ι→ℝ) (h:ℝ) :
    ConvexOn ℝ univ (summand p h q) := by
  have hh:ConvexOn ℝ univ (fun t:ℝ=>t^q):=hq.convexOn_pow
  change ConvexOn ℝ univ (fun x => (linear p x/h)^q)
  simpa only [preimage_univ,Function.comp_def,LinearMap.smul_apply,ContinuousLinearMap.coe_coe,smul_eq_mul,div_eq_mul_inv,mul_comm] using
    hh.comp_linearMap (h⁻¹ • (linear p).toLinearMap)
lemma convex_sum {q:ℕ} (hq:Even q) (p:κ→ι→ℝ) (h:κ→ℝ) :
    ConvexOn ℝ univ (fun x:E=>∑i,summand (p i) (h i) q (C x)) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  simp only [map_add,map_smul,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => (convex_summand hq (p i) (h i)).2
    (mem_univ _) (mem_univ _) ha hb hab
lemma midpoint_curvature {q:ℕ} (hq:Even q) (ε:ℝ) (p:κ→ι→ℝ) (h:κ→ℝ) (x y:E) :
    ε/8*‖x-y‖^2 ≤
      (potential ε p h q (C x)+potential ε p h q (C y))/2-
        potential ε p h q (C ((1/2:ℝ) • (x+y))) := by
  have hh: (∑i,summand (p i) (h i) q (C ((1/2:ℝ) • (x+y)))) ≤
      ((∑i,summand (p i) (h i) q (C x))+(∑i,summand (p i) (h i) q (C y)))/2 := by
    have ht := (convex_sum hq p h).2 (mem_univ x) (mem_univ y)
      (by norm_num:(0:ℝ)≤1/2) (by norm_num:(0:ℝ)≤1/2) (by norm_num:(1:ℝ)/2+1/2=1)
    simp only [← smul_add,smul_eq_mul] at ht
    linarith
  have hn (z:E) : ∑i,(C z) i^2=‖z‖^2 := (EuclideanSpace.real_norm_sq_eq z).symm
  simp only [potential,hn]
  rw [norm_smul, mul_pow, Real.norm_eq_abs,abs_of_pos (by norm_num:(0:ℝ)<1/2),
    norm_add_sq_real,norm_sub_sq_real]
  nlinarith
lemma convex_potential {q:ℕ} (hq:Even q) {ε:ℝ} (hε:0≤ε) (p:κ→ι→ℝ) (h:κ→ℝ) :
    ConvexOn ℝ univ (fun x:E=>potential ε p h q (C x)) := by
  have hsq : ConvexOn ℝ univ (fun x:E=>∑i,(C x) i^2) := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact (even_two.convexOn_pow (𝕜:=ℝ)).2 (mem_univ ((C x) i))
      (mem_univ ((C y) i)) ha hb hab
  exact (hsq.smul (div_nonneg hε (by norm_num))).add (convex_sum hq p h)
lemma integrable_potential {q:ℕ} (hq:Even q) {ε:ℝ} (hε:0<ε)
    (p:κ→ι→ℝ) (h:κ→ℝ) :
    Integrable (fun x:E=>Real.exp (-potential ε p h q (C x))) volume := by
  have hi := GaussianPolynomial.partition_integrable (smooth_potential ε p h q).continuous
    (b:=ε/2) (c:=0) (by positivity) (fun x=>by simpa using potential_lower hq ε p h x)
  exact ((PiLp.volume_preserving_ofLp ι).integrable_comp hi.aestronglyMeasurable).mpr hi
end SoftEuclidean


namespace MomentHessianCap
open MeasureTheory Set Filter Matrix
open scoped InnerProductSpace Topology ContDiff
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
lemma inner_cap {φ:E→ℝ} (hφ:ContDiff ℝ 2 φ) {C:ℝ}
    (hb:∀h z,WeakMomentBound.secondDiff φ h z≤C*‖h‖^2) (x v:E) :
    ⟪(fderiv ℝ (gradient φ) x) v,v⟫_ℝ≤C*‖v‖^2 := by
  have hg:ContDiff ℝ 1 (gradient φ):=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hφ.fderiv_right (by norm_num))
  apply le_of_tendsto (SecondQuotient.gradient_limit (hφ.differentiable (by norm_num))
    (hg.differentiable one_ne_zero x) (e:=v))
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0:t≠0:=ht
  apply (div_le_iff₀ (sq_pos_of_ne_zero ht0)).mpr
  have hh:=hb (t • v) x
  simpa only [WeakMomentBound.secondDiff,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc,mul_comm,mul_left_comm] using hh
lemma matrix_cap (b:OrthonormalBasis ι ℝ E) {φ:E→ℝ} (hφ:ContDiff ℝ 2 φ)
    (hp:∀x,(MomentLinearization.hessian b φ x).PosDef) {C:ℝ}
    (hb:∀h z,WeakMomentBound.secondDiff φ h z≤C*‖h‖^2) (x:E) :
    (C • (1:Matrix ι ι ℝ)-MomentLinearization.hessian b φ x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul (k:=C) (by simp [IsSelfAdjoint])).sub (hp x).isHermitian)
  intro v
  have hi:=inner_cap hφ hb x (HessianCoordinates.vector b v)
  rw [←HessianCoordinates.quadratic_toMatrix b] at hi
  have hn:‖HessianCoordinates.vector b v‖^2=∑i,v i^2 := by
    rw [HessianCoordinates.vector,LinearIsometryEquiv.norm_map,EuclideanSpace.real_norm_sq_eq]
  rw [hn] at hi
  change FiniteElliptic.quadratic (C • (1:Matrix ι ι ℝ)-MomentLinearization.hessian b φ x) v ≥ 0
  simp only [FiniteElliptic.quadratic,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul]
  change 0≤C*(v ⬝ᵥ v)-FiniteElliptic.quadratic (MomentLinearization.hessian b φ x) v
  rw [show v ⬝ᵥ v=∑i,v i^2 by simp only [dotProduct,pow_two]]
  exact sub_nonneg.mpr hi
lemma positive_derivative (b:OrthonormalBasis ι ℝ E) {φ:E→ℝ}
    (hp:∀x,(MomentLinearization.hessian b φ x).PosDef) (x v:E) (hv:v≠0) :
    0<⟪v,(fderiv ℝ (gradient φ) x) v⟫_ℝ := by
  let w:ι→ℝ:=fun i=>b.repr v i
  have hw:w≠0 := by
    intro hh
    apply hv
    apply b.repr.injective
    ext i
    simpa [w] using congrFun hh i
  have hh:0<FiniteElliptic.quadratic (MomentLinearization.hessian b φ x) w:=
    (hp x).dotProduct_mulVec_pos hw
  unfold MomentLinearization.hessian at hh
  rw [HessianCoordinates.quadratic_toMatrix] at hh
  have he:HessianCoordinates.vector b w=v := by
    apply b.repr.injective
    ext i
    simp [HessianCoordinates.vector,w]
  simpa only [he,real_inner_comm] using hh
end MomentHessianCap


namespace PositiveDiffeomorphism
open scoped ContDiff InnerProductSpace
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma injective {G:E→E} (hG:Differentiable ℝ G)
    (hp:∀x v:E,v≠0 → 0<⟪v,fderiv ℝ G x v⟫_ℝ) : Function.Injective G := by
  intro x y he
  by_contra hxy
  let v:=y-x
  have hv:v≠0:=sub_ne_zero.mpr (Ne.symm hxy)
  let f:ℝ→ℝ:=fun t=>⟪v,G (x+t • v)⟫_ℝ
  have hf(t:ℝ):HasDerivAt f ⟪v,fderiv ℝ G (x+t • v) v⟫_ℝ t := by
    have hl:HasDerivAt (fun t:ℝ=>x+t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (InnerProductSpace.toDual ℝ E v).hasFDerivAt.comp_hasDerivAt t
      ((hG (x+t • v)).hasFDerivAt.comp_hasDerivAt t hl)
  have hh:=strictMono_of_hasDerivAt_pos hf (fun t=>hp _ v hv) (by norm_num : (0:ℝ)<1)
  dsimp only [f] at hh
  simp only [zero_smul,add_zero,one_smul] at hh
  have hsum:x+v=y := by dsimp [v]; abel
  rw [hsum,he] at hh
  exact (lt_irrefl _ hh)

theorem exists_homeomorph {G:E→E} (hG:ContDiff ℝ ∞ G)
    (hp:∀x v:E,v≠0 → 0<⟪v,fderiv ℝ G x v⟫_ℝ)
    (hs:Function.Surjective G) :
    ∃Φ:E≃ₜE,(Φ:E→E)=G ∧ ContDiff ℝ ∞ (Φ.symm:E→E) := by
  have hd:=hG.differentiable (by simp)
  have hbij(x:E):Function.Bijective (fderiv ℝ G x) := by
    have hi:Function.Injective (fderiv ℝ G x) := by
      apply LinearMap.ker_eq_bot.mp
      rw [LinearMap.ker_eq_bot']
      intro v hv
      by_contra hn
      have hh:=hp x v hn
      change (fderiv ℝ G x) v=0 at hv
      simp only [hv,inner_zero_right] at hh
      exact (lt_irrefl _ hh)
    exact ⟨hi,(LinearMap.injective_iff_surjective (f:=(fderiv ℝ G x).toLinearMap)).mp hi⟩
  let A:E→E≃L[ℝ]E:=fun x=>ContinuousLinearEquiv.ofBijective (fderiv ℝ G x) (LinearMap.ker_eq_bot.mpr (hbij x).1) (LinearMap.range_eq_top.mpr (hbij x).2)
  have hAd(x:E):HasFDerivAt G (A x:E→L[ℝ]E) x := (hd x).hasFDerivAt
  have ho:IsOpenMap G:=isOpenMap_of_hasStrictFDerivAt_equiv (fun x=>
    show HasStrictFDerivAt G (A x:E→L[ℝ]E) x from hG.contDiffAt.hasStrictFDerivAt (by simp))
  let Φ:E≃ₜE:=(Equiv.ofBijective G ⟨injective hd hp,hs⟩).toHomeomorphOfContinuousOpen hG.continuous ho
  exact ⟨Φ,rfl,Φ.contDiff_symm hAd hG⟩
end PositiveDiffeomorphism


namespace MeasureCoordinates
open MeasureTheory Set
variable {E : Type*} {F : Type*} [MeasurableSpace E] [MeasurableSpace F]
lemma map_density (e:E≃ᵐF) {μ:Measure E} {ν:Measure F}
    (he:MeasurePreserving e μ ν) {f:F→ENNReal} (hf:Measurable f) :
    Measure.map e (μ.withDensity (fun x=>f (e x)))=ν.withDensity f := by
  ext S hS
  rw [Measure.map_apply e.measurable hS,withDensity_apply _ (e.measurable hS),withDensity_apply _ hS,
    ←he.map_eq,setLIntegral_map hS hf e.measurable]
end MeasureCoordinates


namespace MomentCoordinatesBridge
open MeasureTheory MomentCoordinates TargetCoordinates
open scoped ContDiff
variable {ι:Type} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => (ι→ℝ)
local notation "C" => (coord (ι:=ι))
lemma coord_integral (f:P→ℝ) : (∫x:E,f (C x))=∫x:P,f x :=
  (PiLp.volume_preserving_ofLp ι).integral_comp
    (C).toHomeomorph.toMeasurableEquiv.measurableEmbedding f
lemma coord_density {f:P→ENNReal} (hf:Measurable f) :
    Measure.map C (volume.withDensity (fun x:E=>f (C x)))=volume.withDensity f :=
  MeasureCoordinates.map_density (C).toHomeomorph.toMeasurableEquiv
    (PiLp.volume_preserving_ofLp ι) hf
lemma coord_source {φ:E→ℝ} (hφ:ContDiff ℝ ∞ φ) :
    Measure.map C (volume.withDensity (fun x:E=>ENNReal.ofReal (Real.exp (-φ x))))=
      sourceMeasure volume (fun x:P=>φ ((C).symm x)) := by
  have ht:=coord_density (ι:=ι)
    (f:=fun x:P=>ENNReal.ofReal (Real.exp (-φ ((C).symm x))))
    ((hφ.comp (C).symm.contDiff).continuous.neg.rexp.measurable.ennreal_ofReal)
  simpa only [(C).symm_apply_apply,sourceMeasure,WeightedCalculus.weight] using ht
lemma coord_normalized {V:P→ℝ} (hV:ContDiff ℝ ∞ V) :
    Measure.map C (CompactMomentVariational.normalizedSource volume (fun x:E=>V (C x)))=
      targetMeasure volume V (∫x:P,Real.exp (-V x)) := by
  unfold CompactMomentVariational.normalizedSource targetMeasure WeightedCalculus.weight
  rw [coord_integral (ι:=ι) (fun x:P=>Real.exp (-V x))]
  exact coord_density (ι:=ι)
    (f:=fun x:P=>ENNReal.ofReal (Real.exp (-V x)/(∫y:P,Real.exp (-V y))))
    ((hV.continuous.neg.rexp.div_const (∫y:P,Real.exp (-V y))).measurable.ennreal_ofReal)
end MomentCoordinatesBridge


namespace ActualMoment
section
open MeasureTheory Set Matrix MomentCoordinatesBridge
open scoped InnerProductSpace ContDiff
variable {ι κ:Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "C" => (coord (ι:=ι))

theorem euclidean {q:ℕ} (hq:Even q) {ε:ℝ} (hε:0<ε)
    (p:κ→ι→ℝ) (h:κ→ℝ) :
    ∃φ:E→ℝ, ContDiff ℝ ∞ φ ∧
      (∀x,(MomentLinearization.hessian ob φ x).PosDef) ∧
      (∀x,((4/ε) • (1:Matrix ι ι ℝ)-MomentLinearization.hessian ob φ x).PosSemidef) ∧
      (∀x, Real.log (MomentLinearization.hessian ob φ x).det=
        SoftSlab.potential ε p h q (C (gradient φ x))+
        Real.log (∫x:E,Real.exp (-SoftSlab.potential ε p h q (C x)))-φ x) ∧
      ∃Φ:E≃ₜE,(Φ:E→E)=gradient φ ∧ ContDiff ℝ ∞ (Φ.symm:E→E) ∧
        Measure.map (gradient φ) (volume.withDensity (fun x=>ENNReal.ofReal (Real.exp (-φ x))))=
          CompactMomentVariational.normalizedSource volume (fun x:E=>SoftSlab.potential ε p h q (C x)) := by
  let V:E→ℝ:=fun x=>SoftSlab.potential ε p h q (C x)
  have hV:ContDiff ℝ ∞ V := (SoftSlab.smooth_potential ε p h q).comp (C).contDiff
  have hVc:=SoftEuclidean.convex_potential hq hε.le p h
  have hI:=SoftEuclidean.integrable_potential hq hε p h
  obtain ⟨φ,hc,_,hC1,hL,hcap,_,_,hm,hs⟩:=
    CompactMomentVariational.exists_C11_global volume ob hV.continuous
      (fun x=>by simpa only [V,map_neg] using SoftSlab.potential_even hq ε p h (C x))
      hI hε (SoftEuclidean.midpoint_curvature hq ε p h)
  have hC2:=CompactMomentVariational.C11_to_C2 ob hc hC1 hL hs hVc
    (hV.of_le (by simp)) hI hm
  have hSmooth:=CompactMomentVariational.C2_to_smooth ob hc hC2 hL hs hVc hV hI hm
  have hMA:=CompactMomentVariational.C2_positive_MA ob hc hC2 hL hs hV.continuous hI hm
  have hp:∀x,(MomentLinearization.hessian ob φ x).PosDef:=fun x=>(hMA x).1
  have hG:ContDiff ℝ ∞ (gradient φ):=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hSmooth.fderiv_right (by simp))
  obtain ⟨Φ,hΦ,hInv⟩:=PositiveDiffeomorphism.exists_homeomorph hG
    (MomentHessianCap.positive_derivative ob hp) hs
  refine ⟨φ,hSmooth,hp,MomentHessianCap.matrix_cap ob hC2 hp hcap,?_,Φ,hΦ,hInv,hm⟩
  intro x
  simpa only [MomentLinearization.hessian,LinearMap.det_toMatrix] using (hMA x).2
end


section
open MeasureTheory Set Matrix MomentCoordinatesBridge MomentCoordinates TargetCoordinates
open scoped InnerProductSpace ContDiff
variable {ι κ:Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "P" => (ι→ℝ)
local notation "C" => (coord (ι:=ι))
theorem coordinates {q:ℕ} (hq:Even q) {ε:ℝ} (hε:0<ε)
    (p:κ→ι→ℝ) (h:κ→ℝ) :
    ∃φ:P→ℝ, ContDiff ℝ ∞ φ ∧ (∀x,(hess φ x).PosDef) ∧
      (∀x,((4/ε) • (1:Matrix ι ι ℝ)-hess φ x).PosSemidef) ∧
      (∀x, Real.log (hess φ x).det=SoftSlab.potential ε p h q (grad φ x)+
        Real.log (∫x:P,Real.exp (-SoftSlab.potential ε p h q x))-φ x) ∧
      ∃Φ:P≃ₜP,(Φ:P→P)=grad φ ∧ ContDiff ℝ ∞ (Φ.symm:P→P) ∧
        Measure.map (grad φ) (sourceMeasure volume φ)=SoftSlab.law ε p h q := by
  obtain ⟨φ,hφ,hpos,hcap,heq,Φ,hΦ,hInv,hm⟩:=euclidean hq hε p h
  let ψ:P→ℝ:=fun x=>φ ((C).symm x)
  have hψ:ContDiff ℝ ∞ ψ:=hφ.comp (C).symm.contDiff
  let Ψ:P≃ₜP:=((C).symm.toHomeomorph.trans Φ).trans (C).toHomeomorph
  have hg:∀x,grad ψ x=C (gradient φ ((C).symm x)):=grad_pull (hφ.differentiable (by simp))
  have hh:∀x,hess ψ x=MomentLinearization.hessian ob φ ((C).symm x):=hess_pull hφ
  have hΨ:(Ψ:P→P)=grad ψ := by
    funext x
    rw [hg]
    change C (Φ ((C).symm x))=_
    rw [hΦ]
  have hΨi:ContDiff ℝ ∞ (Ψ.symm:P→P):=(C).contDiff.comp (hInv.comp (C).symm.contDiff)
  have hZ:=coord_integral (ι:=ι) (fun x:P=>Real.exp (-SoftSlab.potential ε p h q x))
  have hsrc:Measure.map C (volume.withDensity (fun x:E=>ENNReal.ofReal (Real.exp (-φ x))))=
      sourceMeasure volume ψ := coord_source hφ
  have htar:Measure.map C (CompactMomentVariational.normalizedSource volume
      (fun x:E=>SoftSlab.potential ε p h q (C x)))=SoftSlab.law ε p h q :=
    coord_normalized (SoftSlab.smooth_potential ε p h q)
  have hmap:Measure.map (grad ψ) (sourceMeasure volume ψ)=SoftSlab.law ε p h q := by
    rw [←hsrc,Measure.map_map (smooth_grad hψ).continuous.measurable (C).continuous.measurable]
    have hgC:(grad ψ) ∘ C=C ∘ (gradient φ) := by
      funext x
      simp only [Function.comp_apply,hg,(C).symm_apply_apply]
    rw [hgC,←Measure.map_map (C).continuous.measurable]
    · rw [hm,htar]
    · exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
        (hφ.fderiv_right (m:=∞) (by simp))).continuous.measurable
  refine ⟨ψ,hψ,(fun x=>by rw [hh];exact hpos _),
    (fun x=>by rw [hh];exact hcap _),?_,Ψ,hΨ,hΨi,hmap⟩
  intro x
  rw [hh,hg]
  simpa only [hZ] using heq ((C).symm x)
end


open MeasureTheory Set Matrix MomentCoordinates TargetCoordinates SoftSlab
open scoped ContDiff
variable {ι κ:Type} [Fintype ι] [Fintype κ]
lemma feature_eval (p:ι→ℝ) (h:ℝ) (q:ℕ) (x:ι→ℝ) :
    MvPolynomial.eval x (SlabReduction.feature p h q)=summand p h q x := by
  rw [SlabReduction.eval_feature,summand_eq]
  rfl
lemma density_eq (p:κ→ι→ℝ) (h:κ→ℝ) (ε:ℝ) (q:ℕ) :
    SlabPartition.density ε (SlabReduction.features p h q) (fun _=>0) 0=
      fun x=>Real.exp (-potential ε p h q x) := by
  funext x
  unfold SlabPartition.density SlabPartition.potential potential
  rw [SlabPartition.variation_eq]
  simp only [pow_zero,zero_mul,Real.exp_zero,one_mul,SlabReduction.features,feature_eval]
lemma mean_eq {q:ℕ} (hq:Even q) {ε:ℝ} (hε:0<ε)
    (p:κ→ι→ℝ) (h:κ→ℝ) (F:(ι→ℝ)→ℝ) :
    SlabPartition.mean ε (SlabReduction.features p h q) (fun _=>0) 0 F=
      ∫x,F x ∂law ε p h q := by
  change _ = ∫x,F x ∂targetMeasure volume (potential ε p h q)
    (∫x,Real.exp (-potential ε p h q x))
  rw [target_integral volume (smooth_potential ε p h q) (potential_partition_pos hq hε p h)]
  unfold SlabPartition.mean SlabPartition.partition normalizedE WeightedCalculus.expectation
  rw [density_eq]
  rfl
lemma variance_eq {q:ℕ} (hq:Even q) {ε:ℝ} (hε:0<ε)
    (p:κ→ι→ℝ) (h:κ→ℝ) (b:κ→ℝ) :
    SlabPartition.variance ε (SlabReduction.features p h q) (fun _=>0) 0
      (fun x=>∑i,b i*MvPolynomial.eval x (SlabReduction.features p h q i))=
    (∫x,(∑i,b i*summand (p i) (h i) q x)^2 ∂law ε p h q)-
      (∫x,∑i,b i*summand (p i) (h i) q x ∂law ε p h q)^2 := by
  classical
  let P:MvPolynomial ι ℝ:=∑i,MvPolynomial.C (b i)*SlabReduction.features p h q i
  have hP: (fun x=>MvPolynomial.eval x P)=
      (fun x=>∑i,b i*MvPolynomial.eval x (SlabReduction.features p h q i)) := by
    funext x
    simp [P]
  rw [←hP,SlabPartition.variance_eq hε (SlabReduction.features_nonneg p h hq)]
  simp only [mean_eq hq hε p h,P,map_sum,map_mul,MvPolynomial.eval_C,
    SlabReduction.features,feature_eval]
lemma covariance_rhs {q:ℕ} (hq:Even q) {ε:ℝ} (hε:0<ε)
    (p:κ→ι→ℝ) (h:κ→ℝ) (b:κ→ℝ) :
    SlabPartition.mean ε (SlabReduction.features p h q) (fun _=>0) 0
      (fun x=>∑i,b i^2*MvPolynomial.eval x (SlabReduction.features p h q i))=
      ∑i,b i^2*(∫x,summand (p i) (h i) q x ∂law ε p h q) := by
  rw [mean_eq hq hε p h]
  simp only [SlabReduction.features,feature_eval]
  rw [integral_finsetSum _ (fun i _=>(integrable_summand hq hε p h (p i) (h i) q).const_mul _)]
  simp only [integral_const_mul]
end ActualMoment


namespace LogBrunnMinkowski
open MeasureTheory Set
open scoped InnerProductSpace ENNReal ContDiff

theorem softVariance_oai : SoftVarianceStatement := by
  intro n hn κ _ _ q hq hq2 ε hε p hp h hh b
  classical
  let : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp (by omega)
  have hqm:Even (q-2):=(Nat.even_sub hq2).mpr (iff_of_true hq even_two)
  have hqq:q-2+2=q:=Nat.sub_add_cancel hq2
  obtain ⟨φ,hφ,hpos,hcap,heq,Φ,hΦ,hInv,hm⟩:=
    ActualMoment.coordinates (hqm.add even_two) hε p h
  have hv:=MomentSlab.variance_from_moment hqm hε p h hp hh hφ hpos hcap heq Φ hΦ hInv hm b
  simp only [hqq] at hv
  rw [ActualMoment.variance_eq hq hε p h b,ActualMoment.covariance_rhs hq hε p h b]
  exact hv

end LogBrunnMinkowski
end

end OAI
end

theorem solution : type_of% @OAI.LogBrunnMinkowski.softVariance_oai := @OAI.LogBrunnMinkowski.softVariance_oai

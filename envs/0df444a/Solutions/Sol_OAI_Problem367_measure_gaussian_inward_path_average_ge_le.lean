-- Prove2me | solution 1 for OAI.Problem367.measure_gaussian_inward_path_average_ge_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:45:02.951523+00:00
-- url     : https://prove2.me/submissions/b94bee72-ed5a-4b65-9d23-5ac8d6a4c0e8

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_selectedPosterior_root_component

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem binaryFusion_abs_mul_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |u * v| < 1 := by
  rw [abs_mul]
  calc
    |u| * |v| ≤ |u| * 1 := mul_le_mul_of_nonneg_left hv.le (abs_nonneg u)
    _ < 1 := by simpa using hu

theorem binaryFusion_denominator_pos {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 < 1 + u * v := by
  have h := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).1
  linarith

theorem one_sub_binaryFusion_sq {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    1 - binaryFusion u v ^ 2 =
      (1 - u ^ 2) * (1 - v ^ 2) / (1 + u * v) ^ 2 := by
  have hd := ne_of_gt (binaryFusion_denominator_pos hu hv)
  unfold binaryFusion
  field_simp
  ring

theorem abs_binaryFusion_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |binaryFusion u v| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one _).mp
  have hu' : 0 < 1 - u ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one u).mpr hu
    linarith
  have hv' : 0 < 1 - v ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one v).mpr hv
    linarith
  have hd := binaryFusion_denominator_pos hu hv
  have hpos : 0 < 1 - binaryFusion u v ^ 2 := by
    rw [one_sub_binaryFusion_sq hu hv]
    positivity
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_ArtanhFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tanh_add_eq_binaryFusion (a b : ℝ) :
    Real.tanh (a + b) = binaryFusion (Real.tanh a) (Real.tanh b) := by
  have ha : |Real.tanh a| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one a)
  have hb : |Real.tanh b| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one b)
  apply (eq_div_iff (binaryFusion_denominator_pos ha hb).ne').2
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp
  have hc : Real.cosh b * Real.cosh a + Real.sinh a * Real.sinh b ≠ 0 := by
    simpa only [Real.cosh_add, mul_comm] using (Real.cosh_pos (a + b)).ne'
  exact mul_div_cancel_right₀ _ hc

theorem artanh_binaryFusion {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh (binaryFusion x y) = Real.artanh x + Real.artanh y := by
  apply Real.tanh_injective
  rw [Real.tanh_artanh (abs_lt.mp (abs_binaryFusion_lt_one hx hy)),
    tanh_add_eq_binaryFusion, Real.tanh_artanh (abs_lt.mp hx),
    Real.tanh_artanh (abs_lt.mp hy)]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun m hm f g ν) :
    CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mp hfg U V hU hV)
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.trans (hωmul.trans (congrArg₂ (· * ·) hωE.symm hωH.symm))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentProductIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem setIntegral_prod_preimage_fst
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {f : S × A → ℝ} (hf : Integrable f (ρ.prod μ)) (D : Set S) :
    (∫ z in Prod.fst ⁻¹' D, f z ∂ρ.prod μ) =
      ∫ s in D, ∫ a, f (s, a) ∂μ ∂ρ := by
  have hset : (Prod.fst ⁻¹' D : Set (S × A)) = D ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, ← Measure.restrict_prod_eq_prod_univ]
  apply integral_prod
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hf.restrict

theorem condExp_prod_fst
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    {f : S × A → ℝ} (hfm : StronglyMeasurable f) (hf : Integrable f (ρ.prod μ)) :
    (ρ.prod μ)[f | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
      fun z => ∫ a, f (z.1, a) ∂μ := by
  have hg : Integrable (fun z : S × A => ∫ a, f (z.1, a) ∂μ) (ρ.prod μ) :=
    hf.integral_prod_left.comp_fst μ
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf
    (fun _ _ _ => hg.integrableOn)
  · intro D hD _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hD
    rw [setIntegral_prod_preimage_fst ρ μ hg,
      setIntegral_prod_preimage_fst ρ μ hf]
    simp
  · have hfm' : StronglyMeasurable (Function.uncurry (fun s a => f (s, a))) := by
      simpa only [Function.uncurry_def] using hfm
    exact (hfm'.integral_prod_right.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

theorem condIndepFun_latent_product
    {S A B C D : Type*} [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace S] [StandardBorelSpace A] [StandardBorelSpace B]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap (Prod.fst : S × (A × B) → S)) measurable_fst.comap_le
      (fun z : S × (A × B) => F (z.1, z.2.1))
      (fun z : S × (A × B) => G (z.1, z.2.2)) (ρ.prod (μ.prod ν)) := by
  classical
  have hFm : Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) := by fun_prop
  have hGm : Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) := by fun_prop
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hFm hGm]
  intro U V hU hV
  let E : Set (S × (A × B)) := (fun z => F (z.1, z.2.1)) ⁻¹' U
  let H : Set (S × (A × B)) := (fun z => G (z.1, z.2.2)) ⁻¹' V
  have hE : MeasurableSet E := hU.preimage hFm
  have hH : MeasurableSet H := hV.preimage hGm
  have hcE := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hE).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hE)
  have hcH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hH).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hH)
  have hcEH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator (hE.inter hH)).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  filter_upwards [hcE, hcH, hcEH] with z hzE hzH hzEH
  change ((ρ.prod (μ.prod ν))[(E ∩ H).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzEH, hzE, hzH]
  have hprod : (fun ab : A × B => (E ∩ H).indicator (fun _ => (1 : ℝ)) (z.1, ab)) =
      fun ab => (if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0) *
        (if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0) := by
    funext ab
    by_cases hfa : F (z.1, ab.1) ∈ U <;> by_cases hgb : G (z.1, ab.2) ∈ V <;>
      simp [E, H, hfa, hgb]
  rw [hprod, integral_prod_mul
    (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)
    (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
  have hleft : (∫ ab : A × B, E.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ a, if F (z.1, a) ∈ U then (1 : ℝ) else 0 ∂μ := by
    change (∫ ab : A × B, if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_fst (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)]
    simp
  have hright : (∫ ab : A × B, H.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ b, if G (z.1, b) ∈ V then (1 : ℝ) else 0 ∂ν := by
    change (∫ ab : A × B, if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_snd (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
    simp
  rw [hleft, hright]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_BalancedLatentMean
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

private theorem integrable_of_unit_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact (hb x).2)

theorem integral_binary_channel_le_two_integral
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (ν : Measure A) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) (a : IsingSpin) :
    (∫ r, F (a, r) ∂ν) ≤
      2 * ∫ z : S × A, F (b z.1, z.2) ∂ρ.prod ν := by
  let : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
  let E : Set S := {s | b s = a}
  let q : S → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E := measurableSet_eq_fun hb measurable_const
  have hq : Measurable q := measurable_const.indicator hE
  have hleft : Measurable (fun z : S × A => q z.1 * F (a, z.2)) :=
    (hq.comp measurable_fst).mul (hF.comp (measurable_const.prodMk measurable_snd))
  have hright : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hleftbound : ∀ z : S × A,
      0 ≤ q z.1 * F (a, z.2) ∧ q z.1 * F (a, z.2) ≤ 1 := by
    intro z
    by_cases hz : b z.1 = a
    · simpa [q, E, hz] using hbound (a, z.2)
    · simp [q, E, hz]
  have hmono := integral_mono
    (integrable_of_unit_bounds (ρ.prod ν) hleft hleftbound)
    (integrable_of_unit_bounds (ρ.prod ν) hright (fun z => hbound (b z.1, z.2)))
    (show ∀ z : S × A, q z.1 * F (a, z.2) ≤ F (b z.1, z.2) from by
      intro z
      by_cases hz : b z.1 = a
      · simp [q, E, hz]
      · simpa [q, E, hz] using (hbound (b z.1, z.2)).1)
  have hmass : (∫ s, q s ∂ρ) = (1 / 2 : ℝ) := by
    rw [show q = E.indicator (fun _ => 1) from rfl, integral_indicator_const (1 : ℝ) hE]
    simp only [smul_eq_mul, mul_one, Measure.real, E, hfair]
    norm_num
  rw [integral_prod_mul q (fun r => F (a, r)), hmass] at hmono
  linarith

theorem condExp_binary_channel_le_two_integral
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (ν : Measure A) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂ρ.prod ν,
      ((ρ.prod ν)[(fun z : S × A => F (b z.1, z.2)) | mS.comap Prod.fst]) z ≤
        2 * ∫ w : S × A, F (b w.1, w.2) ∂ρ.prod ν := by
  have hm : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hi := integrable_of_unit_bounds (ρ.prod ν) hm (fun z => hbound (b z.1, z.2))
  filter_upwards [condExp_prod_fst ρ ν hm.stronglyMeasurable hi] with z hz
  rw [hz]
  exact integral_binary_channel_le_two_integral ρ ν b hb hfair F hF hbound (b z.1)

theorem condExp_binary_channel_comp_le_two_integral
    {Ω S A : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S] [MeasurableSpace A]
    (μ : Measure Ω) (ρ : Measure S) (ν : Measure A)
    [IsFiniteMeasure μ] [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (e : Ω → S × A) (he : MeasurePreserving e μ (ρ.prod ν))
    (b : S → IsingSpin) (hb : Measurable b)
    (hfair : ∀ a : IsingSpin, ρ {s | b s = a} = (1 / 2 : ℝ≥0∞))
    (F : IsingSpin × A → ℝ) (hF : Measurable F)
    (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ ω ∂μ,
      (μ[(fun ω => F (b (e ω).1, (e ω).2)) |
        mS.comap (fun ω => (e ω).1)]) ω ≤
          2 * ∫ x, F (b (e x).1, (e x).2) ∂μ := by
  have hm : Measurable (fun z : S × A => F (b z.1, z.2)) :=
    hF.comp ((hb.comp measurable_fst).prodMk measurable_snd)
  have hi := integrable_of_unit_bounds (ρ.prod ν) hm (fun z => hbound (b z.1, z.2))
  have hpull := condExp_comp_measurePreserving μ (ρ.prod ν) e he
    (mS.comap Prod.fst) measurable_fst.comap_le hi
  have hboundpull := he.quasiMeasurePreserving.ae
    (condExp_binary_channel_le_two_integral ρ ν b hb hfair F hF hbound)
  have hint : (∫ x, F (b (e x).1, (e x).2) ∂μ) =
      ∫ z : S × A, F (b z.1, z.2) ∂ρ.prod ν := by
    rw [← he.map_eq]
    exact (integral_map he.measurable.aemeasurable
      (hm.aestronglyMeasurable)).symm
  rw [hint]
  filter_upwards [hpull, hboundpull] with ω hω hωb
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hω.trans_le hωb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_DiscreteConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace Problem367

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSingletonClass A] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem condExp_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap S inferInstance] =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => ∫ ω, f ω ∂μ[|S ⁻¹' {a}] := by
  let s := S ⁻¹' {a}
  have hs : MeasurableSet s := hS (measurableSet_singleton a)
  have hs' : MeasurableSet[MeasurableSpace.comap S inferInstance] s :=
    ⟨{a}, measurableSet_singleton a, rfl⟩
  by_cases hμs : μ s = 0
  · rw [show S ⁻¹' {a} = s from rfl, Measure.restrict_eq_zero.2 hμs]
    rfl
  have havg : (∫ ω, (∫ x, f x ∂μ[|s]) ∂μ.restrict s) =
      ∫ ω, f ω ∂μ.restrict s := by
    rw [integral_const, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr
      ⟨hμs, measure_ne_top _ _⟩), one_mul]
  refine (condExp_restrict_ae_eq_restrict hS.comap_le hs' hf).symm.trans ?_
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hS.comap_le hf.restrict
  · intro t _ _
    exact (integrable_const _).integrableOn
  · rintro t ⟨u, hu, rfl⟩ _
    rw [Measure.restrict_restrict (hS hu)]
    by_cases ha : a ∈ u
    · have heq : S ⁻¹' u ∩ s = s := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨And.right, fun h => ⟨h ▸ ha, h⟩⟩
      rw [heq]
      exact havg
    · have heq : S ⁻¹' u ∩ s = ∅ := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro h hEq
        exact ha (hEq ▸ h)
      simp [heq]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem condExp_indicator_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {t : Set Ω} (ht : MeasurableSet t) :
    μ⟦t | MeasurableSpace.comap S inferInstance⟧ =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => μ[|S ⁻¹' {a}].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_comap_eq_cond_on_fiber hS a ((integrable_const (1 : ℝ)).indicator ht)

theorem indepFun_cond_fiber_of_condIndepFun [StandardBorelSpace Ω]
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    {S : Ω → A} {X : Ω → B} {Y : Ω → C}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hXY : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X Y μ)
    (a : A) : IndepFun X Y μ[|S ⁻¹' {a}] := by
  by_cases hμa : μ (S ⁻¹' {a}) = 0
  · rw [cond_eq_zero_of_meas_eq_zero hμa]
    simp [indepFun_iff_measure_inter_preimage_eq_mul]
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hcond := (condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mp hXY s t hs ht
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a ((hX hs).inter (hY ht))
  have hfirst := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hX hs)
  have hsecond := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hY ht)
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (X ⁻¹' s ∩ Y ⁻¹' t) =
        μ[|S ⁻¹' {a}].real (X ⁻¹' s) * μ[|S ⁻¹' {a}].real (Y ⁻¹' t) := by
    filter_upwards [hcond', hleft, hfirst, hsecond] with ω h h₁ h₂ h₃
    simpa only [h₁, h₂, h₃] using h
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_mul] using hω

theorem iIndepFun_cond_fiber_of_iCondIndepFun [StandardBorelSpace Ω]
    {ι : Type*} {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {S : Ω → A} {X : ∀ i, Ω → B i}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i))
    (hXI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X μ)
    (a : A) (hμa : μ (S ⁻¹' {a}) ≠ 0) : iIndepFun X μ[|S ⁻¹' {a}] := by
  classical
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro I sets hsets
  have hcond := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB X hX).mp hXI I hsets
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hmeas : MeasurableSet (⋂ i ∈ I, X i ⁻¹' sets i) :=
    Finset.measurableSet_biInter I (fun i hi => hX i (hsets i hi))
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a hmeas
  have heach : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), ∀ i ∈ I,
      (μ⟦X i ⁻¹' sets i | MeasurableSpace.comap S inferInstance⟧) ω =
        μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    apply (Finset.eventually_all I).mpr
    intro i hi
    exact condExp_indicator_comap_eq_cond_on_fiber hS a (hX i (hsets i hi))
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (⋂ i ∈ I, X i ⁻¹' sets i) =
        ∏ i ∈ I, μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    filter_upwards [hcond', hleft, heach] with ω h h₁ h₂
    rw [h₁] at h
    simp only [Finset.prod_apply] at h
    exact h.trans (Finset.prod_congr rfl h₂)
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top (fun i hi => measure_ne_top _ _))).mp
  simpa only [measureReal_def, ENNReal.toReal_prod] using hω

theorem condIndepFun_iff_indepFun_cond_fibers [StandardBorelSpace Ω] [Countable A]
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    {S : Ω → A} {X : Ω → B} {Y : Ω → C}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y) :
    CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X Y μ ↔
      ∀ a : A, μ (S ⁻¹' {a}) ≠ 0 → IndepFun X Y μ[|S ⁻¹' {a}] := by
  constructor
  · intro h a _
    exact indepFun_cond_fiber_of_condIndepFun hS hX hY h a
  · intro h
    apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mpr
    intro s t hs ht
    have hOn (a : A) : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
        (μ⟦X ⁻¹' s ∩ Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω =
          (μ⟦X ⁻¹' s | MeasurableSpace.comap S inferInstance⟧) ω *
            (μ⟦Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω := by
      by_cases hμa : μ (S ⁻¹' {a}) = 0
      · rw [Measure.restrict_eq_zero.mpr hμa]
        simp
      have hprod := (h a hμa).measure_inter_preimage_eq_mul s t hs ht
      have hreal := congrArg ENNReal.toReal hprod
      simp only [ENNReal.toReal_mul] at hreal
      filter_upwards
        [condExp_indicator_comap_eq_cond_on_fiber hS a ((hX hs).inter (hY ht)),
         condExp_indicator_comap_eq_cond_on_fiber hS a (hX hs),
         condExp_indicator_comap_eq_cond_on_fiber hS a (hY ht)] with ω h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      exact hreal
    have hAll : ∀ᵐ ω ∂μ, ∀ a : A, ω ∈ S ⁻¹' {a} →
        (μ⟦X ⁻¹' s ∩ Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω =
          (μ⟦X ⁻¹' s | MeasurableSpace.comap S inferInstance⟧) ω *
            (μ⟦Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω := by
      apply ae_all_iff.mpr
      intro a
      exact (ae_restrict_iff' (hS (measurableSet_singleton a))).mp (hOn a)
    filter_upwards [hAll] with ω hω
    exact hω (S ω) rfl

omit [IsFiniteMeasure μ] in

theorem ae_of_ae_restrict_fibers [Countable A] {S : Ω → A} (hS : Measurable S)
    {p : Ω → Prop} (h : ∀ a : A, ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), p ω) :
    ∀ᵐ ω ∂μ, p ω := by
  have hAll : ∀ᵐ ω ∂μ, ∀ a : A, ω ∈ S ⁻¹' {a} → p ω := by
    apply ae_all_iff.mpr
    intro a
    exact (ae_restrict_iff' (hS (measurableSet_singleton a))).mp (h a)
  filter_upwards [hAll] with ω hω
  exact hω (S ω) rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfinitePiPair
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

variable {I A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem infinitePi_map_pair_arrays
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      (fun p : (s → A) × (s → B) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_arrowProdEquivProdArrow A B s
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

theorem infinitePi_map_split_pairs
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (μ i).prod (ν i))).map
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) =
      (Measure.infinitePi μ).prod (Measure.infinitePi ν) := by
  rw [← infinitePi_map_pair_arrays μ ν,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) ∘
        (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) = id := rfl
  rw [hcomp, Measure.map_id]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_DependentInfinitePiPair
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace Problem367

variable {I : Type*} {A B : I → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

theorem measurePreserving_dependentPiPairEquiv [Fintype I]
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (dependentPiPairEquiv (A := A) (B := B))
      (Measure.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := dependentPiPairEquiv.measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
        (FiniteSpanningSetsIn.pi fun i => (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi fun i =>
          (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi fun i =>
          (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      have heq : dependentPiPairEquiv ⁻¹' (univ.pi s ×ˢ univ.pi t) =
          univ.pi (fun i => s i ×ˢ t i) := by
        ext x
        simp [dependentPiPairEquiv, mem_pi, forall_and]
      rw [heq]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

theorem infinitePi_map_pair_dependent_arrays
    (μ : ∀ i, Measure (A i)) (ν : ∀ i, Measure (B i))
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (∀ i, A i) × (∀ i, B i) => fun i => (p.1 i, p.2 i)) =
      (fun p : (∀ i : s, A i) × (∀ i : s, B i) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_dependentPiPairEquiv
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Cardinality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

private lemma mem_inducedEdges_8911 {d : ℕ} (D : Finset (TreeVertex d))
    (u v : TreeVertex d) :
    (u, v) ∈ inducedEdges D ↔
      (u ∈ D ∧ v ∈ D) ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  rw [inducedEdges, Finset.mem_filter]
  exact and_congr Finset.mem_product Iff.rfl

lemma inducedEdges_snd_injOn {d : ℕ} (D : Finset (TreeVertex d)) :
    Set.InjOn Prod.snd (↑(inducedEdges D) : Set (TreeVertex d × TreeVertex d)) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
  have hab' : (a ∈ D ∧ b ∈ D) ∧ treeAdj a b ∧ a.1.length < b.1.length := by
    exact (mem_inducedEdges_8911 D a b).mp hab
  have hce' : (c ∈ D ∧ e ∈ D) ∧ treeAdj c e ∧ c.1.length < e.1.length := by
    exact (mem_inducedEdges_8911 D c e).mp hce
  change b = e at heq
  subst e
  exact Prod.ext (treeAdj_lower_unique hab'.2.1 hce'.2.1 hab'.2.2 hce'.2.2) rfl

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma fairSpin_neg_preimage : fairSpin ⁻¹' {IsingSpin.neg} = Set.Iic (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin]

lemma fairSpin_pos_preimage : fairSpin ⁻¹' {IsingSpin.pos} = Set.Ioi (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin, not_le]

lemma fairSpin_neg_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.neg}) = 1 / 2 := by
  rw [fairSpin_neg_preimage, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, by linarith⟩
  rw [h, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_pos_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.pos}) = 1 / 2 := by
  rw [fairSpin_pos_preimage, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, by linarith, h1⟩
  rw [h, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_mass (a : IsingSpin) : uniform01 (fairSpin ⁻¹' {a}) = 1 / 2 := by
  cases a
  · exact fairSpin_neg_mass
  · exact fairSpin_pos_mass

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.rootedBroadcastMeasurableSingletonSpin
lemma spinMul_comm (a b : IsingSpin) : spinMul a b = spinMul b a := by
  cases a <;> cases b <;> rfl
lemma spinMul_assoc (a b c : IsingSpin) : spinMul (spinMul a b) c = spinMul a (spinMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] lemma spinMul_cancel (a b : IsingSpin) : spinMul a (spinMul a b) = b := by
  rw [← spinMul_assoc, spinMul_self, pos_spinMul]

lemma biasedSpin_pos_mass {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.pos}) = ENNReal.ofReal p := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.pos} = Set.Iic p := by
    ext u
    simp [biasedSpin]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hu,h0,_⟩ => ⟨h0,hu⟩, fun ⟨h0,hu⟩ => ⟨hu,h0,hu.trans hp1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

lemma biasedSpin_neg_mass {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.neg}) = ENNReal.ofReal (1-p) := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.neg} = Set.Ioi p := by
    ext u
    simp [biasedSpin, not_le]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨hu,_,h1⟩ => ⟨hu,h1⟩, fun ⟨hu,h1⟩ => ⟨hu,hp0.trans hu.le,h1⟩⟩
  rw [h, Real.volume_Ioc]

lemma ofNoise_root {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    ofNoise noise ⟨[], List.isChain_nil⟩ = noise ⟨[], List.isChain_nil⟩ := by
  rw [ofNoise]
  simp

@[simp] lemma noiseFromSpins_ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    noiseFromSpins (ofNoise noise) = noise := by
  funext v
  by_cases hv : v.val = []
  · rw [noiseFromSpins, ite_eq_left hv, ofNoise]
    simp [hv]
  · rw [noiseFromSpins, ite_eq_right hv, ofNoise_nonroot noise v hv]
    rw [spinMul_assoc, spinMul_self, spinMul_pos]

@[simp] lemma ofNoise_noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) :
    ofNoise (noiseFromSpins x) = x := by
  funext v
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise (noiseFromSpins x) v = x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · rw [ofNoise]
        simp [hnil, noiseFromSpins]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot _ v hnil, ih _ hlt (parent v) rfl,
          noiseFromSpins, ite_eq_right hnil, spinMul_assoc, spinMul_self, spinMul_pos]
  exact h _ v rfl

lemma edgeNoise_mass {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (a : IsingSpin) :
    uniform01 ((edgeNoise theta) ⁻¹' {a}) =
      ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2) := by
  have hp0 : 0 ≤ (1 + theta) / 2 := by linarith
  have hp1 : (1 + theta) / 2 ≤ 1 := by linarith
  cases a
  · rw [edgeNoise, biasedSpin_neg_mass hp0 hp1, ite_eq_right (by decide : IsingSpin.neg ≠ IsingSpin.pos)]
    congr 1
    ring
  · rw [edgeNoise, biasedSpin_pos_mass hp0 hp1]
    rfl

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SpinEncoding
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma spinAgreementCode_comm (a b : IsingSpin) :
    spinAgreementCode a b = spinAgreementCode b a := by
  cases a <;> cases b <;> rfl

lemma ConnectedFinset.spin_eq_on_iff_root_agreements {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (σ τ : TreeVertex d → IsingSpin) :
    (∀ v ∈ D, σ v = τ v) ↔
      σ r = τ r ∧ ∀ e ∈ inducedEdges D,
        spinAgreementCode (σ e.1) (σ e.2) =
          spinAgreementCode (τ e.1) (τ e.2) := by
  classical
  constructor
  · intro h
    refine ⟨h r hr, ?_⟩
    intro e he
    have heD := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    rw [h e.1 heD.1, h e.2 heD.2]
  · rintro ⟨hroot, hedges⟩
    have step {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D)
        (hadj : treeAdj u v) (heq : σ u = τ u) : σ v = τ v := by
      have hcode : spinAgreementCode (σ u) (σ v) =
          spinAgreementCode (τ u) (τ v) := by
        rcases treeAdj_length hadj with hlen | hlen
        · apply hedges (u, v)
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj, by change u.1.length < v.1.length; omega⟩
        · have his : (v, u) ∈ inducedEdges D := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hv, hu⟩, Or.symm hadj, by change v.1.length < u.1.length; omega⟩
          simpa only [spinAgreementCode_comm (σ v) (σ u),
            spinAgreementCode_comm (τ v) (τ u)] using hedges (v, u) his
      rw [heq] at hcode
      exact spinAgreementCode_injective_right (τ u) hcode
    intro v hv
    have hpath := hD.2 r hr v hv
    induction hpath with
    | refl => exact hroot
    | tail hpath hadj ih => exact step hadj.1 hadj.2.1 hadj.2.2 (ih hadj.1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcastLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

lemma eq_root_iff {d : ℕ} (v : TreeVertex d) : v = root d ↔ v.val = [] := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact h

lemma ofNoise_root_decomposition {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v : TreeVertex d) :
    ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have hvroot : v = root d := (eq_root_iff v).mpr hnil
        subst v
        simp [root, ofNoise_root, eraseRootNoise]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise v hnil, ofNoise_nonroot (eraseRootNoise noise) v hnil,
          eraseRootNoise, ite_eq_right hnil, ih _ hlt (parent v) rfl]
        rw [← spinMul_assoc, spinMul_comm (noise v) (noise (root d)), spinMul_assoc]
  exact h _ v rfl

lemma measurable_nonrootNoise (d : ℕ) (theta : ℝ) : Measurable (@nonrootNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = root d
  · simpa only [nonrootNoise, dite_eq_left hv] using
      (measurable_const : Measurable (fun _ : NonrootVertex d → ℝ => IsingSpin.pos))
  · simpa only [nonrootNoise, dite_eq_right hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp (measurable_pi_apply (X := fun _ : NonrootVertex d => ℝ) ⟨v, hv⟩)

lemma measurable_rootlessFactor (d : ℕ) (theta : ℝ) : Measurable (@rootlessFactor d theta) :=
  (measurable_ofNoise d).comp (measurable_nonrootNoise d theta)

lemma factor_root_decomposition {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v : TreeVertex d) :
    factor theta U v = spinMul (fairSpin (U (root d)))
      (rootlessFactor theta (fun w : NonrootVertex d => U w.val) v) := by
  rw [factor, ofNoise_root_decomposition]
  have heq : eraseRootNoise (inputNoise theta U) =
      nonrootNoise theta (fun w : NonrootVertex d => U w.val) := by
    funext w
    by_cases hw : w = root d
    · subst w
      simp [eraseRootNoise, nonrootNoise]
    · have hnil : w.val ≠ [] := fun h => hw ((eq_root_iff w).mpr h)
      simp [eraseRootNoise, inputNoise, nonrootNoise, hw, hnil]
  rw [heq]
  rfl

lemma factor_edge_agreement {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    {u v : TreeVertex d} (huv : treeAdj u v) (hlt : u.val.length < v.val.length) :
    spinAgreementCode (factor theta U u) (factor theta U v) = edgeNoise theta (U v) := by
  have hp : parent v = u := treeAdj_parent_of_length_lt huv hlt
  have hnil : v.val ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlt
    omega
  change spinMul (factor theta U u) (factor theta U v) = _
  change spinMul (ofNoise (inputNoise theta U) u) (ofNoise (inputNoise theta U) v) = _
  rw [ofNoise_nonroot _ v hnil, hp]
  simp only [inputNoise, ite_eq_right hnil]
  rw [spinMul_comm (edgeNoise theta (U v)), spinMul_cancel]

lemma factor_cylinder_event {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (eta : TreeVertex d → IsingSpin) :
    {U : TreeVertex d → ℝ | ∀ v ∈ D, factor theta U v = eta v} =
      {U | factor theta U r = eta r ∧ ∀ e ∈ inducedEdges D,
        edgeNoise theta (U e.2) = spinAgreementCode (eta e.1) (eta e.2)} := by
  classical
  ext U
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hD.spin_eq_on_iff_root_agreements hr]
  apply and_congr_right
  intro hroot
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have he' := (Finset.mem_filter.mp he).2
  rw [factor_edge_agreement theta U he'.1 he'.2]

lemma edgeVertex_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (edgeVertex D) := by
  intro a b hab
  apply Subtype.ext
  apply inducedEdges_snd_injOn D a.property b.property
  exact congrArg Subtype.val hab

lemma nonroot_edge_event_mass {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))
      {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
        spinAgreementCode (eta e.val.1) (eta e.val.2)} =
      ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  classical
  let A : Set ((e : inducedEdges D) → ℝ) := Set.pi Set.univ
    (fun e => edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)})
  have hA : MeasurableSet A := MeasurableSet.univ_pi
    (fun e => (measurable_edgeNoise theta) (measurableSet_singleton _))
  have hm : Measurable (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e)) := by
    fun_prop
  calc
    _ = (Measure.map (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e))
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) A := by
      rw [Measure.map_apply hm hA]
      congr 1
      ext Y
      simp [A, Set.mem_pi]
    _ = (Measure.infinitePi (fun _ : inducedEdges D => uniform01)) A := by
      rw [Measure.map_infinitePi_infinitePi_of_inj (edgeVertex_injective D)]
    _ = ∏ e : inducedEdges D, uniform01
        (edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)}) := by
      simpa only [A, Finset.coe_univ] using
        (Measure.infinitePi_pi (fun _ : inducedEdges D => uniform01)
          (s := Finset.univ) (fun e _ => (measurable_edgeNoise theta)
            (measurableSet_singleton (spinAgreementCode (eta e.val.1) (eta e.val.2)))))
    _ = _ := by
      simp only [edgeNoise_mass h0 h1, spinAgreementCode_eq_pos_iff]
      exact Finset.prod_coe_sort (inducedEdges D) (fun e : TreeVertex d × TreeVertex d =>
        ENNReal.ofReal ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

lemma freeCylinderWeight_eq_edge_product {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · norm_num [ENNReal.ofReal_div_of_pos]
  · intro e he
    split_ifs <;> linarith

lemma hasFreeIsingLaw_of_root_nonroot_joint {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (hjoint : ∀ r : TreeVertex d,
      (labelMeasure d).map (fun U => (factor theta U r, fun w : NonrootVertex d => U w.val)) =
        (uniform01.map fairSpin).prod (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) :
    HasFreeIsingLaw theta ((labelMeasure d).map (factor theta)) := by
  classical
  intro D hD eta
  obtain ⟨r, hr⟩ := hD.1
  let A : Set (NonrootVertex d → ℝ) :=
    {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
      spinAgreementCode (eta e.val.1) (eta e.val.2)}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact ((measurable_edgeNoise theta).comp (measurable_pi_apply (edgeVertex D e)))
      (measurableSet_singleton _)
  have hS : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U r, fun w : NonrootVertex d => U w.val)) := by
    exact ((measurable_pi_apply r).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun w => measurable_pi_apply w.val))
  rw [Measure.map_apply (measurable_factor d theta) hS]
  change (labelMeasure d) {U | ∀ v ∈ D, factor theta U v = eta v} = _
  rw [factor_cylinder_event theta D hD r hr eta]
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U r, fun w : NonrootVertex d => U w.val))) ({eta r} ×ˢ A) := by
      rw [Measure.map_apply hm ((measurableSet_singleton _).prod hA)]
      congr 1
      ext U
      simp [A, Set.mem_prod, edgeVertex]
    _ = ((uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) ({eta r} ×ˢ A) := by
      rw [hjoint r]
    _ = (uniform01.map fairSpin) {eta r} *
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A :=
      Measure.prod_prod _ _
    _ = (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
      rw [Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass]
      rw [show (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A = _ from
        nonroot_edge_event_mass h0 h1 D eta]
    _ = freeCylinderWeight theta D eta := (freeCylinderWeight_eq_edge_product h0 h1 D eta).symm

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

lemma ofNoise_congr_prefix {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (v : TreeVertex d)
    (heq : ∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      (∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv heq
      by_cases hnil : v.val = []
      · calc
          ofNoise noise₁ v = noise₁ v := by rw [ofNoise]; simp [hnil]
          _ = noise₂ v := heq v (List.prefix_refl _)
          _ = ofNoise noise₂ v := by rw [ofNoise]; simp [hnil]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        apply congrArg₂ spinMul (heq v (List.prefix_refl _))
        apply ih _ hlt (parent v) rfl
        intro w hw
        exact heq w (hw.trans (List.dropLast_prefix v.val))
  exact h _ v rfl heq

lemma factor_congr_prefix {d : ℕ} (theta : ℝ) (U V : TreeVertex d → ℝ)
    (v : TreeVertex d) (heq : ∀ w : TreeVertex d, w.val <+: v.val → U w = V w) :
    factor theta U v = factor theta V v := by
  apply ofNoise_congr_prefix
  intro w hw
  simp only [inputNoise, heq w hw]

lemma prefix_in_branch_or_root {d : ℕ} (c : Fin d)
    {u v : TreeVertex d} (hv : [c] <+: v.val) (huv : u.val <+: v.val) :
    u.val = [] ∨ [c] <+: u.val := by
  by_cases hu : u.val = []
  · exact Or.inl hu
  · right
    apply List.prefix_of_prefix_length_le hv huv
    have : 0 < u.val.length := List.length_pos_iff.mpr hu
    simpa only [List.length_singleton] using Nat.succ_le_of_lt this

lemma measurable_branchNoise {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (fun p : IsingSpin × (BranchVertex c → ℝ) => branchNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.val = []
  · simpa only [branchNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst : IsingSpin × (BranchVertex c → ℝ) → IsingSpin))
  · by_cases hv : [c] <+: v.val
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : BranchVertex c => ℝ) ⟨v,hv⟩).comp measurable_snd)
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ : IsingSpin × (BranchVertex c → ℝ) => IsingSpin.pos))

lemma measurable_branchFactor {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (branchFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.val).comp (measurable_branchNoise theta c)

lemma factor_branch_representation {d : ℕ} (theta : ℝ) (c : Fin d)
    (U : TreeVertex d → ℝ) :
    (fun v : BranchVertex c => factor theta U v.val) =
      branchFactor theta c (fairSpin (U (root d)), fun v : BranchVertex c => U v.val) := by
  funext v
  apply ofNoise_congr_prefix
  intro w hw
  rcases prefix_in_branch_or_root c v.property hw with hnil | hbranch
  · have heq : w = root d := (eq_root_iff w).mpr hnil
    subst w
    simp [inputNoise, branchNoise]
  · have hnil : w.val ≠ [] := by
      intro heq
      rw [heq] at hbranch
      have hl := hbranch.length_le
      simp at hl
    simp [inputNoise, branchNoise, hnil, hbranch]

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastConeLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem ofNoise_congr_cone {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (c : TreeVertex d) (hbase : ofNoise noise₁ c = ofNoise noise₂ c)
    (hedge : ∀ w : TreeVertex d, c.1 <+: w.1 → w ≠ c → noise₁ w = noise₂ w)
    (v : TreeVertex d) (hcv : c.1 <+: v.1) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → c.1 <+: v.1 →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv hcv
      by_cases hvc : v = c
      · simpa only [hvc] using hbase
      · have hlt : c.1.length < v.1.length := by
          have hle := hcv.length_le
          have hne : c.1.length ≠ v.1.length := by
            intro heq
            exact hvc (Subtype.ext (hcv.eq_of_length heq).symm)
          omega
        have hnil : v.1 ≠ [] := by
          intro hh
          simp only [hh, List.length_nil] at hlt
          omega
        have hcp : c.1 <+: (parent v).1 := by
          apply List.prefix_of_prefix_length_le hcv (List.dropLast_prefix v.1)
          change c.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        have hp : (parent v).1.length < n := by
          change (parentVertex v).1.length < n
          rw [parentVertex_length]
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        exact congrArg₂ spinMul (hedge v hcv hvc) (ih _ hp _ rfl hcp)
  exact h _ v rfl hcv

theorem measurable_coneNoise {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (fun p : IsingSpin × (StrictDescendantVertex c → ℝ) =>
      coneNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.1 = []
  · simpa only [coneNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst :
        IsingSpin × (StrictDescendantVertex c → ℝ) → IsingSpin))
  · by_cases hv : c.1 <+: v.1 ∧ v ≠ c
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : StrictDescendantVertex c => ℝ)
            ⟨v, hv⟩).comp measurable_snd)
    · simpa only [coneNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ :
          IsingSpin × (StrictDescendantVertex c → ℝ) => IsingSpin.pos))

theorem ofNoise_coneNoise_at_root {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (s : IsingSpin) (Y : StrictDescendantVertex c → ℝ) :
    ofNoise (coneNoise theta c s Y) c = s := by
  calc
    ofNoise (coneNoise theta c s Y) c =
        ofNoise (noiseFromSpins (fun _ : TreeVertex d => s)) c := by
      apply ofNoise_congr_prefix
      intro w hw
      have hnot : ¬ (c.1 <+: w.1 ∧ w ≠ c) := by
        rintro ⟨hcw, hne⟩
        exact hne (Subtype.ext (hw.eq_of_length_le hcw.length_le))
      by_cases hnil : w.1 = [] <;>
        simp [coneNoise, noiseFromSpins, hnil, hnot]
    _ = s := congrFun (ofNoise_noiseFromSpins (fun _ : TreeVertex d => s)) c

theorem measurable_coneFactor {d : ℕ} (theta : ℝ) (c : TreeVertex d) :
    Measurable (coneFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.1).comp (measurable_coneNoise theta c)

theorem factor_cone_representation {d : ℕ} (theta : ℝ) (c : TreeVertex d)
    (U : TreeVertex d → ℝ) :
    (fun v : DescendantVertex c => factor theta U v.1) =
      coneFactor theta c (factor theta U c,
        fun w : StrictDescendantVertex c => U w.1) := by
  funext v
  apply ofNoise_congr_cone (inputNoise theta U) _ c
  · exact (ofNoise_coneNoise_at_root theta c (factor theta U c) _).symm
  · intro w hcw hne
    have hnil : w.1 ≠ [] := by
      intro hw
      have hc : c.1 = [] := by simpa only [hw, List.prefix_nil] using hcw
      exact hne (Subtype.ext (hw.trans hc.symm))
    simp [inputNoise, coneNoise, hnil, hcw, hne]
  · exact v.2

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FamilyConditionalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

alias ⟨_, iCondIndepFun_of_comp_measurePreserving⟩ :=
  iCondIndepFun_iff_comp_measurePreserving

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfiniteBlockIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory

section Unconditional

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : Measure Ω} {f : ∀ i, Ω → X i}

theorem indepFun_disjoint_blocks (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T) :
    IndepFun (fun ω (i : S) => f i ω) (fun ω (i : T) => f i ω) μ := by
  change Indep (MeasurableSpace.comap (fun ω (i : S) => f i ω) inferInstance)
    (MeasurableSpace.comap (fun ω (i : T) => f i ω) inferInstance) μ
  simp only [MeasurableSpace.comap_process_pi, iSup_subtype]
  exact indep_iSup_of_disjoint (fun i => (hm i).comap_le) hf hst

theorem indepFun_of_disjoint_blocks (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S T : Set ι) (hst : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : (∀ i : S, X i) → A) (G : (∀ i : T, X i) → B)
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun ω => F (fun i => f i ω))
      (fun ω => G (fun i => f i ω)) μ :=
  (indepFun_disjoint_blocks hf hm S T hst).comp hF hG

theorem indepFun_infinitePi_disjoint_blocks
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S T : Set ι) (hst : Disjoint S T)
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : (∀ i : S, X i) → A) (G : (∀ i : T, X i) → B)
    (hF : Measurable F) (hG : Measurable G) :
    IndepFun (fun U : ∀ i, X i => F (fun i => U i))
      (fun U : ∀ i, X i => G (fun i => U i)) (Measure.infinitePi ν) :=
  indepFun_of_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S T hst F G hF hG

theorem iIndepFun_disjoint_blocks {κ : Type*} (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S : κ → Set ι)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepFun (fun j ω (i : S j) => f i ω) μ := by
  have := hf.isProbabilityMeasure
  have : ∀ index, IsProbabilityMeasure (μ.map (f index)) :=
    fun i => Measure.isProbabilityMeasure_map (hm i).aemeasurable
  have hinj : Function.Injective (fun p : (j : κ) × S j => (p.2 : ι)) := by
    rintro ⟨i, u⟩ ⟨j, v⟩ huv
    change (u : ι) = (v : ι) at huv
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hS hne) u.property (huv.symm ▸ v.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext huv)
  have hgroup := hf.precomp hinj
  have hmap := hgroup.map_fun_eq_infinitePi_map (fun p => hm p.2)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  calc
    μ.map (fun ω j (i : S j) => f i ω) =
        (μ.map (fun ω (p : (j : κ) × S j) => f p.2 ω)).map
          (MeasurableEquiv.piCurry (fun j (i : S j) => X i)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.infinitePi (fun j =>
        Measure.infinitePi (fun i : S j => μ.map (f i))) := by
      rw [hmap]
      exact Measure.infinitePi_map_piCurry (fun (j : κ) (i : S j) => μ.map (f i))
    _ = Measure.infinitePi (fun j => μ.map (fun ω (i : S j) => f i ω)) := by
      congr 1
      funext j
      exact (hf.precomp (g := fun i : S j => (i : ι)) Subtype.val_injective
        |>.map_fun_eq_infinitePi_map (fun i : S j => hm (i : ι))).symm

theorem infinitePi_map_disjoint_family {κ : Type*}
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S : κ → Set ι) (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    (Measure.infinitePi ν).map (fun labels index => (S index).domRestrict labels) =
      Measure.infinitePi (fun j => Measure.infinitePi (fun i : S j => ν i)) := by
  have h := iIndepFun_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S hS (μ := Measure.infinitePi ν)
  change iIndepFun (fun index labels => (S index).domRestrict labels)
    (Measure.infinitePi ν) at h
  calc
    _ = Measure.infinitePi (fun index => (Measure.infinitePi ν).map (S index).domRestrict) :=
      h.map_fun_eq_infinitePi_map (by fun_prop)
    _ = _ := by
      congr 1
      funext j
      exact Measure.infinitePi_map_restrict' ν

end Unconditional

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentFamilyIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iCondIndepFun_latent_of_fiber_indep
    {ι S A : Type*} {B : ι → Type*}
    [mS : MeasurableSpace S] [MeasurableSpace A]
    [mB : ∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [StandardBorelSpace A]
    (ρ : Measure S) (μ : Measure A)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    (F : ∀ i, S × A → B i) (hF : ∀ i, Measurable (F i))
    (hind : ∀ s, iIndepFun (fun i a => F i (s, a)) μ) :
    iCondIndepFun (mS.comap (Prod.fst : S × A → S)) measurable_fst.comap_le
      F (ρ.prod μ) := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB F hF]
  intro I sets hsets
  let E : ι → Set (S × A) := fun i => F i ⁻¹' sets i
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi => (hsets i hi).preimage (hF i)
  have hEI : MeasurableSet (⋂ i ∈ I, E i) := by
    exact I.measurableSet_biInter hE
  have hcI := condExp_prod_fst ρ μ
    (measurable_const.indicator hEI).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hEI)
  have hc : ∀ i ∈ I,
      (ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
        fun z => ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ := by
    intro i hi
    exact condExp_prod_fst ρ μ
      (measurable_const.indicator (hE i hi)).stronglyMeasurable
      ((integrable_const (1 : ℝ)).indicator (hE i hi))
  have hcall := (Filter.eventually_all_finset I).2 hc
  filter_upwards [hcI, hcall] with z hzI hz
  change ((ρ.prod μ)[(⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzI]
  simp only [Finset.prod_apply]
  have hprod : (∏ i ∈ I,
      ((ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst]) z) =
      ∏ i ∈ I, ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ :=
    Finset.prod_congr rfl hz
  rw [hprod]
  let T : ι → Set A := fun i => (fun a => F i (z.1, a)) ⁻¹' sets i
  have hT : ∀ i ∈ I, MeasurableSet (T i) := by
    intro i hi
    exact (hsets i hi).preimage ((hF i).comp (measurable_const.prodMk measurable_id))
  have hTI : MeasurableSet (⋂ i ∈ I, T i) := I.measurableSet_biInter hT
  have hleft : (fun a => (⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) (z.1, a)) =
      (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) := by
    funext a
    simp only [Set.indicator, Set.mem_iInter, E, T, Set.mem_preimage]
  rw [hleft]
  have hmass : (∫ a, (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) a ∂μ) =
      μ.real (⋂ i ∈ I, T i) := by
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) hTI)
  rw [hmass]
  have hright : ∀ i ∈ I,
      (∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ) = μ.real (T i) := by
    intro i hi
    change (∫ a, (T i).indicator (fun _ => (1 : ℝ)) a ∂μ) = _
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) (hT i hi))
  rw [Finset.prod_congr rfl hright]
  unfold Measure.real
  rw [(hind z.1).measure_inter_preimage_eq_mul I hsets, ENNReal.toReal_prod]

theorem iCondIndepFun_latent_infinitePi
    {ι S : Type*} [Countable ι] {A B : ι → Type*}
    [mS : MeasurableSpace S] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [∀ i, StandardBorelSpace (A i)]
    (ρ : Measure S) (ν : ∀ i, Measure (A i))
    [IsFiniteMeasure ρ] [∀ i, IsProbabilityMeasure (ν i)]
    (F : ∀ i, S × A i → B i) (hF : ∀ i, Measurable (F i)) :
    iCondIndepFun (mS.comap (Prod.fst : S × (∀ i, A i) → S))
      measurable_fst.comap_le
      (fun i z => F i (z.1, z.2 i)) (ρ.prod (Measure.infinitePi ν)) := by
  apply iCondIndepFun_latent_of_fiber_indep ρ (Measure.infinitePi ν)
    (fun i z => F i (z.1, z.2 i))
  · intro i
    exact (hF i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · intro s
    exact iIndepFun_infinitePi (fun i =>
      (hF i).comp (measurable_const.prodMk measurable_id))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LabelDecomposition
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.LabelDecomposition

theorem indepFun_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    IndepFun (fun U : ι → A => U r)
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i)
      (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have hd : Disjoint ({r} : Set ι) {i | i ≠ r} := by simp
  have h := indep_iSup_of_disjoint hle hi hd
  change Indep (MeasurableSpace.comap (fun U : ι → A => U r) inferInstance)
    (MeasurableSpace.comap
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i) inferInstance)
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

theorem map_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    (Measure.infinitePi μ).map
      (fun U : ι → A => (U r, fun i : {i : ι // i ≠ r} => U i)) =
      (μ r).prod (Measure.infinitePi (fun i : {i : ι // i ≠ r} => μ i)) := by
  rw [(indepFun_coordinate_rest μ r).map_prod_eq_prod_map_map
    (measurable_pi_apply r).aemeasurable
      ((measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)).aemeasurable)]
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

theorem map_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01)) := by
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map _ = _
  have hrest : Measurable
      (fun U : TreeVertex d → ℝ => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_pi_apply r).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  calc
    _ = ((Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map
        (fun U => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v))).map
          (Prod.map fairSpin id) := by
      rw [Measure.map_map (measurable_fairSpin.prodMap measurable_id) hrest]
      rfl
    _ = _ := by
      rw [map_coordinate_rest,
        ← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]

end Problem367.LabelDecomposition

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchLabels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

namespace RootedBroadcast

lemma branch_disjoint {d : ℕ} {c e : Fin d} (hce : c ≠ e) :
    Disjoint {v : TreeVertex d | [c] <+: v.val} {v | [e] <+: v.val} := by
  apply Set.disjoint_left.mpr
  intro v hc he
  have hprefix : [c] <+: [e] := List.prefix_of_prefix_length_le hc he (by simp)
  have heq : [c] = [e] := hprefix.eq_of_length (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hce (by simpa only [List.singleton_inj] using heq)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_UniformTwist
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurePreserving_fiberTwist
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) μ μ) :
    MeasurePreserving (fun p : A × B => (twist p.2 p.1, p.2))
      (μ.prod ν) (μ.prod ν) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm),
    Measure.prod_apply_symm hs]
  apply lintegral_congr
  intro b
  change μ ((twist b) ⁻¹' ((fun a => (a, b)) ⁻¹' s)) =
    μ ((fun a => (a, b)) ⁻¹' s)
  exact (hpres b).measure_preimage ((hs.preimage measurable_prodMk_right).nullMeasurableSet)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Twist
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance localInst_ra6648c_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem measurePreserving_fairSpin_mul (b : IsingSpin) :
    MeasurePreserving (fun a => spinMul a b)
      (uniform01.map fairSpin) (uniform01.map fairSpin) := by
  have hm : Measurable (fun a => spinMul a b) := measurable_of_finite _
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hpre : (fun x => spinMul x b) ⁻¹' {a} = {spinMul a b} := by
    ext x
    cases x <;> cases a <;> cases b <;> simp [spinMul]
  rw [Measure.map_apply hm (measurableSet_singleton a), hpre,
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _),
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass,
    fairSpin_mass]

theorem measurePreserving_fairSpin_twist
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {f : Y → IsingSpin} (hf : Measurable f) :
    MeasurePreserving (fun p : IsingSpin × Y => (spinMul p.1 (f p.2), p.2))
      ((uniform01.map fairSpin).prod ν) ((uniform01.map fairSpin).prod ν) := by
  apply measurePreserving_fiberTwist (uniform01.map fairSpin) ν
    (fun y a => spinMul a (f y))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro y
    exact measurePreserving_fairSpin_mul (f y)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastJointLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem map_factor_rest (d : ℕ) (theta : ℝ) (v : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (factor theta U v, fun w : NonrootVertex d => U w.val)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) := by
  have hf : Measurable (fun Y : NonrootVertex d → ℝ => rootlessFactor theta Y v) :=
    (measurable_pi_apply v).comp (measurable_rootlessFactor d theta)
  have ht := measurePreserving_fairSpin_twist
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) hf
  have hj : Measurable (fun U : TreeVertex d → ℝ =>
      (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val)) :=
    (measurable_fairSpin.comp (measurable_pi_apply (root d))).prodMk
      (measurable_pi_iff.mpr (fun w => measurable_pi_apply w.val))
  calc
    _ = ((labelMeasure d).map
        (fun U => (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val))).map
          (fun p : IsingSpin × (NonrootVertex d → ℝ) =>
            (spinMul p.1 (rootlessFactor theta p.2 v), p.2)) := by
      rw [Measure.map_map ht.measurable hj]
      congr 1
      funext U
      exact Prod.ext (factor_root_decomposition theta U v) rfl
    _ = _ := by
      rw [LabelDecomposition.map_fairSpin_rest]
      exact ht.map_eq

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeIsingMeasure
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem freeIsingMeasure_hasFreeIsingLaw (d : ℕ) {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    HasFreeIsingLaw theta (freeIsingMeasure d theta) :=
  RootedBroadcast.hasFreeIsingLaw_of_root_nonroot_joint h0 h1
    (RootedBroadcast.map_factor_rest d theta)

theorem HasFreeIsingLaw.eq_freeIsingMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) : mu = freeIsingMeasure d theta :=
  hmu.unique (freeIsingMeasure_hasFreeIsingLaw d h0 h1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FreeIsingBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutLevelBranchIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

theorem strictDescendant_length_gt {d n : ℕ} (c : TreeShell d n)
    (v : StrictDescendantVertex c.1) : n < v.1.1.length := by
  have hle := v.2.1.length_le
  have hne : c.1.1.length ≠ v.1.1.length := by
    intro h
    exact v.2.2 (Subtype.ext (v.2.1.eq_of_length h).symm)
  rw [c.2] at hle hne
  omega

theorem cutLevel_descendants_disjoint {d n : ℕ} :
    Pairwise (fun c e : TreeShell d n =>
      Disjoint {v : TreeVertex d | c.1.1 <+: v.1}
        {v : TreeVertex d | e.1.1 <+: v.1}) := by
  intro c e hce
  apply Set.disjoint_left.mpr
  intro v hc he
  have hpre : c.1.1 <+: e.1.1 :=
    List.prefix_of_prefix_length_le hc he (by simp only [c.2, e.2, le_refl])
  exact hce (Subtype.ext (Subtype.ext (hpre.eq_of_length (c.2.trans e.2.symm))))

theorem cutLevel_strictDescendants_disjoint {d n : ℕ} :
    Pairwise (fun c e : TreeShell d n =>
      Disjoint {v : TreeVertex d | c.1.1 <+: v.1 ∧ v ≠ c.1}
        {v : TreeVertex d | e.1.1 <+: v.1 ∧ v ≠ e.1}) := by
  intro c e hce
  exact (cutLevel_descendants_disjoint hce).mono
    (fun _ h => h.1) (fun _ h => h.1)

theorem measurable_cutUpperExtension (d n : ℕ) :
    Measurable (@cutUpperExtension d n) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v.1.length ≤ n
  · simpa only [cutUpperExtension, dite_eq_left hv] using
      (measurable_pi_apply (X := fun _ : TreeBall d n => ℝ) ⟨v, hv⟩)
  · simpa only [cutUpperExtension, dite_eq_right hv] using
      (measurable_const : Measurable (fun _ : TreeBall d n → ℝ => (0 : ℝ)))

theorem cutSpins_upper_extension {d : ℕ} (theta : ℝ) (n : ℕ)
    (U : TreeVertex d → ℝ) :
    cutSpins theta n (cutUpperExtension (fun v : TreeBall d n => U v.1)) =
      cutSpins theta n U := by
  funext c
  apply factor_congr_prefix
  intro w hw
  have hlen : w.1.length ≤ n := hw.length_le.trans_eq c.2
  simp only [cutUpperExtension, dite_eq_left hlen]

theorem measurable_cutLabels (d n : ℕ) : Measurable (@cutLabels d n) := by
  unfold cutLabels
  fun_prop

theorem indepFun_cutSpins_cutLabels (d : ℕ) (theta : ℝ) (n : ℕ) :
    IndepFun (cutSpins theta n) (@cutLabels d n) (labelMeasure d) := by
  let F : (TreeBall d n → ℝ) → (TreeShell d n → IsingSpin) :=
    fun U => cutSpins theta n (cutUpperExtension U)
  let G : ({v : TreeVertex d // n < v.1.length} → ℝ) →
      ((c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ) :=
    fun U c v => U ⟨v.1, strictDescendant_length_gt c v⟩
  have hF : Measurable F :=
    (measurable_cutSpins d theta n).comp (measurable_cutUpperExtension d n)
  have hG : Measurable G := by fun_prop
  have hdisj : Disjoint {v : TreeVertex d | v.1.length ≤ n}
      {v : TreeVertex d | n < v.1.length} := by
    apply Set.disjoint_left.mpr
    intro v hle hlt
    exact (not_lt_of_ge (show v.1.length ≤ n from hle))
      (show n < v.1.length from hlt)
  have h := indepFun_infinitePi_disjoint_blocks (fun _ : TreeVertex d => uniform01)
    {v : TreeVertex d | v.1.length ≤ n} {v : TreeVertex d | n < v.1.length}
    hdisj F G hF hG
  have heq : (fun U : TreeVertex d → ℝ => F (fun v : TreeBall d n => U v.1)) =
      cutSpins theta n := by
    funext U
    exact cutSpins_upper_extension theta n U
  change IndepFun (fun U => F (fun v : TreeBall d n => U v.1))
    (@cutLabels d n) (labelMeasure d) at h
  rw [heq] at h
  exact h

local instance localInst_ra6648c_2 (d : ℕ) : IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
theorem map_cutSpins_cutLabels (d : ℕ) (theta : ℝ) (n : ℕ) :
    (labelMeasure d).map (fun U => (cutSpins theta n U, cutLabels U)) =
      ((labelMeasure d).map (cutSpins theta n)).prod
        (Measure.infinitePi (fun c : TreeShell d n =>
          Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01))) := by
  rw [(indepFun_cutSpins_cutLabels d theta n).map_prod_eq_prod_map_map
    (measurable_cutSpins d theta n).aemeasurable (measurable_cutLabels d n).aemeasurable]
  congr 1
  exact infinitePi_map_disjoint_family (fun _ : TreeVertex d => uniform01)
    (fun c : TreeShell d n => {v : TreeVertex d | c.1.1 <+: v.1 ∧ v ≠ c.1})
    cutLevel_strictDescendants_disjoint

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyCutLevelIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance noisyCutLevelMeasurableSingletonIsingSpin_ra6648c_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
attribute [local instance] OAI.Problem367.RootedBroadcast.noisyCutLevelIsProbabilityLabelMeasure
theorem map_cutSpins_cutLabels_noises {d : ℕ} {A : Type*}
    [MeasurableSpace A] (theta : ℝ) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    ((labelMeasure d).prod (Measure.infinitePi ν)).map
      (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
        (cutSpins theta n z.1, fun c : TreeShell d n =>
          (cutLabels z.1 c, fun v : DescendantVertex c.1 => z.2 v.1))) =
      ((labelMeasure d).map (cutSpins theta n)).prod
        (Measure.infinitePi (fun c : TreeShell d n =>
          (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
            (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))) := by
  let S := TreeShell d n → IsingSpin
  let R := (c : TreeShell d n) → StrictDescendantVertex c.1 → ℝ
  let N := (c : TreeShell d n) → DescendantVertex c.1 → A
  let rho := (labelMeasure d).map (cutSpins theta n)
  let muR := Measure.infinitePi (fun c : TreeShell d n =>
    Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01))
  let muN := Measure.infinitePi (fun c : TreeShell d n =>
    Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1))
  let muP := Measure.infinitePi (fun c : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))
  let f : (TreeVertex d → ℝ) → S × R := fun U => (cutSpins theta n U, cutLabels U)
  let g : (TreeVertex d → A) → N := fun W _ v => W v.1
  let p : R × N → ((c : TreeShell d n) →
      (StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A)) :=
    fun z c => (z.1 c, z.2 c)
  have hf : MeasurePreserving f (labelMeasure d) (rho.prod muR) :=
    ⟨(measurable_cutSpins d theta n).prodMk (measurable_cutLabels d n),
      map_cutSpins_cutLabels d theta n⟩
  have hg : MeasurePreserving g (Measure.infinitePi ν) muN := by
    refine ⟨by fun_prop, ?_⟩
    exact infinitePi_map_disjoint_family ν
      (fun c : TreeShell d n => {v : TreeVertex d | c.1.1 <+: v.1})
      cutLevel_descendants_disjoint
  have hp : MeasurePreserving p (muR.prod muN) muP :=
    ⟨by fun_prop, infinitePi_map_pair_dependent_arrays
      (fun c : TreeShell d n => Measure.infinitePi
        (fun _ : StrictDescendantVertex c.1 => uniform01))
      (fun c : TreeShell d n => Measure.infinitePi
        (fun v : DescendantVertex c.1 => ν v.1))⟩
  have h := ((MeasurePreserving.id rho).prod hp).comp
    ((measurePreserving_prodAssoc rho muR muN).comp (hf.prod hg))
  exact h.map_eq

theorem iCondIndepFun_noisy_factor_cutLevel {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (n : ℕ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) => cutSpins theta n z.1))
      ((measurable_cutSpins d theta n).comp measurable_fst).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → ℝ) × (TreeVertex d → A)) =>
        ((fun v : DescendantVertex c.1 => factor theta z.1 v.1),
          fun v : DescendantVertex c.1 => z.2 v.1))
      ((labelMeasure d).prod (Measure.infinitePi ν)) := by
  let S := TreeShell d n → IsingSpin
  let R := (c : TreeShell d n) →
    (StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A)
  let rho := (labelMeasure d).map (cutSpins theta n)
  let muP := Measure.infinitePi (fun c : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1)))
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) → S × R :=
    fun z => (cutSpins theta n z.1,
      fun c => (cutLabels z.1 c, fun v => z.2 v.1))
  have he : MeasurePreserving e ((labelMeasure d).prod (Measure.infinitePi ν))
      (rho.prod muP) :=
    ⟨((measurable_cutSpins d theta n).comp measurable_fst).prodMk
      (by unfold cutLabels; fun_prop),
      map_cutSpins_cutLabels_noises theta n ν⟩
  let F := fun (c : TreeShell d n)
      (p : S × ((StrictDescendantVertex c.1 → ℝ) × (DescendantVertex c.1 → A))) =>
    (coneFactor theta c.1 (p.1 c, p.2.1), p.2.2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_coneFactor theta c.1).comp
      (((measurable_pi_apply c).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hbase := iCondIndepFun_latent_infinitePi rho
    (fun c : TreeShell d n =>
      (Measure.infinitePi (fun _ : StrictDescendantVertex c.1 => uniform01)).prod
        (Measure.infinitePi (fun v : DescendantVertex c.1 => ν v.1))) F hF
  have hpull := iCondIndepFun_comp_measurePreserving
    ((labelMeasure d).prod (Measure.infinitePi ν)) (rho.prod muP) e he
    ((inferInstance : MeasurableSpace S).comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun p : S × R => F c (p.1, p.2 c)) from
      (hF c).comp (measurable_fst.prodMk
        ((measurable_pi_apply c).comp measurable_snd))) hbase
  have hfun : (fun c => (fun p : S × R => F c (p.1, p.2 c)) ∘ e) =
      (fun (c : TreeShell d n) (z : (TreeVertex d → ℝ) × (TreeVertex d → A)) =>
        ((fun v : DescendantVertex c.1 => factor theta z.1 v.1),
          fun v : DescendantVertex c.1 => z.2 v.1)) := by
    funext c z
    apply Prod.ext
    · exact (factor_cone_representation theta c.1 z.1).symm
    · rfl
  rw [hfun] at hpull
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

end Problem367.RootedBroadcast

namespace Problem367

local instance noisyCutLevelFreeIsingMeasurableSingletonIsingSpin :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem freeIsingMeasure_iCondIndepFun_noisy_cutLevel {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (n : ℕ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        ((fun v : RootedBroadcast.DescendantVertex c.1 => z.1 v.1),
          fun v : RootedBroadcast.DescendantVertex c.1 => z.2 v.1))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hf : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  have he := hf.prod (MeasurePreserving.id (Measure.infinitePi ν))
  apply iCondIndepFun_of_comp_measurePreserving
    ((labelMeasure d).prod (Measure.infinitePi ν))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν))
    (Prod.map (RootedBroadcast.factor theta) id) he
    ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun c : TreeShell d n => z.1 c.1))
    (by fun_prop : Measurable
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun c : TreeShell d n => z.1 c.1)).comap_le
    (fun _ => by fun_prop)
  simp only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map_fst, Prod.map_snd,
    id_eq]
  exact RootedBroadcast.iCondIndepFun_noisy_factor_cutLevel theta n ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_cutLevel {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        ((fun v : RootedBroadcast.DescendantVertex c.1 => z.1 v.1),
          fun v : RootedBroadcast.DescendantVertex c.1 => z.2 v.1))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_cutLevel theta n ν

theorem HasFreeIsingLaw.iCondIndepFun_cutLevel_observables {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    {B : TreeShell d n → Type*} [∀ c, MeasurableSpace (B c)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → B c)
    (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1))
      (by fun_prop : Measurable
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun c : TreeShell d n => z.1 c.1)).comap_le
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        F c ((fun v => z.1 v.1), fun v => z.2 v.1))
      (μ.prod (Measure.infinitePi ν)) :=
  (hμ.iCondIndepFun_noisy_cutLevel h0 h1 n ν).comp F hF

theorem HasFreeIsingLaw.iIndepFun_cutLevel_observables_cond {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (n : ℕ) (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    {B : TreeShell d n → Type*} [∀ c, MeasurableSpace (B c)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → B c)
    (hF : ∀ c, Measurable (F c)) (s : TreeShell d n → IsingSpin)
    (hs : (μ.prod (Measure.infinitePi ν))
      {z | (fun c : TreeShell d n => z.1 c.1) = s} ≠ 0) :
    iIndepFun
      (fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
        F c ((fun v => z.1 v.1), fun v => z.2 v.1))
      (μ.prod (Measure.infinitePi ν))[|{z | (fun c : TreeShell d n => z.1 c.1) = s}] := by
  exact iIndepFun_cond_fiber_of_iCondIndepFun
    (by fun_prop) (fun c => (hF c).comp (by fun_prop))
    (hμ.iCondIndepFun_cutLevel_observables h0 h1 n ν F hF) s hs

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CutLevelConditionalMean
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.appendCutContinuation_prefix_suffix _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_avoidingTreeCut _root_.OAI.Problem367.card_restrictedTreeCut _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_cutDescendants _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367.RootedBroadcast

local instance cutLevelConditionalMeanIsProbabilityLabelMeasure (d : ℕ) :
    IsProbabilityMeasure (labelMeasure d) := by
  unfold labelMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

local instance cutLevelConditionalMeanMeasurableSingletonIsingSpin_ra6648c_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem cutSpins_coordinate_fair {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) (c : TreeShell d n) (a : IsingSpin) :
    ((labelMeasure d).map (cutSpins theta n)) {s | s c = a} = (1 / 2 : ℝ≥0∞) := by
  rw [Measure.map_apply (measurable_cutSpins d theta n)
    (measurableSet_eq_fun (measurable_pi_apply c) measurable_const)]
  have h := (freeIsingMeasure_hasFreeIsingLaw d h0 h1).marginal c.1 a
  rw [freeIsingMeasure, Measure.map_apply (measurable_factor d theta)
    (measurableSet_eq_fun (measurable_pi_apply c.1) measurable_const)] at h
  change (labelMeasure d) {U | factor theta U c.1 = a} = _
  change (labelMeasure d) {U | factor theta U c.1 = a} = _ at h
  simpa using h

theorem condExp_noisy_factor_cone_le_two_integral {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (DescendantVertex c.1 → IsingSpin) × (DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂(labelMeasure d).prod (Measure.infinitePi ν),
      (((labelMeasure d).prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
          F ((fun v => factor theta z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => cutSpins theta n z.1)]) z ≤
      2 * ∫ w : (TreeVertex d → ℝ) × (TreeVertex d → A),
        F ((fun v => factor theta w.1 v.1), fun v => w.2 v.1)
          ∂(labelMeasure d).prod (Measure.infinitePi ν) := by
  let S := TreeShell d n → IsingSpin
  let R := (e : TreeShell d n) →
    (StrictDescendantVertex e.1 → ℝ) × (DescendantVertex e.1 → A)
  let rho := (labelMeasure d).map (cutSpins theta n)
  haveI : IsProbabilityMeasure rho := Measure.isProbabilityMeasure_map (measurable_cutSpins d theta n).aemeasurable
  let muR := Measure.infinitePi (fun e : TreeShell d n =>
    (Measure.infinitePi (fun _ : StrictDescendantVertex e.1 => uniform01)).prod
      (Measure.infinitePi (fun v : DescendantVertex e.1 => ν v.1)))
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) → S × R :=
    fun z => (cutSpins theta n z.1,
      fun c => (cutLabels z.1 c, fun v => z.2 v.1))
  have he : MeasurePreserving e ((labelMeasure d).prod (Measure.infinitePi ν))
      (rho.prod muR) :=
    ⟨((measurable_cutSpins d theta n).comp measurable_fst).prodMk
      (by unfold cutLabels; fun_prop), map_cutSpins_cutLabels_noises theta n ν⟩
  let G : IsingSpin × R → ℝ := fun p =>
    F (coneFactor theta c.1 (p.1, (p.2 c).1), (p.2 c).2)
  have hG : Measurable G :=
    hF.comp (((measurable_coneFactor theta c.1).comp
      (measurable_fst.prodMk
        (measurable_fst.comp ((measurable_pi_apply c).comp measurable_snd)))).prodMk
      (measurable_snd.comp ((measurable_pi_apply c).comp measurable_snd)))
  have h := condExp_binary_channel_comp_le_two_integral
    ((labelMeasure d).prod (Measure.infinitePi ν)) rho muR e he
    (fun s : S => s c) (measurable_pi_apply c)
    (cutSpins_coordinate_fair h0 h1 n c) G hG (fun p => hbound _)
  have hfun : (fun z => G ((e z).1 c, (e z).2)) =
      (fun z : (TreeVertex d → ℝ) × (TreeVertex d → A) =>
        F ((fun v => factor theta z.1 v.1), fun v => z.2 v.1)) := by
    funext z
    apply congrArg F
    apply Prod.ext
    · exact (factor_cone_representation theta c.1 z.1).symm
    · rfl
  rw [hfun] at h
  exact h

end Problem367.RootedBroadcast

namespace Problem367

local instance cutLevelConditionalMeanFreeIsingMeasurableSingletonIsingSpin_ra6648c_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_condExp_cutLevel_observable_le_two_integral
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂(freeIsingMeasure d theta).prod (Measure.infinitePi ν),
      (((freeIsingMeasure d theta).prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F ((fun v => z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => fun e : TreeShell d n => z.1 e.1)]) z ≤
      2 * ∫ w : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        F ((fun v => w.1 v.1), fun v => w.2 v.1)
          ∂(freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let P := (freeIsingMeasure d theta).prod (Measure.infinitePi ν)
  let Q := (labelMeasure d).prod (Measure.infinitePi ν)
  let e : (TreeVertex d → ℝ) × (TreeVertex d → A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    Prod.map (RootedBroadcast.factor theta) id
  let H : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → ℝ :=
    fun z => F ((fun v => z.1 v.1), fun v => z.2 v.1)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) →
      TreeShell d n → IsingSpin := fun z c => z.1 c.1
  have hS : Measurable S := by fun_prop
  have hH : Measurable H := hF.comp (by fun_prop)
  have hInt : Integrable H P := by
    apply Integrable.of_bound hH.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
      exact (hbound _).2)
  have hf : MeasurePreserving (RootedBroadcast.factor theta)
      (labelMeasure d) (freeIsingMeasure d theta) :=
    ⟨RootedBroadcast.measurable_factor d theta, rfl⟩
  have he : MeasurePreserving e Q P := hf.prod (MeasurePreserving.id (Measure.infinitePi ν))
  have hpull := condExp_comp_measurePreserving Q P e he
    ((inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap S)
    hS.comap_le hInt
  have hMean : (∫ x, H (e x) ∂Q) = ∫ z, H z ∂P := by
    rw [← he.map_eq]
    exact (integral_map he.measurable.aemeasurable hH.aestronglyMeasurable).symm
  have hsource := RootedBroadcast.condExp_noisy_factor_cone_le_two_integral
    h0 h1 n ν c F hF hbound
  change ∀ᵐ z ∂P, (P[H | MeasurableSpace.comap S inferInstance]) z ≤
    2 * ∫ w, H w ∂P
  have hgoal : ∀ᵐ z ∂Q.map e,
      (P[H | MeasurableSpace.comap S inferInstance]) z ≤ 2 * ∫ w, H w ∂P := by
    apply (ae_map_iff he.measurable.aemeasurable
      (measurableSet_le (stronglyMeasurable_condExp.mono hS.comap_le).measurable
        measurable_const)).mpr
    filter_upwards [hpull, hsource] with z hz hzbound
    have hmeanbound : (Q[H ∘ e | (MeasurableSpace.comap S inferInstance).comap e]) z ≤
        2 * ∫ x, H (e x) ∂Q := by
      simp only [MeasurableSpace.comap_comp, Function.comp_def, S, H, e,
        Prod.map_fst, Prod.map_snd, id_eq]
      exact hzbound
    rw [hz, hMean] at hmeanbound
    exact hmeanbound
  simpa only [he.map_eq] using hgoal

theorem HasFreeIsingLaw.condExp_cutLevel_observable_le_two_integral
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (c : TreeShell d n)
    (F : (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : Measurable F) (hbound : ∀ p, 0 ≤ F p ∧ F p ≤ 1) :
    ∀ᵐ z ∂μ.prod (Measure.infinitePi ν),
      ((μ.prod (Measure.infinitePi ν))[
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F ((fun v => z.1 v.1), fun v => z.2 v.1)) |
        (inferInstance : MeasurableSpace (TreeShell d n → IsingSpin)).comap
          (fun z => fun e : TreeShell d n => z.1 e.1)]) z ≤
      2 * ∫ w : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
        F ((fun v => w.1 v.1), fun v => w.2 v.1) ∂μ.prod (Measure.infinitePi ν) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_condExp_cutLevel_observable_le_two_integral h0 h1 n ν c F hF hbound

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Descent
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ) : CondIndepFun m hm f g ν := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := (condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)).mp hfg U V hU hV
  have hmeas : MeasurableSet {ω' | (ν⟦f ⁻¹' U ∩ g ⁻¹' V | m⟧) ω' =
      (ν⟦f ⁻¹' U | m⟧) ω' * (ν⟦g ⁻¹' V | m⟧) ω'} :=
    measurableSet_eq_fun (stronglyMeasurable_condExp.mono hm).measurable
      ((stronglyMeasurable_condExp.mono hm).measurable.mul
        (stronglyMeasurable_condExp.mono hm).measurable)
  have hdesc := ae_map_iff (μ := μ) he.measurable.aemeasurable hmeas
  rw [he.map_eq] at hdesc
  apply hdesc.mpr
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.symm.trans (hωmul.trans (congrArg₂ (· * ·) hωE hωH))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

theorem map_root_branch_family_of_sampler {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [MeasurableSpace S]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f) :
    (Measure.infinitePi ν).map (fun U => (f (U (root d)),
      fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun v : BranchVertex c => ν v.val))) := by
  let F : (NonrootVertex d → A) → (∀ c : Fin d, BranchVertex c → A) :=
    fun Y c v => Y (branchEmbedding c v)
  have hF : Measurable F := by fun_prop
  have hind := (LabelDecomposition.indepFun_coordinate_rest ν (root d)).comp hf hF
  have hB : Measurable (fun U : TreeVertex d → A => f (U (root d))) :=
    hf.comp (measurable_pi_apply (root d))
  have hY : Measurable (fun U : TreeVertex d → A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) := by fun_prop
  have hroot : (Measure.infinitePi ν).map (fun U => f (U (root d))) =
      (ν (root d)).map f := by
    change (Measure.infinitePi ν).map (f ∘ (fun U => U (root d))) = _
    rw [← Measure.map_map hf (measurable_pi_apply (root d)), Measure.infinitePi_map_eval]
  change IndepFun (fun U : TreeVertex d → A => f (U (root d)))
    (fun U => fun c : Fin d => fun v : BranchVertex c => U v.val)
    (Measure.infinitePi ν) at hind
  rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable, hroot]
  congr 1
  exact infinitePi_map_disjoint_family ν
    (fun c : Fin d => {v : TreeVertex d | [c] <+: v.val})
    (fun _ _ hce => branch_disjoint hce)

theorem iCondIndepFun_root_branch_observables {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [mS : MeasurableSpace S]
    [StandardBorelSpace A] [StandardBorelSpace S]
    {B : Fin d → Type*} [∀ c, MeasurableSpace (B c)]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f)
    (F : ∀ c, S × (BranchVertex c → A) → B c) (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      (mS.comap (fun U : TreeVertex d → A => f (U (root d))))
      (hf.comp (measurable_pi_apply (root d))).comap_le
      (fun c U => F c (f (U (root d)), fun v => U v.val))
      (Measure.infinitePi ν) := by
  let e : (TreeVertex d → A) → S × (∀ c : Fin d, BranchVertex c → A) :=
    fun U => (f (U (root d)), fun c v => U v.val)
  let ρ := ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
    Measure.infinitePi (fun v : BranchVertex c => ν v.val)))
  have he : MeasurePreserving e (Measure.infinitePi ν) ρ :=
    ⟨(hf.comp (measurable_pi_apply (root d))).prodMk (by fun_prop),
      map_root_branch_family_of_sampler ν f hf⟩
  have hbase := iCondIndepFun_latent_infinitePi ((ν (root d)).map f)
    (fun c : Fin d => Measure.infinitePi (fun v : BranchVertex c => ν v.val)) F hF
  have hpull := iCondIndepFun_comp_measurePreserving (Measure.infinitePi ν) ρ e he
    (mS.comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun z : S × (∀ c : Fin d, BranchVertex c → A) =>
      F c (z.1, z.2 c)) from by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

theorem map_noisyBroadcast {d : ℕ} {A : Type*} [MeasurableSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (factor theta (fun v => (U v).1), fun v => (U v).2)) =
      (freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fun v => (U v).1), fun v => (U v).2))).map
        (Prod.map (factor theta) id) := by
      rw [Measure.map_map ((measurable_factor d theta).prodMap measurable_id) (by fun_prop)]
      rfl
    _ = _ := by
      rw [infinitePi_map_split_pairs, ← Measure.map_prod_map _ _
        (measurable_factor d theta) measurable_id, Measure.map_id]
      rfl

local instance instMeasurableSingletonClassIsingSpin_2_ra6648c_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem iCondIndepFun_noisy_factor_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let F : ∀ c : Fin d, IsingSpin × (BranchVertex c → ℝ × A) →
      (BranchVertex c → IsingSpin) × (BranchVertex c → A) :=
    fun c p => (branchFactor theta c (p.1, fun v => (p.2 v).1),
      fun v => (p.2 v).2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := iCondIndepFun_root_branch_observables
    (fun v => uniform01.prod (ν v)) (fun p : ℝ × A => fairSpin p.1)
    (measurable_fairSpin.comp measurable_fst) F hF
  have heq : (fun (c : Fin d) (U : TreeVertex d → ℝ × A) => F c (fairSpin (U (root d)).1, fun v => U v.val)) =
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2)) := by
    funext c U
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  rw [heq] at h
  exact h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_1_ra6648c_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_iCondIndepFun_noisy_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply iCondIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot : (fun U : TreeVertex d → ℝ × A =>
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d)) =
      (fun U => fairSpin (U (RootedBroadcast.root d)).1) := by
    funext U
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.iCondIndepFun_noisy_factor_branches theta ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_branches {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_branches theta ν

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_NoisyBranchConditionalLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance noisyBranchConditionalLawMeasurableSingletonIsingSpin_ra6648c_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.planted_spin_event_mass
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (v : TreeVertex d) (s : IsingSpin) :
    (μ.prod (Measure.infinitePi ν))
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} = 1 / 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hset :
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} =
        {x : TreeVertex d → IsingSpin | x v = s} ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one, hμ.marginal]
  norm_num [ENNReal.ofReal_div_of_pos]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_PlantedInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem367.PlantedInformation

open PlantedSymmetry

variable {ι κ : Type*}

theorem measurable_spinSign : Measurable spinSign := by
  intro s hs
  trivial

end Problem367.PlantedInformation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Regrouping
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem indepFun_prodMk_left_of_joint
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : IndepFun X (fun ω => (Y ω, Z ω)) μ)
    (hYZ : IndepFun Y Z μ) :
    IndepFun (fun ω => (X ω, Y ω)) Z μ := by
  have hXY : IndepFun X Y μ := hXYZ.comp measurable_id measurable_fst
  have hmapX : IsProbabilityMeasure (μ.map X) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hX.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hmapY : IsProbabilityMeasure (μ.map Y) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hY.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hmapZ : IsProbabilityMeasure (μ.map Z) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hZ.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply (indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable
    hZ.aemeasurable).mpr
  calc
    _ = (μ.map (fun ω => (X ω, Y ω, Z ω))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.map_map (by fun_prop) (hX.prodMk (hY.prodMk hZ))]
      rfl
    _ = ((μ.map X).prod ((μ.map Y).prod (μ.map Z))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [hXYZ.map_prod_eq_prod_map_map hX.aemeasurable (hY.prodMk hZ).aemeasurable,
        hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable]
    _ = ((μ.map X).prod (μ.map Y)).prod (μ.map Z) :=
      (measurePreserving_prodAssoc (μ.map X) (μ.map Y) (μ.map Z)).symm.map_eq
    _ = _ := by
      rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

theorem condIndepFun_prodMk_left_of_joint
    {Ω S A B C : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {R : Ω → S} {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hR : Measurable R) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le
      X (fun ω => (Y ω, Z ω)) μ)
    (hYZ : CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le Y Z μ) :
    CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le
      (fun ω => (X ω, Y ω)) Z μ := by
  apply (condIndepFun_iff_indepFun_cond_fibers hR (hX.prodMk hY) hZ).mpr
  intro s hs
  let : IsProbabilityMeasure μ[|R ⁻¹' {s}] := cond_isProbabilityMeasure hs
  exact indepFun_prodMk_left_of_joint hX hY hZ
    (indepFun_cond_fiber_of_condIndepFun hR hX (hY.prodMk hZ) hXYZ s)
    (indepFun_cond_fiber_of_condIndepFun hR hY hZ hYZ s)

theorem condIndepFun_coordinate_others
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ} {F : ∀ i, Ω → B i}
    (hF : ∀ i, @Measurable Ω (B i) mΩ (mB i) (F i)) (hI : iCondIndepFun m hm F μ) (c : ι) :
    CondIndepFun m hm (F c) (fun ω => fun i : {i : ι // i ≠ c} => F i.val ω) μ := by
  let : MeasurableSpace Ω := mΩ
  have hle : ∀ i : ι, MeasurableSpace.comap (F i) (mB i) ≤ mΩ :=
    fun i => (hF i).comap_le
  have hd : Disjoint ({c} : Set ι) {i | i ≠ c} := by simp
  have h := condIndep_iSup_of_disjoint hle hI hd
  change CondIndep m
    (MeasurableSpace.comap (F c) (mB c))
    (MeasurableSpace.comap (fun ω => fun i : {i : ι // i ≠ c} => F i.val ω)
      inferInstance) hm μ
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_BoundedAverageConcentration
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
namespace BoundedAverageConcentration

variable {Ω ι : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measureReal_average_ge_le
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
    μ.real {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      Real.exp (-(s.card : ℝ) * τ ^ 2 / 2) := by
  classical
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hcenter : iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ := by
    exact h_indep.comp (fun i x => x - ∫ ω, X i ω ∂μ)
      (fun _ => measurable_id.sub_const _)
  have hsub : ∀ i ∈ s,
      HasSubgaussianMGF (fun ω => X i ω - ∫ x, X i x ∂μ) (1 / 4 : ℝ≥0) μ := by
    intro i hi
    convert hasSubgaussianMGF_of_mem_Icc (h_meas i hi) (h_bdd i hi) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hsum_mean : (∑ i ∈ s, ∫ x, X i x ∂μ) ≤ (s.card : ℝ) * τ / 2 := by
    calc
      (∑ i ∈ s, ∫ x, X i x ∂μ) ≤ ∑ _i ∈ s, τ / 2 :=
        Finset.sum_le_sum h_mean
      _ = (s.card : ℝ) * τ / 2 := by simp [mul_div_assoc]
  have hsubset : {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ⊆
      {ω | (s.card : ℝ) * τ / 2 ≤ ∑ i ∈ s, (X i ω - ∫ x, X i x ∂μ)} := by
    intro ω hω
    have hw : τ * (s.card : ℝ) ≤ ∑ i ∈ s, X i ω :=
      (le_div_iff₀ hcard).mp hω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib]
    nlinarith
  have hhoeff := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hcenter hsub
    (show 0 ≤ (s.card : ℝ) * τ / 2 by positivity)
  have hexp :
      -((s.card : ℝ) * τ / 2) ^ 2 /
          (2 * ((∑ _i ∈ s, (1 / 4 : ℝ≥0) : ℝ≥0) : ℝ)) =
        -(s.card : ℝ) * τ ^ 2 / 2 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    push_cast
    field_simp [ne_of_gt hcard]
    ring
  exact (measureReal_mono hsubset).trans (hexp ▸ hhoeff)

theorem measure_average_ge_le
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_bdd : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (h_mean : ∀ i ∈ s, (∫ ω, X i ω ∂μ) ≤ τ / 2) :
    μ {ω | τ ≤ (∑ i ∈ s, X i ω) / (s.card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(s.card : ℝ) * τ ^ 2 / 2)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (measureReal_average_ge_le h_indep s hs hτ h_meas h_bdd h_mean)

end BoundedAverageConcentration
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_LinearSignalTilt
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem linearSignalTilt_density_nonneg {a q : ℝ}
    (ha : |a| ≤ 1) (hq : |q| ≤ 1) : 0 ≤ 1 + a * q := by
  have hab : |a * q| ≤ 1 := by
    rw [abs_mul]
    calc
      |a| * |q| ≤ 1 * |q| := mul_le_mul_of_nonneg_right ha (abs_nonneg q)
      _ ≤ 1 := by simpa using hq
  have := (abs_le.mp hab).1
  linarith

theorem integrable_boundedSignal_mul {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (hf : Integrable f mu) :
    Integrable (fun x => q x * f x) mu := by
  refine hf.norm.mono' (hq.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hqb] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

theorem integral_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu) :
    (∫ x, f x ∂linearSignalTilt mu q a) =
      (∫ x, f x ∂mu) + a * ∫ x, q x * f x ∂mu := by
  rw [linearSignalTilt, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun x => (ENNReal.ofReal (1 + a * q x)).toReal • f x) =ᵐ[mu]
      (fun x => f x + a * (q x * f x)) := by
    filter_upwards [hqb] with x hx
    rw [ENNReal.toReal_ofReal (linearSignalTilt_density_nonneg ha hx), smul_eq_mul]
    ring
  rw [integral_congr_ae heq,
    integral_add hf ((integrable_boundedSignal_mul hq hqb hf).const_mul a),
    integral_const_mul]

theorem map_withDensity_comp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {mu : Measure Ω} {f : Ω → X} {w : X → ENNReal}
    (hf : Measurable f) (hw : Measurable w) :
    Measure.map f (mu.withDensity (w ∘ f)) = (Measure.map f mu).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hw hf]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusionMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem binaryFusion_density_eq_mixture {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    (1 / 2 : ENNReal) * (ENNReal.ofReal (1 + u) * ENNReal.ofReal (1 + v)) +
      (1 / 2 : ENNReal) * (ENNReal.ofReal (1 - u) * ENNReal.ofReal (1 - v)) =
        ENNReal.ofReal (1 + u * v) := by
  have hpu : 0 ≤ 1 + u := by have := (abs_lt.mp hu).1; linarith
  have hpv : 0 ≤ 1 + v := by have := (abs_lt.mp hv).1; linarith
  have hmu : 0 ≤ 1 - u := by have := (abs_lt.mp hu).2; linarith
  have hmv : 0 ≤ 1 - v := by have := (abs_lt.mp hv).2; linarith
  have hh : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hh, ← ENNReal.ofReal_mul hpu, ← ENNReal.ofReal_mul hmu,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ (1 / 2 : ℝ) * ((1 + u) * (1 + v)))
      (by positivity : 0 ≤ (1 / 2 : ℝ) * ((1 - u) * (1 - v)))]
  congr 1
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem selectedObservationField_comap_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (g : TreeAut d) :
    (selectedObservationField F v).comap (Prod.map (relabel g) (relabel g)) =
      selectedObservationField F (fun i => g.toEquiv.symm (v i)) := by
  unfold selectedObservationField
  rw [MeasurableSpace.comap_comp]
  rfl

theorem selectedObservationField_eq_of_range_eq {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hvw : Set.range v = Set.range w) :
    selectedObservationField F v = selectedObservationField F w :=
  le_antisymm (selectedObservationField_le_of_range_subset F hvw.subset)
    (selectedObservationField_le_of_range_subset F hvw.symm.subset)

theorem selectedPosterior_relabel_ae {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
        Prod.map (relabel g) (relabel g) =ᵐ[mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))]
      selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r) := by
  let := hmu.isProbabilityMeasure
  let rho := mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) rho := by
    apply Integrable.of_bound
      ((hsign.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hCE := condExp_comp_measurePreserving rho rho
    (Prod.map (relabel g) (relabel g))
    (PlantedStationarity.measurePreserving_planted_relabel hmu nu g)
    (selectedObservationField F v) (selectedObservationField_le hF v) hi
  rw [selectedObservationField_comap_relabel] at hCE
  exact hCE.symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorChannels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem exists_selectedPosterior_channel
    {d : ℕ} {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ∃ g : (ι → B) → ℝ, Measurable g ∧
      ∀ p, selectedPosterior rho F v r p =
        g (fun i => F (p.1 (v i)) (p.2 (v i))) := by
  have hm : Measurable[selectedObservationField F v]
      (selectedPosterior rho F v r) := stronglyMeasurable_condExp.measurable
  obtain ⟨g, hg, heq⟩ := hm.exists_eq_measurable_comp
  exact ⟨g, hg, fun p => congrFun heq p⟩

theorem exists_selectedAttenuation_channel
    {d : ℕ} {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ∃ g : (ι → B) → ℝ, Measurable g ∧
      (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p, responseAttenuation theta (Real.artanh (selectedPosterior rho F v r p)) ^ 2 =
        g (fun i => F (p.1 (v i)) (p.2 (v i))) := by
  obtain ⟨f, hf, heq⟩ := exists_selectedPosterior_channel rho F v r
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hat : Measurable (responseAttenuation theta) := by
    unfold responseAttenuation
    simp only [Real.tanh_eq_sinh_div_cosh]
    fun_prop
  refine ⟨fun x => responseAttenuation theta (Real.artanh (f x)) ^ 2,
    ((hat.comp (ha.comp hf)).pow_const 2),
    ?_, ?_⟩
  · intro x
    refine ⟨sq_nonneg _, ?_⟩
    have hpos := responseAttenuation_pos hθ (Real.artanh (f x))
    have hone := responseAttenuation_le_one hθ (Real.artanh (f x))
    nlinarith
  · intro p
    rw [heq p]

theorem exists_selectedAttenuation_local_channel
    {d : ℕ} {A B ι κ : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : κ → TreeVertex d) (j : ι → κ) (r : TreeVertex d)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ∃ g : ((κ → IsingSpin) × (κ → A)) → ℝ, Measurable g ∧
      (∀ x, g x ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p, responseAttenuation theta
          (Real.artanh (selectedPosterior rho F (v ∘ j) r p)) ^ 2 =
        g (fun k => p.1 (v k), fun k => p.2 (v k)) := by
  obtain ⟨f, hf, hbound, heq⟩ := exists_selectedAttenuation_channel rho F (v ∘ j) r hθ
  let obs : ((κ → IsingSpin) × (κ → A)) → (ι → B) :=
    fun x i => F (x.1 (j i)) (x.2 (j i))
  have hobs : Measurable obs := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun x : (κ → IsingSpin) × (κ → A) =>
      (x.1 (j i), x.2 (j i))) by fun_prop)
  refine ⟨f ∘ obs, hf.comp hobs, fun x => hbound (obs x), ?_⟩
  intro p
  exact heq p

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutContinuations
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem sum_cutContinuations {M : Type*} [AddCommMonoid M]
    (d k L : ℕ) (f : TreeShell d (k + 1 + L) → M) :
    (∑ v : TreeShell d (k + 1 + L), f v) =
      ∑ p : TreeShell d (k + 1), ∑ w : ReducedTail (cutLastColor p) L,
        f (appendCutContinuation p w) := by
  rw [← (cutContinuationEquiv d k L).sum_comp f, Fintype.sum_sigma]
  rfl

theorem sum_cutDescendants {M : Type*} [AddCommMonoid M] {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (f : TreeShell d (k + 1 + L) → M) :
    (∑ v ∈ cutDescendants I L, f v) =
      ∑ p ∈ I, ∑ w : ReducedTail (cutLastColor p) L, f (appendCutContinuation p w) := by
  classical
  have h := sum_cutContinuations d k L (fun v => if cutPrefix v ∈ I then f v else 0)
  simpa [cutDescendants, Finset.sum_filter] using h

@[simp] theorem card_cutDescendants {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    (cutDescendants I L).card = I.card * (d - 1) ^ L := by
  classical
  have h := sum_cutDescendants I L (fun _ => (1 : ℕ))
  simpa using h

theorem average_cutDescendants {d k : ℕ}
    (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (f : TreeShell d (k + 1 + L) → ℝ) :
    (∑ v ∈ cutDescendants I L, f v) / ((cutDescendants I L).card : ℝ) =
      (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L, f (appendCutContinuation p w)) /
        (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
  rw [sum_cutDescendants, card_cutDescendants, Nat.cast_mul,
    ← Finset.sum_div, div_div, mul_comm]

theorem rootPathProduct_le_cutContinuationProduct {d k L : ℕ}
    (a : TreeVertex d → ℝ) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ 1)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    rootPathProduct a (appendCutContinuation p w).1 ≤ cutContinuationProduct a p w := by
  unfold rootPathProduct
  rw [(appendCutContinuation p w).2, Finset.prod_range_add]
  have hpre : (∏ i ∈ Finset.range (k + 1),
      a (rootPathVertex (appendCutContinuation p w).1 (i + 1))) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (ha _).1) (fun i _ => (ha _).2)
  have htail : 0 ≤ (∏ j ∈ Finset.range L,
      a (rootPathVertex (appendCutContinuation p w).1 (k + 1 + j + 1))) :=
    Finset.prod_nonneg (fun j _ => (ha _).1)
  have h := mul_le_mul_of_nonneg_right hpre htail
  simpa only [one_mul, cutContinuationProduct, Nat.add_assoc] using h

theorem average_rootPathProduct_le_continuation_average {d k : ℕ}
    (a : TreeVertex d → ℝ) (ha : ∀ v, 0 ≤ a v ∧ a v ≤ 1)
    (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    (∑ v ∈ cutDescendants I L, rootPathProduct a v.1) /
        ((cutDescendants I L).card : ℝ) ≤
      (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L,
        cutContinuationProduct a p w) / (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
  rw [average_cutDescendants]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro p hp
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun w _ => rootPathProduct_le_cutContinuationProduct a ha p w)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CutLevelConcentration
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem integral_cond_fiber_le_of_condExp_le
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Ω → S} (hs : Measurable s)
    {f : Ω → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hbound : ∀ᵐ ω ∂μ, (μ[f | MeasurableSpace.comap s inferInstance]) ω ≤ C)
    (a : S) (ha : μ (s ⁻¹' {a}) ≠ 0) :
    (∫ ω, f ω ∂μ[|s ⁻¹' {a}]) ≤ C := by
  have : (ae (μ.restrict (s ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp ha)
  have hCE := condExp_comap_eq_cond_on_fiber hs a hf
  have hB := ae_restrict_le (s := s ⁻¹' {a}) hbound
  obtain ⟨ω, hωCE, hωB⟩ := (hCE.and hB).exists
  exact hωCE.symm.le.trans hωB

theorem measureReal_le_of_cond_fibers
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Countable S]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → S} (hs : Measurable s)
    {E : Set Ω} (hE : MeasurableSet E) {C : ℝ}
    (hbound : ∀ a : S, μ (s ⁻¹' {a}) ≠ 0 → μ[|s ⁻¹' {a}].real E ≤ C) :
    μ.real E ≤ C := by
  have hCE : ∀ᵐ ω ∂μ,
      (μ[E.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap s inferInstance]) ω ≤ C := by
    apply ae_of_ae_restrict_fibers hs
    intro a
    by_cases ha : μ (s ⁻¹' {a}) = 0
    · rw [Measure.restrict_eq_zero.mpr ha]
      simp
    filter_upwards [condExp_indicator_comap_eq_cond_on_fiber hs a hE] with ω hω
    exact hω.le.trans (hbound a ha)
  have hint := integral_mono_ae integrable_condExp (integrable_const C) hCE
  rw [integral_condExp hs.comap_le] at hint
  simpa only [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one,
    integral_const, probReal_univ, one_smul, one_mul] using hint

local instance localInst_ra6648c_3 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.measure_cutLevel_average_ge_cond_le
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4)
    (s : TreeShell d n → IsingSpin)
    (hs : (μ.prod (Measure.infinitePi ν))
      {z | (fun c : TreeShell d n => z.1 c.1) = s} ≠ 0) :
    (μ.prod (Measure.infinitePi ν))[|{z | (fun c : TreeShell d n => z.1 c.1) = s}]
      {z | τ ≤ (∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) / (I.card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  let P := μ.prod (Measure.infinitePi ν)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → TreeShell d n → IsingSpin :=
    fun z c => z.1 c.1
  let X := fun (c : TreeShell d n) (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) =>
    F c ((fun v => z.1 v.1), fun v => z.2 v.1)
  have hS : Measurable S := by fun_prop
  have hX : ∀ c, Measurable (X c) := fun c => (hF c).comp (by fun_prop)
  let : IsProbabilityMeasure ((μ.prod (Measure.infinitePi ν))[|
      {z | (fun c : TreeShell d n => z.1 c.1) = s}]) := cond_isProbabilityMeasure hs
  apply BoundedAverageConcentration.measure_average_ge_le
    (hμ.iIndepFun_cutLevel_observables_cond h0 h1 n ν F hF s hs) I hI hτ
  · intro c _
    exact (hX c).aemeasurable
  · intro c _
    exact Filter.Eventually.of_forall (fun z => hbound c _)
  · intro c hc
    have hi : Integrable (X c) P := by
      apply Integrable.of_bound (hX c).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound c _).1]
        exact (hbound c _).2)
    have hb := integral_cond_fiber_le_of_condExp_le hS hi
      (hμ.condExp_cutLevel_observable_le_two_integral h0 h1 n ν c (F c) (hF c)
        (hbound c)) s hs
    exact hb.trans (by linarith [hmean c hc])

theorem HasFreeIsingLaw.measure_cutLevel_average_ge_le
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (n : ℕ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ c : TreeShell d n, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → A) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d n)) (hI : I.Nonempty) {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → A),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1) ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4) :
    (μ.prod (Measure.infinitePi ν))
      {z | τ ≤ (∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) / (I.card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  let P := μ.prod (Measure.infinitePi ν)
  let S : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → TreeShell d n → IsingSpin :=
    fun z c => z.1 c.1
  have hS : Measurable S := by fun_prop
  have hsum : Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ∑ c ∈ I, F c ((fun v => z.1 v.1), fun v => z.2 v.1)) :=
    Finset.measurable_fun_sum I (fun c _ => (hF c).comp (by fun_prop))
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  apply measureReal_le_of_cond_fibers hS (measurableSet_le measurable_const (hsum.div_const _))
  intro s hs
  have h := hμ.measure_cutLevel_average_ge_cond_le h0 h1 n ν F hF hbound I hI hτ hmean s hs
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr h |>.trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideBranches
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem cone_mono {d : ℕ} {r s : TreeVertex d} (h : r.1 <+: s.1) :
    cone s ⊆ cone r := fun _ hu => h.trans hu

theorem edge_leaving_cone {d : ℕ} {r u w : TreeVertex d}
    (hu : u ∈ cone r) (hw : w ∉ cone r) (huw : treeAdj u w) :
    u = r ∧ w = parentVertex r := by
  have hur : u = r := by
    by_contra hne
    exact hw (treeAdj_preserves_prefix hu huw hne)
  subst u
  refine ⟨rfl, ?_⟩
  rcases huw with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact False.elim (hw (by
      change r.1 <+: w.1
      rw [hc]
      exact List.prefix_append _ _))
  · apply Subtype.ext
    change w.1 = r.1.dropLast
    rw [hc]
    simp

theorem reachable_in_cone {d : ℕ} {r u : TreeVertex d} (hu : u ∈ cone r) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
  have aux : ∀ n : ℕ, ∀ u : TreeVertex d, u.1.length = n → u ∈ cone r →
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hlen hu
      by_cases hur : u = r
      · subst u
        exact .refl
      · have hlt : r.1.length < u.1.length := by
          have hle := hu.length_le
          have hne : r.1.length ≠ u.1.length := by
            intro heq
            exact hur (Subtype.ext (hu.eq_of_length heq).symm)
          omega
        have hnil : u.1 ≠ [] := by
          intro h
          simp [h] at hlt
        have hp : parentVertex u ∈ cone r := by
          apply List.prefix_of_prefix_length_le hu (List.dropLast_prefix u.1)
          rw [List.length_dropLast]
          omega
        have hplen : (parentVertex u).1.length < n := by
          rw [parentVertex_length]
          omega
        exact (ih _ hplen _ rfl hp).tail ⟨hp, hu, treeAdj_parentVertex hnil⟩
  exact aux _ u rfl hu

theorem parent_not_mem_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    parentVertex r ∉ cone r := by
  intro h
  have hlen := h.length_le
  rw [parentVertex_length] at hlen
  have hpos := List.length_pos_iff.mpr hr
  omega

theorem mem_cone_iff_reachable_avoiding_parent {d : ℕ} (r u : TreeVertex d)
    (hr : r.1 ≠ []) : u ∈ cone r ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ parentVertex r ∧ y ≠ parentVertex r ∧ treeAdj x y)
      r u := by
  constructor
  · intro hu
    apply Relation.ReflTransGen.mono (fun x y hxy => ?_) r u (reachable_in_cone hu)
    exact ⟨fun h => parent_not_mem_cone r hr (h ▸ hxy.1),
      fun h => parent_not_mem_cone r hr (h ▸ hxy.2.1), hxy.2.2⟩
  · intro h
    induction h with
    | refl => exact List.prefix_refl _
    | tail h hxy ih =>
        by_contra hy
        exact hxy.2.1 (edge_leaving_cone ih hy hxy.2.2).2

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InwardCutChannels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.InwardCutChannels

open RootedBroadcast CutContinuationChannels

variable {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem exists_regionProduct_channel
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (p : TreeVertex d)
    (R : ℕ → Set (TreeVertex d)) (r : ℕ → TreeVertex d) (s : Finset ℕ)
    (hR : ∀ i, R i ⊆ PathSideBranches.cone p) :
    ∃ g : ConeSample A p → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, regionProduct rho F theta R r s z = g (globalCone p z) := by
  have hex (i : ℕ) : ∃ g : ConeSample A p → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, responseAttenuation theta
        (Real.artanh (selectedPosterior rho F (Subtype.val : R i → TreeVertex d)
          (r i) z)) ^ 2 = g (globalCone p z) := by
    exact exists_selectedAttenuation_local_channel rho hF
      (Subtype.val : DescendantVertex p → TreeVertex d)
      (fun u : R i => (⟨u.1, hR i u.2⟩ : DescendantVertex p)) (r i) hθ
  choose g hg hb heq using hex
  refine ⟨fun z => ∏ i ∈ s, g i z,
    s.measurable_fun_prod (fun i _ => hg i), ?_, ?_⟩
  · intro z
    exact ⟨Finset.prod_nonneg (fun i _ => (hb i z).1),
      Finset.prod_le_one (fun i _ => (hb i z).1) (fun i _ => (hb i z).2)⟩
  · intro z
    exact Finset.prod_congr rfl (fun i _ => heq i z)

theorem exists_regionAverage_channel {W : Type*} [Fintype W] [Nonempty W]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (p : TreeVertex d)
    (R : W → ℕ → Set (TreeVertex d)) (r : W → ℕ → TreeVertex d)
    (s : W → Finset ℕ) (hR : ∀ w i, R w i ⊆ PathSideBranches.cone p) :
    ∃ g : ConeSample A p → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, regionAverage rho F theta R r s z = g (globalCone p z) := by
  choose g hg hb heq using fun w =>
    exists_regionProduct_channel rho hF hθ p (R w) (r w) (s w) (hR w)
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  refine ⟨fun z => (∑ w : W, g w z) / (Fintype.card W : ℝ),
    (Finset.measurable_fun_sum _ (fun w _ => hg w)).div_const _, ?_, ?_⟩
  · intro z
    constructor
    · exact div_nonneg (Finset.sum_nonneg (fun w _ => (hb w z).1)) hc.le
    · apply (div_le_iff₀ hc).mpr
      simpa using Finset.sum_le_sum
        (fun w (_ : w ∈ (Finset.univ : Finset W)) => (hb w z).2)
  · intro z
    unfold regionAverage
    congr 1
    exact Finset.sum_congr rfl (fun w _ => heq w z)

end Problem367.InwardCutChannels

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorTilt
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367

theorem setIntegral_spin_posterior_tilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    {F : Ω → ℝ} (hF : StronglyMeasurable[mSmall] F) (hFi : Integrable F mu)
    (a : IsingSpin) :
    ∫ x in {x | S x = a}, F x ∂mu = (1 / 2 : ℝ) *
      ∫ x, F x * (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hSm : AEStronglyMeasurable (fun x => spinSign (S x)) mu :=
    (hsign.comp hS).aestronglyMeasurable
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hSi : Integrable (fun x => spinSign (S x)) mu := Integrable.of_bound hSm 1 hSb
  have hFSi : Integrable (fun x => F x * spinSign (S x)) mu := hFi.mul_bdd hSm hSb
  have hpull := condExp_mul_of_stronglyMeasurable_left hF hFSi hSi
  have hFMi : Integrable
      (fun x => F x * mu[fun y => spinSign (S y) | mSmall] x) mu :=
    integrable_condExp.congr hpull
  have hint : (∫ x, F x * spinSign (S x) ∂mu) =
      ∫ x, F x * mu[fun y => spinSign (S y) | mSmall] x ∂mu := by
    rw [← integral_condExp (m := mSmall) hm]
    exact integral_congr_ae hpull
  have hA : MeasurableSet {x | S x = a} :=
    (show MeasurableSet ({a} : Set IsingSpin) from trivial).preimage hS
  have hindicator : ({x | S x = a} : Set Ω).indicator F =
      fun x => (1 / 2 : ℝ) * (F x + spinSign a * (F x * spinSign (S x))) := by
    funext x
    cases hs : S x <;> cases a <;> simp [Set.indicator, hs, spinSign] <;> ring
  rw [← integral_indicator hA, hindicator, integral_const_mul,
    integral_add hFi (hFSi.const_mul (spinSign a)), integral_const_mul, hint]
  congr 1
  rw [← integral_const_mul, ← integral_add hFi (hFMi.const_mul (spinSign a))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem integral_cond_spin_posterior_tilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    {F : Ω → ℝ} (hF : StronglyMeasurable[mSmall] F) (hFi : Integrable F mu)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    ∫ x, F x ∂ProbabilityTheory.cond mu {x | S x = a} =
      ∫ x, F x * (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  rw [ProbabilityTheory.cond, integral_smul_measure, hfair]
  rw [setIntegral_spin_posterior_tilt hm hS hF hFi a]
  norm_num
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem map_cond_spin_observation_eq_linearSignalTilt
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hpost : mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x))
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    Measure.map X (ProbabilityTheory.cond mu {x | S x = a}) =
      linearSignalTilt (Measure.map X mu) q (spinSign a) := by
  have hQ : Measurable (fun x => q (X x)) := hq.comp hX
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hQb : ∀ᵐ x ∂mu, |q (X x)| ≤ 1 := by
    have hb := ae_bdd_norm_condExp_of_ae_bdd_norm (m := mY.comap X) hSb
    filter_upwards [hb, hpost] with x hx hp
    simpa only [hp, Real.norm_eq_abs] using hx
  have hQi : Integrable (fun x => q (X x)) mu :=
    Integrable.of_bound hQ.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hQb)
  have ha : |spinSign a| ≤ 1 := by cases a <;> norm_num [spinSign]
  let : IsProbabilityMeasure (ProbabilityTheory.cond mu {x | S x = a}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  have hdi := (integrable_const (1 : ℝ)).add (hQi.const_mul (spinSign a))
  let : IsFiniteMeasure (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) :=
    isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  have hmap : Measure.map X (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) =
      linearSignalTilt (Measure.map X mu) q (spinSign a) := by
    unfold linearSignalTilt
    exact map_withDensity_comp (mu := mu) (f := X)
      (w := fun y => ENNReal.ofReal (1 + spinSign a * q y)) hX
      (ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul hq)))
  rw [← hmap]
  ext t ht
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  let f : Y → ℝ := t.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator ht
  have hfint : Integrable (fun x => f (X x)) mu := by
    refine Integrable.of_bound (hfm.comp hX).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : X x ∈ t <;> simp [f, hx])
  have hfsmall : StronglyMeasurable[mY.comap X] (fun x => f (X x)) :=
    (hfm.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hint : (∫ y, f y ∂Measure.map X (ProbabilityTheory.cond mu {x | S x = a})) =
      ∫ y, f y ∂Measure.map X (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) := by
    rw [integral_map hX.aemeasurable hfm.aestronglyMeasurable,
      integral_map hX.aemeasurable hfm.aestronglyMeasurable,
      integral_cond_spin_posterior_tilt hX.comap_le hS hfsmall hfint a hfair,
      integral_linearSignalTilt hQ hQb ha hfint,
      ← integral_const_mul,
      ← integral_add hfint ((integrable_boundedSignal_mul hQ hQb hfint).const_mul (spinSign a))]
    apply integral_congr_ae
    filter_upwards [hpost] with x hx
    rw [hx]
    ring
  simpa [f, integral_indicator ht, measureReal_def] using hint

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorCertification
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem condExp_spin_eq_of_restricted_density
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ y ∂Measure.map X mu, |q y| ≤ 1)
    (hdensity : Measure.map X (mu.restrict {x | S x = IsingSpin.pos}) =
      (Measure.map X mu).withDensity (fun y => ENNReal.ofReal ((1 + q y) / 2))) :
    mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x) := by
  let E : Set Ω := {x | S x = IsingSpin.pos}
  have hE : MeasurableSet E :=
    (show MeasurableSet ({IsingSpin.pos} : Set IsingSpin) from trivial).preimage hS
  let I : Ω → ℝ := E.indicator (fun _ => 1)
  have hI : Integrable I mu := (integrable_const (1 : ℝ)).indicator hE
  have hsrc : (fun x => ((mu.restrict E).rnDeriv mu x).toReal) =ᵐ[mu] I := by
    filter_upwards [Measure.rnDeriv_restrict_self mu hE] with x hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [I, hxE]
  have hRN := toReal_rnDeriv_map (Measure.absolutelyContinuous_restrict (μ := mu) (s := E)) hX
  have hpost :
      (fun x => ((Measure.map X (mu.restrict E)).rnDeriv (Measure.map X mu) (X x)).toReal)
        =ᵐ[mu] mu[I | mY.comap X] :=
    hRN.trans (condExp_congr_ae hsrc)
  have htarg :
      (fun x => ((Measure.map X (mu.restrict E)).rnDeriv (Measure.map X mu) (X x)).toReal)
        =ᵐ[mu] fun x => (1 + q (X x)) / 2 := by
    have hderiv := Measure.rnDeriv_withDensity (Measure.map X mu)
      (show Measurable (fun y => ENNReal.ofReal ((1 + q y) / 2)) by fun_prop)
    rw [← hdensity] at hderiv
    filter_upwards [ae_of_ae_map hX.aemeasurable hderiv,
      ae_of_ae_map hX.aemeasurable hqb] with x hx hxb
    rw [hx, ENNReal.toReal_ofReal]
    have := (abs_le.mp hxb).1
    linarith
  have hIp : mu[I | mY.comap X] =ᵐ[mu] fun x => (1 + q (X x)) / 2 :=
    hpost.symm.trans htarg
  have hsrepr : (fun x => spinSign (S x)) = (2 : ℝ) • I - (fun _ => 1) := by
    funext x
    cases hs : S x <;> norm_num [I, E, hs, spinSign]
  rw [hsrepr]
  have hsub := condExp_sub (hI.smul (2 : ℝ)) (integrable_const (1 : ℝ)) (mY.comap X)
  have hmul := condExp_smul (μ := mu) (2 : ℝ) I (mY.comap X)
  filter_upwards [hsub, hmul, hIp] with x hxsub hxmul hxI
  rw [hxsub, Pi.sub_apply, hxmul, Pi.smul_apply, smul_eq_mul,
    condExp_const hX.comap_le, hxI]
  ring

theorem condExp_spin_eq_of_conditional_linearTilt
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ y ∂Measure.map X mu, |q y| ≤ 1)
    (hfair : mu {x | S x = IsingSpin.pos} = (1 / 2 : ENNReal))
    (hcond : Measure.map X (ProbabilityTheory.cond mu {x | S x = IsingSpin.pos}) =
      linearSignalTilt (Measure.map X mu) q 1) :
    mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x) := by
  apply condExp_spin_eq_of_restricted_density hS hX hq hqb
  have hscaled := congrArg (fun nu : Measure Y => (1 / 2 : ENNReal) • nu) hcond
  rw [ProbabilityTheory.cond, Measure.map_smul, hfair, smul_smul] at hscaled
  norm_num at hscaled
  rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤), one_smul] at hscaled
  rw [hscaled, linearSignalTilt, ← withDensity_smul (2⁻¹) (by fun_prop)]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [Pi.smul_apply, smul_eq_mul, one_mul]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp [div_eq_mul_inv, mul_comm]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367

theorem measure_eq_fair_spin_mixture
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal)) :
    mu = (1 / 2 : ENNReal) • cond mu {x | S x = .pos} +
      (1 / 2 : ENNReal) • cond mu {x | S x = .neg} := by
  have h := sum_meas_smul_cond_fiber hS mu
  change (∑ a : IsingSpin, mu {x | S x = a} • cond mu {x | S x = a}) = mu at h
  simpa only [sum_isingSpin, hfair, add_comm] using h.symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_ObservationFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

private theorem ae_observation_pair_bounds
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {q : A → ℝ} {r : B → ℝ}
    (hq : ∀ᵐ x ∂mu, |q x| < 1) (hr : ∀ᵐ y ∂nu, |r y| < 1) :
    ∀ᵐ p ∂mu.prod nu, |q p.1| < 1 ∧ |r p.2| < 1 := by
  have hq' : ∀ᵐ p ∂mu.prod nu, |q p.1| < 1 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hq
  have hr' : ∀ᵐ p ∂mu.prod nu, |r p.2| < 1 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae hr
  exact hq'.and hr'

theorem observationFusionJointLaw_eq_mixture
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqb : ∀ᵐ x ∂mu, |q x| < 1) (hrb : ∀ᵐ y ∂nu, |r y| < 1) :
    (1 / 2 : ENNReal) • ((linearSignalTilt mu q 1).prod (linearSignalTilt nu r 1)) +
      (1 / 2 : ENNReal) • ((linearSignalTilt mu q (-1)).prod (linearSignalTilt nu r (-1))) =
        observationFusionJointLaw mu nu q r := by
  unfold linearSignalTilt observationFusionJointLaw
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [prod_withDensity (by fun_prop) (by fun_prop),
    prod_withDensity (by fun_prop) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_add_left (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_observation_pair_bounds hqb hrb] with p hp
  exact binaryFusion_density_eq_mixture hp.1 hp.2

theorem observationFusion_positive_product_eq_tilt
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqb : ∀ᵐ x ∂mu, |q x| < 1) (hrb : ∀ᵐ y ∂nu, |r y| < 1) :
    (linearSignalTilt mu q 1).prod (linearSignalTilt nu r 1) =
      linearSignalTilt (observationFusionJointLaw mu nu q r)
        (fun p => binaryFusion (q p.1) (r p.2)) 1 := by
  unfold linearSignalTilt observationFusionJointLaw
  rw [prod_withDensity (by fun_prop) (by fun_prop),
    ← withDensity_mul _ (by fun_prop) (by unfold binaryFusion; fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_observation_pair_bounds hqb hrb] with p hp
  simp only [one_mul, Pi.mul_apply]
  have hpq : 0 ≤ 1 + q p.1 := by have := (abs_lt.mp hp.1).1; linarith
  have hden := binaryFusion_denominator_pos hp.1 hp.2
  rw [← ENNReal.ofReal_mul hpq, ← ENNReal.ofReal_mul hden.le]
  congr 1
  unfold binaryFusion
  field_simp
  ring

theorem condExp_spin_given_observation_pair_eq_binaryFusion
    {Ω A B : Type*} {mΩ : MeasurableSpace Ω} {mA : MeasurableSpace A}
    {mB : MeasurableSpace B} {rho : Measure Ω} [IsProbabilityMeasure rho]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hpostX : rho[fun x => spinSign (S x) | mA.comap X] =ᵐ[rho] fun x => q (X x))
    (hpostY : rho[fun x => spinSign (S x) | mB.comap Y] =ᵐ[rho] fun x => r (Y x))
    (hqb : ∀ᵐ x ∂rho, |q (X x)| < 1) (hrb : ∀ᵐ x ∂rho, |r (Y x)| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, IndepFun X Y (cond rho {x | S x = a})) :
    rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] =ᵐ[rho]
      fun x => binaryFusion (q (X x)) (r (Y x)) := by
  let mu := Measure.map X rho
  let nu := Measure.map Y rho
  haveI : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hqm : ∀ᵐ x ∂mu, |q x| < 1 :=
    (ae_map_iff hX.aemeasurable (measurableSet_lt hq.abs measurable_const)).2 hqb
  have hrm : ∀ᵐ y ∂nu, |r y| < 1 :=
    (ae_map_iff hY.aemeasurable (measurableSet_lt hr.abs measurable_const)).2 hrb
  have hpair (a : IsingSpin) : Measure.map (fun x => (X x, Y x)) (cond rho {x | S x = a}) =
      (linearSignalTilt mu q (spinSign a)).prod (linearSignalTilt nu r (spinSign a)) := by
    let : IsProbabilityMeasure (cond rho {x | S x = a}) :=
      cond_isProbabilityMeasure (by rw [hfair]; norm_num)
    rw [(hInd a).map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
      map_cond_spin_observation_eq_linearSignalTilt hS hX hq hpostX a (hfair a),
      map_cond_spin_observation_eq_linearSignalTilt hS hY hr hpostY a (hfair a)]
  have hjoint : Measure.map (fun x => (X x, Y x)) rho =
      observationFusionJointLaw mu nu q r := by
    calc
      _ = Measure.map (fun x => (X x, Y x))
          ((1 / 2 : ENNReal) • cond rho {x | S x = .pos} +
           (1 / 2 : ENNReal) • cond rho {x | S x = .neg}) := by
        rw [← measure_eq_fair_spin_mixture hS hfair]
      _ = _ := by
        rw [Measure.map_add _ _ (hX.prodMk hY),
          Measure.map_smul,
          Measure.map_smul,
          hpair .pos, hpair .neg]
        exact observationFusionJointLaw_eq_mixture hq hr hqm hrm
  apply condExp_spin_eq_of_conditional_linearTilt hS (hX.prodMk hY)
    (show Measurable (fun p : A × B => binaryFusion (q p.1) (r p.2)) by
      unfold binaryFusion
      fun_prop)
  · rw [hjoint]
    have hb : ∀ᵐ p ∂observationFusionJointLaw mu nu q r, |q p.1| < 1 ∧ |r p.2| < 1 :=
      (withDensity_absolutelyContinuous (mu.prod nu)
        (fun p => ENNReal.ofReal (1 + q p.1 * r p.2))).ae_le
          (ae_observation_pair_bounds hqm hrm)
    filter_upwards [hb] with p hp
    exact (abs_binaryFusion_lt_one hp.1 hp.2).le
  · exact hfair .pos
  · rw [hpair .pos, hjoint]
    exact observationFusion_positive_product_eq_tilt hq hr hqm hrm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FusionSup
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance localInst_ra6648c_4 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem condExp_spin_comap_sup_eq_binaryFusion
    {Ω A B : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Ω → IsingSpin} {X : Ω → A} {Y : Ω → B}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hfair : ∀ a : IsingSpin, P {ω | S ω = a} = (1 / 2 : ENNReal))
    (hInd : X ⟂ᵢ[S, hS; P] Y)
    (hL : ∀ᵐ ω ∂P, |(P[fun ω => spinSign (S ω) | mA.comap X]) ω| < 1)
    (hR : ∀ᵐ ω ∂P, |(P[fun ω => spinSign (S ω) | mB.comap Y]) ω| < 1) :
    P[fun ω => spinSign (S ω) | mA.comap X ⊔ mB.comap Y] =ᵐ[P]
      fun ω => binaryFusion (P[fun ω => spinSign (S ω) | mA.comap X] ω)
        (P[fun ω => spinSign (S ω) | mB.comap Y] ω) := by
  obtain ⟨q, hq, hqe⟩ :=
    (show Measurable[mA.comap X]
      (P[fun ω => spinSign (S ω) | mA.comap X]) from
      stronglyMeasurable_condExp.measurable).exists_eq_measurable_comp
  obtain ⟨r, hr, hre⟩ :=
    (show Measurable[mB.comap Y]
      (P[fun ω => spinSign (S ω) | mB.comap Y]) from
      stronglyMeasurable_condExp.measurable).exists_eq_measurable_comp
  have hpostX : P[fun ω => spinSign (S ω) | mA.comap X] =ᵐ[P] fun ω => q (X ω) :=
    Filter.Eventually.of_forall (congrFun hqe)
  have hpostY : P[fun ω => spinSign (S ω) | mB.comap Y] =ᵐ[P] fun ω => r (Y ω) :=
    Filter.Eventually.of_forall (congrFun hre)
  have h := condExp_spin_given_observation_pair_eq_binaryFusion hS hX hY hq hr
    hpostX hpostY (by simpa only [hqe, Function.comp_apply] using hL)
    (by simpa only [hre, Function.comp_apply] using hR) hfair
    (fun a => indepFun_cond_fiber_of_condIndepFun hS hX hY hInd a)
  simpa only [Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
    hqe, hre, Function.comp_apply] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem condExp_tanh_bounds_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K)) :
    ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₁]) ω ∧
      (μ[f | m₁]) ω ≤ Real.tanh (X ω + K) := by
  have h₁ : m₁ ≤ m := h₁₂.trans h₂
  have hL : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω - K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.sub stronglyMeasurable_const)
  have hU : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω + K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.add stronglyMeasurable_const)
  have iL : Integrable (fun ω => Real.tanh (X ω - K)) μ := by
    apply Integrable.of_bound (hL.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω - K)).le
  have iU : Integrable (fun ω => Real.tanh (X ω + K)) μ := by
    apply Integrable.of_bound (hU.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω + K)).le
  have hlo := condExp_mono (m := m₁) iL integrable_condExp
    (hb.mono fun ω hω => hω.1)
  have hhi := condExp_mono (m := m₁) integrable_condExp iU
    (hb.mono fun ω hω => hω.2)
  rw [condExp_of_stronglyMeasurable h₁ hL iL] at hlo
  rw [condExp_of_stronglyMeasurable h₁ hU iU] at hhi
  filter_upwards [hlo, hhi, condExp_condExp_of_le (f := f) h₁₂ h₂] with ω hLω hUω hTω
  rw [hTω] at hLω hUω
  exact ⟨hLω, hUω⟩

theorem condExp_field_bound_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, (μ[f | m₂]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₂]) ω) - X ω| ≤ K) :
    ∀ᵐ ω ∂μ, (μ[f | m₁]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₁]) ω) - X ω| ≤ K := by
  have hmono : Monotone Real.tanh := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hasDerivAt_tanh_response x).differentiableAt
    · intro x
      rw [(hasDerivAt_tanh_response x).deriv]
      exact (sub_pos.mpr (Real.tanh_sq_lt_one x)).le
  have hs : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K) := by
    filter_upwards [hb] with ω hω
    have hlo := hmono (show X ω - K ≤ Real.artanh ((μ[f | m₂]) ω) by
      linarith [(abs_le.mp hω.2).1])
    have hhi := hmono (show Real.artanh ((μ[f | m₂]) ω) ≤ X ω + K by
      linarith [(abs_le.mp hω.2).2])
    rw [Real.tanh_artanh hω.1] at hlo hhi
    exact ⟨hlo, hhi⟩
  filter_upwards [condExp_tanh_bounds_of_le (m := m) μ h₁₂ h₂ hX hs] with ω hω
  have h := posterior_field_limit_of_tanh_bounds
    (u := fun _ : ℕ => (μ[f | m₁]) ω) tendsto_const_nhds (fun _ => hω)
  exact ⟨h.1, h.2.1⟩

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_bound
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) :
    ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p) -
          PlantedSymmetry.observation t p r| ≤ (d : ℝ) * β := by
  let := hμ.isProbabilityMeasure
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hsub : selectedObservationField F v ≤
      PlantedSymmetry.observationSigma (TreeVertex d) t := by
    change selectedObservationField F v ≤ selectedObservationField F id
    apply selectedObservationField_le_of_range_subset F
    intro w hw
    exact ⟨w, rfl⟩
  have hX : StronglyMeasurable[selectedObservationField F v]
      (fun p => PlantedSymmetry.observation t p r) := by
    obtain ⟨i, rfl⟩ := hr
    exact ((measurable_pi_apply i).comp (comap_measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun j => F (p.1 (v j)) (p.2 (v j))))).stronglyMeasurable
  exact condExp_field_bound_of_le
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hsub
    (PlantedSymmetry.observationSigma_le (TreeVertex d) t) hX
    (hμ.gaussian_posterior_field_bound hβ t r)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem exists_treeAut_to_root {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = ⟨[], List.IsChain.nil⟩ := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil => exact ⟨TreeAut.refl d, rfl⟩
  | cons a w ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.tail
    obtain ⟨g, hg⟩ := ih hw'
    refine ⟨(prefixTreeAut a).trans g, ?_⟩
    change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
    have hflip : prefixFlip a ⟨a :: w, hw⟩ = ⟨w, hw'⟩ := by
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord]
    rw [hflip]
    exact hg

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_StatisticSideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem statisticMessage_argument_mem {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    theta * q ∈ Set.Ioo (-1 : ℝ) 1 := by
  apply abs_lt.mp
  rw [abs_mul, abs_of_nonneg hθ0]
  exact (mul_le_mul_of_nonneg_left hq hθ0).trans_lt (by simpa using hθ1)

theorem statisticMessage_abs_le {theta q : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1) (hq : |q| ≤ 1) :
    |statisticMessage theta q| ≤ Real.artanh theta := by
  have hm := statisticMessage_argument_mem hθ0 hθ1 hq
  have hupper : Real.artanh (theta * q) ≤ Real.artanh theta := by
    apply Real.artanh_le_artanh hm.1 hθ1
    simpa using mul_le_mul_of_nonneg_left (abs_le.mp hq).2 hθ0
  have hneg : Real.artanh (-(theta * q)) ≤ Real.artanh theta := by
    apply Real.artanh_le_artanh (by linarith [hm.2]) hθ1
    nlinarith [(abs_le.mp hq).1]
  rw [artanh_neg_of_mem hm] at hneg
  exact abs_le.mpr ⟨by simpa only [statisticMessage, neg_neg] using (neg_le_neg hneg), hupper⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_LatentObservationIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_product_jointLaw
    {Ω S A B C D : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure Ω) [IsFiniteMeasure P]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Ω → S} {X : Ω → A} {Y : Ω → B}
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hjoint : Measure.map (fun ω => (Z ω, X ω, Y ω)) P = ρ.prod (μ.prod ν))
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap Z) hZ.comap_le
      (fun ω => F (Z ω, X ω)) (fun ω => G (Z ω, Y ω)) P := by
  have he : MeasurePreserving (fun ω => (Z ω, X ω, Y ω)) P (ρ.prod (μ.prod ν)) :=
    ⟨hZ.prodMk (hX.prodMk hY), hjoint⟩
  have hbase := condIndepFun_latent_product ρ μ ν F G hF hG
  have hpull := condIndepFun_comp_measurePreserving P (ρ.prod (μ.prod ν))
    (fun ω => (Z ω, X ω, Y ω)) he (mS.comap Prod.fst) measurable_fst.comap_le
    (show Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) by fun_prop)
    (show Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hpull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyRootIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_3_ra6648c_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem map_root_ownNoise_branch_family {d : ℕ} {A : Type*}
    [MeasurableSpace A] (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (fairSpin (U (root d)).1, (U (root d)).2,
          fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      (uniform01.map fairSpin).prod ((ν (root d)).prod
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))) := by
  have hbase := map_root_branch_family_of_sampler
    (fun v => uniform01.prod (ν v))
    (fun p : ℝ × A => (fairSpin p.1, p.2))
    ((measurable_fairSpin.comp measurable_fst).prodMk measurable_snd)
  have hroot : (uniform01.prod (ν (root d))).map
      (fun p : ℝ × A => (fairSpin p.1, p.2)) =
      (uniform01.map fairSpin).prod (ν (root d)) := by
    change (uniform01.prod (ν (root d))).map (Prod.map fairSpin id) = _
    rw [← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]
  rw [hroot] at hbase
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val))).map
          MeasurableEquiv.prodAssoc := by
      have hmf : Measurable (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1) :=
        (measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d))
      have hm : Measurable (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val)) :=
        (hmf.prodMk (by fun_prop)).prodMk (by fun_prop)
      rw [Measure.map_map (by fun_prop) hm]
      rfl
    _ = _ := by
      rw [hbase]
      exact (measurePreserving_prodAssoc (uniform01.map fairSpin) (ν (root d))
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))).map_eq

theorem condIndepFun_noisy_factor_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun U => (fairSpin (U (root d)).1, (U (root d)).2))
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let G : IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ × A) →
      (∀ c : Fin d, (BranchVertex c → IsingSpin) × (BranchVertex c → A)) :=
    fun p c => (branchFactor theta c (p.1, fun v => (p.2 c v).1),
      fun v => (p.2 c v).2)
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := condIndepFun_of_product_jointLaw
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    (uniform01.map fairSpin) (ν (root d))
    (Measure.infinitePi (fun c : Fin d =>
      Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))
    ((measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d)))
    (measurable_snd.comp (measurable_pi_apply (root d)))
    (show Measurable (fun U : TreeVertex d → ℝ × A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) from by fun_prop)
    (map_root_ownNoise_branch_family ν) id G measurable_id hG
  have hfun : (fun U : TreeVertex d → ℝ × A =>
      G (fairSpin (U (root d)).1, fun c v => U v.val)) =
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2)) := by
    funext U c
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  simpa only [Function.comp_def, id_eq, hfun] using h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem freeIsingMeasure_condIndepFun_noisy_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply condIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from by fun_prop)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun c : Fin d => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot (U : TreeVertex d → ℝ × A) :
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d) =
      fairSpin (U (RootedBroadcast.root d)).1 := by
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.condIndepFun_noisy_factor_root_branches theta ν

theorem HasFreeIsingLaw.condIndepFun_root_branch_observables
    {d : ℕ} {theta : ℝ} {A C D : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : IsingSpin × A → C)
    (G : (∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → D)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => F (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => G (fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val)))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact (freeIsingMeasure_condIndepFun_noisy_root_branches theta ν).comp hF hG

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin_3_ra6648c_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.measurePreserving_planted_relabel
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (ν : Measure A) [IsProbabilityMeasure ν]
    (g : TreeAut d) :
    MeasurePreserving (Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  apply (hμ.measurePreserving_relabel g).prod
  exact ⟨measurable_relabel g,
    Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchSeparation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_noisyBranchArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (noisyBranchArray (A := A) c) := by
  unfold noisyBranchArray
  fun_prop

theorem measurable_noisyRootOtherArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (noisyRootOtherArray (A := A) c) := by
  unfold noisyRootOtherArray noisyBranchArray
  fun_prop

local instance instMeasurableSingletonClassIsingSpin_4 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.condIndepFun_noisy_root_others_branch
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (noisyRootOtherArray c) (noisyBranchArray c)
      (μ.prod (Measure.infinitePi ν)) := by
  have hbranches : iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (noisyBranchArray (A := A)) (μ.prod (Measure.infinitePi ν)) :=
    hμ.iCondIndepFun_noisy_branches h0 h1 ν
  have hothers := (condIndepFun_coordinate_others
    (fun b => measurable_noisyBranchArray (A := A) b) hbranches c).symm
  have hroot := hμ.condIndepFun_root_branch_observables h0 h1 ν id
    (fun p => ((fun b : {b : Fin d // b ≠ c} => p b.val), p c))
    measurable_id (by fun_prop)
  exact condIndepFun_prodMk_left_of_joint
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from by fun_prop)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun b : {b : Fin d // b ≠ c} => noisyBranchArray b.val z) from
      Measurable.of_eval (fun b => measurable_noisyBranchArray b.val))
    (measurable_noisyBranchArray c) hroot hothers

theorem HasFreeIsingLaw.condIndepFun_relabel_noisy_root_others_branch
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (noisyRootOtherArray c ∘ Prod.map (relabel g) (relabel g))
      (noisyBranchArray c ∘ Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := condIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (measurable_noisyRootOtherArray c) (measurable_noisyBranchArray c)
    (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_BranchObservationRegression
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_noisyRootOtherDecode {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) (w : {w : TreeVertex d // ¬ [c] <+: w.val}) :
    Measurable (fun p : NoisyRootOtherData A c => noisyRootOtherDecode c p w) := by
  unfold noisyRootOtherDecode
  split_ifs <;> dsimp <;> fun_prop

theorem noisyRootOtherDecode_array {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A))
    (w : {w : TreeVertex d // ¬ [c] <+: w.val}) :
    noisyRootOtherDecode c (noisyRootOtherArray c z) w = (z.1 w.val, z.2 w.val) := by
  unfold noisyRootOtherDecode
  split_ifs with hw
  · have hroot : w.val = RootedBroadcast.root d := Subtype.ext hw
    simp only [noisyRootOtherArray, hroot]
  · rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem mem_range_componentIndexVertex {d : ℕ} {c : Fin d} {v : TreeVertex d} :
    v ∈ Set.range (componentIndexVertex (c := c)) ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨⟨n, w⟩, rfl⟩
    exact ⟨w.1, rfl⟩
  · rintro ⟨w, hw⟩
    have hchain : (c :: w).IsChain (fun a b : Fin d => a ≠ b) := by
      rw [← hw]
      exact v.2
    refine ⟨⟨w.length, ⟨w, rfl, hchain⟩⟩, ?_⟩
    exact Subtype.ext hw.symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideReroot
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem map_reachable_avoiding {d : ℕ} (g : TreeAut d)
    {p a b : TreeVertex d}
    (h : Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) := by
  induction h with
  | refl => exact .refl
  | tail h hxy ih =>
      exact ih.tail ⟨fun he => hxy.1 (g.toEquiv.injective he),
        fun he => hxy.2.1 (g.toEquiv.injective he), (g.map_adj _ _).mpr hxy.2.2⟩

theorem map_reachable_avoiding_iff {d : ℕ} (g : TreeAut d)
    (p a b : TreeVertex d) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b := by
  constructor
  · intro h
    have hm := map_reachable_avoiding g.symm h
    simpa only [TreeAut.symm, Equiv.symm_apply_apply] using hm
  · exact map_reachable_avoiding g

theorem mem_cone_iff_map_mem_root_branch {d : ℕ} (g : TreeAut d)
    (r : TreeVertex d) (hr : r.1 ≠ []) (c : Fin d)
    (hp : g.toEquiv (parentVertex r) = ConnectedHull.root d)
    (hc : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩) (u : TreeVertex d) :
    u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  let s : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hs : s.1 ≠ [] := by simp [s]
  have hparent : parentVertex s = ConnectedHull.root d := by
    apply Subtype.ext
    rfl
  have hmap := map_reachable_avoiding_iff g (parentVertex r) r u
  rw [hp, hc, ← hparent] at hmap
  rw [mem_cone_iff_reachable_avoiding_parent r u hr]
  change _ ↔ g.toEquiv u ∈ cone s
  rw [mem_cone_iff_reachable_avoiding_parent s (g.toEquiv u) hs]
  exact hmap.symm

theorem exists_reroot_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv (parentVertex r) = ConnectedHull.root d ∧
      g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root (parentVertex r)
  have hadj := (g.map_adj (parentVertex r) r).mpr (treeAdj_parentVertex hr)
  rw [hg] at hadj
  obtain ⟨c, hc⟩ : ∃ c : Fin d, (g.toEquiv r).1 = [c] := by
    rcases hadj with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by simpa using hc⟩
    · have hlen := congrArg List.length hc
      simp at hlen
  have hgr : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ := Subtype.ext hc
  exact ⟨g, c, hg, hgr, mem_cone_iff_map_mem_root_branch g r hr c hg hgr⟩

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyConeSeparation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

theorem measurable_decodeCone {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Measurable (decodeCone (A := A) g r c hgeo) := by
  unfold decodeCone
  fun_prop

theorem decodeCone_relabel {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    decodeCone g r c hgeo (noisyBranchArray c
      (Prod.map (relabel g) (relabel g) z)) = noisyRegionArray (cone r) z := by
  apply Prod.ext <;> funext u <;>
    simp [decodeCone, noisyBranchArray, noisyRegionArray, relabel]

theorem measurable_decodeConeComplement {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Measurable (decodeConeComplement (A := A) g r c hgeo) := by
  exact (Measurable.of_eval (fun vertex : {u : TreeVertex d // u ∉ cone r} =>
    (measurable_noisyRootOtherDecode c
      ⟨g.toEquiv vertex.1, fun hmem => vertex.2 ((hgeo vertex.1).mpr hmem)⟩).fst)).prodMk
    (Measurable.of_eval (fun vertex : {u : TreeVertex d // u ∉ cone r} =>
      (measurable_noisyRootOtherDecode c
        ⟨g.toEquiv vertex.1, fun hmem => vertex.2 ((hgeo vertex.1).mpr hmem)⟩).snd))

theorem decodeConeComplement_relabel {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    decodeConeComplement g r c hgeo (noisyRootOtherArray c
      (Prod.map (relabel g) (relabel g) z)) = noisyRegionArray (cone r)ᶜ z := by
  apply Prod.ext
  · funext u
    change (noisyRootOtherDecode c _ _).1 = _
    rw [noisyRootOtherDecode_array]
    simp [Prod.map, relabel, noisyRegionArray]
  · funext u
    change (noisyRootOtherDecode c _ _).2 = _
    rw [noisyRootOtherDecode_array]
    simp [Prod.map, relabel, noisyRegionArray]

end Problem367.PathSideBranches

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.condIndepFun_noisy_cone_complement
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex d) (hr : r.1 ≠ []) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (parentVertex r)))
      ((measurable_pi_apply (parentVertex r)).comp measurable_fst).comap_le
      (noisyRegionArray (cone r)ᶜ) (noisyRegionArray (cone r))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hroot : g.toEquiv.symm (RootedBroadcast.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
    rfl
  have h := (hμ.condIndepFun_relabel_noisy_root_others_branch h0 h1 ν g c).comp
    (measurable_decodeConeComplement g r c hgeo) (measurable_decodeCone g r c hgeo)
  classical
  simp only [hroot, Function.comp_def, decodeConeComplement_relabel,
    decodeCone_relabel] at h
  exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyPathLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

theorem measurable_restrictNoisyRegion {d : ℕ} {A : Type*} [MeasurableSpace A]
    {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    Measurable (restrictNoisyRegion (A := A) hST) := by
  unfold restrictNoisyRegion
  fun_prop

theorem measurable_noisyRegionArray_of_subset {d : ℕ} {A : Type*}
    [MeasurableSpace A] {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    Measurable[noisyRegionSigma (A := A) T] (noisyRegionArray (A := A) S) := by
  exact (measurable_restrictNoisyRegion hST).comp
    (comap_measurable (noisyRegionArray (A := A) T))

theorem noisyRegionSigma_mono {d : ℕ} {A : Type*} [MeasurableSpace A]
    {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    noisyRegionSigma (A := A) S ≤ noisyRegionSigma (A := A) T :=
  (measurable_noisyRegionArray_of_subset (A := A) hST).comap_le

end Problem367.PathSideBranches

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.condIndepFun_noisy_cone_observables
    {d : ℕ} {theta : ℝ} {A B C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex d) (hr : r.1 ≠ [])
    (X : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → B)
    (Q : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → C)
    (hX : Measurable[noisyRegionSigma (A := A) (cone r)ᶜ] X)
    (hQ : Measurable[noisyRegionSigma (A := A) (cone r)] Q) :
    CondIndepFun
      (isingSpinMeasurable.comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (parentVertex r)))
      ((measurable_pi_apply (parentVertex r)).comp measurable_fst).comap_le X Q
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  obtain ⟨F, hF, rfl⟩ := hX.exists_eq_measurable_comp
  obtain ⟨G, hG, rfl⟩ := hQ.exists_eq_measurable_comp
  exact (hμ.condIndepFun_noisy_cone_complement h0 h1 ν r hr).comp hF hG

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeComponentAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PathSideBranches

theorem range_relabel_componentIndexVertex_eq_cone
    {d : ℕ} (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Set.range (fun i => g.toEquiv.symm (componentIndexVertex (c := c) i)) =
      Set.range (Subtype.val : cone r → TreeVertex d) := by
  rw [Subtype.range_coe_subtype]
  ext u
  constructor
  · rintro ⟨i, rfl⟩
    apply (hgeo _).mpr
    simp only [Equiv.apply_symm_apply]
    change [c] <+: c :: i.2.1
    simp
  · intro hu
    have hp := (hgeo u).mp hu
    have hm : g.toEquiv u ∈ Set.range (componentIndexVertex (c := c)) := by
      apply mem_range_componentIndexVertex.mpr
      obtain ⟨w, hw⟩ := hp
      exact ⟨w, by simpa using hw.symm⟩
    obtain ⟨i, hi⟩ := hm
    refine ⟨i, ?_⟩
    change g.toEquiv.symm (componentIndexVertex i) = u
    rw [hi, Equiv.symm_apply_apply]

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ConePosteriorRegression
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.selectedPosterior_parent_cone
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (r : TreeVertex d) (hr : r.1 ≠ []) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : cone r → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => theta * selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hparent : g.toEquiv.symm (RootedBroadcast.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
    rfl
  have hchild : g.toEquiv.symm (RootedBroadcast.branchRoot c) = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hc]
    rfl
  have hfield := selectedObservationField_eq_of_range_eq F
    (range_relabel_componentIndexVertex_eq_cone g r c hgeo)
  have hb := hμ.selectedPosterior_root_component h0 h1 ν hF c
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ ν g
  have hbp := hmp.quasiMeasurePreserving.ae_eq_comp hb
  have hpull := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := c)) (RootedBroadcast.root d) g
  have hcpull := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) g
  filter_upwards [hbp, hpull, hcpull] with z hbz hpz hcz
  have h := hpz.symm.trans (hbz.trans (congrArg (fun q : ℝ => theta * q) hcz))
  simpa only [selectedPosterior, hfield, hparent, hchild] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SelectedPathLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

open PathSideBranches

theorem selectedObservationField_region_union {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (S T : Set (TreeVertex d)) :
    selectedObservationField F (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) =
      selectedObservationField F (Subtype.val : S → TreeVertex d) ⊔
        selectedObservationField F (Subtype.val : T → TreeVertex d) := by
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro u
    rcases u.2 with hu | hu
    · exact le_sup_of_le_left (le_iSup_of_le (⟨u.1, hu⟩ : S) le_rfl)
    · exact le_sup_of_le_right (le_iSup_of_le (⟨u.1, hu⟩ : T) le_rfl)
  · apply sup_le
    · apply iSup_le
      intro u
      exact le_iSup_of_le (⟨u.1, Or.inl u.2⟩ : ↥(S ∪ T)) le_rfl
    · apply iSup_le
      intro u
      exact le_iSup_of_le (⟨u.1, Or.inr u.2⟩ : ↥(S ∪ T)) le_rfl

theorem selectedObservationField_le_noisyRegionSigma {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (S : Set (TreeVertex d)) :
    selectedObservationField F (Subtype.val : S → TreeVertex d) ≤
      noisyRegionSigma (A := A) S := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
    noisyRegionSigma (A := A) S
  have hobs : Measurable[noisyRegionSigma (A := A) S]
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : S => F (z.1 u.1) (z.2 u.1)) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp ((((measurable_pi_apply u).comp measurable_fst).prodMk
      ((measurable_pi_apply u).comp measurable_snd)).comp
        (comap_measurable (noisyRegionArray (A := A) S)))
  exact hobs.comap_le

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeSubsetFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367
open PathSideBranches

theorem condExp_regression_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f g : Ω → ℝ} {theta : ℝ}
    (h : P[f | m₂] =ᵐ[P] fun z => theta * (P[g | m₂]) z) :
    P[f | m₁] =ᵐ[P] fun z => theta * (P[g | m₁]) z := by
  have hreg := condExp_congr_ae (m := m₁) h
  have hmul := condExp_smul (μ := P) theta (P[g | m₂]) m₁
  filter_upwards [hreg, hmul, condExp_condExp_of_le (f := f) h₁₂ h₂,
    condExp_condExp_of_le (f := g) h₁₂ h₂] with z hz hm hf hg
  simpa only [Pi.smul_apply, smul_eq_mul, hf, hg] using hz.trans hm

theorem HasFreeIsingLaw.selectedPosterior_parent_subset_cone
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (r : TreeVertex d) (hr : r.1 ≠ [])
    (T : Set (TreeVertex d)) (hT : T ⊆ cone r) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : T → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => theta * selectedPosterior P F (Subtype.val : T → TreeVertex d) r z := by
  let := hμ.isProbabilityMeasure
  have hle : selectedObservationField F (Subtype.val : T → TreeVertex d) ≤
      selectedObservationField F (Subtype.val : cone r → TreeVertex d) := by
    apply selectedObservationField_le_of_range_subset F
    rintro u ⟨v, rfl⟩
    exact ⟨⟨v.1, hT v.2⟩, rfl⟩
  exact condExp_regression_of_le _ hle
    (selectedObservationField_le hF (Subtype.val : cone r → TreeVertex d))
    (hμ.selectedPosterior_parent_cone h0 h1 ν hF r hr)

theorem HasFreeIsingLaw.selected_gaussian_outside_subset_cone_fusion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hT : T ⊆ cone r)
    (hp : parentVertex r ∈ S) (hq : r ∈ T) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    selectedPosterior P F (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => binaryFusion
        (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)
        (Real.tanh beta * selectedPosterior P F
          (Subtype.val : T → TreeVertex d) r z) := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let X := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : S => F (z.1 i.1) (z.2 i.1)
  let Y := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : T => F (z.1 i.1) (z.2 i.1)
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hXout : Measurable[noisyRegionSigma (A := ℝ) (cone r)ᶜ] X :=
    (comap_measurable X).mono
      ((selectedObservationField_le_noisyRegionSigma hF S).trans
        (noisyRegionSigma_mono hS)) le_rfl
  have hYin : Measurable[noisyRegionSigma (A := ℝ) (cone r)] Y :=
    (comap_measurable Y).mono
      ((selectedObservationField_le_noisyRegionSigma hF T).trans
        (noisyRegionSigma_mono hT)) le_rfl
  have hInd := hμ.condIndepFun_noisy_cone_observables
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) r hr X Y hXout hYin
  have hreg : selectedPosterior P F (Subtype.val : T → TreeVertex d)
      (parentVertex r) =ᵐ[P] fun z => Real.tanh beta *
        selectedPosterior P F (Subtype.val : T → TreeVertex d) r z :=
    hμ.selectedPosterior_parent_subset_cone
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) hF r hr T hT
  have hL : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hQ : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : T → TreeVertex d) r z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : T → TreeVertex d) r ⟨⟨r, hq⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hR : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : T → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hreg, hQ] with z hz hq
    rw [hz, abs_mul]
    exact (mul_le_mul_of_nonneg_left hq.le (abs_nonneg (Real.tanh beta))).trans_lt
      (by simpa using Real.abs_tanh_lt_one beta)
  have h := condExp_spin_comap_sup_eq_binaryFusion
    ((measurable_pi_apply (parentVertex r)).comp measurable_fst) hX hY
    (hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) _) hInd hL hR
  dsimp only
  unfold selectedPosterior
  rw [selectedObservationField_region_union]
  filter_upwards [h, hreg] with z hz hregz
  exact hz.trans (congrArg (binaryFusion
    (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)) hregz)

theorem HasFreeIsingLaw.selected_gaussian_outside_subset_cone_field
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hT : T ⊆ cone r)
    (hp : parentVertex r ∈ S) (hq : r ∈ T) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)) =ᵐ[P]
      fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) (parentVertex r) z) +
        statisticMessage (Real.tanh beta) (selectedPosterior P F
          (Subtype.val : T → TreeVertex d) r z) := by
  have h := hμ.selected_gaussian_outside_subset_cone_fusion hbeta t r hr S T hS hT hp hq
  have hL := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩
  have hQ := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : T → TreeVertex d) r ⟨⟨r, hq⟩, rfl⟩
  filter_upwards [h, hL, hQ] with z hz hl hq
  rw [hz]
  exact artanh_binaryFusion (abs_lt.mpr hl.1)
    (binaryFusion_abs_mul_lt_one (Real.abs_tanh_lt_one beta) (abs_lt.mpr hq.1))

theorem HasFreeIsingLaw.selected_gaussian_subset_cone_field_difference
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T U : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ)
    (hT : T ⊆ cone r) (hU : U ⊆ cone r)
    (hp : parentVertex r ∈ S) (ht : r ∈ T) (hu : r ∈ U) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    let field := fun (V : Set (TreeVertex d)) (u : TreeVertex d) z =>
      Real.artanh (selectedPosterior P F (Subtype.val : V → TreeVertex d) u z)
    ∀ᵐ z ∂P,
      |field (S ∪ T) (parentVertex r) z - field (S ∪ U) (parentVertex r) z| ≤
        Real.tanh beta * |field T r z - field U r z| ∧
      |field (S ∪ T) (parentVertex r) z - field (S ∪ U) (parentVertex r) z| ≤
        2 * beta := by
  have hFT := hμ.selected_gaussian_outside_subset_cone_field hbeta t r hr S T hS hT hp ht
  have hFU := hμ.selected_gaussian_outside_subset_cone_field hbeta t r hr S U hS hU hp hu
  have hQT := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : T → TreeVertex d) r ⟨⟨r, ht⟩, rfl⟩
  have hQU := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : U → TreeVertex d) r ⟨⟨r, hu⟩, rfl⟩
  have hθ0 : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  filter_upwards [hFT, hFU, hQT, hQU] with z hft hfu hqt hqu
  rw [hft, hfu, add_sub_add_left_eq_sub]
  constructor
  · have h := (lipschitzWith_cavityMessage hθ0 (Real.tanh_lt_one beta).le).dist_le_mul
      (Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (Subtype.val : T → TreeVertex d) r z))
      (Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (Subtype.val : U → TreeVertex d) r z))
    convert h using 1 <;>
      simp only [Real.dist_eq, cavityMessage, Real.tanh_artanh hqt.1,
        Real.tanh_artanh hqu.1, statisticMessage]
    rfl
  · have ht' := statisticMessage_abs_le hθ0 (Real.tanh_lt_one beta)
      (abs_lt.mpr hqt.1).le
    have hu' := statisticMessage_abs_le hθ0 (Real.tanh_lt_one beta)
      (abs_lt.mpr hqu.1).le
    rw [Real.artanh_tanh] at ht' hu'
    exact (abs_sub _ _).trans (by linarith)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeComplementFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.PathSideBranches

theorem prefixFlip_mem_branch_iff {d : ℕ} (c : Fin d) (u : TreeVertex d) :
    [c] <+: (prefixFlip c u).1 ↔ ¬ [c] <+: u.1 := by
  rcases u with ⟨w, hw⟩
  cases w with
  | nil => simp [prefixFlip, prefixFlipWord]
  | cons a w =>
    by_cases h : c = a
    · subst a
      cases w with
      | nil => simp [prefixFlip, prefixFlipWord]
      | cons b w =>
        have hcb : c ≠ b := (List.isChain_cons_cons.mp hw).1
        simp [prefixFlip, prefixFlipWord, hcb]
    · simp [prefixFlip, prefixFlipWord, h]

theorem exists_reroot_cone_complement {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv r = ConnectedHull.root d ∧
      g.toEquiv (parentVertex r) = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∉ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  refine ⟨g.trans (prefixTreeAut c), c, ?_, ?_, ?_⟩
  · change prefixFlip c (g.toEquiv r) = _
    rw [hc]
    apply Subtype.ext
    simp [prefixFlip, prefixFlipWord, ConnectedHull.root]
  · change prefixFlip c (g.toEquiv (parentVertex r)) = _
    rw [hp]
    rfl
  · intro u
    change u ∉ cone r ↔ [c] <+: (prefixFlip c (g.toEquiv u)).1
    rw [prefixFlip_mem_branch_iff, hgeo]
end Problem367.PathSideBranches

namespace Problem367
open PathSideBranches

theorem selectedPosterior_image_relabel_ae
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (g : TreeAut d) (S : Set (TreeVertex d)) (r : TreeVertex d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : g.toEquiv '' S → TreeVertex d) (g.toEquiv r) ∘
      Prod.map (relabel g) (relabel g) =ᵐ[P]
      selectedPosterior P F (Subtype.val : S → TreeVertex d) r := by
  have heq : Set.range (fun i : g.toEquiv '' S => g.toEquiv.symm i.1) =
      Set.range (Subtype.val : S → TreeVertex d) := by
    ext u
    constructor
    · rintro ⟨⟨v, ⟨x, hx, rfl⟩⟩, rfl⟩
      exact ⟨⟨x, hx⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨g.toEquiv x.1, ⟨x.1, x.2, rfl⟩⟩, by simp⟩
  have hfield := selectedObservationField_eq_of_range_eq F heq
  have h := selectedPosterior_relabel_ae hμ ν hF
    (Subtype.val : g.toEquiv '' S → TreeVertex d) (g.toEquiv r) g
  simpa only [selectedPosterior, hfield, Equiv.symm_apply_apply] using h

theorem HasFreeIsingLaw.selected_gaussian_subset_complement_field_difference
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T U : Set (TreeVertex d)) (hS : S ⊆ cone r)
    (hT : T ⊆ (cone r)ᶜ) (hU : U ⊆ (cone r)ᶜ)
    (hp : r ∈ S) (ht : parentVertex r ∈ T) (hu : parentVertex r ∈ U) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    let field := fun (V : Set (TreeVertex d)) (u : TreeVertex d) z =>
      Real.artanh (selectedPosterior P F (Subtype.val : V → TreeVertex d) u z)
    ∀ᵐ z ∂P,
      |field (S ∪ T) r z - field (S ∪ U) r z| ≤
        Real.tanh beta * |field T (parentVertex r) z - field U (parentVertex r) z| ∧
      |field (S ∪ T) r z - field (S ∪ U) r z| ≤ 2 * beta := by
  obtain ⟨g, c, hr0, hpc, hgeo⟩ := exists_reroot_cone_complement r hr
  let q : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hq : q.1 ≠ [] := by simp [q]
  have hpq : parentVertex q = ConnectedHull.root d := by rfl
  have hS' : g.toEquiv '' S ⊆ (cone q)ᶜ := by
    rintro u ⟨v, hv, rfl⟩ hbad
    exact ((hgeo v).mpr hbad) (hS hv)
  have hT' : g.toEquiv '' T ⊆ cone q := by
    rintro u ⟨v, hv, rfl⟩
    exact (hgeo v).mp (hT hv)
  have hU' : g.toEquiv '' U ⊆ cone q := by
    rintro u ⟨v, hv, rfl⟩
    exact (hgeo v).mp (hU hv)
  have hp' : parentVertex q ∈ g.toEquiv '' S := ⟨r, hp, hr0.trans hpq.symm⟩
  have ht' : q ∈ g.toEquiv '' T := ⟨parentVertex r, ht, hpc⟩
  have hu' : q ∈ g.toEquiv '' U := ⟨parentVertex r, hu, hpc⟩
  have hbase := hμ.selected_gaussian_subset_cone_field_difference hbeta t q hq
    (g.toEquiv '' S) (g.toEquiv '' T) (g.toEquiv '' U) hS' hT' hU' hp' ht' hu'
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hb := hmp.quasiMeasurePreserving.ae hbase
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hST := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g (S ∪ T) r
  have hSU := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g (S ∪ U) r
  have hTT := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g T (parentVertex r)
  have hUU := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g U (parentVertex r)
  filter_upwards [hb, hST, hSU, hTT, hUU] with z hz hst hsu htt huu
  have hpc' : g.toEquiv (parentVertex r) = q := hpc
  rw [hpq, ← hr0, ← hpc', ← Set.image_union, ← Set.image_union] at hz
  simp only [Function.comp_apply] at hst hsu htt huu
  dsimp only [F, PlantedSymmetry.gaussianNoiseLaw] at hst hsu htt huu hz ⊢
  simpa only [hst, hsu, htt, huu] using hz

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCutCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace PathCutCost

theorem abs_sub_le_geometric
    {x y : ℕ → ℝ} {q B : ℝ} (hq : 0 ≤ q)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ n, |x (n + 1) - y (n + 1)| ≤ q * |x n - y n|) :
    ∀ n, |x n - y n| ≤ B * q ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    calc
      |x (n + 1) - y (n + 1)| ≤ q * |x n - y n| := hstep n
      _ ≤ q * (B * q ^ n) := mul_le_mul_of_nonneg_left ih hq
      _ = B * q ^ (n + 1) := by rw [pow_succ]; ring

theorem sum_abs_sub_le
    {x y : ℕ → ℝ} {q B : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ n, |x (n + 1) - y (n + 1)| ≤ q * |x n - y n|) (n : ℕ) :
    (∑ i ∈ Finset.range n, |x i - y i|) ≤ B / (1 - q) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hzero
  have hgeom : (∑ i ∈ Finset.range n, q ^ i) ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    rw [geom_sum_mul_of_le_one hq1.le]
    exact sub_le_self _ (pow_nonneg hq n)
  calc
    (∑ i ∈ Finset.range n, |x i - y i|) ≤ ∑ i ∈ Finset.range n, B * q ^ i :=
      Finset.sum_le_sum (fun i _ => abs_sub_le_geometric hq hzero hstep i)
    _ = B * ∑ i ∈ Finset.range n, q ^ i := (Finset.mul_sum ..).symm
    _ ≤ B * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom hB
    _ = B / (1 - q) := by ring

theorem abs_log_prod_sq_ratio_le {ι : Type*} (s : Finset ι)
    {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i) :
    |Real.log ((∏ i ∈ s, a i ^ 2) / (∏ i ∈ s, b i ^ 2))| ≤
      2 * ∑ i ∈ s, |Real.log (a i) - Real.log (b i)| := by
  have hA : (∏ i ∈ s, a i ^ 2) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i hi => pow_pos (ha i hi) _))
  have hB : (∏ i ∈ s, b i ^ 2) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i hi => pow_pos (hb i hi) _))
  have hlog : Real.log ((∏ i ∈ s, a i ^ 2) / (∏ i ∈ s, b i ^ 2)) =
      2 * ∑ i ∈ s, (Real.log (a i) - Real.log (b i)) := by
    rw [Real.log_div hA hB,
      Real.log_prod (fun i hi => pow_ne_zero _ (ha i hi).ne'),
      Real.log_prod (fun i hi => pow_ne_zero _ (hb i hi).ne')]
    simp_rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hlog, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)

theorem abs_log_attenuation_prod_ratio_le
    {x y : ℕ → ℝ} {theta q B : ℝ} (htheta : theta ^ 2 ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ i, |x (i + 1) - y (i + 1)| ≤ q * |x i - y i|) (n : ℕ) :
    |Real.log ((∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) /
      (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2))| ≤
      4 * B / (1 - q) := by
  have hloglip : ∀ i, |Real.log (responseAttenuation theta (x i)) -
      Real.log (responseAttenuation theta (y i))| ≤ 2 * |x i - y i| := by
    intro i
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using
      (lipschitzWith_log_responseAttenuation htheta).dist_le_mul (x i) (y i)
  calc
    _ ≤ 2 * ∑ i ∈ Finset.range n,
        |Real.log (responseAttenuation theta (x i)) -
          Real.log (responseAttenuation theta (y i))| :=
      abs_log_prod_sq_ratio_le _ (fun i _ => responseAttenuation_pos htheta (x i))
        (fun i _ => responseAttenuation_pos htheta (y i))
    _ ≤ 2 * ∑ i ∈ Finset.range n, 2 * |x i - y i| :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hloglip i)) (by norm_num)
    _ = 4 * ∑ i ∈ Finset.range n, |x i - y i| := by rw [← Finset.mul_sum]; ring
    _ ≤ 4 * (B / (1 - q)) :=
      mul_le_mul_of_nonneg_left (sum_abs_sub_le hq hq1 hzero hstep n) (by norm_num)
    _ = 4 * B / (1 - q) := by ring

theorem attenuation_prod_le_exp_mul
    {x y : ℕ → ℝ} {theta q B : ℝ} (htheta : theta ^ 2 ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ i, |x (i + 1) - y (i + 1)| ≤ q * |x i - y i|) (n : ℕ) :
    (∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) ≤
      Real.exp (4 * B / (1 - q)) *
        (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2) := by
  have hA : 0 < ∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2 :=
    Finset.prod_pos (fun i _ => pow_pos (responseAttenuation_pos htheta (x i)) _)
  have hB : 0 < ∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2 :=
    Finset.prod_pos (fun i _ => pow_pos (responseAttenuation_pos htheta (y i)) _)
  apply (div_le_iff₀ hB).mp
  apply (Real.log_le_iff_le_exp (div_pos hA hB)).mp
  exact (le_abs_self _).trans (abs_log_attenuation_prod_ratio_le htheta hq hq1 hzero hstep n)

end PathCutCost
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InwardCutFields
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches
open ConnectedHull

theorem cone_takeVertex_antitone {d : ℕ} (v : TreeVertex d) {i j : ℕ}
    (hij : i ≤ j) : cone (takeVertex v j) ⊆ cone (takeVertex v i) := by
  apply cone_mono
  exact List.take_isPrefix_take.mpr (Or.inl hij)

theorem parent_takeVertex_succ {d : ℕ} (v : TreeVertex d) {i : ℕ}
    (hi : i < v.1.length) : parentVertex (takeVertex v (i + 1)) = takeVertex v i := by
  apply treeAdj_parent_of_length_lt (prefix_adj v hi)
  simp only [takeVertex, List.length_take, Nat.min_eq_left hi.le,
    Nat.min_eq_left (show i + 1 ≤ v.1.length by omega)]
  omega

theorem takeVertex_not_mem_next_cone {d : ℕ} (v : TreeVertex d) {i : ℕ}
    (hi : i < v.1.length) : takeVertex v i ∉ cone (takeVertex v (i + 1)) := by
  intro h
  have hl := h.length_le
  simp only [takeVertex, List.length_take, Nat.min_eq_left hi.le,
    Nat.min_eq_left (show i + 1 ≤ v.1.length by omega)] at hl
  omega

private theorem takeVertex_succ_ne_nil {d : ℕ} (v : TreeVertex d) {i : ℕ}
    (hi : i < v.1.length) : (takeVertex v (i + 1)).1 ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [takeVertex, List.length_take,
    Nat.min_eq_left (show i + 1 ≤ v.1.length by omega), List.length_nil] at hl
  omega

private theorem diff_union_compl_of_subset {α : Type*} {A B : Set α}
    (hBA : B ⊆ A) : (A \ B) ∪ Aᶜ = Bᶜ := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff]
  constructor
  · rintro (h | h)
    · exact h.2
    · exact fun hb => h (hBA hb)
  · intro hb
    by_cases ha : x ∈ A
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ha

private theorem diff_union_diff_of_subset {α : Type*} {A B C : Set α}
    (hBA : B ⊆ A) (hAC : A ⊆ C) : (A \ B) ∪ (C \ A) = C \ B := by
  ext x
  simp only [Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro (h | h)
    · exact ⟨hAC h.1, h.2⟩
    · exact ⟨h.1, fun hb => h.2 (hBA hb)⟩
  · rintro ⟨hc, hb⟩
    by_cases ha : x ∈ A
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨hc, ha⟩

theorem inward_cut_difference_step {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {k i : ℕ}
    (hki : k ≤ i) (hi : i + 1 < v.1.length) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      |inwardGaussianField μ t v (i + 1) z -
        cutInwardGaussianField μ t v k (i + 1) z| ≤
      Real.tanh beta * |inwardGaussianField μ t v i z -
        cutInwardGaussianField μ t v k i z| := by
  let A := cone (takeVertex v (i + 1))
  let B := cone (takeVertex v (i + 1 + 1))
  let C := cone (takeVertex v k)
  have hBA : B ⊆ A := cone_takeVertex_antitone v (by omega)
  have hAC : A ⊆ C := cone_takeVertex_antitone v (by omega)
  have hpA : takeVertex v i ∉ A := takeVertex_not_mem_next_cone v (by omega)
  have hpC : takeVertex v i ∈ C := List.take_isPrefix_take.mpr (Or.inl hki)
  have hrS : takeVertex v (i + 1) ∈ A \ B :=
    ⟨List.prefix_refl _, takeVertex_not_mem_next_cone v hi⟩
  have h := hμ.selected_gaussian_subset_complement_field_difference hbeta t
    (takeVertex v (i + 1)) (takeVertex_succ_ne_nil v (by omega))
    (A \ B) Aᶜ (C \ A) Set.sdiff_subset (fun _ hx => hx) (fun _ hx => hx.2)
    hrS (by rw [parent_takeVertex_succ v (by omega)]; exact hpA)
    (by rw [parent_takeVertex_succ v (by omega)]; exact ⟨hpC, hpA⟩)
  have hST : (A \ B) ∪ Aᶜ = Bᶜ := diff_union_compl_of_subset hBA
  have hSU : (A \ B) ∪ (C \ A) = C \ B := diff_union_diff_of_subset hBA hAC
  filter_upwards [h] with z hz
  have hz' := hz.1
  change |regionGaussianField μ t ((A \ B) ∪ Aᶜ) (takeVertex v (i + 1)) z -
    regionGaussianField μ t ((A \ B) ∪ (C \ A)) (takeVertex v (i + 1)) z| ≤
    Real.tanh beta * |regionGaussianField μ t Aᶜ
      (parentVertex (takeVertex v (i + 1))) z -
      regionGaussianField μ t (C \ A) (parentVertex (takeVertex v (i + 1))) z| at hz'
  rw [hST, hSU, parent_takeVertex_succ v (by omega)] at hz'
  exact hz'

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_InwardGaussianCutChannels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.InwardCutChannels

open PathSideBranches CutContinuationChannels ConnectedHull

theorem inwardContinuationProduct_Ico_eq_range {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    inwardContinuationProduct μ t theta p w (Finset.Ico (k + 1) (k + 1 + L)) z =
      ∏ j ∈ Finset.range L, responseAttenuation theta
        (cutInwardGaussianField μ t (appendCutContinuation p w).1
          (k + 1) (k + 1 + j) z) ^ 2 := by
  simp only [inwardContinuationProduct, Finset.prod_Ico_eq_prod_range,
    Nat.add_sub_cancel_left]

theorem takeVertex_appendCutContinuation {d k L : ℕ}
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    takeVertex (appendCutContinuation p w).1 (k + 1) = p.1 := by
  apply Subtype.ext
  simp [takeVertex, appendCutContinuation, p.2]

private theorem inward_region_subset_cut {d k L : ℕ}
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (i : ℕ) :
    cone (takeVertex (appendCutContinuation p w).1 (k + 1)) \
        cone (takeVertex (appendCutContinuation p w).1 (i + 1)) ⊆ cone p.1 := by
  rw [takeVertex_appendCutContinuation]
  exact Set.sdiff_subset

private theorem reducedTail_nonempty {d k : ℕ} (hd : 2 ≤ d)
    (p : TreeShell d (k + 1)) (L : ℕ) :
    Nonempty (ReducedTail (cutLastColor p) L) := by
  apply Fintype.card_pos_iff.mp
  rw [card_reducedTail]
  exact pow_pos (by omega : 0 < d - 1) L

theorem exists_inwardContinuationAverage_channel {d k : ℕ} (hd : 2 ≤ d)
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    (p : TreeShell d (k + 1)) (L : ℕ) (s : Finset ℕ) :
    ∃ g : ConeSample ℝ p.1 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ z, inwardContinuationAverage μ t theta p L s z = g (globalCone p.1 z) := by
  let := reducedTail_nonempty hd p L
  have hF : Measurable (Function.uncurry (fun a x => (t : ℝ) * spinSign a + x)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  exact exists_regionAverage_channel
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hF hθ p.1
    (fun w i => cone (takeVertex (appendCutContinuation p w).1 (k + 1)) \
      cone (takeVertex (appendCutContinuation p w).1 (i + 1)))
    (fun w i => takeVertex (appendCutContinuation p w).1 i)
    (fun _ => s) (inward_region_subset_cut p)

end Problem367.InwardCutChannels

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_InwardProducts
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367
open PathSideBranches

theorem gaussianInwardConeFactor_mem_Icc {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) {theta : ℝ}
    (hθ : theta ^ 2 ≤ 1) (z) (v : TreeVertex d) :
    gaussianInwardConeFactor μ t theta z v ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := responseAttenuation_pos hθ
    (regionGaussianField μ t (cone v)ᶜ (parentVertex v) z)
  have hl := responseAttenuation_le_one hθ
    (regionGaussianField μ t (cone v)ᶜ (parentVertex v) z)
  exact ⟨sq_nonneg _, by unfold gaussianInwardConeFactor; nlinarith⟩

theorem gaussianInwardConeFactor_rootPathVertex {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (v : TreeVertex d) {i : ℕ} (hi : i < v.1.length) (z) :
    gaussianInwardConeFactor μ t theta z (rootPathVertex v (i + 1)) =
      responseAttenuation theta (inwardGaussianField μ t v i z) ^ 2 := by
  change responseAttenuation theta (regionGaussianField μ t
    (cone (ConnectedHull.takeVertex v (i + 1)))ᶜ
    (parentVertex (ConnectedHull.takeVertex v (i + 1))) z) ^ 2 = _
  rw [parent_takeVertex_succ v hi]
  rfl

theorem cutContinuationProduct_gaussianInwardConeFactor {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (z) :
    cutContinuationProduct (gaussianInwardConeFactor μ t theta z) p w =
      ∏ j ∈ Finset.range L, responseAttenuation theta
        (inwardGaussianField μ t (appendCutContinuation p w).1 (k + 1 + j) z) ^ 2 := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [← Nat.add_assoc]
  apply gaussianInwardConeFactor_rootPathVertex
  rw [(appendCutContinuation p w).2]
  exact Nat.add_lt_add_left (Finset.mem_range.mp hj) _

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FinitePathCutCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Problem367.PathCutCost

theorem attenuation_prod_le_exp_mul_of_finite_contraction
    {x y : ℕ → ℝ} {theta q B : ℝ} (n : ℕ)
    (htheta : theta ^ 2 ≤ 1) (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ i, i + 1 < n →
      |x (i + 1) - y (i + 1)| ≤ q * |x i - y i|) :
    (∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) ≤
      Real.exp (4 * B / (1 - q)) *
        (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2) := by
  let X : ℕ → ℝ := fun i => if i < n then x i else 0
  let Y : ℕ → ℝ := fun i => if i < n then y i else 0
  have hB : 0 ≤ B := (abs_nonneg _).trans hzero
  have hzero' : |X 0 - Y 0| ≤ B := by
    by_cases hn : 0 < n
    · simpa only [X, Y, ite_eq_left hn] using hzero
    · simpa only [X, Y, ite_eq_right hn, sub_self, abs_zero] using hB
  have hstep' : ∀ i, |X (i + 1) - Y (i + 1)| ≤ q * |X i - Y i| := by
    intro i
    by_cases hi : i + 1 < n
    · have hi' : i < n := by omega
      simpa only [X, Y, ite_eq_left hi, ite_eq_left hi'] using hstep i hi
    · simp only [X, Y, ite_eq_right hi, sub_self, abs_zero]
      exact mul_nonneg hq (abs_nonneg _)
  have h := attenuation_prod_le_exp_mul htheta hq hq1 hzero' hstep' n
  have hx : (∏ i ∈ Finset.range n, responseAttenuation theta (X i) ^ 2) =
      ∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [X, ite_eq_left (Finset.mem_range.mp hi)]
  have hy : (∏ i ∈ Finset.range n, responseAttenuation theta (Y i) ^ 2) =
      ∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Y, ite_eq_left (Finset.mem_range.mp hi)]
  rw [hx, hy] at h
  exact h

end Problem367.PathCutCost

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeComplementField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367
open PathSideBranches

theorem HasFreeIsingLaw.selected_gaussian_inside_subset_complement_field
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T : Set (TreeVertex d)) (hS : S ⊆ cone r) (hT : T ⊆ (cone r)ᶜ)
    (hp : r ∈ S) (ht : parentVertex r ∈ T) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) r z)) =ᵐ[P]
      fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) r z) +
        statisticMessage (Real.tanh beta) (selectedPosterior P F
          (Subtype.val : T → TreeVertex d) (parentVertex r) z) := by
  obtain ⟨g, c, hr0, hpc, hgeo⟩ := exists_reroot_cone_complement r hr
  let q : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hq : q.1 ≠ [] := by simp [q]
  have hpq : parentVertex q = ConnectedHull.root d := by rfl
  have hS' : g.toEquiv '' S ⊆ (cone q)ᶜ := by
    rintro u ⟨v, hv, rfl⟩ hbad
    exact ((hgeo v).mpr hbad) (hS hv)
  have hT' : g.toEquiv '' T ⊆ cone q := by
    rintro u ⟨v, hv, rfl⟩
    exact (hgeo v).mp (hT hv)
  have hp' : parentVertex q ∈ g.toEquiv '' S := ⟨r, hp, hr0.trans hpq.symm⟩
  have ht' : q ∈ g.toEquiv '' T := ⟨parentVertex r, ht, hpc⟩
  have hbase := hμ.selected_gaussian_outside_subset_cone_field hbeta t q hq
    (g.toEquiv '' S) (g.toEquiv '' T) hS' hT' hp' ht'
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hb := hmp.quasiMeasurePreserving.ae_eq_comp hbase
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hST := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g (S ∪ T) r
  have hSS := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g S r
  have hTT := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g T (parentVertex r)
  filter_upwards [hb, hST, hSS, hTT] with z hz hst hss htt
  have hpc' : g.toEquiv (parentVertex r) = q := hpc
  rw [hpq, ← hr0, ← hpc', ← Set.image_union] at hz
  simp only [Function.comp_apply] at hst hss htt
  dsimp only [F, PlantedSymmetry.gaussianNoiseLaw] at hst hss htt hz ⊢
  simpa only [Function.comp_apply, hst, hss, htt] using hz

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InwardCutCost
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches
open ConnectedHull

private theorem tanh_nonneg {beta : ℝ} (hb : 0 ≤ beta) : 0 ≤ Real.tanh beta := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hb) (Real.cosh_pos beta).le

theorem inward_cut_difference_initial_sharp {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {k : ℕ} (hk : k < v.1.length) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      |inwardGaussianField μ t v k z - cutInwardGaussianField μ t v k k z| ≤ beta := by
  by_cases hk0 : k = 0
  · subst k
    have hcone : cone (takeVertex v 0) = Set.univ := by
      ext u
      simp [cone, takeVertex]
    filter_upwards [] with z
    simp only [inwardGaussianField, cutInwardGaussianField, hcone,
      Set.compl_eq_univ_sdiff, sub_self, abs_zero]
    exact hbeta
  · let A := cone (takeVertex v k)
    let B := cone (takeVertex v (k + 1))
    have hBA : B ⊆ A := cone_takeVertex_antitone v (by omega)
    have hr : (takeVertex v k).1 ≠ [] := by
      intro h
      have hl := congrArg List.length h
      simp only [takeVertex, List.length_take, Nat.min_eq_left hk.le,
        List.length_nil] at hl
      omega
    have hparent : parentVertex (takeVertex v k) ∈ Aᶜ := parent_not_mem_cone _ hr
    have hroot : takeVertex v k ∈ A \ B :=
      ⟨List.prefix_refl _, takeVertex_not_mem_next_cone v hk⟩
    have heq : (A \ B) ∪ Aᶜ = Bᶜ := by
      ext u
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff]
      constructor
      · rintro (h | h)
        · exact h.2
        · exact fun hb => h (hBA hb)
      · intro hb
        by_cases ha : u ∈ A
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr ha
    have hfield := hμ.selected_gaussian_inside_subset_complement_field hbeta t
      (takeVertex v k) hr (A \ B) Aᶜ Set.sdiff_subset (fun _ h => h) hroot hparent
    have hbound := hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : (Aᶜ : Set (TreeVertex d)) → TreeVertex d)
      (parentVertex (takeVertex v k)) ⟨⟨_, hparent⟩, rfl⟩
    filter_upwards [hfield, hbound] with z hf hb
    change regionGaussianField μ t ((A \ B) ∪ Aᶜ) (takeVertex v k) z =
      regionGaussianField μ t (A \ B) (takeVertex v k) z + _ at hf
    rw [heq] at hf
    change inwardGaussianField μ t v k z = cutInwardGaussianField μ t v k k z + _ at hf
    rw [hf, add_sub_cancel_left]
    simpa only [Real.artanh_tanh] using
      statisticMessage_abs_le (tanh_nonneg hbeta) (Real.tanh_lt_one beta) (abs_lt.mpr hb.1).le

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InwardCutProducts
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Problem367.PathSideBranches

theorem inward_attenuation_prod_le_cut {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) (k n : ℕ) (hkn : k + n ≤ v.1.length) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      (∏ i ∈ Finset.range n, responseAttenuation (Real.tanh beta)
        (inwardGaussianField μ t v (k + i) z) ^ 2) ≤
      Real.exp (4 * beta / (1 - Real.tanh beta)) *
        (∏ i ∈ Finset.range n, responseAttenuation (Real.tanh beta)
          (cutInwardGaussianField μ t v k (k + i) z) ^ 2) := by
  have hq0 : 0 ≤ Real.tanh beta := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hbeta) (Real.cosh_pos beta).le
  have hq1 := Real.tanh_lt_one beta
  have htheta : Real.tanh beta ^ 2 ≤ 1 := by
    nlinarith [mul_self_le_mul_self hq0 hq1.le]
  by_cases hn : n = 0
  · subst n
    filter_upwards [] with z
    simpa only [Finset.range_zero, Finset.prod_empty, mul_one] using
      Real.one_le_exp (show 0 ≤ 4 * beta / (1 - Real.tanh beta) by positivity)
  · have hk : k < v.1.length := by omega
    have hz := inward_cut_difference_initial_sharp hμ hbeta t v hk
    have hs : ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
        ∀ i : ℕ, i + 1 < n →
          |inwardGaussianField μ t v (k + i + 1) z -
            cutInwardGaussianField μ t v k (k + i + 1) z| ≤
          Real.tanh beta * |inwardGaussianField μ t v (k + i) z -
            cutInwardGaussianField μ t v k (k + i) z| := by
      apply ae_all_iff.mpr
      intro i
      by_cases hi : i + 1 < n
      · filter_upwards [inward_cut_difference_step hμ hbeta t v
          (k := k) (i := k + i) (by omega) (by omega)] with z h
        exact fun _ => h
      · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
    filter_upwards [hz, hs] with z hzero hstep
    apply PathCutCost.attenuation_prod_le_exp_mul_of_finite_contraction n
      htheta hq0 hq1
    · simpa only [Nat.add_zero] using hzero
    · intro i hi
      simpa only [Nat.add_assoc] using hstep i hi

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_InwardCutConcentration
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
open PathSideBranches InwardCutChannels CutContinuationChannels

theorem cutContinuationProduct_gaussianInwardConeFactor_le_cut {d k L : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      cutContinuationProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) p w ≤
        Real.exp (4 * beta / (1 - Real.tanh beta)) *
          inwardContinuationProduct μ t (Real.tanh beta) p w
            (Finset.Ico (k + 1) (k + 1 + L)) z := by
  have h := inward_attenuation_prod_le_cut hμ hbeta t
    (appendCutContinuation p w).1 (k + 1) L (by
      rw [(appendCutContinuation p w).2])
  simpa only [cutContinuationProduct_gaussianInwardConeFactor,
    inwardContinuationProduct_Ico_eq_range] using h

theorem average_gaussianInwardConeFactor_le_cut_average {d k : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (I : Finset (TreeShell d (k + 1))) (L : ℕ) :
    ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      (∑ v ∈ cutDescendants I L,
        rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v.1) /
          ((cutDescendants I L).card : ℝ) ≤
      Real.exp (4 * beta / (1 - Real.tanh beta)) *
        ((∑ p ∈ I, inwardContinuationAverage μ t (Real.tanh beta) p L
          (Finset.Ico (k + 1) (k + 1 + L)) z) / (I.card : ℝ)) := by
  have hθ0 := tanh_nonneg_of_beta_nonneg hbeta
  have hθ1 := Real.tanh_lt_one beta
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  have hcut : ∀ᵐ z ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      ∀ p : TreeShell d (k + 1), ∀ w : ReducedTail (cutLastColor p) L,
      cutContinuationProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) p w ≤
        Real.exp (4 * beta / (1 - Real.tanh beta)) *
          inwardContinuationProduct μ t (Real.tanh beta) p w
            (Finset.Ico (k + 1) (k + 1 + L)) z :=
    ae_all_iff.mpr (fun p => ae_all_iff.mpr (fun w =>
      cutContinuationProduct_gaussianInwardConeFactor_le_cut hμ hbeta t p w))
  filter_upwards [hcut] with z hz
  refine (average_rootPathProduct_le_continuation_average
    (gaussianInwardConeFactor μ t (Real.tanh beta) z)
    (fun v => gaussianInwardConeFactor_mem_Icc μ t hθ z v) I L).trans ?_
  calc
    _ ≤ (∑ p ∈ I, (∑ w : ReducedTail (cutLastColor p) L,
        Real.exp (4 * beta / (1 - Real.tanh beta)) *
          inwardContinuationProduct μ t (Real.tanh beta) p w
            (Finset.Ico (k + 1) (k + 1 + L)) z) /
          (((d - 1) ^ L : ℕ) : ℝ)) / (I.card : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun w _ => hz p w)
    _ = _ := by
      simp only [inwardContinuationAverage, card_reducedTail,
        ← Finset.mul_sum, mul_div_assoc]

theorem measure_gaussian_inward_path_average_ge_le_oai {d k : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 2 ≤ d)
    (t : ℝ≥0) (I : Finset (TreeShell d (k + 1))) (hI : I.Nonempty) (L : ℕ)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ p ∈ I, (∫ z, inwardContinuationAverage μ t (Real.tanh beta) p L
      (Finset.Ico (k + 1) (k + 1 + L)) z
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤ τ / 4) :
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      {z | Real.exp (4 * beta / (1 - Real.tanh beta)) * τ ≤
        (∑ v ∈ cutDescendants I L,
          rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v.1) /
            ((cutDescendants I L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  classical
  let := hμ.isProbabilityMeasure
  have hθ0 := tanh_nonneg_of_beta_nonneg hbeta
  have hθ1 := Real.tanh_lt_one beta
  have hθ : Real.tanh beta ^ 2 ≤ 1 := by nlinarith
  choose F hF hb heq using (fun p : TreeShell d (k + 1) =>
    exists_inwardContinuationAverage_channel hd μ t hθ p L
      (Finset.Ico (k + 1) (k + 1 + L)))
  have hmeanF (p : TreeShell d (k + 1)) (hp : p ∈ I) :
      (∫ z, F p (globalCone p.1 z)
        ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => gaussianReal 0 t))) ≤ τ / 4 := by
    simpa only [heq, PlantedSymmetry.gaussianNoiseLaw] using hmean p hp
  have hcon := hμ.measure_cutLevel_average_ge_le
    (by linarith : -1 ≤ Real.tanh beta) hθ1.le (k + 1)
    (fun _ : TreeVertex d => gaussianReal 0 t) F hF hb I hI hτ hmeanF
  change (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    {z | τ ≤ (∑ p ∈ I, F p (globalCone p.1 z)) / (I.card : ℝ)} ≤ _ at hcon
  refine le_trans ?_ hcon
  apply measure_mono_ae
  filter_upwards [average_gaussianInwardConeFactor_le_cut_average hμ hbeta t I L]
    with z hz
  intro h
  simp only [heq] at hz
  exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp (h.trans hz)

end Problem367

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.measure_gaussian_inward_path_average_ge_le_oai := @OAI.Problem367.measure_gaussian_inward_path_average_ge_le_oai

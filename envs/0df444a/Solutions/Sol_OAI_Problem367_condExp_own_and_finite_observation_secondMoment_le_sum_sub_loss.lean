-- Prove2me | solution 1 for OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:40:57.412192+00:00
-- url     : https://prove2.me/submissions/90b234de-79a2-43ce-8bb8-89fdd5a6ebc0

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

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

theorem map_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q : Ω → ℝ} (hq : Measurable q) (a : ℝ) :
    Measure.map q (linearSignalTilt mu q a) = linearSignalTilt (Measure.map q mu) id a := by
  unfold linearSignalTilt
  simpa only [Function.comp_def, id_eq] using
    (map_withDensity_comp (mu := mu) (f := q)
      (w := fun y : ℝ => ENNReal.ofReal (1 + a * y)) hq (by fun_prop))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorTilt
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
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

theorem integral_cond_spin_posterior_function
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun x => g (mu[fun y => spinSign (S y) | mSmall] x)) mu)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    ∫ x, g (mu[fun y => spinSign (S y) | mSmall] x)
        ∂ProbabilityTheory.cond mu {x | S x = a} =
      ∫ x, g (mu[fun y => spinSign (S y) | mSmall] x) *
        (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  exact integral_cond_spin_posterior_tilt hm hS
    (hg.comp stronglyMeasurable_condExp.measurable).stronglyMeasurable hgi a hfair

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
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
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
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

theorem binaryFusionLoss_denominator_pos {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 < 1 - u ^ 2 * v ^ 2 := by
  have h := (sq_lt_one_iff_abs_lt_one (u * v)).mpr
    (binaryFusion_abs_mul_lt_one hu hv)
  nlinarith

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

theorem binaryFusionLoss_nonneg {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 ≤ binaryFusionLoss u v := by
  have hu' := (sq_lt_one_iff_abs_lt_one u).mpr hu
  have hv' := (sq_lt_one_iff_abs_lt_one v).mpr hv
  have hf : 0 ≤ 2 - u ^ 2 - v ^ 2 := by linarith
  have hd := binaryFusionLoss_denominator_pos hu hv
  unfold binaryFusionLoss
  positivity

theorem binaryFusion_symmetric_square {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    ((u + v) ^ 2 / (1 + u * v) + (u - v) ^ 2 / (1 - u * v)) / 2 =
      u ^ 2 + v ^ 2 - binaryFusionLoss u v := by
  have hp := ne_of_gt (binaryFusion_denominator_pos hu hv)
  have hm : 1 - u * v ≠ 0 := by
    have := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).2
    linarith
  have hq := ne_of_gt (binaryFusionLoss_denominator_pos hu hv)
  unfold binaryFusionLoss
  field_simp
  ring

theorem binaryFusionLoss_lower_bound {u v theta : ℝ}
    (hu : |u| ≤ theta) (hv : |v| ≤ theta) (htheta : theta < 1) :
    2 * (1 - theta ^ 2) * u ^ 2 * v ^ 2 ≤ binaryFusionLoss u v := by
  have ht0 : 0 ≤ theta := le_trans (abs_nonneg u) hu
  have hu' : u ^ 2 ≤ theta ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) ht0).mpr hu
  have hv' : v ^ 2 ≤ theta ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg v) ht0).mpr hv
  have ht2 : theta ^ 2 < 1 := (sq_lt_one_iff₀ ht0).mpr htheta
  have hp : 0 ≤ u ^ 2 * v ^ 2 := mul_nonneg (sq_nonneg u) (sq_nonneg v)
  have hf : 0 ≤ 2 - u ^ 2 - v ^ 2 := by linarith
  have hd := binaryFusionLoss_denominator_pos (lt_of_le_of_lt hu htheta)
    (lt_of_le_of_lt hv htheta)
  have hfactor : 2 * (1 - theta ^ 2) ≤ 2 - u ^ 2 - v ^ 2 := by linarith
  have hnum : 0 ≤ u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) := mul_nonneg hp hf
  unfold binaryFusionLoss
  calc
    2 * (1 - theta ^ 2) * u ^ 2 * v ^ 2 =
        (u ^ 2 * v ^ 2) * (2 * (1 - theta ^ 2)) := by ring
    _ ≤ u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) :=
      mul_le_mul_of_nonneg_left hfactor hp
    _ ≤ u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) / (1 - u ^ 2 * v ^ 2) := by
      apply (le_div_iff₀ hd).mpr
      exact mul_le_of_le_one_right hnum (by linarith)

theorem binaryFusion_integrand_le_two {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : (u + v) ^ 2 / (1 + u * v) ≤ 2 := by
  apply (div_le_iff₀ (binaryFusion_denominator_pos hu hv)).mpr
  have hu' := (sq_lt_one_iff_abs_lt_one u).mpr hu
  have hv' := (sq_lt_one_iff_abs_lt_one v).mpr hv
  nlinarith

theorem binaryFusionLoss_le_sum_sq {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : binaryFusionLoss u v ≤ u ^ 2 + v ^ 2 := by
  have hp : 0 ≤ (u + v) ^ 2 / (1 + u * v) :=
    div_nonneg (sq_nonneg _) (binaryFusion_denominator_pos hu hv).le
  have hmden : 0 < 1 - u * v := by
    have := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).2
    linarith
  have hm : 0 ≤ (u - v) ^ 2 / (1 - u * v) :=
    div_nonneg (sq_nonneg _) hmden.le
  have hid := binaryFusion_symmetric_square hu hv
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_BinaryFusionIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem ae_binaryFusion_bounds {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    ∀ᵐ p ∂mu.prod nu, |p.1| < 1 ∧ |p.2| < 1 := by
  have hu' : ∀ᵐ p ∂mu.prod nu, |p.1| < 1 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hu
  have hv' : ∀ᵐ p ∂mu.prod nu, |p.2| < 1 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae hv
  exact hu'.and hv'

theorem integrable_binaryFusion_integrand {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 / (1 + p.1 * p.2))
      (mu.prod nu) := by
  refine (integrable_const (2 : ℝ)).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (sq_nonneg _) (binaryFusion_denominator_pos hp.1 hp.2).le)]
  exact binaryFusion_integrand_le_two hp.1 hp.2

theorem integrable_binaryFusionLoss {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    Integrable (fun p : ℝ × ℝ => binaryFusionLoss p.1 p.2) (mu.prod nu) := by
  refine (integrable_const (2 : ℝ)).mono' ?_ ?_
  · unfold binaryFusionLoss
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (binaryFusionLoss_nonneg hp.1 hp.2)]
    have h := binaryFusionLoss_le_sum_sq hp.1 hp.2
    have hu' := (sq_lt_one_iff_abs_lt_one p.1).mpr hp.1
    have hv' := (sq_lt_one_iff_abs_lt_one p.2).mpr hp.2
    linarith

theorem integral_binaryFusion_symmetric_square {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu) =
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  let R : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  have hR : MeasurePreserving R (mu.prod nu) (mu.prod nu) :=
    (MeasurePreserving.id mu).prod ⟨measurable_neg, hsym⟩
  have hi := integrable_binaryFusion_integrand hu hv
  have hin : Integrable (fun p : ℝ × ℝ =>
      (p.1 - p.2) ^ 2 / (1 - p.1 * p.2)) (mu.prod nu) := by
    have h := (hR.integrable_comp hi.aestronglyMeasurable).mpr hi
    change Integrable (fun p : ℝ × ℝ =>
      (p.1 + -p.2) ^ 2 / (1 + p.1 * -p.2)) (mu.prod nu) at h
    simpa [sub_eq_add_neg] using h
  have heq : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 / (1 - p.1 * p.2) ∂mu.prod nu) =
      ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu := by
    have h := hR.integral_comp'
      (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 / (1 + p.1 * p.2))
    change (∫ p : ℝ × ℝ, (p.1 + -p.2) ^ 2 / (1 + p.1 * -p.2) ∂mu.prod nu) = _ at h
    simpa [sub_eq_add_neg] using h
  have hiu : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (mu.prod nu) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p.1)] using
      ((sq_lt_one_iff_abs_lt_one p.1).mpr hp.1).le
  have hiv : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (mu.prod nu) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p.2)] using
      ((sq_lt_one_iff_abs_lt_one p.2).mpr hp.2).le
  have hl := integrable_binaryFusionLoss hu hv
  have hiuv : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (mu.prod nu) := hiu.add hiv
  have hsum : (∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 ∂mu.prod nu) =
      (∫ p : ℝ × ℝ, p.1 ^ 2 ∂mu.prod nu) +
        ∫ p : ℝ × ℝ, p.2 ^ 2 ∂mu.prod nu := integral_add hiu hiv
  have hscalar :
      (∫ p : ℝ × ℝ,
        ((p.1 + p.2) ^ 2 / (1 + p.1 * p.2) +
          (p.1 - p.2) ^ 2 / (1 - p.1 * p.2)) / 2 ∂mu.prod nu) =
      ∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 - binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
    apply integral_congr_ae
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    exact binaryFusion_symmetric_square hp.1 hp.2
  rw [integral_div, integral_add hi hin, heq,
    integral_sub hiuv hl, hsum,
    integral_fun_fst (μ := mu) (ν := nu) (fun u : ℝ => u ^ 2),
    integral_fun_snd (μ := mu) (ν := nu) (fun v : ℝ => v ^ 2)] at hscalar
  simp only [probReal_univ, one_smul] at hscalar
  linarith

theorem integral_binaryFusionLoss_nonneg {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    0 ≤ ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  exact binaryFusionLoss_nonneg hp.1 hp.2

private theorem integrable_sq_of_ae_abs_lt_one {mu : Measure ℝ}
    [IsProbabilityMeasure mu] (hu : ∀ᵐ u ∂mu, |u| < 1) :
    Integrable (fun u : ℝ => u ^ 2) mu := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [hu] with u hu
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg u)] using
    ((sq_lt_one_iff_abs_lt_one u).mpr hu).le

theorem integral_binaryFusionLoss_lower_bound {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] {theta : ℝ}
    (hu : ∀ᵐ u ∂mu, |u| ≤ theta) (hv : ∀ᵐ v ∂nu, |v| ≤ theta)
    (htheta : theta < 1) :
    2 * (1 - theta ^ 2) * (∫ u : ℝ, u ^ 2 ∂mu) * (∫ v : ℝ, v ^ 2 ∂nu) ≤
      ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  have hu1 : ∀ᵐ u ∂mu, |u| < 1 := hu.mono (fun _ h => lt_of_le_of_lt h htheta)
  have hv1 : ∀ᵐ v ∂nu, |v| < 1 := hv.mono (fun _ h => lt_of_le_of_lt h htheta)
  have hiu := integrable_sq_of_ae_abs_lt_one hu1
  have hiv := integrable_sq_of_ae_abs_lt_one hv1
  have hip := hiu.mul_prod hiv
  have hl := integrable_binaryFusionLoss hu1 hv1
  have hu' : ∀ᵐ p ∂mu.prod nu, |p.1| ≤ theta :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hu
  have hv' : ∀ᵐ p ∂mu.prod nu, |p.2| ≤ theta :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae hv
  have hb : (∫ p : ℝ × ℝ, (2 * (1 - theta ^ 2)) * (p.1 ^ 2 * p.2 ^ 2) ∂mu.prod nu) ≤
      ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
    apply integral_mono_ae (hip.const_mul _) hl
    filter_upwards [hu', hv'] with p hpu hpv
    simpa only [mul_assoc] using binaryFusionLoss_lower_bound hpu hpv htheta
  rw [integral_const_mul,
    integral_prod_mul (μ := mu) (ν := nu) (fun u : ℝ => u ^ 2) (fun v : ℝ => v ^ 2)] at hb
  simpa only [mul_assoc] using hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusionJointLaw
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem integral_binaryFusion_sq_jointLaw {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    (∫ p : ℝ × ℝ, binaryFusion p.1 p.2 ^ 2 ∂binaryFusionJointLaw mu nu) =
      ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu := by
  rw [binaryFusionJointLaw, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  have hd := binaryFusion_denominator_pos hp.1 hp.2
  rw [ENNReal.toReal_ofReal hd.le, smul_eq_mul, binaryFusion]
  field_simp

theorem binaryFusionJointLaw_secondMoment {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, binaryFusion p.1 p.2 ^ 2 ∂binaryFusionJointLaw mu nu) =
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  rw [integral_binaryFusion_sq_jointLaw hu hv]
  exact integral_binaryFusion_symmetric_square hu hv hsym

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusionMixture
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem binaryFusionJointLaw_eq_conditional_mixture {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    (1 / 2 : ENNReal) •
        ((linearSignalTilt mu id 1).prod (linearSignalTilt nu id 1)) +
      (1 / 2 : ENNReal) •
        ((linearSignalTilt mu id (-1)).prod (linearSignalTilt nu id (-1))) =
      binaryFusionJointLaw mu nu := by
  unfold linearSignalTilt binaryFusionJointLaw
  simp only [id_eq, one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [prod_withDensity (by fun_prop) (by fun_prop),
    prod_withDensity (by fun_prop) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_add_left (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  exact binaryFusion_density_eq_mixture hp.1 hp.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorLaw
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367

theorem map_cond_spin_posterior_eq_linearSignalTilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    Measure.map (mu[fun y => spinSign (S y) | mSmall])
        (ProbabilityTheory.cond mu {x | S x = a}) =
      linearSignalTilt (Measure.map (mu[fun y => spinSign (S y) | mSmall]) mu)
        id (spinSign a) := by
  let M : Ω → ℝ := mu[fun y => spinSign (S y) | mSmall]
  have hM : Measurable M := stronglyMeasurable_condExp.measurable.mono hm le_rfl
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hMb : ∀ᵐ x ∂mu, |M x| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using
      (ae_bdd_norm_condExp_of_ae_bdd_norm (m := mSmall) hSb)
  have ha : |spinSign a| ≤ 1 := by cases a <;> norm_num [spinSign]
  have hMi : Integrable M mu := integrable_condExp
  let : IsProbabilityMeasure (ProbabilityTheory.cond mu {x | S x = a}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  have hdi : Integrable (fun x => 1 + spinSign a * M x) mu :=
    (integrable_const 1).add (hMi.const_mul (spinSign a))
  let : IsFiniteMeasure (linearSignalTilt mu M (spinSign a)) :=
    isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  change Measure.map M (ProbabilityTheory.cond mu {x | S x = a}) =
    linearSignalTilt (Measure.map M mu) id (spinSign a)
  rw [← map_linearSignalTilt hM]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hM.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_map hM.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  have hfi : Integrable (fun x => f (M x)) mu :=
    Integrable.of_bound (f.continuous.measurable.comp hM).aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (M x)))
  rw [integral_cond_spin_posterior_function hm hS f f.continuous.measurable hfi a hfair,
    integral_linearSignalTilt hM hMb ha hfi]
  rw [← integral_const_mul,
    ← integral_add hfi ((integrable_boundedSignal_mul hM hMb hfi).const_mul (spinSign a))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by dsimp [M] <;> ring)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorFusion
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
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

theorem map_posterior_pair_eq_binaryFusionJointLaw
    {Ω : Type*} {mLeft mRight m : MeasurableSpace Ω}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (hLeft : mLeft ≤ m) (hRight : mRight ≤ m)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin,
      IndepFun (mu[fun x => spinSign (S x) | mLeft])
        (mu[fun x => spinSign (S x) | mRight]) (cond mu {x | S x = a}))
    (hL : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mLeft] x| < 1)
    (hR : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mRight] x| < 1) :
    Measure.map (fun x =>
        (mu[fun y => spinSign (S y) | mLeft] x,
         mu[fun y => spinSign (S y) | mRight] x)) mu =
      binaryFusionJointLaw
        (Measure.map (mu[fun y => spinSign (S y) | mLeft]) mu)
        (Measure.map (mu[fun y => spinSign (S y) | mRight]) mu) := by
  let L : Ω → ℝ := mu[fun y => spinSign (S y) | mLeft]
  let R : Ω → ℝ := mu[fun y => spinSign (S y) | mRight]
  have hLm : Measurable L := stronglyMeasurable_condExp.measurable.mono hLeft le_rfl
  have hRm : Measurable R := stronglyMeasurable_condExp.measurable.mono hRight le_rfl
  haveI : IsProbabilityMeasure (Measure.map L mu) := Measure.isProbabilityMeasure_map hLm.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map R mu) := Measure.isProbabilityMeasure_map hRm.aemeasurable
  have hpair (a : IsingSpin) :
      Measure.map (fun x => (L x, R x)) (cond mu {x | S x = a}) =
        (linearSignalTilt (Measure.map L mu) id (spinSign a)).prod
          (linearSignalTilt (Measure.map R mu) id (spinSign a)) := by
    let : IsProbabilityMeasure (cond mu {x | S x = a}) :=
      cond_isProbabilityMeasure (by rw [hfair]; norm_num)
    rw [(hInd a).map_prod_eq_prod_map_map hLm.aemeasurable hRm.aemeasurable,
      map_cond_spin_posterior_eq_linearSignalTilt hLeft hS a (hfair a),
      map_cond_spin_posterior_eq_linearSignalTilt hRight hS a (hfair a)]
  have hLmap : ∀ᵐ u ∂Measure.map L mu, |u| < 1 :=
    (ae_map_iff hLm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hL
  have hRmap : ∀ᵐ v ∂Measure.map R mu, |v| < 1 :=
    (ae_map_iff hRm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hR
  change Measure.map (fun x => (L x, R x)) mu =
    binaryFusionJointLaw (Measure.map L mu) (Measure.map R mu)
  calc
    _ = Measure.map (fun x => (L x, R x))
        ((1 / 2 : ENNReal) • cond mu {x | S x = .pos} +
          (1 / 2 : ENNReal) • cond mu {x | S x = .neg}) := by
      rw [← measure_eq_fair_spin_mixture hS hfair]
    _ = _ := by
      rw [Measure.map_add _ _ (hLm.prodMk hRm),
        Measure.map_smul,
        Measure.map_smul,
        hpair .pos, hpair .neg]
      exact binaryFusionJointLaw_eq_conditional_mixture hLmap hRmap

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_ObservationFusion
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
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
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ObservationInformation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Observations

variable {Ω A B : Type*} {mΩ : MeasurableSpace Ω} {mA : MeasurableSpace A}
  {mB : MeasurableSpace B} {rho : Measure Ω} [IsProbabilityMeasure rho]
  {S : Ω → IsingSpin} (hS : Measurable S)
  {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
  {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
  (hpostX : rho[fun x => spinSign (S x) | mA.comap X] =ᵐ[rho] fun x => q (X x))
  (hpostY : rho[fun x => spinSign (S x) | mB.comap Y] =ᵐ[rho] fun x => r (Y x))
  (hqb : ∀ᵐ x ∂rho, |q (X x)| < 1) (hrb : ∀ᵐ x ∂rho, |r (Y x)| < 1)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hInd : ∀ a : IsingSpin, IndepFun X Y (cond rho {x | S x = a}))

include hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd

theorem map_observation_posterior_pair_eq_binaryFusionJointLaw :
    Measure.map (fun x => (q (X x), r (Y x))) rho =
      binaryFusionJointLaw (Measure.map (fun x => q (X x)) rho)
        (Measure.map (fun x => r (Y x)) rho) := by
  have hL : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mA.comap X] x| < 1 := by
    filter_upwards [hpostX, hqb] with x hx hb
    simpa only [hx] using hb
  have hR : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1 := by
    filter_upwards [hpostY, hrb] with x hx hb
    simpa only [hx] using hb
  have hInd' (a : IsingSpin) :
      IndepFun (rho[fun y => spinSign (S y) | mA.comap X])
        (rho[fun y => spinSign (S y) | mB.comap Y]) (cond rho {x | S x = a}) :=
    ((hInd a).comp hq hr).congr
      (cond_absolutelyContinuous.ae_le hpostX.symm)
      (cond_absolutelyContinuous.ae_le hpostY.symm)
  have hjoint := map_posterior_pair_eq_binaryFusionJointLaw
    hX.comap_le hY.comap_le hS hfair hInd' hL hR
  have hp : (fun x => (rho[fun y => spinSign (S y) | mA.comap X] x,
      rho[fun y => spinSign (S y) | mB.comap Y] x)) =ᵐ[rho]
        (fun x => (q (X x), r (Y x))) := by
    filter_upwards [hpostX, hpostY] with x hx hy
    rw [hx, hy]
  rw [Measure.map_congr hp, Measure.map_congr hpostX, Measure.map_congr hpostY] at hjoint
  exact hjoint

theorem condExp_observation_pair_secondMoment
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) =
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂
          (Measure.map (fun x => q (X x)) rho).prod (Measure.map (fun x => r (Y x)) rho) := by
  haveI : IsProbabilityMeasure (Measure.map (fun x => q (X x)) rho) := Measure.isProbabilityMeasure_map (hq.comp hX).aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (fun x => r (Y x)) rho) := Measure.isProbabilityMeasure_map (hr.comp hY).aemeasurable
  have hCE := condExp_spin_given_observation_pair_eq_binaryFusion
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd
  have hiCE := integral_congr_ae (hCE.fun_comp (fun x : ℝ => x ^ 2))
  simp only [Function.comp_apply] at hiCE
  rw [hiCE]
  have hpair : Measurable (fun x => (q (X x), r (Y x))) :=
    (hq.comp hX).prodMk (hr.comp hY)
  have hmap := integral_map (μ := rho) hpair.aemeasurable
    (show AEStronglyMeasurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2 ^ 2) _ by
      apply Measurable.aestronglyMeasurable; unfold binaryFusion; fun_prop)
  rw [map_observation_posterior_pair_eq_binaryFusionJointLaw
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd] at hmap
  rw [← hmap]
  have hqm : ∀ᵐ u ∂Measure.map (fun x => q (X x)) rho, |u| < 1 :=
    (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hqb
  have hrm : ∀ᵐ u ∂Measure.map (fun x => r (Y x)) rho, |u| < 1 :=
    (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hrb
  rw [binaryFusionJointLaw_secondMoment hqm hrm hsym,
    integral_map (μ := rho) (φ := fun x => q (X x)) (f := fun u : ℝ => u ^ 2)
      (hq.comp hX).aemeasurable (by fun_prop),
    integral_map (μ := rho) (φ := fun x => r (Y x)) (f := fun u : ℝ => u ^ 2)
      (hr.comp hY).aemeasurable (by fun_prop)]

theorem condExp_observation_pair_secondMoment_le_add
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) ≤
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) := by
  haveI : IsProbabilityMeasure (Measure.map (fun x => q (X x)) rho) := Measure.isProbabilityMeasure_map (hq.comp hX).aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (fun x => r (Y x)) rho) := Measure.isProbabilityMeasure_map (hr.comp hY).aemeasurable
  rw [condExp_observation_pair_secondMoment
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd hsym]
  apply sub_le_self
  apply integral_binaryFusionLoss_nonneg
  · exact (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hqb
  · exact (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hrb

omit hqb hrb in

theorem condExp_observation_pair_secondMoment_le
    {theta : ℝ}
    (hqtheta : ∀ᵐ x ∂rho, |q (X x)| ≤ theta)
    (hrtheta : ∀ᵐ x ∂rho, |r (Y x)| ≤ theta) (htheta : theta < 1)
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) ≤
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) -
        2 * (1 - theta ^ 2) * (∫ x, q (X x) ^ 2 ∂rho) * (∫ x, r (Y x) ^ 2 ∂rho) := by
  haveI : IsProbabilityMeasure (Measure.map (fun x => q (X x)) rho) := Measure.isProbabilityMeasure_map (hq.comp hX).aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (fun x => r (Y x)) rho) := Measure.isProbabilityMeasure_map (hr.comp hY).aemeasurable
  have hq1 := hqtheta.mono (fun _ hx => lt_of_le_of_lt hx htheta)
  have hr1 := hrtheta.mono (fun _ hx => lt_of_le_of_lt hx htheta)
  rw [condExp_observation_pair_secondMoment
    hS hX hY hq hr hpostX hpostY hq1 hr1 hfair hInd hsym]
  have hqm : ∀ᵐ u ∂Measure.map (fun x => q (X x)) rho, |u| ≤ theta :=
    (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_le measurable_abs measurable_const)).2 hqtheta
  have hrm : ∀ᵐ u ∂Measure.map (fun x => r (Y x)) rho, |u| ≤ theta :=
    (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_le measurable_abs measurable_const)).2 hrtheta
  have hloss := integral_binaryFusionLoss_lower_bound hqm hrm htheta
  rw [integral_map (μ := rho) (φ := fun x => q (X x)) (f := fun u : ℝ => u ^ 2)
      (hq.comp hX).aemeasurable (by fun_prop),
    integral_map (μ := rho) (φ := fun x => r (Y x)) (f := fun u : ℝ => u ^ 2)
      (hr.comp hY).aemeasurable (by fun_prop)] at hloss
  exact sub_le_sub_left hloss _

end Observations

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteSignalInformation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

theorem finiteSignalField_le {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ) (I : Finset ι) :
    finiteSignalField m I ≤ mΩ := iSup_le fun i => iSup_le fun _ => hm i

theorem indep_finiteSignalField_of_not_mem {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
    {mu : Measure Ω} {m : ι → MeasurableSpace Ω} (hm : ∀ i, m i ≤ mΩ)
    (hInd : iIndep m mu) {I : Finset ι} {a : ι} (ha : a ∉ I) :
    Indep (finiteSignalField m I) (m a) mu := by
  have hd : Disjoint (I : Set ι) ({a} : Set ι) := by
    simpa only [Set.disjoint_singleton_right, Finset.mem_coe] using ha
  simpa [finiteSignalField] using indep_iSup_of_disjoint hm hInd hd

theorem condExp_spin_sup_eq_binaryFusion
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a})) :
    rho[fun y => spinSign (S y) | m₁ ⊔ m₂] =ᵐ[rho]
      fun x => binaryFusion (rho[fun y => spinSign (S y) | m₁] x)
        (rho[fun y => spinSign (S y) | m₂] x) := by
  have hX : @Measurable Ω Ω mΩ m₁ id := measurable_id.mono hm₁ le_rfl
  have hY : @Measurable Ω Ω mΩ m₂ id := measurable_id.mono hm₂ le_rfl
  have hq : @Measurable Ω ℝ m₁ inferInstance
      (rho[fun y => spinSign (S y) | m₁]) := stronglyMeasurable_condExp.measurable
  have hr : @Measurable Ω ℝ m₂ inferInstance
      (rho[fun y => spinSign (S y) | m₂]) := stronglyMeasurable_condExp.measurable
  have hI : ∀ a : IsingSpin,
      @IndepFun Ω Ω Ω mΩ m₁ m₂ id id (cond rho {x | S x = a}) := by
    intro a
    simpa [IndepFun, Kernel.IndepFun, Indep] using hInd a
  have h := @condExp_spin_given_observation_pair_eq_binaryFusion
    Ω Ω Ω mΩ m₁ m₂ rho _ S hS id id hX hY
    (rho[fun y => spinSign (S y) | m₁])
    (rho[fun y => spinSign (S y) | m₂]) hq hr
    (by simp) (by simp) h₁ h₂ hfair hI
  change rho[fun y => spinSign (S y) |
    (m₁.prod m₂).comap (fun x : Ω => (id x, id x))] =ᵐ[rho] _ at h
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_id,
    MeasurableSpace.comap_id] at h
  exact h

theorem abs_condExp_spin_sup_lt_one
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a})) :
    ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁ ⊔ m₂] x| < 1 := by
  filter_upwards [condExp_spin_sup_eq_binaryFusion hm₁ hm₂ hS h₁ h₂ hfair hInd,
    h₁, h₂] with x hx hx₁ hx₂
  rw [hx]
  exact abs_binaryFusion_lt_one hx₁ hx₂

theorem abs_condExp_spin_finiteSignalField_lt_one
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] {m : ι → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ mΩ) {S : Ω → IsingSpin} (hS : Measurable S)
    (hstrict : ∀ i, ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m i] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, iIndep m (cond rho {x | S x = a}))
    (I : Finset ι) (hI : I.Nonempty) :
    ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | finiteSignalField m I] x| < 1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at hI
  | @insert a I ha ih =>
      by_cases hIn : I.Nonempty
      · rw [finiteSignalField_insert, sup_comm]
        exact abs_condExp_spin_sup_lt_one (finiteSignalField_le hm I) (hm a) hS
          (ih hIn) (hstrict a) hfair
          (fun b => indep_finiteSignalField_of_not_mem hm (hInd b) ha)
      · have hIe : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIn
        subst I
        simpa using hstrict a

theorem spinInformation_sup_le_add
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a}))
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) :
    spinInformation rho S (m₁ ⊔ m₂) ≤
      spinInformation rho S m₁ + spinInformation rho S m₂ := by
  have hX : @Measurable Ω Ω mΩ m₁ id := measurable_id.mono hm₁ le_rfl
  have hY : @Measurable Ω Ω mΩ m₂ id := measurable_id.mono hm₂ le_rfl
  have hI : ∀ a : IsingSpin,
      @IndepFun Ω Ω Ω mΩ m₁ m₂ id id (cond rho {x | S x = a}) := by
    intro a
    simpa [IndepFun, Kernel.IndepFun, Indep] using hInd a
  have h := @condExp_observation_pair_secondMoment_le_add
    Ω Ω Ω mΩ m₁ m₂ rho _ S hS id id hX hY
    (rho[fun y => spinSign (S y) | m₁])
    (rho[fun y => spinSign (S y) | m₂])
    stronglyMeasurable_condExp.measurable stronglyMeasurable_condExp.measurable
    (by simp) (by simp) h₁ h₂ hfair hI hsym
  change spinInformation rho S
    ((m₁.prod m₂).comap (fun x : Ω => (id x, id x))) ≤ _ at h
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_id,
    MeasurableSpace.comap_id] at h
  exact h

theorem spinInformation_sup_le_sub_loss
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a}))
    {theta : ℝ}
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| ≤ theta)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| ≤ theta)
    (htheta : theta < 1)
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) :
    spinInformation rho S (m₁ ⊔ m₂) ≤
      spinInformation rho S m₁ + spinInformation rho S m₂ -
        2 * (1 - theta ^ 2) * spinInformation rho S m₁ * spinInformation rho S m₂ := by
  have hX : @Measurable Ω Ω mΩ m₁ id := measurable_id.mono hm₁ le_rfl
  have hY : @Measurable Ω Ω mΩ m₂ id := measurable_id.mono hm₂ le_rfl
  have hI : ∀ a : IsingSpin,
      @IndepFun Ω Ω Ω mΩ m₁ m₂ id id (cond rho {x | S x = a}) := by
    intro a
    simpa [IndepFun, Kernel.IndepFun, Indep] using hInd a
  have h := @condExp_observation_pair_secondMoment_le
    Ω Ω Ω mΩ m₁ m₂ rho _ S hS id id hX hY
    (rho[fun y => spinSign (S y) | m₁])
    (rho[fun y => spinSign (S y) | m₂])
    stronglyMeasurable_condExp.measurable stronglyMeasurable_condExp.measurable
    (by simp) (by simp) hfair hI theta h₁ h₂ htheta hsym
  change spinInformation rho S
    ((m₁.prod m₂).comap (fun x : Ω => (id x, id x))) ≤ _ at h
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_id,
    MeasurableSpace.comap_id] at h
  exact h

section FiniteFamily

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {rho : Measure Ω}
  [IsProbabilityMeasure rho] {m : ι → MeasurableSpace Ω}
  (hm : ∀ i, m i ≤ mΩ) {S : Ω → IsingSpin} (hS : Measurable S)
  (hstrict : ∀ i, ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m i] x| < 1)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hInd : ∀ a : IsingSpin, iIndep m (cond rho {x | S x = a}))
  (hsym : ∀ i, Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | m i]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | m i]) rho)

include hm hS hstrict hfair hInd hsym

theorem spinInformation_finiteSignalField_union_le [DecidableEq ι]
    (J : Finset ι) (hJ : J.Nonempty) (I : Finset ι) (hIJ : Disjoint I J) :
    spinInformation rho S (finiteSignalField m (I ∪ J)) ≤
      (∑ i ∈ I, spinInformation rho S (m i)) + spinInformation rho S (finiteSignalField m J) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
      have hI : Disjoint I J := (Finset.disjoint_insert_left.mp hIJ).2
      have haJ : a ∉ J := (Finset.disjoint_insert_left.mp hIJ).1
      have haIJ : a ∉ I ∪ J := by simp [ha, haJ]
      have hne : (I ∪ J).Nonempty := hJ.mono Finset.subset_union_right
      have hbound := spinInformation_sup_le_add (finiteSignalField_le hm (I ∪ J))
        (hm a) hS
        (abs_condExp_spin_finiteSignalField_lt_one hm hS hstrict hfair hInd (I ∪ J) hne)
        (hstrict a) hfair
        (fun b => indep_finiteSignalField_of_not_mem hm (hInd b) haIJ) (hsym a)
      have hih := ih hI
      rw [Finset.insert_union, finiteSignalField_insert, sup_comm]
      rw [Finset.sum_insert ha]
      linarith

theorem spinInformation_finiteSignalField_le_sum_sub_loss
    (I : Finset ι) {a b : ι} (hab : a ≠ b) (ha : a ∈ I) (hb : b ∈ I)
    {theta : ℝ}
    (haTheta : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m a] x| ≤ theta)
    (hbTheta : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m b] x| ≤ theta)
    (htheta : theta < 1) :
    spinInformation rho S (finiteSignalField m I) ≤
      (∑ i ∈ I, spinInformation rho S (m i)) -
        2 * (1 - theta ^ 2) * spinInformation rho S (m a) * spinInformation rho S (m b) := by
  classical
  have hJsub : ({a, b} : Finset ι) ⊆ I := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact ha
    · have hc' : c = b := Finset.mem_singleton.mp hc
      simpa only [hc'] using hb
  have hdisj : Disjoint (I \ {a, b}) ({a, b} : Finset ι) := by
    apply Finset.disjoint_left.mpr
    intro c hc hcJ
    exact (Finset.mem_sdiff.mp hc).2 hcJ
  have hunion := spinInformation_finiteSignalField_union_le hm hS hstrict hfair hInd hsym
    {a, b} (by simp) (I \ {a, b}) hdisj
  rw [Finset.sdiff_union_of_subset hJsub] at hunion
  have hpairInd (s : IsingSpin) : Indep (m a) (m b) (cond rho {x | S x = s}) := by
    simpa using indep_finiteSignalField_of_not_mem hm (hInd s)
      (I := {a}) (a := b) (by simp [Ne.symm hab])
  have hpair := spinInformation_sup_le_sub_loss (hm a) (hm b) hS hfair hpairInd
    haTheta hbTheta htheta (hsym b)
  have hsum := Finset.sum_sdiff (f := fun i => spinInformation rho S (m i)) hJsub
  simp only [finiteSignalField_insert, finiteSignalField_singleton] at hunion
  simp [hab] at hsum
  linarith

end FiniteFamily

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FiniteObservationInformation
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

theorem iIndep_observationFields_cond_spin
    {Ω ι : Type*} {A : ι → Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [mA : ∀ i, MeasurableSpace (A i)]
    {rho : Measure Ω} [IsProbabilityMeasure rho]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : ∀ i, Ω → A i} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X rho)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (a : IsingSpin) :
    iIndep (fun i => (mA i).comap (X i)) (cond rho {x | S x = a}) := by
  have hne : rho (S ⁻¹' {a}) ≠ 0 := by
    change rho {x | S x = a} ≠ 0
    rw [hfair]
    norm_num
  exact (iIndepFun_cond_fiber_of_iCondIndepFun hS hX hCI a hne).iIndep

section Observations

variable {Ω ι : Type*} {A : ι → Type*} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] [mA : ∀ i, MeasurableSpace (A i)] [Fintype ι]
  {rho : Measure Ω} [IsProbabilityMeasure rho]
  {S : Ω → IsingSpin} (hS : Measurable S)
  {X : ∀ i, Ω → A i} (hX : ∀ i, Measurable (X i))
  (hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X rho)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hstrict : ∀ i, ∀ᵐ x ∂rho,
    |rho[fun y => spinSign (S y) | (mA i).comap (X i)] x| < 1)
  (hsym : ∀ i, Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | (mA i).comap (X i)]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | (mA i).comap (X i)]) rho)

include hS hX hCI hfair hstrict hsym

theorem condExp_finite_observation_secondMoment_le_sum_sub_loss
    {a b : ι} (hab : a ≠ b) {theta : ℝ}
    (haTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA a).comap (X a)] x| ≤ theta)
    (hbTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA b).comap (X b)] x| ≤ theta)
    (htheta : theta < 1) :
    (∫ x, (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x)] x) ^ 2 ∂rho) ≤
      (∑ i, ∫ x, (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) ^ 2 ∂rho) -
        2 * (1 - theta ^ 2) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA a).comap (X a)] x) ^ 2 ∂rho) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA b).comap (X b)] x) ^ 2 ∂rho) := by
  have h := spinInformation_finiteSignalField_le_sum_sub_loss (fun i => (hX i).comap_le)
    hS hstrict hfair (iIndep_observationFields_cond_spin hS hX hCI hfair) hsym
    Finset.univ hab (Finset.mem_univ a) (Finset.mem_univ b) haTheta hbTheta htheta
  have hf : finiteSignalField (fun i => (mA i).comap (X i)) Finset.univ =
      (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x) := by
    simp [finiteSignalField, MeasurableSpace.comap_process_pi]
  rw [hf] at h
  simpa only [spinInformation] using h

theorem condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss_oai
    {B : Type*} [mB : MeasurableSpace B] {Y : Ω → B} (hY : Measurable Y)
    (hOwn : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le
      Y (fun x i => X i x) rho)
    (hOwnStrict : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1)
    (hOwnSym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho)
    {a b : ι} (hab : a ≠ b) {theta : ℝ}
    (haTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA a).comap (X a)] x| ≤ theta)
    (hbTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA b).comap (X b)] x| ≤ theta)
    (htheta : theta < 1) :
    (∫ x, (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (B × (∀ i, A i))).comap
        (fun x => (Y x, fun i => X i x))] x) ^ 2 ∂rho) ≤
      (∫ x, (rho[fun y => spinSign (S y) | mB.comap Y] x) ^ 2 ∂rho) +
      (∑ i, ∫ x, (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) ^ 2 ∂rho) -
        2 * (1 - theta ^ 2) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA a).comap (X a)] x) ^ 2 ∂rho) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA b).comap (X b)] x) ^ 2 ∂rho) := by
  let mAll : MeasurableSpace Ω :=
    (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x)
  let : MeasurableSpace Ω := mΩ
  have hAll : Measurable (fun x i => X i x) := Measurable.of_eval hX
  have hFields := iIndep_observationFields_cond_spin hS hX hCI hfair
  have hf : finiteSignalField (fun i => (mA i).comap (X i)) Finset.univ = mAll := by
    simp [mAll, finiteSignalField, MeasurableSpace.comap_process_pi]
  have hAllStrict : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mAll] x| < 1 := by
    rw [← hf]
    exact abs_condExp_spin_finiteSignalField_lt_one (fun i => (hX i).comap_le)
      hS hstrict hfair hFields Finset.univ ⟨a, Finset.mem_univ a⟩
  have hPairInd (s : IsingSpin) : Indep mAll (mB.comap Y) (cond rho {x | S x = s}) := by
    exact (indepFun_cond_fiber_of_condIndepFun hS hY hAll hOwn s).symm
  have hPair := spinInformation_sup_le_add hAll.comap_le hY.comap_le hS
    hAllStrict hOwnStrict hfair hPairInd hOwnSym
  have hFamily := condExp_finite_observation_secondMoment_le_sum_sub_loss
    hS hX hCI hfair hstrict hsym hab haTheta hbTheta htheta
  change spinInformation rho S
    ((mB.prod MeasurableSpace.pi).comap (fun x => (Y x, fun i => X i x))) ≤ _
  rw [MeasurableSpace.comap_prodMk, sup_comm]
  change spinInformation rho S (mAll ⊔ mB.comap Y) ≤ _
  unfold spinInformation at hPair ⊢
  linarith

end Observations

end Problem367

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss_oai.{u_1, u_2, u_3, u_4} := @OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss_oai.{u_1, u_2, u_3, u_4}

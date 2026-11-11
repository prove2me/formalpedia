-- Prove2me | solution 1 for OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:53.160733+00:00
-- url     : https://prove2.me/submissions/f18a20d4-4def-4e25-9516-6913ba603fbf

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_exists_gaussianComponentField_critical_moment_tail

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal

namespace Problem367
namespace CavityPair

variable {ψ : ℝ → ℝ} {θ : ℝ≥0}

theorem solve_swap (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) :
    solve hψ hθ z.swap = (solve hψ hθ z).swap := by
  apply solve_eq hψ hθ
  exact ⟨(solve_spec hψ hθ z).2, (solve_spec hψ hθ z).1⟩

end CavityPair
end Problem367

end

end OAI
end

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

lemma abs_tanh_le_abs_response (z : ℝ) : |Real.tanh z| ≤ |z| := by
  have h := lipschitzWith_tanh_response.dist_le_mul z 0
  simpa [Real.dist_eq] using h

lemma log_responseAttenuation_small_field {theta R x y : ℝ}
    (hθ : theta ^ 2 ≤ 1) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)| ≤
      (2 * R) * |x - y| := by
  have h := (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hasDerivAt_log_responseAttenuation hθ z).differentiableAt)
    (C := 2 * R) (fun z hz => ?_) (abs_le.mp hy) (abs_le.mp hx)
  · simpa only [Real.norm_eq_abs] using h
  · rw [Real.norm_eq_abs]
    have hzR : |z| ≤ R := abs_le.mpr hz
    exact (abs_deriv_log_responseAttenuation_le hθ z).trans
      (by nlinarith [abs_tanh_le_abs_response z])

lemma log_responseAttenuation_small_field_sq {theta R x y : ℝ}
    (hθ : theta ^ 2 ≤ 1) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)) ^ 2 ≤
      4 * R ^ 2 * (x - y) ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  have h := log_responseAttenuation_small_field hθ hx hy
  have hsq := (sq_le_sq₀ (abs_nonneg
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)))
    (mul_nonneg (mul_nonneg (by norm_num) hR) (abs_nonneg (x - y)))).mpr h
  norm_num [mul_pow, sq_abs, mul_assoc] at hsq ⊢
  exact hsq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Homeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem cavityFromSites_eq {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    {z p : ℝ × ℝ}
    (hp : p.1 + cavityMessage theta p.2 = z.1 ∧
      p.2 + cavityMessage theta p.1 = z.2) : cavityFromSites h0 h1 z = p :=
  CavityPair.solve_eq (lipschitzWith_cavityMessage h0 h1.le) h1 hp

theorem cavityFromSites_swap {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : cavityFromSites h0 h1 z.swap = (cavityFromSites h0 h1 z).swap :=
  CavityPair.solve_swap (lipschitzWith_cavityMessage h0 h1.le) h1 z

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_AttenuationMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma log_responseAttenuation_sub_sq_le {theta x y : ℝ} (hθ : theta ^ 2 ≤ 1) :
    (Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)) ^ 2 ≤
      4 * (x - y) ^ 2 := by
  have h := (lipschitzWith_log_responseAttenuation hθ).dist_le_mul x y
  have ha : |Real.log (responseAttenuation theta x) - Real.log (responseAttenuation theta y)| ≤
      2 * |x - y| := by simpa [Real.dist_eq] using h
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (abs_nonneg (x - y)))).mpr ha
  norm_num [mul_pow, sq_abs] at hs ⊢
  exact hs

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {Y Y' : Ω → ℝ}

lemma integrable_log_responseAttenuation_sub_sq
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ) :
    Integrable (fun w =>
      (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2) μ := by
  have hm : Measurable (fun x => Real.log (responseAttenuation theta x)) :=
    (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  apply (hInt.const_mul 4).mono'
    (((hm.comp hY).sub (hm.comp hY')).pow_const 2).aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact log_responseAttenuation_sub_sq_le hθ

lemma integral_log_responseAttenuation_sub_sq_le [IsProbabilityMeasure μ]
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ)
    {R H V B : ℝ} (hH : 0 ≤ H)
    (hBound : ∀ᵐ w ∂μ, |Y w - Y' w| ≤ H)
    (hVar : (∫ w, (Y w - Y' w) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {w | ¬ (|Y w| ≤ R ∧ |Y' w| ≤ R)} ≤ B) :
    (∫ w, (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2 ∂μ) ≤
      4 * R ^ 2 * V + min (4 * V) (4 * H ^ 2 * B) := by
  let D : Ω → ℝ := fun w =>
    (Real.log (responseAttenuation theta (Y w)) -
      Real.log (responseAttenuation theta (Y' w))) ^ 2
  let E : Ω → ℝ := fun w => (Y w - Y' w) ^ 2
  let G : Set Ω := {w | |Y w| ≤ R ∧ |Y' w| ≤ R}
  have hG : MeasurableSet G :=
    (measurableSet_le hY.abs measurable_const).inter
      (measurableSet_le hY'.abs measurable_const)
  have hDI : Integrable D μ := integrable_log_responseAttenuation_sub_sq hθ hY hY' hInt
  have hEI : Integrable E μ := hInt
  have hD_nonneg : ∀ w, 0 ≤ D w := fun w => sq_nonneg _
  have hE_nonneg : ∀ w, 0 ≤ E w := fun w => sq_nonneg _
  have hglobal : ∀ w, D w ≤ 4 * E w := fun w => log_responseAttenuation_sub_sq_le hθ
  have hglobal_int : (∫ w, D w ∂μ) ≤ 4 * V := by
    calc
      (∫ w, D w ∂μ) ≤ ∫ w, 4 * E w ∂μ :=
        integral_mono hDI (hEI.const_mul 4) hglobal
      _ = 4 * ∫ w, E w ∂μ := integral_const_mul _ _
      _ ≤ 4 * V := mul_le_mul_of_nonneg_left hVar (by norm_num)
  have hgood : (∫ w in G, D w ∂μ) ≤ 4 * R ^ 2 * V := by
    calc
      (∫ w in G, D w ∂μ) ≤ ∫ w in G, (4 * R ^ 2) * E w ∂μ := by
        apply setIntegral_mono_on hDI.integrableOn ((hEI.const_mul _).integrableOn) hG
        intro w hw
        exact log_responseAttenuation_small_field_sq hθ hw.1 hw.2
      _ = (4 * R ^ 2) * ∫ w in G, E w ∂μ := integral_const_mul _ _
      _ ≤ (4 * R ^ 2) * ∫ w, E w ∂μ :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hEI (Filter.Eventually.of_forall hE_nonneg))
          (by positivity)
      _ ≤ 4 * R ^ 2 * V := mul_le_mul_of_nonneg_left hVar (by positivity)
  have hbad_var : (∫ w in Gᶜ, D w ∂μ) ≤ 4 * V := by
    exact (setIntegral_le_integral hDI (Filter.Eventually.of_forall hD_nonneg)).trans hglobal_int
  have hbad_tail : (∫ w in Gᶜ, D w ∂μ) ≤ 4 * H ^ 2 * B := by
    calc
      (∫ w in Gᶜ, D w ∂μ) ≤ ∫ _w in Gᶜ, 4 * H ^ 2 ∂μ := by
        apply setIntegral_mono_ae hDI.integrableOn (integrable_const _).integrableOn
        filter_upwards [hBound] with w hw
        have hs : E w ≤ H ^ 2 := by
          have h := (sq_le_sq₀ (abs_nonneg _) hH).mpr hw
          simpa [E, sq_abs] using h
        exact (hglobal w).trans (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ = 4 * H ^ 2 * μ.real Gᶜ := by rw [setIntegral_const]; simp [mul_comm]
      _ ≤ 4 * H ^ 2 * B := mul_le_mul_of_nonneg_left hTail (by positivity)
  have hsplit := integral_add_compl hG hDI
  change (∫ w, D w ∂μ) ≤ _
  rw [← hsplit]
  exact add_le_add hgood (le_min hbad_var hbad_tail)

lemma measureReal_bad_field_le [IsFiniteMeasure μ] {R B₁ B₂ : ℝ}
    (hTail : μ.real {w | R < |Y w|} ≤ B₁)
    (hTail' : μ.real {w | R < |Y' w|} ≤ B₂) :
    μ.real {w | ¬ (|Y w| ≤ R ∧ |Y' w| ≤ R)} ≤ B₁ + B₂ := by
  have hset : {w | ¬ (|Y w| ≤ R ∧ |Y' w| ≤ R)} =
      {w | R < |Y w|} ∪ {w | R < |Y' w|} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or, not_le]
  rw [hset]
  exact (measureReal_union_le _ _).trans (add_le_add hTail hTail')

lemma integral_log_responseAttenuation_sub_sq_le_of_marginal_tails
    [IsProbabilityMeasure μ]
    (hθ : theta ^ 2 ≤ 1) (hY : Measurable Y) (hY' : Measurable Y')
    (hInt : Integrable (fun w => (Y w - Y' w) ^ 2) μ)
    {R H V B₁ B₂ : ℝ} (hH : 0 ≤ H)
    (hBound : ∀ᵐ w ∂μ, |Y w - Y' w| ≤ H)
    (hVar : (∫ w, (Y w - Y' w) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {w | R < |Y w|} ≤ B₁)
    (hTail' : μ.real {w | R < |Y' w|} ≤ B₂) :
    (∫ w, (Real.log (responseAttenuation theta (Y w)) -
        Real.log (responseAttenuation theta (Y' w))) ^ 2 ∂μ) ≤
      4 * R ^ 2 * V + min (4 * V) (4 * H ^ 2 * (B₁ + B₂)) := by
  exact integral_log_responseAttenuation_sub_sq_le hθ hY hY' hInt hH
    hBound hVar (measureReal_bad_field_le hTail hTail')

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CoupledAttenuation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367

theorem cavity_pair_sub_sq_le
    {theta x y x' y' H K H' K' : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hx : x + cavityMessage theta y = H)
    (hy : y + cavityMessage theta x = K)
    (hx' : x' + cavityMessage theta y' = H')
    (hy' : y' + cavityMessage theta x' = K') :
    (x - x') ^ 2 ≤
      ((1 + theta) / (1 - theta ^ 2) ^ 2) *
        ((H - H') ^ 2 + theta * (K - K') ^ 2) := by
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hdist := CavityPair.stability_fst
    (lipschitzWith_cavityMessage hθ0 hθ1.le)
    (show (⟨theta, hθ0⟩ : ℝ≥0) < 1 from hθ1) hx hy hx' hy'
  change dist x x' ≤ (dist H H' + theta * dist K K') / (1 - theta ^ 2) at hdist
  have habs : |x - x'| ≤
      (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := by
    simpa only [Real.dist_eq, NNReal.coe_mk] using hdist
  have hsquare := (sq_le_sq₀ (abs_nonneg (x - x'))
    (show 0 ≤ (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) by positivity)).2 habs
  rw [sq_abs, div_pow] at hsquare
  have hweighted : (|H - H'| + theta * |K - K'|) ^ 2 ≤
      (1 + theta) * ((H - H') ^ 2 + theta * (K - K') ^ 2) := by
    have h := mul_nonneg hθ0 (sq_nonneg (|H - H'| - |K - K'|))
    nlinarith [sq_abs (H - H'), sq_abs (K - K')]
  calc
    (x - x') ^ 2 ≤ (|H - H'| + theta * |K - K'|) ^ 2 /
        (1 - theta ^ 2) ^ 2 := hsquare
    _ ≤ ((1 + theta) * ((H - H') ^ 2 + theta * (K - K') ^ 2)) /
        (1 - theta ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hweighted (sq_nonneg _)
    _ = _ := by ring

theorem cavity_pair_sub_abs_le
    {theta x y x' y' H K H' K' M : ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hx : x + cavityMessage theta y = H)
    (hy : y + cavityMessage theta x = K)
    (hx' : x' + cavityMessage theta y' = H')
    (hy' : y' + cavityMessage theta x' = K')
    (hH : |H - H'| ≤ M) (hK : |K - K'| ≤ M) :
    |x - x'| ≤ M / (1 - theta) := by
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hminus : 1 - theta ≠ 0 := by linarith
  have hplus : 1 + theta ≠ 0 := by linarith
  have hdist := CavityPair.stability_fst
    (lipschitzWith_cavityMessage hθ0 hθ1.le)
    (show (⟨theta, hθ0⟩ : ℝ≥0) < 1 from hθ1) hx hy hx' hy'
  change dist x x' ≤ (dist H H' + theta * dist K K') / (1 - theta ^ 2) at hdist
  have habs : |x - x'| ≤
      (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := by
    simpa only [Real.dist_eq, NNReal.coe_mk] using hdist
  calc
    |x - x'| ≤ (|H - H'| + theta * |K - K'|) / (1 - theta ^ 2) := habs
    _ ≤ (M + theta * M) / (1 - theta ^ 2) := by gcongr
    _ = M / (1 - theta) := by
      field_simp
      ring

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {theta : ℝ} {X Y X' Y' H K H' K' : Ω → ℝ}

theorem integrable_cavity_pair_sub_sq
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω) :
    Integrable (fun ω => (X ω - X' ω) ^ 2) μ := by
  apply ((hH.add (hK.const_mul theta)).const_mul
    ((1 + theta) / (1 - theta ^ 2) ^ 2)).mono'
    (((hX.sub hX').pow_const 2).aestronglyMeasurable)
  filter_upwards [heq] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact cavity_pair_sub_sq_le hθ0 hθ1 hω.1 hω.2.1 hω.2.2.1 hω.2.2.2

theorem integral_cavity_pair_sub_sq_le
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V : ℝ}
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V) :
    (∫ ω, (X ω - X' ω) ^ 2 ∂μ) ≤ V / (1 - theta) ^ 2 := by
  have hXint := integrable_cavity_pair_sub_sq hθ0 hθ1 hX hX' hH hK heq
  have hden : 0 < 1 - theta ^ 2 := by nlinarith
  have hminus : 1 - theta ≠ 0 := by linarith
  have hplus : 1 + theta ≠ 0 := by linarith
  have hcoef : 0 ≤ (1 + theta) / (1 - theta ^ 2) ^ 2 := by positivity
  calc
    (∫ ω, (X ω - X' ω) ^ 2 ∂μ) ≤
        ∫ ω, ((1 + theta) / (1 - theta ^ 2) ^ 2) *
          ((H ω - H' ω) ^ 2 + theta * (K ω - K' ω) ^ 2) ∂μ := by
      apply integral_mono_ae hXint
        ((hH.add (hK.const_mul theta)).const_mul _)
      filter_upwards [heq] with ω hω
      exact cavity_pair_sub_sq_le hθ0 hθ1 hω.1 hω.2.1 hω.2.2.1 hω.2.2.2
    _ = ((1 + theta) / (1 - theta ^ 2) ^ 2) *
        ((∫ ω, (H ω - H' ω) ^ 2 ∂μ) +
          theta * ∫ ω, (K ω - K' ω) ^ 2 ∂μ) := by
      rw [integral_const_mul, integral_add hH (hK.const_mul theta), integral_const_mul]
    _ ≤ ((1 + theta) / (1 - theta ^ 2) ^ 2) * (V + theta * V) := by
      gcongr
    _ = V / (1 - theta) ^ 2 := by
      field_simp
      ring

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
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

theorem exists_treeAut_map {d : ℕ} (u v : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = v := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root u
  obtain ⟨h, hh⟩ := exists_treeAut_to_root v
  refine ⟨g.trans h.symm, ?_⟩
  change h.toEquiv.symm (g.toEquiv u) = v
  rw [hg, ← hh]
  exact h.toEquiv.symm_apply_apply v

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Array
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

theorem field_reverse (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H w v = (cavityFromSites h0 h1 (H v, H w)).2 := by
  exact congrArg Prod.fst (cavityFromSites_swap h0 h1 (H v, H w))

theorem field_spec (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H v w + cavityMessage theta (field h0 h1 H w v) = H v := by
  rw [field_reverse h0 h1 H v w]
  exact (cavityFromSites_spec h0 h1 (H v, H w)).1

section Joining

theorem measurable_pairRelabel (g : TreeAut d) : Measurable (pairRelabel g) :=
  (measurable_relabel g).prodMap (measurable_relabel g)

theorem site_sub_identDistrib {ν : Measure (SitePair d)}
    (hinv : ∀ g : TreeAut d, MeasurePreserving (pairRelabel g) ν ν)
    (u v : TreeVertex d) :
    IdentDistrib (fun p : SitePair d => p.1 u - p.2 u)
      (fun p : SitePair d => p.1 v - p.2 v) ν ν := by
  obtain ⟨g, hg⟩ := exists_treeAut_map u v
  have hm (w : TreeVertex d) : Measurable (fun p : SitePair d => p.1 w - p.2 w) :=
    ((measurable_pi_apply w).comp measurable_fst).sub
      ((measurable_pi_apply w).comp measurable_snd)
  refine ⟨(hm u).aemeasurable, (hm v).aemeasurable, ?_⟩
  calc
    ν.map (fun p : SitePair d => p.1 u - p.2 u) =
        ν.map ((fun p : SitePair d => p.1 v - p.2 v) ∘ pairRelabel g) := by
      congr 1
      funext p
      simp [pairRelabel, relabel, ← hg]
    _ = (ν.map (pairRelabel g)).map (fun p : SitePair d => p.1 v - p.2 v) :=
      (Measure.map_map (hm v) (measurable_pairRelabel g)).symm
    _ = ν.map (fun p : SitePair d => p.1 v - p.2 v) := by rw [(hinv g).map_eq]

end Joining

end Problem367.CavityArray

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

theorem artanh_binaryFusion_scaled {theta x y : ℝ}
    (hθ : |theta| < 1) (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh ((x + theta * y) / (1 + theta * x * y)) =
      Real.artanh x + cavityMessage theta (Real.artanh y) := by
  have hprod : |theta * y| < 1 := binaryFusion_abs_mul_lt_one hθ hy
  have h := artanh_binaryFusion hx hprod
  simpa only [binaryFusion, cavityMessage, Real.tanh_artanh (abs_lt.mp hy),
    mul_left_comm, mul_assoc] using h

theorem artanh_binaryFusion_scaled_of_mem {theta x y : ℝ}
    (hθ : theta ∈ Set.Ioo (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.artanh ((x + theta * y) / (1 + theta * x * y)) =
      Real.artanh x + cavityMessage theta (Real.artanh y) :=
  artanh_binaryFusion_scaled (abs_lt.mpr hθ) (abs_lt.mpr hx) (abs_lt.mpr hy)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FieldL2Limit
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

private theorem measurable_artanh_field : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem tendsto_integral_sq_sub_posterior_fields
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ m) (f X : Ω → ℝ) {K : ℝ}
    (hb : ∀ n, ∀ᵐ ω ∂μ,
      Real.tanh (X ω - K) ≤ (μ[f | F n]) ω ∧
        (μ[f | F n]) ω ≤ Real.tanh (X ω + K)) :
    Tendsto (fun n => ∫ ω,
      (Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hs : (⨆ n, F n) ≤ m := iSup_le (fun n => F.le n)
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun ω => Real.artanh ((μ[f | F n]) ω)) μ :=
    (measurable_artanh_field.comp
      (stronglyMeasurable_condExp.mono (F.le n)).measurable).aestronglyMeasurable
  have hm' : AEStronglyMeasurable
      (fun ω => Real.artanh ((μ[f | ⨆ n, F n]) ω)) μ :=
    (measurable_artanh_field.comp
      (stronglyMeasurable_condExp.mono hs).measurable).aestronglyMeasurable
  have hlim := tendsto_posterior_fields_ae μ F f X K hb
  have hbfield (n : ℕ) : ∀ᵐ ω ∂μ,
      |Real.artanh ((μ[f | F n]) ω) - X ω| ≤ K := by
    filter_upwards [hb n] with ω hω
    exact (posterior_field_limit_of_tanh_bounds
      (u := fun _ : ℕ => (μ[f | F n]) ω) tendsto_const_nhds
      (fun _ => hω)).2.1
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ,
      ‖(Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2‖ ≤ (2 * K) ^ 2 := by
    filter_upwards [hbfield n, hlim] with ω hn hω
    have hd : |Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)| ≤ 2 * K := by
      calc
        _ = |(Real.artanh ((μ[f | F n]) ω) - X ω) -
            (Real.artanh ((μ[f | ⨆ n, F n]) ω) - X ω)| := by congr 1; ring
        _ ≤ |Real.artanh ((μ[f | F n]) ω) - X ω| +
            |Real.artanh ((μ[f | ⨆ n, F n]) ω) - X ω| := abs_sub _ _
        _ ≤ 2 * K := by linarith [hω.2.1]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hzero : ∀ᵐ ω ∂μ, Tendsto
      (fun n => (Real.artanh ((μ[f | F n]) ω) -
        Real.artanh ((μ[f | ⨆ n, F n]) ω)) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with ω hω
    simpa using (hω.2.2.sub_const (Real.artanh ((μ[f | ⨆ n, F n]) ω))).pow 2
  simpa using tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (2 * K) ^ 2) (fun n => ((hm n).sub hm').pow 2)
    (integrable_const _) hbound hzero

open PlantedSymmetry

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_FieldL2Limit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

private theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem measurable_infiniteCavityField {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (v w : TreeVertex d) : Measurable (infiniteCavityField hbeta v w) := by
  exact (CavityArray.measurable_field_apply _ _ v w).comp
    (Measurable.of_eval (fun u => measurable_artanh.comp
      (measurable_infiniteGibbsSpinMean beta u)))

end CavityFieldLimit

open CavityFieldLimit

theorem HasFreeIsingLaw.exhaustionSiteField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n))
    (hex : ∀ u, ∃ n, u ∈ D n) (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteSiteField beta (D n) ⟨v, hv n⟩ (observation t p))
        atTop (𝓝 (Real.artanh (infiniteGibbsSpinMean beta v (observation t p)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta (D n) (hconn n) t ⟨v, hv n⟩
  have hlim := tendsto_posterior_fields_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) ((d : ℝ) * beta) hb
  rw [finiteObservationFiltration_iSup D hD hex t] at hlim
  have hce (n : ℕ) := hμ.finiteObservation_condExp (D n) (hconn n) t
    (fun eta => spinSign (eta ⟨v, hv n⟩))
  filter_upwards [hlim, ae_all_iff.mpr hce,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hp hce hinf
  convert hp.2.2 using 1
  · ext n
    exact congrArg Real.artanh (hce n).symm
  · exact congrArg (fun x : ℝ => 𝓝 (Real.artanh x)) hinf

theorem HasFreeIsingLaw.exhaustionCavityField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ u, ∃ n, u ∈ D n)
    (v w : TreeVertex d) (hv : ∀ n, v ∈ D n) (hw : ∀ n, w ∈ D n)
    (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteCavityField hbeta (D n) ⟨v, hv n⟩ ⟨w, hw n⟩
        (observation t p)) atTop (𝓝 (infiniteCavityField hbeta v w (observation t p))) := by
  filter_upwards [hμ.exhaustionSiteField_tendsto_ae hbeta D hD hconn hex v hv t,
    hμ.exhaustionSiteField_tendsto_ae hbeta D hD hconn hex w hw t] with p hp hq
  exact (continuous_fst.comp (continuous_cavityFromSites
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta))).continuousAt.tendsto.comp
      (hp.prodMk_nhds hq)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_CompensatedSquareEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace Problem367.DiscrepancyEnergy

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem secondMoment_le_of_ae_abs_le [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ} {t H : ℝ}
    (hInt : Integrable (fun ω => (X t ω) ^ 2) μ)
    (hbound : ∀ᵐ ω ∂μ, |X t ω| ≤ H) :
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hsq : ∀ᵐ ω ∂μ, (X t ω) ^ 2 ≤ H ^ 2 := by
    filter_upwards [hbound] with ω hω
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hω)).2 hω
  calc
    (∫ ω, (X t ω) ^ 2 ∂μ) ≤ ∫ _ : Ω, H ^ 2 ∂μ := integral_mono_ae hInt (integrable_const _) hsq
    _ = H ^ 2 := by simp

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

theorem ConnectedFinset.prefix_mem_of_min_length_le {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {u v : TreeVertex d} (hv : v ∈ D) (huv : u.1 <+: v.1)
    (hru : r.1.length ≤ u.1.length) : u ∈ D := by
  have aux : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → v ∈ D →
      u.1 <+: v.1 → u ∈ D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv huv
      by_cases huv_eq : u = v
      · exact huv_eq.symm ▸ hv
      · have hvne : v ≠ r := by
          intro heq
          subst v
          exact huv_eq (Subtype.ext (huv.eq_of_length_le hru))
        have hp := hD.parent_mem_of_ne_min hr hmin hv hvne
        have hvnil := ConnectedFinset.ne_nil_of_ne_min hmin hv hvne
        have hpos : 0 < v.1.length := List.length_pos_iff.mpr hvnil
        have hplen : (parentVertex v).1.length < n := by
          rw [parentVertex_length]
          omega
        have hup : u.1 <+: (parentVertex v).1 := by
          apply List.prefix_of_prefix_length_le huv (List.dropLast_prefix v.1)
          have hle := huv.length_le
          have hneq : u.1.length ≠ v.1.length := by
            intro heq
            exact huv_eq (Subtype.ext (huv.eq_of_length heq))
          change u.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        exact ih _ hplen _ rfl hp hup
  exact aux _ v rfl hv huv

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteComponentGeometry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem ConnectedFinset.prefix_mem_of_root_mem {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D) {u v : TreeVertex d}
    (hv : v ∈ D) (huv : u.1 <+: v.1) : u ∈ D :=
  hD.prefix_mem_of_min_length_le hroot (fun _ _ => Nat.zero_le _) hv huv (Nat.zero_le _)

theorem ConnectedFinset.filter_prefix_connected {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D) (r : TreeVertex d) (hr : r ∈ D) :
    ConnectedFinset (D.filter (fun v => r.1 <+: v.1)) := by
  classical
  let E := D.filter (fun v => r.1 <+: v.1)
  have hrE : r ∈ E := Finset.mem_filter.mpr ⟨hr, List.prefix_refl _⟩
  let R := fun x y : TreeVertex d => x ∈ E ∧ y ∈ E ∧ treeAdj x y
  have paths : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → v ∈ E →
      Relation.ReflTransGen R r v ∧ Relation.ReflTransGen R v r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv
      by_cases heq : v = r
      · subst v
        exact ⟨.refl, .refl⟩
      have hv' := Finset.mem_filter.mp hv
      have hnil : v.1 ≠ [] := by
        intro he
        have hre : r.1 = [] := by
          have hlen : r.1.length ≤ 0 := by simpa only [he, List.length_nil] using hv'.2.length_le
          exact List.length_eq_zero_iff.mp (by omega)
        exact heq (Subtype.ext (he.trans hre.symm))
      have hadj := treeAdj_parentVertex hnil
      have hpD : parentVertex v ∈ D :=
        hD.prefix_mem_of_root_mem hroot hv'.1 (List.dropLast_prefix v.1)
      have hpE : parentVertex v ∈ E := Finset.mem_filter.mpr
        ⟨hpD, treeAdj_preserves_prefix hv'.2 hadj.symm heq⟩
      have hlt : (parentVertex v).1.length < n := by
        have hpos := List.length_pos_iff.mpr hnil
        rw [parentVertex_length]
        omega
      obtain ⟨hforward, hbackward⟩ := ih _ hlt _ rfl hpE
      exact ⟨hforward.trans (.single ⟨hpE, hv, hadj⟩),
        (Relation.ReflTransGen.single ⟨hv, hpE, hadj.symm⟩).trans hbackward⟩
  refine ⟨⟨r, hrE⟩, ?_⟩
  intro u hu v hv
  exact (paths _ u rfl hu).2.trans (paths _ v rfl hv).1

theorem rootComponentFinset_connected {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    ConnectedFinset (rootComponentFinset D c) :=
  hD.filter_prefix_connected hroot ⟨[c], List.IsChain.singleton c⟩ hc

theorem rootComponentFinset_union_complement {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : rootComponentFinset D c ∪ rootComplementFinset D c = D := by
  classical
  ext v
  simp only [Finset.mem_union, mem_rootComponentFinset, mem_rootComplementFinset]
  tauto

theorem rootComponentFinset_disjoint_complement {d : ℕ} (D : Finset (TreeVertex d))
    (c : Fin d) : Disjoint (rootComponentFinset D c) (rootComplementFinset D c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (mem_rootComplementFinset.mp hw).2 (mem_rootComponentFinset.mp hv).2

theorem root_component_crossing_edge {d : ℕ} {c : Fin d} {u v : TreeVertex d}
    (hu : [c] <+: u.1) (hv : ¬ [c] <+: v.1) (hadj : treeAdj u v) :
    u = ⟨[c], List.IsChain.singleton c⟩ ∧ v = ConnectedHull.root d := by
  have hueq : u = (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) := by
    by_contra hne
    exact hv (treeAdj_preserves_prefix (r := ⟨[c], List.IsChain.singleton c⟩) hu hadj hne)
  refine ⟨hueq, ?_⟩
  subst u
  rcases hadj with ⟨a, ha⟩ | ⟨a, ha⟩
  · exfalso
    apply hv
    rw [ha]
    exact List.prefix_append _ _
  · apply Subtype.ext
    change v.1 = []
    have hlen := congrArg List.length ha
    simp only [List.length_singleton, List.length_append] at hlen
    exact List.length_eq_zero_iff.mp (by omega)

theorem singleton_prefix_iff_cons {d : ℕ} (c : Fin d) (v : TreeVertex d) :
    [c] <+: v.1 ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, hw.symm⟩

private theorem mem_inducedEdges_cut {d : ℕ} {D : Finset (TreeVertex d)}
    {u v : TreeVertex d} : (u, v) ∈ inducedEdges D ↔
      u ∈ D ∧ v ∈ D ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  simp [inducedEdges, and_assoc]

theorem inducedEdges_rootComponent_split {d : ℕ} {D : Finset (TreeVertex d)}
    (hroot : ConnectedHull.root d ∈ D) (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) :
    inducedEdges D = insert (ConnectedHull.root d, ⟨[c], List.IsChain.singleton c⟩)
      (inducedEdges (rootComponentFinset D c) ∪ inducedEdges (rootComplementFinset D c)) := by
  classical
  ext ⟨u, v⟩
  constructor
  · intro he
    obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
    by_cases hcu : [c] <+: u.1
    · by_cases hcv : [c] <+: v.1
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_union.mpr
        exact Or.inl (mem_inducedEdges_cut.mpr
          ⟨mem_rootComponentFinset.mpr ⟨hu, hcu⟩,
            mem_rootComponentFinset.mpr ⟨hv, hcv⟩, hadj, hlen⟩)
      · obtain ⟨rfl, rfl⟩ := root_component_crossing_edge hcu hcv hadj
        change 1 < 0 at hlen
        omega
    · by_cases hcv : [c] <+: v.1
      · obtain ⟨rfl, rfl⟩ := root_component_crossing_edge hcv hcu hadj.symm
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_union.mpr
        exact Or.inr (mem_inducedEdges_cut.mpr
          ⟨mem_rootComplementFinset.mpr ⟨hu, hcu⟩,
            mem_rootComplementFinset.mpr ⟨hv, hcv⟩, hadj, hlen⟩)
  · intro he
    rcases Finset.mem_insert.mp he with heq | he
    · have hu : u = ConnectedHull.root d := congrArg Prod.fst heq
      have hv : v = (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) := congrArg Prod.snd heq
      subst u
      subst v
      exact mem_inducedEdges_cut.mpr ⟨hroot, hc, Or.inl ⟨c, rfl⟩, by change 0 < 1; omega⟩
    · rcases Finset.mem_union.mp he with he | he
      · obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
        exact mem_inducedEdges_cut.mpr ⟨(mem_rootComponentFinset.mp hu).1,
          (mem_rootComponentFinset.mp hv).1, hadj, hlen⟩
      · obtain ⟨hu, hv, hadj, hlen⟩ := mem_inducedEdges_cut.mp he
        exact mem_inducedEdges_cut.mpr ⟨(mem_rootComplementFinset.mp hu).1,
          (mem_rootComplementFinset.mp hv).1, hadj, hlen⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteSpinCoupling
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteSpinCoupling

variable {A B : Type*} [Fintype A] [Fintype B]

lemma mean_eq (E : A → ℝ) (a : A → IsingSpin) :
    mean E a = numerator E a / partition E := by
  simp [mean, numerator, partition, FinitePosterior.mean,
    FinitePosterior.partition, FinitePosterior.weight]

lemma partition_pos [Nonempty A] (E : A → ℝ) : 0 < partition E :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype A] [Fintype B] in
lemma exp_interaction (beta : ℝ) (a b : IsingSpin) :
    Real.exp (beta * spinSign a * spinSign b) =
      Real.cosh beta + Real.sinh beta * spinSign a * spinSign b := by
  cases a <;> cases b <;>
    simp [spinSign, ← sub_eq_add_neg, Real.cosh_add_sinh, Real.cosh_sub_sinh]

omit [Fintype A] [Fintype B] in
lemma exp_energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) (x : A × B) :
    Real.exp (energy beta EA EB a b x) =
      Real.cosh beta * Real.exp (EA x.1) * Real.exp (EB x.2) +
      Real.sinh beta * (spinSign (a x.1) * Real.exp (EA x.1)) *
        (spinSign (b x.2) * Real.exp (EB x.2)) := by
  rw [energy, Real.exp_add, Real.exp_add, exp_interaction]
  ring

theorem partition_energy (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    partition (energy beta EA EB a b) =
      Real.cosh beta * partition EA * partition EB +
      Real.sinh beta * numerator EA a * numerator EB b := by
  simp only [partition, Fintype.sum_prod_type, exp_energy,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, numerator]

theorem numerator_energy_fst (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    numerator (energy beta EA EB a b) (fun x => a x.1) =
      Real.cosh beta * numerator EA a * partition EB +
      Real.sinh beta * partition EA * numerator EB b := by
  have heq (x : A × B) :
      spinSign (a x.1) * Real.exp (energy beta EA EB a b x) =
        Real.cosh beta * (spinSign (a x.1) * Real.exp (EA x.1)) * Real.exp (EB x.2) +
        Real.sinh beta * Real.exp (EA x.1) *
          (spinSign (b x.2) * Real.exp (EB x.2)) := by
    rw [exp_energy]
    cases a x.1 <;> simp only [spinSign_neg, spinSign_pos] <;> ring
  simp only [numerator, Fintype.sum_prod_type, heq,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, partition]

theorem mean_energy_fst [Nonempty A] [Nonempty B]
    (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    mean (energy beta EA EB a b) (fun x => a x.1) =
      (mean EA a + Real.tanh beta * mean EB b) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  rw [mean_eq, numerator_energy_fst, partition_energy, mean_eq, mean_eq]
  rw [Real.tanh_eq_sinh_div_cosh]
  have hA := (partition_pos EA).ne'
  have hB := (partition_pos EB).ne'
  have hC := (Real.cosh_pos beta).ne'
  field_simp

theorem mean_equiv {S : Type*} [Fintype S] (e : S ≃ A)
    (E : A → ℝ) (a : A → IsingSpin) :
    mean (E ∘ e) (a ∘ e) = mean E a := by
  simp only [mean_eq, numerator, partition, Function.comp_apply]
  rw [e.sum_comp (fun x => spinSign (a x) * Real.exp (E x)),
    e.sum_comp (fun x => Real.exp (E x))]

theorem mean_energy_snd [Nonempty A] [Nonempty B]
    (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin) :
    mean (energy beta EA EB a b) (fun x => b x.2) =
      (mean EB b + Real.tanh beta * mean EA a) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  have he : energy beta EA EB a b =
      energy beta EB EA b a ∘ Equiv.prodComm A B := by
    funext x
    simp only [energy, Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [he]
  change mean (energy beta EB EA b a ∘ Equiv.prodComm A B)
    ((fun x : B × A => b x.1) ∘ Equiv.prodComm A B) = _
  rw [mean_equiv, mean_energy_fst]
  congr 1; ring

theorem mean_of_energy_split {S : Type*} [Fintype S]
    [Nonempty A] [Nonempty B] (e : S ≃ A × B)
    (E : S → ℝ) (beta : ℝ) (EA : A → ℝ) (EB : B → ℝ)
    (a : A → IsingSpin) (b : B → IsingSpin)
    (hE : ∀ x, E x = energy beta EA EB a b (e x)) :
    mean E (fun x => a (e x).1) =
      (mean EA a + Real.tanh beta * mean EB b) /
        (1 + Real.tanh beta * mean EA a * mean EB b) := by
  have he : E = energy beta EA EB a b ∘ e := funext hE
  rw [he]
  change mean (energy beta EA EB a b ∘ e) ((fun x : A × B => a x.1) ∘ e) = _
  rw [mean_equiv, mean_energy_fst]

end Problem367.FiniteSpinCoupling

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteIsingSplit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FiniteIsingSplit

variable {V : Type*} [DecidableEq V]

variable {d : ℕ}

lemma inducedEdges_endpoints {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    e.1 ∈ D ∧ e.2 ∈ D := by
  classical
  exact Finset.mem_product.mp (Finset.mem_filter.mp he).1

lemma observedEnergy_restrict (beta : ℝ) (D : Finset (TreeVertex d))
    (y : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    observedEnergy beta D y (D.restrict eta) =
      beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2) +
        ∑ v ∈ D, y v * spinSign (eta v) := by
  classical
  unfold observedEnergy FinitePosterior.fieldEnergy finiteIsingEnergy
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    have he' := inducedEdges_endpoints he
    simp [extendFiniteSpin, he'.1, he'.2]
  · exact Finset.sum_coe_sort D (fun v => y v * spinSign (eta v))

theorem observedEnergy_split_restrict (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    observedEnergy beta (A ∪ B) y ((A ∪ B).restrict eta) =
      observedEnergy beta A y (A.restrict eta) +
      observedEnergy beta B y (B.restrict eta) +
        beta * spinSign (eta u) * spinSign (eta v) := by
  classical
  have hdis : Disjoint (inducedEdges A) (inducedEdges B) := by
    apply Finset.disjoint_left.mpr
    intro e heA heB
    exact Finset.disjoint_left.mp hAB
      (inducedEdges_endpoints heA).1 (inducedEdges_endpoints heB).1
  have hnot : (u.1, v.1) ∉ inducedEdges A ∪ inducedEdges B := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.disjoint_left.mp hAB (inducedEdges_endpoints he).2 v.property
    · exact Finset.disjoint_left.mp hAB u.property (inducedEdges_endpoints he).1
  rw [observedEnergy_restrict, observedEnergy_restrict, observedEnergy_restrict,
    hEdges, Finset.sum_insert hnot, Finset.sum_union hdis, Finset.sum_union hAB]
  ring

theorem observedEnergy_split (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) (eta : ↥(A ∪ B) → IsingSpin) :
    observedEnergy beta (A ∪ B) y eta =
      FiniteSpinCoupling.energy beta (observedEnergy beta A y) (observedEnergy beta B y)
        (fun s => s u) (fun s => s v) (splitEquiv A B hAB eta) := by
  classical
  let sigma := extendFiniteSpin (A ∪ B) eta
  have hU : (A ∪ B).restrict sigma = eta := restrict_extendFiniteSpin _ _
  have hA : A.restrict sigma = (splitEquiv A B hAB eta).1 := by
    funext w
    exact extendFiniteSpin_apply (A ∪ B) eta ⟨w, Finset.mem_union_left B w.property⟩
  have hB : B.restrict sigma = (splitEquiv A B hAB eta).2 := by
    funext w
    exact extendFiniteSpin_apply (A ∪ B) eta ⟨w, Finset.mem_union_right A w.property⟩
  have hu : sigma u = (splitEquiv A B hAB eta).1 u := congrFun hA u
  have hv : sigma v = (splitEquiv A B hAB eta).2 v := congrFun hB v
  have h := observedEnergy_split_restrict beta A B hAB u v hEdges y sigma
  simpa only [hU, hA, hB, hu, hv, FiniteSpinCoupling.energy] using h

lemma mean_eq_fieldMean (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) :
    mean beta D v y = FinitePosterior.fieldMean (finiteIsingEnergy beta D)
      (fun eta w => spinSign (eta w)) (fun eta => spinSign (eta v)) (D.restrict y) := by
  simp only [mean, FiniteSpinCoupling.mean_eq, FiniteSpinCoupling.numerator,
    FiniteSpinCoupling.partition, observedEnergy, FinitePosterior.fieldMean]

theorem mean_union_fst (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    mean beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y =
      (mean beta A u y + Real.tanh beta * mean beta B v y) /
        (1 + Real.tanh beta * mean beta A u y * mean beta B v y) := by
  classical
  let : Nonempty (A → IsingSpin) := ⟨fun _ => .neg⟩
  let : Nonempty (B → IsingSpin) := ⟨fun _ => .neg⟩
  exact FiniteSpinCoupling.mean_of_energy_split (splitEquiv A B hAB)
    (observedEnergy beta (A ∪ B) y) beta (observedEnergy beta A y)
    (observedEnergy beta B y) (fun s => s u) (fun s => s v)
    (observedEnergy_split beta A B hAB u v hEdges y)

theorem mean_union_snd (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    mean beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y =
      (mean beta B v y + Real.tanh beta * mean beta A u y) /
        (1 + Real.tanh beta * mean beta A u y * mean beta B v y) := by
  classical
  let : Nonempty (A → IsingSpin) := ⟨fun _ => .neg⟩
  let : Nonempty (B → IsingSpin) := ⟨fun _ => .neg⟩
  have hE : observedEnergy beta (A ∪ B) y =
      FiniteSpinCoupling.energy beta (observedEnergy beta A y) (observedEnergy beta B y)
        (fun s => s u) (fun s => s v) ∘ splitEquiv A B hAB :=
    funext (observedEnergy_split beta A B hAB u v hEdges y)
  unfold mean
  rw [hE]
  change FiniteSpinCoupling.mean (_ ∘ splitEquiv A B hAB)
    ((fun s : (A → IsingSpin) × (B → IsingSpin) => s.2 v) ∘ splitEquiv A B hAB) = _
  rw [FiniteSpinCoupling.mean_equiv, FiniteSpinCoupling.mean_energy_snd]

lemma mean_mem_Ioo (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : mean beta D v y ∈ Set.Ioo (-1 : ℝ) 1 := by
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .neg⟩
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro eta
    change spinSign (eta v) = -1 ∨ spinSign (eta v) = 1
    cases eta v <;> simp [spinSign]
  · exact ⟨fun _ => .neg, rfl⟩
  · exact ⟨fun _ => .pos, rfl⟩

theorem field_union_fst (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    field beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y =
      field beta A u y + cavityMessage (Real.tanh beta) (field beta B v y) := by
  unfold field
  rw [mean_union_fst beta A B hAB u v hEdges y]
  exact artanh_binaryFusion_scaled_of_mem ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
    (mean_mem_Ioo beta A u y) (mean_mem_Ioo beta B v y)

theorem field_union_snd (beta : ℝ)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    field beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y =
      field beta B v y + cavityMessage (Real.tanh beta) (field beta A u y) := by
  unfold field
  rw [mean_union_snd beta A B hAB u v hEdges y]
  rw [show 1 + Real.tanh beta * mean beta A u y * mean beta B v y =
      1 + Real.tanh beta * mean beta B v y * mean beta A u y by ring]
  exact artanh_binaryFusion_scaled_of_mem
    ⟨Real.neg_one_lt_tanh beta, Real.tanh_lt_one beta⟩
    (mean_mem_Ioo beta B v y) (mean_mem_Ioo beta A u y)

theorem cavityFromSites_eq_component_fields {beta : ℝ} (hbeta : 0 ≤ beta)
    (A B : Finset (TreeVertex d)) (hAB : Disjoint A B)
    (u : A) (v : B)
    (hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B))
    (y : TreeVertex d → ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (field beta (A ∪ B) ⟨u, Finset.mem_union_left B u.property⟩ y,
        field beta (A ∪ B) ⟨v, Finset.mem_union_right A v.property⟩ y) =
      (field beta A u y, field beta B v y) := by
  apply cavityFromSites_eq
  exact ⟨(field_union_fst beta A B hAB u v hEdges y).symm,
    (field_union_snd beta A B hAB u v hEdges y).symm⟩

end Problem367.FiniteIsingSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem selectedObservationField_eq_of_range_eq {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hvw : Set.range v = Set.range w) :
    selectedObservationField F v = selectedObservationField F w :=
  le_antisymm (selectedObservationField_le_of_range_subset F hvw.subset)
    (selectedObservationField_le_of_range_subset F hvw.symm.subset)

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorLimit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem selectedObservationExhaustion_iSup {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (D : ℕ → Finset ι) (hD : Monotone D)
    (hex : ∀ i, ∃ n, i ∈ D n) :
    (⨆ n, selectedObservationExhaustion F hF v D hD n) =
      selectedObservationField F v := by
  change (⨆ n, selectedObservationField F (fun i : D n => v i.1)) = _
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    exact le_iSup_of_le i.1 le_rfl
  · apply iSup_le
    intro i
    obtain ⟨n, hn⟩ := hex i
    exact le_iSup_of_le n (le_iSup_of_le (⟨i, hn⟩ : D n) le_rfl)

private theorem tanh_bounds_of_interior_field_bound {z x K : ℝ}
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) (h : |Real.artanh z - x| ≤ K) :
    Real.tanh (x - K) ≤ z ∧ z ≤ Real.tanh (x + K) := by
  constructor
  · apply (Real.artanh_le_artanh_iff
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ hz).mp
    rw [Real.artanh_tanh]
    linarith [(abs_le.mp h).1]
  · apply (Real.artanh_le_artanh_iff hz
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).mp
    rw [Real.artanh_tanh]
    linarith [(abs_le.mp h).2]

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_limit
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (D : ℕ → Finset ι) (hD : Monotone D) (hex : ∀ i, ∃ n, i ∈ D n)
    (hr : ∀ n, r ∈ Set.range (fun i : D n => v i.1)) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (∀ᵐ p ∂ρ, Tendsto
      (fun n => Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p))
      atTop (𝓝 (Real.artanh (selectedPosterior ρ F v r p)))) ∧
    Tendsto (fun n => ∫ p,
      (Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p) -
        Real.artanh (selectedPosterior ρ F v r p)) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let := hμ.isProbabilityMeasure
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) := by
    have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul (t : ℝ)).add measurable_snd
  let ℱ := selectedObservationExhaustion F hF v D hD
  have hsup : (⨆ n, ℱ n) = selectedObservationField F v :=
    selectedObservationExhaustion_iSup F hF v D hD hex
  have hb (n : ℕ) : ∀ᵐ p ∂ρ,
      Real.tanh (PlantedSymmetry.observation t p r - (d : ℝ) * β) ≤
        (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ∧
      (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ≤
        Real.tanh (PlantedSymmetry.observation t p r + (d : ℝ) * β) := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hβ t
      (fun i : D n => v i.1) r (hr n)] with p hp
    exact tanh_bounds_of_interior_field_bound hp.1 hp.2
  have hae := tendsto_posterior_fields_ae ρ ℱ
    (fun q => spinSign (q.1 r)) (fun p => PlantedSymmetry.observation t p r)
    ((d : ℝ) * β) hb
  have hL2 := tendsto_integral_sq_sub_posterior_fields ρ ℱ
    (fun q => spinSign (q.1 r)) (fun p => PlantedSymmetry.observation t p r) hb
  rw [hsup] at hae hL2
  exact ⟨hae.mono (fun p hp => hp.2.2), hL2⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ComponentGibbsLimit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

theorem rootComponentIndices_monotone {d : ℕ} (c : Fin d) :
    Monotone (fun D : Finset (TreeVertex d) => rootComponentIndices D c) := by
  intro D E hDE u hu
  exact mem_rootComponentIndices.mpr (hDE (mem_rootComponentIndices.mp hu))

theorem selectedObservationField_rootComponentIndices {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (D : Finset (TreeVertex d)) (c : Fin d) :
    selectedObservationField F (fun u : rootComponentIndices D c => componentIndexVertex u.1) =
      selectedObservationField F (fun v : rootComponentFinset D c => v.1) := by
  apply selectedObservationField_eq_of_range_eq
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨⟨componentIndexVertex u.1, mem_rootComponentFinset.mpr
      ⟨mem_rootComponentIndices.mp u.2, ?_⟩⟩, rfl⟩
    apply (singleton_prefix_iff_cons c _).mpr
    exact ⟨u.1.2.1, rfl⟩
  · rintro ⟨v, rfl⟩
    have hv := mem_rootComponentFinset.mp v.2
    obtain ⟨u, hu⟩ := mem_range_componentIndexVertex.mpr
      ((singleton_prefix_iff_cons c v.1).mp hv.2)
    refine ⟨⟨u, mem_rootComponentIndices.mpr ?_⟩, hu⟩
    exact hu.symm ▸ hv.1

theorem HasFreeIsingLaw.rootComponent_gibbsMean_eq_selectedPosterior
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (hroot : ConnectedHull.root d ∈ D) (c : Fin d)
    (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D) (t : ℝ≥0) :
    (fun p => FiniteIsingSplit.mean β (rootComponentFinset D c)
      ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
      (PlantedSymmetry.observation t p)) =ᵐ[μ.prod
        (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)]
    selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
      (fun s z => (t : ℝ) * spinSign s + z)
      (fun u : rootComponentIndices D c => componentIndexVertex u.1)
      ⟨[c], List.IsChain.singleton c⟩ := by
  let E := rootComponentFinset D c
  let r : E := ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
  have hce := hμ.finiteObservation_condExp E
    (rootComponentFinset_connected hD hroot c hc) t (fun eta => spinSign (eta r))
  simp only [selectedPosterior, selectedObservationField_rootComponentIndices]
  have hsigma : selectedObservationField (fun s z => (t : ℝ) * spinSign s + z)
      (fun v : E => v.1) = MeasurableSpace.comap (finiteObservation E t) inferInstance := rfl
  rw [hsigma]
  simp only [FiniteIsingSplit.mean_eq_fieldMean]
  convert hce.symm using 1 <;> rfl

theorem HasFreeIsingLaw.rootComponent_gibbsField_limit
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (t : ℝ≥0) (c : Fin d)
    (D : ℕ → Finset (TreeVertex d)) (hmono : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ v, ∃ n, v ∈ D n)
    (hroot : ∀ n, ConnectedHull.root d ∈ D n)
    (hc : ∀ n, (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D n) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let H : ℕ → ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
      fun n p => Real.artanh (FiniteIsingSplit.mean β (rootComponentFinset (D n) c)
        ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c (hc n)⟩
        (PlantedSymmetry.observation t p))
    let Z := fun p => Real.artanh (selectedPosterior ρ
      (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
        ⟨[c], List.IsChain.singleton c⟩ p)
    (∀ᵐ p ∂ρ, Tendsto (fun n => H n p) atTop (𝓝 (Z p))) ∧
      Tendsto (fun n => ∫ p, (H n p - Z p) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let r : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  let I := fun n => rootComponentIndices (D n) c
  have hI : Monotone I := fun _ _ hnm => rootComponentIndices_monotone c (hmono hnm)
  have hexI : ∀ u : ComponentIndex c, ∃ n, u ∈ I n := by
    intro u
    obtain ⟨n, hn⟩ := hex (componentIndexVertex u)
    exact ⟨n, mem_rootComponentIndices.mpr hn⟩
  have hrI : ∀ n, r ∈ Set.range (fun u : I n => componentIndexVertex u.1) := by
    intro n
    let u : ComponentIndex c := ⟨0, ⟨[], rfl, List.IsChain.singleton c⟩⟩
    exact ⟨⟨u, mem_rootComponentIndices.mpr (hc n)⟩, rfl⟩
  have hlim := hμ.selected_gaussian_posterior_field_limit hβ t
    (componentIndexVertex (c := c)) r I hI hexI hrI
  have hce (n : ℕ) := hμ.rootComponent_gibbsMean_eq_selectedPosterior
    (D n) (hconn n) (hroot n) c (hc n) t
  constructor
  · filter_upwards [hlim.1, ae_all_iff.mpr hce] with p hp hce
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact congrArg Real.artanh (hce n)
  · convert hlim.2 using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    apply integral_congr_ae
    filter_upwards [hce n] with p hp
    rw [hp]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LogInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Real

namespace Problem367

theorem min_linear_exp_le_log_interpolation {A B c J K u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hJ : 0 < J)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K) :
    min (A * u) (B * Real.exp (-c * J)) ≤
      (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
  let I : ℝ := 1 + Real.log (K / u)
  let q : ℝ := c * J / 2
  have hq : 0 < q := by dsimp [q] <;> positivity
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hI : 1 ≤ I := by
    have hratio : 1 ≤ K / u := (one_le_div hu).2 huK
    have := Real.log_nonneg hratio
    dsimp [I]
    linarith
  change min (A * u) (B * Real.exp (-c * J)) ≤
    (2 * (A + B) / c) * u * I / J
  by_cases hsmall : u ≤ Real.exp (-q)
  · have hlogu : Real.log u ≤ -q := (Real.log_le_iff_le_exp hu).2 hsmall
    have hqI : q ≤ I := by
      dsimp [I]
      rw [Real.log_div (ne_of_gt hKpos) (ne_of_gt hu)]
      have := Real.log_nonneg hK
      linarith
    calc
      min (A * u) (B * Real.exp (-c * J)) ≤ A * u := min_le_left _ _
      _ ≤ (A + B) * u := by gcongr; linarith
      _ = (2 * (A + B) / c) * u * q / J := by
        dsimp [q]
        field_simp
      _ ≤ (2 * (A + B) / c) * u * I / J := by gcongr
  · have hlarge : Real.exp (-q) ≤ u := le_of_not_ge hsmall
    have hqexp : q ≤ Real.exp q := by
      have := Real.add_one_le_exp q
      linarith
    have hexp : Real.exp (-q) ≤ 1 / q := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hq hqexp
    have hexps : Real.exp (-c * J) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [q]
      ring
    calc
      min (A * u) (B * Real.exp (-c * J)) ≤ B * Real.exp (-c * J) := min_le_right _ _
      _ = B * Real.exp (-q) * Real.exp (-q) := by rw [hexps]; ring
      _ ≤ B * u * Real.exp (-q) := by gcongr
      _ ≤ (A + B) * u * (1 / q) := by gcongr; linarith
      _ ≤ ((A + B) * u * (1 / q)) * I := by
        have hnonneg : 0 ≤ (A + B) * u * (1 / q) := by positivity
        simpa using mul_le_mul_of_nonneg_left hI hnonneg
      _ = (2 * (A + B) / c) * u * I / J := by
        dsimp [q]
        field_simp

theorem small_log_loss_of_minimum {S A B c J K u R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hJ : 0 < J)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K) (hR : 0 ≤ R)
    (hS : S ≤ A * R * u + min (A * u) (B * Real.exp (-c * J))) :
    S ≤ (A + 2 * (A + B) / c) * u *
      (R + (1 + Real.log (K / u)) / J) := by
  have hI : 0 ≤ 1 + Real.log (K / u) := by
    have := Real.log_nonneg ((one_le_div hu).2 huK)
    linarith
  have hC : 0 ≤ 2 * (A + B) / c := by positivity
  calc
    S ≤ A * R * u + (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J :=
      hS.trans (add_le_add le_rfl (min_linear_exp_le_log_interpolation hA hB hc hJ hK hu huK))
    _ ≤ (A + 2 * (A + B) / c) * R * u +
        (2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
      gcongr
      linarith
    _ ≤ (A + 2 * (A + B) / c) * R * u +
        (A + 2 * (A + B) / c) * u * (1 + Real.log (K / u)) / J := by
      gcongr
      linarith
    _ = (A + 2 * (A + B) / c) * u *
        (R + (1 + Real.log (K / u)) / J) := by ring

theorem small_time_log_loss_of_minimum {S A B c K u t : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (hK : 1 ≤ K) (hu : 0 < u) (huK : u ≤ K)
    (ht : 0 < t) (ht1 : t < 1)
    (hS : S ≤ A * t ^ ((1 : ℝ) / 4) * u +
      min (A * u) (B * Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    S ≤ (A + 2 * (A + B) / c) * u *
      (t ^ ((1 : ℝ) / 4) + (1 + Real.log (K / u)) / (Real.log (1 / t)) ^ 2) := by
  have hlog : 0 < Real.log (1 / t) := Real.log_pos ((one_lt_div ht).2 ht1)
  exact small_log_loss_of_minimum hA hB hc (sq_pos_of_pos hlog) hK hu huK
    (Real.rpow_nonneg ht.le _) hS

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_CoupledSmallLogLoss
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem cavityLogVarianceCoefficient_nonneg (theta : ℝ) :
    0 ≤ cavityLogVarianceCoefficient theta := by
  unfold cavityLogVarianceCoefficient
  positivity

theorem cavityLogTailCoefficient_nonneg (theta M : ℝ) :
    0 ≤ cavityLogTailCoefficient theta M := by
  unfold cavityLogTailCoefficient
  positivity

section Coupling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {theta : ℝ} {X Y X' Y' H K H' K' : Ω → ℝ}

theorem integral_cavity_log_discrepancy_sq_le_of_marginal_tails
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V M R B₁ B₂ : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ ω ∂μ, |H ω - H' ω| ≤ M ∧ |K ω - K' ω| ≤ M)
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {ω | R < |X ω|} ≤ B₁)
    (hTail' : μ.real {ω | R < |X' ω|} ≤ B₂) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * R ^ 2 * V +
        min (cavityLogVarianceCoefficient theta * V)
          (4 * (M / (1 - theta)) ^ 2 * (B₁ + B₂)) := by
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have hInt := integrable_cavity_pair_sub_sq hθ0 hθ1 hX hX' hH hK heq
  have hVar := integral_cavity_pair_sub_sq_le hθ0 hθ1 hX hX' hH hK heq hHV hKV
  have hBound : ∀ᵐ ω ∂μ, |X ω - X' ω| ≤ M / (1 - theta) := by
    filter_upwards [heq, hbound] with ω he hb
    exact cavity_pair_sub_abs_le hθ0 hθ1 he.1 he.2.1 he.2.2.1 he.2.2.2 hb.1 hb.2
  have h := integral_log_responseAttenuation_sub_sq_le_of_marginal_tails
    hθsq hX hX' hInt (div_nonneg hM (by linarith)) hBound hVar hTail hTail'
  have hfirst : 4 * R ^ 2 * (V / (1 - theta) ^ 2) =
      cavityLogVarianceCoefficient theta * R ^ 2 * V := by
    unfold cavityLogVarianceCoefficient
    ring
  have hsecond : 4 * (V / (1 - theta) ^ 2) =
      cavityLogVarianceCoefficient theta * V := by
    unfold cavityLogVarianceCoefficient
    ring
  simpa only [hfirst, hsecond] using h

theorem integral_cavity_log_discrepancy_small_time
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V M t c : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (hbound : ∀ᵐ ω ∂μ, |H ω - H' ω| ≤ M ∧ |K ω - K' ω| ≤ M)
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V)
    (hTail : μ.real {ω | t ^ (1 / 8 : ℝ) < |X ω|} ≤
      Real.exp (-c * (Real.log (1 / t)) ^ 2))
    (hTail' : μ.real {ω | t ^ (1 / 8 : ℝ) < |X' ω|} ≤
      Real.exp (-c * (Real.log (1 / t)) ^ 2)) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * t ^ (1 / 4 : ℝ) * V +
        min (cavityLogVarianceCoefficient theta * V)
          (cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2)) := by
  have h := integral_cavity_log_discrepancy_sq_le_of_marginal_tails
    hθ0 hθ1 hX hX' hH hK heq hM hbound hHV hKV hTail hTail'
  have hr : (t ^ (1 / 8 : ℝ)) ^ 2 = t ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have htail : 4 * (M / (1 - theta)) ^ 2 *
      (Real.exp (-c * (Real.log (1 / t)) ^ 2) + Real.exp (-c * (Real.log (1 / t)) ^ 2)) =
      cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2) := by
    unfold cavityLogTailCoefficient
    ring
  simpa only [hr, htail] using h

theorem integral_cavity_log_discrepancy_small_time_of_common_law
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} {Z : Ξ → ℝ}
    (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    (hX : Measurable X) (hX' : Measurable X')
    (hH : Integrable (fun ω => (H ω - H' ω) ^ 2) μ)
    (hK : Integrable (fun ω => (K ω - K' ω) ^ 2) μ)
    (heq : ∀ᵐ ω ∂μ,
      X ω + cavityMessage theta (Y ω) = H ω ∧
      Y ω + cavityMessage theta (X ω) = K ω ∧
      X' ω + cavityMessage theta (Y' ω) = H' ω ∧
      Y' ω + cavityMessage theta (X' ω) = K' ω)
    {V M t c : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    (hbound : ∀ᵐ ω ∂μ, |H ω - H' ω| ≤ M ∧ |K ω - K' ω| ≤ M)
    (hHV : (∫ ω, (H ω - H' ω) ^ 2 ∂μ) ≤ V)
    (hKV : (∫ ω, (K ω - K' ω) ^ 2 ∂μ) ≤ V)
    (hLaw : IdentDistrib X Z μ ν) (hLaw' : IdentDistrib X' Z μ ν)
    (hTail : ν {z | t ^ (1 / 8 : ℝ) < |Z z|} ≤
      ENNReal.ofReal (Real.exp (-c * (Real.log (1 / t)) ^ 2))) :
    (∫ ω, (Real.log (responseAttenuation theta (X ω)) -
        Real.log (responseAttenuation theta (X' ω))) ^ 2 ∂μ) ≤
      cavityLogVarianceCoefficient theta * t ^ (1 / 4 : ℝ) * V +
        min (cavityLogVarianceCoefficient theta * V)
          (cavityLogTailCoefficient theta M * Real.exp (-c * (Real.log (1 / t)) ^ 2)) := by
  have transfer {W : Ω → ℝ} (hW : IdentDistrib W Z μ ν) :
      μ.real {ω | t ^ (1 / 8 : ℝ) < |W ω|} ≤
        Real.exp (-c * (Real.log (1 / t)) ^ 2) := by
    apply ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
    have hm := (hW.comp measurable_abs).measure_mem_eq
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (t ^ (1 / 8 : ℝ))))
    change μ {ω | t ^ (1 / 8 : ℝ) < |W ω|} =
      ν {z | t ^ (1 / 8 : ℝ) < |Z z|} at hm
    rw [hm]
    exact hTail
  exact integral_cavity_log_discrepancy_small_time hθ0 hθ1 hX hX' hH hK heq
    hM ht hbound hHV hKV (transfer hLaw) (transfer hLaw')

end Coupling

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteComponentFields
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.FiniteIsingSplit

variable {d : ℕ}

lemma field_congr_domain (beta : ℝ) {D E : Finset (TreeVertex d)}
    (h : D = E) (v : D) (w : E) (hv : v.1 = w.1)
    (y : TreeVertex d → ℝ) : field beta D v y = field beta E w y := by
  subst E
  have hw : v = w := Subtype.ext hv
  subst w
  rfl

theorem cavityFromSites_root_component {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (field beta D ⟨ConnectedHull.root d, hroot⟩ y,
        field beta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ y) =
      (field beta (rootComplementFinset D c)
          ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩ y,
        field beta (rootComponentFinset D c)
          ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩ y) := by
  classical
  let A := rootComplementFinset D c
  let B := rootComponentFinset D c
  let u : A := ⟨ConnectedHull.root d, rootComplementFinset_root_mem c hroot⟩
  let v : B := ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩
  have hAB : Disjoint A B := (rootComponentFinset_disjoint_complement D c).symm
  have hUnion : A ∪ B = D := by
    rw [Finset.union_comm]
    exact rootComponentFinset_union_complement D c
  have hEdges : inducedEdges (A ∪ B) =
      insert (u.1, v.1) (inducedEdges A ∪ inducedEdges B) := by
    rw [hUnion, inducedEdges_rootComponent_split hroot c hc]
    congr 1
    exact Finset.union_comm _ _
  have h := cavityFromSites_eq_component_fields hbeta A B hAB u v hEdges y
  have hu := field_congr_domain beta hUnion
    (⟨u, Finset.mem_union_left B u.property⟩ : ↥(A ∪ B))
    ⟨ConnectedHull.root d, hroot⟩ rfl y
  have hv := field_congr_domain beta hUnion
    (⟨v, Finset.mem_union_right A v.property⟩ : ↥(A ∪ B))
    ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ rfl y
  rw [hu, hv] at h
  exact h

end Problem367.FiniteIsingSplit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteCavityComponents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.CavityFieldLimit

variable {d : ℕ}

lemma finiteSiteField_eq_component_field (beta : ℝ) (D : Finset (TreeVertex d))
    (v : D) (y : TreeVertex d → ℝ) :
    finiteSiteField beta D v y = FiniteIsingSplit.field beta D v y := by
  simp only [finiteSiteField, FiniteIsingSplit.field, FiniteIsingSplit.mean_eq_fieldMean]

theorem finiteCavityField_child_eq_component {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hroot : ConnectedHull.root d ∈ D)
    (c : Fin d) (hc : (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D)
    (y : TreeVertex d → ℝ) :
    finiteCavityField hbeta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩
      ⟨ConnectedHull.root d, hroot⟩ y =
    finiteSiteField beta (rootComponentFinset D c)
      ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c hc⟩ y := by
  simp only [finiteCavityField, finiteSiteField_eq_component_field]
  have hswap := cavityFromSites_swap (tanh_nonneg_of_beta_nonneg hbeta)
    (Real.tanh_lt_one beta)
    (FiniteIsingSplit.field beta D ⟨ConnectedHull.root d, hroot⟩ y,
      FiniteIsingSplit.field beta D ⟨⟨[c], List.IsChain.singleton c⟩, hc⟩ y)
  rw [FiniteIsingSplit.cavityFromSites_root_component hbeta D hroot c hc y] at hswap
  exact congrArg Prod.fst hswap

end Problem367.CavityFieldLimit

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfiniteComponentCavity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open CavityFieldLimit PlantedSymmetry

theorem HasFreeIsingLaw.infiniteCavityField_eq_component_of_exhaustion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ v, ∃ n, v ∈ D n)
    (hroot : ∀ n, ConnectedHull.root d ∈ D n)
    (hc : ∀ n, (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) ∈ D n) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
        (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p) := by
  have hfull := hμ.exhaustionCavityField_tendsto_ae hbeta D hD hconn hex
    ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d) hc hroot t
  have hpart := (hμ.rootComponent_gibbsField_limit hbeta t c D hD hconn hex hroot hc).1
  filter_upwards [hfull, hpart] with p hp hpart
  have hseq (n : ℕ) :
      finiteCavityField hbeta (D n) ⟨⟨[c], List.IsChain.singleton c⟩, hc n⟩
        ⟨ConnectedHull.root d, hroot n⟩ (observation t p) =
      Real.artanh (FiniteIsingSplit.mean beta (rootComponentFinset (D n) c)
        ⟨⟨[c], List.IsChain.singleton c⟩, rootComponentFinset_root_mem c (hc n)⟩
        (observation t p)) := by
    rw [finiteCavityField_child_eq_component hbeta (D n) (hroot n) c (hc n)]
    exact finiteSiteField_eq_component_field _ _ _ _
  exact tendsto_nhds_unique ((tendsto_congr hseq).mp hp) hpart

theorem HasFreeIsingLaw.infiniteCavityField_eq_component
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
        (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p) := by
  let r : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  apply hμ.infiniteCavityField_eq_component_of_exhaustion hbeta t c
    (connectedExhaustion r) (connectedExhaustion_monotone r)
    (connectedExhaustion_connected r)
    (fun v => (eventually_mem_connectedExhaustion r v).exists)
    _ (mem_connectedExhaustion r)
  intro n
  classical
  simp [connectedExhaustion, ConnectedHull.hull]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_SharedInnovationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter

namespace Problem367

theorem discrepancy_secondMoment_bounds
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h h' : Ω → ℝ} {H : ℝ}
    (hmeas : AEStronglyMeasurable (fun ω => h ω - h' ω) μ)
    (hbound : ∀ᵐ ω ∂μ, |h ω - h' ω| ≤ H) :
    MemLp (fun ω => h ω - h' ω) 2 μ ∧
      0 ≤ (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ∧
      (∫ ω, (h ω - h' ω) ^ 2 ∂μ) ≤ H ^ 2 := by
  have hLp : MemLp (fun ω => h ω - h' ω) 2 μ :=
    MemLp.of_bound hmeas H (by simpa only [Real.norm_eq_abs] using hbound)
  exact ⟨hLp, integral_nonneg (fun _ => sq_nonneg _),
    DiscrepancyEnergy.secondMoment_le_of_ae_abs_le
      (X := fun _ ω => h ω - h' ω) (t := 0) hLp.integrable_sq hbound⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_CopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem ae_observation_sub_bound_of_shared_progressive_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {m m' : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive G m')
    (hb : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ 1)
    (hb' : ∀ t, ∀ᵐ ω ∂P, |m' t ω| ≤ 1)
    {x x' w : Ω → ℝ} (t : ℝ≥0)
    (hx : ∀ᵐ ω ∂P, x ω = w ω + nnrealTimePrimitive m t ω)
    (hx' : ∀ᵐ ω ∂P, x' ω = w ω + nnrealTimePrimitive m' t ω) :
    ∀ᵐ ω ∂P, |x ω - x' ω| ≤ 2 * (t : ℝ) := by
  have hL := ae_lipschitzWith_nnrealTimePrimitive hm (C := 1) hb
  have hL' := ae_lipschitzWith_nnrealTimePrimitive hm' (C := 1) hb'
  filter_upwards [hL, hL', hx, hx'] with ω hω hω' hxω hxω'
  have h1 : |nnrealTimePrimitive m t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω.dist_le_mul t 0
  have h2 : |nnrealTimePrimitive m' t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω'.dist_le_mul t 0
  rw [hxω, hxω']
  have heq : (w ω + nnrealTimePrimitive m t ω) -
      (w ω + nnrealTimePrimitive m' t ω) =
      nnrealTimePrimitive m t ω - nnrealTimePrimitive m' t ω := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

theorem HasFreeIsingLaw.gibbsField_bound_of_observation_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {X : Ω → TreeVertex d → ℝ}
    (hX : IdentDistrib X (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))) :
    ∀ᵐ ω ∂P, |Real.artanh (infiniteGibbsSpinMean beta v (X ω)) - X ω v| ≤
      (d : ℝ) * beta := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hmeas := (ha.comp (measurable_infiniteGibbsSpinMean beta v)).sub
    (measurable_pi_apply v)
  apply hX.symm.ae_snd (measurableSet_le hmeas.abs measurable_const)
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.gaussian_posterior_field_bound hbeta t v] with p heq hp
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [heq]
  exact hp.2

theorem HasFreeIsingLaw.gibbsField_copy_bound_of_shared_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    ∀ᵐ ω ∂P,
      |Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))| ≤
          2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hobs := ae_observation_sub_bound_of_shared_progressive_innovation hm hm'
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _))
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _)) t hx hx'
  have hl := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw
  have hr := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw'
  filter_upwards [hobs, hl, hr] with ω hobsω hlω hrω
  have htriangle := abs_sub_le
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)))
    (X v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  have htriangle' := abs_sub_le (X v t ω) (X' v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  rw [abs_sub_comm (X' v t ω)] at htriangle'
  linarith

theorem HasFreeIsingLaw.gibbsField_copy_secondMoment_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    let U := fun ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))
    MemLp U 2 P ∧ 0 ≤ (∫ ω, (U ω) ^ 2 ∂P) ∧
      (∫ ω, (U ω) ^ 2 ∂P) ≤ (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  dsimp only
  have hb := hμ.gibbsField_copy_bound_of_shared_innovation hbeta hX hX'
    t v hlaw hlaw' hx hx'
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hmeas := (ha.comp (((hm.stronglyAdapted t).mono (F.le t)).measurable)).sub
    (ha.comp (((hm'.stronglyAdapted t).mono (G.le t)).measurable))
  exact discrepancy_secondMoment_bounds hmeas.aestronglyMeasurable hb

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ConditionalCopyBounds
attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingConditionalCopyBounds

open PlantedSymmetry IsingObservationInnovation WienerSampler

theorem progressive_leftObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.1 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.1 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_fst.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.1 v).continuous)

theorem progressive_rightObservation {d : ℕ} (v : TreeVertex d) :
    IsStronglyProgressive ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
  have had : StronglyAdapted ContinuousCopyBrownian.joinedFiltration
      (fun t (q : CopySpace d) => q.2.2 v t) := by
    intro t
    change StronglyMeasurable[ContinuousCopyBrownian.pastSpace t]
      (fun q : CopySpace d => q.2.2 v t)
    have hh : Measurable[ContinuousCopyBrownian.pastSpace t]
        (ContinuousCopyBrownian.history (ι := TreeVertex d) t) := comap_measurable _
    have hm := (continuous_eval_const t).measurable.comp
      ((measurable_pi_apply v).comp
        ((measurable_snd.comp measurable_snd).comp hh))
    simpa only [Function.comp_def, ContinuousCopyBrownian.history,
      ContinuousObservationHistory.stoppedArray,
      ContinuousObservationHistory.stoppedPath_apply, min_self] using hm.stronglyMeasurable
  exact had.isStronglyProgressive_of_continuous (fun q => (q.2.2 v).continuous)

section Copies

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable {rho : Measure (Paths d)} [IsProbabilityMeasure rho]
variable {eta : Kernel (Paths d) (Paths d)} [IsMarkovKernel eta]

theorem ae_innovationMap_copies (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta),
      innovationMap beta q.2.1 = q.1 ∧ innovationMap beta q.2.2 = q.1 := by
  have hgraph : ∀ᵐ q : Paths d × Paths d ∂rho ⊗ₘ eta,
      innovationMap beta q.2 = q.1 := by
    rw [hjoint, graphLaw]
    apply (ae_map_iff
      ((measurable_innovationMap beta).prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun
        ((measurable_innovationMap beta).comp measurable_snd) measurable_fst)).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  have hleft := (measurePreserving_conditionalCopy_fst rho eta).quasiMeasurePreserving.ae hgraph
  have hright := (measurePreserving_conditionalCopy_snd rho eta).quasiMeasurePreserving.ae hgraph
  filter_upwards [hleft, hright] with q hl hr
  exact ⟨hl, hr⟩

theorem identDistrib_observation_copies
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) :
    IdentDistrib (fun q : CopySpace d => fun i => q.2.1 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    IdentDistrib (fun q : CopySpace d => fun i => q.2.2 i t) (observation t)
      (rho ⊗ₘ (eta ×ₖ eta)) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  obtain ⟨hl, hr⟩ := measurePreserving_observation_copies hjoint
  have heval := hasLaw_observationLaw_eval μ t
  have hobs : HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  exact ⟨(heval.comp hl.hasLaw).identDistrib hobs,
    (heval.comp hr.hasLaw).identDistrib hobs⟩

theorem ae_all_innovation_identities (hjoint : rho ⊗ₘ eta = graphLaw beta μ) :
    ∀ᵐ q : CopySpace d ∂rho ⊗ₘ (eta ×ₖ eta), ∀ v t,
      q.2.1 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q ∧
      q.2.2 v t = q.1 v t + nnrealTimePrimitive
        (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q := by
  filter_upwards [ae_innovationMap_copies hjoint] with q hq
  intro v t
  have hl := congrArg (fun x : Paths d => x v t) hq.1
  have hr := congrArg (fun x : Paths d => x v t) hq.2
  change q.2.1 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.1) t q = q.1 v t at hl
  change q.2.2 v t - nnrealTimePrimitive
    (fun s (p : CopySpace d) => posterior beta v s p.2.2) t q = q.1 v t at hr
  constructor <;> linarith

theorem ae_fieldDifference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    ∀ᵐ q ∂rho ⊗ₘ (eta ×ₖ eta),
      |fieldDifference beta v t q| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  simpa only [fieldDifference, IsingObservationInnovation.posterior] using
    hμ.gibbsField_copy_bound_of_shared_innovation hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

theorem fieldDifference_secondMoment_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hjoint : rho ⊗ₘ eta = graphLaw beta μ) (t : ℝ≥0) (v : TreeVertex d) :
    MemLp (fieldDifference beta v t) 2 (rho ⊗ₘ (eta ×ₖ eta)) ∧
      0 ≤ (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ∧
      (∫ q, (fieldDifference beta v t q) ^ 2 ∂rho ⊗ₘ (eta ×ₖ eta)) ≤
        (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  obtain ⟨hl, hr⟩ := identDistrib_observation_copies hμ hjoint t
  have hx := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).1)
  have hx' := (ae_all_innovation_identities hjoint).mono (fun q hq => (hq v t).2)
  exact hμ.gibbsField_copy_secondMoment_bounds hbeta
      progressive_leftObservation progressive_rightObservation t v hl hr hx hx'

end Copies

end Problem367.IsingConditionalCopyBounds

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyStationarity
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyStationarity

open IsingObservationInnovation IsingObservationFactor

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem posterior_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun x => posterior beta v t (relabel g x)) =ᵐ[observationLaw μ]
      posterior beta (g.toEquiv.symm v) t := by
  have hm (w : TreeVertex d) : Measurable (posterior beta w t) :=
    (measurable_infiniteGibbsSpinMean beta w).comp
      (Measurable.of_eval (fun i => measurable_evaluation i t))
  apply (ae_map_iff measurable_uniformObservation.aemeasurable
    (measurableSet_eq_fun ((hm v).comp (measurable_relabel g))
      (hm (g.toEquiv.symm v)))).mpr
  have hmB (s : ℝ≥0) : Measurable (fun u => WienerSampler.sample u s) :=
    WienerSampler.measurable_sample_eval.comp (measurable_const.prodMk measurable_id)
  have h := ArrayPosteriorStationarity.posterior_version_relabel_ae hμ uniform01
    (fun s u => WienerSampler.sample u s) hmB
    (fun s w => IsingInnovation.posterior_eq_condExp hμ uniform01
      WienerSampler.sample_isBrownianReal.toIsPreBrownianReal hmB s w) g t v
  exact h

omit [IsProbabilityMeasure μ] in
theorem field_array_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (g : TreeAut d) (t : ℝ≥0) :
    (fun x v => field beta v t (relabel g x)) =ᵐ[observationLaw μ]
      (fun x => relabel g (fun v => field beta v t x)) := by
  filter_upwards [ae_all_iff.mpr (fun v => posterior_relabel_ae hμ g t v)] with x hx
  funext v
  exact congrArg Real.artanh (hx v)

theorem measurable_sitePair (beta : ℝ) (t : ℝ≥0) :
    Measurable (sitePair (d := d) beta t) := by
  have hm (v : TreeVertex d) : Measurable (field beta v t) := by
    have hp : Measurable (posterior beta v t) :=
      (measurable_infiniteGibbsSpinMean beta v).comp
        (Measurable.of_eval (fun i => measurable_evaluation i t))
    unfold field Real.artanh
    exact ((measurable_const.add hp).div (measurable_const.sub hp)).sqrt.log
  exact (Measurable.of_eval (fun v => (hm v).comp (measurable_fst.comp measurable_snd))).prodMk
    (Measurable.of_eval (fun v => (hm v).comp (measurable_snd.comp measurable_snd)))

theorem measurePreserving_sitePair_relabel
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (g : TreeAut d) :
    MeasurePreserving (CavityArray.pairRelabel g)
      ((copies beta μ).map (sitePair beta t))
      ((copies beta μ).map (sitePair beta t)) := by
  refine ⟨CavityArray.measurable_pairRelabel g, ?_⟩
  apply FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_copies_relabel hμ g) (CavityArray.measurable_pairRelabel g)
    (measurable_sitePair beta t)
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  filter_upwards [hl.quasiMeasurePreserving.ae (field_array_relabel_ae hμ g t),
    hr.quasiMeasurePreserving.ae (field_array_relabel_ae hμ g t)] with q hq hq'
  exact Prod.ext hq hq'

theorem fieldDifference_identDistrib
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (u v : TreeVertex d) :
    IdentDistrib (IsingConditionalCopyBounds.fieldDifference beta u t)
      (IsingConditionalCopyBounds.fieldDifference beta v t) (copies beta μ) (copies beta μ) := by
  have hm (w : TreeVertex d) : Measurable (fun p : CavityArray.SitePair d => p.1 w - p.2 w) :=
    ((measurable_pi_apply w).comp measurable_fst).sub
      ((measurable_pi_apply w).comp measurable_snd)
  have h := CavityArray.site_sub_identDistrib
    (measurePreserving_sitePair_relabel hμ t) u v
  refine ⟨((hm u).comp (measurable_sitePair beta t)).aemeasurable,
    ((hm v).comp (measurable_sitePair beta t)).aemeasurable, ?_⟩
  change (copies beta μ).map ((fun p : CavityArray.SitePair d => p.1 u - p.2 u) ∘
    sitePair beta t) = (copies beta μ).map
      ((fun p : CavityArray.SitePair d => p.1 v - p.2 v) ∘ sitePair beta t)
  rw [← Measure.map_map (hm u) (measurable_sitePair beta t),
    ← Measure.map_map (hm v) (measurable_sitePair beta t)]
  exact h.map_eq

theorem integral_fieldDifference_sq_eq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (u v : TreeVertex d) :
    (∫ q, (IsingConditionalCopyBounds.fieldDifference beta u t q) ^ 2 ∂copies beta μ) =
      ∫ q, (IsingConditionalCopyBounds.fieldDifference beta v t q) ^ 2 ∂copies beta μ :=
  (fieldDifference_identDistrib hμ t u v).sq.integral_eq

end Problem367.IsingCopyStationarity

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyObservables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity PlantedSymmetry

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem cavityObservable_relabel_ae
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun x => cavityObservable hbeta t v w (relabel g x)) =ᵐ[observationLaw μ]
      cavityObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w) := by
  filter_upwards [field_array_relabel_ae hμ g t] with x hx
  unfold cavityObservable
  rw [hx]
  rfl

end Problem367.IsingCopySpectral

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_ObservationComparison
attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingObservationFactor

open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
variable [IsProbabilityMeasure μ]

theorem kernel_graphLaw :
    ((observationLaw μ).map (innovationMap beta)) ⊗ₘ kernel beta μ =
      IsingConditionalCopyBounds.graphLaw beta μ :=
  ObservableDisintegration.compProd_kernel (observationLaw μ)
    (measurable_innovationMap beta)

theorem integrable_field_difference_sq
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (v : TreeVertex d) (t : ℝ≥0) :
    Integrable (fun p => (field beta v t p.2.1 - field beta v t p.2.2) ^ 2)
      (copies beta μ) := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_innovationMap beta).aemeasurable).mpr inferInstance
  exact (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds
    hμ hbeta kernel_graphLaw t v).1.integrable_sq

end Problem367.IsingObservationFactor

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopySmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open IsingCopySpectral

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem observable_identDistrib_copies {f : Paths d → ℝ} (hf : Measurable f) :
    IdentDistrib (fun q : Paths d × (Paths d × Paths d) => f q.2.1) f
      (copies beta μ) (observationLaw μ) ∧
    IdentDistrib (fun q : Paths d × (Paths d × Paths d) => f q.2.2) f
      (copies beta μ) (observationLaw μ) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  constructor
  · refine ⟨(hf.comp hl.measurable).aemeasurable, hf.aemeasurable, ?_⟩
    change (copies beta μ).map (f ∘ (fun q => q.2.1)) = _
    rw [← Measure.map_map hf hl.measurable, hl.map_eq]
  · refine ⟨(hf.comp hr.measurable).aemeasurable, hf.aemeasurable, ?_⟩
    change (copies beta μ).map (f ∘ (fun q => q.2.2)) = _
    rw [← Measure.map_map hf hr.measurable, hr.map_eq]

theorem ae_site_difference_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (htT : t ≤ T) :
    ∀ᵐ q ∂copies beta μ, ∀ v : TreeVertex d,
      |field beta v t q.2.1 - field beta v t q.2.2| ≤
        2 * (T : ℝ) + 2 * (d : ℝ) * beta := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) :=
    (by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  apply ae_all_iff.mpr
  intro v
  filter_upwards [IsingConditionalCopyBounds.ae_fieldDifference_bound hμ hbeta
    (kernel_graphLaw (beta := beta) (μ := μ)) t v] with q hq
  exact hq.trans (by exact_mod_cast (show
    2 * (t : ℝ) + 2 * (d : ℝ) * beta ≤
      2 * (T : ℝ) + 2 * (d : ℝ) * beta from by
        have h : (t : ℝ) ≤ T := htT
        linarith))

theorem logVariance_small_time_of_tail
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o v w : TreeVertex d) {t T : ℝ≥0} (ht : 0 < (t : ℝ)) (htT : t ≤ T)
    {c : ℝ}
    (hTail : observationLaw μ {x | (t : ℝ) ^ (1 / 8 : ℝ) <
      |cavityObservable hbeta t v w x|} ≤
      ENNReal.ofReal (Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2))) :
    logVariance hbeta μ v w t ≤
      cavityLogVarianceCoefficient (Real.tanh beta) * (t : ℝ) ^ (1 / 4 : ℝ) *
        siteVariance beta μ o t +
      min (cavityLogVarianceCoefficient (Real.tanh beta) * siteVariance beta μ o t)
        (cavityLogTailCoefficient (Real.tanh beta)
          (2 * (T : ℝ) + 2 * (d : ℝ) * beta) *
            Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2)) := by
  obtain ⟨hl, hr⟩ := observable_identDistrib_copies (beta := beta) (μ := μ)
    (measurable_cavityObservable hbeta t v w)
  apply integral_cavity_log_discrepancy_small_time_of_common_law
    (μ := copies beta μ) (ν := observationLaw μ)
    (Z := cavityObservable hbeta t v w)
    (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
    ((measurable_cavityObservable hbeta t v w).comp
      (measurable_fst.comp measurable_snd))
    ((measurable_cavityObservable hbeta t v w).comp
      (measurable_snd.comp measurable_snd))
    (integrable_field_difference_sq hμ hbeta v t)
    (integrable_field_difference_sq hμ hbeta w t)
    (Y := fun q => cavityObservable hbeta t w v q.2.1)
    (Y' := fun q => cavityObservable hbeta t w v q.2.2)
  · exact Filter.Eventually.of_forall fun q =>
      ⟨CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.1) v w,
        CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.1) w v,
        CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.2) v w,
        CavityArray.field_spec (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
          (fun i => field beta i t q.2.2) w v⟩
  · positivity
  · exact ht
  · filter_upwards [ae_site_difference_bound hμ hbeta htT] with q hq
    exact ⟨hq v, hq w⟩
  · exact (integral_fieldDifference_sq_eq hμ t v o).le
  · exact (integral_fieldDifference_sq_eq hμ t w o).le
  · exact hl
  · exact hr
  · exact hTail

end Problem367.IsingCopySmallLogLoss

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CavityTailTransport
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCavityTailTransport

open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open IsingCopySpectral IsingCopySmallLogLoss PlantedSymmetry CavityFieldLimit

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem cavityObservable_identDistrib_relabel [_hprob : IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (g : TreeAut d) (t : ℝ≥0) (v w : TreeVertex d) :
    IdentDistrib (cavityObservable hbeta t v w)
      (cavityObservable hbeta t (g.toEquiv.symm v) (g.toEquiv.symm w))
      (observationLaw μ) (observationLaw μ) := by
  have hm := measurable_cavityObservable hbeta t v w
  have hg := measurePreserving_observationLaw_relabel hμ g
  have hmap : IdentDistrib (fun x => cavityObservable hbeta t v w (relabel g x))
      (cavityObservable hbeta t v w) (observationLaw μ) (observationLaw μ) := by
    refine ⟨(hm.comp hg.measurable).aemeasurable, hm.aemeasurable, ?_⟩
    change (observationLaw μ).map ((cavityObservable hbeta t v w) ∘ relabel g) = _
    rw [← Measure.map_map hm hg.measurable, hg.map_eq]
  exact hmap.symm.trans (IdentDistrib.of_ae_eq (hm.comp hg.measurable).aemeasurable
    (cavityObservable_relabel_ae hμ hbeta g t v w))

theorem cavityObservable_identDistrib_root_component
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    IdentDistrib
      (cavityObservable hbeta t ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d))
      (fun p => Real.artanh (selectedPosterior
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
        ⟨[c], List.IsChain.singleton c⟩ p))
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hobs := (IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).identDistrib
    (show HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) from
      ⟨(measurable_observation t).aemeasurable, rfl⟩)
  have hm := measurable_infiniteCavityField hbeta
    ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)
  have h := hobs.comp hm
  change IdentDistrib
    (cavityObservable hbeta t ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d))
    (fun p => infiniteCavityField hbeta ⟨[c], List.IsChain.singleton c⟩
      (ConnectedHull.root d) (observation t p))
    (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) at h
  exact h.trans (IdentDistrib.of_ae_eq ((hm.comp (measurable_observation t)).aemeasurable)
    (hμ.infiniteCavityField_eq_component hbeta t c))

theorem exists_cavityObservable_identDistrib_root_component
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {v w : TreeVertex d} (hvw : treeAdj v w) :
    ∃ c : Fin d, IdentDistrib (cavityObservable hbeta t v w)
      (fun p => Real.artanh (selectedPosterior
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
        ⟨[c], List.IsChain.singleton c⟩ p))
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root w
  have hgv : treeAdj (⟨[], List.IsChain.nil⟩ : TreeVertex d) (g.toEquiv v) := by
    rw [← hg]
    exact (g.map_adj w v).2 hvw.symm
  obtain ⟨c, hc⟩ : ∃ c : Fin d, (g.toEquiv v).1 = [c] := by
    rcases hgv with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by simpa using hc⟩
    · have hlen := congrArg List.length hc
      simp at hlen
  have hvc : g.toEquiv v = ⟨[c], List.IsChain.singleton c⟩ := Subtype.ext hc
  have h := cavityObservable_identDistrib_relabel hμ hbeta g.symm t v w
  change IdentDistrib (cavityObservable hbeta t v w)
    (cavityObservable hbeta t (g.toEquiv v) (g.toEquiv w))
    (observationLaw μ) (observationLaw μ) at h
  rw [hvc, hg] at h
  exact ⟨c, h.trans (cavityObservable_identDistrib_root_component hμ hbeta t c)⟩

theorem cavityObservable_tail_le_of_component_tails
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) {v w : TreeVertex d} (hvw : treeAdj v w) {a : ℝ} {B : ℝ≥0∞}
    (hTail : ∀ c : Fin d,
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) {p | a < |Real.artanh
        (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          (fun s z => (t : ℝ) * spinSign s + z) (componentIndexVertex (c := c))
          ⟨[c], List.IsChain.singleton c⟩ p)|} ≤ B) :
    observationLaw μ {x | a < |cavityObservable hbeta t v w x|} ≤ B := by
  obtain ⟨c, hc⟩ := exists_cavityObservable_identDistrib_root_component hμ hbeta t hvw
  have heq := (hc.comp measurable_abs).measure_mem_eq
    (measurableSet_Ioi : MeasurableSet (Set.Ioi a))
  exact heq.trans_le (hTail c)

end Problem367.IsingCavityTailTransport

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CriticalSmallLogLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.IsingCriticalSmallLogLoss

open IsingObservationInnovation IsingObservationFactor IsingCopySmallLogLoss
open IsingCavityTailTransport IsingCopySpectral

theorem one_le_varianceScale (d : ℕ) (beta : ℝ) (T : ℝ≥0) :
    1 ≤ varianceScale d beta T := by
  unfold varianceScale
  linarith [sq_nonneg (2 * (T : ℝ) + 2 * (d : ℝ) * beta)]

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem siteVariance_le_varianceScale
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (o : TreeVertex d) {t T : ℝ≥0} (htT : t ≤ T) :
    siteVariance beta μ o t ≤ varianceScale d beta T := by
  have : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := by first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply measurable_innovationMap <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have h := (IsingConditionalCopyBounds.fieldDifference_secondMoment_bounds
    hμ hbeta kernel_graphLaw t o).2.2
  have htime : (t : ℝ) ≤ T := htT
  have hb : 2 * (t : ℝ) + 2 * (d : ℝ) * beta ≤
      2 * (T : ℝ) + 2 * (d : ℝ) * beta := by linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta)
    (by positivity : 0 ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta)).2 hb
  exact h.trans (hsq.trans (by unfold varianceScale; linarith))

theorem exists_cavityObservable_critical_tail
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (ν : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure ν],
      HasFreeIsingLaw (Real.tanh beta) ν →
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → (t : ℝ) ≤ δ →
      ∀ (v w : TreeVertex d), treeAdj v w →
      observationLaw ν {x | (t : ℝ) ^ (1 / 8 : ℝ) <
        |cavityObservable hbeta t v w x|} ≤
        ENNReal.ofReal (Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2)) := by
  obtain ⟨K, hK, hMom⟩ := exists_gaussianComponentField_critical_moment_tail
    hd hbeta hcritical
  have hδ : Real.exp (-32 * K) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  refine ⟨1 / (512 * K), Real.exp (-32 * K), by positivity,
    Real.exp_pos _, hδ, ?_⟩
  intro ν _ hν t ht htδ v w hvw
  have ht1 : (t : ℝ) ≤ 1 := htδ.trans hδ.le
  have hlog : 32 * K ≤ Real.log (1 / (t : ℝ)) := by
    have h := (Real.log_le_iff_le_exp ht).2 htδ
    rw [one_div, Real.log_inv]
    linarith
  apply cavityObservable_tail_le_of_component_tails hν hbeta t hvw
  intro i
  have htail := (hMom ν hν t (show 0 < t from ht) ht1 i).2.2 hlog
  have he : -(1 / (512 * K)) * (Real.log (1 / (t : ℝ))) ^ 2 =
      -(Real.log (1 / (t : ℝ)) ^ 2) / (512 * K) := by ring
  simpa only [selectedGaussianField, RootedBroadcast.branchRoot, he] using htail

theorem exists_critical_small_log_bounds_oai
    (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (ν : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure ν],
      HasFreeIsingLaw (Real.tanh beta) ν →
      ∀ (T : ℝ≥0) (o v w : TreeVertex d), treeAdj v w →
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → t ≤ T → (t : ℝ) ≤ δ →
      (logVariance hbeta ν v w t ≤
        cavityLogVarianceCoefficient (Real.tanh beta) * (t : ℝ) ^ (1 / 4 : ℝ) *
          siteVariance beta ν o t +
        min (cavityLogVarianceCoefficient (Real.tanh beta) * siteVariance beta ν o t)
          (cavityLogTailCoefficient (Real.tanh beta)
            (2 * (T : ℝ) + 2 * (d : ℝ) * beta) *
              Real.exp (-c * (Real.log (1 / (t : ℝ))) ^ 2))) ∧
      (0 < siteVariance beta ν o t →
        logVariance hbeta ν v w t ≤
          (cavityLogVarianceCoefficient (Real.tanh beta) +
            2 * (cavityLogVarianceCoefficient (Real.tanh beta) +
              cavityLogTailCoefficient (Real.tanh beta)
                (2 * (T : ℝ) + 2 * (d : ℝ) * beta)) / c) *
            siteVariance beta ν o t *
            ((t : ℝ) ^ (1 / 4 : ℝ) +
              (1 + Real.log (varianceScale d beta T / siteVariance beta ν o t)) /
                (Real.log (1 / (t : ℝ))) ^ 2)) := by
  obtain ⟨c, δ, hc, hδ, hδ1, hTail⟩ :=
    exists_cavityObservable_critical_tail hd hbeta hcritical
  refine ⟨c, δ, hc, hδ, hδ1, ?_⟩
  intro ν _ hν T o v w hvw t ht htT htδ
  have hsmall := logVariance_small_time_of_tail hν hbeta o v w ht htT
    (hTail ν hν t ht htδ v w hvw)
  refine ⟨hsmall, fun hV => ?_⟩
  exact small_time_log_loss_of_minimum
    (cavityLogVarianceCoefficient_nonneg _) (cavityLogTailCoefficient_nonneg _ _)
    hc (one_le_varianceScale d beta T) hV
    (siteVariance_le_varianceScale hν hbeta o htT) ht (htδ.trans_lt hδ1) hsmall

end Problem367.IsingCriticalSmallLogLoss

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds_oai := @OAI.Problem367.IsingCriticalSmallLogLoss.exists_critical_small_log_bounds_oai

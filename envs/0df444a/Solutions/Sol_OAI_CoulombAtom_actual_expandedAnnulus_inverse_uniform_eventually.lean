-- Prove2me | solution 1 for OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:41:13.272468+00:00
-- url     : https://prove2.me/submissions/bde76783-e46b-4edf-8a39-20e8bc64ac65

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_TailTiltState_event_radial_comparison_of_cell

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialPatchCap
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchOscillationConstant_pos : 0 < tfPatchOscillationConstant :=
  (Classical.choose_spec (exists_weak_tf_oscillation_constant tfReactionCoefficient_pos)).1

lemma tfPatchOscillationConstant_bound {u : Space → ℝ} {R : ℝ} (hR : 0 < R)
    (hu : ContinuousOn u (closedBall 0 R))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R →
      (∫ x, u x*Δ g x) = ∫ x, tfReactionCoefficient*(max (u x) 0)^(3/2:ℝ)*g x)
    (x : Space) (hx : ‖x‖ ≤ R/12) :
    |u x-u 0| ≤ tfPatchOscillationConstant/R*‖x‖*(R⁻¹^4+max (-u 0) 0) :=
  (Classical.choose_spec (exists_weak_tf_oscillation_constant tfReactionCoefficient_pos)).2 u R hR hu hw x hx

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_nonradial_oscillation {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) (x : Space) (hx : ‖x‖ ≤ R/12) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
    |W x-W 0| ≤ tfPatchOscillationConstant/R*‖x‖*(R⁻¹^4+max (-W 0) 0) := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  apply tfPatchOscillationConstant_bound hR
    (actualPatchField_continuousOn hu A hcore y R hd hr hnuc hsep Z lam f) _ x hx
  intro g hg hcg hs
  apply tf_weak_pde_volume _ hg hcg hs
  intro g hg hcg hs
  exact conditionalPatchMinimizer_weak_pde ψ t u hu A hcore y R hd hr hnuc hsep Z lam hg hcg hs

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_NegativePatchControl
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma negative_part_le_of_oscillation {v w δ B : ℝ}
    (hδ : δ ≤ 1/2) (ho : |w-v| ≤ δ*(B+max (-v) 0)) :
    max (-v) 0 ≤ 2*max (-w) 0+2*δ*B := by
  have hn : 0 ≤ max (-v) 0 := le_max_right _ _
  have hdist : max (-v) 0 ≤ max (-w) 0+|w-v| := by
    apply max_le
    · have h1 := le_max_left (-w) 0
      have h2 := le_abs_self (w-v)
      linarith
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hδ hn
  nlinarith

lemma oscillation_negative_center_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {W σ : α → ℝ} {v δ B m : ℝ} (hδ : δ ≤ 1/2)
    (hm : 0 < m) (hσ : ∀ᵐ x ∂μ, 0 ≤ σ x) (hi : Integrable σ μ)
    (hp : Integrable (fun x => max (-W x) 0*σ x) μ)
    (hcount : m ≤ ∫ x, σ x ∂μ)
    (ho : ∀ᵐ x ∂μ, |W x-v| ≤ δ*(B+max (-v) 0)) :
    max (-v) 0 ≤ (2/m)*(∫ x, max (-W x) 0*σ x ∂μ)+2*δ*B := by
  have hN : 0 ≤ ∫ x, max (-W x) 0*σ x ∂μ :=
    integral_nonneg_of_ae (hσ.mono fun x hx => mul_nonneg (le_max_right _ _) hx)
  have hM : 0 < ∫ x, σ x ∂μ := hm.trans_le hcount
  have he : max (-v) 0*(∫ x, σ x ∂μ) ≤
      2*(∫ x, max (-W x) 0*σ x ∂μ)+(2*δ*B)*(∫ x, σ x ∂μ) := by
    rw [←integral_const_mul,←integral_const_mul,←integral_const_mul,←integral_add (hp.const_mul 2) (hi.const_mul _)]
    apply integral_mono_ae (hi.const_mul _) ((hp.const_mul 2).add (hi.const_mul _))
    filter_upwards [hσ,ho] with x hx hox
    have hh := mul_le_mul_of_nonneg_right (negative_part_le_of_oscillation hδ hox) hx
    change max (-v) 0 * σ x ≤ 2 * (max (-W x) 0 * σ x) + 2 * δ * B * σ x
    nlinarith
  have hh : max (-v) 0 ≤ 2*(∫ x, max (-W x) 0*σ x ∂μ)/(∫ x, σ x ∂μ)+2*δ*B := by
    have hd : max (-v) 0-2*δ*B ≤ 2*(∫ x, max (-W x) 0*σ x ∂μ)/(∫ x, σ x ∂μ) := by
      apply (le_div_iff₀ hM).mpr
      nlinarith
    linarith
  apply hh.trans
  apply add_le_add _ le_rfl
  calc
    _ ≤ 2*(∫ x, max (-W x) 0*σ x ∂μ)/m :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hN) hm hcount
    _ = _ := by ring

lemma tfPatchGap_negative_integrable (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (σ : TFLp (ballMeasure R)) :
    Integrable (fun z => max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z) (ballMeasure R) := by
  have hh := tfPatchGradient_eq_negative_field R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun f hf => tfPatchMinimizer_min R T hT Φ hf)
  exact (tfPatchGradient_mul_integrable R T Φ (tfPatchMinimizer R T hT Φ) σ).congr
    (hh.mono fun z hz => by dsimp only; rw [hz])

lemma tfPatchGap_negative_le (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (σ : TFLp (ballMeasure R)) :
    (∫ z, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z ∂ballMeasure R) ≤
      tfPatchGap R T hT Φ σ := by
  have hp := tfCoulombL_nonneg R (σ-tfPatchMinimizer R T hT Φ)
  dsimp [tfPatchGap]
  linarith

theorem tfPatchGap_negative_center_control (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) (W : Space → ℝ)
    (hW : ∀ᵐ z ∂ballMeasure R, W z = Φ z-tfBallPotential R (tfPatchMinimizer R T hT Φ) z)
    {q δ B m : ℝ} (hδ : δ ≤ 1/2) (hm : 0 < m)
    (hcount : m ≤ ∫ z in ball (0 : Space) q, σ z ∂ballMeasure R)
    (ho : ∀ z ∈ ball (0 : Space) q, |W z-W 0| ≤ δ*(B+max (-W 0) 0)) :
    max (-W 0) 0 ≤ (2/m)*tfPatchGap R T hT Φ σ+2*δ*B := by
  have hi : Integrable (fun z => σ z) (ballMeasure R) :=
    (Lp.memLp σ).integrable (Fact.out : (1:ENNReal) ≤ 5/3)
  have he : (fun z => max (-W z) 0*σ z) =ᵐ[ballMeasure R]
      fun z => max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z :=
    hW.mono fun z hz => by dsimp only; rw [hz,neg_sub]
  have hp := (tfPatchGap_negative_integrable R T hT Φ σ).congr he.symm
  have hneg : ∀ᵐ z ∂ballMeasure R, 0 ≤ max (-W z) 0*σ z :=
    hσ.mono fun z hz => mul_nonneg (le_max_right _ _) hz
  have hh := oscillation_negative_center_integral hδ hm (ae_restrict_of_ae hσ)
    hi.integrableOn hp.integrableOn hcount
    ((ae_restrict_mem measurableSet_ball).mono fun z hz => ho z hz)
  apply hh.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2/m)
  apply (setIntegral_le_integral hp hneg).trans
  rw [integral_congr_ae he]
  exact tfPatchGap_negative_le R T hT Φ σ

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TFMeanComparison
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric

namespace CoulombAnalysis
open CoulombAtom

lemma oscillation_upper_of_center_le {w v δ B H : ℝ} (hδ : δ ≤ 1)
    (hH : 0 ≤ H) (hv : v ≤ H) (ho : |w-v| ≤ δ*(B+max (-v) 0)) :
    w ≤ H+δ*B := by
  have hh := (abs_le.mp ho).2
  by_cases h : 0 ≤ v
  · rw [max_eq_right (by linarith : -v ≤ 0)] at hh
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ -v)] at hh
    have hp := mul_nonneg (sub_nonneg.mpr hδ) (neg_nonneg.mpr (le_of_not_ge h))
    nlinarith

lemma oscillation_lower_of_center_ge {w v δ B H : ℝ}
    (hH : 0 ≤ H) (hv : H ≤ v) (ho : |w-v| ≤ δ*(B+max (-v) 0)) :
    H-δ*B ≤ w := by
  have hh := (abs_le.mp ho).1
  rw [max_eq_right (by linarith : -v ≤ 0)] at hh
  linarith

lemma tf_euler_density_mono {a u v : ℝ} (ha : 0 ≤ a) (huv : u ≤ v) :
    (max u 0/a)^(3/2:ℝ) ≤ (max v 0/a)^(3/2:ℝ) := by
  apply Real.rpow_le_rpow (div_nonneg (le_max_right _ _) ha) _ (by norm_num)
  exact div_le_div_of_nonneg_right (max_le_max huv le_rfl) ha

lemma tf_density_average_upper {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ W k : α → ℝ} {a v δ B H : ℝ}
    (ha : 0 ≤ a) (hδ : δ ≤ 1) (hH : 0 ≤ H) (hv : v ≤ H)
    (he : ∀ᵐ x ∂μ, ρ x = (max (W x) 0/a)^(3/2:ℝ))
    (hn : ∀ᵐ x ∂μ, 0 ≤ k x) (hi : Integrable k μ)
    (hp : Integrable (fun x => k x*ρ x) μ)
    (ho : ∀ᵐ x ∂μ, k x ≠ 0 → |W x-v| ≤ δ*(B+max (-v) 0)) :
    (∫ x, k x*ρ x ∂μ) ≤ (max (H+δ*B) 0/a)^(3/2:ℝ)*(∫ x, k x ∂μ) := by
  rw [←integral_const_mul]
  apply integral_mono_ae hp (hi.const_mul _)
  filter_upwards [he,hn,ho] with x hx hkn hox
  by_cases hk : k x = 0
  · simp only [hk,zero_mul,mul_zero,le_refl]
  · rw [hx,mul_comm (k x)]
    exact mul_le_mul_of_nonneg_right
      (tf_euler_density_mono ha (oscillation_upper_of_center_le hδ hH hv (hox hk))) hkn

lemma tf_density_average_lower {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ W k : α → ℝ} {a v δ B H : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hv : H ≤ v)
    (he : ∀ᵐ x ∂μ, ρ x = (max (W x) 0/a)^(3/2:ℝ))
    (hn : ∀ᵐ x ∂μ, 0 ≤ k x) (hi : Integrable k μ)
    (hp : Integrable (fun x => k x*ρ x) μ)
    (ho : ∀ᵐ x ∂μ, k x ≠ 0 → |W x-v| ≤ δ*(B+max (-v) 0)) :
    (max (H-δ*B) 0/a)^(3/2:ℝ)*(∫ x, k x ∂μ) ≤ (∫ x, k x*ρ x ∂μ) := by
  rw [←integral_const_mul]
  apply integral_mono_ae (hi.const_mul _) hp
  filter_upwards [he,hn,ho] with x hx hkn hox
  by_cases hk : k x = 0
  · simp only [hk,zero_mul,mul_zero,le_refl]
  · rw [hx,mul_comm (k x)]
    exact mul_le_mul_of_nonneg_right
      (tf_euler_density_mono ha (oscillation_lower_of_center_ge hH hv (hox hk))) hkn

theorem tfPatchMinimizer_mean_upper (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (W : Space → ℝ)
    (hW : ∀ᵐ x ∂ballMeasure R, W x = Φ x-tfBallPotential R (tfPatchMinimizer R T hT Φ) x)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {δ B H : ℝ}
    (hδ : δ ≤ 1) (hH : 0 ≤ H) (hv : W 0 ≤ H)
    (ho : ∀ᵐ x ∂ballMeasure R, k x ≠ 0 → |W x-W 0| ≤ δ*(B+max (-W 0) 0)) :
    (∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R) ≤
      (max (H+δ*B) 0/((5/3:ℝ)*T))^(3/2:ℝ)*(∫ x, k x ∂ballMeasure R) := by
  apply tf_density_average_upper (mul_nonneg (by norm_num) hT.le) hδ hH hv _ hkn
    (hk.integrable (Fact.out : (1:ENNReal) ≤ 5/2)) (hk.integrable_mul (Lp.memLp _)) ho
  have he := tfPatchFunctional_euler R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun g hg => tfPatchMinimizer_min R T hT Φ hg)
  filter_upwards [he,hW] with x hx hWx
  rw [hx,hWx]

theorem tfPatchMinimizer_mean_lower (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    (W : Space → ℝ)
    (hW : ∀ᵐ x ∂ballMeasure R, W x = Φ x-tfBallPotential R (tfPatchMinimizer R T hT Φ) x)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {δ B H : ℝ}
    (hH : 0 ≤ H) (hv : H ≤ W 0)
    (ho : ∀ᵐ x ∂ballMeasure R, k x ≠ 0 → |W x-W 0| ≤ δ*(B+max (-W 0) 0)) :
    (max (H-δ*B) 0/((5/3:ℝ)*T))^(3/2:ℝ)*(∫ x, k x ∂ballMeasure R) ≤
      ∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R := by
  apply tf_density_average_lower (mul_nonneg (by norm_num) hT.le) hH hv _ hkn
    (hk.integrable (Fact.out : (1:ENNReal) ≤ 5/2)) (hk.integrable_mul (Lp.memLp _)) ho
  have he := tfPatchFunctional_euler R Φ hT (tfPatchMinimizer_nonneg R T hT Φ)
    (fun g hg => tfPatchMinimizer_min R T hT Φ hg)
  filter_upwards [he,hW] with x hx hWx
  rw [hx,hWx]

end CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

theorem conditionalPatchMinimizer_negative_center {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (Z lam : ℝ) {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {q m : ℝ} (hq : 0 < q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1/2) (hm : 0 < m)
    (hcount : m ≤ ∫ z in ball (0 : Space) q, σ z ∂ballMeasure R) :
    let Φ := conditionalPatchField ψ t Z lam y R u
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos Φ
    let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
    max (-W 0) 0 ≤ (2/m)*tfPatchGap R tfKinetic tfKinetic_pos Φ σ+
      2*(tfPatchOscillationConstant/R*q)*R⁻¹^4 := by
  dsimp only
  refine tfPatchGap_negative_center_control R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u) hσ
    (fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-
      tfBallPotential R (tfPatchMinimizer R tfKinetic tfKinetic_pos
        (conditionalPatchField ψ t Z lam y R u)) z)
    (B := R⁻¹^4) ?_ hsmall hm hcount ?_
  · have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
    have he := conditionalPatchField_ae ψ t Z lam y R u hp
    filter_upwards [he] with z hz
    rw [hz]
  · intro z hz
    have hzq : ‖z‖ ≤ q := (mem_ball_zero_iff.mp hz).le
    have hRlarge : 0 < R/12 := hq.trans_le hqR
    have hh := conditionalPatchMinimizer_nonradial_oscillation ψ t u hu A hcore y hR hd hr hnuc hsep Z lam z (hzq.trans hqR)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hzq (div_nonneg tfPatchOscillationConstant_pos.le hR.le)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegratedTruncatedControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma patch_test_continuous_of_memLp (R : ℝ) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    Continuous (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) := by
  have he : (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) =
      tfPatchPair R (hm.toLp g) := by
    funext f
    rw [tfPatchPair_apply]
    exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])
  rw [he]
  exact (tfPatchPair R (hm.toLp g)).continuous

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchCenterObservable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
attribute [local instance] OAI.CoulombAtom.patchCenterMeasurableSpace
local instance patchCenterBorelSpace (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma tfBallPotential_zero_continuous (R : ℝ) :
    Continuous (fun f : TFLp (ballMeasure R) => tfBallPotential R f 0) := by
  convert patch_test_continuous_of_memLp R (nuclear_memLp R) using 1
  all_goals try with_reducible_and_instances rfl
  funext f
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [zero_sub,norm_neg]
    ring

lemma conditionalPatchCenter_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (conditionalPatchCenter ψ t Z lam y R) :=
  (normalizedCoreField_eval_aemeasurable hψ t Z lam y).sub
    ((tfBallPotential_zero_continuous R).measurable.comp_aemeasurable
      (conditionalPatchMinimizer_aemeasurable hψ t Z lam y R))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ActualMeanComparison
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchGap_lipschitz_abs_difference {R q : ℝ} (hq : 0 < q) (hqR : 2*q < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R) {σ : TFLp (ballMeasure R)}
    (hσ : NonnegDensity σ) {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k)
    (hs : Function.support k ⊆ closedBall 0 q) :
    |(∫ x, k x*σ x ∂ballMeasure R)-(∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R)| ≤
      Real.sqrt ((16*q^3*(L:ℝ)^2)*tfPatchGap R T hT Φ σ) := by
  have hcompact := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) q) hs
  have hm : MemLp k (5/2) (ballMeasure R) :=
    (hk.continuous.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  have he := Real.abs_le_sqrt (tfPatchGap_lipschitz_control hq hqR T hT Φ hσ hk hs)
  have hpair : (∫ x, k x*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R) =
      (∫ x, k x*σ x ∂ballMeasure R)-(∫ x, k x*tfPatchMinimizer R T hT Φ x ∂ballMeasure R) := by
    have h1 : Integrable (fun x => k x*σ x) (ballMeasure R) :=
      hm.integrable_mul (Lp.memLp σ)
    have h2 : Integrable (fun x => k x*tfPatchMinimizer R T hT Φ x) (ballMeasure R) :=
      hm.integrable_mul (Lp.memLp _)
    rw [←integral_sub h1 h2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub σ (tfPatchMinimizer R T hT Φ)] with x hx
    simp only [hx,Pi.sub_apply,mul_sub]
  rw [hpair] at he
  exact he

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma conditionalPatchMinimizer_mean_upper {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {q H : ℝ}
    (hs : ∀ z, k z ≠ 0 → ‖z‖ ≤ q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1) (hH : 0 ≤ H)
    (hv : conditionalPatchCenter ψ t Z lam y R u ≤ H) :
    (∫ x, k x*tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) x ∂ballMeasure R) ≤
      (max (H+(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R) := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
  have hW : ∀ᵐ z ∂ballMeasure R, W z = conditionalPatchField ψ t Z lam y R u z-tfBallPotential R f z := by
    have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
    filter_upwards [conditionalPatchField_ae ψ t Z lam y R u hp] with z hz
    simp only [W,hz]
  apply tfPatchMinimizer_mean_upper R tfKinetic tfKinetic_pos _ W hW hk hkn hsmall hH
    (by simpa only [W,conditionalPatchCenter,add_zero] using hv)
  exact Eventually.of_forall fun z hz => by
    have hzq := hs z hz
    have hh := conditionalPatchMinimizer_nonradial_oscillation ψ t u hu A hcore y hR hd hr hnuc hsep Z lam z (hzq.trans hqR)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hzq (div_nonneg tfPatchOscillationConstant_pos.le hR.le)

lemma conditionalPatchMinimizer_mean_lower {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {k : Space → ℝ} (hk : MemLp k (5/2) (ballMeasure R))
    (hkn : ∀ᵐ x ∂ballMeasure R, 0 ≤ k x) {q H : ℝ}
    (hs : ∀ z, k z ≠ 0 → ‖z‖ ≤ q) (hqR : q ≤ R/12) (hH : 0 ≤ H)
    (hv : H ≤ conditionalPatchCenter ψ t Z lam y R u) :
    (max (H-(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R) ≤
      ∫ x, k x*tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) x ∂ballMeasure R := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  let W := fun z => normalizedCoreField Z lam (coreSlice ψ t u) (y+z)-tfBallPotential R f z
  have hW : ∀ᵐ z ∂ballMeasure R, W z = conditionalPatchField ψ t Z lam y R u z-tfBallPotential R f z := by
    have hp := normalizedCoreField_memLp_patch hu A hcore y R hd hr hnuc hsep Z lam
    filter_upwards [conditionalPatchField_ae ψ t Z lam y R u hp] with z hz
    simp only [W,hz]
  apply tfPatchMinimizer_mean_lower R tfKinetic tfKinetic_pos _ W hW hk hkn hH
    (by simpa only [W,conditionalPatchCenter,add_zero] using hv)
  exact Eventually.of_forall fun z hz => by
    have hzq := hs z hz
    have hh := conditionalPatchMinimizer_nonradial_oscillation ψ t u hu A hcore y hR hd hr hnuc hsep Z lam z (hzq.trans hqR)
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hzq (div_nonneg tfPatchOscillationConstant_pos.le hR.le)

theorem conditionalPatch_high_center {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q) (hqR : q ≤ R/12)
    (hsmall : tfPatchOscillationConstant/R*q ≤ 1) (hH : 0 ≤ H)
    (hhigh :
      (max (H+(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)+
        Real.sqrt ((16*q^3*(L:ℝ)^2)*tfPatchGap R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) σ) <
        ∫ x, k x*σ x ∂ballMeasure R) :
    H < conditionalPatchCenter ψ t Z lam y R u := by
  by_contra hv
  have hcompact := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) q) hs
  have hm : MemLp k (5/2) (ballMeasure R) :=
    (hk.continuous.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  have he := conditionalPatchMinimizer_mean_upper ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
    hm (Eventually.of_forall hkn) (fun z hz => mem_closedBall_zero_iff.mp (hs hz)) hqR hsmall hH (le_of_not_gt hv)
  have hc := (abs_le.mp (tfPatchGap_lipschitz_abs_difference hq (by linarith : 2*q < R)
    tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) hσ hk hs)).2
  linarith

theorem conditionalPatch_low_center {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖) (Z lam : ℝ)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q) (hqR : q ≤ R/12) (hH : 0 ≤ H)
    (hlow : (∫ x, k x*σ x ∂ballMeasure R)+
        Real.sqrt ((16*q^3*(L:ℝ)^2)*tfPatchGap R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) σ) <
      (max (H-(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)) :
    conditionalPatchCenter ψ t Z lam y R u < H := by
  by_contra hv
  have hcompact := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) q) hs
  have hm : MemLp k (5/2) (ballMeasure R) :=
    (hk.continuous.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  have he := conditionalPatchMinimizer_mean_lower ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
    hm (Eventually.of_forall hkn) (fun z hz => mem_closedBall_zero_iff.mp (hs hz)) hqR hH (le_of_not_gt hv)
  have hc := (abs_le.mp (tfPatchGap_lipschitz_abs_difference hq (by linarith : 2*q < R)
    tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u) hσ hk hs)).1
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchTruncationLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma local_coulomb_le_of_density_cap {f : TFSpace → ℝ} {q C : ℝ}
    (hq : 0 < q) (hf : MemLp f (5/3) (ballMeasure q))
    (hcap : ∀ᵐ x ∂ballMeasure q, ‖f x‖ ≤ C) :
    (∫ x in ball 0 q, ‖f x‖/‖x‖) ≤ 2*Real.pi*C*q^2 := by
  have hi : Integrable (fun x => ‖f x‖/‖x‖) (ballMeasure q) := by
    convert! (nuclear_memLp q).integrable_mul hf.norm using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hk : Integrable (fun x : TFSpace => ‖x‖⁻¹) (ballMeasure q) := by
    simpa only [one_div] using (nuclear_memLp q).integrable (Fact.out : (1 : ENNReal) ≤ 5/2)
  have hh : (∫ x, ‖f x‖/‖x‖ ∂ballMeasure q) ≤ ∫ x, C*‖x‖⁻¹ ∂ballMeasure q := by
    apply integral_mono_ae hi (hk.const_mul C)
    filter_upwards [hcap] with x hx
    exact (div_le_div_of_nonneg_right hx (norm_nonneg x)).trans_eq (by ring)
  apply hh.trans_eq
  rw [integral_const_mul]
  change C*(∫ x : TFSpace in ball 0 q, ‖x‖⁻¹) = _
  rw [integral_coulomb_ball hq]
  ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchCenterIntegrable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchMinimizer_potential_zero_le {R T F : ℝ} (hR : 0 < R)
    (hT : 0 < T) (Φ : TFField R) (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    tfBallPotential R (tfPatchMinimizer R T hT Φ) 0 ≤
      2*Real.pi*((max F 0/((5/3:ℝ)*T))^(3/2:ℝ))*R^2 := by
  have hn := tfPatchMinimizer_nonneg R T hT Φ
  have hb := tfPatchMinimizer_ae_bound hT Φ hΦ
  have he := local_coulomb_le_of_density_cap hR (Lp.memLp (tfPatchMinimizer R T hT Φ))
    (hb.and hn |>.mono fun x hx => by simpa only [Real.norm_of_nonneg hx.2] using hx.1)
  apply le_trans _ he
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [zero_sub,norm_neg,Real.norm_of_nonneg hx]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma conditionalPatchCenter_abs_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    ∀ᵐ u, |conditionalPatchCenter ψ t Z lam y R u| ≤
      finiteCorePatchBound N Z lam b +
        2*Real.pi*((finiteCorePatchBound N Z lam b/((5/3:ℝ)*tfKinetic))^(3/2:ℝ))*R^2 := by
  have hy : y ∈ closedBall y R := mem_closedBall_self hR.le
  filter_upwards [hψ.ae_coreSlice t,
    conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hsep] with u hu hf
  have h1 := normalizedCoreField_abs_le hu A (hcore u) hb y
    (fun a ha => hsep a ha y hy) hb (hnuc y hy) Z lam
  have h2 := tfPatchMinimizer_potential_zero_le hR tfKinetic_pos _ hf
  rw [max_eq_left (finiteCorePatchBound_nonneg N Z lam hb)] at h2
  have hn := tfBallPotential_nonneg (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u)) 0
  exact (abs_sub _ _).trans (add_le_add h1 (by simpa only [abs_of_nonneg hn] using h2))

lemma weightedPatchCenter_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    Integrable (weightedPatchCenter ψ t Z lam y R) := by
  have hbnd := conditionalPatchCenter_abs_le hψ t y hR Z lam hb A hcore hnuc hsep
  have hm := (conditionalPatchCenter_aemeasurable hψ t Z lam y R).aestronglyMeasurable
  exact ((hψ.coreSlice_mass_integrable t).bdd_mul hm
    (hbnd.mono fun u hu => by simpa only [Real.norm_eq_abs] using hu)).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_ExpectedPatchCenter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace CoulombAnalysis

lemma field_lower_from_good_gap {W D H eta C e : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (heta : 0 < eta) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hg : D ≤ eta → H ≤ W) (hn : max (-W) 0 ≤ C*D+e) :
    H-(H/eta+C)*D-e ≤ W := by
  by_cases hd : D ≤ eta
  · have hh := hg hd
    have hb : 0 ≤ (H/eta+C)*D := mul_nonneg (add_nonneg (div_nonneg hH heta.le) hC) hD
    linarith
  · have hb : H ≤ (H/eta)*D := by
      calc
        H = (H/eta)*eta := (div_mul_cancel₀ H heta.ne').symm
        _ ≤ (H/eta)*D := mul_le_mul_of_nonneg_left (le_of_not_ge hd) (div_nonneg hH heta.le)
    have hn' := (le_max_left (-W) 0).trans hn
    nlinarith

lemma field_upper_from_good_gap {W D H eta C : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (heta : 0 < eta) (hC : 0 ≤ C)
    (hg : D ≤ eta → W ≤ H) (hc : W ≤ C) :
    W ≤ H+(C/eta)*D := by
  by_cases hd : D ≤ eta
  · have hh := hg hd
    have hb : 0 ≤ (C/eta)*D := mul_nonneg (div_nonneg hC heta.le) hD
    linarith
  · have hb : C ≤ (C/eta)*D := by
      calc
        C = (C/eta)*eta := (div_mul_cancel₀ C heta.ne').symm
        _ ≤ (C/eta)*D := mul_le_mul_of_nonneg_left (le_of_not_ge hd) (div_nonneg hC heta.le)
    linarith

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormRawPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma rawPotential_measurable {N : ℕ} (y : Space) : Measurable (rawPotential (N := N) y) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.div (configuration_distance_measurable y i))

lemma formRawLaw_ae_no_poles {N : ℕ} (ψ : FormVector N) (y : Space) :
    ∀ᵐ x ∂formRawLaw ψ, ∀ i, x i ≠ y := by
  apply (withDensity_absolutelyContinuous volume _).ae_le
  exact ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i y)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SmearTestRecovery
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_test_bound {b : ℝ} (hb : 0 < b) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x z : Space) :
    ‖g z*varthetaScaled b (z-x)‖ ≤
      (‖g x‖+(L:ℝ)*(Real.sqrt 3*b))*varthetaScaled b (z-x) := by
  by_cases he : varthetaScaled b (z-x) = 0
  · simp [he]
  have hd : ‖z-x‖ ≤ Real.sqrt 3*b := by
    by_contra h
    exact he (varthetaScaled_support hb _ (le_of_not_ge h))
  have hl := hg.dist_le_mul z x
  rw [dist_eq_norm,dist_eq_norm] at hl
  have ht : ‖g z‖ ≤ ‖g x‖+(L:ℝ)*(Real.sqrt 3*b) :=
    calc
      ‖g z‖ ≤ ‖g x‖+‖g z-g x‖ := by simpa only [add_sub_cancel] using norm_add_le (g x) (g z-g x)
      _ ≤ _ := add_le_add_right (hl.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)) _
  rw [norm_mul,Real.norm_of_nonneg (varthetaScaled_nonneg hb _)]
  exact mul_le_mul_of_nonneg_right ht (varthetaScaled_nonneg hb _)

lemma varthetaScaled_test_integrable {b : ℝ} (hb : 0 < b) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : Space) :
    Integrable (fun z => g z*varthetaScaled b (z-x)) := by
  apply (((varthetaScaled_integrable hb).comp_sub_right x).const_mul
    (‖g x‖+(L:ℝ)*(Real.sqrt 3*b))).mono'
    (hg.continuous.aestronglyMeasurable.mul
      (((varthetaScaled_measurable b).comp (measurable_id.sub_const x)).aestronglyMeasurable))
  exact Eventually.of_forall (varthetaScaled_test_bound hb hg x)

theorem varthetaScaled_test_error {b : ℝ} (hb : 0 < b) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (x : Space) :
    ‖(∫ z, g z*varthetaScaled b (z-x))-g x‖ ≤ (L:ℝ)*(Real.sqrt 3*b) := by
  have hi := (varthetaScaled_integrable hb).comp_sub_right x
  have hm : (∫ z, varthetaScaled b (z-x)) = 1 := by
    rw [integral_sub_right_eq_self,integral_varthetaScaled hb]
  have he : (∫ z, g z*varthetaScaled b (z-x))-g x =
      ∫ z, (g z-g x)*varthetaScaled b (z-x) := by
    simp only [sub_mul]
    rw [integral_sub (varthetaScaled_test_integrable hb hg x) (hi.const_mul _),
      integral_const_mul,hm,mul_one]
  rw [he]
  calc
    _ ≤ ∫ z, ((L:ℝ)*(Real.sqrt 3*b))*varthetaScaled b (z-x) :=
      norm_integral_le_of_norm_le (hi.const_mul _) (Eventually.of_forall fun z => by
        by_cases he : varthetaScaled b (z-x) = 0
        · simp [he]
        have hd : ‖z-x‖ ≤ Real.sqrt 3*b := by
          by_contra h
          exact he (varthetaScaled_support hb _ (le_of_not_ge h))
        rw [norm_mul,Real.norm_of_nonneg (varthetaScaled_nonneg hb _)]
        have hl := hg.dist_le_mul z x
        rw [dist_eq_norm,dist_eq_norm] at hl
        exact mul_le_mul_of_nonneg_right
          (hl.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)) (varthetaScaled_nonneg hb _))
    _ = _ := by rw [integral_const_mul,hm,mul_one]

lemma integral_retainedSmear_test {N : ℕ} {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) :
    (∫ z, g z*retainedSmear b S x z) = ∑ i ∈ S, ∫ z, g z*varthetaScaled b (z-x i) := by
  simp only [retainedSmear,Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => varthetaScaled_test_integrable hb hg (x i))

end CoulombNeumann

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_test_zero_of_far {b r : ℝ} (hb : 0 < b)
    {g : Space → ℝ} {y x : Space}
    (hs : Function.support g ⊆ closedBall y r)
    (hx : r+Real.sqrt 3*b < ‖x-y‖) :
    (∀ z, g z*varthetaScaled b (z-x) = 0) ∧ g x = 0 := by
  have hb0 : 0 ≤ Real.sqrt 3*b := by positivity
  constructor
  · intro z
    by_cases hg : g z = 0
    · simp [hg]
    by_cases he : varthetaScaled b (z-x) = 0
    · simp [he]
    have hz : ‖z-y‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hs hg
    have hd : ‖z-x‖ ≤ Real.sqrt 3*b := by
      by_contra h
      exact he (varthetaScaled_support hb _ (le_of_not_ge h))
    have ht := dist_triangle x z y
    simp only [dist_eq_norm] at ht
    rw [norm_sub_rev x z] at ht
    exfalso; linarith
  · by_contra hg
    have hz : ‖x-y‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hs hg
    linarith

theorem retainedSmear_local_test_error {N : ℕ} {b r : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r) :
    ‖(∫ z, g z*retainedSmear b S x z)-(∑ i ∈ S, g (x i))‖ ≤
      ((S.filter (fun i => ‖x i-y‖ ≤ r+Real.sqrt 3*b)).card:ℝ)*
        ((L:ℝ)*(Real.sqrt 3*b)) := by
  classical
  rw [integral_retainedSmear_test hb S x hg,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ S, if ‖x i-y‖ ≤ r+Real.sqrt 3*b then (L:ℝ)*(Real.sqrt 3*b) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact varthetaScaled_test_error hb hg (x i)
      · obtain ⟨hz,hg0⟩ := varthetaScaled_test_zero_of_far hb hs (lt_of_not_ge hi)
        simp only [hz,integral_zero,hg0,sub_zero,norm_zero,le_refl]
    _ = _ := by rw [←Finset.sum_filter]; simp

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma radialCut_core_distance {N : ℕ} (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (i : Fin N) (hi : c i = 0) : t ≤ ‖x i-y‖ := by
  classical
  change (∏ j, (coreFirstRadialCut y ht hb (c j)).value (x j)) ≠ 0 at hx
  have hf := (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  by_contra hn
  apply hf
  rw [hi]
  exact coreFirstRadialCut_core_zero y ht hb (x i) hn

theorem radialCut_retained_test_eq_raw {N : ℕ} (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (s : Spins (cutOutNumber c)) {g : Space → ℝ}
    (hs : Function.support g ⊆ closedBall y r) :
    (∑ i ∈ radialPatchRetention N y t b c s (cutOutPositions c x),
      g (cutOutPositions c x i)) = ∑ i, g (x i) := by
  classical
  have he : (∑ i ∈ radialPatchRetention N y t b c s (cutOutPositions c x),
      g (cutOutPositions c x i)) = ∑ i, g (cutOutPositions c x i) := by
    unfold radialPatchRetention
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs with hi
    · rfl
    · symm
      apply Function.notMem_support.mp
      intro hg
      have hd : ‖cutOutPositions c x i-y‖ ≤ r := by
        simpa only [mem_closedBall,dist_eq_norm] using hs hg
      exact hi (hd.trans_lt hr)
  rw [he,sum_cutOutPositions]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · symm
    apply Function.notMem_support.mp
    intro hg
    have hd : ‖x i-y‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hs hg
    have hc := radialCut_core_distance y ht hb c x hx i (not_ne_iff.mp hi)
    linarith

theorem radialCut_local_smear_error {N : ℕ} (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    (c : Fin N → Fin 2) (x : Configuration N)
    (hx : (spatialProduct (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) c).value x ≠ 0)
    (s : Spins (cutOutNumber c)) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (hs : Function.support g ⊆ closedBall y r) :
    let u := cutOutPositions c x
    let S := radialPatchRetention N y t b c s u
    ‖(∫ z, g z*retainedSmear b S u z)-(∑ i, g (x i))‖ ≤
      ((S.filter (fun i => ‖u i-y‖ ≤ r+Real.sqrt 3*b)).card:ℝ)*
        ((L:ℝ)*(Real.sqrt 3*b)) := by
  dsimp only
  rw [←radialCut_retained_test_eq_raw y ht hb hr c x hx s hs]
  exact retainedSmear_local_test_error hb _ _ y hg hs

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationIntegral_scope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma eventLog_eq {p : ℝ} (hp : 0 < p) : Real.log (Real.exp 1/p) = 1-Real.log p := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp]

end Work_ObservationIntegral_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

lemma observationFisherConstant_pos : 0 < observationFisherConstant := by
  unfold observationFisherConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) observationMomentConstant_pos

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_DyadicObservation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombObservation

lemma dyadicObservationWidth_pos {r : ℝ} (hr : 0 < r) (k : ℕ) :
    0 < dyadicObservationWidth r k := Real.rpow_pos_of_pos (by positivity) _

end CoulombObservation

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

lemma unorderedStatistic_measurable {N : ℕ} {g : Space → ℝ} (hg : Measurable g) :
    Measurable (unorderedStatistic (N := N) g) := by
  apply measurable_from_quotient.mpr
  change Measurable (fun x : Configuration N => ∑ i, g (x i))
  exact Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

lemma observedStatistic_information_measurable {N K : ℕ} (ell : Fin K → ℝ)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) {g : Space → ℝ} (hg : Measurable g) :
    Measurable[observationInformation ell j]
      (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
        ∑ i, g (physicalObservedConfiguration ell k z i)) := by
  have h := (unorderedStatistic_measurable (N := N) hg).comp
    (comap_measurable (unorderedObservedConfiguration (N := N) ell k))
  apply h.mono
  · exact le_iSup_of_le k (by rw [ite_eq_left hk])
  · exact le_refl _

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

namespace CoulombObservation

lemma compactNoiseLaw_ae_support : ∀ᵐ u ∂compactNoiseLaw, |u| < 1 := by
  rw [compactNoiseLaw,ae_withDensity_iff compactNoiseDensity_measurable.ennreal_ofReal]
  apply ae_of_all
  intro u hu
  by_contra hn
  exact hu (by simp [compactNoiseDensity,compactNoiseWeight,hn])

lemma compactNoiseLaw_pi_ae_support {ι : Type*} [Fintype ι] :
    ∀ᵐ u ∂Measure.pi (fun _ : ι => compactNoiseLaw), ∀ i, |u i| < 1 :=
  eventually_all.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => compactNoiseLaw) (i := i)).eventually
      compactNoiseLaw_ae_support)

end CoulombObservation
namespace CoulombAtom
open CoulombObservation

lemma physicalObservedConfiguration_displacement {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (hk : 0 ≤ ell k) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hu : ∀ q, |z.2 q| < 1) (i : Fin N) :
    ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k := by
  have he (a : Fin 3) : (physicalObservedConfiguration ell k z i-z.1 i) a =
      ell k*z.2 (k,i,a) := by
    change (z.1 i a+ell k*z.2 (k,i,a))-z.1 i a = _
    ring
  have hs : ‖physicalObservedConfiguration ell k z i-z.1 i‖^2 ≤ 3*(ell k)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [he]
    calc
      _ ≤ ∑ _a : Fin 3, (ell k)^2 := by
        apply Finset.sum_le_sum
        intro a _
        have hsq : (z.2 (k,i,a))^2 ≤ 1 := by
          have := hu (k,i,a)
          have := abs_nonneg (z.2 (k,i,a))
          nlinarith [sq_abs (z.2 (k,i,a))]
        rw [mul_pow]
        exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)).trans_eq (mul_one _)
      _ = _ := by simp
  have hs3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 3*ell k := mul_nonneg (Real.sqrt_nonneg _) hk
  nlinarith [sq_nonneg (‖physicalObservedConfiguration ell k z i-z.1 i‖-Real.sqrt 3*ell k)]

lemma physicalObservationLaw_ae_displacement {N K : ℕ} (μ : Measure (Configuration N))
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ k i,
      ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k := by
  have h := (Measure.quasiMeasurePreserving_snd (μ := μ)
    (ν := Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).tendsto_ae.eventually
      compactNoiseLaw_pi_ae_support
  exact h.mono (fun z hz k i => physicalObservedConfiguration_displacement ell k (hell k) z hz i)

lemma observedLocalCount_information_measurable {N K : ℕ} (ell : Fin K → ℝ)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (y : Space) (R : ℝ) :
    Measurable[observationInformation ell j] (observedLocalCount (N := N) ell k y R) := by
  exact observedStatistic_information_measurable ell k hk
    (measurable_const.ite (measurableSet_le (show Measurable (fun x : Space => ‖x-y‖) by fun_prop) measurable_const) measurable_const)

lemma observedLocalCount_nonneg {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) (y : Space) (R : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : 0 ≤ observedLocalCount ell k y R z := by
  unfold observedLocalCount
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma observedLocalCount_le {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) (y : Space) (R : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : observedLocalCount ell k y R z ≤ N := by
  calc
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma matchedLocal_test_error {N : ℕ} (x u : Configuration N) {δ R : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, ‖u i-x i‖ ≤ δ) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (y : Space) (hs : Function.support g ⊆ closedBall y R) :
    |(∑ i, g (x i))-(∑ i, g (u i))| ≤
      (∑ i, if ‖u i-y‖ ≤ R+δ then (1:ℝ) else 0)*((L:ℝ)*δ) := by
  classical
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |g (x i)-g (u i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (if ‖u i-y‖ ≤ R+δ then (1:ℝ) else 0)*((L:ℝ)*δ) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · simp only [one_mul]
        exact (hg.dist_le_mul (x i) (u i)).trans
          (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm,norm_sub_rev] using hx i) L.coe_nonneg)
      · have hu : g (u i) = 0 := by
          apply Function.notMem_support.mp
          intro hu
          have ha := hs hu
          simp only [mem_closedBall,dist_eq_norm] at ha
          exact hi (by linarith)
        have hx0 : g (x i) = 0 := by
          apply Function.notMem_support.mp
          intro h0
          have ha := hs h0
          simp only [mem_closedBall,dist_eq_norm] at ha
          have ht := norm_add_le (u i-x i) (x i-y)
          rw [sub_add_sub_cancel] at ht
          exact hi (by linarith [hx i])
        simp [hu,hx0]
    _ = _ := by rw [Finset.sum_mul]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ConditionalSandwich
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter

namespace CoulombObservation

lemma condExp_observable_sandwich {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀) [IsFiniteMeasure μ]
    {f h d : Ω → ℝ} (hf : Integrable f μ) (hh : Integrable h μ) (hd : Integrable d μ)
    (hhm : StronglyMeasurable[m] h) (hdm : StronglyMeasurable[m] d)
    (hb : ∀ᵐ z ∂μ, |f z-h z| ≤ d z) :
    ∀ᵐ z ∂μ, |μ[f | m] z-h z| ≤ d z := by
  have hlow : (fun z => h z-d z) ≤ᵐ[μ] f := hb.mono (fun z hz => by
    have := (abs_le.mp hz).1
    linarith)
  have hupp : f ≤ᵐ[μ] (fun z => h z+d z) := hb.mono (fun z hz => by
    have := (abs_le.mp hz).2
    linarith)
  have hlo := condExp_mono (m := m) (hh.sub hd) hf hlow
  have hup := condExp_mono (m := m) hf (hh.add hd) hupp
  rw [condExp_of_stronglyMeasurable (m₀ := m₀) (μ := μ) hm (hhm.sub hdm) (hh.sub hd)] at hlo
  rw [condExp_of_stronglyMeasurable (m₀ := m₀) (μ := μ) hm (hhm.add hdm) (hh.add hd)] at hup
  filter_upwards [hlo,hup] with z hl hu
  simp only [Pi.sub_apply,Pi.add_apply] at hl hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end CoulombObservation

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombAtom
open CoulombObservation

lemma integrable_configuration_test {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N : ℕ} {X : Ω → Configuration N}
    (hX : Measurable X) {g : Space → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun z => ∑ i, g (X z i)) μ := by
  obtain ⟨v,hv⟩ := hg.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  apply integrable_finsetSum
  intro i _
  apply (integrable_const ‖g v‖).mono'
    ((hg.measurable.comp ((measurable_pi_apply i).comp hX)).aestronglyMeasurable)
  exact ae_of_all _ (fun z => hv (X z i))

lemma observedLocalCount_integrable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (k : Fin K) (y : Space) (R : ℝ) :
    Integrable (observedLocalCount (N := N) ell k y R) (physicalObservationLaw μ K) := by
  have h := (observedLocalCount_information_measurable (N := N) ell k (Nat.zero_le _) y R).mono
    (observationInformation_le ell 0) (le_refl _)
  apply (integrable_const (N:ℝ)).mono' h.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (observedLocalCount_nonneg ell k y R z)] using
      observedLocalCount_le ell k y R z)

theorem posterior_observed_test_sandwich {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (y : Space) (R : ℝ)
    (hs : Function.support g ⊆ closedBall y R) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      |posteriorTestValue μ ell j g z-(∑ i, g (physicalObservedConfiguration ell k z i))| ≤
        observedLocalCount ell k y (R+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k)) := by
  have hc : HasCompactSupport g := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y R) hs
  have hf := integrable_configuration_test (physicalObservationLaw μ K)
    measurable_fst hg.continuous hc
  have hh := integrable_configuration_test (physicalObservationLaw μ K)
    (physicalObservedConfiguration_measurable ell k) hg.continuous hc
  have hd := (observedLocalCount_integrable μ ell k y (R+Real.sqrt 3*ell k)).mul_const
    ((L:ℝ)*(Real.sqrt 3*ell k))
  have hhm := (observedStatistic_information_measurable (N := N) ell k hk hg.continuous.measurable).stronglyMeasurable
  have hdm := ((observedLocalCount_information_measurable (N := N) ell k hk y (R+Real.sqrt 3*ell k)).mul_const
    ((L:ℝ)*(Real.sqrt 3*ell k))).stronglyMeasurable
  apply condExp_observable_sandwich (observationInformation_le ell j)
    (physicalObservationLaw μ K) hf hh hd hhm hdm
  filter_upwards [physicalObservationLaw_ae_displacement μ ell hell] with z hz
  exact matchedLocal_test_error z.1 (physicalObservedConfiguration ell k z)
    (mul_nonneg (Real.sqrt_nonneg _) (hell k)) (hz k) hg y hs

theorem raw_posterior_local_test_error {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (y : Space) (R : ℝ)
    (hs : Function.support g ⊆ closedBall y R) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      |(∑ i, g (z.1 i))-posteriorTestValue μ ell j g z| ≤
        2*observedLocalCount ell k y (R+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k)) := by
  filter_upwards [physicalObservationLaw_ae_displacement μ ell hell,
    posterior_observed_test_sandwich μ ell hell k hk hg y R hs] with z hz hp
  have hr := matchedLocal_test_error z.1 (physicalObservedConfiguration ell k z)
    (mul_nonneg (Real.sqrt_nonneg _) (hell k)) (hz k) hg y hs
  have he : (∑ i, g (z.1 i))-posteriorTestValue μ ell j g z =
    ((∑ i, g (z.1 i))-(∑ i, g (physicalObservedConfiguration ell k z i)))+
    ((∑ i, g (physicalObservedConfiguration ell k z i))-posteriorTestValue μ ell j g z) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm (∑ i, g (physicalObservedConfiguration ell k z i))]
  change _+_ ≤ 2*observedLocalCount ell k y (R+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k))
  dsimp only [observedLocalCount] at hp ⊢
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma masterWidth_upper {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hs : 0 < s)
    (x : Space) : masterWidth c₁ r₀ s x ≤ c₁*masterBaseDistance r₀ x*s^masterExponent := by
  have hD : 0 < masterBaseDistance r₀ x := hr.trans_le (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_min hD.le hs.le) (min_le_right _ _) masterExponent_nonneg)
    (mul_nonneg hc hD.le)

open Set Metric
open scoped NNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterRecovery
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma masterKernel_test_support {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    Function.support (fun x => masterKernel c₁ r₀ s g x y) ⊆
      closedBall y (2*masterWidth c₁ r₀ s y) :=
  ((masterKernel_uniform_test_constants hg hgs).choose_spec.2 c₁ r₀ s hc hcL hr hs hs1 y).1

lemma masterKernel_test_lipschitz {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    LipschitzWith ⟨(masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ s y)⁻¹^4, by positivity⟩
      (fun x => masterKernel c₁ r₀ s g x y) :=
  ((masterKernel_uniform_test_constants hg hgs).choose_spec.2 c₁ r₀ s hc hcL hr hs hs1 y).2

lemma masterCenteredKernel_support {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    Function.support (masterCenteredKernel c₁ r₀ s g y) ⊆
      closedBall 0 (2*masterWidth c₁ r₀ s y) := by
  intro x hx
  have hh := masterKernel_test_support hg hgs hc hcL hr hs hs1 y hx
  simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hh

lemma masterCenteredKernel_lipschitz {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space) :
    LipschitzWith ⟨(masterTestConstant hg hgs:ℝ)*(masterWidth c₁ r₀ s y)⁻¹^4, by positivity⟩
      (masterCenteredKernel c₁ r₀ s g y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  have hh := (masterKernel_test_lipschitz hg hgs hc hcL hr hs hs1 y).dist_le_mul (y+x) (y+z)
  simpa only [masterCenteredKernel,dist_add_left] using hh

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FreshPosteriorSandwich
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshPosteriorSandwich_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

open CoulombObservation CoulombNeumann CoulombAnalysis

theorem fresh_original_posterior_sandwich {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ (c : Fin N → Fin 2),
      (spatialProduct (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) c).value z.1 ≠ 0 →
      ∀ s : Spins (cutOutNumber c),
      let u := cutOutPositions c z.1
      let S := radialPatchRetention N y t b c s u
      ‖(∫ v, g v*retainedSmear b S u v)-posteriorTestValue μ ell j g z‖ ≤
        ((S.filter (fun i => ‖u i-y‖ ≤ r+Real.sqrt 3*b)).card:ℝ)*
          ((L:ℝ)*(Real.sqrt 3*b))+
        2*observedLocalCount ell k y (r+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k)) := by
  filter_upwards [raw_posterior_local_test_error μ ell hell k hk hg y r hs] with z hz
  intro c hc s
  dsimp only
  have hm := radialCut_local_smear_error y ht hb hr c z.1 hc s hg hs
  have he : (∫ v, g v*retainedSmear b
      (radialPatchRetention N y t b c s (cutOutPositions c z.1)) (cutOutPositions c z.1) v)-
        posteriorTestValue μ ell j g z =
      ((∫ v, g v*retainedSmear b
        (radialPatchRetention N y t b c s (cutOutPositions c z.1)) (cutOutPositions c z.1) v)-
          (∑ i, g (z.1 i)))+((∑ i, g (z.1 i))-posteriorTestValue μ ell j g z) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hm (by simpa only [Real.norm_eq_abs] using hz))

end Work_FreshPosteriorSandwich_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal ContDiff

open CoulombObservation CoulombNeumann CoulombAnalysis

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

lemma originalDatum_comap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace.comap (originalDatum (N := N) ell j) inferInstance =
      observationInformation ell j := MeasurableSpace.comap_id

lemma kernelPosteriorTest_eq {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have h := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable
    ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).stronglyMeasurable) hi
  simpa only [originalDatum_comap,posteriorTestValue,kernelPosteriorTest,originalRawKernel,Function.comp_def] using h

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma jointMasterPosterior_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  have h : StronglyMeasurable (fun p : (OriginalDatum N K ell j × Space) × Configuration N =>
      ∑ i, masterKernel c₁ r₀ s g (p.2 i) p.1.2) :=
    (Finset.measurable_sum _ (fun i _ => hm.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := (originalRawKernel μ ell j).comap Prod.fst measurable_fst)).measurable

lemma jointMasterPosterior_eq_scalar {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1) (y : Space) :
    (fun z => masterPosterior μ ell j c₁ r₀ s g z y) =ᵐ[physicalObservationLaw μ K]
      fun z => jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z) y := by
  have hL := masterKernel_test_lipschitz hg hgs hc hcL hr hs hs1 y
  have hS := masterKernel_test_support hg hgs hc hcL hr hs hs1 y
  exact kernelPosteriorTest_eq μ ell j hL.continuous.measurable
    (integrable_configuration_test _ measurable_fst hL.continuous
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hS))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_MasterPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma scaled_packet_density_radial (b : ℝ) {g : Space → ℝ} (hr : IsRadial g) :
    IsRadial (fun x => (scaledRealPacket b g x)^2) := by
  intro x y hxy
  dsimp only
  rw [scaledRealPacket_radial b hr x y hxy]

lemma scaled_packet_density_support {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) (x : Space) (hx : (scaledRealPacket b g x)^2 ≠ 0) :
    ‖x‖ ≤ b := (scaledRealPacket_support hb hs (by intro hz; exact hx (by rw [hz]; norm_num))).le

lemma scaled_packet_potential_le {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x, (g x)^2 = 1) (hr : IsRadial g) (hs : tsupport g ⊆ ball 0 1)
    {x : Space} (hx : x ≠ 0) :
    tfPotential (fun z => (scaledRealPacket b g z)^2) x ≤ 1/‖x‖ := by
  have hc : Continuous (fun z => (scaledRealPacket b g z)^2) := by
    exact (scaledRealPacket_smooth b hg).continuous.pow 2
  have hcomp : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
    convert! (scaledRealPacket_compact hb hcg).mul_right (f' := scaledRealPacket b g) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact pow_two _
  have hh := radial_potential_le_point (hc.integrable_of_hasCompactSupport hcomp)
    (hc.memLp_of_hasCompactSupport hcomp) (fun z => sq_nonneg _)
    (scaled_packet_density_radial b hr) hb.le (scaled_packet_density_support hb hs) hx
  simpa only [scaledRealPacket_mass hb,hgn] using hh

lemma masterKernel_potential_centered (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    tfPotential (masterKernel c₁ r₀ s g x) y =
      tfPotential (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) (y-x) :=
  integral_translated_pole (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) y x

lemma masterKernel_potential_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ tfPotential (masterKernel c₁ r₀ s g x) y :=
  tfPotential_nonneg (ae_of_all _ (masterKernel_nonneg c₁ r₀ s g x)) y

lemma masterKernel_potential_le {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) :
    tfPotential (masterKernel c₁ r₀ s g x) y ≤ 1/‖y-x‖ := by
  rw [masterKernel_potential_centered]
  exact scaled_packet_potential_le (masterWidth_pos hc hr hs x) hg hcg hgn hrad hgs
    (sub_ne_zero.mpr hxy.symm)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedTruncatedControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

lemma scaled_packet_density_compact {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
  convert! (scaledRealPacket_compact hb hg).mul_right (f' := scaledRealPacket b g) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact pow_two _

lemma masterKernel_pole_measurable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) (y : Space) :
    Measurable (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) := by
  have hm : Measurable (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterKernelFubini
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAnalysis

lemma masterKernel_pole_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x y : Space) :
    Integrable (fun z => masterKernel c₁ r₀ s g x z/‖y-z‖) := by
  have hη := scaled_packet_density_compact (masterWidth_pos hc hr hs x) hcg
  have hηc := (scaledRealPacket_smooth (masterWidth c₁ r₀ s x) hg).continuous.pow 2
  exact translated_pole_integrable (hηc.integrable_of_hasCompactSupport hη)
    (hηc.memLp_of_hasCompactSupport hη) y x

lemma master_configuration_potential_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun x : Configuration N => ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y) ν := by
  apply hi.mono' ((Finset.measurable_sum _ (fun i _ =>
    (masterKernel_pole_measurable hc hr hs hg.continuous y).comp (measurable_pi_apply i))).aestronglyMeasurable)
  filter_upwards [he] with x hx
  change ‖∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y‖ ≤ rawPotential y x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_potential_nonneg c₁ r₀ s g (x i) y))]
  apply Finset.sum_le_sum
  intro i _
  simpa only [norm_sub_rev] using masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs (hx i)

lemma master_configuration_pole_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖)
      (ν.prod volume) := by
  have hm : Measurable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖) :=
    (Finset.measurable_sum _ (fun i _ => (masterKernel_joint_continuous hc hr hs hg.continuous).measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).div (by fun_prop)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => ?_),?_⟩
  · simp only [Finset.sum_div]
    exact integrable_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)
  · have hp := master_configuration_potential_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Finset.sum_div]
    simp_rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
      div_nonneg (masterKernel_nonneg c₁ r₀ s g (x i) _) (norm_nonneg _)))]
    exact integral_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)

theorem master_configuration_potential_fubini {N : ℕ} (ν : Measure (Configuration N)) [SFinite ν]
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    tfPotential (fun z => ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν) y =
      ∫ x, ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y ∂ν := by
  change (∫ z, (∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν)/‖y-z‖) = _
  calc
    _ = ∫ z, ∫ x, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖ ∂ν := by simp only [integral_div]
    _ = ∫ x, (∫ z, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖) ∂ν :=
      integral_integral_swap (master_configuration_pole_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs).swap
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [Finset.sum_div]
        exact integral_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y))

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombObservation ProbabilityTheory

lemma originalRawKernel_comp {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) :
    originalRawKernel μ ell j ∘ₘ ((physicalObservationLaw μ K).map (originalDatum ell j)) = μ := by
  rw [originalRawKernel,condDistrib_comp_map (originalDatum_measurable ell j).aemeasurable
    measurable_fst.aemeasurable]
  simp [physicalObservationLaw,Measure.map_fst_prod]

lemma originalRawKernel_ae {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {P : Configuration N → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ᵐ x ∂originalRawKernel μ ell j (originalDatum ell j z), P x := by
  rw [←originalRawKernel_comp μ ell j] at hP
  exact ae_of_ae_map (originalDatum_measurable ell j).aemeasurable (Measure.ae_ae_of_ae_comp hP)

lemma originalRawKernel_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {f : Configuration N → ℝ} (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      Integrable f (originalRawKernel μ ell j (originalDatum ell j z)) := by
  have hx := originalDatum_measurable (N := N) ell j
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hi0 : Integrable (fun a : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => f a.1)
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  have hi1 : Integrable (fun p : OriginalDatum N K ell j × Configuration N => f p.2)
      ((physicalObservationLaw μ K).map (fun a => (originalDatum ell j a,a.1))) := by
    apply (integrable_map_measure (hf.comp measurable_snd).aestronglyMeasurable
      (hx.prodMk measurable_fst).aemeasurable).mpr
    exact hi0
  exact hi1.condDistrib_ae hx.aemeasurable measurable_fst.aemeasurable

lemma kernelPosteriorTest_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ) :
    Integrable (fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z))
      (physicalObservationLaw μ K) := by
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hf : Measurable (fun x : Configuration N => ∑ i, g (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hg.comp (measurable_pi_apply i))
  have hi0 : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => ∑ i, g (z.1 i))
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  exact integrable_condExp.congr (kernelPosteriorTest_eq μ ell j hg hi0)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterPosteriorPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma jointMasterPosterior_potential_eq_kernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y) =ᵐ[
      physicalObservationLaw μ K] fun z => kernelPosteriorTest μ ell j
        (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  exact master_configuration_potential_fubini _ y hz hze hc hr hs hg hcg hgn hrad hgs

lemma jointMasterPosterior_potential_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y)
      (physicalObservationLaw μ K) :=
  (kernelPosteriorTest_integrable μ ell j (masterKernel_pole_measurable hc hr hs hg.continuous y)
    (master_configuration_potential_integrable μ y hi he hc hr hs hg hcg hgn hrad hgs)).congr
      (jointMasterPosterior_potential_eq_kernel μ ell j y hi he hc hr hs hg hcg hgn hrad hgs).symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

lemma formRawLaw_graph {N : ℕ} (F : fermionGraph N) :
    formRawLaw (graphFormVector F) = graphRawLaw F := rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_UnshiftedCellCountBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombBarrier
open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

lemma masterWidth_radius_lower {c₁ r₀ s r : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r)
    (hrs : r ≤ s) {y : Space} (hy : r ≤ ‖y‖) :
    c₁*r^(1+masterExponent) ≤ masterWidth c₁ r₀ s y := by
  have hd : r ≤ masterBaseDistance r₀ y := hy.trans (le_max_left _ _)
  have hm : r ≤ min (masterBaseDistance r₀ y) s := le_min hd hrs
  rw [masterWidth,Real.rpow_add hr]
  simp only [Real.rpow_one]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hd (Real.rpow_le_rpow hr.le hm masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hd)) hc

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma sharpFreshFieldConstant_one_le : 1 ≤ sharpFreshFieldConstant := by
  have hC := actualCellMomentConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold sharpFreshFieldConstant
  have h : 0 ≤ thinFieldUniversalConstant*(6+actualCellMomentConstant+
      localizationIMSConstant*actualCellMomentConstant) := by positivity
  linarith only [h]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierInitialEventBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma threshold_event_mean_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hi : Integrable f μ) {t : ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hAB : ∀ z ∈ A, t ≤ f z) (hp : 0 < (μ A).toReal) :
    t ≤ ((μ A).toReal)⁻¹*(∫ z in A, f z ∂μ) := by
  have he : (μ A).toReal*t ≤ ∫ z in A, f z ∂μ := by
    calc
      _ = ∫ z in A, t ∂μ := by simp [Measure.real,smul_eq_mul]
      _ ≤ _ := setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn hA hAB
  have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_FreshObservedSandwichBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshObservedSandwich_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

open CoulombObservation CoulombNeumann CoulombAnalysis

lemma observedLocalCount_mono {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) {r R : ℝ} (hr : r ≤ R)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    observedLocalCount ell k y r z ≤ observedLocalCount ell k y R z := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · exact False.elim (hj (hi.trans hr))
  · norm_num
  · exact le_rfl

lemma cut_filtered_count_le_observed {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) (r : ℝ) (c : Fin N → Fin 2)
    (S : Finset (Fin (cutOutNumber c)))
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    ((S.filter (fun i => ‖cutOutPositions c z.1 i-y‖ ≤ r)).card:ℝ) ≤
      observedLocalCount ell k y (r+Real.sqrt 3*ell k) z := by
  classical
  let f : Fin (cutOutNumber c) → Fin N := fun i => cutOrder c (finSumFinEquiv (Sum.inr i))
  have hf : Function.Injective f := (cutOrder c).injective.comp
    (finSumFinEquiv.injective.comp Sum.inr_injective)
  have hh : (S.filter (fun i => ‖cutOutPositions c z.1 i-y‖ ≤ r)).card ≤
      (Finset.univ.filter (fun i => ‖physicalObservedConfiguration ell k z i-y‖ ≤
        r+Real.sqrt 3*ell k)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      change f i ∈ Finset.univ.filter _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have ht := norm_add_le (physicalObservedConfiguration ell k z (f i)-z.1 (f i))
        (z.1 (f i)-y)
      rw [sub_add_sub_cancel] at ht
      exact (ht.trans (add_le_add (hd (f i)) (Finset.mem_filter.mp hi).2)).trans_eq (add_comm _ _)
    · exact fun _ _ _ _ h => hf h
  simpa only [observedLocalCount,Finset.sum_boole] using (Nat.cast_le (α := ℝ)).mpr hh

theorem fresh_original_observed_sandwich {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ (c : Fin N → Fin 2),
      (spatialProduct (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) c).value z.1 ≠ 0 →
      ∀ s : Spins (cutOutNumber c),
      let u := cutOutPositions c z.1
      let S := radialPatchRetention N y t b c s u
      ‖(∫ v, g v*retainedSmear b S u v)-posteriorTestValue μ ell j g z‖ ≤
        observedLocalCount ell k y (r+Real.sqrt 3*(b+ell k)) z*
          ((L:ℝ)*Real.sqrt 3*(b+2*ell k)) := by
  filter_upwards [fresh_original_posterior_sandwich μ ell hell k hk y ht hb hr hg hs,
    physicalObservationLaw_ae_displacement μ ell hell] with z hz hd
  intro c hc s
  dsimp only
  have hnoise := hell k
  have hf := cut_filtered_count_le_observed ell k y (r+Real.sqrt 3*b) c
    (radialPatchRetention N y t b c s (cutOutPositions c z.1)) z (hd k)
  have he : r+Real.sqrt 3*b+Real.sqrt 3*ell k = r+Real.sqrt 3*(b+ell k) := by ring
  rw [he] at hf
  have hm := observedLocalCount_mono ell k y
    (show r+Real.sqrt 3*ell k ≤ r+Real.sqrt 3*(b+ell k) by
      nlinarith [Real.sqrt_nonneg (3:ℝ)]) z
  have h1 := mul_le_mul_of_nonneg_right hf
    (by positivity : 0 ≤ (L:ℝ)*(Real.sqrt 3*b))
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 2))
    (by positivity : 0 ≤ (L:ℝ)*(Real.sqrt 3*ell k))
  exact (hz c hc s).trans ((add_le_add h1 h2).trans_eq (by ring))

end Work_FreshObservedSandwich_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma observed_count_le_raw_enlarged {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) {R Q : ℝ} (hRQ : R+Real.sqrt 3*ell k < Q)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    observedLocalCount ell k y R z ≤ rawBallCount y Q z.1 := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · have ht := norm_add_le (z.1 i-physicalObservedConfiguration ell k z i)
      (physicalObservedConfiguration ell k z i-y)
    rw [sub_add_sub_cancel] at ht
    have hd' : ‖z.1 i-physicalObservedConfiguration ell k z i‖ ≤ Real.sqrt 3*ell k := by
      simpa only [norm_sub_rev] using hd i
    exact False.elim (hj (by linarith [hd']))
  · norm_num
  · exact le_rfl

lemma event_rawLaw_ae {N K : ℕ} (F G : fermionGraph N) (_ell : Fin K → ℝ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    {c : ℝ≥0∞} (hlaw : graphRawLaw G = c • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    {P : Configuration N → Prop} (hP : MeasurableSet {x | P x})
    (hA : MeasurableSet A)
    (h : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A → P z.1) :
    ∀ᵐ x ∂graphRawLaw G, P x := by
  rw [hlaw]
  apply Measure.ae_smul_measure _ c
  exact (ae_map_iff measurable_fst.aemeasurable hP).mpr ((ae_restrict_iff' hA).mpr h)

lemma event_raw_count_lower {N K : ℕ} (F G : fermionGraph N)
    (hGn : ‖fermionGraphValue N G‖^2 = 1) (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    (k : Fin K) (y : Space) {R Q T : ℝ} (hT : 0 ≤ T)
    (hRQ : R+Real.sqrt 3*ell k < Q)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet A) (hcount : ∀ z ∈ A, T ≤ observedLocalCount ell k y R z)
    {c : ℝ≥0∞} (hlaw : graphRawLaw G = c • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A)) :
    T^2 ≤ rawCountMoment (graphFormVector G) y Q := by
  have he := event_rawLaw_ae F G ell hlaw
    (measurableSet_le measurable_const (rawBallCount_measurable y Q)) hA
    (by
      filter_upwards [physicalObservationLaw_ae_displacement (graphRawLaw F) ell hell] with z hz
      intro hzA
      exact (hcount z hzA).trans (observed_count_le_raw_enlarged ell k y hRQ z (hz k)))
  let := graphRawLaw_probability G hGn
  rw [rawCountMoment_eq_integral (graphFormVector_sobolev G).sobolevVector,formRawLaw_graph]
  calc
    T^2 = ∫ _x : Configuration N, T^2 ∂graphRawLaw G := by simp
    _ ≤ ∫ x, rawBallCount y Q x^2 ∂graphRawLaw G :=
      integral_mono_ae (integrable_const _) (rawBallCount_sq_integrable y Q _)
        (he.mono (fun x hx => pow_le_pow_left₀ hT hx 2))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FreshCutBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation

lemma cutOutPositions_measurable {N : ℕ} (c : Fin N → Fin 2) :
    Measurable (cutOutPositions c) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma fresh_cut_support_of_raw_ae {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (c : Fin N → Fin 2) {P : Configuration (cutOutNumber c) → Prop}
    (hP : MeasurableSet {u | P u})
    (hraw : ∀ᵐ x ∂formRawLaw ψ, (spatialProduct p hp c).value x ≠ 0 → P (cutOutPositions c x)) :
    ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm p hp ψ c) s u) ≠ 0 → P u := by
  classical
  let g : Configuration (cutOutNumber c) → ℝ := fun u => if P u then 0 else 1
  have hg : Measurable g := measurable_const.ite hP measurable_const
  have hgn (u) : 0 ≤ g u := by dsimp only [g]; split_ifs <;> norm_num
  have hgb (u) : ‖g u‖ ≤ 1 := by dsimp only [g]; split_ifs <;> norm_num
  have hv := (ae_withDensity_iff' (formRawDensity_integrable hψ).aemeasurable.ennreal_ofReal).mp hraw
  have hzero (s : Spins N) : ∀ᵐ x,
      g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 = 0 := by
    filter_upwards [hv] with x hx
    by_cases hd : ENNReal.ofReal (formRawDensity ψ x) = 0
    · have hs : ‖ψ.value s x‖^2 ≤ formRawDensity ψ x := by
        unfold formRawDensity
        exact Finset.single_le_sum (fun t _ => sq_nonneg ‖ψ.value t x‖) (Finset.mem_univ s)
      have hn : ‖ψ.value s x‖ = 0 := sq_eq_zero_iff.mp
        (le_antisymm (hs.trans (ENNReal.ofReal_eq_zero.mp hd)) (sq_nonneg _))
      simp only [multiplyForm,norm_eq_zero.mp hn,mul_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)]
    · by_cases hm : (spatialProduct p hp c).value x = 0
      · simp only [multiplyForm,hm,Complex.ofReal_zero,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero]
      · simp only [g,ite_eq_left (hx hd hm),zero_mul]
  have hi (s : Spins (cutOutNumber c)) :
      Integrable (fun u => g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) :=
    ((orderedCutForm_sobolev p hp hψ c).coreSlice_mass_integrable s).bdd_mul
      hg.aestronglyMeasurable (ae_of_all _ hgb)
  have hsum : (∑ s : Spins (cutOutNumber c), ∫ u,
      g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = 0 := by
    rw [cutOuter_expectation_eq_full p hp hψ c hg hgb]
    exact Finset.sum_eq_zero (fun s _ => integral_eq_zero_of_ae (hzero s))
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ =>
    integral_nonneg (fun u => mul_nonneg (hgn u) (formMass_nonneg _)))).mp hsum
  intro s
  have he := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all _ (fun u => mul_nonneg (hgn u) (formMass_nonneg _))) (hi s)).mp
      (hterms s (Finset.mem_univ s))
  filter_upwards [he] with u hu
  intro hm
  by_contra hpu
  exact hm (by simpa only [g,ite_eq_right hpu,one_mul,Pi.zero_apply] using hu)

lemma event_fresh_cut_support {N K : ℕ} (F G : fermionGraph N) (ell : Fin K → ℝ)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (c : Fin N → Fin 2) {P : Configuration (cutOutNumber c) → Prop}
    (hP : MeasurableSet {u | P u})
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))} (hA : MeasurableSet A)
    {d : ℝ≥0∞} (hlaw : graphRawLaw G = d • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    (hpath : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A →
      (spatialProduct p hp c).value z.1 ≠ 0 → P (cutOutPositions c z.1)) :
    ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm p hp (graphFormVector G) c) s u) ≠ 0 → P u := by
  have hpred : MeasurableSet {x | (spatialProduct p hp c).value x ≠ 0 → P (cutOutPositions c x)} := by
    have hval : Measurable (spatialProduct p hp c).value :=
      (spatialProduct p hp c).regular.continuous.measurable
    have he : {x | (spatialProduct p hp c).value x ≠ 0 → P (cutOutPositions c x)} =
        {x | (spatialProduct p hp c).value x = 0} ∪ (cutOutPositions c) ⁻¹' {u | P u} := by
      ext x; simp only [mem_ofPred_eq,mem_union,mem_preimage]; tauto
    rw [he]
    exact (measurableSet_eq_fun hval measurable_const).union (hP.preimage (cutOutPositions_measurable c))
  apply fresh_cut_support_of_raw_ae p hp (graphFormVector_sobolev G).sobolevVector c hP
  rw [formRawLaw_graph]
  exact event_rawLaw_ae F G ell hlaw hpred hA hpath

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PosteriorFreshTestBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal ENNReal

namespace CoulombAtom
open CoulombObservation CoulombNeumann CoulombAnalysis
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_5
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_5 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma centered_test_memLp (y : Space) (R : ℝ) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {r : ℝ} (hs : Function.support g ⊆ closedBall y r) :
    MemLp (fun z => g (y+z)) (5/2) (ballMeasure R) := by
  have hc : Continuous (fun z => g (y+z)) := hg.continuous.comp (continuous_const.add continuous_id)
  have hcs : Function.support (fun z => g (y+z)) ⊆ closedBall (0 : Space) r := by
    intro z hz
    have hh := hs hz
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hh
  exact (hc.memLp_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) r) hcs)).mono_measure
      Measure.restrict_le_self

lemma freshRadialTest_measurable {N : ℕ} (y : Space) (t : ℝ) {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) {r : ℝ}
    (hs : Function.support g ⊆ closedBall y r) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
    Measurable (freshRadialTest y t hb g c s) :=
  (patch_test_continuous_of_memLp (t-4*b) (centered_test_memLp y (t-4*b) hg hs)).measurable.comp
    (retainedPatchLp_measurable hb _ id (radialPatchRetention_measurable N y t b c s) measurable_id y (t-4*b))

lemma freshRadialTest_eq_smear {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (g : Space → ℝ) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) :
    freshRadialTest y t hb g c s u =
      ∫ v, g v*retainedSmear b (radialPatchRetention N y t b c s u) u v := by
  exact retainedPatchLp_field hb _ _ y (radialPatch_retained_margin y hb c s u) g

theorem event_fresh_high_test_support {N K : ℕ} (F G : fermionGraph N)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) {j : ℕ} (k : Fin K) (hk : j ≤ k.val)
    (y : Space) {t b r : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))} (hA : MeasurableSet A)
    {d : ℝ≥0∞} (hlaw : graphRawLaw G = d • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    (T Q : ℝ)
    (hdata : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A →
      T+Q*((L:ℝ)*Real.sqrt 3*(b+2*ell k)) < posteriorTestValue (graphRawLaw F) ell j g z ∧
      observedLocalCount ell k y (r+Real.sqrt 3*(b+ell k)) z ≤ Q) :
    ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) (graphFormVector G) c) s u) ≠ 0 →
      T < freshRadialTest y t hb g c s u := by
  intro c s
  have hnoise := hell k
  have hh := fresh_original_observed_sandwich (graphRawLaw F) ell hell k hk y ht hb hr hg hs
  have hp := event_fresh_cut_support F G ell _ _ c
    (P := fun u => T < freshRadialTest y t hb g c s u)
    (measurableSet_lt measurable_const (freshRadialTest_measurable y t hb hg hs c s)) hA hlaw
    (by
      filter_upwards [hh,hdata] with z hz hdatum
      intro hzA hc
      have he := (hz c hc s).trans (mul_le_mul_of_nonneg_right (hdatum hzA).2
        (by positivity : 0 ≤ (L:ℝ)*Real.sqrt 3*(b+2*ell k)))
      rw [←freshRadialTest_eq_smear y hb g c s] at he
      have he' := (abs_le.mp (by simpa only [Real.norm_eq_abs] using he)).1
      linarith [(hdatum hzA).1])
  exact hp s

theorem event_fresh_low_test_support {N K : ℕ} (F G : fermionGraph N)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) {j : ℕ} (k : Fin K) (hk : j ≤ k.val)
    (y : Space) {t b r : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))} (hA : MeasurableSet A)
    {d : ℝ≥0∞} (hlaw : graphRawLaw G = d • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    (T Q : ℝ)
    (hdata : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A →
      posteriorTestValue (graphRawLaw F) ell j g z+Q*((L:ℝ)*Real.sqrt 3*(b+2*ell k)) < T ∧
      observedLocalCount ell k y (r+Real.sqrt 3*(b+ell k)) z ≤ Q) :
    ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) (graphFormVector G) c) s u) ≠ 0 →
      freshRadialTest y t hb g c s u < T := by
  intro c s
  have hnoise := hell k
  have hh := fresh_original_observed_sandwich (graphRawLaw F) ell hell k hk y ht hb hr hg hs
  have hp := event_fresh_cut_support F G ell _ _ c
    (P := fun u => freshRadialTest y t hb g c s u < T)
    (measurableSet_lt (freshRadialTest_measurable y t hb hg hs c s) measurable_const) hA hlaw
    (by
      filter_upwards [hh,hdata] with z hz hdatum
      intro hzA hc
      have he := (hz c hc s).trans (mul_le_mul_of_nonneg_right (hdatum hzA).2
        (by positivity : 0 ≤ (L:ℝ)*Real.sqrt 3*(b+2*ell k)))
      rw [←freshRadialTest_eq_smear y hb g c s] at he
      have he' := (abs_le.mp (by simpa only [Real.norm_eq_abs] using he)).2
      linarith [(hdatum hzA).1])
  exact hp s

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalOrdinaryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

lemma sharpFreshKineticConstant_one_le : 1 ≤ sharpFreshKineticConstant := by
  have := localizationIMSConstant_nonneg
  have := actualCellMomentConstant_one_le
  have := sharpFreshFieldConstant_one_le
  have hh : 0 ≤ localizationIMSConstant*actualCellMomentConstant+
      sharpFreshFieldConstant*actualCellMomentConstant := by positivity
  unfold sharpFreshKineticConstant
  linarith only [hh]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpLocalPotentialBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpLocalPotential_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

lemma sharpOrdinaryDensityConstant_nonneg : 0 ≤ sharpOrdinaryDensityConstant := by
  have hc := le_trans zero_le_one actualCellMomentConstant_one_le
  have hk := le_trans zero_le_one sharpFreshKineticConstant_one_le
  unfold sharpOrdinaryDensityConstant
  positivity

end Work_SharpLocalPotential_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpectedRadialCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

lemma scaled_mass_four_thirds {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) :
    (M/a^3)^(4/3:ℝ) = M^(4/3:ℝ)/a^4 := by
  rw [Real.div_rpow hM (by positivity),←Real.rpow_natCast,←Real.rpow_mul ha.le]
  norm_num

lemma sharpPatchRemainder_rescale {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) :
    a^7*sharpPatchRemainder a (a*β) (M/a^3) = dimensionlessPatchRemainder a β M := by
  have hs : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPatchRemainder dimensionlessPatchRemainder
  rw [hs,scaled_mass_four_thirds ha hM]
  field_simp
  ring

lemma sharpLocalPotentialBudget_rescale {a M u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    a^4*sharpLocalPotentialBudget a (M/a^3) (a*u) = dimensionlessLocalPotential M u := by
  have hC := sharpOrdinaryDensityConstant_nonneg
  have he : sharpOrdinaryDensityConstant*(M/a^3)^2/a =
      sharpOrdinaryDensityConstant*M^2/a^7 := by field_simp
  have hp : (a^7)^(3/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ha.le]; norm_num
  have hprod : a^4*a^(1/5:ℝ) = a^(21/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  unfold sharpLocalPotentialBudget dimensionlessLocalPotential
  rw [he,Real.div_rpow (mul_nonneg hC (sq_nonneg M)) (by positivity),hp,
    Real.mul_rpow ha.le hu]
  have hne : a^(21/5:ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  calc _ = (a^4*a^(1/5:ℝ)/a^(21/5:ℝ))*
        ((sharpOrdinaryDensityConstant*M^2)^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*u^(1/5:ℝ)) := by ring
       _ = _ := by rw [hprod,div_self hne,one_mul]

lemma sharpPotentialRemainder_rescale {a β M E τ : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hM : 0 ≤ M) (hτ : 0 < τ) :
    a^4*sharpPotentialRemainder a (a*β) (M/a^3) (E/a^7) (a*τ) =
      dimensionlessPotentialRemainder a β M E τ := by
  have hR := sharpPatchRemainder_rescale ha hβ hM
  have hroot : a^4*Real.sqrt ((2/(a*τ))*(E/a^7+sharpPatchRemainder a (a*β) (M/a^3))) =
      Real.sqrt ((2/τ)*(E+dimensionlessPatchRemainder a β M)) := by
    rw [←Real.sqrt_sq (by positivity : 0 ≤ a^4),←Real.sqrt_mul (sq_nonneg (a^4))]
    congr 1
    rw [←hR]
    field_simp
  have hpot1 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ τ+Real.sqrt 3*β)
  have hpot2 := sharpLocalPotentialBudget_rescale (M := M) ha
    (by positivity : 0 ≤ Real.sqrt 3*β)
  have he1 : a*τ+Real.sqrt 3*(a*β) = a*(τ+Real.sqrt 3*β) := by ring
  have he2 : Real.sqrt 3*(a*β) = a*(Real.sqrt 3*β) := by ring
  have he3 : 8*(a*β)/a = 8*β := by field_simp
  unfold sharpPotentialRemainder dimensionlessPotentialRemainder
  rw [mul_add,mul_add,mul_add,mul_add]
  rw [hroot,he1,he2,hpot1,hpot2,he3]
  field_simp

lemma localOffsetMass_rescale {D : ℝ} {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) :
    (localCellRadius y)^3*localOffsetMass D y = 1+Real.sqrt (D*(localCellRadius y)^7) := by
  have ha := localCellRadius_pos hy
  have hh : (localCellRadius y)^3 ≤ 1 := pow_le_one₀ ha.le ha1
  have hmax : max (1/(localCellRadius y)^3) 1 = 1/(localCellRadius y)^3 :=
    max_eq_left ((le_div_iff₀ (by positivity : 0 < (localCellRadius y)^3)).mpr (by simpa using hh))
  unfold localOffsetMass
  rw [hmax,mul_add,mul_one_div_cancel (pow_ne_zero _ ha.ne'),←Real.sqrt_sq (by positivity : 0 ≤ (localCellRadius y)^3),
    ←Real.sqrt_mul (sq_nonneg ((localCellRadius y)^3))]
  congr 2
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPosteriorCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_potential_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma normalized_setIntegral_const_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) {f : Ω → ℝ}
    (hi : Integrable f μ) (hp : 0 < (μ A).toReal) (c : ℝ) :
    ((μ A).toReal)⁻¹*(∫ x in A, c-f x ∂μ) =
      c-((μ A).toReal)⁻¹*(∫ x in A, f x ∂μ) := by
  rw [integral_sub (integrable_const c) hi.integrableOn,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_sub,←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

lemma dyadicUniformEventBudget_nonneg {r p₀ δ : ℝ}
    (hr : 0 < r) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (hδ : 0 ≤ δ) :
    0 ≤ dyadicUniformEventBudget r p₀ δ := by
  have hlog : 0 ≤ Real.log (Real.exp 1/p₀) := by
    rw [eventLog_eq hp]
    linarith [Real.log_nonpos hp.le hp1]
  unfold dyadicUniformEventBudget
  exact add_nonneg (mul_nonneg (mul_nonneg observationFisherConstant_pos.le
    (Real.rpow_nonneg hr.le _)) (pow_nonneg hlog _)) hδ

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualTailStateCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

open CoulombAnalysis CoulombNeumann

theorem conditional_high_mean_expected_center_on_support {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) (Z lam : ℝ)
    (S : Configuration M → Finset (Fin M))
    (hi : Integrable (weightedPatchGap ψ t Z lam y R hb S))
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta m : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ R/12) (hsmall : tfPatchOscillationConstant/R*q ≤ 1/2)
    (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hcount : ∀ᵐ u, formMass (coreSlice ψ t u) ≠ 0 → m ≤ ∫ z in ball (0 : Space) q,
      retainedPatchLp hb (S u) u y R z ∂ballMeasure R)
    (hhigh : ∀ᵐ u, formMass (coreSlice ψ t u) ≠ 0 →
      (max (H+(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)+Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
        ∫ x, k x*retainedPatchLp hb (S u) u y R x ∂ballMeasure R) :
    H*(∫ u, formMass (coreSlice ψ t u))-
      (H/eta+2/m)*(∫ u, weightedPatchGap ψ t Z lam y R hb S u)-
      (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*(∫ u, formMass (coreSlice ψ t u)) ≤
      ∫ u, weightedPatchCenter ψ t Z lam y R u := by
  have hOsc := tfPatchOscillationConstant_pos
  have hbound : ∀ᵐ u,
      H*formMass (coreSlice ψ t u)-(H/eta+2/m)*weightedPatchGap ψ t Z lam y R hb S u-
        (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)*formMass (coreSlice ψ t u) ≤
      weightedPatchCenter ψ t Z lam y R u := by
    filter_upwards [hψ.ae_coreSlice t,hcount,hhigh] with u hu hcu hhu
    by_cases hmass : formMass (coreSlice ψ t u) = 0
    · simp only [weightedPatchCenter,weightedPatchGap,hmass,zero_mul,
        mul_zero,sub_zero,le_refl]
    let D := tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)
    have hn := conditionalPatchMinimizer_negative_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
      (retainedPatchLp_nonneg hb (S u) u y R) hq hqR hsmall hm (hcu hmass)
    have hg : D ≤ eta → H ≤ conditionalPatchCenter ψ t Z lam y R u := by
      intro hD
      apply le_of_lt
      apply conditionalPatch_high_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
        (retainedPatchLp_nonneg hb (S u) u y R) hk hkn hq hs hqR (hsmall.trans (by norm_num)) hH
      exact (add_le_add le_rfl (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 16*q^3*(L:ℝ)^2)))).trans_lt (hhu hmass)
    have he := field_lower_from_good_gap
      (tfPatchGap_nonneg R tfKinetic tfKinetic_pos _ (retainedPatchLp_nonneg hb (S u) u y R))
      hH heta (by positivity : 0 ≤ 2/m)
      (by positivity : 0 ≤ 2*(tfPatchOscillationConstant/R*q)*R⁻¹^4) hg
      (by simpa only [conditionalPatchCenter,add_zero] using hn)
    have he' := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ t u))
    dsimp only [weightedPatchCenter,weightedPatchGap,D] at he' ⊢
    nlinarith
  have hmassi := hψ.coreSlice_mass_integrable t
  have hfirst : Integrable (fun u => H*formMass (coreSlice ψ t u)-
      (H/eta+2/m)*weightedPatchGap ψ t Z lam y R hb S u) :=
    (hmassi.const_mul H).sub (hi.const_mul (H/eta+2/m))
  have hleft := hfirst.sub
    (hmassi.const_mul (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4))
  have he := integral_mono_ae hleft
    (weightedPatchCenter_integrable hψ t y hR Z lam hb A hcore hnuc hsep) hbound
  simp only [Pi.sub_apply] at he
  rw [integral_sub hfirst
    (hmassi.const_mul (2*(tfPatchOscillationConstant/R*q)*R⁻¹^4)),
    integral_sub (hmassi.const_mul H) (hi.const_mul (H/eta+2/m)),
    integral_const_mul,integral_const_mul,integral_const_mul] at he
  exact he

theorem conditional_low_mean_expected_center_on_support {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R b : ℝ} (hR : 0 < R) (hb : 0 < b)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) (Z lam : ℝ)
    (S : Configuration M → Finset (Fin M))
    (hi : Integrable (weightedPatchGap ψ t Z lam y R hb S))
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ R/12) (hH : 0 ≤ H) (heta : 0 < eta)
    (hlow : ∀ᵐ u, formMass (coreSlice ψ t u) ≠ 0 → (∫ x, k x*retainedPatchLp hb (S u) u y R x ∂ballMeasure R)+
        Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
      (max (H-(tfPatchOscillationConstant/R*q)*R⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure R)) :
    (∫ u, weightedPatchCenter ψ t Z lam y R u) ≤
      H*(∫ u, formMass (coreSlice ψ t u))+
        ((tfPatchCapConstant/R^4)/eta)*(∫ u, weightedPatchGap ψ t Z lam y R hb S u) := by
  have hCap := tfPatchCapConstant_pos
  have hbound : ∀ᵐ u,
      weightedPatchCenter ψ t Z lam y R u ≤
      H*formMass (coreSlice ψ t u)+((tfPatchCapConstant/R^4)/eta)*weightedPatchGap ψ t Z lam y R hb S u := by
    filter_upwards [hψ.ae_coreSlice t,hlow] with u hu hlu
    by_cases hmass : formMass (coreSlice ψ t u) = 0
    · simp only [weightedPatchCenter,weightedPatchGap,hmass,zero_mul,
        mul_zero,add_zero,le_refl]
    let D := tfPatchGap R tfKinetic tfKinetic_pos
      (conditionalPatchField ψ t Z lam y R u) (retainedPatchLp hb (S u) u y R)
    have hc := conditionalPatchMinimizer_nonradial_cap ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam 0
      (by simpa only [norm_zero] using (by positivity : 0 ≤ 3*R/4))
    have hg : D ≤ eta → conditionalPatchCenter ψ t Z lam y R u ≤ H := by
      intro hD
      apply le_of_lt
      apply conditionalPatch_low_center ψ t u hu A (hcore u) y hR hb hb hnuc hsep Z lam
        (retainedPatchLp_nonneg hb (S u) u y R) hk hkn hq hs hqR hH
      exact (add_le_add le_rfl (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 16*q^3*(L:ℝ)^2)))).trans_lt (hlu hmass)
    have he := field_upper_from_good_gap
      (tfPatchGap_nonneg R tfKinetic tfKinetic_pos _ (retainedPatchLp_nonneg hb (S u) u y R))
      hH heta (by positivity : 0 ≤ tfPatchCapConstant/R^4) hg
      (by simpa only [conditionalPatchCenter,add_zero] using hc)
    have he' := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ t u))
    dsimp only [weightedPatchCenter,weightedPatchGap,D] at he' ⊢
    nlinarith
  have hmassi := hψ.coreSlice_mass_integrable t
  have hright := (hmassi.const_mul H).add (hi.const_mul ((tfPatchCapConstant/R^4)/eta))
  have he := integral_mono_ae
    (weightedPatchCenter_integrable hψ t y hR Z lam hb A hcore hnuc hsep) hright hbound
  simp only [Pi.add_apply] at he
  rw [integral_add (hmassi.const_mul H) (hi.const_mul ((tfPatchCapConstant/R^4)/eta)),
    integral_const_mul,integral_const_mul] at he
  exact he

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialMeanCenterBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RadialMeanCenter_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators NNReal

open CoulombAnalysis CoulombNeumann

lemma radial_coreSlice_zero {N : ℕ} (ψ : FormVector N) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c))
    (i : Fin (cutCoreNumber c)) (hi : v i ∉ radialPatchCore y t) :
    FormZeroAt (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) v := by
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

 theorem radial_high_mean_expected_center {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta m : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ (t-4*b)/12) (hsmall : tfPatchOscillationConstant/(t-4*b)*q ≤ 1/2)
    (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hcount : ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0 →
      m ≤ ∫ z in ball (0 : Space) q,
        retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) z ∂ballMeasure (t-4*b))
    (hhigh : ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0 →
      (max (H+(tfPatchOscillationConstant/(t-4*b)*q)*(t-4*b)⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure (t-4*b))+Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
        ∫ x, k x*retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) x
          ∂ballMeasure (t-4*b)) :
    H*formMass ψ-(H/eta+2/m)*radialPatchGapMean ψ y ht hb Z lam-
      (2*(tfPatchOscillationConstant/(t-4*b)*q)*(t-4*b)⁻¹^4)*formMass ψ ≤
      expectedRadialPatchCenter ψ y ht hb Z lam := by
  have hR : 0 < t-4*b := by linarith
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  have hχ (c : Fin N → Fin 2) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hbound (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    conditional_high_mean_expected_center_on_support (hχ c) s (radialPatchCore y t)
      (radial_coreSlice_zero ψ y ht hb c s) y hR hb
      (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) Z lam
      (radialPatchRetention N y t b c s)
      (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam canonicalRealPacket_smooth
        canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial
        canonicalRealPacket_support c s)
      hk hkn hq hs hqR hsmall hH heta hm (hcount c s) (hhigh c s)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbound c s))
  simp_rw [Finset.sum_sub_distrib,←Finset.mul_sum] at hh
  simp_rw [(hχ _).integral_coreSlice_mass] at hh
  rw [orderedCutForm_mass_sum p hp hψ.sobolevVector] at hh
  exact hh

 theorem radial_low_mean_expected_center {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) (hkn : ∀ x, 0 ≤ k x)
    {q H eta : ℝ} (hq : 0 < q) (hs : Function.support k ⊆ closedBall 0 q)
    (hqR : q ≤ (t-4*b)/12) (hH : 0 ≤ H) (heta : 0 < eta)
    (hlow : ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0 →
      (∫ x, k x*retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) x
          ∂ballMeasure (t-4*b))+Real.sqrt ((16*q^3*(L:ℝ)^2)*eta) <
      (max (H-(tfPatchOscillationConstant/(t-4*b)*q)*(t-4*b)⁻¹^4) 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)*
        (∫ x, k x ∂ballMeasure (t-4*b))) :
    expectedRadialPatchCenter ψ y ht hb Z lam ≤
      H*formMass ψ+((tfPatchCapConstant/(t-4*b)^4)/eta)*radialPatchGapMean ψ y ht hb Z lam := by
  have hR : 0 < t-4*b := by linarith
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  have hχ (c : Fin N → Fin 2) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hbound (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    conditional_low_mean_expected_center_on_support (hχ c) s (radialPatchCore y t)
      (radial_coreSlice_zero ψ y ht hb c s) y hR hb
      (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) Z lam
      (radialPatchRetention N y t b c s)
      (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam canonicalRealPacket_smooth
        canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial
        canonicalRealPacket_support c s)
      hk hkn hq hs hqR hH heta (hlow c s)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbound c s))
  simp_rw [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  simp_rw [(hχ _).integral_coreSlice_mass] at hh
  rw [orderedCutForm_mass_sum p hp hψ.sobolevVector] at hh
  exact hh

end Work_RadialMeanCenter_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ActualLowInverseBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

lemma jointMasterPosterior_value_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s) :
    Measurable (fun z : OriginalDatum N K ell j =>
      jointMasterPosterior μ ell j c₁ r₀ s canonicalRealPacket z y) :=
  (jointMasterPosterior_measurable μ ell j hc hr hs canonicalRealPacket_smooth.continuous).comp
    (measurable_id.prodMk measurable_const)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FreshRetainedMassBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshRetainedMass_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators NNReal ENNReal

open CoulombAnalysis CoulombNeumann

lemma compact_test_le_mass {R : ℝ} (σ : TFLp (ballMeasure R)) (hσ : NonnegDensity σ)
    {k : Space → ℝ} {L : ℝ≥0} (hk : LipschitzWith L k) {r q B : ℝ}
    (hs : Function.support k ⊆ closedBall 0 r) (hrq : r < q) (hb : ∀ z, k z ≤ B) :
    (∫ z, k z*σ z ∂ballMeasure R) ≤ B*(∫ z in ball (0 : Space) q, σ z ∂ballMeasure R) := by
  have hi : Integrable σ (ballMeasure R) := (Lp.memLp σ).integrable (Fact.out : (1 : ℝ≥0∞) ≤ 5/3)
  have hki : MemLp k (5/2) (ballMeasure R) := by
    simpa only [zero_add] using centered_test_memLp 0 R hk hs
  calc
    _ ≤ ∫ z, (ball (0 : Space) q).indicator (fun z => B*σ z) z ∂ballMeasure R := by
      apply integral_mono_ae (hki.integrable_mul (Lp.memLp σ))
        ((hi.const_mul B).indicator measurableSet_ball)
      filter_upwards [hσ] with z hz
      by_cases hzin : z ∈ ball (0 : Space) q
      · rw [indicator_of_mem hzin]
        exact mul_le_mul_of_nonneg_right (hb z) hz
      · rw [indicator_of_notMem hzin]
        have hzk : z ∉ Function.support k := by
          intro hzsup
          exact hzin (lt_of_le_of_lt (hs hzsup) hrq)
        change k z*σ z ≤ 0
        rw [Function.notMem_support.mp hzk,zero_mul]
    _ = _ := by rw [integral_indicator measurableSet_ball,integral_const_mul]

lemma canonicalMasterAmplitude_pos : 0 < canonicalMasterAmplitude :=
  (Classical.choose_spec masterCenteredKernel_amplitude).1

lemma canonicalMasterAmplitude_bound {c₁ r₀ s : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y x : Space) :
    masterCenteredKernel c₁ r₀ s canonicalRealPacket y x ≤
      canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3 :=
  (Classical.choose_spec masterCenteredKernel_amplitude).2 hc hcL hr hs hs1 y x

end Work_FreshRetainedMass_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal

open CoulombAnalysis CoulombObservation CoulombNeumann
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

lemma threshold_event_mean_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hi : Integrable f μ) {A : Set Ω} (hA : MeasurableSet A)
    {θ : ℝ} (hθ : ∀ z ∈ A, f z ≤ θ) (hp : 0 < (μ A).toReal) :
    (μ A).toReal⁻¹*(∫ z in A, f z ∂μ) ≤ θ := by
  have hh := threshold_event_mean_ge μ hi.neg hA (t := -θ) (fun z hz => by dsimp; linarith [hθ z hz]) hp
  change -θ ≤ (μ A).toReal⁻¹*(∫ z in A, -(f z) ∂μ) at hh
  rw [integral_neg] at hh
  linarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_SharpEventLawJointComparisonCell
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

theorem TailTiltState.low_inverse_event_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
    (hqk : 2*masterWidth c₁ r₀ s y ≤ (5*localCellRadius y-4*b)/12)
    {H eta T Q θ : ℝ} (hH : 0 ≤ H) (heta : 0 < eta)
    (hdensity : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      T+Q*((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ r₀ s y)⁻¹^4*Real.sqrt 3*(b+2*dyadicObservationWidth r k)) <
      freshLowThreshold y (t-4*b) H eta c₁ r₀ s)
    (hsmall : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      H+((tfPatchCapConstant/(t-4*b)^4)/eta)*
        (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
          sharpPatchRemainder (localCellRadius y) b
            (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y))+
        (sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) < θ) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | θ ≤ Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y ∧
        jointMasterPosterior (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c₁ r₀ s canonicalRealPacket (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) y ≤ T ∧
        observedLocalCount (fun k : Fin K => dyadicObservationWidth r k) k y
          (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+dyadicObservationWidth r k)) z ≤ Q}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let pot := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let dens := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y
  let A := {z | θ ≤ Z/‖y‖-lam-pot z ∧ dens z ≤ T ∧
    observedLocalCount ell k y (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+ell k)) z ≤ Q}
  have hA : MeasurableSet[observationInformation ell j] A :=
    (measurableSet_le measurable_const (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous))).inter
      ((measurableSet_le (jointMasterPosterior_value_measurable (graphRawLaw F) ell j y hc hr₀ hs) measurable_const).inter
        (measurableSet_le (observedLocalCount_information_measurable ell k hk y _) measurable_const))
  change ((physicalObservationLaw (graphRawLaw F) K) A).toReal < p₀ j
  by_contra! hn
  have hp := (h₀ j).trans_le hn
  obtain ⟨G,t,ht,ht0,hGn,hlaw,hgap,hpot⟩ := hstate.event_radial_comparison_of_cell hZ hlam h₀
    hc hcL hr₀ hs hs1 j hy ha1 hcell hb hba hq hqr hqR hcollar hA hn
  have hψ := graphFormVector_admissible G hGn
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have ha := localCellRadius_pos hy
  have hnuc : t ≤ ‖y‖ := by
    have hh := ht.2
    unfold localCellRadius at hh
    nlinarith [norm_nonneg y]
  have htb : 7*b < t := by linarith [ht.1]
  have hkr : 2*masterWidth c₁ r₀ s y < t-7*b := by linarith [ht.1]
  have hlow := event_fresh_low_test_support F G ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k hk y ht0 hb hkr
    (masterKernel_test_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (masterKernel_test_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    ((observationInformation_le ell j) A hA) hlaw (freshLowThreshold y (t-4*b) H eta c₁ r₀ s) Q
    (by
      filter_upwards [jointMasterPosterior_eq_scalar (graphRawLaw F) ell j hc hcL hr₀ hs hs1
        canonicalRealPacket_smooth canonicalRealPacket_support y] with z hz
      intro hzA
      refine ⟨?_,hzA.2.2⟩
      have hden := hzA.2.1
      dsimp only [dens] at hden
      rw [←hz] at hden
      exact (add_le_add hden le_rfl).trans_lt (hdensity t ht))
  have hcmean := radial_low_mean_expected_center hψ.sobolevFermion y ht0 hb htb hnuc hZ hlam
    (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (fun x => masterKernel_nonneg c₁ r₀ s canonicalRealPacket (y+x) y)
    (by linarith [masterWidth_pos hc hr₀ hs y])
    (masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (by linarith [ht.1] : 2*masterWidth c₁ r₀ s y ≤ (t-4*b)/12) hH heta
    (by
      intro c spin
      filter_upwards [hlow c spin] with u hu
      intro hmu
      have hh := hu hmu
      dsimp only [freshRadialTest,freshLowThreshold] at hh
      exact lt_sub_iff_add_lt.mp hh)
  rw [hm,mul_one] at hcmean
  have hcap : 0 ≤ (tfPatchCapConstant/(t-4*b)^4)/eta := by
    exact div_nonneg (div_nonneg tfPatchCapConstant_pos.le (pow_nonneg (by linarith : 0 ≤ t-4*b) _)) heta.le
  have hcenter := hcmean.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgap hcap))
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi := jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
    canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.1) hp
  simp only [Pi.sub_apply] at hlower
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hlower
  have hpupper := (abs_le.mp hpot).2
  have hstrict := hsmall t ht
  linarith

end

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff NNReal
open CoulombAnalysis CoulombObservation CoulombNeumann
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

theorem TailTiltState.high_inverse_event_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
    (hqk : 3*masterWidth c₁ r₀ s y ≤ (5*localCellRadius y-4*b)/12)
    {H eta m T Q θ : ℝ} (hH : 0 ≤ H) (heta : 0 < eta) (hm : 0 < m)
    (hosc : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y) ≤ 1/2)
    (hdensity : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
        (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)+
      Q*((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ r₀ s y)⁻¹^4*Real.sqrt 3*(b+2*dyadicObservationWidth r k)) < T)
    (hsmall : ∀ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y),
      θ+(sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) <
      H-(H/eta+2/m)*(dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
          sharpPatchRemainder (localCellRadius y) b
            (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y))-
        2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y ≤ θ ∧
        T ≤ jointMasterPosterior (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c₁ r₀ s canonicalRealPacket (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z) y ∧
        observedLocalCount (fun k : Fin K => dyadicObservationWidth r k) k y
          (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+dyadicObservationWidth r k)) z ≤ Q}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let pot := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let dens := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket (originalDatum ell j z) y
  let A := {z | Z/‖y‖-lam-pot z ≤ θ ∧ T ≤ dens z ∧
    observedLocalCount ell k y (2*masterWidth c₁ r₀ s y+Real.sqrt 3*(b+ell k)) z ≤ Q}
  have hA : MeasurableSet[observationInformation ell j] A :=
    (measurableSet_le (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous)) measurable_const).inter
      ((measurableSet_le measurable_const (jointMasterPosterior_value_measurable (graphRawLaw F) ell j y hc hr₀ hs)).inter
        (measurableSet_le (observedLocalCount_information_measurable ell k hk y _) measurable_const))
  change ((physicalObservationLaw (graphRawLaw F) K) A).toReal < p₀ j
  by_contra! hn
  have hp := (h₀ j).trans_le hn
  obtain ⟨G,t,ht,ht0,hGn,hlaw,hgap,hpot⟩ := hstate.event_radial_comparison_of_cell hZ hlam h₀
    hc hcL hr₀ hs hs1 j hy ha1 hcell hb hba hq hqr hqR hcollar hA hn
  have hψ := graphFormVector_admissible G hGn
  have hmass : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have ha := localCellRadius_pos hy
  have hw := masterWidth_pos hc hr₀ hs y
  have hnuc : t ≤ ‖y‖ := by
    have hh := ht.2
    unfold localCellRadius at hh
    nlinarith [norm_nonneg y]
  have htb : 7*b < t := by linarith [ht.1]
  have hkr : 2*masterWidth c₁ r₀ s y < t-7*b := by linarith [ht.1]
  have hhigh := event_fresh_high_test_support F G ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k hk y ht0 hb hkr
    (masterKernel_test_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (masterKernel_test_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    ((observationInformation_le ell j) A hA) hlaw
    (max (freshHighThreshold y (t-4*b) H eta c₁ r₀ s)
      (canonicalMasterAmplitude*(masterWidth c₁ r₀ s y)⁻¹^3*m)) Q
    (by
      filter_upwards [jointMasterPosterior_eq_scalar (graphRawLaw F) ell j hc hcL hr₀ hs hs1
        canonicalRealPacket_smooth canonicalRealPacket_support y] with z hz
      intro hzA
      refine ⟨?_,hzA.2.2⟩
      have hden := hzA.2.1
      dsimp only [dens] at hden
      rw [←hz] at hden
      exact (hdensity t ht).trans_le hden)
  have hcount : ∀ c : Fin N → Fin 2, ∀ spin : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht0 hb)
        (coreFirstRadialCut_partition y ht0 hb) (graphFormVector G) c) spin u) ≠ 0 →
      m ≤ ∫ z in ball (0 : Space) (3*masterWidth c₁ r₀ s y),
        retainedPatchLp hb (radialPatchRetention N y t b c spin u) u y (t-4*b) z ∂ballMeasure (t-4*b) := by
    intro c spin
    filter_upwards [hhigh c spin] with u hu
    intro hmu
    have htest := compact_test_le_mass
      (retainedPatchLp hb (radialPatchRetention N y t b c spin u) u y (t-4*b))
      (retainedPatchLp_nonneg hb _ _ _ _)
      (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
      (masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
      (by linarith : 2*masterWidth c₁ r₀ s y < 3*masterWidth c₁ r₀ s y)
      (canonicalMasterAmplitude_bound hc hcL hr₀ hs hs1 y)
    have hh := ((le_max_right _ _).trans_lt (hu hmu)).le.trans htest
    exact (mul_le_mul_iff_of_pos_left (mul_pos canonicalMasterAmplitude_pos (pow_pos (inv_pos.mpr hw) 3))).mp hh
  have hcmean := radial_high_mean_expected_center hψ.sobolevFermion y ht0 hb htb hnuc hZ hlam
    (masterCenteredKernel_lipschitz canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y)
    (fun x => masterKernel_nonneg c₁ r₀ s canonicalRealPacket (y+x) y)
    (by linarith : 0 < 3*masterWidth c₁ r₀ s y)
    ((masterCenteredKernel_support canonicalRealPacket_smooth canonicalRealPacket_support hc hcL hr₀ hs hs1 y).trans
      (closedBall_subset_closedBall (by linarith)))
    (by linarith [ht.1] : 3*masterWidth c₁ r₀ s y ≤ (t-4*b)/12) (hosc t ht) hH heta hm hcount
    (by
      intro c spin
      filter_upwards [hhigh c spin] with u hu
      intro hmu
      exact (le_max_left _ _).trans_lt (hu hmu))
  rw [hmass,mul_one,mul_one] at hcmean
  have hcoef : 0 ≤ H/eta+2/m := by positivity
  have hcenter := (sub_le_sub_right (sub_le_sub_left (mul_le_mul_of_nonneg_left hgap hcoef) H)
    (2*(tfPatchOscillationConstant/(t-4*b)*(3*masterWidth c₁ r₀ s y))*(t-4*b)⁻¹^4)).trans hcmean
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi := jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
    canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  have hupper := threshold_event_mean_le (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.1) hp
  simp only [Pi.sub_apply] at hupper
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hupper
  have hplower := (abs_le.mp hpot).1
  have hstrict := hsmall t ht
  linarith

end

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

end CoulombAtom
end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_WidthKernelAmplitude
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WidthKernelAmplitude_scope

open Set Metric
open scoped NNReal

lemma scaledDensity_active_width_error {q a b : ℝ} (hq : 0 < q)
    (ha : q ≤ a) (hb : q ≤ b) {h : Space → ℝ} {H : ℝ≥0}
    (hh : LipschitzWith H h) {M : ℝ} (_hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (z : Space) (hz : h (a⁻¹ • z) ≠ 0) :
    ‖a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z)‖ ≤
      (3*M+(H:ℝ))*q⁻¹^4*‖a-b‖ := by
  have hap := hq.trans_le ha
  have hbp := hq.trans_le hb
  have hn : ‖a⁻¹ • z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hs hz
  have he : a⁻¹ • z-b⁻¹ • z = (b⁻¹*(b-a)) • (a⁻¹ • z) := by
    rw [smul_smul,←sub_smul]
    congr 1
    field_simp
  have hd : ‖a⁻¹ • z-b⁻¹ • z‖ ≤ q⁻¹*‖a-b‖ := by
    rw [he,norm_smul,norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hbp.le),norm_sub_rev b a]
    calc
      _ ≤ (b⁻¹*‖a-b‖)*1 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_right (inv_anti₀ hq hb) (norm_nonneg (a-b))
  have hdiff := hh.dist_le_mul (a⁻¹ • z) (b⁻¹ • z)
  simp only [dist_eq_norm] at hdiff
  have hdiff' := hdiff.trans (mul_le_mul_of_nonneg_left hd H.coe_nonneg)
  have hi : ‖b⁻¹^3‖ ≤ q⁻¹^3 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hbp.le) _)]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hbp.le) (inv_anti₀ hq hb) 3
  have hid := invCube_norm_sub_le hq ha hb
  have halg : a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z) =
      (a⁻¹^3-b⁻¹^3)*h (a⁻¹ • z)+b⁻¹^3*(h (a⁻¹ • z)-h (b⁻¹ • z)) := by ring
  rw [halg]
  calc
    _ ≤ ‖(a⁻¹^3-b⁻¹^3)*h (a⁻¹ • z)‖+‖b⁻¹^3*(h (a⁻¹ • z)-h (b⁻¹ • z))‖ := norm_add_le _ _
    _ = ‖a⁻¹^3-b⁻¹^3‖*‖h (a⁻¹ • z)‖+‖b⁻¹^3‖*‖h (a⁻¹ • z)-h (b⁻¹ • z)‖ := by rw [norm_mul,norm_mul]
    _ ≤ (3*q⁻¹^4*‖a-b‖)*M+(q⁻¹^3)*((H:ℝ)*(q⁻¹*‖a-b‖)) :=
      add_le_add (mul_le_mul hid (hbound _) (norm_nonneg _) (by positivity))
        (mul_le_mul hi hdiff' (norm_nonneg _) (by positivity))
    _ = _ := by ring

lemma scaledDensity_width_error {q a b : ℝ} (hq : 0 < q)
    (ha : q ≤ a) (hb : q ≤ b) {h : Space → ℝ} {H : ℝ≥0}
    (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (z : Space) :
    ‖a⁻¹^3*h (a⁻¹ • z)-b⁻¹^3*h (b⁻¹ • z)‖ ≤
      (3*M+(H:ℝ))*q⁻¹^4*‖a-b‖ := by
  by_cases hz : h (a⁻¹ • z) ≠ 0
  · exact scaledDensity_active_width_error hq ha hb hh hM hbound hs z hz
  by_cases hz' : h (b⁻¹ • z) ≠ 0
  · simpa only [norm_sub_rev b a,norm_sub_rev (b⁻¹^3*h (b⁻¹ • z)) _] using
      scaledDensity_active_width_error hq hb ha hh hM hbound hs z hz'
  simp only [not_ne_iff] at hz hz'
  simp only [hz,hz',mul_zero,sub_zero,norm_zero]
  positivity

theorem widthKernel_freeze_error {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1)
    (y x : Space) :
    ‖widthKernel t h x y-widthKernel (fun _ => t y) h x y‖ ≤
      32*(3*M+(H:ℝ))*(T:ℝ)*(t y)⁻¹^3 := by
  have hty := hp y
  by_cases hd : ‖x-y‖ ≤ 2*t y
  · have hcl := congrFun (widthKernel_clamp ht hp (by linarith) hs y) x
    rw [hcl]
    have hq : 0 < t y/2 := half_pos (hp y)
    have hby : t y/2 ≤ t y := by linarith [hp y]
    have hh' := scaledDensity_width_error hq (le_max_right (t x) (t y/2)) hby hh hM hbound hs (y-x)
    have htd := (ht.max_const (t y/2)).dist_le_mul x y
    simp only [max_eq_left hby,dist_eq_norm] at htd
    have hd' := htd.trans (mul_le_mul_of_nonneg_left hd T.coe_nonneg)
    have hcoeff : 0 ≤ (3*M+(H:ℝ))*(t y/2)⁻¹^4 := by positivity
    apply hh'.trans
    calc
      _ ≤ ((3*M+(H:ℝ))*(t y/2)⁻¹^4)*((T:ℝ)*(2*t y)) := mul_le_mul_of_nonneg_left hd' hcoeff
      _ = _ := by field_simp [(hp y).ne']; ring
  · have hv : widthKernel t h x y = 0 := by
      by_contra hn
      exact hd (by simpa only [mem_closedBall,dist_eq_norm] using widthKernel_support_local ht hp hT hs y hn)
    have hf : widthKernel (fun _ => t y) h x y = 0 :=
      widthKernel_eq_zero_of_far (fun _ => hp y) hs (by linarith [lt_of_not_ge hd,hp y])
    rw [hv,hf,sub_self,norm_zero]
    positivity

end Work_WidthKernelAmplitude_scope

open MeasureTheory Set Metric
open scoped NNReal ContDiff

open CoulombAnalysis

lemma widthKernel_frozen_mass {b : ℝ} (hb : 0 < b) (h : Space → ℝ) (y : Space) :
    (∫ x, widthKernel (fun _ => b) h x y) = ∫ x, h x := by
  unfold widthKernel
  rw [integral_sub_left_eq_self (fun z => b⁻¹^3*h (b⁻¹ • z)) volume y,
    integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume h hb.le,
    space_finrank,smul_eq_mul,←mul_assoc,←mul_pow,inv_mul_cancel₀ hb.ne',one_pow,one_mul]

lemma widthKernel_integrable {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    Integrable (fun x => widthKernel t h x y) := by
  apply (widthKernel_local_lipschitz ht hp hT hh hM hbound hs y).continuous.integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y (2*t y))
    (widthKernel_support_local ht hp hT hs y)

theorem widthKernel_mass_error {t : Space → ℝ} {T : ℝ≥0}
    (ht : LipschitzWith T t) (hp : ∀ x, 0 < t x) (hT : (T:ℝ) ≤ 1/2)
    {h : Space → ℝ} {H : ℝ≥0} (hh : LipschitzWith H h) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u, ‖h u‖ ≤ M) (hs : Function.support h ⊆ closedBall 0 1) (y : Space) :
    ‖(∫ x, widthKernel t h x y)-(∫ x, h x)‖ ≤
      ((1024/3:ℝ)*Real.pi*(3*M+(H:ℝ)))*(T:ℝ) := by
  have hty := hp y
  have hk := widthKernel_integrable ht hp hT hh hM hbound hs y
  have hconst : LipschitzWith 0 (fun _ : Space => t y) := LipschitzWith.const _
  have hk0 := widthKernel_integrable hconst (fun _ => hp y) (by norm_num) hh hM hbound hs y
  rw [←widthKernel_frozen_mass hty h y,←integral_sub hk hk0]
  have hs0 := widthKernel_support_local hconst (fun _ => hp y) (by norm_num) hs y
  have hs1 := widthKernel_support_local ht hp hT hs y
  have he : (∫ x in closedBall y (2*t y), widthKernel t h x y-widthKernel (fun _ => t y) h x y) =
      ∫ x, widthKernel t h x y-widthKernel (fun _ => t y) h x y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h1 : widthKernel t h x y = 0 := by
      by_contra hn; exact hx (hs1 hn)
    have h0 : widthKernel (fun _ => t y) h x y = 0 := by
      by_contra hn; exact hx (hs0 hn)
    rw [h1,h0,sub_self]
  rw [←he]
  have hh' := norm_setIntegral_le_of_norm_le_const
    ((isCompact_closedBall y (2*t y)).measure_lt_top (μ := volume))
    (fun x (_ : x ∈ closedBall y (2*t y)) => widthKernel_freeze_error ht hp hT hh hM hbound hs y x)
  apply hh'.trans_eq
  rw [Measure.addHaar_real_closedBall_center volume,tfSpace_closedBall_real (2*t y) (by positivity)]
  field_simp [hty.ne']
  ring

theorem masterKernel_approximate_mass {g : Space → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ x : Space, (g x)^2 = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c₁ r₀ s : ℝ),
      0 < c₁ → c₁ < (10*(100000:ℝ))⁻¹ → 0 < r₀ → 0 < s → s ≤ 1 →
      ∀ y : Space, ‖(∫ x, masterKernel c₁ r₀ s g x y)-1‖ ≤ C*c₁*s^masterExponent := by
  have hp := masterProfile_support hgs
  have hcomp : HasCompactSupport (fun z => (g z)^2) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) 1) hp
  obtain ⟨H,hH⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcomp (hg.pow 2) (by simp)
  obtain ⟨z₀,hz₀⟩ := (hg.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport hcomp.norm
  let M := ‖(g z₀)^2‖
  have hM : 0 ≤ M := norm_nonneg _
  let A := (1024/3:ℝ)*Real.pi*(3*M+(H:ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw := masterExponent_pos
  refine ⟨A*(1+masterExponent)+1,by positivity,?_⟩
  intro c₁ r₀ s hc hcL hr hs hs1 y
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have hT : c₁*(1+masterExponent)*s^masterExponent ≤ (1/2:ℝ) := by
    have hsp := Real.rpow_le_one hs.le hs1 masterExponent_nonneg
    have hcp : 0 ≤ c₁*(1+masterExponent) := by positivity
    calc
      _ ≤ c₁*(1+masterExponent)*1 := mul_le_mul_of_nonneg_left hsp hcp
      _ ≤ _ := by norm_num [masterExponent] at *; nlinarith
  have hh := widthKernel_mass_error (masterWidth_lipschitz hc.le hr hs)
    (masterWidth_pos hc hr hs) hT hH hM hz₀ hp y
  change _ ≤ A*(c₁*(1+masterExponent)*s^masterExponent) at hh
  rw [hgn] at hh
  apply hh.trans
  have hn : 0 ≤ c₁*s^masterExponent := by positivity
  nlinarith only [hn]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseKernelMassBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseKernelMass_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma masterCenteredKernel_ball_mass {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ r₀ s R : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (y : Space)
    (hR : 2*masterWidth c₁ r₀ s y < R) :
    (∫ x, masterCenteredKernel c₁ r₀ s g y x ∂ballMeasure R) =
      ∫ x, masterKernel c₁ r₀ s g x y := by
  have hsup := masterCenteredKernel_support hg hgs hc hcL hr hs hs1 y
  change (∫ x in ball 0 R, masterCenteredKernel c₁ r₀ s g y x) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)]
  · exact integral_add_left_eq_self (fun x => masterKernel c₁ r₀ s g x y) y
  · by_contra hne
    have hh := hsup hne
    exact hx (mem_ball.mpr ((mem_closedBall.mp hh).trans_lt hR))

theorem masterCenteredKernel_mass_tendsto {ι : Type*} {l : Filter ι}
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hgs : tsupport g ⊆ ball 0 1)
    (hgn : ∫ x : Space, (g x)^2 = 1) {c₁ : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    {r₀ s R : ι → ℝ} {y : ι → Space}
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, 2*masterWidth c₁ (r₀ i) (s i) (y i) < R i) :
    Tendsto (fun i => ∫ x, masterCenteredKernel c₁ (r₀ i) (s i) g (y i) x
      ∂ballMeasure (R i)) l (𝓝 1) := by
  obtain ⟨C,hC,hbound⟩ := masterKernel_approximate_mass hg hgs hgn
  have hzero : Tendsto (fun i => C*c₁*(s i)^masterExponent) l (𝓝 0) := by
    simpa only [mul_zero] using (hs0.rpow_const_nhds_zero masterExponent_pos).const_mul (C*c₁)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hzero
  filter_upwards [hr,hs,hR,hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hri hsi hRi hs1
  rw [masterCenteredKernel_ball_mass hg hgs hc hcL hri hsi hs1.le _ hRi]
  exact hbound c₁ (r₀ i) (s i) hc hcL hri hsi hs1.le (y i)

end Work_InverseKernelMass_barrier_scope

open Filter
open scoped Topology

open CoulombAnalysis

lemma rpow_inv_pow_bound {a t c e w : ℝ} (ha : 0 < a) (hc : 0 < c)
    (ht : c*a^w ≤ t) (n : ℕ) :
    a^e*t⁻¹^n ≤ c⁻¹^n*a^(e-w*n) := by
  have hct : 0 < c*a^w := mul_pos hc (Real.rpow_pos_of_pos ha _)
  have hi := pow_le_pow_left₀ (inv_nonneg.mpr ((hct.trans_le ht).le))
    (inv_anti₀ hct ht) n
  have he : (c*a^w)⁻¹^n = c⁻¹^n*a^(-w*n) := by
    rw [mul_inv,mul_pow,←Real.rpow_neg ha.le,←Real.rpow_natCast (a^(-w)),←Real.rpow_mul ha.le]
  calc
    _ ≤ a^e*(c*a^w)⁻¹^n := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg ha.le _)
    _ = c⁻¹^n*(a^e*a^(-w*n)) := by rw [he]; ring
    _ = _ := by rw [←Real.rpow_add ha]; congr 2; ring

lemma inverse_duality_rescale {a t : ℝ} (ha : 0 < a) (ht : 0 < t)
    (n L : ℝ) :
    (a^6)^2*((16*(n*t)^3*(L*t⁻¹^4)^2)*a^(-7+(1/100:ℝ))) =
      (16*n^3*L^2)*(a^(5+(1/100:ℝ))*t⁻¹^5) := by
  have he : a^12*a^(-7+(1/100:ℝ)) = a^(5+(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  have he' : t^3*(t⁻¹^4)^2 = t⁻¹^5 := by
    field_simp
  calc
    _ = (16*n^3*L^2)*((a^12*a^(-7+(1/100:ℝ)))*(t^3*(t⁻¹^4)^2)) := by ring
    _ = _ := by rw [he,he']

lemma inverse_retained_rescale {a t A : ℝ} (ha : 0 < a) :
    a^6*(A*t⁻¹^3*a^(-3+(1/100:ℝ))) =
      A*(a^(3+(1/100:ℝ))*t⁻¹^3) := by
  have he : a^6*a^(-3+(1/100:ℝ)) = a^(3+(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  calc
    _ = A*((a^6*a^(-3+(1/100:ℝ)))*t⁻¹^3) := by ring
    _ = _ := by rw [he]

theorem inverse_duality_tendsto {ι : Type*} {l : Filter ι}
    {a t : ι → ℝ} {c n L : ℝ} (hc : 0 < c) (hn : 0 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i) :
    Tendsto (fun i => (a i)^6*Real.sqrt ((16*(n*t i)^3*(L*(t i)⁻¹^4)^2)*
      (a i)^(-7+(1/100:ℝ)))) l (𝓝 0) := by
  have he : 0 < (5+(1/100:ℝ))-(1+masterExponent)*5 := by norm_num [masterExponent]
  have hpow := ha0.rpow_const_nhds_zero he
  have hbound : Tendsto (fun i => (16*n^3*L^2*c⁻¹^5)*
      (a i)^((5+(1/100:ℝ))-(1+masterExponent)*5)) l (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (16*n^3*L^2*c⁻¹^5)
  have hscaled : Tendsto (fun i => ((a i)^6)^2*((16*(n*t i)^3*(L*(t i)⁻¹^4)^2)*
      (a i)^(-7+(1/100:ℝ)))) l (𝓝 0) := by
    apply squeeze_zero' _ _ hbound
    · filter_upwards [ha,ht] with i hai hti
      have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
      positivity
    · filter_upwards [ha,ht] with i hai hti
      have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
      rw [inverse_duality_rescale hai hti']
      calc
        _ ≤ (16*n^3*L^2)*(c⁻¹^5*(a i)^((5+(1/100:ℝ))-(1+masterExponent)*5)) :=
          mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 5) (by positivity)
        _ = _ := by ring
  have hh := hscaled.sqrt
  rw [Real.sqrt_zero] at hh
  apply hh.congr'
  filter_upwards [ha,ht] with i hai hti
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (pow_nonneg hai.le _)]

theorem inverse_retained_tendsto {ι : Type*} {l : Filter ι}
    {a t : ι → ℝ} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i) :
    Tendsto (fun i => (a i)^6*(A*(t i)⁻¹^3*(a i)^(-3+(1/100:ℝ)))) l (𝓝 0) := by
  have he : 0 < (3+(1/100:ℝ))-(1+masterExponent)*3 := by norm_num [masterExponent]
  have hh : Tendsto (fun i => (A*c⁻¹^3)*(a i)^((3+(1/100:ℝ))-(1+masterExponent)*3))
      l (𝓝 0) := by
    simpa only [mul_zero] using (ha0.rpow_const_nhds_zero he).const_mul (A*c⁻¹^3)
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,ht] with i hai hti
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    positivity
  · filter_upwards [ha,ht] with i hai hti
    rw [inverse_retained_rescale hai]
    calc
      _ ≤ A*(c⁻¹^3*(a i)^((3+(1/100:ℝ))-(1+masterExponent)*3)) :=
        mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 3) hA
      _ = _ := by ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_InverseObservationScaleBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis

lemma inverse_observation_geometry_tendsto {ι : Type*} {l : Filter ι}
    {a t ell : ι → ℝ} {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i)
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ)) :
    Tendsto (fun i => (a i)^3*(t i)⁻¹^4*((a i)^(6/5:ℝ)+2*ell i)) l (𝓝 0) := by
  have he1 : 0 < (21/5:ℝ)-(1+masterExponent)*4 := by norm_num [masterExponent]
  have he2 : 0 < (401/100:ℝ)-(1+masterExponent)*4 := by norm_num [masterExponent]
  have hh : Tendsto (fun i => c⁻¹^4*(a i)^((21/5:ℝ)-(1+masterExponent)*4)+
      (2*E*c⁻¹^4)*(a i)^((401/100:ℝ)-(1+masterExponent)*4)) l (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      ((ha0.rpow_const_nhds_zero he1).const_mul (c⁻¹^4)).add
        ((ha0.rpow_const_nhds_zero he2).const_mul (2*E*c⁻¹^4))
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,ht,hell] with i hai hti helli
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    have hli := helli.1
    positivity
  · filter_upwards [ha,ht,hell] with i hai hti helli
    have hti' := (mul_pos hc (Real.rpow_pos_of_pos hai (1+masterExponent))).trans_le hti
    have he1' : (a i)^3*(a i)^(6/5:ℝ) = (a i)^(21/5:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hai]
      norm_num
    have he2' : (a i)^3*(a i)^(101/100:ℝ) = (a i)^(401/100:ℝ) := by
      rw [←Real.rpow_natCast,←Real.rpow_add hai]
      norm_num
    calc
      _ ≤ (a i)^3*(t i)⁻¹^4*((a i)^(6/5:ℝ)+2*(E*(a i)^(101/100:ℝ))) := by
        gcongr
        exact helli.2
      _ = ((a i)^3*(a i)^(6/5:ℝ))*(t i)⁻¹^4+
          (2*E)*((a i)^3*(a i)^(101/100:ℝ))*(t i)⁻¹^4 := by ring
      _ = (a i)^(21/5:ℝ)*(t i)⁻¹^4+(2*E)*((a i)^(401/100:ℝ)*(t i)⁻¹^4) := by
        rw [he1',he2']; ring
      _ ≤ c⁻¹^4*(a i)^((21/5:ℝ)-(1+masterExponent)*4)+
          (2*E)*(c⁻¹^4*(a i)^((401/100:ℝ)-(1+masterExponent)*4)) :=
        add_le_add (rpow_inv_pow_bound hai hc hti 4)
          (mul_le_mul_of_nonneg_left (rpow_inv_pow_bound hai hc hti 4) (by positivity))
      _ = _ := by ring

theorem inverse_observation_error_tendsto {ι : Type*} {l : Filter ι}
    {a t ell Q : ι → ℝ} {c E L q : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht : ∀ᶠ i in l, c*(a i)^(1+masterExponent) ≤ t i)
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ))
    (hQ : Tendsto (fun i => (a i)^3*Q i) l (𝓝 q)) :
    Tendsto (fun i => (a i)^6*(Q i*(L*(t i)⁻¹^4*Real.sqrt 3*
      ((a i)^(6/5:ℝ)+2*ell i)))) l (𝓝 0) := by
  have hh := (hQ.mul (inverse_observation_geometry_tendsto hc hE ha ha0 ht hell)).const_mul (L*Real.sqrt 3)
  simp only [mul_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun i => by ring)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpErrorLimitBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

lemma patch_power_ratio {a : ℝ} (ha : 0 < a) (p w : ℝ) :
    (a^p/(a^(1/5:ℝ))^2)/a^w = a^(p-2/5-w) := by
  rw [←Real.rpow_mul_natCast ha.le,←Real.rpow_sub ha,←Real.rpow_sub ha]
  norm_num

lemma patch_sqrt_ratio {a : ℝ} (ha : 0 < a) (w : ℝ) :
    Real.sqrt (8*a^(1/5:ℝ))/a^w = Real.sqrt 8*a^(1/10-w) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8),Real.sqrt_eq_rpow (a^(1/5:ℝ)),
    ←Real.rpow_mul ha.le]
  norm_num
  rw [mul_div_assoc,←Real.rpow_sub ha]

lemma dimensionlessPatchRemainder_weight {a : ℝ} (ha : 0 < a) (M w : ℝ) :
    dimensionlessPatchRemainder a (a^(1/5:ℝ)) M/a^w = weightedDimensionlessPatch a M w := by
  have h2 : (a^2/(a^(1/5:ℝ))^2)/a^w = a^(8/5-w) := by
    convert patch_power_ratio ha 2 w using 1 <;> norm_num
  have h1 : (a/(a^(1/5:ℝ))^2)/a^w = a^(3/5-w) := by
    convert patch_power_ratio ha 1 w using 1 <;> norm_num
  have h3 : (a^3/a^(1/5:ℝ))/a^w = a^(14/5-w) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub ha,←Real.rpow_sub ha]
    norm_num
  have hr := patch_sqrt_ratio ha w
  unfold dimensionlessPatchRemainder weightedDimensionlessPatch
  rw [←h2,←h1,←h3,←hr]
  ring

theorem dimensionlessPatchRemainder_div_tendsto {ι : Type*} {l : Filter ι}
    {a M : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : w < 1/10) :
    Tendsto (fun i => dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)/(a i)^w)
      l (𝓝 0) := by
  have hpow (p : ℝ) (hp : 0 < p) := ha0.rpow_const_nhds_zero hp
  have hs : Tendsto (fun i => Real.sqrt (8*(a i)^(1/5:ℝ))) l (𝓝 0) := by
    simpa using ((hpow (1/5) (by norm_num)).const_mul 8).sqrt
  have h1 := ((hpow (8/5-w) (by linarith)).mul_const localizationIMSConstant).mul
    ((hs.mul_const actualCellMomentConstant).mul hM)
  have h2 := (((hpow (3/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    ((actualCellMomentConstant)^(2/3:ℝ))).mul (hM.rpow_const (Or.inr (by norm_num : (0:ℝ) ≤ 4/3)))
  have h3 := (((hpow (8/5-w) (by linarith)).mul_const neumannRemainderConstant).mul_const
    actualCellMomentConstant).mul hM
  have h4 := (((hpow (14/5-w) (by linarith)).mul_const ((2*Real.pi+1)/2)).mul_const
    actualCellMomentConstant).mul hM
  have h5 := ((((hpow (1/10-w) (by linarith)).const_mul (Real.sqrt 8)).const_mul
    sharpFreshFieldConstant).mul_const actualCellMomentConstant).mul (hM.pow 2)
  have h6 := ((((hpow (8/5-w) (by linarith)).mul_const (packetDirichlet canonicalRealPacket/2)).mul_const
    768).mul_const sharpFreshFieldConstant).mul hM
  have hh : Tendsto (fun i => weightedDimensionlessPatch (a i) (M i) w) l (𝓝 0) := by
    simpa only [weightedDimensionlessPatch,zero_mul,mul_zero,add_zero] using
      ((((h1.add h2).add h3).add h4).add h5).add h6
  apply hh.congr'
  filter_upwards [ha] with i hi
  exact (dimensionlessPatchRemainder_weight hi (M i) w).symm

lemma dimensionlessLocalPotential_tendsto {ι : Type*} {l : Filter ι}
    {M u : ι → ℝ} {M₀ : ℝ} (hM : Tendsto M l (𝓝 M₀)) (hu : Tendsto u l (𝓝 0)) :
    Tendsto (fun i => dimensionlessLocalPotential (M i) (u i)) l (𝓝 0) := by
  have h1 := ((hM.pow 2).const_mul sharpOrdinaryDensityConstant).rpow_const
    (Or.inr (by norm_num : (0:ℝ) ≤ 3/5))
  have h2 := hu.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  simpa only [dimensionlessLocalPotential,mul_zero] using
    (h1.mul_const ((8*Real.pi)^(2/5:ℝ))).mul h2

theorem dimensionlessPotentialRemainder_tendsto {ι : Type*} {l : Filter ι}
    {a M E : ι → ℝ} {M₀ w : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0)) (hM : Tendsto M l (𝓝 M₀)) (hw : 0 < w) (hw' : w < 1/10)
    (hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0)) :
    Tendsto (fun i => dimensionlessPotentialRemainder (a i) ((a i)^(1/5:ℝ)) (M i) (E i) ((a i)^w))
      l (𝓝 0) := by
  have hR := dimensionlessPatchRemainder_div_tendsto ha ha0 hM hw'
  have hτ := ha0.rpow_const_nhds_zero hw
  have hβ := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  have hroot : Tendsto (fun i => Real.sqrt ((2/(a i)^w)*
      (E i+dimensionlessPatchRemainder (a i) ((a i)^(1/5:ℝ)) (M i)))) l (𝓝 0) := by
    have ht := ((hE.add hR).const_mul 2).sqrt
    convert ht using 1
    · funext i
      congr 1
      ring
    · simp
  have hu1 : Tendsto (fun i => (a i)^w+Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hτ.add (hβ.const_mul (Real.sqrt 3))
  have hu2 : Tendsto (fun i => Real.sqrt 3*(a i)^(1/5:ℝ)) l (𝓝 0) := by
    simpa using hβ.const_mul (Real.sqrt 3)
  have hcap := (hτ.pow 2).const_mul (2*Real.pi*tfPatchDensityCapConstant)
  have hdel := (((hβ.const_mul 8).sqrt).mul_const actualCellMomentConstant).mul hM
  simpa only [dimensionlessPotentialRemainder,zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),
    Real.sqrt_zero,add_zero] using
    (((hroot.add (dimensionlessLocalPotential_tendsto hM hu1)).add hcap).add
      (dimensionlessLocalPotential_tendsto hM hu2)).add hdel

end Work_SharpErrorLimit_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma microscopicWidth_eq {a : ℝ} (ha : 0 < a) :
    a*a^(1/5:ℝ) = a^(6/5:ℝ) := by
  calc _ = a^(1:ℝ)*a^(1/5:ℝ) := by rw [Real.rpow_one]
       _ = _ := by rw [←Real.rpow_add ha]; norm_num

lemma microscopic_collar {a m : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hm : 1/a^3 ≤ m) : a ≤ (a*a^(1/5:ℝ))^2*m := by
  have hβ : a ≤ a^(1/5:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (1/5:ℝ) ≤ 1)
  have hb : a^2 ≤ a*a^(1/5:ℝ) := by nlinarith
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  have hsq : a^4 ≤ (a*a^(1/5:ℝ))^2 := by nlinarith [sq_nonneg (a*a^(1/5:ℝ)-a^2)]
  calc a = a^4*(1/a^3) := by field_simp
       _ ≤ a^4*m := mul_le_mul_of_nonneg_left hm (by positivity)
       _ ≤ (a*a^(1/5:ℝ))^2*m := mul_le_mul_of_nonneg_right hsq hm0

lemma normalized_excess_ratio {a D w : ℝ} (ha : 0 < a) :
    (D*a^7)/a^w = D*a^(7-w) := by
  rw [mul_div_assoc,←Real.rpow_natCast,←Real.rpow_sub ha]
  norm_num

theorem physical_local_mass_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^3*localOffsetMass (D i) (y i)) l (𝓝 1) := by
  let a := fun i => localCellRadius (y i)
  have hp : Tendsto (fun i => (a i)^w) l (𝓝 0) := hy0.rpow_const_nhds_zero hw
  have hE : Tendsto (fun i => D i*(a i)^7) l (𝓝 0) := by
    have ht := hD.mul hp
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [hy] with i hi
    have ha := localCellRadius_pos hi
    change D i*(a i)^(7-w)*(a i)^w = D i*(a i)^7
    rw [mul_assoc,←Real.rpow_add ha]
    norm_num [a]
  have ht : Tendsto (fun i => 1+Real.sqrt (D i*(a i)^7)) l (𝓝 1) := by
    simpa using hE.sqrt.const_add 1
  apply ht.congr'
  filter_upwards [hy,hy0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi ha1
  exact (localOffsetMass_rescale hi ha1.le).symm

theorem physical_potential_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w) (hw' : w < 1/10)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*
      sharpPotentialRemainder (localCellRadius (y i))
        ((localCellRadius (y i))^(6/5:ℝ)) (localOffsetMass (D i) (y i)) (D i)
        ((localCellRadius (y i))*(localCellRadius (y i))^w)) l (𝓝 0) := by
  let a := fun i => localCellRadius (y i)
  let M := fun i => (a i)^3*localOffsetMass (D i) (y i)
  let E := fun i => D i*(a i)^7
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono (fun i hi => localCellRadius_pos hi)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have hE : Tendsto (fun i => E i/(a i)^w) l (𝓝 0) := by
    apply hD.congr'
    filter_upwards [ha] with i hi
    exact (normalized_excess_ratio hi).symm
  have ht := dimensionlessPotentialRemainder_tendsto ha hy0 hM hw hw' hE
  apply ht.congr'
  filter_upwards [ha] with i hi
  have hMi : 0 ≤ M i := mul_nonneg (pow_nonneg hi.le _) (le_trans zero_le_one (localOffsetMass_one_le _ _))
  have he := sharpPotentialRemainder_rescale (E := E i) hi (Real.rpow_pos_of_pos hi (1/5:ℝ)) hMi (Real.rpow_pos_of_pos hi w)
  have hmass : M i/(a i)^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  have henergy : E i/(a i)^7 = D i := by dsimp [E]; field_simp
  rw [hmass,henergy,microscopicWidth_eq hi] at he
  exact he.symm

theorem physical_patch_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w) (hw' : w < 1/10)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0)) :
    Tendsto (fun i => (D i+sharpPatchRemainder (localCellRadius (y i))
      ((localCellRadius (y i))^(6/5:ℝ)) (localOffsetMass (D i) (y i)))*
        (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  let a := fun i => localCellRadius (y i)
  let M := fun i => (a i)^3*localOffsetMass (D i) (y i)
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono (fun i hi => localCellRadius_pos hi)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have ht := hD.add (dimensionlessPatchRemainder_div_tendsto ha hy0 hM hw')
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [ha] with i hi
  have hMi : 0 ≤ M i := mul_nonneg (pow_nonneg hi.le _) (le_trans zero_le_one (localOffsetMass_one_le _ _))
  have he := sharpPatchRemainder_rescale hi (Real.rpow_pos_of_pos hi (1/5:ℝ)) hMi
  have hmass : M i/(a i)^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  rw [hmass,microscopicWidth_eq hi] at he
  rw [←he,add_mul]
  congr 1
  rw [mul_comm ((a i)^7),normalized_excess_ratio hi]

theorem physical_master_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D u : ι → ℝ} {w : ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0) (hy0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : 0 < w)
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-w)) l (𝓝 0))
    (hu : ∀ᶠ i in l, 0 ≤ u i) (hu0 : Tendsto u l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*sharpLocalPotentialBudget
      (localCellRadius (y i)) (localOffsetMass (D i) (y i))
      ((localCellRadius (y i))*u i)) l (𝓝 0) := by
  let M := fun i => (localCellRadius (y i))^3*localOffsetMass (D i) (y i)
  have hM : Tendsto M l (𝓝 1) := physical_local_mass_tendsto hy hy0 hw hD
  have ht := dimensionlessLocalPotential_tendsto hM hu0
  apply ht.congr'
  filter_upwards [hy,hu] with i hi hui
  have ha := localCellRadius_pos hi
  have he := sharpLocalPotentialBudget_rescale (M := M i) ha hui
  have hm : M i/(localCellRadius (y i))^3 = localOffsetMass (D i) (y i) := by dsimp [M]; field_simp
  rw [hm] at he
  exact he.symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseBudgetScaleBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma inverse_gap_rescale {a R : ℝ} (ha : 0 < a) (hR : 0 < R) (C G : ℝ) :
    a^4*((C/R^4)/a^(-7+(1/100:ℝ)))*G =
      (C*(a/R)^4)*(G*a^(7-(1/100:ℝ))) := by
  have he : a^(-7+(1/100:ℝ)) = (a^(7-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]
    congr 1
    ring
  rw [he,div_inv_eq_mul]
  field_simp

lemma inverse_high_gap_rescale {a : ℝ} (ha : 0 < a) (H G : ℝ) :
    a^4*(H/a^(-7+(1/100:ℝ))+2/a^(-3+(1/100:ℝ)))*G =
      (a^4*H+2)*(G*a^(7-(1/100:ℝ))) := by
  have he1 : a^(-7+(1/100:ℝ)) = (a^(7-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]; congr 1; ring
  have he2 : a^(-3+(1/100:ℝ)) = (a^(3-(1/100:ℝ)))⁻¹ := by
    rw [←Real.rpow_neg ha.le]; congr 1; ring
  have he3 : a^4*a^(3-(1/100:ℝ)) = a^(7-(1/100:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_add ha]
    norm_num
  rw [he1,he2,div_inv_eq_mul,div_inv_eq_mul]
  calc _ = (a^4*H)*(G*a^(7-(1/100:ℝ)))+2*G*(a^4*a^(3-(1/100:ℝ))) := by ring
       _ = _ := by rw [he3]; ring

lemma inverse_low_gap_tendsto {ι : Type*} {l : Filter ι}
    {a R G : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (hG : Tendsto (fun i => G i*(a i)^(7-(1/100:ℝ))) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*((C/(R i)^4)/(a i)^(-7+(1/100:ℝ)))*G i)
      l (𝓝 0) := by
  have hh := bdd_le_mul_tendsto_zero (f := fun i => C*(a i/R i)^4)
    (b := 0) (B := C) (by
      filter_upwards [ha,hR] with i hai hRi
      positivity) (by
      filter_upwards [ha,hR] with i hai hRi
      have hRi' := hai.trans_le hRi
      have hb := pow_le_one₀ (div_nonneg hai.le hRi'.le) ((div_le_one hRi').mpr hRi) (n := 4)
      exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (mul_one C)) hG
  apply hh.congr'
  filter_upwards [ha,hR] with i hai hRi
  exact (inverse_gap_rescale hai (hai.trans_le hRi) C (G i)).symm

lemma inverse_high_gap_tendsto {ι : Type*} {l : Filter ι}
    {a H G : ι → ℝ} {h : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h))
    (hG : Tendsto (fun i => G i*(a i)^(7-(1/100:ℝ))) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*(H i/(a i)^(-7+(1/100:ℝ))+
      2/(a i)^(-3+(1/100:ℝ)))*G i) l (𝓝 0) := by
  have hh := (hH.add_const 2).mul hG
  simp only [mul_zero] at hh
  apply hh.congr'
  exact ha.mono fun i hi => (inverse_high_gap_rescale hi (H i) (G i)).symm

theorem inverse_potential_error_tendsto {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D t : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (ht : ∀ᶠ i in l, 0 ≤ t i)
    (ht0 : Tendsto (fun i => t i/localCellRadius (y i)) l (𝓝 0)) :
    Tendsto (fun i => (localCellRadius (y i))^4*(
      sharpPotentialRemainder (localCellRadius (y i)) ((localCellRadius (y i))^(6/5:ℝ))
        (localOffsetMass (D i) (y i)) (D i)
        ((localCellRadius (y i))*(localCellRadius (y i))^masterExponent)+
      sharpLocalPotentialBudget (localCellRadius (y i)) (localOffsetMass (D i) (y i))
        (2*t i))) l (𝓝 0) := by
  have hpot := physical_potential_error_tendsto hy ha0 masterExponent_pos
    (by norm_num [masterExponent] : masterExponent < 1/10) hD
  have hu : ∀ᶠ i in l, 0 ≤ 2*(t i/localCellRadius (y i)) := by
    filter_upwards [hy,ht] with i hyi hti
    have hai := localCellRadius_pos hyi
    positivity
  have hu0 : Tendsto (fun i => 2*(t i/localCellRadius (y i))) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul 2
  have hmaster := physical_master_error_tendsto hy ha0 masterExponent_pos hD hu hu0
  have hh := hpot.add hmaster
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [hy] with i hyi
  have hai := localCellRadius_pos hyi
  rw [show localCellRadius (y i)*(2*(t i/localCellRadius (y i))) = 2*t i by field_simp]
  ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_InverseThresholdLimitBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma localTFResponse_continuous : Continuous localTFResponse := by
  unfold localTFResponse
  exact (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp
    ((continuous_id.max continuous_const).div_const _)

lemma localTFResponse_rescale {a : ℝ} (ha : 0 < a) (h : ℝ) :
    a^6*localTFResponse h = localTFResponse (a^4*h) := by
  have he : max (a^4*h) 0 = a^4*max h 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _),mul_zero]
  have hT := tfKinetic_pos
  unfold localTFResponse
  rw [he,mul_div_assoc,Real.mul_rpow (pow_nonneg ha.le _) (by positivity),
    ←Real.rpow_natCast a 4,←Real.rpow_mul ha.le]
  norm_num

lemma inverse_oscillation_rescale {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (C n t : ℝ) :
    a^4*(C/R*(n*t))*R⁻¹^4 = C*n*(t/a)*(a/R)^5 := by
  field_simp

lemma inverse_oscillation_tendsto {ι : Type*} {l : Filter ι}
    {a R t : ι → ℝ} {C n : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (ht : ∀ᶠ i in l, 0 ≤ t i) (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*(C/R i*(n*t i))*(R i)⁻¹^4) l (𝓝 0) := by
  have hh : Tendsto (fun i => C*n*(t i/a i)) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul (C*n)
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,hR,ht] with i hai hRi hti
    have hRi' := hai.trans_le hRi
    positivity
  · filter_upwards [ha,hR,ht] with i hai hRi hti
    have hRi' := hai.trans_le hRi
    rw [inverse_oscillation_rescale hai hRi']
    have hh : (a i/R i)^5 ≤ 1 := pow_le_one₀ (div_nonneg hai.le hRi'.le)
      ((div_le_one hRi').mpr hRi)
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (mul_one _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseThresholdMarginsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseThresholdMargins_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAnalysis

lemma eventually_forall_mem_of_selections {ι α : Type*} {l : Filter ι}
    {S : ι → Set α} {P : ι → α → Prop} (d : ι → α)
    (hd : ∀ᶠ i in l, d i ∈ S i)
    (h : ∀ f : ι → α, (∀ᶠ i in l, f i ∈ S i) → ∀ᶠ i in l, P i (f i)) :
    ∀ᶠ i in l, ∀ x ∈ S i, P i x := by
  classical
  let f : ι → α := fun i => if hi : ∃ x ∈ S i, ¬P i x then Classical.choose hi else d i
  have hf : ∀ᶠ i in l, f i ∈ S i := by
    filter_upwards [hd] with i hi
    dsimp only [f]
    split_ifs with hn
    · exact (Classical.choose_spec hn).1
    · exact hi
  filter_upwards [h f hf] with i hi
  intro x hx
  by_contra hn
  have hex : ∃ x ∈ S i, ¬P i x := ⟨x,hx,hn⟩
  exact (Classical.choose_spec hex).2 (by simpa only [f,dite_eq_left hex] using hi)

lemma localTFResponse_nonneg (h : ℝ) : 0 ≤ localTFResponse h := by
  have hT := tfKinetic_pos
  unfold localTFResponse
  exact Real.rpow_nonneg (div_nonneg (le_max_right _ _) (by positivity)) _

lemma localTFResponse_strict_mono {h H : ℝ} (hh : 0 ≤ h) (hH : h < H) :
    localTFResponse h < localTFResponse H := by
  have hT : 0 < (5/3:ℝ)*tfKinetic := mul_pos (by norm_num) tfKinetic_pos
  unfold localTFResponse
  rw [max_eq_left hh,max_eq_left (hh.trans hH.le)]
  exact Real.rpow_lt_rpow (div_nonneg hh hT.le) ((div_lt_div_iff_of_pos_right hT).mpr hH) (by norm_num)

lemma inverse_low_density_margin {ι : Type*} {l : Filter ι}
    {a T E F : ι → ℝ} {t f : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hT : Tendsto (fun i => (a i)^6*T i) l (𝓝 t))
    (hE : Tendsto (fun i => (a i)^6*E i) l (𝓝 0))
    (hF : Tendsto (fun i => (a i)^6*F i) l (𝓝 f)) (htf : t < f) :
    ∀ᶠ i in l, T i+E i < F i := by
  have hh := (hT.add hE).eventually_lt hF (by simpa using htf)
  filter_upwards [ha,hh] with i hai hi
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 6)).mp
  linarith

lemma inverse_high_density_margin {ι : Type*} {l : Filter ι}
    {a T E F M : ι → ℝ} {t f : ℝ} (ha : ∀ᶠ i in l, 0 < a i)
    (hT : Tendsto (fun i => (a i)^6*T i) l (𝓝 t))
    (hE : Tendsto (fun i => (a i)^6*E i) l (𝓝 0))
    (hF : Tendsto (fun i => (a i)^6*F i) l (𝓝 f))
    (hM : Tendsto (fun i => (a i)^6*M i) l (𝓝 0)) (hf : 0 ≤ f) (htf : f < t) :
    ∀ᶠ i in l, max (F i) (M i)+E i < T i := by
  have hh := ((hF.max hM).add hE).eventually_lt hT (by simpa [max_eq_left hf] using htf)
  filter_upwards [ha,hh] with i hai hi
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 6)).mp
  rw [mul_add,mul_max_of_nonneg _ _ (pow_nonneg hai.le _)]
  exact hi

end Work_InverseThresholdMargins_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

lemma observation_relative_tendsto {ι : Type*} {l : Filter ι} {a ell : ι → ℝ}
    {E : ℝ} (_hE : 0 ≤ E) (ha : ∀ᶠ i in l, 0 < a i)
    (ha0 : Tendsto a l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(a i)^(101/100:ℝ)) :
    Tendsto (fun i => ell i/a i) l (𝓝 0) := by
  have hh : Tendsto (fun i => E*(a i)^(1/100:ℝ)) l (𝓝 0) := by
    simpa only [mul_zero] using (ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/100)).const_mul E
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,hell] with i hai hei
    exact div_nonneg hei.1 hai.le
  · filter_upwards [ha,hell] with i hai hei
    calc _ ≤ E*(a i)^(101/100:ℝ)/a i := div_le_div_of_nonneg_right hei.2 hai.le
         _ = _ := by
           have heq : (a i)^(101/100:ℝ)/a i = (a i)^(1/100:ℝ) := by
             calc _ = (a i)^((101/100:ℝ)-1) := by rw [Real.rpow_sub hai,Real.rpow_one]
                  _ = _ := by norm_num
           rw [mul_div_assoc,heq]

lemma microscopic_relative_tendsto {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0)) :
    Tendsto (fun i => (a i)^(6/5:ℝ)/a i) l (𝓝 0) := by
  have hh := ha0.rpow_const_nhds_zero (by norm_num : (0:ℝ) < 1/5)
  apply hh.congr'
  filter_upwards [ha] with i hai
  calc _ = (a i)^((6/5:ℝ)-1) := by norm_num
       _ = _ := by rw [Real.rpow_sub hai,Real.rpow_one]

theorem inverse_geometry_eventually {ι : Type*} {l : Filter ι}
    {a t ell : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0))
    (hell0 : Tendsto (fun i => ell i/a i) l (𝓝 0)) :
    ∀ᶠ i in l,
      a i ≤ 1 ∧
      0 < (a i)^(6/5:ℝ) ∧ 2*(a i)^(6/5:ℝ) ≤ a i ∧
      0 < a i*(a i)^masterExponent ∧
      a i*(a i)^masterExponent+Real.sqrt 3*(a i)^(6/5:ℝ) ≤ 4*a i ∧
      a i*(a i)^masterExponent ≤ 3*(5*a i-4*(a i)^(6/5:ℝ))/4 ∧
      a i ≤ ((a i)^(6/5:ℝ))^2*(1/(a i)^3) ∧
      3*t i ≤ (5*a i-4*(a i)^(6/5:ℝ))/12 ∧
      2*t i+Real.sqrt 3*((a i)^(6/5:ℝ)+2*ell i) < a i := by
  have hb0 := microscopic_relative_tendsto ha ha0
  have hq0 := ha0.rpow_const_nhds_zero masterExponent_pos
  filter_upwards [ha,
    ha0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hb0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    hq0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    ht0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100)),
    hell0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/100))]
    with i hai ha1 hbi hqi hti heli
  have hb : (a i)^(6/5:ℝ) < a i/100 := by linarith [(div_lt_iff₀ hai).mp hbi]
  have ht : t i < a i/100 := by linarith [(div_lt_iff₀ hai).mp hti]
  have he : ell i < a i/100 := by linarith [(div_lt_iff₀ hai).mp heli]
  have hq : a i*(a i)^masterExponent < a i/100 := by nlinarith
  have hbpos : 0 < (a i)^(6/5:ℝ) := Real.rpow_pos_of_pos hai _
  have hqpos : 0 < a i*(a i)^masterExponent := mul_pos hai (Real.rpow_pos_of_pos hai _)
  have hroot : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
  have hprod : Real.sqrt 3*(a i)^(6/5:ℝ) ≤ 2*(a i)^(6/5:ℝ) :=
    mul_le_mul_of_nonneg_right hroot hbpos.le
  have hcol := microscopic_collar hai ha1.le (m := 1/(a i)^3) le_rfl
  rw [microscopicWidth_eq hai] at hcol
  refine ⟨ha1.le,hbpos,by linarith,hqpos,by linarith,by linarith,hcol,by linarith,?_⟩
  have he' : Real.sqrt 3*ell i < 2*a i/100 := by
    calc _ < Real.sqrt 3*(a i/100) := mul_lt_mul_of_pos_left he (Real.sqrt_pos.mpr (by norm_num))
         _ ≤ _ := by nlinarith
  nlinarith

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_InverseNumericalStatementsBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_InverseNumericalStatements_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis

lemma scaled_div_pow_constant {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : ∀ᶠ i in l, 0 < a i) (n : ℕ) (c : ℝ) :
    Tendsto (fun i => (a i)^n*(c/(a i)^n)) l (𝓝 c) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [ha] with i hai
  field_simp

end Work_InverseNumericalStatements_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis

open Filter Set
open scoped Topology

open CoulombAnalysis

lemma inverse_unscaled_oscillation_tendsto {ι : Type*} {l : Filter ι}
    {a R t : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0)) (C n : ℝ) :
    Tendsto (fun i => C/R i*(n*t i)) l (𝓝 0) := by
  have hh : Tendsto (fun i => C*n*(t i/a i)) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul (C*n)
  have hm := bdd_le_mul_tendsto_zero (f := fun i => a i/R i) (b := 0) (B := 1)
    (by filter_upwards [ha,hR] with i hai hRi; exact div_nonneg hai.le (hai.le.trans hRi))
    (by filter_upwards [ha,hR] with i hai hRi; exact (div_le_one (hai.trans_le hRi)).mpr hRi) hh
  apply hm.congr'
  filter_upwards [ha,hR] with i hai hRi
  have hRi' := hai.trans_le hRi
  field_simp

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BandInverseNumericsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BandInverseNumerics_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

lemma quantumInverseCountConstant_pos : 0 < quantumInverseCountConstant := by
  have := universalCellCountConstant_one_le
  unfold quantumInverseCountConstant
  linarith

lemma quantumInverseCountConstant_square : universalCellCountConstant < quantumInverseCountConstant^2 := by
  have := universalCellCountConstant_one_le
  unfold quantumInverseCountConstant
  nlinarith [sq_nonneg universalCellCountConstant]

lemma inverse_count_margin_eventually {ι : Type*} {l : Filter ι}
    {y : ι → Space} {D : ι → ℝ}
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0)) :
    ∀ᶠ i in l, universalCellCountConstant*(localOffsetMass (D i) (y i))^2 <
      (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hm := physical_local_mass_tendsto hy ha0 masterExponent_pos hD
  have hh := ((hm.pow 2).const_mul universalCellCountConstant).eventually_lt
    (tendsto_const_nhds (x := quantumInverseCountConstant^2))
    (by simpa using quantumInverseCountConstant_square)
  filter_upwards [hy,hh] with i hyi hi
  have ha := localCellRadius_pos hyi
  have hscale : (localCellRadius (y i))^6*
      (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 = quantumInverseCountConstant^2 := by
    field_simp
  apply (mul_lt_mul_iff_right₀ (pow_pos ha 6)).mp
  rw [hscale]
  nlinarith only [hi]

end Work_BandInverseNumerics_barrier_scope

open MeasureTheory Filter Set
open scoped ENNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.local_count_failure {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (hstate : TailTiltState Z lam r K p₀ δ F)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0) (R T : ℝ) (hT : 0 ≤ T)
    (hRQ : R+Real.sqrt 3*dyadicObservationWidth r k < localCellRadius y)
    (hlarge : universalCellCountConstant*
      (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)^2 < T^2) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | T < observedLocalCount (fun k : Fin K => dyadicObservationWidth r k) k y R z}).toReal < p₀ j := by
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) := {z | T < observedLocalCount ell k y R z}
  have hA : MeasurableSet[observationInformation ell j] A := measurableSet_lt measurable_const
    (observedLocalCount_information_measurable ell k hk y R)
  by_contra! hn
  obtain ⟨G,hGn,hlaw,hD⟩ := hstate.2.2 j A hA hn
  have hlower := event_raw_count_lower F G hGn ell (fun k => (dyadicObservationWidth_pos hr k).le)
    k y hT hRQ ((observationInformation_le ell j) A hA) (fun z hz => hz.le) hlaw
  have hψ := graphFormVector_admissible G hGn
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  have hupper := priced_local_cell_count hψ.sobolevFermion hm hZ hlam hy
  have he := pow_le_pow_left₀
    (le_trans zero_le_one (localOffsetMass_one_le (max (corePriceExcess Z lam (graphFormVector G)) 0) y))
    (localOffsetMass_mono hD y) 2
  have hbound := hupper.trans (mul_le_mul_of_nonneg_left he
    (le_trans zero_le_one universalCellCountConstant_one_le))
  exact (not_le_of_gt hlarge) (hlower.trans hbound)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPointInverseBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

lemma measureReal_remove_cutoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω} {g : Ω → ℝ} {Q p : ℝ}
    (hA : μ.real {z | z ∈ A ∧ g z ≤ Q} < p)
    (hQ : μ.real {z | Q < g z} < p) : μ.real A < 2*p := by
  have hm : A ⊆ {z | z ∈ A ∧ g z ≤ Q} ∪ {z | Q < g z} := by
    intro z hz
    by_cases h : g z ≤ Q
    · exact Or.inl ⟨hz,h⟩
    · exact Or.inr (lt_of_not_ge h)
  exact (measureReal_mono hm).trans_lt
    ((measureReal_union_le _ _).trans_lt (by linarith only [hA,hQ]))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FullAnnulusWidthNumerics
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombBarrier CoulombObservation

theorem fresh_threshold_response_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ n sign h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hn : 2 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*(
      localTFResponse (H i+sign*(tfPatchOscillationConstant/R i*
        (n*masterWidth c₁ (r₀ i) (s i) (y i)))*(R i)⁻¹^4)*
        (∫ x, masterCenteredKernel c₁ (r₀ i) (s i) canonicalRealPacket (y i) x ∂ballMeasure (R i))+
      sign*Real.sqrt ((16*(n*masterWidth c₁ (r₀ i) (s i) (y i))^3*
        ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ (r₀ i) (s i) (y i))⁻¹^4)^2)*(a i)^(-7+(1/100:ℝ)))))
      l (𝓝 (localTFResponse h)) := by
  let t := fun i => masterWidth c₁ (r₀ i) (s i) (y i)
  have ht : ∀ᶠ i in l, 0 < t i := by
    filter_upwards [hr,hs] with i hri hsi
    exact masterWidth_pos hc hri hsi (y i)
  have hosc := inverse_oscillation_tendsto tfPatchOscillationConstant_pos.le
    (by linarith : 0 ≤ n) ha hR (ht.mono fun _ hi => hi.le) hw0
  have hinner := hH.add (hosc.const_mul sign)
  simp only [mul_zero,add_zero] at hinner
  have hresp := localTFResponse_continuous.continuousAt.tendsto.comp hinner
  have hfit : ∀ᶠ i in l, 2*t i < R i := by
    filter_upwards [ha,hR,hw0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))]
      with i hai hRi hi
    have hh : t i < (1/2:ℝ)*a i := (div_lt_iff₀ hai).mp hi
    linarith
  have hmass := masterCenteredKernel_mass_tendsto canonicalRealPacket_smooth
    canonicalRealPacket_support canonicalRealPacket_normalized hc hcL hr hs hs0 hfit
  have herr := inverse_duality_tendsto (L := (masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ))
    hc₂ (by linarith : 0 ≤ n) ha ha0 hw
  have hh := (hresp.mul hmass).add (herr.const_mul sign)
  simp only [mul_one,mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [ha] with i hai
  simp only [Function.comp_apply]
  rw [show (a i)^4*H i+sign*((a i)^4*(tfPatchOscillationConstant/R i*(n*t i))*(R i)⁻¹^4) =
      (a i)^4*(H i+sign*(tfPatchOscillationConstant/R i*(n*t i))*(R i)⁻¹^4) by ring,
    ←localTFResponse_rescale hai]
  dsimp only [t]
  ring

lemma freshLowThreshold_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshLowThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshLowThreshold,localTFResponse,neg_one_mul,neg_mul,one_mul,sub_eq_add_neg] using
    (fresh_threshold_response_tendsto_of_width (sign := -1) hc hcL hc₂ (by norm_num : (2:ℝ) ≤ 2)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma freshHighThreshold_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshHighThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshHighThreshold,localTFResponse,one_mul] using
    (fresh_threshold_response_tendsto_of_width (sign := 1) hc hcL hc₂ (by norm_num : (2:ℝ) ≤ 3)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma inverse_density_error_tendsto_of_width {ι : Type*} {l : Filter ι}
    {r₀ s ell : ι → ℝ} {y : ι → Space} {c₁ c₂ E C : ℝ}
    (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ)) :
    Tendsto (fun i => (localCellRadius (y i))^6*inverseDensityError c₁ (r₀ i) (s i) (ell i) C (y i)) l (𝓝 0) := by
  have ha := hy.mono fun i hi => localCellRadius_pos hi
  exact inverse_observation_error_tendsto hc₂ hE ha ha0 hw hell (scaled_div_pow_constant ha 3 C)

theorem low_inverse_numerics_eventually_of_width {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ c₂ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hh : 0 ≤ h) (hxi : 0 < xi)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, LowInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h+xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h+xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto_of_width (C := C) hc₂ hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshLowThreshold_tendsto_of_width hc hcL hc₂ ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_low_density_margin ha hT hdenerr hF
    (localTFResponse_strict_mono hh (by linarith : h < h+xi/2))
  have hgap := inverse_low_gap_tendsto tfPatchCapConstant_pos.le ha hR hG
  have hleft := (hH.add hgap).add hpot
  simp only [add_zero] at hleft
  have hright := scaled_div_pow_constant ha 4 (h+xi)
  have hsmall := hleft.eventually_lt hright (by linarith : h+xi/2 < h+xi)
  filter_upwards [ha,hdensity,hsmall] with i hai hdi hsi
  refine ⟨hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

theorem high_inverse_numerics_eventually_of_width {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ c₂ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hxi : 0 < xi) (hxih : xi < 2*h)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, HighInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h-xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h-xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto_of_width (C := C) hc₂ hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  have hgap := inverse_high_gap_tendsto ha hH hG
  have hmass := inverse_retained_tendsto hc₂ canonicalMasterAmplitude_pos.le ha ha0 hw
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshHighThreshold_tendsto_of_width hc hcL hc₂ ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_high_density_margin ha hT hdenerr hF hmass
    (localTFResponse_nonneg (h-xi/2))
    (localTFResponse_strict_mono (by linarith : 0 ≤ h-xi/2) (by linarith : h-xi/2 < h))
  have hosc := inverse_unscaled_oscillation_tendsto ha hR hw0 tfPatchOscillationConstant 3
  have hoscsmall := hosc.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have hoscscaled := inverse_oscillation_tendsto tfPatchOscillationConstant_pos.le
    (by norm_num : (0:ℝ) ≤ 3) ha hR ht hw0
  have hleft := (scaled_div_pow_constant ha 4 (h-xi)).add hpot
  simp only [add_zero] at hleft
  have hright := (hH.sub hgap).sub (hoscscaled.const_mul 2)
  simp only [sub_zero,mul_zero] at hright
  have hsmall := hleft.eventually_lt hright (by linarith : h-xi < h-xi/2)
  filter_upwards [ha,hoscsmall,hdensity,hsmall] with i hai hosi hdi hsi
  refine ⟨hosi.le,hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_PolynomialProbabilityBudgetBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PolynomialProbabilityBudget_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation

lemma polynomial_log_cost_tendsto (n : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun r : ℝ => r^v*(Real.log (Real.exp 1/r^n))^5)
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ := v/5
  have hq : 0 < q := by dsimp [q]; positivity
  have hpow : Tendsto (fun r : ℝ => r^q) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero hq).mono_left inf_le_left
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hq
  have hh := (hpow.sub (hlog.const_mul (n:ℝ))).pow 5
  simp only [mul_zero,sub_zero,zero_pow (by norm_num : (5:ℕ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  rw [Real.log_div (Real.exp_pos 1).ne' (pow_pos hr n).ne',Real.log_exp,Real.log_pow]
  rw [show r^q-n*(Real.log r*r^q) = r^q*(1-n*Real.log r) by ring,
    mul_pow,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 2
  dsimp [q]
  ring

lemma polynomial_probability_budget_tendsto (n : ℕ) {v : ℝ} (hv : 2.02 < v) (δ : ℝ) :
    Tendsto (fun r : ℝ => dyadicUniformEventBudget r (r^n) δ*r^v)
      (𝓝[>] 0) (𝓝 0) := by
  have hp : Tendsto (fun r : ℝ => r^v) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_id.rpow_const_nhds_zero (by linarith : 0 < v)).mono_left inf_le_left
  have hh := ((polynomial_log_cost_tendsto n (by linarith : 0 < v-2.02)).const_mul
    observationFisherConstant).add (hp.const_mul δ)
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have he : r^(-2.02:ℝ)*r^v = r^(v-2.02) := by
    rw [←Real.rpow_add hr]
    congr 1
    ring
  dsimp only [dyadicUniformEventBudget]
  rw [add_mul]
  rw [show observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/r^n))^5*r^v =
    observationFisherConstant*(r^(-2.02:ℝ)*r^v)*(Real.log (Real.exp 1/r^n))^5 by ring,he]
  ring

end Work_PolynomialProbabilityBudget_barrier_scope

open Filter Set
open scoped Topology

open CoulombAnalysis CoulombBarrier

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_FullAnnulusGeometry
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier CoulombObservation

lemma fullAnnulus_local_radius_le {B u : ℝ} {y : Space}
    (hBu : 0 ≤ B*u) (hy : ‖y‖ ≤ B*u) : localCellRadius y ≤ B*u := by
  unfold localCellRadius
  linarith

lemma masterWidth_fullAnnulus_lower {c₁ B r₀ s : ℝ} {y : Space}
    (hc : 0 ≤ c₁) (hB : 1 ≤ B) (hy : y ≠ 0)
    (has : localCellRadius y ≤ B*s) :
    (c₁/B^(1+masterExponent))*(localCellRadius y)^(1+masterExponent) ≤
      masterWidth c₁ r₀ s y := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have ha := localCellRadius_pos hy
  have hr : 0 < localCellRadius y/B := div_pos ha hBp
  have hrs : localCellRadius y/B ≤ s := (div_le_iff₀ hBp).mpr (by nlinarith only [has])
  have hry : localCellRadius y/B ≤ ‖y‖ := by
    have hdiv : localCellRadius y/B ≤ localCellRadius y :=
      div_le_self ha.le hB
    apply hdiv.trans
    unfold localCellRadius
    linarith [norm_nonneg y]
  have hh := masterWidth_radius_lower (r₀ := r₀) hc hr hrs hry
  rw [Real.div_rpow ha.le hBp.le] at hh
  convert hh using 1 <;> first | rfl | ring

lemma fullAnnulus_local_radius_tendsto {ι : Type*} {l : Filter ι}
    {s u : ι → ℝ} {y : ι → Space} {B : ℝ} (hB : 0 ≤ B)
    (hs0 : Tendsto s l (𝓝 0)) (hu : ∀ᶠ i in l, 0 < u i)
    (hus : ∀ᶠ i in l, u i ≤ s i) (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*u i) :
    Tendsto (fun i => localCellRadius (y i)) l (𝓝 0) := by
  have hb : Tendsto (fun i => B*s i) l (𝓝 0) := by
    simpa only [mul_zero] using hs0.const_mul B
  apply squeeze_zero' (Eventually.of_forall (fun _ => by unfold localCellRadius; positivity)) _ hb
  filter_upwards [hu,hus,hy] with i hui husi hyi
  exact (fullAnnulus_local_radius_le (mul_nonneg hB hui.le) hyi).trans
    (mul_le_mul_of_nonneg_left husi hB)

theorem fullAnnulus_event_excess_tendsto (n : ℕ) {ι : Type*} {l : Filter ι}
    {u : ι → ℝ} {y : ι → Space} {B w δ : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᶠ i in l, 0 < u i) (hu0 : Tendsto u l (𝓝 0))
    (hy : ∀ᶠ i in l, ‖y i‖ ≤ B*u i) (hw : w < 1/10) (hδ : 0 ≤ δ) :
    Tendsto (fun i => dyadicUniformEventBudget (u i) ((u i)^n) δ*
      (localCellRadius (y i))^(7-w)) l (𝓝 0) := by
  have he := (polynomial_probability_budget_tendsto n (by linarith : (2.02:ℝ) < 7-w) δ).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu0,hu⟩)
  have hb : Tendsto (fun i => B^(7-w)*
      (dyadicUniformEventBudget (u i) ((u i)^n) δ*(u i)^(7-w))) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using he.const_mul (B^(7-w))
  have hn : ∀ᶠ i in l, 0 ≤ dyadicUniformEventBudget (u i) ((u i)^n) δ := by
    filter_upwards [hu,hu0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi hi1
    exact dyadicUniformEventBudget_nonneg hi (pow_pos hi _) (pow_le_one₀ hi.le hi1.le) hδ
  apply squeeze_zero' _ _ hb
  · filter_upwards [hn] with i hi
    exact mul_nonneg hi (Real.rpow_nonneg (by unfold localCellRadius; positivity) _)
  · filter_upwards [hu,hy,hn] with i hi hyi hni
    calc
      _ ≤ dyadicUniformEventBudget (u i) ((u i)^n) δ*(B*u i)^(7-w) := by
        apply mul_le_mul_of_nonneg_left _ hni
        exact Real.rpow_le_rpow (by unfold localCellRadius; positivity)
          (fullAnnulus_local_radius_le (mul_nonneg hB hi.le) hyi) (by linarith)
      _ = _ := by rw [Real.mul_rpow hB hi.le]; ring

end
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpandedAnnulusGeometry
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier CoulombObservation

lemma masterWidth_relative_tendsto_half {ι : Type*} {l : Filter ι}
    {c₁ : ℝ} (hc : 0 < c₁) {r₀ s : ι → ℝ} {y : ι → Space}
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0)) (hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖) :
    Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i))
      l (𝓝 0) := by
  have ht : Tendsto (fun i => (c₁*200000)*(s i)^masterExponent) l (𝓝 0) := by
    simpa only [mul_zero] using (hs0.rpow_const_nhds_zero masterExponent_pos).const_mul (c₁*200000)
  apply squeeze_zero' _ _ ht
  · filter_upwards [hr,hs] with i hri hsi
    exact div_nonneg (masterWidth_pos hc hri hsi _).le (by unfold localCellRadius; positivity)
  · filter_upwards [hr,hs,hry] with i hri hsi hryi
    have hyi : y i ≠ 0 := norm_pos_iff.mp (by linarith)
    have ha := localCellRadius_pos hyi
    apply (div_le_iff₀ ha).mpr
    have hh := masterWidth_upper hc.le hri hsi (y i)
    have hmax : masterBaseDistance (r₀ i) (y i) ≤ 2*‖y i‖ := by
      exact max_le (by linarith [norm_nonneg (y i)]) hryi
    calc
      _ ≤ c₁*(2*‖y i‖)*(s i)^masterExponent := hh.trans (by gcongr)
      _ = _ := by unfold localCellRadius; ring

lemma half_band_observation_width_bound {u : ℝ} {y : Space} (hu : 0 < u) (hy : u/2 ≤ ‖y‖) :
    0 ≤ u^(101/100:ℝ) ∧
      u^(101/100:ℝ) ≤ (200000:ℝ)^(101/100:ℝ)*(localCellRadius y)^(101/100:ℝ) := by
  constructor
  · positivity
  · have hh := Real.rpow_le_rpow hu.le (by linarith : u ≤ 2*‖y‖)
      (by norm_num : (0:ℝ) ≤ 101/100)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [←Real.mul_rpow (by norm_num) (by unfold localCellRadius; positivity)]
    congr 1
    unfold localCellRadius
    ring

theorem expandedAnnulus_inverse_numerics_eventually {ι : Type*} {l : Filter ι}
    {r₀ u s : ι → ℝ} {y : ι → Space} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i) :
    ∀ᶠ i in l,
      InverseFiniteGeometry c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ)) (y i) ∧
      LowInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      HighInverseNumerics c₁ (r₀ i) (s i) ((u i)^(101/100:ℝ))
        (dyadicUniformEventBudget (u i) ((u i)^40) δ) h xi quantumInverseCountConstant (y i) ∧
      universalCellCountConstant*(localOffsetMass (dyadicUniformEventBudget (u i) ((u i)^40) δ) (y i))^2 <
        (quantumInverseCountConstant/(localCellRadius (y i))^3)^2 := by
  have hBp : 0 < B := lt_of_lt_of_le zero_lt_one hB
  let c₂ : ℝ := c₁/B^(1+masterExponent)
  have hc₂ : 0 < c₂ := div_pos hc (Real.rpow_pos_of_pos hBp _)
  have hr := hband.mono fun _ hi => hi.1
  have hu := hband.mono fun _ hi => hi.1.trans_le hi.2.1
  have hs := hband.mono fun _ hi => (hi.1.trans_le hi.2.1).trans_le hi.2.2.1
  have hus := hband.mono fun _ hi => hi.2.2.1
  have hyl := hband.mono fun _ hi => hi.2.2.2.1
  have hyu := hband.mono fun _ hi => hi.2.2.2.2
  have hry : ∀ᶠ i in l, r₀ i ≤ 2*‖y i‖ := hband.mono fun _ hi => by
    linarith [hi.2.1,hi.2.2.2.1]
  have hu0 : Tendsto u l (𝓝 0) := squeeze_zero' (hu.mono fun _ hi => hi.le) hus hs0
  have hy : ∀ᶠ i in l, y i ≠ 0 := by
    filter_upwards [hu,hyl] with i hui hyi
    exact norm_pos_iff.mp (by linarith)
  have ha := hy.mono fun _ hi => localCellRadius_pos hi
  have ha0 := fullAnnulus_local_radius_tendsto hBp.le hs0 hu hus hyu
  have hwidth := masterWidth_relative_tendsto_half hc hr hs hs0 hry
  have hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤
      masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hy,hu,hus,hyu] with i hyi hui husi hyui
    apply masterWidth_fullAnnulus_lower hc.le hB hyi
    exact (fullAnnulus_local_radius_le (mul_nonneg hBp.le hui.le) hyui).trans
      (mul_le_mul_of_nonneg_left husi hBp.le)
  have hell : ∀ᶠ i in l, 0 ≤ (u i)^(101/100:ℝ) ∧
      (u i)^(101/100:ℝ) ≤ (200000:ℝ)^(101/100:ℝ)*(localCellRadius (y i))^(101/100:ℝ) := by
    filter_upwards [hu,hyl] with i hui hyi
    exact half_band_observation_width_bound hui hyi
  have hD := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num [masterExponent] : masterExponent < 1/10) hδ
  have hDgap := fullAnnulus_event_excess_tendsto 40 (δ := δ) hBp.le hu hu0 hyu
    (by norm_num : (1/100:ℝ) < 1/10) hδ
  have hgeom := inverse_geometry_eventually ha ha0 hwidth
    (observation_relative_tendsto (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) ha ha0 hell)
  have hlow := low_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) (by linarith : 0 ≤ h) hxi
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hhigh := high_inverse_numerics_eventually_of_width (C := quantumInverseCountConstant) hc hcL hc₂
    (by positivity : 0 ≤ (200000:ℝ)^(101/100:ℝ)) hxi hxih
    hy ha0 hr hs hs0 hw hwidth hell hD hDgap
  have hcount := inverse_count_margin_eventually hy ha0 hD
  filter_upwards [hgeom,hlow,hhigh,hcount] with i hi hlo hhi hci
  refine ⟨?_,hlo,hhi,hci⟩
  rcases hi with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

end
open Filter Set
open scoped Topology
open CoulombAnalysis CoulombBarrier

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailInitialEventuallyBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_TailInitialEventually_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

lemma tailPolynomialThreshold_pos {r : ℝ} (hr : 0 < r) {K : ℕ} (j : Fin (K+1)) :
    0 < tailPolynomialThreshold r j := by
  unfold tailPolynomialThreshold
  positivity

end Work_TailInitialEventually_barrier_scope

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped BigOperators Topology

open CoulombAtom CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterWidth masterKernel originalRawKernel physicalObservationLaw
  originalDatum jointMasterPosterior

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_PointInverseEventsCell
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoulombAtom
section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

theorem TailTiltState.point_inverse_events_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s h xi : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hxi : 0 < xi) (hxih : xi < 2*h)
    (j : Fin (K+1)) (k : Fin K) (hk : j.val ≤ k.val)
    {y : Space} (hy : y ≠ 0)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (dyadicObservationWidth r k) y)
    (hlow : LowInverseNumerics c₁ r₀ s (dyadicObservationWidth r k)
      (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) h xi quantumInverseCountConstant y)
    (hhigh : HighInverseNumerics c₁ r₀ s (dyadicObservationWidth r k)
      (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) h xi quantumInverseCountConstant y)
    (hcount : universalCellCountConstant*
      (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)^2 <
      (quantumInverseCountConstant/(localCellRadius y)^3)^2) :
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | (h+xi)/(localCellRadius y)^4 ≤ originalQueryField F Z lam r j c₁ r₀ s z y ∧
        originalQueryDensity F r j c₁ r₀ s z y ≤ localTFResponse h/(localCellRadius y)^6} < 2*p₀ j ∧
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | originalQueryField F Z lam r j c₁ r₀ s z y ≤ (h-xi)/(localCellRadius y)^4 ∧
        localTFResponse h/(localCellRadius y)^6 ≤ originalQueryDensity F r j c₁ r₀ s z y} < 2*p₀ j := by
  have ha := localCellRadius_pos hy
  have hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y := by
    linarith [hgeom.master_fit, hgeom.cut_pos]
  have hw := masterWidth_pos hc hr₀ hs y
  have hHlo : 0 ≤ (h+xi/2)/(localCellRadius y)^4 := div_nonneg (by linarith) (by positivity)
  have hHhi : 0 ≤ (h-xi/2)/(localCellRadius y)^4 := div_nonneg (by linarith) (by positivity)
  have heta : 0 < (localCellRadius y)^(-7+(1/100:ℝ)) := Real.rpow_pos_of_pos ha _
  have hm : 0 < (localCellRadius y)^(-3+(1/100:ℝ)) := Real.rpow_pos_of_pos ha _
  have hlo := hstate.low_inverse_event_of_cell hZ hlam hr h₀ hc hcL hr₀ hs hs1 j k hk hy
    hgeom.radius_le hcell hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit
    hgeom.probe_margin hgeom.collar (by linarith [hgeom.master_fit]) hHlo heta
    (fun t ht => (hlow t ht).1) (fun t ht => (hlow t ht).2)
  have hhi := hstate.high_inverse_event_of_cell hZ hlam hr h₀ hc hcL hr₀ hs hs1 j k hk hy
    hgeom.radius_le hcell hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit
    hgeom.probe_margin hgeom.collar hgeom.master_fit hHhi heta hm
    (fun t ht => (hhigh t ht).1) (fun t ht => (hhigh t ht).2.1) (fun t ht => (hhigh t ht).2.2)
  have hcnt := hstate.local_count_failure hZ hlam hr j k hk hy
    (2*masterWidth c₁ r₀ s y+Real.sqrt 3*((localCellRadius y)^(6/5:ℝ)+dyadicObservationWidth r k))
    (quantumInverseCountConstant/(localCellRadius y)^3)
    (div_nonneg quantumInverseCountConstant_pos.le (by positivity))
    (by linarith only [hgeom.count_fit]) hcount
  constructor
  · apply measureReal_remove_cutoff (physicalObservationLaw (graphRawLaw F) K) (hQ := hcnt)
    unfold originalQueryField originalQueryDensity
    simpa only [mem_ofPred_eq,and_assoc,Measure.real] using hlo
  · apply measureReal_remove_cutoff (physicalObservationLaw (graphRawLaw F) K) (hQ := hcnt)
    unfold originalQueryField originalQueryDensity
    simpa only [mem_ofPred_eq,and_assoc,Measure.real] using hhi

end

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpandedAnnulusInverse
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

 theorem actual_expandedAnnulus_inverse_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {y : ι → Space} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {j : ∀ i, Fin (K i)} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0))
    (hband : ∀ᶠ i in l, 0 < r₀ i ∧ (2:ℝ)^(j i).val*r₀ i ≤ s i ∧
      ((2:ℝ)^(j i).val*r₀ i)/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*((2:ℝ)^(j i).val*r₀ i))
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i) (tailPolynomialThreshold (r₀ i)) δ (F i)) :
    ∀ᶠ i in l,
    (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
      {z | (h+xi)/(localCellRadius (y i))^4 ≤ originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i) ∧
        originalQueryDensity (F i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i) ≤ localTFResponse h/(localCellRadius (y i))^6} <
        2*((2:ℝ)^(j i).val*r₀ i)^40 ∧
    (physicalObservationLaw (graphRawLaw (F i)) (K i)).real
      {z | originalQueryField (F i) (Z i) (lam i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i) ≤ (h-xi)/(localCellRadius (y i))^4 ∧
        localTFResponse h/(localCellRadius (y i))^6 ≤ originalQueryDensity (F i) (r₀ i) (j i) c₁ (r₀ i) (s i) z (y i)} <
        2*((2:ℝ)^(j i).val*r₀ i)^40 := by
  let u := fun i => (2:ℝ)^(j i).val*r₀ i
  have hb : ∀ᶠ i in l, 0 < r₀ i ∧ r₀ i ≤ u i ∧ u i ≤ s i ∧
      u i/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ B*u i := by
    filter_upwards [hband] with i hi
    refine ⟨hi.1,?_,hi.2⟩
    dsimp only [u]
    exact le_mul_of_one_le_left hi.1.le (one_le_pow₀ (by norm_num))
  have hn := expandedAnnulus_inverse_numerics_eventually hB hc hcL hxi hxih hδ hs0 hb
  have hs1 := hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hb,hn,hs1,hstate] with i hi hni hsi hFi
  have hui : 0 < u i := hi.1.trans_le hi.2.1
  have hsy : 0 < s i := hui.trans_le hi.2.2.1
  have hy : y i ≠ 0 := norm_pos_iff.mp (by linarith [hi.2.2.2.1])
  have hpow : tailPolynomialThreshold (r₀ i) (j i).castSucc = (u i)^40 := by
    unfold tailPolynomialThreshold
    exact min_eq_right (pow_le_one₀ hui.le (hi.2.2.1.trans hsi.le))
  have hell : dyadicObservationWidth (r₀ i) (j i) = (u i)^(101/100:ℝ) := by
    unfold dyadicObservationWidth u
    norm_num
  have hh := hFi.2.2.point_inverse_events_of_cell hFi.1 hFi.2.1 hi.1
    (tailPolynomialThreshold_pos hi.1) hc hcL hi.1 hsy hsi.le hxi hxih
    (j i).castSucc (j i) (by rfl) hy
    (by simpa only [hell] using hni.1)
    (by simpa only [Fin.val_castSucc,hpow,hell] using hni.2.1)
    (by simpa only [Fin.val_castSucc,hpow,hell] using hni.2.2.1)
    (by simpa only [Fin.val_castSucc,hpow] using hni.2.2.2)
  simpa only [Fin.val_castSucc,hpow] using hh

end
open MeasureTheory Filter Set
open scoped Topology BigOperators
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem actual_expandedAnnulus_inverse_uniform_eventually_oai {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {B c₁ h xi δ : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hxi : 0 < xi) (hxih : xi < 2*h) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i) (tailPolynomialThreshold (r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ (j : Fin (K i)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i →
      ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ → ‖y‖ ≤ B*((2:ℝ)^j.val*r₀ i) →
      OriginalPointInverseBounds (F i) (Z i) (lam i) (r₀ i) (s i) c₁ h xi j y := by
  let A : ι → Type := fun i => {p : Fin (K i) × Space //
    (2:ℝ)^p.1.val*r₀ i ≤ s i ∧
    ((2:ℝ)^p.1.val*r₀ i)/2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ B*((2:ℝ)^p.1.val*r₀ i)}
  let π : (Σ i, A i) → ι := Sigma.fst
  let L : Filter (Σ i, A i) := Filter.comap π l
  have ht : Tendsto π L l := tendsto_comap
  have hb : ∀ᶠ q in L, 0 < r₀ (π q) ∧
      (2:ℝ)^q.2.1.1.val*r₀ (π q) ≤ s (π q) ∧
      ((2:ℝ)^q.2.1.1.val*r₀ (π q))/2 ≤ ‖q.2.1.2‖ ∧
      ‖q.2.1.2‖ ≤ B*((2:ℝ)^q.2.1.1.val*r₀ (π q)) := by
    filter_upwards [ht.eventually hr₀] with q hq
    exact ⟨hq,q.2.2⟩
  have hh := actual_expandedAnnulus_inverse_eventually
    (F := fun q : Σ i, A i => F (π q)) (j := fun q => q.2.1.1)
    hB hc hcL hxi hxih hδ (hs0.comp ht) hb (ht.eventually hstate)
  have he := Filter.eventually_comap.mp hh
  filter_upwards [he] with i hi
  intro j y hjs hyl hyu
  exact hi ⟨i,⟨(j,y),hjs,hyl,hyu⟩⟩ rfl

end CoulombAtom

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually_oai.{u_1} := @OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually_oai.{u_1}

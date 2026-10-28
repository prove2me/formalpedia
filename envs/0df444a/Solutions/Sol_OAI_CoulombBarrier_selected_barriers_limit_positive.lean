-- Prove2me | solution 1 for OAI.CoulombBarrier.selected_barriers_limit_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:12:39.361441+00:00
-- url     : https://prove2.me/submissions/ed9ed6cb-c316-40c0-ab61-19a40281c81f

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C005
import Definitions.Def_OAIQ071C006

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierWeakMaxGeneralBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology Convolution BigOperators Manifold

open CoulombAnalysis CoulombPDE CoulombAtom

lemma locallyIntegrable_mul_test {h φ : TFSpace → ℝ} (hh : LocallyIntegrable h)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x => h x*φ x) :=
  hh.integrable_smul_right_of_hasCompactSupport hφ hcφ

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNonlinearBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma WeakLaplacianLowerOn.mono_set {U V : Set TFSpace} {u h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hVU : V ⊆ U) : WeakLaplacianLowerOn V u h :=
  fun φ hφ hc hs hn => hw φ hφ hc (hs.trans hVU) hn

lemma WeakLaplacianLowerOn.congr_field {U : Set TFSpace} {u v h : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (he : ∀ x ∈ U, u x = v x) :
    WeakLaplacianLowerOn U v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · rw [hx,mul_zero,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakLaplacianLowerOn.source_mono_ae {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ᵐ x, x ∈ U → h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := by
  intro φ hφ hc hs hn
  apply le_trans _ (hw φ hφ hc hs hn)
  apply integral_mono_ae (locallyIntegrable_mul_test hh' hφ.continuous hc)
    (locallyIntegrable_mul_test hh hφ.continuous hc)
  filter_upwards [hle] with x hx
  by_cases hφx : φ x = 0
  · simp only [hφx,mul_zero,le_refl]
  · exact mul_le_mul_of_nonneg_right (hx (hs (subset_tsupport φ hφx))) (hn x)

lemma WeakLaplacianLowerOn.source_mono {U : Set TFSpace} {u h h' : TFSpace → ℝ}
    (hw : WeakLaplacianLowerOn U u h) (hh : LocallyIntegrable h)
    (hh' : LocallyIntegrable h') (hle : ∀ x ∈ U, h' x ≤ h x) :
    WeakLaplacianLowerOn U u h' := hw.source_mono_ae hh hh' (Eventually.of_forall hle)

lemma semilinear_source_locallyIntegrable {g χ u : TFSpace → ℝ} {F : ℝ → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hF : Continuous F) (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*F (u x)) := by
  have hχl : LocallyIntegrable χ :=
    (memLp_top_of_bound hχ.aestronglyMeasurable 1 (Eventually.of_forall hbχ)).locallyIntegrable le_top
  exact hg.add (LocallyIntegrable.mul_continuous (hF.comp hu) hχl)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierConditionalBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CoulombBarrier

lemma reaction_monotone {k : ℝ} (hk : 0 ≤ k) : Monotone (reaction k) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right _ _) (max_le_max hst le_rfl) (by norm_num))
    (by positivity)

lemma reaction_continuous (k : ℝ) : Continuous (reaction k) := by
  apply continuous_const.mul
  exact (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr (by norm_num))

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNuclearBarrier
attribute [-instance] _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma nuclearField_locallyIntegrable (Z : ℝ) : LocallyIntegrable (nuclearField Z) := by
  change LocallyIntegrable (fun x : TFSpace => Z*‖x‖⁻¹)
  exact newtonInverse_locallyIntegrable.smul Z

lemma clippedNuclearField_continuous (Z : ℝ) {R : ℝ} (hR : 0 < R) :
    Continuous (clippedNuclearField Z R) := by
  exact continuous_const.div (continuous_const.max continuous_norm)
    (fun x => ne_of_gt (hR.trans_le (le_max_left R ‖x‖)))

lemma weighted_clipped_reaction (Z R : ℝ) {χ : TFSpace → ℝ}
    (hχ : ∀ x, ‖x‖ < R → χ x = 0) (F : ℝ → ℝ) (t : ℝ) (x : TFSpace) :
    χ x*F (nuclearField Z x+t) = χ x*F (clippedNuclearField Z R x+t) := by
  by_cases hx : ‖x‖ < R
  · rw [hχ x hx,zero_mul,zero_mul]
  · simp only [clippedNuclearField,max_eq_right (le_of_not_gt hx),nuclearField]

lemma nuclearField_weak_laplacian (Z : ℝ) {φ : TFSpace → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, nuclearField Z x*Δ φ x) = -(4*Real.pi*Z)*φ 0 := by
  have h := tfPotential_laplacian hφ hc (0 : TFSpace)
  have he : (fun x => nuclearField Z x*Δ φ x) = fun x => Z*(Δ φ x/‖x‖) := by
    funext x
    dsimp only [nuclearField]
    ring
  rw [he,integral_const_mul]
  simp only [tfPotential,zero_sub,norm_neg] at h
  rw [h]
  ring

theorem weakNuclearLower_add_iff {U : Set TFSpace} (Z : ℝ) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h ↔
      WeakLaplacianLowerOn U u h := by
  have he (φ : TFSpace → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
      (∫ x, (nuclearField Z x+u x)*Δ φ x) =
        -(4*Real.pi*Z)*φ 0+(∫ x, u x*Δ φ x) := by
    simp_rw [add_mul]
    rw [integral_add
      (locallyIntegrable_mul_test (nuclearField_locallyIntegrable Z)
        (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc))
      (locallyIntegrable_mul_test hu (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)),
      nuclearField_weak_laplacian Z hφ hc]
  constructor
  · intro hw φ hφ hc hs hn
    have ht := hw φ hφ hc hs hn
    rw [he φ hφ hc] at ht
    exact (add_le_add_iff_left _).mp ht
  · intro hw φ hφ hc hs hn
    rw [he φ hφ hc]
    exact add_le_add_right (hw φ hφ hc hs hn) _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BoundedL1PotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma bounded_coulomb_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z/‖x-z‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [hn z]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hd' : 1 ≤ ‖x-z‖ := le_of_not_gt hd
    exact (div_le_self (hn z) hd')

lemma bounded_invSquare_majorant {ρ : TFSpace → ℝ} {M : ℝ}
    (_hM : 0 ≤ M) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x z : TFSpace) :
    ρ z*‖x-z‖⁻¹^2 ≤ M*truncatedInvSquare 1 (x-z)+ρ z := by
  by_cases hd : ‖x-z‖ < 1
  · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr hd)]
    have hh := mul_le_mul_of_nonneg_right (hb z) (sq_nonneg ‖x-z‖⁻¹)
    linarith [hn z]
  · rw [truncatedInvSquare,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hd),mul_zero,zero_add]
    have hi : ‖x-z‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_gt hd)
    have hi0 := inv_nonneg.mpr (norm_nonneg (x-z))
    have hs : ‖x-z‖⁻¹^2 ≤ 1 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs (hn z)).trans_eq (mul_one _)

lemma bounded_L1_potential_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  apply ((hk.const_mul M).add hi).mono' (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/‖x-z‖‖ ≤ M*truncatedCoulomb 1 (x-z)+ρ z
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact bounded_coulomb_majorant hM hn hb x z

lemma bounded_L1_potential_difference {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x y : TFSpace) :
    |tfPotential ρ x-tfPotential ρ y| ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖ := by
  have hpi (w : TFSpace) := bounded_L1_potential_integrable hm hi hM hn hb w
  let A (w z : TFSpace) := M*truncatedInvSquare 1 (w-z)+ρ z
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare 1 (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable 1)
  have hAi (w : TFSpace) : Integrable (A w) := ((hk w).const_mul M).add hi
  have hAm (w : TFSpace) : (∫ z, A w z) = 4*Real.pi*M+∫ z, ρ z := by
    dsimp only [A]
    rw [integral_add ((hk w).const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
      truncatedInvSquare_integral (by norm_num : (0:ℝ) < 1)]
    ring
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hpi x) (hpi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (‖x-y‖/2)*(A x z+A y z) := by
      apply integral_mono_ae ((hpi x).sub (hpi y)).abs (((hAi x).add (hAi y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤ _
      rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
      calc
        _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
          mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
        _ = (‖x-y‖/2)*(ρ z*‖x-z‖⁻¹^2+ρ z*‖y-z‖⁻¹^2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
          (bounded_invSquare_majorant hM hn hb x z) (bounded_invSquare_majorant hM hn hb y z)) (by positivity)
    _ = _ := by
      rw [integral_const_mul,integral_add (hAi x) (hAi y),hAm,hAm]
      ring

lemma bounded_L1_potential_lipschitz {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) :
    LipschitzWith ⟨4*Real.pi*M+∫ z, ρ z,add_nonneg (by positivity) (integral_nonneg hn)⟩ (tfPotential ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖tfPotential ρ x-tfPotential ρ y‖ ≤ (4*Real.pi*M+∫ z, ρ z)*‖x-y‖
  simpa only [Real.norm_eq_abs] using bounded_L1_potential_difference hm hi hM hn hb x y

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BoundedL1PoissonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma bounded_L1_laplacian_pair_integrable {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) (volume.prod volume) := by
  have hΔ := tfLaplacian_continuous hφ
  have hΔc := tfLaplacian_compact hφ hc
  have hj : Measurable (fun z : TFSpace × TFSpace => ρ z.2/‖z.1-z.2‖*Δ φ z.1) :=
    ((hm.comp measurable_snd).div (measurable_fst.sub measurable_snd).norm).mul (hΔ.measurable.comp measurable_fst)
  apply (integrable_prod_iff hj.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => (bounded_L1_potential_integrable hm hi hM hn hb x).mul_const (Δ φ x)),?_⟩
  have hp := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have htest := CoulombBarrier.locallyIntegrable_mul_test hp.locallyIntegrable hΔ.norm hΔc.norm
  have he (x : TFSpace) : (∫ y, ‖ρ y/‖x-y‖*Δ φ x‖) = tfPotential ρ x*‖Δ φ x‖ := by
    simp_rw [norm_mul,Real.norm_of_nonneg (div_nonneg (hn _) (norm_nonneg _))]
    exact integral_mul_const _ _
  simpa only [he] using htest

theorem bounded_L1_weak_poisson {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    {φ : TFSpace → ℝ} (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, tfPotential ρ x*Δ φ x) = -(4*Real.pi)*(∫ x, ρ x*φ x) := by
  calc
    _ = ∫ x, ∫ y, ρ y/‖x-y‖*Δ φ x := by simp only [integral_mul_const,tfPotential]
    _ = ∫ y, ∫ x, ρ y/‖x-y‖*Δ φ x :=
      integral_integral_swap (bounded_L1_laplacian_pair_integrable hm hi hM hn hb hφ hc)
    _ = ∫ y, ρ y*tfPotential (Δ φ) y := by
      apply integral_congr_ae
      exact ae_of_all _ fun y => by
        change (∫ x, ρ y/‖x-y‖*Δ φ x) = ρ y*(∫ x, Δ φ x/‖y-x‖)
        rw [←integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by dsimp only; rw [norm_sub_rev]; ring
    _ = _ := by
      simp_rw [tfPotential_laplacian hφ hc]
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring

end CoulombAnalysis

end Work_BoundedL1Poisson_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakPositiveComparisonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

theorem weak_subharmonic_positive_ball {u : Space → ℝ} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall 0 R))
    (hb : ∀ x : Space, ‖x‖ = R → u x ≤ 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R ∩ {x | 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x) : ∀ x ∈ closedBall (0 : Space) R, u x ≤ 0 := by
  intro x hx
  by_contra! hux
  let e := u x/(2*(R^2+1))
  have he : 0 < e := div_pos hux (by positivity)
  have heq : e*(2*(R^2+1)) = u x := div_mul_cancel₀ _ (by positivity)
  let w : Space → ℝ := fun z => u z+e*(‖z‖^2-R^2)
  have hwcont : ContinuousOn w (closedBall 0 R) :=
    hu.add (continuousOn_const.mul ((continuous_norm.pow 2).continuousOn.sub continuousOn_const))
  have hwx : 0 < w x := by
    dsimp only [w]
    nlinarith [sq_nonneg ‖x‖,mul_nonneg he.le (sq_nonneg ‖x‖),sq_nonneg R]
  obtain ⟨y,hy,hmax⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn ⟨x,hx⟩ hwcont
  have hwy : 0 < w y := hwx.trans_le (hmax hx)
  have hyi : y ∈ ball (0 : Space) R := by
    have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
    by_contra hn
    have heqR : ‖y‖ = R := le_antisymm hyR (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hn))
    have hub := hb y heqR
    dsimp only [w] at hwy
    rw [heqR,sub_self,mul_zero,add_zero] at hwy
    exact (not_lt_of_ge hub) hwy
  have huyp : 0 < u y := by
    have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hsq := pow_le_pow_left₀ (norm_nonneg y) hyR 2
    have hneg := mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr hsq)
    dsimp only [w] at hwy
    linarith
  have hyn : closedBall (0 : Space) R ∈ 𝓝 y :=
    mem_of_superset (isOpen_ball.mem_nhds hyi) ball_subset_closedBall
  have hnb : ball (0 : Space) R ∩ {z | 0 < u z} ∈ 𝓝 y :=
    inter_mem (isOpen_ball.mem_nhds hyi)
      ((hu.continuousAt hyn).preimage_mem_nhds (Ioi_mem_nhds huyp))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnb
  have hsub : closedBall y (r/2) ⊆ ball (0 : Space) R ∩ {z | 0 < u z} :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrs
  apply weak_laplacian_no_positive_at_max_local
    (hwcont.mono (hsub.trans (inter_subset_left.trans ball_subset_closedBall)))
    (half_pos hr) (mul_pos (by norm_num : (0:ℝ) < 6) he)
  · intro z hz
    exact hmax (ball_subset_closedBall (hsub (ball_subset_closedBall hz)).1)
  · intro g hg hcg hs hn
    have hs' : tsupport g ⊆ ball (0 : Space) R ∩ {z | 0 < u z} :=
      hs.trans (ball_subset_closedBall.trans hsub)
    have hui := continuousOn_mul_integrable_support (isCompact_closedBall (0 : Space) R)
      hu (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans (inter_subset_left.trans ball_subset_closedBall)))
    change 6*e*(∫ z, g z) ≤ ∫ z, (u z+e*(‖z‖^2-R^2))*Δ g z
    rw [quadratic_weak_pairing hg hcg hui]
    linarith only [hw g hg hcg hs' hn]

end Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTowerBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSourceTower_barrier_scope

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped BigOperators Topology

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma outerCoefficient_measurable (R : ℝ) : Measurable (outerCoefficient R) :=
  Measurable.ite (measurableSet_le measurable_const continuous_norm.measurable)
    measurable_const measurable_const

lemma outerCoefficient_bound (R : ℝ) (x : TFSpace) : ‖outerCoefficient R x‖ ≤ 1 := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_nonneg (R : ℝ) (x : TFSpace) : 0 ≤ outerCoefficient R x := by
  unfold outerCoefficient
  split_ifs <;> norm_num

lemma outerCoefficient_zero (R : ℝ) (x : TFSpace) (hx : ‖x‖ < R) :
    outerCoefficient R x = 0 := ite_eq_right (not_le_of_gt hx)

end Work_BarrierSourceTower_barrier_scope

open Set Filter Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierOuterWeakBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric InnerProductSpace
open scoped Topology ContDiff

open CoulombAnalysis

lemma WeakNuclearLowerOn.congr_field {U : Set TFSpace} {Z : ℝ} {u v h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, u x = v x) :
    WeakNuclearLowerOn U Z v h := by
  intro φ hφ hc hs hn
  calc
    _ ≤ ∫ x, u x*Δ φ x := hw φ hφ hc hs hn
    _ = _ := integral_congr_ae (ae_of_all _ fun x => by
      dsimp only
      by_cases hx : Δ φ x = 0
      · simp only [hx,mul_zero]
      · rw [he x (hs (tfLaplacian_support hφ hx))])

lemma WeakNuclearLowerOn.congr_source {U : Set TFSpace} {Z : ℝ} {u h h' : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn U Z u h) (he : ∀ x ∈ U, h x = h' x) :
    WeakNuclearLowerOn U Z u h' := by
  intro φ hφ hc hs hn
  have hh : (∫ x, h' x*φ x) = ∫ x, h x*φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : φ x = 0
    · simp only [hx,mul_zero]
    · rw [he x (hs (subset_tsupport φ hx))]
  rw [hh]
  exact hw φ hφ hc hs hn

end Work_BarrierOuterWeak_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff

open CoulombAnalysis

lemma nuclear_source_locallyIntegrable (Z k : ℝ) {r : ℝ} (hr : 0 < r)
    {g χ u : TFSpace → ℝ} (hg : LocallyIntegrable g) (hχ : Measurable χ)
    (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hu : Continuous u) :
    LocallyIntegrable (fun x => g x+χ x*reaction k (nuclearField Z x+u x)) := by
  simp_rw [weighted_clipped_reaction Z r hzero]
  exact semilinear_source_locallyIntegrable hg hχ hbχ (reaction_continuous k)
    ((clippedNuclearField_continuous Z hr).add hu)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Metric
open scoped Topology

open CoulombAtom CoulombAnalysis

lemma innerSource_locallyIntegrable {μ p : TFSpace → ℝ}
    (hμ : LocallyIntegrable μ) (hp : LocallyIntegrable p) (R : ℝ) :
    LocallyIntegrable (innerSource R μ p) := by
  have hi := hμ.indicator (s := {x : TFSpace | ‖x‖ < R})
    (isOpen_lt continuous_norm continuous_const).measurableSet
  exact (hi.sub hp).smul (4*Real.pi)

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierQuantitativeStepBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom CoulombAnalysis

theorem monotone_reaction_comparison_ball {u v L χ : TFSpace → ℝ}
    {f : ℝ → ℝ} {R c lam : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hL : ∀ x, 0 ≤ L x) (hχ : ∀ x, 0 ≤ χ x) (hf : Monotone f)
    (hcont : ContinuousOn (fun x => u x-v x-L x) (closedBall 0 R))
    (hb : ∀ x : TFSpace, ‖x‖ = R → u x-v x-L x ≤ c)
    (hw : WeakLaplacianLowerOn (ball 0 R) (fun x => u x-v x-L x)
      (fun x => χ x*(f (u x)-f (v x-lam)))) :
    ∀ x ∈ closedBall (0 : TFSpace) R, u x-v x-L x ≤ c := by
  have hcmp := weak_subharmonic_positive_ball hR (hcont.sub continuousOn_const)
    (fun x hx => sub_nonpos.mpr (hb x hx)) (fun g hg hcg hs hn => ?_)
  · intro x hx
    exact sub_nonpos.mp (hcmp x hx)
  · have hs' : tsupport g ⊆ ball (0 : TFSpace) R := hs.trans inter_subset_left
    have hu := continuousOn_mul_integrable_support (isCompact_closedBall (0 : TFSpace) R)
      hcont (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans ball_subset_closedBall))
    have hgi : Integrable (Δ g) :=
      (tfLaplacian_continuous hg).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg)
    have he : (∫ x, (u x-v x-L x-c)*Δ g x) = ∫ x, (u x-v x-L x)*Δ g x := by
      calc
        _ = ∫ x, (u x-v x-L x)*Δ g x-c*Δ g x := by
          apply integral_congr_ae
          exact ae_of_all _ fun x => by ring
        _ = _ := by
          rw [integral_sub hu (hgi.const_mul c),integral_const_mul,compact_laplacian_mass hg hcg,mul_zero,sub_zero]
    change 0 ≤ ∫ x, (u x-v x-L x-c)*Δ g x
    rw [he]
    apply le_trans _ (hw g hg hcg hs' hn)
    apply integral_nonneg
    intro x
    by_cases hx : g x = 0
    · simp only [hx,mul_zero,Pi.zero_apply,le_refl]
    · have hpos := (hs (subset_tsupport g hx)).2
      have hvu : v x-lam ≤ u x := by
        change 0 < u x-v x-L x-c at hpos
        linarith [hL x]
      exact mul_nonneg (mul_nonneg (hχ x) (sub_nonneg.mpr (hf hvu))) (hn x)

theorem WeakLaplacianLowerOn.add_bounded_L1_potential
    {U : Set TFSpace} {u h ρ : TFSpace → ℝ}
    (hu : LocallyIntegrable u) (hh : LocallyIntegrable h)
    (hw : WeakLaplacianLowerOn U u h) (hm : Measurable ρ) (hi : Integrable ρ)
    {M : ℝ} (hM : 0 ≤ M) (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) (b : ℝ) :
    WeakLaplacianLowerOn U (fun x => u x+b*tfPotential ρ x)
      (fun x => h x-b*(4*Real.pi)*ρ x) := by
  intro g hg hcg hs hgn
  have hΔ := tfLaplacian_continuous hg
  have hcΔ := tfLaplacian_compact hg hcg
  have hui := locallyIntegrable_mul_test hu hΔ hcΔ
  have hhi := locallyIntegrable_mul_test hh hg.continuous hcg
  have hρi := locallyIntegrable_mul_test hi.locallyIntegrable hg.continuous hcg
  have hpi := locallyIntegrable_mul_test
    (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.locallyIntegrable hΔ hcΔ
  have hleft : (∫ x, (h x-b*(4*Real.pi)*ρ x)*g x) =
      (∫ x, h x*g x)-b*(4*Real.pi)*(∫ x, ρ x*g x) := by
    calc
      _ = ∫ x, h x*g x-(b*(4*Real.pi))*(ρ x*g x) := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => by ring
      _ = _ := by
        rw [integral_sub hhi (hρi.const_mul (b*(4*Real.pi))),integral_const_mul]
  have hright : (∫ x, (u x+b*tfPotential ρ x)*Δ g x) =
      (∫ x, u x*Δ g x)-b*(4*Real.pi)*(∫ x, ρ x*g x) := by
    simp_rw [add_mul,mul_assoc]
    rw [integral_add hui (hpi.const_mul b),integral_const_mul,
      bounded_L1_weak_poisson hm hi hM hn hb hg hcg]
    ring
  rw [hleft,hright]
  exact sub_le_sub_right (hw g hg hcg hs hgn) _

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierTransferPoissonBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_weak {a ρ p q : TFSpace → ℝ} {Z k r S lam M P Q : ℝ}
    (hr : 0 < r) (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x ∈ ball (0 : TFSpace) S, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x) :
    WeakLaplacianLowerOn (ball 0 S) (fun x => a x+tfPotential ρ x-tfPotential (fun y => p y+q y) x)
      (fun x => outerCoefficient r x*(reaction k (nuclearField Z x+a x)-
        reaction k (nuclearField Z x-tfPotential ρ x-lam))) := by
  let χ := outerCoefficient r
  let U : TFSpace → ℝ := fun x => nuclearField Z x+a x
  let F : TFSpace → ℝ := fun x => nuclearField Z x-tfPotential ρ x-lam
  let h : TFSpace → ℝ := fun x => innerSource r ρ p x+χ x*reaction k (U x)
  let e : TFSpace → ℝ := fun x => p x+q x
  have hem : Measurable e := hpm.add hqm
  have hei : Integrable e := hpi.add hqi
  have heN : ∀ x, 0 ≤ e x := fun x => add_nonneg (hpn x) (hqn x)
  have heB : ∀ x, e x ≤ P+Q := fun x => add_le_add (hpb x) (hqb x)
  have hePQ : 0 ≤ P+Q := add_nonneg hP hQ
  have hpot := (bounded_L1_potential_lipschitz hρm hρi hM hρn hρb).continuous
  have hhs : LocallyIntegrable h := nuclear_source_locallyIntegrable Z k hr
    (innerSource_locallyIntegrable hρi.locallyIntegrable hpi.locallyIntegrable r)
    (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r) ha
  have hzero : LocallyIntegrable (fun _ : TFSpace => (0 : ℝ)) := locallyIntegrable_zero
  have hUr : LocallyIntegrable (fun x => χ x*reaction k (U x)) := by
    simpa only [zero_add] using nuclear_source_locallyIntegrable Z k hr hzero
      (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r) ha
  have hFr : LocallyIntegrable (fun x => χ x*reaction k (F x)) := by
    have hfr₀ : LocallyIntegrable (fun x => χ x*reaction k
        (nuclearField Z x+(-tfPotential ρ x-lam))) := by
      simpa only [zero_add,Pi.sub_apply,Pi.neg_apply,χ] using nuclear_source_locallyIntegrable Z k hr hzero
        (outerCoefficient_measurable r) (outerCoefficient_bound r) (outerCoefficient_zero r)
        (hpot.neg.sub continuous_const)
    have heq : (fun x => χ x*reaction k (nuclearField Z x+(-tfPotential ρ x-lam))) =
        (fun x => χ x*reaction k (F x)) := by
      funext x
      congr 1
      dsimp only [F]
      congr 1
      ring
    rwa [heq] at hfr₀
  have htarget : LocallyIntegrable (fun x => χ x*(reaction k (U x)-reaction k (F x))) := by
    convert hUr.sub hFr using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Pi.sub_apply,mul_sub]
  have hbase := (weakNuclearLower_add_iff Z ha.locallyIntegrable).mp hw
  have hw₁ := hbase.add_bounded_L1_potential ha.locallyIntegrable hhs hρm hρi hM hρn hρb 1
  have hu₁ : LocallyIntegrable (fun x => a x+1*tfPotential ρ x) :=
    (ha.add (continuous_const.mul hpot)).locallyIntegrable
  have hh₁ : LocallyIntegrable (fun x => h x-1*(4*Real.pi)*ρ x) :=
    hhs.sub (hρi.locallyIntegrable.smul (1*(4*Real.pi)))
  have hw₂ := hw₁.add_bounded_L1_potential hu₁ hh₁ hem hei hePQ heN heB (-1)
  have hh₂ : LocallyIntegrable (fun x => (h x-1*(4*Real.pi)*ρ x)-(-1)*(4*Real.pi)*e x) :=
    hh₁.sub (hei.locallyIntegrable.smul ((-1)*(4*Real.pi)))
  have hs := (hw₂.mono_set (subset_univ (ball (0 : TFSpace) S))).source_mono hh₂ htarget
    (fun x hx => ?_)
  · apply hs.congr_field
    intro x _
    simp only [one_mul,neg_one_mul]
    rfl
  · by_cases hxr : ‖x‖ < r
    · dsimp only [χ,h,e,innerSource,outerCoefficient]
      rw [ite_eq_left hxr,ite_eq_right (not_le_of_gt hxr)]
      nlinarith [Real.pi_pos,mul_nonneg Real.pi_pos.le (hqn x)]
    · have hc := hd x hx (le_of_not_gt hxr)
      dsimp only [χ,h,e,innerSource,outerCoefficient]
      rw [ite_eq_right hxr,ite_eq_left (le_of_not_gt hxr)]
      change 1*(reaction k (U x)-reaction k (F x)) ≤
        (4*Real.pi*(0-p x)+1*reaction k (U x)-1*(4*Real.pi)*ρ x)-(-1)*(4*Real.pi)*(p x+q x)
      change 4*Real.pi*ρ x ≤ reaction k (F x)+4*Real.pi*q x at hc
      linarith

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LaplacianCompDilation
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombPDE

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma laplacian_comp_dilation {f : E → ℝ} (a : ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f (a • x)) : Δ (fun y => f (a • y)) x = a^2 * Δ f (a • x) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (a • y)) x := hf.comp x (contDiffAt_id.const_smul a)
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← second_deriv_line hc]
  have he : (fun t : ℝ => f (a • (x + t • (stdOrthonormalBasis ℝ E) i))) =
      (fun t : ℝ => f (a • x + t • (a • (stdOrthonormalBasis ℝ E) i))) := by
    funext t
    simp only [smul_add, smul_smul, mul_comm]
  rw [he, second_deriv_line hf]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end

open Filter Set Metric Topology InnerProductSpace Laplacian

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTransferBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem barrier_transfer_ball {a ρ p q : TFSpace → ℝ} {Z k r S lam M P Q c : ℝ}
    (hr : 0 < r) (hS : 0 < S) (hlam : 0 ≤ lam) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (ha : Continuous a)
    (hρm : Measurable ρ) (hρi : Integrable ρ) (hM : 0 ≤ M)
    (hρn : ∀ x, 0 ≤ ρ x) (hρb : ∀ x, ρ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r ρ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x ∈ ball (0 : TFSpace) S, r ≤ ‖x‖ →
      4*Real.pi*ρ x ≤ reaction k (nuclearField Z x-tfPotential ρ x-lam)+4*Real.pi*q x)
    (hb : ∀ x : TFSpace, ‖x‖ = S → a x+tfPotential ρ x ≤ c) :
    ∀ x ∈ closedBall (0 : TFSpace) S,
      nuclearField Z x+a x ≤ nuclearField Z x-tfPotential ρ x+
        tfPotential (fun y => p y+q y) x+c := by
  let e : TFSpace → ℝ := fun x => p x+q x
  have hm : Measurable e := hpm.add hqm
  have hi : Integrable e := hpi.add hqi
  have hn : ∀ x, 0 ≤ e x := fun x => add_nonneg (hpn x) (hqn x)
  have hB : ∀ x, e x ≤ P+Q := fun x => add_le_add (hpb x) (hqb x)
  have heN (x : TFSpace) : 0 ≤ tfPotential e x := tfPotential_nonneg (ae_of_all _ hn) x
  have hp := (bounded_L1_potential_lipschitz hρm hρi hM hρn hρb).continuous
  have he := (bounded_L1_potential_lipschitz hm hi (add_nonneg hP hQ) hn hB).continuous
  have hcont : ContinuousOn (fun x => (nuclearField Z x+a x)-
      (nuclearField Z x-tfPotential ρ x)-tfPotential e x) (closedBall 0 S) := by
    convert ((ha.add hp).sub he).continuousOn using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Pi.sub_apply,Pi.add_apply]
    ring
  have hw' : WeakLaplacianLowerOn (ball 0 S)
      (fun x => (nuclearField Z x+a x)-(nuclearField Z x-tfPotential ρ x)-tfPotential e x)
      (fun x => outerCoefficient r x*(reaction k (nuclearField Z x+a x)-
        reaction k (nuclearField Z x-tfPotential ρ x-lam))) := by
    apply (barrier_transfer_weak hr ha hρm hρi hM hρn hρb
      hpm hpi hP hpn hpb hqm hqi hQ hqn hqb hw hd).congr_field
    intro x _
    ring
  have hcmp := monotone_reaction_comparison_ball hS hc hlam heN
    (outerCoefficient_nonneg r) (reaction_monotone hk) hcont (fun x hx => ?_) hw'
  · intro x hx
    have hh := hcmp x hx
    dsimp only [e] at hh
    linarith
  · linarith [hb x hx,heN x]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_NuclearDilationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombPDE

lemma nuclearField_dilation {b : ℝ} (hb : 0 < b) (Z : ℝ) (x : TFSpace) :
    b^4*nuclearField Z (b • x) = nuclearField (b^3*Z) x := by
  simp only [nuclearField,norm_smul,Real.norm_of_nonneg hb.le]
  field_simp

lemma weakNuclearLower_dilation {b Z : ℝ} (hb : 0 < b) {u h : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn univ Z u h) :
    WeakNuclearLowerOn univ (b^3*Z) (fun x => b^4*u (b • x)) (tfDilation b h) := by
  intro φ hφ hc _ hn
  let ψ : TFSpace → ℝ := fun x => φ (b⁻¹ • x)
  have hψ : ContDiff ℝ 2 ψ := hφ.comp (contDiff_id.const_smul b⁻¹)
  have hcψ : HasCompactSupport ψ := hc.comp_smul (inv_ne_zero hb.ne')
  have hi := mul_le_mul_of_nonneg_left
    (hw ψ hψ hcψ (subset_univ _) (fun x => hn _)) (pow_nonneg hb.le 3)
  have heh : (∫ x, tfDilation b h x*φ x) = b^3*(∫ x, h x*ψ x) := by
    have he : (fun x => tfDilation b h x*φ x) =
        fun x => b^6*((fun y => h y*ψ y) (b • x)) := by
      funext x
      simp only [tfDilation,ψ,smul_smul,inv_mul_cancel₀ hb.ne',one_smul]
      ring
    rw [he,integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
      (fun y => h y*ψ y) b (hR := hb.le)]
    rw [show Module.finrank ℝ TFSpace = 3 from space_finrank]
    simp only [smul_eq_mul]
    change b^6*((b^3)⁻¹*(∫ y, h y*ψ y)) = _
    field_simp
  have heu : (∫ x, b^4*u (b • x)*Δ φ x) = b^3*(∫ x, u x*Δ ψ x) := by
    have he : (fun x => u x*Δ ψ x) =
        fun x => (b⁻¹)^2*((fun y => u (b • y)*Δ φ y) (b⁻¹ • x)) := by
      funext x
      rw [show Δ ψ x = (b⁻¹)^2*Δ φ (b⁻¹ • x) from
        laplacian_comp_dilation b⁻¹ x hφ.contDiffAt]
      simp only [smul_smul,mul_inv_cancel₀ hb.ne',one_smul]
      ring
    rw [he,integral_const_mul,Measure.integral_comp_smul_of_nonneg volume
      (fun y => u (b • y)*Δ φ y) b⁻¹ (hR := (inv_pos.mpr hb).le)]
    have hel : (fun x => b^4*u (b • x)*Δ φ x) =
        fun x => b^4*(u (b • x)*Δ φ x) := by funext x; ring
    rw [hel,integral_const_mul]
    rw [show Module.finrank ℝ TFSpace = 3 from space_finrank]
    simp only [smul_eq_mul]
    change b^4*(∫ x, u (b • x)*Δ φ x) =
      b^3*((b⁻¹)^2*(((b⁻¹)^3)⁻¹*(∫ y, u (b • y)*Δ φ y)))
    field_simp
  rw [heh,heu]
  have hz : ψ 0 = φ 0 := by simp [ψ]
  rw [hz] at hi
  calc
    _ = b^3*(-(4*Real.pi*Z)*φ 0+(∫ x, h x*ψ x)) := by ring
    _ ≤ _ := hi

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierDilationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierDilation_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma reaction_dilation {b : ℝ} (hb : 0 < b) (k t : ℝ) :
    reaction k (b^4*t) = b^6*reaction k t := by
  have hm : max (b^4*t) 0 = b^4*max t 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg hb.le 4),mul_zero]
  have hp : (b^4)^(3/2:ℝ) = b^6 := by
    rw [←Real.rpow_natCast b 4,←Real.rpow_mul hb.le]
    norm_num [Real.rpow_natCast]
  rw [reaction,hm,Real.mul_rpow (pow_nonneg hb.le 4) (le_max_right _ _),hp,reaction]
  ring

lemma innerSource_dilation {b : ℝ} (hb : 0 < b) (r : ℝ) (μ p : TFSpace → ℝ)
    (x : TFSpace) : tfDilation b (innerSource r μ p) x =
      innerSource (r/b) (tfDilation b μ) (tfDilation b p) x := by
  have he : ‖b • x‖ < r ↔ ‖x‖ < r/b := by
    rw [norm_smul,Real.norm_of_nonneg hb.le,lt_div_iff₀ hb,mul_comm]
  simp only [tfDilation,innerSource,he]
  split_ifs <;> ring

lemma outerCoefficient_dilation {b : ℝ} (hb : 0 < b) (r : ℝ) (x : TFSpace) :
    outerCoefficient r (b • x) = outerCoefficient (r/b) x := by
  have he : r ≤ ‖b • x‖ ↔ r/b ≤ ‖x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hb.le,div_le_iff₀ hb,mul_comm]
  simp only [outerCoefficient,he]

lemma outerBarrier_dilation {b : ℝ} (hb : 0 < b) (B r : ℝ) (x : TFSpace) :
    b^4*outerBarrier B r (b • x) = outerBarrier B (r/b) x := by
  simp only [outerBarrier,norm_smul,Real.norm_of_nonneg hb.le]
  field_simp

theorem barrier_weak_dilation {b Z k r : ℝ} (hb : 0 < b)
    {a μ p : TFSpace → ℝ}
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r μ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x))) :
    WeakNuclearLowerOn univ (b^3*Z)
      (fun x => nuclearField (b^3*Z) x+b^4*a (b • x))
      (fun x => innerSource (r/b) (tfDilation b μ) (tfDilation b p) x+
        outerCoefficient (r/b) x*reaction k (nuclearField (b^3*Z) x+b^4*a (b • x))) := by
  have hh := weakNuclearLower_dilation hb hw
  have hf (x : TFSpace) : b^4*(nuclearField Z (b • x)+a (b • x)) =
      nuclearField (b^3*Z) x+b^4*a (b • x) := by
    rw [mul_add,nuclearField_dilation hb]
  apply (hh.congr_field (fun x _ => hf x)).congr_source
  intro x _
  change b^6*(innerSource r μ p (b • x)+
    outerCoefficient r (b • x)*reaction k (nuclearField Z (b • x)+a (b • x))) = _
  rw [mul_add,←show tfDilation b (innerSource r μ p) x = b^6*innerSource r μ p (b • x) from rfl,
    innerSource_dilation hb,outerCoefficient_dilation hb]
  rw [←hf, reaction_dilation hb]
  ring

end CoulombBarrier

end Work_BarrierDilation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma local_coulomb_majorant {ρ : TFSpace → ℝ} {x : TFSpace} {b L : ℝ}
    (hb : 0 < b) (hn : ∀ z, 0 ≤ ρ z)
    (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) (z : TFSpace) :
    ρ z/‖x-z‖ ≤ L*truncatedCoulomb b (x-z)+ρ z/b := by
  by_cases hz : ‖x-z‖ < b
  · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr hz)]
    have hh := mul_le_mul_of_nonneg_right (hlocal z hz) (inv_nonneg.mpr (norm_nonneg (x-z)))
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    linarith [mul_nonneg (hn z) (inv_pos.mpr hb).le]
  · rw [truncatedCoulomb,indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hz),mul_zero,zero_add]
    exact div_le_div_of_nonneg_left (hn z) hb (le_of_not_gt hz)

lemma local_bounded_potential_integrable {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) {x : TFSpace} {b L : ℝ} (hb : 0 < b)
    (hn : ∀ z, 0 ≤ ρ z) (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) :
    Integrable (fun z => ρ z/‖x-z‖) := by
  have hk : Integrable (fun z => truncatedCoulomb b (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable b).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable b)
  apply ((hk.const_mul L).add (hi.div_const b)).mono'
    (hm.div (measurable_const.sub measurable_id).norm).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z / ‖x-z‖‖ ≤ L*truncatedCoulomb b (x-z)+ρ z/b
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (norm_nonneg _))]
    exact local_coulomb_majorant hb hn hlocal z

theorem local_bounded_potential_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    (hi : Integrable ρ) {x : TFSpace} {b L : ℝ} (hb : 0 < b)
    (hn : ∀ z, 0 ≤ ρ z) (hlocal : ∀ z, ‖x-z‖ < b → ρ z ≤ L) :
    tfPotential ρ x ≤ 2*Real.pi*L*b^2+(∫ z, ρ z)/b := by
  have hk : Integrable (fun z => truncatedCoulomb b (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable b).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable b)
  calc
    _ ≤ ∫ z, L*truncatedCoulomb b (x-z)+ρ z/b := integral_mono
      (local_bounded_potential_integrable hm hi hb hn hlocal)
      ((hk.const_mul L).add (hi.div_const b)) (local_coulomb_majorant hb hn hlocal)
    _ = _ := by
      rw [integral_add (hk.const_mul L) (hi.div_const b),integral_const_mul,
        integral_div,integral_sub_left_eq_self,truncatedCoulomb,integral_indicator measurableSet_ball]
      simp only [one_div]
      rw [integral_coulomb_ball hb]
      ring

theorem potential_tendsto_zero_of_local_mass {ι : Type*} {F : Filter ι}
    {ρ : ι → TFSpace → ℝ} {L : ι → ℝ} {x : TFSpace} {b : ℝ} (hb : 0 < b)
    (hm : ∀ j, Measurable (ρ j)) (hi : ∀ j, Integrable (ρ j))
    (hn : ∀ j z, 0 ≤ ρ j z)
    (hlocal : ∀ᶠ j in F, ∀ z, ‖x-z‖ < b → ρ j z ≤ L j)
    (hL : Tendsto L F (𝓝 0)) (hMass : Tendsto (fun j => ∫ z, ρ j z) F (𝓝 0)) :
    Tendsto (fun j => tfPotential (ρ j) x) F (𝓝 0) := by
  have hupper : Tendsto (fun j => 2*Real.pi*L j*b^2+(∫ z, ρ j z)/b) F (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_div,zero_add] using
      ((hL.const_mul (2*Real.pi)).mul_const (b^2)).add (hMass.div_const b)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun j => tfPotential_nonneg (ae_of_all _ (hn j)) x
  · filter_upwards [hlocal] with j hj
    exact local_bounded_potential_le (hm j) (hi j) hb (hn j) hj

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_CorrectionPotentialSmallBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma potential_tendsto_zero_of_shrinking_support {ι : Type*} {F : Filter ι}
    {ρ : ι → TFSpace → ℝ} {a : ι → ℝ} {x : TFSpace} (hx : x ≠ 0)
    (hm : ∀ j, Measurable (ρ j)) (hi : ∀ j, Integrable (ρ j))
    (hn : ∀ j z, 0 ≤ ρ j z)
    (hs : ∀ j z, a j < ‖z‖ → ρ j z = 0)
    (ha : Tendsto a F (𝓝 0)) (hMass : Tendsto (fun j => ∫ z, ρ j z) F (𝓝 0)) :
    Tendsto (fun j => tfPotential (ρ j) x) F (𝓝 0) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply potential_tendsto_zero_of_local_mass (L := fun _ => 0)
    (b := ‖x‖/2) (by positivity) hm hi hn _ tendsto_const_nhds hMass
  filter_upwards [ha.eventually (Iio_mem_nhds (by positivity : (0:ℝ) < ‖x‖/2))] with j hj
  intro z hz
  have hnorm : ‖x‖ ≤ ‖x-z‖+‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x-z) z
  have hzs : a j < ‖z‖ := by change a j < ‖x‖/2 at hj; linarith
  rw [hs j z hzs]

lemma bounded_compact_mass_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {L S : ℝ} (_hL : 0 ≤ L) (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ L)
    (hs : ∀ z, S < ‖z‖ → ρ z = 0) :
    Integrable ρ ∧ (∫ z, ρ z) ≤ volume.real (closedBall (0:TFSpace) S)*L := by
  have hmajor : ∀ z, ρ z ≤ (closedBall (0:TFSpace) S).indicator (fun _ => L) z := by
    intro z
    by_cases hz : ‖z‖ ≤ S
    · rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hz)]
      exact hb z
    · rw [indicator_of_notMem (by simpa only [mem_closedBall_zero_iff] using hz),hs z (lt_of_not_ge hz)]
  have hI : Integrable ((closedBall (0:TFSpace) S).indicator (fun _ => L)) :=
    (integrableOn_const (C := L) measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hρ : Integrable ρ := hI.mono' hm.aestronglyMeasurable (ae_of_all _ fun z => by
    simpa only [Real.norm_of_nonneg (hn z)] using hmajor z)
  refine ⟨hρ,(integral_mono hρ hI hmajor).trans_eq ?_⟩
  rw [integral_indicator measurableSet_closedBall,setIntegral_const,smul_eq_mul]

lemma potential_tendsto_zero_of_compact_bound {ι : Type*} {F : Filter ι}
    {ρ : ι → TFSpace → ℝ} {L : ι → ℝ} {S : ℝ} (x : TFSpace)
    (hm : ∀ j, Measurable (ρ j)) (hL : ∀ j, 0 ≤ L j)
    (hn : ∀ j z, 0 ≤ ρ j z) (hb : ∀ j z, ρ j z ≤ L j)
    (hs : ∀ j z, S < ‖z‖ → ρ j z = 0) (hlim : Tendsto L F (𝓝 0)) :
    Tendsto (fun j => tfPotential (ρ j) x) F (𝓝 0) := by
  have hi := fun j => bounded_compact_mass_le (hm j) (hL j) (hn j) (hb j) (hs j)
  apply potential_tendsto_zero_of_local_mass (b := 1) (by norm_num) hm
    (fun j => (hi j).1) hn (Eventually.of_forall fun j z _ => hb j z) hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero] using hlim.const_mul (volume.real (closedBall (0:TFSpace) S)))
  · exact Eventually.of_forall fun j => integral_nonneg (hn j)
  · exact Eventually.of_forall fun j => (hi j).2

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma annularApproximationError_measurable (l a S : ℝ) :
    Measurable (annularApproximationError l a S) :=
  (measurable_const.div (measurable_norm.pow_const 6)).indicator
    ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const))

lemma annularApproximationError_nonneg (l a S : ℝ) (x : TFSpace) :
    0 ≤ annularApproximationError l a S x :=
  indicator_nonneg (fun _ _ => div_nonneg (by positivity) (by positivity)) _

lemma annularApproximationError_support (l a S : ℝ) (x : TFSpace) (hx : S < ‖x‖) :
    annularApproximationError l a S x = 0 :=
  indicator_of_notMem (fun h => (not_le.mpr hx) h.2) _

lemma annularApproximationError_bound {l a S : ℝ} (hl : 0 < l) (ha : 1/(2*l) ≤ a)
    (x : TFSpace) : annularApproximationError l a S x ≤ 64*l⁻¹^2 := by
  by_cases hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ S
  · rw [annularApproximationError,indicator_of_mem (show x ∈ {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S} from hx)]
    have hnear : 0 < 1/(2*l) := by positivity
    calc
      _ ≤ l⁻¹^8/(1/(2*l))^6 := div_le_div_of_nonneg_left (by positivity)
        (pow_pos hnear 6) (pow_le_pow_left₀ hnear.le (ha.trans hx.1) 6)
      _ = _ := by field_simp [hl.ne']; ring
  · rw [annularApproximationError,indicator_of_notMem (show x ∉ {x : TFSpace | a ≤ ‖x‖ ∧ ‖x‖ ≤ S} from hx)]
    positivity

lemma annular_correction_potential_tendsto_zero {ι : Type*} {F : Filter ι}
    {l a : ι → ℝ} {S : ℝ} (x : TFSpace)
    (hl : ∀ j, 0 < l j) (ha : ∀ j, 1/(2*l j) ≤ a j) (ht : Tendsto l F atTop) :
    Tendsto (fun j => tfPotential (annularApproximationError (l j) (a j) S) x) F (𝓝 0) := by
  apply potential_tendsto_zero_of_compact_bound (L := fun j => 64*(l j)⁻¹^2) x
    (fun j => annularApproximationError_measurable _ _ _) (fun _ => by positivity)
    (fun j => annularApproximationError_nonneg _ _ _)
    (fun j => annularApproximationError_bound (hl j) (ha j))
    (fun j => annularApproximationError_support _ _ _)
  simpa using ((tendsto_inv_atTop_zero.comp ht).pow 2).const_mul (64:ℝ)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ScaledBarrierCorrectionBarrier
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
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfDilation_measurable {b : ℝ} {ρ : TFSpace → ℝ} (hm : Measurable ρ) :
    Measurable (tfDilation b ρ) :=
  measurable_const.mul (hm.comp (continuous_const_smul b).measurable)

lemma tfDilation_integrable {b : ℝ} (hb : 0 < b) {ρ : TFSpace → ℝ}
    (hi : Integrable ρ) : Integrable (tfDilation b ρ) :=
  (hi.comp_smul hb.ne').const_mul _

lemma tfDilation_nonneg {b : ℝ} {ρ : TFSpace → ℝ} (hn : ∀ x, 0 ≤ ρ x) :
    ∀ x, 0 ≤ tfDilation b ρ x := fun x => mul_nonneg (by positivity) (hn _)

lemma tfDilation_support {b r : ℝ} (hb : 0 < b) {ρ : TFSpace → ℝ}
    (hs : ∀ x, r < ‖x‖ → ρ x = 0) :
    ∀ x, r/b < ‖x‖ → tfDilation b ρ x = 0 := by
  intro x hx
  rw [tfDilation,hs _ (by
    rw [norm_smul,Real.norm_of_nonneg hb.le]
    exact (div_lt_iff₀ hb).mp hx |>.trans_eq (mul_comm _ _)),mul_zero]

lemma selected_scaled_error_potential_tendsto_zero {ι : Type*} {F : Filter ι}
    {s r : ι → ℝ} {p : ι → TFSpace → ℝ}
    (hs : ∀ i, 0 < s i) (hs0 : Tendsto s F (𝓝 0))
    (ha : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hm : ∀ i, Measurable (p i)) (hi : ∀ i, Integrable (p i))
    (hn : ∀ i x, 0 ≤ p i x) (hsp : ∀ i x, r i < ‖x‖ → p i x = 0)
    (hMass : ∀ i, (∫ x, p i x) ≤ 1) (x : TFSpace) (hx : x ≠ 0) :
    Tendsto (fun i => tfPotential (tfDilation (s i) (p i)) x) F (𝓝 0) := by
  apply potential_tendsto_zero_of_shrinking_support hx
    (fun i => tfDilation_measurable (hm i)) (fun i => tfDilation_integrable (hs i) (hi i))
    (fun i => tfDilation_nonneg (hn i)) (fun i => tfDilation_support (hs i) (hsp i)) ha
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_pow (by norm_num : 3 ≠ 0)] using hs0.pow 3)
  · exact Eventually.of_forall fun i => integral_nonneg (tfDilation_nonneg (hn i))
  · apply Eventually.of_forall
    intro i
    rw [tfDilation_mass (hs i)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hMass i) (pow_nonneg (hs i).le 3)

lemma tfPotential_add_bounded {p q : TFSpace → ℝ} {P Q : ℝ}
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hqm : Measurable q) (hqi : Integrable q) (hQ : 0 ≤ Q)
    (hqn : ∀ x, 0 ≤ q x) (hqb : ∀ x, q x ≤ Q) (x : TFSpace) :
    tfPotential (fun y => p y+q y) x = tfPotential p x+tfPotential q x := by
  simp only [tfPotential,add_div]
  exact integral_add (bounded_L1_potential_integrable hpm hpi hP hpn hpb x)
    (bounded_L1_potential_integrable hqm hqi hQ hqn hqb x)

theorem literal_barrier_correction_tendsto_zero {ι : Type*} {F : Filter ι}
    {s r l : ι → ℝ} {p : ι → TFSpace → ℝ} (S : ℝ)
    (hs : ∀ i, 0 < s i) (hs0 : Tendsto s F (𝓝 0))
    (ha : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
    (hal : ∀ i, 1/(2*l i) ≤ r i/s i)
    (hm : ∀ i, Measurable (p i)) (hi : ∀ i, Integrable (p i))
    (hn : ∀ i x, 0 ≤ p i x) (hb : ∀ i, ∃ P ≥ 0, ∀ x, p i x ≤ P)
    (hsp : ∀ i x, r i < ‖x‖ → p i x = 0)
    (hMass : ∀ i, (∫ x, p i x) ≤ 1) (x : TFSpace) (hx : x ≠ 0) :
    Tendsto (fun i => tfPotential (fun y => tfDilation (s i) (p i) y+
      annularApproximationError (l i) (r i/s i) S y) x) F (𝓝 0) := by
  have he (i : ι) : tfPotential (fun y => tfDilation (s i) (p i) y+
      annularApproximationError (l i) (r i/s i) S y) x =
      tfPotential (tfDilation (s i) (p i)) x+
      tfPotential (annularApproximationError (l i) (r i/s i) S) x := by
    obtain ⟨P,hP,hbp⟩ := hb i
    have hqm := annularApproximationError_measurable (l i) (r i/s i) S
    have hqn := annularApproximationError_nonneg (l i) (r i/s i) S
    have hqb := annularApproximationError_bound (S := S) (hl i) (hal i)
    have hqs := annularApproximationError_support (l i) (r i/s i) S
    have hqi := (bounded_compact_mass_le hqm (by positivity : 0 ≤ 64*(l i)⁻¹^2) hqn hqb hqs).1
    exact tfPotential_add_bounded (tfDilation_measurable (hm i))
      (tfDilation_integrable (hs i) (hi i)) (mul_nonneg (pow_nonneg (hs i).le 6) hP)
      (tfDilation_nonneg (hn i)) (fun y => mul_le_mul_of_nonneg_left (hbp _) (by positivity))
      hqm hqi (by positivity) hqn hqb x
  simp_rw [he]
  have hp := selected_scaled_error_potential_tendsto_zero hs hs0 ha hm hi hn hsp hMass x hx
  have hq := annular_correction_potential_tendsto_zero (S := S) x hl hal hl0
  simpa only [add_zero] using hp.add hq

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SelectedBarrierTransferBarrier
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
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma scaled_barrier_eq {s : ℝ} (hs : 0 < s) (Z : ℝ)
    (a : TFSpace → ℝ) (x : TFSpace) :
    s^4*(nuclearField Z (s • x)+a (s • x)) =
      nuclearField (s^3*Z) x+s^4*a (s • x) := by
  rw [mul_add,nuclearField_dilation hs]

lemma scaled_barrier_lower {s r B Z : ℝ} (hs : 0 < s) {a : TFSpace → ℝ}
    (hlo : ∀ y, r ≤ ‖y‖ → outerBarrier B r y ≤ nuclearField Z y+a y) :
    ∀ x, r/s ≤ ‖x‖ → outerBarrier B (r/s) x ≤
      nuclearField (s^3*Z) x+s^4*a (s • x) := by
  intro x hx
  have hy : r ≤ ‖s • x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    exact ((div_le_iff₀ hs).mp hx).trans_eq (mul_comm _ _)
  have ht := mul_le_mul_of_nonneg_left (hlo (s • x) hy) (pow_nonneg hs.le 4)
  rwa [outerBarrier_dilation hs,scaled_barrier_eq hs] at ht

lemma scaled_barrier_upper {s r C Z : ℝ} (hs : 0 < s) {a : TFSpace → ℝ}
    (hup : ∀ y, r ≤ ‖y‖ → nuclearField Z y+a y ≤ C/‖y‖^4) :
    ∀ x, r/s ≤ ‖x‖ → nuclearField (s^3*Z) x+s^4*a (s • x) ≤ C/‖x‖^4 := by
  intro x hx
  have hy : r ≤ ‖s • x‖ := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    exact ((div_le_iff₀ hs).mp hx).trans_eq (mul_comm _ _)
  have ht := mul_le_mul_of_nonneg_left (hup (s • x) hy) (pow_nonneg hs.le 4)
  rw [scaled_barrier_eq hs] at ht
  have hh : s^4*(C/‖s • x‖^4) = C/‖x‖^4 := by
    rw [norm_smul,Real.norm_of_nonneg hs.le]
    field_simp
  exact ht.trans_eq hh

theorem selected_scaled_barrier_transfer_ball {a μ p : TFSpace → ℝ}
    {Z k r s l S M P c : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hl : 0 < l) (hS : 0 < S)
    (hal : 1/(2*l) ≤ r/s) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (ha : Continuous a)
    (hμm : Measurable μ) (hμi : Integrable μ) (hM : 0 ≤ M)
    (hμn : ∀ x, 0 ≤ μ x) (hμb : ∀ x, μ x ≤ M)
    (hpm : Measurable p) (hpi : Integrable p) (hP : 0 ≤ P)
    (hpn : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ P)
    (hw : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+a x)
      (fun x => innerSource r μ p x+outerCoefficient r x*reaction k (nuclearField Z x+a x)))
    (hd : ∀ x : TFSpace, r/s ≤ ‖x‖ → ‖x‖ ≤ S →
      tfDilation s μ x ≤ k*(max (nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x-1) 0)^(3/2:ℝ)+
        l⁻¹^8/‖x‖^6)
    (hb : ∀ x : TFSpace, ‖x‖ = S → s^4*a (s • x)+tfPotential (tfDilation s μ) x ≤ c) :
    ∀ x ∈ closedBall (0:TFSpace) S,
      nuclearField (s^3*Z) x+s^4*a (s • x) ≤
      nuclearField (s^3*Z) x-tfPotential (tfDilation s μ) x+
        tfPotential (fun y => tfDilation s p y+annularApproximationError l (r/s) S y) x+c := by
  let q := annularApproximationError l (r/s) S
  have hqm : Measurable q := annularApproximationError_measurable _ _ _
  have hqn : ∀ x, 0 ≤ q x := annularApproximationError_nonneg _ _ _
  have hqb : ∀ x, q x ≤ 64*l⁻¹^2 := annularApproximationError_bound hl hal
  have hqi : Integrable q := (bounded_compact_mass_le hqm
    (by positivity : 0 ≤ 64*l⁻¹^2) hqn hqb (annularApproximationError_support _ _ _)).1
  apply barrier_transfer_ball (div_pos hr hs) hS (by norm_num : (0:ℝ) ≤ 1) hk hc
    ((ha.comp (continuous_id.const_smul s)).const_mul (s^4))
    (tfDilation_measurable hμm) (tfDilation_integrable hs hμi)
    (mul_nonneg (pow_nonneg hs.le 6) hM) (tfDilation_nonneg hμn)
    (fun x => mul_le_mul_of_nonneg_left (hμb _) (pow_nonneg hs.le 6))
    (tfDilation_measurable hpm) (tfDilation_integrable hs hpi)
    (mul_nonneg (pow_nonneg hs.le 6) hP) (tfDilation_nonneg hpn)
    (fun x => mul_le_mul_of_nonneg_left (hpb _) (pow_nonneg hs.le 6))
    hqm hqi (by positivity) hqn hqb (barrier_weak_dilation hs hw) _ hb
  intro x hx hxr
  have hxs : ‖x‖ ≤ S := (mem_ball_zero_iff.mp hx).le
  have hq : q x = l⁻¹^8/‖x‖^6 := by
    apply indicator_of_mem
    exact ⟨hxr,hxs⟩
  rw [hq,reaction]
  have hh := mul_le_mul_of_nonneg_left (hd x hxr hxs) (by positivity : (0:ℝ) ≤ 4*Real.pi)
  nlinarith only [hh]

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierLimitPositiveBarrier
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

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma outerBarrier_tendsto {ι : Type*} {l : Filter ι} {a : ι → ℝ}
    (ha : Tendsto a l (𝓝 0)) (B : ℝ) (x : TFSpace) :
    Tendsto (fun i => outerBarrier B (a i) x) l (𝓝 (B/‖x‖^4)) := by
  have ht := (((tendsto_const_nhds (x := (1:ℝ))).sub (ha.div_const (8*‖x‖))).const_mul (B/‖x‖^4))
  simpa only [outerBarrier,zero_div,sub_zero,mul_one] using ht

theorem positive_limit_of_eventual_barrier_transfer {ι : Type*} {l : Filter ι} [NeBot l]
    {U F : ι → TFSpace → ℝ} {L : ℝ → ι → TFSpace → ℝ}
    {a : ι → ℝ} {B C : ℝ} {F_lim : TFSpace → ℝ} (hC : 0 ≤ C)
    (ha : Tendsto a l (𝓝 0))
    (hlo : ∀ i x, a i ≤ ‖x‖ → outerBarrier B (a i) x ≤ U i x)
    (hup : ∀ i x, a i ≤ ‖x‖ → U i x ≤ C/‖x‖^4)
    (hconv : ∀ S : ℝ, 0 < S → TendstoUniformlyOn F F_lim l (sphere (0:TFSpace) S))
    (hL : ∀ S : ℝ, 0 < S → ∀ x : TFSpace, x ≠ 0 →
      Tendsto (fun i => L S i x) l (𝓝 0))
    (hdecay : ∀ ε > 0, ∃ R > 0, ∀ x : TFSpace, R ≤ ‖x‖ → |F_lim x| < ε)
    (htransfer : ∀ (S : ℝ), 0 < S → ∀ᶠ i in l, ∀ c : ℝ, 0 ≤ c →
      (∀ x : TFSpace, ‖x‖ = S → U i x-F i x ≤ c) →
      ∀ x ∈ closedBall (0:TFSpace) S, U i x ≤ F i x+L S i x+c) :
    ∀ x : TFSpace, x ≠ 0 → B/‖x‖^4 ≤ F_lim x := by
  intro x hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨R,hR,hdec⟩ := hdecay (ε/4) (by positivity)
  let S : ℝ := max R (max (‖x‖+1) (max 1 (4*C/ε)))
  have hRS : R ≤ S := le_max_left _ _
  have hxS : ‖x‖+1 ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have h1S : 1 ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCS : 4*C/ε ≤ S := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hS : 0 < S := hR.trans_le hRS
  have hpow : S ≤ S^4 := by
    have hh : 1 ≤ S^3 := one_le_pow₀ h1S
    nlinarith
  have hsmallC : C/S^4 ≤ ε/4 := calc
    _ ≤ C/S := div_le_div_of_nonneg_left hC hS hpow
    _ ≤ _ := (div_le_iff₀ hS).mpr (by
      have hh := (div_le_iff₀ hε).mp hCS
      nlinarith)
  have ha' : ∀ᶠ i in l, a i < ‖x‖ := ha.eventually (Iio_mem_nhds hxpos)
  have he := Metric.tendstoUniformlyOn_iff.mp (hconv S hS) (ε/4) (by positivity)
  have hb : ∀ᶠ i in l, ∀ y : TFSpace, ‖y‖ = S → U i y-F i y ≤ ε := by
    filter_upwards [ha',he] with i hai hei
    intro y hy
    have hUi := hup i y (by rw [hy]; linarith)
    have hFi := hei y (by simpa only [mem_sphere,dist_zero_right] using hy)
    rw [Real.dist_eq] at hFi
    have hyR : R ≤ ‖y‖ := hy ▸ hRS
    have hFy := hdec y hyR
    rw [hy] at hUi
    have hab1 := (abs_lt.mp hFi).2
    have hab2 := (abs_lt.mp hFy).1
    linarith
  have hFi : Tendsto (fun i => F i x) l (𝓝 (F_lim x)) :=
    (hconv ‖x‖ hxpos).tendsto_at (by simp only [mem_sphere,dist_zero_right])
  have hright := (hFi.add (hL S hS x hx)).add_const ε
  simp only [add_zero] at hright
  apply le_of_tendsto_of_tendsto (outerBarrier_tendsto ha B x) hright
  filter_upwards [ha',hb,htransfer S hS] with i hai hbi hti
  exact (hlo i x hai.le).trans (hti ε hε.le hbi x
    (mem_closedBall_zero_iff.mpr (by linarith)))

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectedBarrierLimitBarrier
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
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem selected_barriers_limit_positive_oai {ι : Type*} {F : Filter ι} [NeBot F]
    {s r l Z : ι → ℝ} {a μ p : ι → TFSpace → ℝ} {k B C : ℝ}
    {F_lim : TFSpace → ℝ}
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i)
    (hs0 : Tendsto s F (𝓝 0)) (hr0 : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
    (hal : ∀ i, 1/(2*l i) ≤ r i/s i) (hk : 0 ≤ k) (hC : 0 ≤ C)
    (ha : ∀ i, Continuous (a i))
    (hμm : ∀ i, Measurable (μ i)) (hμi : ∀ i, Integrable (μ i))
    (hμn : ∀ i x, 0 ≤ μ i x) (hμb : ∀ i, ∃ M ≥ 0, ∀ x, μ i x ≤ M)
    (hpm : ∀ i, Measurable (p i)) (hpi : ∀ i, Integrable (p i))
    (hpn : ∀ i x, 0 ≤ p i x) (hpb : ∀ i, ∃ P ≥ 0, ∀ x, p i x ≤ P)
    (hpSupport : ∀ i x, r i < ‖x‖ → p i x = 0)
    (hpMass : ∀ i, (∫ x, p i x) ≤ 1)
    (hweak : ∀ i, WeakNuclearLowerOn univ (Z i)
      (fun x => nuclearField (Z i) x+a i x)
      (fun x => innerSource (r i) (μ i) (p i) x+
        outerCoefficient (r i) x*reaction k (nuclearField (Z i) x+a i x)))
    (hlower : ∀ i y, r i ≤ ‖y‖ → outerBarrier B (r i) y ≤ nuclearField (Z i) y+a i y)
    (hupper : ∀ i y, r i ≤ ‖y‖ → nuclearField (Z i) y+a i y ≤ C/‖y‖^4)
    (hTF : ∀ i x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
      tfDilation (s i) (μ i) x ≤
        k*(max (nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x-1) 0)^(3/2:ℝ)+
          (l i)⁻¹^8/‖x‖^6)
    (hconv : ∀ S : ℝ, 0 < S → TendstoUniformlyOn
      (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
      F_lim F (sphere (0:TFSpace) S))
    (hdecay : ∀ ε > 0, ∃ R > 0, ∀ x : TFSpace, R ≤ ‖x‖ → |F_lim x| < ε) :
    ∀ x : TFSpace, x ≠ 0 → B/‖x‖^4 ≤ F_lim x := by
  apply positive_limit_of_eventual_barrier_transfer
    (U := fun i x => nuclearField ((s i)^3*Z i) x+(s i)^4*a i (s i • x))
    (L := fun S i x => tfPotential (fun y => tfDilation (s i) (p i) y+
      annularApproximationError (l i) (r i/s i) S y) x)
    hC hr0 (fun i => scaled_barrier_lower (hs i) (hlower i))
    (fun i => scaled_barrier_upper (hs i) (hupper i)) hconv
    (fun S _ x hx => literal_barrier_correction_tendsto_zero S hs hs0 hr0 hl hl0 hal
      hpm hpi hpn hpb hpSupport hpMass x hx) hdecay
  intro S hS
  filter_upwards [hl0.eventually (eventually_ge_atTop S)] with i hi
  intro c hc hb
  obtain ⟨M,hM,hMb⟩ := hμb i
  obtain ⟨P,hP,hPb⟩ := hpb i
  apply selected_scaled_barrier_transfer_ball (hr i) (hs i) (hl i) hS (hal i) hk hc
    (ha i) (hμm i) (hμi i) hM (hμn i) hMb (hpm i) (hpi i) hP (hpn i) hPb
    (hweak i) (fun x hx hxs => hTF i x hx (hxs.trans hi))
  intro x hx
  have hh := hb x hx
  linarith only [hh]

end CoulombBarrier

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CoulombBarrier.selected_barriers_limit_positive_oai.{u_1} := @OAI.CoulombBarrier.selected_barriers_limit_positive_oai.{u_1}

-- Prove2me | solution 1 for OAI.CoulombBarrier.selected_data_profile_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:57:56.156961+00:00
-- url     : https://prove2.me/submissions/39191163-d355-414c-b62d-d600c0590e18

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombBarrier_selected_barriers_limit_positive

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_RadialPower
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombPDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma radialPower_pos (a : ℝ) {x : E} (hx : x ≠ 0) : 0 < radialPower a x :=
  Real.rpow_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hx)) a

lemma exists_small_rpow_bound {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∃ a > 0, ∀ t : ℝ, 0 < t → t ≤ a → M ≤ t ^ (-s) := by
  have he := (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually (eventually_ge_atTop M)
  obtain ⟨b, hb, hsub⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨b / 2, by positivity, ?_⟩
  intro t ht htb
  apply hsub
  exact ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using
    (show t < b by linarith), ht⟩

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma exists_small_radialPower_bound {s : ℝ} (hs : 0 < s) (M : ℝ) :
    ∃ a > 0, ∀ x : E, x ≠ 0 → ‖x‖ ≤ a → M ≤ radialPower (-s) x := by
  obtain ⟨b, hb, hbound⟩ := exists_small_rpow_bound hs M
  refine ⟨min 1 b, lt_min (by norm_num) hb, ?_⟩
  intro x hx ha
  have h1 : ‖x‖ ≤ 1 := ha.trans (min_le_left _ _)
  have hb' : ‖x‖ ≤ b := ha.trans (min_le_right _ _)
  apply hbound _ (sq_pos_of_pos (norm_pos_iff.mpr hx))
  nlinarith [norm_nonneg x]

lemma exists_small_exponent {q : ℝ} (hq : 12 < q) :
    ∃ s > 0, 12 + 14 * s + 4 * s ^ 2 ≤ q := by
  let s := min 1 ((q - 12) / 36)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have h1 : s ≤ 1 := min_le_left _ _
  have hq' : s ≤ (q - 12) / 36 := min_le_right _ _
  refine ⟨s, hs, ?_⟩
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr h1)]

lemma rpow_three_halves_upper {B v : ℝ} (hv : 0 ≤ v) (hB : v ≤ B) :
    v ^ (3 / 2 : ℝ) ≤ B ^ (1 / 2 : ℝ) * v := by
  rw [rpow_three_halves v hv]
  have h := Real.rpow_le_rpow hv hB (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith [mul_nonneg hv (sub_nonneg.mpr h)]

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SommerfeldCoefficient
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

lemma lower_barrier_laplacian {d B e s c c₀ F : ℝ} (hd : 0 ≤ d)
    (he : 0 ≤ e) (hs : 0 ≤ s) (hc : 0 ≤ c) (hc₀ : 0 < c₀)
    (hq : d * B ^ (1 / 2 : ℝ) ≤ 12)
    (hκ : (14 * s + 4 * s ^ 2) * B ≤ (12 - d * B ^ (1 / 2 : ℝ)) * c₀)
    {x : Space} (hx : x ≠ 0) (hlow : c₀ * radialPower (-2) x ≤ F)
    (hgt : F < radialCombination B (-e) s (-c) x) :
    reaction d F ≤ Δ (radialCombination B (-e) s (-c)) x := by
  let z := e * radialPower (-s) x
  let v := B - z
  have hz : 0 ≤ z := mul_nonneg he (radialPower_nonneg _ _)
  have hp := radialPower_pos (-2) hx
  have hfac : radialCombination B (-e) s (-c) x = radialPower (-2) x * v - c := by
    rw [radialCombination_factor _ _ _ _ hx]; dsimp [v, z]; ring
  have hv : c₀ < v := by
    rw [hfac] at hgt
    nlinarith
  have hvpos : 0 < v := hc₀.trans hv
  have hvB : v ≤ B := by dsimp [v]; linarith
  have hzB : z ≤ B := by dsimp [v] at hvpos; linarith
  have hf : max (F - 1) 0 ≤ radialPower (-2) x * v := by
    apply max_le
    · rw [hfac] at hgt; linarith
    · positivity
  have hcoeff : 0 ≤ 14 * s + 4 * s ^ 2 := by positivity
  have hscalar : d * B ^ (1 / 2 : ℝ) * v ≤ 12 * B - (12 + 14 * s + 4 * s ^ 2) * z := by
    have h1 := mul_le_mul_of_nonneg_left hzB hcoeff
    have h2 := mul_le_mul_of_nonneg_left hv.le (sub_nonneg.mpr hq)
    dsimp [v] at *
    nlinarith
  calc
    reaction d F ≤ d * (radialPower (-2) x * v) ^ (3 / 2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_max_right _ _) hf (by norm_num)) hd
    _ = radialPower (-3) x * (d * v ^ (3 / 2 : ℝ)) := by
      rw [radial_scaled_reaction hvpos.le]; ring
    _ ≤ radialPower (-3) x * (d * B ^ (1 / 2 : ℝ) * v) := by
      apply mul_le_mul_of_nonneg_left _ (radialPower_nonneg _ _)
      have h := mul_le_mul_of_nonneg_left (rpow_three_halves_upper hvpos.le hvB) hd
      nlinarith
    _ ≤ radialPower (-3) x * (12 * B - (12 + 14 * s + 4 * s ^ 2) * z) :=
      mul_le_mul_of_nonneg_left hscalar (radialPower_nonneg _ _)
    _ = Δ (radialCombination B (-e) s (-c)) x := by
      rw [radialCombination_laplacian _ _ _ _ hx]; dsimp [z]; ring

lemma reaction_superlinear {d α δ v : ℝ} (hd : 0 ≤ d) (hα : 1 ≤ α) (hδ : 0 ≤ δ) :
    α * reaction d v ≤ reaction d (α * v + δ) := by
  have hα₀ : 0 ≤ α := by linarith
  have hm : α * max (v - 1) 0 ≤ max (α * v + δ - 1) 0 := by
    by_cases hv : v ≤ 1
    · rw [max_eq_right (sub_nonpos.mpr hv), mul_zero]
      exact le_max_right _ _
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hv))]
      apply le_trans _ (le_max_left _ _)
      nlinarith
  have hpow : α ≤ α ^ (3 / 2 : ℝ) := by
    simpa using rpow_three_halves_lower (by norm_num : (0 : ℝ) ≤ 1) hα
  unfold reaction
  calc
    α * (d * max (v - 1) 0 ^ (3 / 2 : ℝ))
        = d * (α * max (v - 1) 0 ^ (3 / 2 : ℝ)) := by ring
    _ ≤ d * (α ^ (3 / 2 : ℝ) * max (v - 1) 0 ^ (3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hd
      exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (le_max_right _ _) _)
    _ = d * (α * max (v - 1) 0) ^ (3 / 2 : ℝ) := by
      rw [Real.mul_rpow hα₀ (le_max_right _ _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hα₀ (le_max_right _ _)) hm (by norm_num)) hd

lemma deleted_eventually_to_small_ball {P : Space → Prop}
    (h : ∀ᶠ x in 𝓝[≠] (0 : Space), P x) :
    ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → P x := by
  obtain ⟨a, ha, hbound⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine ⟨a / 2, by positivity, ?_⟩
  intro x hx hxa
  apply hbound
  refine ⟨?_, hx⟩
  simpa only [Metric.mem_ball, dist_zero_right] using (show ‖x‖ < a by linarith)

lemma laplacian_comp_isometry {f : E → ℝ} (e : E ≃ₗᵢ[ℝ] E) (x : E)
    (hf : ContDiffAt ℝ 2 f (e x)) : Δ (fun y => f (e y)) x = Δ f (e x) := by
  have hc : ContDiffAt ℝ 2 (fun y => f (e y)) x := hf.comp x e.contDiff.contDiffAt
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map e)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, OrthonormalBasis.map_apply]
  rw [← second_deriv_line hc, ← second_deriv_line hf]
  congr 2
  funext t
  simp only [map_add, map_smul]

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialRotation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
namespace CoulombAtom

lemma rotate_continuous : Continuous (fun p : SpatialRotation × Space => rotate p.1 p.2) :=
  continuous_subtype_val.fst'.clm_apply continuous_snd

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierWeakMaxBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology Convolution

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

lemma newtonMul_flip_eq : newtonMul.flip = newtonMul := by
  exact ContinuousLinearMap.flip_mul

lemma laplacian_sub_left {k : TFSpace → ℝ} (hk : ContDiff ℝ 2 k)
    (x y : TFSpace) : Δ (fun z => k (x-z)) y = Δ k (x-y) := by
  have hd : ContDiff ℝ 2 (fun z : TFSpace => k (x+z)) :=
    hk.comp (contDiff_const.add contDiff_id)
  have hh := laplacian_comp_isometry (LinearIsometryEquiv.neg ℝ) y hd.contDiffAt
  simpa only [LinearIsometryEquiv.coe_neg,sub_eq_add_neg,tfLaplacian_translate] using hh

lemma tsupport_sub_left {k : TFSpace → ℝ} {r : ℝ}
    (hk : ∀ z, k z ≠ 0 → ‖z‖ ≤ r) (x : TFSpace) :
    tsupport (fun y => k (x-y)) ⊆ closedBall x r := by
  apply closure_minimal _ isClosed_closedBall
  intro y hy
  rw [mem_closedBall,dist_eq_norm_sub']
  exact hk (x-y) hy

end CoulombBarrier

end

end OAI
end

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
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_BarrierNuclearBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakHarmonicL1Barrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

namespace CoulombAnalysis
open CoulombAtom

lemma packetDensity_scaled_upper {P : ℝ}
    (hP : ∀ z : Space, packetDensity 0 1 z ≤ P) (x y : Space) {r : ℝ} (hr : 0 < r) :
    packetDensity x r y ≤ P/r^3 := by
  rw [packetDensity_scale x y hr]
  have hh := mul_le_mul_of_nonneg_left (hP (r⁻¹ • (y-x))) (pow_nonneg (inv_nonneg.mpr hr.le) 3)
  simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hh

lemma weak_harmonic_mean_from_larger_ball {u : Space → ℝ} {c : Space} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall c (3*R)))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ x, u x*Δ g x) = 0)
    {x : Space} (hx : x ∈ closedBall c R) :
    (∫ z, packetDensity x R z*u z) = u x := by
  have hsub : closedBall x (2*R) ⊆ closedBall c (3*R) := by
    intro z hz
    rw [mem_closedBall] at hx hz ⊢
    have hh := dist_triangle z x c
    linarith
  apply weak_harmonic_packet_mean_local (hu.mono hsub) hR (by linarith)
  intro g hg hcg hs
  exact hw g hg hcg (hs.trans (by
    intro z hz
    rw [mem_ball] at hz ⊢
    have hxc : dist x c ≤ R := hx
    have hh := dist_triangle z x c
    linarith))

lemma packet_integrable_on_larger_ball {u : Space → ℝ} {c : Space} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall c (3*R)))
    {x : Space} (hx : x ∈ closedBall c R) :
    Integrable (fun z => packetDensity x R z*u z) := by
  have hh := continuousOn_mul_integrable_support (isCompact_closedBall c (3*R)) hu
    (packetDensity_continuous x R) (fun z hz => by
      have hz' := packetDensity_support x hR hz
      rw [mem_closedBall] at hx ⊢
      rw [←dist_eq_norm] at hz'
      have ht := dist_triangle z x c
      linarith)
  simpa only [mul_comm] using hh

theorem exists_weak_harmonic_L1_constants : ∃ P L : ℝ, 0 ≤ P ∧ 0 ≤ L ∧
    ∀ (u : Space → ℝ) (c : Space) (R : ℝ), 0 < R →
    ContinuousOn u (closedBall c (3*R)) →
    (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ x, u x*Δ g x) = 0) →
    ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      |u x| ≤ P/R^3*(∫ z in closedBall c (3*R), |u z|) ∧
      |u x-u y| ≤ L/R^4*(∫ z in closedBall c (3*R), |u z|)*‖x-y‖ := by
  obtain ⟨P,hP⟩ := (packetDensity_compact (0 : Space) (by norm_num : (0:ℝ)<1)).exists_bound_of_continuous
    (packetDensity_continuous 0 1)
  obtain ⟨L,_p,_hp,hL,_hlow⟩ := exists_packet_unit_control
  have hP0 : 0 ≤ P := (norm_nonneg (packetDensity 0 1 0)).trans (hP 0)
  have hPu (z : Space) : packetDensity 0 1 z ≤ P :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hP z)
  refine ⟨P,L,hP0,L.coe_nonneg,?_⟩
  intro u c R hR hu hw x hx y hy
  let K := closedBall c (3*R)
  have hK : MeasurableSet K := isClosed_closedBall.measurableSet
  have hi : Integrable (K.indicator (fun z => |u z|)) :=
    (hu.abs.integrableOn_compact (isCompact_closedBall c (3*R))).integrable_indicator hK
  have hm := weak_harmonic_mean_from_larger_ball hR hu hw hx
  have hm' := weak_harmonic_mean_from_larger_ball hR hu hw hy
  have hix := packet_integrable_on_larger_ball hR hu hx
  have hiy := packet_integrable_on_larger_ball hR hu hy
  have hzpacket (z : Space) (hz : z ∉ K) (w : Space) (hw' : w ∈ closedBall c R) :
      packetDensity w R z = 0 := by
    by_contra hne
    have hs := packetDensity_support w hR hne
    apply hz
    rw [mem_closedBall] at hw' ⊢
    rw [←dist_eq_norm] at hs
    have ht := dist_triangle z w c
    linarith
  constructor
  · have hb := norm_integral_le_of_norm_le (hi.const_mul (P/R^3))
      (f := fun z => packetDensity x R z*u z) (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (packetDensity_nonneg x R z)]
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz]
          exact mul_le_mul_of_nonneg_right (packetDensity_scaled_upper hPu x z hR) (abs_nonneg _)
        · simp only [indicator_of_notMem hz,hzpacket z hz x hx,zero_mul,mul_zero,le_refl]))
    rw [Real.norm_eq_abs,hm,integral_const_mul,integral_indicator hK] at hb
    exact hb
  · have he : (∫ z, (packetDensity x R z-packetDensity y R z)*u z) = u x-u y := by
      simp_rw [sub_mul]
      rw [integral_sub hix hiy,hm,hm']
    have hb := norm_integral_le_of_norm_le (hi.const_mul ((L:ℝ)/R^4*‖x-y‖))
      (f := fun z => (packetDensity x R z-packetDensity y R z)*u z)
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_mul]
        by_cases hz : z ∈ K
        · rw [indicator_of_mem hz]
          exact mul_le_mul_of_nonneg_right (packetDensity_scaled_difference hL hR x y z) (abs_nonneg _)
        · simp only [indicator_of_notMem hz,hzpacket z hz x hx,hzpacket z hz y hy,
            sub_self,abs_zero,zero_mul,mul_zero,le_refl]))
    rw [Real.norm_eq_abs,he,integral_const_mul,integral_indicator hK] at hb
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BoundedL1PotentialBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
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

lemma bounded_L1_potential_le {ρ : TFSpace → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (x : TFSpace) :
    tfPotential ρ x ≤ 2*Real.pi*M+∫ z, ρ z := by
  have hk : Integrable (fun z => truncatedCoulomb 1 (x-z)) :=
    (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable 1).aestronglyMeasurable
      |>.mpr (truncatedCoulomb_integrable 1)
  calc
    _ ≤ ∫ z, M*truncatedCoulomb 1 (x-z)+ρ z := integral_mono
      (bounded_L1_potential_integrable hm hi hM hn hb x) ((hk.const_mul M).add hi)
      (bounded_coulomb_majorant hM hn hb x)
    _ = _ := by
      rw [integral_add (hk.const_mul M) hi,integral_const_mul,integral_sub_left_eq_self,
        truncatedCoulomb,integral_indicator measurableSet_ball]
      simp only [one_div]
      rw [integral_coulomb_ball (by norm_num : (0:ℝ) < 1)]
      ring

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
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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

namespace CoulombAnalysis
open CoulombAtom

lemma weak_poisson_plus_potential_harmonic {u ρ : Space → ℝ} {c : Space} {R M : ℝ}
    (hu : ContinuousOn u (closedBall c R))
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c R → (∫ x, u x*Δ g x) = 4*Real.pi*∫ x, ρ x*g x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ ball c R) :
    (∫ x, (u x+tfPotential ρ x)*Δ g x) = 0 := by
  have hiu := continuousOn_mul_integrable_support (isCompact_closedBall c R) hu
    (tfLaplacian_continuous hg) (fun x hx => ball_subset_closedBall (hs (tfLaplacian_support hg hx)))
  have hvcont := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have hiv := continuousOn_mul_integrable_support (isCompact_closedBall c R) hvcont.continuousOn
    (tfLaplacian_continuous hg) (fun x hx => ball_subset_closedBall (hs (tfLaplacian_support hg hx)))
  simp_rw [add_mul]
  rw [integral_add hiu hiv,hw g hg hcg hs,bounded_L1_weak_poisson hm hi hM hn hb hg hcg]
  ring

theorem exists_weak_poisson_L1_constants : ∃ P L : ℝ, 0 ≤ P ∧ 0 ≤ L ∧
    ∀ (u ρ : Space → ℝ) (c : Space) (R M A B : ℝ), 0 < R → 0 ≤ M →
    Measurable ρ → Integrable ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ρ z ≤ M) →
    (∫ z, ρ z) ≤ B → ContinuousOn u (closedBall c (3*R)) →
    (∫ z in closedBall c (3*R), |u z|) ≤ A →
    (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ z, u z*Δ g z) = 4*Real.pi*∫ z, ρ z*g z) →
    ∀ x ∈ closedBall c R, ∀ y ∈ closedBall c R,
      |u x| ≤ P/R^3*(A+(2*Real.pi*M+B)*(volume (closedBall c (3*R))).toReal)+(2*Real.pi*M+B) ∧
      |u x-u y| ≤ (L/R^4*(A+(2*Real.pi*M+B)*(volume (closedBall c (3*R))).toReal)+4*Real.pi*M+B)*‖x-y‖ := by
  obtain ⟨P,L,hP,hL,h⟩ := exists_weak_harmonic_L1_constants
  refine ⟨P,L,hP,hL,?_⟩
  intro u ρ c R M A B hR hM hm hi hn hb hmass hu hL1 hw x hx y hy
  let V := tfPotential ρ
  let K := closedBall c (3*R)
  let C := 2*Real.pi*M+B
  have hB : 0 ≤ B := (integral_nonneg hn).trans hmass
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hVcont : Continuous V := (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous
  have hVnonneg (z : Space) : 0 ≤ V z := tfPotential_nonneg (ae_of_all _ hn) z
  have hVbound (z : Space) : V z ≤ C :=
    (bounded_L1_potential_le hm hi hM hn hb z).trans (add_le_add le_rfl hmass)
  have hKfin : volume K ≠ ⊤ := (isCompact_closedBall c (3*R)).measure_lt_top.ne
  have hic : IntegrableOn (fun _ : Space => C) K := integrableOn_const hKfin
  have hui : IntegrableOn (fun z => |u z|) K := hu.abs.integrableOn_compact (isCompact_closedBall c (3*R))
  have huV : ContinuousOn (fun z => u z+V z) K := hu.add hVcont.continuousOn
  have hiuV : IntegrableOn (fun z => |u z+V z|) K := huV.abs.integrableOn_compact (isCompact_closedBall c (3*R))
  have hL1' : (∫ z in K, |u z+V z|) ≤ A+C*(volume K).toReal := by
    have hh := integral_mono_ae hiuV (hui.add hic) (ae_of_all _ (fun z => by
      change |u z+V z| ≤ |u z|+C
      exact (abs_add_le _ _).trans (add_le_add le_rfl (by rw [abs_of_nonneg (hVnonneg z)]; exact hVbound z))))
    change (∫ z in K, |u z+V z|) ≤ ∫ z in K, |u z|+C at hh
    rw [integral_add hui hic] at hh
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hh
    calc
      _ ≤ (∫ z in K, |u z|)+(volume K).toReal*C := hh
      _ ≤ A+(volume K).toReal*C := add_le_add hL1 le_rfl
      _ = _ := by ring
  have hhar : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball c (3*R) → (∫ z, (u z+V z)*Δ g z) = 0 :=
    fun g hg hcg hs => weak_poisson_plus_potential_harmonic hu hm hi hM hn hb hw hg hcg hs
  have hest := h (fun z => u z+V z) c R hR huV hhar x hx y hy
  have habs : |u x| ≤ |u x+V x|+C := by
    calc
      _ = |(u x+V x)-V x| := by ring_nf
      _ ≤ |u x+V x|+|V x| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl (by rw [abs_of_nonneg (hVnonneg x)]; exact hVbound x)
  have hdiff : |V x-V y| ≤ (4*Real.pi*M+B)*‖x-y‖ :=
    (bounded_L1_potential_difference hm hi hM hn hb x y).trans
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl hmass) (norm_nonneg _))
  constructor
  · exact habs.trans (add_le_add (hest.1.trans
      (mul_le_mul_of_nonneg_left hL1' (div_nonneg hP (pow_nonneg hR.le 3)))) le_rfl)
  · calc
      _ = |((u x+V x)-(u y+V y))-(V x-V y)| := by ring_nf
      _ ≤ |(u x+V x)-(u y+V y)|+|V x-V y| := abs_sub _ _
      _ ≤ L/R^4*(A+C*(volume K).toReal)*‖x-y‖+(4*Real.pi*M+B)*‖x-y‖ :=
        add_le_add (hest.2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hL1' (div_nonneg hL (pow_nonneg hR.le 4))) (norm_nonneg _))) hdiff
      _ = _ := by dsimp only [C,K]; ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FiniteProfile
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombPDE

lemma FiniteProfile.compare {d Z W : ℝ} {F G : Space → ℝ}
    (hF : FiniteProfile d Z F) (hG : FiniteProfile d W G) (hd : 0 ≤ d) (hZW : Z < W)
    (x : Space) (hx : x ≠ 0) : F x ≤ G x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => F y - (G y + δ)
  have hgd (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 (G + fun _ : Space => δ) y :=
    (hG.regular y hy).add contDiffAt_const
  have hdif (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hF.regular y hy).sub (hgd y hy)
  have hl (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hfg : G y ≤ F y := by dsimp [u] at hp; linarith
    change 0 ≤ Δ (F - (G + fun _ : Space => δ)) y
    rw [(hF.regular y hy).laplacian_sub (hgd y hy),
      (hG.regular y hy).laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_const, Pi.zero_apply, add_zero, hF.equation y hy, hG.equation y hy]
    exact sub_nonneg.mpr (reaction_monotone hd hfg)
  have hnear : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hnF⟩ := hF.nucleus
    obtain ⟨D, hD, b, hb, hnG⟩ := hG.nucleus
    refine ⟨min (min a b) ((W-Z)/(C+D+1)),
      lt_min (lt_min ha hb) (div_pos (sub_pos.mpr hZW) (by linarith)), ?_⟩
    intro y hy hr
    have hFa := (abs_le.mp (hnF y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _))))).2
    have hGa := (abs_le.mp (hnG y hy (hr.trans ((min_le_left _ _).trans (min_le_right _ _))))).1
    have hsmall := (le_div_iff₀ (show 0 < C+D+1 by linarith)).mp (hr.trans (min_le_right _ _))
    have hgap : C+D ≤ (W-Z)/‖y‖ := (le_div_iff₀ (norm_pos_iff.mpr hy)).mpr (by nlinarith [norm_nonneg y])
    rw [sub_div] at hgap
    dsimp [u]
    linarith
  have hfar : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨a, ha, hFa⟩ := hF.decay (δ/2) (by positivity)
    obtain ⟨b, hb, hGb⟩ := hG.decay (δ/2) (by positivity)
    refine ⟨max a b, ha.trans_le (le_max_left _ _), ?_⟩
    intro y hy
    have hf := abs_lt.mp (hFa y ((le_max_left _ _).trans hy))
    have hg := abs_lt.mp (hGb y ((le_max_right _ _).trans hy))
    dsimp [u]
    linarith
  have hh := global_punctured_maximum_principle hdif hl hnear hfar x hx
  dsimp [u] at hh
  linarith

end CoulombPDE

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

lemma compare_subsolution_finite {d Z W : ℝ} {L G : Space → ℝ}
    (hd : 0 ≤ d) (hW : 0 < W) (hZW : Z < W) (hG : FiniteProfile d W G)
    (hreg : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 L x)
    (hpde : ∀ x, x ≠ 0 → reaction d (L x) ≤ Δ L x)
    (hnear : ∃ C > 0, ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → L x ≤ Z/‖x‖ + C)
    (hfar : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → L x ≤ ε)
    (x : Space) (hx : x ≠ 0) : L x ≤ G x := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let u : Space → ℝ := fun y => L y - (G y + δ)
  have hgd (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 (G + fun _ : Space => δ) y :=
    (hG.regular y hy).add contDiffAt_const
  have hud (y : Space) (hy : y ≠ 0) : ContDiffAt ℝ 2 u y := (hreg y hy).sub (hgd y hy)
  have hul (y : Space) (hy : y ≠ 0) (hp : 0 < u y) : 0 ≤ Δ u y := by
    have hlg : G y ≤ L y := by dsimp [u] at hp; linarith
    change 0 ≤ Δ (L - (G + fun _ : Space => δ)) y
    rw [(hreg y hy).laplacian_sub (hgd y hy),
      (hG.regular y hy).laplacian_add (show ContDiffAt ℝ 2 (fun _ : Space => δ) y from contDiffAt_const),
      laplacian_const, Pi.zero_apply, add_zero, hG.equation y hy]
    linarith [reaction_monotone hd hlg, hpde y hy]
  have hn : ∃ a > 0, ∀ y, y ≠ 0 → ‖y‖ ≤ a → u y ≤ 0 := by
    obtain ⟨C, hC, a, ha, hL⟩ := hnear
    obtain ⟨D, hD, b, hb, hG'⟩ := hG.nucleus
    refine ⟨min (min a b) ((W-Z)/(C+D+1)),
      lt_min (lt_min ha hb) (div_pos (sub_pos.mpr hZW) (by linarith)), ?_⟩
    intro y hy hr
    have hl := hL y hy (hr.trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hg := (abs_le.mp (hG' y hy (hr.trans ((min_le_left _ _).trans (min_le_right _ _))))).1
    have hsmall := (le_div_iff₀ (show 0 < C+D+1 by linarith)).mp (hr.trans (min_le_right _ _))
    have hgap : C+D ≤ (W-Z)/‖y‖ := (le_div_iff₀ (norm_pos_iff.mpr hy)).mpr (by nlinarith [norm_nonneg y])
    rw [sub_div] at hgap
    dsimp [u]
    linarith
  have hf : ∃ R > 0, ∀ y, R ≤ ‖y‖ → u y ≤ 0 := by
    obtain ⟨R, hR, hb⟩ := hfar (δ/2) (by positivity)
    refine ⟨R, hR, fun y hy => ?_⟩
    have hz : y ≠ 0 := norm_pos_iff.mp (hR.trans_le hy)
    dsimp [u]
    linarith [hb y hy, hG.nonneg hW y hz]
  have hh := global_punctured_maximum_principle hud hul hn hf x hx
  dsimp [u] at hh
  linarith

lemma reaction_shiftedDilation {a : ℝ} (ha : 0 < a) (d v : ℝ) :
    reaction d (a^4*v + (1-a^4)) = a^6 * reaction d v := by
  unfold reaction
  rw [show a^4*v+(1-a^4)-1 = a^4*(v-1) by ring]
  rw [show max (a^4*(v-1)) 0 = a^4 * max (v-1) 0 by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _), mul_zero]]
  rw [Real.mul_rpow (pow_nonneg ha.le _) (le_max_right _ _)]
  have hp : (a^4)^(3/2:ℝ) = a^6 := by
    rw [← Real.rpow_natCast a 4, ← Real.rpow_mul ha.le]
    norm_num
  rw [hp]
  ring

lemma FiniteProfile.shifted_dilation_regular {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (shiftedDilation a F) x := by
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  exact (((hF.regular _ hax).comp x (contDiffAt_id.const_smul a)).const_smul (a^4)).add contDiffAt_const

lemma FiniteProfile.shifted_dilation_equation {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) (x : Space) (hx : x ≠ 0) :
    Δ (shiftedDilation a F) x = reaction d (shiftedDilation a F x) := by
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  have hc : ContDiffAt ℝ 2 (fun y : Space => F (a • y)) x :=
    (hF.regular _ hax).comp x (contDiffAt_id.const_smul a)
  have hs : Δ (fun y : Space => (a^4) • F (a • y)) x =
      (a^4) • Δ (fun y : Space => F (a • y)) x := laplacian_smul (a^4) hc
  change (Δ ((fun y : Space => (a^4) • F (a • y)) + (fun _ : Space => 1-a^4)) : Space → ℝ) x = _
  rw [(hc.const_smul (a^4)).laplacian_add
    (show ContDiffAt ℝ 2 (fun _ : Space => 1-a^4) x from contDiffAt_const),
    hs, laplacian_const, Pi.zero_apply, add_zero,
    laplacian_comp_dilation a x (hF.regular _ hax), hF.equation _ hax]
  rw [shiftedDilation, reaction_shiftedDilation ha]
  simp only [smul_eq_mul]
  ring

lemma FiniteProfile.shifted_dilation_near {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∃ b > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ b → shiftedDilation a F x ≤ a^3*Z/‖x‖ + C := by
  obtain ⟨C, hC, b, hb, hn⟩ := hF.nucleus
  refine ⟨a^4*C+2, by positivity, b/a, div_pos hb ha, ?_⟩
  intro x hx hxb
  have hnorm : ‖a • x‖ = a*‖x‖ := by rw [norm_smul, Real.norm_of_nonneg ha.le]
  have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
  have htt : ‖a • x‖ ≤ b := by rw [hnorm]; nlinarith [(le_div_iff₀ ha).mp hxb]
  have hh := (abs_le.mp (hn _ hax htt)).2
  rw [hnorm] at hh
  have hi := mul_le_mul_of_nonneg_left hh (pow_nonneg ha.le 4)
  have he : a^4 * (Z/(a*‖x‖)) = a^3*Z/‖x‖ := by field_simp
  unfold shiftedDilation
  rw [mul_sub, he] at hi
  nlinarith [pow_nonneg ha.le 4]

lemma FiniteProfile.shifted_dilation_far {d Z : ℝ} {F : Space → ℝ}
    (hF : FiniteProfile d Z F) {a : ℝ} (ha : 1 ≤ a) :
    ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → shiftedDilation a F x ≤ ε := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  intro ε hε
  obtain ⟨R, hR, hb⟩ := hF.decay (ε/a^4) (by positivity)
  refine ⟨R/a, div_pos hR ha0, ?_⟩
  intro x hx
  have hh : R ≤ ‖a • x‖ := by
    rw [norm_smul, Real.norm_of_nonneg ha0.le]
    nlinarith [(div_le_iff₀ ha0).mp hx]
  have hf := (abs_lt.mp (hb _ hh)).2
  have hg := (lt_div_iff₀ (pow_pos ha0 4)).mp hf
  have hp : 1 ≤ a^4 := one_le_pow₀ ha
  unfold shiftedDilation
  nlinarith

end CoulombPDE

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_WeakPuncturedMaximumBarrier
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
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma punctured_test_integrable {u g : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) : Integrable (fun x => u x*g x) :=
  continuousOn_mul_integrable_support hcg (hu.mono hs) hg (subset_tsupport g)

lemma punctured_laplacian_pairing_integrable {u g : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) : Integrable (fun x => u x*Δ g x) :=
  continuousOn_mul_integrable_support hcg (hu.mono hs) (tfLaplacian_continuous hg)
    (tfLaplacian_support hg)

theorem weak_annular_maximum {a R : ℝ} (ha : 0 < a) {u : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | x ≠ 0 ∧ ‖x‖ ≤ R ∧ 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x)
    (hb : ∀ x, ‖x‖ = a ∨ ‖x‖ = R → u x ≤ 0) :
    ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → u x ≤ 0 := by
  let K : Set Space := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  have hk : IsCompact K := by
    have he : K = closedBall (0 : Space) R ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [K,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hn (x : Space) (hx : x ∈ K) : x ≠ 0 :=
    norm_pos_iff.mp (ha.trans_le hx.1)
  have hb' (x : Space) (hx : x ∈ K) (hi : x ∉ interior K) : u x ≤ 0 := by
    apply hb
    by_contra! h
    have ha' : a < ‖x‖ := lt_of_le_of_ne hx.1 h.1.symm
    have hr' : ‖x‖ < R := lt_of_le_of_ne hx.2 h.2
    apply hi
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨ha',hr'⟩)
    exact fun y hy => ⟨hy.1.le,hy.2.le⟩
  have hm := weak_subharmonic_positive_compact hk (hu.mono (fun x hx => hn x hx)) hb'
    (fun g hg hcg hs hgn => hw g hg hcg
      (fun x hx => ⟨hn x (interior_subset (hs hx).1),(interior_subset (hs hx).1).2,(hs hx).2⟩) hgn)
  exact fun x hx hxR => hm x ⟨hx,hxR⟩

theorem weak_punctured_ball_maximum {R : ℝ} {u : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | x ≠ 0 ∧ ‖x‖ ≤ R ∧ 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x)
    (hb : ∀ x, ‖x‖ = R → u x ≤ 0)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R → u x ≤ 0 := by
  obtain ⟨a,ha,hnear⟩ := hz
  intro x hx hxR
  by_cases hxa : ‖x‖ ≤ a
  · exact hnear x hx hxa
  · exact weak_annular_maximum ha hu hw (fun y hy => by
      rcases hy with hy | hy
      · exact hnear y (norm_pos_iff.mp (hy ▸ ha)) hy.le
      · exact hb y hy) x (le_of_not_ge hxa) hxR

theorem weak_global_punctured_maximum {u : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | x ≠ 0 ∧ 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0)
    (hinfty : ∃ R > 0, ∀ x, R ≤ ‖x‖ → u x ≤ 0) :
    ∀ x, x ≠ 0 → u x ≤ 0 := by
  obtain ⟨R,_hR,hfar⟩ := hinfty
  intro x hx
  by_cases hxr : R ≤ ‖x‖
  · exact hfar x hxr
  · exact weak_punctured_ball_maximum hu
      (fun g hg hcg hs hgn => hw g hg hcg (fun x hx => ⟨(hs hx).1,(hs hx).2.2⟩) hgn)
      (fun y hy => hfar y hy.ge) hz
      x hx (le_of_not_ge hxr)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_PuncturedGreenBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

lemma punctured_laplacian_green {f g : TFSpace → ℝ}
    (hf : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 f x)
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) :
    (∫ x, f x*Δ g x) = ∫ x, Δ f x*g x := by
  have hn : (tsupport g)ᶜ ∈ 𝓝 (0 : TFSpace) :=
    (isClosed_tsupport g).isOpen_compl.mem_nhds (by
      intro hh
      exact hs hh rfl)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hn
  let b : ContDiffBump (0 : TFSpace) := ⟨r/4,r/2,by positivity,by linarith⟩
  let F : TFSpace → ℝ := fun x => (1-b x)*f x
  have hF : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : TFSpace) b.rIn_pos] with z hz
      simp only [F,b.one_of_mem_closedBall (ball_subset_closedBall hz),sub_self,zero_mul]
    · exact (contDiffAt_const.sub b.contDiffAt).mul (hf x hx)
  have he {x : TFSpace} (hx : x ∈ tsupport g) : F =ᶠ[𝓝 x] f := by
    have hxr : r ≤ ‖x‖ := by
      by_contra! hh
      exact hrs (by simpa only [mem_ball,dist_zero_right] using hh) hx
    have hxb : b.rOut < ‖x‖ := by dsimp [b]; linarith
    filter_upwards [continuous_norm.continuousAt.eventually (Ioi_mem_nhds hxb)] with z hz
    simp only [F,b.zero_of_le_dist (by simpa only [dist_zero_right] using hz.le),sub_zero,one_mul]
  calc
    _ = ∫ x, F x*Δ g x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : Δ g x = 0
        · simp only [hx,mul_zero]
        · change f x*Δ g x = F x*Δ g x
          rw [(he (tfLaplacian_support hg hx)).eq_of_nhds]
    _ = ∫ x, Δ F x*g x := compact_laplacian_green hF hg hcg
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : g x = 0
        · simp only [hx,mul_zero]
        · change Δ F x*g x = Δ f x*g x
          rw [(laplacian_congr_nhds (he (subset_tsupport g hx))).eq_of_nhds]

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

open CoulombAtom

lemma PuncturedPoisson.of_classical {u : Space → ℝ}
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 u x) : PuncturedPoisson u (Δ u) :=
  fun _ hg hcg hs => punctured_laplacian_green hu hg hcg hs

lemma PuncturedPoisson.congr_source {u f h : Space → ℝ} (hu : PuncturedPoisson u f)
    (he : EqOn f h {0}ᶜ) : PuncturedPoisson u h := by
  intro g hg hcg hs
  rw [hu g hg hcg hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : g x = 0
    · simp only [hx,mul_zero]
    · change f x*g x = h x*g x
      rw [he (hs (subset_tsupport g hx))]

lemma PuncturedPoisson.sub {u v f h : Space → ℝ}
    (hu : PuncturedPoisson u f) (hv : PuncturedPoisson v h)
    (huc : ContinuousOn u {0}ᶜ) (hvc : ContinuousOn v {0}ᶜ)
    (hfc : ContinuousOn f {0}ᶜ) (hhc : ContinuousOn h {0}ᶜ) :
    PuncturedPoisson (u-v) (f-h) := by
  intro g hg hcg hs
  have hui := punctured_laplacian_pairing_integrable huc hg hcg hs
  have hvi := punctured_laplacian_pairing_integrable hvc hg hcg hs
  have hfi := punctured_test_integrable hfc hg.continuous hcg hs
  have hhi := punctured_test_integrable hhc hg.continuous hcg hs
  change (∫ x, (u x-v x)*Δ g x) = ∫ x, (f x-h x)*g x
  simp_rw [sub_mul]
  rw [integral_sub hui hvi,integral_sub hfi hhi,hu g hg hcg hs,hv g hg hcg hs]

lemma PuncturedPoisson.const_mul {u f : Space → ℝ} (hu : PuncturedPoisson u f) (a : ℝ) :
    PuncturedPoisson (fun x => a*u x) (fun x => a*f x) := by
  intro g hg hcg hs
  change (∫ x, (a*u x)*Δ g x) = ∫ x, (a*f x)*g x
  simp_rw [mul_assoc]
  rw [integral_const_mul,integral_const_mul,hu g hg hcg hs]

lemma PuncturedPoisson.constant (c : ℝ) : PuncturedPoisson (fun _ => c) (fun _ => 0) := by
  intro g hg hcg _
  simp only [zero_mul,integral_zero]
  rw [integral_const_mul,compact_laplacian_mass hg hcg,mul_zero]

lemma PuncturedPoisson.add_const {u f : Space → ℝ} (hu : PuncturedPoisson u f)
    (huc : ContinuousOn u {0}ᶜ) (hfc : ContinuousOn f {0}ᶜ) (c : ℝ) :
    PuncturedPoisson (fun x => u x+c) f := by
  have hh := hu.sub (PuncturedPoisson.constant (-c)) huc continuousOn_const hfc continuousOn_const
  convert hh using 1 <;> (try funext x) <;> simp

lemma PuncturedPoisson.nonneg_on {u f : Space → ℝ}
    (hu : PuncturedPoisson u f) {U : Set Space} (hU : U ⊆ {0}ᶜ)
    (hf : ∀ x ∈ U, 0 ≤ f x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ U) (hgn : ∀ x, 0 ≤ g x) :
    0 ≤ ∫ x, u x*Δ g x := by
  rw [hu g hg hcg (hs.trans hU)]
  apply integral_nonneg
  intro x
  by_cases hx : g x = 0
  · simp only [hx,mul_zero,Pi.zero_apply,le_refl]
  · exact mul_nonneg (hf x (hs (subset_tsupport g hx))) (hgn x)

lemma PuncturedPoisson.nonneg_on_positive {u f : Space → ℝ}
    (hu : PuncturedPoisson u f)
    (hf : ∀ x, x ≠ 0 → 0 < u x → 0 ≤ f x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {x | x ≠ 0 ∧ 0 < u x}) (hgn : ∀ x, 0 ≤ g x) :
    0 ≤ ∫ x, u x*Δ g x := by
  rw [hu g hg hcg (fun x hx => (hs hx).1)]
  apply integral_nonneg
  intro x
  by_cases hx : g x = 0
  · simp only [hx,mul_zero,Pi.zero_apply,le_refl]
  · have hh := hs (subset_tsupport g hx)
    exact mul_nonneg (hf x hh.1 hh.2) (hgn x)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RotationShellBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology

namespace CoulombAtom

lemma rotation_integral_inverse {f : SpatialRotation → ℝ} (hf : Continuous f) :
    (∫ g, f g⁻¹ ∂rotationMeasure) = ∫ g, f g ∂rotationMeasure := by
  have hi : Integrable (fun q : SpatialRotation × SpatialRotation => f (q.1⁻¹*q.2))
      (rotationMeasure.prod rotationMeasure) :=
    (hf.comp (continuous_fst.inv.mul continuous_snd)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))
  have hx (x : SpatialRotation) : (∫ y, f (x⁻¹*y) ∂rotationMeasure) = ∫ y, f y ∂rotationMeasure :=
    rotation_integral_left f x⁻¹
  have hy (y : SpatialRotation) : (∫ x, f (x⁻¹*y) ∂rotationMeasure) = ∫ x, f x⁻¹ ∂rotationMeasure := by
    rw [←rotation_integral_left (fun x => f (x⁻¹*y)) y]
    simp only [mul_inv_rev,inv_mul_cancel_right]
  calc
    _ = ∫ y, ∫ x, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := by
      simp only [hy,integral_const,probReal_univ,smul_eq_mul,one_mul]
    _ = ∫ x, ∫ y, f (x⁻¹*y) ∂rotationMeasure ∂rotationMeasure := integral_integral_swap hi.swap
    _ = _ := by simp only [hx,integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma rotate_inv_rotate (g : SpatialRotation) (p : Space) :
    rotate g⁻¹ (rotate g p) = p := by
  rw [←rotate_mul,inv_mul_cancel,rotate_one]

lemma rotate_kernel_inverse (g : SpatialRotation) (p z : Space) :
    ‖rotate g p-z‖ = ‖p-rotate g⁻¹ z‖ := by
  rw [←(rotate g⁻¹).norm_map (rotate g p-z),(rotate g⁻¹).map_sub,rotate_inv_rotate]

lemma rotation_kernel_inner (p z : Space) (hz : ‖z‖ < ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) = 1/‖p‖ := by
  simp_rw [rotate_kernel_inverse]
  have hc : Continuous (fun g : SpatialRotation => rotate g z) :=
    continuous_subtype_val.clm_apply continuous_const
  have hn (g : SpatialRotation) : ‖p-rotate g z‖ ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp (norm_eq_zero.mp he)
    have hh : ‖p‖ = ‖z‖ := by rw [he',(rotate g).norm_map]
    linarith
  have hfi : Continuous (fun g : SpatialRotation => (1:ℝ)/‖p-rotate g z‖) :=
    continuous_const.div (continuous_const.sub hc).norm hn
  rw [rotation_integral_inverse hfi]
  exact rotation_kernel_newton z p hz

theorem rotation_kernel_shell (p z : Space) (h : ‖z‖ ≠ ‖p‖) :
    (∫ g : SpatialRotation, 1/‖rotate g p-z‖ ∂rotationMeasure) =
      1/max ‖p‖ ‖z‖ := by
  rcases lt_or_gt_of_ne h with hz | hz
  · rw [max_eq_left hz.le]
    exact rotation_kernel_inner p z hz
  · rw [max_eq_right hz.le]
    simp_rw [norm_sub_rev (rotate _ p) z]
    exact rotation_kernel_newton p z hz

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_SphericalMeanFieldBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
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

lemma potential_rotation_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    Integrable (fun g : SpatialRotation => tfPotential ρ (rotate g p)) rotationMeasure :=
  ((bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.comp
    (continuous_subtype_val.clm_apply continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))

lemma rotation_density_kernel_measurable {ρ : Space → ℝ}
    (hm : Measurable ρ) (p : Space) :
    Measurable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖) := by
  have hg : Continuous (fun q : SpatialRotation × Space => rotate q.1 p) :=
    continuous_subtype_val.fst'.clm_apply continuous_const
  exact (hm.comp measurable_snd).div (hg.sub continuous_snd).norm.measurable

lemma rotation_density_kernel_normIntegral {ρ : Space → ℝ}
    (hn : ∀ z, 0 ≤ ρ z) (p : Space) (g : SpatialRotation) :
    (∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) = tfPotential ρ (rotate g p) := by
  change (∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) = ∫ z : Space, ρ z/‖rotate g p-z‖
  exact integral_congr_ae (ae_of_all _ (fun z => Real.norm_of_nonneg
    (div_nonneg (hn z) (norm_nonneg _))))

lemma rotation_density_kernel_integrable {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    Integrable (fun q : SpatialRotation × Space => ρ q.2/‖rotate q.1 p-q.2‖)
      (rotationMeasure.prod volume) := by
  refine (integrable_prod_iff (μ := rotationMeasure) (ν := volume)
    (rotation_density_kernel_measurable hm p).aestronglyMeasurable).mpr ⟨?_,?_⟩
  · exact ae_of_all _ (fun g => bounded_L1_potential_integrable hm hi hM hn hb (rotate g p))
  · have he : (fun g : SpatialRotation => ∫ z : Space, ‖ρ z/‖rotate g p-z‖‖) =
        fun g => tfPotential ρ (rotate g p) :=
      funext (rotation_density_kernel_normIntegral hn p)
    rw [he]
    exact potential_rotation_integrable hm hi hM hn hb p

theorem sphereMean_potential {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (p : Space) :
    sphereMean (tfPotential ρ) p = ∫ z, ρ z/max ‖p‖ ‖z‖ := by
  have hs : ∀ᵐ z : Space, ‖z‖ ≠ ‖p‖ := by
    apply ae_iff.mpr
    have he : {a : Space | ¬ ‖a‖ ≠ ‖p‖} = sphere (0:Space) ‖p‖ := by
      ext a
      simp only [mem_ofPred_eq,not_not,mem_sphere,dist_zero_right]
    rw [he]
    exact Measure.addHaar_sphere volume (0:Space) ‖p‖
  calc
    _ = ∫ g : SpatialRotation, ∫ z : Space, ρ z/‖rotate g p-z‖ ∂volume ∂rotationMeasure := rfl
    _ = ∫ z : Space, ∫ g : SpatialRotation, ρ z/‖rotate g p-z‖ ∂rotationMeasure :=
      integral_integral_swap (rotation_density_kernel_integrable hm hi hM hn hb p)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hs] with z hz
      rw [show (fun g : SpatialRotation => ρ z/‖rotate g p-z‖) =
        fun g => ρ z*(1/‖rotate g p-z‖) by funext g; ring,
        integral_const_mul,rotation_kernel_shell p z hz,mul_one_div]

lemma density_shell_integrable {ρ : Space → ℝ} (hm : Measurable ρ) (hi : Integrable ρ)
    (hn : ∀ z, 0 ≤ ρ z) {p : Space} (hp : p ≠ 0) :
    Integrable (fun z => ρ z/max ‖p‖ ‖z‖) := by
  apply (hi.div_const ‖p‖).mono' (hm.div (measurable_const.max measurable_norm)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖ρ z/max ‖p‖ ‖z‖‖ ≤ ρ z/‖p‖
    rw [Real.norm_of_nonneg (div_nonneg (hn z) (le_max_of_le_left (norm_nonneg p)))]
    exact div_le_div_of_nonneg_left (hn z) (norm_pos_iff.mpr hp) (le_max_left _ _)

theorem sphereMean_field_bracket {ρ : Space → ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) {M : ℝ} (hM : 0 ≤ M)
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M) (Z : ℝ) {p : Space} (hp : p ≠ 0) :
    0 ≤ sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ ∧
    sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ ≤
      (∫ z in {z : Space | ‖p‖ < ‖z‖}, ρ z)/‖p‖ := by
  have hp0 := norm_pos_iff.mpr hp
  have hsh := density_shell_integrable hm hi hn hp
  have hrem := (hi.div_const ‖p‖).sub hsh
  have he : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p-(Z-∫ z, ρ z)/‖p‖ =
      ∫ z, ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ := by
    have hf : sphereMean (fun x => Z/‖x‖-tfPotential ρ x) p =
        Z/‖p‖-sphereMean (tfPotential ρ) p := by
      unfold sphereMean
      simp only [(rotate _).norm_map]
      rw [integral_sub (integrable_const _) (potential_rotation_integrable hm hi hM hn hb p)]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [hf,sphereMean_potential hm hi hM hn hb p,
      integral_sub (hi.div_const _) hsh,integral_div]
    ring
  rw [he]
  have hnrem (z : Space) : 0 ≤ ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ :=
    sub_nonneg.mpr (div_le_div_of_nonneg_left (hn z) hp0 (le_max_left _ _))
  refine ⟨integral_nonneg hnrem,?_⟩
  let T : Set Space := {z | ‖p‖ < ‖z‖}
  have hT : MeasurableSet T := measurableSet_lt measurable_const measurable_norm
  have ht := (hi.indicator hT).div_const ‖p‖
  have hbrem (z : Space) : ρ z/‖p‖-ρ z/max ‖p‖ ‖z‖ ≤ T.indicator ρ z/‖p‖ := by
    by_cases hz : z ∈ T
    · rw [indicator_of_mem hz]
      exact sub_le_self _ (div_nonneg (hn z) (le_max_of_le_left (norm_nonneg p)))
    · have hzr : ‖z‖ ≤ ‖p‖ := le_of_not_gt hz
      rw [indicator_of_notMem hz,max_eq_left hzr,sub_self,zero_div]
  calc
    _ ≤ ∫ z, T.indicator ρ z/‖p‖ := integral_mono hrem ht hbrem
    _ = _ := by rw [integral_div,integral_indicator hT]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfReactionCoefficient
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

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
section
open CoulombAtom

namespace TFUnitData
variable {Z : ℝ} (D : TFUnitData Z)

lemma field_radial : IsRadial D.field := by
  intro x y hxy
  unfold field tfField
  rw [hxy, tfPotential_radial D.radial x y hxy]

lemma charge_equation {r : ℝ} (hr : 0 < r) (hZ : 0 < Z) :
    HasDerivAt D.charge (-r^2 * CoulombPDE.reaction tfReactionCoefficient (D.radialField r)) r := by
  have hh := D.charge_hasDerivAt hr
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  have hray : D.radialField r = tfField Z D.density (r • radialAxis) := D.radialField_ray hZ hr
  rw [radialTrace, D.euler, tfEulerDensity, ← hray]
  unfold CoulombPDE.reaction tfReactionCoefficient
  rw [Real.div_rpow (le_max_right _ _) (mul_pos (by norm_num) tfKinetic_pos).le]
  ring

lemma deriv_bound (hZ : 0 < Z) {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    ‖deriv D.radialField r‖ ≤ slopeCap a := by
  rw [(D.radialField_hasDerivAt (ha.trans_le hr)).deriv,
    norm_div, norm_neg, Real.norm_of_nonneg (D.charge_nonneg hZ r), Real.norm_of_nonneg (sq_nonneg r)]
  exact (div_le_div_of_nonneg_right (D.charge_le_cap hZ ha hr) (sq_nonneg r)).trans
    (div_le_div_of_nonneg_left (chargeCap_pos ha).le (sq_pos_of_pos ha) (by nlinarith))

lemma lipschitz (hZ : 0 < Z) {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨slopeCap a, (slopeCap_pos ha).le⟩ D.radialField (Ici a) := by
  apply (convex_Ici a).lipschitzOnWith_of_nnnorm_deriv_le
    (fun r hr => (D.radialField_hasDerivAt (ha.trans_le hr)).differentiableAt)
  exact fun r hr => D.deriv_bound hZ ha hr

end TFUnitData
end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakHarmonicRegularityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakHarmonicRegularity_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology Convolution ContDiff

open CoulombAtom CoulombBarrier

lemma packetSmooth_mean (r : ℝ) (v : Space → ℝ) (x : Space) :
    packetSmooth r v x = ∫ z, packetDensity x r z*v z := by
  rw [packetSmooth,convolution_eq_swap]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change packetDensity 0 r (x-z)*v z = packetDensity x r z*v z
    rw [packetDensity_translate x r z]
    exact congrArg (fun a : ℝ => a*v z)
      (packetDensity_radial r (x-z) (z-x) (norm_sub_rev x z))

theorem weak_harmonic_regular_at {u : Space → ℝ} {y : Space} {S : ℝ}
    (hS : 0 < S) (hu : ContinuousOn u (closedBall y S))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∫ x, u x*Δ g x) = 0) :
    ContDiffAt ℝ ∞ u y ∧ Δ u y = 0 := by
  let f : C(closedBall y S,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall y S) : v z = u z :=
    congrArg (fun h : C(closedBall y S,ℝ) => h ⟨z,hz⟩) hv
  have hvw (g : Space → ℝ) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
      (hs : tsupport g ⊆ ball y S) : (∫ x, v x*Δ g x) = 0 := by
    rw [←hw g hg hcg hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : Δ g x = 0
      · simp only [hx,mul_zero]
      · change v x*Δ g x = u x*Δ g x
        rw [he x (ball_subset_closedBall (hs (tfLaplacian_support hg hx)))]
  let r := S/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrS : r < S/2 := by dsimp [r]; linarith
  have hws : ContDiff ℝ ∞ (packetSmooth r v) := packetSmooth_contDiff hr v.continuous
  have heq : packetSmooth r v =ᶠ[𝓝 y] u := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    have hzdist : dist z y < r := hz
    have hsub : ball z (S/2) ⊆ ball y S := by
      intro x hx
      have hd : dist x z < S/2 := hx
      have ht := dist_triangle x z y
      change dist x y < S
      dsimp [r] at hzdist
      linarith
    rw [packetSmooth_mean,weak_harmonic_packet_mean v.continuous z hr hrS
      (fun g hg hcg hs => hvw g hg hcg (hs.trans hsub)),he z]
    exact mem_closedBall.mpr (hzdist.le.trans (by dsimp [r]; linarith))
  have hlap : Δ (packetSmooth r v) y = 0 := by
    let k := packetDensity 0 r
    have hk : ContDiff ℝ 2 k := (packetDensity_smooth 0 r).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    have hkc : HasCompactSupport k := packetDensity_compact 0 hr
    have hkg : ContDiff ℝ 2 (fun x => k (y-x)) := hk.comp (contDiff_const.sub contDiff_id)
    have hcg : HasCompactSupport (fun x => k (y-x)) :=
      hkc.comp_homeomorph (Homeomorph.subLeft y)
    have hsg : tsupport (fun x => k (y-x)) ⊆ ball y S :=
      (tsupport_sub_left (fun z hz => by
        simpa only [sub_zero] using packetDensity_support 0 hr hz) y).trans
          (closedBall_subset_ball (by dsimp [r]; linarith))
    have htest := hvw _ hkg hcg hsg
    have hflip : k ⋆[newtonMul] (v:Space → ℝ) = (v:Space → ℝ) ⋆[newtonMul] k := by
      simpa only [newtonMul_flip_eq] using (convolution_flip newtonMul (f := (v:Space → ℝ)) (g := k))
    change Δ (k ⋆[newtonMul] (v:Space → ℝ)) y = 0
    rw [hflip,laplacian_convolution v.continuous.locallyIntegrable hkc hk]
    simp_rw [laplacian_sub_left hk] at htest
    exact htest
  exact ⟨hws.contDiffAt.congr_of_eventuallyEq heq.symm,
    (laplacian_congr_nhds heq).eq_of_nhds.symm.trans hlap⟩

end Work_WeakHarmonicRegularity_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

theorem weak_harmonic_bounded_above_constant {u : Space → ℝ} (hu : Continuous u)
    {K : ℝ} (hb : ∀ x, u x ≤ K)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∫ x, u x*Δ g x) = 0) : ∀ x, u x = u 0 := by
  obtain ⟨C,hC,hosc⟩ := exists_weak_harmonic_oscillation_constant
  intro x
  have he (R : ℝ) (hR : 0 < R) (hx : ‖x‖ ≤ R/2) :
      |u x-u 0| ≤ C/R*‖x‖*(K-u 0) := by
    have hh := hosc (fun z => K-u z) R hR (continuous_const.sub hu).continuousOn
      (fun z _ => sub_nonneg.mpr (hb z))
      (fun g hg hcg hsg => weak_harmonic_upper_distance hu K
        (fun φ hφ hcφ _ => hw φ hφ hcφ) hg hcg hsg) x hx
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [show K-u x-(K-u 0) = -(u x-u 0) by ring, abs_neg]
  have hlim : Tendsto (fun R : ℝ => C/R*‖x‖*(K-u 0)) atTop (𝓝 0) := by
    simpa only [id_eq,zero_mul] using ((tendsto_const_nhds.div_atTop tendsto_id).mul_const ‖x‖).mul_const (K-u 0)
  have hle : |u x-u 0| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [eventually_gt_atTop (max 1 (2*‖x‖))] with R hR
    exact he R (by linarith [le_max_left 1 (2*‖x‖)])
      (by linarith [le_max_right 1 (2*‖x‖)]))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

lemma compact_source_weak_poisson {ρ : Space → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) :
    (∫ x, tfPotential ρ x*Δ g x) = -(4*Real.pi)*(∫ x, ρ x*g x) := by
  obtain ⟨R,_,hR⟩ := hcρ.isBounded.exists_pos_norm_le
  obtain ⟨S,_,hS⟩ := hcg.isBounded.exists_pos_norm_le
  apply tfPotential_weak_laplacian_ball (hρ.memLp_of_hasCompactSupport hcρ)
    (S := max R S+1) _ hg hcg
  · intro x hx
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (hS x hx)
      (lt_of_le_of_lt (le_max_right R S) (lt_add_one _)))
  · intro x hx
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (hR x (subset_tsupport ρ hx))
      (lt_of_le_of_lt (le_max_left R S) (lt_add_one _)))

theorem compact_laplacian_representation {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (hcu : HasCompactSupport (Δ u)) {K : ℝ} (hb : ∀ x, u x ≤ K) :
    ∃ A : ℝ, ∀ x, u x = A-tfPotential (fun y => Δ u y/(4*Real.pi)) x := by
  let ρ := fun y => Δ u y/(4*Real.pi)
  have hρ : Continuous ρ := (tfLaplacian_continuous hu).div_const _
  have hcρ : HasCompactSupport ρ := hcu.mul_right
  have hp : Continuous (tfPotential ρ) := tfPotential_continuous
    (hρ.integrable_of_hasCompactSupport hcρ) (hρ.memLp_of_hasCompactSupport hcρ)
  obtain ⟨P,hP⟩ := compact_potential_bounded hρ hcρ
  have hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∫ x, (u x+tfPotential ρ x)*Δ g x) = 0 := by
    intro g hg hcg
    have hi₁ : Integrable (fun x => u x*Δ g x) :=
      (hu.continuous.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    have hi₂ : Integrable (fun x => tfPotential ρ x*Δ g x) :=
      (hp.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    simp_rw [add_mul]
    rw [integral_add hi₁ hi₂,compact_laplacian_green hu hg hcg,
      compact_source_weak_poisson hρ hcρ hg hcg]
    have he : (fun x => ρ x*g x) = fun x => (Δ u x*g x)/(4*Real.pi) := by
      funext x
      dsimp [ρ]
      ring
    rw [he,integral_div]
    field_simp
    ring
  have hh := weak_harmonic_bounded_above_constant (hu.continuous.add hp)
    (u := fun x => u x+tfPotential ρ x)
    (K := K+P) (fun x => add_le_add (hb x)
      ((le_abs_self (tfPotential ρ x)).trans (hP x))) hw
  refine ⟨u 0+tfPotential ρ 0,fun x => ?_⟩
  have ht := hh x
  change u x = u 0+tfPotential ρ 0-tfPotential ρ x
  linarith only [ht]

theorem compact_laplacian_uniform_limit {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (hcu : HasCompactSupport (Δ u)) {K : ℝ} (hb : ∀ x, u x ≤ K) :
    ∃ A : ℝ, ∀ ε > 0, ∃ R > 0, ∀ x : Space, R ≤ ‖x‖ → |u x-A| < ε := by
  obtain ⟨A,hA⟩ := compact_laplacian_representation hu hcu hb
  let ρ := fun y => Δ u y/(4*Real.pi)
  have hρ : Continuous ρ := (tfLaplacian_continuous hu).div_const _
  have hcρ : HasCompactSupport ρ := hcu.mul_right
  obtain ⟨S,_,hS⟩ := hcρ.isBounded.exists_pos_norm_le
  refine ⟨A,?_⟩
  intro ε hε
  obtain ⟨R,hR,hdec⟩ := tfPotential_compact_decay
    (hρ.integrable_of_hasCompactSupport hcρ) (hρ.memLp_of_hasCompactSupport hcρ)
    (fun y hy => hS y (subset_tsupport ρ hy)) (ε/2) (by positivity)
  refine ⟨R,hR,fun x hx => ?_⟩
  rw [hA x,sub_sub_cancel_left,abs_neg]
  exact (hdec x hx).trans_lt (by linarith)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SphericalMeanLimitBarrier
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
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

lemma rotate_ne_zero (g : SpatialRotation) {p : Space} (hp : p ≠ 0) :
    rotate g p ≠ 0 := norm_pos_iff.mp (by simpa only [(rotate g).norm_map] using norm_pos_iff.mpr hp)

lemma sphereFunction_integrable {u : Space → ℝ}
    (hu : ∀ x, x ≠ 0 → ContinuousAt u x) {p : Space} (hp : p ≠ 0) :
    Integrable (fun g : SpatialRotation => u (rotate g p)) rotationMeasure := by
  have hrot : Continuous (fun g : SpatialRotation => rotate g p) :=
    continuous_subtype_val.clm_apply continuous_const
  have hc : Continuous (fun g : SpatialRotation => u (rotate g p)) := by
    apply continuous_iff_continuousAt.mpr
    intro g
    exact (hu _ (rotate_ne_zero g hp)).comp (f := fun t : SpatialRotation => rotate t p) hrot.continuousAt
  exact hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _))

lemma sphereMean_close_to_constant {u : Space → ℝ} {p : Space} {A ε : ℝ}
    (hi : Integrable (fun g : SpatialRotation => u (rotate g p)) rotationMeasure)
    (hb : ∀ x, ‖x‖ = ‖p‖ → |u x-A| ≤ ε) :
    |sphereMean u p-A| ≤ ε := by
  have hn := norm_integral_le_of_norm_le_const (μ := rotationMeasure)
    (f := fun g : SpatialRotation => u (rotate g p)-A)
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb _ ((rotate g).norm_map p)))
  rw [integral_sub hi (integrable_const A)] at hn
  simpa only [sphereMean,integral_const,probReal_univ,smul_eq_mul,one_mul,mul_one,
    Real.norm_eq_abs] using hn

lemma sphereMean_tendsto_of_uniform {ι : Type*} {l : Filter ι}
    {f : ι → Space → ℝ} {u : Space → ℝ} {p : Space}
    (hi : ∀ i, Integrable (fun g : SpatialRotation => f i (rotate g p)) rotationMeasure)
    (hu : Integrable (fun g : SpatialRotation => u (rotate g p)) rotationMeasure)
    (hconv : TendstoUniformlyOn f u l (sphere (0:Space) ‖p‖)) :
    Tendsto (fun i => sphereMean (f i) p) l (𝓝 (sphereMean u p)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := Metric.tendstoUniformlyOn_iff.mp hconv (ε/2) (by positivity)
  filter_upwards [he] with i hei
  have hn := norm_integral_le_of_norm_le_const (μ := rotationMeasure)
    (f := fun g : SpatialRotation => f i (rotate g p)-u (rotate g p))
    (ae_of_all _ (fun g => by
      have hh := hei (rotate g p) (by simpa only [mem_sphere,dist_zero_right] using (rotate g).norm_map p)
      simpa only [Real.dist_eq,Real.norm_eq_abs,abs_sub_comm] using hh.le))
  rw [integral_sub (hi i) hu] at hn
  have hn' : |sphereMean (f i) p-sphereMean u p| ≤ ε/2 := by
    simpa only [sphereMean,probReal_univ,mul_one,Real.norm_eq_abs] using hn
  rw [Real.dist_eq]
  linarith

attribute [local irreducible] tfPotential sphereMean

lemma mean_charge_of_bracket {ι : Type*} {l : Filter ι} [NeBot l]
    {a b t : ι → ℝ} {A B : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (ht : Tendsto t l (𝓝 0)) (hn : ∀ i, 0 ≤ a i-b i)
    (hu : ∀ i, a i-b i ≤ t i) : A = B := by
  have hzero := squeeze_zero hn hu ht
  exact sub_eq_zero.mp (tendsto_nhds_unique (ha.sub hb) hzero)

theorem sphericalMean_limit_charge {ι : Type*} {l : Filter ι} [NeBot l]
    {ρ : ι → Space → ℝ} {Z : ι → ℝ} {u : Space → ℝ} {q : ℝ} {p : Space}
    (hp : p ≠ 0) (hm : ∀ i, Measurable (ρ i)) (hi : ∀ i, Integrable (ρ i))
    (hn : ∀ i x, 0 ≤ ρ i x) (hb : ∀ i, ∃ M ≥ 0, ∀ x, ρ i x ≤ M)
    (hu : ∀ x, x ≠ 0 → ContinuousAt u x)
    (hconv : TendstoUniformlyOn (fun i x => Z i/‖x‖-tfPotential (ρ i) x)
      u l (sphere (0:Space) ‖p‖))
    (hq : Tendsto (fun i => Z i-∫ x, ρ i x) l (𝓝 q))
    (htail : Tendsto (fun i => ∫ x in {x : Space | ‖p‖ < ‖x‖}, ρ i x) l (𝓝 0)) :
    sphereMean u p = q/‖p‖ := by
  have hfi (i : ι) : Integrable
      (fun g : SpatialRotation => Z i/‖rotate g p‖-tfPotential (ρ i) (rotate g p)) rotationMeasure := by
    obtain ⟨M,hM,hMb⟩ := hb i
    have hf1 : Integrable (fun _ : SpatialRotation => Z i/‖p‖) rotationMeasure := integrable_const _
    have hf2 := potential_rotation_integrable (hm i) (hi i) hM (hn i) hMb p
    convert hf1.sub hf2 using 1
    all_goals try with_reducible_and_instances rfl
    ext g
    simp only [Pi.sub_apply,(rotate g).norm_map]
  have hs : Tendsto (fun i => sphereMean (fun x => Z i/‖x‖-tfPotential (ρ i) x) p)
      l (𝓝 (sphereMean u p)) :=
    sphereMean_tendsto_of_uniform hfi (sphereFunction_integrable hu hp) hconv
  apply mean_charge_of_bracket hs (hq.div_const ‖p‖)
    (by simpa only [zero_div] using htail.div_const ‖p‖)
  · intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact (sphereMean_field_bracket (hm i) (hi i) hM (hn i) hMb (Z i) hp).1
  · intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact (sphereMean_field_bracket (hm i) (hi i) hM (hn i) hMb (Z i) hp).2

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakExteriorDecayBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

theorem exterior_harmonic_uniform_constant_local {u : Space → ℝ} {R K : ℝ}
    (hR : 0 < R) (hu : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x)
    (hh : ∀ x, R ≤ ‖x‖ → Δ u x = 0) (hb : ∀ x, R ≤ ‖x‖ → u x ≤ K) :
    ∃ A : ℝ, ∀ ε > 0, ∃ S > 0, ∀ x : Space, S ≤ ‖x‖ → |u x-A| < ε := by
  let b : ContDiffBump (0:Space) := ⟨2*R,4*R,by linarith,by linarith⟩
  let v : Space → ℝ := fun x => (1-b x)*u x
  have hv : ContDiff ℝ 2 v := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < 2*R
    · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      have hb : y ∈ closedBall (0:Space) b.rIn := by
        simpa only [mem_closedBall,dist_zero_right] using hy.le
      simp only [v,b.one_of_mem_closedBall hb,sub_self,zero_mul]
    · exact (contDiffAt_const.sub b.contDiffAt).mul (hu x (by linarith [le_of_not_gt hx]))
  have he (x : Space) (hx : 4*R < ‖x‖) : v =ᶠ[𝓝 x] u := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
    simp only [v,b.zero_of_le_dist (by simpa only [dist_zero_right] using hy.le),sub_zero,one_mul]
  have hcv : HasCompactSupport (Δ v) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) (4*R))
    intro x hx
    by_contra hn
    have hxr : 4*R < ‖x‖ := lt_of_not_ge (fun h => hn (mem_closedBall_zero_iff.mpr h))
    apply hx
    rw [(laplacian_congr_nhds (he x hxr)).eq_of_nhds]
    exact hh x (by linarith)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:Space) (4*R)).exists_bound_of_continuousOn hv.continuous.continuousOn
  have hvb : ∀ x, v x ≤ max B K := by
    intro x
    by_cases hx : ‖x‖ ≤ 4*R
    · exact (le_abs_self (v x)).trans ((hB x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _))
    · rw [(he x (lt_of_not_ge hx)).eq_of_nhds]
      exact (hb x (by linarith)).trans (le_max_right _ _)
  obtain ⟨A,hA⟩ := compact_laplacian_uniform_limit hv hcv hvb
  refine ⟨A,?_⟩
  intro ε hε
  obtain ⟨S,hS,hdec⟩ := hA ε hε
  refine ⟨max S (4*R+1),hS.trans_le (le_max_left _ _),fun x hx => ?_⟩
  have hsx : S ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hrx : 4*R < ‖x‖ := by linarith [le_trans (le_max_right S (4*R+1)) hx]
  simpa only [(he x hrx).eq_of_nhds] using hdec x hsx

lemma weak_exterior_regular {u : Space → ℝ} {R : ℝ}
    (hu : ContinuousOn u {x | R < ‖x‖})
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0)
    (y : Space) (hy : R < ‖y‖) : ContDiffAt ℝ ∞ u y ∧ Δ u y = 0 := by
  let S := (‖y‖-R)/2
  have hS : 0 < S := by dsimp [S]; linarith
  have hsub : closedBall y S ⊆ {x | R < ‖x‖} := by
    intro x hx
    have hd : dist x y ≤ S := hx
    have ht : ‖y‖ ≤ ‖x‖+dist x y := by
      have hh := norm_le_norm_add_norm_sub x y
      simpa only [dist_eq_norm, norm_sub_rev] using hh
    change R < ‖x‖
    dsimp [S] at hd
    linarith
  exact weak_harmonic_regular_at hS (hu.mono hsub)
    (fun g hg hcg hs => hw g hg hcg (hs.trans (ball_subset_closedBall.trans hsub)))

theorem weak_exterior_mean_uniform_decay {u : Space → ℝ} {R K q : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0)
    (hb : ∀ x, R ≤ ‖x‖ → u x ≤ K)
    (hmean : ∀ p : Space, R < ‖p‖ → sphereMean u p = q/‖p‖) :
    ∀ ε > 0, ∃ S > 0, ∀ x : Space, S ≤ ‖x‖ → |u x| < ε := by
  have huc : ContinuousOn u {x | R < ‖x‖} :=
    hu.mono (fun x hx => norm_pos_iff.mp (hR.trans hx))
  have hreg (x : Space) (hx : R < ‖x‖) : ContDiffAt ℝ 2 u x :=
    (weak_exterior_regular huc hw x hx).1.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hhi (x : Space) (hx : 2*R ≤ ‖x‖) : Δ u x = 0 :=
    (weak_exterior_regular huc hw x (by linarith)).2
  obtain ⟨A,hA⟩ := exterior_harmonic_uniform_constant_local (by linarith : 0 < 2*R)
    (fun x hx => hreg x (by linarith)) hhi (fun x hx => hb x (by linarith))
  have he : A = 0 := by
    by_contra hn
    have ha : 0 < |A| := abs_pos.mpr hn
    obtain ⟨S,hS,hs⟩ := hA (|A|/4) (by positivity)
    let r := max S (max (R+1) (4*|q|/|A|+1))
    have hSr : S ≤ r := le_max_left _ _
    have hRr : R+1 ≤ r := (le_max_left _ _).trans (le_max_right _ _)
    have hqr : 4*|q|/|A|+1 ≤ r := (le_max_right _ _).trans (le_max_right _ _)
    have hr : 0 < r := hS.trans_le hSr
    let p : Space := r • radialAxis
    have hpn : ‖p‖ = r := TFUnitData.ray_norm hr
    have hp : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hpn]; exact hr.ne')
    have hm := sphereMean_close_to_constant (sphereFunction_integrable
      (fun x hx => hu.continuousAt (isOpen_compl_singleton.mem_nhds hx)) hp)
      (fun x hx => (hs x (by rw [hx,hpn]; exact hSr)).le)
    rw [hmean p (by rw [hpn]; linarith),hpn] at hm
    have hsmall : |q/r| ≤ |A|/4 := by
      rw [abs_div,abs_of_pos hr]
      apply (div_le_iff₀ hr).mpr
      have ht : 4*|q|/|A| ≤ r := by linarith
      have ht' := (div_le_iff₀ ha).mp ht
      nlinarith
    have hh := abs_sub_le (q/r-A) (q/r) 0
    have hab : |A| ≤ |q/r-A|+|q/r| := by
      have h := abs_sub (q/r-A) (q/r)
      rw [show q/r-A-q/r = -A by ring,abs_neg] at h
      exact h
    linarith
  subst A
  simpa only [sub_zero] using hA

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_WeakFieldLimitBarrier
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
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma compact_pairing_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → Space → ℝ} {u g : Space → ℝ}
    (hg : Integrable g) (hfi : ∀ i, Integrable (fun x => f i x*g x))
    (hui : Integrable (fun x => u x*g x))
    (hc : TendstoUniformlyOn f u l (tsupport g)) :
    Tendsto (fun i => ∫ x, f i x*g x) l (𝓝 (∫ x, u x*g x)) := by
  let G := ∫ x, |g x|
  have hG : 0 ≤ G := integral_nonneg (fun _ => abs_nonneg _)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(G+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc δ hδ] with i hi
  have hn := norm_integral_le_of_norm_le (hg.abs.const_mul δ)
    (f := fun x => f i x*g x-u x*g x) (ae_of_all _ (fun x => by
      rw [←sub_mul,norm_mul,Real.norm_eq_abs (g x)]
      by_cases hx : g x = 0
      · simp only [hx,abs_zero,mul_zero,le_refl]
      · have hh := (hi x (subset_tsupport g hx)).le
        rw [dist_eq_norm,norm_sub_rev] at hh
        exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)))
  rw [integral_sub (hfi i) hui,integral_const_mul] at hn
  rw [Real.dist_eq]
  have hb : δ*G < ε := by
    have he : δ*(G+1) = ε := div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hn' : |(∫ x, f i x*g x)-(∫ x, u x*g x)| ≤ δ*G := by
    simpa only [Real.norm_eq_abs] using hn
  exact hn'.trans_lt hb

lemma punctured_field_pairing_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → Space → ℝ} {u : Space → ℝ}
    (hf : ∀ i, ContinuousOn (f i) {0}ᶜ) (hu : ContinuousOn u {0}ᶜ)
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u l K)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) :
    Tendsto (fun i => ∫ x, f i x*Δ g x) l (𝓝 (∫ x, u x*Δ g x)) := by
  have hΔ := tfLaplacian_compact hg hcg
  exact compact_pairing_tendsto ((tfLaplacian_continuous hg).integrable_of_hasCompactSupport hΔ)
    (fun i => punctured_laplacian_pairing_integrable (hf i) hg hcg hs)
    (punctured_laplacian_pairing_integrable hu hg hcg hs)
    (hc _ hΔ (closure_minimal (fun x hx => tfLaplacian_support hg hx)
      (isClosed_tsupport g) |>.trans hs))

lemma screened_field_punctured_poisson {ρ : Space → ℝ} {Z M : ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) :
    PuncturedPoisson (fun x => Z/‖x‖-tfPotential ρ x) (fun x => 4*Real.pi*ρ x) := by
  intro g hg hcg hs
  have hg0 : g 0 = 0 := by
    by_contra hn0
    exact hs (subset_tsupport g hn0) rfl
  have hni := CoulombBarrier.locallyIntegrable_mul_test
    (CoulombBarrier.nuclearField_locallyIntegrable Z)
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  have hpi := CoulombBarrier.locallyIntegrable_mul_test
    (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.locallyIntegrable
    (tfLaplacian_continuous hg) (tfLaplacian_compact hg hcg)
  change Integrable (fun x : Space => Z/‖x‖*Δ g x) at hni
  simp_rw [sub_mul]
  rw [integral_sub hni hpi,
    show (∫ x, Z/‖x‖*Δ g x) = -(4*Real.pi*Z)*g 0 from
      CoulombBarrier.nuclearField_weak_laplacian Z hg hcg,
    hg0,mul_zero,zero_sub,bounded_L1_weak_poisson hm hi hM hn hb hg hcg]
  simp only [mul_assoc,integral_const_mul]
  ring

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_WeakSommerfeldBoundsBarrier
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
open scoped Topology

namespace CoulombAnalysis
open CoulombPDE

lemma reaction_continuous (d : ℝ) : Continuous (reaction d) := by
  unfold reaction
  exact continuous_const.mul (((continuous_id.sub continuous_const).max continuous_const).rpow_const
    (fun _ => Or.inr (by norm_num)))

lemma radialCombination_continuousOn (B e s c : ℝ) :
    ContinuousOn (radialCombination B e s c) {0}ᶜ :=
  fun _x hx => (radialCombination_contDiffAt B e s c hx).continuousAt.continuousWithinAt

lemma radialCombinationSource_continuousOn (B e s : ℝ) :
    ContinuousOn (radialCombinationSource B e s) {0}ᶜ := by
  intro x hx
  exact ((radialPower_contDiffAt (-3) hx).continuousAt.mul
    (continuousAt_const.add (continuousAt_const.mul
      (radialPower_contDiffAt (-s) hx).continuousAt))).continuousWithinAt

lemma radialCombination_poisson (B e s c : ℝ) :
    PuncturedPoisson (radialCombination B e s c) (radialCombinationSource B e s) :=
  (PuncturedPoisson.of_classical (fun _x hx => radialCombination_contDiffAt B e s c hx)).congr_source
    (fun _x hx => radialCombination_laplacian B e s c hx)

theorem weak_singular_upper_bound {F : Space → ℝ} {d C R B : ℝ}
    (hd : 0 < d) (hC : 0 ≤ C) (hR : 0 < R) (hB : 0 < B)
    (hq : 12 < d * B ^ (1 / 2 : ℝ))
    (hreg : ContinuousOn F {0}ᶜ)
    (hpde : PuncturedPoisson F (fun x => reaction d (F x)))
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ B * radialPower (-2) x + C * (R ^ 2) ^ (-2 : ℝ) + 1 := by
  obtain ⟨s, hs, hκ⟩ := exists_small_exponent hq
  let c : ℝ := C * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hC (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      F x ≤ radialCombination B e s (c + 1) x := by
    have hvc := radialCombination_continuousOn B e s (c+1)
    have hdiff := hpde.sub (radialCombination_poisson B e s (c+1)) hreg hvc
      ((reaction_continuous d).comp_continuousOn hreg) (radialCombinationSource_continuousOn B e s)
    have hm := weak_punctured_ball_maximum (R := R) (u := F-radialCombination B e s (c+1))
      (hreg.sub hvc) (fun g hg hcg hsg hgn => hdiff.nonneg_on
        (fun x hx => hx.1) (fun x hx => ?_) hg hcg hsg hgn) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · change 0 ≤ reaction d (F x)-radialCombinationSource B e s x
      have hu := upper_barrier_laplacian hd.le hB he.le (by linarith : 1 ≤ c+1) hq.le hκ hx.1
      rw [radialCombination_laplacian] at hu
      have hmon := reaction_monotone hd.le (show radialCombination B e s (c+1) x ≤ F x by
        exact le_of_lt (sub_pos.mp hx.2.2))
      change radialCombinationSource B e s x ≤ reaction d (radialCombination B e s (c+1) x) at hu
      linarith
      exact hx.1
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hu := hupper x hx0 hx.le
      have hrad : C * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      rw [hrad] at hu
      have h1 := radialPower_nonneg (-2 : ℝ) x
      have h2 := radialPower_nonneg (-2 - s) x
      change F x - radialCombination B e s (c + 1) x ≤ 0
      unfold radialCombination
      nlinarith [mul_nonneg hB.le h1, mul_nonneg he.le h2]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (C / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hu := hupper x hx (hxa.trans (min_le_right _ _))
      have heC : C ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change F x - radialCombination B e s (c + 1) x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heC),
        mul_nonneg hB.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [div_mul_cancel₀ _ hp.ne'] at h
  change F x ≤ B * radialPower (-2) x + c + 1 + δ
  linarith

theorem weak_singular_lower_bound {F : Space → ℝ} {d c₀ R B : ℝ}
    (hd : 0 < d) (hc₀ : 0 < c₀) (hR : 0 < R) (hB : 0 < B)
    (hq : d * B ^ (1 / 2 : ℝ) < 12)
    (hreg : ContinuousOn F {0}ᶜ)
    (hpde : PuncturedPoisson F (fun x => reaction d (F x)))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c₀ * radialPower (-2) x ≤ F x) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      B * radialPower (-2) x - B * (R ^ 2) ^ (-2 : ℝ) ≤ F x := by
  let q := d * B ^ (1 / 2 : ℝ)
  have hgap : 0 < (12 - q) * c₀ / B := div_pos (mul_pos (sub_pos.mpr hq) hc₀) hB
  obtain ⟨s, hs, hsκ⟩ := exists_small_exponent (show 12 < 12 + (12 - q) * c₀ / B by linarith)
  have hκ : (14 * s + 4 * s ^ 2) * B ≤ (12 - q) * c₀ := by
    apply (le_div_iff₀ hB).mp
    linarith
  let c : ℝ := B * (R ^ 2) ^ (-2 : ℝ)
  have hc : 0 ≤ c := mul_nonneg hB.le (Real.rpow_nonneg (sq_nonneg R) _)
  have heBound (e : ℝ) (he : 0 < e) : ∀ x, x ≠ 0 → ‖x‖ ≤ R →
      radialCombination B (-e) s (-c) x ≤ F x := by
    have hvc := radialCombination_continuousOn B (-e) s (-c)
    have hdiff := (radialCombination_poisson B (-e) s (-c)).sub hpde hvc hreg
      (radialCombinationSource_continuousOn B (-e) s) ((reaction_continuous d).comp_continuousOn hreg)
    have hm := weak_punctured_ball_maximum (R := R) (u := radialCombination B (-e) s (-c)-F)
      (hvc.sub hreg) (fun g hg hcg hsg hgn => hdiff.nonneg_on
        (fun x hx => hx.1) (fun x hx => ?_) hg hcg hsg hgn) (fun x hx => ?_) ?_
    · intro x hx hr
      exact sub_nonpos.mp (hm x hx hr)
    · change 0 ≤ radialCombinationSource B (-e) s x-reaction d (F x)
      have ht := lower_barrier_laplacian hd.le he.le hs.le hc hc₀ hq.le hκ hx.1
        (hlower x hx.1 hx.2.1) (sub_pos.mp hx.2.2)
      rw [radialCombination_laplacian _ _ _ _ hx.1] at ht
      exact sub_nonneg.mpr ht
    · have hx0 : x ≠ 0 := norm_pos_iff.mp (hx ▸ hR)
      have hl := hlower x hx0 hx.le
      have hrad : B * radialPower (-2) x = c := by simp only [radialPower, hx, c]
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      unfold radialCombination
      rw [hrad]
      nlinarith [mul_nonneg hc₀.le (radialPower_nonneg (-2) x),
        mul_nonneg he.le (radialPower_nonneg (-2 - s) x)]
    · obtain ⟨a, ha, hsmall⟩ := exists_small_radialPower_bound (E := Space) hs (B / e)
      refine ⟨min a R, lt_min ha hR, ?_⟩
      intro x hx hxa
      have ht := hsmall x hx (hxa.trans (min_le_left _ _))
      have hl := hlower x hx (hxa.trans (min_le_right _ _))
      have heB : B ≤ e * radialPower (-s) x := by
        have ht' := (div_le_iff₀ he).mp ht
        nlinarith
      change radialCombination B (-e) s (-c) x - F x ≤ 0
      rw [radialCombination_factor _ _ _ _ hx]
      nlinarith [mul_nonneg (radialPower_nonneg (-2) x) (sub_nonneg.mpr heB),
        mul_nonneg hc₀.le (radialPower_nonneg (-2) x)]
  intro x hx hr
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp := radialPower_pos (-2 - s) hx
  have h := heBound (δ / radialPower (-2 - s) x) (div_pos hδ hp) x hx hr
  unfold radialCombination at h
  rw [neg_mul, div_mul_cancel₀ _ hp.ne'] at h
  change B * radialPower (-2) x - c ≤ F x + δ
  linarith

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_ScaledBarrierCorrectionBarrier
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

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_NonlinearLocalLimitBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_NonlinearLocalLimit_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom
open CoulombPDE (reaction)

lemma compact_uniformly_comp_continuous_real {ι X : Type*} [TopologicalSpace X]
    {l : Filter ι} {K : Set X} {f : ι → X → ℝ} {u : X → ℝ} {G : ℝ → ℝ}
    (hK : IsCompact K) (hu : ContinuousOn u K) (hG : Continuous G)
    (hc : TendstoUniformlyOn f u l K) :
    TendstoUniformlyOn (fun i x => G (f i x)) (fun x => G (u x)) l K := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hu
  let C := max M 0+1
  have hub (x : X) (hx : x ∈ K) : |u x| ≤ max M 0 :=
    (hM x hx).trans (le_max_left _ _)
  have huC (x : X) (hx : x ∈ K) : u x ∈ Icc (-C) C := by
    have hh := abs_le.mp (hub x hx)
    dsimp [C]
    constructor <;> linarith only [hh.1,hh.2]
  have huf := Metric.tendstoUniformlyOn_iff.mp hc 1 zero_lt_one
  have hUC : UniformContinuousOn G (Icc (-C) C) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hG.continuousOn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  filter_upwards [huf,Metric.tendstoUniformlyOn_iff.mp hc δ hδ] with i h1 hi x hx
  have hfC : f i x ∈ Icc (-C) C := by
    have hh := h1 x hx
    have hub' := abs_le.mp (hub x hx)
    rw [Real.dist_eq,abs_lt] at hh
    dsimp [C]
    constructor <;> linarith only [hh.1,hh.2,hub'.1,hub'.2]
  exact hd (u x) (huC x hx) (f i x) hfC (hi x hx)

lemma uniformly_of_uniform_error {ι X : Type*} {l : Filter ι} {K : Set X}
    {f g : ι → X → ℝ} {u : X → ℝ} {e : ι → ℝ}
    (hc : TendstoUniformlyOn f u l K) (he : Tendsto e l (𝓝 0))
    (hb : ∀ᶠ i in l, ∀ x ∈ K, |g i x-f i x| ≤ e i) :
    TendstoUniformlyOn g u l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc (ε/2) (by positivity),
    he.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)),hb] with i hi hei hbi x hx
  have ht := dist_triangle (u x) (f i x) (g i x)
  have hd : dist (f i x) (g i x) ≤ e i := by
    simpa only [Real.dist_eq,abs_sub_comm] using hbi x hx
  linarith only [ht,hi x hx,hd,hei]

lemma local_tf_density_limit {ι : Type*} {l : Filter ι} {K : Set Space}
    {f ρ : ι → Space → ℝ} {u : Space → ℝ} {k : ℝ} {e : ι → ℝ}
    (hK : IsCompact K) (hu : ContinuousOn u K)
    (hc : TendstoUniformlyOn f u l K) (he : Tendsto e l (𝓝 0))
    (hb : ∀ᶠ i in l, ∀ x ∈ K,
      |ρ i x-k*(max (f i x-1) 0)^(3/2:ℝ)| ≤ e i) :
    TendstoUniformlyOn ρ (fun x => k*(max (u x-1) 0)^(3/2:ℝ)) l K := by
  exact uniformly_of_uniform_error
    (compact_uniformly_comp_continuous_real (f := f) (u := u) (G := reaction k)
      hK hu (reaction_continuous k) hc) he hb

theorem punctured_poisson_integrable_density_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {f ρ : ι → Space → ℝ} {u σ : Space → ℝ}
    (hf : ∀ i, ContinuousOn (f i) {0}ᶜ) (hu : ContinuousOn u {0}ᶜ)
    (hρ : ∀ i, Integrable (ρ i)) (hσ : ContinuousOn σ {0}ᶜ)
    (he : ∀ i, PuncturedPoisson (f i) (ρ i))
    (hfc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u l K)
    (hρc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn ρ σ l K) :
    PuncturedPoisson u σ := by
  intro g hg hcg hs
  have ht := punctured_field_pairing_tendsto hf hu hfc hg hcg hs
  obtain ⟨M,hM⟩ := hcg.exists_bound_of_continuous hg.continuous
  have hgi (i : ι) : Integrable (fun x => ρ i x*g x) := by
    apply ((hρ i).norm.const_mul M).mono'
      ((hρ i).aestronglyMeasurable.mul hg.continuous.aestronglyMeasurable)
    exact ae_of_all _ (fun x => by
      change ‖ρ i x*g x‖ ≤ M*‖ρ i x‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have ht' := compact_pairing_tendsto (hg.continuous.integrable_of_hasCompactSupport hcg)
    hgi (punctured_test_integrable hσ hg.continuous hcg hs) (hρc _ hcg hs)
  apply tendsto_nhds_unique ht
  exact ht'.congr' (Eventually.of_forall (fun i => (he i g hg hcg hs).symm))

end Work_NonlinearLocalLimit_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

lemma tail_pairing_bound {ρ g : Space → ℝ} {R M : ℝ}
    (hi : Integrable ρ) (hn : ∀ x, 0 ≤ ρ x) ( _hM : 0 ≤ M)
    (hg : ∀ x, |g x| ≤ M) (hs : Function.support g ⊆ {x | R < ‖x‖}) :
    |∫ x, ρ x*g x| ≤ M*∫ x in {x : Space | R < ‖x‖}, ρ x := by
  let S : Set Space := {x | R < ‖x‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_norm
  have hh := norm_integral_le_of_norm_le ((hi.indicator hS).const_mul M)
    (f := fun x => ρ x*g x) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hn x)]
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx]
        exact (mul_le_mul_of_nonneg_left (hg x) (hn x)).trans_eq (mul_comm _ _)
      · have hgz : g x = 0 := by by_contra hh; exact hx (hs hh)
        simp only [indicator_of_notMem hx,hgz,abs_zero,mul_zero,le_refl]))
  rw [integral_const_mul,integral_indicator hS,Real.norm_eq_abs] at hh
  exact hh

theorem weak_field_tail_harmonic {ι : Type*} {l : Filter ι} [NeBot l]
    {f ρ : ι → Space → ℝ} {u : Space → ℝ} {R : ℝ}
    (hR : 0 < R)
    (hf : ∀ i, ContinuousOn (f i) {0}ᶜ) (hu : ContinuousOn u {0}ᶜ)
    (hi : ∀ i, Integrable (ρ i)) (hn : ∀ i x, 0 ≤ ρ i x)
    (he : ∀ i, PuncturedPoisson (f i) (fun x => 4*Real.pi*ρ i x))
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u l K)
    (ht : Tendsto (fun i => ∫ x in {x : Space | R < ‖x‖}, ρ i x) l (𝓝 0))
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {x | R < ‖x‖}) : (∫ x, u x*Δ g x) = 0 := by
  have hs0 : tsupport g ⊆ {0}ᶜ := fun x hx => norm_pos_iff.mp (hR.trans (hs hx))
  obtain ⟨M,hM⟩ := hcg.exists_bound_of_continuous hg.continuous
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0)
  have hb := fun i => tail_pairing_bound (hi i) (hn i) hM0
    (fun x => by simpa only [Real.norm_eq_abs] using hM x) ((subset_tsupport g).trans hs)
  have ht0 : Tendsto (fun i => ∫ x, ρ i x*g x) l (𝓝 0) :=
    squeeze_zero_norm (fun i => by simpa only [Real.norm_eq_abs] using hb i)
      (by simpa only [mul_zero] using ht.const_mul M)
  have ht' := ht0.const_mul (4*Real.pi)
  have hleft := punctured_field_pairing_tendsto hf hu hc hg hcg hs0
  apply tendsto_nhds_unique hleft
  apply (show Tendsto (fun i => 4*Real.pi*∫ x, ρ i x*g x) l (𝓝 0) by
    simpa only [mul_zero] using ht').congr'
  filter_upwards [] with i
  rw [he i g hg hcg hs0]
  simp only [mul_assoc,integral_const_mul]

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalArzelaAscoliBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalArzelaAscoli_barrier_scope

open Filter Set Topology

theorem local_arzela_ascoli {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SigmaCompactSpace X] [T2Space X]
    (f : ℕ → C(X,ℝ))
    (he : Equicontinuous (fun n x => f n x))
    (hb : ∀ x, ∃ M : ℝ, ∀ n, |f n x| ≤ M) :
    ∃ u : C(X,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → TendstoUniformlyOn (fun n x => f (φ n) x) u atTop K := by
  let : T2Space (UniformOnFun X ℝ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have hce := (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
    (α := X) (β := ℝ)).isClosedEmbedding
  have heq (K : Set X) : EquicontinuousOn
      (fun g : range f => fun x => (g.val : C(X,ℝ)) x) K := by
    have hh := (he.comp (fun g : range f => Classical.choose g.property)).equicontinuousOn K
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext g x
    exact (congrArg (fun F : C(X,ℝ) => F x) (Classical.choose_spec g.property)).symm
  have hc : IsCompact (closure (range f)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := {K : Set X | IsCompact K}) (fun _ hK => hK)
      (F := fun g : C(X,ℝ) => (g : X → ℝ)) hce
      (fun K _ => heq K) (fun _ _ x _ => by
        obtain ⟨M,hM⟩ := hb x
        refine ⟨Icc (-M) M,isCompact_Icc,?_⟩
        rintro g ⟨n,rfl⟩
        exact abs_le.mp (hM n))
  obtain ⟨u,_hu,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨u,φ,hφ,ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht⟩

end Work_LocalArzelaAscoli_barrier_scope

section Work_LocalLipschitzAscoli_barrier_scope

open Filter Set Metric
open scoped Topology

theorem equicontinuous_of_local_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    {f : ι → X → ℝ}
    (hl : ∀ x, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ i y, dist y x < r → |f i x-f i y| ≤ L*dist y x) : Equicontinuous f := by
  intro x
  obtain ⟨r,L,hr,hL,h⟩ := hl x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min r (ε/(L+1)),lt_min hr (div_pos hε (by linarith)),?_⟩
  intro y hy i
  rw [lt_min_iff] at hy
  rw [Real.dist_eq]
  calc
    _ ≤ L*dist y x := h i y hy.1
    _ ≤ (L+1)*dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by
      have hh := (lt_div_iff₀ (show 0 < L+1 by linarith)).mp hy.2
      linarith only [hh]

theorem local_lipschitz_arzela_ascoli
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → ℝ) (hf : ∀ n, ContinuousOn (f n) U)
    (hb : ∀ x ∈ U, ∃ M : ℝ, ∀ n, |f n x| ≤ M)
    (hl : ∀ x ∈ U, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ n y, y ∈ U → dist y x < r → |f n x-f n y| ≤ L*dist y x) :
    ∃ u : X → ℝ, ContinuousOn u U ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn (fun n => f (φ n)) u atTop K := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let F : ℕ → C(U,ℝ) := fun n => ⟨fun x => f n x,(hf n).domRestrict⟩
  have he : Equicontinuous (fun n x => F n x) := by
    apply equicontinuous_of_local_lipschitz
    intro x
    obtain ⟨r,L,hr,hL,h⟩ := hl x x.property
    exact ⟨r,L,hr,hL,fun n y hy => h n y y.property hy⟩
  obtain ⟨v,φ,hφ,hv⟩ := local_arzela_ascoli F he (fun x => hb x x.property)
  let u : X → ℝ := fun x => if hx : x ∈ U then v ⟨x,hx⟩ else 0
  have heq (x : U) : u x = v x := by simp only [u,dite_eq_left x.property]
  refine ⟨u,?_,φ,hφ,?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert v.continuous using 1
    all_goals try with_reducible_and_instances rfl
    exact funext heq
  · intro K hK hKU
    let K' : Set U := Subtype.val ⁻¹' K
    have hK' : IsCompact K' := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      convert hK using 1
      all_goals try with_reducible_and_instances rfl
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,hKU hx⟩,hx,rfl⟩
    have hh := hv K' hK'
    rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
    intro ε hε
    filter_upwards [hh ε hε] with n hn x hx
    have hs := hn ⟨x,hKU hx⟩ hx
    change dist (v ⟨x,hKU hx⟩) (f (φ n) x) < ε at hs
    rw [show u x = v ⟨x,hKU hx⟩ from heq ⟨x,hKU hx⟩]
    exact hs

end Work_LocalLipschitzAscoli_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

lemma nonnegative_density_restrict_integrable {ρ : Space → ℝ} {K : Set Space} {M : ℝ}
    (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z) (hK : MeasurableSet K)
    (hfin : volume K ≠ ⊤) (hb : ∀ z ∈ K, ρ z ≤ M) : Integrable (K.indicator ρ) := by
  apply IntegrableOn.integrable_indicator _ hK
  apply IntegrableOn.of_bound hfin.lt_top hm.aestronglyMeasurable.restrict M
  exact ae_restrict_of_forall_mem hK (fun z hz => by rw [Real.norm_of_nonneg (hn z)]; exact hb z hz)

lemma nonnegative_density_restrict_mass {ρ : Space → ℝ} {K : Set Space} {M : ℝ}
    (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z) (hK : MeasurableSet K)
    (hfin : volume K ≠ ⊤) (hb : ∀ z ∈ K, ρ z ≤ M) :
    (∫ z, K.indicator ρ z) ≤ M*(volume K).toReal := by
  rw [integral_indicator hK]
  have hi := (integrable_indicator_iff hK).mp (nonnegative_density_restrict_integrable hm hn hK hfin hb)
  have hc : IntegrableOn (fun _ : Space => M) K := integrableOn_const hfin
  have hh := integral_mono_ae hi hc (ae_restrict_of_forall_mem hK hb)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh

theorem punctured_poisson_normal_family {f ρ : ℕ → Space → ℝ}
    (hf : ∀ n, ContinuousOn (f n) {0}ᶜ) (hρ : ∀ n, Measurable (ρ n))
    (hn : ∀ n z, 0 ≤ ρ n z)
    (he : ∀ n, PuncturedPoisson (f n) (fun z => 4*Real.pi*ρ n z))
    (hb : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M A : ℝ, 0 ≤ M ∧ 0 ≤ A ∧ (∀ n z, z ∈ K → ρ n z ≤ M) ∧
        ∀ n, (∫ z in K, |f n z|) ≤ A) :
    ∃ u : Space → ℝ, ContinuousOn u {0}ᶜ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn (fun n => f (φ n)) u atTop K := by
  obtain ⟨P,L,hP,hL,hest⟩ := exists_weak_poisson_L1_constants
  have hlocal : ∀ c : Space, c ≠ 0 → ∃ r b l : ℝ, 0 < r ∧ 0 ≤ l ∧
      (∀ n, |f n c| ≤ b) ∧ ∀ n y, dist y c < r → |f n c-f n y| ≤ l*dist y c := by
    intro c hc
    let r := ‖c‖/8
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hr : 0 < r := by dsimp [r]; positivity
    let K := closedBall c (3*r)
    have hK : IsCompact K := isCompact_closedBall c (3*r)
    have hK0 : K ⊆ {0}ᶜ := by
      intro z hz hzero
      have hez : z = 0 := hzero
      rw [hez] at hz
      change dist 0 c ≤ 3*r at hz
      rw [dist_zero_left] at hz
      dsimp [r] at hz
      linarith
    obtain ⟨M,A,hM,hA,hρM,hfA⟩ := hb K hK hK0
    let B := M*(volume K).toReal
    have hB : 0 ≤ B := mul_nonneg hM ENNReal.toReal_nonneg
    let C := A+(2*Real.pi*M+B)*(volume K).toReal
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let b := P/r^3*C+(2*Real.pi*M+B)
    let l := L/r^4*C+4*Real.pi*M+B
    have hl : 0 ≤ l := by dsimp [l]; positivity
    have hi (n : ℕ) : Integrable (K.indicator (ρ n)) :=
      nonnegative_density_restrict_integrable (hρ n) (hn n) hK.measurableSet hK.measure_lt_top.ne (hρM n)
    have hm (n : ℕ) : Measurable (K.indicator (ρ n)) := (hρ n).indicator hK.measurableSet
    have hnon (n : ℕ) (z : Space) : 0 ≤ K.indicator (ρ n) z := indicator_nonneg (fun x _ => hn n x) z
    have hbound (n : ℕ) (z : Space) : K.indicator (ρ n) z ≤ M := by
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz]; exact hρM n z hz
      · rw [indicator_of_notMem hz]; exact hM
    have hmass (n : ℕ) : (∫ z, K.indicator (ρ n) z) ≤ B :=
      nonnegative_density_restrict_mass (hρ n) (hn n) hK.measurableSet hK.measure_lt_top.ne (hρM n)
    have hw (n : ℕ) : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball c (3*r) →
        (∫ z, f n z*Δ g z) = 4*Real.pi*∫ z, K.indicator (ρ n) z*g z := by
      intro g hg hcg hs
      rw [he n g hg hcg (hs.trans (ball_subset_closedBall.trans hK0)),←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        by_cases hz : g z = 0
        · simp only [hz,mul_zero]
        · have hzK : z ∈ K := ball_subset_closedBall (hs (subset_tsupport g hz))
          change 4*Real.pi*ρ n z*g z = 4*Real.pi*(K.indicator (ρ n) z*g z)
          rw [indicator_of_mem hzK]
          ring)
    have hx : c ∈ closedBall c r := mem_closedBall_self hr.le
    have hh (n : ℕ) (y : Space) (hy : y ∈ closedBall c r) :=
      hest (f n) (K.indicator (ρ n)) c r M A B hr hM (hm n) (hi n) (hnon n)
        (hbound n) (hmass n) ((hf n).mono hK0) (hfA n) (hw n) c hx y hy
    refine ⟨r,b,l,hr,hl,fun n => (hh n c hx).1,?_⟩
    intro n y hy
    have hd := (hh n y hy.le).2
    simpa only [dist_eq_norm,norm_sub_rev] using hd
  apply local_lipschitz_arzela_ascoli isOpen_compl_singleton f hf
  · intro c hc
    obtain ⟨r,b,l,_hr,_hl,hb',_hd⟩ := hlocal c hc
    exact ⟨b,hb'⟩
  · intro c hc
    obtain ⟨r,b,l,hr,hl,_hb,hd⟩ := hlocal c hc
    exact ⟨r,l,hr,hl,fun n y _hy hy => hd n y hy⟩

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RotationIntegralBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
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

lemma rotation_spatial_integral {v : Space → ℝ} (hm : Measurable v) (hi : Integrable v) :
    Integrable (fun x => sphereMean v x) ∧ (∫ x, sphereMean v x) = ∫ x, v x := by
  have he (g : SpatialRotation) (w : Space → ℝ) :
      (∫ x, w (rotate g x)) = ∫ x, w x :=
    (rotate g).measurePreserving.integral_comp (rotate g).toHomeomorph.measurableEmbedding w
  have hip : Integrable (fun q : SpatialRotation × Space => v (rotate q.1 q.2))
      (rotationMeasure.prod volume) := by
    apply (integrable_prod_iff (hm.comp rotate_continuous.measurable).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun g => (rotate g).measurePreserving.integrable_comp_of_integrable hi),?_⟩
    change Integrable (fun g : SpatialRotation => ∫ x, (fun z => ‖v z‖) (rotate g x)) rotationMeasure
    have hh : (fun g : SpatialRotation => ∫ x, (fun z => ‖v z‖) (rotate g x)) =
        fun _ => ∫ x, ‖v x‖ := funext (fun g => he g (fun z => ‖v z‖))
    rw [hh]
    exact integrable_const _
  refine ⟨hip.swap.integral_prod_left,?_⟩
  change (∫ x, ∫ g : SpatialRotation, v (rotate g x) ∂rotationMeasure) = _
  rw [←integral_integral_swap (f := fun g x => v (rotate g x)) hip]
  simp only [he,integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma sphereMean_indicator {K : Set Space} {u : Space → ℝ}
    (hrot : ∀ g : SpatialRotation, ∀ x, rotate g x ∈ K ↔ x ∈ K) (x : Space) :
    sphereMean (K.indicator u) x = K.indicator (sphereMean u) x := by
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx]
    apply integral_congr_ae
    exact ae_of_all _ (fun g => indicator_of_mem ((hrot g x).mpr hx) _)
  · rw [indicator_of_notMem hx]
    change (∫ g : SpatialRotation, K.indicator u (rotate g x) ∂rotationMeasure) = 0
    have he : (fun g : SpatialRotation => K.indicator u (rotate g x)) = 0 := by
      funext g
      exact indicator_of_notMem (fun hg => hx ((hrot g x).mp hg)) _
    rw [he]
    exact integral_zero SpatialRotation ℝ

theorem rotation_annular_L1 {K : Set Space} (hK : MeasurableSet K)
    (hfin : volume K ≠ ⊤)
    (hrot : ∀ g : SpatialRotation, ∀ x, rotate g x ∈ K ↔ x ∈ K)
    {u : Space → ℝ} (hm : Measurable u) (hi : IntegrableOn u K)
    {M L : ℝ} (hM : 0 ≤ M) (hcap : ∀ x ∈ K, u x ≤ M)
    (hmean : ∀ x ∈ K, -L ≤ sphereMean u x) :
    (∫ x in K, |u x|) ≤ (2*M+L)*(volume K).toReal := by
  have hv := hi.integrable_indicator hK
  have hrotInt := rotation_spatial_integral (hm.indicator hK) hv
  have he : sphereMean (K.indicator u) = K.indicator (sphereMean u) :=
    funext (sphereMean_indicator hrot)
  rw [he] at hrotInt
  have hsmi : IntegrableOn (sphereMean u) K :=
    (integrable_indicator_iff hK).mp hrotInt.1
  have htotal : (∫ x in K, sphereMean u x) = ∫ x in K, u x := by
    simpa only [integral_indicator hK] using hrotInt.2
  have hconst : IntegrableOn (fun _ : Space => -L) K := integrableOn_const hfin
  have hlow : -L * (volume K).toReal ≤ ∫ x in K, u x := by
    rw [←htotal]
    have hh := integral_mono_ae hconst hsmi (ae_restrict_of_forall_mem hK hmean)
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh
  have hupper : (∫ x in K, |u x|) ≤ 2*M*(volume K).toReal-∫ x in K, u x := by
    have hc : IntegrableOn (fun _ : Space => 2*M) K := integrableOn_const hfin
    have hh := integral_mono_ae hi.abs (hc.sub hi) (ae_restrict_of_forall_mem hK (fun x hx => by
      change |u x| ≤ 2*M-u x
      rw [abs_le]
      constructor <;> linarith [hcap x hx, hM]))
    change (∫ x in K, |u x|) ≤ ∫ x in K, 2*M-u x at hh
    rw [integral_sub hc hi] at hh
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh
  linarith only [hlow,hupper]

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom

lemma compact_away_zero_annulus {K : Set Space} (hK : IsCompact K) (h0 : K ⊆ {0}ᶜ) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ K ⊆ {x : Space | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  rcases K.eq_empty_or_nonempty with he | hn
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    rw [he]
    exact empty_subset _
  · obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hn continuous_norm.continuousOn
    obtain ⟨b,hb,hmax⟩ := hK.isBounded.exists_pos_norm_le
    refine ⟨‖z‖,b,norm_pos_iff.mpr (h0 hz),hb,?_⟩
    exact fun x hx => ⟨hmin hx,hmax x hx⟩

lemma compact_closed_annulus (a b : ℝ) :
    IsCompact {x : Space | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  apply (isCompact_closedBall (0:Space) b).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
  exact fun x hx => by simpa only [mem_closedBall,dist_zero_right,mem_ofPred_eq] using hx.2

lemma screened_field_continuousOn {ρ : Space → ℝ} {Z M : ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) :
    ContinuousOn (fun x => Z/‖x‖-tfPotential ρ x) {0}ᶜ := by
  apply (continuousOn_const.div continuous_norm.continuousOn (fun x hx => norm_ne_zero_iff.mpr hx)).sub
  exact (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.continuousOn

lemma screened_field_measurable {ρ : Space → ℝ} {Z M : ℝ}
    (hm : Measurable ρ) (hi : Integrable ρ) (hM : 0 ≤ M)
    (hn : ∀ x, 0 ≤ ρ x) (hb : ∀ x, ρ x ≤ M) :
    Measurable (fun x => Z/‖x‖-tfPotential ρ x) :=
  (measurable_const.div measurable_norm).sub
    (bounded_L1_potential_lipschitz hm hi hM hn hb).continuous.measurable

theorem screened_field_local_L1 {ρ : ℕ → Space → ℝ} {Z : ℕ → ℝ} {Q : ℝ}
    (hm : ∀ n, Measurable (ρ n)) (hi : ∀ n, Integrable (ρ n))
    (hn : ∀ n x, 0 ≤ ρ n x) (hglobal : ∀ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ρ n x ≤ M)
    (hQ : 0 ≤ Q) (hq : ∀ n, |Z n-∫ x, ρ n x| ≤ Q)
    (hcap : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ K → Z n/‖x‖-tfPotential (ρ n) x ≤ M)
    {K : Set Space} (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n, (∫ x in K, |Z n/‖x‖-tfPotential (ρ n) x|) ≤ A := by
  obtain ⟨a,b,ha,_hb,hKS⟩ := compact_away_zero_annulus hK hK0
  let S : Set Space := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  have hS := compact_closed_annulus a b
  have hS0 : S ⊆ {0}ᶜ := fun _ hx => norm_pos_iff.mp (ha.trans_le hx.1)
  obtain ⟨M,hM,hc⟩ := hcap S hS hS0
  let A := (2*M+Q/a)*(volume S).toReal
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro n
  obtain ⟨B,hB,hρB⟩ := hglobal n
  have hcont := screened_field_continuousOn (Z := Z n) (hm n) (hi n) hB (hn n) hρB
  have hii : IntegrableOn (fun z => Z n/‖z‖-tfPotential (ρ n) z) S :=
    (hcont.mono hS0).integrableOn_compact hS
  have hmean : ∀ x ∈ S, -(Q/a) ≤ sphereMean (fun z => Z n/‖z‖-tfPotential (ρ n) z) x := by
    intro x hx
    have hnx : 0 < ‖x‖ := ha.trans_le hx.1
    have hbr := (sphereMean_field_bracket (hm n) (hi n) hB (hn n) hρB (Z n) (hS0 hx)).1
    have hres := (abs_le.mp (hq n)).1
    have hl := div_le_div_of_nonneg_left hQ ha hx.1
    have hr := div_le_div_of_nonneg_right hres hnx.le
    rw [neg_div] at hr
    linarith
  have hrot : ∀ g : SpatialRotation, ∀ x, rotate g x ∈ S ↔ x ∈ S := by
    intro g x
    simp only [S,mem_ofPred_eq,(rotate g).norm_map]
  have hbound := rotation_annular_L1 hS.measurableSet hS.measure_lt_top.ne hrot
    (screened_field_measurable (Z := Z n) (hm n) (hi n) hB (hn n) hρB) hii hM (hc n) hmean
  exact (setIntegral_mono_set hii.abs (ae_of_all _ (fun _ => abs_nonneg _))
    (ae_of_all _ (fun _ hx => hKS hx))).trans hbound

theorem screened_field_normal_family {ρ : ℕ → Space → ℝ} {Z : ℕ → ℝ} {Q : ℝ}
    (hm : ∀ n, Measurable (ρ n)) (hi : ∀ n, Integrable (ρ n))
    (hn : ∀ n x, 0 ≤ ρ n x) (hglobal : ∀ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ρ n x ≤ M)
    (hQ : 0 ≤ Q) (hq : ∀ n, |Z n-∫ x, ρ n x| ≤ Q)
    (hcap : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ K → Z n/‖x‖-tfPotential (ρ n) x ≤ M)
    (hρcap : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n x, x ∈ K → ρ n x ≤ M) :
    ∃ u : Space → ℝ, ContinuousOn u {0}ᶜ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ {0}ᶜ →
        TendstoUniformlyOn (fun n x => Z (φ n)/‖x‖-tfPotential (ρ (φ n)) x) u atTop K := by
  apply punctured_poisson_normal_family (f := fun n x => Z n/‖x‖-tfPotential (ρ n) x) (ρ := ρ) _ hm hn _
  · intro K hK hK0
    obtain ⟨M,hM,hMbound⟩ := hρcap K hK hK0
    obtain ⟨A,hA,hAbound⟩ := screened_field_local_L1 hm hi hn hglobal hQ hq hcap hK hK0
    exact ⟨M,A,hM,hA,hMbound,hAbound⟩
  · intro n
    obtain ⟨M,hM,hMb⟩ := hglobal n
    exact screened_field_continuousOn (hm n) (hi n) hM (hn n) hMb
  · intro n
    obtain ⟨M,hM,hMb⟩ := hglobal n
    exact screened_field_punctured_poisson (hm n) (hi n) hM (hn n) hMb

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ScreenedLimitDynamicsBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
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

namespace CoulombAnalysis
open CoulombAtom

lemma exterior_tail_tendsto_of_le {ι : Type*} {l : Filter ι}
    {ρ : ι → Space → ℝ} {R S : ℝ}
    (hi : ∀ i, Integrable (ρ i)) (hn : ∀ i x, 0 ≤ ρ i x) (hRS : R ≤ S)
    (ht : Tendsto (fun i => ∫ x in {x : Space | R < ‖x‖}, ρ i x) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in {x : Space | S < ‖x‖}, ρ i x) l (𝓝 0) := by
  apply squeeze_zero (fun i => integral_nonneg (hn i)) _ ht
  intro i
  exact setIntegral_mono_set (hi i).integrableOn (ae_of_all _ (hn i))
    (ae_of_all _ (fun x hx => hRS.trans_lt hx))

theorem screened_limit_dynamics {ι : Type*} {l : Filter ι} [NeBot l]
    {ρ : ι → Space → ℝ} {Z : ι → ℝ} {u : Space → ℝ} {q R k C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hm : ∀ i, Measurable (ρ i)) (hi : ∀ i, Integrable (ρ i))
    (hn : ∀ i x, 0 ≤ ρ i x) (hb : ∀ i, ∃ M ≥ 0, ∀ x, ρ i x ≤ M)
    (hu : ContinuousOn u {0}ᶜ)
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      TendstoUniformlyOn (fun i x => Z i/‖x‖-tfPotential (ρ i) x) u l K)
    (hTF : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ e : ι → ℝ, Tendsto e l (𝓝 0) ∧ ∀ᶠ i in l, ∀ x ∈ K,
        |ρ i x-k*(max (Z i/‖x‖-tfPotential (ρ i) x-1) 0)^(3/2:ℝ)| ≤ e i)
    (hq : Tendsto (fun i => Z i-∫ x, ρ i x) l (𝓝 q))
    (ht : Tendsto (fun i => ∫ x in {x : Space | R < ‖x‖}, ρ i x) l (𝓝 0))
    (hcap : ∀ x, x ≠ 0 → u x ≤ 1+C/‖x‖^4) :
    PuncturedPoisson u (fun x => CoulombPDE.reaction (4*Real.pi*k) (u x)) ∧
    (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0) ∧
    (∀ p : Space, R < ‖p‖ → sphereMean u p = q/‖p‖) ∧
    (∀ ε > 0, ∃ S > 0, ∀ x : Space, S ≤ ‖x‖ → |u x| < ε) := by
  let f : ι → Space → ℝ := fun i x => Z i/‖x‖-tfPotential (ρ i) x
  have hf : ∀ i, ContinuousOn (f i) {0}ᶜ := by
    intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact screened_field_continuousOn (hm i) (hi i) hM (hn i) hMb
  have he : ∀ i, PuncturedPoisson (f i) (fun x => 4*Real.pi*ρ i x) := by
    intro i
    obtain ⟨M,hM,hMb⟩ := hb i
    exact screened_field_punctured_poisson (hm i) (hi i) hM (hn i) hMb
  have hρc (K : Set Space) (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
      TendstoUniformlyOn ρ (fun x => k*(max (u x-1) 0)^(3/2:ℝ)) l K := by
    obtain ⟨e,he0,hebound⟩ := hTF K hK hK0
    exact local_tf_density_limit hK (hu.mono hK0) (hc K hK hK0) he0 hebound
  have hρc' (K : Set Space) (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
      TendstoUniformlyOn (fun i x => 4*Real.pi*ρ i x)
        (fun x => CoulombPDE.reaction (4*Real.pi*k) (u x)) l K := by
    have hh := compact_uniformly_comp_continuous_real (f := ρ)
      (u := fun x => k*(max (u x-1) 0)^(3/2:ℝ)) (G := fun t : ℝ => 4*Real.pi*t)
      hK ((reaction_continuous k).continuousOn.comp (hu.mono hK0)
        (fun _ _ => mem_univ _)) (continuous_const.mul continuous_id) (hρc K hK hK0)
    simpa only [CoulombPDE.reaction,mul_assoc] using hh
  have hpart := punctured_poisson_integrable_density_limit hf hu
    (fun i => (hi i).const_mul (4*Real.pi))
    ((reaction_continuous (4*Real.pi*k)).continuousOn.comp hu
      (fun _ _ => mem_univ _)) he hc hρc'
  have hhar : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0 := by
    intro g hg hcg hs
    exact weak_field_tail_harmonic hR hf hu hi hn he hc ht hg hcg hs
  have hmean (p : Space) (hp : R < ‖p‖) : sphereMean u p = q/‖p‖ := by
    have hp0 : p ≠ 0 := norm_pos_iff.mp (hR.trans hp)
    apply sphericalMean_limit_charge hp0 hm hi hn hb
      (fun x hx => hu.continuousAt (isOpen_compl_singleton.mem_nhds hx))
      (hc _ (isCompact_sphere _ _) (by
        intro x hx hx0
        rw [mem_sphere_zero_iff_norm,hx0,norm_zero] at hx
        exact (norm_ne_zero_iff.mpr hp0) hx.symm)) hq
    exact exterior_tail_tendsto_of_le hi hn hp.le ht
  refine ⟨hpart,hhar,hmean,?_⟩
  apply weak_exterior_mean_uniform_decay (K := 1+C/R^4) hR hu hhar _ hmean
  intro x hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hR.trans_le hx)
  apply (hcap x hx0).trans
  exact add_le_add_right (div_le_div_of_nonneg_left hC (pow_pos hR 4)
    (pow_le_pow_left₀ hR.le hx 4)) 1

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfIncreasingData
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAnalysis
open CoulombAtom

lemma tfIncreasingField_monotone {r : ℝ} (hr : 0 < r) : Monotone (fun n => tfIncreasingField n r) := by
  intro n m hnm
  rcases hnm.eq_or_lt with h | h
  · subst h; rfl
  · have hh := ((tfIncreasingData n).finiteProfile (by positivity)).compare
      ((tfIncreasingData m).finiteProfile (by positivity)) tfReactionCoefficient_pos.le
      (show (n:ℝ)+1 < m+1 by exact_mod_cast Nat.add_lt_add_right h 1)
      (r • radialAxis) (TFUnitData.ray_ne_zero hr)
    rwa [← (tfIncreasingData n).radialField_ray (by positivity) hr,
      ← (tfIncreasingData m).radialField_ray (by positivity) hr] at hh

lemma tfIncreasingField_bounded {r : ℝ} (hr : 0 < r) :
    BddAbove (range (fun n => tfIncreasingField n r)) := by
  refine ⟨1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (tfIncreasingData n).radialField_upper (by positivity) hr

lemma tfIncreasingField_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    tfIncreasingField n r ≤ tfInfiniteRadial r := le_ciSup (tfIncreasingField_bounded hr) n

lemma tfInfiniteRadial_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ tfInfiniteRadial r :=
  ((tfIncreasingData 0).radialField_nonneg (by positivity) hr).trans (tfIncreasingField_le hr 0)

lemma tfIncreasingField_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => tfIncreasingField n r) atTop (𝓝 (tfInfiniteRadial r)) := by
  exact tendsto_atTop_ciSup (tfIncreasingField_monotone hr) (tfIncreasingField_bounded hr)

lemma tfInfiniteRadial_upper {r : ℝ} (hr : 0 < r) :
    tfInfiniteRadial r ≤ 1 + CoulombPDE.sommerfeldCoefficient tfReactionCoefficient / r^4 := by
  apply ciSup_le
  exact fun n => (tfIncreasingData n).radialField_upper (by positivity) hr

lemma tfInfiniteRadial_far_bound {a r : ℝ} (ha : 0 < a) (hr : a ≤ r) :
    tfInfiniteRadial r ≤ TFUnitData.chargeCap a / r := by
  apply ciSup_le
  exact fun n => (tfIncreasingData n).radialField_far_bound (by positivity) ha hr

lemma tfInfiniteRadial_lipschitz {a : ℝ} (ha : 0 < a) :
    LipschitzOnWith ⟨TFUnitData.slopeCap a, (TFUnitData.slopeCap_pos ha).le⟩ tfInfiniteRadial (Ici a) := by
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  apply le_of_tendsto ((tfIncreasingField_tendsto (ha.trans_le hx)).sub
    (tfIncreasingField_tendsto (ha.trans_le hy))).norm
  exact Eventually.of_forall fun n => ((tfIncreasingData n).lipschitz (by positivity) ha).norm_sub_le hx hy

lemma tfInfiniteRadial_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfInfiniteRadial r := by
  apply (tfInfiniteRadial_lipschitz (show 0 < r/2 by positivity)).continuousOn.continuousAt
  exact Ici_mem_nhds (by linarith)

lemma positive_uIcc {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ uIcc a b) : 0 < t :=
  (lt_min ha hb).trans_le ht.1

lemma positive_uIoc {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : t ∈ uIoc a b) : 0 < t :=
  (lt_min ha hb).trans ht.1

lemma tf_reaction_continuous : Continuous (CoulombPDE.reaction tfReactionCoefficient) := by
  unfold CoulombPDE.reaction
  exact continuous_const.mul (((continuous_id.sub continuous_const).max continuous_const).rpow_const
    (fun _ => Or.inr (by norm_num)))

lemma tf_reaction_nonneg (v : ℝ) : 0 ≤ CoulombPDE.reaction tfReactionCoefficient v := by
  unfold CoulombPDE.reaction
  exact mul_nonneg tfReactionCoefficient_pos.le (Real.rpow_nonneg (le_max_right _ _) _)

lemma tfFluxSource_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfFluxSource r :=
  (continuousAt_id.pow 2).mul (tf_reaction_continuous.continuousAt.comp (tfInfiniteRadial_continuous hr))

lemma tfFiniteSource_continuous (n : ℕ) {r : ℝ} (hr : 0 < r) : ContinuousAt (tfFiniteSource n) r :=
  (continuousAt_id.pow 2).mul (tf_reaction_continuous.continuousAt.comp
    ((tfIncreasingData n).radialField_hasDerivAt hr).continuousAt)

lemma tfFluxSource_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable tfFluxSource volume a b :=
  (show ContinuousOn tfFluxSource (uIcc a b) from
    fun _ ht => (tfFluxSource_continuous (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSource_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (tfFiniteSource n) volume a b :=
  (show ContinuousOn (tfFiniteSource n) (uIcc a b) from
    fun _ ht => (tfFiniteSource_continuous n (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSource_integral_tendsto {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ t in a..b, tfFiniteSource n t) atTop (𝓝 (∫ t in a..b, tfFluxSource t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence tfFluxSource
  · exact Eventually.of_forall fun n =>
      (show ContinuousOn (tfFiniteSource n) (uIoc a b) from fun _ ht =>
        (tfFiniteSource_continuous n (positive_uIoc ha hb ht)).continuousWithinAt).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun n => Eventually.of_forall fun t ht => ?_
    rw [tfFiniteSource, Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (tf_reaction_nonneg _))]
    exact mul_le_mul_of_nonneg_left (CoulombPDE.reaction_monotone tfReactionCoefficient_pos.le
      (tfIncreasingField_le (positive_uIoc ha hb ht) n)) (sq_nonneg t)
  · exact tfFluxSource_intervalIntegrable ha hb
  · refine Eventually.of_forall fun t ht => ?_
    exact tendsto_const_nhds.mul (tf_reaction_continuous.continuousAt.tendsto.comp
      (tfIncreasingField_tendsto (positive_uIoc ha hb ht)))

lemma tfIncreasingCharge_integral (n : ℕ) {r : ℝ} (hr : 0 < r) :
    tfIncreasingCharge n r = tfIncreasingCharge n 1 - ∫ t in (1:ℝ)..r, tfFiniteSource n t := by
  have hd (t : ℝ) (ht : t ∈ uIcc (1:ℝ) r) :
      HasDerivAt (fun x => -tfIncreasingCharge n x) (tfFiniteSource n t) t := by
    convert ((tfIncreasingData n).charge_equation (positive_uIcc zero_lt_one hr ht) (by positivity)).neg using 1 <;> (try rfl)
    unfold tfFiniteSource tfIncreasingField
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (tfFiniteSource_intervalIntegrable n zero_lt_one hr)
  change (∫ t in (1:ℝ)..r, tfFiniteSource n t) = -(tfIncreasingCharge n r) - -(tfIncreasingCharge n 1) at hh
  linarith

lemma tfIncreasingCharge_subseq_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => tfIncreasingCharge (tfChargeAnchor.index n) r) atTop (𝓝 (tfInfiniteCharge r)) := by
  have hh := tfChargeAnchor.limit.sub
    ((tfFiniteSource_integral_tendsto zero_lt_one hr).comp tfChargeAnchor.strict.tendsto_atTop)
  exact hh.congr (fun n => (tfIncreasingCharge_integral _ hr).symm)

lemma tfInfiniteCharge_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt tfInfiniteCharge (-tfFluxSource r) r := by
  exact (intervalIntegral.integral_hasDerivAt_right (tfFluxSource_intervalIntegrable zero_lt_one hr)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun _ ht => tfFluxSource_continuous ht) r hr)
    (tfFluxSource_continuous hr)).const_sub _

lemma tfInfiniteSlope_continuous {r : ℝ} (hr : 0 < r) : ContinuousAt tfInfiniteSlope r :=
  (tfInfiniteCharge_hasDerivAt hr).continuousAt.neg.div (continuousAt_id.pow 2) (pow_ne_zero _ hr.ne')

lemma tfFiniteSlope_continuous (n : ℕ) {r : ℝ} (hr : 0 < r) : ContinuousAt (tfFiniteSlope n) r :=
  ((tfIncreasingData n).charge_hasDerivAt hr).continuousAt.neg.div (continuousAt_id.pow 2) (pow_ne_zero _ hr.ne')

lemma tfInfiniteSlope_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable tfInfiniteSlope volume a b :=
  (show ContinuousOn tfInfiniteSlope (uIcc a b) from
    fun _ ht => (tfInfiniteSlope_continuous (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSlope_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (tfFiniteSlope n) volume a b :=
  (show ContinuousOn (tfFiniteSlope n) (uIcc a b) from
    fun _ ht => (tfFiniteSlope_continuous n (positive_uIcc ha hb ht)).continuousWithinAt).intervalIntegrable

lemma tfFiniteSlope_integral_subseq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n => ∫ t in a..b, tfFiniteSlope (tfChargeAnchor.index n) t) atTop
      (𝓝 (∫ t in a..b, tfInfiniteSlope t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => TFUnitData.slopeCap (min a b))
  · exact Eventually.of_forall fun n =>
      (show ContinuousOn (tfFiniteSlope (tfChargeAnchor.index n)) (uIoc a b) from fun _ ht =>
        (tfFiniteSlope_continuous _ (positive_uIoc ha hb ht)).continuousWithinAt).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun n => Eventually.of_forall fun t ht => ?_
    have hh := (tfIncreasingData (tfChargeAnchor.index n)).deriv_bound (by positivity) (lt_min ha hb) ht.1.le
    rwa [((tfIncreasingData (tfChargeAnchor.index n)).radialField_hasDerivAt (positive_uIoc ha hb ht)).deriv] at hh
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    exact (tfIncreasingCharge_subseq_tendsto (positive_uIoc ha hb ht)).neg.div tendsto_const_nhds
      (pow_ne_zero _ (positive_uIoc ha hb ht).ne')

lemma tfInfiniteRadial_integral {r : ℝ} (hr : 0 < r) :
    tfInfiniteRadial r = tfInfiniteRadial 1 + ∫ t in (1:ℝ)..r, tfInfiniteSlope t := by
  have hi (n : ℕ) : (∫ t in (1:ℝ)..r, tfFiniteSlope n t) = tfIncreasingField n r - tfIncreasingField n 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => (tfIncreasingData n).radialField_hasDerivAt (positive_uIcc zero_lt_one hr ht))
      (tfFiniteSlope_intervalIntegrable n zero_lt_one hr)
  have hl := ((tfIncreasingField_tendsto hr).sub (tfIncreasingField_tendsto zero_lt_one)).comp
    tfChargeAnchor.strict.tendsto_atTop
  have he := tendsto_nhds_unique (tfFiniteSlope_integral_subseq zero_lt_one hr)
    (hl.congr (fun n => (hi _).symm))
  linarith

lemma tfInfiniteRadial_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt tfInfiniteRadial (tfInfiniteSlope r) r := by
  have hh := (intervalIntegral.integral_hasDerivAt_right (tfInfiniteSlope_intervalIntegrable zero_lt_one hr)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun _ ht => tfInfiniteSlope_continuous ht) r hr)
    (tfInfiniteSlope_continuous hr)).const_add (tfInfiniteRadial 1)
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  exact tfInfiniteRadial_integral ht

lemma tfInfiniteCharge_contDiffOn : ContDiffOn ℝ 1 tfInfiniteCharge (Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (tfInfiniteCharge_hasDerivAt hr).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [contDiffOn_zero]
  apply ContinuousOn.congr (f := fun r => -tfFluxSource r)
    (fun r hr => (tfFluxSource_continuous hr).neg.continuousWithinAt)
  exact fun r hr => (tfInfiniteCharge_hasDerivAt hr).deriv

lemma tfInfiniteRadial_contDiffOn : ContDiffOn ℝ 2 tfInfiniteRadial (Ioi 0) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun r hr => (tfInfiniteRadial_hasDerivAt hr).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  apply ContDiffOn.congr (f := tfInfiniteSlope)
    (tfInfiniteCharge_contDiffOn.neg.div (contDiffOn_id.pow 2) (fun r hr => pow_ne_zero _ hr.ne'))
  exact fun r hr => (tfInfiniteRadial_hasDerivAt hr).deriv

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfInfiniteField
attribute [-instance] _root_.OAI.CoulombAtom.cosetWedgeFintype
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
namespace CoulombAnalysis

lemma tfInfinite_sqrt_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => tfInfiniteRadial (Real.sqrt t))
      (-tfInfiniteCharge (Real.sqrt s) / (2 * (Real.sqrt s)^3)) s := by
  have hh := (tfInfiniteRadial_hasDerivAt (Real.sqrt_pos.mpr hs)).comp s (Real.hasDerivAt_sqrt hs.ne')
  convert hh using 1 <;> (try rfl)
  unfold tfInfiniteSlope
  field_simp [Real.sqrt_ne_zero'.mpr hs]

lemma tfInfinite_sqrt_second {s : ℝ} (hs : 0 < s) :
    deriv (deriv (fun t => tfInfiniteRadial (Real.sqrt t))) s =
      CoulombPDE.reaction tfReactionCoefficient (tfInfiniteRadial (Real.sqrt s)) / (4 * (Real.sqrt s)^2) +
        3 * tfInfiniteCharge (Real.sqrt s) / (4 * (Real.sqrt s)^5) := by
  have he : deriv (fun t => tfInfiniteRadial (Real.sqrt t)) =ᶠ[𝓝 s]
      fun t => -tfInfiniteCharge (Real.sqrt t) / (2 * (Real.sqrt t)^3) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (tfInfinite_sqrt_hasDerivAt ht).deriv
  rw [he.deriv_eq]
  have hm := (tfInfiniteCharge_hasDerivAt (Real.sqrt_pos.mpr hs)).comp s (Real.hasDerivAt_sqrt hs.ne')
  have ht := ((Real.hasDerivAt_sqrt hs.ne').pow 3).const_mul 2
  have hh := hm.neg.div ht (by
    change 2 * Real.sqrt s ^ 3 ≠ 0
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (Real.sqrt_ne_zero'.mpr hs)))
  change HasDerivAt (fun t => -tfInfiniteCharge (Real.sqrt t) / (2 * (Real.sqrt t)^3)) _ s at hh
  rw [hh.deriv]
  simp only [Pi.pow_apply, Pi.neg_apply, Function.comp_apply, tfFluxSource]
  field_simp [Real.sqrt_ne_zero'.mpr hs]
  ring

lemma tfInfiniteField_classical {x : TFSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 tfInfiniteField x ∧
      Δ tfInfiniteField x = CoulombPDE.reaction tfReactionCoefficient (tfInfiniteField x) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let g : ℝ → ℝ := fun s => tfInfiniteRadial (Real.sqrt s)
  have hg : ContDiffAt ℝ 2 g (‖x‖ ^ 2) := by
    have hrp := tfInfiniteRadial_contDiffOn.contDiffAt (Ioi_mem_nhds hn)
    have hrp' : ContDiffAt ℝ 2 tfInfiniteRadial (Real.sqrt (‖x‖ ^ 2)) := by
      rwa [Real.sqrt_sq (norm_nonneg x)]
    exact hrp'.comp (‖x‖ ^ 2) (Real.contDiffAt_sqrt (pow_ne_zero _ hn.ne'))
  have he : tfInfiniteField = (fun y : TFSpace => g (‖y‖ ^ 2)) := by
    funext y
    simp [tfInfiniteField, g, Real.sqrt_sq (norm_nonneg y)]
  have hfull : ContDiffAt ℝ 2 (fun y : TFSpace => g (‖y‖ ^ 2)) x :=
    ContDiffAt.comp (g := g) (f := fun y : TFSpace => ‖y‖ ^ 2) x hg (contDiff_norm_sq ℝ).contDiffAt
  refine ⟨he ▸ hfull, ?_⟩
  rw [he, CoulombPDE.laplacian_norm_sq_comp hg]
  dsimp only [g]
  rw [(tfInfinite_sqrt_hasDerivAt (sq_pos_of_pos hn)).deriv,
    tfInfinite_sqrt_second (sq_pos_of_pos hn), Real.sqrt_sq (norm_nonneg x)]
  have hdim : Module.finrank ℝ TFSpace = 3 := by simp [TFSpace]
  rw [hdim]
  norm_num only [Nat.cast_ofNat]
  field_simp [hn.ne']
  ring

lemma tfInfiniteField_decay : ∀ ε > 0, ∃ R > 0, ∀ x, R ≤ ‖x‖ → |tfInfiniteField x| < ε := by
  intro ε hε
  refine ⟨max 1 (2 * TFUnitData.chargeCap 1 / ε), lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x hx
  have h1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hn : 0 < ‖x‖ := zero_lt_one.trans_le h1
  change |tfInfiniteRadial ‖x‖| < ε
  rw [abs_of_nonneg (tfInfiniteRadial_nonneg hn)]
  apply (tfInfiniteRadial_far_bound zero_lt_one h1).trans_lt
  apply (div_lt_iff₀ hn).mpr
  have hh := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hx)
  have hc := TFUnitData.chargeCap_pos zero_lt_one
  nlinarith

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_TfInfiniteFieldDominatesDilation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

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
open Filter Set Metric Topology InnerProductSpace Laplacian

lemma tfInfiniteField_dominates_dilation {a : ℝ} (ha : 1 ≤ a) (x : TFSpace) (hx : x ≠ 0) :
    CoulombPDE.shiftedDilation a (tfIncreasingData 0).field x ≤ tfInfiniteField x := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  obtain ⟨n, hn⟩ := exists_nat_gt (a^3)
  have hw : a^3 * ((0:ℝ)+1) < (n:ℝ)+1 := by nlinarith
  have hF := (tfIncreasingData 0).finiteProfile (by positivity)
  have hh := CoulombPDE.compare_subsolution_finite tfReactionCoefficient_pos.le (by positivity) hw
    ((tfIncreasingData n).finiteProfile (by positivity))
    (hF.shifted_dilation_regular ha0)
    (fun y hy => (hF.shifted_dilation_equation ha0 y hy).ge)
    (by simpa only [Nat.cast_zero] using hF.shifted_dilation_near ha0) (hF.shifted_dilation_far ha) x hx
  apply hh.trans
  rw [← (tfIncreasingData n).radialField_eq (by positivity) hx]
  exact tfIncreasingField_le (norm_pos_iff.mpr hx) n

lemma tf_first_field_large : ∃ (r₀ : ℝ), 0 < r₀ ∧ 2 ≤ (tfIncreasingData 0).field (r₀ • radialAxis) := by
  obtain ⟨C, hC, a, ha, hn⟩ := ((tfIncreasingData 0).finiteProfile (by positivity)).nucleus
  let r₀ := min a (1/(C+2))
  have hr : 0 < r₀ := lt_min ha (div_pos zero_lt_one (by linarith))
  refine ⟨r₀, hr, ?_⟩
  have hh := (abs_le.mp (hn (r₀ • radialAxis) (TFUnitData.ray_ne_zero hr)
    (by rw [TFUnitData.ray_norm hr]; exact min_le_left _ _))).1
  rw [TFUnitData.ray_norm hr] at hh
  have ht := (le_div_iff₀ (show 0 < C+2 by linarith)).mp (show r₀ ≤ 1/(C+2) from min_le_right _ _)
  have hi : C+2 ≤ 1/r₀ := (le_div_iff₀ hr).mpr (by nlinarith)
  norm_num at hh
  rw [one_div] at hi
  linarith

lemma tfInfiniteField_singular_lower : ∃ c > 0, ∃ R > 0,
    ∀ x, x ≠ 0 → ‖x‖ ≤ R → c * CoulombPDE.radialPower (-2) x ≤ tfInfiniteField x := by
  obtain ⟨r₀, hr, hb⟩ := tf_first_field_large
  refine ⟨r₀^4, pow_pos hr _, r₀, hr, ?_⟩
  intro x hx hxr
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let a := r₀/‖x‖
  have ha : 1 ≤ a := (one_le_div hn).mpr hxr
  have he : ‖a • x‖ = ‖r₀ • radialAxis‖ := by
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans ha), TFUnitData.ray_norm hr]
    exact div_mul_cancel₀ _ hn.ne'
  have hval := (tfIncreasingData 0).field_radial _ _ he
  have hc := tfInfiniteField_dominates_dilation ha x hx
  rw [CoulombPDE.shiftedDilation, hval] at hc
  have hp : a^4 ≤ tfInfiniteField x := by nlinarith [pow_nonneg (zero_le_one.trans ha) 4]
  have ht : a^4 = r₀^4 * CoulombPDE.radialPower (-2) x := by
    have hmul := CoulombPDE.norm_four_mul_radialPower hx
    dsimp [a]
    rw [div_pow, div_eq_iff (pow_ne_zero _ hn.ne')]
    calc
      r₀^4 = r₀^4 * (‖x‖^4 * CoulombPDE.radialPower (-2) x) := by rw [hmul, mul_one]
      _ = _ := by ring
  rwa [ht] at hp

theorem tfInfiniteField_singularProfile : CoulombPDE.SingularProfile tfReactionCoefficient tfInfiniteField := by
  refine ⟨fun _ hx => (tfInfiniteField_classical hx).1,
    fun _ hx => (tfInfiniteField_classical hx).2, tfInfiniteField_decay, ?_⟩
  obtain ⟨c, hc, R, hR, hl⟩ := tfInfiniteField_singular_lower
  let A := CoulombPDE.sommerfeldCoefficient tfReactionCoefficient
  have hA : 0 < A := CoulombPDE.sommerfeldCoefficient_pos tfReactionCoefficient_pos
  refine ⟨c, hc, A+1, by linarith, min R 1, lt_min hR zero_lt_one,
    fun x hx hr => hl x hx (hr.trans (min_le_left _ _)), ?_⟩
  intro x hx hr
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu := tfInfiniteRadial_upper hn
  have hmul := CoulombPDE.norm_four_mul_radialPower hx
  have hpow : ‖x‖^4 ≤ 1 := by
    exact pow_le_one₀ (norm_nonneg x) (hr.trans (min_le_right _ _))
  have hrp := CoulombPDE.radialPower_pos (-2) hx
  have hlow : 1 ≤ CoulombPDE.radialPower (-2) x := by nlinarith
  have he : A / ‖x‖^4 = A * CoulombPDE.radialPower (-2) x := by
    apply (div_eq_iff (pow_ne_zero _ hn.ne')).mpr
    nlinarith
  change tfInfiniteField x ≤ 1 + A / ‖x‖^4 at hu
  rw [he] at hu
  nlinarith


open MeasureTheory Filter Set Metric Topology
section
open CoulombAtom

lemma TFUnitData.exterior_field {Z r : ℝ} (D : TFUnitData Z) (hZ : 0 < Z)
    (hr : tfSupportRadius ≤ r) : D.radialField r = (Z-D.mass)/r := by
  have hr0 : 0 < r := (zero_lt_one.trans tfSupportRadius_gt_one).trans_le hr
  rw [D.radialField_ray hZ hr0, TFUnitData.field, tfField]
  rw [tfPotential_newton_exterior_closed D.admissible.2.1 (tfAdmissible_memLp D.admissible)
    D.radial (zero_lt_one.trans tfSupportRadius_gt_one)
    (fun y hy => le_of_not_gt (fun hh => hy (D.uniform_support hZ y hh.le)))
    (by rw [TFUnitData.ray_norm hr0]; exact hr)]
  rw [D.admissible.2.2.1, TFUnitData.ray_norm hr0, sub_div]

lemma TFUnitData.radialField_le_infinite {Z r : ℝ} (D : TFUnitData Z)
    (hZ : 0 < Z) (hr : 0 < r) : D.radialField r ≤ tfInfiniteRadial r := by
  obtain ⟨n, hn⟩ := exists_nat_gt Z
  have hh := (D.finiteProfile hZ).compare ((tfIncreasingData n).finiteProfile (by positivity))
    tfReactionCoefficient_pos.le (show Z < (n:ℝ)+1 by linarith)
    (r • radialAxis) (TFUnitData.ray_ne_zero hr)
  rw [← D.radialField_ray hZ hr, ← (tfIncreasingData n).radialField_ray (by positivity) hr] at hh
  exact hh.trans (tfIncreasingField_le hr n)

lemma tfRealRadial_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun Z => tfRealRadial Z r) atTop (𝓝 (tfInfiniteRadial r)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨n, hn⟩ := (eventually_atTop.1 ((tendsto_order.1 (tfIncreasingField_tendsto hr)).1 a ha))
    filter_upwards [eventually_gt_atTop ((n:ℝ)+1)] with Z hZ
    have hZ0 : 0 < Z := (by positivity : (0:ℝ) < n+1).trans hZ
    rw [tfRealRadial, dite_eq_left hZ0]
    have hh := ((tfIncreasingData n).finiteProfile (by positivity)).compare
      ((tfUnitData Z hZ0).finiteProfile hZ0) tfReactionCoefficient_pos.le hZ
      (r • radialAxis) (TFUnitData.ray_ne_zero hr)
    rw [← (tfIncreasingData n).radialField_ray (by positivity) hr,
      ← (tfUnitData Z hZ0).radialField_ray hZ0 hr] at hh
    exact (hn n le_rfl).trans_le hh
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
    rw [tfRealRadial, dite_eq_left hZ]
    exact ((tfUnitData Z hZ).radialField_le_infinite hZ hr).trans_lt ha

lemma TFUnitData.deficit_eq {Z : ℝ} (D : TFUnitData Z) (hZ : 0 < Z) :
    Z-D.mass = tfSupportRadius * D.radialField tfSupportRadius := by
  rw [D.exterior_field hZ le_rfl]
  exact (mul_div_cancel₀ _ (zero_lt_one.trans tfSupportRadius_gt_one).ne').symm

theorem tf_unit_deficit_tendsto : Tendsto tfUnitDeficit atTop (𝓝 tfResidualCharge) := by
  have ht := (tfRealRadial_tendsto (zero_lt_one.trans tfSupportRadius_gt_one)).const_mul tfSupportRadius
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
  rw [tfRealRadial, tfUnitDeficit, dite_eq_left hZ, dite_eq_left hZ]
  exact ((tfUnitData Z hZ).deficit_eq hZ).symm

end

open MeasureTheory Filter Set Metric Topology

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_WeakSommerfeldAsymptoticBarrier
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
open scoped Topology

namespace CoulombAnalysis
open CoulombPDE

theorem weak_sommerfeld_asymptotic {F : Space → ℝ} {d c C R : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hC : 0 ≤ C) (hR : 0 < R)
    (hreg : ContinuousOn F {0}ᶜ)
    (hpde : PuncturedPoisson F (fun x => reaction d (F x)))
    (hlower : ∀ x, x ≠ 0 → ‖x‖ ≤ R → c * radialPower (-2) x ≤ F x)
    (hupper : ∀ x, x ≠ 0 → ‖x‖ ≤ R → F x ≤ C * radialPower (-2) x) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space)) (𝓝 (sommerfeldCoefficient d)) := by
  have hA : 0 < sommerfeldCoefficient d := sommerfeldCoefficient_pos hd
  have hn : Tendsto (fun x : Space => ‖x‖) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt.tendsto (x := (0 : Space))).mono_left nhdsWithin_le_nhds
  have hfour : Tendsto (fun x : Space => ‖x‖ ^ 4) (𝓝[≠] (0 : Space)) (𝓝 0) := by
    simpa using hn.pow 4
  have hball : ∀ᶠ x : Space in 𝓝[≠] (0 : Space), x ≠ 0 ∧ ‖x‖ ≤ R := by
    have hsmall : ∀ᶠ x : Space in 𝓝 (0 : Space), ‖x‖ < R := by
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hR] with x hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with x hx hr
    exact ⟨hx, hr.le⟩
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨B, hB₁, hB₂⟩ := exists_between (max_lt hA ha)
    have hB : 0 < B := (le_max_left _ _).trans_lt hB₁
    have haB : a < B := (le_max_right _ _).trans_lt hB₁
    have hq : d * B ^ (1 / 2 : ℝ) < 12 := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hB.le hB₂ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := B * (R ^ 2) ^ (-2 : ℝ)
    have ht : Tendsto (fun x : Space => B - ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.sub (hfour.mul_const D)
    have he := ht.eventually (eventually_gt_nhds haB)
    filter_upwards [hball, he] with x hx he
    have hl := weak_singular_lower_bound hd hc hR hB hq hreg hpde hlower x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith
  · intro b hb
    obtain ⟨B, hB₁, hB₂⟩ := exists_between hb
    have hB : 0 < B := hA.trans hB₁
    have hq : 12 < d * B ^ (1 / 2 : ℝ) := by
      have h := mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hA.le hB₁ (by norm_num : (0 : ℝ) < 1 / 2)) hd
      rwa [sommerfeldCoefficient_half hd] at h
    let D := C * (R ^ 2) ^ (-2 : ℝ) + 1
    have ht : Tendsto (fun x : Space => B + ‖x‖ ^ 4 * D) (𝓝[≠] (0 : Space)) (𝓝 B) := by
      simpa using tendsto_const_nhds.add (hfour.mul_const D)
    have he := ht.eventually (eventually_lt_nhds hB₂)
    filter_upwards [hball, he] with x hx he
    have hl := weak_singular_upper_bound hd hC hR hB hq hreg hpde hupper x hx.1 hx.2
    have hmul := mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg x) 4)
    have hu := norm_four_mul_radialPower hx.1
    dsimp [D] at he
    nlinarith

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_WeakSingularProfileBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakSingularProfile_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

open CoulombPDE

lemma WeakSingularProfile.of_classical {d : ℝ} {F : Space → ℝ}
    (h : SingularProfile d F) : WeakSingularProfile d F :=
  ⟨fun x hx => (h.regular x hx).continuousAt.continuousWithinAt,
    (PuncturedPoisson.of_classical h.regular).congr_source (fun x hx => h.equation x hx),
    h.decay,h.bounds⟩

lemma WeakSingularProfile.asymptotic {d : ℝ} {F : Space → ℝ}
    (h : WeakSingularProfile d F) (hd : 0 < d) :
    Tendsto (fun x => ‖x‖ ^ 4 * F x) (𝓝[≠] (0 : Space))
      (𝓝 (sommerfeldCoefficient d)) := by
  obtain ⟨c,hc,C,hC,R,hR,hl,hu⟩ := h.bounds
  exact weak_sommerfeld_asymptotic hd hc hC.le hR h.continuous h.equation hl hu

lemma WeakSingularProfile.scaled_comparison {d α δ : ℝ} {F₁ F₂ : Space → ℝ}
    (h₁ : WeakSingularProfile d F₁) (h₂ : WeakSingularProfile d F₂)
    (hd : 0 < d) (hα : 1 < α) (hδ : 0 < δ) :
    ∀ x, x ≠ 0 → F₂ x ≤ α * F₁ x + δ := by
  let G : Space → ℝ := fun x => α * F₁ x + δ
  have hGc : ContinuousOn G {0}ᶜ :=
    (continuousOn_const.mul h₁.continuous).add continuousOn_const
  have hG : PuncturedPoisson G (fun x => α*reaction d (F₁ x)) :=
    (h₁.equation.const_mul α).add_const
      (continuousOn_const.mul h₁.continuous)
      (continuousOn_const.mul ((reaction_continuous d).comp_continuousOn h₁.continuous)) δ
  have hdiff := h₂.equation.sub hG h₂.continuous hGc
    ((reaction_continuous d).comp_continuousOn h₂.continuous)
    (continuousOn_const.mul ((reaction_continuous d).comp_continuousOn h₁.continuous))
  have hnear : ∀ᶠ x in 𝓝[≠] (0 : Space), F₂ x - G x ≤ 0 := by
    have ht : Tendsto (fun x : Space => ‖x‖ ^ 4 * (α * F₁ x - F₂ x))
        (𝓝[≠] (0 : Space)) (𝓝 ((α - 1) * sommerfeldCoefficient d)) := by
      convert ((h₁.asymptotic hd).const_mul α).sub (h₂.asymptotic hd) using 1 <;> (try funext x) <;> ring_nf
    have hp : 0 < (α - 1) * sommerfeldCoefficient d :=
      mul_pos (sub_pos.mpr hα) (sommerfeldCoefficient_pos hd)
    filter_upwards [ht.eventually (eventually_gt_nhds hp), self_mem_nhdsWithin] with x hx hxn
    have hn : 0 < ‖x‖ ^ 4 := pow_pos (norm_pos_iff.mpr hxn) _
    have hu : 0 < α * F₁ x - F₂ x := (mul_pos_iff_of_pos_left hn).mp hx
    dsimp [G]
    linarith
  have hfar : ∃ R > 0, ∀ x, R ≤ ‖x‖ → F₂ x - G x ≤ 0 := by
    let ε := δ / (2 * (α + 1))
    have he : 0 < ε := div_pos hδ (by linarith)
    have heq : ε * (2 * (α + 1)) = δ := by
      exact div_mul_cancel₀ _ (by linarith)
    obtain ⟨R₁, hR₁, hb₁⟩ := h₁.decay ε he
    obtain ⟨R₂, _hR₂, hb₂⟩ := h₂.decay ε he
    refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
    intro x hx
    have h1 := (abs_lt.mp (hb₁ x ((le_max_left _ _).trans hx))).1
    have h2 := (abs_lt.mp (hb₂ x ((le_max_right _ _).trans hx))).2
    dsimp [G]
    nlinarith [mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ F₁ x + ε by linarith)]
  have hm := weak_global_punctured_maximum
    (u := F₂-G) (h₂.continuous.sub hGc)
    (fun g hg hcg hs hgn => hdiff.nonneg_on_positive (fun x _hx hp => ?_) hg hcg hs hgn)
    (deleted_eventually_to_small_ball hnear) hfar
  · exact fun x hx => sub_nonpos.mp (hm x hx)
  · have hmon := reaction_monotone hd.le (le_of_lt (sub_pos.mp hp))
    have hsuper := reaction_superlinear (v := F₁ x) hd.le hα.le hδ.le
    change 0 ≤ reaction d (F₂ x)-α*reaction d (F₁ x)
    dsimp [G] at hmon
    linarith

theorem weak_singular_profile_unique {d : ℝ} {F₁ F₂ : Space → ℝ}
    (hd : 0 < d) (h₁ : WeakSingularProfile d F₁) (h₂ : WeakSingularProfile d F₂) :
    EqOn F₁ F₂ ({0}ᶜ) := by
  have hle {F G : Space → ℝ} (hF : WeakSingularProfile d F) (hG : WeakSingularProfile d G)
      (x : Space) (hx : x ≠ 0) : G x ≤ F x := by
    have hscaled (α : ℝ) (hα : 1 < α) : G x ≤ α * F x := by
      apply le_of_forall_pos_le_add
      intro δ hδ
      exact hF.scaled_comparison hG hd hα hδ x hx
    have ht : Tendsto (fun t : ℝ => (1 + t) * F x) (𝓝[>] 0) (𝓝 (F x)) := by
      have h : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa using (h.const_add 1).mul_const (F x)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hscaled (1 + t) (by change 0 < t at ht; linarith)
  intro x hx
  exact le_antisymm (hle h₂ h₁ x hx) (hle h₁ h₂ x hx)

theorem weak_profile_eq_tfInfiniteField {F : Space → ℝ}
    (h : WeakSingularProfile tfReactionCoefficient F) :
    EqOn F tfInfiniteField {0}ᶜ :=
  weak_singular_profile_unique tfReactionCoefficient_pos h
    (WeakSingularProfile.of_classical tfInfiniteField_singularProfile)

end Work_WeakSingularProfile_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombAtom CoulombPDE

lemma weak_profile_of_cap_barrier {F : CoulombAtom.Space → ℝ} {d B C : ℝ}
    (hc : ContinuousOn F {0}ᶜ)
    (he : PuncturedPoisson F (fun x => reaction d (F x)))
    (hB : 0 < B) (hC : 0 ≤ C)
    (hl : ∀ x, x ≠ 0 → B/‖x‖^4 ≤ F x)
    (hu : ∀ x, x ≠ 0 → F x ≤ 1+C/‖x‖^4)
    (hd : ∀ ε > 0, ∃ R > 0, ∀ x : CoulombAtom.Space, R ≤ ‖x‖ → |F x| < ε) :
    WeakSingularProfile d F := by
  refine ⟨hc,he,hd,B,hB,C+1,by linarith,1,zero_lt_one,?_,?_⟩
  · intro x hx _
    have hm := norm_four_mul_radialPower hx
    have hn : ‖x‖^4 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    have heq : B/‖x‖^4 = B*radialPower (-2) x := by
      apply (div_eq_iff hn).mpr
      nlinarith
    simpa only [heq] using hl x hx
  · intro x hx hr
    have hm := norm_four_mul_radialPower hx
    have hn : ‖x‖^4 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
    have hp := radialPower_pos (-2) hx
    have hpow : ‖x‖^4 ≤ 1 := pow_le_one₀ (norm_nonneg x) hr
    have hrp : 1 ≤ radialPower (-2) x := by nlinarith
    have heq : C/‖x‖^4 = C*radialPower (-2) x := by
      apply (div_eq_iff hn).mpr
      nlinarith
    have hh := hu x hx
    rw [heq] at hh
    nlinarith

lemma tfInfiniteRadial_exterior {r : ℝ} (hr : tfSupportRadius ≤ r) :
    tfInfiniteRadial r = tfResidualCharge/r := by
  have hr0 : 0 < r := (zero_lt_one.trans tfSupportRadius_gt_one).trans_le hr
  apply tendsto_nhds_unique (tfRealRadial_tendsto hr0)
  apply (tf_unit_deficit_tendsto.div_const r).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Z hZ
  rw [tfRealRadial,tfUnitDeficit,dite_eq_left hZ,dite_eq_left hZ]
  exact ((tfUnitData Z hZ).exterior_field hZ hr).symm

lemma tfInfiniteField_sphereMean (p : CoulombAtom.Space) : sphereMean tfInfiniteField p = tfInfiniteRadial ‖p‖ := by
  unfold sphereMean tfInfiniteField
  simp only [(rotate _).norm_map,integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem weak_profile_charge_eq {F : CoulombAtom.Space → ℝ} {q R : ℝ}
    (h : WeakSingularProfile tfReactionCoefficient F)
    (hm : ∀ p : CoulombAtom.Space, R < ‖p‖ → sphereMean F p = q/‖p‖) :
    q = tfResidualCharge := by
  let r := max R tfSupportRadius+1
  have hr : 0 < r := by
    have hh := le_max_right R tfSupportRadius
    have hh' := zero_lt_one.trans tfSupportRadius_gt_one
    dsimp [r]
    linarith
  let p : CoulombAtom.Space := r • radialAxis
  have hpn : ‖p‖ = r := TFUnitData.ray_norm hr
  have he : sphereMean F p = sphereMean tfInfiniteField p := by
    unfold sphereMean
    apply integral_congr_ae
    exact ae_of_all _ (fun g => weak_profile_eq_tfInfiniteField h
      (rotate_ne_zero g (TFUnitData.ray_ne_zero hr)))
  rw [hm p (by rw [hpn]; dsimp [r]; linarith [le_max_left R tfSupportRadius]),
    tfInfiniteField_sphereMean,hpn,tfInfiniteRadial_exterior (by
      dsimp [r]; linarith [le_max_right R tfSupportRadius])] at he
  exact (div_left_inj' hr.ne').mp he

theorem weak_limit_identification {F : CoulombAtom.Space → ℝ} {q R B C : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hC : 0 ≤ C)
    (hc : ContinuousOn F {0}ᶜ)
    (he : PuncturedPoisson F (fun x => reaction tfReactionCoefficient (F x)))
    (hh : ∀ g : CoulombAtom.Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, F x*Laplacian.laplacian g x) = 0)
    (hm : ∀ p : CoulombAtom.Space, R < ‖p‖ → sphereMean F p = q/‖p‖)
    (hl : ∀ x, x ≠ 0 → B/‖x‖^4 ≤ F x)
    (hu : ∀ x, x ≠ 0 → F x ≤ 1+C/‖x‖^4) :
    EqOn F tfInfiniteField {0}ᶜ ∧ q = tfResidualCharge := by
  have hb : ∀ x : CoulombAtom.Space, R ≤ ‖x‖ → F x ≤ 1+C/R^4 := by
    intro x hx
    have hp : 0 < ‖x‖ := hR.trans_le hx
    apply (hu x (norm_pos_iff.mp hp)).trans
    exact add_le_add_right (div_le_div_of_nonneg_left hC (pow_pos hR 4)
      (pow_le_pow_left₀ hR.le hx 4)) 1
  have hd := weak_exterior_mean_uniform_decay hR hc hh hb hm
  have hp := weak_profile_of_cap_barrier hc he hB hC hl hu hd
  exact ⟨weak_profile_eq_tfInfiniteField hp,weak_profile_charge_eq hp hm⟩

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_AnnularApproximationLimitBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite
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

lemma annular_tf_error_local {ι : Type*} {F : Filter ι}
    {a l : ι → ℝ} {f ρ : ι → Space → ℝ} {k : ℝ}
    (ha : Tendsto a F (𝓝 0)) (hl : Tendsto l F atTop)
    (hTF : ∀ i x, a i ≤ ‖x‖ → ‖x‖ ≤ l i →
      |ρ i x-k*(max (f i x-1) 0)^(3/2:ℝ)| ≤ (l i)⁻¹^8/‖x‖^6)
    {K : Set Space} (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
    ∃ e : ι → ℝ, Tendsto e F (𝓝 0) ∧ ∀ᶠ i in F, ∀ x ∈ K,
      |ρ i x-k*(max (f i x-1) 0)^(3/2:ℝ)| ≤ e i := by
  obtain ⟨A,B,hA,_hB,hKB⟩ := compact_away_zero_annulus hK hK0
  refine ⟨fun i => (l i)⁻¹^8/A^6,?_,?_⟩
  · simpa only [Function.comp_def,zero_pow (by norm_num : (8:ℕ) ≠ 0),zero_div] using
      ((tendsto_inv_atTop_zero.comp hl).pow 8).div_const (A^6)
  · filter_upwards [ha.eventually (gt_mem_nhds hA),hl.eventually (eventually_ge_atTop B)]
      with i hi hi' x hx
    apply (hTF i x (hi.le.trans (hKB hx).1) ((hKB hx).2.trans hi')).trans
    exact div_le_div_of_nonneg_left (by positivity)
      (pow_pos hA 6) (pow_le_pow_left₀ hA.le (hKB hx).1 6)

lemma annular_upper_cap_limit {ι : Type*} {F : Filter ι} [NeBot F]
    {a l : ι → ℝ} {f : ι → Space → ℝ} {u : Space → ℝ} {C : ℝ}
    (ha : Tendsto a F (𝓝 0)) (hl : Tendsto l F atTop)
    (hc : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn f u F K)
    (hcap : ∀ᶠ i in F, ∀ x, a i ≤ ‖x‖ → ‖x‖ ≤ l i → f i x ≤ 1+C/‖x‖^4) :
    ∀ x, x ≠ 0 → u x ≤ 1+C/‖x‖^4 := by
  intro x hx
  have ht : Tendsto (fun i => f i x) F (𝓝 (u x)) :=
    (hc {x} (isCompact_singleton) (singleton_subset_iff.mpr hx)).tendsto_at (mem_singleton x)
  apply le_of_tendsto ht
  filter_upwards [hcap,ha.eventually (gt_mem_nhds (norm_pos_iff.mpr hx)),
    hl.eventually (eventually_ge_atTop ‖x‖)] with i hi hi' hi''
  exact hi x hi'.le hi''

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_SelectedScreenedProfileBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite
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

lemma tfDensityCoefficient_pos : 0 < tfDensityCoefficient := by
  unfold tfDensityCoefficient
  have hh := tfKinetic_pos
  positivity
lemma tfDensityCoefficient_reaction : 4*Real.pi*tfDensityCoefficient = tfReactionCoefficient := rfl
end CoulombAnalysis

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

theorem selected_screened_profile {ι : Type*} {F : Filter ι} [NeBot F]
    {s r l Z : ι → ℝ} {a μ p : ι → TFSpace → ℝ} {B C Ccap R q : ℝ}
    {F_lim : TFSpace → ℝ}
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i)
    (hs0 : Tendsto s F (𝓝 0)) (hr0 : Tendsto (fun i => r i/s i) F (𝓝 0))
    (hl : ∀ i, 0 < l i) (hl0 : Tendsto l F atTop)
    (hal : ∀ i, 1/(2*l i) ≤ r i/s i)
    (hB : 0 < B) (hC : 0 ≤ C) (hCcap : 0 ≤ Ccap) (hR : 0 < R)
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
        outerCoefficient (r i) x*reaction tfDensityCoefficient (nuclearField (Z i) x+a i x)))
    (hlower : ∀ i y, r i ≤ ‖y‖ → outerBarrier B (r i) y ≤ nuclearField (Z i) y+a i y)
    (hupper : ∀ i y, r i ≤ ‖y‖ → nuclearField (Z i) y+a i y ≤ C/‖y‖^4)
    (hTF : ∀ i x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
      |tfDilation (s i) (μ i) x-
        tfDensityCoefficient*(max (nuclearField ((s i)^3*Z i) x-
          tfPotential (tfDilation (s i) (μ i)) x-1) 0)^(3/2:ℝ)| ≤ (l i)⁻¹^8/‖x‖^6)
    (hcont : ContinuousOn F_lim {0}ᶜ)
    (hconv : ∀ K : Set TFSpace, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn
      (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
      F_lim F K)
    (hcap : ∀ᶠ i in F, ∀ x, r i/s i ≤ ‖x‖ → ‖x‖ ≤ l i →
      nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x ≤ 1+Ccap/‖x‖^4)
    (hq : Tendsto (fun i => (s i)^3*(Z i-∫ x, μ i x)) F (𝓝 q))
    (htail : Tendsto (fun i => ∫ x in {x : TFSpace | R < ‖x‖}, tfDilation (s i) (μ i) x)
      F (𝓝 0)) :
    EqOn F_lim tfInfiniteField {0}ᶜ ∧ q = tfResidualCharge := by
  have hscaled (i : ι) : ∃ M ≥ 0, ∀ x, tfDilation (s i) (μ i) x ≤ M := by
    obtain ⟨M,hM,hMb⟩ := hμb i
    exact ⟨(s i)^6*M,mul_nonneg (by positivity) hM,
      fun x => mul_le_mul_of_nonneg_left (hMb _) (by positivity)⟩
  have hcaplim := annular_upper_cap_limit hr0 hl0 hconv hcap
  have hq' : Tendsto (fun i => (s i)^3*Z i-∫ x, tfDilation (s i) (μ i) x) F (𝓝 q) := by
    simpa only [tfDilation_mass (hs _),mul_sub] using hq
  have hdyn := screened_limit_dynamics hR hCcap
    (fun i => tfDilation_measurable (hμm i))
    (fun i => tfDilation_integrable (hs i) (hμi i))
    (fun i => tfDilation_nonneg (hμn i)) hscaled hcont hconv
    (fun _ hK hK0 => annular_tf_error_local hr0 hl0 hTF hK hK0) hq' htail hcaplim
  have hsphere (S : ℝ) (hS : 0 < S) : TendstoUniformlyOn
      (fun i x => nuclearField ((s i)^3*Z i) x-tfPotential (tfDilation (s i) (μ i)) x)
      F_lim F (sphere (0:TFSpace) S) := by
    apply hconv _ (isCompact_sphere _ _)
    intro x hx hx0
    rw [mem_sphere_zero_iff_norm,hx0,norm_zero] at hx
    exact hS.ne' hx.symm
  have hpositive := selected_barriers_limit_positive hs hr hs0 hr0 hl hl0 hal
    tfDensityCoefficient_pos.le hC ha hμm hμi hμn hμb hpm hpi hpn hpb hpSupport hpMass
    hweak hlower hupper (fun i x hx hx' => by
      have hh := (abs_le.mp (hTF i x hx hx')).2
      linarith only [hh]) hsphere hdyn.2.2.2
  apply weak_limit_identification hR hB hCcap hcont _ hdyn.2.1 hdyn.2.2.1 hpositive hcaplim
  simpa only [tfDensityCoefficient_reaction] using hdyn.1

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SelectedData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis

lemma uniform_bound_of_eventual {α : Type*} {f : ℕ → α → ℝ} {K : Set α}
    (hf : ∀ n, ∃ M ≥ 0, ∀ x ∈ K, f n x ≤ M)
    (he : ∃ M ≥ 0, ∀ᶠ n in atTop, ∀ x ∈ K, f n x ≤ M) :
    ∃ M ≥ 0, ∀ n x, x ∈ K → f n x ≤ M := by
  classical
  choose b hb hfb using hf
  obtain ⟨M,hM,he⟩ := he
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp he
  refine ⟨M+∑ n ∈ Finset.range n₀, b n,add_nonneg hM (Finset.sum_nonneg (fun n _ => hb n)),?_⟩
  intro n x hx
  by_cases hn : n₀ ≤ n
  · exact (hn₀ n hn x hx).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun n _ => hb n)))
  · have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range n₀) => hb i)
      (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact (hfb n x hx).trans (hh.trans (le_add_of_nonneg_left hM))

lemma SelectedQuantumData.scaled_bounded {Z s l τ B C R : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hs : 0 < s) :
    ∃ M ≥ 0, ∀ x, tfDilation s d.density x ≤ M := by
  obtain ⟨M,hM,hMb⟩ := d.bounded_density
  exact ⟨s^6*M,mul_nonneg (pow_nonneg hs.le 6) hM,
    fun x => mul_le_mul_of_nonneg_left (hMb _) (pow_nonneg hs.le 6)⟩

lemma SelectedQuantumData.scaled_TF_bound {Z s l τ B C R a : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hl : 1 ≤ l) (ha : 0 < a)
    {x : TFSpace} (hxa : a ≤ ‖x‖) (hxl : d.radius/s ≤ ‖x‖) (hxh : ‖x‖ ≤ l) :
    tfDilation s d.density x ≤
      tfDensityCoefficient*(actualInverseCap/a^4)^(3/2:ℝ)+1/a^6 := by
  have hC : 0 ≤ actualInverseCap := by
    have := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  have hcap := d.cap x hxl hxh
  have hdiv : actualInverseCap/‖x‖^4 ≤ actualInverseCap/a^4 := by gcongr
  have hmax : max (nuclearField (s^3*Z) x-tfPotential (tfDilation s d.density) x-1) 0 ≤ actualInverseCap/a^4 :=
    max_le (by linarith) (by positivity)
  have hpow : l⁻¹^8 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (zero_lt_one.trans_le hl).le)
    ((inv_le_one₀ (zero_lt_one.trans_le hl)).mpr hl)
  have herr : l⁻¹^8/‖x‖^6 ≤ 1/a^6 := by gcongr
  have hreact : tfDensityCoefficient*(max (nuclearField (s^3*Z) x-
      tfPotential (tfDilation s d.density) x-1) 0)^(3/2:ℝ) ≤
      tfDensityCoefficient*(actualInverseCap/a^4)^(3/2:ℝ) := by
    apply mul_le_mul_of_nonneg_left _ tfDensityCoefficient_pos.le
    exact Real.rpow_le_rpow (le_max_right _ _) hmax (by norm_num)
  have ht := (abs_le.mp (d.TF x hxl hxh)).2
  linarith

lemma selected_data_local_bounds {Z s l τ : ℕ → ℝ} {N : ℕ → ℕ} {B C R : ℝ}
    (d : ∀ n, SelectedQuantumData (Z n) (N n) (s n) (l n) (τ n) B C R)
    (hZ : ∀ n, 0 ≤ Z n) (hs : ∀ n, 0 < s n) (hl : ∀ n, 1 ≤ l n)
    (hl0 : Tendsto l atTop atTop) :
    (∀ K : Set TFSpace, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M ≥ 0, ∀ n x, x ∈ K → nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M) ∧
    (∀ K : Set TFSpace, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M ≥ 0, ∀ n x, x ∈ K → tfDilation (s n) (d n).density x ≤ M) := by
  have hC : 0 ≤ actualInverseCap := by
    have := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  have local_bounds (K : Set TFSpace) (hK : IsCompact K) (hK0 : K ⊆ {0}ᶜ) :
      (∃ M ≥ 0, ∀ n x, x ∈ K → nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M) ∧
      (∃ M ≥ 0, ∀ n x, x ∈ K → tfDilation (s n) (d n).density x ≤ M) := by
    obtain ⟨a,b,ha,hb,hann⟩ := compact_away_zero_annulus hK hK0
    have hinv : Tendsto (fun n => (l n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hl0
    have he : ∀ᶠ n in atTop, ∀ x ∈ K, (d n).radius/s n ≤ ‖x‖ ∧ ‖x‖ ≤ l n := by
      filter_upwards [hinv.eventually (gt_mem_nhds ha),hl0.eventually_ge_atTop b] with n hna hnb x hx
      exact ⟨((d n).radius_upper.trans hna.le).trans (hann hx).1,(hann hx).2.trans hnb⟩
    have hf (n) : ∃ M ≥ 0, ∀ x ∈ K, nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M := by
      refine ⟨((s n)^3*Z n)/a,div_nonneg (mul_nonneg (pow_nonneg (hs n).le 3) (hZ n)) ha.le,?_⟩
      intro x hx
      have hp : 0 ≤ tfPotential (tfDilation (s n) (d n).density) x :=
        tfPotential_nonneg (Eventually.of_forall (tfDilation_nonneg (d n).nonneg_density)) x
      have hn : ((s n)^3*Z n)/‖x‖ ≤ ((s n)^3*Z n)/a := by
        apply div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg (hs n).le 3) (hZ n)) ha (hann hx).1
      unfold nuclearField
      linarith
    have hfe : ∃ M ≥ 0, ∀ᶠ n in atTop, ∀ x ∈ K, nuclearField ((s n)^3*Z n) x-
        tfPotential (tfDilation (s n) (d n).density) x ≤ M := by
      refine ⟨1+actualInverseCap/a^4,by positivity,?_⟩
      filter_upwards [he] with n hn x hx
      have hh := (d n).cap x (hn x hx).1 (hn x hx).2
      have hd : actualInverseCap/‖x‖^4 ≤ actualInverseCap/a^4 := by
        gcongr
        exact (hann hx).1
      linarith
    have hρf (n) : ∃ M ≥ 0, ∀ x ∈ K, tfDilation (s n) (d n).density x ≤ M := by
      obtain ⟨M,hM,hMb⟩ := (d n).scaled_bounded (hs n)
      exact ⟨M,hM,fun x _ => hMb x⟩
    have hρe : ∃ M ≥ 0, ∀ᶠ n in atTop, ∀ x ∈ K, tfDilation (s n) (d n).density x ≤ M := by
      refine ⟨tfDensityCoefficient*(actualInverseCap/a^4)^(3/2:ℝ)+1/a^6,by
        have := tfDensityCoefficient_pos
        positivity,?_⟩
      filter_upwards [he] with n hn x hx
      exact (d n).scaled_TF_bound (hl n) ha (hann hx).1 (hn x hx).1 (hn x hx).2
    exact ⟨uniform_bound_of_eventual hf hfe,uniform_bound_of_eventual hρf hρe⟩
  exact ⟨fun K hK hK0 => (local_bounds K hK hK0).1,fun K hK hK0 => (local_bounds K hK hK0).2⟩

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_SelectedProfileSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma selected_data_profile_subsequence_oai {Z s l τ : ℕ → ℝ} {N : ℕ → ℕ} {B C R Q : ℝ}
    (d : ∀ n, SelectedQuantumData (Z n) (N n) (s n) (l n) (τ n) B C R)
    (hZ : ∀ n, 0 ≤ Z n) (hs : ∀ n, 0 < s n) (hl : ∀ n, 1 ≤ l n)
    (hs0 : Tendsto s atTop (𝓝 0)) (hl0 : Tendsto l atTop atTop)
    (hτ0 : Tendsto τ atTop (𝓝 0)) (hB : 0 < B) (hC : 0 ≤ C) (hR : 0 < R)
    (hQ : 0 ≤ Q) (hq : ∀ n, |(s n)^3*(Z n-(N n:ℝ))| ≤ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (s (φ n))^3*(Z (φ n)-(N (φ n):ℝ))) atTop (𝓝 tfResidualCharge) := by
  let ρ : ℕ → TFSpace → ℝ := fun n => tfDilation (s n) (d n).density
  have hmass (n) : (∫ x, ρ n x) = (s n)^3*(N n:ℝ) := by
    rw [show ρ n = tfDilation (s n) (d n).density from rfl,tfDilation_mass (hs n),(d n).mass_density]
  have hq' (n) : |(s n)^3*Z n-∫ x, ρ n x| ≤ Q := by rw [hmass,←mul_sub]; exact hq n
  have hb := selected_data_local_bounds d hZ hs hl hl0
  obtain ⟨U,hUc,φ,hφ,hconv⟩ := screened_field_normal_family
    (fun n => tfDilation_measurable (d n).measurable_density)
    (fun n => tfDilation_integrable (hs n) (d n).integrable_density)
    (fun n => tfDilation_nonneg (d n).nonneg_density)
    (fun n => (d n).scaled_bounded (hs n)) hQ hq' hb.1 hb.2
  obtain ⟨q,hqI,ψ,hψ,hqlim⟩ := (isCompact_Icc : IsCompact (Icc (-Q) Q)).tendsto_subseq
    (fun n => abs_le.mp (hq (φ n)))
  let κ := φ ∘ ψ
  have hκ : StrictMono κ := hφ.comp hψ
  have hκt : Tendsto κ atTop atTop := hκ.tendsto_atTop
  have hrlim : Tendsto (fun n => (d (κ n)).radius/s (κ n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (div_pos (d (κ n)).radius_pos (hs (κ n))).le)
      (fun n => (d (κ n)).radius_upper) (tendsto_inv_atTop_zero.comp (hl0.comp hκt))
  have htail : Tendsto (fun n => ∫ x in {x : TFSpace | R < ‖x‖}, ρ (κ n) x) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun x => tfDilation_nonneg (d (κ n)).nonneg_density x))
      (fun n => (d (κ n)).tail) (hτ0.comp hκt)
  have hcap : 0 ≤ actualInverseCap := by
    have := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  have hprof := selected_screened_profile (s := s ∘ κ) (r := fun n => (d (κ n)).radius)
    (l := l ∘ κ) (Z := Z ∘ κ) (a := fun n => (d (κ n)).offset)
    (μ := fun n => (d (κ n)).density) (p := fun n => (d (κ n)).error)
    (B := B) (C := C) (Ccap := actualInverseCap) (R := R) (q := q) (F_lim := U)
    (fun n => hs (κ n)) (fun n => (d (κ n)).radius_pos) (hs0.comp hκt) hrlim
    (fun n => zero_lt_one.trans_le (hl (κ n))) (hl0.comp hκt)
    (fun n => (d (κ n)).radius_lower) hB hC hcap hR
    (fun n => (d (κ n)).continuous_offset) (fun n => (d (κ n)).measurable_density)
    (fun n => (d (κ n)).integrable_density) (fun n => (d (κ n)).nonneg_density)
    (fun n => (d (κ n)).bounded_density) (fun n => (d (κ n)).measurable_error)
    (fun n => (d (κ n)).integrable_error) (fun n => (d (κ n)).nonneg_error)
    (fun n => (d (κ n)).bounded_error) (fun n => (d (κ n)).support_error)
    (fun n => (d (κ n)).mass_error) (fun n => (d (κ n)).weak)
    (fun n => (d (κ n)).lower) (fun n => (d (κ n)).upper)
    (fun n => (d (κ n)).TF) hUc
    (fun K hK hK0 u hu => hψ.tendsto_atTop.eventually (hconv K hK hK0 u hu))
    (Eventually.of_forall (fun n => (d (κ n)).cap))
    (by simpa only [Function.comp_def,κ,(d _).mass_density] using hqlim) htail
  exact ⟨κ,hκ,hprof.2 ▸ hqlim⟩

end CoulombBarrier

end

end OAI
end

theorem solution : type_of% @OAI.CoulombBarrier.selected_data_profile_subsequence_oai := @OAI.CoulombBarrier.selected_data_profile_subsequence_oai

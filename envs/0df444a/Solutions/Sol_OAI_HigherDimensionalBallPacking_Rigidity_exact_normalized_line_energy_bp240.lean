-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:23.794688+00:00
-- url     : https://prove2.me/submissions/e324bb62-3e96-403b-88ad-31dee0fbd679

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp017
import Definitions.Def_OAIQ240Bp018
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_line_local_energy_of_slope_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CompatibleStructures
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.capacity_eq_stdDot _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_one _root_.OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdDot_J_right _root_.OAI.HigherDimensionalBallPacking.Rigidity.stdOmega_apply _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_nonneg {n : ℕ} (v : Phase n) : 0 ≤ stdDot n v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (stdDot_pos hv).le

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_TranslatedSquare
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma dilatedCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) :
    ContDiff ℝ ∞ (dilatedCurve u c) := hu.comp (contDiff_const.mul contDiff_id)

lemma dilatedCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c z : ℂ) :
    fderiv ℝ (dilatedCurve u c) z=(fderiv ℝ u (c*z)).comp (ContinuousLinearMap.mul ℝ ℂ c) := by
  have hh := (hu.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (c*z)).hasFDerivAt.comp z
    (ContinuousLinearMap.mul ℝ ℂ c).hasFDerivAt
  change HasFDerivAt (dilatedCurve u c) _ z at hh
  exact hh.fderiv

lemma dilatedCurve_CR {J : Phase n → End n} {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hCR : ∀ z,PseudoHolomorphicAt J u z) (c z : ℂ) :
    PseudoHolomorphicAt J (dilatedCurve u c) z := by
  refine ⟨(dilatedCurve_smooth hu c).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z,?_⟩
  intro w
  rw [dilatedCurve_fderiv hu]
  simp only [ContinuousLinearMap.comp_apply,dilatedCurve]
  change fderiv ℝ u (c*z) (c*(Complex.I*w))=J (u (c*z)) (fderiv ℝ u (c*z) (c*w))
  rw [show c*(Complex.I*w)=Complex.I*(c*w) by ring]
  exact (hCR (c*z)).2 (c*w)

lemma dilatedCurve_slope {u : ℂ → Phase n} {a : Phase n}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a))
    {c : ℂ} (hc : c≠0) :
    Tendsto (fun z : ℂ => z⁻¹ • dilatedCurve u c z) (cocompact ℂ) (𝓝 (c • a)) := by
  have hh := (ha.comp (Filter.tendsto_cocompact_mul_left₀ hc)).const_smul c
  apply hh.congr'
  exact Eventually.of_forall fun z => by
    dsimp only [Function.comp_def,dilatedCurve]
    rw [smul_smul]
    congr 1
    rw [mul_inv_rev,←mul_assoc,mul_comm c z⁻¹,mul_assoc,mul_inv_cancel₀ hc,mul_one]

lemma AffineLineCurve.dilate {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) {c : ℂ} (hc : c≠0) :
    AffineLineCurve J p (u c) (dilatedCurve u c) := by
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  refine ⟨dilatedCurve_smooth hu.1 c,dilatedCurve_CR hu.1 hu.2.1 c,?_,?_,
    c • a,smul_ne_zero hc ha,dilatedCurve_slope hlim hc⟩
  · simpa only [dilatedCurve,mul_zero] using hu.2.2.1
  · simp only [dilatedCurve,mul_one]


lemma slopeScale_pos {a : Phase n} (ha : a≠0) : 0 < slopeScale a := by
  unfold slopeScale
  exact inv_pos.mpr (Real.sqrt_pos.mpr (stdDot_pos ha))

lemma normalizedSlope_unit {a : Phase n} (ha : a≠0) :
    stdDot n ((slopeScale a) • a) ((slopeScale a) • a)=1 := by
  simp only [map_smul,smul_apply,smul_eq_mul,slopeScale]
  have hs : (Real.sqrt (stdDot n a a))^2=stdDot n a a := Real.sq_sqrt (stdDot_nonneg a)
  have hp : 0<Real.sqrt (stdDot n a a) := Real.sqrt_pos.mpr (stdDot_pos ha)
  field_simp
  nlinarith

lemma exact_normalized_line_energy_bp240_oai {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S < capacity x → J x=standardJ n) :
    ∃ B θ : ℝ,0<B ∧ 0<θ ∧ θ<1 ∧
      ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
        AffineLineCurve (lineHomotopy J t) p q u →
        ∀ a : Phase n,a≠0 → Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        ∀ (c : ℂ) (k : ℕ),
          radialCurveEnergy (centeredCurve (dilatedCurve u (slopeScale a)) c) ((1/16)^k)≤B*θ^k := by
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_local_energy_of_slope_bp240 hJs hJ hJc hST hT hout
  refine ⟨C+M,θ,by linarith,hθ,hθ1,?_⟩
  intro t ht p q u hu a ha hlim c k
  have hs : (slopeScale a : ℂ)≠0 := by exact_mod_cast (slopeScale_pos ha).ne'
  have hlu := dilatedCurve_slope hlim hs
  have he' := he t ht p (u (slopeScale a)) (dilatedCurve u (slopeScale a)) (hu.dilate hs)
    ((slopeScale a : ℂ) • a) hlu c k
  have hnorm : stdDot n ((slopeScale a : ℂ) • a) ((slopeScale a : ℂ) • a)=1 := by
    simpa only [Complex.coe_smul] using normalizedSlope_unit ha
  simpa only [hnorm,mul_one] using he'


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.exact_normalized_line_energy_bp240_oai

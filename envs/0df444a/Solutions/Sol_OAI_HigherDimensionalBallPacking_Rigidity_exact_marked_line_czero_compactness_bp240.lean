-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:55:28.571388+00:00
-- url     : https://prove2.me/submissions/4a948616-1ae1-4ceb-a174-71e6a844a2e7

import Mathlib
import Definitions.Def_BallPacking
import Definitions.Def_OAIQ240Bp020
import Definitions.Def_OAIQ240Bp021
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_exact_line_homotopy_residual_energy_bound_bp240
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

namespace HigherDimensionalBallPacking
open scoped ContDiff

noncomputable section
open scoped Topology
open Set Function Filter

namespace Rigidity

theorem complex_differentiable_of_CR {n : ℕ} {u : ℂ → Phase n} {z : ℂ}
    (hu : DifferentiableAt ℝ u z)
    (hCR : ∀ w : ℂ, fderiv ℝ u z (Complex.I * w) = standardJ n (fderiv ℝ u z w)) :
    DifferentiableAt ℂ u z := by
  let A := fderiv ℝ u z
  let L : ℂ →L[ℂ] Phase n := (ContinuousLinearMap.id ℂ ℂ).smulRight (A 1)
  have hL : L.restrictScalars ℝ = A := by
    ext w i
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_one, mul_one]
        using (Complex.re_add_im w).symm
    have hI : A Complex.I = standardJ n (A 1) := by
      simpa only [mul_one] using hCR 1
    have hAw : A w = w.re • A 1 + w.im • standardJ n (A 1) := by
      conv_lhs => rw [hw]
      simp only [map_add, map_smul, hI]
    rw [hAw]
    change w * A 1 i = _
    simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, standardJ_apply]
    rw [←mul_assoc, ←add_mul]
    congr 1
    exact (Complex.re_add_im w).symm
  exact (hasFDerivAt_of_restrictScalars ℝ hu.hasFDerivAt hL).differentiableAt

end Rigidity
end
end HigherDimensionalBallPacking

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity

theorem stdDot_symm {n : ℕ} (v w : Phase n) : stdDot n v w = stdDot n w v := by
  simp only [stdDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem stdDot_nonneg {n : ℕ} (v : Phase n) : 0 ≤ stdDot n v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (stdDot_pos hv).le

theorem standardForm_skew {n : ℕ} (v w : Phase n) :
    standardForm v w = -standardForm w v := by
  unfold standardForm
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Adapted
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter

theorem lineHomotopy_support {n : ℕ} (J : Phase n → End n)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    tsupport (fun x => lineHomotopy J t x - standardJ n) ⊆
      tsupport (fun x => J x - standardJ n) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hzero := image_eq_zero_of_notMem_tsupport hn
  have hJx : J x = standardJ n := sub_eq_zero.mp hzero
  apply hx
  change interpolateJ (J x) t - standardJ n = 0
  rw [hJx,interpolateJ_standard ht,sub_self]

theorem lineHomotopy_compact {n : ℕ} {J : Phase n → End n}
    (hJc : HasCompactSupport (fun x => J x - standardJ n))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasCompactSupport (fun x => lineHomotopy J t x - standardJ n) :=
  hJc.of_isClosed_subset (isClosed_tsupport _) (lineHomotopy_support J ht)


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_RadialForm
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.normalizedPrimitive_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem linear_asymptotic_norm_tendsto {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    Tendsto (fun z => ‖u z‖) (cocompact ℂ) atTop := by
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, ‖v‖ / 2 < ‖z⁻¹ • u z‖ :=
    (tendsto_order.mp hlim.norm).1 _ (by linarith)
  have hb : (fun z : ℂ => (‖v‖ / 2) * ‖z‖) ≤ᶠ[cocompact ℂ] fun z => ‖u z‖ := by
    filter_upwards [hev,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa using hz0)
    rw [norm_smul,norm_inv,inv_mul_eq_div] at hz
    exact ((lt_div_iff₀ hn).mp hz).le
  exact tendsto_atTop_mono' _ hb
    (Tendsto.const_mul_atTop (by linarith : 0 < ‖v‖ / 2) tendsto_norm_cocompact_atTop)

theorem AffineLineCurve.tendsto_cocompact {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) :
    Tendsto u (cocompact ℂ) (cocompact (Phase n)) := by
  obtain ⟨v,hv,hlim⟩ := hu.2.2.2.2
  rw [←Metric.cobounded_eq_cocompact (α := Phase n),←tendsto_norm_atTop_iff_cobounded]
  exact linear_asymptotic_norm_tendsto hv hlim

theorem AffineLineCurve.isProperMap {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) : IsProperMap u :=
  isProperMap_iff_tendsto_cocompact.mpr ⟨hu.1.continuous,hu.tendsto_cocompact⟩

theorem AffineLineCurve.holomorphic_at_infinity {n : ℕ} {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x - standardJ n)) :
    ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z := by
  filter_upwards [hu.tendsto_cocompact.eventually hJc.compl_mem_cocompact] with z hz
  have hJ : J (u z) = standardJ n :=
    sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun x => J x - standardJ n) hz)
  apply complex_differentiable_of_CR (hu.2.1 z).1
  intro w
  rw [(hu.2.1 z).2,hJ]

theorem infinityGerm_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n)
    {w : ℂ} (hw : w ≠ 0) :
    infinityGerm u v =ᶠ[𝓝 w] fun z => z • u z⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hw] with z hz
  exact ite_eq_right hz

theorem infinityGerm_analyticAt {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 v)) :
    AnalyticAt ℂ (infinityGerm u v) 0 := by
  have hi : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have ht : Tendsto (fun w : ℂ => w • u w⁻¹) (𝓝[≠] 0) (𝓝 v) := by
    simpa only [Function.comp_def,inv_inv] using hlim.comp hi
  have he : infinityGerm u v = Function.update (fun w : ℂ => w • u w⁻¹) 0 v := by
    classical
    funext w
    by_cases hw : w = 0
    · subst w; simp [infinityGerm]
    · simp [infinityGerm,hw]
  have hc : ContinuousAt (infinityGerm u v) 0 := by
    classical
    rw [he,continuousAt_update_same]
    exact ht
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  filter_upwards [hi.eventually hholo,self_mem_nhdsWithin] with w hw hw0
  have hn : w ≠ 0 := hw0
  have hd : DifferentiableAt ℂ (fun z : ℂ => z • u z⁻¹) w :=
    differentiableAt_id.smul (hw.comp w (differentiableAt_id.inv hn))
  exact hd.congr_of_eventuallyEq (infinityGerm_eventuallyEq u v hn)

end HigherDimensionalBallPacking.Rigidity

namespace SymplecticBallPacking.Hamiltonian
open scoped ContDiff Topology
open Set Function Filter MeasureTheory

theorem HasCompactSupport.comp_radiusSq {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z : Plane => g (radiusSq z)) := by
  obtain ⟨B,hB,hbound⟩ := hg.isBounded.exists_pos_norm_le
  apply HasCompactSupport.intro ((isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))).prod (isCompact_Icc : IsCompact (Icc (-(B+1)) (B+1))))
  intro z hz
  by_contra hg0
  have hb := hbound (radiusSq z) (subset_tsupport g hg0)
  have hq : 0 ≤ radiusSq z := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hq] at hb
  apply hz
  dsimp only [radiusSq] at hb
  constructor <;> constructor <;> nlinarith [sq_nonneg z.1,sq_nonneg z.2]

theorem HasCompactSupport.comp_square {F : Type*} [Zero F] {g : ℝ → F}
    (hg : HasCompactSupport g) : HasCompactSupport (fun x : ℝ => g (x^2)) := by
  simpa only [radiusSq,zero_pow (by decide : (2:ℕ)≠0),add_zero] using
    HasCompactSupport.left_slice (HasCompactSupport.comp_radiusSq hg) 0

theorem integral_radial_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : (∫ z : Plane,2*deriv g (radiusSq z))= -2*Real.pi*g 0 := by
  let h : ℝ → ℝ := fun r => g (r^2)
  have hh : ContDiff ℝ ∞ h := hg.comp (contDiff_id.pow 2)
  have hhC : HasCompactSupport h := HasCompactSupport.comp_square hc
  have hd (r : ℝ) : deriv h r=2*r*deriv g (r^2) := by
    have H := (hg.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (r^2)).hasDerivAt.comp r ((hasDerivAt_id r).pow 2)
    change HasDerivAt h _ r at H
    rw [H.deriv]
    simp only [Nat.cast_ofNat,mul_one,id_eq]
    norm_num
    ring
  rw [← integral_comp_polarCoord_symm]
  have he : (fun p : Plane => p.1 • (2*deriv g (radiusSq (polarCoord.symm p))))=
      (fun p : Plane => deriv h p.1 * (1 : ℝ)) := by
    funext p
    rw [radiusSq_polar,hd]
    simp only [smul_eq_mul]
    ring
  rw [he,polarCoord_target,Measure.volume_eq_prod,setIntegral_prod_mul (deriv h) (fun _ : ℝ => (1 : ℝ)),
    HasCompactSupport.integral_Ioi_deriv_eq (hh.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hhC]
  simp only [h,zero_pow (by decide : (2:ℕ)≠0),integral_const,smul_eq_mul,
    Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0≤Real.pi-(-Real.pi))]
  ring

theorem radiusSq_hasFDerivAt (z : Plane) :
    HasFDerivAt radiusSq ((2:ℝ) • planarDot z) z := by
  have H := (((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2).add
    (((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := z)).pow 2)
  change HasFDerivAt radiusSq _ z at H
  apply H.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change (2 • z.1^(2-1))*v.1+(2 • z.2^(2-1))*v.2=2*(z.1*v.1+z.2*v.2)
  norm_num
  ring

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_PlanarResidueCutoff
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SymplecticBallPacking.Hamiltonian
open Set Function MeasureTheory Filter
open scoped ContDiff Topology

theorem planarCurl_contDiff {β : Plane → Plane →L[ℝ] ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (planarCurl β) :=
  (((hβ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).clm_apply contDiff_const).sub
    (((hβ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const).clm_apply contDiff_const)

theorem planarCurl_compact {β : Plane → Plane →L[ℝ] ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (planarCurl β) := by
  exact ((hβ.fderiv_apply (𝕜 := ℝ) (1,0)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (0,1)) rfl).sub
    ((hβ.fderiv_apply (𝕜 := ℝ) (0,1)).comp_left
    (g := fun L : Plane →L[ℝ] ℝ => L (1,0)) rfl)

theorem planarCurl_spatial_smul {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    {z : Plane}
    (hf : DifferentiableAt ℝ f z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => f y • β y) z=cutoffWedge f β z+f z*planarCurl β z := by
  unfold planarCurl cutoffWedge
  have H := hf.hasFDerivAt.smul hβ.hasFDerivAt
  change HasFDerivAt (fun y => f y • β y) _ z at H
  rw [H.fderiv]
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  ring

theorem integral_cutoffWedge {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    (∫ z,cutoffWedge f β z)= -(∫ z,f z*planarCurl β z) := by
  have hp : ContDiff ℝ ∞ (fun z => f z • β z) := hf.smul hβ
  have hpc : HasCompactSupport (fun z => f z • β z) := hc.smul_right
  have hci : Integrable (planarCurl (fun z => f z • β z)) := (planarCurl_contDiff hp).continuous.integrable_of_hasCompactSupport (planarCurl_compact hpc)
  have hgi : Integrable (fun z => f z*planarCurl β z) := (hf.mul (planarCurl_contDiff hβ)).continuous.integrable_of_hasCompactSupport hc.mul_right
  have he : cutoffWedge f β=(fun z => planarCurl (fun y => f y • β y) z-f z*planarCurl β z) := by
    funext z
    rw [planarCurl_spatial_smul (hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z) (hβ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)]
    ring
  rw [he,integral_sub hci hgi,show (∫ z,planarCurl (fun y => f y • β y) z)=0 from compact_planar_stokes hp hpc,zero_sub]

theorem cutoffWedge_integrable {f : Plane → ℝ} {β : Plane → Plane →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hβ : ContDiff ℝ ∞ β) :
    Integrable (cutoffWedge f β) := by
  have h1 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (1,0)) := (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := ((1:ℝ),(0:ℝ))))
  have h2 : ContDiff ℝ ∞ (fun z => fderiv ℝ f z (0,1)) := (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply (contDiff_const (c := ((0:ℝ),(1:ℝ))))
  exact ((h1.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (1,0)).mul_right).sub
    ((h2.mul (hβ.clm_apply contDiff_const)).continuous.integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) (0,1)).mul_right)

end SymplecticBallPacking.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_CurveArea
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.realCurve_zero _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

theorem realCurve_smooth {n : ℕ} {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (realCurve u) := hu.comp Complex.equivRealProdCLM.symm.contDiff

theorem realCurve_fderiv {n : ℕ} {u : ℂ → Phase n} {z : Plane}
    (hu : DifferentiableAt ℝ u (Complex.equivRealProdCLM.symm z)) (v : Plane) :
    fderiv ℝ (realCurve u) z v =
      fderiv ℝ u (Complex.equivRealProdCLM.symm z) (Complex.equivRealProdCLM.symm v) := by
  rw [realCurve, fderiv_comp z hu Complex.equivRealProdCLM.symm.differentiableAt]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.fderiv]

theorem planarPullback_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) :
    ContDiff ℝ ∞ (planarPullback v α) :=
  (hα.comp hv).clm_comp (hv.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

theorem oneForm_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : E → E →L[ℝ] ℝ} (hα : ContDiff ℝ ∞ α) : ContDiff ℝ ∞ (oneForm α) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp hα

theorem planarCurl_eq_extDeriv {α : Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl α z = extDeriv (oneForm α) z ![(1,0),(0,1)] := by
  rw [extDeriv_apply ((oneForm_smooth hα).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change planarCurl α z =
    fderiv ℝ (fun y => α y (0,1)) z (1,0) - fderiv ℝ (fun y => α y (1,0)) z (0,1)
  rw [fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _),
    fderiv_clm_apply (hα.differentiable (by simp) z) (differentiableAt_const _)]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    fderiv_const_apply, zero_apply, map_zero, zero_add]
  rfl

theorem planarPullback_curl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : Plane → E} {α : E → E →L[ℝ] ℝ}
    (hv : ContDiff ℝ ∞ v) (hα : ContDiff ℝ ∞ α) (z : Plane) :
    planarCurl (planarPullback v α) z =
      extDeriv (oneForm α) (v z) ![fderiv ℝ v z (1,0), fderiv ℝ v z (0,1)] := by
  rw [planarCurl_eq_extDeriv (planarPullback_smooth hv hα)]
  have he : oneForm (planarPullback v α) = fun y =>
      (oneForm α (v y)).compContinuousLinearMap (fderiv ℝ v y) := by
    funext y
    ext w
    rfl
  rw [he,extDeriv_pullback ((oneForm_smooth hα).differentiable (by simp) (v z))
    hv.contDiffAt (by
      norm_num [minSmoothness] <;> first | done | exact WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  ext i
  fin_cases i <;> rfl


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_Correction
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
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
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem oneForm_extDeriv_apply {α : E → E →L[ℝ] ℝ} {x : E}
    (hα : DifferentiableAt ℝ α x) (v w : E) :
    extDeriv (oneForm α) x ![v,w] = fderiv ℝ α x v w - fderiv ℝ α x w v := by
  have hω : DifferentiableAt ℝ (oneForm α) x :=
    (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
      (0 : Fin 1)).toContinuousLinearEquiv.differentiableAt.comp x hα
  rw [extDeriv_apply hω,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_one, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    pow_one, neg_smul, zero_add]
  change fderiv ℝ (fun y => α y w) x v - fderiv ℝ (fun y => α y v) x w = _
  rw [fderiv_clm_apply hα (differentiableAt_const w),
    fderiv_clm_apply hα (differentiableAt_const v)]
  simp


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem outerProfile_smooth (A : ℝ) : ContDiff ℝ ∞ (outerProfile A) :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const A)))

theorem outerProfile_compact {A : ℝ} (hA : 0 < A) : HasCompactSupport (outerProfile A) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-2:ℝ)) (b := 2*A))
  intro t ht
  have ht' : t < -2 ∨ 2*A < t := by simpa only [mem_Icc,not_and_or,not_le] using ht
  rcases ht' with ht' | ht'
  · simp only [outerProfile,Real.smoothTransition.zero_of_nonpos (by linarith : t+2 ≤ 0),zero_mul]
  · have h : 1 ≤ (t-A)/A := (le_div_iff₀ hA).mpr (by linarith)
    simp only [outerProfile,Real.smoothTransition.one_of_one_le h,sub_self,mul_zero]

theorem outerProfile_nonneg (A t : ℝ) : 0 ≤ outerProfile A t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))

theorem outerProfile_zero_value {A : ℝ} (hA : 0 < A) : outerProfile A 0 = 1 := by
  have h : (0-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le
  simp only [outerProfile,zero_add,Real.smoothTransition.one_of_one_le (by norm_num : (1:ℝ)≤2),
    Real.smoothTransition.zero_of_nonpos h,sub_zero,mul_one]

theorem outerProfile_deriv {A t : ℝ} (ht : 0 ≤ t) :
    deriv (outerProfile A) t = -(deriv Real.smoothTransition ((t-A)/A) / A) := by
  have he : outerProfile A =ᶠ[𝓝 t] fun s => 1 - Real.smoothTransition ((s-A)/A) := by
    filter_upwards [isOpen_Ioi.mem_nhds (by linarith : (-1:ℝ) < t)] with s hs
    have hs' : -1 < s := hs
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ s + 2),one_mul]
  rw [he.deriv_eq]
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hh := (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) ((t-A)/A)).hasDerivAt.comp t
    (((hasDerivAt_id t).sub_const A).div_const A)
  have hd := hh.const_sub 1
  change HasDerivAt (fun s => 1 - Real.smoothTransition ((s-A)/A)) _ t at hd
  rw [hd.deriv]
  simp only [div_eq_mul_inv,one_mul]

theorem outerProfile_deriv_nonpos {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) :
    deriv (outerProfile A) t ≤ 0 := by
  rw [outerProfile_deriv ht]
  exact neg_nonpos.mpr (div_nonneg Real.smoothTransition.monotone.deriv_nonneg hA.le)

theorem outerProfile_deriv_zero_before {A t : ℝ} (hA : 0 < A) (ht : 0 ≤ t) (htA : t < A) :
    deriv (outerProfile A) t = 0 := by
  have he : outerProfile A =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo (-1:ℝ) A from ⟨by linarith,htA⟩)] with s hs
    have hn : (s-A)/A ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hA.le
    simp only [outerProfile,Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s + 2),
      Real.smoothTransition.zero_of_nonpos hn,sub_zero,mul_one]
  rw [he.deriv_eq,deriv_const]

theorem cutoffWedge_radial_rotation {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (β : Plane → Plane →L[ℝ] ℝ) (z : Plane) :
    cutoffWedge (fun y => g (radiusSq y)) β z =
      2 * deriv g (radiusSq z) * β z (planeRotation z) := by
  have hh := (hg.differentiable (by simp) (radiusSq z)).hasDerivAt.comp_hasFDerivAt z
    (radiusSq_hasFDerivAt z)
  change HasFDerivAt (fun y => g (radiusSq y)) _ z at hh
  have he : planeRotation z = (-z.2) • ((1,0) : Plane) + z.1 • (0,1) := by
    ext <;> simp [planeRotation]
  unfold cutoffWedge
  rw [hh.fderiv, he,map_add,map_smul,map_smul]
  simp only [smul_apply,smul_eq_mul,planarDot_apply]
  simp only [mul_one,mul_zero,add_zero,zero_add]
  ring



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Rigidity_AngularPoles
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.SymplecticBallPacking.Hamiltonian.coordinateForm_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem equivRealProd_rotation (z : Plane) :
    Complex.equivRealProdCLM.symm (planeRotation z) =
      Complex.I * Complex.equivRealProdCLM.symm z := by
  apply Complex.ext <;> simp [planeRotation,Complex.equivRealProdCLM_symm_apply]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_AffineCorrectionInfinity
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleFrame_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.compatibleInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedDX_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedFrameJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedInverseJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedQ_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.completedStructureJet_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficientHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveMarkCoefficient_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrderHolder_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.curveZeroOrder_apply _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.smoothMarkedPrincipal_value _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open SymplecticBallPacking.Hamiltonian (Plane)
namespace HigherDimensionalBallPacking.Rigidity
variable {n : ℕ}

lemma analyticAt_dslope_zero {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (dslope h 0) 0 := by
  obtain ⟨P,hP⟩ := hh
  exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩

lemma infinityGerm_affine_reconstruction (u : ℂ → Phase n) (a : Phase n) {z : ℂ} (hz : z≠0) :
    u z=z • a+dslope (infinityGerm u a) 0 z⁻¹ := by
  rw [dslope_of_ne _ (inv_ne_zero hz),slope,sub_zero]
  simp only [infinityGerm,inv_ne_zero hz,ite_false, if_false,inv_inv,ite_true, if_true,vsub_eq_sub]
  rw [smul_sub,smul_smul,mul_inv_cancel₀ hz,one_smul]
  abel

lemma analytic_inverse_angular_fderiv_limit {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0) :
    Tendsto (fun z : ℂ => fderiv ℝ (fun w : ℂ => h w⁻¹) z (Complex.I*z))
      (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hc : ContDiffAt ℝ ∞ h 0 := hh.contDiffAt.restrict_scalars ℝ
  have hdh : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹) (cocompact ℂ) (𝓝 (fderiv ℝ h 0)) :=
    (hc.fderiv_right (m := 0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hvec : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdh.prodMk_nhds harg)
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  apply hvec.congr'
  filter_upwards [hi.eventually hd,(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz hz0
  have hid := (hasDerivAt_inv hz0).hasFDerivAt.restrictScalars ℝ
  have hder := hz.hasFDerivAt.comp z hid
  change HasFDerivAt (fun w : ℂ => h w⁻¹) _ z at hder
  rw [hder.fderiv]
  change fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)=
    fderiv ℝ h z⁻¹ ((Complex.I*z) • (-(z^2)⁻¹))
  rw [smul_eq_mul]
  congr 1
  field_simp

lemma affineCorrection_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    ContDiff ℝ ∞ (affineCorrection u a) := hu.sub (contDiff_id.smul contDiff_const)

lemma affineCorrection_locally_inverse {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) {z : ℂ} (hz : z≠0) :
    affineCorrection u a =ᶠ[𝓝 z] fun w : ℂ => h w⁻¹ := by
  filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
  rw [affineCorrection,he w hw]
  abel

lemma affineCorrection_limit {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (affineCorrection u a) (cocompact ℂ) (𝓝 (h 0)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  apply (hh.continuousAt.tendsto.comp hi).congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  exact ((affineCorrection_locally_inverse he hz).self_of_nhds).symm

lemma affineCorrection_angular_fderiv_limit {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : ℂ => fderiv ℝ (affineCorrection u a) z (Complex.I*z))
      (cocompact ℂ) (𝓝 0) := by
  apply (analytic_inverse_angular_fderiv_limit hh).congr'
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  rw [(affineCorrection_locally_inverse he hz).fderiv_eq]

lemma affineCorrection_primitive_flux_zero {u : ℂ → Phase n} {a : Phase n} {h : ℂ → Phase n}
    (hh : AnalyticAt ℂ h 0) (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : ℂ => stdOmega n (affineCorrection u a z)
      (fderiv ℝ (affineCorrection u a) z (Complex.I*z))) (cocompact ℂ) (𝓝 0) := by
  have hv := affineCorrection_limit hh he
  have hd := affineCorrection_angular_fderiv_limit hh he
  have ho : Tendsto (fun z => stdOmega n (affineCorrection u a z))
      (cocompact ℂ) (𝓝 (stdOmega n (h 0))) := (stdOmega n).continuous.continuousAt.tendsto.comp hv
  simpa only [Function.comp_def,map_zero] using
    (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (ho.prodMk_nhds hd)

end HigherDimensionalBallPacking.Rigidity

end
noncomputable section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity

lemma outerProfile_one_before {A t : ℝ} (ht : 0≤t) (htA : t≤A) (hA : 0<A) :
    outerProfile A t=1 := by
  have h1 : 1≤t+2 := by linarith
  have h2 : (t-A)/A≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htA) hA.le
  simp only [outerProfile,Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.zero_of_nonpos h2,sub_zero,mul_one]

lemma radiusSq_pos_bound_of_compact {K : Set Plane} (hK : IsCompact K) :
    ∃ A : ℝ, 0<A ∧ ∀ z∈K, radiusSq z<A := by
  obtain ⟨B,hB,hb⟩ := (hK.image radiusSq_smooth.continuous).isBounded.exists_pos_norm_le
  refine ⟨B+1,by linarith,?_⟩
  intro z hz
  have hh := hb (radiusSq z) ⟨z,hz,rfl⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (radiusSq_nonneg z)] at hh
  linarith

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_TranslationContinuity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter

variable {n : ℕ}

local instance gcInst1_r67a22c_1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gcInst2_r67a22c_1 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gcInst3_r67a22c_1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gcInst4_r67a22c_1 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gcInst5_r67a22c_1 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gcInst6_r67a22c_1 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
local instance gcInst7_r67a22c_1 (K : Set ℂ) : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance gcInst8_r67a22c_1 (K : Set ℂ) : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance gcInst9_r67a22c_1 (K : Set ℂ) : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance gcInst10_r67a22c_1 (K : Set ℂ) : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
lemma geometricResidual_compact {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (geometricResidual u) := by
  apply HasCompactSupport.of_support_subset_isCompact (hu.isProperMap.isCompact_preimage hJc)
  intro z hz
  by_contra hn
  have hstd : J (u z)=standardJ n := sub_eq_zero.mp
    (image_eq_zero_of_notMem_tsupport (f := fun x => J x-standardJ n) hn)
  have hcr := (hu.2.1 z).2 1
  simp only [mul_one,hstd] at hcr
  apply hz
  exact sub_eq_zero.mpr hcr

end HigherDimensionalBallPacking.Rigidity.HolderCompletion
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_ResidualEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.reInst2
lemma lineResidualEnergy_continuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    Continuous (lineResidualEnergy u) := by
  have h := (geometricResidual_smooth hu).continuous.comp Complex.equivRealProdCLM.symm.continuous
  exact ((stdDot n).continuous.comp h).clm_apply h

attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.reInst1
lemma lineResidualEnergy_compact {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u) (hJc : HasCompactSupport (fun x => J x-standardJ n)) :
    HasCompactSupport (lineResidualEnergy u) := by
  have h := (geometricResidual_compact hu hJc).comp_left
    (g := fun v : Phase n => stdDot n v v) (by simp only [map_zero])
  exact h.comp_isClosedEmbedding Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

lemma sourceRadialCutoff_smooth (A : ℝ) : ContDiff ℝ ∞ (sourceRadialCutoff A) :=
  (outerProfile_smooth A).comp radiusSq_smooth

lemma sourceRadialCutoff_compact {A : ℝ} (hA : 0<A) : HasCompactSupport (sourceRadialCutoff A) :=
  HasCompactSupport.comp_radiusSq (outerProfile_compact hA)

lemma sourceRadialCutoff_nonneg (A : ℝ) (z : Plane) : 0 ≤ sourceRadialCutoff A z :=
  outerProfile_nonneg A _

lemma sourceRadialCutoff_le_one (A : ℝ) (z : Plane) : sourceRadialCutoff A z≤1 := by
  have h : 1 ≤ radiusSq z+2 := by linarith [radiusSq_nonneg z]
  simp only [sourceRadialCutoff,outerProfile,Real.smoothTransition.one_of_one_le h,one_mul]
  linarith [Real.smoothTransition.nonneg ((radiusSq z-A)/A)]

lemma sourceRadialCutoff_eventually_one_on_compact {K : Set Plane} (hK : IsCompact K) :
    ∀ᶠ A : ℝ in atTop, ∀ z∈K, sourceRadialCutoff A z=1 := by
  obtain ⟨B,hB,hbound⟩ := radiusSq_pos_bound_of_compact hK
  filter_upwards [eventually_ge_atTop B] with A hA z hz
  exact outerProfile_one_before (radiusSq_nonneg z) ((hbound z hz).le.trans hA) (hB.trans_le hA)

lemma sourceRadialCutoff_tendsto (z : Plane) :
    Tendsto (fun A : ℝ => sourceRadialCutoff A z) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [sourceRadialCutoff_eventually_one_on_compact (isCompact_singleton (x := z))] with A hA
  exact (hA z (mem_singleton z)).symm

lemma smooth_cutoff_integrable_mul {A : ℝ} (hA : 0<A) {e : Plane → ℝ} (he : Continuous e) :
    Integrable (fun z => sourceRadialCutoff A z*e z) :=
  ((sourceRadialCutoff_smooth A).continuous.mul he).integrable_of_hasCompactSupport
    ((sourceRadialCutoff_compact hA).mul_right)

lemma radial_curl_integral_between {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {A a b : ℝ} (hA : 0<A)
    (hb : ∀ z : Plane, A ≤ radiusSq z → a≤β z (planeRotation z) ∧ β z (planeRotation z)≤b) :
    2*Real.pi*a≤(∫ z, sourceRadialCutoff A z*planarCurl β z) ∧
      (∫ z, sourceRadialCutoff A z*planarCurl β z)≤2*Real.pi*b := by
  let g := outerProfile A
  have hg : ContDiff ℝ ∞ g := outerProfile_smooth A
  have hc : HasCompactSupport g := outerProfile_compact hA
  have hpoint (z : Plane) :
      2*deriv g (radiusSq z)*b ≤ cutoffWedge (sourceRadialCutoff A) β z ∧
      cutoffWedge (sourceRadialCutoff A) β z≤2*deriv g (radiusSq z)*a := by
    rw [show sourceRadialCutoff A=fun y => g (radiusSq y) from rfl,cutoffWedge_radial_rotation hg]
    by_cases hd : deriv g (radiusSq z)=0
    · simp only [hd,mul_zero,zero_mul,le_refl,and_self]
    have hzA : A ≤ radiusSq z := by
      by_contra! hz
      exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) hz)
    have hneg : 2*deriv g (radiusSq z)≤0 :=
      mul_nonpos_of_nonneg_of_nonpos (by norm_num) (outerProfile_deriv_nonpos hA (radiusSq_nonneg z))
    exact ⟨mul_le_mul_of_nonpos_left (hb z hzA).2 hneg,
      mul_le_mul_of_nonpos_left (hb z hzA).1 hneg⟩
  have hdi (c : ℝ) : Integrable (fun z : Plane => 2*deriv g (radiusSq z)*c) :=
    ((((hg.continuous_deriv (by simp)).comp radiusSq_smooth.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.comp_radiusSq hc.deriv)).const_mul 2).mul_const c
  have hwi := cutoffWedge_integrable (sourceRadialCutoff_smooth A) (sourceRadialCutoff_compact hA) hβ
  have hlow := integral_mono (hdi b) hwi (fun z => (hpoint z).1)
  have hupp := integral_mono hwi (hdi a) (fun z => (hpoint z).2)
  have hg0 : g 0=1 := outerProfile_zero_value hA
  rw [integral_mul_const,integral_radial_derivative hg hc,hg0,mul_one] at hlow hupp
  rw [integral_cutoffWedge (sourceRadialCutoff_smooth A) (sourceRadialCutoff_compact hA) hβ] at hlow hupp
  constructor <;> nlinarith only [hlow,hupp]

lemma radial_curl_integral_tendsto {β : Plane → Plane →L[ℝ] ℝ}
    (hβ : ContDiff ℝ ∞ β) {k : ℝ}
    (hlim : Tendsto (fun z => β z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z*planarCurl β z)
      atTop (𝓝 (2*Real.pi*k)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hp : 0<2*Real.pi := by positivity
  let δ := ε/(4*Real.pi)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hev : ∀ᶠ z in cocompact Plane,
      k-δ<β z (planeRotation z) ∧ β z (planeRotation z)<k+δ :=
    hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨K,hK,hKb⟩ := mem_cocompact.mp hev
  obtain ⟨B,hB,hbound⟩ := radiusSq_pos_bound_of_compact hK
  refine ⟨B,?_⟩
  intro A hA
  have hAp : 0<A := hB.trans_le hA
  have hh : ∀ z : Plane, A ≤ radiusSq z →
      k-δ≤β z (planeRotation z) ∧ β z (planeRotation z)≤k+δ := by
    intro z hz
    have hzK : z∉K := by
      intro hzK
      exact (not_lt_of_ge (hA.trans hz)) (hbound z hzK)
    exact ⟨(hKb hzK).1.le,(hKb hzK).2.le⟩
  have hb := radial_curl_integral_between hβ hAp hh
  rw [Real.dist_eq]
  apply abs_lt.mpr
  have he : 2*Real.pi*δ=ε/2 := by dsimp [δ]; field_simp <;> ring_nf
  constructor <;> nlinarith only [hb.1,hb.2,he,hε]

lemma compact_integral_cutoff_eventually {e : Plane → ℝ} (he : HasCompactSupport e) :
    ∀ᶠ A : ℝ in atTop, (fun z => sourceRadialCutoff A z*e z)=e := by
  filter_upwards [sourceRadialCutoff_eventually_one_on_compact he] with A hA
  funext z
  by_cases hz : z∈tsupport e
  · rw [hA z hz,one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]



lemma integrable_of_radial_exhaustion_limit {e : Plane → ℝ}
    (he : Continuous e) (hn : ∀ z, 0 ≤ e z) {L : ℝ}
    (hlim : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z * e z) atTop (𝓝 L)) :
    Integrable e ∧ (∫ z, e z)=L := by
  let a : ℕ → ℝ := fun i => (i:ℝ)+1
  have ha : Tendsto a atTop atTop := tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
  have hap (i : ℕ) : 0<a i := by dsimp [a] <;> positivity
  let f : ℕ → Plane → ℝ := fun i z => sourceRadialCutoff (a i) z * e z
  have hfn (i : ℕ) (z : Plane) : 0≤f i z := mul_nonneg (sourceRadialCutoff_nonneg _ _) (hn _)
  have hfc (i : ℕ) : Continuous (f i) := (sourceRadialCutoff_smooth _).continuous.mul he
  have hfi (i : ℕ) : Integrable (f i) := smooth_cutoff_integrable_mul (hap i) he
  have hfl (z : Plane) : Tendsto (fun i => f i z) atTop (𝓝 (e z)) := by
    simpa only [one_mul, f, Function.comp_def] using ((sourceRadialCutoff_tendsto z).comp ha).mul_const (e z)
  have hlim' : Tendsto (fun i => ∫ z, f i z) atTop (𝓝 L) := hlim.comp ha
  have hfat := lintegral_liminf_le' (u := (atTop : Filter ℕ)) (μ := (volume : Measure Plane))
    (f := fun i z => ENNReal.ofReal (f i z)) (fun i => (hfc i).measurable.ennreal_ofReal.aemeasurable)
  have hpoint (z : Plane) : liminf (fun i => ENNReal.ofReal (f i z)) atTop=ENNReal.ofReal (e z) :=
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hfl z)).liminf_eq
  simp only [hpoint] at hfat
  have hil : Tendsto (fun i => ∫⁻ z, ENNReal.ofReal (f i z)) atTop (𝓝 (ENNReal.ofReal L)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim'
    simpa only [Function.comp_def, ofReal_integral_eq_lintegral_ofReal (hfi _) (ae_of_all _ (hfn _))] using h
  rw [hil.liminf_eq] at hfat
  have hei : Integrable e := (lintegral_ofReal_ne_top_iff_integrable he.aestronglyMeasurable
    (ae_of_all _ hn)).mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfat)
  refine ⟨hei,?_⟩
  have hdc := tendsto_integral_filter_of_dominated_convergence (F := fun A z => sourceRadialCutoff A z * e z) e
    (Eventually.of_forall fun A : ℝ =>
      ((sourceRadialCutoff_smooth A).continuous.mul he).aestronglyMeasurable)
    (Eventually.of_forall fun A : ℝ => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRadialCutoff_nonneg _ _) (hn z))]
      exact mul_le_of_le_one_left (hn z) (sourceRadialCutoff_le_one A z)) hei
    (ae_of_all _ fun z => by simpa only [one_mul] using (sourceRadialCutoff_tendsto z).mul_const (e z))
  exact tendsto_nhds_unique hdc hlim


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
open HolderCompletion
variable {n : ℕ}

lemma dirichletEnergy_nonneg (v : ℂ → Phase n) (z : Plane) : 0≤dirichletEnergy v z :=
  add_nonneg (stdDot_nonneg _) (stdDot_nonneg _)

lemma dirichletEnergy_continuous {v : ℂ → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (dirichletEnergy v) := by
  have hd := ((realCurve_smooth hv).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous
  have hx := hd.clm_apply (continuous_const (y := ((1,0):Plane)))
  have hy := hd.clm_apply (continuous_const (y := ((0,1):Plane)))
  exact (((stdDot n).continuous.comp hx).clm_apply hx).add (((stdDot n).continuous.comp hy).clm_apply hy)

lemma residual_energy_algebra (x y : Phase n) :
    stdDot n x x+stdDot n y y-stdDot n (y-standardJ n x) (y-standardJ n x)=2*stdOmega n x y := by
  simp only [map_sub,sub_apply,stdDot_J_right,stdOmega_apply]
  rw [stdDot_symm (standardJ n x) y,stdDot_J_right,standardForm_skew (standardJ n x) x,standardForm_J_right,
    standardForm_skew y x]
  ring

lemma lineResidualEnergy_real {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    lineResidualEnergy u z=stdDot n
      (fderiv ℝ (realCurve u) z (0,1)-standardJ n (fderiv ℝ (realCurve u) z (1,0)))
      (fderiv ℝ (realCurve u) z (0,1)-standardJ n (fderiv ℝ (realCurve u) z (1,0))) := by
  simp only [realCurve_fderiv (hu.differentiable (by simp) _)]
  rfl

lemma standard_primitive_curl {v : ℂ → Phase n} (hv : ContDiff ℝ ∞ v) (z : Plane) :
    planarCurl (planarPullback (realCurve v) (stdOmega n)) z=
      dirichletEnergy v z-lineResidualEnergy v z := by
  rw [planarPullback_curl (realCurve_smooth hv) (stdOmega n).contDiff,
    oneForm_extDeriv_apply (stdOmega n).differentiableAt,(stdOmega n).fderiv]
  rw [lineResidualEnergy_real hv]
  change stdOmega n _ _-stdOmega n _ _ = _
  rw [dirichletEnergy,residual_energy_algebra,stdOmega_apply,stdOmega_apply,standardForm_skew]
  ring

lemma affineCorrection_residual {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    geometricResidual (affineCorrection u a)=geometricResidual u := by
  funext z
  have hlin := (hasFDerivAt_id (𝕜 := ℝ) z).smul_const a
  have hd := (hu.differentiable (by simp) z).hasFDerivAt.sub hlin
  change HasFDerivAt (affineCorrection u a) _ z at hd
  rw [geometricResidual,hd.fderiv]
  simp only [sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,smul_sub,one_smul,geometricResidual]
  abel

lemma affineCorrection_residual_energy {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (a : Phase n) :
    lineResidualEnergy (affineCorrection u a)=lineResidualEnergy u := by
  funext z
  simp only [lineResidualEnergy,affineCorrection_residual hu]

lemma affineCorrection_real_flux_zero {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {a : Phase n} {h : ℂ → Phase n} (hh : AnalyticAt ℂ h 0)
    (he : ∀ z : ℂ, z≠0 → u z=z • a+h z⁻¹) :
    Tendsto (fun z : Plane => planarPullback (realCurve (affineCorrection u a)) (stdOmega n) z
      (planeRotation z)) (cocompact Plane) (𝓝 0) := by
  have ht := (affineCorrection_primitive_flux_zero hh he).comp
    (le_of_eq Complex.equivRealProdCLM.symm.toHomeomorph.map_cocompact)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rw [planarPullback]
  simp only [ContinuousLinearMap.comp_apply]
  rw [realCurve_fderiv ((affineCorrection_smooth hu a).differentiable (by simp) _),equivRealProd_rotation]
  rfl


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma stdDot_sub_self (x y : Phase n) :
    stdDot n (x-y) (x-y)=stdDot n x x-2*stdDot n x y+stdDot n y y := by
  simp only [map_sub,sub_apply]
  rw [stdDot_symm y x]
  ring

lemma interval_integral_stdDot_const {f : ℝ → Phase n} (hf : Continuous f) (a b : ℝ) (v : Phase n) :
    (∫ t in a..b, stdDot n (f t) v)=stdDot n (∫ t in a..b, f t) v :=
  ((stdDot n).flip v).intervalIntegral_comp_comm (hf.intervalIntegrable a b)

lemma interval_stdDot_variance {f : ℝ → Phase n} (hf : Continuous f) (a b : ℝ) (v : Phase n) :
    (∫ t in a..b, stdDot n (f t-v) (f t-v))=
      (∫ t in a..b, stdDot n (f t) (f t))-2*stdDot n (∫ t in a..b, f t) v+
        (b-a)*stdDot n v v := by
  have he : Continuous (fun t => stdDot n (f t) (f t)) := ((stdDot n).continuous.comp hf).clm_apply hf
  have hv : Continuous (fun t => 2*stdDot n (f t) v) := continuous_const.mul
    (((stdDot n).continuous.comp hf).clm_apply continuous_const)
  simp_rw [stdDot_sub_self]
  have hei : IntervalIntegrable (fun t => stdDot n (f t) (f t)-2*stdDot n (f t) v) volume a b :=
    (he.sub hv).intervalIntegrable a b
  rw [intervalIntegral.integral_add hei intervalIntegrable_const,
    intervalIntegral.integral_sub (he.intervalIntegrable a b) (hv.intervalIntegrable a b),
    intervalIntegral.integral_const_mul,interval_integral_stdDot_const hf,
    intervalIntegral.integral_const,smul_eq_mul]

lemma interval_stdDot_integral_sq_le {f : ℝ → Phase n} (hf : Continuous f) {a b : ℝ} (hab : a≤b) :
    stdDot n (∫ t in a..b, f t) (∫ t in a..b, f t)≤(b-a)*(∫ t in a..b, stdDot n (f t) (f t)) := by
  rcases eq_or_lt_of_le hab with heq | hab'
  · subst b
    simp only [intervalIntegral.integral_same,sub_self,zero_mul,map_zero,le_refl]
  have hL : 0<b-a := sub_pos.mpr hab'
  let v : Phase n := (b-a)⁻¹ • (∫ t in a..b, f t)
  have hv := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab (fun t => stdDot_nonneg (f t-v))
  rw [interval_stdDot_variance hf] at hv
  have hm := mul_nonneg hL.le hv
  have hid : (b-a)*((∫ t in a..b, stdDot n (f t) (f t))-
      2*stdDot n (∫ t in a..b, f t) v+(b-a)*stdDot n v v)=
      (b-a)*(∫ t in a..b, stdDot n (f t) (f t))-
        stdDot n (∫ t in a..b, f t) (∫ t in a..b, f t) := by
    dsimp only [v]
    simp only [map_smul,smul_apply,smul_eq_mul]
    field_simp
    ring
  rw [hid] at hm
  linarith

lemma curve_chord_energy_le {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v) {a b t : ℝ}
    (hat : a≤t) (htb : t≤b) :
    stdDot n (v t-v a) (v t-v a)≤(b-a)*(∫ s in a..b, stdDot n (deriv v s) (deriv v s)) := by
  have hd : Continuous (deriv v) := hv.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hf : (∫ s in a..t, deriv v s)=v t-v a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => (hv.differentiable (by simp) s).hasDerivAt)
      (hd.intervalIntegrable a t)
  have hj := interval_stdDot_integral_sq_le hd hat
  rw [hf] at hj
  have hec : Continuous (fun s => stdDot n (deriv v s) (deriv v s)) :=
    ((stdDot n).continuous.comp hd).clm_apply hd
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hec.intervalIntegrable a t)
    (hec.intervalIntegrable t b)
  have h1 := intervalIntegral.integral_nonneg_of_forall (μ := volume) hat (fun s => stdDot_nonneg (deriv v s))
  have h2 := intervalIntegral.integral_nonneg_of_forall (μ := volume) htb (fun s => stdDot_nonneg (deriv v s))
  nlinarith



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Energy_CircularEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.squareMeasure_finite _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.HigherDimensionalBallPacking.Rigidity.HolderCompletion.frozenTargetCoefficient_zero _root_.OAI.HigherDimensionalBallPacking.Rigidity.geometricHolder_value _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma centeredCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) :
    ContDiff ℝ ∞ (centeredCurve u c) := hu.comp (contDiff_id.add contDiff_const)

lemma realCurve_centered (u : ℂ → Phase n) (c : ℂ) :
    realCurve (centeredCurve u c)=fun z => realCurve u (z+Complex.equivRealProdCLM c) := by
  funext z
  simp only [realCurve,centeredCurve,Function.comp_def,map_add,ContinuousLinearEquiv.symm_apply_apply]

lemma centeredCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    fderiv ℝ (realCurve (centeredCurve u c)) z=
      fderiv ℝ (realCurve u) (z+Complex.equivRealProdCLM c) := by
  rw [realCurve_centered]
  have hh := ((realCurve_smooth hu).differentiable (by simp) (z+Complex.equivRealProdCLM c)).hasFDerivAt.comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).add_const (Complex.equivRealProdCLM c))
  change HasFDerivAt (fun z => realCurve u (z+Complex.equivRealProdCLM c)) _ z at hh
  simpa only [ContinuousLinearMap.comp_id] using hh.fderiv

lemma dirichletEnergy_centered {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    dirichletEnergy (centeredCurve u c) z=dirichletEnergy u (z+Complex.equivRealProdCLM c) := by
  simp only [dirichletEnergy,centeredCurve_fderiv hu]

lemma stdDot_add_self_le (v w : Phase n) :
    stdDot n (v+w) (v+w)≤2*stdDot n v v+2*stdDot n w w := by
  have hh := stdDot_nonneg (v-w)
  rw [stdDot_sub_self] at hh
  simp only [map_add,add_apply]
  rw [stdDot_symm w v]
  linarith


theorem AffineLineCurve.affine_correction_energy_of_slope {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) {a : Phase n}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a)) :
    Integrable (dirichletEnergy (affineCorrection u a)) ∧
      (∫ z, dirichletEnergy (affineCorrection u a) z)=∫ z, lineResidualEnergy u z := by
  have hh := analyticAt_dslope_zero (infinityGerm_analyticAt (hu.holomorphic_at_infinity hJc) ha)
  have he := fun z hz => infinityGerm_affine_reconstruction u a (z := z) hz
  have hv := affineCorrection_smooth hu.1 a
  have hβ := planarPullback_smooth (realCurve_smooth hv) (stdOmega n).contDiff
  have hlim := radial_curl_integral_tendsto hβ (affineCorrection_real_flux_zero hu.1 hh he)
  simp only [mul_zero] at hlim
  have hfl : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z * lineResidualEnergy u z)
      atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [compact_integral_cutoff_eventually (lineResidualEnergy_compact hu hJc)] with A hA
    rw [hA]
  have helim : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z *
      dirichletEnergy (affineCorrection u a) z) atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    have hl := hlim.add hfl
    simp only [zero_add] at hl
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
    rw [←integral_add
      (smooth_cutoff_integrable_mul hA ((planarCurl_contDiff hβ).continuous))
      (smooth_cutoff_integrable_mul hA (lineResidualEnergy_continuous hu.1))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [standard_primitive_curl hv,affineCorrection_residual_energy hu.1]
    ring
  exact integrable_of_radial_exhaustion_limit (dirichletEnergy_continuous hv)
    (dirichletEnergy_nonneg _) helim



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_MeasureEnergy
attribute [-instance] _root_.OAI.HigherDimensionalBallPacking.Rigidity.translatedSquare_finite _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

lemma integral_stdDot_variance {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (v : Phase n) :
    (∫ x, stdDot n (f x-v) (f x-v) ∂μ)=
      (∫ x, stdDot n (f x) (f x) ∂μ)-2*stdDot n (∫ x,f x ∂μ) v+
        μ.real univ*stdDot n v v := by
  have hi : Integrable (fun x => 2*stdDot n (f x) v) μ :=
    (((stdDot n).flip v).integrable_comp hf).const_mul 2
  have hsub : Integrable (fun x => stdDot n (f x) (f x)-2*stdDot n (f x) v) μ := he.sub hi
  have hint : (∫ x,stdDot n (f x) v ∂μ)=stdDot n (∫ x,f x ∂μ) v :=
    ((stdDot n).flip v).integral_comp_comm hf
  simp_rw [stdDot_sub_self]
  rw [integral_add hsub (integrable_const _),integral_sub he hi,integral_const_mul,
    hint,integral_const,smul_eq_mul]

lemma stdDot_integral_sq_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) :
    stdDot n (∫ x,f x ∂μ) (∫ x,f x ∂μ)≤μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ) := by
  let v : Phase n := (μ.real univ)⁻¹ • (∫ x,f x ∂μ)
  have hn : 0≤(∫ x,stdDot n (f x-v) (f x-v) ∂μ) :=
    integral_nonneg (fun x => stdDot_nonneg (f x-v))
  rw [integral_stdDot_variance hf he] at hn
  have hm := mul_nonneg hμ.le hn
  have hid : μ.real univ*((∫ x,stdDot n (f x) (f x) ∂μ)-
      2*stdDot n (∫ x,f x ∂μ) v+μ.real univ*stdDot n v v)=
      μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ)-stdDot n (∫ x,f x ∂μ) (∫ x,f x ∂μ) := by
    dsimp only [v]
    simp only [map_smul,smul_apply,smul_eq_mul]
    field_simp
    ring
  rw [hid] at hm
  linarith

lemma stdDot_average_sq_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) :
    stdDot n ((μ.real univ)⁻¹ • (∫ x,f x ∂μ)) ((μ.real univ)⁻¹ • (∫ x,f x ∂μ))≤
      (μ.real univ)⁻¹*(∫ x,stdDot n (f x) (f x) ∂μ) := by
  have hh := mul_le_mul_of_nonneg_left (stdDot_integral_sq_le hf he hμ) (sq_nonneg ((μ.real univ)⁻¹))
  simp only [map_smul,smul_apply,smul_eq_mul]
  have hid : ((μ.real univ)⁻¹)^2*(μ.real univ*(∫ x,stdDot n (f x) (f x) ∂μ))=
      (μ.real univ)⁻¹*(∫ x,stdDot n (f x) (f x) ∂μ) := by field_simp
  rw [hid] at hh
  nlinarith only [hh]

lemma norm_sq_le_stdDot (v : Phase n) : ‖v‖^2≤ stdDot n v v := by
  have hroot : ‖v‖≤Real.sqrt (stdDot n v v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (stdDot_nonneg v)).mpr
    have hle : (v i).re*(v i).re+(v i).im*(v i).im≤ stdDot n v v := by
      rw [stdDot_apply]
      exact Finset.single_le_sum (f := fun j : Fin n => (v j).re*(v j).re+(v j).im*(v j).im)
        (fun j _ => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (Finset.mem_univ i)
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    exact hle
  nlinarith [Real.sq_sqrt (stdDot_nonneg v),norm_nonneg v,Real.sqrt_nonneg (stdDot n v v)]


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

lemma integrable_stdDot_const_sub {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (v : Phase n) :
    Integrable (fun x => stdDot n (v-f x) (v-f x)) μ := by
  have hvf : Integrable (fun x => 2*stdDot n v (f x)) μ :=
    (((stdDot n) v).integrable_comp hf).const_mul 2
  have hi : Integrable (fun x => stdDot n v v-2*stdDot n v (f x)+stdDot n (f x) (f x)) μ :=
    ((integrable_const _).sub hvf).add he
  simpa only [stdDot_sub_self] using hi

lemma phaseAverage_const_sub {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ) (hμ : 0<μ.real univ) (v : Phase n) :
    phaseAverage μ (fun x => v-f x)=v-phaseAverage μ f := by
  rw [phaseAverage,integral_sub (integrable_const _) hf,integral_const,smul_sub,inv_smul_smul₀ hμ.ne']
  rfl

lemma phaseAverage_deviation_energy_le {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hf : Integrable f μ)
    (he : Integrable (fun x => stdDot n (f x) (f x)) μ) (hμ : 0<μ.real univ) (v : Phase n) :
    stdDot n (v-phaseAverage μ f) (v-phaseAverage μ f)≤
      (μ.real univ)⁻¹*(∫ x,stdDot n (v-f x) (v-f x) ∂μ) := by
  have hh := stdDot_average_sq_le ((integrable_const v).sub hf) (integrable_stdDot_const_sub hf he v) hμ
  change stdDot n (phaseAverage μ (fun x => v-f x)) (phaseAverage μ (fun x => v-f x))≤_ at hh
  rw [phaseAverage_const_sub hf hμ v] at hh
  exact hh


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma stdDot_sub_self_le (v w : Phase n) :
    stdDot n (v-w) (v-w)≤2*stdDot n v v+2*stdDot n w w := by
  simpa only [map_neg,neg_apply,neg_neg,sub_eq_add_neg] using stdDot_add_self_le v (-w)

lemma curve_pair_energy_le {v : ℝ → Phase n} (hv : ContDiff ℝ ∞ v) {a b s t : ℝ}
    (hs : s∈Icc a b) (ht : t∈Icc a b) :
    stdDot n (v s-v t) (v s-v t)≤4*(b-a)*
      (∫ r in a..b,stdDot n (deriv v r) (deriv v r)) := by
  have h1 := curve_chord_energy_le hv hs.1 hs.2
  have h2 := curve_chord_energy_le hv ht.1 ht.2
  have h3 := stdDot_sub_self_le (v s-v a) (v t-v a)
  rw [sub_sub_sub_cancel_right] at h3
  nlinarith only [h1,h2,h3]

lemma horizontal_curve_deriv {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (y x : ℝ) :
    deriv (fun s : ℝ => v (s,y)) x=fderiv ℝ v (x,y) (1,0) := by
  have hh := (hv.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x,y)).hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))
  change HasDerivAt (fun s : ℝ => v (s,y)) _ x at hh
  exact hh.deriv

lemma vertical_curve_deriv {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (x y : ℝ) :
    deriv (fun s : ℝ => v (x,s)) y=fderiv ℝ v (x,y) (0,1) := by
  have hh := (hv.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x,y)).hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
  change HasDerivAt (fun s : ℝ => v (x,s)) _ y at hh
  exact hh.deriv

lemma horizontalEnergy_continuous {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (horizontalEnergy v) := by
  have hh := (hv.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous.clm_apply (continuous_const (y := ((1,0):Plane)))
  exact ((stdDot n).continuous.comp hh).clm_apply hh

lemma verticalEnergy_continuous {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) :
    Continuous (verticalEnergy v) := by
  have hh := (hv.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous.clm_apply (continuous_const (y := ((0,1):Plane)))
  exact ((stdDot n).continuous.comp hh).clm_apply hh

lemma rectangle_pair_energy_bound {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} {p q : Plane} (hp : p∈(Icc a b) ×ˢ (Icc a b)) (hq : q∈(Icc a b) ×ˢ (Icc a b)) :
    stdDot n (v p-v q) (v p-v q)≤
      8*(b-a)*((∫ x in a..b,horizontalEnergy v (x,p.2))+
        (∫ y in a..b,verticalEnergy v (q.1,y))) := by
  have hx := curve_pair_energy_le (v := fun x => v (x,p.2)) (hv.comp (contDiff_id.prodMk (contDiff_const (c := p.2)))) hp.1 hq.1
  have hy := curve_pair_energy_le (v := fun y => v (q.1,y)) (hv.comp ((contDiff_const (c := q.1)).prodMk contDiff_id)) hp.2 hq.2
  change stdDot n (v (p.1,p.2)-v (q.1,p.2)) (v (p.1,p.2)-v (q.1,p.2))≤_ at hx
  change stdDot n (v (q.1,p.2)-v (q.1,q.2)) (v (q.1,p.2)-v (q.1,q.2))≤_ at hy
  simp only [horizontal_curve_deriv hv] at hx
  simp only [vertical_curve_deriv hv] at hy
  have hh := stdDot_add_self_le (v p-v (q.1,p.2)) (v (q.1,p.2)-v q)
  rw [sub_add_sub_cancel] at hh
  change stdDot n (v p-v (q.1,p.2)) (v p-v (q.1,p.2))≤
    4*(b-a)*(∫ x in a..b,horizontalEnergy v (x,p.2)) at hx
  change stdDot n (v (q.1,p.2)-v q) (v (q.1,p.2)-v q)≤
    4*(b-a)*(∫ y in a..b,verticalEnergy v (q.1,y)) at hy
  nlinarith only [hx,hy,hh]


lemma squareMeasure_eq (a b : ℝ) :
    squareMeasure a b=volume.restrict ((Icc a b) ×ˢ (Icc a b)) := by
  rw [squareMeasure,Measure.prod_restrict,←Measure.volume_eq_prod]

lemma squareMeasure_mass {a b : ℝ} (hab : a≤b) :
    (squareMeasure a b).real univ=(b-a)^2 := by
  rw [squareMeasure,Measure.real,←univ_prod_univ,Measure.prod_prod]
  simp [Real.volume_Icc,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab),pow_two]

lemma intervalMeasure_mass {a b : ℝ} (hab : a≤b) :
    (volume.restrict (Icc a b)).real univ=b-a := by
  simp [Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma continuous_square_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Continuous f) (a b : ℝ) : Integrable f (squareMeasure a b) := by
  rw [squareMeasure_eq]
  exact hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma square_ae_mem (a b : ℝ) : ∀ᵐ z ∂squareMeasure a b,z∈(Icc a b) ×ˢ (Icc a b) := by
  rw [squareMeasure_eq]
  exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)

lemma square_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f : Plane → E} (hf : Integrable f (squareMeasure a b)) :
    (∫ z,f z ∂squareMeasure a b)=∫ x in Icc a b,∫ y in Icc a b,f (x,y) :=
  integral_prod f hf

lemma square_integral_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} {f : Plane → E} (hf : Integrable f (squareMeasure a b)) :
    (∫ z,f z ∂squareMeasure a b)=∫ y in Icc a b,∫ x in Icc a b,f (x,y) :=
  integral_prod_symm f hf

lemma integral_Icc_eq_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a≤b) :
    (∫ x in Icc a b,f x)=∫ x in a..b,f x := by
  rw [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc]


lemma horizontalSlice_integrable {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    Integrable (horizontalSlice v a b) (volume.restrict (Icc a b)) :=
  (continuous_square_integrable (horizontalEnergy_continuous hv) a b).integral_prod_right

lemma verticalSlice_integrable {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v) (a b : ℝ) :
    Integrable (verticalSlice v a b) (volume.restrict (Icc a b)) :=
  (continuous_square_integrable (verticalEnergy_continuous hv) a b).integral_prod_left

lemma square_point_deviation_bound {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a<b) {p : Plane} (hp : p∈(Icc a b) ×ˢ (Icc a b)) :
    stdDot n (v p-phaseAverage (squareMeasure a b) v) (v p-phaseAverage (squareMeasure a b) v)≤
      8*(b-a)*horizontalSlice v a b p.2+8*(∫ z,verticalEnergy v z ∂squareMeasure a b) := by
  have hvi := continuous_square_integrable hv.continuous a b
  have hve := continuous_square_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) a b
  have hm : 0<(squareMeasure a b).real univ := by rw [squareMeasure_mass hab.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (v p)
  have hvsi : Integrable (fun q : Plane => verticalSlice v a b q.1) (squareMeasure a b) :=
    (verticalSlice_integrable hv a b).comp_fst _
  have hright : Integrable (fun q : Plane => 8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1))
      (squareMeasure a b) :=
    ((integrable_const _).add hvsi).const_mul _
  have hcomp : (∫ q,stdDot n (v p-v q) (v p-v q) ∂squareMeasure a b)≤
      ∫ q,8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1) ∂squareMeasure a b := by
    apply integral_mono_ae (integrable_stdDot_const_sub hvi hve (v p)) hright
    filter_upwards [square_ae_mem a b] with q hq
    have hh := rectangle_pair_energy_bound hv hp hq
    simpa only [horizontalSlice,verticalSlice,integral_Icc_eq_interval hab.le] using hh
  have hmass := intervalMeasure_mass hab.le
  have hfub := square_integral (continuous_square_integrable (verticalEnergy_continuous hv) a b)
  have hrightVal : (∫ q,8*(b-a)*(horizontalSlice v a b p.2+verticalSlice v a b q.1) ∂squareMeasure a b)=
      8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
        (b-a)*(∫ z,verticalEnergy v z ∂squareMeasure a b)) := by
    rw [integral_const_mul,integral_add (integrable_const _) hvsi,
      integral_const,squareMeasure_mass hab.le]
    change 8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
      (∫ q,verticalSlice v a b q.1 ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b))))=_
    rw [integral_fun_fst,hmass]
    rw [hfub]
    rfl
  rw [hrightVal] at hcomp
  have hh := hj.trans (mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hm.le))
  rw [squareMeasure_mass hab.le] at hh
  have hid : ((b-a)^2)⁻¹*(8*(b-a)*((b-a)^2*horizontalSlice v a b p.2+
      (b-a)*(∫ z,verticalEnergy v z ∂squareMeasure a b)))=
      8*(b-a)*horizontalSlice v a b p.2+8*(∫ z,verticalEnergy v z ∂squareMeasure a b) := by
    field_simp [(sub_pos.mpr hab).ne']
  rwa [hid] at hh

lemma square_poincare {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (hab : a<b) :
    (∫ z,stdDot n (v z-phaseAverage (squareMeasure a b) v) (v z-phaseAverage (squareMeasure a b) v)
      ∂squareMeasure a b)≤
      8*(b-a)^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
  have hleft : Integrable (fun z => stdDot n (v z-phaseAverage (squareMeasure a b) v)
      (v z-phaseAverage (squareMeasure a b) v)) (squareMeasure a b) := continuous_square_integrable
    (((stdDot n).continuous.comp (hv.continuous.sub continuous_const)).clm_apply
      (hv.continuous.sub continuous_const)) a b
  have hxsi : Integrable (fun p : Plane => horizontalSlice v a b p.2) (squareMeasure a b) :=
    (horizontalSlice_integrable hv a b).comp_snd _
  have hright : Integrable (fun p : Plane => 8*(b-a)*horizontalSlice v a b p.2+
      8*(∫ z,verticalEnergy v z ∂squareMeasure a b)) (squareMeasure a b) :=
    (hxsi.const_mul _).add (integrable_const _)
  have hcomp := integral_mono_ae hleft hright (by
    filter_upwards [square_ae_mem a b] with p hp
    exact square_point_deviation_bound hv hab hp)
  have hx := continuous_square_integrable (horizontalEnergy_continuous hv) a b
  have hy := continuous_square_integrable (verticalEnergy_continuous hv) a b
  have hfub := square_integral_swap hx
  rw [integral_add (hxsi.const_mul _) (integrable_const _)] at hcomp
  rw [integral_const_mul,integral_const] at hcomp
  change _≤8*(b-a)*(∫ p,horizontalSlice v a b p.2 ∂(volume.restrict (Icc a b)).prod (volume.restrict (Icc a b)))+
    (squareMeasure a b).real univ*(8*(∫ z,verticalEnergy v z ∂squareMeasure a b)) at hcomp
  rw [integral_fun_snd,intervalMeasure_mass hab.le,squareMeasure_mass hab.le] at hcomp
  change _≤8*(b-a)*((b-a)*(∫ y in Icc a b,∫ x in Icc a b,horizontalEnergy v (x,y)))+_ at hcomp
  rw [←hfub] at hcomp
  rw [integral_add hx hy]
  nlinarith only [hcomp]


lemma stdDot_sub_swap (v w : Phase n) : stdDot n (v-w) (v-w)=stdDot n (w-v) (w-v) := by
  have h : w-v=-(v-w) := by abel
  rw [h]
  simp only [map_neg,neg_apply,neg_neg]

lemma square_energy_mono {f : Plane → ℝ} (hf : Continuous f) (hn : ∀ z,0≤f z)
    {a b c d : ℝ} (hac : a ≤ c) (hdb : d≤b) :
    (∫ z,f z ∂squareMeasure c d)≤∫ z,f z ∂squareMeasure a b := by
  simp only [squareMeasure_eq]
  apply setIntegral_mono_set (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc))
    (Eventually.of_forall hn)
  exact Eventually.of_forall (fun z hz =>
    ⟨⟨hac.trans hz.1.1,hz.1.2.trans hdb⟩,⟨hac.trans hz.2.1,hz.2.2.trans hdb⟩⟩)

lemma square_means_energy {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {a b c d : ℝ} (hab : a<b) (hcd : c<d) (hac : a ≤ c) (hdb : d≤b) :
    stdDot n (phaseAverage (squareMeasure a b) v-phaseAverage (squareMeasure c d) v)
      (phaseAverage (squareMeasure a b) v-phaseAverage (squareMeasure c d) v)≤
      ((d-c)^2)⁻¹*(8*(b-a)^2)*
        (∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
  have hvi := continuous_square_integrable hv.continuous c d
  have hve := continuous_square_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) c d
  have hm : 0<(squareMeasure c d).real univ := by rw [squareMeasure_mass hcd.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (phaseAverage (squareMeasure a b) v)
  rw [squareMeasure_mass hcd.le] at hj
  have hm' : 0≤((d-c)^2)⁻¹ := by positivity
  have hmono := square_energy_mono
    (((stdDot n).continuous.comp (continuous_const.sub hv.continuous)).clm_apply
      (continuous_const.sub hv.continuous))
    (fun z => stdDot_nonneg (phaseAverage (squareMeasure a b) v-v z)) hac hdb
  have hs : (∫ z,stdDot n (phaseAverage (squareMeasure a b) v-v z)
      (phaseAverage (squareMeasure a b) v-v z) ∂squareMeasure a b)≤
      8*(b-a)^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure a b) := by
    simp_rw [stdDot_sub_swap (phaseAverage (squareMeasure a b) v)]
    exact square_poincare hv hab
  have hh := hj.trans (mul_le_mul_of_nonneg_left (hmono.trans hs) hm')
  simpa only [mul_assoc] using hh

lemma quarter_square_mean_norm {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {r : ℝ} (hr : 0 < r) :
    ‖phaseAverage (squareMeasure (-r) r) v-phaseAverage (squareMeasure (-(r/4)) (r/4)) v‖^2≤
      128*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-r) r) := by
  have hh := square_means_energy hv (a := -r) (b := r) (c := -(r/4)) (d := r/4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hid : ((r/4-(-(r/4)))^2)⁻¹*(8*(r-(-r))^2)=(128:ℝ) := by
    field_simp [hr.ne']
    ring
  rw [hid] at hh
  exact (norm_sq_le_stdDot _).trans hh

lemma square_dirichlet_le_radial {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {r A : ℝ} (hr : 0 ≤ r) (hA : 0<A) (hrA : 2*r^2≤A) :
    (∫ z,horizontalEnergy (realCurve u) z+verticalEnergy (realCurve u) z ∂squareMeasure (-r) r)≤
      radialCurveEnergy u A := by
  change (∫ z,dirichletEnergy u z ∂squareMeasure (-r) r)≤_
  rw [squareMeasure_eq]
  have heq : (∫ z in (Icc (-r) r) ×ˢ (Icc (-r) r),dirichletEnergy u z)=
      ∫ z in (Icc (-r) r) ×ˢ (Icc (-r) r),sourceRadialCutoff A z*dirichletEnergy u z := by
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro z hz
    have h1 : z.1^2 ≤ r^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg z.1) hr).mpr (abs_le.mpr hz.1)
    have h2 : z.2^2 ≤ r^2 := sq_le_sq' hz.2.1 hz.2.2
    have hrad : radiusSq z≤A := by dsimp [radiusSq] <;> nlinarith
    change dirichletEnergy u z=sourceRadialCutoff A z*dirichletEnergy u z
    rw [show sourceRadialCutoff A z=1 from
      outerProfile_one_before (radiusSq_nonneg z) hrad hA,one_mul]
  rw [heq]
  exact setIntegral_le_integral (smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu))
    (Eventually.of_forall (fun z => mul_nonneg (sourceRadialCutoff_nonneg A z) (dirichletEnergy_nonneg u z)))


lemma phaseAverage_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → Phase n} (hμ : 0<μ.real univ) {C : ℝ} (hf : ∀ᵐ x ∂μ,‖f x‖≤C) :
    ‖phaseAverage μ f‖≤C := by
  rw [phaseAverage,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hμ.le)]
  have hh := mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hf) (inv_nonneg.mpr hμ.le)
  have hid : (μ.real univ)⁻¹*(C*μ.real univ)=C := by field_simp
  rwa [hid] at hh

lemma plane_norm_le_square {r : ℝ} {z : Plane} (hz : z∈(Icc (-r) r) ×ˢ (Icc (-r) r)) : ‖z‖ ≤ r := by
  rw [Prod.norm_def]
  exact max_le (abs_le.mpr hz.1) (abs_le.mpr hz.2)

lemma squareAverage_tendsto {v : Plane → Phase n} (hv : Continuous v)
    {r : ℕ → ℝ} (hr : ∀ k,0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun k => phaseAverage (squareMeasure (-(r k)) (r k)) v) atTop (𝓝 (v 0)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδv⟩ := Metric.continuousAt_iff.mp hv.continuousAt (ε/2) (by positivity)
  have hev : ∀ᶠ k in atTop,r k<δ := hr0.eventually (gt_mem_nhds hδ)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,?_⟩
  intro k hk
  have hm : 0<(squareMeasure (-(r k)) (r k)).real univ := by
    rw [squareMeasure_mass (by linarith [hr k])]
    exact sq_pos_of_pos (by linarith [hr k])
  have hb : ∀ᵐ z ∂squareMeasure (-(r k)) (r k),‖v 0-v z‖≤ε/2 := by
    filter_upwards [square_ae_mem (-(r k)) (r k)] with z hz
    have hzδ : dist z 0<δ := by simpa only [dist_zero_right] using (plane_norm_le_square hz).trans_lt (hN k hk)
    have hh := hδv hzδ
    simpa only [dist_eq_norm,norm_sub_rev] using hh.le
  have hh := phaseAverage_norm_le hm hb
  rw [phaseAverage_const_sub (continuous_square_integrable hv _ _) hm] at hh
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt (by linarith)


lemma campRadius_pos (k : ℕ) : 0 < campRadius k := by unfold campRadius; positivity

lemma campRadius_succ (k : ℕ) : campRadius (k+1)=campRadius k/4 := by
  unfold campRadius
  rw [pow_succ]
  ring

lemma campRadius_sq (k : ℕ) : 2*(campRadius k)^2≤(1/16)^k := by
  unfold campRadius
  have hid : ((1/4:ℝ)^k)^2=(1/16:ℝ)^k := by
    rw [←pow_mul,Nat.mul_comm k 2,pow_mul]
    norm_num
  rw [mul_pow,hid]
  have hh : 0≤(1/16:ℝ)^k := by positivity
  nlinarith

lemma campRadius_tendsto : Tendsto campRadius atTop (𝓝 0) := by
  change Tendsto (fun k : ℕ => (1/2:ℝ)*(1/4)^k) atTop (𝓝 0)
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num : (1/4:ℝ)<1)).const_mul (1/2:ℝ)
  simpa only [campRadius,mul_zero] using hh

lemma geometric_sqrt_norm_bound {v : Phase n} {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (k : ℕ)
    (hv : ‖v‖^2≤128*B*θ^k) : ‖v‖≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by
  have hc : 0≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hc).mp
  have hid : (Real.sqrt (128*B)*(Real.sqrt θ)^k)^2=128*B*θ^k := by
    rw [mul_pow,Real.sq_sqrt (by positivity),←pow_mul,Nat.mul_comm k 2,pow_mul,Real.sq_sqrt hθ]
  rwa [hid]

lemma campanato_point_mean {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ k : ℕ,radialCurveEnergy u ((1/16)^k)≤B*θ^k) (k : ℕ) :
    ‖phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)-u 0‖≤
      Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  let f : ℕ → Phase n := fun j => phaseAverage (squareMeasure (-(campRadius j)) (campRadius j)) (realCurve u)
  have hf : Tendsto f atTop (𝓝 (u 0)) := by
    have hh := squareAverage_tendsto (realCurve_smooth hu).continuous campRadius_pos campRadius_tendsto
    simpa only [f,realCurve,Function.comp_apply,map_zero] using hh
  have hs (j : ℕ) : dist (f j) (f (j+1))≤Real.sqrt (128*B)*(Real.sqrt θ)^j := by
    rw [dist_eq_norm]
    apply geometric_sqrt_norm_bound hB hθ j
    have hq := quarter_square_mean_norm (realCurve_smooth hu) (campRadius_pos j)
    have hr := square_dirichlet_le_radial hu (campRadius_pos j).le
      (by positivity : (0:ℝ)<(1/16)^j) (campRadius_sq j)
    change ‖phaseAverage (squareMeasure (-(campRadius j)) (campRadius j)) (realCurve u)-
      phaseAverage (squareMeasure (-(campRadius (j+1))) (campRadius (j+1))) (realCurve u)‖^2≤_
    rw [campRadius_succ]
    exact hq.trans ((mul_le_mul_of_nonneg_left (hr.trans (he j)) (by norm_num)).trans_eq (by ring))
  have hsqrt : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  simpa only [dist_eq_norm] using dist_le_of_le_geometric_of_tendsto (Real.sqrt θ) (Real.sqrt (128*B)) hsqrt hs hf k



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Campanato_TranslatedSquare
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma translatedSquare_mass (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (translatedSquare c r).real univ=(2*r)^2 := by
  rw [translatedSquare,Measure.real,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  change (squareMeasure (-r) r).real univ=(2*r)^2
  rw [squareMeasure_mass (by linarith)]
  ring

lemma translatedSquare_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} (hf : Continuous f) (c : Plane) (r : ℝ) :
    Integrable f (translatedSquare c r) := by
  unfold translatedSquare
  apply ((Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding.integrable_map_iff).mpr
  exact continuous_square_integrable (hf.comp (continuous_id.add continuous_const)) _ _

lemma translatedSquare_average (c : Plane) (r : ℝ) (v : Plane → Phase n) :
    phaseAverage (translatedSquare c r) v=
      phaseAverage (squareMeasure (-r) r) (fun z => v (z+c)) := by
  have he : MeasurableEmbedding (fun z : Plane => z+c) := (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  unfold phaseAverage translatedSquare
  rw [he.integral_map]
  congr 1
  rw [Measure.real,Measure.map_apply (by fun_prop) MeasurableSet.univ]
  rfl

lemma translatedSquare_le {c : Plane} {r R : ℝ} (hrr : ‖c‖+r≤R) :
    translatedSquare c r≤ squareMeasure (-R) R := by
  have hsub : (Icc (-r) r) ×ˢ (Icc (-r) r)⊆
      (fun z : Plane => z+c) ⁻¹' ((Icc (-R) R) ×ˢ (Icc (-R) R)) := by
    intro z hz
    have hc1 := norm_fst_le c
    have hc2 := norm_snd_le c
    have hc1' := abs_le.mp hc1
    have hc2' := abs_le.mp hc2
    change (z.1+c.1,z.2+c.2)∈(Icc (-R) R) ×ˢ (Icc (-R) R)
    exact ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩
  have hh := Measure.map_mono (Measure.restrict_mono hsub (le_refl (volume : Measure Plane)))
    (show Measurable (fun z : Plane => z+c) by fun_prop)
  rw [←Measure.restrict_map (by fun_prop) (measurableSet_Icc.prod measurableSet_Icc),
    (measurePreserving_add_right (volume : Measure Plane) c).map_eq] at hh
  simpa only [translatedSquare,squareMeasure_eq] using hh

lemma translated_square_means_energy {v : Plane → Phase n} (hv : ContDiff ℝ ∞ v)
    {c : Plane} {r R : ℝ} (hr : 0 < r) (hR : 0<R) (hrr : ‖c‖+r≤R) :
    ‖phaseAverage (squareMeasure (-R) R) v-phaseAverage (translatedSquare c r) v‖^2≤
      ((2*r)^2)⁻¹*(8*(2*R)^2)*
        (∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-R) R) := by
  have hvi := translatedSquare_integrable hv.continuous c r
  have hve := translatedSquare_integrable (((stdDot n).continuous.comp hv.continuous).clm_apply hv.continuous) c r
  have hm : 0<(translatedSquare c r).real univ := by rw [translatedSquare_mass c hr.le]; positivity
  have hj := phaseAverage_deviation_energy_le hvi hve hm (phaseAverage (squareMeasure (-R) R) v)
  rw [translatedSquare_mass c hr.le] at hj
  have hii : Integrable (fun z => stdDot n (phaseAverage (squareMeasure (-R) R) v-v z)
      (phaseAverage (squareMeasure (-R) R) v-v z)) (squareMeasure (-R) R) :=
    continuous_square_integrable
      (((stdDot n).continuous.comp (continuous_const.sub hv.continuous)).clm_apply
        (continuous_const.sub hv.continuous)) _ _
  have hmono := integral_mono_measure (translatedSquare_le hrr)
    (Eventually.of_forall (fun z => stdDot_nonneg (phaseAverage (squareMeasure (-R) R) v-v z))) hii
  have hp := square_poincare hv (a := -R) (b := R) (by linarith)
  have hp' : (∫ z,stdDot n (phaseAverage (squareMeasure (-R) R) v-v z)
      (phaseAverage (squareMeasure (-R) R) v-v z) ∂squareMeasure (-R) R)≤
      8*(R-(-R))^2*(∫ z,horizontalEnergy v z+verticalEnergy v z ∂squareMeasure (-R) R) := by
    simpa only [stdDot_sub_swap (phaseAverage (squareMeasure (-R) R) v)] using hp
  have hh := (norm_sq_le_stdDot _).trans (hj.trans
    (mul_le_mul_of_nonneg_left (hmono.trans hp') (by positivity)))
  simpa only [sub_neg_eq_add,←two_mul,mul_assoc] using hh


lemma correction_norm_triangle (a b c : Phase n) : ‖a-c‖≤‖a-b‖+‖b-c‖ := by
  simpa only [dist_eq_norm] using dist_triangle a b c

lemma square_dirichlet_le_total {w : ℂ → Phase n}
    (hi : Integrable (dirichletEnergy w)) (r : ℝ) :
    (∫ z,dirichletEnergy w z ∂squareMeasure (-r) r)≤∫ z,dirichletEnergy w z := by
  rw [squareMeasure_eq]
  exact setIntegral_le_integral hi (Eventually.of_forall (dirichletEnergy_nonneg w))

lemma centered_dirichlet_integrable {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) (c : ℂ) :
    Integrable (dirichletEnergy (centeredCurve w c)) := by
  have hh := (measurePreserving_add_right volume (Complex.equivRealProdCLM c)).integrable_comp_of_integrable hi
  change Integrable (fun z => dirichletEnergy (centeredCurve w c) z)
  simp_rw [dirichletEnergy_centered hw]
  exact hh

lemma centered_dirichlet_integral {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w) (c : ℂ) :
    (∫ z,dirichletEnergy (centeredCurve w c) z)=∫ z,dirichletEnergy w z := by
  simp only [dirichletEnergy_centered hw,integral_add_right_eq_self]

lemma curveSquareAverage_translated (w : ℂ → Phase n) (c : ℂ) (r : ℝ) :
    curveSquareAverage w c r=phaseAverage (translatedSquare (Complex.equivRealProdCLM c) r) (realCurve w) := by
  rw [translatedSquare_average,curveSquareAverage,realCurve_centered]

lemma curveSquareAverage_zero (w : ℂ → Phase n) (r : ℝ) :
    curveSquareAverage w 0 r=phaseAverage (squareMeasure (-r) r) (realCurve w) := by
  unfold curveSquareAverage
  congr 2
  funext z
  simp only [centeredCurve,add_zero]

lemma growing_square_step {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ‖curveSquareAverage w c (4*r)-curveSquareAverage w c r‖≤Real.sqrt (128*D) := by
  have hq := quarter_square_mean_norm (realCurve_smooth (centeredCurve_smooth hw c))
    (r := 4*r) (by positivity)
  have ht := (square_dirichlet_le_total (centered_dirichlet_integrable hw hi c) (4*r))
  rw [centered_dirichlet_integral hw] at ht
  have hm := mul_le_mul_of_nonneg_left (ht.trans he) (by norm_num : (0:ℝ)≤128)
  have hb : ‖curveSquareAverage w c (4*r)-curveSquareAverage w c r‖^2≤128*D := by
    rw [show 4*r/4=r by ring] at hq
    exact hq.trans hm
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hb

lemma growing_square_telescope {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) (c : ℂ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ‖curveSquareAverage w c (r*4^k)-curveSquareAverage w c r‖≤(k:ℝ)*Real.sqrt (128*D) := by
  induction k with
  | zero => simp
  | succ k hk =>
    have hs := growing_square_step hw hi hD he c (r := r*4^k) (by positivity)
    have hid : r*4^(k+1)=4*(r*4^k) := by rw [pow_succ]; ring
    rw [hid]
    have ht := correction_norm_triangle (curveSquareAverage w c (4*(r*4^k)))
      (curveSquareAverage w c (r*4^k)) (curveSquareAverage w c r)
    push_cast
    nlinarith only [ht,hs,hk]

lemma neighboring_growing_means {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ‖Complex.equivRealProdCLM c‖ ≤ r) :
    ‖curveSquareAverage w c r-curveSquareAverage w 0 r‖≤2*Real.sqrt (128*D) := by
  have hq := translated_square_means_energy (realCurve_smooth hw) hr
    (R := 4*r) (by positivity) (c := Complex.equivRealProdCLM c) (by linarith)
  have hid : ((2*r)^2)⁻¹*(8*(2*(4*r))^2)=(128:ℝ) := by
    field_simp [hr.ne']
    ring
  rw [hid] at hq
  have hm := mul_le_mul_of_nonneg_left ((square_dirichlet_le_total hi (4*r)).trans he)
    (by norm_num : (0:ℝ)≤128)
  have hb : ‖curveSquareAverage w 0 (4*r)-curveSquareAverage w c r‖≤Real.sqrt (128*D) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    rw [curveSquareAverage_zero,curveSquareAverage_translated]
    exact hq.trans hm
  have hs := growing_square_step hw hi hD he 0 hr
  have ht := correction_norm_triangle (curveSquareAverage w c r) (curveSquareAverage w 0 (4*r))
    (curveSquareAverage w 0 r)
  rw [norm_sub_rev (curveSquareAverage w c r) (curveSquareAverage w 0 (4*r))] at ht
  linarith

lemma correction_growth_by_scales {w : ℂ → Phase n} (hw : ContDiff ℝ ∞ w)
    (hi : Integrable (dirichletEnergy w)) {D L : ℝ} (hD : 0≤D)
    (he : (∫ z,dirichletEnergy w z)≤D) {r : ℝ} (hr : 0 < r)
    (hlocal : ∀ c : ℂ,‖w c-curveSquareAverage w c r‖≤L)
    (k : ℕ) (c : ℂ) (hc : ‖Complex.equivRealProdCLM c‖ ≤ r*4^k) :
    ‖w c-w 0‖≤2*L+2*((k:ℝ)+1)*Real.sqrt (128*D) := by
  have htc := growing_square_telescope hw hi hD he c hr k
  have ht0 := growing_square_telescope hw hi hD he 0 hr k
  have hnb := neighboring_growing_means hw hi hD he (by positivity) hc
  have h1 := correction_norm_triangle (w c) (curveSquareAverage w c r) (w 0)
  have h2 := correction_norm_triangle (curveSquareAverage w c r) (curveSquareAverage w c (r*4^k)) (w 0)
  have h3 := correction_norm_triangle (curveSquareAverage w c (r*4^k)) (curveSquareAverage w 0 (r*4^k)) (w 0)
  have h4 := correction_norm_triangle (curveSquareAverage w 0 (r*4^k)) (curveSquareAverage w 0 r) (w 0)
  rw [norm_sub_rev (curveSquareAverage w c r) (curveSquareAverage w c (r*4^k))] at h2
  rw [norm_sub_rev (curveSquareAverage w 0 r) (w 0)] at h4
  linarith [hlocal c,hlocal 0]


lemma realProd_norm_le (c : ℂ) : ‖Complex.equivRealProdCLM c‖≤‖c‖ := by
  change max ‖c.re‖ ‖c.im‖≤‖c‖
  exact max_le (Complex.abs_re_le_norm c) (Complex.abs_im_le_norm c)

lemma translated_camp_mean_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (k : ℕ)
    (he : radialCurveEnergy u ((1/16)^k)≤B*θ^k)
    {c : ℂ} (hc : ‖c‖ ≤ campRadius (k+1)) :
    ‖phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)-
      phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1)))
        (realCurve (centeredCurve u c))‖≤Real.sqrt (128*B)*(Real.sqrt θ)^k := by
  have hc' : ‖Complex.equivRealProdCLM c‖+campRadius (k+1) ≤ campRadius k := by
    have hh := (realProd_norm_le c).trans hc
    rw [campRadius_succ] at hh ⊢
    linarith [campRadius_pos k]
  have hh := translated_square_means_energy (realCurve_smooth hu)
    (campRadius_pos (k+1)) (campRadius_pos k) hc'
  rw [translatedSquare_average,←realCurve_centered] at hh
  have hid : ((2*campRadius (k+1))^2)⁻¹*(8*(2*campRadius k)^2)=(128:ℝ) := by
    rw [campRadius_succ]
    field_simp [(campRadius_pos k).ne']
    ring
  rw [hid] at hh
  have hr := square_dirichlet_le_radial hu (campRadius_pos k).le (by positivity : (0:ℝ)<(1/16)^k) (campRadius_sq k)
  apply geometric_sqrt_norm_bound hB hθ k
  exact hh.trans ((mul_le_mul_of_nonneg_left (hr.trans he) (by norm_num)).trans_eq (by ring))

lemma centeredCurve_zero (u : ℂ → Phase n) : centeredCurve u 0=u := by
  funext z
  simp only [centeredCurve,add_zero]

lemma centeredCurve_centered (u : ℂ → Phase n) (p q : ℂ) :
    centeredCurve (centeredCurve u p) q=centeredCurve u (q+p) := by
  funext z
  simp only [centeredCurve,add_assoc]

lemma campanato_oscillation_zero {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k)
    (k : ℕ) {c : ℂ} (hc : ‖c‖ ≤ campRadius (k+1)) :
    ‖u c-u 0‖≤2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  have hroot : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  have hden : 0<1-Real.sqrt θ := by linarith
  have he0 : ∀ j : ℕ,radialCurveEnergy u ((1/16)^j)≤B*θ^j := by
    intro j
    simpa only [centeredCurve_zero] using he 0 j
  have hpc := campanato_point_mean (centeredCurve_smooth hu c) hB hθ hθ1 (he c) (k+1)
  have hp0 := campanato_point_mean hu hB hθ hθ1 he0 (k+1)
  have hmc := translated_camp_mean_bound hu hB hθ k (he0 k) hc
  have hm0 := translated_camp_mean_bound hu hB hθ k (he0 k) (c := 0) (by simpa using (campRadius_pos (k+1)).le)
  rw [centeredCurve_zero] at hm0
  simp only [centeredCurve,zero_add] at hpc
  let m := phaseAverage (squareMeasure (-(campRadius k)) (campRadius k)) (realCurve u)
  let m0 := phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1))) (realCurve u)
  let mc := phaseAverage (squareMeasure (-(campRadius (k+1))) (campRadius (k+1))) (realCurve (centeredCurve u c))
  have htri : ‖u c-u 0‖≤‖mc-u c‖+‖m-mc‖+‖m-m0‖+‖m0-u 0‖ := by
    have h1 := dist_triangle (u c) mc (u 0)
    have h2 := dist_triangle mc m (u 0)
    have h3 := dist_triangle m m0 (u 0)
    simp only [dist_eq_norm] at h1 h2 h3
    rw [norm_sub_rev (u c) mc] at h1
    rw [norm_sub_rev mc m] at h2
    linarith
  have ht : ‖u c-u 0‖≤
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^(k+1)/(1-Real.sqrt θ))+
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^k) := by
    dsimp [m,m0,mc] at htri
    linarith only [htri,hpc,hp0,hmc,hm0]
  have hid : 2*(Real.sqrt (128*B)*(Real.sqrt θ)^(k+1)/(1-Real.sqrt θ))+
      2*(Real.sqrt (128*B)*(Real.sqrt θ)^k)=
      2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
    rw [pow_succ]
    field_simp
    ring
  exact ht.trans_eq hid

lemma campanato_oscillation {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k)
    (k : ℕ) {p q : ℂ} (hpq : ‖q-p‖ ≤ campRadius (k+1)) :
    ‖u q-u p‖≤2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ) := by
  have hh := campanato_oscillation_zero (centeredCurve_smooth hu p) hB hθ hθ1
    (fun c j => by simpa only [centeredCurve_centered] using he (c+p) j) k hpq
  simpa only [centeredCurve,sub_add_cancel,zero_add] using hh


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma energy_uniform_modulus {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧
      ∀ (u : ℂ → Phase n),ContDiff ℝ ∞ u →
        (∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k) →
        ∀ p q : ℂ,dist p q<δ →dist (u p) (u q)<ε := by
  have hroot : Real.sqrt θ<1 := (Real.sqrt_lt' (by norm_num)).mpr (by simpa using hθ1)
  have ht : Tendsto (fun k : ℕ => 2*Real.sqrt (128*B)*(Real.sqrt θ)^k/(1-Real.sqrt θ)) atTop (𝓝 0) := by
    have hh := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.sqrt_nonneg θ) hroot).const_mul
      (2*Real.sqrt (128*B))).div_const (1-Real.sqrt θ)
    simpa only [mul_zero,zero_div] using hh
  obtain ⟨k,hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  refine ⟨campRadius (k+1),campRadius_pos (k+1),?_⟩
  intro u hu he p q hpq
  have hpq' : ‖q-p‖ ≤ campRadius (k+1) := by
    simpa only [dist_eq_norm,norm_sub_rev] using hpq.le
  have hh := campanato_oscillation hu hB hθ hθ1 he k hpq'
  rw [dist_eq_norm,norm_sub_rev]
  exact hh.trans_lt hk

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


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma complex_norm_le_two_plane_norm (z : Plane) : ‖Complex.equivRealProdCLM.symm z‖≤2*‖z‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (Complex.equivRealProdCLM.symm z)
  simp only [Complex.equivRealProdCLM_symm_apply_re,Complex.equivRealProdCLM_symm_apply_im] at hh
  have h1 := norm_fst_le z
  have h2 := norm_snd_le z
  simp only [Real.norm_eq_abs] at h1 h2
  exact hh.trans (by linarith)

lemma unit_slope_norm_le {a : Phase n} (ha : stdDot n a a=1) : ‖a‖≤1 := by
  have hh := norm_sq_le_stdDot a
  rw [ha] at hh
  nlinarith [norm_nonneg a]

lemma correction_local_average {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) :
    ∃ r : ℝ,0 < r ∧ ∀ (u : ℂ → Phase n),ContDiff ℝ ∞ u →
      (∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k) →
      ∀ a : Phase n,stdDot n a a=1 →∀ c : ℂ,
        ‖affineCorrection u a c-curveSquareAverage (affineCorrection u a) c r‖≤2 := by
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB hθ hθ1 (by norm_num : (0:ℝ)<1)
  let r : ℝ := min (δ/4) (1/4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrδ : 2*r<δ := by have hh := min_le_left (δ/4) (1/4:ℝ); dsimp [r] <;> linarith
  have hr1 : 2*r≤1 := by have hh := min_le_right (δ/4) (1/4:ℝ); dsimp [r] <;> linarith
  refine ⟨r,hr,?_⟩
  intro u hu he a ha c
  have hm : 0<(squareMeasure (-r) r).real univ := by
    rw [squareMeasure_mass (by linarith)]
    exact sq_pos_of_pos (by linarith)
  have hi := continuous_square_integrable (realCurve_smooth
    (centeredCurve_smooth (affineCorrection_smooth hu a) c)).continuous (-r) r
  have hb : ∀ᵐ z ∂squareMeasure (-r) r,
      ‖affineCorrection u a c-realCurve (centeredCurve (affineCorrection u a) c) z‖≤2 := by
    filter_upwards [square_ae_mem (-r) r] with z hz
    have hzn : ‖Complex.equivRealProdCLM.symm z‖≤2*r :=
      (complex_norm_le_two_plane_norm z).trans (mul_le_mul_of_nonneg_left (plane_norm_le_square hz) (by norm_num))
    have hd : dist c (Complex.equivRealProdCLM.symm z+c)<δ := by
      rw [dist_eq_norm,show c-(Complex.equivRealProdCLM.symm z+c)=-(Complex.equivRealProdCLM.symm z) by abel,norm_neg]
      exact hzn.trans_lt hrδ
    have huosc := hmod u hu he c (Complex.equivRealProdCLM.symm z+c) hd
    rw [dist_eq_norm] at huosc
    have han : ‖a‖≤1 := unit_slope_norm_le ha
    have hzsmul : ‖Complex.equivRealProdCLM.symm z • a‖≤1 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left han (norm_nonneg _)).trans (by simpa only [mul_one] using hzn.trans hr1)
    have hid : affineCorrection u a c-affineCorrection u a (Complex.equivRealProdCLM.symm z+c)=
        (u c-u (Complex.equivRealProdCLM.symm z+c))+Complex.equivRealProdCLM.symm z • a := by
      simp only [affineCorrection,add_smul]
      abel
    change ‖affineCorrection u a c-affineCorrection u a (Complex.equivRealProdCLM.symm z+c)‖≤2
    rw [hid]
    exact (norm_add_le _ _).trans (by linarith)
  have hh := phaseAverage_norm_le hm hb
  rw [phaseAverage_const_sub hi hm] at hh
  exact hh


lemma scale_growth_squared {w : ℂ → Phase n} {p : Phase n} {r A : ℝ}
    (hr : 0 < r) (hA : 0≤A)
    (hg : ∀ (k : ℕ) (c : ℂ),‖Complex.equivRealProdCLM c‖ ≤ r*4^k →
      ‖w c-p‖≤4+2*((k:ℝ)+1)*A) (c : ℂ) :
    ‖w c-p‖^2≤((4+4*A)^2/r)*(‖c‖+r) := by
  have hx : 1≤‖c‖/r+1 := by linarith [div_nonneg (norm_nonneg c) hr.le]
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<4)
  have hc : ‖Complex.equivRealProdCLM c‖ ≤ r*4^(k+1) := by
    have hcn : ‖c‖ < r*4^(k+1) := by
      have hh : ‖c‖/r<4^(k+1) := by linarith
      have htt := (div_lt_iff₀ hr).mp hh
      simpa only [mul_comm] using htt
    exact (Complex.equivRealProd_apply_le c).trans hcn.le
  have hh := hg (k+1) c hc
  have hnat : (k:ℝ)+2≤2*(2:ℝ)^k := by
    have hn : k+2≤2^(k+1) := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k+1))
    have hn' : (k:ℝ)+2≤(2:ℝ)^(k+1) := by exact_mod_cast hn
    simpa only [pow_succ,mul_comm] using hn'
  have hpow : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  have hsmall : ‖w c-p‖≤(4+4*A)*(2:ℝ)^k := by
    push_cast at hh
    nlinarith only [hh,hnat,hpow,hA]
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤(4+4*A)*(2:ℝ)^k)).mpr hsmall
  have hid : ((4+4*A)*(2:ℝ)^k)^2=(4+4*A)^2*(4:ℝ)^k := by
    rw [mul_pow,←pow_mul,Nat.mul_comm k 2,pow_mul]
    norm_num
  rw [hid] at hsq
  have hmul := mul_le_mul_of_nonneg_left hk (sq_nonneg (4+4*A))
  have hid' : (4+4*A)^2*(‖c‖/r+1)=((4+4*A)^2/r)*(‖c‖+r) := by field_simp
  exact hsq.trans (hmul.trans_eq hid')

theorem exact_unit_line_correction_growth {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n) :
    ∃ K r : ℝ,0<K ∧ 0 < r ∧ ∀ t∈Icc (0:ℝ) 1,∀ (p q : Phase n) (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ a : Phase n,stdDot n a a=1 →
        Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →∀ c : ℂ,
          ‖affineCorrection u a c-p‖^2≤K*(‖c‖+r) := by
  obtain ⟨D,hD,hres⟩ := exact_line_homotopy_residual_energy_bound_bp240 hJs hJ hJc hST hT hout
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_local_energy_of_slope_bp240 hJs hJ hJc hST hT hout
  have hB : 0≤C+M := by linarith
  obtain ⟨r,hr,hlocal⟩ := correction_local_average (n := n) hB hθ.le hθ1
  refine ⟨(4+4*Real.sqrt (128*D))^2/r,r,by positivity,hr,?_⟩
  intro t ht p q u hu a ha hlim c
  have hi := hu.affine_correction_energy_of_slope (lineHomotopy_compact hJc ht) hlim
  have htotal : (∫ z,dirichletEnergy (affineCorrection u a) z)≤D := by
    rw [hi.2]
    exact hres t ht p q u hu
  have he' : ∀ c : ℂ,∀ k : ℕ,
      radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤(C+M)*θ^k := by
    intro c k
    simpa only [ha,mul_one] using he t ht p q u hu a hlim c k
  have hp : affineCorrection u a 0=p := by simpa only [affineCorrection,zero_smul,sub_zero] using hu.2.2.1
  apply scale_growth_squared hr (Real.sqrt_nonneg _) (c := c)
  intro k z hz
  have hh := correction_growth_by_scales (affineCorrection_smooth hu.1 a) hi.1 hD.le htotal hr
    (hlocal u hu.1 he' a ha) k z hz
  rw [hp] at hh
  simpa only [show (2:ℝ)*2=4 by norm_num] using hh


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ}

lemma stdDot_le_dimension_norm_sq (a : Phase n) : stdDot n a a≤(n:ℝ)*‖a‖^2 := by
  rw [stdDot_apply]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (f := fun i =>
    (a i).re*(a i).re+(a i).im*(a i).im) (g := fun _ => ‖a‖^2) (fun i _ => by
      rw [←Complex.normSq_apply,Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm a i) 2)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

lemma unit_slope_linear_norm {a : Phase n} (ha : stdDot n a a=1) (z : ℂ) :
    ‖z‖^2≤(n:ℝ)*‖z • a‖^2 := by
  have hh := stdDot_le_dimension_norm_sq a
  rw [ha] at hh
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖z‖)
  rw [norm_smul,mul_pow]
  nlinarith only [hm]

lemma nonnegative_quadratic_bound {x A B : ℝ} (hx : 0≤x) (hA : 0≤A) (hB : 0≤B)
    (h : x^2≤A+B*x) : x≤A+B+1 := by
  by_contra! hh
  have hxB : B+1<x := by linarith
  have hm := mul_le_mul_of_nonneg_right hxB.le hx
  nlinarith only [h,hm,hh,hB]

lemma sublinear_correction_preimage_bound {u : ℂ → Phase n} {a p : Phase n}
    (ha : stdDot n a a=1) {K r Q : ℝ} (hK : 0≤K) (hr : 0 ≤ r) (hQ : 0≤Q)
    (hg : ∀ c : ℂ,‖affineCorrection u a c-p‖^2≤K*(‖c‖+r))
    {c : ℂ} (hc : ‖u c‖≤Q) :
    ‖c‖≤2*(n:ℝ)*(Q+‖p‖)^2+2*(n:ℝ)*K*r+2*(n:ℝ)*K+1 := by
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hlin := unit_slope_linear_norm ha c
  have hcor := hg c
  have htri1 := norm_le_norm_add_norm_sub (u c) (c • a)
  change ‖c • a‖≤‖u c‖+‖affineCorrection u a c‖ at htri1
  have htri2 := norm_le_norm_add_norm_sub p (affineCorrection u a c)
  rw [norm_sub_rev p] at htri2
  have hnlin : ‖c • a‖≤Q+‖p‖+‖affineCorrection u a c-p‖ := by linarith
  have hs : ‖c • a‖^2≤2*(Q+‖p‖)^2+2*‖affineCorrection u a c-p‖^2 := by
    have hs' := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤Q+‖p‖+‖affineCorrection u a c-p‖)).mpr hnlin
    nlinarith [sq_nonneg ((Q+‖p‖)-‖affineCorrection u a c-p‖)]
  have hh := hlin.trans (mul_le_mul_of_nonneg_left hs hn)
  have hm := mul_le_mul_of_nonneg_left hcor (by positivity : 0≤2*(n:ℝ))
  have hquad : ‖c‖^2≤(2*(n:ℝ)*(Q+‖p‖)^2+2*(n:ℝ)*K*r)+(2*(n:ℝ)*K)*‖c‖ := by
    nlinarith only [hh,hm]
  exact nonnegative_quadratic_bound (norm_nonneg _) (by positivity) (by positivity) hquad

theorem exact_unit_line_source_escape {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n) (p : Phase n) {Q : ℝ} (hQ : 0≤Q) :
    ∃ R : ℝ,0<R ∧ ∀ t∈Icc (0:ℝ) 1,∀ (q : Phase n) (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ a : Phase n,stdDot n a a=1 →
      Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →∀ c : ℂ,
      ‖u c‖≤Q →‖c‖≤R := by
  obtain ⟨K,r,hK,hr,hg⟩ := exact_unit_line_correction_growth hJs hJ hJc hST hT hout
  refine ⟨2*(n:ℝ)*(Q+‖p‖)^2+2*(n:ℝ)*K*r+2*(n:ℝ)*K+1,by positivity,?_⟩
  intro t ht q u hu a ha hlim c hc
  exact sublinear_correction_preimage_bound ha hK.le hr.le hQ (hg t ht p q u hu a ha hlim) hc


lemma dilatedCurve_original_second_mark {J : Phase n → End n} {p q : Phase n}
    {u : ℂ → Phase n} (hu : AffineLineCurve J p q u) {a : Phase n} (ha : a≠0) :
    dilatedCurve u (slopeScale a) (Real.sqrt (stdDot n a a))=q := by
  change u ((slopeScale a : ℂ)*(Real.sqrt (stdDot n a a) : ℂ))=q
  rw [←Complex.ofReal_mul]
  have hid : slopeScale a*Real.sqrt (stdDot n a a)=1 :=
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (stdDot_pos ha)).ne'
  rw [hid,Complex.ofReal_one]
  exact hu.2.2.2.1


theorem exact_line_slope_upper_bound {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n) (p q : Phase n) :
    ∃ D : ℝ,0<D ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ a : Phase n,a≠0 →Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) →
        stdDot n a a≤D := by
  obtain ⟨R,hR,hesc⟩ := exact_unit_line_source_escape hJs hJ hJc hST hT hout p (norm_nonneg q)
  refine ⟨R^2,sq_pos_of_pos hR,?_⟩
  intro t ht u hu a ha hlim
  have hs : (slopeScale a : ℂ)≠0 := by exact_mod_cast (slopeScale_pos ha).ne'
  have hlu := dilatedCurve_slope hlim hs
  have hnorm : stdDot n ((slopeScale a : ℂ) • a) ((slopeScale a : ℂ) • a)=1 := by
    simpa only [Complex.coe_smul] using normalizedSlope_unit ha
  have hh := hesc t ht (u (slopeScale a)) (dilatedCurve u (slopeScale a)) (hu.dilate hs)
    ((slopeScale a : ℂ) • a) hnorm hlu (Real.sqrt (stdDot n a a)) (by
      rw [dilatedCurve_original_second_mark hu ha])
  have hb : Real.sqrt (stdDot n a a)≤R := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using hh
  nlinarith [Real.sq_sqrt (stdDot_nonneg a),Real.sqrt_nonneg (stdDot n a a)]


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {n : ℕ} {ι : Type*}

lemma anchored_uniform_point_bound {F : ι → ℂ → Phase n} {p : Phase n}
    (hp : ∀ i,F i 0=p) {δ : ℝ} (hδ : 0<δ)
    (hF : ∀ i,∀ z w : ℂ,dist z w<δ →dist (F i z) (F i w)≤1) (x : ℂ) :
    ∃ M : ℝ,∀ i,‖F i x‖≤M := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (‖x‖/δ) 0)
  have hNp : 0<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hstep : ‖x‖/(N:ℝ)<δ := (div_lt_iff₀ hNp).mpr (by
    have hh := lt_of_le_of_lt (le_max_left _ _) hN
    have hh' := (div_lt_iff₀ hδ).mp hh
    nlinarith)
  let path : ℕ → ℂ := fun k => ((k:ℝ)/(N:ℝ)) • x
  have hp0 : path 0=0 := by simp [path]
  have hpN : path N=x := by
    change ((N:ℝ)/(N:ℝ)) • x=x
    rw [div_self hNp.ne',one_smul]
  have hdiff (k : ℕ) : path (k+1)-path k=((1:ℝ)/(N:ℝ)) • x := by
    dsimp only [path]
    rw [←sub_smul]
    congr 1
    push_cast
    ring
  have hpath (k : ℕ) : dist (path k) (path (k+1))<δ := by
    rw [dist_comm,dist_eq_norm,hdiff,norm_smul,Real.norm_of_nonneg (by positivity)]
    convert hstep using 1
    all_goals try with_reducible_and_instances rfl
    ring
  refine ⟨‖p‖+(N:ℝ),?_⟩
  intro i
  have hh := dist_le_range_sum_of_dist_le (f := fun k => F i (path k)) N (d := fun _ => (1:ℝ))
    (fun {k} _ => hF i (path k) (path (k+1)) (hpath k))
  simp only [hp0,hpN,hp,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hh
  have htri := dist_triangle (0:Phase n) p (F i x)
  simp only [dist_zero_left] at htri
  linarith

lemma energy_family_point_bound {F : ι → ℂ → Phase n} {p : Phase n}
    (hp : ∀ i,F i 0=p) (hs : ∀ i,ContDiff ℝ ∞ (F i))
    {B θ : ℝ} (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1)
    (he : ∀ i,∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve (F i) c) ((1/16)^k)≤B*θ^k)
    (x : ℂ) : ∃ M : ℝ,∀ i,‖F i x‖≤M := by
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB hθ hθ1 (by norm_num : (0:ℝ)<1)
  exact anchored_uniform_point_bound hp hδ (fun i z w hzw => (hmod (F i) (hs i) (he i) z w hzw).le) x



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Compactness_MarkedCurves
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.FiniteMoment.Radial.instInhabitedQuadrant _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open HolderCompletion
open scoped BoundedContinuousFunction
variable {n : ℕ}

lemma anchoredEnergyFamily_equicontinuous (p : Phase n) {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) :
    Equicontinuous (fun u : anchoredEnergyFamily p B θ => (u.val : ℂ → Phase n)) := by
  intro z
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := energy_uniform_modulus (n := n) hB hθ hθ1 hε
  refine ⟨δ,hδ,?_⟩
  intro w hw u
  exact hmod u.val u.property.2.1 u.property.2.2 z w (by rwa [dist_comm])

lemma anchoredEnergyFamily_pointwise (p : Phase n) {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) (z : ℂ) :
    ∃ Q : Set (Phase n),IsCompact Q ∧ ∀ u∈anchoredEnergyFamily p B θ,u z∈Q := by
  obtain ⟨M,hM⟩ := energy_family_point_bound
    (F := fun u : anchoredEnergyFamily p B θ => (u.val : ℂ → Phase n))
    (fun u => u.property.1) (fun u => u.property.2.1) hB hθ hθ1
    (fun u => u.property.2.2) z
  refine ⟨Metric.closedBall 0 M,isCompact_closedBall 0 M,?_⟩
  intro u hu
  simpa only [Metric.mem_closedBall,dist_zero_right] using hM ⟨u,hu⟩

lemma anchoredEnergyFamily_compactClosure (p : Phase n) {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) :
    IsCompact (closure (anchoredEnergyFamily p B θ)) := by
  let : T2Space (UniformOnFun ℂ (Phase n) {K : Set ℂ | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun u : C(ℂ,Phase n) => (u : ℂ → Phase n))
    (𝔖 := {K : Set ℂ | IsCompact K}) (fun K hK => hK)
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding)
  · intro K hK
    exact (anchoredEnergyFamily_equicontinuous p hB hθ hθ1).equicontinuousOn K
  · intro K hK z hz
    exact anchoredEnergyFamily_pointwise p hB hθ hθ1 z

lemma energy_family_czero_subsequence {p : Phase n} {B θ : ℝ}
    (hB : 0≤B) (hθ : 0≤θ) (hθ1 : θ<1) (u : ℕ → ℂ → Phase n)
    (hu : ∀ j,ContDiff ℝ ∞ (u j)) (hp : ∀ j,u j 0=p)
    (he : ∀ j,∀ c : ℂ,∀ k : ℕ,radialCurveEnergy (centeredCurve (u j) c) ((1/16)^k)≤B*θ^k) :
    ∃ v : C(ℂ,Phase n),v 0=p ∧ ∃ φ : ℕ → ℕ,StrictMono φ ∧
      ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn (fun j => u (φ j)) v atTop K := by
  let f : ℕ → C(ℂ,Phase n) := fun j => ⟨u j,(hu j).continuous⟩
  have hf (j : ℕ) : f j∈closure (anchoredEnergyFamily p B θ) :=
    subset_closure ⟨hp j,hu j,he j⟩
  obtain ⟨v,hv,φ,hφ,hlim⟩ := (anchoredEnergyFamily_compactClosure p hB hθ hθ1).tendsto_subseq hf
  have heval : Tendsto (fun j => u (φ j) 0) atTop (𝓝 (v 0)) :=
    ((show Continuous (fun g : C(ℂ,Phase n) => g 0) from continuous_eval_const 0).tendsto v).comp hlim
  have hv0 : v 0=p := tendsto_nhds_unique heval (by simpa only [hp] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)))
  refine ⟨v,hv0,φ,hφ,?_⟩
  intro K hK
  exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim) K hK

lemma exact_marked_line_uniform_energy {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n) (p q : Phase n) :
    ∃ B θ : ℝ,0<B ∧ 0<θ ∧ θ<1 ∧ ∀ t∈Icc (0:ℝ) 1,∀ (u : ℂ → Phase n),
      AffineLineCurve (lineHomotopy J t) p q u →∀ c : ℂ,∀ k : ℕ,
      radialCurveEnergy (centeredCurve u c) ((1/16)^k)≤B*θ^k := by
  obtain ⟨D,hD,hup⟩ := exact_line_slope_upper_bound hJs hJ hJc hST hT hout p q
  obtain ⟨C,M,θ,hC,hM,hθ,hθ1,he⟩ := exact_line_local_energy_of_slope_bp240 hJs hJ hJc hST hT hout
  refine ⟨C+M*D,θ,by positivity,hθ,hθ1,?_⟩
  intro t ht u hu c k
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  have hh := he t ht p q u hu a hlim c k
  have hsum : C+M*stdDot n a a≤C+M*D := add_le_add (le_refl C) (mul_le_mul_of_nonneg_left
    (hup t ht u hu a ha hlim) hM)
  exact hh.trans (mul_le_mul_of_nonneg_right hsum (by positivity))

theorem exact_marked_line_czero_compactness_bp240_oai {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x,S < capacity x →J x=standardJ n)
    {p q : Phase n} {t : ℕ → ℝ} (ht : ∀ j,t j∈Icc (0:ℝ) 1)
    {u : ℕ → ℂ → Phase n} (hu : ∀ j,AffineLineCurve (lineHomotopy J (t j)) p q (u j)) :
    ∃ v : C(ℂ,Phase n),v 0=p ∧ v 1=q ∧ ∃ φ : ℕ → ℕ,StrictMono φ ∧
      ∀ K : Set ℂ,IsCompact K →TendstoUniformlyOn (fun j => u (φ j)) v atTop K := by
  obtain ⟨B,θ,hB,hθ,hθ1,he⟩ := exact_marked_line_uniform_energy hJs hJ hJc hST hT hout p q
  obtain ⟨v,hv,φ,hφ,hsub⟩ := energy_family_czero_subsequence hB.le hθ.le hθ1 u
    (fun j => (hu j).1) (fun j => (hu j).2.2.1) (fun j => he (t j) (ht j) (u j) (hu j))
  have hlim : Tendsto (fun j => u (φ j) 1) atTop (𝓝 (v 1)) :=
    (hsub {1} isCompact_singleton).tendsto_at (mem_singleton 1)
  have hq : v 1=q := tendsto_nhds_unique hlim (by
    simpa only [fun j => (hu (φ j)).2.2.2.1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q)))
  exact ⟨v,hv,hq,φ,hφ,hsub⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240_oai := @OAI.HigherDimensionalBallPacking.Rigidity.exact_marked_line_czero_compactness_bp240_oai

-- Prove2me | solution 1 for OAI.CubicTorus.isMinimizerAt_three_vertex_parameters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:29:15.845997+00:00
-- url     : https://prove2.me/submissions/1ea75f58-1bd4-4c82-9fb0-3453e83c99c1

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_bottom_both_extents
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_missing_neighbor_projection
import Theorems.Thm_OAI_CubicTorus_isMinimizerAt_three_vertex_bottom

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVRegularity
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceElemCoverCompactCell _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma adjacent_faces {i : Fin 3} (x : Fin 2 → ℝ) :
    WithLp.toLp 2 (i.insertNth 1 x) =
      (WithLp.toLp 2 (i.insertNth 0 x) : Cover) + latticeVector (Pi.single i 1) := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
  · simp [latticeVector]
  · simp [latticeVector, Fin.succAbove_ne i k]

end CubicTorus

namespace CubicTorus

lemma divergence_smul_const {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point) (a : Cover) :
    divergence (fun y => f y • a) point = fderiv ℝ f point a := by
  have ha : (∑ i : Fin 3, a i • EuclideanSpace.single i 1) = a := by
    ext j
    simp [Pi.single_apply]
  simp only [divergence, fderiv_smul_const hf, ContinuousLinearMap.smulRight_apply,
    PiLp.smul_apply, smul_eq_mul]
  conv_rhs => rw [← ha, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

lemma divergence_const_smul {F : Cover → Cover} {point : Cover}
    (hF : DifferentiableAt ℝ F point) (c : ℝ) :
    divergence (fun y => c • F y) point = c * divergence F point := by
  change (∑ i : Fin 3, (fderiv ℝ (c • F) point (EuclideanSpace.single i 1)) i) = _
  rw [fderiv_const_smul hF c]
  simp [divergence, Finset.mul_sum]

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SmoothApproxLip
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.instCompactSpaceNormalSphere _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus

lemma measurableSet_stripe (V : ℝ) : MeasurableSet (stripe V) := by
  apply measurableSet_lt _ measurable_const
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))

lemma stripe_lift_preimage {V : ℝ} (hV : V ∈ Icc 0 1) :
    (WithLp.toLp 2 : (Fin 3 → ℝ) → Cover) ⁻¹'
      (fundamentalCube ∩ quotientMap ⁻¹' stripe V) =
      univ.pi (fun i : Fin 3 => Ico 0 (stripeUpper V i)) := by
  ext x
  change ((∀ i, 0 ≤ x i ∧ x i < 1) ∧
    ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) < V) ↔ _
  constructor
  · rintro ⟨hc, hs⟩ i _
    have he : ((AddCircle.equivIco (1 : ℝ) 0) (x 0 : AddCircle (1 : ℝ)) : ℝ) = x 0 :=
      AddCircle.equivIco_coe_of_mem (by simpa using hc 0)
    rw [he] at hs
    by_cases hi : i = 0
    · subst i
      simpa [stripeUpper] using And.intro (hc 0).1 hs
    · simpa [stripeUpper, hi] using hc i
  · intro hx
    have hc : ∀ i, 0 ≤ x i ∧ x i < 1 := by
      intro i
      have hh := hx i (mem_univ i)
      by_cases hi : i = 0
      · subst i
        simp only [stripeUpper, Function.update_self, mem_Ico] at hh
        exact ⟨hh.1, lt_of_lt_of_le hh.2 hV.2⟩
      · simpa [stripeUpper, hi] using hh
    refine ⟨hc, ?_⟩
    rw [AddCircle.equivIco_coe_of_mem (by simpa using hc 0)]
    simpa [stripeUpper] using (hx 0 (mem_univ 0)).2

lemma volume_stripe {V : ℝ} (hV : V ∈ Icc 0 1) :
    torusVolume (stripe V) = ENNReal.ofReal V := by
  rw [torusVolume, Measure.map_apply measurable_quotientMap (measurableSet_stripe V),
    Measure.restrict_apply (measurable_quotientMap (measurableSet_stripe V)), inter_comm]
  have hm := (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    ((measurableSet_fundamentalCube.inter (measurable_quotientMap (measurableSet_stripe V))).nullMeasurableSet)
  rw [stripe_lift_preimage hV] at hm
  rw [← hm, Real.volume_pi_Ico]
  norm_num [stripeUpper, Fin.prod_univ_succ]

lemma integral_divergence_stripe {V : ℝ} (hV : V ∈ Icc 0 1)
    {F : Cover → Cover} (hF : AdmissibleField F) :
    (∫ x in fundamentalCube ∩ quotientMap ⁻¹' stripe V, divergence F x) =
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
        F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let b := stripeUpper V
  let g : Fin 3 → (Fin 3 → ℝ) → ℝ := fun i x => F (e.symm x) i
  let dg : Fin 3 → (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ :=
    fun i x => (EuclideanSpace.proj i).comp
      ((fderiv ℝ F (e.symm x)).comp e.symm.toContinuousLinearMap)
  have hdg : ∀ i x, HasFDerivAt (g i) (dg i x) x := by
    intro i x
    exact (EuclideanSpace.proj i).hasFDerivAt.comp x
      (((hF.1.differentiable (by simp)) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt)
  have hd : (fun x => ∑ i : Fin 3, dg i x (Pi.single i 1)) =
      fun x => divergence F (e.symm x) := by
    funext x
    simp [dg, divergence, e, PiLp.toLp_single]
  have hct : Continuous (fun x => divergence F (e.symm x)) :=
    (continuous_divergence hF.1).comp e.symm.continuous
  have hb : ∀ i, (0 : Fin 3 → ℝ) i ≤ b i := by
    intro i
    by_cases hi : i = 0
    · subst i; simpa [b, stripeUpper] using hV.1
    · simp [b, stripeUpper, hi]
  have hth := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Fin 3 → ℝ) b hb g dg ∅ countable_empty
    (fun i => ((EuclideanSpace.proj i).continuous.comp
      (hF.1.continuous.comp e.symm.continuous)).continuousOn)
    (fun x _ i => hdg i x) (by rw [hd]; exact hct.integrableOn_Icc)
  rw [hd] at hth
  have hzero : ∀ i : Fin 3, i ≠ 0 →
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth (b i) x)) -
      (∫ x in Icc ((0 : Fin 3 → ℝ) ∘ i.succAbove) (b ∘ i.succAbove),
        g i (i.insertNth 0 x)) = 0 := by
    intro i hi
    have heq : (fun x : Fin 2 → ℝ => g i (i.insertNth (b i) x)) =
        (fun x : Fin 2 → ℝ => g i (i.insertNth 0 x)) := by
      funext x
      have hbi : b i = 1 := by simp [b, stripeUpper, hi]
      rw [hbi]
      change F (WithLp.toLp 2 (i.insertNth 1 x)) i = F (WithLp.toLp 2 (i.insertNth 0 x)) i
      rw [adjacent_faces, hF.2.1]
    rw [heq, sub_self]
  simp only [Pi.zero_apply] at hth
  rw [Finset.sum_eq_single 0 (fun i _ hi => hzero i hi) (by simp)] at hth
  have hab : b ∘ (0 : Fin 3).succAbove = (1 : Fin 2 → ℝ) := by
    ext i
    simp [b, stripeUpper]
  have ha0 : (0 : Fin 3 → ℝ) ∘ (0 : Fin 3).succAbove = (0 : Fin 2 → ℝ) := rfl
  rw [hab, ha0] at hth
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.symm.toHomeomorph.measurableEmbedding, stripe_lift_preimage hV]
  rw [volume_pi, setIntegral_congr_set Measure.univ_pi_Ico_ae_eq_Icc]
  rw [← volume_pi]
  convert hth using 1 <;> simp [g, b, stripeUpper, e]
  rfl

end CubicTorus

namespace CubicTorus

lemma volume_square_face : volume (Icc (0 : Fin 2 → ℝ) 1) = 1 := by
  rw [Real.volume_Icc_pi]
  norm_num

lemma stripe_flux_bound {F : Cover → Cover} (hF : AdmissibleField F) (a : ℝ) :
    |∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x)) 0| ≤ 1 := by
  have hh := norm_setIntegral_le_of_norm_le_const
    (show volume (Icc (0 : Fin 2 → ℝ) 1) < ⊤ by rw [volume_square_face]; norm_num)
    (fun x (_ : x ∈ Icc (0 : Fin 2 → ℝ) 1) =>
      (PiLp.norm_apply_le (F (WithLp.toLp 2 ((0 : Fin 3).insertNth a x))) 0).trans (hF.2.2 _))
  simpa only [Real.norm_eq_abs, Measure.real, volume_square_face, ENNReal.toReal_one, mul_one] using hh

theorem perimeter_stripe_le {V : ℝ} (hV : V ∈ Icc 0 1) : perimeter (stripe V) ≤ 2 := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  rw [integral_divergence_stripe hV hF]
  have hupper := (abs_le.1 (stripe_flux_bound hF V)).2
  have hlower := (abs_le.1 (stripe_flux_bound hF 0)).1
  have hh : (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth V x)) 0) -
      (∫ x in Icc (0 : Fin 2 → ℝ) 1,
      F (WithLp.toLp 2 ((0 : Fin 3).insertNth 0 x)) 0) ≤ 2 := by linarith
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by norm_num)

theorem finitePerimeter_stripe {V : ℝ} (hV : V ∈ Icc 0 1) : FinitePerimeter (stripe V) :=
  ⟨(measurableSet_stripe V).nullMeasurableSet, (perimeter_stripe_le hV).trans_lt (by norm_num)⟩

end CubicTorus

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_GradientCalibration
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant _root_.OAI.CubicTorus.supportedMeasure_finite _root_.OAI.CubicTorus.torus_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CubicTorus
open scoped RealInnerProductSpace

lemma normalMeasure_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ n x, F (x + latticeVector n) = F x)
    {k : ℝ} (hk : 0 < k) (hb : ∀ x, ‖F x‖ ≤ k) :
    (∫ z, normalTest F hF.continuous z ∂(μ : Measure NormalBundle)) =
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' E, divergence F x := by
  have hG : AdmissibleField (fun x ↦ k⁻¹ • F x) := by
    refine ⟨hF.const_smul (k⁻¹ : ℝ), ?_, ?_⟩
    · intro n x
      change k⁻¹ • F (x + latticeVector n) = k⁻¹ • F x
      rw [hp]
    · intro x
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
      exact (mul_le_mul_of_nonneg_left (hb x) (inv_nonneg.mpr hk.le)).trans_eq
        (inv_mul_cancel₀ hk.ne')
  have hh := hμ.2 _ hG
  simp only [normalTest, ContinuousMap.coe_mk, real_inner_smul_right,
    integral_const_mul] at hh ⊢
  simp_rw [divergence_const_smul (hF.differentiable (by simp)).differentiableAt,
    integral_const_mul] at hh
  exact mul_left_cancel₀ (inv_ne_zero hk.ne') hh

end CubicTorus

open scoped RealInnerProductSpace

end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Variation_ComponentDivergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cover_decompose (v : Cover) : v=∑ i : Fin 3,v i • EuclideanSpace.single i 1 := by
  ext j
  simp [Pi.single_apply]

lemma coverTrace_smulRight (l : Cover →L[ℝ] ℝ) (v : Cover) :
    coverTrace (l.smulRight v)=l v := by
  conv_rhs => rw [cover_decompose v]
  simp only [coverTrace,ContinuousLinearMap.smulRight_apply,PiLp.smul_apply,
    smul_eq_mul,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TranslateNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cofactorLinear_inner (L : Cover →L[ℝ] Cover) {n : Cover} (hn : ‖n‖=1) :
    ⟪n,cofactorLinear L n⟫=coverTrace L-⟪n,L n⟫ := by
  simp only [cofactorLinear,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hn,one_pow,mul_one,ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm]

lemma cofactorLinear_coordinate {f : Cover → ℝ} {point : Cover}
    (hf : DifferentiableAt ℝ f point)
    (i : Fin 3) (n : Cover) :
    cofactorLinear (fderiv ℝ (fun y ↦ f y • EuclideanSpace.single i 1) point) n=
      coordinateNormalVelocity i f point n := by
  rw [fderiv_smul_const hf]
  have ha : ((fderiv ℝ f point).smulRight (EuclideanSpace.single i (1 : ℝ))).adjoint n=
      ⟪n,EuclideanSpace.single i 1⟫ • gradient f point := by
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.smulRight_apply,
      real_inner_smul_right,real_inner_smul_left,inner_gradient_left]
    ring
  simp only [cofactorLinear,coverTrace_smulRight,ha,coordinateNormalVelocity]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma variationField_smooth (a : Variation) : ContDiff ℝ (⊤ : ℕ∞) (variationField a) :=
  a.smooth.smul contDiff_const

lemma variationField_periodic (a : Variation) (m : Fin 3 → ℤ) (x : Cover) :
    variationField a (x+latticeVector m)=variationField a x := by
  simp only [variationField,a.periodic]

end Periodic
end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_ChainAcceleration
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_normal_flux {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x := by
  obtain ⟨C,_,hb⟩ := periodic_bounded hF.continuous hp
  have hc : 0<C+‖F 0‖+1 := by linarith [hb 0,norm_nonneg (F 0)]
  exact normalMeasure_flux hμ hF hp hc
    (fun x ↦ (hb x).trans (by linarith [norm_nonneg (F 0)] : C≤C+‖F 0‖+1))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_LatticeHeightHom
attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

lemma coordinateCMC_of_global {E : Set Torus} {μ : FiniteMeasure NormalBundle}
    (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (b : Variation) : normalFirstVariation μ b=H*directionalFlux E b.coordinate b.function := by
  have he := hCMC (variationField b) (variationField_smooth b) (variationField_periodic b)
  rw [periodic_normal_flux hμ (variationField_smooth b) (variationField_periodic b)] at he
  have hleft : normalFirstVariation μ b=
      ∫ z,tangentialDivergence (variationField b) z.1 z.2 ∂(μ : Measure NormalBundle) := by
    apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      change ⟪(z.2 : Cover),coordinateNormalVelocity b.coordinate b.function z.1 z.2⟫=_
      rw [← cofactorLinear_coordinate (b.smooth.differentiable (by simp) z.1),
        cofactorLinear_inner _ z.2.property]
      rfl
  rw [hleft,he]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ divergence_smul_const (b.smooth.differentiable (by simp) x) _

end Periodic
end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SectionExtentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Shape

lemma positive_quadratic_root {a : ℝ} (ha : 0 < a) :
    let r := 2 / (1 + Real.sqrt (1 + 4 * a / Real.pi))
    0 < r ∧ r < 1 ∧ a * r ^ 2 = Real.pi * (1 - r) := by
  have hp := Real.pi_pos
  have hr : 1 < 1 + 4 * a / Real.pi := by
    have : 0 < 4 * a / Real.pi := by positivity
    linarith
  have hs0 := Real.sqrt_nonneg (1 + 4 * a / Real.pi)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * a / Real.pi)
  have hs1 : 1 < Real.sqrt (1 + 4 * a / Real.pi) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 4 * a / Real.pi) := by linarith
  refine ⟨div_pos (by norm_num) hd, (div_lt_one hd).2 (by linarith), ?_⟩
  generalize hz : Real.sqrt (1 + 4 * a / Real.pi) = z at *
  field_simp at hs ⊢
  nlinarith

lemma t_spec {h : ℝ} (hh : 0 < h) :
    0 < t h ∧ t h < 1 ∧ h ^ 2 * t h ^ 2 = Real.pi * (1 - t h) := by
  exact positive_quadratic_root (sq_pos_of_pos hh)

end CubicTorus.Shape
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingEndpointBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma source_root_le_of_bottom {h s : ℝ} (hh : 0<h) (hs : 0 ≤ s)
    (hdisc : Real.pi*(1-s)≤(h*s)^2) : Shape.t h ≤ s := by
  have ht := Shape.t_spec hh
  by_contra hn
  have hst : s<Shape.t h := lt_of_not_ge hn
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hst.le 2) (sq_nonneg h)
  have hp := mul_lt_mul_of_pos_left hst Real.pi_pos
  nlinarith [ht.2.2]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingBaseline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set
namespace CubicTorus

private lemma phi_deriv (s : ℝ) : HasDerivAt phi (s*(1+s)*(2+s-5*s^2)) s := by
  have hh := (((hasDerivAt_id s).pow 2).mul ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))).mul
    (((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_id s)).pow 2)
  convert hh using 1 <;> first | rfl | (dsimp [phi]; ring)

private lemma phi_mono : MonotoneOn phi (Icc 0 (107/200)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (by unfold phi; fun_prop) (fun s _ ↦ (phi_deriv s).hasDerivWithinAt) ?_
  intro s hs
  have hs' : s∈Icc (0 : ℝ) (107/200) := interior_subset hs
  have hsq := pow_le_pow_left₀ hs'.1 hs'.2 2
  exact mul_nonneg (mul_nonneg hs'.1 (by linarith [hs'.1])) (by nlinarith)

private lemma phi_anti : AntitoneOn phi (Icc (89/100) 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (by unfold phi; fun_prop) (fun s _ ↦ (phi_deriv s).hasDerivWithinAt) ?_
  intro s hs
  have hs' : s∈Icc (89/100 : ℝ) 1 := interior_subset hs
  have hs0 : 0 ≤ s := by linarith [hs'.1]
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 89/100) hs'.1 2
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs0 (by linarith)) (by nlinarith)

theorem three_vertex_parameter_algebra {h s A : ℝ}
    (hs : 0 < s) (hh : 0<h) (hA : A∈Icc 0 1)
    (hdisc : Real.pi*(1-s) ≤ (h*s)^2)
    (hproj : s^2 ≤ A*(A-h/Real.pi)) :
    Real.sqrt (Real.pi*(1-s))/s ≤ h ∧ h ≤ Real.pi*(1-s^2) ∧
    s∈Ioo (107/200 : ℝ) (89/100 : ℝ) ∧ h∈Icc (16/25 : ℝ) (9/4 : ℝ) ∧ Shape.t h ≤ s := by
  have hp : 0<Real.pi := Real.pi_pos
  have hApos : 0<A := by
    by_contra hn
    have hz : A=0 := le_antisymm (le_of_not_gt hn) hA.1
    rw [hz,zero_mul] at hproj
    nlinarith
  have hdif : 0 ≤ A-h/Real.pi := by
    by_contra hn
    have hneg := mul_neg_of_pos_of_neg hApos (lt_of_not_ge hn)
    nlinarith [sq_nonneg s]
  have hup1 := hproj.trans (mul_le_of_le_one_left hdif hA.2)
  have hup : h ≤ Real.pi*(1-s^2) := by
    have hquot : h/Real.pi ≤ 1-s^2 := by linarith [hA.2]
    have hmul := (div_le_iff₀ hp).mp hquot
    nlinarith
  have hs1 : s<1 := by
    by_contra hn
    have hss : 1 ≤ s^2 := by nlinarith
    have hh' := mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr hss)
    linarith
  have hsqrt : Real.sqrt (Real.pi*(1-s)) ≤ h*s := (Real.sqrt_le_iff).mpr ⟨by positivity,hdisc⟩
  have hlo : Real.sqrt (Real.pi*(1-s))/s ≤ h := (div_le_iff₀ hs).mpr hsqrt
  have hue0 : 0 ≤ Real.pi*(1-s^2) := hh.le.trans hup
  have hsq := pow_le_pow_left₀ hh.le hup 2
  have hsq' := mul_le_mul_of_nonneg_right hsq (sq_nonneg s)
  have hexpand : (Real.pi*(1-s^2))^2*s^2-Real.pi*(1-s)=
      Real.pi*(1-s)*(Real.pi*phi s-1) := by unfold phi; ring
  have hmulnonneg : 0 ≤ Real.pi*(1-s)*(Real.pi*phi s-1) := by rw [←hexpand]; nlinarith
  have hph : 1 ≤ Real.pi*phi s := by
    have hh' := nonneg_of_mul_nonneg_right hmulnonneg (mul_pos hp (sub_pos.mpr hs1))
    linarith
  have hpiU : Real.pi < (22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hslo : (107/200 : ℝ) < s := by
    by_contra hn
    have hss : s ≤ (107/200 : ℝ) := le_of_not_gt hn
    have hmon := phi_mono ⟨hs.le,hss⟩ (by constructor <;> norm_num) hss
    have hbound := (mul_le_mul_of_nonneg_left hmon hp.le)
    have hstrict := mul_lt_mul_of_pos_right hpiU (show 0<phi (107/200) by norm_num [phi])
    have hpval : phi (107/200)=(100352282493/320000000000 : ℝ) := by norm_num [phi]
    rw [hpval] at hbound hstrict
    norm_num at hstrict
    linarith
  have hshi : s<(89/100 : ℝ) := by
    by_contra hn
    have hss : (89/100 : ℝ) ≤ s := le_of_not_gt hn
    have hmon := phi_anti (by constructor <;> norm_num) ⟨hss,hs1.le⟩ hss
    have hbound := mul_le_mul_of_nonneg_left hmon hp.le
    have hstrict := mul_lt_mul_of_pos_right hpiU (show 0<phi (89/100) by norm_num [phi])
    have hpval : phi (89/100)=(3112406451/10000000000 : ℝ) := by norm_num [phi]
    rw [hpval] at hbound hstrict
    norm_num at hstrict
    linarith
  have hhlo : (16/25 : ℝ) ≤ h := by
    by_contra hn
    have hh' : h<(16/25 : ℝ) := lt_of_not_ge hn
    have hhs : h*s < (16/25 : ℝ)*(89/100) := (mul_lt_mul_of_pos_right hh' hs).trans_le (mul_le_mul_of_nonneg_left hshi.le (by norm_num))
    have hsqb := pow_le_pow_left₀ (mul_nonneg hh.le hs.le) hhs.le 2
    have hpiL := Real.pi_gt_three
    have hdlo := (mul_lt_mul_of_pos_right hpiL (sub_pos.mpr hs1))
    have h33 : (33/100 : ℝ)<3*(1-s) := by linarith
    nlinarith
  have hsup2 : 1-s^2 < 1-(107/200 : ℝ)^2 := by nlinarith [mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 107/200) hslo]
  have hhhi : h ≤ (9/4 : ℝ) := by
    have hss0 : 0 ≤ 1-s^2 := (nonneg_of_mul_nonneg_right hue0 hp)
    have hcomp := (mul_le_mul_of_nonneg_right hpiU.le hss0).trans_lt
      (mul_lt_mul_of_pos_left hsup2 (by norm_num : (0 : ℝ)<22/7))
    nlinarith
  exact ⟨hlo,hup,⟨hslo,hshi⟩,⟨hhlo,hhhi⟩,source_root_le_of_bottom hh hs.le hdisc⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_perimeter_half_le_one {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) : (perimeter E).toReal/2 ≤ 1 := by
  have hupper : perimeter E ≤ 2 :=
    (hmin.2.2 (stripe V) (finitePerimeter_stripe ⟨hV.1.le,hV.2.le⟩)
      (volume_stripe ⟨hV.1.le,hV.2.le⟩)).trans (perimeter_stripe_le ⟨hV.1.le,hV.2.le⟩)
  have hup : (perimeter E).toReal ≤ 2 := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞)≠⊤) hupper
  linarith

theorem isMinimizerAt_three_vertex_parameters_oai {E : Set Torus}
    (hE : MeasurableSet E) (hmin : IsMinimizerAt (1/Real.pi) E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (haxes : ∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    (perimeter E).toReal/2 ≤ 1 ∧
    Real.sqrt (Real.pi*(1-s))/s ≤ H/2 ∧ H/2 ≤ Real.pi*(1-s^2) ∧
    s∈Ioo (107/200 : ℝ) (89/100 : ℝ) ∧ H/2∈Icc (16/25 : ℝ) (9/4 : ℝ) ∧ Shape.t (H/2) ≤ s := by
  dsimp only
  have hV : (1/Real.pi)∈Ioo (0 : ℝ) 1 := ⟨by positivity,(div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  obtain ⟨hout,hin⟩ := isMinimizerAt_three_vertex_bottom hV hmin hc hR b hd i hv haxes
  obtain ⟨hHs,hdisc,_⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout (hin 0) (hin 1)
  have hproj := isMinimizerAt_missing_neighbor_projection hV hE hmin hR b hd hμ (Periodic.coordinateCMC_of_global hμ hCMC) i ha hv
  let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hs : 0 < s := by
    change 0<H*s at hHs
    by_contra hn
    have hz : s=0 := le_antisymm (le_of_not_gt hn) hs0
    simp [hz] at hHs
  have hH : 0<H/2 := by
    change 0<H*s at hHs
    have hh : 0<H := (mul_pos_iff.mp hHs).resolve_right (fun hn ↦ (not_lt_of_ge hs0) hn.2) |>.1
    linarith
  have hA := isMinimizerAt_perimeter_half_le_one hV hmin
  have heq : (H/2)*(1/Real.pi)=(H/2)/Real.pi := by ring
  rw [heq] at hproj
  exact ⟨hA,three_vertex_parameter_algebra hs hH ⟨by positivity,hA⟩ hdisc hproj⟩

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.isMinimizerAt_three_vertex_parameters_oai := @OAI.CubicTorus.isMinimizerAt_three_vertex_parameters_oai

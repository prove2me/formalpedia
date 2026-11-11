-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:41.227666+00:00
-- url     : https://prove2.me/submissions/6df369a8-963f-4c6d-8db3-ba98f60f62a3

import Mathlib
import Definitions.Def_TamingCompatibility
import Definitions.Def_OAIQ239Tc021
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_normalDensity_smooth
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledA_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_GeometricNormalCharts_pulledB_joint
import Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_NormalMetricCalculus_volumeDensity_pos

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

lemma J_inner (u v : V) : ⟪J u, J v⟫ = ⟪u, v⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, J]
  ring

lemma inner_self_J (v : V) : ⟪v, J v⟫ = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, J]
  ring

lemma wedge_inner (u v a b : V) :
    ⟪wedge u v, wedge a b⟫ = ⟪u, a⟫ * ⟪v, b⟫ - ⟪u, b⟫ * ⟪v, a⟫ := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, wedge]
  ring

lemma line_norm_sq (v : V) : ‖line v‖ ^ 2 = (‖v‖ ^ 2) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, line, wedge_inner, J_inner, inner_self_J,
    zero_mul, sub_zero, real_inner_self_eq_norm_sq]
  ring

lemma unit_line_norm {v : V} (hv : ‖v‖ = 1) : ‖line v‖ = 1 := by
  have hs := line_norm_sq v
  rw [hv] at hs
  nlinarith [norm_nonneg (line v)]

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_HermitianCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma pullback_complexLine (J : AlmostComplexStructure X) (β : TwoForm X) (p : X)
    {y : Space} (hy : y ∈ (extChartAt Model p).target) (v : Space) :
    ManifoldForms.pullback β (extChartAt Model p).symm y ![v,coordinateJ J p y v] =
      eval β ((extChartAt Model p).symm y) (mfderiv Model Model (extChartAt Model p).symm y v)
        (J.endomorphism _ (mfderiv Model Model (extChartAt Model p).symm y v)) := by
  have hi := coordinateJ_intertwine J p hy v
  change (inverseChartEquiv p y hy).toContinuousLinearMap (coordinateJ J p y v) =
    J.endomorphism _ ((inverseChartEquiv p y hy).toContinuousLinearMap v) at hi
  rw [inverseChartEquiv_coe] at hi
  change β _ ((mfderiv Model Model (extChartAt Model p).symm y) ∘ ![v,coordinateJ J p y v]) = _
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact hi

end TamingCompatibility.GeometricChart

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDirectionCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma alternating_swap (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u v : E) :
    a ![v,u] = -a ![u,v] := by
  have hv : ![u,v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v,u] := by
    ext i
    fin_cases i <;> simp
  simpa only [hv, ContinuousAlternatingMap.coe_toAlternatingMap] using
    a.map_swap ![u,v] (by decide : (0 : Fin 2) ≠ 1)

lemma alternating_sum_left {ι : Type*} (a : E [⋀^Fin 2]→L[ℝ] ℝ)
    (s : Finset ι) (f : ι → E) (v : E) :
    a ![∑ i ∈ s, f i, v] = ∑ i ∈ s, a ![f i,v] := by
  have hu (w : E) : Function.update ![0,v] (0 : Fin 2) w = ![w,v] := by
    ext i
    fin_cases i <;> simp
  simpa only [hu,ContinuousAlternatingMap.coe_toAlternatingMap] using
    a.toAlternatingMap.map_update_sum s 0 f ![0,v]

lemma alternating_smul_left (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![c • u,v] = c * a ![u,v] := by
  simpa only [smul_eq_mul] using a.vecCons_smul ![v] c u

lemma alternating_sum_right {ι : Type*} (a : E [⋀^Fin 2]→L[ℝ] ℝ)
    (s : Finset ι) (f : ι → E) (u : E) :
    a ![u, ∑ i ∈ s, f i] = ∑ i ∈ s, a ![u,f i] := by
  rw [alternating_swap,alternating_sum_left,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [alternating_swap,neg_neg]

lemma alternating_smul_right (a : E [⋀^Fin 2]→L[ℝ] ℝ) (c : ℝ) (u v : E) :
    a ![u,c • v] = c * a ![u,v] := by
  rw [alternating_swap,alternating_smul_left,alternating_swap]
  ring

lemma alternating_self (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) : a ![u,u] = 0 :=
  a.map_eq_zero_of_eq ![u,u] (i := 0) (j := 1) rfl (by decide : (0 : Fin 2) ≠ 1)

lemma alternating_frame_eval (a : E [⋀^Fin 2]→L[ℝ] ℝ) (b : Fin 4 → E) (v w : V) :
    a ![∑ i : Fin 4, v i • b i, ∑ i : Fin 4, w i • b i] =
      ⟪WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
        a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]], wedge v w⟫ := by
  rw [alternating_sum_left]
  simp_rw [alternating_sum_right,alternating_smul_left,alternating_smul_right]
  simp [Fin.sum_univ_succ,alternating_self,wedge,
    EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  rw [alternating_swap a (b 0) (b 1),alternating_swap a (b 0) (b 2),
    alternating_swap a (b 0) (b 3),alternating_swap a (b 1) (b 2),
    alternating_swap a (b 1) (b 3),alternating_swap a (b 2) (b 3)]
  ring

end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma sum_directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E) :
    ∑ i : Fin 4, directionCoordinates g hdim b hb u i • b i = u := by
  have h := congrArg (equiv g) ((basisOfFrame g hdim b hb).sum_repr (ofOriginal g u))
  have he (x : E) : equiv g (ofOriginal g x) = x := rfl
  simpa only [map_sum,map_smul,basisOfFrame_apply,he,directionCoordinates] using h

lemma norm_directionCoordinates (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) (u : E)
    (hu : g.bilinear u u = 1) : ‖directionCoordinates g hdim b hb u‖ = 1 := by
  rw [directionCoordinates,LinearIsometryEquiv.norm_map]
  have h : ‖ofOriginal g u‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hu
  nlinarith [norm_nonneg (ofOriginal g u)]

omit [FiniteDimensional ℝ E] in
lemma complex_frame_sum (b : Fin 4 → E) (j : E →L[ℝ] E)
    (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2) (v : UnitaryFrame.V) :
    j (∑ i : Fin 4, v i • b i) = ∑ i : Fin 4, UnitaryFrame.J v i • b i := by
  simp [Fin.sum_univ_succ,UnitaryFrame.J,h0,h1,h2,h3]
  abel

lemma directionCoordinates_eval (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (j : E →L[ℝ] E) (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2)
    (a : E [⋀^Fin 2]→L[ℝ] ℝ) (u : E) :
    a ![u,j u] =
      ⟪WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
        a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]],
        UnitaryFrame.line (directionCoordinates g hdim b hb u)⟫ := by
  let v := directionCoordinates g hdim b hb u
  have hv : ∑ i : Fin 4, v i • b i = u := sum_directionCoordinates g hdim b hb u
  have hw : ∑ i : Fin 4, UnitaryFrame.J v i • b i = j u := by
    rw [← complex_frame_sum b j h0 h1 h2 h3,hv]
  calc
    _ = a ![∑ i : Fin 4, v i • b i, ∑ i : Fin 4, UnitaryFrame.J v i • b i] := by rw [hv,hw]
    _ = _ := UnitaryFrame.alternating_frame_eval a b v (UnitaryFrame.J v)

end TamingCompatibility.HodgeFrame

namespace TamingCompatibility.HodgeFrame
open MetricModel MetricForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma coordinates_eq_six (b : Fin 4 → E) (a : MetricForms.Form E 2) :
    coordinates b a = WithLp.toLp 2 ![a ![b 0,b 1],a ![b 0,b 2],a ![b 0,b 3],
      a ![b 1,b 2],a ![b 1,b 3],a ![b 2,b 3]] := by
  ext i
  fin_cases i <;> rfl

variable [FiniteDimensional ℝ E]
lemma coordinates_direction_eval (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (j : E →L[ℝ] E) (h0 : j (b 0) = b 1) (h1 : j (b 1) = -b 0)
    (h2 : j (b 2) = b 3) (h3 : j (b 3) = -b 2)
    (a : MetricForms.Form E 2) (u : E) :
    a ![u,j u] = ⟪coordinates b a,UnitaryFrame.line (directionCoordinates g hdim b hb u)⟫ := by
  rw [coordinates_eq_six]
  exact directionCoordinates_eval g hdim b hb j h0 h1 h2 h3 a u
end TamingCompatibility.HodgeFrame

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WedgeTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.UnitaryFrame
open FormMetric

lemma wedgeTransform_apply (b : Fin 4 → V) (w : W) :
    wedgeTransform b w = ∑ i : Fin 6, w i • wedge (b (pairLeft i)) (b (pairRight i)) := by
  simp [wedgeTransform]

lemma wedgeTransform_wedge (b : Fin 4 → V) (u v : V) :
    wedgeTransform b (wedge u v) =
      wedge (∑ i : Fin 4, u i • b i) (∑ i : Fin 4, v i • b i) := by
  rw [wedgeTransform_apply]
  ext i
  fin_cases i <;> simp [wedge,pairLeft,pairRight,Fin.sum_univ_succ] <;> ring

lemma wedge_smul_left (c : ℝ) (u v : V) : wedge (c • u) v = c • wedge u v := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma wedge_smul_right (c : ℝ) (u v : V) : wedge u (c • v) = c • wedge u v := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma wedge_sub_right (u v w : V) : wedge u (v-w) = wedge u v - wedge u w := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma wedge_self (u : V) : wedge u u = 0 := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma norm_wedge_orthonormal (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖wedge u v‖ = 1 := by
  have h := wedge_inner u v u v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hu,hv,huv,zero_mul,sub_zero,one_pow,mul_one] at h
  nlinarith [norm_nonneg (wedge u v)]

lemma wedge_normalized (a b : V) (_ha : a ≠ 0) :
    wedge (PlaneVariation.first a) (PlaneVariation.second a b) =
      (PlaneVariation.area a b)⁻¹ • wedge a b := by
  simp only [PlaneVariation.first,PlaneVariation.second,PlaneVariation.normalPart,
    PlaneVariation.area,wedge_smul_left,wedge_smul_right,wedge_sub_right,wedge_self,
    smul_zero,sub_zero,smul_smul,mul_inv_rev]

lemma norm_wedge_area (a b : V) (ha : a ≠ 0) (hab : PlaneVariation.normalPart a b ≠ 0) :
    ‖wedge a b‖ = PlaneVariation.area a b := by
  have hh := norm_wedge_orthonormal _ _ (PlaneVariation.norm_first ha)
    (PlaneVariation.norm_second hab) (PlaneVariation.first_second_orthogonal ha b)
  rw [wedge_normalized a b ha,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_pos (PlaneVariation.area_pos ha hab)] at hh
  exact ((inv_mul_eq_one₀ (ne_of_gt (PlaneVariation.area_pos ha hab))).mp hh).symm

lemma wedge_contDiff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : WithTop ℕ∞} {u v : D → V} (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (fun x => wedge (u x) (v x)) := by
  apply (contDiff_piLp _).mpr
  intro i
  have huc (j : Fin 4) := (contDiff_piLp _).mp hu j
  have hvc (j : Fin 4) := (contDiff_piLp _).mp hv j
  fin_cases i <;> simp [wedge] <;> fun_prop

lemma wedgeTransform_contDiff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : WithTop ℕ∞} {b : Fin 4 → D → V} (hb : ∀ i, ContDiff ℝ n (b i)) :
    ContDiff ℝ n (fun z => wedgeTransform (fun i => b i z)) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smulRight (wedge_contDiff (hb _) (hb _))

end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma first_lipschitz_bound {a b : V} {m : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖) (hb : b ≠ 0) :
    ‖first a-first b‖ ≤ (2/m)*‖a-b‖ := by
  have han : 0 < ‖a‖ := lt_of_lt_of_le hm ha
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have he : first a-first b = ‖a‖⁻¹ • (a-b) + (‖a‖⁻¹-‖b‖⁻¹) • b := by
    simp only [first,smul_sub,sub_smul]
    abel
  have hc : |‖a‖⁻¹-‖b‖⁻¹| * ‖b‖ = |‖b‖-‖a‖|/‖a‖ := by
    rw [inv_sub_inv han.ne' hbn.ne',abs_div,abs_mul,abs_of_pos han,abs_of_pos hbn]
    field_simp
  calc
    _ ≤ ‖‖a‖⁻¹ • (a-b)‖+‖(‖a‖⁻¹-‖b‖⁻¹) • b‖ := by rw [he]; exact norm_add_le _ _
    _ = (‖a-b‖+|‖b‖-‖a‖|)/‖a‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,hc]
      ring
    _ ≤ (2*‖a-b‖)/‖a‖ := by
      apply div_le_div_of_nonneg_right _ han.le
      have hh := abs_norm_sub_norm_le a b
      rw [abs_sub_comm] at hh
      linarith
    _ ≤ _ := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hm ha
end TamingCompatibility.PlaneVariation

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Dpos2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.UniformJets

open Filter
open scoped ContDiff Topology
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma slice_fderiv_contDiffAt (F : P × V → W) {x : P × V}
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (fun y : P × V => fderiv ℝ (fun z => F (y.1,z)) y.2) x := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    ((hF.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by norm_num)).mono
      fun y hy => hy.differentiableAt (by norm_num)
  apply (dpos_contDiffAt F x hF).congr_of_eventuallyEq
  filter_upwards [hd] with y hy
  exact (dpos_eq_at F y.1 y.2 hy).symm

end TamingCompatibility.GeometricHilbert.UniformJets

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FirstMatrixJoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus

section MatrixFamilies
open UniformJets
open scoped ContDiff
variable {P V W Q ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma firstMatrix_joint (e : ι → V) (a : ι → P × V → W →L[ℝ] Q)
    (b : P × V → W →L[ℝ] Q) (ρ : P × V → ℝ) {x : P × V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hρx : ρ x ≠ 0) (j : ι) :
    ContDiffAt ℝ ∞ (fun y : P × V => firstMatrix e (fun i z => a i (y.1,z))
      (fun z => b (y.1,z)) (fun z => ρ (y.1,z)) j y.2) x := by
  let S : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hp (i : ι) : ContDiffAt ℝ ∞ (fun y : P × V =>
      principalMatrix (fun k z => a k (y.1,z)) (fun z => ρ (y.1,z)) i j y.2) x :=
    (S.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_comp (ha j)
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    (slice_fderiv_contDiffAt _ (hp i)).clm_apply (contDiffAt_const (c := e i)))
  exact (((hρ.inv hρx).neg.smul hsum).add
    ((S.contDiff.contDiffAt.comp x hb).clm_comp (ha j))).sub
      ((S.contDiff.contDiffAt.comp x (ha j)).clm_comp hb)

end MatrixFamilies
open UniformJets FirstJetGauge OrthogonalJets
open scoped ContDiff
variable {P V W ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W] [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

lemma gauge_joint (q : ι → V →L[ℝ] ℝ) (b : ι → P → W →L[ℝ] W)
    {x : P × V} (hb : ∀ i, ContDiffAt ℝ ∞ (b i) x.1) :
    ContDiffAt ℝ ∞ (fun y : P × V => gauge (halfJet q (fun i => b i y.1)) y.2) x := by
  have he : ContDiffAt ℝ ∞ (NormedSpace.exp : (W →L[ℝ] W) → (W →L[ℝ] W))
      (halfJet q (fun i => b i x.1) x.2) := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  apply he.comp x
  simp only [halfJet, sum_apply, ContinuousLinearMap.smulRight_apply]
  exact ContDiffAt.sum fun i _ =>
    ((q i).contDiff.contDiffAt.comp x contDiffAt_snd).smul
      (((hb i).comp x contDiffAt_fst).const_smul (1/2 : ℝ))

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_4
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_4
lemma normalFirst_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : x ∈ normalDomain J α ht p D g B) (j : Fin 4) :
    ContDiffAt ℝ ∞ (normalFirst J α ht p D g B j) x :=
  firstMatrix_joint EuclideanEnergy.e (fun i y => pulledA J α ht p D g B y.1 i y.2)
    (fun y => pulledB J α ht p D g B y.1 y.2) (normalDensity g B)
    (pulledA_joint J α ht p D g B hg hB hx.1)
    (pulledB_joint J α hs ht p D g B hg hB hx.1)
    (normalDensity_smooth g B hg hB hx.2) (ne_of_gt (volumeDensity_pos hx.2)) j

attribute [local irreducible] normalFirst

lemma normalGauge_smooth (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {x : Space × Space} (hx : (x.1,0) ∈ normalDomain J α ht p D g B) :
    ContDiffAt ℝ ∞ (normalGauge J α ht p D g B) x := by
  have hc : ContDiffAt ℝ ∞ (fun q : Space => (q,(0 : Space))) x.1 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hf (i : Fin 4) : ContDiffAt ℝ ∞
      (fun q : Space => normalFirst J α ht p D g B i (q,0)) x.1 := by
    have hi : ContDiffAt ℝ ∞ (normalFirst J α ht p D g B i) (x.1,0) :=
      normalFirst_smooth J α ht p D g B hs hg hB hx i
    exact hi.comp x.1 hc
  exact gauge_joint (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
    (fun i q => normalFirst J α ht p D g B i (q,0)) (x := x) hf

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixPartition
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Add _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Inner _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Module _root_.OAI.TamingCompatibility.GeometricHilbert.preL2Normed _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldLocalization
open Set ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (A : FiniteCharts X)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma coordinatePartition_bounds (p : A.centers) (q : Space) :
    0 ≤ coordinatePartition A p q ∧ coordinatePartition A p q ≤ 1 := by
  by_cases hq : q ∈ (extChartAt Model p.val).target
  · simp only [coordinatePartition,Set.indicator_of_mem hq]
    exact ⟨A.partition.nonneg _ _,A.partition.le_one _ _⟩
  · simp only [coordinatePartition,Set.indicator_of_notMem hq,le_refl,zero_le_one,and_self]

end TamingCompatibility.ManifoldLocalization

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeParametrixWeakEquation
attribute [-instance] _root_.OAI.TamingCompatibility.ManifoldLocalization.globalH1_complete _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (D : ParametrixData J α ht p)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedAddCommGroup
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.parametrixDataMetricTensorNormedSpace
lemma actual {q : Space} (hq : q ∈ Metric.closedBall (extChartAt Model p p) D.radius) :
    ActualData J α ht p D.chart q D.metricExtension D.frameExtension :=
  ⟨D.actualDomain,D.actual_open,D.centers_actual hq,D.actual_subset,
    D.metric_actual,D.frame_actual,D.metric_symmetric⟩

end ParametrixData

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCoordinateRetraction
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
attribute [-simp] _root_.OAI.TamingCompatibility.GeometricHilbert.hodgeScaledDerivative_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2AntiProjection_apply _root_.OAI.TamingCompatibility.GeometricHilbert.l2JAction_smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

omit [T2Space X] [CompactSpace X] in
lemma coordinateEncode_rawVector (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q) =
      frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)) := by
  ext i
  change ⟪HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q,
    HodgeChart.rawVector J α ht p.val (D p).chart a q⟫ = _
  rw [real_inner_comm]
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ ((D p).chart.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p.val a (globalFrame J α ht A D i.1 i.2)
      ((D p).chart.domain_subset hq)]
  rfl

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_apply (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
      ∑ i : A.centers × Fin 6, v i •
        HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q := by
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ • ((∑ i : A.centers × Fin 6,
    (ContinuousLinearMap.proj i : FrameSpace A →L[ℝ] ℝ).smulRight
      (HodgeChart.rawVector J α ht p.val (D p).chart (globalFrame J α ht A D i.1 i.2) q)) v) = _
  simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_rawVector (p : A.centers) (q : Space) (v : FrameSpace A) :
    coordinateDecode J α ht A D p q v = HodgeChart.rawVector J α ht p.val (D p).chart
      (fun x => frameDecode J α ht A D x v) q := by
  rw [coordinateDecode_apply,Fintype.sum_prod_type]
  let L : MetricForms.Form Space 2 →L[ℝ] W :=
    HodgeFrame.coordinates (fun i => (D p).chart.frame i q) ∘L
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (mfderiv Model Model (extChartAt Model p.val).symm q)
  change (squareMass A ((extChartAt Model p.val).symm q))⁻¹ •
    (∑ i : A.centers, ∑ j : Fin 6, v (i,j) • L (globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))) = _
  simp only [HodgeChart.rawVector,ManifoldForms.pullback,frameDecode_apply]
  change _ = L _
  simp only [Finset.smul_sum,smul_smul]
  have he (g : A.centers → Fin 6 → MetricForms.Form Space 2) (c : A.centers → Fin 6 → ℝ) :
      L (∑ i : A.centers, ∑ j : Fin 6, c i j • g i j) = ∑ i : A.centers, ∑ j : Fin 6, c i j • L (g i j) := by
    simp only [map_sum,map_smul]
  exact (he (fun i j => globalFrame J α ht A D i j ((extChartAt Model p.val).symm q))
    (fun i j => (squareMass A ((extChartAt Model p.val).symm q))⁻¹*v (i,j))).symm

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_encode_raw (p : A.centers) (a : TwoForm X) {q : Space}
    (hq : q ∈ (D p).chart.domain) :
    coordinateDecode J α ht A D p q
      (coordinateEncode J α ht A D p q (HodgeChart.rawVector J α ht p.val (D p).chart a q)) =
      HodgeChart.rawVector J α ht p.val (D p).chart a q := by
  rw [coordinateEncode_rawVector J α ht A D p a hq,coordinateDecode_rawVector]
  change HodgeFrame.coordinates _ ((frameDecode J α ht A D ((extChartAt Model p.val).symm q)
    (frameEncode J α ht A D ((extChartAt Model p.val).symm q) (a ((extChartAt Model p.val).symm q)))).compContinuousLinearMap _) = _
  erw [frameDecode_encode J α ht A D hD]
  rfl

include hD in
omit [T2Space X] [CompactSpace X] in
lemma coordinateDecode_encode (p : A.centers) {q : Space} (hq : q ∈ (D p).chart.domain) (v : W) :
    coordinateDecode J α ht A D p q (coordinateEncode J α ht A D p q v) = v := by
  let a := HodgeChart.manifoldTest J α ht p.val (D p).chart (fun _ => v)
  have ha : HodgeChart.rawVector J α ht p.val (D p).chart a q = v := by
    unfold HodgeChart.rawVector a
    rw [HodgeChart.pullback_manifoldTest J α ht p.val (D p).chart _ ((D p).chart.domain_subset hq)]
    exact coordinates_reconstruct _ _ ((D p).chart.frame_gram q hq) v
  rw [← ha]
  exact coordinateDecode_encode_raw J α ht A D hD p a hq

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeManifoldKernelExtension
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set Filter
open scoped Manifold Topology
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X]
  [NormedAddCommGroup G]
attribute [local instance] Classical.propDecidable
local notation "I" => 𝓘(ℝ,E)

lemma liftSet_source (p : X) (K : Set (E × E))
    (hK : K ⊆ (extChartAt I p).target ×ˢ (extChartAt I p).target) :
    liftSet p K ⊆ (extChartAt I p).source ×ˢ (extChartAt I p).source := by
  rintro x ⟨z,hz,rfl⟩
  exact ⟨(extChartAt I p).map_target (hK hz).1,(extChartAt I p).map_target (hK hz).2⟩

end TamingCompatibility.ManifoldKernelExtension

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeGlobalParametrix
attribute [-instance] _root_.OAI.TamingCompatibility.instCompactSpaceMetricUnitOfT2Space
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeFrame HodgeNormalSymbol Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
attribute [local instance] Classical.propDecidable

omit [T2Space X] [CompactSpace X] in
lemma physicalCompact_target (p : A.centers) :
    (D p).physicalCompact ⊆ (extChartAt Model p.val).target ×ˢ (extChartAt Model p.val).target :=
  fun _ hz => ⟨(D p).chart.domain_subset ((D p).physicalCompact_domain hz).1,
    (D p).chart.domain_subset ((D p).physicalCompact_domain hz).2⟩

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

attribute [local irreducible] frameDecode unitFrameDirection

include hE in
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_direction (a : TwoForm X) (u : MetricUnit g) :
    framePairing A J α ht E a u.val.proj (unitFrameDirection A J α ht E g u) =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  have he := globalFrame_full_resolution J α ht A E hE a u.val.proj
  have hh := congrArg (fun b : MetricForms.Form Space 2 =>
    b ![u.val.2,J.endomorphism u.val.proj u.val.2]) he
  let v : A.centers → Fin 6 → MetricForms.Form Space 2 := fun p j =>
    globalFrame J α ht A E p j u.val.proj
  let c : A.centers → Fin 6 → ℝ := fun p j => (squareMass A u.val.proj)⁻¹ *
    GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) u.val.proj
  change (∑ p : A.centers, ∑ j : Fin 6, c p j • v p j)
    ![u.val.2,J.endomorphism u.val.proj u.val.2] =
    a u.val.proj ![u.val.2,J.endomorphism u.val.proj u.val.2] at hh
  simp only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hh
  calc
    _ = ∑ p : A.centers, ∑ j : Fin 6,
        ((squareMass A u.val.proj)⁻¹ * GeometricAdjoint.pairing J α ht a
          (globalFrame J α ht A E p j) u.val.proj) *
          eval (globalFrame J α ht A E p j) u.val.proj u.val.2
            (J.endomorphism u.val.proj u.val.2) := by
      simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul,Finset.mul_sum,unitFrameDirection,mul_assoc]
    _ = _ := hh

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitDual_pairing (a : TwoForm X) (u : MetricUnit g) :
    GeometricAdjoint.pairing J α ht (unitDual A J α hs ht E hE g u).val a u.val.proj =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  rw [← framePairing_direction A J α ht E hE g a u,framePairing_apply]
  exact MetricForms.pairing_symm _ _ _

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUnitKernelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma unitDual_encode (u : MetricUnit g) :
    frameEncode J α ht A E u.val.proj ((unitDual A J α hs ht E hE g u).val u.val.proj) =
      unitFrameDirection A J α ht E g u := by
  ext i
  rw [frameEncode_apply]
  exact unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E i.1 i.2) u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeIntrinsicUnitLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma exists_intrinsic_unit_line (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧ ∀ a : TwoForm X,
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) =
        ⟪HodgeChart.rawVector J α ht p D a q,UnitaryFrame.line v⟫ := by
  have hqt := D.domain_subset hq
  have hall : ∀ w : TangentSpace Model ((extChartAt Model p).symm q),
      (hermitianMetric J α hs ht).inner _ w w = 1 →
      ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧ ∀ a : TwoForm X,
        eval a ((extChartAt Model p).symm q) w (J.endomorphism _ w) =
          ⟪HodgeChart.rawVector J α ht p D a q,UnitaryFrame.line v⟫ := by
    intro w hw
    let L := inverseChartEquiv p q hqt
    let c : Space := L.symm w
    let v := directionCoordinates (coordinateMetric J α ht p q)
      (by simp [Space]) (fun i => D.frame i q) (D.frame_gram q hq) c
    have he : L c = w := L.apply_symm_apply w
    have hc : (coordinateMetric J α ht p q).bilinear c c = 1 := by
      rw [coordinateMetric_bilinear J α ht p hqt,chartMetric_derivative J α p hqt]
      have he' : mfderiv Model Model (extChartAt Model p).symm q c = w := by
        rw [← inverseChartEquiv_coe p q hqt]
        exact he
      rw [he']
      exact hw
    refine ⟨v,norm_directionCoordinates _ _ _ _ c hc,?_⟩
    intro a
    obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex q hq
    calc
      _ = ManifoldForms.pullback a (extChartAt Model p).symm q ![c,coordinateJ J p q c] := by
        rw [GeometricChart.pullback_complexLine J a p hqt,← inverseChartEquiv_coe p q hqt]
        exact congrArg (fun z => eval a ((extChartAt Model p).symm q) z (J.endomorphism _ z)) he.symm
      _ = _ := coordinates_direction_eval _ _ _ (D.frame_gram q hq)
        (coordinateJ J p q) h0 h1 h2 h3 _ c
  rw [hx] at hall
  exact hall u.val.2 u.property

omit [CompactSpace X] [T2Space X] in
lemma rawVector_pairing (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (a b : TwoForm X) :
    ⟪HodgeChart.rawVector J α ht p D a q,HodgeChart.rawVector J α ht p D b q⟫ =
      GeometricAdjoint.pairing J α ht a b ((extChartAt Model p).symm q) := by
  unfold HodgeChart.rawVector
  rw [coordinates_pairing _ (by simp [Space]) _ (D.frame_gram q hq),
    GeometricAdjoint.pairing_two_chart J α ht p a b (D.domain_subset hq)]

omit [CompactSpace X] [T2Space X] in
lemma rawVector_constant_test (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (v : UnitaryFrame.W) :
    HodgeChart.rawVector J α ht p D (HodgeChart.manifoldTest J α ht p D (fun _ => v)) q = v := by
  unfold HodgeChart.rawVector
  rw [HodgeChart.pullback_manifoldTest J α ht p D _ (D.domain_subset hq)]
  exact coordinates_reconstruct _ _ (D.frame_gram q hq) v

omit [CompactSpace X] [T2Space X] in
lemma rawVector_star (p : X) (D : GeometricChart.Data J α ht p)
    {q : Space} (hq : q ∈ D.domain) (a : TwoForm X) :
    HodgeChart.rawVector J α ht p D (starTwo J α ht a) q =
      UnitaryFrame.star (HodgeChart.rawVector J α ht p D a q) := by
  unfold HodgeChart.rawVector
  rw [pullback_starTwo J α ht a p (D.domain_subset hq)]
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex q hq
  exact coordinates_star _ (by simp [Space]) _ (D.frame_gram q hq)
    (coordinateJ J p q) (coordinateMetric_hermitian J α ht p (D.domain_subset hq))
    h0 h1 h2 h3 _ (ManifoldTop.coordinateFundamental J α ht p (D.domain_subset hq)) _

include hE in
omit [CompactSpace X] [T2Space X] in
lemma framePairing_coordinateEncode (p : A.centers) {q : Space}
    (hq : q ∈ (E p).chart.domain) (a : TwoForm X) (v : UnitaryFrame.W) :
    framePairing A J α ht E a ((extChartAt Model p.val).symm q)
      (coordinateEncode J α ht A E p q v) =
        ⟪HodgeChart.rawVector J α ht p.val (E p).chart a q,v⟫ := by
  rw [framePairing_apply]
  erw [← rawVector_pairing J α ht p.val (E p).chart hq,
    ← coordinateDecode_rawVector J α ht A E p q,
    coordinateDecode_encode J α ht A E hE p hq]

lemma exists_unitDual_raw_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧
      HodgeChart.rawVector J α ht p.val (E p).chart
        (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val q = UnitaryFrame.line v := by
  obtain ⟨v,hv,heval⟩ := exists_intrinsic_unit_line J α hs ht p.val (E p).chart hq u hx
  refine ⟨v,hv,?_⟩
  apply ext_inner_right ℝ
  intro w
  let a := HodgeChart.manifoldTest J α ht p.val (E p).chart (fun _ => w)
  have ha : HodgeChart.rawVector J α ht p.val (E p).chart a q = w :=
    rawVector_constant_test J α ht p.val (E p).chart hq w
  rw [← ha,rawVector_pairing J α ht p.val (E p).chart hq,hx,
    unitDual_pairing A J α hs ht E hE (hermitianMetric J α hs ht) a u,heval a,real_inner_comm]

lemma exists_unitDual_coordinate_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hx : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ v : UnitaryFrame.V, ‖v‖ = 1 ∧
      coordinateDecode J α ht A E p q
        (frameEncode J α ht A E u.val.proj
          ((unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val u.val.proj)) =
          UnitaryFrame.line v ∧
      coordinateDecode J α ht A E p q
        (frameEncode J α ht A E u.val.proj
          ((starTwo J α ht (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val) u.val.proj)) =
          UnitaryFrame.star (UnitaryFrame.line v) ∧
      ∀ w : UnitaryFrame.W,
        framePairing A J α ht E (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val
          u.val.proj (coordinateEncode J α ht A E p q w) = ⟪UnitaryFrame.line v,w⟫ := by
  obtain ⟨v,hv,he⟩ := exists_unitDual_raw_line A J α hs ht E hE p hq u hx
  refine ⟨v,hv,?_,?_,?_⟩
  · rw [← hx,← coordinateEncode_rawVector J α ht A E p _ hq,
      coordinateDecode_encode J α ht A E hE p hq,he]
  · rw [← hx,← coordinateEncode_rawVector J α ht A E p _ hq,
      coordinateDecode_encode J α ht A E hE p hq,rawVector_star J α ht p.val (E p).chart hq,he]
  · intro w
    rw [← hx,framePairing_coordinateEncode A J α ht E hE p hq,he]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeActualAngular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma unitCoordinate_line (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht)) (hu : (extChartAt Model p.val).symm q = u.val.proj) :
    ∃ a : UnitaryFrame.V, ‖a‖ = 1 ∧ unitCoordinate A J α hs ht E p q u = UnitaryFrame.line a := by
  obtain ⟨a,ha,he,-,-⟩ := exists_unitDual_coordinate_line A J α hs ht E hE p hq u hu
  refine ⟨a,ha,?_⟩
  unfold unitCoordinate
  rw [← unitDual_encode A J α hs ht E hE]
  exact he

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_EuclideanCoordinateLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
lemma unitChart_eval_raw (p : X) (β : TwoForm X)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p).source) :
    ManifoldForms.pullback β (extChartAt Model p).symm (unitChartBase J α hs ht p u)
      ![unitChartVector J α hs ht p u,unitChartJVector J α hs ht p u] =
      eval β u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  let t := trivializationAt Space (TangentSpace Model) p
  have hb : u.val.proj ∈ t.baseSet := by
    simpa only [t,TangentBundle.trivializationAt_baseSet,extChartAt_source] using hu
  have hv : t.symmL ℝ u.val.proj (unitChartVector J α hs ht p u) = u.val.2 := by
    change t.symmL ℝ u.val.proj ((t u.val).2) = _
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hb]
    exact t.symmL_continuousLinearMapAt hb _
  dsimp only [unitChartJVector,unitChartBase]
  rw [pullback_complexLine J β p ((extChartAt Model p).map_source hu),
    inverseChart_derivative p ((extChartAt Model p).map_source hu)]
  change eval β ((extChartAt Model p).symm (extChartAt Model p u.val.proj))
    (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)
    (J.endomorphism _ (t.symmL ℝ ((extChartAt Model p).symm (extChartAt Model p u.val.proj)) _)) = _
  rw [(extChartAt Model p).left_inv hu,hv]
end TamingCompatibility.GeometricHilbert.Hermitian

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma unitCoordinate_rawVector (p : A.centers) {q : Space} (hq : q ∈ (E p).chart.domain)
    (u : MetricUnit (hermitianMetric J α hs ht)) (hu : (extChartAt Model p.val).symm q = u.val.proj) :
    unitCoordinate A J α hs ht E p q u = HodgeChart.rawVector J α ht p.val (E p).chart
      (unitDual A J α hs ht E hE (hermitianMetric J α hs ht) u).val q := by
  unfold unitCoordinate
  rw [← unitDual_encode A J α hs ht E hE,← hu,
    ← coordinateEncode_rawVector J α ht A E p _ hq,coordinateDecode_encode J α ht A E hE p hq]

include hE in
lemma unitCoordinate_directionCoordinates (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).chart.domain) :
    unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u =
      line (directionCoordinates (coordinateMetric J α ht p.val
        (unitChartBase J α hs ht p.val u)) (by simp [Space])
        (fun i => (E p).chart.frame i (unitChartBase J α hs ht p.val u))
        ((E p).chart.frame_gram _ hq) (unitChartVector J α hs ht p.val u)) := by
  let q := unitChartBase J α hs ht p.val u
  have he : (extChartAt Model p.val).symm q = u.val.proj := (extChartAt Model p.val).left_inv hu
  rw [unitCoordinate_rawVector A J α hs ht E hE p hq u he]
  apply ext_inner_right ℝ
  intro w
  let β := HodgeChart.manifoldTest J α ht p.val (E p).chart (fun _ => w)
  have hβ : HodgeChart.rawVector J α ht p.val (E p).chart β q = w :=
    rawVector_constant_test J α ht p.val (E p).chart hq w
  rw [← hβ,rawVector_pairing J α ht p.val (E p).chart hq,he,
    unitDual_pairing A J α hs ht E hE (hermitianMetric J α hs ht) β u,
    ← unitChart_eval_raw J α hs ht p.val β u hu,real_inner_comm]
  obtain ⟨h0,h1,h2,h3⟩ := (E p).chart.frame_complex q hq
  exact coordinates_direction_eval _ _ _ ((E p).chart.frame_gram q hq)
    (coordinateJ J p.val q) h0 h1 h2 h3 _ _

include hE in
lemma unitCoordinate_wedgeTransform (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).chart.domain) :
    wedgeTransform (fun i => (E p).chart.frame i (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u) =
      wedge (unitChartVector J α hs ht p.val u) (unitChartJVector J α hs ht p.val u) := by
  rw [unitCoordinate_directionCoordinates A J α hs ht E hE p u hu hq,line,wedgeTransform_wedge]
  have hv := sum_directionCoordinates (coordinateMetric J α ht p.val
    (unitChartBase J α hs ht p.val u)) (by simp [Space]) _ ((E p).chart.frame_gram _ hq)
    (unitChartVector J α hs ht p.val u)
  obtain ⟨h0,h1,h2,h3⟩ := (E p).chart.frame_complex _ hq
  rw [← complex_frame_sum _ _ h0 h1 h2 h3,hv]
  rfl

include hE in
lemma unitCoordinate_normalized_wedgeTransform (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).chart.domain) :
    PlaneVariation.first (wedgeTransform (fun i => (E p).chart.frame i (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u)) =
      wedge (unitChartFirst J α hs ht p.val u) (unitChartSecond J α hs ht p.val u) := by
  rw [unitCoordinate_wedgeTransform A J α hs ht E hE p u hu hq]
  have ha := unitChartVector_ne_zero J α hs ht p.val u hu
  have hab := normalPart_complex_ne_zero (coordinateJ J p.val
    (unitChartBase J α hs ht p.val u))
    (coordinateJ_square J p.val ((extChartAt Model p.val).map_source hu)) ha
  rw [show unitChartFirst J α hs ht p.val u = PlaneVariation.first (unitChartVector J α hs ht p.val u) from rfl,
    show unitChartSecond J α hs ht p.val u = PlaneVariation.second (unitChartVector J α hs ht p.val u)
      (unitChartJVector J α hs ht p.val u) from rfl,wedge_normalized _ _ ha]
  change ‖wedge _ _‖⁻¹ • wedge _ _ = _
  dsimp only [unitChartJVector]
  rw [norm_wedge_area _ _ ha hab]
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.UnitaryFrame
open scoped ContDiff

lemma exteriorTransform_smooth {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → V →L[ℝ] V} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun q => exteriorTransform (B q)) :=
  wedgeTransform_contDiff (fun _i => hB.clm_apply contDiff_const)

lemma exteriorTransform_frame (b : Fin 4 → V) :
    exteriorTransform (GeometricHilbert.GeometricNormalCharts.frameMap b) = wedgeTransform b := by
  unfold exteriorTransform
  congr 1
  funext i
  simp [GeometricHilbert.GeometricNormalCharts.frameMap_apply]
end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator Filter Set UniformJets
open UnitaryFrame
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedAddCommGroupMetricTensorSpace_15
attribute [local instance] OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.instNormedSpaceRealMetricTensorSpace_15
lemma euclidean_transport_linear (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (K : Set Space) (hK : IsCompact K)
    (hactual : ∀ q ∈ K, ActualData J α ht p D q g B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ‖(exteriorTransform (B (normalMap g B q z))).comp (normalGauge J α ht p D g B (q,z)) -
        exteriorTransform (B q)‖ ≤ C*‖z‖ := by
  let F : Space × Space → W →L[ℝ] W := fun x =>
    (exteriorTransform (B (normalMap g B x.1 x.2))).comp (normalGauge J α ht p D g B x)
  let Ω : Set (Space × Space) := (fun x : Space × Space => (x.1,(0 : Space))) ⁻¹' normalDomain J α ht p D g B
  have hΩ : IsOpen Ω := (normalDomain_open J α ht p D g B hg hB).preimage
    (continuous_fst.prodMk continuous_const)
  have hKΩ : K ×ˢ {(0 : Space)} ⊆ Ω := by
    rintro ⟨q,z⟩ ⟨hq,_⟩
    exact ((hactual q hq).center J α ht p D g B).1
  have hF : ∀ x ∈ Ω, ContDiffAt ℝ ∞ F x := fun x hx =>
    ((exteriorTransform_smooth hB).comp (normalMap_joint g B hg hB)).contDiffAt.clm_comp
      (normalGauge_smooth J α ht p D g B hs hg hB hx)
  obtain ⟨C,hC,r,hr,_,hb⟩ := local_linear_bound F K hK Ω hΩ hKΩ hF
  refine ⟨C,hC,r,hr,fun q hq z hz => ?_⟩
  simpa only [F,normalMap_zero,normalGauge_zero,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id] using hb q hq z hz

lemma euclidean_transport_difference {K : Set Space} {C r : ℝ}
    (hC : ∀ q ∈ K, ∀ z : Space, ‖z‖ ≤ r →
      ‖(exteriorTransform (B (normalMap g B q z))).comp (normalGauge J α ht p D g B (q,z)) -
        exteriorTransform (B q)‖ ≤ C*‖z‖)
    {q : Space} (hq : q ∈ K) {z : Space} (hz : ‖z‖ ≤ r) (a b : W) (hb : ‖b‖ = 1) :
    ‖exteriorTransform (B (normalMap g B q z)) a - exteriorTransform (B q) b‖ ≤
      ‖exteriorTransform (B (normalMap g B q z))‖ *
        ‖a-normalGauge J α ht p D g B (q,z) b‖ + C*‖z‖ := by
  let T := exteriorTransform (B (normalMap g B q z))
  let U := normalGauge J α ht p D g B (q,z)
  let S := exteriorTransform (B q)
  have he : T a-S b = T (a-U b)+(T.comp U-S) b := by simp only [map_sub,sub_apply,ContinuousLinearMap.comp_apply]; abel
  calc
    _ ≤ ‖T (a-U b)‖+‖(T.comp U-S) b‖ := by rw [he]; exact norm_add_le _ _
    _ ≤ ‖T‖*‖a-U b‖+‖T.comp U-S‖*‖b‖ := add_le_add (T.le_opNorm _) ((T.comp U-S).le_opNorm _)
    _ ≤ _ := by rw [hb,mul_one]; exact add_le_add le_rfl (hC q hq z hz)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePatchContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set _root_.MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_mem (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    angularChartCoordinates A J α hs ht p uv ∈ (E p).physicalCompact := by
  obtain ⟨w,hw,he⟩ := huv
  have he' := congrArg (fun xy : X × X => (extChartAt Model p.val xy.1,extChartAt Model p.val xy.2)) he
  have ht' := physicalCompact_target J α ht A E p hw
  simp only [(extChartAt Model p.val).right_inv ht'.1,(extChartAt Model p.val).right_inv ht'.2] at he'
  change w = angularChartCoordinates A J α hs ht p uv at he'
  rw [← he']
  exact hw

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_source (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    uv.2.val.proj ∈ (extChartAt Model p.val).source ∧ uv.1.val.proj ∈ (extChartAt Model p.val).source :=
  ManifoldKernelExtension.liftSet_source p.val _ (physicalCompact_target J α ht A E p) huv

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_mem (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    angularCoordinates A J α hs ht E p uv ∈ (E p).normalCompact := by
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  unfold angularCoordinates
  rw [← he,(E p).normalChart.left_inv ((E p).normalCompact_source hz)]
  exact hz

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_chart (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    (E p).normalChart (angularCoordinates A J α hs ht E p uv) =
      angularChartCoordinates A J α hs ht p uv := by
  apply (E p).normalChart.right_inv
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  rw [← he]
  exact (E p).normalChart.map_source ((E p).normalCompact_source hz)

omit [CompactSpace X] [T2Space X] in
lemma angularWeight_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ angularWeight A J α hs ht E p uv := by
  apply mul_nonneg (mul_nonneg (coordinatePartition_bounds A p _).1 (E p).normalCutoff.nonneg) (sq_nonneg _)

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma angularNear_nonneg (r : ℝ) (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ angularNear A J α hs ht E r p uv :=
  Set.indicator_nonneg (fun v _ => angularWeight_nonneg A J α hs ht E p v) uv

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hE in
lemma unitCoordinate_exterior_norm (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).actualDomain) :
    ‖exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u)‖ =
        unitChartArea J α hs ht p.val u := by
  rw [(E p).frame_actual _ hq,exteriorTransform_frame,
    unitCoordinate_wedgeTransform A J α hs ht E hE p u hu ((E p).actual_subset hq)]
  have hn := unitChartVector_ne_zero J α hs ht p.val u hu
  exact norm_wedge_area _ _ hn (normalPart_complex_ne_zero _
    (coordinateJ_square J p.val ((extChartAt Model p.val).map_source hu)) hn)

include hE in
lemma unitCoordinate_exterior_first (p : A.centers)
    (u : MetricUnit (hermitianMetric J α hs ht))
    (hu : u.val.proj ∈ (extChartAt Model p.val).source)
    (hq : unitChartBase J α hs ht p.val u ∈ (E p).actualDomain) :
    first (exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val u))
      (unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val u) u)) =
        euclideanLine A J α hs ht p u := by
  rw [(E p).frame_actual _ hq,exteriorTransform_frame]
  exact unitCoordinate_normalized_wedgeTransform A J α hs ht E hE p u hu ((E p).actual_subset hq)

include hE in

lemma euclidean_angular_point (p : A.centers) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ uv ∈ angularDomain A J α hs ht E p,
      ‖(angularCoordinates A J α hs ht E p uv).2‖ ≤ r →
      ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖ ≤
        C*(normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2 +
          ‖(angularCoordinates A J α hs ht E p uv).2‖) := by
  let K := Prod.snd '' (E p).physicalCompact
  have hK : IsCompact K := (E p).physicalCompact_compact.image continuous_snd
  have hKT : K ⊆ (extChartAt Model p.val).target := by
    rintro y ⟨xy,hxy,rfl⟩
    exact (E p).chart.domain_subset ((E p).physicalCompact_domain hxy).2
  obtain ⟨m,M,hm,_,harea⟩ := unitChartArea_bounds J α hs ht p.val hK hKT
  obtain ⟨L,hL,r,hr,hlin⟩ := euclidean_transport_linear J α ht p.val (E p).chart
    (E p).metricExtension (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth
    (Metric.closedBall (extChartAt Model p.val p.val) (E p).radius)
    (isCompact_closedBall _ _) (fun q hq => (E p).actual hq)
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (exteriorTransform_smooth (E p).frame_smooth).continuous.continuousOn
  let C := (2/m)*max (max B 0) L
  have hC : 0 ≤ C := mul_nonneg (by positivity) (le_max_of_le_left (le_max_right _ _))
  refine ⟨C,hC,r,hr,?_⟩
  intro uv huv hz
  let z := angularCoordinates A J α hs ht E p uv
  have hzn := angularCoordinates_mem A J α hs ht E p huv
  have he := angularCoordinates_chart A J α hs ht E p huv
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change z.1 = unitChartBase J α hs ht p.val uv.2 at he1
  change normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 =
    unitChartBase J α hs ht p.val uv.1 at he2
  have hus := angularChartCoordinates_source A J α hs ht E p huv
  have hq := (E p).centers_actual hzn.1
  have hy := ((E p).tube hzn).2
  rw [he1] at hq
  change normalMap (E p).metricExtension (E p).frameExtension z.1 z.2 ∈ (E p).actualDomain at hy
  rw [he2] at hy
  have hynK : unitChartBase J α hs ht p.val uv.1 ∈ K :=
    ⟨angularChartCoordinates A J α hs ht p uv,angularChartCoordinates_mem A J α hs ht E p huv,rfl⟩
  have huK : uv.1 ∈ unitChartDomain J α hs ht p.val K := by
    refine ⟨unitChartBase J α hs ht p.val uv.1,hynK,?_⟩
    exact (extChartAt Model p.val).left_inv hus.2
  have ham := (harea uv.1 huK).1
  let a := unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val uv.1) uv.1
  let b := unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val uv.2) uv.2
  let T := exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val uv.1))
  let S := exteriorTransform ((E p).frameExtension (unitChartBase J α hs ht p.val uv.2))
  have han : m ≤ ‖T a‖ := by
    rw [unitCoordinate_exterior_norm A J α hs ht E hE p uv.1 hus.2 hy]
    exact ham
  have hbn : S b ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [unitCoordinate_exterior_norm A J α hs ht E hE p uv.2 hus.1 hq]
    exact ne_of_gt (unitChartPlane J α hs ht p.val uv.2 hus.1).2.2.2
  have hbu : ‖b‖ = 1 := by
    obtain ⟨v,hv,hvb⟩ := unitCoordinate_line A J α hs ht E hE p ((E p).actual_subset hq) uv.2
      ((extChartAt Model p.val).left_inv hus.1)
    change ‖unitCoordinate A J α hs ht E p (unitChartBase J α hs ht p.val uv.2) uv.2‖ = 1
    rw [hvb]
    exact unit_line_norm hv
  have hd := euclidean_transport_difference J α ht p.val (E p).chart
    (E p).metricExtension (E p).frameExtension hlin hzn.1 hz a b hbu
  rw [he2,he1] at hd
  have hAB : ‖T a-S b‖ ≤ ‖T‖*normalAngular A J α hs ht E p z uv.1 uv.2 + L*‖z.2‖ := by
    dsimp only [normalAngular]
    rw [he2]
    have hez : z = (unitChartBase J α hs ht p.val uv.2,z.2) := Prod.ext he1 rfl
    rw [hez]
    exact hd
  have hnorm : ‖T‖ ≤ max (max B 0) L :=
    (hB _ hynK).trans ((le_max_left B 0).trans (le_max_left _ _))
  have ha0 : 0 ≤ normalAngular A J α hs ht E p z uv.1 uv.2 := norm_nonneg _
  have hlf := first_lipschitz_bound hm han hbn
  rw [unitCoordinate_exterior_first A J α hs ht E hE p uv.1 hus.2 hy,
    unitCoordinate_exterior_first A J α hs ht E hE p uv.2 hus.1 hq] at hlf
  apply hlf.trans
  apply (mul_le_mul_of_nonneg_left hAB (by positivity : 0 ≤ 2/m)).trans
  change (2/m)*(‖T‖*_+L*‖z.2‖) ≤ C*(_+‖z.2‖)
  dsimp only [C]
  calc
    _ ≤ (2/m)*(max (max B 0) L*normalAngular A J α hs ht E p z uv.1 uv.2+
        max (max B 0) L*‖z.2‖) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_right hnorm ha0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))) (by positivity)
    _ = _ := by ring
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_EuclideanAngularNearPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set _root_.MeasureTheory
open Hermitian UnitaryFrame PlaneVariation
open scoped Manifold ContDiff Topology RealInnerProductSpace ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [SecondCountableTopology X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel 
include hE in
omit [SecondCountableTopology X] in
lemma euclidean_angular_near_point_oai (p : A.centers) :
    ∃ C B L ρ : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ 0 < L ∧ 0 < ρ ∧
      ∀ s : ℝ, 0 < s → s ≤ ρ → ∀ uv : UnitPair J α hs ht,
      euclideanAngularNear A J α hs ht E s p uv ≤ C*angularNear A J α hs ht E (L*s) p uv +
        B*s^2*(euclideanNearSet A J α hs ht E s p).indicator (fun _ => (1:ℝ)) uv := by
  obtain ⟨C,hC,r,hr,hang⟩ := euclidean_angular_point A J α hs ht E hE p
  obtain ⟨L,hL,ε,hε,hinv⟩ := (E p).normal_inverse_near
  let ρ := min ε (r/L)
  have hρ : 0 < ρ := lt_min hε (div_pos hr hL)
  refine ⟨2*C ^ 2,2*C ^ 2*L^2,L,ρ,by positivity,by positivity,hL,hρ,fun s hs' hsρ uv => ?_⟩
  by_cases huv : uv ∈ euclideanNearSet A J α hs ht E s p
  · have hz := angularCoordinates_mem A J α hs ht E p huv.1
    have he := angularCoordinates_chart A J α hs ht E p huv.1
    have he1 := congrArg Prod.fst he
    change (angularCoordinates A J α hs ht E p uv).1 = (angularChartCoordinates A J α hs ht p uv).1 at he1
    have hq : (angularChartCoordinates A J α hs ht p uv).1 ∈ Metric.closedBall
        (extChartAt Model p.val p.val) (E p).radius := by rw [← he1]; exact hz.1
    have hi := hinv _ hq _ (huv.2.trans (hsρ.trans (min_le_left _ _)))
    have hn : ‖(angularCoordinates A J α hs ht E p uv).2‖ ≤ L*s :=
      hi.2.1.trans (mul_le_mul_of_nonneg_left huv.2 hL.le)
    have hnr : ‖(angularCoordinates A J α hs ht E p uv).2‖ ≤ r := by
      apply hn.trans
      simpa only [mul_comm] using (le_div_iff₀ hL).mp (hsρ.trans (min_le_right _ _))
    have ha := hang uv huv.1 hnr
    have ha0 : 0 ≤ normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2 := norm_nonneg _
    have hnorm0 : 0 ≤ ‖(angularCoordinates A J α hs ht E p uv).2‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have hn2 := pow_le_pow_left₀ hnorm0 hn 2
    have htwo := sq_nonneg (normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2 -
      ‖(angularCoordinates A J α hs ht E p uv).2‖)
    have hh : ‖euclideanLine A J α hs ht p uv.1-euclideanLine A J α hs ht p uv.2‖^2 ≤
        2*C ^ 2*(normalAngular A J α hs ht E p (angularCoordinates A J α hs ht E p uv) uv.1 uv.2)^2 +
          2*C ^ 2*L^2*s^2 := by
      nlinarith [mul_nonneg (sq_nonneg C) htwo,mul_le_mul_of_nonneg_left hn2 (sq_nonneg C)]
    have hpart0 := A.partition.nonneg p uv.2.val.proj
    have hpart1 := A.partition.le_one p uv.2.val.proj
    have hmul := mul_le_mul_of_nonneg_left hh hpart0
    have hlast := mul_le_mul_of_nonneg_right hpart1 (by positivity : 0 ≤ 2*C ^ 2*L^2*s^2)
    have hangmem : uv ∈ angularNearSet A J α hs ht E (L*s) p := ⟨huv.1,hn⟩
    rw [euclideanAngularNear,indicator_of_mem huv,angularNear,indicator_of_mem hangmem,indicator_of_mem huv]
    dsimp only [euclideanAngularWeight,angularWeight]
    have hep : coordinatePartition A p (angularCoordinates A J α hs ht E p uv).1 = A.partition p uv.2.val.proj := by
      rw [he1]
      exact coordinatePartition_apply A p (angularChartCoordinates_source A J α hs ht E p huv.1).1
    have hec : (E p).normalCutoff (angularCoordinates A J α hs ht E p uv).2 = 1 := hi.2.2
    rw [hep,hec]
    nlinarith
  · rw [euclideanAngularNear,indicator_of_notMem huv,indicator_of_notMem huv,mul_zero,add_zero]
    exact mul_nonneg (by positivity) (angularNear_nonneg A J α hs ht E (L*s) p uv)
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.euclidean_angular_near_point_oai.{u_1}

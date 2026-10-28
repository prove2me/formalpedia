-- Prove2me | solution 1 for OAI.SK.Analytic.exists_scalarCDFParisi_minimizer_locking_data
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:05:53.795784+00:00
-- url     : https://prove2.me/submissions/98109d62-67c5-48cd-a815-48c8e4bbed31

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Theorems.Thm_OAI_SK_Analytic_exists_stationary_quantile_sequence
import Theorems.Thm_OAI_SK_Analytic_scalarCDFParisi_origin_stability
import Theorems.Thm_OAI_SK_Analytic_scalarCDFPotential_minimum_bound

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic

theorem scalarSign_gaussian (b : Bool) :
    MeasurePreserving (scalarSign b) (gaussianReal 0 1) (gaussianReal 0 1) := by
  refine ⟨(scalarSign_continuous b).measurable, ?_⟩
  cases b
  · simp only [scalarSign_false,Measure.map_id]
  · simpa only [scalarSign_true,neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))

end SK.Analytic

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK.Analytic
section GaussianGrowth
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem HasExpGrowth.norm_id : HasExpGrowth (fun x : E => ‖x‖) := by
  refine ⟨1,1,zero_le_one,zero_le_one,?_⟩
  intro x
  simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),one_mul]
  exact le_trans (by linarith) (Real.add_one_le_exp ‖x‖)

end GaussianGrowth

end SK.Analytic
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert! h using 1
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one,
      Pi.neg_apply,Pi.pow_apply,id_eq]
  · simp only [Pi.neg_apply,Pi.pow_apply,id_eq]
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    norm_num
    ring

theorem integrable_standardGaussian_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => f x*gaussianPDFReal 0 1 x) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul,mul_comm]

theorem gaussian_integral_mul_eq_integral_deriv (f f' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal 0 1))
    (hi' : Integrable f' (gaussianReal 0 1))
    (hix : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hi₀ := (integrable_standardGaussian_iff f).mp hi
  have hi₁ := (integrable_standardGaussian_iff f').mp hi'
  have hi₂ := (integrable_standardGaussian_iff (fun x => x*f x)).mp hix
  have hx : Integrable (fun x => f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert hi₂.neg using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    change _ = -(x*f x*gaussianPDFReal 0 1 x)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x) hx hi₁ hi₀
  have he : (fun x => f x*(-x*gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x*(x*f x))) := by funext x; ring
  rw [he,integral_neg] at h
  have h' := neg_injective h
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul,mul_comm] using h'

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyLevels
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.Analytic.fiberGaussian_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [-instance] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyLevel_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) :
    BoundedDerivs (hierarchyLevel n m f j) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [hierarchyLevel,Fin.lastCases_last] using hf
    · simp only [hierarchyLevel,Fin.lastCases_castSucc]
      let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
        ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
      exact (ih (fun i => m i.castSucc) _ (hf.gaussianStep (m (Fin.last n))) i).compCLM P

theorem fderiv_hierarchyPenalty_apply (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (z v : ParameterSpace n) :
    fderiv ℝ (hierarchyPenalty n m u f) z v =
      ∑ j, hierarchyAtom n m u j*fderiv ℝ (hierarchyLevel n m f j) z v := by
  have he : hierarchyPenalty n m u f = fun z =>
      ∑ j, hierarchyAtom n m u j*hierarchyLevel n m f j z := funext (hierarchyPenalty_sum n m u f)
  rw [he]
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((hierarchyLevel_boundedDerivs n m f hf j).1.differentiable (by norm_num) z).hasFDerivAt.const_mul
      (hierarchyAtom n m u j))
  rw [hd.fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul]

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyMomentLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyAverage_momentLevel (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) (x : ℝ) :
    hierarchyAverage n m f (hierarchyMomentLevel n m f g j) x = hierarchyAverage n m f g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix hf]
      exact ih (fun i => m i.castSucc) _ _ (hf.gaussianStep _) j

theorem hierarchyLevel_gradient (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1))
    (u z : ParameterSpace n) (hz : TailZero n j u) :
    fderiv ℝ (hierarchyLevel n m f j) z u =
      hierarchyMomentLevel n m f (directionalGradient f u) j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun _ => ?_) (fun j hz => ?_) j
    · simp only [hierarchyLevel,hierarchyMomentLevel,Fin.lastCases_last,directionalGradient]
    · simp only [TailZero,Fin.lastCases_castSucc] at hz
      simp only [hierarchyLevel,hierarchyMomentLevel,Fin.lastCases_castSucc]
      let f' := gaussianStep (m (Fin.last n)) f
      let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
        ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
      have hD := ((hierarchyLevel_boundedDerivs n (fun i => m i.castSucc) f'
        (hf.gaussianStep _) j).1.differentiable (by norm_num) z.1).hasFDerivAt.comp z
        P.hasFDerivAt
      change fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j ∘ P) z u = _
      have hDeq : fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j ∘ P) z =
          (fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j) z.1).comp P := hD.fderiv
      rw [hDeq]
      change fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j) z.1 u.1 = _
      rw [ih (fun i => m i.castSucc) f' (hf.gaussianStep _) j u.1 z.1 hz.2]
      have he : directionalGradient f' u.1 = gaussianAverage (m (Fin.last n)) f (directionalGradient f u) := by
        funext y
        rw [directionalGradient,fderiv_gaussianStep_apply hf]
        have hui : u = (u.1,0) := Prod.ext rfl hz.1
        rw [hui]
        rfl
      rw [he]

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAverageProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section AverageProduct
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_prefix_mul (m : ℝ) (f g : E × ℝ → ℝ) (h : E → ℝ) :
    gaussianAverage m f (fun z => h z.1*g z) = fun z => h z*gaussianAverage m f g z := by
  funext z
  exact integral_const_mul (h z) (fun y : ℝ => g (z,y))
end AverageProduct

theorem hierarchyMomentLevel_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => hierarchyMomentLevel n m f h j z*g z) j =
      fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      rw [gaussianAverage_prefix_mul]
      simp_rw [ih (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
        (gaussianAverage (m (Fin.last n)) f g) (gaussianAverage (m (Fin.last n)) f h) j]

theorem hierarchyAverage_prefix_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) (x : ℝ) :
    hierarchyAverage n m f (fun z => hierarchyMomentLevel n m f h j z*g z) x =
      hierarchyAverage n m f
        (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) x := by
  rw [← hierarchyAverage_momentLevel n m f _ hf j,hierarchyMomentLevel_mul]

theorem hierarchyPathLaw_prefix_mul (n : ℕ) (m : Fin n → ℝ)
    (f g h : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g) (hh : Continuous h)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hgb : ∀ z, ‖g z‖ ≤ C) (hhb : ∀ z, ‖h z‖ ≤ D)
    (j : Fin (n+1)) (x : ℝ) :
    (∫ z, hierarchyMomentLevel n m f h j z*g z ∂hierarchyPathLaw n m f x) =
      ∫ z, hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z
        ∂hierarchyPathLaw n m f x := by
  have H := hierarchyMomentLevel_bounded_continuous n m f h hf hh hD hhb j
  have G := hierarchyMomentLevel_bounded_continuous n m f g hf hg hC hgb j
  have hb₁ (z) : ‖hierarchyMomentLevel n m f h j z*g z‖ ≤ D*C := by
    rw [norm_mul]
    exact mul_le_mul (H.2 z) (hgb z) (norm_nonneg _) hD
  have hb₂ (z) : ‖hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z‖ ≤ D*C := by
    rw [norm_mul]
    exact mul_le_mul (H.2 z) (G.2 z) (norm_nonneg _) hD
  have hcont₁ : Continuous (fun z => hierarchyMomentLevel n m f h j z*g z) := H.1.mul hg
  have hcont₂ : Continuous (fun z => hierarchyMomentLevel n m f h j z*hierarchyMomentLevel n m f g j z) := H.1.mul G.1
  rw [← hierarchyAverage_eq_integral n m f hf _ hcont₁ (mul_nonneg hD hC) hb₁,
    ← hierarchyAverage_eq_integral n m f hf _ hcont₂ (mul_nonneg hD hC) hb₂]
  exact hierarchyAverage_prefix_mul n m f g h hf j x

end SK.Analytic

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_DisorderPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

theorem covariance_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z W : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (a b c d : ℝ) :
    cov[fun ω => a * X ω + b * Y ω, fun ω => c * Z ω + d * W ω; μ] =
      a * c * cov[X, Z; μ] + a * d * cov[X, W; μ] +
      b * c * cov[Y, Z; μ] + b * d * cov[Y, W; μ] := by
  change cov[(fun ω => a * X ω) + (fun ω => b * Y ω),
    (fun ω => c * Z ω) + (fun ω => d * W ω); μ] = _
  rw [covariance_add_left (hX.const_mul a) (hY.const_mul b)
      ((hZ.const_mul c).add (hW.const_mul d)),
    covariance_add_right (hX.const_mul a) (hZ.const_mul c) (hW.const_mul d),
    covariance_add_right (hY.const_mul b) (hZ.const_mul c) (hW.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarMassOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarStep_one_spin (v : ℝ) :
    scalarStep 1 v scalarSpinTerminal = fun z => scalarSpinTerminal z+v^2/2 := by
  funext z
  have he (y : ℝ) : Real.exp (scalarSpinTerminal (z+v*y)) =
      Real.exp z*Real.exp (v*y)+Real.exp (-z)*Real.exp (-v*y) := by
    rw [scalarSpinTerminal,Real.exp_log (mul_pos (by norm_num) (Real.cosh_pos _)),Real.cosh_eq]
    rw [Real.exp_add,show -(z+v*y) = -z+(-v)*y by ring,Real.exp_add]
    ring
  have hm (a : ℝ) : (∫ y : ℝ, Real.exp (a*y) ∂gaussianReal 0 1) = Real.exp (a^2/2) := by
    simpa only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add] using
      congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) a
  simp only [scalarStep,gaussianStep,one_ne_zero,ite_false,positiveGaussianLogStep,one_mul,div_one]
  simp_rw [he]
  rw [integral_add ((integrable_exp_mul_gaussianReal v).const_mul (Real.exp z))
      ((integrable_exp_mul_gaussianReal (-v)).const_mul (Real.exp (-z))),
    integral_const_mul,integral_const_mul,hm v,hm (-v),neg_sq]
  have H : Real.exp z*Real.exp (v^2/2)+Real.exp (-z)*Real.exp (v^2/2) =
      (2*Real.cosh z)*Real.exp (v^2/2) := by rw [Real.cosh_eq]; ring
  rw [H,Real.log_mul (ne_of_gt (mul_pos (by norm_num) (Real.cosh_pos z))) (Real.exp_ne_zero _),Real.log_exp]
  rfl

theorem scalarStep_add_const {f : ℝ → ℝ} (hf : BoundedDerivs f) (m v c : ℝ) :
    scalarStep m v (fun z => f z+c) = fun z => scalarStep m v f z+c := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ+v • ContinuousLinearMap.snd ℝ ℝ ℝ
  exact gaussianStep_add_prefix (hf.compCLM L) (fun _ => c) m

theorem scalarHierarchy_add_const (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ)
    (hf : BoundedDerivs f) (c : ℝ) :
    scalarHierarchy n m v (fun z => f z+c) = fun z => scalarHierarchy n m v f z+c := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [scalarHierarchy,scalarStep_add_const hf]
    exact ih _ _ _ (scalarStep_regular hf _ _)

theorem scalar_quantile_terminal_shift (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q (Fin.last k) ≤ 1) :
    scalarHierarchy (k+1) (quantileMass k)
      (fun b => β*Real.sqrt (cumulativeGapMap k Q b))
      (scalarStep 1 (β*Real.sqrt (1-Q (Fin.last k))) scalarSpinTerminal) 0 =
      scalarHierarchy (k+1) (quantileMass k)
        (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0+
      (β^2/2)*(1-Q (Fin.last k)) := by
  have hf : BoundedDerivs scalarSpinTerminal := scalarHierarchy_spin_regular 0 Fin.elim0 Fin.elim0
  rw [scalarStep_one_spin,scalarHierarchy_add_const _ _ _ _ hf]
  rw [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hQ)]
  ring
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_ParameterMomentSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarMomentSquare_eq_parameterAverage (n : ℕ) (m v : Fin n → ℝ)
    (F H : ℝ → ℝ → ℝ) (x a : ℝ)
    (hf : BoundedDerivs (scalarParameterTerminal n v F x)) (j : Fin (n+1)) :
    scalarMomentSquare n m v (F a) (H a) j x =
      hierarchyAverage n m (scalarParameterTerminal n v F x)
        (fun z => (hierarchyMomentLevel n m (scalarParameterTerminal n v F x)
          (scalarParameterTerminal n v H x) j z)^2) a := by
  induction n generalizing F H with
  | zero => simp [scalarMomentSquare,hierarchyAverage,hierarchyMomentLevel,
      scalarParameterTerminal,coordinateLinear,parameter]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last,hierarchyMomentLevel]
      exact (hierarchyAverage_scalarParameterTerminal (n+1) m v F
        (fun a x => (H a x)^2) x a).symm
    · simp only [scalarMomentSquare,hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix hf (m (Fin.last n)) (fun z =>
        (hierarchyMomentLevel n (fun i => m i.castSucc)
          (gaussianStep (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x))
          (gaussianAverage (m (Fin.last n)) (scalarParameterTerminal (n+1) v F x)
            (scalarParameterTerminal (n+1) v H x)) j z)^2)]
      simp only [gaussianStep_scalarParameterTerminal,gaussianAverage_scalarParameterTerminal]
      have hf' := hf.gaussianStep (m (Fin.last n))
      rw [gaussianStep_scalarParameterTerminal] at hf'
      exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
        (fun a => scalarStep (m (Fin.last n)) (v (Fin.last n)) (F a))
        (fun a => scalarStepAverage (m (Fin.last n)) (v (Fin.last n)) (F a) (H a)) hf' j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_C1Taylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussian_abs_pow_integrable (n : ℕ) :
    Integrable (fun z : ℝ => |z|^n) (gaussianReal 0 1) := by
  have H := (memLp_id_gaussianReal' (μ:=0) (v:=1) (n:ℝ≥0∞) (by simp)).integrable_norm_pow'
  simpa only [id_eq,Real.norm_eq_abs] using H

theorem gaussian_second_moment : (∫ z : ℝ, z^2 ∂gaussianReal 0 1)=1 := by
  have H := variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (by fun_prop)] at H
  simpa using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianPair_fst : HasLaw (Prod.fst : ℝ × ℝ → ℝ) (gaussianReal 0 1) gaussianPair :=
  measurePreserving_fst.hasLaw

theorem gaussianPair_snd : HasLaw (Prod.snd : ℝ × ℝ → ℝ) (gaussianReal 0 1) gaussianPair :=
  measurePreserving_snd.hasLaw

theorem gaussianPair_independent : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd gaussianPair := by
  exact (indepFun_iff_hasLaw_prodMk_prod gaussianPair_fst gaussianPair_snd).2 HasLaw.id

theorem gaussianPair_gaussian : HasGaussianLaw (fun p : ℝ × ℝ => p) gaussianPair :=
  gaussianPair_independent.hasGaussianLaw gaussianPair_fst.hasGaussianLaw gaussianPair_snd.hasGaussianLaw

theorem gaussianMix_gaussian (a b : ℝ) : HasGaussianLaw (gaussianMix a b) gaussianPair :=
  gaussianPair_gaussian.map_fun (gaussianMixCLM a b)

theorem gaussianMix_mean (a b : ℝ) : (∫ p, gaussianMix a b p ∂gaussianPair)=0 := by
  unfold gaussianMix
  rw [integral_add (gaussianPair_fst.hasGaussianLaw.integrable.const_mul a)
    (gaussianPair_snd.hasGaussianLaw.integrable.const_mul b),integral_const_mul,integral_const_mul]
  have hf := gaussianPair_fst.integral_comp (continuous_id.aestronglyMeasurable)
  have hs := gaussianPair_snd.integral_comp (continuous_id.aestronglyMeasurable)
  simp only [Function.comp_def,id_eq,integral_id_gaussianReal] at hf hs
  rw [hf,hs]; ring

theorem gaussianMix_covariance (a b c d : ℝ) :
    cov[gaussianMix a b,gaussianMix c d;gaussianPair]=a*c+b*d := by
  have hcross : cov[(Prod.fst : ℝ × ℝ → ℝ),Prod.snd;gaussianPair]=0 :=
    gaussianPair_independent.covariance_eq_zero gaussianPair_fst.hasGaussianLaw.memLp_two
      gaussianPair_snd.hasGaussianLaw.memLp_two
  have hf : cov[(Prod.fst : ℝ × ℝ → ℝ),Prod.fst;gaussianPair]=1 := by
    rw [covariance_self gaussianPair_fst.aemeasurable]
    have H := gaussianPair_fst.variance_eq
    simpa only [variance_id_gaussianReal,NNReal.coe_one] using H
  have hs : cov[(Prod.snd : ℝ × ℝ → ℝ),Prod.snd;gaussianPair]=1 := by
    rw [covariance_self gaussianPair_snd.aemeasurable]
    have H := gaussianPair_snd.variance_eq
    simpa only [variance_id_gaussianReal,NNReal.coe_one] using H
  unfold gaussianMix
  rw [SK.covariance_linear_combination gaussianPair_fst.hasGaussianLaw.memLp_two
    gaussianPair_snd.hasGaussianLaw.memLp_two gaussianPair_fst.hasGaussianLaw.memLp_two
    gaussianPair_snd.hasGaussianLaw.memLp_two,hf,hs,hcross,covariance_comm Prod.snd,hcross]
  ring

theorem gaussianMix_law (a b : ℝ) (hab : a^2+b^2=1) :
    HasLaw (gaussianMix a b) (gaussianReal 0 1) gaussianPair := by
  have hg := gaussianMix_gaussian a b
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,gaussianMix_mean,← covariance_self hg.aemeasurable,
    gaussianMix_covariance]
  have he : a*a+b*b=1 := by nlinarith [hab]
  rw [he]; norm_num

theorem gaussianRotate_law (θ : ℝ) : HasLaw (gaussianRotate θ) gaussianPair gaussianPair := by
  have hg : HasGaussianLaw (gaussianRotate θ) gaussianPair :=
    gaussianPair_gaussian.map_fun ((gaussianMixCLM (Real.cos θ) (Real.sin θ)).prod
      (gaussianMixCLM (-Real.sin θ) (Real.cos θ)))
  have hi := hg.indepFun_of_covariance_eq_zero (by rw [gaussianMix_covariance]; ring)
  exact hi.hasLaw_prod
    (gaussianMix_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))
    (gaussianMix_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))

theorem gaussianRotate_inverse (θ : ℝ) (p : ℝ × ℝ) :
    gaussianRotate (-θ) (gaussianRotate θ p)=p := by
  ext <;> simp only [gaussianRotate,gaussianMix,Real.cos_neg,Real.sin_neg]
  · calc
      _=(Real.sin θ^2+Real.cos θ^2)*p.1 := by ring
      _=p.1 := by rw [Real.sin_sq_add_cos_sq]; ring
  · calc
      _=(Real.sin θ^2+Real.cos θ^2)*p.2 := by ring
      _=p.2 := by rw [Real.sin_sq_add_cos_sq]; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianPair_integrable_bounded {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) : Integrable f gaussianPair := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hB p)

theorem gaussianPair_integrable_linear_bounded {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    {B C : ℝ} (hB : ∀ p, |f p| ≤ B*(|p.1|+|p.2|)+C) : Integrable f gaussianPair := by
  have hi := ((gaussianPair_fst.hasGaussianLaw.integrable.norm.add
    gaussianPair_snd.hasGaussianLaw.integrable.norm).const_mul B).add (integrable_const C)
  apply hi.mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Pi.add_apply] using hB p)

theorem gaussianPair_rotation_derivative {f g dg : ℝ → ℝ}
    (hf : Continuous f) (hd : ∀ x, HasDerivAt g (dg x) x) (hc : Continuous dg)
    {B D C : ℝ} (hB : 0 ≤ B) (_hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdg : ∀ x, |g x| ≤ D) (hdc : ∀ x, |dg x| ≤ C) (θ : ℝ) :
    HasDerivAt (fun a => ∫ p, f p.1*g (gaussianMix (Real.cos a) (Real.sin a) p) ∂gaussianPair)
      (∫ p, f p.1*dg (gaussianMix (Real.cos θ) (Real.sin θ) p)*
        gaussianMix (-Real.sin θ) (Real.cos θ) p ∂gaussianPair) θ := by
  have hg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hm (a : ℝ) (p : ℝ × ℝ) :
      |gaussianMix (-Real.sin a) (Real.cos a) p| ≤ |p.1|+|p.2| := by
    unfold gaussianMix
    calc
      _ ≤ |-Real.sin a*p.1|+|Real.cos a*p.2| := abs_add_le _ _
      _ ≤ |p.1|+|p.2| := by
        simp only [abs_mul,abs_neg]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
  have hi : Integrable (fun p : ℝ × ℝ => B*C*(|p.1|+|p.2|)) gaussianPair := by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using
      ((gaussianPair_fst.hasGaussianLaw.integrable.norm.add
        gaussianPair_snd.hasGaussianLaw.integrable.norm).const_mul (B*C))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ) (x₀:=θ)
    (F:=fun a p => f p.1*g (gaussianMix (Real.cos a) (Real.sin a) p))
    (F':=fun a p => f p.1*dg (gaussianMix (Real.cos a) (Real.sin a) p)*gaussianMix (-Real.sin a) (Real.cos a) p)
    (bound:=fun p : ℝ × ℝ => B*C*(|p.1|+|p.2|)) (by simp) _ _ _ _ hi _).2
  · exact Eventually.of_forall (fun a => (hf.comp continuous_fst |>.mul
      (hg.comp (by unfold gaussianMix; fun_prop))).aestronglyMeasurable)
  · apply gaussianPair_integrable_bounded (hf.comp continuous_fst |>.mul
      (hg.comp (by unfold gaussianMix; fun_prop)))
    intro p; simp only [Function.comp_def,Pi.mul_apply,abs_mul]; exact mul_le_mul (hb _) (hdg _) (abs_nonneg _) hB
  · exact (((hf.comp continuous_fst).mul (hc.comp (by unfold gaussianMix; fun_prop))).mul
      (by unfold gaussianMix; fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun p a _ => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul]
      exact mul_le_mul (mul_le_mul (hb _) (hdc _) (abs_nonneg _) hB) (hm a p)
        (abs_nonneg _) (mul_nonneg hB hC))
  · exact ae_of_all _ (fun p a _ => by
      have H := (hd (gaussianMix (Real.cos a) (Real.sin a) p)).comp a
        (((Real.hasDerivAt_cos a).mul_const p.1).add ((Real.hasDerivAt_sin a).mul_const p.2))
      simpa only [gaussianMix,mul_assoc,Function.comp_def,Pi.add_apply] using H.const_mul (f p.1))

theorem gaussianPair_rotation_stein {f df k : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df) (hk : Continuous k)
    {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) (hkd : ∀ x, |k x| ≤ D) (θ : ℝ) :
    (∫ p, f p.1*k (gaussianMix (Real.cos θ) (Real.sin θ) p)*
        gaussianMix (-Real.sin θ) (Real.cos θ) p ∂gaussianPair)=
      -Real.sin θ*(∫ p, df p.1*k (gaussianMix (Real.cos θ) (Real.sin θ) p) ∂gaussianPair) := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  let A : ℝ × ℝ → ℝ := fun p => f (gaussianMix (Real.cos θ) (-Real.sin θ) p)*k p.1*p.2
  let A' : ℝ × ℝ → ℝ := fun p => df (gaussianMix (Real.cos θ) (-Real.sin θ) p)*k p.1
  have hAc : Continuous A := by dsimp [A,gaussianMix]; fun_prop
  have hA'c : Continuous A' := by dsimp [A',gaussianMix]; fun_prop
  have heq (p : ℝ × ℝ) : gaussianMix (Real.cos θ) (-Real.sin θ) (gaussianRotate θ p)=p.1 := by
    have H := congrArg Prod.fst (gaussianRotate_inverse θ p)
    simpa only [gaussianRotate,Real.cos_neg,Real.sin_neg] using H
  have hA : (fun p => A (gaussianRotate θ p))=(fun p => f p.1*
      k (gaussianMix (Real.cos θ) (Real.sin θ) p)*gaussianMix (-Real.sin θ) (Real.cos θ) p) := by
    funext p; dsimp only [A]; rw [heq]; rfl
  have hA' : (fun p => A' (gaussianRotate θ p))=(fun p => df p.1*
      k (gaussianMix (Real.cos θ) (Real.sin θ) p)) := by
    funext p; dsimp only [A']; rw [heq]; rfl
  have HA := (gaussianRotate_law θ).integral_comp hAc.aestronglyMeasurable
  have HA' := (gaussianRotate_law θ).integral_comp hA'c.aestronglyMeasurable
  simp only [Function.comp_def] at HA HA'
  rw [← hA,← hA',HA,HA']
  have hAi : Integrable A gaussianPair := by
    apply gaussianPair_integrable_linear_bounded hAc (B:=B*D) (C:=0)
    intro p
    dsimp [A]; rw [abs_mul,abs_mul]
    calc
      _ ≤ B*D*|p.2| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hb _) (hkd _) (abs_nonneg _) hB) (abs_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hB hD,abs_nonneg p.1]
  have hA'i : Integrable A' gaussianPair := by
    apply gaussianPair_integrable_bounded hA'c
    intro p
    dsimp [A']; rw [abs_mul]
    exact mul_le_mul (hdf _) (hkd _) (abs_nonneg _) hC
  rw [show gaussianPair=(gaussianReal 0 1).prod (gaussianReal 0 1) from rfl,
    integral_prod _ hAi,integral_prod _ hA'i,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    have hfc : Continuous (fun z : ℝ => f (Real.cos θ*y-Real.sin θ*z)) := by fun_prop
    have hdfc : Continuous (fun z : ℝ => -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z)) := by fun_prop
    have hfint : Integrable (fun z : ℝ => f (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) :=
      (integrable_const B).mono' hfc.aestronglyMeasurable (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb _))
    have hdint : Integrable (fun z : ℝ => -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) := by
      apply (integrable_const (|Real.sin θ| *C)).mono' hdfc.aestronglyMeasurable
      exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_mul,abs_neg]; exact mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _))
    have hzint : Integrable (fun z : ℝ => z*f (Real.cos θ*y-Real.sin θ*z)) (gaussianReal 0 1) := by
      apply ((HasExpGrowth.norm_id (E:=ℝ)).integrable_gaussianMeasure continuous_norm (μ:=gaussianReal 0 1) |>.mul_const B).mono'
        (continuous_id.mul hfc).aestronglyMeasurable
      exact ae_of_all _ (fun z => by simp only [Real.norm_eq_abs,Pi.mul_apply,id_eq,abs_mul]; exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _))
    have H := gaussian_integral_mul_eq_integral_deriv _ _ (fun z => by
      simpa only [mul_comm,Function.comp_def,Pi.sub_apply,id_eq,mul_one,one_mul,zero_sub] using (hd (Real.cos θ*y-Real.sin θ*z)).comp z
        ((hasDerivAt_const z (Real.cos θ*y)).sub ((hasDerivAt_id z).const_mul (Real.sin θ)))) hfint hdint hzint
    dsimp only [A,A',gaussianMix]
    simp only [neg_mul,← sub_eq_add_neg]
    calc
      _=k y*(∫ z : ℝ, z*f (Real.cos θ*y-Real.sin θ*z) ∂gaussianReal 0 1) := by
        rw [← integral_const_mul]; congr 1; funext z; ring
      _=k y*(∫ z : ℝ, -Real.sin θ*df (Real.cos θ*y-Real.sin θ*z) ∂gaussianReal 0 1) := by rw [H]
      _=_ := by rw [integral_const_mul,integral_mul_const]; ring)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianAngle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianAngle_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    Continuous (gaussianAngle f g) := by
  apply continuous_iff_continuousAt.mpr
  intro θ
  apply continuousAt_of_dominated (bound:=fun _ : ℝ × ℝ => B*C)
  · exact Eventually.of_forall (fun a => ((hf.comp continuous_fst).mul
      (hg.comp (by unfold gaussianMix; fun_prop))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun p => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hb _) (hc _) (abs_nonneg _) hB))
  · exact integrable_const _
  · exact ae_of_all _ (fun p => (continuous_const.mul
      (hg.comp (by unfold gaussianMix; fun_prop))).continuousAt)

theorem gaussian_integrable_bounded {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f (gaussianReal 0 1) := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem gaussian_integrable_sq_bounded {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Integrable (fun x => f x^2) (gaussianReal 0 1) :=
  gaussian_integrable_bounded (hf.pow 2) (fun x => by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x))

theorem gaussianAngle_zero (f : ℝ → ℝ) (hf : Continuous f) :
    gaussianAngle f f 0=∫ x, f x^2 ∂gaussianReal 0 1 := by
  have H := gaussianPair_fst.integral_comp (hf.pow 2).aestronglyMeasurable
  simpa only [gaussianAngle,gaussianMix,Real.cos_zero,Real.sin_zero,one_mul,zero_mul,
    add_zero,pow_two,Function.comp_def,Pi.mul_apply] using H

theorem gaussianAngle_pi_half {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |g x| ≤ C) :
    gaussianAngle f g (Real.pi/2)=(∫ x, f x ∂gaussianReal 0 1)*(∫ x, g x ∂gaussianReal 0 1) := by
  have hi : Integrable (fun p : ℝ × ℝ => f p.1*g p.2) gaussianPair :=
    gaussianPair_integrable_bounded (by fun_prop) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hb _) (hc _) (abs_nonneg _) hB)
  simp only [gaussianAngle,gaussianMix,Real.cos_pi_div_two,Real.sin_pi_div_two,
    zero_mul,one_mul,zero_add,gaussianPair]
  rw [integral_prod _ hi]
  simp only [integral_const_mul,integral_mul_const]

theorem gaussianAngle_le_square {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (θ : ℝ) :
    gaussianAngle f f θ ≤ ∫ x, f x^2 ∂gaussianReal 0 1 := by
  have hfc : Continuous (fun p : ℝ × ℝ => f p.1) := hf.comp continuous_fst
  have hgc : Continuous (fun p : ℝ × ℝ => f (gaussianMix (Real.cos θ) (Real.sin θ) p)) :=
    hf.comp (by unfold gaussianMix; fun_prop)
  have hi : Integrable (fun p : ℝ × ℝ => f p.1*f (gaussianMix (Real.cos θ) (Real.sin θ) p)) gaussianPair :=
    gaussianPair_integrable_bounded (hfc.mul hgc) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hb _) (hb _) (abs_nonneg _) hB)
  have hb2 (x : ℝ) : |f x^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x)
  have hf2 := gaussianPair_integrable_bounded (hfc.pow 2) (fun p => hb2 p.1)
  have hg2 := gaussianPair_integrable_bounded (hgc.pow 2) (fun p => hb2 _)
  have H := integral_mono (hi.const_mul 2) (hf2.add hg2)
    (fun p => by dsimp; nlinarith [sq_nonneg (f p.1-f (gaussianMix (Real.cos θ) (Real.sin θ) p))])
  simp only [Pi.add_apply,Pi.pow_apply] at hf2 hg2 H
  have Hplus := integral_add hf2 hg2
  simp only [Pi.pow_apply] at Hplus
  rw [integral_const_mul,Hplus] at H
  have HA := gaussianPair_fst.integral_comp (hf.pow 2).aestronglyMeasurable
  have HB := (gaussianMix_law (Real.cos θ) (Real.sin θ)
    (by nlinarith [Real.sin_sq_add_cos_sq θ])).integral_comp (hf.pow 2).aestronglyMeasurable
  simp only [Function.comp_def,Pi.pow_apply] at HA HB
  rw [HA,HB] at H
  exact (by change _ ≤ _; unfold gaussianAngle; linarith)

theorem gaussian_variance_pos {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B)
    (hne : ¬∃ c, ∀ x, f x=c) :
    (∫ x, f x ∂gaussianReal 0 1)^2 < ∫ x, f x^2 ∂gaussianReal 0 1 := by
  let a : ℝ := ∫ x, f x ∂gaussianReal 0 1
  have hint := gaussian_integrable_bounded hf hb
  have hi2 := gaussian_integrable_sq_bounded hf hB hb
  have his : Integrable (fun x => (f x-a)^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hf.sub continuous_const) (B:=B+|a|) (by positivity)
      (fun x => (abs_sub _ _).trans (add_le_add (hb x) (le_refl _)))
  have hp : 0<∫ x, (f x-a)^2 ∂gaussianReal 0 1 := by
    apply lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (f x-a)))
    intro he
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x-a)) his).mp he.symm
    have hv := hz.filter_mono (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:ℝ≥0)≠0)).ae_le
    have heq := MeasureTheory.Measure.eq_of_ae_eq hv ((hf.sub continuous_const).pow 2) continuous_const
    apply hne
    refine ⟨a,fun x => ?_⟩
    have H := congrFun heq x
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp H)
  have he : (∫ x, (f x-a)^2 ∂gaussianReal 0 1)=
      (∫ x, f x^2 ∂gaussianReal 0 1)-a^2 := by
    simp_rw [show ∀ x, (f x-a)^2=f x^2-2*a*f x+a^2 by intro x; ring]
    have Hplus := integral_add (hi2.sub (hint.const_mul (2*a))) (integrable_const (a^2))
    have Hsub := integral_sub hi2 (hint.const_mul (2*a))
    simp only [Pi.sub_apply] at Hplus Hsub
    rw [Hplus,Hsub,integral_const_mul]
    simp only [integral_const,probReal_univ,one_smul]
    dsimp only [a]; ring
  rw [he] at hp
  exact sub_pos.mp hp

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAtomic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileAtomLaw_supported (k : ℕ) (Q : Fin (k+1) → ℝ) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    quantileAtomLaw k Q (Set.Icc 0 1) = 1 := by
  rw [quantileAtomLaw_apply]
  simp only [hQ,ite_true,uniformAtom_sum,ENNReal.ofReal_one]

theorem quantileCDF_integral (k : ℕ) (Q : Fin (k+1) → ℝ) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    (∫ s in Set.Icc (0:ℝ) 1, s*quantileCDF k Q s) =
      (1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)/2 := by
  have he (s : ℝ) : s*quantileCDF k Q s =
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Set.Ici (Q j)).indicator (fun x => x) s := by
    rw [quantileCDF_formula,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Set.indicator_apply,Set.mem_Ici]
    split_ifs <;> ring
  have hi (j : Fin (k+1)) : IntegrableOn ((Set.Ici (Q j)).indicator (fun x : ℝ => x)) (Set.Icc (0:ℝ) 1) :=
    (continuous_id.integrableOn_Icc).indicator measurableSet_Ici
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => (hi j).const_mul _)]
  have hI (j : Fin (k+1)) : (∫ s in Set.Icc (0:ℝ) 1,
      ((k+1:ℕ):ℝ)⁻¹*(Set.Ici (Q j)).indicator (fun x => x) s) =
      ((k+1:ℕ):ℝ)⁻¹*((1-(Q j)^2)/2) := by
    rw [integral_const_mul,setIntegral_indicator measurableSet_Ici]
    have hs : Set.Icc (0:ℝ) 1 ∩ Set.Ici (Q j) = Set.Icc (Q j) 1 := by
      ext x
      simp only [Set.mem_inter_iff,Set.mem_Icc,Set.mem_Ici]
      constructor
      · intro H; exact ⟨H.2,H.1.2⟩
      · intro H; exact ⟨⟨(hQ j).1.trans H.1,H.2⟩,H.1⟩
    rw [hs,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (hQ j).2,integral_id,one_pow]
  simp_rw [hI]
  have he' (j : Fin (k+1)) : ((k+1:ℕ):ℝ)⁻¹*((1-(Q j)^2)/2) =
      (((k+1:ℕ):ℝ)⁻¹-((k+1:ℕ):ℝ)⁻¹*(Q j)^2)/2 := by ring
  simp_rw [he']
  rw [← Finset.sum_div,Finset.sum_sub_distrib,uniformAtom_sum]

theorem atomicParisi_eq_extended (k : ℕ) (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    atomicParisi k β Q = extendedQuantileParisi k β Q := by
  rw [atomicParisi,atomicScalarValue,scalar_quantile_terminal_shift k β Q (hQ (Fin.last k)).2,
    quantileCDF_integral k Q hQ,extendedQuantileParisi]
  ring
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_knots_gap (k : ℕ) (Q : Fin (k+1) → ℝ) (i : Fin (k+1)) :
    Fin.cons (α := fun _ => ℝ) 0 Q i.succ-Fin.cons (α := fun _ => ℝ) 0 Q i.castSucc=cumulativeGapMap k Q i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · rfl

theorem quantile_prefix_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) :
    ∃ l : List (ℝ × ℝ≥0),
      (chainDuration l:ℝ)=Q (Fin.last k) ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧
      TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β f, scalarTimeChain β l f=scalarHierarchy (k+1) (quantileMass k)
        (fun i => β*Real.sqrt (cumulativeGapMap k Q i)) f := by
  let q := Fin.cons (α := fun _ => ℝ) 0 Q
  let hq := monotone_cons_zero_quantiles Q hQ h0
  let l := partitionTimeChain (k+1) q hq (quantileMass k)
  refine ⟨l,?_,?_,?_,?_⟩
  · have H := partitionTimeChain_duration (k+1) q hq (quantileMass k)
    simpa only [q,← Fin.succ_last,Fin.cons_succ,Fin.cons_zero,sub_zero] using H
  · intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    change quantileMass k i ∈ Icc (0:ℝ) 1
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · apply (div_le_one (by positivity : (0:ℝ)<(k+1:ℕ))).mpr
      exact_mod_cast i.isLt.le
  · change TimeChainModels (quantileCDF k Q) (q 0) (partitionTimeChain (k+1) q hq (quantileMass k))
    apply partitionTimeChain_models
    intro i z hz
    exact quantileCDF_on_interval Q hQ i z hz
  · intro β f
    dsimp only [l,partitionTimeChain]
    rw [scalarTimeChain_ofFn]
    congr 2
    funext i
    simp only [NNReal.coe_mk, q]
    rw [quantile_knots_gap]
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFAtomicRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantile_full_chain {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) (h1 : Q (Fin.last k) ≤ 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=1 ∧
      (∀ p ∈ l, p.1 ∈ Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) 0 l ∧
      ∀ β, scalarTimeChain β l scalarSpinTerminal 0=atomicScalarValue k β Q := by
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_prefix_chain Q hQ h0
  let t := NNReal.mk (1-Q (Fin.last k)) (sub_nonneg.mpr h1)
  refine ⟨l++[(1,t)],?_,?_,?_,?_⟩
  · apply NNReal.coe_injective
    simp only [chainDuration_append,chainDuration_cons,chainDuration_nil,add_zero,
      NNReal.coe_add,hd,t,NNReal.coe_mk,NNReal.coe_one]
    ring
  · intro p hp
    rcases List.mem_append.mp hp with hp|hp
    · exact hm p hp
    · have hp' := List.mem_singleton.mp hp
      subst p
      exact ⟨zero_le_one,le_rfl⟩
  · apply hmodel.append
    constructor
    · intro z hz
      apply quantileCDF_of_last_le Q hQ
      simpa only [zero_add,hd] using hz.1
    · trivial
  · intro β
    rw [scalarTimeChain_append]
    simp only [scalarTimeChain]
    rw [he]
    rfl

theorem scalarCDFValue_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Monotone Q) (h0 : 0 ≤ Q 0) (h1 : Q (Fin.last k) ≤ 1) :
    scalarCDFValue β (quantileCDF k Q) 0 1 0=atomicScalarValue k β Q := by
  obtain ⟨l,hd,hm,hmodel,he⟩ := quantile_full_chain Q hQ h0 h1
  exact (scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
    β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l hm 0 1 le_rfl hd hmodel 0).trans (he β)

theorem scalarCDFParisi_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q ∈ admissibleQuantiles k) :
    scalarCDFParisi β (quantileCDF k Q)=extendedQuantileParisi k β Q := by
  rw [scalarCDFParisi,scalarCDFValue_quantile β Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2]
  exact atomicParisi_eq_extended k β Q hQ.2

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFDerivativeConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem uniform_derivative_convergence {F D : ℕ → ℝ → ℝ} {f d : ℝ → ℝ} (K : ℝ≥0)
    (hD : ∀ n x, HasDerivAt (F n) (D n x) x) (hd : ∀ x, HasDerivAt f (d x) x)
    (hLip : ∀ n, LipschitzWith K (D n)) (hlip : LipschitzWith K d)
    (hF : TendstoUniformly F f atTop) : TendstoUniformly D d atTop := by
  rw [Metric.tendstoUniformly_iff] at hF ⊢
  intro ε hε
  let h : ℝ := ε/(8*((K:ℝ)+1))
  have hh : 0<h := div_pos hε (by positivity)
  have hke : 8*((K:ℝ)+1)*h=ε := by dsimp [h]; field_simp
  let δ : ℝ := ε*h/8
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [hF δ hδ] with n hn x
  have hb (z : ℝ) : |F n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hn z).le
  have H := derivative_bound_of_uniform_value_and_lipschitz _ _ (K+K) δ
    (fun z => (hD n z).sub (hd z)) ((hLip n).sub hlip) hb x h hh
  have he : 2*δ/h=ε/4 := by dsimp [δ]; field_simp; ring
  rw [he,NNReal.coe_add] at H
  rw [Real.dist_eq,abs_sub_comm]
  have hk := K.coe_nonneg
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOperator_uniform_nonexpansive {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : LipschitzWith L g)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) {ε : ℝ} (hfg : ∀ x, |f x-g x|≤ε) (x : ℝ) :
    |scalarCDFOperator β α s t f x-scalarCDFOperator β α s t g x|≤ε := by
  apply le_of_tendsto (((dyadicScalar_general_uniform hf hK β hα hm s t ht).tendsto_at x).sub
    ((dyadicScalar_general_uniform hg hL β hα hm s t ht).tendsto_at x)).abs
  exact Eventually.of_forall (fun n => dyadicScalar_uniform_nonexpansive hf hg β hα n s t hfg x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSuffixSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOperator_semigroup_of_chain {f : ℝ → ℝ}
    (hf : BoundedDerivs f) {K : ℝ≥0} (hK : LipschitzWith K f)
    (β : ℝ) {α : ℝ → ℝ} (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t r : ℝ≥0) (htr : t+r ≤ 1) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1) (hd : chainDuration l=t+r)
    (hmodel : TimeChainModels α s l) :
    scalarCDFOperator β α s (t+r) f=
      scalarCDFOperator β α s t (scalarCDFOperator β α (s+t) r f) := by
  have ht : t ≤ 1 := (le_add_of_nonneg_right (show (0:ℝ≥0) ≤ r from bot_le)).trans htr
  have hr : r ≤ 1 := (le_add_of_nonneg_left (show (0:ℝ≥0) ≤ t from bot_le)).trans htr
  obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,hs₁,hs₂,he⟩ := scalarTimeChain_split_at β α l hm s hmodel t r hd
  have htail : scalarCDFOperator β α (s+t) r f=scalarTimeChain β l₂ f := by
    funext x
    exact scalarCDFOperator_eq_chain hf hK β ha hmono l₂ hm₂ (s+t) r hr h₂ hs₂ x
  funext x
  rw [htail,scalarCDFOperator_eq_chain hf hK β ha hmono l hm s (t+r) htr hd hmodel,
    scalarCDFOperator_eq_chain (scalarTimeChain_regular hf β l₂)
      (scalarTimeChain_lipschitz hf hK β l₂ (fun p hp => (hm₂ p hp).1))
      β ha hmono l₁ hm₁ s t ht h₁ hs₁]
  exact (congrFun (he f hf) x).symm

theorem quantile_suffix_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=Real.toNNReal (1-s) ∧
      (∀ p∈l, p.1∈Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have he : chainDuration l=Real.toNNReal s+Real.toNNReal (1-s) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal s hs.1,Real.coe_toNNReal (1-s) (sub_nonneg.mpr hs.2),NNReal.coe_one]
    ring
  obtain ⟨_,l₂,_,h₂,_,hm₂,_,hs₂,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm 0 hmodel _ _ he
  exact ⟨l₂,h₂,hm₂,by simpa only [zero_add,Real.coe_toNNReal s hs.1] using hs₂⟩

theorem scalarCDFValue_suffix_semigroup_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s q : ℝ} (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) :
    scalarCDFValue β (quantileCDF k Q) s (Real.toNNReal (1-s))=
      scalarCDFOperator β (quantileCDF k Q) s (Real.toNNReal (q-s))
        (scalarCDFValue β (quantileCDF k Q) q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal (q-s)
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q-s := Real.coe_toNNReal _ (sub_nonneg.mpr hsq)
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq)
  have hb : t+r=Real.toNNReal (1-s) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,ht,hr,Real.coe_toNNReal _ (by linarith)]
    ring
  have htr : t+r ≤ 1 := by rw [← NNReal.coe_le_coe,NNReal.coe_add,ht,hr,NNReal.coe_one]; linarith
  obtain ⟨l,hd,hm,hmodel⟩ := quantile_suffix_chain β Q hQ ⟨hs,hsq.trans hq⟩
  have H := scalarCDFOperator_semigroup_of_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
    β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) s t r htr l hm (hd.trans hb.symm) hmodel
  rw [hb,show s+(t:ℝ)=q by rw [ht]; ring] at H
  exact H

theorem scalarCDFValue_suffix_semigroup (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) :
    scalarCDFValue β α s (Real.toNNReal (1-s))=
      scalarCDFOperator β α s (Real.toNNReal (q-s))
        (scalarCDFValue β α q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal (q-s)
  let r := Real.toNNReal (1-q)
  let u := Real.toNNReal (1-s)
  have ht : (t:ℝ)=q-s := Real.coe_toNNReal _ (sub_nonneg.mpr hsq)
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq)
  have hu : (u:ℝ)=1-s := Real.coe_toNNReal _ (sub_nonneg.mpr (hsq.trans hq))
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; linarith
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith
  have hu1 : u ≤ 1 := by rw [← NNReal.coe_le_coe,hu,NNReal.coe_one]; linarith
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hb (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD : Tendsto (fun n => cdfDistance (a n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α ha h1
  funext x
  have hvalue (n : ℕ) {b : ℝ} {v : ℝ≥0} (hb0 : 0 ≤ b) (hv1 : b+v ≤ 1) (hv : v ≤ 1) (z : ℝ) :
      |scalarCDFValue β (a n) b v z-scalarCDFValue β α b v z| ≤ scalarTimeMassConstant β*cdfDistance (a n) α :=
    (scalarCDFValue_cdf_lipschitz β (hb n) (hm n) ha α.mono b v hv z).trans
      (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono hb0 hv1)
        (scalarTimeMassConstant_nonneg β))
  have herr (n : ℕ) : |scalarCDFValue β α s u x-
      scalarCDFOperator β α s t (scalarCDFValue β α q r) x| ≤
      (2*scalarTimeMassConstant β+scalarTimeMassConstantK β 1)*cdfDistance (a n) α := by
    have E := hvalue n (hs.trans hsq) (v:=r) (by rw [hr]; linarith) hr1
    have H₁ := scalarCDFOperator_uniform_nonexpansive
      (scalarCDFValue_regular β (hb n) (hm n) q r hr1) (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β (hb n) (hm n) q r hr1) (scalarCDFValue_lipschitz β ha α.mono q r hr1)
      β (hb n) (hm n) s t ht1 E x
    have H₂ := (scalarCDFOperator_cdf_lipschitz (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β ha α.mono q r hr1) β (hb n) (hm n) ha α.mono s t ht1 x).trans
      (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono hs (by rw [ht]; linarith))
        (scalarTimeMassConstantK_nonneg β 1))
    have H₀ := hvalue n hs (v:=u) (by rw [hu]; linarith) hu1 x
    rw [abs_sub_comm] at H₀
    have he := congrFun (scalarCDFValue_suffix_semigroup_quantile β (uniformCDFQuantiles n α)
      (uniformCDFQuantiles_admissible n α h1) hs hsq hq) x
    calc
      _  ≤  |scalarCDFValue β α s u x-scalarCDFValue β (a n) s u x|+
          |scalarCDFValue β (a n) s u x-scalarCDFOperator β α s t (scalarCDFValue β α q r) x| := abs_sub_le _ _ _
      _  ≤  scalarTimeMassConstant β*cdfDistance (a n) α+
          (scalarTimeMassConstant β+scalarTimeMassConstantK β 1)*cdfDistance (a n) α := by
        apply add_le_add H₀
        change |scalarCDFValue β (quantileCDF n (uniformCDFQuantiles n α)) s (Real.toNNReal (1-s)) x-_| ≤ _
        rw [he]
        exact (abs_sub_le _ _ _).trans ((add_le_add H₁ H₂).trans_eq (by ring))
      _ = _ := by ring
  have H := ge_of_tendsto (hD.const_mul (2*scalarTimeMassConstant β+scalarTimeMassConstantK β 1))
    (Eventually.of_forall herr)
  simp only [mul_zero] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFHeatPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianHeat_hasDerivAt {f df : ℝ → ℝ} (hf : BoundedDerivs f)
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {C : ℝ} (hb : ∀ x, |df x|  ≤  C) (v x : ℝ) :
    HasDerivAt (gaussianHeat v f) (gaussianHeat v df x) x := by
  let L : ℝ →L[ℝ] ℝ := v • ContinuousLinearMap.id ℝ ℝ
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ) (x₀:=x)
    (F:=fun a z => f (a+v*z)) (F':=fun a z => df (a+v*z)) (bound:=fun _ : ℝ => C)
    (by simp) _ _ _ _ (integrable_const C) _).2
  · exact Eventually.of_forall (fun a => (hf.1.continuous.comp (by fun_prop)).aestronglyMeasurable)
  · exact ((hf.translate x).compCLM L).hasExpGrowth.integrable_gaussianMeasure
      ((hf.translate x).compCLM L).1.continuous
  · exact (hc.comp (by fun_prop)).aestronglyMeasurable
  · exact ae_of_all _ (fun z a _ => by simpa only [Real.norm_eq_abs] using hb (a+v*z))
  · exact ae_of_all _ (fun z a _ => by
      convert (hd (a+v*z)).comp a ((hasDerivAt_id a).add_const (v*z)) using 1 <;> first | rfl | simp)

theorem scalarCDFOperator_zero_on {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hK : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1)
    (hz : ∀ z∈Ico s (s+t), α z=0) :
    scalarCDFOperator β α s t f=gaussianHeat (β*Real.sqrt (t:ℝ)) f := by
  funext x
  rw [scalarCDFOperator_eq_chain hf hK β ha hm [(0,t)] (by simp) s t ht (by simp)
    (show TimeChainModels α s [(0,t)] from ⟨hz,True.intro⟩)]
  simp [scalarTimeChain,scalarTimeStep,scalarStep,gaussianStep,gaussianHeat]

theorem scalarCDFAverage_zero_on {f g dg : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : ∀ y, HasDerivAt g (dg y) y) (hc : Continuous dg)
    {K B C : ℝ≥0} (hK : LipschitzWith K f)
    (hB : ∀ y, |g y|  ≤  B) (hC : ∀ y, |dg y|  ≤  C)
    (β : ℝ) {α : ℝ → ℝ} (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (hz : ∀ z∈Ico s (s+t), α z=0) (x : ℝ) :
    scalarCDFAverage β α s t f g x=gaussianHeat (β*Real.sqrt (t:ℝ)) g x := by
  rw [scalarCDFAverage_eq_chainAverage hf hg hc hK hB hC β ha hm [(0,t)] (by simp)
    s t ht (by simp) (show TimeChainModels α s [(0,t)] from ⟨hz,True.intro⟩)]
  simp [scalarTimeChainAverage,scalarHierarchyAverage,scalarStepAverage,gaussianAverage,
    gaussianStepLaw,gaussianHeat]

theorem scalarCDFGradient_heat_prefix (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0 ≤ s) (hsq : s ≤ q) (hq : q ≤ 1) (hz : ∀ z∈Ico s q, α z=0) :
    scalarCDFGradient β α s (Real.toNNReal (1-s))=
      gaussianHeat (β*Real.sqrt (q-s)) (scalarCDFGradient β α q (Real.toNNReal (1-q))) := by
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have ht : Real.toNNReal (q-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hu : Real.toNNReal (1-s) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have he := scalarCDFValue_suffix_semigroup β α ha h1 hs hsq hq
  rw [scalarCDFOperator_zero_on (scalarCDFValue_regular β ha α.mono q _ hr)
    (scalarCDFValue_lipschitz β ha α.mono q _ hr) β ha α.mono s _ ht
    (by simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr hsq),add_sub_cancel] using hz),
    Real.coe_toNNReal _ (sub_nonneg.mpr hsq)] at he
  funext x
  have HD := scalarCDFValue_hasDerivAt β ha α.mono s _ hu x
  rw [he] at HD
  exact HD.unique (gaussianHeat_hasDerivAt (scalarCDFValue_regular β ha α.mono q _ hr)
    (scalarCDFValue_hasDerivAt β ha α.mono q _ hr)
    (scalarCDFGradient_lipschitz β ha α.mono q _ hr).continuous
    (fun y => (scalarCDF_derivative_bounds β ha α.mono q _ hr y).1) _ x)

theorem scalarCDFOverlap_heat_prefix (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α) {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) (hz : ∀ z∈Ico 0 q, α z=0) :
    scalarCDFOverlap β α q=∫ z, (scalarCDFGradient β α q (Real.toNNReal (1-q))
      (β*Real.sqrt q*z))^2 ∂gaussianReal 0 1 := by
  have ht : Real.toNNReal q ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; exact hq.2
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith [hq.1]
  obtain ⟨hd,hc,hB,hC⟩ := scalarCDFGradient_sq_regular β ha hm q _ hr
  unfold scalarCDFOverlap
  rw [scalarCDFAverage_zero_on (B:=1) (C:=2) (scalarCDFValue_regular β ha hm q _ hr) hd hc
    (scalarCDFValue_lipschitz β ha hm q _ hr) hB hC β ha hm 0 _ ht
    (by simpa only [zero_add,Real.coe_toNNReal _ hq.1] using hz)]
  simp only [gaussianHeat,Real.coe_toNNReal _ hq.1,zero_add]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianCramer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussian_covariance_derivative {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ z, z*f z ∂gaussianReal 0 1)=∫ z, df z ∂gaussianReal 0 1 := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  apply gaussian_integral_mul_eq_integral_deriv f df hd
    (gaussian_integrable_bounded hf hb) (gaussian_integrable_bounded hc hdf)
  apply ((gaussian_abs_pow_integrable 1).const_mul B).mono'
    ((continuous_id.mul hf).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simp only [Pi.mul_apply,id_eq,Real.norm_eq_abs,abs_mul]
    simpa only [pow_one,mul_comm] using mul_le_mul_of_nonneg_left (hb z) (abs_nonneg z))

theorem gaussian_cramer_variance {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ z, df z ∂gaussianReal 0 1)^2 ≤
      (∫ z, f z^2 ∂gaussianReal 0 1)-(∫ z, f z ∂gaussianReal 0 1)^2 := by
  let m := ∫ z, f z ∂gaussianReal 0 1
  let d := ∫ z, df z ∂gaussianReal 0 1
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hi := gaussian_integrable_bounded hf hb
  have h2 := gaussian_integrable_sq_bounded hf hB hb
  have hz : Integrable (fun z : ℝ => z) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable le_rfl
  have hz2 : Integrable (fun z : ℝ => z^2) (gaussianReal 0 1) := by
    simpa only [sq_abs] using gaussian_abs_pow_integrable 2
  have hfz : Integrable (fun z : ℝ => z*f z) (gaussianReal 0 1) := by
    apply ((gaussian_abs_pow_integrable 1).const_mul B).mono'
      ((continuous_id.mul hf).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      simp only [Pi.mul_apply,id_eq,Real.norm_eq_abs,abs_mul]
      simpa only [pow_one,mul_comm] using mul_le_mul_of_nonneg_left (hb z) (abs_nonneg z))
  have heq (z : ℝ) : (f z-m-d*z)^2 =
      f z^2-2*m*f z+m^2-2*d*(z*f z)+2*m*d*z+d^2*z^2 := by ring
  have H : 0 ≤ ∫ z, (f z-m-d*z)^2 ∂gaussianReal 0 1 := integral_nonneg (fun _ => sq_nonneg _)
  simp_rw [heq] at H
  have hA := integral_sub h2 (hi.const_mul (2*m))
  have hB' := integral_add (h2.sub (hi.const_mul (2*m))) (integrable_const (m^2))
  have hC' := integral_sub ((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2)))
    (hfz.const_mul (2*d))
  have hD' := integral_add (((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2))).sub
    (hfz.const_mul (2*d))) (hz.const_mul (2*m*d))
  have hE' := integral_add ((((h2.sub (hi.const_mul (2*m))).add (integrable_const (m^2))).sub
    (hfz.const_mul (2*d))).add (hz.const_mul (2*m*d))) (hz2.const_mul (d^2))
  simp only [Pi.add_apply,Pi.sub_apply] at hA hB' hC' hD' hE'
  rw [hE',hD',hC',hB',hA] at H
  rw [integral_const_mul (2*m*d) (fun z : ℝ => z),
    show (∫ z : ℝ, z ∂gaussianReal 0 1)=0 from integral_id_gaussianReal] at H
  simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,
    gaussian_second_moment,mul_zero,add_zero,mul_one,
    gaussian_covariance_derivative hd hc hb hdf] at H
  dsimp [m,d] at H ⊢
  nlinarith

theorem gaussianHeat_variance_lower {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (a x : ℝ) : a^2*(gaussianHeat a df x)^2 ≤
      gaussianHeat a (fun y => f y^2) x-(gaussianHeat a f x)^2 := by
  have HD (z : ℝ) : HasDerivAt (fun z => f (x+a*z)) (a*df (x+a*z)) z := by
    convert (hd (x+a*z)).comp z (((hasDerivAt_id z).const_mul a).const_add x) using 1 <;>
      first | rfl | ring
  have H := gaussian_cramer_variance HD (by fun_prop) hB (fun z => hb (x+a*z))
    (C:=|a| * C) (fun z => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hdf (x+a*z)) (abs_nonneg a))
  rw [integral_const_mul] at H
  simpa only [mul_pow,gaussianHeat] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianHeatVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianHeat_abs_le {f : ℝ → ℝ} {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    (a x : ℝ) : |gaussianHeat a f x| ≤ B := by
  have H := norm_integral_le_of_norm_le (μ:=gaussianReal 0 1) (f:=fun z => f (x+a*z)) (integrable_const B)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb (x+a*z)))
  simpa only [gaussianHeat,Real.norm_eq_abs,integral_const,probReal_univ,smul_eq_mul,one_mul] using H

theorem gaussianHeat_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hb : ∀ x, |f x| ≤ B) :
    Continuous (fun p : ℝ × ℝ => gaussianHeat p.1 f p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound:=fun _ : ℝ => B)
  · exact Eventually.of_forall (fun a => (hf.comp (by fun_prop)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      simpa only [Real.norm_eq_abs] using hb (a.2+a.1*z)))
  · exact integrable_const _
  · exact ae_of_all _ (fun z => (hf.comp (by fun_prop)).continuousAt)

theorem gaussianHeat_variance_integral_lower {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (a b c : ℝ) (he : c^2=b^2+a^2) :
    a^2*(∫ z, (gaussianHeat a df (b*z))^2 ∂gaussianReal 0 1) ≤
      (∫ z, f (c*z)^2 ∂gaussianReal 0 1)-
        (∫ z, (gaussianHeat a f (b*z))^2 ∂gaussianReal 0 1) := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hb2 (x : ℝ) : |f x^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hb x)
  have hdheat := gaussianHeat_continuous hc hdf
  have hfheat := gaussianHeat_continuous hf hb
  have hf2heat := gaussianHeat_continuous (hf.pow 2) hb2
  have hi1 : Integrable (fun z => (gaussianHeat a df (b*z))^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hdheat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) hC (fun z => gaussianHeat_abs_le hdf a _)
  have hi2 : Integrable (fun z => gaussianHeat a (fun y => f y^2) (b*z)) (gaussianReal 0 1) :=
    gaussian_integrable_bounded (hf2heat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) (fun z => gaussianHeat_abs_le hb2 a _)
  have hi3 : Integrable (fun z => (gaussianHeat a f (b*z))^2) (gaussianReal 0 1) :=
    gaussian_integrable_sq_bounded (hfheat.comp (show Continuous (fun z : ℝ => (a,b*z)) by fun_prop)) hB (fun z => gaussianHeat_abs_le hb a _)
  have H := integral_mono (hi1.const_mul (a^2)) (hi2.sub hi3)
    (fun z => gaussianHeat_variance_lower hd hc hB hb hdf a (b*z))
  have HI := integral_sub hi2 hi3
  simp only [Pi.sub_apply] at H
  rw [integral_const_mul,HI] at H
  have HC := integral_gaussian_sum (hf.pow 2)
    (HasExpGrowth.of_bounded (sq_nonneg B) (fun x => by
      simpa only [Real.norm_eq_abs,Pi.pow_apply] using hb2 x)) b a c he
  change (∫ z, gaussianHeat a (fun y => f y^2) (b*z) ∂gaussianReal 0 1)=_ at HC
  rw [HC] at H
  exact H

theorem gaussianHeat_sq_average_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) :
    Continuous (fun p : ℝ × ℝ => ∫ z, (gaussianHeat p.1 f (p.2*z))^2 ∂gaussianReal 0 1) := by
  have hh := gaussianHeat_continuous hf hb
  apply continuous_iff_continuousAt.mpr
  intro p
  apply continuousAt_of_dominated (bound:=fun _ : ℝ => B^2)
  · exact Eventually.of_forall (fun a => ((hh.comp (show Continuous (fun z : ℝ => (a.1,a.2*z)) by fun_prop)).pow 2).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (gaussianHeat_abs_le hb a.1 (a.2*z))))
  · exact integrable_const _
  · exact ae_of_all _ (fun z => ((hh.comp (show Continuous (fun a : ℝ × ℝ => (a.1,a.2*z)) by fun_prop)).pow 2).continuousAt)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gaussianAngle_hasDerivAt {f df g dg : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (df x) x) (hfc : Continuous df)
    (hdg : ∀ x, HasDerivAt g (dg x) x) (hgc : Continuous dg)
    {B C D E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |df x| ≤ C)
    (hd : ∀ x, |g x| ≤ D) (he : ∀ x, |dg x| ≤ E) (θ : ℝ) :
    HasDerivAt (gaussianAngle f g) (-Real.sin θ*gaussianAngle df dg θ) θ := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hdf x).continuousAt)
  have H := gaussianPair_rotation_derivative hf hdg hgc hB hD hE hb hd he θ
  rw [gaussianPair_rotation_stein hdf hfc hgc hB hC hE hb hc he θ] at H
  exact H

theorem gaussian_variance_angle_identity {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2=
      ∫ θ in 0..Real.pi/2, Real.sin θ*gaussianAngle df df θ := by
  have hf := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have hdc := gaussianAngle_continuous hc hc hC hdf hdf
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=0) (b:=Real.pi/2)
    (fun θ _ => gaussianAngle_hasDerivAt hd hc hd hc hB hC hB hC hb hdf hb hdf θ)
    ((Real.continuous_sin.neg.mul hdc).intervalIntegrable _ _)
  simp_rw [neg_mul] at H
  rw [intervalIntegral.integral_neg, gaussianAngle_zero f hf,
    gaussianAngle_pi_half hf hf hB hb hb] at H
  nlinarith

theorem gaussian_strict_poincare_of_derivative_nonconstant {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (hne : ¬∃ c, ∀ x, df x=c) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2 <
      ∫ x, df x^2 ∂gaussianReal 0 1 := by
  let A : ℝ := ∫ x, df x^2 ∂gaussianReal 0 1
  have hdc := gaussianAngle_continuous hc hc hC hdf hdf
  have hpos : 0<∫ θ in 0..Real.pi/2, Real.sin θ*(A-gaussianAngle df df θ) := by
    apply intervalIntegral.integral_pos (by positivity)
      ((Real.continuous_sin.mul (continuous_const.sub hdc)).continuousOn)
    · intro θ hθ
      exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2,Real.pi_pos]))
        (sub_nonneg.mpr (gaussianAngle_le_square hc hC hdf θ))
    · refine ⟨Real.pi/2,⟨by positivity,le_rfl⟩,?_⟩
      change 0 < Real.sin (Real.pi/2)*(A-gaussianAngle df df (Real.pi/2))
      rw [Real.sin_pi_div_two,one_mul,gaussianAngle_pi_half hc hc hC hdf hdf]
      exact sub_pos.mpr (by simpa only [A,pow_two] using gaussian_variance_pos hc hC hdf hne)
  have H := gaussian_variance_angle_identity hd hc hB hC hb hdf
  have heq : (∫ θ in 0..Real.pi/2, Real.sin θ*(A-gaussianAngle df df θ))=
      A-(∫ θ in 0..Real.pi/2, Real.sin θ*gaussianAngle df df θ) := by
    simp_rw [mul_sub]
    have HS := intervalIntegral.integral_sub (μ:=volume)
      ((Real.continuous_sin.mul (continuous_const (y:=A))).intervalIntegrable 0 (Real.pi/2))
      ((Real.continuous_sin.mul hdc).intervalIntegrable 0 (Real.pi/2))
    simp only [Pi.mul_apply] at HS
    rw [HS,intervalIntegral.integral_mul_const,
      integral_sin,Real.cos_zero,Real.cos_pi_div_two]
    ring
  rw [heq,← H] at hpos
  exact sub_pos.mp hpos

theorem bounded_derivative_constant_imp_constant {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (hc : ∃ c, ∀ x, df x=c) : ∃ c, ∀ x, f x=c := by
  obtain ⟨c,hc⟩ := hc
  have hder (x : ℝ) : HasDerivAt (fun y => f y-c*y) 0 x := by
    convert (hd x).sub ((hasDerivAt_id x).const_mul c) using 1 <;> first | rfl | simp_all
  have heq (x : ℝ) : f x=c*x+f 0 := by
    have H := is_const_of_deriv_eq_zero (fun y => (hder y).differentiableAt)
      (fun y => (hder y).deriv) x 0
    linarith
  have hz : c=0 := by
    by_contra hn
    have H := (abs_le.mp (hb ((2*B+1)/c))).2
    rw [heq] at H
    have hm : c*((2*B+1)/c)=2*B+1 := by field_simp
    rw [hm] at H
    have H0 := (abs_le.mp (hb 0)).1
    linarith
  refine ⟨f 0,fun x => ?_⟩
  simpa only [hz,zero_mul,zero_add] using heq x

theorem gaussian_strict_poincare {f df : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hc : Continuous df)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ x, |f x| ≤ B) (hdf : ∀ x, |df x| ≤ C)
    (hne : ¬∃ c, ∀ x, f x=c) :
    (∫ x, f x^2 ∂gaussianReal 0 1)-(∫ x, f x ∂gaussianReal 0 1)^2 <
      ∫ x, df x^2 ∂gaussianReal 0 1 := by
  apply gaussian_strict_poincare_of_derivative_nonconstant hd hc hB hC hb hdf
  intro h
  exact hne (bounded_derivative_constant_imp_constant hd hB hb h)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarAverageCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarStepAverage_continuous {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |g x| ≤ B) (m v : ℝ) :
    Continuous (scalarStepAverage m v f g) := by
  apply gaussianAverage_continuous (hf.compCLM (scalarStepLinear v)) m
    (hg.comp (scalarStepLinear v).continuous) hB
  intro z
  exact hb _

theorem scalarStepAverage_bound {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {B : ℝ} (hb : ∀ x, |g x| ≤ B) (m v x : ℝ) :
    |scalarStepAverage m v f g x| ≤ B := by
  exact gaussianAverage_norm_le (hf.compCLM (scalarStepLinear v)) m
    (g:=fun z => g (z.1+v*z.2)) (fun z => hb _) x

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarHierarchyAverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem BoundedScalar.const (c : ℝ) : BoundedScalar (fun _ => c) :=
  ⟨continuous_const,|c|,abs_nonneg _,fun _ => le_rfl⟩

theorem BoundedScalar.add {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x+h x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  obtain ⟨C,hC,hc⟩ := hh.bounded
  exact ⟨hg.continuous.add hh.continuous,B+C,add_nonneg hB hC,
    fun x => (abs_add_le _ _).trans (add_le_add (hb x) (hc x))⟩

theorem BoundedScalar.const_mul {g : ℝ → ℝ} (hg : BoundedScalar g) (c : ℝ) :
    BoundedScalar (fun x => c*g x) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨continuous_const.mul hg.continuous,|c| * B,mul_nonneg (abs_nonneg _) hB,fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

theorem BoundedScalar.sub {g h : ℝ → ℝ} (hg : BoundedScalar g) (hh : BoundedScalar h) :
    BoundedScalar (fun x => g x-h x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hg.add (hh.const_mul (-1))

theorem BoundedScalar.sq {g : ℝ → ℝ} (hg : BoundedScalar g) :
    BoundedScalar (fun x => (g x)^2) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  refine ⟨hg.continuous.pow 2,B^2,sq_nonneg _,fun x => ?_⟩
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hb x) _

theorem BoundedScalar.scalarStepAverage {f g : ℝ → ℝ} (hg : BoundedScalar g)
    (hf : BoundedDerivs f) (m v : ℝ) : BoundedScalar (scalarStepAverage m v f g) := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact ⟨scalarStepAverage_continuous hf hg.continuous hB hb m v,B,hB,
    scalarStepAverage_bound hf hb m v⟩

theorem scalarHierarchyAverage_bounded {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) :
    BoundedScalar (scalarHierarchyAverage n m v f g) := by
  induction n generalizing f g with
  | zero => exact hg
  | succ n ih => exact ih (scalarStep_regular hf _ _) (hg.scalarStepAverage hf _ _) _ _

theorem scalarHierarchyAverage_integrable {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    Integrable (fun z => g (x+coordinateLinear n v z))
      (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) := by
  obtain ⟨B,_,hb⟩ := hg.bounded
  apply hierarchyPathLaw_integrable n m _ _ ((hf.translate x).compCLM (coordinateLinear n v))
    (hg.continuous.comp (continuous_const.add (coordinateLinear n v).continuous))
  exact fun z => hb _

theorem scalarHierarchyAverage_integral {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f g x=
      ∫ z, g (x+coordinateLinear n v z) ∂hierarchyPathLaw n m
        (fun z => f (x+coordinateLinear n v z)) 0 := by
  obtain ⟨B,hB,hb⟩ := hg.bounded
  exact scalarHierarchyAverage_eq_integral n m v hf hg.continuous hB hb x

theorem scalarHierarchyAverage_const_mul {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (x c : ℝ) :
    scalarHierarchyAverage n m v f (fun y => c*g y) x=c*scalarHierarchyAverage n m v f g x := by
  rw [scalarHierarchyAverage_integral hf (hg.const_mul c),scalarHierarchyAverage_integral hf hg,
    integral_const_mul]

theorem scalarHierarchyAverage_add {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y+h y) x=
      scalarHierarchyAverage n m v f g x+scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.add hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_add
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

theorem scalarHierarchyAverage_sub {f g h : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (hh : BoundedScalar h) (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => g y-h y) x=
      scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f h x := by
  rw [scalarHierarchyAverage_integral hf (hg.sub hh),scalarHierarchyAverage_integral hf hg,
    scalarHierarchyAverage_integral hf hh,integral_sub
    (scalarHierarchyAverage_integrable hf hg n m v x) (scalarHierarchyAverage_integrable hf hh n m v x)]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_SmoothedObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarWindow_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    HasDerivAt (scalarWindow g h) (scalarWindowDerivative g h x) x := by
  convert (((boundedPrimitive_hasDerivAt hg (x+h)).comp x
    ((hasDerivAt_id x).add_const h)).sub (boundedPrimitive_hasDerivAt hg x)).div_const h using 1 <;>
    first | rfl | exact Subsingleton.elim _ _ | simp only [scalarWindowDerivative,mul_one]

theorem scalarWindowDerivative_continuous {g : ℝ → ℝ} (hg : Continuous g) (h : ℝ) :
    Continuous (scalarWindowDerivative g h) :=
  ((hg.comp (continuous_id.add continuous_const)).sub hg).div_const h

theorem scalarWindow_bound {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindow g h x| ≤ B := by
  have H := (boundedPrimitive_lipschitz hg hB).dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindow,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindowDerivative_bound {g : ℝ → ℝ} {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ 2*(B:ℝ)/h := by
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh]
  exact div_le_div_of_nonneg_right ((abs_sub (g (x+h)) (g x)).trans (by linarith [hB (x+h),hB x])) hh.le

theorem scalarWindow_integral {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    scalarWindow g h x=(∫ y in x..x+h, g y)/h := by
  have H := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ:=volume) 0 x) (hg.intervalIntegrable (μ:=volume) x (x+h))
  dsimp only [scalarWindow,boundedPrimitive]
  congr 1
  linarith

theorem scalarWindow_approx {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {h : ℝ} (hh : 0<h) (x : ℝ) : |scalarWindow g h x-g x| ≤ (L:ℝ)*h := by
  rw [scalarWindow_integral hg.continuous]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=x) (b:=x+h)
    (f:=fun y => g y-g x) (C:=(L:ℝ)*h) (by
      intro y hy
      rw [uIoc_of_le (by linarith)] at hy
      have H := hg.dist_le_mul y x
      simp only [Real.dist_eq] at H
      rw [abs_of_nonneg (show 0≤y-x by linarith [hy.1])] at H
      rw [Real.norm_eq_abs]
      exact H.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) L.coe_nonneg))
  rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,Real.norm_eq_abs,
    abs_of_pos hh] at H
  rw [show (∫ y in x..x+h, g y)/h-g x=((∫ y in x..x+h, g y)-h*g x)/h by field_simp,
    abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarHierarchyAverage_observable_distance {f g a : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (ha : BoundedScalar a)
    {δ : ℝ} (_hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f a x| ≤ δ := by
  rw [← scalarHierarchyAverage_sub hf hg ha,
    scalarHierarchyAverage_integral hf (hg.sub ha)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  have H := norm_integral_le_of_norm_le_const (μ:=hierarchyPathLaw n m
    (fun z => f (x+coordinateLinear n v z)) 0) (f:=fun z => g (x+coordinateLinear n v z)-a (x+coordinateLinear n v z))
    (C:=δ) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hga (x+coordinateLinear n v z)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzObservable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem dyadicScalarAverage_tendsto_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B L : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (hB : ∀ z, |g z| ≤ B) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply CauchySeq.tendsto_limUnder
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let h := ε/(4*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/4 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/4 := by dsimp [h]; field_simp
  let C : ℝ≥0 := ⟨2*(B:ℝ)/h,div_nonneg (by positivity) hh.le⟩
  have hW := dyadicScalarAverage_tendsto_C1 β hα hmono hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (C:=C)
    (scalarWindowDerivative_bound hB hh) s t ht x
  have hc := Metric.cauchySeq_iff.mp hW.cauchySeq (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := hc
  refine ⟨N,fun m hm n hn => ?_⟩
  have he (j : ℕ) : |dyadicScalarAverage β α j s t f g x-
      dyadicScalarAverage β α j s t f (scalarWindow g h) x| ≤ ε/4 := by
    apply (scalarHierarchyAverage_observable_distance hf
      ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
      ⟨continuous_iff_continuousAt.mpr (fun z => (scalarWindow_hasDerivAt hgL.continuous h z).continuousAt),
        B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
      (mul_nonneg L.coe_nonneg hh.le) (fun z => ?_) _ _ _ x).trans hsmall
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have hd := hN m hm n hn
  simp only [Real.dist_eq] at hd ⊢
  have H₁ := abs_sub_le (dyadicScalarAverage β α m s t f g x)
    (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  have H₂ := abs_sub_le (dyadicScalarAverage β α m s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f (scalarWindow g h) x)
    (dyadicScalarAverage β α n s t f g x)
  rw [abs_sub_comm (dyadicScalarAverage β α n s t f (scalarWindow g h) x)] at H₂
  linarith [he m,he n]

theorem scalarCDFAverage_observable_distance (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B C L M : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (haM : LipschitzWith M a)
    (hB : ∀ z, |g z| ≤ B) (hC : ∀ z, |a z| ≤ C)
    {δ : ℝ} (hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β α s t f a x| ≤ δ := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK hgL hB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haM hC s t ht x)).abs
  exact Eventually.of_forall (fun n => scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩ ⟨haM.continuous,C,C.coe_nonneg,hC⟩ hδ hga _ _ _ x)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzChainRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarWindowDerivative_lipschitz_bound {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ L := by
  have H := hg.dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindow_lipschitz {g : ℝ → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {h : ℝ} (hh : 0<h) : LipschitzWith L (scalarWindow g h) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (scalarWindow_hasDerivAt hg.continuous h x).differentiableAt)
  intro x
  rw [(scalarWindow_hasDerivAt hg.continuous h x).deriv]
  exact_mod_cast scalarWindowDerivative_lipschitz_bound hg hh x

theorem scalarCDFAverage_eq_chainAverage_lipschitz {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) {K B L : ℝ≥0} (hfK : LipschitzWith K f)
    (hgL : LipschitzWith L g) (hB : ∀ z, |g z| ≤ B)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFAverage β α s t f g x=scalarTimeChainAverage β l f g x := by
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm ?_ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simp only [zero_add]
  let h := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hh : 0<h := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*h ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*h := mul_le_mul_of_nonneg_right (by linarith) hh.le
      _ = ε/2 := by dsimp [h]; field_simp
  have hd (z) : |g z-scalarWindow g h z| ≤ (L:ℝ)*h := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hh z
  have H₁ := scalarCDFAverage_observable_distance β hα hmono hf hfK hgL
    (scalarWindow_lipschitz hgL hh) hB (scalarWindow_bound hgL.continuous hB hh)
    (mul_nonneg L.coe_nonneg hh.le) hd s t ht x
  have H₂ := scalarHierarchyAverage_observable_distance hf
    ⟨hgL.continuous,B,B.coe_nonneg,hB⟩
    ⟨(scalarWindow_lipschitz hgL hh).continuous,B,B.coe_nonneg,scalarWindow_bound hgL.continuous hB hh⟩
    (mul_nonneg L.coe_nonneg hh.le) hd l.length (fun i => (l.get i).1)
    (fun i => β*Real.sqrt ((l.get i).2:ℝ)) x
  change |scalarTimeChainAverage β l f g x-scalarTimeChainAverage β l f (scalarWindow g h) x|≤_ at H₂
  have HE := scalarCDFAverage_eq_chainAverage hf
    (scalarWindow_hasDerivAt hgL.continuous h) (scalarWindowDerivative_continuous hgL.continuous h)
    hfK (scalarWindow_bound hgL.continuous hB hh) (scalarWindowDerivative_lipschitz_bound hgL hh)
    β hα hmono l hm s t ht hdur hmodel x
  rw [HE] at H₁
  have H := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarTimeChainAverage β l f (scalarWindow g h) x) (scalarTimeChainAverage β l f g x)
  rw [abs_sub_comm (scalarTimeChainAverage β l f (scalarWindow g h) x)] at H
  linarith

theorem scalarCDFAverage_eq_partition_lipschitz {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    {K B L : ℝ≥0} (hK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ y, |g y|≤B)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (t : ℝ≥0) (ht : t≤1) (hd : (t:ℝ)=q (Fin.last n)-q 0) (x : ℝ) :
    scalarCDFAverage β α (q 0) t f g x=scalarHierarchyAverage n m (timeGridCoefficients n β q) f g x := by
  have hdur : chainDuration (partitionTimeChain n q hq m)=t := by
    apply NNReal.coe_injective
    exact (partitionTimeChain_duration n q hq m).trans hd.symm
  have hml (p) (hp : p∈partitionTimeChain n q hq m) : p.1∈Icc (0:ℝ) 1 := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact hm i
  have H := scalarCDFAverage_eq_chainAverage_lipschitz hf hK hgL hB β hα hαm
    (partitionTimeChain n q hq m) hml (q 0) t ht hdur (partitionTimeChain_models n q hq m hmodel) x
  simp only [partitionTimeChain,scalarTimeChainAverage_ofFn,NNReal.coe_mk] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzCDFStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_cdf_stability_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z∈Icc (0:ℝ) 1) (hγm : Monotone γ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x h : ℝ) (hh : 0<h) :
    |scalarCDFAverage β α s t f g x-scalarCDFAverage β γ s t f g x| ≤
      2*(scalarTimeMassConstantK β (K+B+B)*(∫ z in s..s+t, |α z-γ z|))/h+
        2*((L:ℝ)+2*(B:ℝ)^2)*h := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := ε/(2*((L:ℝ)+1))
  have hL : 0<(L:ℝ)+1 := by positivity
  have hd : 0<d := div_pos hε (mul_pos (by norm_num) hL)
  have hsmall : (L:ℝ)*d ≤ ε/2 := by
    calc
      _ ≤ ((L:ℝ)+1)*d := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = ε/2 := by dsimp [d]; field_simp
  have hga (z) : |g z-scalarWindow g d z| ≤ (L:ℝ)*d := by
    rw [abs_sub_comm]
    exact scalarWindow_approx hgL hd z
  have Hα := scalarCDFAverage_observable_distance β hα hαm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hγ := scalarCDFAverage_observable_distance β hγ hγm hf hfK hgL
    (scalarWindow_lipschitz hgL hd) hB (scalarWindow_bound hgL.continuous hB hd)
    (mul_nonneg L.coe_nonneg hd.le) hga s t ht x
  have Hc := scalarCDFAverage_cdf_stability_C1 β hα hαm hγ hγm hf
    (scalarWindow_hasDerivAt hgL.continuous d) (scalarWindowDerivative_continuous hgL.continuous d)
    hfK (scalarWindow_bound hgL.continuous hB hd) (scalarWindowDerivative_lipschitz_bound hgL hd)
    s t ht x h hh
  have H₁ := abs_sub_le (scalarCDFAverage β α s t f g x)
    (scalarCDFAverage β α s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  have H₂ := abs_sub_le (scalarCDFAverage β α s t f (scalarWindow g d) x)
    (scalarCDFAverage β γ s t f (scalarWindow g d) x) (scalarCDFAverage β γ s t f g x)
  rw [abs_sub_comm (scalarCDFAverage β γ s t f (scalarWindow g d) x)] at H₂
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_LipschitzTerminalStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFAverage_terminal_stability_lipschitz (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {f g a b : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    {K L B A C : ℝ≥0} (hfK : LipschitzWith K f) (hgL : LipschitzWith L g)
    (haA : LipschitzWith A a) (hbC : LipschitzWith C b)
    (haB : ∀ z, |a z| ≤ B) (hbB : ∀ z, |b z| ≤ B)
    {ε δ : ℝ} (hε : 0≤ε) (hfg : ∀ z, |f z-g z| ≤ ε)
    (hab : ∀ z, |a z-b z| ≤ δ) (s : ℝ) (t : ℝ≥0) (ht : t≤1) (x : ℝ) :
    |scalarCDFAverage β α s t f a x-scalarCDFAverage β α s t g b x| ≤
      δ+2*(B:ℝ)*(Real.exp (2*ε)-1) := by
  apply le_of_tendsto ((dyadicScalarAverage_tendsto_lipschitz β hα hmono hf hfK haA haB s t ht x).sub
    (dyadicScalarAverage_tendsto_lipschitz β hα hmono hg hgL hbC hbB s t ht x)).abs
  apply Eventually.of_forall
  intro n
  apply scalarHierarchyAverage_terminal_stability _ _ _
    (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
    (fun i j hij => ?_) hf hg hε hfg haA.continuous hbC.continuous B.coe_nonneg haB hbB hab x
  rcases lt_or_eq_of_le hij with hij|rfl
  · exact List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t) i j hij
  · exact le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileScalarOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarMomentSquare_cast {n l : ℕ} (hn : n=l) (m v : Fin l → ℝ)
    (f g : ℝ → ℝ) (j : Fin (l+1)) (x : ℝ) :
    scalarMomentSquare n (fun i => m (Fin.cast hn i)) (fun i => v (Fin.cast hn i)) f g
      (Fin.cast (congrArg (·+1) hn.symm) j) x=scalarMomentSquare l m v f g j x := by
  subst l
  rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_split (a b : ℕ) (m v : Fin (a+b) → ℝ) (f g : ℝ → ℝ) :
    scalarHierarchyAverage (a+b) m v f g=
      scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (scalarHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  induction b generalizing f g with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (scalarStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PartitionOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem gridPrefix_monotone {a b : ℕ} {q : Fin (a+b+1) → ℝ}
    (h : Monotone q) : Monotone (gridPrefix a b q) := by
  intro i j hij
  exact h (show (⟨i.1,by omega⟩:Fin (a+b+1)) ≤ ⟨j.1,by omega⟩ from hij)
theorem gridSuffix_monotone {a b : ℕ} {q : Fin (a+b+1) → ℝ}
    (h : Monotone q) : Monotone (gridSuffix a b q) := by
  intro i j hij
  apply h
  exact Nat.add_le_add_left hij a

theorem scalarCDFOverlap_eq_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+b+1) → ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last (a+b))=1)
    (m : Fin (a+b) → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin (a+b), ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i) :
    scalarCDFOverlap β α (q ⟨a,by omega⟩)=
      scalarMomentSquare (a+b) m (timeGridCoefficients (a+b) β q)
        scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  let r := q ⟨a,by omega⟩
  have hr : r∈Icc (0:ℝ) 1 := by
    constructor
    · rw [← hq0]; exact hq (Fin.zero_le _)
    · rw [← hq1]; exact hq (Fin.le_last _)
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  let v := timeGridCoefficients (a+b) β q
  let f := scalarCDFValue β α r s
  let u := scalarCDFGradient β α r s
  have hsuffix : f=scalarHierarchy b (fun i => m (i.natAdd a))
      (fun i => v (i.natAdd a)) scalarSpinTerminal := by
    funext x
    have H := scalarCDFOperator_eq_partition scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hα hαm b (gridSuffix a b q) (gridSuffix_monotone hq)
      (fun i => m (i.natAdd a)) (fun i => hm (i.natAdd a))
      (fun i z hz => hmodel (i.natAdd a) z hz) s hs1
      (by change (s:ℝ)=q (Fin.last (a+b))-r; rw [hq1,hs]) x
    exact H
  have hu : u=scalarHierarchyAverage b (fun i => m (i.natAdd a))
      (fun i => v (i.natAdd a)) scalarSpinTerminal scalarMagnetization := by
    funext x
    have H := (scalarCDFValue_hasDerivAt β hα hαm r s hs1 x).deriv
    change deriv f x=u x at H
    rw [hsuffix,scalarHierarchy_gradient_average _ _ _ scalarSpinTerminal_regular
      scalarSpinTerminal_hasDerivAt] at H
    exact H.symm
  have HG := scalarCDFGradient_sq_regular β hα hαm r s hs1
  have hp0 : gridPrefix a b q 0=0 := by simpa [gridPrefix] using hq0
  have H := scalarCDFAverage_eq_partition (scalarCDFValue_regular β hα hαm r s hs1)
    HG.1 HG.2.1 (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (B:=1) (C:=2) HG.2.2.1 HG.2.2.2 β hα hαm a (gridPrefix a b q)
    (gridPrefix_monotone hq) (fun i => m (i.castAdd b)) (fun i => hm (i.castAdd b))
    (fun i z hz => hmodel (i.castAdd b) z hz) t ht1
    (by change (t:ℝ)=r-gridPrefix a b q 0; rw [hp0,sub_zero,ht]) 0
  rw [hp0] at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_ at H
  change scalarCDFAverage β α 0 t f (fun z => (u z)^2) 0=_
  rw [H,scalarMomentSquare_split]
  change scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
    f (fun x => (u x)^2) 0=_
  rw [hsuffix,hu]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_PartitionOverlapIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_eq_partition_index (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q)
    (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (m : Fin n → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmodel : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (j : Fin (n+1)) :
    scalarCDFOverlap β α (q j)=
      scalarMomentSquare n m (timeGridCoefficients n β q) scalarSpinTerminal scalarMagnetization j 0 := by
  let a := j.1
  let b := n-a
  have hn : a+b=n := Nat.add_sub_of_le (Nat.le_of_lt_succ j.isLt)
  let q' : Fin (a+b+1) → ℝ := fun i => q (Fin.cast (congrArg (·+1) hn) i)
  let m' : Fin (a+b) → ℝ := fun i => m (Fin.cast hn i)
  have hq' : Monotone q' := fun i l hil => hq hil
  have h0 : q' 0=0 := by simpa [q'] using hq0
  have h1 : q' (Fin.last (a+b))=1 := by simpa [q'] using hq1
  have hm' (i : Fin (a+b)) : m' i∈Icc (0:ℝ) 1 := hm _
  have hmodel' (i : Fin (a+b)) (z : ℝ) (hz : z∈Ico (q' i.castSucc) (q' i.succ)) : α z=m' i :=
    hmodel (Fin.cast hn i) z hz
  have H := scalarCDFOverlap_eq_partition β hα hαm a b q' hq' h0 h1 m' hm' hmodel'
  have heq : q' ⟨a,by omega⟩=q j := by congr 1
  rw [heq] at H
  have hv : timeGridCoefficients (a+b) β q'=
      fun i => timeGridCoefficients n β q (Fin.cast hn i) := rfl
  rw [hv] at H
  have hj : (⟨a,by omega⟩:Fin (a+b+1))=Fin.cast (congrArg (·+1) hn.symm) j := by ext; rfl
  rw [hj] at H
  exact H.trans (scalarMomentSquare_cast hn m (timeGridCoefficients n β q)
    scalarSpinTerminal scalarMagnetization j 0)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AppendTimeGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem appendTimeGrid_right (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (j : Fin (b+1)) : appendTimeGrid a b q p (j.natAdd a)=p j := by
  exact Fin.append_right _ _ _

theorem appendTimeGrid_left (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hr : q (Fin.last a)=p 0) (i : Fin (a+1)) : appendTimeGrid a b q p ⟨i,by omega⟩=q i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [show (⟨(Fin.last a).val,by omega⟩:Fin (a+b+1))=(0:Fin (b+1)).natAdd a by ext; simp,
      appendTimeGrid_right,hr]
  · change appendTimeGrid a b q p (j.castAdd (b+1))=q j.castSucc
    exact Fin.append_left _ _ _

theorem appendTimeGrid_left_start (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hr : q (Fin.last a)=p 0) (i : Fin a) :
    appendTimeGrid a b q p (i.castAdd b).castSucc=q i.castSucc :=
  appendTimeGrid_left a b q p hr i.castSucc

theorem appendTimeGrid_left_end (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hr : q (Fin.last a)=p 0) (i : Fin a) :
    appendTimeGrid a b q p (i.castAdd b).succ=q i.succ :=
  appendTimeGrid_left a b q p hr i.succ

theorem appendTimeGrid_right_start (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (j : Fin b) : appendTimeGrid a b q p (j.natAdd a).castSucc=p j.castSucc :=
  appendTimeGrid_right a b q p j.castSucc

theorem appendTimeGrid_right_end (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (j : Fin b) : appendTimeGrid a b q p (j.natAdd a).succ=p j.succ := by
  rw [show (j.natAdd a).succ=j.succ.natAdd a by ext; simp; omega]
  exact appendTimeGrid_right a b q p j.succ

theorem appendTimeGrid_monotone (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hr : q (Fin.last a)=p 0) :
    Monotone (appendTimeGrid a b q p) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i
    rw [appendTimeGrid_left_start a b q p hr,appendTimeGrid_left_end a b q p hr]
    exact hq (Fin.castSucc_le_succ i)
  · intro j
    rw [appendTimeGrid_right_start,appendTimeGrid_right_end]
    exact hp (Fin.castSucc_le_succ j)

theorem timeGridCoefficients_append (a b : ℕ) (β : ℝ)
    (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ) (hr : q (Fin.last a)=p 0) :
    timeGridCoefficients (a+b) β (appendTimeGrid a b q p)=
      Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp only [timeGridCoefficients,Fin.append_left,
      appendTimeGrid_left_start a b q p hr,appendTimeGrid_left_end a b q p hr]
  · intro j
    simp only [timeGridCoefficients,Fin.append_right,appendTimeGrid_right_start,appendTimeGrid_right_end]

theorem appendTimeGrid_models {α : ℝ → ℝ} (a b : ℕ)
    (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ) (hr : q (Fin.last a)=p 0)
    (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hl : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i) :
    ∀ i : Fin (a+b), ∀ z∈Ico (appendTimeGrid a b q p i.castSucc)
      (appendTimeGrid a b q p i.succ), α z=Fin.append m l i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i z hz
    rw [appendTimeGrid_left_start a b q p hr,appendTimeGrid_left_end a b q p hr] at hz
    simpa only [Fin.append_left] using hm i z hz
  · intro j z hz
    rw [appendTimeGrid_right_start,appendTimeGrid_right_end] at hz
    simpa only [Fin.append_right] using hl j z hz

theorem scalarCDFOverlap_eq_two_partitions_index (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hq0 : q 0=0) (hp1 : p (Fin.last b)=1)
    (hr : q (Fin.last a)=p 0) (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hl : ∀ i, l i∈Icc (0:ℝ) 1)
    (hmodelq : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hmodelp : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i)
    (j : Fin (b+1)) :
    scalarCDFOverlap β α (p j)=
      scalarMomentSquare (a+b) (Fin.append m l)
        (Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p))
        scalarSpinTerminal scalarMagnetization (j.natAdd a) 0 := by
  have h0 : appendTimeGrid a b q p 0=0 := by
    have H := appendTimeGrid_left a b q p hr 0
    simpa only [Fin.val_zero,Fin.mk_zero,hq0] using H
  have h1 : appendTimeGrid a b q p (Fin.last (a+b))=1 := by
    have H := appendTimeGrid_right a b q p (Fin.last b)
    rw [show (Fin.last b).natAdd a=Fin.last (a+b) by ext; simp] at H
    exact H.trans hp1
  have hml (i : Fin (a+b)) : Fin.append m l i∈Icc (0:ℝ) 1 := by
    refine Fin.addCases ?_ ?_ i
    · intro i; simpa only [Fin.append_left] using hm i
    · intro j; simpa only [Fin.append_right] using hl j
  have H := scalarCDFOverlap_eq_partition_index β hα hαm (a+b) (appendTimeGrid a b q p)
    (appendTimeGrid_monotone a b q p hq hp hr) h0 h1 (Fin.append m l) hml
    (appendTimeGrid_models a b q p hr m l hmodelq hmodelp) (j.natAdd a)
  rwa [appendTimeGrid_right,timeGridCoefficients_append a b β q p hr] at H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_RootSusceptibilitySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tailZero_parameterAxis (n : ℕ) (j : Fin (n+1)) :
    TailZero n j (parameterAxis n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [TailZero,Fin.lastCases_last]
    · simp only [TailZero,Fin.lastCases_castSucc,parameterAxis]
      exact ⟨trivial,ih j⟩

theorem hierarchyLevel_rootGradient (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (j : Fin (n+1)) :
    rootGradient n (hierarchyLevel n m f j)=
      hierarchyMomentLevel n m f (rootGradient n f) j := by
  funext z
  exact hierarchyLevel_gradient n m f hf j (parameterAxis n) z (tailZero_parameterAxis n j)

theorem hierarchyPressure_rootHessian_overlap_sum (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (h : RootSpinCurvature n f)
    (he : ∀ z, rootHessian n f z=1-(rootGradient n f z)^2) (x : ℝ) :
    rootHessian 0 (hierarchyPressure n m f) x=
      1-∑ j, hierarchyAtom n m 1 j*(∫ z,
        (hierarchyMomentLevel n m f (rootGradient n f) j z)^2 ∂hierarchyPathLaw n m f x) := by
  have hg := rootGradient_continuous n hf
  have hb (z) : ‖rootGradient n f z‖≤1 := (h.bounds z).1
  have hM := hierarchyMomentLevel_bounded_continuous n m f (rootGradient n f) hf hg zero_le_one hb
  have hint (j : Fin (n+1)) : Integrable (fun z => hierarchyAtom n m 1 j*
      (hierarchyMomentLevel n m f (rootGradient n f) j z*rootGradient n f z))
      (hierarchyPathLaw n m f x) := by
    apply Integrable.const_mul
    apply hierarchyPathLaw_integrable n m f _ hf ((hM j).1.mul hg) (C:=1)
    intro z
    simpa only [Pi.mul_apply,norm_mul,one_mul] using mul_le_mul ((hM j).2 z) (hb z) (norm_nonneg _) zero_le_one
  have Hpair : rootPair n m f=fun z => ∑ j, hierarchyAtom n m 1 j*
      (hierarchyMomentLevel n m f (rootGradient n f) j z*rootGradient n f z) := by
    funext z
    have Hp := fderiv_hierarchyPenalty_apply n m 1 f hf z (parameterAxis n)
    change rootGradient n (hierarchyPenalty n m 1 f) z=
      ∑ j, hierarchyAtom n m 1 j*rootGradient n (hierarchyLevel n m f j) z at Hp
    rw [rootPair,Hp]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hierarchyLevel_rootGradient n m hf]
    ring
  rw [hierarchyPressure_rootHessian_spin_formula n m hm hmono hf h he x,Hpair,
    integral_finsetSum _ (fun j _ => hint j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,hierarchyPathLaw_prefix_mul n m f (rootGradient n f)
    (rootGradient n f) hf hg hg zero_le_one zero_le_one hb hb j x]
  simp only [pow_two]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSusceptibilitySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarSpinParameter_eq (n : ℕ) (v : Fin n → ℝ) :
    scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0=
      affineLogPartition (fun _ : Bool => 0) (fun b => spin b • scalarSpinField n v) := by
  rw [← scalarSpinTerminal_affine]
  funext z
  simp only [scalarParameterTerminal,zero_add,coordinateLinear_apply]

theorem scalarSpinRoot_gradient (n : ℕ) (v : Fin n → ℝ) :
    rootGradient n (affineLogPartition (fun _ : Bool => 0)
      (fun b => spin b • scalarSpinField n v))=
      scalarParameterTerminal n v (fun a y => scalarMagnetization (a+y)) 0 := by
  rw [← scalarSpinParameter_eq]
  funext z
  have HE : scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0=
      fun z => scalarSpinTerminal (scalarSpinField n v z) := by
    funext z
    simp only [scalarParameterTerminal,zero_add,scalarSpinField,add_apply]
  have HD := (scalarSpinTerminal_hasDerivAt (scalarSpinField n v z)).comp_hasFDerivAt z
    (scalarSpinField n v).hasFDerivAt
  have HD' : fderiv ℝ (fun z => scalarSpinTerminal (scalarSpinField n v z)) z=
      scalarMagnetization (scalarSpinField n v z) • scalarSpinField n v := by
    convert HD.fderiv using 1; rfl
  rw [rootGradient,HE,HD']
  simp only [smul_apply,smul_eq_mul,scalarSpinField,add_apply,parameter_axis,
    coordinateLinear_axis,add_zero,mul_one,scalarParameterTerminal,zero_add]

theorem scalarStepAverage_translate (m v c : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    scalarStepAverage m v (fun t => f (c+t)) (fun t => g (c+t)) x=
      scalarStepAverage m v f g (c+x) := by
  simp only [scalarStepAverage,gaussianAverage,gaussianStepLaw,add_assoc]

theorem scalarHierarchyAverage_translate (n : ℕ) (m v : Fin n → ℝ)
    (f g : ℝ → ℝ) (c x : ℝ) :
    scalarHierarchyAverage n m v (fun y => f (c+y)) (fun y => g (c+y)) x=
      scalarHierarchyAverage n m v f g (c+x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [scalarHierarchyAverage]
    rw [funext (scalarStep_translate _ _ c f),funext (scalarStepAverage_translate _ _ c f g)]
    exact ih _ _ _ _

theorem scalarMomentSquare_translate (n : ℕ) (m v : Fin n → ℝ)
    (f g : ℝ → ℝ) (j : Fin (n+1)) (c x : ℝ) :
    scalarMomentSquare n m v (fun y => f (c+y)) (fun y => g (c+y)) j x=
      scalarMomentSquare n m v f g j (c+x) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last]
      exact scalarHierarchyAverage_translate (n+1) m v f (fun x => (g x)^2) c x
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc]
      rw [funext (scalarStep_translate _ _ c f),funext (scalarStepAverage_translate _ _ c f g)]
      exact ih _ _ _ _ j

theorem scalarHierarchy_spin_hessian_overlap_sum (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (x : ℝ) :
    rootHessian 0 (scalarHierarchy n m v scalarSpinTerminal) x=
      1-∑ j, hierarchyAtom n m 1 j*
        scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
  rw [scalarHierarchy_spin_eq,hierarchyPressure_rootHessian_overlap_sum n m hm hmono
    (affineLogPartition_boundedDerivs _ _) (scalarSpinRoot_curvature n v)
    (scalarSpinRoot_curvature_eq n v)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hf₀ := affineLogPartition_boundedDerivs (fun _ : Bool => (0:ℝ))
    (fun b => spin b • scalarSpinField n v)
  have hM := hierarchyMomentLevel_bounded_continuous n m _ _ hf₀
    (rootGradient_continuous n hf₀) zero_le_one (fun z => (scalarSpinRoot_curvature n v |>.bounds z).1) j
  rw [← hierarchyAverage_eq_integral n m _ hf₀ (fun z =>
    (hierarchyMomentLevel n m _ _ j z)^2) (hM.1.pow 2) zero_le_one (fun z => by
    rw [norm_pow]
    simpa using (pow_le_pow_left₀ (norm_nonneg _) (hM.2 z) 2)) x]
  rw [scalarSpinRoot_gradient n v,← scalarSpinParameter_eq n v]
  have hf : BoundedDerivs (scalarParameterTerminal n v (fun a y => scalarSpinTerminal (a+y)) 0) := by
    rw [scalarSpinParameter_eq]
    exact affineLogPartition_boundedDerivs _ _
  have H := scalarMomentSquare_eq_parameterAverage n m v
    (fun a y => scalarSpinTerminal (a+y)) (fun a y => scalarMagnetization (a+y)) 0 x hf j
  have HE : scalarMomentSquare n m v (fun y => scalarSpinTerminal (x+y))
      (fun y => scalarMagnetization (x+y)) j 0=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization j x := by
    simpa only [add_zero] using scalarMomentSquare_translate n m v scalarSpinTerminal scalarMagnetization j x 0
  exact (H.symm.trans HE)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyAtomCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem hierarchyAtom_zero_coordinate (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ) :
    hierarchyAtom (n+1) m u 0=m 0 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    change Fin.lastCases (u-m (Fin.last (n+1)))
      (hierarchyAtom (n+1) (fun i => m i.castSucc) (m (Fin.last (n+1))))
      (0:Fin (n+1+1)).castSucc=m 0
    rw [Fin.lastCases_castSucc]
    exact ih _ _

theorem hierarchyAtom_succ_coordinate (n : ℕ) (m : Fin (n+1) → ℝ) (u : ℝ)
    (j : Fin (n+1)) : hierarchyAtom (n+1) m u j.succ=Fin.snoc (α:=fun _ => ℝ) m u j.succ-m j := by
  induction n generalizing u with
  | zero =>
    have hj : j.succ=Fin.last 1 := by ext; simp [Fin.eq_zero j]
    rw [hj]
    simp only [hierarchyAtom,Fin.lastCases_last,Fin.snoc_last,Fin.eq_zero j,Fin.last_zero]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.succ_last,hierarchyAtom,Fin.lastCases_last,Fin.snoc_last]
    · rw [← Fin.castSucc_succ]
      rw [hierarchyAtom,Fin.lastCases_castSucc,Fin.snoc_castSucc]
      rw [ih]
      congr 1
      refine Fin.lastCases ?_ (fun l => ?_) i
      · simp
      · simp only [← Fin.castSucc_succ,Fin.snoc_castSucc]

theorem hierarchyAtom_quantile_succ (k : ℕ) (j : Fin (k+1)) :
    hierarchyAtom (k+1) (quantileMass k) 1 j.succ=1/(k+1:ℕ) := by
  rw [hierarchyAtom_succ_coordinate]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [Fin.succ_last,Fin.snoc_last,quantileMass,Fin.val_last]
    field_simp
    push_cast
    ring
  · simp only [← Fin.castSucc_succ,Fin.snoc_castSucc,quantileMass,Fin.val_succ,Fin.val_castSucc]
    push_cast
    ring

theorem monotone_quantileMass (k : ℕ) : Monotone (quantileMass k) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarStep_even {f : ℝ → ℝ} (hf : Function.Even f) (m v : ℝ) :
    Function.Even (scalarStep m v f) := by
  intro z
  have he (y : ℝ) : f (-z+v*y) = f (z+v*(-y)) := by
    rw [← hf (-z+v*y)]
    congr 1
    ring
  have hi (g : ℝ → ℝ) : (∫ y, g (-y) ∂gaussianReal 0 1) = ∫ y, g y ∂gaussianReal 0 1 := by
    simpa only [scalarSign_true] using
      (scalarSign_gaussian true).integral_comp (scalarSignEquiv true).measurableEmbedding g
  simp only [scalarStep,gaussianStep,positiveGaussianLogStep,he]
  rw [hi (fun y => f (z+v*y)),hi (fun y => Real.exp (m*f (z+v*y)))]

theorem scalarHierarchy_even (n : ℕ) (m v : Fin n → ℝ) {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (scalarHierarchy n m v f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih => exact ih _ _ (scalarStep_even hf _ _)

theorem scalarHierarchy_spin_even (n : ℕ) (m v : Fin n → ℝ) :
    Function.Even (scalarHierarchy n m v scalarSpinTerminal) :=
  scalarHierarchy_even n m v (fun z => by simp only [scalarSpinTerminal,Real.cosh_neg])

theorem scalarHierarchy_spin_gradient_zero (n : ℕ) (m v : Fin n → ℝ) :
    fderiv ℝ (scalarHierarchy n m v scalarSpinTerminal) 0 1 = 0 := by
  let f := scalarHierarchy n m v scalarSpinTerminal
  have hf : BoundedDerivs f := scalarHierarchy_spin_regular n m v
  have hD := ((hf.1.differentiable (by norm_num)) 0).hasDerivAt
  have hD' : HasDerivAt f (deriv f 0) (-(0:ℝ)) := by simpa only [neg_zero] using hD
  have H := hD'.comp (0:ℝ) (hasDerivAt_neg (0:ℝ))
  have he : (fun x => f (-x)) = f := funext (scalarHierarchy_spin_even n m v)
  change HasDerivAt (fun x => f (-x)) (deriv f 0 * (-1)) 0 at H
  rw [he] at H
  have hh := H.unique hD
  change deriv f 0 = 0
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFGradient_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) : scalarCDFGradient β α s t 0=0 := by
  have H := (dyadicScalar_gradient_uniform β hα hmono s t ht).tendsto_at 0
  have he (n : ℕ) : rootGradient 0 (dyadicScalar β α n s t scalarSpinTerminal) 0=0 := by
    simp only [dyadicScalar,scalarTimeChain_eq_hierarchy]
    exact scalarHierarchy_spin_gradient_zero _ _ _
  simp only [he] at H
  exact tendsto_nhds_unique H tendsto_const_nhds

theorem scalarCDFOverlap_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α) : scalarCDFOverlap β α 0=0 := by
  have HR := scalarCDFGradient_sq_regular β hα hmono 0 1 le_rfl
  have HE := scalarCDFAverage_eq_chainAverage
    (scalarCDFValue_regular β hα hmono 0 1 le_rfl) HR.1 HR.2.1
    (scalarCDFValue_lipschitz β hα hmono 0 1 le_rfl) (B:=1) HR.2.2.1 (C:=2) HR.2.2.2 β hα hmono
    [] (by simp) 0 0 (by norm_num) rfl trivial 0
  simpa only [scalarCDFOverlap,sub_zero,Real.toNNReal_one,Real.toNNReal_zero,
    scalarTimeChainAverage,List.length_nil,scalarHierarchyAverage,scalarCDFGradient_zero β hα hmono 0 1 le_rfl,zero_pow (by decide : 2≠0)] using HE

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_OverlapModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfGradientTest_continuous {β : ℝ} {α : ℝ → ℝ}
    (hΓ : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) :
    Continuous (cdfGradientTest β α) :=
  continuous_id.sub ((continuousOn_iff_continuous_domRestrict.mp hΓ).comp continuous_projIcc)

theorem cdfGradientTest_eq {β : ℝ} {α : ℝ → ℝ} {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    cdfGradientTest β α s=s-scalarCDFOverlap β α s := by
  simp only [cdfGradientTest,projIcc_of_mem _ hs]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_SignedCDFTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem unitCDF_mul_indicator (q : ℝ) (f : ℝ → ℝ) :
    (fun x => unitCDF q x*f x)=(Ici q).indicator f := by
  funext x
  simp only [unitCDF,Set.indicator_apply,mem_Ici]
  split_ifs <;> simp

theorem unitCDF_mul_integral (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (f : ℝ → ℝ) :
    (∫ x in Icc (0:ℝ) 1, unitCDF q x*f x)=∫ x in q..1, f x := by
  rw [unitCDF_mul_indicator,setIntegral_indicator measurableSet_Ici]
  have he : Icc (0:ℝ) 1∩Ici q=Icc q 1 := by
    ext x
    simp only [mem_inter_iff,mem_Icc,mem_Ici]
    constructor
    · intro H; exact ⟨H.2,H.1.2⟩
    · intro H; exact ⟨⟨hq.1.trans H.1,H.2⟩,H.1⟩
  rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hq.2]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFParisiContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfPenalty_integrable {α : ℝ → ℝ} (hαm : Monotone α) :
    IntegrableOn (fun s => s*α s) (Icc (0:ℝ) 1) :=
  IntegrableOn.continuousOn_mul continuousOn_id (MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)) isCompact_Icc

theorem cdfPenalty_lipschitz {α γ : ℝ → ℝ} (hαm : Monotone α) (hγm : Monotone γ) :
    |(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| ≤
      ∫ s in Icc (0:ℝ) 1, |α s-γ s| := by
  rw [← integral_sub (cdfPenalty_integrable hαm) (cdfPenalty_integrable hγm)]
  calc
    _ ≤ ∫ s in Icc (0:ℝ) 1, |s*α s-s*γ s| := abs_integral_le_integral_abs
    _ ≤ _ := setIntegral_mono_on ((cdfPenalty_integrable hαm).sub (cdfPenalty_integrable hγm)).abs
      ((MonotoneOn.integrableOn_isCompact isCompact_Icc (hαm.monotoneOn _)).sub (MonotoneOn.integrableOn_isCompact isCompact_Icc (hγm.monotoneOn _))).abs measurableSet_Icc (by
        intro s hs
        rw [← mul_sub,abs_mul,abs_of_nonneg hs.1]
        exact mul_le_of_le_one_left (abs_nonneg _) hs.2)

theorem scalarCDFParisi_cdf_lipschitz (β : ℝ) {α γ : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hγ : ∀ z, γ z ∈ Icc (0:ℝ) 1) (hγm : Monotone γ) :
    |scalarCDFParisi β α-scalarCDFParisi β γ| ≤
      (scalarTimeMassConstant β+β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) := by
  have H := scalarCDFValue_cdf_lipschitz β hα hαm hγ hγm 0 1 le_rfl 0
  simp only [NNReal.coe_one,zero_add,intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] at H
  unfold scalarCDFParisi
  calc
    _ = |(scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0)-
        (β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by congr 1; ring
    _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
        (β^2/2)*|(∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s)| := by
      calc
        _ ≤ |scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0|+
            |(β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))| := by
          simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le
            (scalarCDFValue β α 0 1 0-scalarCDFValue β γ 0 1 0) 0
            ((β^2/2)*((∫ s in Icc (0:ℝ) 1, s*α s)-(∫ s in Icc (0:ℝ) 1, s*γ s))))
        _ = _ := by rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ β^2/2)]
    _ ≤ scalarTimeMassConstant β*(∫ s in Icc (0:ℝ) 1, |α s-γ s|)+
        (β^2/2)*(∫ s in Icc (0:ℝ) 1, |α s-γ s|) :=
      add_le_add H (mul_le_mul_of_nonneg_left (cdfPenalty_lipschitz hαm hγm) (by positivity))
    _ = _ := by ring

theorem scalarCDFParisi_tendsto_of_L1 (β : ℝ) {α : ℝ → ℝ} {αs : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hαm : Monotone α)
    (hs : ∀ n z, αs n z ∈ Icc (0:ℝ) 1) (hsm : ∀ n, Monotone (αs n))
    (ht : Tendsto (fun n => ∫ z in Icc (0:ℝ) 1, |αs n z-α z|) atTop (𝓝 0)) :
    Tendsto (fun n => scalarCDFParisi β (αs n)) atTop (𝓝 (scalarCDFParisi β α)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => scalarCDFParisi_cdf_lipschitz β (hs n) (hsm n) hα hαm)
    (by simpa only [mul_zero] using ht.const_mul (scalarTimeMassConstant β+β^2/2))
  simpa only [mul_zero,Real.norm_eq_abs] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFWeakLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem cdf_tendsto_of_weak {μ : ProbabilityMeasure ℝ} {μs : ℕ → ProbabilityMeasure ℝ}
    (ht : Tendsto μs atTop (𝓝 μ)) {x : ℝ} (hx : (μ : Measure ℝ) {x} = 0) :
    Tendsto (fun n => cdf (μs n : Measure ℝ) x) atTop (𝓝 (cdf (μ : Measure ℝ) x)) := by
  have H := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' ht
    (show (μ : Measure ℝ) (frontier (Set.Iic x)) = 0 by simpa only [frontier_Iic] using hx)
  simpa only [cdf_eq_real,Measure.real,Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure ℝ) (Set.Iic x))).comp H

theorem cdf_L1_tendsto_of_weak {μ : ProbabilityMeasure ℝ} {μs : ℕ → ProbabilityMeasure ℝ}
    (ht : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => ∫ x in Set.Icc (0:ℝ) 1,
      |cdf (μs n : Measure ℝ) x-cdf (μ : Measure ℝ) x|) atTop (𝓝 0) := by
  have hc : Set.Countable {x : ℝ | 0 < (μ : Measure ℝ) {x}} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun x => measurableSet_singleton x)
      (fun _ _ hij => Set.disjoint_singleton.mpr hij)
  have hae : ∀ᵐ x ∂volume, Tendsto (fun n => cdf (μs n : Measure ℝ) x) atTop
      (𝓝 (cdf (μ : Measure ℝ) x)) := by
    filter_upwards [hc.ae_notMem volume] with x hx
    apply cdf_tendsto_of_weak ht
    exact le_antisymm (not_lt.mp hx) bot_le
  have H := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0:ℝ) 1))
    (F := fun n x => |cdf (μs n : Measure ℝ) x-cdf (μ : Measure ℝ) x|)
    (f := fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (fun n => (((monotone_cdf (μs n : Measure ℝ)).measurable.sub
      (monotone_cdf (μ : Measure ℝ)).measurable).abs).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      apply abs_le.mpr
      constructor <;> linarith [cdf_nonneg (μs n : Measure ℝ) x,cdf_nonneg (μ : Measure ℝ) x,
        cdf_le_one (μs n : Measure ℝ) x,cdf_le_one (μ : Measure ℝ) x])) (by
      filter_upwards [ae_restrict_of_ae hae] with x hx
      simpa only [sub_self,abs_zero] using (hx.sub_const (cdf (μ : Measure ℝ) x)).abs)
  simpa only [integral_zero] using H

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileWeakCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem quantileProbability_weak_subsequence (K : ℕ → ℕ)
    (A : (n : ℕ) → Fin (K n+1) → ℝ)
    (hA : ∀ n j, A n j ∈ Set.Icc 0 1) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Set.Icc 0 1) = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => quantileProbability (K (φ n)) (A (φ n))) atTop (𝓝 μ) := by
  have hc : IsCompact {μ : ProbabilityMeasure ℝ | ∀ _n : ℕ, μ (Set.Icc (0:ℝ) 1)ᶜ ≤ 0} :=
    isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
      (u := fun _ => (0:NNReal)) (K := fun _ => Set.Icc (0:ℝ) 1)
      tendsto_const_nhds (fun _ => isCompact_Icc) (Or.inl inferInstance)
  have hm (n : ℕ) : quantileProbability (K n) (A n) ∈
      {μ : ProbabilityMeasure ℝ | ∀ _n : ℕ, μ (Set.Icc (0:ℝ) 1)ᶜ ≤ 0} := by
    intro _
    apply le_of_eq
    apply (ProbabilityMeasure.null_iff_toMeasure_null _ _).mpr
    exact (prob_compl_eq_zero_iff measurableSet_Icc).mpr
      (quantileAtomLaw_supported (K n) (A n) (hA n))
  obtain ⟨μ,hμ,φ,hφ,ht⟩ := hc.tendsto_subseq hm
  refine ⟨μ,?_,φ,hφ,ht⟩
  apply (prob_compl_eq_zero_iff measurableSet_Icc).mp
  exact (ProbabilityMeasure.null_iff_toMeasure_null μ _).mp (le_antisymm (hμ 0) bot_le)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFMinimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_probability_cdf_one (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) : cdf (μ : Measure ℝ) 1=1 := by
  have H : (μ : Measure ℝ) (Iic 1)=1 := le_antisymm prob_le_one
    (by rw [← hμ]; exact measure_mono Icc_subset_Iic_self)
  rw [cdf_eq_real,Measure.real,H,ENNReal.toReal_one]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSupportDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_probability_ae (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) :
    ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0:ℝ) 1 := by
  rw [ae_iff]
  change (μ : Measure ℝ) (Icc (0:ℝ) 1)ᶜ=0
  rw [measure_compl measurableSet_Icc (by simp [hμ]),hμ,measure_univ,tsub_self]

theorem integral_unitCDF_probability (μ : ProbabilityMeasure ℝ) (s c : ℝ) :
    (∫ t, unitCDF t s*c ∂(μ : Measure ℝ))=cdf (μ : Measure ℝ) s*c := by
  have E : (fun t => unitCDF t s*c)=(Iic s).indicator (fun _ => c) := by
    funext t
    simp only [unitCDF,indicator_apply,mem_Iic]
    split_ifs <;> simp
  rw [E,integral_indicator measurableSet_Iic,setIntegral_const,cdf_eq_real,smul_eq_mul]

theorem supported_cdf_integral_duality (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Icc (0:ℝ) 1)) :
    (∫ s in Icc (0:ℝ) 1, cdf (μ : Measure ℝ) s*g s)=
      ∫ q, (∫ s in q..1, g s) ∂(μ : Measure ℝ) := by
  have E : (fun p : ℝ×ℝ => unitCDF p.1 p.2*g p.2)=
      {p : ℝ×ℝ | p.1≤p.2}.indicator (fun p => g p.2) := by
    funext p
    simp only [unitCDF,indicator_apply,mem_ofPred_eq]
    split_ifs <;> simp
  have HI : Integrable (fun p : ℝ×ℝ => unitCDF p.1 p.2*g p.2)
      ((μ : Measure ℝ).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    rw [E]
    exact (hg.comp_snd (μ : Measure ℝ)).indicator (measurableSet_le measurable_fst measurable_snd)
  have H := integral_integral_swap (f:=fun q s => unitCDF q s*g s) HI
  simp_rw [integral_unitCDF_probability] at H
  rw [← H]
  apply integral_congr_ae
  filter_upwards [supported_probability_ae μ hμ] with q hq
  exact unitCDF_mul_integral q hq g

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_SupportMinima
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_continuous_integrable (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) : Integrable f (μ : Measure ℝ) := by
  have H := hf.integrableOn_Icc (μ:=(μ : Measure ℝ))
  rw [IntegrableOn,Measure.restrict_eq_self_of_ae_mem (supported_probability_ae μ hμ)] at H
  exact H

theorem support_minima_of_integral_le (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {f : ℝ → ℝ} (hf : Continuous f)
    (hmin : ∀ q∈Icc (0:ℝ) 1, (∫ x, f x ∂(μ : Measure ℝ))≤f q) :
    ∀ q∈(μ : Measure ℝ).support,
      q∈Icc (0:ℝ) 1 ∧ f q=(∫ x, f x ∂(μ : Measure ℝ)) ∧
      ∀ r∈Icc (0:ℝ) 1, f q≤f r := by
  let C := ∫ x, f x ∂(μ : Measure ℝ)
  have HI := supported_continuous_integrable μ hμ hf.continuousOn
  have Hn : ∀ᵐ x ∂(μ : Measure ℝ), 0≤f x-C := by
    filter_upwards [supported_probability_ae μ hμ] with x hx
    exact sub_nonneg.mpr (hmin x hx)
  have Hz : ∫ x, (f x-C) ∂(μ : Measure ℝ)=0 := by
    rw [integral_sub HI (integrable_const C),integral_const,probReal_univ,one_smul]
    exact sub_self _
  have He : ∀ᵐ x ∂(μ : Measure ℝ), f x=C := by
    have H := (integral_eq_zero_iff_of_nonneg_ae Hn (HI.sub (integrable_const C))).mp Hz
    filter_upwards [H] with x hx
    exact sub_eq_zero.mp hx
  have HS := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    (isClosed_eq hf continuous_const) He
  have HD := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  intro q hq
  have Hq : f q=C := HS hq
  exact ⟨HD hq,Hq,fun r hr => Hq ▸ hmin r hr⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFPotential_eq {β : ℝ} {α : ℝ → ℝ} {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) :
    scalarCDFPotential β α q=∫ s in q..1, (scalarCDFOverlap β α s-s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hq.2] at hs
  dsimp only
  rw [cdfGradientTest_eq ⟨hq.1.trans hs.1,hs.2⟩]
  ring

theorem scalarCDFPotential_hasDerivAt {β : ℝ} {α : ℝ → ℝ}
    (hc : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) (q : ℝ) :
    HasDerivAt (scalarCDFPotential β α) (cdfGradientTest β α q) q := by
  have Hc := (cdfGradientTest_continuous hc).neg
  have H := intervalIntegral.integral_hasDerivAt_left
    (Hc.intervalIntegrable q 1) Hc.stronglyMeasurable.stronglyMeasurableAtFilter Hc.continuousAt
  convert H using 1 <;> first | rfl | exact Subsingleton.elim _ _ | simp only [Pi.neg_apply, neg_neg]

theorem scalarCDFPotential_continuous {β : ℝ} {α : ℝ → ℝ}
    (hc : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) :
    Continuous (scalarCDFPotential β α) :=
  continuous_iff_continuousAt.mpr (fun q => (scalarCDFPotential_hasDerivAt hc q).continuousAt)

theorem scalarCDFParisi_support_minima {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    ∀ q∈(μ : Measure ℝ).support,
      q∈Icc (0:ℝ) 1 ∧
      scalarCDFPotential β (cdf (μ : Measure ℝ)) q=
        (∫ x, scalarCDFPotential β (cdf (μ : Measure ℝ)) x ∂(μ : Measure ℝ)) ∧
      ∀ r∈Icc (0:ℝ) 1,
        scalarCDFPotential β (cdf (μ : Measure ℝ)) q≤ scalarCDFPotential β (cdf (μ : Measure ℝ)) r := by
  let α := cdf (μ : Measure ℝ)
  have ha : ∀ z, α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 := supported_probability_cdf_one μ hμ
  have HC := scalarCDFOverlap_continuousOn β α ha h1
  apply support_minima_of_integral_le μ hμ (scalarCDFPotential_continuous HC)
  intro q hq
  have HG : ContinuousOn (fun s => scalarCDFOverlap β α s-s) (Icc (0:ℝ) 1) := HC.sub continuousOn_id
  have HD := supported_cdf_integral_duality μ hμ HG.integrableOn_Icc
  have HE : (∫ x, scalarCDFPotential β α x ∂(μ : Measure ℝ))=
      (∫ x, (∫ s in x..1, scalarCDFOverlap β α s-s) ∂(μ : Measure ℝ)) := by
    apply integral_congr_ae
    filter_upwards [supported_probability_ae μ hμ] with x hx
    exact scalarCDFPotential_eq hx
  rw [HE,← HD]
  exact scalarCDFPotential_minimum_bound hβ α ha h1 hmin hq

theorem scalarCDFParisi_overlap_on_interior_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {q : ℝ} (hqs : q∈(μ : Measure ℝ).support) (hq : q∈Ioo (0:ℝ) 1) :
    scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have Hm := (scalarCDFParisi_support_minima hβ μ hμ hmin q hqs).2.2
  have HL : IsLocalMin (scalarCDFPotential β (cdf (μ : Measure ℝ))) q := by
    filter_upwards [Icc_mem_nhds hq.1 hq.2] with r hr
    exact Hm r hr
  have HC := scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one μ hμ)
  have HE := HL.hasDerivAt_eq_zero (scalarCDFPotential_hasDerivAt HC q)
  rw [cdfGradientTest_eq ⟨hq.1.le,hq.2.le⟩] at HE
  exact (sub_eq_zero.mp HE).symm

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFHeatContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ENNReal NNReal Topology Interval
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOverlap_heat_increment_lower (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0) :
    β^2*(q-s)*(∫ z, (gaussianHeat (β*Real.sqrt (q-s))
      (scalarCDFHessian β α q (Real.toNNReal (1-q))) (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)  ≤
      scalarCDFOverlap β α q-scalarCDFOverlap β α s := by
  have hr : Real.toNNReal (1-q)  ≤  1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hu := scalarCDFGradient_hasDerivAt β ha α.mono q _ hr
  have hc := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hb (x : ℝ) := (scalarCDF_derivative_bounds β ha α.mono q _ hr x).1
  have hdf (x : ℝ) : |scalarCDFHessian β α q (Real.toNNReal (1-q)) x|  ≤  1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (scalarCDFGradient β α q (Real.toNNReal (1-q)) x)]
  have he : (β*Real.sqrt q)^2=(β*Real.sqrt s)^2+(β*Real.sqrt (q-s))^2 := by
    simp only [mul_pow,Real.sq_sqrt (hs.trans hsq),Real.sq_sqrt hs,Real.sq_sqrt (sub_nonneg.mpr hsq)]
    ring
  have H := gaussianHeat_variance_integral_lower hu hc zero_le_one zero_le_one hb hdf
    (β*Real.sqrt (q-s)) (β*Real.sqrt s) (β*Real.sqrt q) he
  have HG := scalarCDFGradient_heat_prefix β α ha h1 hs hsq hq
    (fun z hz' => hz z ⟨hs.trans hz'.1,hz'.2⟩)
  rw [scalarCDFOverlap_heat_prefix β ha α.mono ⟨hs.trans hsq,hq⟩ hz,
    scalarCDFOverlap_heat_prefix β ha α.mono ⟨hs,hsq.trans hq⟩
      (fun z hz' => hz z ⟨hz'.1,hz'.2.trans_le hsq⟩),HG]
  simpa only [mul_pow,Real.sq_sqrt (sub_nonneg.mpr hsq)] using H

theorem scalarCDFHeatContact_chi_sq_gt (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0)
    (hcontact : scalarCDFOverlap β α q=q) :
    1 < β^2*(∫ z, (scalarCDFHessian β α q (Real.toNNReal (1-q))
      (β*Real.sqrt q*z))^2 ∂gaussianReal 0 1) := by
  let f : ℝ → ℝ := scalarCDFGradient β α q (Real.toNNReal (1-q))
  let df : ℝ → ℝ := scalarCDFHessian β α q (Real.toNNReal (1-q))
  let k : ℝ := β*Real.sqrt q
  have hr : Real.toNNReal (1-q)  ≤  1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hd (x : ℝ) : HasDerivAt f (df x) x := scalarCDFGradient_hasDerivAt β ha α.mono q _ hr x
  have hc : Continuous df := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hb (x : ℝ) : |f x|  ≤  1 := (scalarCDF_derivative_bounds β ha α.mono q _ hr x).1
  have hdf (x : ℝ) : |df x|  ≤  1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (f x)]
  have hmean : (∫ z, f (k*z) ∂gaussianReal 0 1)=0 := by
    have H := congrFun (scalarCDFGradient_heat_prefix β α ha h1 le_rfl hq0.le hq1 hz) 0
    rw [scalarCDFGradient_zero β ha α.mono 0 _ (by simp)] at H
    simpa only [gaussianHeat,sub_zero,zero_add,f,k] using H.symm
  have hsecond : (∫ z, f (k*z)^2 ∂gaussianReal 0 1)=q := by
    simpa only [f,k,scalarCDFOverlap_heat_prefix β ha α.mono ⟨hq0.le,hq1⟩ hz] using hcontact
  have hnonconstant : ¬∃ c, ∀ z, f (k*z)=c := by
    rintro ⟨c,hc⟩
    simp only [hc,integral_const,probReal_univ,one_smul] at hmean hsecond
    rw [hmean,zero_pow (by decide)] at hsecond
    exact hq0.ne' hsecond.symm
  have HD (z : ℝ) : HasDerivAt (fun z => f (k*z)) (k*df (k*z)) z := by
    convert (hd (k*z)).comp z ((hasDerivAt_id z).const_mul k) using 1 <;> first | rfl | ring
  have HP := gaussian_strict_poincare HD (by fun_prop) zero_le_one (abs_nonneg k)
    (fun z => hb (k*z)) (fun z => by
      rw [abs_mul]; simpa only [mul_one] using mul_le_mul_of_nonneg_left (hdf (k*z)) (abs_nonneg k)) hnonconstant
  rw [hmean,hsecond,zero_pow (by decide),sub_zero] at HP
  simp_rw [mul_pow] at HP
  rw [integral_const_mul] at HP
  have hk : k^2=β^2*q := by dsimp [k]; rw [mul_pow,Real.sq_sqrt hq0.le]
  rw [hk] at HP
  change 1 < β^2*(∫ z, df (k*z)^2 ∂gaussianReal 0 1)
  nlinarith

theorem not_min_of_contact_increment {G Γ J : ℝ → ℝ} (hG : Continuous G)
    (hd : ∀ s∈Icc (0:ℝ) 1, HasDerivAt G (s-Γ s) s) (hJ : Continuous J)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (hcontact : Γ q=q) (hJq : 1 < J q)
    (hi : ∀ s∈Icc (0:ℝ) q, (q-s)*J s ≤ Γ q-Γ s) :
    ¬∀ r∈Icc (0:ℝ) 1, G q ≤ G r := by
  obtain ⟨ε,hε,hεJ⟩ := Metric.eventually_nhds_iff.mp (hJ.continuousAt.preimage_mem_nhds
    (Ioi_mem_nhds hJq))
  let δ := min (q/2) (ε/2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδq : δ  ≤  q/2 := min_le_left _ _
  have hδε : δ  ≤  ε/2 := min_le_right _ _
  let r := q-δ
  have hr0 : 0  ≤  r := by dsimp [r]; linarith
  have hrq : r < q := by dsimp [r]; linarith
  have hpos {s : ℝ} (hs : s∈Ioo r q) : 0 < s-Γ s := by
    have hs0 : 0  ≤  s := hr0.trans hs.1.le
    have hsJ : 1 < J s := by
      apply hεJ
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hs.2.le)]
      dsimp [r] at hs
      linarith [hs.1]
    have H := hi s ⟨hs0,hs.2.le⟩
    rw [hcontact] at H
    have HH := mul_lt_mul_of_pos_left hsJ (sub_pos.mpr hs.2)
    nlinarith
  have hstrict := strictMonoOn_of_deriv_pos (convex_Icc r q) hG.continuousOn
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s ⟨hr0.trans hs.1.le,hs.2.le.trans hq1⟩).deriv]
      exact hpos hs)
  intro hmin
  exact (not_lt_of_ge (hmin r ⟨hr0,hrq.le.trans hq1⟩))
    (hstrict ⟨le_rfl,hrq.le⟩ ⟨hrq.le,le_rfl⟩ hrq)

theorem heat_increment_coefficient_continuous {f : ℝ → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B) (β q : ℝ) :
    Continuous (fun s : ℝ => β^2*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) f
      (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)) := by
  have hp : Continuous (fun s : ℝ => (β*Real.sqrt (q-s),β*Real.sqrt s)) :=
    (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).prodMk
      (continuous_const.mul Real.continuous_sqrt)
  exact continuous_const.mul ((gaussianHeat_sq_average_continuous hf hB hb).comp hp)

theorem scalarCDFPotential_not_min_heat_prefix (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q  ≤  1) (hz : ∀ z∈Ico 0 q, α z=0)
    (hcontact : scalarCDFOverlap β α q=q) :
    ¬∀ r∈Icc (0:ℝ) 1, scalarCDFPotential β α q ≤ scalarCDFPotential β α r := by
  let df : ℝ → ℝ := scalarCDFHessian β α q (Real.toNNReal (1-q))
  let k : ℝ := β*Real.sqrt q
  have hr : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]; linarith
  have hc : Continuous df := (scalarCDFHessian_lipschitz β ha α.mono q _ hr).continuous
  have hdf (x : ℝ) : |df x| ≤ 1 := by
    have H := scalarCDF_derivative_bounds β ha α.mono q _ hr x
    rw [abs_of_nonneg H.2.1]; nlinarith [sq_nonneg (scalarCDFGradient β α q (Real.toNNReal (1-q)) x)]
  let J : ℝ → ℝ := fun s => β^2*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) df
    (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1)
  have hJ : Continuous J := heat_increment_coefficient_continuous hc zero_le_one hdf β q
  have hJq : 1 < J q := by
    have HJ : J q=β^2*(∫ z, df (k*z)^2 ∂gaussianReal 0 1) := by
      simp [J,gaussianHeat,k]
    rw [HJ]
    exact scalarCDFHeatContact_chi_sq_gt β α ha h1 hq0 hq1 hz hcontact
  have hΓ := scalarCDFOverlap_continuousOn β α ha h1
  apply not_min_of_contact_increment (scalarCDFPotential_continuous hΓ)
    (fun s hs => by simpa only [cdfGradientTest_eq hs] using scalarCDFPotential_hasDerivAt hΓ s)
    hJ hq0 hq1 hcontact hJq
  intro s hs
  have H := scalarCDFOverlap_heat_increment_lower β α ha h1 hs.1 hs.2 hq1 hz
  have HE : (q-s)*J s=β^2*(q-s)*(∫ z, (gaussianHeat (β*Real.sqrt (q-s)) df
      (β*Real.sqrt s*z))^2 ∂gaussianReal 0 1) := by dsimp [J]; ring
  rw [HE]
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFIntervalConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFValue_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) s t)
      (scalarCDFValue β α s t) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have HT : Tendsto (fun n => scalarTimeMassConstant β*cdfDistance (αn n) α) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul (scalarTimeMassConstant β)
  filter_upwards [(tendsto_order.mp HT).2 ε hε] with n hn' x
  have H := scalarCDFValue_cdf_lipschitz β (hn n) (hnm n) hα hαm s t ht x
  have HE := cdfDistance_subinterval_le (hnm n) hαm hs hst
  have HB := H.trans (mul_le_mul_of_nonneg_left HE (scalarTimeMassConstant_nonneg β))
  rw [Real.dist_eq,abs_sub_comm]
  exact HB.trans_lt hn'

theorem scalarCDFHessian_tendstoUniformly_interval (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) :
    TendstoUniformly (fun n => scalarCDFHessian β (αn n) s t)
      (scalarCDFHessian β α s t) atTop := by
  apply uniform_derivative_convergence susceptibilityLipschitzConstant
    (fun n x => scalarCDFGradient_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFGradient_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFHessian_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFHessian_lipschitz β hα hαm s t ht)
  exact uniform_derivative_convergence 1
    (fun n x => scalarCDFValue_hasDerivAt β (hn n) (hnm n) s t ht x)
    (scalarCDFValue_hasDerivAt β hα hαm s t ht)
    (fun n => scalarCDFGradient_lipschitz β (hn n) (hnm n) s t ht)
    (scalarCDFGradient_lipschitz β hα hαm s t ht)
    (scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD s t ht hs hst)

theorem scalarCDFAverage_tendsto_cdf_lipschitz (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) {K B L : ℝ≥0}
    (hfK : LipschitzWith K f) (hgL : LipschitzWith L g) (hB : ∀ z, |g z|≤B)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hs : 0 ≤ s) (hst : s + t ≤ 1) (x : ℝ) :
    Tendsto (fun n => scalarCDFAverage β (αn n) s t f g x) atTop
      (𝓝 (scalarCDFAverage β α s t f g x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A : ℝ := 2*((L:ℝ)+2*(B:ℝ)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  let h : ℝ := ε/(4*(A+1))
  have hh : 0<h := by dsimp [h]; positivity
  have hsmall : A*h<ε := by
    have HE : 4*(A+1)*h=ε := by dsimp [h]; field_simp
    nlinarith
  have HT : Tendsto (fun n =>
      2*(scalarTimeMassConstantK β (K+B+B)*cdfDistance (αn n) α)/h+A*h) atTop (𝓝 (A*h)) := by
    simpa only [mul_zero,zero_div,zero_add] using
      (((hD.const_mul (scalarTimeMassConstantK β (K+B+B))).const_mul 2).div_const h).add_const (A*h)
  filter_upwards [(tendsto_order.mp HT).2 ε hsmall] with n hbound
  rw [Real.dist_eq]
  have H := scalarCDFAverage_cdf_stability_lipschitz β (hn n) (hnm n) hα hαm
    hf hfK hgL hB s t ht x h hh
  have HD := cdfDistance_subinterval_le (hnm n) hαm hs hst
  apply (H.trans ?_).trans_lt hbound
  exact add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left HD (scalarTimeMassConstantK_nonneg β _)) (by norm_num : (0:ℝ)≤2)) hh.le) le_rfl

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFSupportContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem derivative_nonpos_at_right_minimum {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 1) (hm : ∀ r∈Icc (0:ℝ) 1, f 1≤f r) : d≤0 := by
  have H := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto H
  have HP : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), 0 < r :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [HP,self_mem_nhdsWithin] with r hr0 hr1
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm r ⟨hr0.le,hr1.le⟩))
    (sub_nonpos.mpr hr1.le)

theorem scalarCDFParisi_overlap_on_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {q : ℝ} (hqs : q∈(μ : Measure ℝ).support) :
    scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have hs := scalarCDFParisi_support_minima hβ μ hμ hmin q hqs
  have ha (x : ℝ) : cdf (μ : Measure ℝ) x∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  by_cases hq0 : q=0
  · subst q
    exact scalarCDFOverlap_zero β ha (cdf (μ : Measure ℝ)).mono
  by_cases hq1 : q=1
  · subst q
    have HC := scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ)) ha
      (supported_probability_cdf_one μ hμ)
    have HD := derivative_nonpos_at_right_minimum (scalarCDFPotential_hasDerivAt HC 1) hs.2.2
    rw [cdfGradientTest_eq ⟨zero_le_one,le_rfl⟩] at HD
    have HB := scalarCDFOverlap_nonneg_le_one β ha (cdf (μ : Measure ℝ)).mono
      (show (1:ℝ)∈Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
    linarith [HB.2]
  · exact scalarCDFParisi_overlap_on_interior_support hβ μ hμ hmin hqs
      ⟨lt_of_le_of_ne hs.1.1 (Ne.symm hq0),lt_of_le_of_ne hs.1.2 hq1⟩

theorem scalarCDFParisi_overlap_eq_ae {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    ∀ᵐ q ∂(μ : Measure ℝ), scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have H : ∀ᵐ q ∂(μ : Measure ℝ), q∈(μ : Measure ℝ).support := (μ : Measure ℝ).support_mem_ae
  exact H.mono (fun _ hq => scalarCDFParisi_overlap_on_support hβ μ hμ hmin hq)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSuffixSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_const {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (n : ℕ) (m v : Fin n → ℝ) (c x : ℝ) :
    scalarHierarchyAverage n m v f (fun _ => c) x=c := by
  rw [scalarHierarchyAverage_integral hf (BoundedScalar.const c)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  simp

theorem BoundedScalar.finset_sum {ι : Type*} (s : Finset ι) {g : ι → ℝ → ℝ}
    (hg : ∀ i∈s, BoundedScalar (g i)) : BoundedScalar (fun x => ∑ i∈s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BoundedScalar.const 0
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      (hg a (Finset.mem_insert_self a s)).add (ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)))

theorem scalarHierarchyAverage_sum {ι : Type*} (s : Finset ι) {f : ℝ → ℝ}
    {g : ι → ℝ → ℝ} (hf : BoundedDerivs f) (hg : ∀ i∈s, BoundedScalar (g i))
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    scalarHierarchyAverage n m v f (fun y => ∑ i∈s, g i y) x=
      ∑ i∈s, scalarHierarchyAverage n m v f (g i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using scalarHierarchyAverage_const hf n m v 0 x
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [scalarHierarchyAverage_add hf (hg a (Finset.mem_insert_self a s))
      (BoundedScalar.finset_sum s (fun i hi => hg i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))]

theorem scalarMomentSquare_bounded {f g : ℝ → ℝ} (hf : BoundedDerivs f)
    (hg : BoundedScalar g) (n : ℕ) (m v : Fin n → ℝ) (j : Fin (n+1)) :
    BoundedScalar (scalarMomentSquare n m v f g j) := by
  induction n generalizing f g with
  | zero => exact hg.sq
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [scalarMomentSquare,Fin.lastCases_last]
      exact scalarHierarchyAverage_bounded hf hg.sq (n+1) m v
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc]
      exact ih (scalarStep_regular hf _ _) (hg.scalarStepAverage hf _ _) _ _ j

theorem scalarMomentSquare_last (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    scalarMomentSquare n m v f g (Fin.last n)=scalarHierarchyAverage n m v f (fun x => (g x)^2) := by
  cases n with
  | zero => rfl
  | succ n => simp only [scalarMomentSquare,Fin.lastCases_last]

theorem scalarMomentSquare_suffix_average (a b : ℕ) (m v : Fin (a+b) → ℝ)
    (f g : ℝ → ℝ) (j : Fin (b+1)) :
    scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
      (scalarMomentSquare b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g j)=
      scalarMomentSquare (a+b) m v f g (j.natAdd a) := by
  induction b generalizing f g with
  | zero =>
    have hj : j=0 := by ext; omega
    subst j
    rw [show (0:Fin 1).natAdd a=Fin.last a by ext; simp]
    change scalarHierarchyAverage a m v f (fun x => (g x)^2)=scalarMomentSquare a m v f g (Fin.last a)
    exact (scalarMomentSquare_last a m v f g).symm
  | succ b ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [scalarMomentSquare_last,show (Fin.last (b+1)).natAdd a=Fin.last (a+(b+1)) by ext; simp,
        scalarMomentSquare_last]
      exact (scalarHierarchyAverage_split a (b+1) m v f (fun x => (g x)^2)).symm
    · simp only [scalarMomentSquare,Fin.lastCases_castSucc]
      have he : j.castSucc.natAdd a=(j.natAdd a).castSucc := by ext; rfl
      rw [he,Fin.lastCases_castSucc]
      exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
        (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
        (scalarStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g) j

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_SuffixPartitionSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchy_suffix_hessian_overlap_sum_of_suffix (a b : ℕ) (m v : Fin (a+b) → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone (fun i : Fin b => m (i.natAdd a))) (x : ℝ) :
    scalarHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) scalarSpinTerminal)
      (rootHessian 0 (scalarHierarchy b (fun i => m (i.natAdd a))
        (fun i => v (i.natAdd a)) scalarSpinTerminal)) x=
      1-∑ j, hierarchyAtom b (fun i => m (i.natAdd a)) 1 j*
        scalarMomentSquare (a+b) m v scalarSpinTerminal scalarMagnetization (j.natAdd a) x := by
  let mb := fun i : Fin b => m (i.natAdd a)
  let vb := fun i : Fin b => v (i.natAdd a)
  have hf : BoundedDerivs (scalarHierarchy b mb vb scalarSpinTerminal) :=
    scalarHierarchy_regular b mb vb scalarSpinTerminal_regular
  have hg : BoundedScalar scalarMagnetization :=
    ⟨(Real.continuous_sinh.div Real.continuous_cosh (fun x => ne_of_gt (Real.cosh_pos x))),1,zero_le_one,scalarMagnetization_abs_le_one⟩
  have hM (j : Fin (b+1)) : BoundedScalar (scalarMomentSquare b mb vb scalarSpinTerminal scalarMagnetization j) :=
    scalarMomentSquare_bounded scalarSpinTerminal_regular hg b mb vb j
  have HE : rootHessian 0 (scalarHierarchy b mb vb scalarSpinTerminal)=
      fun y => 1-∑ j, hierarchyAtom b mb 1 j*scalarMomentSquare b mb vb scalarSpinTerminal scalarMagnetization j y := by
    funext y
    exact scalarHierarchy_spin_hessian_overlap_sum b mb vb (fun i => hm _) hmono y
  change scalarHierarchyAverage a _ _ (scalarHierarchy b mb vb scalarSpinTerminal) _ x=_
  rw [HE,scalarHierarchyAverage_sub hf (BoundedScalar.const 1)
    (BoundedScalar.finset_sum Finset.univ (fun j _ => (hM j).const_mul _)),
    scalarHierarchyAverage_const hf,scalarHierarchyAverage_sum Finset.univ hf
    (fun j _ => (hM j).const_mul _)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarHierarchyAverage_const_mul hf (hM j)]
  congr 1
  exact congrFun (scalarMomentSquare_suffix_average a b m v scalarSpinTerminal scalarMagnetization j) x

theorem scalarCDFSusceptibilityAverage_eq_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (a b : ℕ) (q : Fin (a+1) → ℝ) (p : Fin (b+1) → ℝ)
    (hq : Monotone q) (hp : Monotone p) (hq0 : q 0=0) (hp1 : p (Fin.last b)=1)
    (hr : q (Fin.last a)=p 0) (m : Fin a → ℝ) (l : Fin b → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hl : ∀ i, l i∈Icc (0:ℝ) 1) (hlm : Monotone l)
    (hmodelq : ∀ i : Fin a, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    (hmodelp : ∀ i : Fin b, ∀ z∈Ico (p i.castSucc) (p i.succ), α z=l i) :
    scalarCDFSusceptibilityAverage β α (p 0)=
      1-∑ j, hierarchyAtom b l 1 j*scalarCDFOverlap β α (p j) := by
  let r := p 0
  have hr0 : r∈Icc (0:ℝ) 1 := by
    constructor
    · change 0 ≤ p 0
      rw [← hr,← hq0]; exact hq (Fin.zero_le _)
    · rw [← hp1]; exact hp (Fin.le_last _)
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr0.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr0.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr0.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr0.1]
  let f := scalarCDFValue β α r s
  let u := scalarCDFGradient β α r s
  let χ := scalarCDFHessian β α r s
  have hf : f=scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal := by
    funext x
    exact scalarCDFOperator_eq_partition scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β hα hαm b p hp l hl hmodelp s hs1 (by rw [hp1]; exact hs) x
  have hu : u=rootGradient 0 (scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal) := by
    funext x
    have H := scalarCDFValue_hasDerivAt β hα hαm r s hs1 x
    change HasDerivAt f (u x) x at H
    rw [hf] at H
    exact H.unique (scalarHierarchy_spin_hasDerivAt _ _ _ x)
  have hχ : χ=rootHessian 0 (scalarHierarchy b l (timeGridCoefficients b β p) scalarSpinTerminal) := by
    funext x
    have H := scalarCDFGradient_hasDerivAt β hα hαm r s hs1 x
    change HasDerivAt u (χ x) x at H
    rw [hu] at H
    exact H.unique (scalarHierarchy_spin_gradient_hasDerivAt _ _ _ x)
  have H := scalarCDFAverage_eq_partition_lipschitz (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    β hα hαm a q hq m hm hmodelq t ht1 (by rw [hr,hq0,sub_zero]; exact ht) 0
  rw [hq0] at H
  change scalarCDFAverage β α 0 t f χ 0=_ at H
  change scalarCDFAverage β α 0 t f χ 0=_
  rw [H]
  change scalarHierarchyAverage a m (timeGridCoefficients a β q) f χ 0=_
  rw [hf,hχ]
  have hml (i : Fin (a+b)) : Fin.append m l i∈Icc (0:ℝ) 1 := by
    refine Fin.addCases ?_ ?_ i
    · intro i; simpa only [Fin.append_left] using hm i
    · intro j; simpa only [Fin.append_right] using hl j
  have hmono : Monotone (fun i : Fin b => Fin.append m l (i.natAdd a)) := by
    simpa only [Fin.append_right] using hlm
  have HS := scalarHierarchy_suffix_hessian_overlap_sum_of_suffix a b (Fin.append m l)
    (Fin.append (timeGridCoefficients a β q) (timeGridCoefficients b β p)) hml hmono 0
  simp only [Fin.append_left,Fin.append_right] at HS
  rw [HS]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarCDFOverlap_eq_two_partitions_index β hα hαm a b q p hq hp hq0 hp1 hr
    m l hm hl hmodelq hmodelp j]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFUpperArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_cdf_upper_area (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    (∫ s in r..1, cdf (μ : Measure ℝ) s)=1-∫ q,max q r ∂(μ : Measure ℝ) := by
  have E : (fun p : ℝ×ℝ => unitCDF p.1 p.2)=
      {p : ℝ×ℝ | p.1≤p.2}.indicator (fun _ => (1:ℝ)) := by
    funext p
    simp only [unitCDF,indicator_apply,mem_ofPred_eq]
  have HI : Integrable (fun p : ℝ×ℝ => unitCDF p.1 p.2)
      ((μ : Measure ℝ).prod (volume.restrict (Icc r 1))) := by
    rw [E]
    exact (integrable_const 1).indicator (measurableSet_le measurable_fst measurable_snd)
  have H := integral_integral_swap (f:=fun q s => unitCDF q s) HI
  have hc (s : ℝ) : (∫ q,unitCDF q s ∂(μ : Measure ℝ))=cdf (μ : Measure ℝ) s := by
    simpa only [mul_one] using integral_unitCDF_probability μ s 1
  simp_rw [hc] at H
  rw [intervalIntegral.integral_of_le hr.2,← integral_Icc_eq_integral_Ioc,← H]
  have he : (∫ q, ∫ s in Icc r 1,unitCDF q s ∂volume ∂(μ : Measure ℝ))=
      ∫ q,1-max q r ∂(μ : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [supported_probability_ae μ hμ] with q hq
    have E : (fun s => unitCDF q s)=(Ici q).indicator (fun _ => (1:ℝ)) := by
      simpa only [mul_one] using unitCDF_mul_indicator q (fun _ => (1:ℝ))
    rw [E,setIntegral_indicator measurableSet_Ici]
    have he : Icc r 1∩Ici q=Icc (max q r) 1 := by
      ext x; simp only [mem_inter_iff,mem_Icc,mem_Ici,max_le_iff]; tauto
    rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (max_le hq.2 hr.2)]
    simp
  have hM : Integrable (fun q : ℝ => max q r) (μ : Measure ℝ) :=
    supported_continuous_integrable μ hμ (continuous_id.max continuous_const).continuousOn
  rw [he,integral_sub (integrable_const 1) hM]
  simp

theorem scalarCDFParisi_susceptibility_area {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    (hs : ∀ r∈Icc (0:ℝ) 1, scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
      1-∫ x,scalarCDFOverlap β (cdf (μ : Measure ℝ)) (max x r) ∂(μ : Measure ℝ))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
      (∫ s in r..1,cdf (μ : Measure ℝ) s)+cdf (μ : Measure ℝ) r*
        (r-scalarCDFOverlap β (cdf (μ : Measure ℝ)) r) := by
  let Γ := scalarCDFOverlap β (cdf (μ : Measure ℝ))
  have he : (fun x => Γ (max x r))=ᵐ[(μ : Measure ℝ)]
      (fun x => max x r+(Iic r).indicator (fun _ => Γ r-r) x) := by
    filter_upwards [scalarCDFParisi_overlap_eq_ae hβ μ hμ hmin] with x hx
    by_cases hxr : x ≤ r
    · simp only [max_eq_right hxr,indicator_apply,mem_Iic,ite_eq_left hxr]
      ring
    · simp only [max_eq_left (le_of_not_ge hxr),indicator_apply,mem_Iic,ite_eq_right hxr,add_zero]
      exact hx
  have hM : Integrable (fun x : ℝ => max x r) (μ : Measure ℝ) :=
    supported_continuous_integrable μ hμ (continuous_id.max continuous_const).continuousOn
  rw [hs r hr,integral_congr_ae he,integral_add hM ((integrable_const (Γ r-r)).indicator measurableSet_Iic),
    integral_indicator measurableSet_Iic,setIntegral_const,supported_cdf_upper_area μ hμ hr,
    smul_eq_mul,← cdf_eq_real]
  dsimp [Γ]
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFZeroSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdf_zero_below_least_support (μ : ProbabilityMeasure ℝ) {q z : ℝ}
    (hq : IsLeast (μ : Measure ℝ).support q) (hz : z<q) :
    cdf (μ : Measure ℝ) z=0 := by
  have H : (μ : Measure ℝ) (Iic z)=0 := by
    apply measure_mono_null (t:=(μ : Measure ℝ).supportᶜ) _ (μ : Measure ℝ).measure_compl_support
    intro x hx hs
    exact (not_le_of_gt hz) (le_trans (hq.2 hs) hx)
  rw [cdf_eq_real,measureReal_def,H,ENNReal.toReal_zero]

theorem scalarCDFParisi_zero_mem_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    (0:ℝ)∈(μ : Measure ℝ).support := by
  have HS := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  have HC : IsCompact (μ : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (μ : Measure ℝ).isClosed_support HS
  obtain ⟨q,hq⟩ := HC.exists_isLeast ((μ : Measure ℝ).nonempty_support (by
    intro H
    have H1 := measure_univ (μ:=(μ : Measure ℝ))
    simp only [H,Measure.coe_zero,Pi.zero_apply,zero_ne_one] at H1))
  have hbound := HS hq.1
  have he : q=0 := by
    by_contra H
    have hq0 : 0<q := lt_of_le_of_ne hbound.1 (Ne.symm H)
    have hm := (scalarCDFParisi_support_minima hβ μ hμ hmin q hq.1).2.2
    exact scalarCDFPotential_not_min_heat_prefix β (cdf (μ : Measure ℝ))
      (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one μ hμ)
      hq0 hbound.2 (fun z hz => cdf_zero_below_least_support μ hq hz.2)
      (scalarCDFParisi_overlap_on_support hβ μ hμ hmin hq.1) hm
  simpa only [he] using hq.1

theorem cdf_pos_of_zero_mem_support (μ : ProbabilityMeasure ℝ)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support) {s : ℝ} (hs : 0 < s) :
    0 < cdf (μ : Measure ℝ) s := by
  have H : 0<(μ : Measure ℝ) (Iic s) :=
    (Measure.mem_support_iff_forall (μ:=(μ : Measure ℝ)) 0).mp h0 _ (Iic_mem_nhds hs)
  rw [cdf_eq_real,measureReal_def]
  exact ENNReal.toReal_pos H.ne' (measure_ne_top _ _)

theorem cdf_area_strict (μ : ProbabilityMeasure ℝ)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support) {h : ℝ} (hh : 0<h) :
    (∫ s in h..1, cdf (μ : Measure ℝ) s)<(∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) := by
  have HI (a b : ℝ) : IntervalIntegrable (cdf (μ : Measure ℝ)) volume a b :=
    (cdf (μ : Measure ℝ)).mono.intervalIntegrable
  have HP := intervalIntegral.intervalIntegral_pos_of_pos_on (HI 0 h)
    (fun s hs => cdf_pos_of_zero_mem_support μ h0 hs.1) hh
  have HE := intervalIntegral.integral_add_adjacent_intervals (HI 0 h) (HI h 1)
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileWeakIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileAtomLaw_integrable (k : ℕ) (Q : Fin (k+1) → ℝ) (f : ℝ → ℝ) :
    Integrable f (quantileAtomLaw k Q) := by
  unfold quantileAtomLaw
  apply integrable_finsetSum_measure.mpr
  intro j _
  exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

theorem quantileAtomLaw_integral (k : ℕ) (Q : Fin (k+1) → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂quantileAtomLaw k Q)=(1/(k+1:ℕ))*∑ j, f (Q j) := by
  unfold quantileAtomLaw
  rw [integral_finsetSum_measure (fun j _ =>
    (integrable_dirac (by finiteness)).smul_measure (by finiteness))]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (by positivity :
    0≤((k+1:ℕ):ℝ)⁻¹),smul_eq_mul,← Finset.mul_sum,one_div]

theorem scalarCDFOverlapTest_eq (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ x, α x∈Icc (0:ℝ) 1) (h1 : α 1=1) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    scalarCDFOverlapTest β α ha h1 x=scalarCDFOverlap β α x := by
  change scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x)=_
  rw [projIcc_of_mem _ hx]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileMaxOverlapIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileMaxOverlap_integral_tendsto (β : ℝ) (K : ℕ → ℕ)
    (Q : (n : ℕ) → Fin (K n+1) → ℝ) (hQ : ∀ n, Q n∈admissibleQuantiles (K n))
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1)
    (ht : Tendsto (fun n => quantileProbability (K n) (Q n)) atTop (𝓝 μ)) :
    Tendsto (fun n => (1/(K n+1:ℕ))*∑ j, scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max (Q n j) r))
      atTop (𝓝 (∫ x, scalarCDFOverlap β (cdf (μ : Measure ℝ)) (max x r) ∂(μ : Measure ℝ))) := by
  let α := cdf (μ : Measure ℝ)
  have ha (x : ℝ) : α x∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have h1 : α 1=1 := supported_probability_cdf_one μ hμ
  let f := (scalarCDFOverlapTest β α ha h1).compContinuous
    ⟨fun x : ℝ => max x r,continuous_id.max continuous_const⟩
  have hf (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : f x=scalarCDFOverlap β α (max x r) :=
    scalarCDFOverlapTest_eq β α ha h1 ⟨hx.1.trans (le_max_left _ _),max_le hx.2 hr.2⟩
  have hcdf (n : ℕ) : cdf (quantileProbability (K n) (Q n) : Measure ℝ)=
      quantileCDF (K n) (Q n) := by
    ext x
    exact cdf_eq_real _ _
  have hD : Tendsto (fun n => cdfDistance (quantileCDF (K n) (Q n)) α) atTop (𝓝 0) := by
    simpa only [cdfDistance,hcdf] using cdf_L1_tendsto_of_weak ht
  have hU := scalarCDFOverlap_tendstoUniformlyOn β ha α.mono
    (fun n => quantileCDF_bounds (K n) (Q n))
    (fun n => quantileCDF_monotone (K n) (Q n)) hD
  have hInt := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht f
  have hIμ : (∫ x, f x ∂(μ : Measure ℝ))=
      ∫ x, scalarCDFOverlap β α (max x r) ∂(μ : Measure ℝ) :=
    integral_congr_ae ((supported_probability_ae μ hμ).mono hf)
  rw [hIμ] at hInt
  let a (n : ℕ) := ∫ x, scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max x r)
    ∂quantileAtomLaw (K n) (Q n)
  let b (n : ℕ) := ∫ x, f x ∂quantileAtomLaw (K n) (Q n)
  have hdiff : Tendsto (fun n => a n-b n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (ε/2) (by positivity)] with n hn
    have H := norm_integral_le_of_norm_le_const (μ:=quantileAtomLaw (K n) (Q n))
      (f:=fun x => scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max x r)-f x) (C:=ε/2) (by
        filter_upwards [supported_probability_ae (quantileProbability (K n) (Q n))
          (quantileAtomLaw_supported (K n) (Q n) (hQ n).2)] with x hx
        rw [hf x hx,Real.norm_eq_abs,abs_sub_comm]
        exact (hn (max x r) ⟨hx.1.trans (le_max_left _ _),max_le hx.2 hr.2⟩).le)
    rw [integral_sub (quantileAtomLaw_integrable _ _ _) (quantileAtomLaw_integrable _ _ _)] at H
    have := quantileAtomLaw_probability (K n) (Q n)
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] at H
    rw [Real.dist_eq,sub_zero]
    exact H.trans_lt (by linarith)
  have H := hdiff.add hInt
  simp only [zero_add] at H
  have HE (n : ℕ) : a n-b n+∫ x, f x ∂(quantileProbability (K n) (Q n) : Measure ℝ)=
      (1/(K n+1:ℕ))*∑ j, scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max (Q n j) r) := by
    change a n-b n+b n=_
    rw [sub_add_cancel]
    exact quantileAtomLaw_integral _ _ _
  simpa only [HE] using H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_SusceptibilityConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_tendsto (β : ℝ) {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (hn : ∀ n z, αn n z∈Icc (0:ℝ) 1) (hnm : ∀ n, Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarCDFSusceptibilityAverage β (αn n) r) atTop
      (𝓝 (scalarCDFSusceptibilityAverage β α r)) := by
  let t := Real.toNNReal r
  let s := Real.toNNReal (1-r)
  have ht : (t:ℝ)=r := Real.coe_toNNReal r hr.1
  have hs : (s:ℝ)=1-r := Real.coe_toNNReal (1-r) (sub_nonneg.mpr hr.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hr.2
  have hs1 : s≤1 := by rw [← NNReal.coe_le_coe,hs,NNReal.coe_one]; linarith [hr.1]
  have hrs : r+s≤1 := by rw [hs]; linarith
  let f := scalarCDFValue β α r s
  let g := scalarCDFHessian β α r s
  let fn := fun n => scalarCDFValue β (αn n) r s
  let gn := fun n => scalarCDFHessian β (αn n) r s
  have hfU : TendstoUniformly fn f atTop :=
    scalarCDFValue_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hgU : TendstoUniformly gn g atTop :=
    scalarCDFHessian_tendstoUniformly_interval β hα hαm hn hnm hD r s hs1 hr.1 hrs
  have hc := scalarCDFAverage_tendsto_cdf_lipschitz β hα hαm hn hnm hD
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    0 t ht1 le_rfl (by simpa only [zero_add,ht] using hr.2) 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := Real.log (1+ε/8)/2
  have hd : 0<δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have he : Real.exp (2*δ)-1=ε/8 := by
    rw [show 2*δ=Real.log (1+ε/8) by dsimp [δ]; ring,
      Real.exp_log (by linarith : 0<1+ε/8)]
    ring
  filter_upwards [(Metric.tendstoUniformly_iff.mp hfU) δ hd,
    (Metric.tendstoUniformly_iff.mp hgU) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hc) (ε/4) (by positivity)] with n hf hg hcn
  have hfg (z) : |fn n z-f z|≤δ := by simpa only [Real.dist_eq,abs_sub_comm] using (hf z).le
  have hgg (z) : |gn n z-g z|≤ε/4 := by simpa only [Real.dist_eq,abs_sub_comm] using (hg z).le
  have Ht := scalarCDFAverage_terminal_stability_lipschitz β (hn n) (hnm n)
    (scalarCDFValue_regular β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_regular β hα hαm r s hs1)
    (scalarCDFValue_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFValue_lipschitz β hα hαm r s hs1)
    (scalarCDFHessian_lipschitz β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_lipschitz β hα hαm r s hs1)
    (B:=1) (scalarCDFHessian_abs_le_one β (hn n) (hnm n) r s hs1)
    (scalarCDFHessian_abs_le_one β hα hαm r s hs1)
    hd.le hfg hgg 0 t ht1 0
  rw [he,NNReal.coe_one] at Ht
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β (αn n) 0 t f g 0|≤_ at Ht
  change dist (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)<ε/4 at hcn
  rw [Real.dist_eq] at hcn
  rw [Real.dist_eq]
  change |scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0-
    scalarCDFAverage β α 0 t f g 0|<ε
  have H := abs_sub_le (scalarCDFAverage β (αn n) 0 t (fn n) (gn n) 0)
    (scalarCDFAverage β (αn n) 0 t f g 0) (scalarCDFAverage β α 0 t f g 0)
  linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ClippedPartitionSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_eq_clipped_partition (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hαm : Monotone α)
    (n : ℕ) (q : Fin (n+1) → ℝ) (hq : Monotone q) (hq0 : q 0=0) (hq1 : q (Fin.last n)=1)
    (m : Fin n → ℝ) (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmm : Monotone m)
    (hmodel : ∀ i : Fin n, ∀ z∈Ico (q i.castSucc) (q i.succ), α z=m i)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    scalarCDFSusceptibilityAverage β α r=
      1-∑ j, hierarchyAtom n m 1 j*scalarCDFOverlap β α (max (q j) r) := by
  let p := fun i => min (q i) r
  let s := fun i => max (q i) r
  have hp : Monotone p := fun i j hij => min_le_min_right _ (hq hij)
  have hs : Monotone s := fun i j hij => max_le_max_right _ (hq hij)
  have hp0 : p 0=0 := by simp only [p,hq0,min_eq_left hr.1]
  have hs1 : s (Fin.last n)=1 := by simp only [s,hq1,max_eq_left hr.2]
  have hp1 : p (Fin.last n)=r := by simp only [p,hq1,min_eq_right hr.2]
  have hs0 : s 0=r := by simp only [s,hq0,max_eq_right hr.1]
  have hmp (i : Fin n) (z : ℝ) (hz : z∈Ico (p i.castSucc) (p i.succ)) : α z=m i := by
    apply hmodel i z
    change min (q i.castSucc) r ≤ z ∧ z < min (q i.succ) r at hz
    have hzr : z  <  r := (lt_min_iff.mp hz.2).2
    have hzq : z < q i.succ := (lt_min_iff.mp hz.2).1
    have hl : q i.castSucc ≤ z := by
      by_cases h : q i.castSucc ≤  r
      · simpa only [min_eq_left h] using hz.1
      · rw [min_eq_right (le_of_not_ge h)] at hz
        linarith [hz.1]
    exact ⟨hl,hzq⟩
  have hms (i : Fin n) (z : ℝ) (hz : z∈Ico (s i.castSucc) (s i.succ)) : α z=m i := by
    apply hmodel i z
    change max (q i.castSucc) r ≤ z ∧ z < max (q i.succ) r at hz
    have hzr : r ≤ z := (max_le_iff.mp hz.1).2
    have hl : q i.castSucc ≤ z := (max_le_iff.mp hz.1).1
    have hu : z < q i.succ := by
      rcases lt_max_iff.mp hz.2 with h|h
      · exact h
      · linarith
    exact ⟨hl,hu⟩
  have H := scalarCDFSusceptibilityAverage_eq_partition β hα hαm n n p s hp hs hp0 hs1
    (hp1.trans hs0.symm) m m hm hm hmm hmp hms
  rwa [hs0] at H

theorem scalarCDFSusceptibilityAverage_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    scalarCDFSusceptibilityAverage β (quantileCDF k Q) r=
      1-(1/(k+1:ℕ))*∑ j, scalarCDFOverlap β (quantileCDF k Q) (max (Q j) r) := by
  let q := Fin.snoc (α := fun _ => ℝ) (Fin.cons (α := fun _ => ℝ) 0 Q) (1:ℝ)
  let m := Fin.snoc (α := fun _ => ℝ) (quantileMass k) (1:ℝ)
  have hq : Monotone q := monotone_snoc_one _
    (monotone_cons_zero_quantiles Q hQ.1 (hQ.2 0).1) (by simpa using (hQ.2 (Fin.last k)).2)
  have hq0 : q 0=0 := by simp [q]
  have hq1 : q (Fin.last (k+2))=1 := by simp [q]
  have hm (i : Fin (k+2)) : m i ∈ Icc (0:ℝ) 1 := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [m]
    · simpa [m] using quantileMass_bounds k i
  have hmm : Monotone m := monotone_snoc_one _ (monotone_quantileMass k)
    (quantileMass_bounds k (Fin.last k)).2
  have hmodel (i : Fin (k+2)) (z : ℝ) (hz : z ∈ Ico (q i.castSucc) (q i.succ)) :
      quantileCDF k Q z=m i := by
    revert hz
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hz
      simp only [m,Fin.snoc_last]
      apply quantileCDF_of_last_le Q hQ.1
      simpa [q] using hz.1
    · intro hz
      simpa [m] using quantileCDF_on_interval Q hQ.1 i z (by
        simpa only [q,← Fin.castSucc_succ,Fin.snoc_castSucc,Fin.cons_succ] using hz)
  rw [scalarCDFSusceptibilityAverage_eq_clipped_partition β (quantileCDF_bounds k Q)
    (quantileCDF_monotone k Q) (k+2) q hq hq0 hq1 m hm hmm hmodel hr]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hA (j : Fin (k+2)) : hierarchyAtom (k+2) m 1 j.castSucc=
      hierarchyAtom (k+1) (quantileMass k) 1 j := by
    rw [hierarchyAtom,Fin.lastCases_castSucc]
    simp only [m,Fin.snoc_castSucc,Fin.snoc_last]
  have hlast : hierarchyAtom (k+2) m 1 (Fin.last (k+2))=0 := by
    rw [hierarchyAtom,Fin.lastCases_last]
    simp only [m,Fin.snoc_last,sub_self]
  simp only [hA,hlast,zero_mul,add_zero]
  rw [Fin.sum_univ_succ,hierarchyAtom_zero_coordinate]
  simp only [quantileMass,Fin.val_zero,Nat.cast_zero,zero_div,zero_mul,zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hierarchyAtom_quantile_succ]
  simp only [q,Fin.snoc_castSucc,Fin.cons_succ]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_FullTimeSusceptibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_weak_quantile_limit (β : ℝ) (K : ℕ → ℕ)
    (Q : (n : ℕ) → Fin (K n+1) → ℝ) (hQ : ∀ n, Q n∈admissibleQuantiles (K n))
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (ht : Tendsto (fun n => quantileProbability (K n) (Q n)) atTop (𝓝 μ))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
      1-∫ x, scalarCDFOverlap β (cdf (μ : Measure ℝ)) (max x r) ∂(μ : Measure ℝ) := by
  have hcdf (n : ℕ) : cdf (quantileProbability (K n) (Q n) : Measure ℝ)=
      quantileCDF (K n) (Q n) := by ext x; exact cdf_eq_real _ _
  have hD : Tendsto (fun n => cdfDistance (quantileCDF (K n) (Q n))
      (cdf (μ : Measure ℝ))) atTop (𝓝 0) := by
    simpa only [cdfDistance,hcdf] using cdf_L1_tendsto_of_weak ht
  have HU := scalarCDFSusceptibilityAverage_tendsto β
    (fun x => ⟨cdf_nonneg (μ : Measure ℝ) x,cdf_le_one (μ : Measure ℝ) x⟩)
    (cdf (μ : Measure ℝ)).mono (fun n => quantileCDF_bounds (K n) (Q n))
    (fun n => quantileCDF_monotone (K n) (Q n)) hD hr
  have HE (n : ℕ) : scalarCDFSusceptibilityAverage β (quantileCDF (K n) (Q n)) r=
      1-(1/(K n+1:ℕ))*∑ j, scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max (Q n j) r) :=
    scalarCDFSusceptibilityAverage_quantile β (Q n) (hQ n) hr
  simp_rw [HE] at HU
  exact tendsto_nhds_unique HU
    ((quantileMaxOverlap_integral_tendsto β K Q hQ μ hμ hr ht).const_sub 1)

theorem exists_scalarCDFParisi_minimizer_full_susceptibility (β : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      ∀ r∈Icc (0:ℝ) 1,
      scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
        1-∫ x, scalarCDFOverlap β (cdf (μ : Measure ℝ)) (max x r) ∂(μ : Measure ℝ) := by
  obtain ⟨K,Q,hQ,_,_,hv⟩ := exists_stationary_quantile_sequence β
  obtain ⟨μ,hμ,φ,hφ,ht⟩ := quantileProbability_weak_subsequence K Q (fun n => (hQ n).2)
  have hcdf (n : ℕ) : cdf (quantileProbability (K (φ n)) (Q (φ n)) : Measure ℝ)=
      quantileCDF (K (φ n)) (Q (φ n)) := by ext x; exact cdf_eq_real _ _
  have hD : Tendsto (fun n => cdfDistance (quantileCDF (K (φ n)) (Q (φ n)))
      (cdf (μ : Measure ℝ))) atTop (𝓝 0) := by
    simpa only [cdfDistance,hcdf] using cdf_L1_tendsto_of_weak ht
  have HP := scalarCDFParisi_tendsto_of_L1 β
    (fun x => ⟨cdf_nonneg (μ : Measure ℝ) x,cdf_le_one (μ : Measure ℝ) x⟩)
    (cdf (μ : Measure ℝ)).mono
    (fun n => quantileCDF_bounds (K (φ n)) (Q (φ n)))
    (fun n => quantileCDF_monotone (K (φ n)) (Q (φ n))) hD
  simp_rw [scalarCDFParisi_quantile β _ (hQ _)] at HP
  exact ⟨μ,hμ,tendsto_nhds_unique HP (hv.comp hφ.tendsto_atTop),fun r hr =>
    scalarCDFSusceptibilityAverage_weak_quantile_limit β (fun n => K (φ n)) (fun n => Q (φ n))
      (fun n => hQ (φ n)) μ hμ ht hr⟩

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CommonMinimizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α) :
    scalarCDFSusceptibilityAverage β α 0=scalarCDFHessian β α 0 1 0 := by
  have HE := scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β hα hmono 0 1 le_rfl)
    (scalarCDFValue_lipschitz β hα hmono 0 1 le_rfl)
    (scalarCDFHessian_lipschitz β hα hmono 0 1 le_rfl)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hmono 0 1 le_rfl)
    β hα hmono [] (by simp) 0 0 (by norm_num) rfl trivial 0
  simpa only [scalarCDFSusceptibilityAverage,sub_zero,Real.toNNReal_one,Real.toNNReal_zero,
    scalarTimeChainAverage,List.length_nil,scalarHierarchyAverage] using HE

theorem exists_scalarCDFParisi_minimizer_locking_data_oai {β : ℝ} (hβ : β≠0) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      (0:ℝ)∈(μ : Measure ℝ).support ∧
      scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
        (∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) ∧
      |β| *(∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) ≤ 1 ∧
      (∀ h : ℝ, 0<h → (∫ s in h..1, cdf (μ : Measure ℝ) s)<
        (∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s)) ∧
      (∀ r∈Icc (0:ℝ) 1, scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
        (∫ s in r..1,cdf (μ : Measure ℝ) s)+cdf (μ : Measure ℝ) r*
          (r-scalarCDFOverlap β (cdf (μ : Measure ℝ)) r)) := by
  obtain ⟨μ,hμ,hm,hs⟩ := exists_scalarCDFParisi_minimizer_full_susceptibility β
  have h0 := scalarCDFParisi_zero_mem_support hβ μ hμ hm
  have hA (r : ℝ) (hr : r∈Icc (0:ℝ) 1) := scalarCDFParisi_susceptibility_area hβ μ hμ hm hs hr
  have ha (z : ℝ) : cdf (μ : Measure ℝ) z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have hArea : scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
      (∫ s in (0:ℝ)..1,cdf (μ : Measure ℝ) s) := by
    have H := hA 0 ⟨le_rfl,zero_le_one⟩
    simpa only [scalarCDFSusceptibilityAverage_zero β ha (cdf (μ : Measure ℝ)).mono,
      scalarCDFOverlap_zero β ha (cdf (μ : Measure ℝ)).mono,sub_self,mul_zero,add_zero] using H
  refine ⟨μ,hμ,hm,h0,hArea,?_,fun h hh => cdf_area_strict μ h0 hh,fun r hr => hA r hr⟩
  have HS := scalarCDFParisi_origin_stability hβ μ hμ hm
  rw [hArea] at HS
  have HB := (sq_le_one_iff_abs_le_one (β*(∫ s in (0:ℝ)..1,cdf (μ : Measure ℝ) s))).mp
    (by simpa only [mul_pow] using HS)
  have hnonneg : 0≤∫ s in (0:ℝ)..1,cdf (μ : Measure ℝ) s :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => cdf_nonneg _ s)
  simpa only [abs_mul,abs_of_nonneg hnonneg] using HB

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.exists_scalarCDFParisi_minimizer_locking_data_oai := @OAI.SK.Analytic.exists_scalarCDFParisi_minimizer_locking_data_oai

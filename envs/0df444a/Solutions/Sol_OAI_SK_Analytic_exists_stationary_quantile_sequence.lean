-- Prove2me | solution 1 for OAI.SK.Analytic.exists_stationary_quantile_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:06:17.239479+00:00
-- url     : https://prove2.me/submissions/46a28b73-9107-40bb-8729-fb971f08ffd6

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Theorems.Thm_OAI_SK_Analytic_skBlockPressure_hasDerivAt

section
-- module Solutions.OAIQ036_SK.SKBarriers_Calculus_CoordinateGaussianLaw
attribute [-instance] _root_.OAI.SK.Analytic.fiberGaussian_isGaussian _root_.OAI.SK.disorderPairLaw_probability
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem coordinateArray_continuous (n : ℕ) : Continuous (coordinateArray n) :=
  continuous_pi (fun i => (coordinateProjection n i).continuous)

theorem coordinateArray_measurePreserving (n : ℕ) (x : ℝ) :
    MeasurePreserving (coordinateArray n) (fiberGaussian n x)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  induction n with
  | zero =>
    refine ⟨(coordinateArray_continuous 0).measurable,?_⟩
    rw [fiberGaussian,Measure.map_dirac' (coordinateArray_continuous 0).measurable,
      Measure.pi_of_empty _ (coordinateArray 0 x)]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) (Fin.last n)
    have he : MeasurePreserving e (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1))
        ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1))) :=
      measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) (Fin.last n)
    have hprod := (Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)) (ν := gaussianReal 0 1)).comp (ih.prod (MeasurePreserving.id (gaussianReal 0 1)))
    have H := he.symm.comp hprod
    convert H using 1 <;> try rfl
    funext z
    apply e.injective
    rw [Function.comp_apply,e.apply_symm_apply]
    apply Prod.ext
    · simp [e,coordinateArray,coordinateProjection]
    · funext i
      simp [e,coordinateArray,coordinateProjection,Fin.init]

theorem enumeratedDisorder_measurePreserving (N : ℕ) (x : ℝ) :
    MeasurePreserving (enumeratedDisorder N) (fiberGaussian (Fintype.card (Edge N)) x)
      (disorderLaw N) := by
  have H := (measurePreserving_piCongrLeft (fun _ : Edge N => gaussianReal 0 1)
    (Fintype.equivFin (Edge N)).symm).comp (coordinateArray_measurePreserving (Fintype.card (Edge N)) x)
  convert H using 1
  · funext z e
    simp [enumeratedDisorder, coordinateArray, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  · rfl
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyLevels
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

section Translation
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem TranslationInvariant.gaussianStep {f : E × ℝ → ℝ} {u : E}
    (hi : TranslationInvariant f (u,0)) (m : ℝ) : TranslationInvariant (gaussianStep m f) u := by
  intro z t
  have he (y : ℝ) : f (z+t • u,y) = f (z,y) := by
    simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hi (z,y) t
  unfold SK.Analytic.gaussianStep positiveGaussianLogStep
  simp only [he]

theorem affineLogPartition_translation {S : Type} [Fintype S]
    (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (u : E) (hu : ∀ s, L s u = 0) :
    TranslationInvariant (affineLogPartition c L) u := by
  intro z t
  simp only [affineLogPartition,map_add,map_smul,hu,smul_eq_mul,mul_zero,add_zero]

end Translation

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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeBlockLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem gaussianStep_append (a b : ℕ) (p : ℝ) (f : ParameterSpace (a+(b+1)) → ℝ) :
    gaussianStep p (fun z => f (parameterAppend a (b+1) z)) =
      fun z => gaussianStep p f (parameterAppend a b z) := by
  rfl

theorem hierarchyPressure_split (a b : ℕ) (m : Fin (a+b) → ℝ)
    (f : ParameterSpace (a+b) → ℝ) :
    hierarchyPressure (a+b) m f = hierarchyPressure a (fun i => m (Fin.castAdd b i))
      (cascadePressure b (fun i => m (Fin.natAdd a i)) (fun z => f (parameterAppend a b z))) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change hierarchyPressure ((a+b)+1) m f = _
    rw [hierarchyPressure,ih,cascadePressure,gaussianStep_append]
    rfl

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianStepAlgebra
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
section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussianStep_sum_independent {I : Type} [Fintype I] [DecidableEq I]
    (f : I → E × ℝ → ℝ) (hf : ∀ i, BoundedDerivs (f i)) (j : I)
    (hi : ∀ i, i ≠ j → TranslationInvariant (f i) (0,1)) (m : ℝ) :
    gaussianStep m (fun z => ∑ i, f i z) = fun x => ∑ i, gaussianStep m (f i) x := by
  have he (i : I) (h : i ≠ j) (x : E) (y : ℝ) : f i (x,y) = f i (x,0) := by
    simpa using hi i h (x,0) y
  have hex : (fun z => ∑ i, f i z) = fun z => f j z+∑ i ∈ Finset.univ.erase j, f i (z.1,0) := by
    funext z
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    apply Finset.sum_congr rfl
    intro i h
    exact he i (Finset.mem_erase.mp h).1 z.1 z.2
  rw [hex,gaussianStep_add_prefix (hf j) (fun x => ∑ i ∈ Finset.univ.erase j, f i (x,0)) m]
  funext x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  congr 1
  apply Finset.sum_congr rfl
  intro i h
  have H : f i = fun z => f i (z.1,0) := funext (fun z => he i (Finset.mem_erase.mp h).1 z.1 z.2)
  rw [H,gaussianStep_prefix (fun y => f i (y,0)) m]
end Generic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_zero (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPressure n (fun _ => 0) f x = ∫ z, f z ∂fiberGaussian n x := by
  induction n with
  | zero => simp [hierarchyPressure,fiberGaussian]
  | succ n ih =>
    rw [hierarchyPressure,ih _ (hf.gaussianStep 0),fiberGaussian,
      integral_prod _ (hf.hasExpGrowth.integrable_fiberGaussian (n+1) hf.1.continuous x)]
    simp only [gaussianStep,ite_true]

theorem hierarchyPressure_sum_independent {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (m : Fin n → ℝ) (owner : Fin n → I)
    (f : I → ParameterSpace n → ℝ) (hf : ∀ i, BoundedDerivs (f i))
    (hi : ∀ t i, i ≠ owner t → TranslationInvariant (f i) (coordinateAxis n t)) :
    hierarchyPressure n m (fun z => ∑ i, f i z) = fun x => ∑ i, hierarchyPressure n m (f i) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hierarchyPressure,gaussianStep_sum_independent f hf (owner (Fin.last n))
      (by simpa only [coordinateAxis_last] using hi (Fin.last n))]
    rw [ih (fun t => m t.castSucc) (fun t => owner t.castSucc)
      (fun i => gaussianStep (m (Fin.last n)) (f i))
      (fun i => (hf i).gaussianStep _) (fun t i h => ?_)]
    · rfl
    · apply TranslationInvariant.gaussianStep
      simpa only [coordinateAxis_castSucc] using hi t.castSucc i h
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BlockStein
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

theorem normalizedDot_sq_le {N : ℕ} (a b : Fin N → ℝ) :
    (normalizedDot a b)^2 ≤ normalizedSquare a*normalizedSquare b := by
  have H := div_le_div_of_nonneg_right
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b) (sq_nonneg (N : ℝ))
  simpa only [normalizedDot,normalizedSquare,div_pow,div_mul_div_comm,← pow_two] using H

theorem abs_normalizedDot_le {N : ℕ} (a b : Fin N → ℝ) :
    |normalizedDot a b| ≤ Real.sqrt (normalizedSquare a)*Real.sqrt (normalizedSquare b) := by
  rw [← Real.sqrt_mul (normalizedSquare_nonneg a)]
  apply Real.le_sqrt_of_sq_le
  simpa only [sq_abs] using normalizedDot_sq_le a b

end SK.Analytic
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section MeanTower
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) (x : ℝ) :
    Integrable (hierarchyMeanSquare n m U c j)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) x) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hierarchyMeanSquare_continuous n m U c hc j) (C := 1) _ x
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds n m U c hc j z).1]
  exact (hierarchyMeanSquare_bounds n m U c hc j z).2

theorem hierarchyMeanOverlap_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : Fin N → S → ℝ)
    (hc : ∀ i s, ‖c i s‖ ≤ 1) (j : Fin (n+1)) :
    hierarchyMeanOverlap n m U c j ∈ Set.Icc (0 : ℝ) 1 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  refine ⟨integral_nonneg (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (1 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono (hierarchyMeanSquare_integrable n m U c hc j 0) (integrable_const 1)
        (fun z => (hierarchyMeanSquare_bounds n m U c hc j z).2)
    _ = 1 := by simp

end MeanTower
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockMassValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

 theorem blockMass_eq_sum (D N k : ℕ) (i : Fin (blockDimension D N k)) :
    blockMass D N k i = ∑ b : Fin (k+1),
      if (blockLevel D N k b).val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0 := by
  unfold blockMass massFromAtoms blockAtom
  calc
    _ = ∑ t : Fin (blockDimension D N k+1), ∑ b : Fin (k+1),
      if blockLevel D N k b = t then
        (if t.val ≤ i.val then ((k+1 : ℕ) : ℝ)⁻¹ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val ≤ i.val <;> simp only [ht,ite_true,ite_false,ite_self,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem blockMass_at_field (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    blockMass D N k (fieldIndex D N k b i) = (b.val : ℝ)/((k+1 : ℕ) : ℝ) := by
  rw [blockMass_eq_sum]
  have hh (c : Fin (k+1)) : (blockLevel D N k c).val ≤ (fieldIndex D N k b i).val ↔ c < b := by
    simp only [blockLevel_val,fieldIndex_val,Fin.lt_def]
    constructor
    · intro h
      by_contra hn
      have hc : b.val ≤ c.val := by omega
      have hc' := Nat.mul_le_mul_right N hc
      nlinarith [i.isLt]
    · intro h
      have hc := Nat.mul_le_mul_right N h
      nlinarith
  simp only [hh]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun c : Fin (k+1) => c < b) = Finset.Iio b := by
    ext c
    simp
  rw [hs]
  simp only [Finset.sum_const,Fin.card_Iio,nsmul_eq_mul,div_eq_mul_inv]
end SK.Analytic

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

theorem continuous_partition {n : ℕ} (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x)))

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_LogPartition
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

theorem continuous_logPartition {n : ℕ} (β : ℝ) :
    Continuous (logPartition (n := n) β) :=
  (continuous_partition β).log (fun J => ne_of_gt (partition_pos β J))

end SK
end
end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_AverageMeanVariance
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fieldIndex_eq_natAdd (D N k : ℕ) (b : Fin (k+1)) (i : Fin N) :
    fieldIndex D N k b i = Fin.natAdd D (finProdFinEquiv (b,i)) := by
  apply Fin.ext
  change D+b.val*N+i.val = D+(i.val+N*b.val)
  ring

@[simp] theorem blockInteraction_field {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (b : Fin (k+1)) (i : Fin N) : blockInteraction (k := k) I (fieldIndex D N k b i) = {i} := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockInteraction,Fin.addCases_right,Equiv.symm_apply_apply]

@[simp] theorem blockCoefficients_field {D N k : ℕ} (a : Fin D → ℝ) (v : Fin (k+1) → ℝ)
    (b : Fin (k+1)) (i : Fin N) : blockCoefficients (N := N) a v (fieldIndex D N k b i) = v b := by
  rw [fieldIndex_eq_natAdd]
  simp only [blockCoefficients,Fin.addCases_right,Equiv.symm_apply_apply]

theorem blockExponent_expansion {D N k : ℕ} (I : Fin D → Finset (Fin N)) (a : Fin D → ℝ)
    (v : Fin (k+1) → ℝ) (s : Config N) (z : ParameterSpace (blockDimension D N k)) :
    blockExponent I a v s z =
      (∑ t : Fin D, a t*spinMonomial s (I t)*coordinateProjection (blockDimension D N k) (Fin.castAdd ((k+1)*N) t) z)+
      ∑ b : Fin (k+1), ∑ i : Fin N, v b*spin (s i)*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) z := by
  unfold blockExponent spinExponent
  rw [coordinateLinear_apply,Fin.sum_univ_add]
  simp only [blockCoefficients,blockInteraction,Fin.addCases_left,Fin.addCases_right]
  congr 1
  rw [← finProdFinEquiv.sum_comp (fun t => v (finProdFinEquiv.symm t).1*
    spinMonomial s {(finProdFinEquiv.symm t).2}*
      coordinateProjection (blockDimension D N k) (Fin.natAdd D t) z)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,spinMonomial,Finset.prod_singleton,
    fieldIndex_eq_natAdd]

end SK.Analytic
namespace SK.Analytic

section MeanVariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem abs_normalizedDot_le_one {N : ℕ} (a b : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) (hb : ∀ i, |b i| ≤ 1) : |normalizedDot a b| ≤ 1 := by
  have h₁ : Real.sqrt (normalizedSquare a) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one a ha)
  have h₂ : Real.sqrt (normalizedSquare b) ≤ 1 := by simpa using Real.sqrt_le_sqrt (normalizedSquare_le_one b hb)
  exact (abs_normalizedDot_le a b).trans (by nlinarith [Real.sqrt_nonneg (normalizedSquare a),Real.sqrt_nonneg (normalizedSquare b)])

end MeanVariance
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_CascadeProbability
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
section CascadeProbability
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {S : Type} [Fintype S] [Nonempty S]

theorem affineGibbs_continuous (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (s : S) :
    Continuous (fun x => affineGibbs c L x s) := by
  exact (Real.continuous_exp.comp (continuous_const.add (L s).continuous)).div
    (continuous_finsetSum _ (fun t _ => Real.continuous_exp.comp (continuous_const.add (L t).continuous)))
    (fun x => (affinePartition_pos c L x).ne')

theorem affineGibbs_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    affineGibbs c L x s ≤ 1 := by
  rw [← affineGibbs_sum c L x]
  exact Finset.single_le_sum (fun t _ => (affineGibbs_pos c L x t).le) (Finset.mem_univ s)

theorem affineGibbs_norm_le_one (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) (s : S) :
    ‖affineGibbs c L x s‖ ≤ 1 := by
  rw [Real.norm_eq_abs,abs_of_pos (affineGibbs_pos c L x s)]
  exact affineGibbs_le_one c L x s

end CascadeProbability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_GaussianSpinTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped MatrixOrder BigOperators
noncomputable section
open scoped BigOperators MatrixOrder
open MeasureTheory ProbabilityTheory Matrix
namespace SK.Analytic
section FiniteCovariance
variable {S I : Type} [Fintype S] [Fintype I]

omit [Fintype I] in
theorem finiteMean_apply (p : S → ℝ) (v : S → I → ℝ) (i : I) :
    finiteMean p v i = ∑ s, p s*v s i := by simp only [finiteMean,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

end FiniteCovariance
end SK.Analytic

end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
namespace SK.Analytic
open Matrix
section ReplicaOverlap
variable {S I : Type} [Fintype S] [Fintype I]

theorem finiteReplicaMoment_dot (p : S → ℝ) (v : S → I → ℝ) :
    finiteReplicaMoment p (fun s t => v s ⬝ᵥ v t) = finiteMean p v ⬝ᵥ finiteMean p v := by
  simp only [finiteMean,finiteReplicaMoment,sum_dotProduct,dotProduct_sum,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [dotProduct_comm (v t) (v s)]
  ring

end ReplicaOverlap
end SK.Analytic

end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyMomentLevel_nonneg (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (hg : ∀ z, 0 ≤ g z) (j : Fin (n+1)) (z : ParameterSpace n) :
    0 ≤ hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => exact hg z
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using hg z
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      apply ih
      intro x
      exact integral_nonneg (fun y => hg (x,y))

theorem hierarchyMomentLevel_const (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun _ => a) j = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      rw [gaussianAverage_const_prefix hf _ (fun _ => a),ih _ _ (hf.gaussianStep _)]

theorem hierarchyMomentLevel_const_mul (n : ℕ) (m : Fin n → ℝ) (f g : ParameterSpace n → ℝ)
    (a : ℝ) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => a*g z) j = fun z => a*hierarchyMomentLevel n m f g j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => a*g z) =
          fun z => a*gaussianAverage (m (Fin.last n)) f g z := by
        funext z; exact integral_const_mul a _
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he,ih]

theorem hierarchyMomentLevel_sum {T : Type} [Fintype T] (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f)
    (g : T → ParameterSpace n → ℝ) (hg : ∀ t, Continuous (g t))
    (C : T → ℝ) (hC : ∀ t, 0 ≤ C t) (hb : ∀ t z, ‖g t z‖ ≤ C t) (j : Fin (n+1)) :
    hierarchyMomentLevel n m f (fun z => ∑ t, g t z) j =
      fun z => ∑ t, hierarchyMomentLevel n m f (g t) j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · have he : gaussianAverage (m (Fin.last n)) f (fun z => ∑ t, g t z) =
          fun z => ∑ t, gaussianAverage (m (Fin.last n)) f (g t) z := by
        funext z
        let := gaussianStepLaw_probability hf (m (Fin.last n)) z
        apply integral_finsetSum
        intro t _
        exact Integrable.of_bound ((hg t).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          (C t) (ae_of_all _ (fun y => hb t (z,y)))
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,he]
      rw [ih _ _ (hf.gaussianStep _) _
        (fun t => gaussianAverage_continuous hf _ (hg t) (hC t) (hb t))
        (fun t z => gaussianAverage_norm_le hf _ (hb t) z) j]

section Probability
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchySpinWeight_regular (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (s : S) :
    Continuous (fun z => hierarchySpinWeight n m U j z s) ∧
      ∀ z, ‖hierarchySpinWeight n m U j z s‖ ≤ 1 :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (affineGibbs_continuous (fun _ => 0) U s) (by norm_num) (fun z => affineGibbs_norm_le_one (fun _ => 0) U z s) j

theorem hierarchySpinWeight_nonneg (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) (s : S) : 0 ≤ hierarchySpinWeight n m U j z s :=
  hierarchyMomentLevel_nonneg n m _ _ (fun z => le_of_lt (affineGibbs_pos (fun _ => 0) U z s)) j z

theorem hierarchySpinWeight_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (j : Fin (n+1)) (z : ParameterSpace n) : ∑ s, hierarchySpinWeight n m U j z s = 1 := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => affineGibbs (fun _ => 0) U z s)
    (affineGibbs_continuous (fun _ => 0) U) (fun _ => 1) (fun _ => by norm_num)
    (fun s z => affineGibbs_norm_le_one (fun _ => 0) U z s) j
  have he : (fun z => ∑ s, affineGibbs (fun _ => 0) U z s) = fun _ => 1 :=
    funext (fun z => affineGibbs_sum (fun _ => 0) U z)
  rw [he,hierarchyMomentLevel_const n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U)] at H
  exact (congrFun H z).symm

theorem hierarchySpinMean_eq_sum (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (v : S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchySpinMean n m U v j z = ∑ s, hierarchySpinWeight n m U j z s*v s := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition (fun _ => 0) U)
    (affineLogPartition_boundedDerivs (fun _ => 0) U) (fun s z => v s*affineGibbs (fun _ => 0) U z s)
    (fun s => continuous_const.mul (affineGibbs_continuous (fun _ => 0) U s))
    (fun s => ‖v s‖) (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one (fun _ => 0) U z s) (norm_nonneg _)).trans_eq (mul_one _)) j
  simp_rw [hierarchyMomentLevel_const_mul] at H
  change hierarchyMomentLevel n m (affineLogPartition (fun _ => 0) U)
    (fun z => ∑ s, affineGibbs (fun _ => 0) U z s*v s) j z = _
  simpa only [hierarchySpinWeight,mul_comm] using congrFun H z
end Probability
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinParameterRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section ParameterHierarchy
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem hierarchyPressure_paramRegular (n : ℕ) (m : Fin n → ℝ)
    (f : P × ParameterSpace n → ℝ) (hf : ParamRegular f) :
    ParamRegular (fun z : P × ℝ => hierarchyPressure n m (fun w => f (z.1,w)) z.2) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact ih (fun i => m i.castSucc)
      (gaussianStep (m (Fin.last n)) (fun z : (P × ParameterSpace n) × ℝ =>
        f (z.1.1,(z.1.2,z.2)))) (hf.gaussianStep (m (Fin.last n)))

end ParameterHierarchy

theorem spinPressure_paramRegular {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (m : Fin d → ℝ) :
    ParamRegular (fun z : (Fin d → ℝ) × ℝ =>
      hierarchyPressure d m (affineLogPartition c (spinExponent d z.1 I)) z.2) :=
  hierarchyPressure_paramRegular d m _ (spinTerminal_paramRegular d I c)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaVarianceSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section ReplicaVarianceSplit
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_const (p : S → ℝ) (hp : ∑ s, p s = 1) (c : ℝ) :
    finiteReplicaMoment p (fun _ _ => c) = c := by
  simp only [finiteReplicaMoment,← Finset.mul_sum,← Finset.sum_mul,hp,mul_one,one_mul]

theorem finiteReplicaMoment_add (p : S → ℝ) (g h : S → S → ℝ) :
    finiteReplicaMoment p (fun s t => g s t+h s t) = finiteReplicaMoment p g+finiteReplicaMoment p h := by
  simp only [finiteReplicaMoment,mul_add,Finset.sum_add_distrib]

theorem finiteReplicaMoment_const_mul (p : S → ℝ) (g : S → S → ℝ) (c : ℝ) :
    finiteReplicaMoment p (fun s t => c*g s t) = c*finiteReplicaMoment p g := by
  simp only [finiteReplicaMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

theorem finiteReplicaMoment_sub_square (p : S → ℝ) (hp : ∑ s, p s = 1) (g : S → S → ℝ) (r : ℝ) :
    finiteReplicaMoment p (fun s t => (g s t-r)^2) =
      finiteReplicaMoment p (fun s t => (g s t)^2)-2*r*finiteReplicaMoment p g+r^2 := by
  have he : (fun s t => (g s t-r)^2) = fun s t => (g s t)^2+(-2*r)*g s t+r^2 := by
    funext s t; ring
  rw [he,finiteReplicaMoment_add,finiteReplicaMoment_add,finiteReplicaMoment_const_mul,finiteReplicaMoment_const p hp]
  ring

theorem finiteReplicaMoment_normalizedDot {N : ℕ} (p : S → ℝ) (v : S → Fin N → ℝ) :
    finiteReplicaMoment p (fun s t => normalizedDot (v s) (v t)) = normalizedSquare (finiteMean p v) := by
  have he : (fun s t => normalizedDot (v s) (v t)) = fun s t => (N : ℝ)⁻¹*(v s ⬝ᵥ v t) := by
    funext s t; simp only [normalizedDot,dotProduct,div_eq_mul_inv]; ring
  rw [he,finiteReplicaMoment_const_mul,finiteReplicaMoment_dot]
  simp only [normalizedSquare,dotProduct,pow_two,div_eq_mul_inv,mul_comm]

end ReplicaVarianceSplit
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
section FiniteReplicaBounds
variable {S : Type} [Fintype S]

theorem finiteReplicaMoment_mono (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g h : S → S → ℝ)
    (hgh : ∀ s t, g s t ≤ h s t) : finiteReplicaMoment p g ≤ finiteReplicaMoment p h := by
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro t _
  exact mul_le_mul_of_nonneg_left (hgh s t) (mul_nonneg (hp s) (hp t))

theorem finiteReplicaMoment_nonneg (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (g : S → S → ℝ)
    (hg : ∀ s t, 0 ≤ g s t) : 0 ≤ finiteReplicaMoment p g :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => mul_nonneg (mul_nonneg (hp s) (hp t)) (hg s t)

theorem finiteReplicaMoment_le_const (p : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hs : ∑ s, p s = 1)
    (g : S → S → ℝ) (C : ℝ) (hg : ∀ s t, g s t ≤ C) : finiteReplicaMoment p g ≤ C := by
  exact (finiteReplicaMoment_mono p hp g (fun _ _ => C) hg).trans_eq (finiteReplicaMoment_const p hs C)

theorem finiteReplicaMoment_continuous {Ω : Type} [TopologicalSpace Ω]
    (P : Ω → S → ℝ) (hP : ∀ s, Continuous (fun z => P z s)) (g : S → S → ℝ) :
    Continuous (fun z => finiteReplicaMoment (P z) g) := by
  exact continuous_finsetSum _ (fun s _ => continuous_finsetSum _ (fun t _ => ((hP s).mul (hP t)).mul continuous_const))
end FiniteReplicaBounds

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section HierarchyReplica
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyMeanSquare_eq_finiteMean {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMeanSquare n m U (fun i s => v s i) j z = normalizedSquare (finiteMean (hierarchySpinWeight n m U j z) v) := by
  simp only [hierarchyMeanSquare,hierarchySpinMean_eq_sum]
  congr 1
  funext i
  exact (finiteMean_apply _ _ i).symm

theorem hierarchyOverlap_integrand_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
    let Q := finiteReplicaMoment (hierarchySpinWeight n m U j z) (fun s t => (normalizedDot (v s) (v t)-r)^2)
    0 ≤ Q ∧ Q ≤ 4 := by
  dsimp only
  refine ⟨finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _),?_⟩
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have hdot := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have hr := hierarchyMeanOverlap_bounds n m U (fun i s => v s i)
    (fun i s => by simpa only [Real.norm_eq_abs] using hv s i) j
  have ha : |normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j| ≤ 2 := by
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hr.1]; linarith [hr.2])
  have hb := abs_nonneg (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)
  nlinarith [sq_abs (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)]

theorem hierarchyOverlapError_bounds {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1) (j : Fin (n+1)) :
    0 ≤ hierarchyOverlapError n m U v j ∧ hierarchyOverlapError n m U v j ≤ 4 := by
  let f := affineLogPartition (fun _ => 0) U
  let := hierarchyPathLaw_probability n m f (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hc := finiteReplicaMoment_continuous (hierarchySpinWeight n m U j)
    (fun s => (hierarchySpinWeight_regular n m U j s).1)
    (fun s t => (normalizedDot (v s) (v t)-hierarchyMeanOverlap n m U (fun i s => v s i) j)^2)
  have hi := Integrable.of_bound (μ := hierarchyPathLaw n m f 0) hc.aestronglyMeasurable 4
    (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyOverlap_integrand_bounds n m U v hv j z).1]
      exact (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
  refine ⟨integral_nonneg (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).1),?_⟩
  calc
    _ ≤ ∫ _ : ParameterSpace n, (4 : ℝ) ∂hierarchyPathLaw n m f 0 :=
      integral_mono hi (integrable_const 4) (fun z => (hierarchyOverlap_integrand_bounds n m U v hv j z).2)
    _ = 4 := by simp
end HierarchyReplica
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyReplicaSecond
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SecondMoment
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyReplicaSecond_integrable {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) : Integrable (fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t))^2))
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (finiteReplicaMoment_continuous _ (fun s => (hierarchySpinWeight_regular n m U j s).1) _) (C := 1) _ 0
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (finiteReplicaMoment_nonneg _ (hierarchySpinWeight_nonneg n m U j z) _ (fun _ _ => sq_nonneg _))]
  apply finiteReplicaMoment_le_const _ (hierarchySpinWeight_nonneg n m U j z) (hierarchySpinWeight_sum n m U j z)
  intro s t
  have H := abs_normalizedDot_le_one (v s) (v t) (hv s) (hv t)
  have H0 := abs_nonneg (normalizedDot (v s) (v t))
  nlinarith [sq_abs (normalizedDot (v s) (v t))]

theorem hierarchyOverlapError_eq_second_sub_sq {N : ℕ} (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (v : S → Fin N → ℝ) (hv : ∀ s i, |v s i| ≤ 1)
    (j : Fin (n+1)) : hierarchyOverlapError n m U v j = hierarchyReplicaSecond n m U v j -
      (hierarchyMeanOverlap n m U (fun i s => v s i) j)^2 := by
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  let r := hierarchyMeanOverlap n m U (fun i s => v s i) j
  have hs := hierarchyReplicaSecond_integrable n m U v hv j
  have hm := hierarchyMeanSquare_integrable n m U (fun i s => v s i)
    (fun i s => by simpa only [Real.norm_eq_abs] using hv s i) j 0
  have he (z : ParameterSpace n) : finiteReplicaMoment (hierarchySpinWeight n m U j z)
      (fun s t => (normalizedDot (v s) (v t)-r)^2) =
      finiteReplicaMoment (hierarchySpinWeight n m U j z) (fun s t => (normalizedDot (v s) (v t))^2)-
        2*r*hierarchyMeanSquare n m U (fun i s => v s i) j z+r^2 := by
    rw [finiteReplicaMoment_sub_square _ (hierarchySpinWeight_sum n m U j z),
      finiteReplicaMoment_normalizedDot,← hierarchyMeanSquare_eq_finiteMean]
  change (∫ z, finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t)-r)^2) ∂μ) = hierarchyReplicaSecond n m U v j-r^2
  simp_rw [he]
  rw [integral_add (f := fun z => finiteReplicaMoment (hierarchySpinWeight n m U j z)
    (fun s t => (normalizedDot (v s) (v t))^2)-2*r*hierarchyMeanSquare n m U (fun i s => v s i) j z)
    (g := fun _ => r^2) (hs.sub (hm.const_mul (2*r))) (integrable_const (r^2)),
    integral_sub hs (hm.const_mul (2*r)),integral_const_mul]
  have hc : (∫ _ : ParameterSpace n, r^2 ∂μ) = r^2 := by simp [μ]
  rw [hc]
  change hierarchyReplicaSecond n m U v j-2*r*r+r^2 = hierarchyReplicaSecond n m U v j-r^2
  ring
end SecondMoment
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKBlockCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem spinMonomial_skInteraction (N : ℕ) (i : Fin (Fintype.card (Edge N))) (s : Config N) :
    spinMonomial s (skInteraction N i) =
      spin (s ((Fintype.equivFin (Edge N)).symm i).val.1)*
        spin (s ((Fintype.equivFin (Edge N)).symm i).val.2) := by
  exact Finset.prod_pair (ne_of_lt (((Fintype.equivFin (Edge N)).symm i).property))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_ZeroFieldEndpoint
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
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cascadePressure_root (b : ℕ) (m : Fin b → ℝ) (g : E → ℝ) :
    cascadePressure b m (fun z => g (cascadeRoot (E := E) b z)) = g := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change cascadePressure b _ (gaussianStep _ (fun z => g (cascadeRoot (E := E) b z.1))) = g
    rw [gaussianStep_prefix (fun z => g (cascadeRoot (E := E) b z)) (m (Fin.last b)),ih]
end Generic

theorem coordinateProjection_append_prefix (a b : ℕ) (i : Fin a)
    (z : CascadeSpace (ParameterSpace a) b) :
    coordinateProjection (a+b) (Fin.castAdd b i) (parameterAppend a b z) =
      coordinateProjection a i (cascadeRoot (E := ParameterSpace a) b z) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change coordinateProjection ((a+b)+1) (Fin.castSucc (Fin.castAdd b i))
      (parameterAppend a b z.1,z.2) = _
    rw [coordinateProjection_castSucc,ih]
    rfl

theorem blockExponent_zeroFields_append {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (s : Config N) (z : CascadeSpace (ParameterSpace D) ((k+1)*N)) :
    blockExponent I a (fun _ : Fin (k+1) => 0) s (parameterAppend D ((k+1)*N) z) =
      spinExponent D a I s (cascadeRoot (E := ParameterSpace D) ((k+1)*N) z) := by
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,add_zero,coordinateProjection_append_prefix,
    spinExponent,coordinateLinear_apply]

theorem blockMass_at_disorder (D N k : ℕ) (i : Fin D) :
    blockMass D N k (Fin.castAdd ((k+1)*N) i) = 0 := by
  rw [blockMass_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  simp only [blockLevel_val,Fin.val_castAdd]
  omega

theorem skBlockRoot_zero_fields (N k : ℕ) (β : ℝ) :
    skBlockRoot N k β (fun _ => 0) =
      ∫ z, affineLogPartition (fun _ : Config N => 0)
        (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N)) z
        ∂fiberGaussian (Fintype.card (Edge N)) 0 := by
  unfold skBlockRoot
  rw [hierarchyPressure_split]
  have he : (fun z => affineLogPartition (fun _ : Config N => 0)
      (blockExponent (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) (fun _ : Fin (k+1) => 0))
        (parameterAppend (Fintype.card (Edge N)) ((k+1)*N) z)) =
      fun z => affineLogPartition (fun _ : Config N => 0)
        (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N))
          (cascadeRoot (E := ParameterSpace (Fintype.card (Edge N))) ((k+1)*N) z) := by
    funext z
    simp only [affineLogPartition,blockExponent_zeroFields_append]
  rw [he,cascadePressure_root]
  simp only [blockMass_at_disorder]
  apply hierarchyPressure_zero
  exact affineLogPartition_boundedDerivs _ _
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_QuenchedEndpoint
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinExponent_sk_eq (N : ℕ) (β : ℝ) (s : Config N)
    (z : ParameterSpace (Fintype.card (Edge N))) :
    spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N) s z =
      β*hamiltonian (enumeratedDisorder N z) s := by
  simp only [spinExponent,coordinateLinear_apply,spinMonomial_skInteraction,hamiltonian,
    enumeratedDisorder]
  rw [← (Fintype.equivFin (Edge N)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  simp only [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem affineLogPartition_sk_eq (N : ℕ) (β : ℝ)
    (z : ParameterSpace (Fintype.card (Edge N))) :
    affineLogPartition (fun _ : Config N => 0)
      (spinExponent (Fintype.card (Edge N)) (fun _ => β/Real.sqrt (N:ℝ)) (skInteraction N)) z =
      logPartition β (enumeratedDisorder N z) := by
  simp only [affineLogPartition,spinExponent_sk_eq,zero_add,logPartition,partition]

theorem skBlockRoot_zero_fields_eq (N k : ℕ) (β : ℝ) :
    skBlockRoot N k β (fun _ => 0) = ∫ J, logPartition β J ∂disorderLaw N := by
  rw [skBlockRoot_zero_fields]
  simp only [affineLogPartition_sk_eq]
  have H := enumeratedDisorder_measurePreserving N 0
  rw [← H.map_eq,integral_map H.measurable.aemeasurable (continuous_logPartition β).aestronglyMeasurable]
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockAdaptiveOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem blockCoefficients_contDiff {D N k : ℕ} (a : Fin D → ℝ) (β : ℝ) :
    ContDiff ℝ 2 (fun p : ℝ × (Fin (k+1) → ℝ) =>
      blockCoefficients (N := N) (fun i => p.1*a i) (fun b => β*p.2 b)) := by
  apply contDiff_pi.mpr
  intro t
  refine Fin.addCases (fun i => ?_) (fun i => ?_) t
  · simp only [blockCoefficients,Fin.addCases_left]
    exact contDiff_fst.mul contDiff_const
  · simp only [blockCoefficients,Fin.addCases_right]
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ _).comp contDiff_snd)

theorem blockAdaptiveOverlap_contDiff {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (a : Fin D → ℝ) (β : ℝ) : ContDiff ℝ 2 (blockAdaptiveOverlap (k := k) I a β) := by
  apply contDiff_pi.mpr
  intro j
  exact (spinHierarchyOverlap_contDiff (blockDimension D N k) (blockMass D N k)
    (blockInteraction I) (fun i s => spin (s i)) (fun i s => by cases s i <;> norm_num [spin])
    (blockLevel D N k j)).comp (blockCoefficients_contDiff a β)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptiveSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace SK.Analytic

theorem cumulativeGapMap_sum (k : ℕ) (q : Fin (k+1) → ℝ) :
    ∑ b, cumulativeGapMap k q b = q (Fin.last k) := by
  rw [Fin.sum_univ_succ]
  simp only [cumulativeGapMap_zero,cumulativeGapMap_succ,Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ q
  have h2 := Fin.sum_univ_castSucc q
  linarith

theorem cumulativeGapMap_castSucc (k : ℕ) (q : Fin (k+2) → ℝ) (b : Fin (k+1)) :
    cumulativeGapMap (k+1) q b.castSucc = cumulativeGapMap k (fun i => q i.castSucc) b := by
  refine Fin.cases ?_ (fun i => ?_) b
  · rfl
  · rfl

theorem cumulativeGapMap_partial_sum (k : ℕ) (q : Fin (k+1) → ℝ) (l : Fin (k+1)) :
    (∑ b, if b ≤ l then cumulativeGapMap k q b else 0) = q l := by
  induction k with
  | zero => simp [Fin.eq_zero l]
  | succ k ih =>
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp only [Fin.le_last,ite_true,cumulativeGapMap_sum]
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.castSucc_le_castSucc_iff,cumulativeGapMap_castSucc]
      have h : ¬ Fin.last (k+1) ≤ l.castSucc := by simp [Fin.le_def]; omega
      rw [ite_eq_right h,add_zero]
      exact ih (fun i => q i.castSucc) l

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKAdaptiveContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem skBlockRoot_contDiff (N k : ℕ) :
    ContDiff ℝ 2 (fun p : ℝ × (Fin (k+1) → ℝ) => skBlockRoot N k p.1 p.2) := by
  have H := parameter_contDiff_at_field
    (spinPressure_paramRegular (blockDimension (Fintype.card (Edge N)) N k)
      (blockInteraction (skInteraction N)) (fun _ => 0)
      (blockMass (Fintype.card (Edge N)) N k)).1 (0:ℝ)
  have HC := H.comp (blockCoefficients_contDiff (N := N) (k := k)
    (fun _ : Fin (Fintype.card (Edge N)) => 1/Real.sqrt (N:ℝ)) 1)
  convert HC using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [mul_one_div,one_mul]
  rfl

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarCompression
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

theorem scalarHierarchy_compress (n : ℕ) {r : ℕ} (e : Fin r → Fin n)
    (he : StrictMono e) (m v : Fin n → ℝ)
    (hv : ∀ t, (∀ j, e j ≠ t) → v t = 0) (f : ℝ → ℝ) :
    scalarHierarchy n m v f = scalarHierarchy r (m ∘ e) (v ∘ e) f := by
  induction n generalizing r f with
  | zero =>
    cases r with
    | zero => rfl
    | succ r => exact Fin.elim0 (e 0)
  | succ n ih =>
    cases r with
    | zero =>
      have hlast : v (Fin.last n) = 0 := hv _ (fun j => Fin.elim0 j)
      simp only [scalarHierarchy,hlast,scalarStep_zero]
      exact ih (fun j => Fin.elim0 j) (fun a => Fin.elim0 a)
        (fun i => m i.castSucc) (fun i => v i.castSucc)
        (fun t _ => hv t.castSucc (fun j => Fin.elim0 j)) f
    | succ r =>
      by_cases hlast : e (Fin.last r) = Fin.last n
      · have hlt (i : Fin r) : (e i.castSucc).val < n := by
          have H := he (Fin.castSucc_lt_last i)
          rw [hlast] at H
          exact H
        let e' : Fin r → Fin n := fun i => ⟨(e i.castSucc).val,hlt i⟩
        have hcast (i : Fin r) : (e' i).castSucc = e i.castSucc := Fin.ext rfl
        have he' : StrictMono e' := by
          intro a b hab
          exact he (show a.castSucc < b.castSucc from hab)
        have hv' (t : Fin n) (ht : ∀ j, e' j ≠ t) : v t.castSucc = 0 := by
          apply hv
          intro j
          refine Fin.lastCases ?_ (fun i => ?_) j
          · rw [hlast]
            exact (Fin.castSucc_ne_last t).symm
          · intro h
            exact ht i (Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h))
        rw [scalarHierarchy,scalarHierarchy,← hlast]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv'
          (scalarStep (m (e (Fin.last r))) (v (e (Fin.last r))) f)
        simpa only [Function.comp_def,hcast] using H
      · have hlt (i : Fin (r+1)) : (e i).val < n := by
          have H := he.monotone (Fin.le_last i)
          have H' : (e (Fin.last r)).val < n := by
            have H'' := (e (Fin.last r)).isLt
            have Hne : (e (Fin.last r)).val ≠ n := by
              intro h
              exact hlast (Fin.ext h)
            omega
          exact lt_of_le_of_lt H H'
        let e' : Fin (r+1) → Fin n := fun i => ⟨(e i).val,hlt i⟩
        have hcast (i : Fin (r+1)) : (e' i).castSucc = e i := Fin.ext rfl
        have he' : StrictMono e' := by
          intro a b hab
          exact he hab
        have hzero : v (Fin.last n) = 0 := by
          apply hv
          intro j h
          have H := hlt j
          rw [h] at H
          exact (lt_irrefl n) H
        have hv' (t : Fin n) (ht : ∀ j, e' j ≠ t) : v t.castSucc = 0 := by
          apply hv
          intro j h
          exact ht j (Fin.ext (congrArg (fun z : Fin (n+1) => z.val) h))
        rw [scalarHierarchy,hzero,scalarStep_zero]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv' f
        simpa only [Function.comp_def,hcast] using H
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_SpinSiteTensorization
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Terminal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineLogPartition_sites (N : ℕ) (L : Fin N → E →L[ℝ] ℝ) :
    affineLogPartition (fun _ : Config N => 0) (fun s => ∑ i, spin (s i) • L i) =
      fun z => ∑ i, affineLogPartition (fun _ : Bool => 0) (fun b => spin b • L i) z := by
  funext z
  simp only [affineLogPartition,zero_add,sum_apply,
    smul_apply,smul_eq_mul,Real.exp_sum]
  rw [← Fintype.prod_sum (fun i b => Real.exp (spin b * L i z)),Real.log_prod]
  intro i _
  exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

end Terminal

theorem blockExponent_zero_disorder {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (v : Fin (k+1) → ℝ) (s : Config N) :
    blockExponent I (fun _ => 0) v s = ∑ i, spin (s i) • siteField (D := D) v i := by
  ext z
  rw [blockExponent_expansion]
  simp only [zero_mul,Finset.sum_const_zero,zero_add,siteField,
    sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem blockLogPartition_zero_disorder {D N k : ℕ} (I : Fin D → Finset (Fin N))
    (v : Fin (k+1) → ℝ) :
    affineLogPartition (fun _ => 0) (blockExponent I (fun _ => 0) v) =
      fun z => ∑ i, siteLogPartition (D := D) v i z := by
  convert affineLogPartition_sites N (siteField (D := D) v) using 1
  · congr 1
    funext s
    exact blockExponent_zero_disorder I v s
  · rfl

@[simp] theorem fieldOwner_field {D N k : ℕ} (i₀ : Fin N) (b : Fin (k+1)) (i : Fin N) :
    fieldOwner i₀ (fieldIndex D N k b i) = i := by
  rw [fieldIndex_eq_natAdd]
  unfold fieldOwner
  rw [Fin.addCases_right]
  rw [Equiv.symm_apply_apply]

theorem siteLogPartition_invariant {D N k : ℕ} (v : Fin (k+1) → ℝ) (i₀ i : Fin N)
    (t : Fin (blockDimension D N k)) (h : i ≠ fieldOwner i₀ t) :
    TranslationInvariant (siteLogPartition (D := D) v i) (coordinateAxis (blockDimension D N k) t) := by
  apply affineLogPartition_translation
  intro b
  simp only [smul_apply,siteField,sum_apply,
    smul_eq_mul,coordinateProjection_coordinateAxis]
  have he (j : Fin (k+1)) : fieldIndex D N k j i ≠ t := by
    intro ht
    apply h
    rw [← ht,fieldOwner_field]
  simp only [he,ite_false,mul_zero,Finset.sum_const_zero]

theorem skBlockRoot_zero_disorder_tensorizes {N k : ℕ} (hN : 0 < N) (v : Fin (k+1) → ℝ) :
    skBlockRoot N k 0 v =
      ∑ i, hierarchyPressure (blockDimension (Fintype.card (Edge N)) N k)
        (blockMass (Fintype.card (Edge N)) N k)
        (siteLogPartition (D := Fintype.card (Edge N)) v i) 0 := by
  simp only [skBlockRoot,zero_div,blockLogPartition_zero_disorder]
  exact congrFun (hierarchyPressure_sum_independent _ _ (fieldOwner ⟨0,hN⟩)
    (fun i => siteLogPartition (D := Fintype.card (Edge N)) v i)
    (fun i => affineLogPartition_boundedDerivs _ _)
    (fun t i h => siteLogPartition_invariant v ⟨0,hN⟩ i t h)) 0
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarSpinRecursion
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
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem siteScalarCoefficients_field {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (z : ParameterSpace (blockDimension D N k)) :
    (∑ t, siteScalarCoefficients (D := D) v i t*coordinateProjection (blockDimension D N k) t z) =
      siteField (D := D) v i z := by
  simp only [siteScalarCoefficients,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [siteField,sum_apply,smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem hierarchyPressure_site_scalar {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    hierarchyPressure (blockDimension D N k) (blockMass D N k)
      (siteLogPartition (D := D) v i) =
    fun _ => scalarHierarchy (blockDimension D N k) (blockMass D N k)
      (siteScalarCoefficients (D := D) v i) scalarSpinTerminal 0 := by
  have he : siteLogPartition (D := D) v i = fun z =>
      scalarSpinTerminal (0+∑ t, siteScalarCoefficients (D := D) v i t*
        coordinateProjection (blockDimension D N k) t z) := by
    funext z
    rw [zero_add,siteScalarCoefficients_field]
    exact affineLogPartition_bool (siteField (D := D) v i) z
  rw [he]
  exact hierarchyPressure_scalar_linear _ _ _ scalarSpinTerminal (fun _ => 0)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ScalarEndpoint
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fieldIndex_strictMono (D N k : ℕ) (i : Fin N) :
    StrictMono (fun b => fieldIndex D N k b i) := by
  intro a b hab
  change D+a.val*N+i.val < D+b.val*N+i.val
  exact Nat.add_lt_add_right (Nat.add_lt_add_left
    (Nat.mul_lt_mul_of_pos_right hab (Nat.zero_lt_of_lt i.isLt)) D) i.val

theorem siteScalarCoefficients_at {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (b : Fin (k+1)) :
    siteScalarCoefficients (D := D) v i (fieldIndex D N k b i) = v b := by
  have he (a : Fin (k+1)) : fieldIndex D N k a i = fieldIndex D N k b i ↔ a=b :=
    (fieldIndex_strictMono D N k i).injective.eq_iff
  simp only [siteScalarCoefficients,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem siteScalarCoefficients_off {D N k : ℕ} (v : Fin (k+1) → ℝ)
    (i : Fin N) (t : Fin (blockDimension D N k)) (ht : ∀ b, fieldIndex D N k b i ≠ t) :
    siteScalarCoefficients (D := D) v i t = 0 := by
  simp only [siteScalarCoefficients,ht,ite_false,Finset.sum_const_zero]

theorem hierarchyPressure_site_condensed {D N k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin N) :
    hierarchyPressure (blockDimension D N k) (blockMass D N k)
      (siteLogPartition (D := D) v i) =
      fun _ => scalarHierarchy (k+1) (quantileMass k) v scalarSpinTerminal 0 := by
  rw [hierarchyPressure_site_scalar]
  have H := scalarHierarchy_compress (blockDimension D N k)
    (fun b => fieldIndex D N k b i) (fieldIndex_strictMono D N k i)
    (blockMass D N k) (siteScalarCoefficients (D := D) v i)
    (fun t ht => siteScalarCoefficients_off v i t ht) scalarSpinTerminal
  have hm : (blockMass D N k ∘ fun b => fieldIndex D N k b i) = quantileMass k := by
    funext b
    exact blockMass_at_field D N k b i
  have hv : (siteScalarCoefficients (D := D) v i ∘ fun b => fieldIndex D N k b i) = v := by
    funext b
    exact siteScalarCoefficients_at v i b
  rw [hm,hv] at H
  rw [H]

theorem skBlockRoot_zero_disorder_scalar {N k : ℕ} (hN : 0 < N) (v : Fin (k+1) → ℝ) :
    skBlockRoot N k 0 v = (N:ℝ)*scalarHierarchy (k+1) (quantileMass k) v scalarSpinTerminal 0 := by
  rw [skBlockRoot_zero_disorder_tensorizes hN]
  simp only [hierarchyPressure_site_condensed,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_GuerraUpper
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem fixed_field_summation (k : ℕ) (Q r w : Fin (k+1) → ℝ) :
    (∑ b, cumulativeGapMap k Q b*(1-∑ l, if b ≤ l then w l*r l else 0)) =
      Q (Fin.last k)-∑ l, w l*Q l*r l := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,cumulativeGapMap_sum,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have he (b : Fin (k+1)) : cumulativeGapMap k Q b*(if b ≤ l then w l*r l else 0) =
      (if b ≤ l then cumulativeGapMap k Q b else 0)*(w l*r l) := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul,cumulativeGapMap_partial_sum]
  ring

theorem quenched_le_extendedQuantileParisi {N k : ℕ} (hN : 0 < N) (β : ℝ)
    (Q : Fin (k+1) → ℝ) (hgap : ∀ j, 0 ≤ cumulativeGapMap k Q j) :
    (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) ≤ extendedQuantileParisi k β Q := by
  let h : ℝ → ℝ := fun t => β*Real.sqrt t
  let v : ℝ → Fin (k+1) → ℝ := fun t j => β*Real.sqrt (1-t)*Real.sqrt (cumulativeGapMap k Q j)
  let f : ℝ → ℝ := fun t => skBlockRoot N k (h t) (v t)/(N:ℝ)
  let C : ℝ := (β^2/4)*(1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)
  let U := fun t => blockExponent (skInteraction N) (fun _ => h t/Real.sqrt (N:ℝ)) (v t)
  let r := fun t j => hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (U t) (fun i s => spin (s i))
    (blockLevel (Fintype.card (Edge N)) N k j)
  let s := fun t j => hierarchyReplicaSecond (blockDimension (Fintype.card (Edge N)) N k)
    (blockMass (Fintype.card (Edge N)) N k) (U t) (fun s i => spin (s i))
    (blockLevel (Fintype.card (Edge N)) N k j)
  let d := fun t => (β^2/4)*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t j)-
    (β^2/2)*(Q (Fin.last k)-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q j*r t j)
  have hcont : Continuous f := by
    have hv : Continuous v := by
      apply continuous_pi
      intro j
      exact (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).mul continuous_const
    exact ((skBlockRoot_contDiff N k).continuous.comp
      ((continuous_const.mul Real.continuous_sqrt).prodMk hv)).div_const _
  have hd : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (d t) t := by
    intro t ht
    let hp := β*(1/(2*Real.sqrt t))
    let vp := fun j => β*(-1/(2*Real.sqrt (1-t)))*Real.sqrt (cumulativeGapMap k Q j)
    have hh : HasDerivAt h hp t := (Real.hasDerivAt_sqrt ht.1.ne').const_mul β
    have hv : HasDerivAt v vp t := by
      apply hasDerivAt_pi.mpr
      intro j
      simpa only [v,vp,Pi.sub_apply,id_eq,zero_sub] using ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).sqrt
        (by linarith [ht.2] : 1-t ≠ 0)).const_mul β).mul_const (Real.sqrt (cumulativeGapMap k Q j))
    have hhp : h t*hp/2 = β^2/4 := by
      have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht.1).ne'
      dsimp only [h,hp]
      field_simp
      ring
    have hvp (j : Fin (k+1)) : vp j*v t j = -(β^2/2)*cumulativeGapMap k Q j := by
      have hs : Real.sqrt (1-t) ≠ 0 := (Real.sqrt_pos.mpr (by linarith [ht.2])).ne'
      dsimp only [vp,v]
      calc
        _ = -(β^2/2)*(Real.sqrt (cumulativeGapMap k Q j))^2*
          (Real.sqrt (1-t)/Real.sqrt (1-t)) := by ring
        _ = _ := by rw [div_self hs,mul_one,Real.sq_sqrt (hgap j)]
    have H := skBlockPressure_hasDerivAt hN h v hh hv
    dsimp only at H
    apply H.congr_deriv
    rw [hhp]
    simp only [hvp]
    have hsum : (∑ b, -(β^2/2)*cumulativeGapMap k Q b*
        (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r t l else 0)) =
        -(β^2/2)*(Q (Fin.last k)-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*Q l*r t l) := by
      rw [← fixed_field_summation k Q (r t) (fun _ => ((k+1:ℕ):ℝ)⁻¹),Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    change (β^2/4)*(1-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t l)+
      (∑ b, -(β^2/2)*cumulativeGapMap k Q b*
        (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r t l else 0)) = d t
    rw [hsum]
    dsimp only [d]
    ring
  have hbound (t : ℝ) : d t ≤ C := by
    have hs (j : Fin (k+1)) : 2*Q j*r t j-(Q j)^2 ≤ s t j := by
      have H := (hierarchyOverlapError_bounds _ (blockMass (Fintype.card (Edge N)) N k) (U t) (fun s i => spin (s i))
        (fun s i => by cases s i <;> norm_num [spin])
        (blockLevel (Fintype.card (Edge N)) N k j)).1
      rw [hierarchyOverlapError_eq_second_sub_sq _ _ _ _
        (fun s i => by cases s i <;> norm_num [spin])] at H
      change 0 ≤ s t j-(r t j)^2 at H
      nlinarith [sq_nonneg (r t j-Q j)]
    have H : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q j*r t j-(Q j)^2)) ≤
        ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*s t j :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hs j) (by positivity))
    have he (j : Fin (k+1)) : ((k+1:ℕ):ℝ)⁻¹*(2*Q j*r t j-(Q j)^2) =
        2*(((k+1:ℕ):ℝ)⁻¹*Q j*r t j)-((k+1:ℕ):ℝ)⁻¹*(Q j)^2 := by ring
    simp only [he,Finset.sum_sub_distrib] at H
    rw [← Finset.mul_sum (s := Finset.univ) (f := fun j : Fin (k+1) => ((k+1:ℕ):ℝ)⁻¹*Q j*r t j)] at H
    have HB := mul_le_mul_of_nonneg_left H (show 0 ≤ β^2/4 by positivity)
    dsimp only [d,C]
    nlinarith
  have H : f 1-C ≤ f 0 := by
    have HM : AntitoneOn (fun t => f t-C*t) (Set.Icc (0:ℝ) 1) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0:ℝ) 1)
        (hcont.sub (continuous_const.mul continuous_id)).continuousOn
        (fun t ht => ((hd t (by simpa only [interior_Icc] using ht)).sub
          ((hasDerivAt_id t).const_mul C)).hasDerivWithinAt)
        (fun t _ => by simpa only [mul_one] using sub_nonpos.mpr (hbound t))
    simpa using HM (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  have hzero : f 0 = scalarHierarchy (k+1) (quantileMass k)
      (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0 := by
    simp only [f,h,v,Real.sqrt_zero,mul_zero,sub_zero,Real.sqrt_one,mul_one,
      skBlockRoot_zero_disorder_scalar hN]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')
  have hone : f 1 = (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) := by
    simp only [f,h,v,Real.sqrt_one,mul_one,sub_self,Real.sqrt_zero,mul_zero,zero_mul,
      skBlockRoot_zero_fields_eq]
  rw [hzero,hone] at H
  change _ ≤ _+C
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileClamp
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

theorem cumulativeGapMap_nonneg_iff (k : ℕ) (Q : Fin (k+1) → ℝ) :
    (∀ j, 0 ≤ cumulativeGapMap k Q j) ↔ 0 ≤ Q 0 ∧ Monotone Q := by
  constructor
  · intro h
    refine ⟨h 0,Fin.monotone_iff_le_succ.mpr (fun j => ?_)⟩
    exact sub_nonneg.mp (h j.succ)
  · rintro ⟨h0,hm⟩ j
    refine Fin.cases h0 (fun i => ?_) j
    exact sub_nonneg.mpr (hm (Fin.castSucc_le_succ i))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Coverage_ThermodynamicLimit
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
open scoped Topology

theorem finiteParisiValues_nonempty (β : ℝ) : (finiteParisiValues β).Nonempty := by
  refine ⟨extendedQuantileParisi 0 β (fun _ => 0),0,fun _ => 0,?_,?_,rfl⟩
  · exact monotone_const
  · intro j; exact ⟨le_rfl,zero_le_one⟩

theorem quenched_le_finiteParisiValue {N : ℕ} (hN : 0 < N) (β : ℝ)
    {p : ℝ} (hp : p ∈ finiteParisiValues β) : quenchedPressure β N ≤ p := by
  obtain ⟨k,Q,hm,hQ,rfl⟩ := hp
  exact quenched_le_extendedQuantileParisi hN β Q
    ((cumulativeGapMap_nonneg_iff k Q).mpr ⟨(hQ 0).1,hm⟩)

theorem finiteParisiValues_bddBelow (β : ℝ) : BddBelow (finiteParisiValues β) :=
  ⟨quenchedPressure β 1,fun _ hp => quenched_le_finiteParisiValue (by norm_num) β hp⟩

theorem finiteParisiInf_le {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hm : Monotone Q) (hQ : ∀ j, Q j ∈ Set.Icc 0 1) :
    finiteParisiInf β ≤ extendedQuantileParisi k β Q :=
  csInf_le (finiteParisiValues_bddBelow β) ⟨k,Q,hm,hQ,rfl⟩

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileVariation
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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem extendedQuantileParisi_continuous (k : ℕ) (β : ℝ) :
    Continuous (extendedQuantileParisi k β) := by
  have hv : Continuous (fun Q : Fin (k+1) → ℝ => fun b => β*Real.sqrt (cumulativeGapMap k Q b)) := by
    apply continuous_pi
    intro b
    exact continuous_const.mul (Real.continuous_sqrt.comp ((continuous_apply b).comp (cumulativeGapMap k).continuous))
  have H := (skBlockRoot_contDiff 1 k).continuous.comp ((continuous_const (y := (0:ℝ))).prodMk hv)
  change Continuous (fun Q : Fin (k+1) → ℝ => skBlockRoot 1 k 0 (fun b => β*Real.sqrt (cumulativeGapMap k Q b))) at H
  simp only [skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),Nat.cast_one,one_mul] at H
  apply H.add
  apply continuous_const.mul
  exact (continuous_const.sub (continuous_const.mul (continuous_apply (Fin.last k)))).add
    (continuous_finsetSum _ (fun j _ => continuous_const.mul ((continuous_apply j).pow 2)))

theorem extendedQuantileParisi_hasDerivAt {k : ℕ} (β : ℝ)
    (Q : ℝ → Fin (k+1) → ℝ) {t : ℝ} {V : Fin (k+1) → ℝ}
    (hQ : HasDerivAt Q V t) (hgap : ∀ j, 0 < cumulativeGapMap k (Q t) j) :
    HasDerivAt (fun u => extendedQuantileParisi k β (Q u))
      ((β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*
        (Q t j-quantileOverlapMean k β (Q t) j)) t := by
  let v := fun u j => β*Real.sqrt (cumulativeGapMap k (Q u) j)
  let vp := fun j => β*(cumulativeGapMap k V j/(2*Real.sqrt (cumulativeGapMap k (Q t) j)))
  let r := quantileOverlapMean k β (Q t)
  have hv : HasDerivAt v vp t := by
    apply hasDerivAt_pi.mpr
    intro j
    have H := hasDerivAt_pi.mp ((cumulativeGapMap k).hasFDerivAt.comp_hasDerivAt t hQ) j
    exact (H.sqrt (hgap j).ne').const_mul β
  have hvp (j : Fin (k+1)) : vp j*v t j = (β^2/2)*cumulativeGapMap k V j := by
    have hsqrt := (Real.sqrt_pos.mpr (hgap j)).ne'
    dsimp only [vp,v]
    field_simp [hsqrt]
  have H := skBlockPressure_hasDerivAt (N := 1) (by norm_num) (fun _ => 0) v
    (hasDerivAt_const t (0:ℝ)) hv
  dsimp only at H
  simp only [zero_mul,zero_div,zero_add,Nat.cast_one,div_one,
    skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),one_mul,hvp] at H
  have he : (∑ b, (β^2/2)*cumulativeGapMap k V b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) =
      (β^2/2)*(V (Fin.last k)-∑ l : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V l*r l) := by
    rw [← fixed_field_summation k V r (fun _ => ((k+1:ℕ):ℝ)⁻¹),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  change HasDerivAt (fun u => scalarHierarchy (k+1) (quantileMass k) (v u) scalarSpinTerminal 0)
    (∑ b, (β^2/2)*cumulativeGapMap k V b*
      (1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) t at H
  rw [he] at H
  have HS : HasDerivAt (fun u => ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q u j)^2)
      (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q t j*V j)) t := by
    apply HasDerivAt.fun_sum
    intro j _
    simpa using ((hasDerivAt_pi.mp hQ j).pow 2).const_mul (((k+1:ℕ):ℝ)⁻¹)
  have HC := (((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_pi.mp hQ (Fin.last k)).const_mul 2)).add HS).const_mul (β^2/4)
  have HA := H.add HC
  apply HA.congr_deriv
  have he1 : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(2*Q t j*V j)) =
      2*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*Q t j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he2 : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*(Q t j-r j)) =
      (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*Q t j)-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*r j := by
    simp only [mul_sub,Finset.sum_sub_distrib]
  change _ = (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V j*(Q t j-r j)
  rw [he1,he2]
  ring
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileBoundary
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

theorem quantileOverlapMean_continuous (k : ℕ) (β : ℝ) :
    Continuous (quantileOverlapMean k β) := by
  have hv : Continuous (fun Q : Fin (k+1) → ℝ => fun b => Real.sqrt (cumulativeGapMap k Q b)) := by
    apply continuous_pi
    intro b
    exact Real.continuous_sqrt.comp ((continuous_apply b).comp (cumulativeGapMap k).continuous)
  have H := (blockAdaptiveOverlap_contDiff (k := k) (skInteraction 1) (fun _ => (0:ℝ)) β).continuous.comp
    ((continuous_const (y := (0:ℝ))).prodMk hv)
  have he : quantileOverlapMean k β = fun Q =>
      blockAdaptiveOverlap (k := k) (skInteraction 1) (fun _ => (0:ℝ)) β
        (0,fun b => Real.sqrt (cumulativeGapMap k Q b)) := by
    funext Q j
    simp only [quantileOverlapMean,blockAdaptiveOverlap,mul_zero]
  rw [he]
  exact H

theorem extendedQuantileParisi_hasDerivWithinAt_segment {k : ℕ} (β : ℝ)
    (A B : Fin (k+1) → ℝ) (hA : ∀ j, 0 ≤ cumulativeGapMap k A j)
    (hB : ∀ j, 0 < cumulativeGapMap k B j) :
    HasDerivWithinAt (fun t : ℝ => extendedQuantileParisi k β ((1-t) • A+t • B))
      ((β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
        (A j-quantileOverlapMean k β A j)) (Set.Ici 0) 0 := by
  let Q := fun t : ℝ => (1-t) • A+t • B
  let d := fun t => (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
    (Q t j-quantileOverlapMean k β (Q t) j)
  have hQ (t : ℝ) : HasDerivAt Q (B-A) t := by
    apply hasDerivAt_pi.mpr
    intro j
    have H := (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (A j)).add
      ((hasDerivAt_id t).mul_const (B j))
    exact H.congr_deriv (by simp; ring)
  have hQc : Continuous Q := continuous_iff_continuousAt.mpr (fun t => (hQ t).continuousAt)
  have hdc : Continuous d := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul (((continuous_apply j).comp hQc).sub
      ((continuous_apply j).comp ((quantileOverlapMean_continuous k β).comp hQc)))
  have hd (t : ℝ) (ht : t ∈ Set.Ioo (0:ℝ) 1) :
      HasDerivAt (fun t => extendedQuantileParisi k β (Q t)) (d t) t := by
    apply extendedQuantileParisi_hasDerivAt β Q (hQ t)
    intro j
    simp only [Q,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2.le) (hA j))
      (mul_pos ht.1 (hB j))
  have hs : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have he : (fun t => deriv (fun t => extendedQuantileParisi k β (Q t)) t) =ᶠ[𝓝[>] (0:ℝ)] d := by
    filter_upwards [hs] with t ht
    exact (hd t ht).deriv
  have H := hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (((extendedQuantileParisi_continuous k β).comp hQc).continuousAt.continuousWithinAt)
    hs ((hdc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  simpa only [d,Q,sub_zero,one_smul,zero_smul,add_zero] using H

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileLipschitz
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
open scoped Topology

theorem strictQuantile_gap (k : ℕ) (j : Fin (k+1)) :
    cumulativeGapMap k (strictQuantile k) j = 1/((k:ℝ)+2) := by
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [cumulativeGapMap_zero,strictQuantile]
  · simp only [cumulativeGapMap_succ,strictQuantile,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring

theorem strictQuantile_mem (k : ℕ) (j : Fin (k+1)) : strictQuantile k j ∈ Set.Icc 0 1 := by
  have hj : (j.val:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  unfold strictQuantile
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    linarith

theorem regularizeQuantile_positive {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) {ε : ℝ} (hε : ε ∈ Set.Ioc 0 1) (j : Fin (k+1)) :
    0 < cumulativeGapMap k (regularizeQuantile k Q ε) j := by
  simp only [regularizeQuantile,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,strictQuantile_gap]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hε.2) (hQ j))
    (mul_pos hε.1 (by positivity))

theorem regularizeQuantile_mem {k : ℕ} (Q : Fin (k+1) → ℝ) (hQ : ∀ j, Q j ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : ε ∈ Set.Icc 0 1) (j : Fin (k+1)) :
    regularizeQuantile k Q ε j ∈ Set.Icc 0 1 := by
  change (1-ε)*Q j+ε*strictQuantile k j ∈ Set.Icc 0 1
  have hR := strictQuantile_mem k j
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) (hQ j).1) (mul_nonneg hε.1 hR.1)
  · have H1 := mul_le_mul_of_nonneg_left (hQ j).2 (sub_nonneg.mpr hε.2)
    have H2 := mul_le_mul_of_nonneg_left hR.2 hε.1
    linarith

theorem regularizeQuantile_tendsto (k : ℕ) (Q : Fin (k+1) → ℝ) :
    Tendsto (fun n : ℕ => regularizeQuantile k Q (1/((n:ℝ)+1))) atTop (𝓝 Q) := by
  have H : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [regularizeQuantile,sub_zero,one_smul,zero_smul,add_zero] using
    (((tendsto_const_nhds (x := (1:ℝ))).sub H).smul (tendsto_const_nhds (x := Q))).add
      (H.smul (tendsto_const_nhds (x := strictQuantile k)))

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileMinimizer
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

theorem admissibleQuantiles_compact (k : ℕ) : IsCompact (admissibleQuantiles k) := by
  have he : admissibleQuantiles k = Set.Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) ∩ {Q | Monotone Q} := by
    ext Q
    simp only [admissibleQuantiles,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_Icc,Pi.le_def]
    aesop
  rw [he]
  exact isCompact_Icc.inter_right isClosed_monotone

theorem admissibleQuantiles_nonempty (k : ℕ) : (admissibleQuantiles k).Nonempty :=
  ⟨fun _ => 0,monotone_const,fun _ => ⟨le_rfl,zero_le_one⟩⟩

theorem exists_finite_quantile_minimizer (k : ℕ) (β : ℝ) :
    ∃ Q ∈ admissibleQuantiles k,
      ∀ R ∈ admissibleQuantiles k, extendedQuantileParisi k β Q ≤ extendedQuantileParisi k β R := by
  exact (admissibleQuantiles_compact k).exists_isMinOn (admissibleQuantiles_nonempty k)
    (extendedQuantileParisi_continuous k β).continuousOn
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_QuantileStationarity
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

theorem finite_quantile_minimizer_stationary {k : ℕ} (β : ℝ)
    (A : Fin (k+1) → ℝ) (hA : A ∈ admissibleQuantiles k)
    (hmin : ∀ R ∈ admissibleQuantiles k, extendedQuantileParisi k β A ≤ extendedQuantileParisi k β R)
    (B : Fin (k+1) → ℝ) (hB : B ∈ admissibleQuantiles k) :
    0 ≤ (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*
      (A j-quantileOverlapMean k β A j) := by
  have hgapA := (cumulativeGapMap_nonneg_iff k A).mpr ⟨(hA.2 0).1,hA.1⟩
  have strict (R : Fin (k+1) → ℝ) (hR : R ∈ admissibleQuantiles k)
      (hgapR : ∀ j, 0 < cumulativeGapMap k R j) :
      0 ≤ (β^2/2)*∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(R j-A j)*
        (A j-quantileOverlapMean k β A j) := by
    let Q := fun t : ℝ => (1-t) • A+t • R
    have hQ (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : Q t ∈ admissibleQuantiles k := by
      constructor
      · intro i j hij
        exact add_le_add (mul_le_mul_of_nonneg_left (hA.1 hij) (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left (hR.1 hij) ht.1)
      · intro j
        change (1-t)*A j+t*R j ∈ Set.Icc 0 1
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hA.2 j).1) (mul_nonneg ht.1 (hR.2 j).1)
        · have H₁ := mul_le_mul_of_nonneg_left (hA.2 j).2 (sub_nonneg.mpr ht.2)
          have H₂ := mul_le_mul_of_nonneg_left (hR.2 j).2 ht.1
          linarith
    have hm : IsMinOn (fun t => extendedQuantileParisi k β (Q t)) (Set.Icc (0:ℝ) 1) 0 := by
      intro t ht
      simpa only [Q,sub_zero,one_smul,zero_smul,add_zero,Set.mem_ofPred_eq] using hmin (Q t) (hQ t ht)
    have hd := (extendedQuantileParisi_hasDerivWithinAt_segment β A R hgapA hgapR).mono (show Set.Icc (0:ℝ) 1 ⊆ Set.Ici 0 from Set.Icc_subset_Ici_self)
    have ht : (1:ℝ)-0 ∈ posTangentConeAt (Set.Icc (0:ℝ) 1) 0 :=
      sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc (by norm_num : (0:ℝ) ≤ 1) ▸ Set.Subset.rfl)
    simpa only [sub_zero,ContinuousLinearMap.toSpanSingleton_apply,ContinuousLinearMap.smulRight_apply,one_apply_eq_self,smul_eq_mul,one_mul]
       using hm.localize.hasFDerivWithinAt_nonneg hd ht
  let ε := fun n : ℕ => 1/((n:ℝ)+1)
  have hε (n : ℕ) : ε n ∈ Set.Ioc 0 1 := by
    dsimp only [ε]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hgapB := (cumulativeGapMap_nonneg_iff k B).mpr ⟨(hB.2 0).1,hB.1⟩
  have HR (n : ℕ) := regularizeQuantile_positive B hgapB (hε n)
  have H (n : ℕ) := strict (regularizeQuantile k B (ε n))
    ⟨((cumulativeGapMap_nonneg_iff k _).mp (fun j => (HR n j).le)).2,
      regularizeQuantile_mem B hB.2 ⟨(hε n).1.le,(hε n).2⟩⟩ (HR n)
  let F := fun R : Fin (k+1) → ℝ => (β^2/2)*∑ j : Fin (k+1),
    ((k+1:ℕ):ℝ)⁻¹*(R j-A j)*(A j-quantileOverlapMean k β A j)
  have hF : Continuous F := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro j _
    exact (continuous_const.mul ((continuous_apply j).sub continuous_const)).mul continuous_const
  exact ge_of_tendsto (hF.continuousAt.tendsto.comp (regularizeQuantile_tendsto k B)) (Eventually.of_forall H)

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_StationaryApproximation
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

theorem exists_stationary_quantile_approximation (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∃ A : Fin (k+1) → ℝ,
      A ∈ admissibleQuantiles k ∧
      (∀ B ∈ admissibleQuantiles k, extendedQuantileParisi k β A ≤ extendedQuantileParisi k β B) ∧
      extendedQuantileParisi k β A < finiteParisiInf β+ε ∧
      (∀ B ∈ admissibleQuantiles k, 0 ≤ (β^2/2)*∑ j : Fin (k+1),
        ((k+1:ℕ):ℝ)⁻¹*(B j-A j)*(A j-quantileOverlapMean k β A j)) := by
  obtain ⟨p,hp,hlt⟩ := exists_lt_of_csInf_lt (finiteParisiValues_nonempty β)
    (show sInf (finiteParisiValues β) < finiteParisiInf β+ε by
      change finiteParisiInf β < finiteParisiInf β+ε
      linarith)
  obtain ⟨k,Q,hm,hQ,rfl⟩ := hp
  obtain ⟨A,hA,hmin⟩ := exists_finite_quantile_minimizer k β
  exact ⟨k,A,hA,hmin,(hmin Q ⟨hm,hQ⟩).trans_lt hlt,
    fun B hB => finite_quantile_minimizer_stationary β A hA hmin B hB⟩

theorem exists_stationary_quantile_sequence_oai (β : ℝ) :
    ∃ K : ℕ → ℕ, ∃ A : (n : ℕ) → Fin (K n+1) → ℝ,
      (∀ n, A n ∈ admissibleQuantiles (K n)) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) →
        extendedQuantileParisi (K n) β (A n) ≤ extendedQuantileParisi (K n) β B) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) → 0 ≤ (β^2/2)*∑ j : Fin (K n+1),
        ((K n+1:ℕ):ℝ)⁻¹*(B j-A n j)*(A n j-quantileOverlapMean (K n) β (A n) j)) ∧
      Tendsto (fun n => extendedQuantileParisi (K n) β (A n)) atTop (𝓝 (finiteParisiInf β)) := by
  have H (n : ℕ) := exists_stationary_quantile_approximation β
    (show 0 < 1/((n:ℝ)+1) by positivity)
  choose K A ha hm hu hs using H
  refine ⟨K,A,ha,hm,hs,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n : ℕ => finiteParisiInf β+1/((n:ℝ)+1)) atTop (𝓝 (finiteParisiInf β)) from ?_)
    (fun n => finiteParisiInf_le β (A n) (ha n).1 (ha n).2) (fun n => (hu n).le)
  simpa only [add_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (finiteParisiInf β)

end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.exists_stationary_quantile_sequence_oai := @OAI.SK.Analytic.exists_stationary_quantile_sequence_oai

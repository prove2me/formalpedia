-- Prove2me | solution 1 for OAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:13:25.441601+00:00
-- url     : https://prove2.me/submissions/88053ec3-9aa5-42cc-9fe4-b2270be0b3f7

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S006
import Theorems.Thm_OAI_SK_Analytic_exists_block_adaptive_path
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
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptiveEndpointAlgebra
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

theorem weighted_square_shift_bound {I : Type} [Fintype I]
    (w Q a : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (ha : ∀ i, a i ∈ Set.Icc 0 δ)
    (hQ : ∀ i, Q i ≤ 1+δ) :
    (∑ i, w i*(Q i)^2)-(∑ i, w i*(Q i-a i)^2) ≤ 2*δ*(1+δ) := by
  calc
    _ = ∑ i, w i*((Q i)^2-(Q i-a i)^2) := by
      simp only [mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ i, w i*(2*δ*(1+δ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have H1 := mul_le_mul_of_nonneg_right (hQ i) (ha i).1
      have H2 := mul_le_mul_of_nonneg_left (ha i).2 (by linarith : 0 ≤ 1+δ)
      nlinarith [sq_nonneg (a i)]
    _ = _ := by rw [← Finset.sum_mul,hs,one_mul]

theorem adaptive_endpoint_lower_algebra {I : Type} [Fintype I]
    (i₀ : I) (w Q a : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    {δ c ε f₀ f₁ p : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c)
    (ha : ∀ i, a i ∈ Set.Icc 0 δ) (hQ : ∀ i, Q i ≤ 1+δ)
    (hpath : f₁-f₀ ≤ c*(-1+2*(Q i₀-a i₀)-∑ i, w i*(Q i-a i)^2+ε))
    (hfield : f₀ ≤ p+2*c*δ) :
    f₁+c*(1-2*Q i₀+∑ i, w i*(Q i)^2)-c*(ε+2*δ*(1+δ)+2*δ) ≤ p := by
  have H := mul_le_mul_of_nonneg_left (weighted_square_shift_bound w Q a hw hs hδ ha hQ) hc
  have H0 := mul_nonneg hc (ha i₀).1
  nlinarith
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
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_AdaptiveIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SK.Analytic

theorem integral_square_ge_square {r : ℝ → ℝ}
    (hr : ContinuousOn r (Set.Icc (0:ℝ) 1)) :
    (∫ u in (0:ℝ)..1, r u)^2 ≤ ∫ u in (0:ℝ)..1, (r u)^2 := by
  let d := ∫ u in (0:ℝ)..1, r u
  have hi := hr.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have hi2 := (hr.pow 2).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have H := intervalIntegral.integral_nonneg_of_forall (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (fun u => sq_nonneg (r u-d))
  have he : (fun u => (r u-d)^2) = (fun u => (r u)^2-2*d*r u+d^2) := by
    funext u; ring
  rw [he,intervalIntegral.integral_add (f := fun u => (r u)^2-2*d*r u) (g := fun _ => d^2)
    (hi2.sub (hi.const_mul (2*d))) intervalIntegrable_const,
    intervalIntegral.integral_sub (f := fun u => (r u)^2) (g := fun u => 2*d*r u) hi2 (hi.const_mul (2*d)),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at H
  change 0 ≤ (∫ u in (0:ℝ)..1, (r u)^2)-2*d*d+(1-0)*d^2 at H
  dsimp only [d] at H
  nlinarith

theorem adaptive_integrated_bound {k : ℕ} (f : ℝ → ℝ) (q : ℝ → Fin (k+1) → ℝ)
    (r : ℝ → Fin (k+1) → ℝ) (e : ℝ → ℝ) (w : Fin (k+1) → ℝ)
    (hw : ∀ j, 0 ≤ w j) {c ε : ℝ} (hc : 0 ≤ c)
    (hf : ContinuousOn f (Set.Icc (0:ℝ) 1))
    (hr : ∀ j, ContinuousOn (fun u => r u j) (Set.Icc (0:ℝ) 1))
    (hq : ∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q (r u) (Set.Icc (0:ℝ) 1) u)
    (hD : ∀ u ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f
      (c*(-1+2*r u (Fin.last k)-∑ j, w j*(r u j)^2+e u)) u)
    (he : ∀ u ∈ Set.Ioo (0:ℝ) 1, e u ≤ ε) :
    f 1-f 0 ≤ c*(-1+2*(q 1 (Fin.last k)-q 0 (Fin.last k))-
      ∑ j, w j*(q 1 j-q 0 j)^2+ε) := by
  have hqc := HasDerivWithinAt.continuousOn hq
  have hqi (j : Fin (k+1)) := (continuous_apply j).comp_continuousOn hqc
  have hri (j : Fin (k+1)) := (hr j).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have hr2 (j : Fin (k+1)) := ((hr j).pow 2).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
  have hint (j : Fin (k+1)) : (∫ u in (0:ℝ)..1, r u j) = q 1 j-q 0 j := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) (hqi j) _ (hri j)
    intro u hu
    exact hasDerivAt_pi.mp ((hq u ⟨hu.1.le,hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2)) j
  let g := fun u => c*(-1+2*r u (Fin.last k)-∑ j, w j*(r u j)^2+ε)
  have hg : ContinuousOn g (Set.Icc (0:ℝ) 1) := by
    exact continuousOn_const.mul (((continuousOn_const.add (continuousOn_const.mul (hr _))).sub
      (continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul ((hr j).pow 2)))).add continuousOn_const)
  have H : f 1-f 0 ≤ ∫ u in (0:ℝ)..1, g u := by
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num) hf
      (fun u hu => (hD u hu).hasDerivWithinAt) hg.integrableOn_Icc
    intro u hu
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (he u hu)) hc
  have hs : (∫ u in (0:ℝ)..1, ∑ j, w j*(r u j)^2) =
      ∑ j, w j*(∫ u in (0:ℝ)..1, (r u j)^2) := by
    rw [intervalIntegral.integral_finsetSum]
    · simp only [intervalIntegral.integral_const_mul]
    · intro j _; exact (hr2 j).const_mul (w j)
  have hsum : IntervalIntegrable (fun u => ∑ j, w j*(r u j)^2) volume 0 1 :=
    (continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul ((hr j).pow 2))).intervalIntegrable_of_Icc (by norm_num)
  have hgint : (∫ u in (0:ℝ)..1, g u) =
      c*(-1+2*(q 1 (Fin.last k)-q 0 (Fin.last k))-
        ∑ j, w j*(∫ u in (0:ℝ)..1, (r u j)^2)+ε) := by
    dsimp only [g]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((intervalIntegrable_const.add ((hri _).const_mul 2)).sub hsum) intervalIntegrable_const,
      intervalIntegral.integral_sub (intervalIntegrable_const.add ((hri _).const_mul 2)) hsum,
      intervalIntegral.integral_add intervalIntegrable_const ((hri _).const_mul 2),
      intervalIntegral.integral_const_mul,hs,hint]
    simp
  rw [hgint] at H
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ hc
  have hx : (∑ j, w j*(q 1 j-q 0 j)^2) ≤
      ∑ j, w j*(∫ u in (0:ℝ)..1, (r u j)^2) := by
    apply Finset.sum_le_sum
    intro j _
    have HH := integral_square_ge_square (hr j)
    rw [hint] at HH
    exact mul_le_mul_of_nonneg_left HH (hw j)
  linarith
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

theorem adaptive_field_summation (k : ℕ) (r w : Fin (k+1) → ℝ) :
    (∑ b, cumulativeGapMap k r b*(1-∑ l, if b ≤ l then w l*r l else 0)) =
      r (Fin.last k)-∑ l, w l*(r l)^2 := by
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,cumulativeGapMap_sum,Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have he (b : Fin (k+1)) : cumulativeGapMap k r b*(if b ≤ l then w l*r l else 0) =
      (if b ≤ l then cumulativeGapMap k r b else 0)*(w l*r l) := by split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul,cumulativeGapMap_partial_sum]
  ring

theorem adaptive_pressure_algebra (k : ℕ) (r w e : Fin (k+1) → ℝ) (β : ℝ) :
    -(β^2/4)*(1-∑ l, w l*((r l)^2+e l))+
      (β^2/2)*(∑ b, cumulativeGapMap k r b*(1-∑ l, if b ≤ l then w l*r l else 0)) =
      (β^2/4)*(-1+2*r (Fin.last k)-∑ l, w l*(r l)^2+∑ l, w l*e l) := by
  rw [adaptive_field_summation]
  simp only [mul_add,Finset.sum_add_distrib]
  ring
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKAdaptiveDerivative
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

theorem skAdaptiveMean_eq_block (N k : ℕ) (β u : ℝ) (q : Fin (k+1) → ℝ) :
    skAdaptiveMean N k β u q = blockAdaptiveOverlap (skInteraction N)
      (fun _ => β/Real.sqrt (N:ℝ)) β
      (Real.sqrt (1-u),fun b => Real.sqrt (cumulativeGapMap k q b)) := by
  have ha : (fun _ : Fin (Fintype.card (Edge N)) => β*Real.sqrt (1-u)/Real.sqrt (N:ℝ)) =
      (fun _ => Real.sqrt (1-u)*(β/Real.sqrt (N:ℝ))) := by
    funext i
    ring
  funext j
  simp only [skAdaptiveMean,skAdaptiveExponent,blockAdaptiveOverlap,ha]

theorem skAdaptivePressure_hasDerivAt {N k : ℕ} (hN : 0 < N)
    (β : ℝ) (q : ℝ → Fin (k+1) → ℝ) {u : ℝ} (hu : u < 1)
    (hgap : ∀ b, 0 < cumulativeGapMap k (q u) b)
    (hq : HasDerivAt q (skAdaptiveMean N k β u (q u)) u) :
    HasDerivAt (fun t => skAdaptivePressure N k β (q t) t)
      ((β^2/4)*(-1+2*skAdaptiveMean N k β u (q u) (Fin.last k)-
        ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(skAdaptiveMean N k β u (q u) j)^2+
        ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*skAdaptiveError N k β u (q u) j)) u := by
  let r := skAdaptiveMean N k β u (q u)
  let h : ℝ → ℝ := fun t => β*Real.sqrt (1-t)
  let v : ℝ → Fin (k+1) → ℝ := fun t b => β*Real.sqrt (cumulativeGapMap k (q t) b)
  let hp : ℝ := β*(-1/(2*Real.sqrt (1-u)))
  let vp : Fin (k+1) → ℝ := fun b => β*(cumulativeGapMap k r b/(2*Real.sqrt (cumulativeGapMap k (q u) b)))
  have hh : HasDerivAt h hp u := by
    have H := ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).sqrt (by linarith : 1-u ≠ 0)
    simpa [h,hp] using H.const_mul β
  have hv : HasDerivAt v vp u := by
    apply hasDerivAt_pi.mpr
    intro b
    have H := hasDerivAt_pi.mp ((cumulativeGapMap k).hasFDerivAt.comp_hasDerivAt u hq) b
    exact (H.sqrt (hgap b).ne').const_mul β
  have hham : h u*hp/2 = -(β^2/4) := by
    have hs : Real.sqrt (1-u) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
    dsimp only [h,hp]
    field_simp [hs]
    ring
  have hvp (b : Fin (k+1)) : vp b*v u b = (β^2/2)*cumulativeGapMap k r b := by
    have hs : Real.sqrt (cumulativeGapMap k (q u) b) ≠ 0 := (Real.sqrt_pos.mpr (hgap b)).ne'
    dsimp only [v,vp]
    field_simp [hs]
  have hsecond (j : Fin (k+1)) : hierarchyReplicaSecond
      (blockDimension (Fintype.card (Edge N)) N k) (blockMass (Fintype.card (Edge N)) N k)
      (skAdaptiveExponent N k β u (q u)) (fun s i => spin (s i))
      (blockLevel (Fintype.card (Edge N)) N k j) = (r j)^2+skAdaptiveError N k β u (q u) j := by
    have H := hierarchyOverlapError_eq_second_sub_sq
      (blockDimension (Fintype.card (Edge N)) N k) (blockMass (Fintype.card (Edge N)) N k)
      (skAdaptiveExponent N k β u (q u)) (fun s i => spin (s i))
      (fun s i => by cases s i <;> norm_num [spin]) (blockLevel (Fintype.card (Edge N)) N k j)
    change skAdaptiveError N k β u (q u) j = _-(r j)^2 at H
    linarith
  have H := skBlockPressure_hasDerivAt hN h v hh hv
  dsimp only at H
  change HasDerivAt (fun t => skAdaptivePressure N k β (q t) t) _ u at H
  apply H.congr_deriv
  rw [hham]
  simp only [hvp]
  change -(β^2/4)*(1-∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*hierarchyReplicaSecond
      (blockDimension (Fintype.card (Edge N)) N k) (blockMass (Fintype.card (Edge N)) N k)
      (skAdaptiveExponent N k β u (q u)) (fun s i => spin (s i))
      (blockLevel (Fintype.card (Edge N)) N k j))+
    (∑ b, (β^2/2)*cumulativeGapMap k r b*(1-∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*r l else 0)) = _
  simp_rw [hsecond]
  simpa only [mul_assoc,← Finset.mul_sum] using adaptive_pressure_algebra k r (fun _ => ((k+1:ℕ):ℝ)⁻¹) (skAdaptiveError N k β u (q u)) β
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

theorem skAdaptivePressure_continuousOn {N k : ℕ} (β : ℝ)
    {q : ℝ → Fin (k+1) → ℝ} {s : Set ℝ} (hq : ContinuousOn q s) :
    ContinuousOn (fun u => skAdaptivePressure N k β (q u) u) s := by
  have hgap : ContinuousOn (fun u => cumulativeGapMap k (q u)) s :=
    (cumulativeGapMap k).continuous.comp_continuousOn hq
  have hv : ContinuousOn (fun u b => β*Real.sqrt (cumulativeGapMap k (q u) b)) s := by
    apply continuousOn_pi.mpr
    intro b
    exact continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      ((continuous_apply b).comp_continuousOn hgap))
  have hh : ContinuousOn (fun u : ℝ => β*Real.sqrt (1-u)) s :=
    continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.sub continuousOn_id))
  exact ((skBlockRoot_contDiff N k).continuous.comp_continuousOn (hh.prodMk hv)).div_const _

theorem skAdaptiveMean_continuousOn {N k : ℕ} (β : ℝ)
    {q : ℝ → Fin (k+1) → ℝ} {s : Set ℝ} (hq : ContinuousOn q s) :
    ContinuousOn (fun u => skAdaptiveMean N k β u (q u)) s := by
  have hgap := (cumulativeGapMap k).continuous.comp_continuousOn hq
  have hv : ContinuousOn (fun u b => Real.sqrt (cumulativeGapMap k (q u) b)) s := by
    apply continuousOn_pi.mpr
    intro b
    exact Real.continuous_sqrt.comp_continuousOn ((continuous_apply b).comp_continuousOn hgap)
  have hh : ContinuousOn (fun u : ℝ => Real.sqrt (1-u)) s :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub continuousOn_id)
  convert (blockAdaptiveOverlap_contDiff (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) β).continuous.comp_continuousOn
      (hh.prodMk hv) using 1
  all_goals try with_reducible_and_instances rfl
  funext time
  exact skAdaptiveMean_eq_block N k β time (q time)
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKFiniteInterpolation
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

theorem exists_sk_finite_interpolation {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ q : ℝ → Fin (k+1) → ℝ,
      q 0 = (fun j => ((j.val:ℝ)+1)*η) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q (skAdaptiveMean N k β u (q u))
        (Set.Icc (0:ℝ) 1) u) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, η ≤ cumulativeGapMap k (q u) j) ∧
      (∀ u ∈ Set.Icc (0:ℝ) 1, ∀ j, q u j ≤ ((j.val:ℝ)+1)*η+u) ∧
      skAdaptivePressure N k β (q 1) 1-skAdaptivePressure N k β (q 0) 0 ≤
        (β^2/4)*(-1+2*(q 1 (Fin.last k)-q 0 (Fin.last k))-
          ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(q 1 j-q 0 j)^2+
          20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))) := by
  obtain ⟨q,h0,hD,hgap,hupper,herr⟩ := exists_block_adaptive_path hN hk
    (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) hβ hη hsmall
  have hD' : ∀ u ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt q (skAdaptiveMean N k β u (q u))
      (Set.Icc (0:ℝ) 1) u := by
    simpa only [skAdaptiveMean_eq_block] using hD
  refine ⟨q,h0,hD',hgap,hupper,?_⟩
  have hqc := HasDerivWithinAt.continuousOn hD'
  have hrc := skAdaptiveMean_continuousOn (N := N) β hqc
  apply adaptive_integrated_bound (fun u => skAdaptivePressure N k β (q u) u) q
    (fun u => skAdaptiveMean N k β u (q u))
    (fun u => ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*skAdaptiveError N k β u (q u) j)
    (fun _ => ((k+1:ℕ):ℝ)⁻¹) (fun _ => by positivity) (by positivity)
    (skAdaptivePressure_continuousOn β hqc)
    (fun j => (continuous_apply j).comp_continuousOn hrc) hD'
  · intro u hu
    exact skAdaptivePressure_hasDerivAt hN β q hu.2
      (fun b => hη.trans_le (hgap u ⟨hu.1.le,hu.2.le⟩ b))
      ((hD' u ⟨hu.1.le,hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
  · intro u hu
    have H := herr u ⟨hu.1.le,hu.2.le⟩
    have ha : (fun _ : Fin (Fintype.card (Edge N)) => Real.sqrt (1-u)*(β/Real.sqrt (N:ℝ))) =
        (fun _ => β*Real.sqrt (1-u)/Real.sqrt (N:ℝ)) := by funext i; ring
    dsimp only at H
    simpa only [ha,skAdaptiveError,skAdaptiveExponent] using H
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKSmallField
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

theorem skBlock_smallField_cost {N k : ℕ} (hN : 0 < N) (β : ℝ)
    {η : ℝ} (hη : 0 < η) :
    skBlockRoot N k β (fun _ => β*Real.sqrt η)/(N:ℝ)-
      skBlockRoot N k β (fun _ => 0)/(N:ℝ) ≤ β^2/2*((k+1:ℕ):ℝ)*η := by
  let v : ℝ → Fin (k+1) → ℝ := fun u _ => β*Real.sqrt (u*η)
  let f : ℝ → ℝ := fun u => skBlockRoot N k β (v u)/(N:ℝ)
  let d : ℝ → ℝ := fun u => β^2*η/2*∑ b : Fin (k+1), (1-
    ∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
      hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
        (blockMass (Fintype.card (Edge N)) N k)
        (blockExponent (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) (v u))
        (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k l) else 0)
  have hvcont : Continuous v := by
    apply continuous_pi
    intro b
    exact continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.mul continuous_const))
  have hf : Continuous f :=
    ((skBlockRoot_contDiff N k).continuous.comp (continuous_const.prodMk hvcont)).div_const _
  have hd : ∀ u ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (d u) u := by
    intro u hu
    let vp : Fin (k+1) → ℝ := fun _ => β*(η/(2*Real.sqrt (u*η)))
    have hs : Real.sqrt (u*η) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hu.1 hη)).ne'
    have hv : HasDerivAt v vp u := by
      apply hasDerivAt_pi.mpr
      intro b
      exact ((hasDerivAt_mul_const η (x := u)).sqrt (mul_pos hu.1 hη).ne').const_mul β
    have hvp (b : Fin (k+1)) : vp b*v u b = β^2*η/2 := by
      dsimp only [v,vp]
      calc
        _ = (β^2*η/2)*(Real.sqrt (u*η)/Real.sqrt (u*η)) := by ring
        _ = _ := by rw [div_self hs,mul_one]
    have H := skBlockPressure_hasDerivAt hN (fun _ => β) v (hasDerivAt_const u β) hv
    dsimp only at H
    apply H.congr_deriv
    simp only [mul_zero,zero_div,zero_mul,zero_add,hvp,← Finset.mul_sum]
    rfl
  have hb (u : ℝ) : d u ≤ β^2/2*((k+1:ℕ):ℝ)*η := by
    have hsum : (∑ b : Fin (k+1), (1-
        ∑ l : Fin (k+1), if b ≤ l then ((k+1:ℕ):ℝ)⁻¹*
          hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
            (blockMass (Fintype.card (Edge N)) N k)
            (blockExponent (skInteraction N) (fun _ => β/Real.sqrt (N:ℝ)) (v u))
            (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k l) else 0)) ≤
        ((k+1:ℕ):ℝ) := by
      calc
        _ ≤ ∑ _ : Fin (k+1), (1:ℝ) := by
          apply Finset.sum_le_sum
          intro b _
          apply sub_le_self
          apply Finset.sum_nonneg
          intro l _
          split_ifs
          · exact mul_nonneg (by positivity) (hierarchyMeanOverlap_bounds _ _ _ _
              (fun i s => by cases s i <;> norm_num [spin]) _).1
          · exact le_rfl
        _ = _ := by simp
    calc
      d u ≤ β^2*η/2*((k+1:ℕ):ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have H : f 1-f 0 ≤ ∫ _ in (0:ℝ)..1, β^2/2*((k+1:ℕ):ℝ)*η := by
    apply intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num) hf.continuousOn
      (fun u hu => (hd u hu).hasDerivWithinAt) (continuousOn_const.integrableOn_Icc)
    exact fun u _ => hb u
  simpa [f,v] using H

theorem cumulativeGapMap_initial (k : ℕ) (η : ℝ) :
    cumulativeGapMap k (fun j => ((j.val:ℝ)+1)*η) = fun _ => η := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp only [cumulativeGapMap_succ,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    ring

theorem skAdaptivePressure_initial_cost {N k : ℕ} (hN : 0 < N) (β : ℝ)
    {η : ℝ} (hη : 0 < η) :
    skAdaptivePressure N k β (fun j => ((j.val:ℝ)+1)*η) 0 ≤
      skBlockRoot N k β (fun _ => 0)/(N:ℝ)+β^2/2*((k+1:ℕ):ℝ)*η := by
  have H := skBlock_smallField_cost (k := k) hN β hη
  simp only [skAdaptivePressure,sub_zero,Real.sqrt_one,mul_one,cumulativeGapMap_initial]
  linarith
end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_SKFiniteEndpoint
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

theorem exists_sk_finite_endpoint {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ Q : Fin (k+1) → ℝ,
      (∀ j, η ≤ cumulativeGapMap k Q j) ∧
      (∀ j, Q j ≤ 1+((k+1:ℕ):ℝ)*η) ∧
      skAdaptivePressure N k β Q 1+
        (β^2/4)*(1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2)-
        (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
          2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+2*(((k+1:ℕ):ℝ)*η)) ≤
        skBlockRoot N k β (fun _ => 0)/(N:ℝ) := by
  obtain ⟨q,h0,_hD,hgap,hupper,hpath⟩ := exists_sk_finite_interpolation hN hk hβ hη hsmall
  have ha (j : Fin (k+1)) : ((j.val:ℝ)+1)*η ∈ Set.Icc 0 (((k+1:ℕ):ℝ)*η) := by
    constructor
    · positivity
    · apply mul_le_mul_of_nonneg_right _ hη.le
      exact_mod_cast j.isLt
  have hQ (j : Fin (k+1)) : q 1 j ≤ 1+((k+1:ℕ):ℝ)*η := by
    have H := hupper 1 (by norm_num) j
    linarith [(ha j).2]
  refine ⟨q 1,hgap 1 (by norm_num),hQ,?_⟩
  apply adaptive_endpoint_lower_algebra (Fin.last k) (fun _ => ((k+1:ℕ):ℝ)⁻¹)
    (q 1) (fun j => ((j.val:ℝ)+1)*η) (fun _ => by positivity) (uniformAtom_sum k)
    (by positivity) (by positivity) ha hQ
  · simpa only [h0] using hpath
  · have H := skAdaptivePressure_initial_cost (k := k) hN β hη
    convert H using 1 <;> first | rfl | ring
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

theorem skAdaptivePressure_terminal {N k : ℕ} (hN : 0 < N) (β : ℝ) (Q : Fin (k+1) → ℝ) :
    skAdaptivePressure N k β Q 1 =
      scalarHierarchy (k+1) (quantileMass k)
        (fun b => β*Real.sqrt (cumulativeGapMap k Q b)) scalarSpinTerminal 0 := by
  simp only [skAdaptivePressure,sub_self,Real.sqrt_zero,mul_zero,
    skBlockRoot_zero_disorder_scalar hN]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')

theorem exists_quenched_scalar_lower_bound {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ Q : Fin (k+1) → ℝ,
      (∀ j, η ≤ cumulativeGapMap k Q j) ∧
      (∀ j, Q j ≤ 1+((k+1:ℕ):ℝ)*η) ∧
      extendedQuantileParisi k β Q-
        (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
          2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+2*(((k+1:ℕ):ℝ)*η)) ≤
        (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) := by
  obtain ⟨Q,hgap,hupper,H⟩ := exists_sk_finite_endpoint hN hk hβ hη hsmall
  refine ⟨Q,hgap,hupper,?_⟩
  simpa only [extendedQuantileParisi,skAdaptivePressure_terminal hN,skBlockRoot_zero_fields_eq] using H
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
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FieldVarianceMonotone
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

theorem skBlock_field_variance_mono {N k : ℕ} (hN : 0 < N) (B β : ℝ)
    (a b : Fin (k+1) → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 < b j)
    (hab : ∀ j, a j ≤ b j) :
    skBlockRoot N k B (fun j => β*Real.sqrt (a j))/(N:ℝ) ≤
      skBlockRoot N k B (fun j => β*Real.sqrt (b j))/(N:ℝ) := by
  let V : ℝ → Fin (k+1) → ℝ := fun u j => (1-u)*a j+u*b j
  let v : ℝ → Fin (k+1) → ℝ := fun u j => β*Real.sqrt (V u j)
  let f : ℝ → ℝ := fun u => skBlockRoot N k B (v u)/(N:ℝ)
  let E : ℝ → Fin (k+1) → ℝ := fun u l =>
    hierarchyMeanOverlap (blockDimension (Fintype.card (Edge N)) N k)
      (blockMass (Fintype.card (Edge N)) N k)
      (blockExponent (skInteraction N) (fun _ => B/Real.sqrt (N:ℝ)) (v u))
      (fun i s => spin (s i)) (blockLevel (Fintype.card (Edge N)) N k l)
  let d : ℝ → ℝ := fun u => ∑ j, (β^2/2)*(b j-a j)*
    (1-∑ l : Fin (k+1), if j ≤ l then ((k+1:ℕ):ℝ)⁻¹*E u l else 0)
  have hvcont : Continuous v := by
    apply continuous_pi
    intro j
    exact continuous_const.mul (Real.continuous_sqrt.comp
      (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)))
  have hf : Continuous f :=
    ((skBlockRoot_contDiff N k).continuous.comp (continuous_const.prodMk hvcont)).div_const _
  have hd : ∀ u ∈ Set.Ioo (0:ℝ) 1, HasDerivAt f (d u) u := by
    intro u hu
    have hV (j : Fin (k+1)) : 0 < V u j :=
      add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hu.2.le) (ha j)) (mul_pos hu.1 (hb j))
    let vp : Fin (k+1) → ℝ := fun j => β*((b j-a j)/(2*Real.sqrt (V u j)))
    have hv : HasDerivAt v vp u := by
      apply hasDerivAt_pi.mpr
      intro j
      have HV : HasDerivAt (fun t => V t j) (b j-a j) u := by
        have H := (((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).mul_const (a j)).add
          ((hasDerivAt_id u).mul_const (b j))
        exact H.congr_deriv (by ring)
      exact (HV.sqrt (hV j).ne').const_mul β
    have hvp (j : Fin (k+1)) : vp j*v u j = (β^2/2)*(b j-a j) := by
      dsimp only [v,vp]
      calc
        _ = ((β^2/2)*(b j-a j))*(Real.sqrt (V u j)/Real.sqrt (V u j)) := by ring
        _ = _ := by rw [div_self (Real.sqrt_pos.mpr (hV j)).ne',mul_one]
    have H := skBlockPressure_hasDerivAt hN (fun _ => B) v (hasDerivAt_const u B) hv
    dsimp only at H
    apply H.congr_deriv
    simp only [mul_zero,zero_div,zero_mul,zero_add,hvp]
    rfl
  have hdpos (u : ℝ) : 0 ≤ d u := by
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (hab j)))
    apply sub_nonneg.mpr
    calc
      _ ≤ ∑ _ : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro l _
        split_ifs
        · exact mul_le_of_le_one_right (by positivity) (hierarchyMeanOverlap_bounds _ _ _ _
            (fun i s => by cases s i <;> norm_num [spin]) _).2
        · positivity
      _ = 1 := uniformAtom_sum k
  have H : f 0 ≤ f 1 := by
    apply (monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1) hf.continuousOn
      (fun u hu => (hd u (by simpa only [interior_Icc] using hu)).hasDerivWithinAt)
      (fun u _ => hdpos u)) (by norm_num) (by norm_num) (by norm_num)
  simpa only [f,v,V,sub_zero,one_mul,zero_mul,add_zero,sub_self,zero_add] using H
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

theorem clampQuantile_gap {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) (j : Fin (k+1)) :
    0 ≤ cumulativeGapMap k (clampQuantile Q) j ∧
      cumulativeGapMap k (clampQuantile Q) j ≤ cumulativeGapMap k Q j := by
  obtain ⟨h0,hm⟩ := (cumulativeGapMap_nonneg_iff k Q).mp hQ
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨le_min h0 zero_le_one,min_le_left _ _⟩
  · simp only [cumulativeGapMap_succ,clampQuantile]
    have hi := hm (Fin.castSucc_le_succ i)
    by_cases hb : Q i.succ ≤ 1
    · rw [min_eq_left hb,min_eq_left (hi.trans hb)]
      exact ⟨sub_nonneg.mpr hi,le_rfl⟩
    · rw [min_eq_right (le_of_not_ge hb)]
      by_cases ha : Q i.castSucc ≤ 1
      · rw [min_eq_left ha]
        constructor <;> linarith
      · rw [min_eq_right (le_of_not_ge ha),sub_self]
        exact ⟨le_rfl,sub_nonneg.mpr hi⟩

theorem clampQuantile_admissible {k : ℕ} (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 ≤ cumulativeGapMap k Q j) :
    Monotone (clampQuantile Q) ∧ ∀ j, clampQuantile Q j ∈ Set.Icc 0 1 := by
  have H := (cumulativeGapMap_nonneg_iff k (clampQuantile Q)).mp (fun j => (clampQuantile_gap Q hQ j).1)
  refine ⟨H.2,fun j => ⟨H.1.trans (H.2 (Fin.zero_le j)),min_le_right _ _⟩⟩

theorem extendedQuantileParisi_clamp_le {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : ∀ j, 0 < cumulativeGapMap k Q j) {δ : ℝ} (hδ : 0 ≤ δ)
    (hupper : ∀ j, Q j ≤ 1+δ) :
    extendedQuantileParisi k β (clampQuantile Q) ≤ extendedQuantileParisi k β Q+(β^2/4)*(2*δ) := by
  have hg := clampQuantile_gap Q (fun j => (hQ j).le)
  have H := skBlock_field_variance_mono (N := 1) (k := k) (by norm_num) 0 β
    (cumulativeGapMap k (clampQuantile Q)) (cumulativeGapMap k Q)
    (fun j => (hg j).1) hQ (fun j => (hg j).2)
  simp only [skBlockRoot_zero_disorder_scalar (by norm_num : 0 < 1),Nat.cast_one,one_mul,div_one] at H
  have hqn := (cumulativeGapMap_nonneg_iff k Q).mp (fun j => (hQ j).le)
  have hnonneg (j : Fin (k+1)) : 0 ≤ Q j := hqn.1.trans (hqn.2 (Fin.zero_le j))
  have hsq : (∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(clampQuantile Q j)^2) ≤
      ∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2 := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sq_le_sq₀ (le_min (hnonneg j) zero_le_one) (hnonneg j) |>.mpr (min_le_left _ _)
  have hlast : Q (Fin.last k)-clampQuantile Q (Fin.last k) ≤ δ := by
    dsimp only [clampQuantile]
    by_cases h : Q (Fin.last k) ≤ 1
    · rw [min_eq_left h,sub_self]
      exact hδ
    · rw [min_eq_right (le_of_not_ge h)]
      linarith [hupper (Fin.last k)]
  unfold extendedQuantileParisi
  have hc : 0 ≤ β^2/4 := by positivity
  have hcineq := mul_le_mul_of_nonneg_left (show
      1-2*clampQuantile Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(clampQuantile Q j)^2 ≤
      1-2*Q (Fin.last k)+∑ j : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*(Q j)^2+2*δ by linarith) hc
  nlinarith

theorem exists_admissible_scalar_lower_bound {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    ∃ Q : Fin (k+1) → ℝ,
      Monotone Q ∧ (∀ j, Q j ∈ Set.Icc 0 1) ∧
      extendedQuantileParisi k β Q-
        (β^2/4)*(20*((k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))+1/Real.sqrt (k:ℝ))+
          2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η)+4*(((k+1:ℕ):ℝ)*η)) ≤
        (∫ J, logPartition β J ∂disorderLaw N)/(N:ℝ) := by
  obtain ⟨Q,hgap,hupper,H⟩ := exists_quenched_scalar_lower_bound hN hk hβ hη hsmall
  have hpos (j : Fin (k+1)) : 0 < cumulativeGapMap k Q j := hη.trans_le (hgap j)
  have ha := clampQuantile_admissible Q (fun j => (hpos j).le)
  refine ⟨clampQuantile Q,ha.1,ha.2,?_⟩
  have HC := extendedQuantileParisi_clamp_le β Q hpos (by positivity) hupper
  linarith
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

theorem quenched_le_finiteParisiInf {N : ℕ} (hN : 0 < N) (β : ℝ) :
    quenchedPressure β N ≤ finiteParisiInf β :=
  le_csInf (finiteParisiValues_nonempty β) (fun _ hp => quenched_le_finiteParisiValue hN β hp)

theorem finiteParisiInf_sub_error_le {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hsmall : (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η)) ≤ 1) :
    finiteParisiInf β-finiteComparisonError β k η N ≤ quenchedPressure β N := by
  obtain ⟨Q,hm,hQ,H⟩ := exists_admissible_scalar_lower_bound hN hk hβ hη hsmall
  exact (sub_le_sub_right (finiteParisiInf_le β Q hm hQ) _).trans H

theorem finiteComparisonRatio_tendsto (k : ℕ) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    Tendsto (fun N : ℕ => (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*η))) atTop (𝓝 0) := by
  exact (Real.tendsto_sqrt_atTop.comp
    (Filter.Tendsto.atTop_mul_const (by positivity : 0 < β^2*η)
      (tendsto_natCast_atTop_atTop (R := ℝ)))).const_div_atTop (k:ℝ)

theorem finiteComparisonError_tendsto (k : ℕ) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η) :
    Tendsto (finiteComparisonError β k η) atTop (𝓝 (finiteComparisonErrorLimit β k η)) := by
  unfold finiteComparisonError
  have H := finiteComparisonRatio_tendsto k hβ hη
  simpa only [finiteComparisonErrorLimit,zero_add] using
    ((((H.add_const (1/Real.sqrt (k:ℝ))).const_mul 20).add_const
      (2*(((k+1:ℕ):ℝ)*η)*(1+((k+1:ℕ):ℝ)*η))).add_const
        (4*(((k+1:ℕ):ℝ)*η))).const_mul (β^2/4)

theorem finiteComparisonErrorLimit_continuous (β : ℝ) (k : ℕ) :
    Continuous (finiteComparisonErrorLimit β k) := by
  unfold finiteComparisonErrorLimit
  fun_prop

theorem eventually_lt_quenched_of_error {k : ℕ} (hk : 0 < k)
    {β η a : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (ha : a < finiteParisiInf β-finiteComparisonErrorLimit β k η) :
    ∀ᶠ N : ℕ in atTop, a < quenchedPressure β N := by
  have he := (finiteComparisonError_tendsto k hβ hη).eventually_lt_const
    (show finiteComparisonErrorLimit β k η < finiteParisiInf β-a by linarith)
  have hr := (finiteComparisonRatio_tendsto k hβ hη).eventually_lt_const (by norm_num : (0:ℝ)<1)
  filter_upwards [he,hr,eventually_gt_atTop (0:ℕ)] with N hE hR hN
  have H := finiteParisiInf_sub_error_le hN hk hβ hη hR.le
  linarith

theorem eventually_lt_quenched_of_mesh {k : ℕ} (hk : 0 < k) {β a : ℝ} (hβ : 0 < β)
    (ha : a < finiteParisiInf β-(β^2/4)*(20/Real.sqrt (k:ℝ))) :
    ∀ᶠ N : ℕ in atTop, a < quenchedPressure β N := by
  have H := (finiteComparisonErrorLimit_continuous β k).continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : finiteComparisonErrorLimit β k 0 = (β^2/4)*(20/Real.sqrt (k:ℝ)) := by
    simp only [finiteComparisonErrorLimit,mul_zero,add_zero,zero_mul,mul_one_div]
  rw [he] at H
  obtain ⟨n,hn⟩ := (H.eventually (eventually_lt_nhds
    (show (β^2/4)*(20/Real.sqrt (k:ℝ)) < finiteParisiInf β-a by linarith))).exists
  apply eventually_lt_quenched_of_error hk hβ (show 0 < 1/((n:ℝ)+1) by positivity)
  dsimp only [Function.comp_def] at hn
  linarith

theorem quenchedPressure_tendsto_finiteParisiInf_oai {β : ℝ} (hβ : 0 < β) :
    Tendsto (quenchedPressure β) atTop (𝓝 (finiteParisiInf β)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have H : Tendsto (fun k : ℕ => (β^2/4)*(20/Real.sqrt (k:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero,Function.comp_def] using ((Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 20).const_mul (β^2/4)
    have HE := H.eventually (eventually_lt_nhds (sub_pos.mpr ha))
    obtain ⟨k,hk,hE⟩ := ((eventually_gt_atTop (0:ℕ)).and HE).exists
    exact eventually_lt_quenched_of_mesh hk hβ (by linarith)
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact (quenched_le_finiteParisiInf hN β).trans_lt ha
end SK.Analytic

end
end

end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf_oai := @OAI.SK.Analytic.quenchedPressure_tendsto_finiteParisiInf_oai

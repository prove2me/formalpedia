-- Prove2me | solution 1 for OAI.SK.Analytic.tripleConstrainedPressure_schedule
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:18:34.374759+00:00
-- url     : https://prove2.me/submissions/926b5a58-658e-4b67-93f2-0bbea8bad8f9

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S004
import Definitions.Def_OAIQ036S005
import Theorems.Thm_OAI_SK_Analytic_matrixFiniteInterpolation_offset

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_Basic
attribute [-instance] _root_.OAI.SK.disorderPairLaw_probability
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

theorem sum_edges {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : Edge n, f e.val) = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then f (i, j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) f]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_sq_eq_edges {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 = (∑ i, (a i) ^ 2) + 2 * ∑ e : Edge n, a e.val.1 * a e.val.2 := by
  classical
  rw [sum_edges (fun p : Fin n × Fin n => a p.1 * a p.2), pow_two, Fintype.sum_mul_sum]
  have hsplit (i j : Fin n) : a i * a j =
      (if i = j then a i ^ 2 else 0) +
      (if i < j then a i * a j else 0) +
      (if j < i then a i * a j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp [pow_two]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then a i ^ 2 else 0) +
        (if i < j then a i * a j else 0) +
        (if j < i then a i * a j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : Fin n, ∑ j : Fin n, if i = j then a i ^ 2 else 0) =
      ∑ i, a i ^ 2 := by simp
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hd, hs]
  ring

end SK
end
end
end

end OAI
end

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

theorem massFromAtoms_castSucc (n : ℕ) (w : Fin (n+2) → ℝ) (i : Fin n) :
    massFromAtoms (n+1) w i.castSucc = massFromAtoms n (fun j => w j.castSucc) i := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  have h : ¬ n+1 ≤ i.val := by omega
  rw [ite_eq_right h,add_zero]

theorem massFromAtoms_last (n : ℕ) (w : Fin (n+2) → ℝ) :
    massFromAtoms (n+1) w (Fin.last n) = ∑ j : Fin (n+1), w j.castSucc := by
  unfold massFromAtoms
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,show ¬ n+1 ≤ n by omega,ite_false,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left (by omega)]

theorem massFromAtoms_nonneg (n : ℕ) (w : Fin (n+1) → ℝ) (hw : ∀ j, 0 ≤ w j) (i : Fin n) :
    0 ≤ massFromAtoms n w i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hw j
  · exact le_rfl

end SK.Analytic

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

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedBlockMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem weightedBlockAtom_nonneg (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (t : Fin (blockDimension D N k+1)) :
    0  ≤  weightedBlockAtom D N k w t := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact hw b
  · exact le_rfl

theorem weightedBlockMass_eq_sum (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (i : Fin (blockDimension D N k)) :
    weightedBlockMass D N k w i=∑ b : Fin (k+1),
      if (blockLevel D N k b).val ≤ i.val then w b else 0 := by
  unfold weightedBlockMass massFromAtoms weightedBlockAtom
  calc
    _ = ∑ t : Fin (blockDimension D N k+1), ∑ b : Fin (k+1),
      if blockLevel D N k b=t then (if t.val ≤ i.val then w b else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases ht : t.val ≤ i.val <;> simp only [ht,ite_true,ite_false,ite_self,Finset.sum_const_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

theorem weightedBlockMass_at_disorder (D N k : ℕ) (w : Fin (k+1) → ℝ) (i : Fin D) :
    weightedBlockMass D N k w (Fin.castAdd ((k+1)*N) i)=0 := by
  rw [weightedBlockMass_eq_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [ite_eq_right]
  simp only [blockLevel_val,Fin.val_castAdd]
  omega

theorem weightedBlockMass_at_field (D N k : ℕ) (w : Fin (k+1) → ℝ)
    (b : Fin (k+1)) (i : Fin N) :
    weightedBlockMass D N k w (fieldIndex D N k b i)=∑ l, if l<b then w l else 0 := by
  rw [weightedBlockMass_eq_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hh : (blockLevel D N k l).val ≤ (fieldIndex D N k b i).val ↔ l<b := by
    simp only [blockLevel_val,fieldIndex_val,Fin.lt_def]
    constructor
    · intro h
      by_contra hn
      have hl : b.val ≤ l.val := by omega
      have hl' := Nat.mul_le_mul_right N hl
      nlinarith [i.isLt]
    · intro h
      have hl := Nat.mul_le_mul_right N h
      nlinarith
  simp only [hh]

end SK.Analytic

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

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem blockObservable_endpoint_one {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (s : S) (z : ParameterSpace (blockDimension D N k)) :
    observableExponent (blockDimension D N k) (blockObservable H F)
      (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1) s z=
      ∑ i, H i s*coordinateProjection (blockDimension D N k) (Fin.castAdd ((k+1)*N) i) z := by
  rw [observableExponent,coordinateLinear_apply,Fin.sum_univ_add]
  simp only [interpolationCoefficient,blockInterpolationChoice,blockObservable,Fin.addCases_left,
    Fin.addCases_right,ite_true,Bool.false_eq_true,ite_false,sub_self,Real.sqrt_zero,Real.sqrt_one,
    one_mul,zero_mul,Finset.sum_const_zero,add_zero]

omit [Fintype S] [Nonempty S] in
theorem blockObservable_endpoint_zero {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (s : S) (z : ParameterSpace (blockDimension D N k)) :
    observableExponent (blockDimension D N k) (blockObservable H F)
      (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 0) s z=
      ∑ b, ∑ i, F b i s*coordinateProjection (blockDimension D N k) (fieldIndex D N k b i) z := by
  rw [observableExponent,coordinateLinear_apply,Fin.sum_univ_add]
  simp only [interpolationCoefficient,blockInterpolationChoice,blockObservable,Fin.addCases_left,
    Fin.addCases_right,ite_true,Bool.false_eq_true,ite_false,sub_zero,Real.sqrt_zero,Real.sqrt_one,
    one_mul,zero_mul,Finset.sum_const_zero,zero_add]
  rw [← finProdFinEquiv.sum_comp (fun t : Fin ((k+1)*N) =>
    F (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 s*
      coordinateProjection (blockDimension D N k) (Fin.natAdd D t) z)]
  simp only [Equiv.symm_apply_apply,Fintype.sum_prod_type,fieldIndex_eq_natAdd]

theorem blockObservable_root_one {D N k : ℕ} (H : Fin D → S → ℝ)
    (F : Fin (k+1) → Fin N → S → ℝ) (c : S → ℝ) (w : Fin (k+1) → ℝ) :
    hierarchyPressure (blockDimension D N k) (weightedBlockMass D N k w)
      (affineLogPartition c (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1))) 0=
      ∫ z, affineLogPartition c (fun s => coordinateLinear D (fun i => H i s)) z ∂fiberGaussian D 0 := by
  rw [hierarchyPressure_split]
  have he : (fun z => affineLogPartition c
      (observableExponent (blockDimension D N k) (blockObservable H F)
        (interpolationCoefficient (blockDimension D N k) (blockInterpolationChoice D N k) 1))
          (parameterAppend D ((k+1)*N) z))=
      fun z => affineLogPartition c (fun s => coordinateLinear D (fun i => H i s))
        (cascadeRoot (E:=ParameterSpace D) ((k+1)*N) z) := by
    funext z
    simp only [affineLogPartition,blockObservable_endpoint_one,coordinateProjection_append_prefix,
      coordinateLinear_apply]
  rw [he,cascadePressure_root]
  simp only [weightedBlockMass_at_disorder]
  exact hierarchyPressure_zero D _ (affineLogPartition_boundedDerivs _ _) 0
end
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockSiteEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem blockSiteEmbedding_apply (D N r k : ℕ) (i : Fin N) (b : Fin (k+1)) (u : Fin r) :
    blockSiteEmbedding D N r k i (finProdFinEquiv (b,u))=
      fieldIndex D (N*r) k b (finProdFinEquiv (i,u)) := by
  simp only [blockSiteEmbedding,Equiv.symm_apply_apply]

theorem blockSiteEmbedding_strictMono (D N r k : ℕ) (i : Fin N) :
    StrictMono (blockSiteEmbedding D N r k i) := by
  intro a b hab
  obtain ⟨⟨ba,ua⟩,rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨bb,ub⟩,rfl⟩ := finProdFinEquiv.surjective b
  rw [blockSiteEmbedding_apply,blockSiteEmbedding_apply]
  change D+ba.val*(N*r)+(ua.val+r*i.val)<D+bb.val*(N*r)+(ub.val+r*i.val)
  change ua.val+r*ba.val<ub.val+r*bb.val at hab
  have hN : 0<N := Nat.zero_lt_of_lt i.isLt
  have hba : ba.val ≤ bb.val := by
    by_contra h
    have hmul := Nat.mul_le_mul_left r (show bb.val+1 ≤ ba.val by omega)
    nlinarith [ub.isLt]
  by_cases he : ba.val=bb.val
  · rw [he] at hab ⊢
    omega
  · have hmul := Nat.mul_le_mul_right (N*r) (show ba.val+1 ≤ bb.val by omega)
    have hrN : r ≤ N*r := Nat.le_mul_of_pos_left r hN
    nlinarith [ua.isLt]

theorem blockSiteOwner_embedding {D N r k : ℕ} (i₀ i : Fin N) (j : Fin ((k+1)*r)) :
    blockSiteOwner (D:=D) (r:=r) (k:=k) i₀ (blockSiteEmbedding D N r k i j)=i := by
  unfold blockSiteEmbedding
  rw [fieldIndex_eq_natAdd]
  simp only [blockSiteOwner,Fin.addCases_right,Equiv.symm_apply_apply]

theorem blockSiteEmbedding_mass (D N r k : ℕ) (w : Fin (k+1) → ℝ)
    (i : Fin N) (j : Fin ((k+1)*r)) :
    weightedBlockMass D (N*r) k w (blockSiteEmbedding D N r k i j)=siteBlockMass r k w j := by
  exact weightedBlockMass_at_field D (N*r) k w _ _

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Interpolation_FinitePressureAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_mono (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, 0  ≤  m i)
    {f g : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g)
    (hfg : ∀ z, f z ≤ g z) (x : ℝ) : hierarchyPressure n m f x ≤ hierarchyPressure n m g x := by
  induction n with
  | zero => exact hfg x
  | succ n ih =>
    exact ih (fun i => m i.castSucc) (fun i => hm i.castSucc)
      (hf.gaussianStep _) (hg.gaussianStep _)
      (fun z => gaussianStep_mono hf hg (hm (Fin.last n)) hfg z)

theorem hierarchyPressure_add_const (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) (c : ℝ) :
    hierarchyPressure n m (fun z => f z+c)=fun x => hierarchyPressure n m f x+c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hierarchyPressure,gaussianStep_add_prefix hf (fun _ => c)]
    exact ih _ (hf.gaussianStep _)

section Terminal
variable {E A T : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype A] [Nonempty A] [Fintype T] [Nonempty T]

theorem affineLogPartition_const_weight (c : ℝ) (L : A → E →L[ℝ] ℝ) :
    affineLogPartition (fun _ => c) L=fun z => affineLogPartition (fun _ => 0) L z+c := by
  funext z
  simp only [affineLogPartition,zero_add,Real.exp_add,← Finset.mul_sum]
  rw [Real.log_mul (Real.exp_ne_zero _) (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne',Real.log_exp]
  ring

omit [Nonempty A] in
theorem affineLogPartition_restrict (e : T → A) (he : Function.Injective e)
    (c : A → ℝ) (L : A → E →L[ℝ] ℝ) (z : E) :
    affineLogPartition (c ∘ e) (L ∘ e) z ≤ affineLogPartition c L z := by
  unfold affineLogPartition
  apply Real.log_le_log (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty)
  classical
  change (∑ t : T, (fun a => Real.exp (c a+L a z)) (e t)) ≤ ∑ a : A, Real.exp (c a+L a z)
  rw [← Finset.sum_image (s:=Finset.univ) (f:=fun a => Real.exp (c a+L a z)) (g:=e)
    (fun a _ b _ h => he h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)

theorem affineLogPartition_product (N : ℕ) (c : Fin N → A → ℝ)
    (L : Fin N → A → E →L[ℝ] ℝ) :
    affineLogPartition (fun s : Fin N → A => ∑ i, c i (s i)) (fun s => ∑ i, L i (s i))=
      fun z => ∑ i, affineLogPartition (c i) (L i) z := by
  funext z
  simp only [affineLogPartition,sum_apply,← Finset.sum_add_distrib,Real.exp_sum]
  rw [← Fintype.prod_sum (fun i a => Real.exp (c i a+L i a z)),Real.log_prod]
  intro i _
  exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
end Terminal

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hierarchyPressure_vector_linear (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f : E → ℝ) (c : ℝ → E) :
    hierarchyPressure n m (fun z => f (c (parameter n z)+∑ j, coordinateProjection n j z • v j))=
      fun x => vectorHierarchy n m v f (c x) := by
  induction n generalizing f with
  | zero => simp [hierarchyPressure,vectorHierarchy,parameter]
  | succ n ih =>
    have he : (fun z : ParameterSpace (n+1) =>
        f (c (parameter (n+1) z)+∑ j, coordinateProjection (n+1) j z • v j))=
        fun z => f ((c (parameter n z.1)+∑ j : Fin n, coordinateProjection n j z.1 • v j.castSucc)+
          z.2 • v (Fin.last n)) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he,hierarchyPressure]
    change hierarchyPressure n (fun j => m j.castSucc)
      (fun z => vectorStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))=_
    rw [ih]
    rfl

theorem vectorHierarchy_compress (n : ℕ) {r : ℕ} (e : Fin r → Fin n)
    (he : StrictMono e) (m : Fin n → ℝ) (v : Fin n → E)
    (hv : ∀ t, (∀ j, e j ≠ t) → v t = 0) (f : E → ℝ) :
    vectorHierarchy n m v f = vectorHierarchy r (m ∘ e) (v ∘ e) f := by
  induction n generalizing r f with
  | zero =>
    cases r with
    | zero => rfl
    | succ r => exact Fin.elim0 (e 0)
  | succ n ih =>
    cases r with
    | zero =>
      have hlast : v (Fin.last n) = 0 := hv _ (fun j => Fin.elim0 j)
      simp only [vectorHierarchy,hlast,vectorStep_zero]
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
        rw [vectorHierarchy,vectorHierarchy,← hlast]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv'
          (vectorStep (m (e (Fin.last r))) (v (e (Fin.last r))) f)
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
        rw [vectorHierarchy,hzero,vectorStep_zero]
        have H := ih e' he' (fun i => m i.castSucc) (fun i => v i.castSucc) hv' f
        simpa only [Function.comp_def,hcast] using H
end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_EmbeddedSites
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {A : Type} [Fintype A] [Nonempty A]

omit [Fintype A] [Nonempty A] in
theorem embeddedVector_at {n r : ℕ} (e : Fin r → Fin n) (he : Function.Injective e)
    (V : Fin r → A → ℝ) (j : Fin r) : embeddedVector e V (e j)=V j := by
  classical
  simp only [embeddedVector,he.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

omit [Fintype A] [Nonempty A] in
theorem embeddedVector_off {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (t : Fin n) (ht : ∀ j, e j≠t) : embeddedVector e V t=0 := by
  simp only [embeddedVector,ht,ite_false,Finset.sum_const_zero]

omit [Nonempty A] in
theorem embeddedSite_terminal {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (c : A → ℝ) :
    affineLogPartition c (embeddedSiteExponent e V)=fun z =>
      siteValueTerminal c (0+∑ t, coordinateProjection n t z • embeddedVector e V t) := by
  classical
  funext z
  simp only [affineLogPartition,embeddedSiteExponent,siteValueTerminal,sum_apply,smul_apply,
    smul_eq_mul,zero_add,ContinuousLinearMap.proj_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,embeddedVector,Finset.mul_sum,
    Finset.sum_apply,ite_apply,Pi.zero_apply,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Nonempty A] in

theorem embeddedSite_pressure {n r : ℕ} (e : Fin r → Fin n) (he : StrictMono e)
    (m : Fin n → ℝ) (V : Fin r → A → ℝ) (c : A → ℝ) (x : ℝ) :
    hierarchyPressure n m (affineLogPartition c (embeddedSiteExponent e V)) x=
      vectorHierarchy r (m ∘ e) V (siteValueTerminal c) 0 := by
  rw [embeddedSite_terminal,hierarchyPressure_vector_linear n m (embeddedVector e V) (siteValueTerminal c) (fun _ => 0)]
  rw [vectorHierarchy_compress n e he m (embeddedVector e V)
    (embeddedVector_off e V) (siteValueTerminal c)]
  have hV : embeddedVector e V ∘ e=V := by
    funext j
    exact embeddedVector_at e he.injective V j
  rw [hV]

omit [Nonempty A] in
theorem embeddedSite_invariant {n r : ℕ} (e : Fin r → Fin n) (V : Fin r → A → ℝ)
    (c : A → ℝ) (t : Fin n) (ht : ∀ j, e j≠t) :
    TranslationInvariant (affineLogPartition c (embeddedSiteExponent e V)) (coordinateAxis n t) := by
  apply affineLogPartition_translation
  intro a
  simp only [embeddedSiteExponent,sum_apply,smul_apply,smul_eq_mul,
    coordinateProjection_coordinateAxis,ht,ite_false,mul_zero,Finset.sum_const_zero]

theorem embeddedSites_tensorizes {I : Type} [Fintype I] [DecidableEq I]
    {n r : ℕ} (e : I → Fin r → Fin n) (he : ∀ i, StrictMono (e i))
    (owner : Fin n → I) (howner : ∀ i j, owner (e i j)=i)
    (m : Fin n → ℝ) (μ : Fin r → ℝ) (hm : ∀ i j, m (e i j)=μ j)
    (V : Fin r → A → ℝ) (c : A → ℝ) (x : ℝ) :
    hierarchyPressure n m
      (affineLogPartition (fun s : I → A => ∑ i, c (s i))
        (fun s => ∑ i, embeddedSiteExponent (e i) V (s i))) x=
      (Fintype.card I:ℝ)*vectorHierarchy r μ V (siteValueTerminal c) 0 := by
  have hterm : affineLogPartition (fun s : I → A => ∑ i, c (s i))
      (fun s => ∑ i, embeddedSiteExponent (e i) V (s i))=
      fun z => ∑ i, affineLogPartition c (embeddedSiteExponent (e i) V) z := by
    funext z
    simp only [affineLogPartition,sum_apply,← Finset.sum_add_distrib,Real.exp_sum]
    rw [← Fintype.prod_sum (fun i a => Real.exp (c a+embeddedSiteExponent (e i) V a z)),Real.log_prod]
    intro i _
    exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  rw [hterm,hierarchyPressure_sum_independent n m owner _
    (fun i => affineLogPartition_boundedDerivs c (embeddedSiteExponent (e i) V))
    (fun t i hi => embeddedSite_invariant (e i) V c t (fun j ht => by
      apply hi
      rw [← ht,howner]))]
  simp_rw [embeddedSite_pressure _ (he _) m V c x]
  have heq (i : I) : m ∘ e i=μ := funext (hm i)
  simp only [heq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_BlockSiteFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]

omit [Fintype A] [Nonempty A] [Fintype S] [Nonempty S] in
theorem siteBlock_fields_sum {D N r k : ℕ} (V : Fin ((k+1)*r) → A → ℝ)
    (s : Fin N → A) (z : ParameterSpace (blockDimension D (N*r) k)) :
    (∑ b, ∑ p, siteBlockObservables V b p s*
      coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b p) z)=
      (∑ i, embeddedSiteExponent (blockSiteEmbedding D N r k i) V (s i)) z := by
  simp only [sum_apply,embeddedSiteExponent,smul_apply,smul_eq_mul]
  have he (b : Fin (k+1)) : (∑ p, siteBlockObservables V b p s*
      coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b p) z)=
      ∑ i, ∑ u, V (finProdFinEquiv (b,u)) (s i)*
        coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b (finProdFinEquiv (i,u))) z := by
    rw [← finProdFinEquiv.sum_comp (fun p : Fin (N*r) => siteBlockObservables V b p s*
      coordinateProjection (blockDimension D (N*r) k) (fieldIndex D (N*r) k b p) z)]
    simp only [siteBlockObservables,Equiv.symm_apply_apply,Fintype.sum_prod_type]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← finProdFinEquiv.sum_comp (fun j : Fin ((k+1)*r) =>
    V j (s i)*coordinateProjection (blockDimension D (N*r) k) (blockSiteEmbedding D N r k i j) z)]
  simp only [Fintype.sum_prod_type,blockSiteEmbedding_apply]

theorem siteBlock_root_zero_le {D N r k : ℕ} (hN : 0<N)
    (e : S → Fin N → A) (he : Function.Injective e)
    (H : Fin D → S → ℝ) (V : Fin ((k+1)*r) → A → ℝ)
    (c : A → ℝ) (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) :
    hierarchyPressure (blockDimension D (N*r) k) (weightedBlockMass D (N*r) k w)
      (affineLogPartition (fun s => ∑ i, c (e s i))
        (observableExponent (blockDimension D (N*r) k)
          (blockObservable H (fun b p s => siteBlockObservables V b p (e s)))
          (interpolationCoefficient (blockDimension D (N*r) k) (blockInterpolationChoice D (N*r) k) 0))) 0 ≤
      (N:ℝ)*vectorHierarchy ((k+1)*r) (siteBlockMass r k w) V (siteValueTerminal c) 0 := by
  let L : (Fin N → A) → ParameterSpace (blockDimension D (N*r) k) →L[ℝ] ℝ :=
    fun s => ∑ i, embeddedSiteExponent (blockSiteEmbedding D N r k i) V (s i)
  have hL : observableExponent (blockDimension D (N*r) k)
      (blockObservable H (fun b p s => siteBlockObservables V b p (e s)))
      (interpolationCoefficient (blockDimension D (N*r) k) (blockInterpolationChoice D (N*r) k) 0)=L ∘ e := by
    funext s
    ext z
    rw [blockObservable_endpoint_zero]
    exact siteBlock_fields_sum V (e s) z
  rw [hL]
  have hmon := hierarchyPressure_mono (blockDimension D (N*r) k) (weightedBlockMass D (N*r) k w)
    (fun i => massFromAtoms_nonneg _ _ (weightedBlockAtom_nonneg D (N*r) k w hw) i)
    (affineLogPartition_boundedDerivs (fun s => ∑ i, c (e s i)) (L ∘ e))
    (affineLogPartition_boundedDerivs (fun s : Fin N → A => ∑ i, c (s i)) L)
    (fun z => affineLogPartition_restrict e he (fun s : Fin N → A => ∑ i, c (s i)) L z) 0
  have ht := embeddedSites_tensorizes (fun i => blockSiteEmbedding D N r k i)
    (fun i => blockSiteEmbedding_strictMono D N r k i)
    (blockSiteOwner (D:=D) (r:=r) (k:=k) ⟨0,hN⟩)
    (fun i j => blockSiteOwner_embedding ⟨0,hN⟩ i j)
    (weightedBlockMass D (N*r) k w) (siteBlockMass r k w)
    (fun i j => blockSiteEmbedding_mass D N r k w i j) V c 0
  exact hmon.trans_eq (by simpa only [Fintype.card_fin,L] using ht)
end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_HierarchyMassPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem massFromAtoms_hierarchyAtom (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (i : Fin n) :
    massFromAtoms n (hierarchyAtom n m u) i=m i := by
  induction n generalizing u with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [massFromAtoms_last]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact hierarchyAtom_sum n _ _
    · rw [massFromAtoms_castSucc]
      simp only [hierarchyAtom,Fin.lastCases_castSucc]
      exact ih _ _ j

theorem zeroInitialAtoms_prefix (k : ℕ) (m : Fin (k+1) → ℝ) (hm : m 0=0)
    (b : Fin (k+1)) : (∑ l, if l<b then zeroInitialAtoms k m l else 0)=m b := by
  refine Fin.cases ?_ (fun i => ?_) b
  · simpa using hm.symm
  · simpa only [massFromAtoms,zeroInitialAtoms,Fin.lt_def,Fin.val_succ,Nat.lt_add_one_iff] using
      massFromAtoms_hierarchyAtom k (fun i => m i.succ) 1 i

theorem siteBlockMass_zeroInitial {k r : ℕ} (m : Fin (k+1) → ℝ) (hm : m 0=0)
    (j : Fin ((k+1)*r)) : siteBlockMass r k (zeroInitialAtoms k m) j=m (finProdFinEquiv.symm j).1 :=
  zeroInitialAtoms_prefix k m hm _

theorem zeroInitialAtoms_nonneg {k : ℕ} (m : Fin (k+1) → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m) (j : Fin (k+1)) :
    0≤zeroInitialAtoms k m j :=
  hierarchyAtom_nonneg k _ (by norm_num) (fun i => (hm i.succ).1)
    (fun i => (hm i.succ).2) (fun _ _ h => hmono (Fin.succ_le_succ_iff.mpr h)) j

theorem zeroInitialAtoms_sum {k : ℕ} (m : Fin (k+1) → ℝ) :
    ∑ j, zeroInitialAtoms k m j=1 := hierarchyAtom_sum k _ 1

end SK.Analytic

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

@[simp] theorem fieldOwner_field {D N k : ℕ} (i₀ : Fin N) (b : Fin (k+1)) (i : Fin N) :
    fieldOwner i₀ (fieldIndex D N k b i) = i := by
  rw [fieldIndex_eq_natAdd]
  unfold fieldOwner
  rw [Fin.addCases_right]
  rw [Equiv.symm_apply_apply]

end SK.Analytic

end
end

end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorHierarchy_split (a b : ℕ) (m : Fin (a+b) → ℝ) (v : Fin (a+b) → E) (f : E → ℝ) :
    vectorHierarchy (a+b) m v f=
      vectorHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorStep_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f : F → ℝ) :
    vectorStep m v (f ∘ L)=vectorStep m (L v) f ∘ L := by
  funext x
  simp only [vectorStep,Function.comp_def,map_add,map_smul]
  rfl

theorem vectorHierarchy_pullback (L : E →L[ℝ] F) (n : ℕ) (m : Fin n → ℝ)
    (v : Fin n → E) (f : F → ℝ) :
    vectorHierarchy n m v (f ∘ L)=vectorHierarchy n m (L ∘ v) f ∘ L := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchy,vectorStep_pullback,ih]
    rfl

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_VectorBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorIncrementChain_append (l r : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain (l++r) f=vectorIncrementChain l (vectorIncrementChain r f) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementChain,ih]

theorem vectorIncrementChain_ofFn (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f : E → ℝ) :
    vectorIncrementChain (List.ofFn (fun i => (m i,v i))) f=vectorHierarchy n m v f := by
  induction n generalizing f with
  | zero => simp [vectorIncrementChain,vectorHierarchy]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,vectorIncrementChain_append]
    exact ih _ _ _

end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixGuerraKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem matrixSquare_sub (d : ℕ) (R Q : Fin d → Fin d → ℝ) :
    matrixSquare d (fun a b => R a b-Q a b)=matrixSquare d R-2*matrixInner d Q R+matrixSquare d Q := by
  simp only [matrixSquare,matrixInner,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixGuerraEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {A S : Type} [Fintype A] [Nonempty A] [Fintype S] [Nonempty S]

omit [Fintype A] [Nonempty A] [Fintype S] [Nonempty S] in
theorem matrixSiteWeight_sum {N d : ℕ} (Λ : Fin d → Fin d → ℝ) (v : A → Fin d → ℝ)
    (e : S → Fin N → A) (s : S) :
    (∑ i, matrixSiteWeight Λ v (e s i))=(N:ℝ)*matrixInner d Λ (replicaCrossOverlap N d (fun i => v (e s i)) (fun i => v (e s i))) := by
  by_cases hN : N=0
  · subst N; simp
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN
  simp only [matrixSiteWeight,matrixInner,replicaCrossOverlap,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  field_simp [hNr]

omit [Fintype A] [Nonempty A] [Fintype S] [Nonempty S] in
theorem matrixSiteVector_observables {N d r k : ℕ} (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (v : A → Fin d → ℝ) (e : S → Fin N → A) :
    matrixFieldObservables N d r k β B (fun s i => v (e s i))=
      fun b p s => siteBlockObservables (matrixSiteVector β B v) b p (e s) := by
  funext b p s
  simp only [matrixFieldObservables,matrixFieldFeature,siteBlockObservables,matrixSiteVector,
    Equiv.symm_apply_apply]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixSKCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem matrixSKObservables_covariance {S : Type} {N d : ℕ} (hN : 0<N) (β : ℝ)
    (e : S → Fin N → Config d) (s t : S) :
    (∑ u, matrixSKObservables N d β e u s*matrixSKObservables N d β e u t)=
      ((N:ℝ)*β^2/2)*(∑ a, ∑ b,
        (replicaCrossOverlap N d (fun i a => spin (e s i a)) (fun i a => spin (e t i a)) a b)^2)-
          β^2*(d:ℝ)^2/2 := by
  have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hb : (β/Real.sqrt (N:ℝ))^2=β^2/(N:ℝ) := by
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  have hp (a b : Fin d) :
      (∑ p : Edge N, (spin (e s p.val.1 a)*spin (e s p.val.2 a))*
        (spin (e t p.val.1 b)*spin (e t p.val.2 b)))=
      ((∑ i, spin (e s i a)*spin (e t i b))^2-(N:ℝ))/2 := by
    have H := sum_sq_eq_edges (fun i => spin (e s i a)*spin (e t i b))
    simp only [mul_pow,spin_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at H
    have he (p : Edge N) :
        (spin (e s p.val.1 a)*spin (e t p.val.1 b))*(spin (e s p.val.2 a)*spin (e t p.val.2 b))=
        (spin (e s p.val.1 a)*spin (e s p.val.2 a))*(spin (e t p.val.1 b)*spin (e t p.val.2 b)) := by ring
    simp_rw [he] at H
    linarith
  simp only [matrixSKObservables]
  rw [← (Fintype.equivFin (Edge N)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  have he (p : Edge N) :
    (β/Real.sqrt (N:ℝ)*(∑ a, spin (e s p.val.1 a)*spin (e s p.val.2 a)))*
      (β/Real.sqrt (N:ℝ)*(∑ b, spin (e t p.val.1 b)*spin (e t p.val.2 b)))=
        (β^2/(N:ℝ))*((∑ a, spin (e s p.val.1 a)*spin (e s p.val.2 a))*
          (∑ b, spin (e t p.val.1 b)*spin (e t p.val.2 b))) := by rw [← hb]; ring
  simp_rw [he,← Finset.mul_sum,Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (p : Edge N) (b : Fin d) => _)]
  simp_rw [hp,sub_div,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [replicaCrossOverlap,div_pow,← Finset.sum_div]
  field_simp

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem matrixSKObservables_exponent {S : Type} (N d : ℕ) (β : ℝ)
    (e : S → Fin N → Config d) (s : S) (z : ParameterSpace (Fintype.card (Edge N))) :
    coordinateLinear (Fintype.card (Edge N)) (fun u => matrixSKObservables N d β e u s) z=
      β*∑ a, hamiltonian (enumeratedDisorder N z) (fun i => e s i a) := by
  simp only [coordinateLinear_apply,matrixSKObservables,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  convert spinExponent_sk_eq N β (fun i => e s i a) z using 1
  all_goals try with_reducible_and_instances rfl
  simp only [spinExponent,coordinateLinear_apply,spinMonomial_skInteraction]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixSKGuerra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {S : Type} [Fintype S] [Nonempty S]

theorem matrixSKLogPartition_continuous (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) :
    Continuous (matrixSKLogPartition N d β e) := by
  apply Continuous.log
    (continuous_finsetSum _ (fun s _ => Real.continuous_exp.comp
      (continuous_const.mul (continuous_finsetSum _ (fun a _ => continuous_hamiltonian (fun i => e s i a))))))
  intro J
  exact (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

theorem matrixSKQuenched_endpoint (N d : ℕ) (β : ℝ) (e : S → Fin N → Config d) :
    (∫ z, affineLogPartition (fun _ : S => 0)
      (fun s => coordinateLinear (Fintype.card (Edge N)) (fun u => matrixSKObservables N d β e u s))
      z ∂fiberGaussian (Fintype.card (Edge N)) 0)=
        ∫ J, matrixSKLogPartition N d β e J ∂disorderLaw N := by
  simp only [affineLogPartition,matrixSKObservables_exponent,zero_add]
  change (∫ z, matrixSKLogPartition N d β e (enumeratedDisorder N z) ∂_)=_
  have H := enumeratedDisorder_measurePreserving N 0
  rw [← H.map_eq,integral_map H.measurable.aemeasurable (matrixSKLogPartition_continuous N d β e).aestronglyMeasurable]

theorem matrixSKGuerra {N d r k : ℕ} (hN : 0<N) (hr : 0 < r) (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (e : S → Fin N → Config d) (he : Function.Injective e)
    (D Λ : Fin d → Fin d → ℝ)
    (hself : ∀ s, replicaCrossOverlap N d (fun i a => spin (e s i a)) (fun i a => spin (e s i a))=D)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    (∫ J, matrixSKLogPartition N d β e J ∂disorderLaw N)/(N:ℝ) ≤
      vectorHierarchy ((k+1)*r) (siteBlockMass r k w) (matrixSiteVector β B (fun (a : Config d) u => spin (a u)))
        (siteValueTerminal (matrixSiteWeight Λ (fun (a : Config d) u => spin (a u)))) 0 - matrixInner d Λ D+
        (β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
          ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let v : Config d → Fin d → ℝ := fun a u => spin (a u)
  let X : S → Fin N → Fin d → ℝ := fun s i => v (e s i)
  let c : S → ℝ := fun s => ∑ i, matrixSiteWeight Λ v (e s i)
  let M:=Fintype.card (Edge N)
  let n:=blockDimension M (N*r) k
  let H:=matrixSKObservables N d β e
  let F:=matrixFieldObservables N d r k β B X
  let m:=weightedBlockMass M (N*r) k w
  let I:=blockInterpolationChoice M (N*r) k
  have hc : c=fun _ => (N:ℝ)*matrixInner d Λ D := by
    funext s
    rw [show c s=∑ i, matrixSiteWeight Λ v (e s i) from rfl,matrixSiteWeight_sum,hself s]
  have hinter := matrixFiniteInterpolation_offset hN hr β B X H (β^2*(d:ℝ)^2/2)
    (matrixSKObservables_covariance hN β e) D hself c w hw hs
  change hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
    (interpolationCoefficient n I 1))) 0 ≤ _ at hinter
  rw [hc,affineLogPartition_const_weight,hierarchyPressure_add_const n m
    (affineLogPartition_boundedDerivs (fun _ : S => 0) _) ((N:ℝ)*matrixInner d Λ D)] at hinter
  dsimp only at hinter
  rw [blockObservable_root_one,matrixSKQuenched_endpoint] at hinter
  have hz := siteBlock_root_zero_le hN e he H (matrixSiteVector β B v) (matrixSiteWeight Λ v) w hw
  rw [← matrixSiteVector_observables] at hz
  change hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
    (interpolationCoefficient n I 0))) 0 ≤ _ at hz
  rw [hc] at hz
  have htotal := hinter.trans (add_le_add hz le_rfl)
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ hNr).2
  dsimp only [X,H,c,n,m,I,F,M,v] at htotal ⊢
  nlinarith

theorem matrixConstrainedPressure_le {N d r k : ℕ} (hN : 0<N) (hr : 0 < r) (β : ℝ)
    (D Λ : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    matrixConstrainedPressure N d β D ≤
      vectorHierarchy ((k+1)*r) (siteBlockMass r k w) (matrixSiteVector β B (fun (a : Config d) u => spin (a u)))
        (siteValueTerminal (matrixSiteWeight Λ (fun (a : Config d) u => spin (a u)))) 0 - matrixInner d Λ D+
        (β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
          ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  let := hD
  exact matrixSKGuerra hN hr β B (fun s : MatrixStates N d D => s.val) Subtype.val_injective
    D Λ (fun s => s.property) w hw hs

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorHierarchy_cast {n r : ℕ} (h : n=r) (m : Fin n → ℝ)
    (v : Fin n → E) (f : E → ℝ) :
    vectorHierarchy n m v f=vectorHierarchy r (fun i => m (Fin.cast h.symm i))
      (fun i => v (Fin.cast h.symm i)) f := by
  subst r; rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem finProd_symm_prefix (n r : ℕ) (i : Fin (n*r)) :
    finProdFinEquiv.symm (Fin.cast (Nat.succ_mul n r).symm (i.castAdd r))=
      ((finProdFinEquiv.symm i).1.castSucc,(finProdFinEquiv.symm i).2) := by
  apply Prod.ext <;> apply Fin.ext <;> rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem finProd_symm_suffix (n r : ℕ) (i : Fin r) :
    finProdFinEquiv.symm (Fin.cast (Nat.succ_mul n r).symm (i.natAdd (n*r)))=(Fin.last n,i) := by
  apply finProdFinEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change n*r+i.val=i.val+r*n
  ring

theorem vectorHierarchy_blocks (n r : ℕ) (m : Fin n → ℝ) (v : Fin n → Fin r → E) (f : E → ℝ) :
    vectorHierarchy (n*r) (fun i => m (finProdFinEquiv.symm i).1)
      (fun i => v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) f=
      vectorBlockHierarchy r n m v f := by
  induction n generalizing f with
  | zero => rw [vectorHierarchy_cast (Nat.zero_mul r)]; rfl
  | succ n ih =>
    rw [vectorHierarchy_cast (Nat.succ_mul n r),vectorHierarchy_split]
    simp only [finProd_symm_prefix,finProd_symm_suffix]
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc) _

end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_SpinGlass_FinitePrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem finitePrefix_succ (n : ℕ) (v : Fin (n+1) → ℝ) (i : Fin n) :
    finitePrefix v i.succ=finitePrefix v i.castSucc+v i.succ := by
  have H (l : Fin (n+1)) : (if l ≤ i.succ then v l else 0)=
      (if l ≤ i.castSucc then v l else 0)+(if l=i.succ then v l else 0) := by
    by_cases h : l=i.succ
    · subst l
      rw [ite_eq_left le_rfl,ite_eq_right (by simp),ite_eq_left rfl,zero_add]
    · have hle : l ≤ i.succ ↔ l ≤ i.castSucc := by
        have hn : l.val ≠ i.val+1 := by simpa only [Fin.val_succ] using Fin.val_ne_of_ne h
        simp only [Fin.le_def,Fin.val_succ,Fin.val_castSucc]
        omega
      simp only [ite_eq_right h,add_zero,hle]
  simp only [finitePrefix,H,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem hierarchyAtom_sum_mul_parts (n : ℕ) (m : Fin n → ℝ) (u : ℝ) (v : Fin (n+1) → ℝ) :
    (∑ j, hierarchyAtom n m u j*v j)=u*v (Fin.last n)-∑ i, m i*(v i.succ-v i.castSucc) := by
  induction n generalizing u with
  | zero => simp [hierarchyAtom]
  | succ n ih =>
    conv_lhs => rw [Fin.sum_univ_castSucc]
    simp only [hierarchyAtom,Fin.lastCases_castSucc,Fin.lastCases_last]
    rw [ih (fun i => m i.castSucc) (m (Fin.last n)) (fun j => v j.castSucc)]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [Fin.castSucc_succ,Fin.succ_last]
    ring

theorem zeroInitialAtoms_sum_mul_parts (n : ℕ) (m v : Fin (n+1) → ℝ) :
    (∑ j, zeroInitialAtoms n m j*v j)=v (Fin.last n)-∑ i : Fin n, m i.succ*(v i.succ-v i.castSucc) := by
  simpa only [zeroInitialAtoms,one_mul] using hierarchyAtom_sum_mul_parts n (fun i => m i.succ) 1 v

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_RankOneMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem replicaSpin_terminal (d : ℕ) :
    siteValueTerminal (fun _ : Config d => 0) ∘ replicaSpinMap d=
      fun x => ∑ i, scalarSpinTerminal (x i) := by
  funext x
  have H := congrFun (affineLogPartition_product d
    (fun (_ : Fin d) (_ : Bool) => (0:ℝ))
    (fun i b => spin b • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ))) x
  simp only [affineLogPartition_bool,ContinuousLinearMap.proj_apply] at H
  simpa only [Function.comp_def,siteValueTerminal,affineLogPartition,
    Finset.sum_const_zero,zero_add,replicaSpinMap_apply,sum_apply,
    smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply,scalarSpinTerminal] using H

section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem vectorBlockHierarchy_one (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f : E → ℝ) :
    vectorBlockHierarchy 1 n m (fun i _ => v i) f=vectorHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    change vectorBlockHierarchy 1 n _ _ (vectorStep (m (Fin.last n)) (v (Fin.last n)) f)=_
    exact ih _ _ _
end Vector

theorem factorPath_rankOne {k : ℕ} (d : ℕ) (b : Fin (k+1) → Fin d → ℝ) (j : Fin (k+1)) :
    factorPath d 1 k (fun i _ => b i) j=rankOnePath d b j := by
  funext u v
  simp [factorPath,factorCovariance,rankOnePath]

theorem rankOne_siteValue {k : ℕ} (d : ℕ) (β : ℝ) (m : Fin (k+1) → ℝ) (hm : m 0=0)
    (b : Fin (k+1) → Fin d → ℝ) :
    vectorHierarchy ((k+1)*1) (siteBlockMass 1 k (zeroInitialAtoms k m))
      (matrixSiteVector β (fun i _ => b i) (fun (s : Config d) u => spin (s u)))
      (siteValueTerminal (fun _ : Config d => 0)) 0=
      vectorHierarchy (k+1) m (fun i => β • b i) (fun x => ∑ u, scalarSpinTerminal (x u)) 0 := by
  rw [funext (siteBlockMass_zeroInitial m hm)]
  have hev : matrixSiteVector β (fun i (_ : Fin 1) => b i) (fun (s : Config d) u => spin (s u))=
      replicaSpinMap d ∘ (fun i => β • b (finProdFinEquiv.symm i).1) := by
    funext i s
    simp only [matrixSiteVector,Function.comp_apply,replicaSpinMap_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hev]
  have H := congrFun (vectorHierarchy_pullback (replicaSpinMap d) ((k+1)*1)
    (fun i => m (finProdFinEquiv.symm i).1)
    (fun i => β • b (finProdFinEquiv.symm i).1)
    (siteValueTerminal (fun _ : Config d => 0))) (0 : Fin d → ℝ)
  simp only [Function.comp_apply,map_zero] at H
  rw [← H,replicaSpin_terminal]
  rw [vectorHierarchy_blocks (k+1) 1 m (fun i _ => β • b i),vectorBlockHierarchy_one]

theorem matrixConstrainedPressure_rankOne {N d k : ℕ} (hN : 0<N) (β : ℝ)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (m : Fin (k+1) → ℝ) (hm0 : m 0=0) (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (b : Fin (k+1) → Fin d → ℝ) :
    matrixConstrainedPressure N d β D ≤
      vectorHierarchy (k+1) m (fun i => β • b i) (fun x => ∑ u,scalarSpinTerminal (x u)) 0+
        β^2/4*matrixSquare d (fun i j => D i j-rankOnePath d b (Fin.last k) i j)-
        β^2/4*∑ i : Fin k,m i.succ*(matrixSquare d (rankOnePath d b i.succ)-
          matrixSquare d (rankOnePath d b i.castSucc)) := by
  have H := matrixConstrainedPressure_le hN (by norm_num : 0<1) β D (fun _ _ => 0) hD
    (fun i (_ : Fin 1) => b i) (zeroInitialAtoms k m)
    (zeroInitialAtoms_nonneg m hm hmono) (zeroInitialAtoms_sum m)
  have hz : matrixSiteWeight (fun (_ _ : Fin d) => (0:ℝ)) (fun (s : Config d) u => spin (s u))=fun _ => 0 := by
    funext s; simp [matrixSiteWeight]
  rw [hz,rankOne_siteValue d β m hm0 b] at H
  simp only [matrixInner,zero_mul,Finset.sum_const_zero,sub_zero] at H
  simp_rw [factorPath_rankOne] at H
  rw [zeroInitialAtoms_sum_mul_parts] at H
  rw [matrixSquare_sub]
  unfold matrixInner
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

section Penalty
variable {E : Type} [AddCommMonoid E]

theorem chainSum_append (l r : List (ℝ × E)) : chainSum (l++r)=chainSum l+chainSum r := by
  simp [chainSum,List.sum_append]

theorem chainPotentialPenalty_append (F : E → ℝ) (l r : List (ℝ × E)) (Q : E) :
    chainPotentialPenalty F (l++r) Q=chainPotentialPenalty F l Q+
      chainPotentialPenalty F r (Q+chainSum l) := by
  induction l generalizing Q with
  | nil => simp [chainPotentialPenalty]
  | cons p l ih => simp only [List.cons_append,chainPotentialPenalty,ih,chainSum_cons,add_assoc]

theorem chainSum_ofFn (n : ℕ) (p : Fin n → ℝ × E) : chainSum (List.ofFn p)=∑ i,(p i).2 := by
  simp [chainSum,List.map_ofFn,List.sum_ofFn,Function.comp_def]

theorem strictPrefix_castSucc {n : ℕ} (v : Fin (n+1) → E) (i : Fin n) :
    strictPrefix v i.castSucc=strictPrefix (fun j => v j.castSucc) i := by
  simp [strictPrefix,Fin.sum_univ_castSucc,not_lt_of_ge (Fin.le_last i.castSucc)]

theorem strictPrefix_last (n : ℕ) (v : Fin (n+1) → E) :
    strictPrefix v (Fin.last n)=∑ j : Fin n,v j.castSucc := by
  simp [strictPrefix,Fin.sum_univ_castSucc]

theorem chainPotentialPenalty_ofFn (n : ℕ) (F : E → ℝ) (p : Fin n → ℝ × E) (Q : E) :
    chainPotentialPenalty F (List.ofFn p) Q=
      ∑ i,(p i).1*(F (Q+strictPrefix (fun j => (p j).2) i+(p i).2)-
        F (Q+strictPrefix (fun j => (p j).2) i)) := by
  induction n with
  | zero => simp [chainPotentialPenalty]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,chainPotentialPenalty_append,ih]
    simp only [chainPotentialPenalty,add_zero,chainSum_ofFn,Fin.sum_univ_castSucc,
      strictPrefix_castSucc,strictPrefix_last]
end Penalty

theorem rankOnePath_cons_castSucc {n d : ℕ} (b : Fin n → Fin d → ℝ) (i : Fin n) :
    rankOnePath d (Fin.cons 0 b) i.castSucc=strictPrefix (fun j => rankOneMatrix (b j)) i := by
  funext u v
  simp only [rankOnePath,strictPrefix,Fin.sum_univ_succ,Fin.cons_zero,Pi.zero_apply,
    zero_mul,ite_self,zero_add,Fin.cons_succ,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have he : j.succ ≤ i.castSucc ↔ j < i := by exact Fin.succ_le_castSucc_iff
  simp only [he]
  split_ifs <;> rfl

theorem rankOnePath_cons_succ {n d : ℕ} (b : Fin n → Fin d → ℝ) (i : Fin n) :
    rankOnePath d (Fin.cons 0 b) i.succ=
      strictPrefix (fun j => rankOneMatrix (b j)) i+rankOneMatrix (b i) := by
  have H : rankOnePath d (Fin.cons 0 b) i.succ=
      rankOnePath d (Fin.cons 0 b) i.castSucc+rankOneMatrix (b i) := by
    funext u v
    let c : Fin (n+1) → Fin d → ℝ := Fin.cons 0 b
    have HH := finitePrefix_succ n (fun j => c j u*c j v) i
    simpa only [rankOnePath,finitePrefix,Pi.add_apply,rankOneMatrix,c,Fin.cons_succ] using HH
  rw [H,rankOnePath_cons_castSucc]

theorem rankOnePath_cons_last {n d : ℕ} (b : Fin n → Fin d → ℝ) :
    rankOnePath d (Fin.cons 0 b) (Fin.last n)=∑ i,rankOneMatrix (b i) := by
  funext u v
  simp only [rankOnePath,Fin.le_last,ite_true,Fin.sum_univ_succ,Fin.cons_zero,
    Pi.zero_apply,zero_mul,zero_add,Fin.cons_succ,Finset.sum_apply,rankOneMatrix]

theorem matrixConstrainedPressure_chain {N d : ℕ} (hN : 0<N) (β : ℝ)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (l : List (ℝ × (Fin d → ℝ))) (hm : ∀ p∈l,p.1∈Icc (0:ℝ) 1)
    (hmono : l.Pairwise (fun p q => p.1≤q.1)) :
    matrixConstrainedPressure N d β D ≤
      vectorIncrementChain (l.map (fun p => (p.1,β • p.2)))
        (fun x => ∑ u,scalarSpinTerminal (x u)) 0+
      β^2/4*matrixSquare d (fun i j => D i j-matrixChainCovariance l i j)-
      β^2/4*matrixChainPenalty l 0 := by
  let m : Fin (l.length+1) → ℝ := Fin.cons 0 (fun i => (l.get i).1)
  let b : Fin (l.length+1) → Fin d → ℝ := Fin.cons 0 (fun i => (l.get i).2)
  have hm' : ∀ i,m i∈Icc (0:ℝ) 1 := by
    intro i
    refine Fin.cases (by norm_num [m]) (fun j => ?_) i
    exact hm _ (List.get_mem l j)
  have hs : Monotone m := by
    have H : ((0,0)::l).Pairwise (fun p q => p.1≤q.1) :=
      List.pairwise_cons.mpr ⟨fun p hp => (hm p hp).1,hmono⟩
    have HL : List.ofFn (Fin.cons (0,0) l.get)=(0,0)::l := by simp [List.ofFn_succ]
    rw [← HL,List.pairwise_ofFn] at H
    intro i j hij
    rcases lt_or_eq_of_le hij with hij|rfl
    · have hh := H hij
      have he (a : Fin (l.length+1)) : m a=((Fin.cons (0,0) l.get : Fin (l.length+1) → ℝ × (Fin d → ℝ)) a).1 := by
        refine Fin.cases rfl (fun _ => rfl) a
      simpa only [← he] using hh
    · exact le_rfl
  have H := matrixConstrainedPressure_rankOne hN β D hD m rfl hm' hs b
  have hv : vectorHierarchy (l.length+1) m (fun i => β • b i)
      (fun x => ∑ u,scalarSpinTerminal (x u))=
      vectorIncrementChain (l.map (fun p => (p.1,β • p.2))) (fun x => ∑ u,scalarSpinTerminal (x u)) := by
    rw [← vectorIncrementChain_ofFn]
    have he : (fun i => (m i,β • b i))=Fin.cons (0,0) (fun i => ((l.get i).1,β • (l.get i).2)) := by
      funext i; refine Fin.cases ?_ (fun _ => rfl) i
      simp [m,b]
    rw [he,List.ofFn_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,vectorIncrementChain,vectorStep_zero]
    congr 1
    simpa only [List.ofFn_get,Function.comp_def] using (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,β • p.2))).symm
  have hc : rankOnePath d b (Fin.last l.length)=matrixChainCovariance l := by
    rw [rankOnePath_cons_last]
    unfold matrixChainCovariance
    have he : l.map (fun p => (p.1,rankOneMatrix p.2))=
        List.ofFn (fun i => ((l.get i).1,rankOneMatrix (l.get i).2)) := by
      simpa only [List.ofFn_get,Function.comp_def] using
        (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,rankOneMatrix p.2)))
    rw [he,chainSum_ofFn]
  have hp : (∑ i : Fin l.length,m i.succ*(matrixSquare d (rankOnePath d b i.succ)-
      matrixSquare d (rankOnePath d b i.castSucc)))=matrixChainPenalty l 0 := by
    unfold matrixChainPenalty
    have he : l.map (fun p => (p.1,rankOneMatrix p.2))=
        List.ofFn (fun i => ((l.get i).1,rankOneMatrix (l.get i).2)) := by
      simpa only [List.ofFn_get,Function.comp_def] using
        (List.map_ofFn (f:=l.get) (g:=fun p => (p.1,rankOneMatrix p.2)))
    rw [he,chainPotentialPenalty_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    simp only [m,Fin.cons_succ,b,rankOnePath_cons_succ,rankOnePath_cons_castSucc,zero_add]
  rw [hv,hc,hp] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ProductMerge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E F : Type}

theorem mergedProductBranches_left (l : List (ℝ × E)) (r : List (ℝ × F)) :
    productLeft (mergedProductBranches l r)=l := by
  induction l generalizing r with
  | nil => simp [mergedProductBranches,productLeft,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedProductBranches,productLeft,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedProductBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [productLeft,List.filterMap_cons]
        exact congrArg (List.cons p) (ih (q::r))
      · simp only [productLeft,List.filterMap_cons]
        exact ihr

theorem mergedProductBranches_right (l : List (ℝ × E)) (r : List (ℝ × F)) :
    productRight (mergedProductBranches l r)=r := by
  induction l generalizing r with
  | nil => simp [mergedProductBranches,productRight,List.filterMap_map]
  | cons p l ih =>
    induction r with
    | nil => simp [mergedProductBranches,productRight,List.filterMap_map]
    | cons q r ihr =>
      unfold mergedProductBranches
      simp only [List.map_cons,List.cons_merge_cons]
      split
      · simp only [productRight,List.filterMap_cons]
        exact ih (q::r)
      · simp only [productRight,List.filterMap_cons]
        exact congrArg (List.cons q) ihr

theorem mergedProductBranches_monotone (l : List (ℝ × E)) (r : List (ℝ × F))
    (hl : l.Pairwise (fun p q => p.1 ≤ q.1))
    (hr : r.Pairwise (fun p q => p.1 ≤ q.1)) :
    (mergedProductBranches l r).Pairwise (fun p q => productMass p ≤ productMass q) := by
  unfold mergedProductBranches
  have hl' : (l.map (Sum.inl : (ℝ × E) → (ProductIncrement (E:=E) (F:=F)))).Pairwise
      (fun p q => productMass p ≤ productMass q) := by simpa [List.pairwise_map,productMass] using hl
  have hr' : (r.map (Sum.inr : (ℝ × F) → (ProductIncrement (E:=E) (F:=F)))).Pairwise
      (fun p q => productMass p ≤ productMass q) := by
    rw [List.pairwise_map]
    exact hr.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  have ht : ∀ a b c : (ProductIncrement (E:=E) (F:=F)),
      decide (productMass a ≤ productMass b) = true →
      decide (productMass b ≤ productMass c) = true →
      decide (productMass a ≤ productMass c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at hab hbc ⊢
    exact le_trans hab hbc
  have htot : ∀ a b : (ProductIncrement (E:=E) (F:=F)),
      (decide (productMass a ≤ productMass b) || decide (productMass b ≤ productMass a)) = true := by
    intro a b
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact le_total _ _
  simpa only [decide_eq_true_eq] using List.pairwise_merge ht htot
    _ _ (by simpa only [decide_eq_true_eq] using hl') (by simpa only [decide_eq_true_eq] using hr')

end Vector
end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TriplePerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem triplePerturbedMatrix_endpoint (r q δ K : ℝ) :
    triplePerturbedMatrix 1 1 r q δ 1 K=
      fun i j => tripleGram r δ q i j+δ^2*K*tripleQuadraticCorrection i j := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triplePerturbedMatrix,tripleSymmetricMatrix,tripleGram,tripleImbalance,tripleQuadraticCorrection] <;> ring

theorem triplePerturbedMatrix_mismatch (β r q δ K : ℝ) :
    β^2/4*matrixSquare 3 (fun i j => tripleGram r δ q i j-
      triplePerturbedMatrix 1 1 r q δ 1 K i j)=β^2*δ^4*K^2 := by
  rw [triplePerturbedMatrix_endpoint]
  norm_num [matrixSquare,tripleQuadraticCorrection,Fin.sum_univ_succ]
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleClockAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleClockMatrix_square (a b c r q : ℝ) :
    matrixSquare 3 (tripleClockMatrix a b c r q)=a^2+b^2+c^2+4*r^2+2*q^2 := by
  norm_num [matrixSquare,tripleClockMatrix,Fin.sum_univ_succ]
  ring

theorem tripleClockPerturbed_square (a b c r q δ g G : ℝ) :
    matrixSquare 3 (tripleClockPerturbed a b c r q δ g G)-
      matrixSquare 3 (tripleClockMatrix a b c r q)=
      4*δ^2*g^2+2*δ^2*G*(b+c-2*q)+4*δ^4*G^2 := by
  norm_num [matrixSquare,tripleClockMatrix,tripleClockPerturbed,tripleImbalance,
    tripleQuadraticCorrection,Fin.sum_univ_succ]
  ring

theorem tripleClockPerturbed_symmetric (a b r q δ g G : ℝ) :
    tripleClockPerturbed a b b r q δ g G=triplePerturbedMatrix a b r q δ g G := rfl

theorem tripleClockPerturbed_singleton (a b c r q δ g G v w : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![v,δ*w,-δ*w] : Fin 3 → ℝ) i*(![v,δ*w,-δ*w] : Fin 3 → ℝ) j)=
      tripleClockPerturbed (a+v^2) b c r q δ (g+v*w) (G+w^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_pair (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![0,v,v] : Fin 3 → ℝ) i*(![0,v,v] : Fin 3 → ℝ) j)=
      tripleClockPerturbed a (b+v^2) (c+v^2) r (q+v^2) δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_tail0 (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![v,0,0] : Fin 3 → ℝ) i*(![v,0,0] : Fin 3 → ℝ) j)=
      tripleClockPerturbed (a+v^2) b c r q δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_tail1 (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![0,v,0] : Fin 3 → ℝ) i*(![0,v,0] : Fin 3 → ℝ) j)=
      tripleClockPerturbed a (b+v^2) c r q δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_tail2 (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![0,0,v] : Fin 3 → ℝ) i*(![0,0,v] : Fin 3 → ℝ) j)=
      tripleClockPerturbed a b (c+v^2) r q δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_common (r v : ℝ) :
    (fun i j => tripleClockMatrix r r r r r i j+
      (![v,v,v] : Fin 3 → ℝ) i*(![v,v,v] : Fin 3 → ℝ) j)=
      tripleClockMatrix (r+v^2) (r+v^2) (r+v^2) (r+v^2) (r+v^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [tripleClockMatrix] <;> ring

theorem tripleClockPerturbed_tail_penalty (a b c r q δ g G m v : ℝ) :
    m*(matrixSquare 3 (tripleClockPerturbed (a+v^2) (b+v^2) (c+v^2) r q δ g G)-
      matrixSquare 3 (tripleClockPerturbed a b c r q δ g G))=
    m*((a+v^2)^2-a^2+(b+v^2)^2-b^2+(c+v^2)^2-c^2)+4*m*δ^2*G*v^2 := by
  have H := tripleClockPerturbed_square a b c r q δ g G
  have H' := tripleClockPerturbed_square (a+v^2) (b+v^2) (c+v^2) r q δ g G
  rw [tripleClockMatrix_square] at H H'
  linear_combination m*H'-m*H

theorem tripleClockPerturbed_middle_penalty (a b r δ g G m v w : ℝ) :
    m*(matrixSquare 3 (tripleClockPerturbed (a+v^2) b b r b δ (g+v*w) (G+w^2))-
      matrixSquare 3 (tripleClockPerturbed a b b r b δ g G))=
      m*((a+v^2)^2-a^2)+4*m*δ^2*((g+v*w)^2-g^2)+4*m*δ^4*((G+w^2)^2-G^2) := by
  have H := tripleClockPerturbed_square a b b r b δ g G
  have H' := tripleClockPerturbed_square (a+v^2) b b r b δ (g+v*w) (G+w^2)
  rw [tripleClockMatrix_square] at H H'
  linear_combination m*H'-m*H

theorem tripleClockPerturbed_pair_penalty (a b r δ g G m v : ℝ) :
    m/2*(matrixSquare 3 (tripleClockPerturbed a (b+v^2) (b+v^2) r (b+v^2) δ g G)-
      matrixSquare 3 (tripleClockPerturbed a b b r b δ g G))=
      2*m*((b+v^2)^2-b^2) := by
  have H := tripleClockPerturbed_square a b b r b δ g G
  have H' := tripleClockPerturbed_square a (b+v^2) (b+v^2) r (b+v^2) δ g G
  rw [tripleClockMatrix_square] at H H'
  linear_combination m/2*H'-m/2*H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem matrixChainCovariance_append {d : ℕ} (l r : List (ℝ × (Fin d → ℝ))) :
    matrixChainCovariance (l++r)=matrixChainCovariance l+matrixChainCovariance r := by
  simp only [matrixChainCovariance,List.map_append,chainSum_append]

theorem matrixChainPenalty_append {d : ℕ} (l r : List (ℝ × (Fin d → ℝ))) (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty (l++r) Q=matrixChainPenalty l Q+matrixChainPenalty r (Q+matrixChainCovariance l) := by
  simp only [matrixChainPenalty,List.map_append,chainPotentialPenalty_append,matrixChainCovariance]

theorem tripleCommonSchedule_covariance (l : List (ℝ × ℝ)) (r : ℝ) :
    tripleClockMatrix r r r r r+matrixChainCovariance (tripleCommonSchedule l)=
      tripleClockMatrix (r+rawVariance l) (r+rawVariance l) (r+rawVariance l) (r+rawVariance l) (r+rawVariance l) := by
  induction l generalizing r with
  | nil => simp [tripleCommonSchedule,rawVariance]
  | cons p l ih =>
    simp only [tripleCommonSchedule] at ih
    simp only [tripleCommonSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
    change (fun i j => tripleClockMatrix r r r r r i j+(![p.2,p.2,p.2] : Fin 3 → ℝ) i*(![p.2,p.2,p.2] : Fin 3 → ℝ) j)+_=_
    rw [tripleClockPerturbed_common,ih]
    simp only [rawVariance,List.map_cons,List.sum_cons,add_assoc]

theorem tripleCommonSchedule_penalty (l : List (ℝ × ℝ)) (r : ℝ) :
    matrixChainPenalty (tripleCommonSchedule l) (tripleClockMatrix r r r r r)=3*rawPenalty l r := by
  induction l generalizing r with
  | nil => simp [tripleCommonSchedule,rawPenalty,chainPotentialPenalty]
  | cons p l ih =>
    simp only [tripleCommonSchedule] at ih
    simp only [tripleCommonSchedule,List.map_cons,matrixChainPenalty_cons]
    change p.1/3*(matrixSquare 3 ((fun i j => tripleClockMatrix r r r r r i j+(![p.2,p.2,p.2] : Fin 3 → ℝ) i*(![p.2,p.2,p.2] : Fin 3 → ℝ) j))-_)+
      matrixChainPenalty _ (fun i j => tripleClockMatrix r r r r r i j+(![p.2,p.2,p.2] : Fin 3 → ℝ) i*(![p.2,p.2,p.2] : Fin 3 → ℝ) j)=_
    rw [tripleClockPerturbed_common,ih,tripleClockMatrix_square,tripleClockMatrix_square]
    simp only [rawPenalty,List.map_cons,chainPotentialPenalty]
    ring

theorem tripleMiddleSchedule_covariance (δ : ℝ) (l : List TripleMiddleIncrement) (a b r g G : ℝ) :
    tripleClockPerturbed a b b r b δ g G+matrixChainCovariance (tripleMiddleSchedule δ l)=
      tripleClockPerturbed (a+rawVariance (weightedUnderlying (productLeft l)))
        (b+rawVariance (productRight l)) (b+rawVariance (productRight l)) r
        (b+rawVariance (productRight l)) δ (g+weightedCross (productLeft l)) (G+weightedVariance (productLeft l)) := by
  induction l generalizing a b g G with
  | nil => simp [tripleMiddleSchedule,productLeft,productRight,weightedUnderlying,rawVariance,weightedCross,weightedVariance]
  | cons p l ih =>
    simp only [tripleMiddleSchedule] at ih
    cases p with
    | inl p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
      change (fun i j => tripleClockPerturbed a b b r b δ g G i j+
        (![p.2.1,δ*p.2.2,-δ*p.2.2] : Fin 3 → ℝ) i*(![p.2.1,δ*p.2.2,-δ*p.2.2] : Fin 3 → ℝ) j)+_=_
      rw [tripleClockPerturbed_singleton,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawVariance,weightedCross,weightedVariance,List.map_cons,List.sum_cons,add_assoc]
    | inr p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
      change (fun i j => tripleClockPerturbed a b b r b δ g G i j+
        (![0,p.2,p.2] : Fin 3 → ℝ) i*(![0,p.2,p.2] : Fin 3 → ℝ) j)+_=_
      rw [tripleClockPerturbed_pair,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawVariance,weightedCross,weightedVariance,List.map_cons,List.sum_cons,add_assoc]

theorem tripleMiddleSchedule_penalty (δ : ℝ) (l : List TripleMiddleIncrement) (a b r g G : ℝ) :
    matrixChainPenalty (tripleMiddleSchedule δ l) (tripleClockPerturbed a b b r b δ g G)=
      rawPenalty (weightedUnderlying (productLeft l)) a+2*rawPenalty (productRight l) b+
      4*δ^2*weightedCrossPenalty (productLeft l) g+4*δ^4*weightedVariancePenalty (productLeft l) G := by
  induction l generalizing a b g G with
  | nil => simp [tripleMiddleSchedule,productLeft,productRight,weightedUnderlying,rawPenalty,
      weightedCrossPenalty,weightedVariancePenalty,chainPotentialPenalty]
  | cons p l ih =>
    simp only [tripleMiddleSchedule] at ih
    cases p with
    | inl p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainPenalty_cons]
      have he := tripleClockPerturbed_singleton a b b r b δ g G p.2.1 p.2.2
      change tripleClockPerturbed a b b r b δ g G+rankOneMatrix (tripleMiddleVector δ (.inl p))=_ at he
      rw [he]
      change p.1*(_-_)+_=_
      rw [tripleClockPerturbed_middle_penalty,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawPenalty,
        weightedCrossPenalty,weightedVariancePenalty,List.map_cons,chainPotentialPenalty]
      ring
    | inr p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainPenalty_cons]
      have he := tripleClockPerturbed_pair a b b r b δ g G p.2
      change tripleClockPerturbed a b b r b δ g G+rankOneMatrix (tripleMiddleVector δ (.inr p))=_ at he
      rw [he]
      change p.1/2*(_-_)+_=_
      rw [tripleClockPerturbed_pair_penalty,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawPenalty,
        weightedCrossPenalty,weightedVariancePenalty,List.map_cons,chainPotentialPenalty]
      ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleCommonSchedule_mem_mass {c : List (ℝ × ℝ)} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleCommonSchedule c) : ∃ q∈c,p.1=q.1/3 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨q,hq,rfl⟩

theorem tripleMiddleSchedule_mem_mass {δ : ℝ} {w : List (ℝ × (ℝ × ℝ))} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))) :
    ∃ q∈weightedUnderlying w,p.1=q.1 ∨ p.1=q.1/2 := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
  simp only [mergedProductBranches,List.mem_merge,List.mem_map] at hs
  rcases hs with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
  · exact ⟨(q.1,q.2.1),List.mem_map.mpr ⟨q,hq,rfl⟩,Or.inl rfl⟩
  · exact ⟨q,hq,Or.inr rfl⟩

theorem tripleTailSchedule_mem_mass {t : List (ℝ × ℝ)} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleTailSchedule t) : ∃ q∈t,p.1=q.1 := by
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  simp only [tripleTailBlock,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> exact ⟨q,hq,rfl⟩

theorem tripleTailSchedule_monotone (t : List (ℝ × ℝ))
    (ht : t.Pairwise (fun p q => p.1≤q.1)) :
    (tripleTailSchedule t).Pairwise (fun p q => p.1≤q.1) := by
  induction t with
  | nil => simp [tripleTailSchedule]
  | cons a t ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp ht
    change (tripleTailBlock a++tripleTailSchedule t).Pairwise _
    apply List.pairwise_append.mpr
    refine ⟨?_,ih ht,?_⟩
    · simp [tripleTailBlock]
    · intro p hp q hq
      obtain ⟨b,hb,hqb⟩ := tripleTailSchedule_mem_mass hq
      have hpa : p.1=a.1 := by
        simp only [tripleTailBlock,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl <;> rfl
      rw [hpa,hqb]
      exact ha b hb

theorem tripleSchedule_mass_bounds (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1) :
    ∀ p∈tripleSchedule δ c w t,p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  simp only [tripleSchedule,List.mem_append] at hp
  rcases hp with (hp|hp)|hp
  · obtain ⟨q,hq,hpq⟩ := tripleCommonSchedule_mem_mass hp
    have H := hm q (by simp [hq])
    rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := tripleMiddleSchedule_mem_mass hp
    have H := hm q (by simp [hq])
    rcases hpq with hpq|hpq
    · simpa only [hpq] using H
    · rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := tripleTailSchedule_mem_mass hp
    simpa only [hpq] using hm q (by simp [hq])

theorem tripleSchedule_monotone (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) (hm : ∀ p∈c++weightedUnderlying w++t,0≤p.1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1)) :
    (tripleSchedule δ c w t).Pairwise (fun p q => p.1≤q.1) := by
  obtain ⟨hcw,ht,hct⟩ := List.pairwise_append.mp hs
  obtain ⟨hc,hw,hcw⟩ := List.pairwise_append.mp hcw
  have hmid : (tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))).Pairwise
      (fun p q => p.1≤q.1) := by
    rw [tripleMiddleSchedule,List.pairwise_map]
    apply mergedProductBranches_monotone
    · simpa only [weightedUnderlying,List.pairwise_map] using hw
    · exact hw
  have hcom : (tripleCommonSchedule c).Pairwise (fun p q => p.1≤q.1) := by
    rw [tripleCommonSchedule,List.pairwise_map]
    exact hc.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  unfold tripleSchedule
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨hcom,hmid,?_⟩,tripleTailSchedule_monotone t ht,?_⟩
  · intro p hp q hq
    obtain ⟨a,ha,hpa⟩ := tripleCommonSchedule_mem_mass hp
    obtain ⟨b,hb,hqb⟩ := tripleMiddleSchedule_mem_mass hq
    have H := hcw a ha b hb
    have Ha := hm a (by simp [ha])
    rw [hpa]
    rcases hqb with hqb|hqb <;> rw [hqb] <;> linarith
  · intro p hp q hq
    obtain ⟨b,hb,hqb⟩ := tripleTailSchedule_mem_mass hq
    rw [hqb]
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨a,ha,hpa⟩ := tripleCommonSchedule_mem_mass hp
      have H := hct a (List.mem_append_left _ ha) b hb
      have Ha := hm a (by simp [ha])
      rw [hpa]; linarith
    · obtain ⟨a,ha,hpa⟩ := tripleMiddleSchedule_mem_mass hp
      have H := hct a (List.mem_append_right _ ha) b hb
      have Ha := hm a (by simp [ha])
      rcases hpa with hpa|hpa <;> rw [hpa] <;> linarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleTailSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem tripleTailBlock_covariance (p : ℝ × ℝ) (a b c r q δ g G : ℝ) :
    tripleClockPerturbed a b c r q δ g G+matrixChainCovariance (tripleTailBlock p)=
      tripleClockPerturbed (a+p.2^2) (b+p.2^2) (c+p.2^2) r q δ g G := by
  simp only [tripleTailBlock,matrixChainCovariance_cons,matrixChainCovariance_nil,add_zero,← add_assoc]
  have h0 := tripleClockPerturbed_tail0 a b c r q δ g G p.2
  have h1 := tripleClockPerturbed_tail1 (a+p.2^2) b c r q δ g G p.2
  have h2 := tripleClockPerturbed_tail2 (a+p.2^2) (b+p.2^2) c r q δ g G p.2
  change tripleClockPerturbed a b c r q δ g G+rankOneMatrix ![p.2,0,0]=_ at h0
  change tripleClockPerturbed (a+p.2^2) b c r q δ g G+rankOneMatrix ![0,p.2,0]=_ at h1
  change tripleClockPerturbed (a+p.2^2) (b+p.2^2) c r q δ g G+rankOneMatrix ![0,0,p.2]=_ at h2
  rw [h0,h1,h2]

theorem tripleTailBlock_penalty (p : ℝ × ℝ) (a b c r q δ g G : ℝ) :
    matrixChainPenalty (tripleTailBlock p) (tripleClockPerturbed a b c r q δ g G)=
      p.1*((a+p.2^2)^2-a^2)+p.1*((b+p.2^2)^2-b^2)+p.1*((c+p.2^2)^2-c^2)+4*p.1*δ^2*G*p.2^2 := by
  simp only [tripleTailBlock,matrixChainPenalty_cons,matrixChainPenalty_nil,add_zero]
  have h0 := tripleClockPerturbed_tail0 a b c r q δ g G p.2
  have h1 := tripleClockPerturbed_tail1 (a+p.2^2) b c r q δ g G p.2
  have h2 := tripleClockPerturbed_tail2 (a+p.2^2) (b+p.2^2) c r q δ g G p.2
  change tripleClockPerturbed a b c r q δ g G+rankOneMatrix ![p.2,0,0]=_ at h0
  change tripleClockPerturbed (a+p.2^2) b c r q δ g G+rankOneMatrix ![0,p.2,0]=_ at h1
  change tripleClockPerturbed (a+p.2^2) (b+p.2^2) c r q δ g G+rankOneMatrix ![0,0,p.2]=_ at h2
  rw [h0,h1,h2]
  have H := tripleClockPerturbed_tail_penalty a b c r q δ g G p.1 p.2
  linear_combination H

theorem tripleTailSchedule_covariance (l : List (ℝ × ℝ)) (a b c r q δ g G : ℝ) :
    tripleClockPerturbed a b c r q δ g G+matrixChainCovariance (tripleTailSchedule l)=
      tripleClockPerturbed (a+rawVariance l) (b+rawVariance l) (c+rawVariance l) r q δ g G := by
  induction l generalizing a b c with
  | nil => simp [tripleTailSchedule,rawVariance]
  | cons p l ih =>
    simp only [tripleTailSchedule] at ih
    simp only [tripleTailSchedule,List.flatMap_cons,matrixChainCovariance_append,← add_assoc,
      tripleTailBlock_covariance,ih]
    simp only [rawVariance,List.map_cons,List.sum_cons,add_assoc]

theorem tripleTailSchedule_penalty (l : List (ℝ × ℝ)) (a b c r q δ g G : ℝ) :
    matrixChainPenalty (tripleTailSchedule l) (tripleClockPerturbed a b c r q δ g G)=
      rawPenalty l a+rawPenalty l b+rawPenalty l c+4*δ^2*G*rawArea l := by
  induction l generalizing a b c with
  | nil => simp [tripleTailSchedule,rawPenalty,rawArea,chainPotentialPenalty]
  | cons p l ih =>
    simp only [tripleTailSchedule] at ih
    simp only [tripleTailSchedule,List.flatMap_cons,matrixChainPenalty_append,
      tripleTailBlock_covariance,tripleTailBlock_penalty,ih]
    simp only [rawPenalty,rawArea,List.map_cons,List.sum_cons,chainPotentialPenalty]
    ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_TripleScheduleEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem rawVariance_append (l r : List (ℝ × ℝ)) : rawVariance (l++r)=rawVariance l+rawVariance r := by
  simp [rawVariance,List.sum_append]

theorem rawPenalty_append (l r : List (ℝ × ℝ)) (a : ℝ) :
    rawPenalty (l++r) a=rawPenalty l a+rawPenalty r (a+rawVariance l) := by
  simp only [rawPenalty,List.map_append,chainPotentialPenalty_append,chainSum,List.map_map,rawVariance,Function.comp_def]

theorem tripleSchedule_covariance (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    matrixChainCovariance (tripleSchedule δ c w t)=
      tripleClockPerturbed (rawVariance (c++weightedUnderlying w++t)) (rawVariance (c++weightedUnderlying w++t))
        (rawVariance (c++weightedUnderlying w++t)) (rawVariance c) (rawVariance (c++weightedUnderlying w))
        δ (weightedCross w) (weightedVariance w) := by
  have hc := tripleCommonSchedule_covariance c 0
  simp only [tripleClockMatrix_zero,zero_add] at hc
  have hm := tripleMiddleSchedule_covariance δ (mergedProductBranches w (weightedUnderlying w))
    (rawVariance c) (rawVariance c) (rawVariance c) 0 0
  simp only [tripleClockPerturbed_zero,mergedProductBranches_left,mergedProductBranches_right,zero_add] at hm
  simp only [tripleSchedule,matrixChainCovariance_append,hc]
  rw [hm,tripleTailSchedule_covariance]
  simp only [rawVariance_append]

theorem tripleSchedule_penalty (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ)) :
    matrixChainPenalty (tripleSchedule δ c w t) 0=
      3*rawPenalty (c++weightedUnderlying w++t) 0+
      4*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+
      4*δ^4*weightedVariancePenalty w 0 := by
  have hc := tripleCommonSchedule_covariance c 0
  simp only [tripleClockMatrix_zero,zero_add] at hc
  have hpc := tripleCommonSchedule_penalty c 0
  simp only [tripleClockMatrix_zero] at hpc
  have hm := tripleMiddleSchedule_covariance δ (mergedProductBranches w (weightedUnderlying w))
    (rawVariance c) (rawVariance c) (rawVariance c) 0 0
  simp only [tripleClockPerturbed_zero,mergedProductBranches_left,mergedProductBranches_right,zero_add] at hm
  have hpm := tripleMiddleSchedule_penalty δ (mergedProductBranches w (weightedUnderlying w))
    (rawVariance c) (rawVariance c) (rawVariance c) 0 0
  simp only [tripleClockPerturbed_zero,mergedProductBranches_left,mergedProductBranches_right] at hpm
  simp only [tripleSchedule,matrixChainPenalty_append,matrixChainCovariance_append,zero_add,hc,hpc,hm,hpm,
    tripleTailSchedule_penalty,rawPenalty_append,rawVariance_append]
  ring

theorem weightedVariancePenalty_nonneg (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,0≤p.1) {G : ℝ} (hG : 0≤G) : 0≤weightedVariancePenalty w G := by
  induction w generalizing G with
  | nil => rfl
  | cons p w ih =>
    change 0≤p.1*((G+p.2.2^2)^2-G^2)+weightedVariancePenalty w (G+p.2.2^2)
    apply add_nonneg
    · apply mul_nonneg (hm p (List.mem_cons_self ..))
      nlinarith [sq_nonneg p.2.2]
    · exact ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) (by positivity)

theorem tripleConstrainedPressure_schedule_oai {N : ℕ} (hN : 0<N) (β δ : ℝ)
    (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1))
    (ht : rawVariance (c++weightedUnderlying w++t)=1) (hg : weightedCross w=1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))))) :
    matrixConstrainedPressure N 3 β (tripleGram (rawVariance c) δ (rawVariance (c++weightedUnderlying w))) ≤
      vectorIncrementChain ((tripleSchedule δ c w t).map (fun p => (p.1,β • p.2)))
        (fun x => ∑ u,scalarSpinTerminal (x u)) 0-
      3*β^2/4*rawPenalty (c++weightedUnderlying w++t) 0-
      β^2*δ^2*(weightedCrossPenalty w 0+weightedVariance w*rawArea t)+
      β^2*δ^4*(weightedVariance w)^2 := by
  have H := matrixConstrainedPressure_chain hN β _ hD (tripleSchedule δ c w t)
    (tripleSchedule_mass_bounds δ c w t hm)
    (tripleSchedule_monotone δ c w t (fun p hp => (hm p hp).1) hs)
  have hq : 0≤weightedVariancePenalty w 0 := weightedVariancePenalty_nonneg w (by
    intro p hp
    exact (hm (p.1,p.2.1) (by simp only [List.mem_append]; exact Or.inl (Or.inr (List.mem_map.mpr ⟨p,hp,rfl⟩)))).1) le_rfl
  simp only [tripleSchedule_covariance,ht,hg,tripleClockPerturbed_symmetric,
    triplePerturbedMatrix_mismatch,tripleSchedule_penalty] at H
  have hn : 0≤β^2*δ^4*weightedVariancePenalty w 0 := by positivity
  nlinarith

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.tripleConstrainedPressure_schedule_oai := @OAI.SK.Analytic.tripleConstrainedPressure_schedule_oai

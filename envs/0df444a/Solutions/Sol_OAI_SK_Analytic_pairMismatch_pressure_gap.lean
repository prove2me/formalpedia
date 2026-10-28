-- Prove2me | solution 1 for OAI.SK.Analytic.pairMismatch_pressure_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:12:17.629136+00:00
-- url     : https://prove2.me/submissions/2751c4e3-d40a-40b5-8387-b0df5a1fb789

import Mathlib
import Definitions.Def_SKBarriers
import Definitions.Def_OAIQ036S006
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

theorem overlap_comm {n : ℕ} (x y : Config n) : overlap x y = overlap y x := by
  simp only [overlap, mul_comm]

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

theorem overlap_self {n : ℕ} (hn : 0 < n) (x : Config n) : overlap x x = 1 := by
  simp only [overlap, ← pow_two, spin_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hn.ne')

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_ThermalMoments
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
section ThermalMoments
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem affineMoment_variance_nonneg (c : S → ℝ) (L : S → E →L[ℝ] ℝ)
    (g : S → ℝ) (x : E) : 0 ≤ affineMoment c L (fun s => (g s)^2) x-(affineMoment c L g x)^2 := by
  let a := affineMoment c L g x
  have H : 0 ≤ ∑ s, affineGibbs c L x s*(g s-a)^2 :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (affineGibbs_pos c L x s).le (sq_nonneg _))
  have he : (∑ s, affineGibbs c L x s*(g s-a)^2) =
      affineMoment c L (fun s => (g s)^2) x-a^2 := by
    simp only [sub_sq]
    simp_rw [mul_add,mul_sub]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have h₁ : (∑ s, affineGibbs c L x s*(2*g s*a)) = 2*a*a := by
      calc
        _ = (∑ s, affineGibbs c L x s*g s)*(2*a) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring
        _ = _ := by change a*(2*a) = _; ring
    have h₂ : (∑ s, affineGibbs c L x s*a^2) = a^2 := by
      rw [← Finset.sum_mul,affineGibbs_sum,one_mul]
    rw [h₁,h₂]
    dsimp only [affineMoment]
    ring
  rwa [he] at H

end ThermalMoments
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
-- module Solutions.OAIQ036_SK.SKBarriers_Gaussian_BoundedObservableCurvature
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

theorem RootBoundedCurvature.gaussianStep {n : ℕ} {f : ParameterSpace (n+1) → ℝ}
    (h : RootBoundedCurvature (n+1) f) (hf : BoundedDerivs f) {m : ℝ}
    (hm : m ∈ Icc (0:ℝ) 1) : RootBoundedCurvature n (Analytic.gaussianStep m f) := by
  intro x
  let μ := gaussianStepLaw m f x
  let := gaussianStepLaw_probability hf m x
  let u := parameterAxis n
  obtain ⟨hcG,B,_hB,hbG⟩ := prefixGradient_data hf u
  obtain ⟨hcH,C,_hC,hbH⟩ := prefixHessian_data hf u u
  have hmem : MemLp (fun y => prefixGradient f u (x,y)) 2 μ :=
    MemLp.of_bound (hcG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      B (ae_of_all _ (fun y => hbG (x,y)))
  have iH : Integrable (fun y => prefixHessian f u u (x,y)) μ :=
    integrable_gaussianStep_of_bounded hf m x
      (hcH.comp (continuous_const.prodMk continuous_id)) (fun y => hbH (x,y))
  have hv := variance_nonneg (fun y => prefixGradient f u (x,y)) μ
  rw [variance_eq_sub hmem] at hv
  have hpos : 0 ≤ ∫ y, prefixHessian f u u (x,y) ∂μ :=
    integral_nonneg (fun y => (h (x,y)).1)
  have hupper := integral_mono iH ((integrable_const (1:ℝ)).sub hmem.integrable_sq)
    (fun y => (h (x,y)).2)
  change (∫ y, prefixHessian f u u (x,y) ∂μ) ≤
    ∫ y, 1-(prefixGradient f u (x,y))^2 ∂μ at hupper
  rw [integral_sub (integrable_const _) hmem.integrable_sq,integral_const] at hupper
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hupper
  change 0 ≤ fderiv ℝ (fderiv ℝ (Analytic.gaussianStep m f)) x u u ∧
    fderiv ℝ (fderiv ℝ (Analytic.gaussianStep m f)) x u u ≤ 1-(fderiv ℝ (Analytic.gaussianStep m f) x u)^2
  rw [fderiv_fderiv_gaussianStep_apply hf,fderiv_gaussianStep_apply hf]
  simp only [gaussianAverage,pow_two,Pi.mul_apply] at hv hupper ⊢
  dsimp only [μ] at hv hupper hpos
  constructor
  · nlinarith [mul_nonneg hm.1 hv]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) hv]

theorem RootBoundedCurvature.hierarchyPressure {n : ℕ} {f : ParameterSpace n → ℝ}
    (h : RootBoundedCurvature n f) (hf : BoundedDerivs f) (m : Fin n → ℝ)
    (hm : ∀ i, m i ∈ Icc (0:ℝ) 1) : RootBoundedCurvature 0 (hierarchyPressure n m f) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    exact ih (h.gaussianStep hf (hm (Fin.last n))) (hf.gaussianStep _) _ (fun j => hm j.castSucc)

theorem affineLogPartition_bounded_root {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, |U s (parameterAxis n)| ≤ 1) :
    RootBoundedCurvature n (affineLogPartition c U) := by
  intro z
  simp only [rootHessian,rootGradient,fderiv_fderiv_affineLogPartition_apply,
    fderiv_affineLogPartition_apply]
  have hv := affineMoment_variance_nonneg c U (fun s => U s (parameterAxis n)) z
  have hupper := affineMoment_norm_le c U (fun s => (U s (parameterAxis n))^2)
    (C:=1) (fun s => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (hU s)) z
  simp only [pow_two] at hv hupper
  constructor
  · exact hv
  · have hh := le_trans (le_abs_self _) hupper
    nlinarith

theorem hierarchy_bounded_observable_curvature {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, |U s (parameterAxis n)| ≤ 1) :
    RootBoundedCurvature 0 (hierarchyPressure n m (affineLogPartition c U)) :=
  (affineLogPartition_bounded_root n c U hU).hierarchyPressure
    (affineLogPartition_boundedDerivs c U) m hm

end SK.Analytic

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

theorem scalarHierarchy_split (a b : ℕ) (m v : Fin (a+b) → ℝ) (f : ℝ → ℝ) :
    scalarHierarchy (a+b) m v f=
      scalarHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (scalarHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (scalarStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)

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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainAverageAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem scalarTimeChain_pairs_ofFn (n : ℕ) (β : ℝ) (p : Fin n → ℝ × ℝ≥0) (f : ℝ → ℝ) :
    scalarTimeChain β (List.ofFn p) f=
      scalarHierarchy n (fun i => (p i).1) (fun i => β*Real.sqrt ((p i).2:ℝ)) f :=
  scalarTimeChain_ofFn β n (fun i => (p i).1) (fun i => (p i).2) f

theorem scalarTimeChainAverage_append (β : ℝ) (l r : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β (l++r) f g=
      scalarTimeChainAverage β l (scalarTimeChain β r f) (scalarTimeChainAverage β r f g) := by
  conv_lhs => rw [← List.ofFn_get l,← List.ofFn_get r,← List.ofFn_fin_append]
  rw [scalarTimeChainAverage_ofFn,scalarHierarchyAverage_split]
  simp only [Fin.append_left,Fin.append_right]
  conv_rhs => rw [← List.ofFn_get l,← List.ofFn_get r]
  rw [scalarTimeChain_pairs_ofFn,scalarTimeChainAverage_ofFn,scalarTimeChainAverage_ofFn]

@[simp] theorem scalarTimeChainAverage_cons_zero (β m : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β ((m,0)::l) f g=scalarTimeChainAverage β l f g := by
  change scalarTimeChainAverage β ([(m,0)]++l) f g=_
  rw [scalarTimeChainAverage_append,scalarTimeChainAverage_singleton_zero]

@[simp] theorem scalarTimeChainAverage_snoc_zero (β m : ℝ) (l : List (ℝ × ℝ≥0)) (f g : ℝ → ℝ) :
    scalarTimeChainAverage β (l++[(m,0)]) f g=scalarTimeChainAverage β l f g := by
  rw [scalarTimeChainAverage_append,scalarTimeChainAverage_singleton_zero]
  simp [scalarTimeChain]

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

theorem finitePrefix_last (n : ℕ) (v : Fin (n+1) → ℝ) :
    finitePrefix v (Fin.last n)=∑ l, v l := by simp [finitePrefix, Fin.le_last]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_TimeChainPressureAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem chainQuadraticPenalty_append (s : ℝ) (l r : List (ℝ × ℝ≥0)) :
    chainQuadraticPenalty s (l++r)=chainQuadraticPenalty s l+
      chainQuadraticPenalty (s+chainDuration l) r := by
  induction l generalizing s with
  | nil => simp [chainQuadraticPenalty,chainDuration]
  | cons p l ih =>
    simp only [List.cons_append,chainQuadraticPenalty,ih]
    rw [chainDuration_cons,NNReal.coe_add]
    simp only [add_assoc]

theorem chainQuadraticPenalty_zero (s m : ℝ) (l : List (ℝ × ℝ≥0)) :
    chainQuadraticPenalty s ((m,0)::l)=chainQuadraticPenalty s l := by simp [chainQuadraticPenalty]

theorem chainQuadraticPenalty_singleton (s m : ℝ) (t : ℝ≥0) :
    chainQuadraticPenalty s [(m,t)]=m*((s+t)^2-s^2) := by simp [chainQuadraticPenalty]

theorem chainDuration_ofFn (n : ℕ) (p : Fin n → ℝ × ℝ≥0) :
    chainDuration (List.ofFn p)=∑ i, (p i).2 := by
  simp [chainDuration,List.map_ofFn,List.sum_ofFn]

theorem finitePrefix_castSucc {n : ℕ} (v : Fin (n+1) → ℝ) (i : Fin n) :
    finitePrefix v i.castSucc=finitePrefix (fun l => v l.castSucc) i := by
  unfold finitePrefix
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.castSucc_le_castSucc_iff,
    ite_eq_right (not_le.mpr (Fin.castSucc_lt_last i)),add_zero]

theorem chainQuadraticPenalty_ofFn_zero (n : ℕ) (p : Fin (n+1) → ℝ × ℝ≥0)
    (hp : (p 0).2=0) :
    chainQuadraticPenalty 0 (List.ofFn p)=
      ∑ i : Fin n, (p i.succ).1*
        ((finitePrefix (fun l => ((p l).2:ℝ)) i.succ)^2-
         (finitePrefix (fun l => ((p l).2:ℝ)) i.castSucc)^2) := by
  induction n with
  | zero => simp [List.ofFn_succ,chainQuadraticPenalty,hp]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,chainQuadraticPenalty_append]
    rw [ih (fun i => p i.castSucc) (by simpa using hp)]
    rw [chainQuadraticPenalty_singleton,zero_add,chainDuration_ofFn]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [← Fin.castSucc_succ,Fin.succ_last,finitePrefix_castSucc,finitePrefix_last,NNReal.coe_sum]
    congr 1
    rw [show (∑ l : Fin (n+2), ((p l).2:ℝ))=
      (∑ l : Fin (n+1), ((p l.castSucc).2:ℝ))+((p (Fin.last (n+1))).2:ℝ) from Fin.sum_univ_castSucc _]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Hierarchy_WeightedMoments
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

theorem abs_overlap_le_one {n : ℕ} (x y : Config n) : |overlap x y| ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp [overlap]
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold overlap
  rw [abs_div,abs_of_pos hnpos]
  apply (div_le_one hnpos).mpr
  calc
    _ ≤ ∑ i : Fin n, |spin (x i)*spin (y i)| := Finset.abs_sum_le_sum_abs _ _
    _ = (n:ℝ) := by
      have hs (i : Fin n) : |spin (x i)*spin (y i)| = 1 := by
        cases hx : x i <;> cases hy : y i <;> norm_num [spin]
      simp only [hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

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
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_MultiplierTaylor
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

theorem quadratic_bound_of_secondDeriv_le {f g h : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (h x) x)
    (hh : ∀ x, h x ≤ 1) (L : ℝ) : f L ≤ f 0+L*g 0+L^2/2 := by
  let F : ℝ → ℝ := fun x => f x-x^2/2
  have hF (x : ℝ) : HasDerivAt F (g x-x) x := by
    convert (hf x).sub (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hG (x : ℝ) : HasDerivAt (fun x => g x-x) (h x-1) x := (hg x).sub (hasDerivAt_id x)
  have hD : deriv F=fun x => g x-x := funext (fun x => (hF x).deriv)
  have hconc : ConcaveOn ℝ univ F := concaveOn_univ_of_deriv2_nonpos
    (fun x => (hF x).differentiableAt)
    (by rw [hD]; exact fun x => (hG x).differentiableAt)
    (fun x => by simpa only [Function.iterate_succ_apply,Function.iterate_zero_apply,hD,(hG x).deriv] using sub_nonpos.mpr (hh x))
  rcases lt_trichotomy 0 L with hL|hL|hL
  · have H := hconc.slope_le_of_hasDerivAt (mem_univ _) (mem_univ _) hL (hF 0)
    rw [slope_def_field,sub_zero,sub_zero,div_le_iff₀ hL] at H
    dsimp only [F] at H
    nlinarith
  · subst L
    simp
  · have H := hconc.le_slope_of_hasDerivAt (mem_univ _) (mem_univ _) hL (hF 0)
    rw [slope_def_field,sub_zero,le_div_iff₀ (sub_pos.mpr hL)] at H
    dsimp only [F] at H
    nlinarith

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem rootBoundedCurvature_quadratic {f : ℝ → ℝ} (hf : BoundedDerivs f)
    (h : RootBoundedCurvature 0 f) (L : ℝ) :
    f L ≤ f 0+L*rootGradient 0 f 0+L^2/2 := by
  have hd (x : ℝ) : HasDerivAt f (rootGradient 0 f x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootLine_hasDerivAt 0 hf 0 x
  have hdd (x : ℝ) : HasDerivAt (rootGradient 0 f) (rootHessian 0 f x) x := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootGradientLine_hasDerivAt 0 hf 0 x
  exact quadratic_bound_of_secondDeriv_le hd hdd
    (fun x => (h x).2.trans (sub_le_self _ (sq_nonneg _))) L

theorem hierarchy_bounded_observable_quadratic {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (hm : ∀ i, m i ∈ Icc (0:ℝ) 1)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ)
    (hU : ∀ s, |U s (parameterAxis n)| ≤ 1) (L : ℝ) :
    hierarchyPressure n m (affineLogPartition c U) L ≤
      hierarchyPressure n m (affineLogPartition c U) 0+
      L*rootGradient 0 (hierarchyPressure n m (affineLogPartition c U)) 0+L^2/2 :=
  rootBoundedCurvature_quadratic
    (hierarchyPressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c U))
    (hierarchy_bounded_observable_curvature n m hm c U hU) L

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairRecursion
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

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_add_prefix (m : ℝ) (f g : E × ℝ → ℝ) (c : E → ℝ) :
    gaussianAverage m (fun z => f z+c z.1) g=gaussianAverage m f g := by
  funext x
  have htilt : (gaussianReal 0 1).tilted (fun y => m*(f (x,y)+c x))=
      (gaussianReal 0 1).tilted (fun y => m*f (x,y)) := by
    have H := tilted_tilted (μ:=gaussianReal 0 1)
      (f:=fun _ : ℝ => m*c x) (integrable_const _) (fun y => m*f (x,y))
    rw [tilted_const] at H
    rw [H]
    congr 1
    funext y
    simp only [Pi.add_apply]
    ring
  exact congrArg (fun μ => ∫ y, g (x,y) ∂μ) htilt

end Generic

theorem vectorStep_pair_right {f g : ℝ → ℝ} (hg : BoundedDerivs g) (m v : ℝ) :
    vectorStep m (0,v) (fun p : ℝ × ℝ => f p.1+g p.2)=
      fun p => f p.1+scalarStep m v g p.2 := by
  let L : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
      v • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hL : (fun z : (ℝ × ℝ) × ℝ => g (z.1.2+v*z.2))=g ∘ L := rfl
  have H := gaussianStep_add_prefix (hL.symm ▸ hg.compCLM L) (fun p : ℝ × ℝ => f p.1) m
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (0,v)))=
      fun z => g (z.1.2+v*z.2)+f z.1.1 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v,add_comm]
  rw [← hL] at H
  rw [vectorStep,he,H]
  funext p
  rw [add_comm]
  rfl

theorem vectorStep_pair_left {f g : ℝ → ℝ} (hf : BoundedDerivs f) (m v : ℝ) :
    vectorStep m (v,0) (fun p : ℝ × ℝ => f p.1+g p.2)=
      fun p => scalarStep m v f p.1+g p.2 := by
  let L : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
      v • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hL : (fun z : (ℝ × ℝ) × ℝ => f (z.1.1+v*z.2))=f ∘ L := rfl
  have H := gaussianStep_add_prefix (hL.symm ▸ hf.compCLM L) (fun p : ℝ × ℝ => g p.2) m
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (v,0)))=
      fun z => f (z.1.1+v*z.2)+g z.1.2 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v]
  rw [← hL] at H
  rw [vectorStep,he,H]
  rfl

theorem pairIndependentStep_separate {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (m v : ℝ) :
    pairIndependentStep m v (fun p => f p.1+g p.2)=
      fun p => scalarStep m v f p.1+scalarStep m v g p.2 := by
  rw [pairIndependentStep,vectorStep_pair_right hg,vectorStep_pair_left hf]

theorem vectorStepAverage_pair_right (f g a b : ℝ → ℝ) (m v : ℝ) :
    vectorStepAverage m (0,v) (fun p : ℝ × ℝ => f p.1+g p.2)
      (fun p => a p.1*b p.2)=fun p => a p.1*scalarStepAverage m v g b p.2 := by
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (0,v)))=
      fun z => g (z.1.2+v*z.2)+f z.1.1 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v,add_comm]
  rw [vectorStepAverage,he,gaussianAverage_add_prefix m (fun z : (ℝ × ℝ) × ℝ => g (z.1.2+v*z.2)) _ (fun p => f p.1)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    mul_zero,add_zero,integral_const_mul,scalarStepAverage,mul_comm _ v]

theorem vectorStepAverage_pair_left (f g a b : ℝ → ℝ) (m v : ℝ) :
    vectorStepAverage m (v,0) (fun p : ℝ × ℝ => f p.1+g p.2)
      (fun p => a p.1*b p.2)=fun p => scalarStepAverage m v f a p.1*b p.2 := by
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (v,0)))=
      fun z => f (z.1.1+v*z.2)+g z.1.2 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v]
  rw [vectorStepAverage,he,gaussianAverage_add_prefix m (fun z : (ℝ × ℝ) × ℝ => f (z.1.1+v*z.2)) _ (fun p => g p.2)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    mul_zero,add_zero,integral_mul_const,scalarStepAverage,mul_comm _ v]

theorem pairIndependentAverage_product {f g : ℝ → ℝ} (hg : BoundedDerivs g)
    (a b : ℝ → ℝ) (m v : ℝ) :
    pairIndependentAverage m v (fun p => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => scalarStepAverage m v f a p.1*scalarStepAverage m v g b p.2 := by
  rw [pairIndependentAverage,vectorStep_pair_right hg,vectorStepAverage_pair_right,
    vectorStepAverage_pair_left]

theorem vectorStep_pair_diagonal (F : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (h : ∀ x, F (x,x)=2*f x) (m v x : ℝ) :
    vectorStep (m/2) (v,v) F (x,x)=2*scalarStep m v f x := by
  simp only [vectorStep,gaussianStep,positiveGaussianLogStep,Prod.mk_add_mk,Prod.smul_mk,
    smul_eq_mul,h,mul_comm _ v]
  by_cases hm : m=0
  · simp [hm,integral_const_mul,scalarStep,gaussianStep]
  · have hm2 : m/2≠0 := div_ne_zero hm (by norm_num)
    simp only [ite_eq_right hm2,scalarStep,gaussianStep,positiveGaussianLogStep,ite_eq_right hm]
    simp only [show ∀ y, m/2*(2*f (x+v*y))=m*f (x+v*y) by intro y; ring]
    ring

theorem vectorStepAverage_pair_diagonal (F G : ℝ × ℝ → ℝ) (f g : ℝ → ℝ)
    (h : ∀ x, F (x,x)=2*f x) (hg : ∀ x, G (x,x)=g x) (m v x : ℝ) :
    vectorStepAverage (m/2) (v,v) F G (x,x)=scalarStepAverage m v f g x := by
  change (∫ y, G (x+y*v,x+y*v) ∂(gaussianReal 0 1).tilted
    (fun y => (m/2)*F (x+y*v,x+y*v)))=
    ∫ y, g (x+v*y) ∂(gaussianReal 0 1).tilted (fun y => m*f (x+v*y))
  simp only [h,hg,mul_comm _ v]
  simp only [show ∀ y, m/2*(2*f (x+v*y))=m*f (x+v*y) by intro y; ring]

end SK.Analytic

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

theorem hierarchyAverage_vector_linear (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f g : E → ℝ) (c : ℝ → E) :
    hierarchyAverage n m (fun z => f (c (parameter n z)+∑ j, coordinateProjection n j z • v j))
      (fun z => g (c (parameter n z)+∑ j, coordinateProjection n j z • v j))=
      fun x => vectorHierarchyAverage n m v f g (c x) := by
  induction n generalizing f g with
  | zero => simp [hierarchyAverage,vectorHierarchyAverage,parameter]
  | succ n ih =>
    have he (F : E → ℝ) : (fun z : ParameterSpace (n+1) =>
        F (c (parameter (n+1) z)+∑ j, coordinateProjection (n+1) j z • v j))=
        fun z => F ((c (parameter n z.1)+∑ j : Fin n, coordinateProjection n j z.1 • v j.castSucc)+
          z.2 • v (Fin.last n)) := by
      funext z
      rw [Fin.sum_univ_castSucc]
      simp [coordinateProjection,parameter,add_assoc]
    rw [he f,he g,hierarchyAverage]
    change hierarchyAverage n (fun j => m j.castSucc)
      (fun z => vectorStep (m (Fin.last n)) (v (Fin.last n)) f
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))
      (fun z => vectorStepAverage (m (Fin.last n)) (v (Fin.last n)) f g
        (c (parameter n z)+∑ j, coordinateProjection n j z • v j.castSucc))=_
    rw [ih]
    rfl

theorem vectorHierarchy_split (a b : ℕ) (m : Fin (a+b) → ℝ) (v : Fin (a+b) → E) (f : E → ℝ) :
    vectorHierarchy (a+b) m v f=
      vectorHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)

theorem vectorHierarchyAverage_split (a b : ℕ) (m : Fin (a+b) → ℝ) (v : Fin (a+b) → E)
    (f g : E → ℝ) :
    vectorHierarchyAverage (a+b) m v f g=
      vectorHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (vectorHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  induction b generalizing f g with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorStep (m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (vectorStepAverage (m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorStep_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f : F → ℝ) :
    vectorStep m v (f ∘ L)=vectorStep m (L v) f ∘ L := by
  funext x
  simp only [vectorStep,Function.comp_def,map_add,map_smul]
  rfl

theorem vectorStepAverage_pullback (L : E →L[ℝ] F) (m : ℝ) (v : E) (f g : F → ℝ) :
    vectorStepAverage m v (f ∘ L) (g ∘ L)=vectorStepAverage m (L v) f g ∘ L := by
  funext x
  simp only [vectorStepAverage,Function.comp_def,map_add,map_smul]
  rfl

theorem vectorHierarchy_pullback (L : E →L[ℝ] F) (n : ℕ) (m : Fin n → ℝ)
    (v : Fin n → E) (f : F → ℝ) :
    vectorHierarchy n m v (f ∘ L)=vectorHierarchy n m (L ∘ v) f ∘ L := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchy,vectorStep_pullback,ih]
    rfl

theorem vectorHierarchyAverage_pullback (L : E →L[ℝ] F) (n : ℕ) (m : Fin n → ℝ)
    (v : Fin n → E) (f g : F → ℝ) :
    vectorHierarchyAverage n m v (f ∘ L) (g ∘ L)=vectorHierarchyAverage n m (L ∘ v) f g ∘ L := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchyAverage,vectorStep_pullback,vectorStepAverage_pullback,ih]
    rfl
end Vector

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_VectorMultiplier
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

theorem vectorStep_translate (m : ℝ) (v c : E) (f : E → ℝ) (x : E) :
    vectorStep m v (fun y => f (c+y)) x=vectorStep m v f (c+x) := by
  simp only [vectorStep,gaussianStep,positiveGaussianLogStep,add_assoc]

theorem vectorHierarchy_translate (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (f : E → ℝ) (c x : E) :
    vectorHierarchy n m v (fun y => f (c+y)) x=vectorHierarchy n m v f (c+x) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [vectorHierarchy]
    rw [funext (vectorStep_translate _ _ c f)]
    exact ih _ _ _
end Vector

section Site
variable {S : Type} [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem siteMultiplierExponent_axis (n : ℕ) (V : Fin n → S → ℝ) (O : S → ℝ) (s : S) :
    siteMultiplierExponent n V O s (parameterAxis n)=O s := by
  simp [siteMultiplierExponent,parameter_axis,coordinateProjection_axis]

omit [Nonempty S] in
theorem siteMultiplier_terminal (n : ℕ) (V : Fin n → S → ℝ) (O c : S → ℝ) :
    affineLogPartition c (siteMultiplierExponent n V O)=fun z =>
      siteValueTerminal c (parameter n z • O+∑ j, coordinateProjection n j z • V j) := by
  funext z
  simp only [affineLogPartition,siteValueTerminal,siteMultiplierExponent,add_apply,smul_apply,
    smul_eq_mul,sum_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,Pi.smul_apply,Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  congr 2
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem siteMultiplier_terminal_gradient (n : ℕ) (V : Fin n → S → ℝ) (O c : S → ℝ) :
    rootGradient n (affineLogPartition c (siteMultiplierExponent n V O))=fun z =>
      affineMoment c (fun s => ContinuousLinearMap.proj s) O
        (parameter n z • O+∑ j, coordinateProjection n j z • V j) := by
  funext z
  rw [rootGradient,fderiv_affineLogPartition_apply]
  simp only [affineMoment,affineGibbs,siteMultiplierExponent,
    add_apply,smul_apply,smul_eq_mul,sum_apply,ContinuousLinearMap.proj_apply,Pi.add_apply,
    Pi.smul_apply,Finset.sum_apply]
  have he (s : S) : O s*parameter n z+∑ j, V j s*coordinateProjection n j z=
      parameter n z*O s+∑ j, coordinateProjection n j z*V j s := by
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  simp only [he,parameter_axis,coordinateProjection_axis,mul_one,mul_zero,Finset.sum_const_zero,add_zero]

omit [Nonempty S] in
theorem siteValueTerminal_add_multiplier (c O : S → ℝ) (L : ℝ) :
    siteValueTerminal (fun s => c s+L*O s)=fun z => siteValueTerminal c (L • O+z) := by
  funext z
  simp only [siteValueTerminal,affineLogPartition,ContinuousLinearMap.proj_apply,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_assoc]

theorem vectorHierarchy_bounded_multiplier (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (V : Fin n → S → ℝ) (c O : S → ℝ)
    (hO : ∀ s, |O s|≤1) (L : ℝ) :
    vectorHierarchy n m V (siteValueTerminal (fun s => c s+L*O s)) 0 ≤
      vectorHierarchy n m V (siteValueTerminal c) 0+
      L*vectorHierarchyAverage n m V (siteValueTerminal c)
        (affineMoment c (fun s => ContinuousLinearMap.proj s) O) 0+L^2/2 := by
  have H := hierarchy_bounded_observable_quadratic n m hm c (siteMultiplierExponent n V O)
    (fun s => by rw [siteMultiplierExponent_axis]; exact hO s) L
  rw [funext (hierarchyPressure_rootGradient n m (affineLogPartition_boundedDerivs _ _)),
    siteMultiplier_terminal_gradient,siteMultiplier_terminal,
    hierarchyAverage_vector_linear n m V (siteValueTerminal c)
      (affineMoment c (fun s => ContinuousLinearMap.proj s) O) (fun x => x • O),
    hierarchyPressure_vector_linear n m V (siteValueTerminal c) (fun x => x • O)] at H
  simp only [zero_smul] at H
  rw [siteValueTerminal_add_multiplier,vectorHierarchy_translate,add_zero]
  exact H
end Site

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixMultiplierGap
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

theorem matrixConstrainedPressure_quadratic_gap {N d r k : ℕ} (hN : 0<N)
    (hr : 0 < r) (β : ℝ) (D A : Fin d → Fin d → ℝ)
    (hD : Nonempty (MatrixStates N d D))
    (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1)
    (hO : ∀ s : Config d, |matrixSiteWeight A (fun a u => spin (a u)) s|≤1) :
    let V := matrixSiteVector β B (fun (a : Config d) u => spin (a u))
    let O := matrixSiteWeight A (fun (a : Config d) u => spin (a u))
    let f := siteValueTerminal (fun _ : Config d => 0)
    let g := vectorHierarchyAverage ((k+1)*r) (siteBlockMass r k w) V f
      (affineMoment (fun _ : Config d => 0) (fun s => ContinuousLinearMap.proj s) O) 0
    matrixConstrainedPressure N d β D ≤
      vectorHierarchy ((k+1)*r) (siteBlockMass r k w) V f 0+
        (β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
          ∑ j, w j*matrixSquare d (factorPath d r k B j))-
        (g-matrixInner d A D)^2/2 := by
  dsimp only
  let V := matrixSiteVector β B (fun (a : Config d) u => spin (a u))
  let O := matrixSiteWeight A (fun (a : Config d) u => spin (a u))
  let f := siteValueTerminal (fun _ : Config d => 0)
  let g := vectorHierarchyAverage ((k+1)*r) (siteBlockMass r k w) V f
    (affineMoment (fun _ : Config d => 0) (fun s => ContinuousLinearMap.proj s) O) 0
  let L := matrixInner d A D-g
  have hm (i : Fin ((k+1)*r)) : siteBlockMass r k w i∈Icc (0:ℝ) 1 := by
    refine ⟨Finset.sum_nonneg (fun b _ => ?_),?_⟩
    · split_ifs; exact hw b; rfl
    · calc
        siteBlockMass r k w i ≤ ∑ b, w b := Finset.sum_le_sum (fun b _ => by
          change (if _ then w b else 0) ≤ w b
          split_ifs; rfl; exact hw b)
        _ = 1 := hs
  have HB := matrixConstrainedPressure_le hN hr β D (fun u t => L*A u t) hD B w hw hs
  have he : matrixSiteWeight (fun u t => L*A u t) (fun (a : Config d) u => spin (a u))=
      fun s => 0+L*O s := by
    funext s
    simp only [O,matrixSiteWeight,zero_add,Finset.mul_sum,mul_assoc]
  have hi : matrixInner d (fun u t => L*A u t) D=L*matrixInner d A D := by
    simp only [matrixInner,Finset.mul_sum,mul_assoc]
  rw [he,hi] at HB
  have HM := vectorHierarchy_bounded_multiplier ((k+1)*r) (siteBlockMass r k w) hm
    V (fun _ : Config d => 0) O hO L
  change _ ≤ vectorHierarchy ((k+1)*r) (siteBlockMass r k w) V f 0+L*g+L^2/2 at HM
  change matrixConstrainedPressure N d β D ≤ _
  dsimp only [L] at HB HM
  dsimp only [V,f,g] at HB HM ⊢
  nlinarith

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_MatrixReplicaBridge
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

theorem matrixReplicaSet_nonempty_iff {n d : ℕ} (D : Fin d → Fin d → ℝ) :
    (matrixReplicaSet n d D).Nonempty ↔ Nonempty (MatrixStates n d D) := by
  rw [← Finset.nonempty_coe_sort]
  exact (matrixReplicaEquiv n d D).nonempty_congr.symm

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairSplit
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

theorem pairIndependentHierarchy_separate (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    pairIndependentHierarchy n m v (fun p => f p.1+g p.2)=
      fun p => scalarHierarchy n m v f p.1+scalarHierarchy n m v g p.2 := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [pairIndependentHierarchy,pairIndependentStep_separate hf hg,ih _ _
      (scalarStep_regular hf _ _) (scalarStep_regular hg _ _)]
    rfl

theorem pairIndependentHierarchyAverage_product (n : ℕ) (m v : Fin n → ℝ)
    {f g : ℝ → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) (a b : ℝ → ℝ) :
    pairIndependentHierarchyAverage n m v (fun p => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => scalarHierarchyAverage n m v f a p.1*scalarHierarchyAverage n m v g b p.2 := by
  induction n generalizing f g a b with
  | zero => rfl
  | succ n ih =>
    rw [pairIndependentHierarchyAverage,pairIndependentStep_separate hf hg,
      pairIndependentAverage_product hg,ih _ _ (scalarStep_regular hf _ _) (scalarStep_regular hg _ _)]
    rfl

theorem pairCommonHierarchy_diagonal (n : ℕ) (m v : Fin n → ℝ)
    (F : ℝ × ℝ → ℝ) (f : ℝ → ℝ) (h : ∀ x, F (x,x)=2*f x) (x : ℝ) :
    pairCommonHierarchy n m v F (x,x)=2*scalarHierarchy n m v f x := by
  induction n generalizing f F with
  | zero => exact h x
  | succ n ih =>
    exact ih _ _ _ _ (vectorStep_pair_diagonal F f h _ _)

theorem pairCommonHierarchyAverage_diagonal (n : ℕ) (m v : Fin n → ℝ)
    (F G : ℝ × ℝ → ℝ) (f g : ℝ → ℝ) (h : ∀ x, F (x,x)=2*f x)
    (hg : ∀ x, G (x,x)=g x) (x : ℝ) :
    pairCommonHierarchyAverage n m v F G (x,x)=scalarHierarchyAverage n m v f g x := by
  induction n generalizing f g F G with
  | zero => exact hg x
  | succ n ih =>
    exact ih _ _ _ _ _ _ (vectorStep_pair_diagonal F f h _ _)
      (vectorStepAverage_pair_diagonal F G f g h hg _ _)

theorem pairSplit_pressure (a b : ℕ) (m v : Fin (a+b) → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (x : ℝ) :
    pairCommonHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (fun p => f p.1+f p.2)) (x,x)=2*scalarHierarchy (a+b) m v f x := by
  rw [pairIndependentHierarchy_separate b _ _ hf hf,scalarHierarchy_split a b]
  exact pairCommonHierarchy_diagonal a _ _ _ _ (fun y => by ring) x

theorem pairSplit_overlap (a b : ℕ) (m v : Fin (a+b) → ℝ)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ → ℝ) (x : ℝ) :
    pairCommonHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
      (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (fun p => f p.1+f p.2))
      (pairIndependentHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a))
        (fun p => f p.1+f p.2) (fun p => g p.1*g p.2)) (x,x)=
      scalarMomentSquare (a+b) m v f g ⟨a,by omega⟩ x := by
  rw [pairIndependentHierarchy_separate b _ _ hf hf,pairIndependentHierarchyAverage_product b _ _ hf hf,
    scalarMomentSquare_split a b]
  exact pairCommonHierarchyAverage_diagonal a _ _ _ _ _ _ (fun y => by ring)
    (fun y => (pow_two _).symm) x

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

theorem vectorHierarchyAverage_cast {n r : ℕ} (h : n=r) (m : Fin n → ℝ)
    (v : Fin n → E) (f g : E → ℝ) :
    vectorHierarchyAverage n m v f g=vectorHierarchyAverage r (fun i => m (Fin.cast h.symm i))
      (fun i => v (Fin.cast h.symm i)) f g := by
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

theorem vectorHierarchyAverage_blocks (n r : ℕ) (m : Fin n → ℝ) (v : Fin n → Fin r → E)
    (f g : E → ℝ) :
    vectorHierarchyAverage (n*r) (fun i => m (finProdFinEquiv.symm i).1)
      (fun i => v (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) f g=
      vectorBlockHierarchyAverage r n m v f g := by
  induction n generalizing f g with
  | zero => rw [vectorHierarchyAverage_cast (Nat.zero_mul r)]; rfl
  | succ n ih =>
    rw [vectorHierarchyAverage_cast (Nat.succ_mul n r),vectorHierarchyAverage_split]
    simp only [finProd_symm_prefix,finProd_symm_suffix]
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc) _ _
end

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairBlocks
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

theorem vectorHierarchy_pairBlock (shared : Bool) (m v : ℝ) (f : ℝ × ℝ → ℝ) :
    vectorHierarchy 2 (fun _ => m) (pairBlockVector shared v) f=
      if shared then vectorStep m (v,v) f else pairIndependentStep m v f := by
  cases shared <;> simp [vectorHierarchy,pairBlockVector,pairIndependentStep]

theorem vectorHierarchyAverage_pairBlock (shared : Bool) (m v : ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorHierarchyAverage 2 (fun _ => m) (pairBlockVector shared v) f g=
      if shared then vectorStepAverage m (v,v) f g else pairIndependentAverage m v f g := by
  cases shared <;> simp [vectorHierarchyAverage,pairBlockVector,pairIndependentAverage]

section Blocks
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorBlockHierarchy_split (a b r : ℕ) (m : Fin (a+b) → ℝ)
    (v : Fin (a+b) → Fin r → E) (f : E → ℝ) :
    vectorBlockHierarchy r (a+b) m v f=
      vectorBlockHierarchy r a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorBlockHierarchy r b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  induction b generalizing f with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last (a+b))) (v (Fin.last (a+b))) f)

theorem vectorBlockHierarchyAverage_split (a b r : ℕ) (m : Fin (a+b) → ℝ)
    (v : Fin (a+b) → Fin r → E) (f g : E → ℝ) :
    vectorBlockHierarchyAverage r (a+b) m v f g=
      vectorBlockHierarchyAverage r a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (vectorBlockHierarchy r b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (vectorBlockHierarchyAverage r b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  induction b generalizing f g with
  | zero => rfl
  | succ b ih =>
    exact ih (fun i => m i.castSucc) (fun i => v i.castSucc)
      (vectorHierarchy r (fun _ => m (Fin.last (a+b))) (v (Fin.last (a+b))) f)
      (vectorHierarchyAverage r (fun _ => m (Fin.last (a+b))) (v (Fin.last (a+b))) f g)
end Blocks

theorem vectorBlockHierarchy_independent (n : ℕ) (m v : Fin n → ℝ) (f : ℝ × ℝ → ℝ) :
    vectorBlockHierarchy 2 n m (fun i => pairBlockVector false (v i)) f=pairIndependentHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchy,vectorHierarchy_pairBlock]
    exact ih _ _ _

theorem vectorBlockHierarchy_common (n : ℕ) (m v : Fin n → ℝ) (f : ℝ × ℝ → ℝ) :
    vectorBlockHierarchy 2 n (fun i => m i/2) (fun i => pairBlockVector true (v i)) f=pairCommonHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchy,vectorHierarchy_pairBlock]
    exact ih _ _ _

theorem vectorBlockHierarchyAverage_independent (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorBlockHierarchyAverage 2 n m (fun i => pairBlockVector false (v i)) f g=pairIndependentHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchyAverage,vectorHierarchy_pairBlock,vectorHierarchyAverage_pairBlock]
    exact ih _ _ _ _

theorem vectorBlockHierarchyAverage_common (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorBlockHierarchyAverage 2 n (fun i => m i/2) (fun i => pairBlockVector true (v i)) f g=pairCommonHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorBlockHierarchyAverage,vectorHierarchy_pairBlock,vectorHierarchyAverage_pairBlock]
    exact ih _ _ _ _

theorem splitPairVector_prefix (a b : ℕ) (v : Fin (a+b) → ℝ) (i : Fin a) :
    splitPairVector a v (i.castAdd b)=pairBlockVector true (v (i.castAdd b)) := by
  simp [splitPairVector,i.isLt]

theorem splitPairVector_suffix (a b : ℕ) (v : Fin (a+b) → ℝ) (i : Fin b) :
    splitPairVector a v (i.natAdd a)=pairBlockVector false (v (i.natAdd a)) := by
  simp [splitPairVector]

theorem splitPairMass_prefix (a b : ℕ) (m : Fin (a+b) → ℝ) (i : Fin a) :
    splitPairMass a m (i.castAdd b)=m (i.castAdd b)/2 := by simp [splitPairMass,i.isLt]

theorem splitPairMass_suffix (a b : ℕ) (m : Fin (a+b) → ℝ) (i : Fin b) :
    splitPairMass a m (i.natAdd a)=m (i.natAdd a) := by simp [splitPairMass]

theorem splitPairHierarchy (a b : ℕ) (m v : Fin (a+b) → ℝ) (f : ℝ × ℝ → ℝ) :
    vectorBlockHierarchy 2 (a+b) (splitPairMass a m) (splitPairVector a v) f=
      pairCommonHierarchy a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f) := by
  rw [vectorBlockHierarchy_split a b]
  simp only [splitPairVector_prefix,splitPairVector_suffix,splitPairMass_prefix,splitPairMass_suffix]
  rw [vectorBlockHierarchy_independent,vectorBlockHierarchy_common]

theorem splitPairHierarchyAverage (a b : ℕ) (m v : Fin (a+b) → ℝ) (f g : ℝ × ℝ → ℝ) :
    vectorBlockHierarchyAverage 2 (a+b) (splitPairMass a m) (splitPairVector a v) f g=
      pairCommonHierarchyAverage a (fun i => m (i.castAdd b)) (fun i => v (i.castAdd b))
        (pairIndependentHierarchy b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f)
        (pairIndependentHierarchyAverage b (fun i => m (i.natAdd a)) (fun i => v (i.natAdd a)) f g) := by
  rw [vectorBlockHierarchyAverage_split a b]
  simp only [splitPairVector_prefix,splitPairVector_suffix,splitPairMass_prefix,splitPairMass_suffix]
  rw [vectorBlockHierarchy_independent,vectorBlockHierarchyAverage_independent,vectorBlockHierarchyAverage_common]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairTerminal
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

theorem pairSpin_terminal : siteValueTerminal (fun _ : Config 2 => 0) ∘ pairSpinMap=
    fun p => scalarSpinTerminal p.1+scalarSpinTerminal p.2 := by
  funext p
  have H := affineLogPartition_product 2 (fun (_ : Fin 2) (_ : Bool) => (0:ℝ))
    (fun i b => spin b • (if i=0 then ContinuousLinearMap.fst ℝ ℝ ℝ else ContinuousLinearMap.snd ℝ ℝ ℝ))
  have E := congrFun H p
  simp only [Fin.sum_univ_two,ite_true,show (1:Fin 2)≠0 by decide,ite_false,
    affineLogPartition_bool,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] at E
  simpa only [Function.comp_def,siteValueTerminal,affineLogPartition,zero_add,add_zero,
    pairSpinMap_apply,add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',scalarSpinTerminal] using E

theorem pairSpinObservable_bound (s : Config 2) : |pairSpinObservable s|≤1 := by
  unfold pairSpinObservable spin
  split_ifs <;> norm_num

theorem pairSpin_thermal_observable :
    (affineMoment (fun _ : Config 2 => 0) (fun s => ContinuousLinearMap.proj s) pairSpinObservable) ∘ pairSpinMap=
      fun p => scalarMagnetization p.1*scalarMagnetization p.2 := by
  funext p
  unfold affineMoment affineGibbs
  simp only [Function.comp_def,ContinuousLinearMap.proj_apply,pairSpinMap_apply,zero_add]
  have HS (f : Config 2 → ℝ) : (∑ s, f s)=∑ a : Bool, ∑ b : Bool, f ![a,b] := by
    rw [← (finTwoArrowEquiv Bool).symm.sum_comp]
    simp only [Fintype.sum_prod_type,finTwoArrowEquiv_symm_apply]
  rw [HS]
  simp only [HS,Fintype.sum_bool,pairSpinObservable,Matrix.cons_val_zero,Matrix.cons_val_one,
    spin,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,mul_one,mul_neg_one,neg_neg]
  simp only [Real.exp_add,Real.exp_neg,scalarMagnetization,Real.sinh_eq,Real.cosh_eq]
  have ha := Real.exp_pos p.1
  have hb := Real.exp_pos p.2
  field_simp
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairFactor
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

theorem pairFactor_covariance (shared : Bool) (c : ℝ) :
    factorCovariance 2 2 (pairFactor shared c)=pairMatrix (c^2) (if shared then c^2 else 0) := by
  funext i j
  fin_cases i <;> fin_cases j <;> cases shared <;>
    simp [factorCovariance,pairFactor,pairBlockVector,pairMatrix,Fin.sum_univ_two,pow_two]

theorem pairFactor_vector (shared : Bool) (β c : ℝ) (u : Fin 2) (s : Config 2) :
    β*(∑ i, pairFactor shared c u i*spin (s i))=pairSpinMap (pairBlockVector shared (β*c) u) s := by
  fin_cases u <;> cases shared <;>
    simp [pairFactor,pairBlockVector,pairSpinMap_apply,Fin.sum_univ_two] <;> ring

theorem splitPairFactor_vector {k : ℕ} (a : ℕ) (β : ℝ) (c : Fin (k+1) → ℝ) :
    matrixSiteVector β (splitPairFactor a c) (fun (s : Config 2) i => spin (s i))=
      pairSpinMap ∘ (fun j => splitPairVector a (fun i => β*c i) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) := by
  funext j s
  exact pairFactor_vector _ _ _ _ _

theorem splitPairFactor_path {k : ℕ} (a : ℕ) (c : Fin (k+1) → ℝ) (j : Fin (k+1)) :
    factorPath 2 2 k (splitPairFactor a c) j=
      pairMatrix (finitePrefix (fun l => (c l)^2) j)
        (finitePrefix (fun l => if l.val<a then (c l)^2 else 0) j) := by
  funext u v
  simp only [factorPath,splitPairFactor,pairFactor_covariance,pairMatrix,finitePrefix]
  by_cases h : u=v <;> simp [h]

theorem pairMultiplier_observable :
    matrixSiteWeight pairMultiplier (fun (s : Config 2) i => spin (s i))=pairSpinObservable := by
  funext s
  simp only [matrixSiteWeight,pairMultiplier,pairMatrix,Fin.sum_univ_two,ite_true,
    show (0:Fin 2)≠1 by decide,show (1:Fin 2)≠0 by decide,ite_false,zero_mul,zero_add,add_zero,pairSpinObservable]
  ring

theorem pairMultiplier_inner (t q : ℝ) : matrixInner 2 pairMultiplier (pairMatrix t q)=q := by
  norm_num [matrixInner,pairMultiplier,pairMatrix,Fin.sum_univ_two]
  ring

theorem pairMatrix_square (t q : ℝ) : matrixSquare 2 (pairMatrix t q)=2*t^2+2*q^2 := by
  norm_num [matrixSquare,pairMatrix,Fin.sum_univ_two]
  ring

theorem matrixInner_self (d : ℕ) (D : Fin d → Fin d → ℝ) : matrixInner d D D=matrixSquare d D := by
  simp only [matrixInner,matrixSquare,pow_two]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_OverlapCode
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

theorem overlap_eq_codeOverlap {n : ℕ} (x y : Config n) :
    overlap x y=codeOverlap n (overlapCode x y) := by
  have he (i : Fin n) : spin (x i)*spin (y i)=2*(if x i=y i then (1:ℝ) else 0)-1 := by
    cases hx : x i <;> cases hy : y i <;> norm_num [spin]
  simp only [overlap,he,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  congr 1
  simp [overlapCode,Finset.sum_boole]

theorem replicaGram_pair {n : ℕ} (hn : 0 < n) (s : ReplicaConfig n 2) :
    replicaGram s=pairMatrix 1 (codeOverlap n (pairReplicaCode s)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [replicaGram,pairMatrix,pairReplicaCode,← overlap_eq_codeOverlap,overlap_comm,overlap_self hn]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicPenalty
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

theorem dyadicIntervals_duration (α : ℝ → ℝ) (n : ℕ) (s : ℝ) (t : ℝ≥0) :
    chainDuration (dyadicIntervals α n s t)=t := by
  induction n generalizing s t with
  | zero => simp [dyadicIntervals,chainDuration]
  | succ n ih =>
    simp only [dyadicIntervals,chainDuration,List.map_append,List.sum_append] at *
    rw [ih,ih]
    exact add_halves t

theorem dyadicPenalty_error {α : ℝ → ℝ} (hα : Monotone α)
    (n : ℕ) (s : ℝ) (t : ℝ≥0) (hs : 0 ≤ s) (ht : s+t ≤ 1) :
    |chainQuadraticPenalty s (dyadicIntervals α n s t)-2*∫ u in s..s+t, u*α u| ≤
      2*(t:ℝ)/(2:ℝ)^n*(α (s+t)-α s) := by
  have hi (a b : ℝ) : IntervalIntegrable (fun u => u*α u) volume a b :=
    hα.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
  induction n generalizing s t with
  | zero =>
    have hst : s ≤ s+(t:ℝ) := by linarith [t.coe_nonneg]
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=s) (b:=s+t)
      (f:=fun u => 2*u*(α u-α s)) (C:=2*(α (s+t)-α s)) (by
        intro u hu
        rw [uIoc_of_le hst] at hu
        have ha := hα hu.1.le
        have hb := hα hu.2
        have hu0 : 0 ≤ u := hs.trans hu.1.le
        have hu1 : u ≤ 1 := hu.2.trans ht
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hb) hu0,
          mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hu1)])
    have he : (∫ u in s..s+t, 2*u*(α u-α s))=
        2*(∫ u in s..s+t, u*α u)-α s*((s+t)^2-s^2) := by
      simp_rw [show ∀ u : ℝ, 2*u*(α u-α s)=2*(u*α u)-2*(u*α s) by intro u; ring]
      have hic : IntervalIntegrable (fun u : ℝ => 2*(u*α s)) volume s (s+t) :=
        ((continuous_id.intervalIntegrable s (s+t)).mul_const (α s)).const_mul 2
      rw [intervalIntegral.integral_sub ((hi s (s+t)).const_mul 2) hic,
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const,integral_id]
      ring
    rw [he,Real.norm_eq_abs,abs_sub_comm,add_sub_cancel_left,abs_of_nonneg t.coe_nonneg] at H
    simpa only [dyadicIntervals,chainQuadraticPenalty_singleton,pow_zero,div_one,mul_comm (2*(α (s+t)-α s)) (t:ℝ),mul_assoc,mul_left_comm] using H
  | succ n ih =>
    have hc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have he : s+(t:ℝ)/2+(t:ℝ)/2=s+t := by ring
    have hmid : 0 ≤ s+(t:ℝ)/2 := by positivity
    have hmid1 : s+(t/2:ℝ≥0) ≤ 1 := by rw [hc]; linarith [t.coe_nonneg]
    have hend1 : s+(t:ℝ)/2+(t/2:ℝ≥0) ≤ 1 := by rw [hc,he]; exact ht
    have H₁ := ih s (t/2) hs hmid1
    have H₂ := ih (s+(t:ℝ)/2) (t/2) hmid hend1
    rw [dyadicIntervals,chainQuadraticPenalty_append,dyadicIntervals_duration]
    rw [hc]
    have hint := intervalIntegral.integral_add_adjacent_intervals
      (hi s (s+(t:ℝ)/2)) (hi (s+(t:ℝ)/2) (s+t))
    rw [← hint]
    calc
      _ ≤ |chainQuadraticPenalty s (dyadicIntervals α n s (t/2))-
            2*(∫ u in s..s+(t:ℝ)/2, u*α u)|+
          |chainQuadraticPenalty (s+(t:ℝ)/2) (dyadicIntervals α n (s+(t:ℝ)/2) (t/2))-
            2*(∫ u in s+(t:ℝ)/2..s+t, u*α u)| := by
        have hh : ∀ A B C D : ℝ, |A+B-2*(C+D)| ≤ |A-2*C|+|B-2*D| := by
          intro A B C D
          rw [show A+B-2*(C+D)=(A-2*C)+(B-2*D) by ring]
          exact abs_add_le _ _
        exact hh _ _ _ _
      _ ≤ _ := add_le_add (by simpa only [hc] using H₁) (by simpa only [hc,he] using H₂)
      _ = _ := by rw [pow_succ]; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Scalar_DyadicVaryingTerminal
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

theorem dyadicScalarAverage_varying_terminal (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {F A : ℕ → ℝ → ℝ} {f a da : ℝ → ℝ}
    (hF : ∀ n, BoundedDerivs (F n)) (hf : BoundedDerivs f)
    (hA : ∀ n, Continuous (A n))
    (ha : ∀ z, HasDerivAt a (da z) z) (hda : Continuous da)
    {K B C : ℝ≥0} (hfK : LipschitzWith K f)
    (hAB : ∀ n z, |A n z| ≤ B) (haB : ∀ z, |a z| ≤ B)
    (hdaC : ∀ z, |da z| ≤ C)
    (hFf : TendstoUniformly F f atTop) (hAa : TendstoUniformly A a atTop)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) (x : ℝ) :
    Tendsto (fun n => dyadicScalarAverage β α n s t (F n) (A n) x)
      atTop (𝓝 (scalarCDFAverage β α s t f a x)) := by
  have hfixed := dyadicScalarAverage_tendsto_C1 β hα hmono hf ha hda hfK haB hdaC s t ht x
  have hac : Continuous a := continuous_iff_continuousAt.mpr (fun z => (ha z).continuousAt)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let φ : ℝ → ℝ := fun e => 2*e+2*(B:ℝ)*(Real.exp (2*e)-1)
  have hφ : ContinuousAt φ 0 := by dsimp [φ]; fun_prop
  obtain ⟨δ,hδ,hbound⟩ := Metric.continuousAt_iff.mp hφ ε hε
  let e := δ/2
  have he : 0<e := half_pos hδ
  have hsmall : φ e<ε := by
    have H := hbound (show dist e 0<δ by rw [Real.dist_eq,sub_zero,abs_of_pos he]; dsimp [e]; linarith)
    have hzero : φ 0=0 := by simp [φ]
    rw [hzero,Real.dist_eq,sub_zero] at H
    exact (le_abs_self _).trans_lt H
  have E : ∀ᶠ n in atTop, dist (dyadicScalarAverage β α n s t (F n) (A n) x)
      (scalarCDFAverage β α s t f a x)<ε := by
    filter_upwards [Metric.tendstoUniformly_iff.mp hFf e he,
      Metric.tendstoUniformly_iff.mp hAa e he,Metric.tendsto_nhds.mp hfixed e he] with n hfn han hfix
    have H := scalarHierarchyAverage_terminal_stability _ _
      (fun i => β*Real.sqrt (((dyadicIntervals α n s t).get i).2:ℝ))
      (fun i => dyadicIntervals_mass_bounds hα n s t (List.get_mem _ _))
      (show Monotone (fun i : Fin (dyadicIntervals α n s t).length =>
        ((dyadicIntervals α n s t).get i).1) from by
        intro i j hij
        rcases lt_or_eq_of_le hij with hij|rfl
        · exact (List.pairwise_iff_get.mp (dyadicIntervals_pairwise hmono n s t)) i j hij
        · exact le_rfl)
      (hF n) hf he.le (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hfn z).le)
      (hA n) hac B.coe_nonneg (hAB n) haB
      (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (han z).le) x
    change |dyadicScalarAverage β α n s t (F n) (A n) x-
      dyadicScalarAverage β α n s t f a x| ≤ _ at H
    rw [Real.dist_eq] at hfix ⊢
    calc
      _ ≤ |dyadicScalarAverage β α n s t (F n) (A n) x-
            dyadicScalarAverage β α n s t f a x|+
          |dyadicScalarAverage β α n s t f a x-scalarCDFAverage β α s t f a x| := abs_sub_le _ _ _
      _ < e+2*(B:ℝ)*(Real.exp (2*e)-1)+e := add_lt_add_of_le_of_lt H hfix
      _ = φ e := by dsimp [φ]; ring
      _ < ε := hsmall
  exact eventually_atTop.mp E

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairContinuumConvergence
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

theorem scalarTimeChainAverage_spin_gradient (β : ℝ) (l : List (ℝ × ℝ≥0)) :
    scalarTimeChainAverage β l scalarSpinTerminal scalarMagnetization=
      rootGradient 0 (scalarTimeChain β l scalarSpinTerminal) := by
  funext x
  rw [← (scalarTimeChain_spin_hasDerivAt β l x).deriv,scalarTimeChain_eq_hierarchy]
  exact (scalarHierarchy_gradient_average _ _ _ scalarSpinTerminal_regular scalarSpinTerminal_hasDerivAt x).symm

theorem dyadicScalar_varying_terminal_uniform (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hF : ∀ n, BoundedDerivs (F n))
    (hf : BoundedDerivs f) {K : ℝ≥0} (hfK : LipschitzWith K f)
    (hFf : TendstoUniformly F f atTop) (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    TendstoUniformly (fun n => dyadicScalar β α n s t (F n))
      (scalarCDFOperator β α s t f) atTop := by
  have H := dyadicScalar_general_uniform hf hfK β hα hmono s t ht
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hFf (ε/2) (half_pos hε),
    Metric.tendstoUniformly_iff.mp H (ε/2) (half_pos hε)] with n hfn hn x
  have H' := dyadicScalar_uniform_nonexpansive (hF n) hf β hα n s t
    (fun z => by simpa only [Real.dist_eq,abs_sub_comm] using (hfn z).le) x
  rw [Real.dist_eq,abs_sub_comm]
  calc
    _ ≤ |dyadicScalar β α n s t (F n) x-dyadicScalar β α n s t f x|+
        |dyadicScalar β α n s t f x-scalarCDFOperator β α s t f x| := abs_sub_le _ _ _
    _ < ε/2+ε/2 := add_lt_add_of_le_of_lt H' (by simpa only [Real.dist_eq,abs_sub_comm] using hn x)
    _ = ε := add_halves ε

theorem dyadicPenalty_tendsto {α : ℝ → ℝ} (hα : Monotone α)
    (s : ℝ) (t : ℝ≥0) (hs : 0 ≤ s) (ht : s+t ≤ 1) :
    Tendsto (fun n => chainQuadraticPenalty s (dyadicIntervals α n s t)) atTop
      (𝓝 (2*∫ u in s..s+t, u*α u)) := by
  have H : Tendsto (fun n : ℕ => 2*(t:ℝ)/(2:ℝ)^n*(α (s+t)-α s)) atTop (𝓝 0) := by
    have Hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ)<1)).const_mul (2*(t:ℝ)*(α (s+t)-α s))
    convert Hp using 1
    · funext n
      rw [div_pow,one_pow]
      ring
    · ring_nf
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp H).2 ε hε] with n hn
  rw [Real.dist_eq]
  exact (dyadicPenalty_error hα n s t hs ht).trans_lt hn

theorem dyadicPairOverlap_tendsto (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    Tendsto (fun n => scalarTimeChainAverage β (dyadicIntervals α n 0 (Real.toNNReal q))
      (scalarTimeChain β (dyadicIntervals α n q (Real.toNNReal (1-q))) scalarSpinTerminal)
      (fun x => (scalarTimeChainAverage β (dyadicIntervals α n q (Real.toNNReal (1-q)))
        scalarSpinTerminal scalarMagnetization x)^2) 0) atTop (𝓝 (scalarCDFOverlap β α q)) := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : t ≤ 1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ hq.1,NNReal.coe_one]; exact hq.2
  have hr : r ≤ 1 := by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ (sub_nonneg.mpr hq.2),NNReal.coe_one]; linarith [hq.1]
  let F (n : ℕ) := dyadicScalar β α n q r scalarSpinTerminal
  let A (n : ℕ) := fun x => (rootGradient 0 (F n) x)^2
  have hsq := scalarCDFGradient_sq_regular β ha hm q r hr
  have hAu : TendstoUniformly A (fun x => (scalarCDFGradient β α q r x)^2) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp (dyadicScalar_gradient_uniform β ha hm q r hr)
      (ε/2) (half_pos hε)] with n hn x
    rw [Real.dist_eq,abs_sub_comm]
    have H := abs_sq_sub_sq_le_two (dyadicScalar_spin_bounds β ha n q r x).1
      (scalarCDF_derivative_bounds β ha hm q r hr x).1
    have H' : |rootGradient 0 (F n) x-scalarCDFGradient β α q r x|<ε/2 := by
      simpa only [Real.dist_eq,abs_sub_comm] using hn x
    exact H.trans_lt (by nlinarith)
  have H := dyadicScalarAverage_varying_terminal β ha hm
    (fun n => dyadicScalar_regular scalarSpinTerminal_regular β α n q r)
    (scalarCDFValue_regular β ha hm q r hr)
    (show ∀ n, Continuous (A n) from fun n =>
      (scalarTimeChain_spin_gradient_lipschitz β _
        (fun _ hp => dyadicIntervals_mass_bounds ha n q r hp)).continuous.pow 2)
    hsq.1 hsq.2.1 (scalarCDFValue_lipschitz β ha hm q r hr)
    (B:=1) (C:=2)
    (fun n x => by
      change |(rootGradient 0 (F n) x)^2| ≤ (1:ℝ)
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (dyadicScalar_spin_bounds β ha n q r x).1)
    hsq.2.2.1 hsq.2.2.2 (dyadicScalar_value_uniform β ha hm q r hr) hAu 0 t ht 0
  simp_rw [scalarTimeChainAverage_spin_gradient]
  change Tendsto (fun n => dyadicScalarAverage β α n 0 t (F n) (A n) 0)
    atTop (𝓝 (scalarCDFOverlap β α q))
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairEndpoint
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

theorem splitPairMass_zero {k : ℕ} (a : ℕ) (m : Fin (k+1) → ℝ) (h : m 0=0) :
    splitPairMass a m 0=0 := by simp [splitPairMass,h]

theorem splitPairMass_mem {n : ℕ} (a : ℕ) (m : Fin n → ℝ)
    (h : ∀ i, m i∈Icc (0:ℝ) 1) (i : Fin n) : splitPairMass a m i∈Icc (0:ℝ) 1 := by
  have H := h i
  unfold splitPairMass
  split_ifs <;> constructor <;> linarith [H.1,H.2]

theorem splitPairMass_mono {n : ℕ} (a : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, 0 ≤ m i) (h : Monotone m) : Monotone (splitPairMass a m) := by
  intro i j hij
  have H := h hij
  have H0 := hm j
  simp only [splitPairMass]
  split_ifs with hi hj hj
  · linarith
  · linarith
  · have hv : i.val ≤ j.val := hij
    omega
  · exact H

theorem splitPairBlock_pressure (n a b : ℕ) (hn : n=a+b) (m v : Fin n → ℝ) :
    vectorBlockHierarchy 2 n (splitPairMass a m) (splitPairVector a v)
      (fun p => scalarSpinTerminal p.1+scalarSpinTerminal p.2) (0:ℝ × ℝ)=
      2*scalarHierarchy n m v scalarSpinTerminal 0 := by
  subst n
  rw [splitPairHierarchy]
  exact pairSplit_pressure a b m v scalarSpinTerminal_regular 0

theorem splitPairBlock_observable (n a b : ℕ) (hn : n=a+b) (m v : Fin n → ℝ) :
    vectorBlockHierarchyAverage 2 n (splitPairMass a m) (splitPairVector a v)
      (fun p => scalarSpinTerminal p.1+scalarSpinTerminal p.2)
      (fun p => scalarMagnetization p.1*scalarMagnetization p.2) (0:ℝ × ℝ)=
      scalarMomentSquare n m v scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  subst n
  rw [splitPairHierarchyAverage]
  exact pairSplit_overlap a b m v scalarSpinTerminal_regular scalarMagnetization 0

theorem pairSiteValue (a b : ℕ) (β : ℝ) (m c : Fin (a+b+1) → ℝ) (hm : m 0=0) :
    vectorHierarchy ((a+b+1)*2)
      (siteBlockMass 2 (a+b) (zeroInitialAtoms (a+b) (splitPairMass a m)))
      (matrixSiteVector β (splitPairFactor a c) (fun (s : Config 2) i => spin (s i)))
      (siteValueTerminal (fun _ : Config 2 => 0)) 0=
      2*scalarHierarchy (a+b+1) m (fun i => β*c i) scalarSpinTerminal 0 := by
  rw [funext (siteBlockMass_zeroInitial (splitPairMass a m) (splitPairMass_zero a m hm))]
  simp only [splitPairFactor_vector]
  have H := congrFun (vectorHierarchy_pullback pairSpinMap ((a+b+1)*2)
    (fun j => splitPairMass a m (finProdFinEquiv.symm j).1)
    (fun j => splitPairVector a (fun i => β*c i) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    (siteValueTerminal (fun _ : Config 2 => 0))) (0:ℝ × ℝ)
  simp only [Function.comp_apply,map_zero] at H
  rw [← H,pairSpin_terminal,vectorHierarchy_blocks]
  exact splitPairBlock_pressure _ a (b+1) (by omega) m _

theorem pairSiteObservable (a b : ℕ) (β : ℝ) (m c : Fin (a+b+1) → ℝ) (hm : m 0=0) :
    vectorHierarchyAverage ((a+b+1)*2)
      (siteBlockMass 2 (a+b) (zeroInitialAtoms (a+b) (splitPairMass a m)))
      (matrixSiteVector β (splitPairFactor a c) (fun (s : Config 2) i => spin (s i)))
      (siteValueTerminal (fun _ : Config 2 => 0))
      (affineMoment (fun _ : Config 2 => 0) (fun s => ContinuousLinearMap.proj s)
        (matrixSiteWeight pairMultiplier (fun (s : Config 2) i => spin (s i)))) 0=
      scalarMomentSquare (a+b+1) m (fun i => β*c i) scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0 := by
  rw [funext (siteBlockMass_zeroInitial (splitPairMass a m) (splitPairMass_zero a m hm))]
  simp only [splitPairFactor_vector,pairMultiplier_observable]
  have H := congrFun (vectorHierarchyAverage_pullback pairSpinMap ((a+b+1)*2)
    (fun j => splitPairMass a m (finProdFinEquiv.symm j).1)
    (fun j => splitPairVector a (fun i => β*c i) (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
    (siteValueTerminal (fun _ : Config 2 => 0))
    (affineMoment (fun _ : Config 2 => 0) (fun s => ContinuousLinearMap.proj s) pairSpinObservable)) (0:ℝ × ℝ)
  simp only [Function.comp_apply,map_zero] at H
  rw [← H,pairSpin_terminal,pairSpin_thermal_observable,vectorHierarchyAverage_blocks]
  exact splitPairBlock_observable _ a (b+1) (by omega) m _

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairPenalty
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

theorem finitePrefix_shared {n : ℕ} (a : ℕ) (v : Fin n → ℝ) (j : Fin n) (hj : j.val<a) :
    finitePrefix (fun l => if l.val<a then v l else 0) j=finitePrefix v j := by
  apply Finset.sum_congr rfl
  intro l _
  by_cases hl : l ≤ j
  · have H : l.val<a := lt_of_le_of_lt hl hj
    simp only [ite_eq_left hl,ite_eq_left H]
  · simp only [ite_eq_right hl]

theorem splitPairFactor_penalty {k : ℕ} (a : ℕ) (m c : Fin (k+1) → ℝ) :
    let D := factorPath 2 2 k (splitPairFactor a c) (Fin.last k)
    matrixSquare 2 D-2*matrixInner 2 D D+
      (∑ j, zeroInitialAtoms k (splitPairMass a m) j*matrixSquare 2 (factorPath 2 2 k (splitPairFactor a c) j))=
      -2*∑ i : Fin k, m i.succ*((finitePrefix (fun l => (c l)^2) i.succ)^2-
        (finitePrefix (fun l => (c l)^2) i.castSucc)^2) := by
  dsimp only
  rw [matrixInner_self,zeroInitialAtoms_sum_mul_parts]
  have H (i : Fin k) :
      splitPairMass a m i.succ*(matrixSquare 2 (factorPath 2 2 k (splitPairFactor a c) i.succ)-
        matrixSquare 2 (factorPath 2 2 k (splitPairFactor a c) i.castSucc))=
      2*(m i.succ*((finitePrefix (fun l => (c l)^2) i.succ)^2-
        (finitePrefix (fun l => (c l)^2) i.castSucc)^2)) := by
    simp only [splitPairFactor_path,pairMatrix_square,splitPairMass]
    by_cases hi : i.succ.val<a
    · have hp : i.castSucc.val<a := by simpa only [Fin.val_castSucc] using Nat.lt_of_succ_lt hi
      rw [ite_eq_left hi,finitePrefix_shared a _ i.succ hi,finitePrefix_shared a _ i.castSucc hp]
      ring
    · have HP := finitePrefix_succ k (fun l => if l.val<a then (c l)^2 else 0) i
      rw [ite_eq_right hi,add_zero] at HP
      rw [ite_eq_right hi,HP]
      ring
  simp_rw [H]
  rw [← Finset.mul_sum]
  ring

theorem splitPairFactor_last {k : ℕ} (a : ℕ) (c : Fin (k+1) → ℝ) (hc : ∑ l, (c l)^2=1) :
    factorPath 2 2 k (splitPairFactor a c) (Fin.last k)=
      pairMatrix 1 (∑ l, if l.val<a then (c l)^2 else 0) := by
  rw [splitPairFactor_path,finitePrefix_last,finitePrefix_last,hc]

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairFinitePressure
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

theorem pairConstrainedPressure_finite {N : ℕ} (hN : 0<N) (a b : ℕ) (β : ℝ)
    (m c : Fin (a+b+1) → ℝ) (hm0 : m 0=0) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmono : Monotone m) (hc : ∑ i, (c i)^2=1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 (∑ i, if i.val<a then (c i)^2 else 0)))) :
    let q := ∑ i, if i.val<a then (c i)^2 else 0
    matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤
      2*(scalarHierarchy (a+b+1) m (fun i => β*c i) scalarSpinTerminal 0-
        β^2/4*∑ i : Fin (a+b), m i.succ*
          ((finitePrefix (fun l => (c l)^2) i.succ)^2-(finitePrefix (fun l => (c l)^2) i.castSucc)^2))-
      (scalarMomentSquare (a+b+1) m (fun i => β*c i) scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0-q)^2/2 := by
  dsimp only
  have H := matrixConstrainedPressure_quadratic_gap hN (by norm_num : 0<2) β _ pairMultiplier hD
    (splitPairFactor a c) (zeroInitialAtoms (a+b) (splitPairMass a m))
    (zeroInitialAtoms_nonneg _ (splitPairMass_mem a m hm) (splitPairMass_mono a m (fun i => (hm i).1) hmono))
    (zeroInitialAtoms_sum _) (by intro s; rw [pairMultiplier_observable]; exact pairSpinObservable_bound s)
  dsimp only at H
  rw [pairSiteValue a b β m c hm0,pairSiteObservable a b β m c hm0,pairMultiplier_inner] at H
  have HP := splitPairFactor_penalty a m c
  rw [splitPairFactor_last a c hc] at HP
  rw [splitPairFactor_last a c hc] at H
  rw [HP] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairTimeChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem pairConstrainedPressure_twoChains {N : ℕ} (hN : 0<N) (a b : ℕ) (β : ℝ)
    (l : Fin (a+1) → ℝ × ℝ≥0) (r : Fin (b+1) → ℝ × ℝ≥0)
    (hm0 : (l 0).1=0) (ht0 : (l 0).2=0)
    (hm : ∀ i, (Fin.append l r i).1∈Icc (0:ℝ) 1)
    (hmono : Monotone (fun i => (Fin.append l r i).1))
    (ht : (∑ i, ((l i).2:ℝ))+(∑ i, ((r i).2:ℝ))=1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 (∑ i, ((l i).2:ℝ))))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 (∑ i, ((l i).2:ℝ))) ≤
      2*(scalarTimeChain β (List.ofFn l++List.ofFn r) scalarSpinTerminal 0-
        β^2/4*chainQuadraticPenalty 0 (List.ofFn l++List.ofFn r))-
      (scalarTimeChainAverage β (List.ofFn l) (scalarTimeChain β (List.ofFn r) scalarSpinTerminal)
        (fun x => (scalarTimeChainAverage β (List.ofFn r) scalarSpinTerminal scalarMagnetization x)^2) 0-
        (∑ i, ((l i).2:ℝ)))^2/2 := by
  let p := Fin.append l r
  let c (i : Fin ((a+1)+b+1)) := Real.sqrt ((p i).2:ℝ)
  have hc (i) : (c i)^2=((p i).2:ℝ) := Real.sq_sqrt (p i).2.coe_nonneg
  have hsum : ∑ i, (c i)^2=1 := by
    simp only [hc]
    change (∑ i : Fin ((a+1)+(b+1)), ((Fin.append l r i).2:ℝ))=1
    rw [Fin.sum_univ_add]
    simpa only [Fin.append_left,Fin.append_right] using ht
  have hq : (∑ i : Fin ((a+1)+b+1), if i.val<a+1 then (c i)^2 else 0)=∑ i, ((l i).2:ℝ) := by
    simp only [hc]
    change (∑ i : Fin ((a+1)+(b+1)), if i.val<a+1 then ((Fin.append l r i).2:ℝ) else 0)=_
    rw [Fin.sum_univ_add]
    simp only [Fin.val_castAdd,Fin.val_natAdd,Fin.append_left,Fin.append_right]
    simp only [Fin.is_lt,ite_true,Nat.not_lt.mpr (Nat.le_add_right _ _),ite_false,Finset.sum_const_zero,add_zero]
  have H := pairConstrainedPressure_finite hN (a+1) b β (fun i => (p i).1) c
    (by simpa only [p,show (0 : Fin ((a+1)+(b+1)))=(0:Fin (a+1)).castAdd (b+1) from rfl,Fin.append_left] using hm0) hm hmono hsum (by simpa only [hq] using hD)
  dsimp only at H
  rw [hq] at H
  have hp0 : (p 0).2=0 := by simpa only [p,show (0 : Fin ((a+1)+(b+1)))=(0:Fin (a+1)).castAdd (b+1) from rfl,Fin.append_left] using ht0
  have HP := chainQuadraticPenalty_ofFn_zero ((a+1)+b) p hp0
  change chainQuadraticPenalty 0 (List.ofFn (Fin.append l r))=_ at HP
  rw [List.ofFn_fin_append] at HP
  simp only [hc] at H
  rw [← HP] at H
  have HV : scalarTimeChain β (List.ofFn l++List.ofFn r) scalarSpinTerminal=
      scalarHierarchy ((a+1)+b+1) (fun i => (p i).1) (fun i => β*c i) scalarSpinTerminal := by
    rw [← List.ofFn_fin_append]
    exact scalarTimeChain_ofFn β _ _ _ _
  rw [← HV] at H
  have HG : scalarMomentSquare ((a+1)+b+1) (fun i => (p i).1) (fun i => β*c i)
      scalarSpinTerminal scalarMagnetization ⟨a+1,by omega⟩=
      scalarTimeChainAverage β (List.ofFn l) (scalarTimeChain β (List.ofFn r) scalarSpinTerminal)
        (fun x => (scalarTimeChainAverage β (List.ofFn r) scalarSpinTerminal scalarMagnetization x)^2) := by
    change scalarMomentSquare ((a+1)+(b+1)) (fun i => (p i).1)
      (fun i => β*Real.sqrt ((p i).2:ℝ)) scalarSpinTerminal scalarMagnetization ⟨a+1,by omega⟩=_
    rw [scalarMomentSquare_split (a+1) (b+1)]
    simp only [p,Fin.append_left,Fin.append_right]
    rw [scalarTimeChain_ofFn,scalarTimeChainAverage_ofFn,scalarTimeChainAverage_ofFn]
  rw [HG] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairLists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem pairConstrainedPressure_lists {N : ℕ} (hN : 0<N) (β : ℝ)
    (l r : List (ℝ × ℝ≥0)) (hm : ∀ p∈l++r, p.1∈Icc (0:ℝ) 1)
    (hmono : (l++r).Pairwise (fun p q => p.1 ≤ q.1))
    (ht : chainDuration l+chainDuration r=1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 (chainDuration l)))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 (chainDuration l)) ≤
      2*(scalarTimeChain β (l++r) scalarSpinTerminal 0-
        β^2/4*chainQuadraticPenalty 0 (l++r))-
      (scalarTimeChainAverage β l (scalarTimeChain β r scalarSpinTerminal)
        (fun x => (scalarTimeChainAverage β r scalarSpinTerminal scalarMagnetization x)^2) 0-
        (chainDuration l:ℝ))^2/2 := by
  let L : Fin (l.length+1) → ℝ × ℝ≥0 := Fin.cons (0,0) l.get
  let R : Fin (r.length+1) → ℝ × ℝ≥0 := Fin.snoc r.get (1,0)
  have hL : List.ofFn L=(0,0)::l := by rw [List.ofFn_succ]; simp [L]
  have hR : List.ofFn R=r++[(1,0)] := by rw [List.ofFn_succ']; simp [R,List.concat_eq_append]
  have hLR : List.ofFn (Fin.append L R)=(0,0)::((l++r)++[(1,0)]) := by
    rw [List.ofFn_fin_append,hL,hR]
    simp only [List.cons_append,List.append_assoc]
  have hbounds (p) (hp : p∈(0,0)::((l++r)++[(1,0)])) : p.1∈Icc (0:ℝ) 1 := by
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|hp|rfl
    · norm_num
    · exact hm p (List.mem_append.mpr hp)
    · norm_num
  have hsorted : ((0,0)::((l++r)++[(1,0)])).Pairwise (fun p q => p.1 ≤ q.1) := by
    apply List.pairwise_cons.mpr
    constructor
    · intro p hp
      exact (hbounds p (List.mem_cons_of_mem _ hp)).1
    · apply List.pairwise_append.mpr
      refine ⟨hmono,by simp,?_⟩
      intro p hp q hq
      obtain rfl := List.mem_singleton.mp hq
      exact (hm p hp).2
  have hmass (i) : (Fin.append L R i).1∈Icc (0:ℝ) 1 := by
    apply hbounds
    rw [← hLR]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hmon : Monotone (fun i => (Fin.append L R i).1) := by
    rw [← hLR,List.pairwise_ofFn] at hsorted
    intro i j hij
    rcases lt_or_eq_of_le hij with hij|rfl
    · exact hsorted hij
    · exact le_rfl
  have hdL : (∑ i, ((L i).2:ℝ))=chainDuration l := by
    rw [← NNReal.coe_sum,← chainDuration_ofFn,hL]
    simp
  have hdR : (∑ i, ((R i).2:ℝ))=chainDuration r := by
    rw [← NNReal.coe_sum,← chainDuration_ofFn,hR]
    simp [chainDuration]
  have htime : (∑ i, ((L i).2:ℝ))+(∑ i, ((R i).2:ℝ))=1 := by
    rw [hdL,hdR,← NNReal.coe_add,ht,NNReal.coe_one]
  have H := pairConstrainedPressure_twoChains hN l.length r.length β L R
    (by simp [L]) (by simp [L]) hmass hmon htime (by simpa only [hdL] using hD)
  rw [hL,hR,hdL] at H
  simp only [scalarTimeChainAverage_snoc_zero,scalarTimeChain_snoc_zero,
    scalarTimeChainAverage_cons_zero,List.cons_append] at H
  have hpen : chainQuadraticPenalty 0 ((0,0)::(l++(r++[(1,0)])))=
      chainQuadraticPenalty 0 (l++r) := by
    rw [chainQuadraticPenalty_zero,← List.append_assoc,chainQuadraticPenalty_append,
      chainQuadraticPenalty_singleton]
    simp
  rw [hpen] at H
  have hval : scalarTimeChain β ((0,0)::(l++(r++[(1,0)]))) scalarSpinTerminal=
      scalarTimeChain β (l++r) scalarSpinTerminal := by
    rw [← List.append_assoc,scalarTimeChain]
    simp only [scalarTimeStep_zero]
    exact scalarTimeChain_snoc_zero β 1 (l++r) scalarSpinTerminal
  rw [hval] at H
  exact H

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairContinuumPressure
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

theorem pairConstrainedPressure_continuum {N : ℕ} (hN : 0<N) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 q))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤
      2*scalarCDFParisi β α-(scalarCDFOverlap β α q-q)^2/2 := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal _ hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hq.2
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith [hq.1]
  let l (n : ℕ) := dyadicIntervals α n 0 t
  let R (n : ℕ) := dyadicIntervals α n q r
  have hvalue : Tendsto (fun n => scalarTimeChain β (l n++R n) scalarSpinTerminal 0)
      atTop (𝓝 (scalarCDFValue β α 0 1 0)) := by
    have H := (dyadicScalar_varying_terminal_uniform β ha α.mono
      (fun n => dyadicScalar_regular scalarSpinTerminal_regular β α n q r)
      (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β ha α.mono q r hr1)
      (dyadicScalar_value_uniform β ha α.mono q r hr1) 0 t ht1).tendsto_at 0
    have he := scalarCDFValue_suffix_semigroup β α ha h1 (s:=0) le_rfl hq.1 hq.2
    simp only [sub_zero,Real.toNNReal_one] at he
    rw [← he] at H
    simpa only [scalarTimeChain_append,l,R,dyadicScalar] using H
  have hpen : Tendsto (fun n => chainQuadraticPenalty 0 (l n++R n)) atTop
      (𝓝 (2*∫ u in Icc (0:ℝ) 1, u*α u)) := by
    have H := (dyadicPenalty_tendsto α.mono 0 t le_rfl (by rw [zero_add,ht]; exact hq.2)).add
      (dyadicPenalty_tendsto α.mono q r hq.1 (by rw [hr]; linarith))
    have hi (a b : ℝ) : IntervalIntegrable (fun u => u*α u) volume a b :=
      α.mono.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
    have he : 2*(∫ u in (0:ℝ)..0+t, u*α u)+2*(∫ u in q..q+r, u*α u)=
        2*∫ u in Icc (0:ℝ) 1, u*α u := by
      rw [zero_add,ht,hr,show q+(1-q)=1 by ring,← mul_add,
        intervalIntegral.integral_add_adjacent_intervals (hi 0 q) (hi q 1),
        intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
    rw [he] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    rw [chainQuadraticPenalty_append]
    simp only [l,R,dyadicIntervals_duration,zero_add,ht]
  have hgamma := dyadicPairOverlap_tendsto β ha α.mono hq
  have Hlimit := (hvalue.sub (hpen.const_mul (β^2/4))).const_mul 2 |>.sub
    (((hgamma.sub_const q).pow 2).div_const 2)
  have Hseq (n : ℕ) : matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤
      2*(scalarTimeChain β (l n++R n) scalarSpinTerminal 0-
        β^2/4*chainQuadraticPenalty 0 (l n++R n))-
        (scalarTimeChainAverage β (l n) (scalarTimeChain β (R n) scalarSpinTerminal)
          (fun x => (scalarTimeChainAverage β (R n) scalarSpinTerminal scalarMagnetization x)^2) 0-q)^2/2 := by
    have hm (p) (hp : p∈l n++R n) : p.1∈Icc (0:ℝ) 1 := by
      rcases List.mem_append.mp hp with hp|hp
      · exact dyadicIntervals_mass_bounds ha n 0 t hp
      · exact dyadicIntervals_mass_bounds ha n q r hp
    have hmono : (l n++R n).Pairwise (fun p q => p.1 ≤ q.1) := by
      refine List.pairwise_append.mpr ⟨dyadicIntervals_pairwise α.mono n 0 t,
        dyadicIntervals_pairwise α.mono n q r,?_⟩
      intro p hp p' hp'
      have H := (dyadicIntervals_mem_bounds α.mono n 0 t hp).2.1
      have H' := (dyadicIntervals_mem_bounds α.mono n q r hp').1
      rw [zero_add,ht] at H
      exact H.trans H'
    have hd : chainDuration (l n)+chainDuration (R n)=1 := by
      simp only [l,R,dyadicIntervals_duration]
      apply NNReal.eq
      simp only [NNReal.coe_add,NNReal.coe_one,ht,hr]
      ring
    have HL : (chainDuration (l n):ℝ)=q := by dsimp only [l]; rw [dyadicIntervals_duration,ht]
    have H := pairConstrainedPressure_lists hN β (l n) (R n) hm hmono hd (by simpa only [HL] using hD)
    simpa only [HL] using H
  have H := ge_of_tendsto Hlimit (Eventually.of_forall Hseq)
  calc
    _ ≤ 2*(scalarCDFValue β α 0 1 0-β^2/4*(2*∫ u in Icc (0:ℝ) 1, u*α u))-
        (scalarCDFOverlap β α q-q)^2/2 := H
    _ = _ := by rw [scalarCDFParisi]; ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_ReplicaCoordinates
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

theorem replicaGram_pair_overlap {n : ℕ} (hn : 0<n) (s : ReplicaConfig n 2) :
    replicaGram s=pairMatrix 1 (overlap (s 0) (s 1)) := by
  rw [replicaGram_pair hn]
  congr 1
  exact (overlap_eq_codeOverlap _ _).symm

theorem replicaGram_feasible {n d : ℕ} (s : ReplicaConfig n d) :
    Nonempty (MatrixStates n d (replicaGram s)) :=
  (matrixReplicaSet_nonempty_iff _).mp ⟨s,(mem_matrixReplicaSet _ _).mpr rfl⟩

@[simp] theorem tripleR_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleR (replicaFlip 0 s)= -tripleR s := by
  simp only [tripleR,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

@[simp] theorem tripleDelta_flip {n : ℕ} (s : ReplicaConfig n 3) :
    tripleDelta (replicaFlip 0 s)= -tripleDelta s := by
  simp only [tripleDelta,replicaFlip]
  norm_num only [ite_true,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,ite_false]
  rw [overlap_comm (flip (s 0)),overlap_flip_right,
    overlap_comm (flip (s 0)),overlap_flip_right]
  rw [overlap_comm (s 1),overlap_comm (s 2)]
  ring

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Replicas_PairGibbsGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem pairMismatch_pressure_gap_oai {n : ℕ} (hn : 0<n) (β : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hmin : scalarCDFParisi β α=finiteParisiInf β)
    {e : ℝ} (he : 0≤e) {s : ReplicaConfig n 2} (hs : s∈pairMismatchSet n β α e) :
    matrixConstrainedPressure n 2 β (replicaGram s)≤2*finiteParisiInf β-e^2/2 := by
  classical
  obtain ⟨hs0,hse⟩ := (Finset.mem_filter.mp hs).2
  have hq : overlap (s 0) (s 1)∈Icc (0:ℝ) 1 := ⟨hs0,(abs_le.mp (abs_overlap_le_one _ _)).2⟩
  have hfeas := replicaGram_feasible s
  rw [replicaGram_pair_overlap hn] at hfeas ⊢
  have H := pairConstrainedPressure_continuum hn β α hα hα1 hq hfeas
  rw [hmin] at H
  have he2 := pow_le_pow_left₀ he hse 2
  rw [sq_abs] at he2
  nlinarith only [H,he2]

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.pairMismatch_pressure_gap_oai := @OAI.SK.Analytic.pairMismatch_pressure_gap_oai

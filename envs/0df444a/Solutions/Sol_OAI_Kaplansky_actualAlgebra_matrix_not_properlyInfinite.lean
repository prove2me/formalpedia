-- Prove2me | solution 1 for OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:50:49.44569+00:00
-- url     : https://prove2.me/submissions/f05f94e4-6e13-464c-b451-5e533145d3b4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf010
import Theorems.Thm_OAI_Kaplansky_retainedGrouped_no_test_frame

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Shift
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert shifts, their relations, and block operator bounds. -/

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)]

variable [∀ j, CompleteSpace (E j)]

theorem forwardShift_single (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (j : ℕ) (v : E j) : forwardShift T hT (lp.single 2 j v) =
      lp.single 2 (j+1) (T j v) := by
  have he : lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v) =
      lp.single 2 j (T j v) := by
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [Pi.single_eq_of_ne hk]
  change successorInclusion (lp.mapCLM 2 T zero_le_one hT (lp.single 2 j v)) = _
  rw [he]
  exact OrthogonalFamily.linearIsometry_apply_single _ _

end Kaplansky

end

noncomputable section
open scoped BigOperators ENNReal
namespace Kaplansky
variable {E : ℕ → Type*} [∀ j, NormedAddCommGroup (E j)]
  [∀ j, InnerProductSpace ℂ (E j)] [∀ j, CompleteSpace (E j)]

/-- The adjoint lowers degree, using the adjoint of the actual block. -/
theorem forwardShift_adjoint_apply (T : ∀ j, E j →L[ℂ] E (j+1)) (hT : ∀ j, ‖T j‖ ≤ 1)
    (f : FiberHilbertSum E) (j : ℕ) :
    (forwardShift T hT).adjoint f j = (T j).adjoint (f (j+1)) := by
  apply ext_inner_left ℂ
  intro v
  rw [← lp.inner_single_left j v, ContinuousLinearMap.adjoint_inner_right,
    forwardShift_single, lp.inner_single_left, ContinuousLinearMap.adjoint_inner_right]

theorem forwardShift_adjoint_single_zero (T : ∀ j, E j →L[ℂ] E (j+1))
    (hT : ∀ j, ‖T j‖ ≤ 1) (v : E 0) :
    (forwardShift T hT).adjoint (lp.single 2 0 v) = 0 := by
  ext j
  rw [forwardShift_adjoint_apply]
  simp

theorem forwardShift_adjoint_single_succ (T : ∀ j, E j →L[ℂ] E (j+1))
    (hT : ∀ j, ‖T j‖ ≤ 1) (j : ℕ) (v : E (j+1)) :
    (forwardShift T hT).adjoint (lp.single 2 (j+1) v) =
      lp.single 2 j ((T j).adjoint v) := by
  ext k
  rw [forwardShift_adjoint_apply]
  by_cases hk : k = j
  · subst k; simp
  · simp [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne (show k+1 ≠ j+1 by omega)]

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundleWords
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Continuous bundle words and their finite-tower Hilbert realization. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ}

section Evaluation

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

theorem bundleWordValue_raise_single (W : BundleWordValue a) (i : Fin 24)
    (y : ProjectiveProduct K) (v : (a 0).Fiber y) :
    forwardShift (towerOperator X i y) (towerOperator_norm X i y)
      (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 W.level (W.map y v)) =
      lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 (W.raise X i).level ((W.raise X i).map y v) := by
  exact forwardShift_single (towerOperator X i y) (towerOperator_norm X i y) W.level (W.map y v)

theorem bundleWordValue_lower_single (W : BundleWordValue a) (i : Fin 24)
    (y : ProjectiveProduct K) (v : (a 0).Fiber y) :
    (forwardShift (towerOperator X i y) (towerOperator_norm X i y)).adjoint
      (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 W.level (W.map y v)) =
      lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 (W.lower X i).level ((W.lower X i).map y v) := by
  obtain ⟨k,T,hT⟩ := W
  cases k with
  | zero =>
    exact (forwardShift_adjoint_single_zero (towerOperator X i y)
      (towerOperator_norm X i y) (T y v)).trans
      (lp.single_zero (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0).symm
  | succ k =>
    have hs := forwardShift_adjoint_single_succ (towerOperator X i y)
      (towerOperator_norm X i y) k (T y v)
    let U : NormalizedHermitianTuple (EuclideanSpace ℂ (a k).Slot)
      (EuclideanSpace ℂ (a (k+1)).Slot) := (X k).tuple y
    have hAdj := U.operator_adjoint i
    have hval := congrArg (fun f : EuclideanSpace ℂ (a (k+1)).Slot →L[ℂ]
      EuclideanSpace ℂ (a k).Slot => f (T y v)) hAdj
    exact hs.trans (congrArg (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 k) hval)

/-- The continuous intrinsic monomial is exactly the Hilbert-shift word
restricted to level zero, including adjoints at zero and constant words. -/
theorem bundleWordValue_shift_eval (w : List (Bool × Fin 24))
    (y : ProjectiveProduct K) (v : (a 0).Fiber y) :
    applyWord (shiftLetter (fun i j => towerOperator X i y j)
      (fun i j => towerOperator_norm X i y j)) w (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0 v) =
      lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 (bundleWordValue X w).level ((bundleWordValue X w).map y v) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b,i⟩ := l
    cases b with
    | false =>
      change forwardShift (towerOperator X i y) (towerOperator_norm X i y)
        (applyWord _ w (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0 v)) = _
      rw [ih]
      exact bundleWordValue_raise_single X _ i y v
    | true =>
      change (forwardShift (towerOperator X i y) (towerOperator_norm X i y)).adjoint
        (applyWord _ w (lp.single (E := fun j => EuclideanSpace ℂ (a j).Slot) 2 0 v)) = _
      rw [ih]
      exact bundleWordValue_lower_single X _ i y v

end Evaluation

open scoped BigOperators

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Polynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Star-word polynomials and matrix polynomial density in the generated algebra. -/

noncomputable section
open scoped BigOperators Pointwise
namespace Kaplansky
variable {A : Type*} [CStarAlgebra A] {N : ℕ}

/-- Every element of the actual algebraic star-adjoin is a finite sum of
explicit generator/adjoint words; this includes scalar constants. -/
theorem starAdjoin_exists_wordPolynomial (x : Fin N → A) {z : A}
    (hz : z ∈ StarAlgebra.adjoin ℂ (Set.range x)) :
    ∃ p : StarWordPolynomial N, evalStarWordPolynomial x p=z := by
  change z ∈ (StarAlgebra.adjoin ℂ (Set.range x)).toSubalgebra.toSubmodule at hz
  rw [starAdjoin_eq_wordSpan,← Finsupp.range_linearCombination] at hz
  exact hz

/-- Norm approximation in the actual closed generated algebra by a
finite star polynomial. No density hypothesis is supplied by the caller. -/
theorem generated_exists_wordPolynomial (x : Fin N → A) (z : generatedAlgebra (Set.range x))
    {ε : ℝ} (hε : 0<ε) :
    ∃ p : StarWordPolynomial N, ‖evalStarWordPolynomial x p - (z : A)‖ < ε := by
  have hz : (z : A) ∈ closure (StarAlgebra.adjoin ℂ (Set.range x) : Set A) := z.property
  obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp hz ε hε
  obtain ⟨p,rfl⟩ := starAdjoin_exists_wordPolynomial x hw
  refine ⟨p,?_⟩
  simpa only [dist_eq_norm,norm_sub_rev] using hd

end Kaplansky

end

noncomputable section
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] {N : ℕ}

theorem generatedWordPolynomial_dense (x : Fin N → A) : DenseRange (generatedWordPolynomial x) := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨p,hp⟩ := generated_exists_wordPolynomial x z hε
  refine ⟨p,?_⟩
  rw [Subtype.dist_eq,dist_eq_norm]
  change ‖(z : A)-evalStarWordPolynomial x p‖ < ε
  simpa only [norm_sub_rev] using hp

/-- Arbitrary rectangular matrices over the actual generated algebra have
finite star-polynomial approximants in their C*-matrix operator norm. -/
theorem generated_matrix_polynomial_approximation (x : Fin N → A)
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : CStarMatrix m n (generatedAlgebra (Set.range x))) {ε : ℝ} (hε : 0<ε) :
    ∃ p : m → n → StarWordPolynomial N,
      ‖CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial x (p i j)) - W‖ < ε := by
  have hd : DenseRange (fun p : m → n → StarWordPolynomial N =>
      CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial x (p i j))) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => generatedWordPolynomial_dense x))
  obtain ⟨p,hp⟩ := Metric.denseRange_iff.mp hd W ε hε
  exact ⟨p,by simpa only [dist_eq_norm,norm_sub_rev] using hp⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_BundlePolynomials
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.actualHilbert_nontrivial _root_.OAI.Kaplansky.finiteCoordinateBundle_norm _root_.OAI.Kaplansky.finiteCoordinateBundle_normedSpace _root_.OAI.Kaplansky.finiteCoordinateBundle_smooth _root_.OAI.Kaplansky.finiteCoordinateHilbertInner _root_.OAI.Kaplansky.finiteCoordinateHilbertNorm _root_.OAI.Kaplansky.instCompactSpaceSmoothTestBase _root_.OAI.Kaplansky.instT2SpaceSmoothTestBase _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.smoothNext_inner _root_.OAI.Kaplansky.smoothNext_norm _root_.OAI.Kaplansky.smoothTestBundle_inner _root_.OAI.Kaplansky.smoothTestBundle_norm _root_.OAI.Kaplansky.smoothTestBundle_smooth _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Bundle matrix polynomial evaluation, Hilbert isometries, and polynomial action. -/

open Bundle Topology
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann

variable {ι : Type*} {K : ι → ℕ}

variable {a : ℕ → LineStage K} (X : ∀ j, (a j).Step (a (j+1)))

theorem matrixPolynomialTerm_sum {m n : ℕ} (p : Fin m → Fin n → StarWordPolynomial 24)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Bool × Fin 24 → Module.End ℂ V) (v : Fin n → V) (row : Fin m) :
    (∑ k : MatrixPolynomialTermIndex p,
      if (matrixPolynomialTerm p k).row=row then (matrixPolynomialTerm p k).coeff •
        applyWord T (matrixPolynomialTerm p k).word (v (matrixPolynomialTerm p k).col) else 0) =
    ∑ col : Fin n, ∑ w ∈ (p row col).support, p row col w • applyWord T w (v col) := by
  classical
  simp only [MatrixPolynomialTermIndex,Fintype.sum_sigma,matrixPolynomialTerm]
  rw [Finset.sum_eq_single row]
  · simp only [ite_true]
    apply Finset.sum_congr rfl
    intro col _
    exact Finset.sum_coe_sort (p row col).support (fun w => p row col w • applyWord T w (v col))
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro col _
    apply Finset.sum_eq_zero
    intro w _
    exact ite_eq_right hk
  · simp

/-- A matrix monomial has exactly its claimed shift-operator action in
each output row. No unspecified representation or evaluation is used. -/
theorem bundleMatrixTerm_shift_eval {m n R : ℕ} (t : BoundedMatrixTerm m n R)
    (y : ProjectiveProduct K) (v : (towerInputStage a n).Fiber y) (row : Fin m) :
    retainedRowHilbert a m R y row ((bundleMatrixTerm X t).map y v) =
      if t.row=row then t.coeff •
        applyWord (shiftLetter (fun i j => towerOperator X i y j)
          (fun i j => towerOperator_norm X i y j)) t.word
            (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) t.col y v)) else 0 := by
  classical
  let W := bundleWordValue X t.word
  let j : Fin (R+1) := ⟨W.level,Nat.lt_succ_of_le ((bundleWordValue_level_le X t.word).trans t.degree_le)⟩
  change finiteTowerHilbert a R y
    (LineStage.sumProj (fun _ : Fin m => LineStage.sum (fun k : Fin (R+1) => a k.val)) row y
      (t.coeff • LineStage.sumInj (fun _ : Fin m => LineStage.sum (fun k : Fin (R+1) => a k.val)) t.row y
        (LineStage.sumInj (fun k : Fin (R+1) => a k.val) j y
          (W.map y (LineStage.sumProj (fun _ : Fin n => a 0) t.col y v))))) = _
  rw [map_smul,map_smul]
  by_cases h : t.row=row
  · subst row
    simp only [LineStage.sumProj_sumInj_same,finiteTowerHilbert_inj,ite_true]
    rw [bundleWordValue_shift_eval]
    rfl
  · simp [LineStage.sumProj_sumInj_ne _ (Ne.symm h),h]
    rfl

/-- Exact evaluation agreement for the entire rectangular polynomial,
including all coefficients, rows, columns, constants, and adjoints. -/
theorem bundleMatrixPolynomial_shift_eval {m n R : ℕ} {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K)
    (v : (towerInputStage a n).Fiber y) (row : Fin m) :
    retainedRowHilbert a m R y row ((bundleMatrixPolynomial X s t).map y v) =
      ∑ k ∈ s, if (t k).row=row then (t k).coeff •
        applyWord (shiftLetter (fun i j => towerOperator X i y j)
          (fun i j => towerOperator_norm X i y j)) (t k).word
            (lp.single 2 0 (LineStage.sumProj (fun _ : Fin n => a 0) (t k).col y v)) else 0 := by
  simp only [bundleMatrixPolynomial,ContinuousStageMap.sum,LinearMap.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact bundleMatrixTerm_shift_eval X (t k) y v row

/-- The entire intrinsic matrix restriction agrees exactly with evaluation
on bottom-level inputs, through norm-preserving Hilbert embeddings. -/
theorem bundleMatrixPolynomial_evaluation {m n R : ℕ} {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K)
    (v : (towerInputStage a n).Fiber y) :
    retainedMatrixHilbertIsometry a m R y ((bundleMatrixPolynomial X s t).map y v) =
      matrixPolynomialAction X s t y (inputMatrixHilbertIsometry a n y v) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => lp (fun j => (a j).Fiber y) 2)).injective
  funext row
  exact bundleMatrixPolynomial_shift_eval X s t y v row

/-- A lower bound for the evaluated operator passes to the actual finite
bundle map. The two Hilbert inclusions are proved isometries. -/
theorem bundleMatrixPolynomial_lower_bound {m n R : ℕ} {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : ProjectiveProduct K) (c : ℝ)
    (h : ∀ v : MatrixTowerHilbert a n y, c*‖v‖ ≤ ‖matrixPolynomialAction X s t y v‖)
    (v : (towerInputStage a n).Fiber y) :
    c*‖v‖ ≤ ‖(bundleMatrixPolynomial X s t).map y v‖ := by
  have hb := h (inputMatrixHilbertIsometry a n y v)
  rw [← bundleMatrixPolynomial_evaluation,LinearIsometry.norm_map,LinearIsometry.norm_map] at hb
  exact hb

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_MatrixImage
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Matrix restriction, trivial input bundles, and matrix images. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type*} {K : ι → ℕ} {a b : LineStage K}

theorem norm_lower_bound_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : E →ₗ[ℂ] F) {c : ℝ}
    (hc : 0 < c) (hL : ∀ v, c*‖v‖ ≤ ‖L v‖) : Function.Injective L := by
  intro v w h
  have he : L (v-w)=0 := by simp [h]
  have hn := hL (v-w)
  rw [he,norm_zero] at hn
  have hz : ‖v-w‖=0 := by nlinarith [norm_nonneg (v-w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- All matrix input coordinates are actual copies of E₀. -/
theorem actualInput_label_none (m n R : ℕ)
    (s : (towerInputStage (testSequenceStage m R) n).Slot) :
    (towerInputStage (testSequenceStage m R) n).label s=none := by
  revert s
  unfold towerInputStage
  rw [testSequenceStage_prefix (Nat.zero_le R)]
  intro s
  obtain ⟨col,⟨j,k⟩⟩ := s
  have hj : j=0 := Fin.eq_zero j
  subst j
  rfl

theorem actualInput_finrank (m n R : ℕ) (y : SmoothTestBase m R) :
    Module.finrank ℂ ((towerInputStage (testSequenceStage m R) n).Fiber y)=n*testRank m R 0 := by
  change Module.finrank ℂ (EuclideanSpace ℂ (towerInputStage (testSequenceStage m R) n).Slot)=_
  rw [finrank_euclideanSpace]
  unfold towerInputStage
  change Fintype.card (Σ _ : Fin n, (testSequenceStage m R 0).Slot)=_
  rw [Fintype.card_sigma]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  congr 1
  rw [testSequenceStage_prefix (Nat.zero_le R)]
  exact testBundleSlot_card (Nat.zero_le R)

open scoped BigOperators

theorem actualMatrixRestriction_lower_bound {m n R : ℕ} (hm : 0 < m) {T : Type*}
    (s : Finset T) (t : T → BoundedMatrixTerm m n R) (y : SmoothTestBase m R) (c : ℝ)
    (h : ∀ v : MatrixTowerHilbert (testSequenceStage m R) n y,
      c*‖v‖ ≤ ‖matrixPolynomialAction (testSequenceStep (R := R) hm) s t y v‖)
    (v : (towerInputStage (testSequenceStage m R) n).Fiber y) :
    c*‖v‖ ≤ ‖actualMatrixRestriction hm s t y v‖ := by
  change c*‖v‖ ≤ ‖(actualRetainedUnitary m R).fiber y
    ((bundleMatrixPolynomial (testSequenceStep (R := R) hm) s t).map y v)‖
  rw [LinearIsometryEquiv.norm_map]
  exact bundleMatrixPolynomial_lower_bound _ s t y c h v

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Operators
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix operator action and norm perturbation estimates. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {m n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem operatorMatrixAction_norm_le (W : Fin m → Fin n → H →L[ℂ] H)
    {δ : ℝ} (hδ : 0≤δ) (hW : ∀ row col, ‖W row col‖ ≤ δ) (v : HilbertColumns n H) :
    ‖operatorMatrixAction W v‖ ≤ (m*n : ℝ)*δ*‖v‖ := by
  calc
    ‖operatorMatrixAction W v‖ ≤ ∑ row, ‖(PiLp.single 2 row (∑ col, W row col (v col)) : HilbertColumns m H)‖ := norm_sum_le _ _
    _ ≤ ∑ _row : Fin m, ∑ _col : Fin n, δ*‖v‖ := by
      apply Finset.sum_le_sum
      intro row _
      rw [PiLp.norm_single]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro col _
      exact (W row col).le_opNorm (v col) |>.trans
        (mul_le_mul (hW row col) (PiLp.norm_apply_le v col) (norm_nonneg _) hδ)
    _ = _ := by simp; ring

variable [CompleteSpace H]

/-- The rectangular matrix column identity implies a Hilbert-space
isometry, with no finite-dimensional assumption on the Hilbert fibers. -/
theorem operatorMatrixAction_inner (W : Fin m → Fin n → H →L[ℂ] H)
    (hW : ∀ i j, (∑ row, (W row i).adjoint.comp (W row j)) =
      if i=j then ContinuousLinearMap.id ℂ H else 0)
    (v w : HilbertColumns n H) :
    inner ℂ (operatorMatrixAction W v) (operatorMatrixAction W w)=inner ℂ v w := by
  classical
  simp only [PiLp.inner_apply,operatorMatrixAction_apply,sum_inner,inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  have he (j : Fin n) : (∑ row, inner ℂ (W row j (v j)) (W row i (w i))) =
      inner ℂ (v j) ((∑ row, (W row j).adjoint.comp (W row i)) (w i)) := by
    simp only [sum_apply,ContinuousLinearMap.comp_apply,inner_sum,
      ContinuousLinearMap.adjoint_inner_right]
  simp only [he,hW]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem operatorMatrixAction_norm (W : Fin m → Fin n → H →L[ℂ] H)
    (hW : ∀ i j, (∑ row, (W row i).adjoint.comp (W row j)) =
      if i=j then ContinuousLinearMap.id ℂ H else 0) (v : HilbertColumns n H) :
    ‖operatorMatrixAction W v‖=‖v‖ := by
  have he := congrArg RCLike.re (operatorMatrixAction_inner W hW v v)
  simp only [inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (operatorMatrixAction W v),norm_nonneg v]

end Kaplansky

end

noncomputable section
open scoped BigOperators
namespace Kaplansky
variable {m n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem operatorMatrixAction_sub (P W : Fin m → Fin n → H →L[ℂ] H)
    (v : HilbertColumns n H) :
    operatorMatrixAction (P-W) v = operatorMatrixAction P v - operatorMatrixAction W v := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => H)).injective
  funext row
  change operatorMatrixAction (P-W) v row = operatorMatrixAction P v row-operatorMatrixAction W v row
  simp only [operatorMatrixAction_apply,Pi.sub_apply,sub_apply,
    Finset.sum_sub_distrib]

theorem operatorMatrix_perturbation_lower_bound (P W : Fin m → Fin n → H →L[ℂ] H)
    (hW : ∀ v : HilbertColumns n H, ‖operatorMatrixAction W v‖=‖v‖)
    {δ : ℝ} (hδ : 0≤δ) (hclose : ∀ i j, ‖P i j-W i j‖ ≤ δ)
    (v : HilbertColumns n H) :
    (1-(m*n : ℝ)*δ)*‖v‖ ≤ ‖operatorMatrixAction P v‖ := by
  have hd := operatorMatrixAction_norm_le (P-W) hδ hclose v
  rw [operatorMatrixAction_sub] at hd
  have he : operatorMatrixAction W v =
      (operatorMatrixAction W v-operatorMatrixAction P v)+operatorMatrixAction P v := by simp
  have hb : ‖v‖ ≤ ‖operatorMatrixAction P v-operatorMatrixAction W v‖+‖operatorMatrixAction P v‖ := by
    rw [← hW v]
    conv_lhs => rw [he]
    simpa only [norm_sub_rev] using norm_add_le
      (operatorMatrixAction W v-operatorMatrixAction P v) (operatorMatrixAction P v)
  nlinarith

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Quasitrace_Infiniteness
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.complexCoreFiberRealModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Proper infiniteness, isometry columns, and C-star matrix amplification. -/

open scoped ComplexOrder CStarAlgebra BigOperators
namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

variable {m : ℕ}

/-- The rectangular concatenation of a pair of orthogonal isometries has
column adjoint-square identity, with exactly 2m input columns. -/
theorem properIsometryColumns_column (s t : CStarMatrix (Fin m) (Fin m) A)
    (hs : star s*s=1) (ht : star t*t=1) (hst : star s*t=0) (i j : Fin (m+m)) :
    (∑ row, star (properIsometryColumns s t row i)*properIsometryColumns s t row j) =
      if i=j then (1 : A) else 0 := by
  have hts : star t*s=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hst
  let S := CStarMatrix.ofMatrix.symm s
  let T := CStarMatrix.ofMatrix.symm t
  have hS : S.conjTranspose*S=1 := hs
  have hT : T.conjTranspose*T=1 := ht
  have hST : S.conjTranspose*T=0 := hst
  have hTS : T.conjTranspose*S=0 := hts
  have hc : (Matrix.fromCols S T).conjTranspose * Matrix.fromCols S T = 1 := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,Matrix.fromRows_mul_fromCols,
      hS,hT,hST,hTS,Matrix.fromBlocks_one]
  let e := (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m+m)).symm
  have he := congrArg (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A => M (e i) (e j)) hc
  have he' : (∑ row, star (Matrix.fromCols S T row (e i)) *
      Matrix.fromCols S T row (e j)) = if i=j then (1 : A) else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Equiv.apply_eq_iff_eq] using he
  exact he'

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_MatrixTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.retainedBundle_inner _root_.OAI.Kaplansky.retainedBundle_norm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Polynomial evaluation and actual matrix test operators. -/

open scoped BigOperators
namespace Kaplansky

/-- Algebraic words in the constructed bounded-product generators evaluate
as the actual Hilbert-shift words, on arbitrary Hilbert vectors. -/
theorem actualAlgebraWord_eval (z : ActualTestIndex) (w : List (Bool × Fin 24)) (v : ActualHilbert z) :
    algebraStarWord actualBoundedGenerator w z v =
      applyWord (shiftLetter (fun i j => actualTestOperator i z j)
        (fun i j => actualTestOperator_norm i z j)) w v := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b,i⟩ := l
    cases b with
    | false =>
      change forwardShift (actualTestOperator i z) (actualTestOperator_norm i z)
        (algebraStarWord actualBoundedGenerator w z v) = _
      rw [ih]
      rfl
    | true =>
      change (forwardShift (actualTestOperator i z) (actualTestOperator_norm i z)).adjoint
        (algebraStarWord actualBoundedGenerator w z v) = _
      rw [ih]
      rfl

/-- Exact representation of the finitely supported polynomial supplied by
density, before restriction to the bottom-level bundle. -/
theorem actualAlgebraPolynomial_eval (z : ActualTestIndex) (p : StarWordPolynomial 24)
    (v : ActualHilbert z) :
    actualRepresentation z (generatedWordPolynomial actualBoundedGenerator p) v =
      ∑ w ∈ p.support, p w • applyWord (shiftLetter (fun i j => actualTestOperator i z j)
        (fun i j => actualTestOperator_norm i z j)) w v := by
  change (∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w) z v = _
  rw [show ((∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w) z) =
      ∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w z from by
    exact map_sum (boundedProductEval z) _ _]
  simp only [sum_apply,smul_apply]
  exact Finset.sum_congr rfl (fun w _ => congrArg (fun u => p w • u) (actualAlgebraWord_eval z w v))

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem actualRepresentation_matrix_column {m n : ℕ}
    (W : CStarMatrix (Fin m) (Fin n) ActualAlgebra)
    (h : ∀ i j, (∑ row, star (W row i)*W row j)=if i=j then 1 else 0)
    (z : ActualTestIndex) (i j : Fin n) :
    (∑ row, (actualRepresentation z (W row i)).adjoint.comp (actualRepresentation z (W row j))) =
      if i=j then ContinuousLinearMap.id ℂ (ActualHilbert z) else 0 := by
  have he := congrArg (actualRepresentation z) (h i j)
  have hstar (b : ActualAlgebra) : actualRepresentation z (star b) = (actualRepresentation z b).adjoint := rfl
  simp only [map_sum,map_mul,hstar] at he
  have hone : actualRepresentation z 1 = ContinuousLinearMap.id ℂ (ActualHilbert z) := rfl
  have hzero : actualRepresentation z 0 = 0 := rfl
  change (∑ row, (actualRepresentation z (W row i)).adjoint * (actualRepresentation z (W row j))) = _
  by_cases hij : i=j
  · simpa only [hij,ite_true,hone] using he
  · simpa only [hij,ite_false,hzero] using he

theorem actualRepresentation_matrix_entry_close {m n : ℕ}
    (P W : CStarMatrix (Fin m) (Fin n) ActualAlgebra) {δ : ℝ} (h : ‖P-W‖ < δ)
    (z : ActualTestIndex) (i : Fin m) (j : Fin n) :
    ‖actualRepresentation z (P i j)-actualRepresentation z (W i j)‖ ≤ δ := by
  have hentry := CStarMatrix.norm_entry_le_norm (M := P-W) (i := i) (j := j)
  have he := NonUnitalStarAlgHom.norm_apply_le (actualRepresentation z) ((P-W) i j)
  have hsub := map_sub (actualRepresentation z) (P i j) (W i j)
  exact (congrArg norm hsub).symm.le.trans (he.trans (hentry.trans h.le))

/-- The matrix entries supplied by density and their extracted term list
have precisely the same action on the matching actual test Hilbert space. -/
theorem actualPolynomialMatrix_action {m n : ℕ} (hm : 0 < m)
    (p : Fin m → Fin n → StarWordPolynomial 24)
    (y : SmoothTestBase m (matrixPolynomialDegree p))
    (v : MatrixTowerHilbert (testSequenceStage m (matrixPolynomialDegree p)) n y) :
    operatorMatrixAction (fun row col => actualRepresentation
      ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩
      (generatedWordPolynomial actualBoundedGenerator (p row col))) v =
    matrixPolynomialAction (testSequenceStep (R := matrixPolynomialDegree p) hm)
      Finset.univ (matrixPolynomialTerm p) y v := by
  apply (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Fin m => ActualHilbert ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩)).injective
  funext row
  change operatorMatrixAction (fun r c => actualRepresentation
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (generatedWordPolynomial actualBoundedGenerator (p r c))) v row =
    (matrixPolynomialAction (testSequenceStep (R := matrixPolynomialDegree p) hm)
      Finset.univ (matrixPolynomialTerm p) y v) row
  have hleft := operatorMatrixAction_apply (fun r c => actualRepresentation
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (generatedWordPolynomial actualBoundedGenerator (p r c))) v row
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun col _ => actualAlgebraPolynomial_eval
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (p row col) (v col))
  exact hleft.trans (hsum.trans (matrixPolynomialTerm_sum p _ (fun col => v col) row).symm)

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_PolynomialTest
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.ComplexGrassmann.grassmannZero_subsingleton _root_.OAI.Kaplansky.ComplexGrassmann.instTopologicalSpaceCoordinatePunctureFactor _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace _root_.OAI.Kaplansky.projectiveSpaceZero_nonempty _root_.OAI.Kaplansky.twistedHyperplaneFiberInnerProductSpace _root_.OAI.Kaplansky.twistedHyperplaneFiberNormedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial test excluding proper infiniteness of the actual algebra. -/

noncomputable section
open scoped BigOperators
namespace Kaplansky
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem properlyInfinite_actual_polynomial_bound {m : ℕ} (hm : 0 < m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ p : Fin m → Fin (m+m) → StarWordPolynomial 24,
      ∀ (y : SmoothTestBase m (matrixPolynomialDegree p))
        (v : MatrixTowerHilbert (testSequenceStage m (matrixPolynomialDegree p)) (m+m) y),
        (1/2 : ℝ)*‖v‖ ≤ ‖matrixPolynomialAction
          (testSequenceStep (R := matrixPolynomialDegree p) hm) Finset.univ
          (matrixPolynomialTerm p) y v‖ := by
  obtain ⟨s,t,hs,ht,hst⟩ := hpi
  let W := properIsometryColumns s t
  let δ : ℝ := 1/(4*((m : ℝ)*(m+m)+1))
  have hd : 0 < 4*((m : ℝ)*(m+m)+1) := by positivity
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨p,hp⟩ := generated_matrix_polynomial_approximation actualBoundedGenerator W hδ
  refine ⟨p,?_⟩
  intro y v
  let z : ActualTestIndex := ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩
  let P : CStarMatrix (Fin m) (Fin (m+m)) ActualAlgebra :=
    CStarMatrix.ofMatrix (fun i j => generatedWordPolynomial actualBoundedGenerator (p i j))
  let Wz := fun i j => actualRepresentation z (W i j)
  let Pz := fun i j => actualRepresentation z (P i j)
  have hW : ∀ v : HilbertColumns (m+m) (ActualHilbert z), ‖operatorMatrixAction Wz v‖=‖v‖ :=
    operatorMatrixAction_norm Wz
      (actualRepresentation_matrix_column W (properIsometryColumns_column s t hs ht hst) z)
  have hb := operatorMatrix_perturbation_lower_bound Pz Wz hW hδ.le
    (actualRepresentation_matrix_entry_close P W hp z) v
  have hfactor : (1/2 : ℝ) ≤ 1-(m : ℝ)*(m+m)*δ := by
    have he : δ*(4*((m : ℝ)*(m+m)+1))=1 := by
      dsimp [δ]
      field_simp
    have hnonneg : 0 ≤ (m : ℝ)*(m+m) := by positivity
    nlinarith
  simp only [Nat.cast_add] at hb
  have h := (mul_le_mul_of_nonneg_right hfactor (norm_nonneg v)).trans hb
  change (1/2 : ℝ)*‖v‖ ≤ ‖operatorMatrixAction
    (fun i j => actualRepresentation z (generatedWordPolynomial actualBoundedGenerator (p i j))) v‖ at h
  rw [actualPolynomialMatrix_action hm p y v] at h
  exact h

theorem properlyInfinite_retained_frame {m : ℕ} (hm : 0 < m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ R : ℕ, 0<R ∧ Nonempty (ContinuousOrthonormalStageFrame (retainedLineStage m R)
      (2*m*testRank m R 0)) := by
  obtain ⟨p,hp⟩ := properlyInfinite_actual_polynomial_bound hm hpi
  let R := matrixPolynomialDegree p
  let y₀ := testBaseProjectiveHomeomorph m R (bundleTestBasePoint m R)
  let L := actualMatrixStageMap hm Finset.univ (matrixPolynomialTerm p)
  have hi : ∀ y, Function.Injective (L.map y) := fun y =>
    norm_lower_bound_injective _ (by norm_num : (0 : ℝ)<1/2)
      (actualMatrixRestriction_lower_bound hm Finset.univ (matrixPolynomialTerm p) y (1/2) (hp y))
  let f := (trivialMapFrame L (actualInput_label_none m (m+m) R) y₀ hi).normalize
  have hc : Fintype.card (towerInputStage (testSequenceStage m R) (m+m)).Slot =
      2*m*testRank m R 0 := by
    have hr := actualInput_finrank m (m+m) R y₀
    change Module.finrank ℂ (EuclideanSpace ℂ (towerInputStage (testSequenceStage m R) (m+m)).Slot)=_ at hr
    rw [finrank_euclideanSpace] at hr
    rw [hr]
    ring
  refine ⟨R,matrixPolynomialDegree_pos p,?_⟩
  rw [← hc]
  exact ⟨f⟩

end Kaplansky

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Complement
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Kaplansky.lineStageTotal_locallyCompactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Regrouping retained frames and their complement bundles. -/

section
open Bundle
open scoped BigOperators
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- The polynomial image frame is transported to the actual line-bundle
presentation used in the Chern computation. No characteristic-class
nonvanishing or obstruction is a premise. -/
theorem properlyInfinite_regrouped_frame {m : ℕ} (hm : 0 < m)
    (hpi : ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra)) :
    ∃ R : ℕ, 0<R ∧ Nonempty (ContinuousOrthonormalStageFrame (retainedGroupedStage m R)
      (2*m*testRank m R 0)) := by
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_retained_frame hm hpi
  exact ⟨R,hR,⟨f.congr (retainedRegroupingUnitary m R)⟩⟩

end Kaplansky

end

open Bundle Topology
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.BundleTests_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Nonvanishing twisted section classes and the stable retained-bundle obstruction. -/

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem actualAlgebra_matrix_not_properlyInfinite_oai {m : ℕ} (hm : 0 < m) :
    ¬ ProperlyInfinite (CStarMatrix (Fin m) (Fin m) ActualAlgebra) := by
  intro hpi
  obtain ⟨R,hR,⟨f⟩⟩ := properlyInfinite_regrouped_frame hm hpi
  have := retainedGrouped_no_test_frame hm hR
  exact isEmptyElim f

end Kaplansky

end

end OAI
end

theorem solution : type_of% @OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite_oai := @OAI.Kaplansky.actualAlgebra_matrix_not_properlyInfinite_oai

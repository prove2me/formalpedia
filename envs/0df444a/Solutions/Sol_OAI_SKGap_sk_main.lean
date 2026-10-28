-- Prove2me | solution 1 for OAI.SKGap.sk_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:55:34.162365+00:00
-- url     : https://prove2.me/submissions/bc4f8091-9132-4fb5-91eb-a3ac4995f0ad

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A002
import Theorems.Thm_OAI_SKGap_FullMain_quenched_grid_root_stability
import Theorems.Thm_OAI_SKGap_FullMain_quenched_posterior_covariance
import Theorems.Thm_OAI_SKGap_terminal_gap_high_probability
import Theorems.Thm_OAI_SKGapCutoff_Recipe_disorder_norm_event
import Theorems.Thm_OAI_SKGapCutoff_Recipe_disorder_word_event
import Theorems.Thm_OAI_SKGapCutoff_Recipe_uniform_stable_square_mean

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarVariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
namespace SKGapCutoff

lemma scalarVariance_pos (y : ℝ) : 0 < scalarVariance y :=
  sub_pos.mpr (Real.tanh_sq_lt_one y)

lemma scalarVariance_le_one (y : ℝ) : scalarVariance y ≤ 1 := by
  unfold scalarVariance
  nlinarith [sq_nonneg (Real.tanh y)]

lemma halfDiff_as_flip {n : ℕ} (f : Observables n) (x : Spin n) (i : Fin n) :
    halfDiff i f x = spin x i * (f x - f (flip x i)) / 2 := by
  have hx := replace_self x i
  cases hi : x i <;> simp only [hi] at hx
  · simp only [spin, hi, Bool.false_eq_true, ↓reduceIte, flip, Bool.not_false, halfDiff]
    rw [hx]; ring
  · simp only [spin, hi, ↓reduceIte, flip, Bool.not_true, halfDiff]
    rw [hx]; ring

end SKGapCutoff

open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FiniteSpinCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKGap

section FiniteSpinCalculus

variable {n : ℕ}

theorem coupling_symm (g : Disorder n) (i k : Fin n) : coupling g i k = coupling g k i := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · simp [coupling, hik, not_lt_of_gt hik]
  · rfl
  · simp [coupling, hki, not_lt_of_gt hki]

theorem sum_flip (i : Fin n) (f : Spin n → ℝ) : ∑ x, f (flip i x) = ∑ x, f x :=
  (flipEquiv i).sum_comp f

theorem expectation_nonneg (g : Disorder n) (h : Fin n → ℝ) {f : Spin n → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectation g h f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg g h x) (hf x))

theorem variance_nonneg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    0 ≤ variance g h f := expectation_nonneg g h (fun _ => sq_nonneg _)

theorem variance_eq_zero_iff (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    variance g h f = 0 ↔ ∀ x, f x = expectation g h f := by
  unfold variance expectation
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    mul_nonneg (mass_nonneg g h x) (sq_nonneg _))]
  simp only [Finset.mem_univ, true_implies, mul_eq_zero, ne_of_gt (mass_pos g h _),
    false_or, sq_eq_zero_iff, sub_eq_zero]

theorem variance_pos_of_ne (g : Disorder n) (h : Fin n → ℝ) {f : Spin n → ℝ}
    {x y : Spin n} (hxy : f x ≠ f y) : 0 < variance g h f := by
  refine lt_of_le_of_ne (variance_nonneg g h f) ?_
  intro heq
  have hf := (variance_eq_zero_iff g h f).mp heq.symm
  exact hxy ((hf x).trans (hf y).symm)

theorem exists_positive_variance (g : Disorder n) (hn : 0 < n) :
    ∃ f : Spin n → ℝ, 0 < variance g 0 f := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨fun x => spinValue (x i), variance_pos_of_ne g 0 (x := fun _ => true)
    (y := fun _ => false) ?_⟩
  norm_num

theorem lower_bound_discreteGap (g : Disorder n) (hn : 0 < n) {C : ℝ} (hC : 0 < C)
    (hP : ∀ f : Spin n → ℝ, variance g 0 f ≤ C * dirichlet g 0 f) :
    1 / (C * (n : ℝ)) ≤ discreteGap g := by
  obtain ⟨f, hf⟩ := exists_positive_variance g hn
  apply le_csInf
  · exact ⟨_, f, hf, rfl⟩
  · rintro r ⟨f, hv, rfl⟩
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    apply (div_le_div_iff₀ (mul_pos hC hn') (mul_pos hn' hv)).mpr
    nlinarith [mul_le_mul_of_nonneg_left (hP f) hn'.le]

theorem gap_probability_of_poincare (β C : ℝ) (hC : 0 < C)
    (hP : Tendsto (fun n : ℕ => disorderLaw β n (poincareEvent n C)) atTop (nhds 1)) :
    Tendsto (fun n : ℕ => disorderLaw β n {g | 1 / (C * (n : ℝ)) ≤ discreteGap g})
      atTop (nhds 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hP tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply measure_mono
    intro g hg
    exact lower_bound_discreteGap g hn hC hg
  · filter_upwards [] with n
    exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)

end FiniteSpinCalculus

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiAlgebra
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.Stein

namespace KernelExpr

lemma mass_nonneg (f : KernelExpr) : 0 ≤ mass f := by
  induction f <;> simp only [mass] <;> positivity

end KernelExpr

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableFields
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open Real Matrix
namespace SKGap

theorem spinVariance_pos {n : ℕ} (y : Field n) (i : Fin n) :
    0 < spinVariance y i := sub_pos.mpr (tanh_sq_lt_one _)

theorem spinVariance_le_one {n : ℕ} (y : Field n) (i : Fin n) :
    spinVariance y i ≤ 1 := sub_le_self _ (sq_nonneg _)

theorem vectorNorm_sq {n : ℕ} (x : Field n) : vectorNorm x ^ 2 = vectorSqNorm x := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

attribute [local irreducible] vectorNorm

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PhiFrechet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology
namespace SKGap.Stein

namespace KernelExpr
lemma dBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.dBudget R := by
  unfold dBudget
  exact mul_nonneg (add_nonneg (add_nonneg f.dz.mass_nonneg f.dr.mass_nonneg) f.da.mass_nonneg)
    (Real.exp_pos _).le
lemma ddBudget_nonneg (f : KernelExpr) (R : ℝ) : 0≤f.ddBudget R :=
  add_nonneg (add_nonneg (f.dz.dBudget_nonneg R) (f.dr.dBudget_nonneg R)) (f.da.dBudget_nonneg R)

end KernelExpr

end SKGap.Stein

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_mul (M N : Matrix ι ι ℝ) : opNorm (M*N) ≤ opNorm M*opNorm N := by
  have he : (M*N).toEuclideanLin.toContinuousLinearMap =
      M.toEuclideanLin.toContinuousLinearMap * N.toEuclideanLin.toContinuousLinearMap := by
    ext x i
    exact congrFun (congrArg (fun T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι => (T x).ofLp)
      (Matrix.toLpLin_mul 2 2 2 M N)) i
  exact (congrArg norm he).le.trans (norm_mul_le _ _)

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixSeminorm
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance instFactLeENNRealOfNat_solutions : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
omit [DecidableEq ι] in
lemma diagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    diagonalSeminorm (M+N)≤diagonalSeminorm M+diagonalSeminorm N := by
  simpa only [diagonalSeminorm,diagonalVector_add] using norm_add_le (diagonalVector M) (diagonalVector N)
lemma offDiagonalSeminorm_add (M N : Matrix ι ι ℝ) :
    offDiagonalSeminorm (M+N)≤offDiagonalSeminorm M+offDiagonalSeminorm N := by
  simpa only [offDiagonalSeminorm,offDiagonalVector_add] using norm_add_le (offDiagonalVector M) (offDiagonalVector N)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_OpNormDiagonal
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma opNorm_diagonal_eq (d : ι → ℝ) : opNorm (diagonal d) = ‖d‖ :=
  Matrix.l2_opNorm_diagonal d

lemma opNorm_diagonal_le {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) :
    opNorm (diagonal d) ≤ C := by
  rw [opNorm_diagonal_eq]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun i => by simpa only [Real.norm_eq_abs] using hd i)

lemma opNorm_one_le : opNorm (1 : Matrix ι ι ℝ) ≤ 1 := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (1 : Matrix ι ι ℝ)‖ ≤ _
  rw [map_one]
  exact ContinuousLinearMap.norm_id_le

lemma opNorm_sub (M N : Matrix ι ι ℝ) : opNorm (M-N) ≤ opNorm M+opNorm N := by
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (M-N)‖ ≤ _
  rw [map_sub]
  exact norm_sub_le _ _

end SKGap

end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_DiscreteMatrixCalculus
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

local instance instFactLeENNRealOfNat_solutions_rff806f_1 : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
lemma opNorm_eq (M : Interaction n) :
    SKGap.opNorm M = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) M‖ := rfl

lemma opNorm_smul (c : ℝ) (M : Interaction n) : SKGap.opNorm (c • M) = |c| * SKGap.opNorm M := by
  simp only [opNorm_eq,map_smul,norm_smul,Real.norm_eq_abs]

end SKGapCutoff.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Operation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_sq (u : Fin n→ℝ) : vectorNorm u^2=∑i,(u i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq _

lemma vectorNorm_nonneg (u : Fin n→ℝ) : 0 ≤ vectorNorm u := norm_nonneg _

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix
variable {n : ℕ}

lemma vectorNorm_add (u v : Fin n→ℝ) :
    vectorNorm (u+v) ≤ vectorNorm u+vectorNorm v := by
  exact norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 v)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_SeparateCut
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.Noncrossing
universe u v
namespace Diagram
variable {D : Type*}

section Value
variable {ι : Type*} [Fintype ι]

lemma mean_const_mul (c : ℝ) (a : ι→ℝ) :
    mean (fun i => c*a i) = c*mean a := by
  simp only [mean,← Finset.mul_sum,mul_div_assoc]

end Value

end Diagram
end SKGap.Noncrossing

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_InverseDiagram
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing

namespace InverseDiagram

variable {ι : Type*} [Fintype ι]

lemma sum_flatMap {α : Type*} {R : Type*} [AddMonoid R]
    (l : List α) (f : α → List R) : (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

end InverseDiagram
end SKGap.Noncrossing

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryPrediction
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFinite _root_.OAI.SKGap.Noncrossing.Diagram.noiseSplitFintype _root_.OAI.SKGap.Noncrossing.Diagram.pairedNilUnique _root_.OAI.SKGap.Noncrossing.WordSeries.noiseSplitNilIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitDiagIsEmpty _root_.OAI.SKGap.Noncrossing.noiseSplitNoiseUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open Diagram

namespace Partial
variable {D : Type*}
lemma word_contract (p q : Partial D) (h : p.contract=some q) : q.word = .noise :: p.word := by
  cases p with
  | done d => simp [contract] at h
  | more d p => cases p <;> simp only [contract,Option.some.injEq] at h <;> subst q <;>
      simp [word,Diagram.word,List.append_assoc]
lemma diag_injective (a : D) : Function.Injective (diag a : Partial D → Partial D) := by
  intro p q h; cases p <;> cases q <;> simp_all [diag]
lemma create_injective : Function.Injective (create : Partial D → Partial D) := by
  intro p q h; exact Partial.more.inj h |>.2
lemma contract_injective {p q r : Partial D} (hp : p.contract=some r) (hq : q.contract=some r) : p=q := by
  cases p with
  | done d => simp [contract] at hp
  | more d p =>
    cases q with
    | done e => simp [contract] at hq
    | more e q =>
      cases p <;> cases q <;> simp only [contract,Option.some.injEq] at hp hq <;>
        subst r <;> simp_all
lemma create_ne_contract (p q r : Partial D) (h : q.contract=some r) : p.create≠r := by
  cases q with
  | done d => simp [contract] at h
  | more d q => cases q <;> simp only [contract,Option.some.injEq] at h <;> subst r <;> simp [create]

lemma diag_preimage (a : D) (F : List (Letter D)) (p : Partial D)
    (h : p.word = .diag a :: F) : ∃ q : Partial D, q.word=F ∧ p=q.diag a := by
  cases p with
  | done d => cases d <;> simp only [word,Diagram.word] at h
              case diag b d => simp only [List.cons.injEq,Letter.diag.injEq] at h
                               obtain ⟨rfl,h⟩ := h; exact ⟨.done d,h,rfl⟩
              all_goals simp at h
  | more d p =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | arch d e => simp [word,Diagram.word] at h
    | diag b d =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,Letter.diag.injEq] at h
      obtain ⟨rfl,h⟩ := h; exact ⟨.more d p,h,rfl⟩
lemma noise_preimage (F : List (Letter D)) (p : Partial D)
    (h : p.word = .noise :: F) :
    ∃ q : Partial D, q.word=F ∧ (p=q.create ∨ q.contract=some p) := by
  cases p with
  | done d =>
    cases d with
    | nil => simp [word,Diagram.word] at h
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons.injEq,true_and] at h
      exact ⟨.more d (.done e),h,Or.inr rfl⟩
  | more d p =>
    cases d with
    | nil =>
      simp only [word,Diagram.word,List.nil_append,List.cons.injEq,true_and] at h
      exact ⟨p,h,Or.inl rfl⟩
    | diag a d => simp [word,Diagram.word] at h
    | arch d e =>
      simp only [word,Diagram.word,List.cons_append,List.cons.injEq,true_and,List.append_assoc] at h
      exact ⟨.more d (.more e p),h,Or.inr rfl⟩

@[simp] lemma mem_enumerate (F : List (Letter D)) (p : Partial D) :
    p∈enumerate F ↔ p.word=F := by
  induction F generalizing p with
  | nil =>
    cases p with
    | done d => cases d <;> simp [enumerate,word,Diagram.word]
    | more d p => simp [enumerate,word]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [enumerate,List.mem_map,ih]
      constructor
      · rintro ⟨q,hq,rfl⟩; simp [hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := diag_preimage a F p hp; exact ⟨q,hq,hp.symm⟩
    | noise =>
      simp only [enumerate,List.mem_flatMap,noise,List.mem_cons,Option.mem_toList,ih]
      constructor
      · rintro ⟨q,hq,hp|hp⟩
        · subst p; simp [hq]
        · rw [word_contract q p hp,hq]
      · intro hp; obtain ⟨q,hq,hp⟩ := noise_preimage F p hp; exact ⟨q,hq,hp⟩

lemma noise_nodup (p : Partial D) : p.noise.Nodup := by
  cases p with
  | done d => simp [noise,contract]
  | more d p => cases p <;> simp [noise,contract,create]
lemma noise_disjoint {p q : Partial D} (h : p≠q) : List.Disjoint p.noise q.noise := by
  apply List.disjoint_left.mpr
  intro r hr hq
  simp only [noise,List.mem_cons,Option.mem_toList] at hr hq
  rcases hr with hr|hr <;> rcases hq with hq|hq
  · exact h (create_injective (hr.symm.trans hq))
  · exact create_ne_contract p q r hq hr.symm
  · exact create_ne_contract q p r hr hq.symm
  · exact h (contract_injective hr hq)
lemma enumerate_nodup (F : List (Letter D)) : (enumerate F).Nodup := by
  induction F with
  | nil => simp [enumerate]
  | cons a F ih =>
    cases a with
    | diag a => exact ih.map (diag_injective a)
    | noise =>
      rw [enumerate,List.nodup_flatMap]
      exact ⟨fun p _ => noise_nodup p, List.Pairwise.imp (fun h => noise_disjoint h) ih⟩
end Partial

section Fock
variable {ι : Type*} [Fintype ι]

lemma value_factor (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    d.value j i=coefficient j d * outer d i := by
  induction d with
  | nil => simp [Diagram.value,coefficient,outer]
  | diag a d ih => simp [Diagram.value,coefficient,outer,ih]; ring
  | arch a b ia ib => simp [Diagram.value,coefficient,outer,ib]; ring
lemma mean_value (j : ℝ) (d : Diagram (D (ι:=ι))) :
    Diagram.mean (d.value j)=coefficient j d * Diagram.mean (outer d) := by
  simp only [funext (value_factor j d),Diagram.mean_const_mul]

lemma Partial.state_diag (j : ℝ) (a : D (ι:=ι)) (p : Partial (D (ι:=ι))) :
    (p.diag a).state j = diagonal a (p.state j) := by
  cases p <;> simp [state,stack,Partial.diag,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_create (j : ℝ) (p : Partial (D (ι:=ι))) :
    p.create.state j = creation (p.state j) := by
  simp [state,stack,create,Partial.coefficient,Primary.coefficient,Primary.outer]
lemma Partial.state_contract (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.contract.toList).map (Partial.state j)).sum = j • annihilation (p.state j) := by
  cases p with
  | done d => simp [state,stack,Partial.contract]
  | more d p =>
    cases p <;> simp [state,stack,Partial.contract,Partial.coefficient,
      Primary.coefficient,Primary.outer,mean_value,smul_smul,mul_assoc,mul_left_comm,mul_comm]
lemma Partial.state_noise (j : ℝ) (p : Partial (D (ι:=ι))) :
    ((p.noise).map (Partial.state j)).sum = Primary.noise j (p.state j) := by
  simp only [Partial.noise,List.map_cons,List.sum_cons,state_create,state_contract]
  rfl

lemma word_vacuum (j : ℝ) (F : List (Letter (D (ι:=ι)))) :
    word j F vacuum = ((Partial.enumerate F).map (Partial.state j)).sum := by
  induction F with
  | nil => simp [word,vacuum,Partial.enumerate,Partial.state,Partial.stack,
      Partial.coefficient,Primary.coefficient,Primary.outer]
  | cons a F ih =>
    cases a with
    | diag a =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_map]
      simp only [map_list_sum,Function.comp_def,Partial.state_diag,List.map_map]
    | noise =>
      simp only [word,letter,LinearMap.comp_apply,ih,Partial.enumerate,List.map_flatMap]
      rw [SKGap.Noncrossing.InverseDiagram.sum_flatMap]
      simp only [Partial.state_noise,map_list_sum,List.map_map,Function.comp_def]

lemma Partial.project_state_done (j : ℝ) (d : Diagram (D (ι:=ι))) (i : ι) :
    project ((.done d : Partial _).state j) i = d.value j i := by
  simp [Partial.state,Partial.stack,Partial.coefficient,value_factor]
lemma Partial.project_state_more (j : ℝ) (d : Diagram (D (ι:=ι)))
    (p : Partial (D (ι:=ι))) : project ((Partial.more d p).state j) = 0 := by
  simp [Partial.state,Partial.stack]

lemma prediction_as_finset (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    Diagram.prediction j F i = ∑ d∈Diagram.enumerate F, d.value j i := by
  classical
  let e : Diagram.Paired F ≃ {d // d∈Diagram.enumerate F} :=
    { toFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mpr d.property⟩
      invFun := fun d => ⟨d.val,(Diagram.mem_enumerate F d.val).mp d.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (∑ d : Diagram.Paired F, d.val.value j i) = _
  calc
    _ = ∑ d : {d // d∈Diagram.enumerate F}, d.val.value j i :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort (Diagram.enumerate F) (fun d => d.value j i)

theorem project_word (j : ℝ) (F : List (Letter (D (ι:=ι)))) (i : ι) :
    project (word j F vacuum) i = Diagram.prediction j F i := by
  classical
  rw [word_vacuum,map_list_sum,List.map_map]
  change (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i = _
  have heval : (((Partial.enumerate F).map (fun p => project (p.state j))).sum) i =
      ((Partial.enumerate F).map (fun p => project (p.state j) i)).sum := by
    induction Partial.enumerate F with
    | nil => rfl
    | cons p L ih => simp [ih]
  rw [heval,← List.sum_toFinset _ (Partial.enumerate_nodup F),prediction_as_finset]
  have hsub : (Diagram.enumerate F).image Partial.done ⊆ (Partial.enumerate F).toFinset := by
    intro p hp
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
    simpa [Partial.word] using hd
  rw [← Finset.sum_subset hsub (fun p hp hn => ?_)]
  · rw [Finset.sum_image (fun d _ e _ h => Partial.done.inj h)]
    exact Finset.sum_congr rfl (fun d _ => Partial.project_state_done j d i)
  · cases p with
    | done d =>
      exfalso; apply hn
      exact Finset.mem_image.mpr ⟨d,by simpa [Partial.word] using hp,rfl⟩
    | more d p => simp [Partial.project_state_more]

theorem primaryOperator_vacuum (j : ℝ) (a : ℕ → D (ι:=ι)) (n : ℕ) :
    primaryOperator j a n vacuum = ket (1,creationLabels a n) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [primaryOperator,noise,vacuum,creationLabels,previousDiagonal]
  | more n hn hn1 =>
    simp [primaryOperator,LinearMap.comp_apply,hn,hn1,noise,creationLabels,
      previousDiagonal,smul_smul]

theorem primaryOperator_prediction_zero (j : ℝ) (a : ℕ → D (ι:=ι))
    (n : ℕ) (hn : 0<n) : project (primaryOperator j a n vacuum) = 0 := by
  cases n with
  | zero => omega
  | succ n => rw [primaryOperator_vacuum]; simp [creationLabels]

lemma word_append (j : ℝ) (F G : List (Letter (D (ι:=ι)))) :
    word j (F++G) = (word j F).comp (word j G) := by
  induction F with
  | nil => simp [word]
  | cons a F ih => simp [word,ih,LinearMap.comp_assoc]
lemma polynomialOperator_append (j : ℝ) (P Q : WordPolynomial (ι:=ι)) :
    polynomialOperator j (P++Q) = polynomialOperator j P + polynomialOperator j Q := by
  simp [polynomialOperator]
lemma polynomialOperator_prefix (j : ℝ) (F : List (Letter (D (ι:=ι))))
    (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (prependWords F P) = (word j F).comp (polynomialOperator j P) := by
  induction P with
  | nil => simp [prependWords,polynomialOperator]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [word_append,ih,LinearMap.comp_add,LinearMap.comp_smul]
lemma polynomialOperator_scale (j c : ℝ) (P : WordPolynomial (ι:=ι)) :
    polynomialOperator j (scale c P)=c • polynomialOperator j P := by
  induction P with
  | nil => simp [scale,polynomialOperator]
  | cons p P ih =>
    simp only [scale,List.map_cons,polynomialOperator,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

lemma primaryPolynomial_operator (j : ℝ) (a : ℕ → D (ι:=ι)) (n : ℕ) :
    polynomialOperator j (primaryPolynomial j a n)=primaryOperator j a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,polynomialOperator,primaryOperator,word]
  | one => simp [primaryPolynomial,polynomialOperator,primaryOperator,word,letter]
  | more n hn hn1 =>
    simp only [primaryPolynomial,polynomialOperator_append,polynomialOperator_prefix,
      polynomialOperator_scale,hn,hn1,word,letter,LinearMap.comp_id,primaryOperator]
    ext v k
    simp [LinearMap.comp_apply,sub_eq_add_neg,neg_smul]

lemma polynomialPrediction_eq_project (j : ℝ) (P : WordPolynomial (ι:=ι)) (i : ι) :
    polynomialPrediction j P i = project (polynomialOperator j P vacuum) i := by
  induction P with
  | nil => simp [polynomialPrediction,polynomialOperator]
  | cons p P ih =>
    simp only [polynomialPrediction,polynomialOperator,List.map_cons,List.sum_cons,
      LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul] at *
    rw [project_word,ih]

theorem primaryPolynomial_prediction_zero (j : ℝ) (a : ℕ → D (ι:=ι))
    (n : ℕ) (hn : 0<n) (i : ι) :
    polynomialPrediction j (primaryPolynomial j a n) i = 0 := by
  rw [polynomialPrediction_eq_project,primaryPolynomial_operator,
    primaryOperator_prediction_zero j a n hn]
  rfl

end Fock
end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixQuad
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKGap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma matrixQuad_smul (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (c : ℝ) :
    matrixQuad M (c • p) = c^2 * matrixQuad M p := by
  simp only [matrixQuad, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end SKGap

end
end
end
end
end
end
end
end
end
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
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_MatrixNormTail
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma matrixWordSeminorm_add (p : Bool) (M N : Matrix ι ι ℝ) :
    matrixWordSeminorm p (M+N)≤ matrixWordSeminorm p M+matrixWordSeminorm p N := by
  cases p
  · exact diagonalSeminorm_add M N
  · exact offDiagonalSeminorm_add M N
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary
open WordSeries
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixWord_append (J : Matrix ι ι ℝ) (F G : List (Letter (ι→ℝ))) :
    matrixWord J (F++G)=matrixWord J F*matrixWord J G := by simp [matrixWord]
lemma matrixPolynomial_append (J : Matrix ι ι ℝ) (P Q : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (P++Q)=matrixPolynomial J P+matrixPolynomial J Q := by
  simp [matrixPolynomial]
lemma matrixPolynomial_prefix (J : Matrix ι ι ℝ) (F : List (Letter (ι→ℝ)))
    (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (prependWords F P)=matrixWord J F*matrixPolynomial J P := by
  induction P with
  | nil => simp [prependWords,matrixPolynomial]
  | cons p P ih =>
    simp only [prependWords,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [matrixWord_append,ih,mul_add,mul_smul_comm]
lemma matrixPolynomial_scale (J : Matrix ι ι ℝ) (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    matrixPolynomial J (scale c P)=c • matrixPolynomial J P := by
  induction P with
  | nil => simp [scale,matrixPolynomial]
  | cons p P ih =>
    simp only [scale,List.map_cons,matrixPolynomial,List.sum_cons] at *
    rw [ih,smul_add,mul_smul]

lemma primaryPolynomial_matrix (j : ℝ) (J : Matrix ι ι ℝ) (a : ℕ→ι→ℝ) (n : ℕ) :
    matrixPolynomial J (primaryPolynomial j a n)=primaryMatrix j J a n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,matrixPolynomial,primaryMatrix,matrixWord]
  | one => simp [primaryPolynomial,matrixPolynomial,primaryMatrix,matrixWord,matrixLetter]
  | more n hn hn1 =>
    simp only [primaryPolynomial,matrixPolynomial_append,matrixPolynomial_prefix,
      matrixPolynomial_scale,hn,hn1,primaryMatrix,matrixWord,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,matrixLetter]
    simp [mul_assoc,sub_eq_add_neg,neg_smul]

lemma matrixWordSeminorm_zero (p : Bool) : matrixWordSeminorm (ι:=ι) p 0=0 := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hd : diagonalVector (0 : Matrix ι ι ℝ)=0 := by ext i; rfl
  have ho : offDiagonalVector (0 : Matrix ι ι ℝ)=0 := by ext ⟨i,k⟩; simp [offDiagonalVector]
  cases p <;> simp [matrixWordSeminorm,diagonalSeminorm,offDiagonalSeminorm,hd,ho]
lemma matrixWordSeminorm_smul (p : Bool) (c : ℝ) (J : Matrix ι ι ℝ) :
    matrixWordSeminorm p (c • J)=|c| *matrixWordSeminorm p J := by
  let : Fact (1≤(4:ENNReal)) := ⟨by norm_num⟩
  have hd : diagonalVector (c • J)=c • diagonalVector J := by ext i; rfl
  have ho : offDiagonalVector (c • J)=c • offDiagonalVector J := by
    ext ⟨i,k⟩
    by_cases h : i=k <;> simp [offDiagonalVector,h]
  cases p
  · simp [matrixWordSeminorm,diagonalSeminorm,hd,norm_smul,Real.norm_eq_abs]
  · simp [matrixWordSeminorm,offDiagonalSeminorm,ho,norm_smul,Real.norm_eq_abs]

lemma polynomial_error (p : Bool) (j : ℝ) (J : Matrix ι ι ℝ)
    (P : WordPolynomial (ι:=ι)) {C : ℝ}
    (h : ∀ t∈P, matrixWordSeminorm p
      (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))≤C) :
    matrixWordSeminorm p (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P))≤
      coefficientMass P*C := by
  induction P with
  | nil => simp [matrixPolynomial,polynomialPrediction,coefficientMass,matrixWordSeminorm_zero]
  | cons t P ih =>
    have he : matrixPolynomial J (t::P)-Matrix.diagonal (polynomialPrediction j (t::P))=
        t.1 • (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))+
        (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P)) := by
      have hp : polynomialPrediction j (t::P)=
          t.1 • Diagram.prediction j t.2+polynomialPrediction j P := by
        ext i; simp [polynomialPrediction]
      have hd (u v : ι→ℝ) : Matrix.diagonal (u+v)=Matrix.diagonal u+Matrix.diagonal v :=
        (Matrix.diagonal_add u v).symm
      simp only [matrixPolynomial,List.map_cons,List.sum_cons,hp,hd,Matrix.diagonal_smul]
      rw [smul_sub]
      abel
    rw [he]
    calc
      _ ≤ matrixWordSeminorm p (t.1 • (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2)))+
          matrixWordSeminorm p (matrixPolynomial J P-Matrix.diagonal (polynomialPrediction j P)) :=
        matrixWordSeminorm_add _ _ _
      _ ≤ |t.1| *C+coefficientMass P*C := by
        rw [matrixWordSeminorm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_left (h t (by simp)) (abs_nonneg _))
          (ih (fun q hq=>h q (List.mem_cons_of_mem _ hq)))
      _ = coefficientMass (t::P)*C := by simp [coefficientMass,add_mul]

theorem primaryMatrix_seminorm (p : Bool) (j : ℝ) (J : Matrix ι ι ℝ)
    (a : ℕ→ι→ℝ) (n : ℕ) (hn : 0<n) {C : ℝ}
    (h : ∀ t∈primaryPolynomial j a n, matrixWordSeminorm p
      (matrixWord J t.2-Matrix.diagonal (Diagram.prediction j t.2))≤C) :
    matrixWordSeminorm p (primaryMatrix j J a n) ≤ coefficientMass (primaryPolynomial j a n)*C := by
  have hz : polynomialPrediction j (primaryPolynomial j a n)=0 :=
    funext (primaryPolynomial_prediction_zero j a n hn)
  simpa only [primaryPolynomial_matrix,hz,Matrix.diagonal_zero',sub_zero] using
    polynomial_error p j J (primaryPolynomial j a n) h

omit [DecidableEq ι]

omit [Fintype ι] in
lemma coefficientMass_nonneg (P : WordPolynomial (ι:=ι)) : 0 ≤ coefficientMass P :=
  List.sum_nonneg (by intro x hx; obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
omit [Fintype ι] in
lemma coefficientMass_append (P Q : WordPolynomial (ι:=ι)) :
    coefficientMass (P++Q)=coefficientMass P+coefficientMass Q := by simp [coefficientMass]
omit [Fintype ι] in
lemma coefficientMass_prefix (F : List (Letter (ι→ℝ))) (P : WordPolynomial (ι:=ι)) :
    coefficientMass (prependWords F P)=coefficientMass P := by
  simp [coefficientMass,prependWords,Function.comp_def]
omit [Fintype ι] in
lemma coefficientMass_scale (c : ℝ) (P : WordPolynomial (ι:=ι)) :
    coefficientMass (scale c P)=|c| *coefficientMass P := by
  simp [coefficientMass,scale,Function.comp_def,abs_mul,List.sum_map_mul_left]

lemma mean_abs_le_one [Nonempty ι] {a : ι→ℝ} (ha : ∀ i,|a i|≤1) :
    |Diagram.mean a|≤1 := by
  have hn : (0:ℝ)<Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    |Diagram.mean a| = |∑ i,a i|/(Fintype.card ι:ℝ) := by
      rw [Diagram.mean,abs_div,abs_of_pos hn]
    _ ≤ (∑ i,|a i|)/(Fintype.card ι:ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
    _ ≤ 1 := by
      rw [div_le_one hn]
      simpa using Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => ha i)

lemma massBound_pos (j : ℝ) (n : ℕ) : 0< massBound j n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [massBound]
  | one => norm_num [massBound]
  | more n hn hn1 => exact add_pos_of_pos_of_nonneg hn1 (mul_nonneg (abs_nonneg _) hn.le)
lemma primaryMass_bound [Nonempty ι] (j : ℝ) (a : ℕ→ι→ℝ)
    (ha : ∀ n i,|a n i|≤1) (n : ℕ) :
    coefficientMass (primaryPolynomial j a n)≤ massBound j n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,coefficientMass,massBound]
  | one => simp [primaryPolynomial,coefficientMass,massBound]
  | more n hn hn1 =>
    simp only [primaryPolynomial,coefficientMass_append,coefficientMass_prefix,
      coefficientMass_scale,abs_neg,abs_mul,massBound]
    apply add_le_add hn1
    calc
      |j| * |Diagram.mean (a n)| * coefficientMass (primaryPolynomial j a n) ≤
          |j| * 1 * coefficientMass (primaryPolynomial j a n) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mean_abs_le_one (ha n)) (abs_nonneg _))
          (coefficientMass_nonneg _)
      _ ≤ |j| * massBound j n := by simpa using mul_le_mul_of_nonneg_left hn (abs_nonneg j)

lemma primaryPolynomial_admissible (j : ℝ) (a : ℕ→ι→ℝ)
    (ha : ∀ n i,|a n i|≤1) (n : ℕ) :
    ∀ t∈primaryPolynomial j a n, t.2.length≤2*n ∧
      ∀ l∈liftWord t.2,l.bounded 1 := by
  have hp (n : ℕ) : ∀ i,|previousDiagonal a n i|≤1 := by
    cases n <;> simp [previousDiagonal,ha]
  induction n using Nat.twoStepInduction with
  | zero => simp [primaryPolynomial,liftWord]
  | one =>
    intro t ht
    simp only [primaryPolynomial,List.mem_singleton] at ht
    subst t
    simp [liftWord,Letter.toWord,WordLetter.bounded]
  | more n hn hn1 =>
    intro t ht
    simp only [primaryPolynomial,List.mem_append,prependWords,scale,List.mem_map] at ht
    rcases ht with ⟨q,hq,rfl⟩ | ⟨u,⟨q,hq,rfl⟩,rfl⟩
    · obtain ⟨hql,hqb⟩ := hn1 q hq
      constructor
      · simp only [List.length_append,List.length_cons,List.length_nil]; omega
      · intro l hl
        simp only [liftWord_append,liftWord_cons,liftWord_nil,Letter.toWord,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with (rfl|rfl)|hl
        · trivial
        · exact ha n
        · exact hqb l hl
    · obtain ⟨hql,hqb⟩ := hn q hq
      constructor
      · simp only [List.length_append,List.length_cons,List.length_nil]; omega
      · intro l hl
        simp only [liftWord_append,liftWord_cons,liftWord_nil,Letter.toWord,
          List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|hl
        · exact hp n
        · exact hqb l hl

end SKGap.Noncrossing.Primary
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix
variable {n : ℕ}

lemma primaryDiagonal_bounded (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (x : Spin n) :
    ∀ k i, |primaryDiagonal j J h x k i|≤1 := by
  intro k i
  rw [primaryDiagonal,abs_of_pos (scalarVariance_pos _)]
  exact scalarVariance_le_one _

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Reference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

lemma integrable_exp_linear (a : Fin n → ℝ) :
    Integrable (fun z => exp (∑ i, a i * z i)) (reference n) := by
  simp_rw [exp_sum]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a i))

lemma integral_exp_linear (a : Fin n → ℝ) :
    (∫ z, exp (∑ i, a i * z i) ∂reference n) = exp ((∑ i, (a i)^2) / 2) := by
  simp_rw [exp_sum]
  rw [reference, integral_fintype_prod_eq_prod (fun i (z : ℝ) => exp (a i*z))]
  have hi (i : Fin n) : (∫ z : ℝ, exp (a i * z) ∂gaussianReal 0 1) = exp ((a i)^2/2) := by
    simpa only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add, id_eq] using
      mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1) (by simp) (a i)
  simp_rw [hi]
  rw [← exp_sum, Finset.sum_div]

lemma integrable_likelihood (t : ℝ) (x : Spin n) :
    Integrable (likelihood t x) (reference n) := by
  have he : likelihood t x = fun z => exp (∑ i, (sqrt t * spinValue (x i)) * z i) *
      exp (-(t*n/2)) := by
    funext z
    simp only [likelihood, exp_sub, exp_neg, ← Finset.mul_sum, mul_assoc, div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : Spin n) :
    (∫ z, likelihood t x z ∂reference n) = 1 := by
  have he : likelihood t x = fun z => exp (∑ i, (sqrt t * spinValue (x i)) * z i) *
      exp (-(t*n/2)) := by
    funext z
    simp only [likelihood, exp_sub, exp_neg, ← Finset.mul_sum, mul_assoc, div_eq_mul_inv]
  rw [he, integral_mul_const, integral_exp_linear, ← exp_add]
  have hs : (∑ i, (sqrt t * spinValue (x i)) ^ 2) = t*n := by
    simp [mul_pow, sq_sqrt ht, spinValue_sq, mul_comm]
  rw [hs]
  simp

lemma integrable_density (p : Prior n) (t : ℝ) :
    Integrable (density p t) (reference n) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul (p x))

lemma integral_density (p : Prior n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density p t z ∂reference n) = 1 := by
  change (∫ z, ∑ x, p x * likelihood t x z ∂reference n) = 1
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul (p x))]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  exact p.sum_one

lemma mean_abs_le_one (p : Prior n) (i : Fin n) : |mean p i| ≤ 1 := by
  calc
    |mean p i| ≤ ∑ x, |p x * spinValue (x i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, p x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (p.nonneg x)]
      have hs : |spinValue (x i)| = 1 := by cases x i <;> norm_num [spinValue]
      rw [hs, mul_one]
    _ = 1 := p.sum_one

lemma interaction_abs_le (p : Prior n) (x y : Spin n) :
    |interaction p x y| ≤ 4*n := by
  have hl : (0 : ℝ) ≤ ∑ i : Fin n, (spinValue (x i) + spinValue (y i) - mean p i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hu : (∑ i : Fin n, (spinValue (x i) + spinValue (y i) - mean p i)^2) ≤ 9*n := by
    calc
      _ ≤ ∑ _i : Fin n, (9 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hx : |spinValue (x i)| = 1 := by cases x i <;> norm_num [spinValue]
        have hy : |spinValue (y i)| = 1 := by cases y i <;> norm_num [spinValue]
        have hb : |spinValue (x i) + spinValue (y i) - mean p i| ≤ 3 := by
          calc
            _ ≤ |spinValue (x i) + spinValue (y i)| + |mean p i| := abs_sub _ _
            _ ≤ |spinValue (x i)| + |spinValue (y i)| + |mean p i| :=
              add_le_add (abs_add_le _ _) le_rfl
            _ ≤ 3 := by rw [hx, hy]; linarith [mean_abs_le_one p i]
        have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 3)).mpr hb
        simpa only [sq_abs, show (3:ℝ)^2 = 9 by norm_num] using hh
      _ = 9*n := by simp [mul_comm]
  rw [abs_le]
  unfold interaction
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma interaction_remainder_bound (p : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) (x y : Spin n) :
    |exp (t * interaction p x y) - 1 - t * interaction p x y| ≤
      16*(n:ℝ)^2*t^2 := by
  have hb := interaction_abs_le p x y
  have htb : |t * interaction p x y| ≤ 4*(n:ℝ)*t := by
    rw [abs_mul, abs_of_nonneg ht]
    nlinarith [mul_le_mul_of_nonneg_left hb ht]
  apply (abs_exp_sub_one_sub_id_le (htb.trans htn)).trans
  have hs := sq_le_sq₀ (abs_nonneg (t * interaction p x y)) (by positivity) |>.mpr htb
  simpa only [sq_abs] using (hs.trans_eq (by ring : (4*(n:ℝ)*t)^2 = 16*(n:ℝ)^2*t^2))

lemma interaction_sum (p : Prior n) (x y : Spin n) :
    interaction p x y = ∑ i, ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := by
  have ha : interaction p x y = ∑ i, ((spinValue (x i) + spinValue (y i) - mean p i)^2 - 1)/2 := by
    unfold interaction
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  rw [ha]
  apply Finset.sum_congr rfl
  intro i _
  nlinarith [spinValue_sq (x i), spinValue_sq (y i)]

lemma signed_sum_left (a u : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x * a y * u x) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  calc
    _ = (a x * u x) * ∑ y, a y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = 0 := by rw [ha, mul_zero]

lemma signed_sum_right (a u : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x * a y * u y) = 0 := by
  rw [Finset.sum_comm]
  convert signed_sum_left a u ha using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma signed_sum_product (a u : Spin n → ℝ) :
    (∑ x, ∑ y, a x * a y * (u x * u y)) = (∑ x, a x*u x)^2 := by
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma signed_interaction (p : Prior n) (a : Spin n → ℝ) (ha : ∑ x, a x = 0) :
    (∑ x, ∑ y, a x*a y*interaction p x y) =
      ∑ i, (∑ x, a x*spinValue (x i))^2 := by
  simp_rw [interaction_sum, Finset.mul_sum]
  calc
    _ = ∑ x, ∑ i, ∑ y, a x*a y* ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, a x*a y* ((1/2 : ℝ) + spinValue (x i)*spinValue (y i) -
      spinValue (x i)*mean p i - spinValue (y i)*mean p i + (mean p i)^2/2) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [signed_sum_left a (fun _ => (1/2 : ℝ)) ha,
        signed_sum_product a (fun x => spinValue (x i)),
        signed_sum_left a (fun x => spinValue (x i)*mean p i) ha,
        signed_sum_right a (fun y => spinValue (y i)*mean p i) ha,
        signed_sum_left a (fun _ => (mean p i)^2/2) ha]
      ring

lemma integrable_pairKernel (p : Prior n) (t : ℝ) (x y : Spin n) :
    Integrable (pairKernel p t x y) (reference n) := by
  have he : pairKernel p t x y = fun z =>
      exp (∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) *
        exp (-(t*n/2)) := by funext z; simp [pairKernel, exp_sub, exp_neg, div_eq_mul_inv]
  rw [he]
  exact (integrable_exp_linear _).mul_const _

lemma integral_pairKernel (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (x y : Spin n) :
    (∫ z, pairKernel p t x y z ∂reference n) = exp (t*interaction p x y) := by
  have he : pairKernel p t x y = fun z =>
      exp (∑ i, (sqrt t * (spinValue (x i) + spinValue (y i) - mean p i)) * z i) *
        exp (-(t*n/2)) := by funext z; simp [pairKernel, exp_sub, exp_neg, div_eq_mul_inv]
  rw [he, integral_mul_const, integral_exp_linear, ← exp_add]
  congr 1
  simp only [mul_pow, sq_sqrt ht, ← Finset.mul_sum, interaction]
  ring

lemma likelihood_pair (p : Prior n) (t : ℝ) (x y : Spin n) (z : Fin n → ℝ) :
    likelihood t x z * likelihood t y z *
      exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2)) = pairKernel p t x y z := by
  unfold likelihood pairKernel
  rw [← exp_add, ← exp_add]
  congr 1
  simp only [add_mul, sub_mul, mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, mul_assoc]
  ring

lemma majorant_eq_sum (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    majorant p a t z = ∑ x, ∑ y, (a x*a y)*pairKernel p t x y z := by
  unfold majorant
  rw [pow_two, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = (a x*a y)*(likelihood t x z*likelihood t y z*
        exp (-(sqrt t * (∑ i, mean p i * z i) - t*n/2))) := by ring
    _ = _ := by rw [likelihood_pair]

lemma integrable_majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Integrable (majorant p a t) (reference n) := by
  simp_rw [show majorant p a t = fun z => ∑ x, ∑ y, (a x*a y)*pairKernel p t x y z from
    funext (majorant_eq_sum p a t)]
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel p t x y).const_mul _))

lemma integral_majorant (p : Prior n) (a : Spin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, majorant p a t z ∂reference n) = ∑ x, ∑ y, (a x*a y)*exp (t*interaction p x y) := by
  simp_rw [majorant_eq_sum]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ =>
    (integrable_pairKernel p t x y).const_mul _))]
  apply Finset.sum_congr rfl
  intro x _
  rw [integral_finsetSum _ (fun y _ => (integrable_pairKernel p t x y).const_mul _)]
  simp_rw [integral_const_mul, integral_pairKernel p ht]

lemma interaction_exp_sum_bound (p : Prior n) (a : Spin n → ℝ)
    (ha : ∑ x, a x = 0) {t : ℝ} (ht : 0 ≤ t) (htn : 4*(n:ℝ)*t ≤ 1) :
    (∑ x, ∑ y, a x*a y*exp (t*interaction p x y)) ≤
      t*(∑ i, (∑ x, a x*spinValue (x i))^2) +
        16*(n:ℝ)^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∑ x, ∑ y, ((a x*a y + t*(a x*a y*interaction p x y)) +
        (16*(n:ℝ)^2*t^2)*(|a x| * |a y|)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      have hr := interaction_remainder_bound p ht htn x y
      have hb : a x*a y*(exp (t*interaction p x y)-1-t*interaction p x y) ≤
          |a x| * |a y| * (16*(n:ℝ)^2*t^2) := by
        calc
          _ ≤ |a x*a y*(exp (t*interaction p x y)-1-t*interaction p x y)| := le_abs_self _
          _ = |a x| * |a y| * |exp (t*interaction p x y)-1-t*interaction p x y| := by simp [abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      nlinarith only [hb]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [ha, signed_interaction p a ha]
      simp only [mul_zero, Finset.sum_const_zero, zero_add, ← Finset.sum_mul]
      ring

lemma quadraticIntegrand_nonneg (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    0 ≤ quadraticIntegrand p a t z := div_nonneg (sq_nonneg _) (density_pos p t z).le

lemma quadraticIntegrand_le_majorant (p : Prior n) (a : Spin n → ℝ) (t : ℝ) (z : Fin n → ℝ) :
    quadraticIntegrand p a t z ≤ majorant p a t z := by
  unfold quadraticIntegrand
  calc
    _ ≤ (∑ x, a x*likelihood t x z)^2 /
        exp (sqrt t * (∑ i, mean p i*z i) - t*n/2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (exp_pos _) (density_jensen p t z)
    _ = _ := by simp only [majorant, div_eq_mul_inv, exp_neg]

lemma continuous_likelihood (t : ℝ) (x : Spin n) : Continuous (likelihood t x) := by
  unfold likelihood
  fun_prop

lemma continuous_density (p : Prior n) (t : ℝ) : Continuous (density p t) := by
  unfold density
  exact continuous_finsetSum _ (fun x _ => (continuous_likelihood t x).const_mul _)

lemma continuous_quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Continuous (quadraticIntegrand p a t) := by
  apply Continuous.div
    ((continuous_finsetSum _ (fun x _ => (continuous_likelihood t x).const_mul (a x))).pow 2)
    (continuous_density p t)
  intro z
  exact (density_pos p t z).ne'

lemma integrable_quadraticIntegrand (p : Prior n) (a : Spin n → ℝ) (t : ℝ) :
    Integrable (quadraticIntegrand p a t) (reference n) := by
  apply (integrable_majorant p a t).mono' (continuous_quadraticIntegrand p a t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticIntegrand_nonneg p a t z)]
  exact quadraticIntegrand_le_majorant p a t z

theorem quadratic_bound (p : Prior n) (a : Spin n → ℝ) (ha : ∑ x, a x = 0)
    {t : ℝ} (ht : 0 ≤ t) (htn : 4*(n:ℝ)*t ≤ 1) :
    (∫ z, quadraticIntegrand p a t z ∂reference n) ≤
      t*(∑ i, (∑ x, a x*spinValue (x i))^2) +
        16*(n:ℝ)^2*t^2*(∑ x, |a x|)^2 := by
  calc
    _ ≤ ∫ z, majorant p a t z ∂reference n :=
      integral_mono (integrable_quadraticIntegrand p a t) (integrable_majorant p a t)
        (quadraticIntegrand_le_majorant p a t)
    _ = _ := integral_majorant p a ht
    _ ≤ _ := interaction_exp_sum_bound p a ha ht htn

lemma var_nonneg (p : Prior n) (f : Spin n → ℝ) : 0 ≤ var p f :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (p.nonneg _) (sq_nonneg _))

lemma avg_const (p : Prior n) (c : ℝ) : avg p (fun _ => c) = c := by
  rw [avg, ← Finset.sum_mul, p.sum_one, one_mul]

lemma avg_sub (p : Prior n) (f g : Spin n → ℝ) :
    avg p (fun x => f x-g x) = avg p f-avg p g := by
  simp only [avg, mul_sub, Finset.sum_sub_distrib]

lemma avg_mul_const (p : Prior n) (f : Spin n → ℝ) (c : ℝ) :
    avg p (fun x => f x*c) = avg p f*c := by
  simp only [avg, mul_assoc, Finset.sum_mul]

lemma avg_center (p : Prior n) (f : Spin n → ℝ) :
    avg p (fun x => f x-avg p f) = 0 := by rw [avg_sub, avg_const, sub_self]

lemma avg_shift_square (p : Prior n) (f : Spin n → ℝ) (c : ℝ) :
    avg p (fun x => (f x-c)^2) = avg p (fun x => (f x)^2)-2*c*avg p f+c^2 := by
  unfold avg
  calc
    _ = ∑ x, ((p x*(f x)^2-(p x*f x)*(2*c))+p x*c^2) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, p.sum_one]
      ring

end
end SKGap.GaussianStep

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DivergenceIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
noncomputable section
variable {n : ℕ}

lemma var_eq (p : Prior n) (f : Spin n → ℝ) :
    var p f = avg p (fun x => (f x)^2) - (avg p f)^2 := by
  rw [var, avg_shift_square]
  ring

lemma var_le_square (p : Prior n) (f : Spin n → ℝ) :
    var p f ≤ avg p (fun x => (f x)^2) := by rw [var_eq]; linarith [sq_nonneg (avg p f)]

lemma l1_square_le_avg_square (p : Prior n) (f : Spin n → ℝ) :
    (∑ x, |p x*f x|)^2 ≤ avg p (fun x => (f x)^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => sqrt (p x)) (fun x => sqrt (p x)*|f x|)
  have hs : (∑ x, (sqrt (p x))^2) = 1 := by
    simp_rw [sq_sqrt (p.nonneg _)]; exact p.sum_one
  have he : (∑ x, sqrt (p x)*(sqrt (p x)*|f x|)) = ∑ x, |p x*f x| := by
    apply Finset.sum_congr rfl
    intro x _
    rw [← mul_assoc, mul_self_sqrt (p.nonneg x), abs_mul, abs_of_nonneg (p.nonneg x)]
  have hf : (∑ x, (sqrt (p x)*|f x|)^2) = avg p (fun x => (f x)^2) := by
    simp only [avg, mul_pow, sq_sqrt (p.nonneg _), sq_abs]
  rw [he, hs, hf, one_mul] at hc
  exact hc

lemma centered_l1_bound (p : Prior n) (f : Spin n → ℝ) :
    (∑ x, |p x*(f x-avg p f)|)^2 ≤ var p f :=
  l1_square_le_avg_square p (fun x => f x-avg p f)

lemma posterior_avg_weight (p : Prior n) (t : ℝ) (z : Fin n → ℝ) (f : Spin n → ℝ) :
    density p t z * avg (posterior p t z) f = ∑ x, (p x*f x)*likelihood t x z := by
  unfold avg posterior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  dsimp
  field_simp [(density_pos p t z).ne']

lemma integrable_posterior_avg_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) :
    Integrable (fun z => density p t z * avg (posterior p t z) f) (reference n) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul _)

lemma integral_posterior_avg_weight (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) :
    (∫ z, density p t z * avg (posterior p t z) f ∂reference n) = avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x).const_mul _)]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  rfl

lemma posterior_variance_identity (p : Prior n) (t : ℝ) (z : Fin n → ℝ) (f : Spin n → ℝ) :
    density p t z * var (posterior p t z) f =
      density p t z * avg (posterior p t z) (fun x => (f x-avg p f)^2) -
        quadraticIntegrand p (fun x => p x*(f x-avg p f)) t z := by
  have ha := posterior_avg_weight p t z (fun x => f x-avg p f)
  have hshift := avg_shift_square (posterior p t z) f (avg p f)
  rw [avg_sub, avg_const] at ha
  rw [var_eq, hshift, quadraticIntegrand, ← ha]
  field_simp [(density_pos p t z).ne']
  ring

lemma integrable_posterior_variance_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) :
    Integrable (fun z => density p t z * var (posterior p t z) f) (reference n) := by
  simp_rw [posterior_variance_identity]
  exact (integrable_posterior_avg_weight p t _).sub (integrable_quadraticIntegrand p _ t)

lemma integral_posterior_variance (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) :
    (∫ z, density p t z * var (posterior p t z) f ∂reference n) =
      var p f - ∫ z, quadraticIntegrand p (fun x => p x*(f x-avg p f)) t z ∂reference n := by
  simp_rw [posterior_variance_identity]
  rw [integral_sub (integrable_posterior_avg_weight p t _)
    (integrable_quadraticIntegrand p _ t), integral_posterior_avg_weight p ht]
  rfl

theorem variance_step_bound (p : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) (f : Spin n → ℝ) :
    var p f - t*(∑ i, (∑ x, p x*(f x-avg p f)*spinValue (x i))^2) -
        16*(n:ℝ)^2*t^2*var p f ≤
      ∫ z, density p t z*var (posterior p t z) f ∂reference n := by
  rw [integral_posterior_variance p ht]
  have hq := quadratic_bound p (fun x => p x*(f x-avg p f)) (avg_center p f) ht htn
  have he := mul_le_mul_of_nonneg_left (centered_l1_bound p f)
    (show 0 ≤ 16*(n:ℝ)^2*t^2 by positivity)
  linarith

lemma scalar_entropy_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ r*log r-r+1 := by
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hr) hr.le
  have hi : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith

lemma scalar_entropy_le_square {r : ℝ} (hr : 0 < r) : r*log r-r+1 ≤ (r-1)^2 := by
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hr) hr.le
  nlinarith

lemma divergenceIntegrand_eq (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    divergenceIntegrand p q t z = density p t z *
      ((density q t z/density p t z)*log (density q t z/density p t z)-
        density q t z/density p t z+1) := by
  unfold divergenceIntegrand
  field_simp [(density_pos p t z).ne']

lemma divergenceIntegrand_nonneg (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    0 ≤ divergenceIntegrand p q t z := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos p t z).le
    (scalar_entropy_nonneg (div_pos (density_pos q t z) (density_pos p t z)))

lemma density_sub (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    (∑ x, (q x-p x)*likelihood t x z) = density q t z-density p t z := by
  simp only [sub_mul, Finset.sum_sub_distrib, density]

lemma divergenceIntegrand_le_quadratic (p q : Prior n) (t : ℝ) (z : Fin n → ℝ) :
    divergenceIntegrand p q t z ≤ quadraticIntegrand p (fun x => q x-p x) t z := by
  rw [divergenceIntegrand_eq, quadraticIntegrand, density_sub]
  calc
    _ ≤ density p t z*(density q t z/density p t z-1)^2 :=
      mul_le_mul_of_nonneg_left
        (scalar_entropy_le_square (div_pos (density_pos q t z) (density_pos p t z)))
        (density_pos p t z).le
    _ = _ := by field_simp [(density_pos p t z).ne']

lemma continuous_divergenceIntegrand (p q : Prior n) (t : ℝ) :
    Continuous (divergenceIntegrand p q t) := by
  have hd := (continuous_density q t).div (continuous_density p t)
    (fun z => (density_pos p t z).ne')
  exact (((continuous_density q t).mul (hd.log (fun z =>
    (div_pos (density_pos q t z) (density_pos p t z)).ne'))).sub
      (continuous_density q t)).add (continuous_density p t)

lemma integrable_divergenceIntegrand (p q : Prior n) (t : ℝ) :
    Integrable (divergenceIntegrand p q t) (reference n) := by
  apply (integrable_quadraticIntegrand p (fun x => q x-p x) t).mono'
    (continuous_divergenceIntegrand p q t).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (divergenceIntegrand_nonneg p q t z)]
  exact divergenceIntegrand_le_quadratic p q t z

lemma prior_sub_l1 (p q : Prior n) : (∑ x, |q x-p x|) ≤ 2 := by
  calc
    _ ≤ ∑ x, (q x+p x) := Finset.sum_le_sum (fun x _ => by
      simpa only [abs_of_nonneg (q.nonneg x), abs_of_nonneg (p.nonneg x)] using abs_sub (q x) (p x))
    _ = 2 := by rw [Finset.sum_add_distrib, q.sum_one, p.sum_one]; norm_num

lemma prior_sub_sum (p q : Prior n) : (∑ x, (q x-p x)) = 0 := by
  rw [Finset.sum_sub_distrib, q.sum_one, p.sum_one, sub_self]

theorem entropy_step_bound (p q : Prior n) {t : ℝ} (ht : 0 ≤ t)
    (htn : 4*(n:ℝ)*t ≤ 1) :
    (∫ z, divergenceIntegrand p q t z ∂reference n) ≤
      t*(∑ i, (mean q i-mean p i)^2)+64*(n:ℝ)^2*t^2 := by
  have hmean : (∑ i, (∑ x, (q x-p x)*spinValue (x i))^2) =
      ∑ i, (mean q i-mean p i)^2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mean]
  have he : (∑ x, |q x-p x|)^2 ≤ 4 := by
    have hl : 0 ≤ ∑ x, |q x-p x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    nlinarith [prior_sub_l1 p q]
  calc
    _ ≤ ∫ z, quadraticIntegrand p (fun x => q x-p x) t z ∂reference n :=
      integral_mono (integrable_divergenceIntegrand p q t) (integrable_quadraticIntegrand p _ t)
        (divergenceIntegrand_le_quadratic p q t)
    _ ≤ t*(∑ i, (mean q i-mean p i)^2)+16*(n:ℝ)^2*t^2*(∑ x, |q x-p x|)^2 := by
      simpa only [hmean] using quadratic_bound p (fun x => q x-p x) (prior_sub_sum p q) ht htn
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 16*(n:ℝ)^2*t^2 by positivity)]

lemma integrable_relativeEntropy (p q : Prior n) (t : ℝ) :
    Integrable (fun z => density q t z*log (density q t z/density p t z)) (reference n) := by
  have he : (fun z => density q t z*log (density q t z/density p t z)) =
      fun z => divergenceIntegrand p q t z+density q t z-density p t z := by
    funext z
    unfold divergenceIntegrand
    ring
  rw [he]
  exact ((integrable_divergenceIntegrand p q t).add (integrable_density q t)).sub
    (integrable_density p t)

lemma integral_relativeEntropy (p q : Prior n) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z, density q t z*log (density q t z/density p t z) ∂reference n) =
      ∫ z, divergenceIntegrand p q t z ∂reference n := by
  have hi := integral_add
    ((integrable_relativeEntropy p q t).sub (integrable_density q t)) (integrable_density p t)
  have hj := integral_sub (integrable_relativeEntropy p q t) (integrable_density q t)
  simp only [Pi.sub_apply] at hi hj
  rw [hj, integral_density q ht, integral_density p ht] at hi
  change (∫ z, divergenceIntegrand p q t z ∂reference n) = _ at hi
  linarith

lemma avg_add (p : Prior n) (f g : Spin n → ℝ) :
    avg p (fun x => f x+g x) = avg p f+avg p g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

lemma avg_const_mul (p : Prior n) (c : ℝ) (f : Spin n → ℝ) :
    avg p (fun x => c*f x) = c*avg p f := by
  simpa only [mul_comm c] using avg_mul_const p f c

lemma avg_nonneg (p : Prior n) (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ avg p f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (p.nonneg x) (hf x))

lemma cond_flip (p : Prior n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    cond p i f (flip i x) = cond p i f x := by
  simp only [cond, flip_flip, add_comm]

lemma avg_flip (p : Prior n) (i : Fin n) (f : Spin n → ℝ) :
    avg p f = (1/2:ℝ)*∑ x, (p x*f x+p (flip i x)*f (flip i x)) := by
  rw [Finset.sum_add_distrib, sum_flip i (fun x => p x*f x)]
  unfold avg
  ring

lemma conditional_orthogonal (p : Prior n) (hp : ∀ x, 0 < p x) (i : Fin n)
    (f c : Spin n → ℝ) (hc : ∀ x, c (flip i x)=c x) :
    avg p (fun x => (f x-cond p i f x)*c x) = 0 := by
  rw [avg_flip p i]
  have hs : (∑ x, (p x*((f x-cond p i f x)*c x)+
      p (flip i x)*((f (flip i x)-cond p i f (flip i x))*c (flip i x)))) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [cond_flip, hc]
    unfold cond
    field_simp [(add_pos (hp x) (hp (flip i x))).ne']
    ring
  rw [hs, mul_zero]

lemma conditional_minimal (p : Prior n) (hp : ∀ x, 0 < p x) (i : Fin n)
    (f c : Spin n → ℝ) (hc : ∀ x, c (flip i x)=c x) :
    avg p (fun x => (f x-cond p i f x)^2) ≤ avg p (fun x => (f x-c x)^2) := by
  have ho := conditional_orthogonal p hp i f (fun x => cond p i f x-c x)
    (fun x => by rw [cond_flip, hc])
  have he (x : Spin n) : (f x-c x)^2 =
      (f x-cond p i f x)^2+(cond p i f x-c x)^2+
        2*((f x-cond p i f x)*(cond p i f x-c x)) := by ring
  simp_rw [he]
  rw [avg_add, avg_add, avg_const_mul, ho, mul_zero, add_zero]
  exact le_add_of_nonneg_right (avg_nonneg p _ (fun _ => sq_nonneg _))

lemma energy_nonneg (p : Prior n) (f : Spin n → ℝ) : 0 ≤ energy p f :=
  Finset.sum_nonneg (fun _ _ => avg_nonneg p _ (fun _ => sq_nonneg _))

lemma avg_sum (p : Prior n) {ι : Type*} [Fintype ι] (f : ι → Spin n → ℝ) :
    avg p (fun x => ∑ i, f i x) = ∑ i, avg p (f i) := by
  simp only [avg, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma gibbsPrior_avg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    avg (gibbsPrior g h) f = expectation g h f := rfl

lemma gibbsPrior_var (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    var (gibbsPrior g h) f = variance g h f := rfl

lemma gibbsPrior_cond (g : Disorder n) (h : Fin n → ℝ) (i : Fin n)
    (f : Spin n → ℝ) (x : Spin n) :
    cond (gibbsPrior g h) i f x = conditionalExpectation g h i f x := by
  unfold cond gibbsPrior conditionalExpectation
  dsimp
  unfold mass
  field_simp [(partition_pos g h).ne', (add_pos (weight_pos g h x) (weight_pos g h (flip i x))).ne']

lemma gibbsPrior_energy (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    energy (gibbsPrior g h) f = dirichlet g h f := by
  simp only [energy, gibbsPrior_cond, gibbsPrior_avg, dirichlet]

end
end SKGap.GaussianStep

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma continuous_likelihood (t : ℝ) (x : Spin n) : ∀ k,
    Continuous (likelihood t x (k := k))
  | 0 => continuous_const
  | k+1 => (continuous_likelihood t x k).comp continuous_fst |>.mul
      ((GaussianStep.continuous_likelihood t x).comp continuous_snd)

lemma integrable_likelihood (t : ℝ) (x : Spin n) : ∀ k,
    Integrable (likelihood t x (k := k)) (reference n k)
  | 0 => by
    change Integrable (fun _ : Unit => (1:ℝ)) (Measure.dirac ())
    exact integrable_const 1
  | k+1 => (integrable_likelihood t x k).mul_prod (GaussianStep.integrable_likelihood t x)

lemma integral_likelihood {t : ℝ} (ht : 0 ≤ t) (x : Spin n) : ∀ k,
    (∫ h : History n k, likelihood t x h ∂reference n k) = 1
  | 0 => by
    change (∫ _ : Unit, (1:ℝ) ∂Measure.dirac ()) = 1
    rw [integral_dirac]
  | k+1 => by
    change (∫ h, likelihood t x h.1 * GaussianStep.likelihood t x h.2
      ∂(reference n k).prod (GaussianStep.reference n)) = 1
    rw [integral_prod_mul, integral_likelihood ht x k, GaussianStep.integral_likelihood ht, mul_one]

lemma continuous_density (p : Prior n) (t : ℝ) (k : ℕ) : Continuous (density p t (k := k)) :=
  continuous_finsetSum _ (fun x _ => (continuous_likelihood t x k).const_mul (p x))

lemma integrable_density (p : Prior n) (t : ℝ) (k : ℕ) :
    Integrable (density p t (k := k)) (reference n k) :=
  integrable_finsetSum _ (fun x _ => (integrable_likelihood t x k).const_mul (p x))

lemma integral_density (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (∫ h : History n k, density p t h ∂reference n k) = 1 := by
  unfold density
  rw [integral_finsetSum _ (fun x _ => (integrable_likelihood t x k).const_mul (p x))]
  simp_rw [integral_const_mul, integral_likelihood ht, mul_one]
  exact p.sum_one

lemma density_zero (p : Prior n) (t : ℝ) (h : History n 0) : density p t h=1 := by
  simp only [density, likelihood, mul_one, p.sum_one]

lemma posterior_zero (p : Prior n) (t : ℝ) (h : History n 0) : posterior p t h=p := by
  apply Prior.ext
  funext x
  change p x*1/density p t h=p x
  rw [density_zero, mul_one, div_one]

lemma density_succ (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    density p t (k := k+1) (h,z) = density p t h*GaussianStep.density (posterior p t h) t z := by
  change (∑ x, p x*(likelihood t x h*GaussianStep.likelihood t x z)) =
    density p t h*(∑ x, (p x*likelihood t x h/density p t h)*GaussianStep.likelihood t x z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(density_pos p t h).ne']

lemma posterior_succ (p : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    posterior p t (k := k+1) (h,z) = GaussianStep.posterior (posterior p t h) t z := by
  apply Prior.ext
  funext x
  change p x*(likelihood t x h*GaussianStep.likelihood t x z)/density p t (k := k+1) (h,z) =
    (p x*likelihood t x h/density p t h)*GaussianStep.likelihood t x z /
      GaussianStep.density (posterior p t h) t z
  rw [density_succ]
  field_simp [(density_pos p t h).ne', (GaussianStep.density_pos (posterior p t h) t z).ne']

lemma integrable_posterior_avg_weight (p : Prior n) (t : ℝ) (f : Spin n → ℝ) (k : ℕ) :
    Integrable (fun h : History n k => density p t h*avg (posterior p t h) f) (reference n k) := by
  simp_rw [posterior_avg_weight]
  exact integrable_finsetSum _ (fun x _ => ((integrable_likelihood t x k).const_mul (p x)).mul_const (f x))

lemma integral_posterior_avg_weight (p : Prior n) {t : ℝ} (ht : 0 ≤ t) (f : Spin n → ℝ) (k : ℕ) :
    (∫ h : History n k, density p t h*avg (posterior p t h) f ∂reference n k)=avg p f := by
  simp_rw [posterior_avg_weight]
  rw [integral_finsetSum _ (fun x _ => ((integrable_likelihood t x k).const_mul (p x)).mul_const (f x))]
  simp_rw [integral_mul_const, integral_const_mul, integral_likelihood ht, mul_one]
  rfl

lemma density_le (p q : Prior n) {B : ℝ} (hB : ∀x, q x ≤ B*p x)
    (t : ℝ) {k : ℕ} (h : History n k) : density q t h ≤ B*density p t h := by
  unfold density
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _ => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hB x) (likelihood_pos t x h).le)

lemma exists_domination (p q : Prior n) (hp : ∀x,0<p x) :
    ∃B:ℝ,0≤B ∧ ∀x,q x≤B*p x := by
  let B := ∑x,q x/p x
  have hnonneg (x : Spin n) : 0≤q x/p x := div_nonneg (q.nonneg x) (hp x).le
  refine ⟨B,Finset.sum_nonneg (fun x _ => hnonneg x),?_⟩
  intro x
  have hle : q x/p x ≤ B := Finset.single_le_sum (fun y _ => hnonneg y) (Finset.mem_univ x)
  exact (div_le_iff₀ (hp x)).mp hle

lemma divergenceIntegrand_eq (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    divergenceIntegrand p q t h = density p t h*
      ((density q t h/density p t h)*log (density q t h/density p t h)-
        density q t h/density p t h+1) := by
  unfold divergenceIntegrand relativeEntropyIntegrand
  field_simp [(density_pos p t h).ne']

lemma divergenceIntegrand_nonneg (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0≤divergenceIntegrand p q t h := by
  rw [divergenceIntegrand_eq]
  exact mul_nonneg (density_pos p t h).le
    (scalar_entropy_nonneg (div_pos (density_pos q t h) (density_pos p t h)))

lemma continuous_log_ratio (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (fun h : History n k => log (density q t h/density p t h)) :=
  ((continuous_density q t k).div (continuous_density p t k)
    (fun h => (density_pos p t h).ne')).log
      (fun h => (div_pos (density_pos q t h) (density_pos p t h)).ne')

lemma continuous_relativeEntropyIntegrand (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (relativeEntropyIntegrand p q t (k := k)) :=
  (continuous_density q t k).mul (continuous_log_ratio p q t k)

lemma continuous_divergenceIntegrand (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (divergenceIntegrand p q t (k := k)) :=
  ((continuous_relativeEntropyIntegrand p q t k).sub (continuous_density q t k)).add
    (continuous_density p t k)

lemma integrable_divergenceIntegrand (p q : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ) :
    Integrable (divergenceIntegrand p q t (k := k)) (reference n k) := by
  obtain ⟨B,hB,hdom⟩:=exists_domination p q hp
  apply ((integrable_density p t k).mul_const ((B+1)^2)).mono'
    (continuous_divergenceIntegrand p q t k).aestronglyMeasurable
  filter_upwards [] with h
  change |divergenceIntegrand p q t h|≤density p t h*(B+1)^2
  rw [abs_of_nonneg (divergenceIntegrand_nonneg p q t h), divergenceIntegrand_eq]
  apply mul_le_mul_of_nonneg_left _ (density_pos p t h).le
  have hr : 0<density q t h/density p t h := div_pos (density_pos q t h) (density_pos p t h)
  have hle : density q t h/density p t h≤B :=
    (div_le_iff₀ (density_pos p t h)).mpr (density_le p q hdom t h)
  exact (scalar_entropy_le_square hr).trans (by nlinarith)

lemma integrable_relativeEntropyIntegrand (p q : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ) :
    Integrable (relativeEntropyIntegrand p q t (k := k)) (reference n k) := by
  have hi := ((integrable_divergenceIntegrand p q hp t k).add (integrable_density q t k)).sub
    (integrable_density p t k)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  simp only [Pi.sub_apply,Pi.add_apply,divergenceIntegrand]
  ring

lemma entropy_eq_divergence (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    entropy p q t k = ∫h:History n k,divergenceIntegrand p q t h ∂reference n k := by
  have hi := integral_add
    ((integrable_relativeEntropyIntegrand p q hp t k).sub (integrable_density q t k))
    (integrable_density p t k)
  have hj := integral_sub (integrable_relativeEntropyIntegrand p q hp t k)
    (integrable_density q t k)
  simp only [Pi.sub_apply] at hi hj
  rw [hj,integral_density p ht,integral_density q ht] at hi
  change (∫h:History n k,divergenceIntegrand p q t h ∂reference n k) = _ at hi
  change (∫h:History n k,relativeEntropyIntegrand p q t h ∂reference n k) = _
  linarith

lemma entropy_zero (p q : Prior n) (t : ℝ) : entropy p q t 0=0 := by
  unfold entropy relativeEntropyIntegrand
  simp only [density_zero,div_self one_ne_zero,log_one,mul_zero,integral_zero]

lemma integrable_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ} (F : History n k → ℝ)
    (hF : Measurable F) (hi : Integrable (fun h => density p t h*F h) (reference n k)) :
    Integrable (fun h : History n (k+1) => density p t h*F h.1) (reference n (k+1)) := by
  change Integrable (fun h : History n k × (Fin n → ℝ) => density p t (k := k+1) h*F h.1)
    ((reference n k).prod (GaussianStep.reference n))
  apply (integrable_prod_iff (((continuous_density p t (k+1)).measurable.mul
    (hF.comp measurable_fst)).aestronglyMeasurable)).mpr
  constructor
  · filter_upwards [] with h
    change Integrable (fun z => density p t (k := k+1) (h,z)*F h) (GaussianStep.reference n)
    simp_rw [density_succ]
    have he : (fun z => density p t h*GaussianStep.density (posterior p t h) t z*F h) =
        fun z => (density p t h*F h)*GaussianStep.density (posterior p t h) t z := by
      funext z; ring
    rw [he]
    exact (GaussianStep.integrable_density (posterior p t h) t).const_mul _
  · have he (h : History n k) :
        (∫z, ‖density p t (k := k+1) (h,z)*F h‖ ∂GaussianStep.reference n) = ‖density p t h*F h‖ := by
      simp_rw [density_succ,Real.norm_eq_abs,abs_mul,abs_of_pos (density_pos p t h),
        abs_of_pos (GaussianStep.density_pos (posterior p t h) t _)]
      rw [integral_mul_const,integral_const_mul,GaussianStep.integral_density _ ht]
      ring
    change Integrable (fun h : History n k =>
      ∫z, ‖density p t (k := k+1) (h,z)*F h‖ ∂GaussianStep.reference n) (reference n k)
    simp_rw [he]
    exact hi.norm

lemma integral_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ} (F : History n k → ℝ)
    (hF : Measurable F) (hi : Integrable (fun h => density p t h*F h) (reference n k)) :
    (∫h:History n (k+1),density p t h*F h.1 ∂reference n (k+1)) =
      ∫h:History n k,density p t h*F h ∂reference n k := by
  rw [show reference n (k+1)=(reference n k).prod (GaussianStep.reference n) from rfl,
    integral_prod _ (integrable_lift p ht F hF hi)]
  apply integral_congr_ae
  filter_upwards [] with h
  simp_rw [density_succ]
  rw [integral_mul_const,integral_const_mul,GaussianStep.integral_density _ ht,mul_one]

lemma relativeEntropy_succ (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) (z : Fin n → ℝ) :
    relativeEntropyIntegrand p q t (k := k+1) (h,z) =
      density q t (k := k+1) (h,z)*log (density q t h/density p t h)+
      density q t h*(GaussianStep.density (posterior q t h) t z *
        log (GaussianStep.density (posterior q t h) t z/GaussianStep.density (posterior p t h) t z)) := by
  unfold relativeEntropyIntegrand
  rw [density_succ,density_succ]
  rw [mul_div_mul_comm,log_mul
    (div_pos (density_pos q t h) (density_pos p t h)).ne'
    (div_pos (GaussianStep.density_pos (posterior q t h) t z)
      (GaussianStep.density_pos (posterior p t h) t z)).ne']
  ring

theorem entropy_succ (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    entropy p q t (k+1) = entropy p q t k+
      ∫h:History n k,density q t h*
        (∫z,GaussianStep.divergenceIntegrand (posterior p t h) (posterior q t h) t z
          ∂GaussianStep.reference n) ∂reference n k := by
  let L : History n k → ℝ := fun h => log (density q t h/density p t h)
  have hL : Measurable L := (continuous_log_ratio p q t k).measurable
  have hiL : Integrable (fun h => density q t h*L h) (reference n k) :=
    integrable_relativeEntropyIntegrand p q hp t k
  have hLift := integrable_lift q ht L hL hiL
  have hi := (integrable_relativeEntropyIntegrand p q hp t (k+1)).sub hLift
  have he : (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz - density q t hz*L hz.1) =
      fun hz => density q t hz.1*(GaussianStep.density (posterior q t hz.1) t hz.2*
        log (GaussianStep.density (posterior q t hz.1) t hz.2/GaussianStep.density (posterior p t hz.1) t hz.2)) := by
    funext ⟨h,z⟩
    rw [relativeEntropy_succ]
    dsimp [L]
    ring
  have hs := integral_sub (integrable_relativeEntropyIntegrand p q hp t (k+1)) hLift
  change (∫hz:History n (k+1),relativeEntropyIntegrand p q t hz-density q t hz*L hz.1
    ∂reference n (k+1)) = _ at hs
  rw [integral_lift q ht L hL hiL] at hs
  change (∫hz:History n (k+1),relativeEntropyIntegrand p q t hz-density q t hz*L hz.1
    ∂reference n (k+1)) = entropy p q t (k+1)-entropy p q t k at hs
  change Integrable (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-
    density q t hz*L hz.1) (reference n (k+1)) at hi
  rw [he] at hi hs
  rw [show reference n (k+1)=(reference n k).prod (GaussianStep.reference n) from rfl,
    integral_prod _ hi] at hs
  simp_rw [integral_const_mul,GaussianStep.integral_relativeEntropy _ _ ht] at hs
  linarith

lemma eventProbability_nonneg (p : Prior n) (t : ℝ) {k : ℕ} (E : Set (History n k)) :
    0≤eventProbability p t E := integral_nonneg (fun h => (density_pos p t h).le)

lemma eventProbability_eq (p : Prior n) (t : ℝ) {k : ℕ} (E : Set (History n k))
    (hE : MeasurableSet E) : ENNReal.ofReal (eventProbability p t E)=law p t k E := by
  rw [eventProbability,law,withDensity_apply _ hE]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_density p t k).integrableOn
    (ae_of_all _ (fun h => (density_pos p t h).le))

lemma scalar_entropy_fenchel {r : ℝ} (hr : 0 < r) (c : ℝ) :
    c*r-exp c+1 ≤ r*log r-r+1 := by
  have he := mul_le_mul_of_nonneg_left (add_one_le_exp (c-log r)) hr.le
  have hx : r*exp (c-log r)=exp c := by
    rw [exp_sub,exp_log hr]
    field_simp
  rw [hx] at he
  nlinarith

theorem entropy_event_bound (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (k : ℕ) (E : Set (History n k)) (hE : MeasurableSet E) (c : ℝ)
    (hsmall : eventProbability p t E≤exp (-c)) :
    c*eventProbability q t E ≤ entropy p q t k+1 := by
  have hpoint (h : History n k) :
      c*E.indicator (density q t) h ≤ divergenceIntegrand p q t h+
        exp c*E.indicator (density p t) h := by
    by_cases he : h∈E
    · rw [Set.indicator_of_mem he,Set.indicator_of_mem he,divergenceIntegrand_eq]
      have hf := mul_le_mul_of_nonneg_left
        (scalar_entropy_fenchel (div_pos (density_pos q t h) (density_pos p t h)) c)
        (density_pos p t h).le
      have hd : density p t h*(density q t h/density p t h)=density q t h :=
        mul_div_cancel₀ _ (density_pos p t h).ne'
      have hmul : density p t h*(c*(density q t h/density p t h))=c*density q t h := by
        rw [←mul_assoc, mul_comm (density p t h) c,mul_assoc,hd]
      nlinarith [density_pos p t h]
    · rw [Set.indicator_of_notMem he,Set.indicator_of_notMem he,mul_zero,mul_zero,add_zero]
      exact divergenceIntegrand_nonneg p q t h
  have hi := integral_mono (((integrable_density q t k).indicator hE).const_mul c)
    ((integrable_divergenceIntegrand p q hp t k).add
      (((integrable_density p t k).indicator hE).const_mul (exp c))) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (integrable_divergenceIntegrand p q hp t k)
      (((integrable_density p t k).indicator hE).const_mul (exp c)),integral_const_mul,
    integral_indicator hE,integral_indicator hE,←entropy_eq_divergence p q hp ht] at hi
  change c*eventProbability q t E≤entropy p q t k+exp c*eventProbability p t E at hi
  have hm := mul_le_mul_of_nonneg_left hsmall (exp_pos c).le
  rw [←exp_add,add_neg_cancel,exp_zero] at hm
  linarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_ContinuousPosteriorMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma continuous_posterior_mass (p : Prior n) (t : ℝ) (k : ℕ) (x : Spin n) :
    Continuous (fun h : History n k => posterior p t h x) :=
  ((continuous_likelihood t x k).const_mul (p x)).div (continuous_density p t k)
    (fun h => (density_pos p t h).ne')

lemma continuous_posterior_avg (p : Prior n) (t : ℝ) (k : ℕ) (f : Spin n→ℝ) :
    Continuous (fun h : History n k => avg (posterior p t h) f) :=
  continuous_finsetSum _ (fun x _ => (continuous_posterior_mass p t k x).mul_const (f x))

lemma continuous_posterior_var (p : Prior n) (t : ℝ) (k : ℕ) (f : Spin n→ℝ) :
    Continuous (fun h : History n k => var (posterior p t h) f) := by
  simp_rw [var_eq]
  exact (continuous_posterior_avg p t k _).sub ((continuous_posterior_avg p t k f).pow 2)

lemma posterior_mass_pos (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) {k : ℕ} (h : History n k)
    (x : Spin n) : 0<posterior p t h x :=
  div_pos (mul_pos (hp x) (likelihood_pos t x h)) (density_pos p t h)

lemma posterior_energy_bound (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) {k : ℕ} (h : History n k)
    (f : Spin n→ℝ) : energy (posterior p t h) f ≤
      avg (posterior p t h) (fun x => ∑i,(f x-cond p i f x)^2) := by
  rw [avg_sum]
  exact Finset.sum_le_sum (fun i _ => conditional_minimal (posterior p t h)
    (posterior_mass_pos p hp t h) i f (cond p i f) (cond_flip p i f))

lemma continuous_posterior_cond (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    Continuous (fun h : History n k => cond (posterior p t h) i f x) := by
  apply Continuous.div
    (((continuous_posterior_mass p t k x).mul_const (f x)).add
      ((continuous_posterior_mass p t k (flip i x)).mul_const (f (flip i x))))
    ((continuous_posterior_mass p t k x).add (continuous_posterior_mass p t k (flip i x)))
  intro h
  exact (add_pos (posterior_mass_pos p hp t h x) (posterior_mass_pos p hp t h (flip i x))).ne'

lemma continuous_posterior_energy (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (f : Spin n→ℝ) : Continuous (fun h : History n k => energy (posterior p t h) f) := by
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  exact (continuous_posterior_mass p t k x).mul
    ((continuous_const.sub (continuous_posterior_cond p hp t k i f x)).pow 2)

lemma integrable_posterior_energy_weight (p : Prior n) (hp : ∀x,0<p x) (t : ℝ) (k : ℕ)
    (f : Spin n→ℝ) :
    Integrable (fun h : History n k => density p t h*energy (posterior p t h) f) (reference n k) := by
  apply (integrable_posterior_avg_weight p t (fun x => ∑i,(f x-cond p i f x)^2) k).mono'
    ((continuous_density p t k).mul (continuous_posterior_energy p hp t k f)).aestronglyMeasurable
  filter_upwards [] with h
  change |density p t h*energy (posterior p t h) f|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos p t h).le (energy_nonneg _ _))]
  exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t h f) (density_pos p t h).le

theorem energy_history_bound (p : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (k : ℕ) (f : Spin n→ℝ) :
    (∫h:History n k,density p t h*energy (posterior p t h) f ∂reference n k) ≤ energy p f := by
  let F : Spin n→ℝ := fun x => ∑i,(f x-cond p i f x)^2
  have hle : (∫h:History n k,density p t h*energy (posterior p t h) f ∂reference n k) ≤
      ∫h:History n k,density p t h*avg (posterior p t h) F ∂reference n k := by
    apply integral_mono (integrable_posterior_energy_weight p hp t k f)
      (integrable_posterior_avg_weight p t F k)
    intro h
    exact mul_le_mul_of_nonneg_left (posterior_energy_bound p hp t h f) (density_pos p t h).le
  rw [integral_posterior_avg_weight p ht] at hle
  change _≤avg p (fun x => ∑i,(f x-cond p i f x)^2) at hle
  rw [avg_sum] at hle
  exact hle

lemma squarePrior_posterior (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2))
    (t : ℝ) {k : ℕ} (h : History n k) :
    posterior (squarePrior p f hf) t h =
      squarePrior (posterior p t h) f (posterior_square_pos p f hf t h) := by
  apply Prior.ext
  funext x
  change (p x*(f x)^2/avg p (fun x => (f x)^2))*likelihood t x h /
      density (squarePrior p f hf) t h =
    (p x*likelihood t x h/density p t h)*(f x)^2/avg (posterior p t h) (fun x => (f x)^2)
  rw [squarePrior_density]
  field_simp [hf.ne', (density_pos p t h).ne', (posterior_square_pos p f hf t h).ne']

lemma weighted_energy_identity (p : Prior n) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) (t : ℝ) {k : ℕ} (h : History n k) :
    density (squarePrior p f hf) t h*
      (energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)) =
        density p t h*energy (posterior p t h) f/avg p (fun x => (f x)^2) := by
  rw [squarePrior_density]
  field_simp [(posterior_square_pos p f hf t h).ne']

lemma mean_difference_square_le (p q : Prior n) :
    (∑i,(mean q i-mean p i)^2)≤4*(n:ℝ) := by
  calc
    _≤∑i:Fin n,(4:ℝ) := Finset.sum_le_sum (fun i _ => by
      have hp:=abs_le.mp (mean_abs_le_one p i)
      have hq:=abs_le.mp (mean_abs_le_one q i)
      nlinarith [sq_nonneg (mean q i-mean p i)])
    _=_ := by simp; ring

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_GibbsContinuity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
open scoped BigOperators
variable {n : ℕ}

lemma continuous_weight (g : Disorder n) (x : Spin n) : Continuous (fun h : Fin n→ℝ=>weight g h x) := by
  unfold weight hamiltonian
  fun_prop

lemma continuous_partition (g : Disorder n) : Continuous (partition g) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _=>continuous_weight g x)

lemma continuous_mass (g : Disorder n) (x : Spin n) : Continuous (fun h : Fin n→ℝ=>mass g h x) :=
  (continuous_weight g x).div (continuous_partition g) (fun h=>(partition_pos g h).ne')

lemma continuous_expectation (g : Disorder n) (f : Spin n→ℝ) : Continuous (fun h : Fin n→ℝ=>expectation g h f) := by
  unfold expectation
  exact continuous_finsetSum _ (fun x _=>(continuous_mass g x).mul continuous_const)

lemma continuous_conditionalExpectation (g : Disorder n) (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    Continuous (fun h : Fin n→ℝ=>conditionalExpectation g h i f x) := by
  unfold conditionalExpectation
  exact ((continuous_weight g x).mul continuous_const |>.add
    ((continuous_weight g (flip i x)).mul continuous_const)).div
    ((continuous_weight g x).add (continuous_weight g (flip i x)))
    (fun h=>(add_pos (weight_pos g h x) (weight_pos g h (flip i x))).ne')

lemma continuous_variance (g : Disorder n) (f : Spin n→ℝ) : Continuous (fun h : Fin n→ℝ=>variance g h f) := by
  unfold variance expectation
  apply continuous_finsetSum
  intro x _
  exact (continuous_mass g x).mul ((continuous_const.sub (continuous_expectation g f)).pow 2)

lemma continuous_dirichlet (g : Disorder n) (f : Spin n→ℝ) : Continuous (fun h : Fin n→ℝ=>dirichlet g h f) := by
  unfold dirichlet expectation
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  exact (continuous_mass g x).mul ((continuous_const.sub (continuous_conditionalExpectation g i f x)).pow 2)

lemma terminal_goodSet_closed (g : Disorder n) (C : ℝ) :
    IsClosed {h : Fin n→ℝ | ∀ f : Spin n→ℝ,variance g h f ≤ C*dirichlet g h f} := by
  have he : {h : Fin n→ℝ | ∀ f : Spin n→ℝ,variance g h f ≤ C*dirichlet g h f}=
      ⋂ f : Spin n→ℝ,{h | variance g h f ≤ C*dirichlet g h f} := by ext h;simp
  rw [he]
  exact isClosed_iInter (fun f=>isClosed_le (continuous_variance g f) (continuous_const.mul (continuous_dirichlet g f)))

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_ConditionalBadSet
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma isClosed_badFieldSet (n : ℕ) (j A ε c : ℝ) : IsClosed (badFieldSet n j A ε c) := by
  let X := ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) × ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  let : CompactSpace ↥(Set.Icc (0 : Fin n → ℝ) (fun _=>A)) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ))) :=
    {p | (∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2) ≤ ε^2*(n:ℝ) ∧
      quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1) (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp ≤ c}
  have ha (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.1:Fin n → ℝ) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
  have hx (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp i) :=
    (continuous_apply i).comp ((PiLp.continuous_ofLp 2 (fun _ : Fin n=>ℝ)).comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hy (i : Fin n) : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
      tanh (p.2.2 i)) := continuous_tanh.comp ((continuous_apply i).comp (continuous_snd.comp continuous_snd))
  have hS : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        ∑ i,((p.1.1:Fin n → ℝ) i-spinVariance p.2.2 i)^2)
        (g := fun _ => ε^2*(n:ℝ)) (by
        apply continuous_finsetSum
        intro i _
        exact ((ha i).sub (continuous_const.sub ((hy i).pow 2))).pow 2) continuous_const
    · exact isClosed_le (f := fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) =>
        quadraticForm (fieldHessian j (plantedInteraction j p.2.1) p.2.2 p.1.1)
          (p.1.2:EuclideanSpace ℝ (Fin n)).ofLp) (g := fun _=>c) (by
        dsimp [X,quadraticForm,fieldHessian,hessianCore,plantedInteraction,onsager,overlap,magnetization]
        apply continuous_finsetSum; intro i _
        apply continuous_finsetSum; intro k _
        apply Continuous.mul _ (hx k)
        apply Continuous.mul (hx i)
        apply Continuous.add continuous_const
        apply Continuous.mul _ (Real.continuous_sqrt.comp (ha k))
        apply Continuous.mul (Real.continuous_sqrt.comp (ha i))
        exact (((continuous_const.mul (continuous_const.sub
          ((continuous_finsetSum _ (fun l _ => (hy l).pow 2)).div_const _))).mul continuous_const).sub
          ((by fun_prop : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) => p.2.1 i k)).add continuous_const)).sub
          (((continuous_const.mul (hy i))).mul (hy k))) continuous_const
  have hproj := isClosedMap_snd_of_compactSpace S hS
  convert hproj using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨a,ha,hclose,x,hx,hquad⟩
    have ha' : a ∈ Icc (0 : Fin n → ℝ) (fun _=>A) := ⟨fun i=>(ha i).1,fun i=>(ha i).2⟩
    have hx' : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
    exact ⟨((⟨a,ha'⟩,⟨x,hx'⟩),p),⟨hclose,hquad⟩,rfl⟩
  · rintro ⟨⟨⟨a,x⟩,p'⟩,hS,rfl⟩
    exact ⟨a,fun i=>⟨a.2.1 i,a.2.2 i⟩,hS.1,x,by simpa only [Metric.mem_sphere,dist_zero_right] using x.2,hS.2⟩

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_SteinRecipeRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein
variable {n : ℕ} {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]

lemma steinCoefficientBudget_nonneg (R : ℝ) : 0 ≤ steinCoefficientBudget R := by
  have h0:= (KernelExpr.atom 0 0 false).mass_nonneg
  have h1:= (KernelExpr.atom 0 0 false).dBudget_nonneg R
  have h2:= (KernelExpr.atom 0 0 false).ddBudget_nonneg R
  unfold steinCoefficientBudget
  positivity

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_MarkedDiagnostic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.MarkedPolynomial
variable {n : ℕ}

lemma wordBounded_mono {A B : ℝ} {u : OrdinaryWord n} (h : wordBounded A u) (hab : A≤B) :
    wordBounded B u := by
  intro l hl; cases l with
  | noise=>trivial
  | diag p=>exact fun i=>(h (.diag p) hl i).trans hab

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_UniformResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M Nmax : ℕ} {A j : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {P : ∀a,Observables (n a)}

lemma residualCoefficientBudget_ge (j : ℝ) {K : ℝ} (hK : 0≤K) (t p : ℕ) :
    K ≤ residualCoefficientBudget j K t p := by
  simpa only [mul_one,residualCoefficientBudget] using mul_le_mul_of_nonneg_left
    (one_le_pow₀ (by linarith [steinCoefficientBudget_nonneg |j|]) :
      1≤(1+4*steinCoefficientBudget |j|)^(t-p)) hK

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_PrimaryQuenched
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Primary
open SKGap Matrix MeasureTheory ProbabilityTheory Real Set
open SKGap.Noncrossing.Primary

variable {n : ℕ}

lemma formalOpBound_nonneg (j : ℝ) {R : ℝ} (hR : 0≤R) (k : ℕ) :
    0≤formalOpBound j R k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [formalOpBound]
  | one => exact hR
  | more k hk hk1 => dsimp only [formalOpBound]; positivity

lemma primaryMatrix_opNorm {j R : ℝ} (J : Interaction n) (a : ℕ→Fin n→ℝ)
    (hn : 0<n) (hR : 0≤R) (hJ : SKGap.opNorm J≤R) (ha : ∀ l i,|a l i|≤1) (k : ℕ) :
    SKGap.opNorm (primaryMatrix j J a k)≤formalOpBound j R k := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hd (l : ℕ) : SKGap.opNorm (Matrix.diagonal (a l))≤1 :=
    SKGap.opNorm_diagonal_le zero_le_one (ha l)
  have hp (l : ℕ) : SKGap.opNorm (Matrix.diagonal (previousDiagonal a l))≤1 := by
    apply SKGap.opNorm_diagonal_le zero_le_one
    cases l with
    | zero => simp [previousDiagonal]
    | succ l => exact ha l
  induction k using Nat.twoStepInduction with
  | zero => exact SKGap.opNorm_one_le
  | one => exact hJ
  | more k hk hk1 =>
    dsimp only [primaryMatrix,formalOpBound]
    apply (SKGap.opNorm_sub _ _).trans
    apply add_le_add
    · apply (SKGap.opNorm_mul _ _).trans
      have hJD : SKGap.opNorm (J*Matrix.diagonal (a k))≤R :=
        (SKGap.opNorm_mul _ _).trans ((mul_le_mul hJ (hd k) (norm_nonneg _) hR).trans_eq (mul_one _))
      exact mul_le_mul hJD hk1 (norm_nonneg _) hR
    · rw [opNorm_smul,abs_mul]
      have hm : SKGap.opNorm (Matrix.diagonal (previousDiagonal a k)*primaryMatrix j J a k)≤
          formalOpBound j R k :=
        (SKGap.opNorm_mul _ _).trans ((mul_le_mul (hp k) hk (norm_nonneg _)
          zero_le_one).trans_eq (one_mul _))
      calc
        _ ≤ (|j| *1)*formalOpBound j R k := mul_le_mul
          (mul_le_mul_of_nonneg_left (mean_abs_le_one (ha k)) (abs_nonneg _)) hm
          (norm_nonneg _) (by positivity)
        _ = _ := by ring

end SKGapCutoff.Primary

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_OrdinaryWordEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma wordBounded_lift (A : ℝ) (w : OrdinaryWord n) :
    wordBounded A w ↔ ∀l∈liftWord w,l.bounded A := by
  constructor
  · intro h l hl
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hl
    cases a <;> exact h _ ha
  · intro h l hl
    have hh:=h (Letter.toWord l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
    cases l <;> exact hh

lemma wordSeminormBound_diagram {J : Interaction n} {j A C : ℝ} {L : ℕ}
    (h : WordSeminormBound J j A C L) : WordDiagramBound J j A C L := h false

lemma offDiagonalSeminorm_sub_diagonal (M : Interaction n) (a : Fin n→ℝ) :
    SKGap.offDiagonalSeminorm (M-Matrix.diagonal a)=SKGap.offDiagonalSeminorm M := by
  unfold SKGap.offDiagonalSeminorm
  congr 1
  ext ⟨i,k⟩
  by_cases hik:i=k <;> simp [SKGap.offDiagonalVector,Matrix.diagonal_apply,hik]

lemma matrixWord_opNorm (J : Interaction n) (hn : 0<n) {R : ℝ}
    (hR : 1≤R) (hJ : SKGap.opNorm J≤R) (w : OrdinaryWord n) (hw : wordBounded R w) :
    SKGap.opNorm (matrixWord J w)≤R^w.length := by
  let : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  induction w with
  | nil=>simpa [matrixWord] using (SKGap.opNorm_one_le (ι:=Fin n))
  | cons l w ih=>
    have hl : SKGap.opNorm (matrixLetter J l)≤R := by
      cases l with
      | noise=>exact hJ
      | diag a=>exact SKGap.opNorm_diagonal_le (by linarith) (hw (.diag a) (List.mem_cons_self))
    have hh:=ih (fun a ha=>hw a (List.mem_cons_of_mem _ ha))
    simp only [matrixWord,List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    exact (SKGap.opNorm_mul _ _).trans ((mul_le_mul hl hh (norm_nonneg _) (by linarith)).trans_eq (mul_comm _ _))

lemma wordSeminormBound_test {J : Interaction n} {j A C R : ℝ} {L : ℕ}
    (h : WordSeminormBound J j A C L) (hn : 0<n) (hR : 1≤R) (hA : A≤R) (hJ : SKGap.opNorm J≤R) :
    WordTestBound J A (R^L+C) L := by
  intro w hw hb
  have hs:=h true w hw hb
  simp only [matrixWordSeminorm,↓reduceIte,offDiagonalSeminorm_sub_diagonal] at hs
  exact add_le_add ((matrixWord_opNorm J hn hR hJ w (wordBounded_mono hb hA)).trans
    (pow_le_pow_right₀ hR hw)) hs

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_PrimaryWordEventBinding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary MeasureTheory ProbabilityTheory Real Set
variable {n : ℕ}

lemma WordSeminormBound.mono {J : Interaction n} {j A C : ℝ} {L K : ℕ}
    (h : WordSeminormBound J j A C L) (hK : K≤L) : WordSeminormBound J j A C K :=
  fun p w hw hb=>h p w (hw.trans hK) hb

lemma primaryEventBudget_nonneg {j R C : ℝ} (hR : 0≤R) (hC : 0≤C) (M : ℕ) :
    0≤primaryEventBudget j R C M :=
  Finset.sum_nonneg (fun _ _=>add_nonneg (formalOpBound_nonneg j hR _) (mul_nonneg (massBound_pos j _).le hC))

lemma wordEvent_formal {j R A C : ℝ} (J : Interaction n) (hn : 0<n)
    (hR : 0≤R) (hC : 0≤C) (hA : 1≤A) (hJ : SKGap.opNorm J≤R) (M L : ℕ) (hML : 2*M≤L)
    (hw : WordSeminormBound J j A C L) (h : Fin n→ℝ) (x : Spin n) (l : ℕ) (hl : l<M) :
    ShapeBound (formalField j J h x l) (primaryEventBudget j R C M) := by
  let : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let q:Fin M:=⟨l,hl⟩
  have hnon := formalOpBound_nonneg j hR (l+1)
  have hmass := mul_nonneg (massBound_pos j (l+1)).le hC
  have hb:=Finset.single_le_sum (s:=Finset.univ)
    (f:=fun q:Fin M=>formalOpBound j R (q.val+1)+massBound j (q.val+1)*C)
    (fun q _=>add_nonneg (formalOpBound_nonneg j hR _) (mul_nonneg (massBound_pos j _).le hC))
    (Finset.mem_univ q)
  have ho : formalOpBound j R (l+1)≤primaryEventBudget j R C M :=
    (le_add_of_nonneg_right hmass).trans hb
  have hm : massBound j (l+1)*C≤primaryEventBudget j R C M :=
    (le_add_of_nonneg_left hnon).trans hb
  have ha:=primaryDiagonal_bounded j J h x
  have hp (p : Bool) : matrixWordSeminorm p (formalField j J h x l)≤primaryEventBudget j R C M := by
    apply (primaryMatrix_seminorm p j J (primaryDiagonal j J h x) (l+1) (by omega) ?_).trans
    · exact (mul_le_mul_of_nonneg_right (primaryMass_bound j _ ha (l+1)) hC).trans hm
    · intro t ht
      have htB:=primaryPolynomial_admissible j _ ha (l+1) t ht
      exact hw p t.2 (htB.1.trans (by omega))
        (wordBounded_mono ((wordBounded_lift 1 _).mpr htB.2) hA)
  exact ⟨(primaryMatrix_opNorm J _ hn hR hJ ha (l+1)).trans ho,hp false,hp true⟩

lemma wordEvent_recipeEvent {j R A C : ℝ} (J : Interaction n) (hn : 0<n)
    (hR : 1≤R) (hA : 1≤A) (hAR : A≤R) (hC : 0≤C) (hJ : SKGap.opNorm J≤R)
    (M Nmax : ℕ) (hw : WordSeminormBound J j A C (2*M+2*Nmax+3)) :
    RecipeMatrixEvent j R A (primaryEventBudget j R C M) (R^(2*Nmax+3)+C) C M Nmax J := by
  refine ⟨hJ,fun h x l hl=>wordEvent_formal J hn (by linarith) hC hA hJ M _ (by omega) hw h x l hl,
    wordSeminormBound_test (hw.mono (by omega)) hn hR hAR hJ,?_⟩
  exact wordSeminormBound_diagram (hw.mono (by omega))

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary

lemma exp_rate_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ=>exp (-c*(n:ℝ))) atTop (𝓝 0) := by
  simpa using (summable_pow_mul_exp_neg_nat_mul 0 hc).tendsto_atTop_zero
lemma n_exp_rate_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ=>(n:ℝ)*exp (-c*(n:ℝ))) atTop (𝓝 0) := by
  simpa using (summable_pow_mul_exp_neg_nat_mul 1 hc).tendsto_atTop_zero

lemma recipeNormTail_limit {j : ℝ} (hj : 0<j) :
    Tendsto (recipeNormTail j) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))) atTop (𝓝 0) := by
    have H:=ENNReal.tendsto_ofReal ((exp_rate_limit (c:=1/(π^2*j)) (by positivity)).const_mul 2)
    simpa only [mul_zero,ENNReal.ofReal_zero,show ∀(n : ℕ),-(1/(π^2*j))*(n:ℝ)=-(n:ℝ)/(π^2*j) by intro n;ring] using H
  have h₂ : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))) atTop (𝓝 0) := by
    have H:=ENNReal.tendsto_ofReal ((n_exp_rate_limit (c:=1/(8*j)) (by positivity)).const_mul 2)
    have HH : Tendsto (fun n : ℕ=>ENNReal.ofReal (2*((n:ℝ)*exp (-(1/(8*j))*(n:ℝ))))) atTop (𝓝 0):=by simpa using H
    apply HH.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ)≠0:=by exact_mod_cast (by omega : n≠0)
    congr 1
    rw [mul_assoc]
    congr 2
    field_simp
  convert h₁.add h₂ using 1 <;> first | rfl | simp

lemma ordinaryWordTail_limit {j : ℝ} (hj : 0<j) (L : ℕ) :
    Tendsto (ordinaryWordTail j L) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun n : ℕ=>ENNReal.ofReal (3*exp (-(n:ℝ)))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal ((exp_rate_limit (c:=1) (by norm_num)).const_mul 3)
  have h₂ : Tendsto (fun n : ℕ=>ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2)))) atTop (𝓝 0) := by
    have hsq : 0<(sqrt (2*j))^2:=by rw [sq_sqrt (by positivity)]; positivity
    have H:=ENNReal.tendsto_ofReal (exp_rate_limit (c:=2/(π^2*(sqrt (2*j))^2)) (by positivity))
    simpa only [ENNReal.ofReal_zero,show ∀(n : ℕ),-(2/(π^2*(sqrt (2*j))^2))*(n:ℝ)= -2*(n:ℝ)/(π^2*(sqrt (2*j))^2) by intro n;ring] using H
  have h₃:=(ENNReal.Tendsto.const_mul h₁ (a:=((wordPatternSet L L).card:ENNReal)) (Or.inr (by simp))).add h₂ |>.add (recipeNormTail_limit hj)
  convert ENNReal.Tendsto.const_mul h₃ (a:=2) (Or.inr (by simp)) using 1 <;> first | rfl | simp

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_FixedNormRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary

lemma physicalNormBound_pos (j : ℝ) : 0<physicalNormBound j := by
  unfold physicalNormBound
  positivity

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_FieldGibbs
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff
variable {n : ℕ}

lemma fieldGibbs_edge (g : SKGap.Disorder n) (h : Fin n→ℝ) :
    fieldGibbs (GapBridge.edgeInteraction g) h=SKGap.mass g h := by
  have he (x : Spin n) : fieldEnergy (GapBridge.edgeInteraction g) h x=SKGap.hamiltonian g h x := by
    simp [fieldEnergy,energy,SKGap.hamiltonian,GapBridge.edgeInteraction,spin,SKGap.spinValue,Matrix.of_apply]
    ring
  funext x
  simp only [fieldGibbs,fieldPartition,he,SKGap.mass,SKGap.partition,SKGap.weight]

end SKGapCutoff

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_NormalizedWeightedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static

lemma choose_selection_depth {ρ : ℝ} (hρ : 0<ρ) :
    ∃m:ℕ,∃ε:ℝ,0<ε ∧ 2<(m:ℝ)*ρ^2/4 ∧ 2*(2*m:ℕ)*ε≤1 := by
  obtain ⟨m,hm⟩:=exists_nat_gt (8/ρ^2)
  have hρ2 : 0<ρ^2:=sq_pos_of_pos hρ
  have hm' : 2<(m:ℝ)*ρ^2/4 := by
    have H:8<(m:ℝ)*ρ^2:=(div_lt_iff₀ hρ2).mp hm
    linarith
  refine ⟨m,1/(2*(2*m:ℕ)+1),by positivity,hm',?_⟩
  have hp : 0≤(2*(2*m:ℕ):ℝ):=by positivity
  rw [mul_one_div]
  exact (div_le_one (by positivity)).mpr (by linarith)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ProductGaussianDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace SKGap.GaussianDensity
variable {ι : Type*} [Fintype ι]

theorem pi_gaussian_density (m : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i,v i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (v i)) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : ι → ℝ => ∏ i,gaussianPDFReal (m i) (v i) (x i))
      (volume.restrict (Set.univ.pi s)) := by
    exact (Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (m i) (v i))).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  change ENNReal.ofReal (∫ x, (∏ i,gaussianPDFReal (m i) (v i) (x i))
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s))=_
  rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero _ (hv i),withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal (m i) (v i)).restrict
    (Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _))

lemma measurable_productPDF (m : ι → ℝ) (v : ι → ℝ≥0) :
    Measurable (fun x : ι → ℝ => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  fun_prop

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_LocalVolumeEnergy
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal

lemma continuous_vectorNorm (n : ℕ) : Continuous (vectorNorm (n := n)) := by
  unfold vectorNorm
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_RootBadMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {n : ℕ}
attribute [local instance] OAI.SKGap.matrixMeasurable
local instance matrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma continuous_joint_tapField (j : ℝ) :
    Continuous (fun p : (Matrix (Fin n) (Fin n) ℝ × Field n) × Field n=>tapField j p.1.1 p.1.2 p.2) := by
  unfold tapField onsager overlap magnetization
  fun_prop

lemma rootBad_iff_unplanted (j A ε c ρ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (h : Field n) :
    rootBad j A ε c ρ J h ↔ ∃ y : Field n,vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ) ∧
      (J-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c := by
  simp only [rootBad,badFieldSet,mem_ofPred_eq,plantedInteraction,sub_add_cancel]

lemma isClosed_bounded_rootBad (j A ε c ρ : ℝ) (m : ℕ) :
    IsClosed {p : Matrix (Fin n) (Fin n) ℝ × Field n | ∃ y ∈ Metric.closedBall (0 : Field n) m,
      vectorNorm (tapField j p.1 p.2 y) ≤ ρ*sqrt (n:ℝ) ∧
      (p.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c} := by
  let X := ↥(Metric.closedBall (0 : Field n) m)
  let : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Field n) m)
  let S : Set (X × (Matrix (Fin n) (Fin n) ℝ × Field n)) :=
    {p | vectorNorm (tapField j p.2.1 p.2.2 p.1) ≤ ρ*sqrt (n:ℝ) ∧
      (p.2.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),(p.1:Field n))∈badFieldSet n j A ε c}
  have hy : Continuous (fun p : X × (Matrix (Fin n) (Fin n) ℝ × Field n)=>(p.1:Field n)) :=
    continuous_subtype_val.comp continuous_fst
  have ht := (continuous_joint_tapField (n:=n) j).comp (continuous_snd.prodMk hy)
  have hS : IsClosed S := (isClosed_le ((continuous_vectorNorm n).comp ht) continuous_const).inter
    ((isClosed_badFieldSet n j A ε c).preimage
      (((continuous_fst.comp continuous_snd).sub continuous_const).prodMk hy))
  have hp := isClosedMap_snd_of_compactSpace S hS
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨y,hy,hr,hb⟩
    exact ⟨(⟨y,hy⟩,p),⟨hr,hb⟩,rfl⟩
  · rintro ⟨⟨y,p⟩,⟨hr,hb⟩,rfl⟩
    exact ⟨y,y.property,hr,hb⟩

theorem measurableSet_rootBad (j A ε c ρ : ℝ) :
    MeasurableSet {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2} := by
  have he : {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2}=
      ⋃ m : ℕ,{p : Matrix (Fin n) (Fin n) ℝ × Field n | ∃ y ∈ Metric.closedBall (0 : Field n) m,
        vectorNorm (tapField j p.1 p.2 y) ≤ ρ*sqrt (n:ℝ) ∧
        (p.1-(j/(n:ℝ)) • vecMulVec (fun _=>1) (fun _=>1),y)∈badFieldSet n j A ε c} := by
    ext p
    rw [mem_ofPred_eq,rootBad_iff_unplanted]
    constructor
    · rintro ⟨y,hr,hb⟩
      obtain ⟨m,hm⟩ := exists_nat_ge ‖y‖
      exact mem_iUnion.mpr ⟨m,y,by simpa only [Metric.mem_closedBall,dist_zero_right] using hm,hr,hb⟩
    · intro hp
      obtain ⟨m,y,_,hr,hb⟩ := mem_iUnion.mp hp
      exact ⟨y,hr,hb⟩
  rw [he]
  exact MeasurableSet.iUnion (fun m=>(isClosed_bounded_rootBad j A ε c ρ m).measurableSet)
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_GaugeStabilityLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
attribute [local instance] OAI.SKGap.ObservationBridge.matrixMeasurable
local instance matrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma isClosed_operatorBound (K : ℝ) : IsClosed {J : Matrix (Fin n) (Fin n) ℝ | operatorBound K J} := by
  have he : {J : Matrix (Fin n) (Fin n) ℝ | operatorBound K J} =
      ⋂ z : Field n,{J | vectorNorm (J*ᵥz) ≤ K*vectorNorm z} := by ext J; simp [operatorBound]
  rw [he]
  apply isClosed_iInter
  intro z
  exact isClosed_le ((continuous_vectorNorm n).comp (by unfold Matrix.mulVec; fun_prop)) continuous_const

lemma measurableSet_literalBadPair (j A K ε c ρ : ℝ) :
    MeasurableSet (literalBadPair (n:=n) j A K ε c ρ) :=
  ((isClosed_operatorBound K).measurableSet.preimage measurable_fst).inter
    (measurableSet_rootBad j A ε c ρ)

lemma continuous_coupling : Continuous (coupling (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  unfold coupling
  split_ifs <;> fun_prop

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DisorderRecipeEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section
open scoped BigOperators Topology
namespace SKGapCutoff.Recipe
open SKGap SKGap.ObservationBridge SKGap.Noncrossing SKGap.Noncrossing.Primary
open MeasureTheory ProbabilityTheory Real Set Filter

theorem disorder_fixed_norm_recipe_probability {β A : ℝ} (hβ : 0<β) (hβ1 : β<1)
    (hA : 1≤A) (M Nmax : ℕ) : ∃B W C : ℝ,0≤B ∧ 0≤W ∧ 0<C ∧
      Tendsto (fun n=>SKGap.disorderLaw β n
        {g | ¬RecipeMatrixEvent (β^2) (physicalNormBound (β^2)) A B W C M Nmax
          (coupling g)}) atTop (𝓝 0) := by
  let j:=β^2
  have hj : 0<j:=sq_pos_of_pos hβ
  let R:=max A (physicalNormBound j)
  have hAR : A≤R:=le_max_left _ _
  have hR : 1≤R:=hA.trans hAR
  obtain ⟨C,N,hC,hN,hword⟩:=disorder_word_event hβ hβ1 hA (2*M+2*Nmax+3)
  refine ⟨primaryEventBudget j R C M,R^(2*Nmax+3)+C,C,
    primaryEventBudget_nonneg (by linarith) hC.le M,
    add_nonneg (pow_nonneg (by linarith) _) hC.le,hC,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun n=>recipeNormTail j n+ordinaryWordTail j (2*M+2*Nmax+3) n) atTop (𝓝 0) from
      by simpa using (recipeNormTail_limit hj).add (ordinaryWordTail_limit hj _))
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn0 : 0<n:=hN.trans_le hn
  let E:Set (Disorder n):={g | physicalNormBound j<SKGap.opNorm (coupling g)}
  let F:Set (Disorder n):={g | ¬WordSeminormBound (coupling g) j A C (2*M+2*Nmax+3)}
  have hE : SKGap.disorderLaw β n E ≤ recipeNormTail j n:=disorder_norm_event hβ hn0
  have hF : SKGap.disorderLaw β n F≤ordinaryWordTail j (2*M+2*Nmax+3) n:=hword n hn
  apply (measure_mono (t:=E∪F) ?_).trans ((measure_union_le _ _).trans (add_le_add hE hF))
  intro g hg
  by_contra hh
  have hp : SKGap.opNorm (coupling g)≤physicalNormBound j:=le_of_not_gt (fun hbad=>hh (.inl hbad))
  have hw : WordSeminormBound (coupling g) j A C (2*M+2*Nmax+3):=by
    by_contra hbad;exact hh (.inr hbad)
  have hev:=wordEvent_recipeEvent (coupling g) hn0 hR hA hAR hC.le
    (hp.trans (le_max_right _ _)) M Nmax hw
  exact hg ⟨hp,hev.2⟩

end SKGapCutoff.Recipe

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_StableRootInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

lemma stable_hessian_coercive {n : ℕ} {j A ε c ρ : ℝ}
    {J : Matrix (Fin n) (Fin n) ℝ} {h y a : Field n}
    (hbad : ¬rootBad j A ε c ρ J h)
    (hy : vectorNorm (tapField j J h y) ≤ ρ*sqrt (n:ℝ))
    (ha : ∀ i,a i∈Icc 0 A) (hd : (∑ i,(a i-spinVariance y i)^2)≤ε^2*(n:ℝ)) :
    ∀ v : Field n,c*vectorSqNorm v ≤ quadraticForm (fieldHessian j J y a) v := by
  intro v
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  let H := fieldHessian j J y a
  have hunit : ∀ z : EuclideanSpace ℝ (Fin n),‖z‖=1 → c < matrixQuad H z := by
    intro z hz
    exact lt_of_not_ge (fun hh=>hbad ⟨y,hy,a,ha,hd,z,hz,hh⟩)
  by_cases hx : x=0
  · have hv : v=0 := congrArg WithLp.ofLp hx
    simp [hv,vectorSqNorm,quadraticForm]
  · have hx0 : 0<‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖(‖x‖⁻¹:ℝ) • x‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hx0),inv_mul_cancel₀ hx0.ne']
    have hh := (hunit (‖x‖⁻¹ • x) hu).le
    rw [matrixQuad_smul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖x‖)
    have he : ‖x‖^2*((‖x‖⁻¹)^2*matrixQuad H x)=matrixQuad H x := by
      field_simp
    rw [he] at hmul
    have hn : ‖x‖^2=vectorSqNorm v := vectorNorm_sq v
    rw [hn,mul_comm] at hmul
    exact hmul

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_DisorderWeightedMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Topology Matrix
open Filter MeasureTheory ProbabilityTheory Real
namespace SKGapCutoff.Recipe
open SKGap SKGap.ObservationBridge SKGap.Noncrossing SKGap.Noncrossing.Primary Primary Static

theorem disorder_stable_square_mean {β c r₀ : ℝ} (hβ : 0<β) (hβ1 : β<1)
    (hc : 0 < c) (hr₀ : 0 < r₀) :
    ∀ρ:ℝ,0<ρ→(physicalNormBound (β^2)+4*β^2)*ρ < r₀→
    ∃A:ℝ,0≤A ∧
      Tendsto (fun n=>SKGap.disorderLaw β n
        {g | ¬StableSquareMeanProperty (β^2) c r₀ ρ
          ((1+(physicalNormBound (β^2)+3*β^2)/c)*(physicalNormBound (β^2)+4*β^2)) A
          (coupling g)}) atTop (𝓝 0) := by
  intro ρ hρ hbuffer
  obtain ⟨m,ε,hε,hm,he⟩:=choose_selection_depth hρ
  have hbudget : 1 ≤ residualCoefficientBudget (β^2) 2 (2*m) 0 :=
    (by norm_num : (1:ℝ)≤2).trans (residualCoefficientBudget_ge (β^2) (by norm_num) (2*m) 0)
  obtain ⟨B,W,C,hB,hW,hC,hprob⟩:=disorder_fixed_norm_recipe_probability hβ hβ1 hbudget
    (2*m+1) (2*(2*m))
  obtain ⟨A,hA,hAall⟩:=uniform_stable_square_mean m (sq_nonneg β)
    (physicalNormBound_pos (β^2)).le hc hr₀ hρ hε hbuffer hm he hB hW hC.le
  refine ⟨A,hA,?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprob
    (Filter.Eventually.of_forall (fun _=>bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply measure_mono
  intro g hg
  by_contra hnot
  have hev : RecipeMatrixEvent (β^2) (physicalNormBound (β^2))
      (residualCoefficientBudget (β^2) 2 (2*m) 0) B W C (2*m+1) (2*(2*m))
      (coupling g) := by simpa using hnot
  apply hg
  intro h hst
  apply hAall (by omega) _ h _ _ hev hst
  · ext i k
    exact coupling_symm g k i
  · exact coupling_diag g

lemma stableSquareMeanProperty_rootBad {n : ℕ} {j A₀ ε c r₀ ρ C₀ C : ℝ}
    (hA₀ : 1≤A₀) (J : Interaction n)
    (H : StableSquareMeanProperty j c r₀ ρ C₀ C J) (h : Fin n→ℝ)
    (hbad : ¬rootBad j A₀ ε c r₀ J h) :
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀f:Observables n,0<(∑x,fieldGibbs J h x*(f x)^2)→
      vectorNorm (squareMean (fieldGibbs J h) f-SKGap.magnetization r)/Real.sqrt (n:ℝ)≤
        C₀*ρ+C/Real.sqrt (n:ℝ)*
          (1+varianceEnergy (fieldGibbs J h) f/(∑x,fieldGibbs J h x*(f x)^2)) := by
  apply H h
  intro y hy
  apply stable_hessian_coercive hbad hy
  · intro i
    exact ⟨(spinVariance_pos y i).le,(spinVariance_le_one y i).trans hA₀⟩
  · simp only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    positivity

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_AffineUpper
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.DiscreteRecurrence
open Real

lemma affine_upper (u : ℕ→ℝ) {b r : ℝ} (hb : 0≤b) (hr : 0 ≤ r)
    (hzero : u 0≤0) (K : ℕ)
    (hstep : ∀k<K,u (k+1)≤(1+b)*u k+r) :
    u K≤(K:ℝ)*r*exp ((K:ℝ)*b) := by
  have hh : ∀ k≤K,u k≤(k:ℝ)*r*(1+b)^k := by
    intro k hk
    induction k with
    | zero => simpa using hzero
    | succ k ih =>
      have hi:=mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le hk)) (by linarith : 0≤1+b)
      have hp : 1≤(1+b)^(k+1) := one_le_pow₀ (by linarith)
      have hrp:=mul_le_mul_of_nonneg_left hp hr
      have hs:=hstep k (Nat.lt_of_succ_le hk)
      simp only [Nat.cast_add,Nat.cast_one,pow_succ] at hrp ⊢
      nlinarith
  have hp:=pow_le_pow_left₀ (by linarith : 0≤1+b) (by simpa only [add_comm] using Real.add_one_le_exp b) K
  have hm:=mul_le_mul_of_nonneg_left hp (show 0≤(K:ℝ)*r by positivity)
  rw [←Real.exp_nat_mul] at hm
  simpa only [mul_comm b] using (hh K le_rfl).trans hm

lemma affine_lower (u : ℕ→ℝ) {r b : ℝ} (hr : 0 ≤ r) (hr1 : r≤1) (hb : 0≤b)
    (K : ℕ) (hstep : ∀k<K,r*u k-b≤u (k+1)) :
    r^K*u 0-(K:ℝ)*b≤u K := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hi:=mul_le_mul_of_nonneg_left (ih (fun k hk => hstep k (hk.trans (Nat.lt_succ_self K)))) hr
    have hs:=hstep K (Nat.lt_succ_self K)
    have hb':=mul_le_mul_of_nonneg_right hr1 (show 0≤(K:ℝ)*b by positivity)
    rw [Nat.cast_add,Nat.cast_one,pow_succ]
    nlinarith

lemma exp_neg_two_le {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) :
    exp (-2*x)≤1-x := by
  have hpos : 0<1-x := by linarith
  have hi : (1-x)⁻¹≤1+2*x := by
    rw [inv_eq_one_div,div_le_iff₀ hpos]
    nlinarith
  have hl:=Real.one_sub_inv_le_log_of_pos hpos
  have hh : -2*x≤log (1-x) := by linarith
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hh

lemma pow_one_sub_lower {x : ℝ} (hx : 0≤x) (hx1 : x≤1/2) (K : ℕ) :
    exp (-2*(K:ℝ)*x)≤(1-x)^K := by
  have hh:=pow_le_pow_left₀ (exp_pos (-2*x)).le (exp_neg_two_le hx hx1) K
  rw [←Real.exp_nat_mul] at hh
  have he : (K:ℝ)*(-2*x)= -2*(K:ℝ)*x := by ring
  rwa [he] at hh

end SKGap.DiscreteRecurrence

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_DriftSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma driftSquare_nonneg (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    0≤driftSquare p q t h := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma driftSquare_le (p q : Prior n) (t : ℝ) {k : ℕ} (h : History n k) :
    driftSquare p q t h≤4*(n:ℝ) := mean_difference_square_le _ _

lemma continuous_driftSquare (p q : Prior n) (t : ℝ) (k : ℕ) :
    Continuous (driftSquare p q t (k := k)) := by
  unfold driftSquare mean
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_finsetSum _ (fun x _ => (continuous_posterior_mass q t k x).mul_const _)).sub
      (continuous_finsetSum _ (fun x _ => (continuous_posterior_mass p t k x).mul_const _))).pow 2)

lemma integrable_driftSquare_weight (p q : Prior n) (t : ℝ) (k : ℕ) :
    Integrable (fun h : History n k => density q t h*driftSquare p q t h) (reference n k) := by
  apply ((integrable_density q t k).mul_const (4*(n:ℝ))).mono'
    ((continuous_density q t k).mul (continuous_driftSquare p q t k)).aestronglyMeasurable
  filter_upwards [] with h
  change |density q t h*driftSquare p q t h|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos q t h).le (driftSquare_nonneg _ _ _ _))]
  exact mul_le_mul_of_nonneg_left (driftSquare_le p q t h) (density_pos q t h).le

lemma integrable_entropy_increment (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    Integrable (fun h : History n k => density q t h*
      (∫z,GaussianStep.divergenceIntegrand (posterior p t h) (posterior q t h) t z
        ∂GaussianStep.reference n)) (reference n k) := by
  let L : History n k → ℝ := fun h => log (density q t h/density p t h)
  have hL : Measurable L := (continuous_log_ratio p q t k).measurable
  have hiL : Integrable (fun h => density q t h*L h) (reference n k) :=
    integrable_relativeEntropyIntegrand p q hp t k
  have hLift := integrable_lift q ht L hL hiL
  have hi := (integrable_relativeEntropyIntegrand p q hp t (k+1)).sub hLift
  have he : (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-density q t hz*L hz.1) =
      fun hz => density q t hz.1*(GaussianStep.density (posterior q t hz.1) t hz.2*
        log (GaussianStep.density (posterior q t hz.1) t hz.2/GaussianStep.density (posterior p t hz.1) t hz.2)) := by
    funext ⟨h,z⟩
    rw [relativeEntropy_succ]
    dsimp [L]
    ring
  change Integrable (fun hz : History n (k+1) => relativeEntropyIntegrand p q t hz-
    density q t hz*L hz.1) ((reference n k).prod (GaussianStep.reference n)) at hi
  rw [he] at hi
  have hh := hi.integral_prod_left
  simp_rw [integral_const_mul,GaussianStep.integral_relativeEntropy _ _ ht] at hh
  exact hh

lemma entropy_step_history_bound (p q : Prior n) (hp : ∀x,0<p x) {t : ℝ} (ht : 0≤t)
    (htn : 4*(n:ℝ)*t≤1) (k : ℕ) :
    entropy p q t (k+1)≤entropy p q t k+
      t*(∫h:History n k,density q t h*driftSquare p q t h ∂reference n k)+64*(n:ℝ)^2*t^2 := by
  rw [entropy_succ p q hp ht]
  have hh := integral_mono (integrable_entropy_increment p q hp ht k)
    (((integrable_driftSquare_weight p q t k).const_mul t).add
      ((integrable_density q t k).mul_const (64*(n:ℝ)^2*t^2)))
      (fun h => (mul_le_mul_of_nonneg_left
        (GaussianStep.entropy_step_bound (posterior p t h) (posterior q t h) ht htn)
        (density_pos q t h).le).trans_eq (by dsimp [driftSquare]; ring))
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_driftSquare_weight p q t k).const_mul t)
      ((integrable_density q t k).mul_const (64*(n:ℝ)^2*t^2)),integral_const_mul,
      integral_mul_const,integral_density q ht,one_mul] at hh
  linarith

lemma drift_integral_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (k : ℕ)
    (B : Set (History n k)) (hB : MeasurableSet B) (W A : ℝ) (hW : 0≤W) (hA : 0≤A)
    (hgood : ∀h:History n k,h∉B → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    (∫h:History n k,density (squarePrior p f hf) t h*driftSquare p (squarePrior p f hf) t h ∂reference n k) ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+
        4*(n:ℝ)*eventProbability (squarePrior p f hf) t B := by
  let q:=squarePrior p f hf
  let N:=avg p (fun x => (f x)^2)
  let d : History n k→ℝ := fun h => density p t h*energy (posterior p t h) f
  have hiD : Integrable d (reference n k) := integrable_posterior_energy_weight p hp t k f
  have hiQ := integrable_density q t k
  have hiB := hiQ.indicator hB
  have hpoint (h : History n k) : density q t h*driftSquare p q t h ≤
      (W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+
        (A*sqrt (n:ℝ)/N)*d h+4*(n:ℝ)*B.indicator (density q t) h := by
    have he := weighted_energy_identity p f hf t h
    change density q t h*(energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)) = d h/N at he
    have hd0 : 0≤d h := mul_nonneg (density_pos p t h).le (energy_nonneg _ _)
    have hconst : 0≤(W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h :=
      mul_nonneg (by positivity) (density_pos q t h).le
    have hdpos : 0≤(A*sqrt (n:ℝ)/N)*d h := mul_nonneg (div_nonneg (mul_nonneg hA (sqrt_nonneg _)) hf.le) hd0
    by_cases hb : h∈B
    · rw [Set.indicator_of_mem hb]
      have hh:=mul_le_mul_of_nonneg_left (driftSquare_le p q t h) (density_pos q t h).le
      nlinarith
    · rw [Set.indicator_of_notMem hb,mul_zero,add_zero]
      have hh:=mul_le_mul_of_nonneg_left (hgood h hb) (density_pos q t h).le
      calc
        _≤density q t h*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) := hh
        _=(W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+A*sqrt (n:ℝ)*
            (density q t h*(energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) := by ring
        _=_ := by rw [he]; ring
  have hi1 := hiQ.const_mul (W*(n:ℝ)+2*A*sqrt (n:ℝ))
  have hi2 := hiD.const_mul (A*sqrt (n:ℝ)/N)
  have hi3 := hiB.const_mul (4*(n:ℝ))
  have hi12 : Integrable (fun h => (W*(n:ℝ)+2*A*sqrt (n:ℝ))*density q t h+
      (A*sqrt (n:ℝ)/N)*d h) (reference n k) := hi1.add hi2
  have hh := integral_mono (integrable_driftSquare_weight p q t k) (hi12.add hi3) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hi12 hi3,integral_add hi1 hi2,integral_const_mul,
    integral_const_mul,integral_const_mul,integral_density q ht,integral_indicator hB,mul_one] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f)
    (show 0≤A*sqrt (n:ℝ)/N from div_nonneg (mul_nonneg hA (sqrt_nonneg _)) hf.le)
  change _≤(W*(n:ℝ)+2*A*sqrt (n:ℝ))+(A*sqrt (n:ℝ)/N)*(∫h,d h ∂reference n k)+
    4*(n:ℝ)*eventProbability q t B at hh
  change (A*sqrt (n:ℝ)/N)*(∫h,d h ∂reference n k)≤(A*sqrt (n:ℝ)/N)*energy p f at hd
  dsimp [N,q] at hh hd
  simp only [div_eq_mul_inv] at hh hd ⊢
  nlinarith

theorem entropy_good_step (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (k : ℕ)
    (B : Set (History n k)) (hB : MeasurableSet B) (W A a : ℝ)
    (hW : 0≤W) (hA : 0≤A) (ha : 0<a)
    (hsmall : eventProbability p t B≤exp (-a*(n:ℝ)))
    (hgood : ∀h:History n k,h∉B → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    entropy p (squarePrior p f hf) t (k+1)≤
      (1+4*t/a)*entropy p (squarePrior p f hf) t k+
        t*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*t^2 := by
  have hs:=entropy_step_history_bound p (squarePrior p f hf) hp ht htn k
  have hd:=mul_le_mul_of_nonneg_left (drift_integral_bound p hp f hf ht k B hB W A hW hA hgood) ht
  have he:=entropy_event_bound p (squarePrior p f hf) hp ht k B hB (a*(n:ℝ))
    (by simpa only [neg_mul] using hsmall)
  have he':=mul_le_mul_of_nonneg_left he (show 0≤4*t/a by positivity)
  have heq : (4*t/a)*(a*(n:ℝ)*eventProbability (squarePrior p f hf) t B)=
      t*(4*(n:ℝ)*eventProbability (squarePrior p f hf) t B) := by field_simp
  rw [heq] at he'
  simp only [div_eq_mul_inv] at hs hd he' ⊢
  nlinarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_Envelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma envelope_nonneg (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) : 0≤envelope p t A f h := by
  unfold envelope
  split_ifs
  · exact var_nonneg _ _
  · exact avg_nonneg _ _ (fun _ => sq_nonneg _)

lemma var_le_envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) : var (posterior p t h) f≤envelope p t A f h := by
  unfold envelope
  split_ifs
  · rfl
  · exact var_le_square _ _

lemma envelope_le_square (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (f : Spin n→ℝ) (h : History n k) :
    envelope p t A f h≤avg (posterior p t h) (fun x => (f x)^2) := by
  unfold envelope
  split_ifs
  · exact var_le_square _ _
  · rfl

lemma measurable_envelope (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (hA : MeasurableSet A) (f : Spin n→ℝ) : Measurable (envelope p t A f) :=
  Measurable.ite hA (continuous_posterior_var p t k f).measurable
    (continuous_posterior_avg p t k _).measurable

lemma integrable_envelope_weight (p : Prior n) (t : ℝ) {k : ℕ} (A : Set (History n k))
    (hA : MeasurableSet A) (f : Spin n→ℝ) :
    Integrable (fun h => density p t h*envelope p t A f h) (reference n k) := by
  apply (integrable_posterior_avg_weight p t (fun x => (f x)^2) k).mono'
    (((continuous_density p t k).measurable.mul (measurable_envelope p t A hA f)).aestronglyMeasurable)
  filter_upwards [] with h
  change |density p t h*envelope p t A f h|≤_
  rw [abs_of_nonneg (mul_nonneg (density_pos p t h).le (envelope_nonneg p t A f h))]
  exact mul_le_mul_of_nonneg_left (envelope_le_square p t A f h) (density_pos p t h).le

lemma variance_le_envelope_zero (p : Prior n) (t : ℝ) (A : Set (History n 0)) (f : Spin n→ℝ) :
    var p f≤envelopeIntegral p t A f := by
  unfold envelopeIntegral reference
  rw [integral_dirac,density_zero,one_mul]
  have hh:=var_le_envelope p t A f ()
  rw [posterior_zero] at hh
  exact hh

lemma integrable_envelope_section (p : Prior n) (t : ℝ) {k : ℕ} (G : Set (History n (k+1)))
    (hG : MeasurableSet G) (f : Spin n→ℝ) (h : History n k) :
    Integrable (fun z => GaussianStep.density (posterior p t h) t z *
      envelope p t G f (h,z)) (GaussianStep.reference n) := by
  have hm : Measurable (fun z => envelope p t G f (h,z)) :=
    (measurable_envelope p t G hG f).comp (measurable_const.prodMk measurable_id)
  have hn : Integrable (fun z => GaussianStep.density (posterior p t h) t z*
      avg (posterior p t (k := k+1) (h,z)) (fun x => (f x)^2)) (GaussianStep.reference n) := by
    simp_rw [posterior_succ]
    exact GaussianStep.integrable_posterior_avg_weight _ t _
  apply hn.mono' (((GaussianStep.continuous_density (posterior p t h) t).measurable.mul hm).aestronglyMeasurable)
  filter_upwards [] with z
  change |GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)|≤_
  rw [abs_of_nonneg (mul_nonneg (GaussianStep.density_pos _ _ _).le (envelope_nonneg _ _ _ _ _))]
  exact mul_le_mul_of_nonneg_left (envelope_le_square p t G f (h,z)) (GaussianStep.density_pos _ _ _).le

lemma envelope_step_point (p : Prior n) (t : ℝ) {k : ℕ}
    (A : Set (History n k)) (G : Set (History n (k+1))) (hG : MeasurableSet G)
    (hprefix : ∀h:History n (k+1),h∈G→h.1∈A) (f : Spin n→ℝ)
    (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (D : ℝ) (hD : 0≤D)
    (hgood : ∀h:History n k,h∈A→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (h : History n k) :
    (1-D*t)*envelope p t A f h-D*t*energy (posterior p t h) f-
        16*(n:ℝ)^2*t^2*avg (posterior p t h) (fun x => (f x)^2) ≤
      ∫z,GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)
        ∂GaussianStep.reference n := by
  by_cases hh : h∈A
  · have hv : (∫z,GaussianStep.density (posterior p t h) t z*
        var (GaussianStep.posterior (posterior p t h) t z) f ∂GaussianStep.reference n) ≤
        ∫z,GaussianStep.density (posterior p t h) t z*envelope p t G f (h,z)
          ∂GaussianStep.reference n := by
      apply integral_mono (GaussianStep.integrable_posterior_variance_weight _ t f)
        (integrable_envelope_section p t G hG f h)
      intro z
      have he:=var_le_envelope p t G f (h,z)
      rw [posterior_succ] at he
      exact mul_le_mul_of_nonneg_left he (GaussianStep.density_pos _ _ _).le
    have hs:=GaussianStep.variance_step_bound (posterior p t h) ht htn f
    have hc:=mul_le_mul_of_nonneg_left (hgood h hh) ht
    have hn:=mul_le_mul_of_nonneg_left (var_le_square (posterior p t h) f)
      (show 0≤16*(n:ℝ)^2*t^2 by positivity)
    rw [envelope,ite_eq_left hh]
    nlinarith
  · have he (z : Fin n→ℝ) : envelope p t G f (h,z)=
        avg (GaussianStep.posterior (posterior p t h) t z) (fun x => (f x)^2) := by
      rw [envelope,ite_eq_right (fun hmem => hh (hprefix (h,z) hmem)),posterior_succ]
    simp_rw [he]
    rw [GaussianStep.integral_posterior_avg_weight _ ht,envelope,ite_eq_right hh]
    have hN : 0≤avg (posterior p t h) (fun x => (f x)^2) := avg_nonneg _ _ (fun _ => sq_nonneg _)
    have hE:=energy_nonneg (posterior p t h) f
    have hdt : 0≤D*t := mul_nonneg hD ht
    have herr : 0≤16*(n:ℝ)^2*t^2 := by positivity
    nlinarith [mul_nonneg hdt hN,mul_nonneg hdt hE,mul_nonneg herr hN]

theorem envelope_step_bound (p : Prior n) (hp : ∀x,0<p x) {t : ℝ} {k : ℕ}
    (A : Set (History n k)) (hA : MeasurableSet A)
    (G : Set (History n (k+1))) (hG : MeasurableSet G)
    (hprefix : ∀h:History n (k+1),h∈G→h.1∈A) (f : Spin n→ℝ)
    (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (D : ℝ) (hD : 0≤D)
    (hgood : ∀h:History n k,h∈A→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f)) :
    (1-D*t)*envelopeIntegral p t A f-D*t*energy p f-
        16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2) ≤ envelopeIntegral p t G f := by
  have hi:=integrable_envelope_weight p t G hG f
  change Integrable (fun hz : History n k × (Fin n→ℝ) => density p t (k := k+1) hz*envelope p t G f hz)
    ((reference n k).prod (GaussianStep.reference n)) at hi
  have hiR:=hi.integral_prod_left
  have he : (∫h:History n k,∫z,density p t (k := k+1) (h,z)*envelope p t G f (h,z)
      ∂GaussianStep.reference n ∂reference n k)=envelopeIntegral p t G f :=
    (integral_prod _ hi).symm
  have hi1:=(integrable_envelope_weight p t A hA f).const_mul (1-D*t)
  have hi2:=(integrable_posterior_energy_weight p hp t k f).const_mul (D*t)
  have hi3:=(integrable_posterior_avg_weight p t (fun x => (f x)^2) k).const_mul (16*(n:ℝ)^2*t^2)
  have hi12 : Integrable (fun h => (1-D*t)*(density p t h*envelope p t A f h)-
      D*t*(density p t h*energy (posterior p t h) f)) (reference n k) := hi1.sub hi2
  have hh:=integral_mono (hi12.sub hi3) hiR (fun h => ?_)
  swap
  · simp only [Pi.sub_apply]
    simp_rw [density_succ,mul_assoc]
    rw [integral_const_mul]
    convert mul_le_mul_of_nonneg_left (envelope_step_point p t A G hG hprefix f ht htn D hD hgood h)
      (density_pos p t h).le using 1; ring
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hi12 hi3,integral_sub hi1 hi2,integral_const_mul,
    integral_const_mul,integral_const_mul,integral_posterior_avg_weight p ht,he] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f) (mul_nonneg hD ht)
  change (1-D*t)*envelopeIntegral p t A f-D*t*(∫h,density p t h*energy (posterior p t h) f ∂reference n k)-
    16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2)≤envelopeIntegral p t G f at hh
  linarith

theorem envelope_terminal_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) {k : ℕ}
    (A E : Set (History n k)) (hA : MeasurableSet A) (hE : MeasurableSet E)
    (hprefix : Aᶜ⊆E) (L : ℝ) (hL : 0≤L)
    (hterminal : ∀h:History n k,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    envelopeIntegral p t A f≤ L*energy p f+
      avg p (fun x => (f x)^2)*eventProbability (squarePrior p f hf) t E := by
  let N:=avg p (fun x => (f x)^2)
  have hi1:=(integrable_posterior_energy_weight p hp t k f).const_mul L
  have hi2:=((integrable_density (squarePrior p f hf) t k).indicator hE).const_mul N
  have hh:=integral_mono (integrable_envelope_weight p t A hA f) (hi1.add hi2) (fun h => ?_)
  swap
  · simp only [Pi.add_apply]
    by_cases he : h∈E
    · rw [Set.indicator_of_mem he,squarePrior_density]
      have henv:=mul_le_mul_of_nonneg_left (envelope_le_square p t A f h) (density_pos p t h).le
      have hden : N*(density p t h*avg (posterior p t h) (fun x => (f x)^2)/N)=
          density p t h*avg (posterior p t h) (fun x => (f x)^2) := mul_div_cancel₀ _ hf.ne'
      change _≤L*(density p t h*energy (posterior p t h) f)+N*(_/N)
      rw [hden]
      exact henv.trans (le_add_of_nonneg_left (mul_nonneg hL
        (mul_nonneg (density_pos p t h).le (energy_nonneg _ _))))
    · have ha : h∈A := by by_contra hn; exact he (hprefix hn)
      simp only [Set.indicator_of_notMem he,mul_zero,add_zero,envelope,ite_eq_left ha]
      simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hterminal h he) (density_pos p t h).le
  simp only [Pi.add_apply] at hh
  rw [integral_add hi1 hi2,integral_const_mul,integral_const_mul,integral_indicator hE] at hh
  have hd:=mul_le_mul_of_nonneg_left (energy_history_bound p hp ht k f) hL
  change envelopeIntegral p t A f≤L*(∫h,density p t h*energy (posterior p t h) f ∂reference n k)+
    N*eventProbability (squarePrior p f hf) t E at hh
  dsimp [N] at hh
  linarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_EntropyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep DiscreteRecurrence
noncomputable section
variable {n : ℕ}

lemma entropy_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B : ∀k,Set (History n k)) (hB : ∀k,MeasurableSet (B k))
    (W A a T : ℝ) (hW : 0≤W) (hA : 0≤A) (ha : 0<a) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hgood : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2))) :
    entropy p (squarePrior p f hf) t K≤
      exp (4*T/a)*(T*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*T*t) := by
  have hh:=affine_upper (entropy p (squarePrior p f hf) t)
    (show 0≤4*t/a by positivity)
    (show 0≤t*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
        64*(n:ℝ)^2*t^2 by have := energy_nonneg p f; positivity)
    (entropy_zero p (squarePrior p f hf) t).le K
    (fun k hk => by
      simpa only [add_assoc] using entropy_good_step p hp f hf ht htn k (B k) (hB k) W A a hW hA ha
        (hsmall k hk) (hgood k hk))
  have he : (K:ℝ)*(4*t/a)=4*T/a := by rw [←hT]; ring
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [←hT]
  ring

lemma envelope_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1) (K : ℕ)
    (G : ∀k,Set (History n k)) (hG : ∀k,MeasurableSet (G k))
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (D T : ℝ) (hD : 0≤D) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hgood : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f)) :
    exp (-2*D*T)*var p f≤ envelopeIntegral p t (G K) f+D*T*energy p f+
      16*(n:ℝ)^2*T*t*avg p (fun x => (f x)^2) := by
  have hh:=affine_lower (fun k => envelopeIntegral p t (G k) f)
    (show 0≤1-D*t by linarith) (show 1-D*t≤1 by nlinarith)
    (show 0≤D*t*energy p f+16*(n:ℝ)^2*t^2*avg p (fun x => (f x)^2) by
      have := energy_nonneg p f
      have := avg_nonneg p (fun x => (f x)^2) (fun _ => sq_nonneg _)
      positivity) K (fun k hk => by
        have hs:=envelope_step_bound p hp (G k) (hG k) (G (k+1)) (hG (k+1))
          (hprefix k hk) f ht htn D hD (hgood k hk)
        linarith)
  have hz:=mul_le_mul_of_nonneg_left (variance_le_envelope_zero p t (G 0) f)
    (pow_nonneg (show 0≤1-D*t by linarith) K)
  have he:=mul_le_mul_of_nonneg_right (pow_one_sub_lower (mul_nonneg hD ht) hDt K) (var_nonneg p f)
  have heq : -2*(K:ℝ)*(D*t)= -2*D*T := by rw [←hT]; ring
  rw [heq] at he
  rw [←hT]
  rw [←hT] at he
  nlinarith

theorem localization_bound (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ)
    (hf : 0<avg p (fun x => (f x)^2)) {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    b*(n:ℝ)*exp (-2*D*T)*var p f ≤
      b*(n:ℝ)*((D*T+L)*energy p f+16*(n:ℝ)^2*T*t*avg p (fun x => (f x)^2))+
      avg p (fun x => (f x)^2)*(exp (4*T/a)*(T*(W*(n:ℝ)+
        A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+64*(n:ℝ)^2*T*t)+1) := by
  have hv:=envelope_bound p hp f ht htn K G hG hprefix D T hD hDt hT hcov
  have hterm:=envelope_terminal_bound p hp f hf ht (G K) E (hG K) hE hGE L hL hterminal
  have hentropy:=entropy_bound p hp f hf ht htn K B hB W A a T hW hA ha hT hsmall hmean
  have he:=entropy_event_bound p (squarePrior p f hf) hp ht K E hE (b*(n:ℝ))
    (by simpa only [neg_mul] using hEsmall)
  have heN:=mul_le_mul_of_nonneg_left he hf.le
  have hvb:=mul_le_mul_of_nonneg_left hv (show 0≤b*(n:ℝ) by positivity)
  have htb:=mul_le_mul_of_nonneg_left hterm (show 0≤b*(n:ℝ) by positivity)
  have hHN:=mul_le_mul_of_nonneg_left hentropy hf.le
  nlinarith

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma pi_gaussian_add (m₁ m₂ : Fin n → ℝ) (v₁ v₂ : ℝ≥0) :
    ((Measure.pi fun i => gaussianReal (m₁ i) v₁).prod
      (Measure.pi fun i => gaussianReal (m₂ i) v₂)).map
        (fun z : (Fin n → ℝ) × (Fin n → ℝ) => fun i => z.1 i+z.2 i) =
      Measure.pi (fun i => gaussianReal (m₁ i+m₂ i) (v₁+v₂)) := by
  rw [← (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun i => gaussianReal (m₁ i) v₁) (fun i => gaussianReal (m₂ i) v₂)).map_eq]
  rw [Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  change (Measure.pi (fun i => (gaussianReal (m₁ i) v₁).prod (gaussianReal (m₂ i) v₂))).map
    (fun z i => (z i).1+(z i).2) = _
  rw [Measure.pi_map_pi (f := fun _ (z : ℝ × ℝ) => z.1+z.2) (fun _ => by fun_prop)]
  congr 1
  funext i
  exact gaussianReal_conv_gaussianReal

lemma continuous_field (t : ℝ) : ∀k,Continuous (field (n := n) t (k := k))
  | 0 => continuous_const
  | k+1 => (continuous_field t k).comp continuous_fst |>.add
      (by fun_prop)

lemma map_scaled_reference {t : ℝ} (ht : 0≤t) :
    (GaussianStep.reference n).map (fun z : Fin n→ℝ => fun i => sqrt t*z i) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 (toNNReal t)) := by
  unfold GaussianStep.reference
  rw [Measure.pi_map_pi (fun _ => by fun_prop)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [sq_sqrt ht,ht]

lemma map_field_reference {t : ℝ} (ht : 0≤t) : ∀k,
    (reference n k).map (field t (k := k)) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 (toNNReal ((k:ℝ)*t)))
  | 0 => by
    simp only [reference,field,Nat.cast_zero,zero_mul,toNNReal_zero,gaussianReal_zero_var]
    rw [Measure.map_dirac' (by fun_prop) ()]
    apply (Measure.pi_eq (μ := fun _ : Fin n => Measure.dirac (0:ℝ)) (μ' := Measure.dirac (0:Fin n→ℝ)) ?_).symm
    intro s hs
    by_cases hx : ∀i:Fin n,(0:ℝ)∈s i
    · rw [Measure.dirac_apply_of_mem (by simpa only [mem_univ_pi,Pi.zero_apply] using hx)]
      symm
      exact Finset.prod_eq_one (fun i _ => Measure.dirac_apply_of_mem (hx i))
    · push Not at hx
      obtain ⟨i,hi⟩ := hx
      rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
        Set.indicator_of_notMem (by simp only [mem_univ_pi,Pi.zero_apply]; exact not_forall.mpr ⟨i,hi⟩)]
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [Measure.dirac_apply' _ (hs i),Set.indicator_of_notMem hi])
  | k+1 => by
    change ((reference n k).prod (GaussianStep.reference n)).map
      ((fun z : (Fin n→ℝ) × (Fin n→ℝ) => fun i => z.1 i+z.2 i) ∘
        Prod.map (field t) (fun z : Fin n→ℝ => fun i => sqrt t*z i)) = _
    rw [← Measure.map_map (by fun_prop) ((continuous_field t k).measurable.prodMap (by fun_prop)), ← Measure.map_prod_map
      (reference n k) (GaussianStep.reference n)
      (continuous_field t k).measurable (by fun_prop),
      map_field_reference ht k,map_scaled_reference ht,pi_gaussian_add]
    congr 1
    funext i
    simp only [zero_add]
    congr 1
    rw [←toNNReal_add (mul_nonneg (by positivity) ht) ht]
    congr 1
    push_cast
    ring

lemma likelihood_field (t : ℝ) (x : Spin n) : ∀{k : ℕ} (h : History n k),
    likelihood t x h = exp ((∑i,spinValue (x i)*field t h i)-(k:ℝ)*t*(n:ℝ)/2)
  | 0, _ => by simp [likelihood,field]
  | k+1, h => by
    rw [likelihood,likelihood_field t x h.1,GaussianStep.likelihood,←exp_add]
    congr 1
    simp only [field,Finset.sum_add_distrib,mul_add,Nat.cast_add,Nat.cast_one]
    have he : (∑i,spinValue (x i)*(sqrt t*h.2 i)) = sqrt t*∑i,spinValue (x i)*h.2 i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    ring

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α→β) (g : β→ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs]
  rw [←lintegral_indicator (hf hs),←lintegral_indicator hs,
    lintegral_map (hg.indicator hs) hf]
  apply lintegral_congr
  intro x
  by_cases hx : f x∈s <;> simp [hx]

theorem field_law (p : Prior n) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    (law p t k).map (field t) =
      ((GaussianStep.reference n).withDensity
        (fun z => ENNReal.ofReal (GaussianStep.density p ((k:ℝ)*t) z))).map
        (fun z : Fin n→ℝ => fun i => sqrt ((k:ℝ)*t)*z i) := by
  let D : (Fin n→ℝ)→ℝ≥0∞ := fun y => ENNReal.ofReal
    (∑ x, p x*exp ((∑i,spinValue (x i)*y i)-(k:ℝ)*t*(n:ℝ)/2))
  have hD : Measurable D := by unfold D; fun_prop
  have hd : (fun h : History n k => ENNReal.ofReal (density p t h))=D ∘ field t := by
    funext h
    simp only [density,likelihood_field,Function.comp_def,D]
  have hs : (fun z => ENNReal.ofReal (GaussianStep.density p ((k:ℝ)*t) z)) =
      D ∘ (fun z : Fin n→ℝ => fun i => sqrt ((k:ℝ)*t)*z i) := by
    funext z
    unfold D GaussianStep.density GaussianStep.likelihood
    dsimp
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    congr 2
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [law,hd,hs,map_withDensity_comp _ _ _ (continuous_field t k).measurable hD,
    map_withDensity_comp _ _ _ (by fun_prop) hD,map_field_reference ht,
    map_scaled_reference (mul_nonneg (by positivity) ht)]

lemma weight_field (g : Disorder n) (h₀ y : Fin n→ℝ) (x : Spin n) :
    weight g (h₀+y) x=weight g h₀ x*exp (∑i,spinValue (x i)*y i) := by
  unfold weight hamiltonian
  rw [←exp_add]
  congr 1
  simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  have he : (∑i,y i*spinValue (x i))=∑i,spinValue (x i)*y i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he]
  ring

lemma posterior_gibbs_field (g : Disorder n) (h₀ : Fin n→ℝ) (t : ℝ)
    {k : ℕ} (h : History n k) : posterior (gibbsPrior g h₀) t h = gibbsPrior g (h₀+field t h) := by
  have he (x : Spin n) : gibbsPrior g h₀ x*likelihood t x h =
      (exp (-(k:ℝ)*t*(n:ℝ)/2)/partition g h₀)*weight g (h₀+field t h) x := by
    rw [likelihood_field,weight_field]
    change (weight g h₀ x/partition g h₀)*exp (_-_) = _
    rw [exp_sub]
    have hn : -(k:ℝ)*t*(n:ℝ)/2 = -((k:ℝ)*t*(n:ℝ)/2) := by ring
    rw [hn,exp_neg]
    ring
  have hd : density (gibbsPrior g h₀) t h =
      (exp (-(k:ℝ)*t*(n:ℝ)/2)/partition g h₀)*partition g (h₀+field t h) := by
    simp only [density,he,←Finset.mul_sum,partition]
  apply Prior.ext
  funext x
  change gibbsPrior g h₀ x*likelihood t x h/density (gibbsPrior g h₀) t h =
    weight g (h₀+field t h) x/partition g (h₀+field t h)
  rw [he,hd]
  exact mul_div_mul_left _ _ (div_ne_zero (exp_ne_zero _) (partition_pos _ _).ne')

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_CondSubConst
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianStep
open scoped BigOperators
noncomputable section
variable {n : ℕ}

lemma cond_sub_const (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) (c : ℝ)
    (i : Fin n) (x : Spin n) : cond p i (fun x => f x-c) x=cond p i f x-c := by
  unfold cond
  field_simp [(add_pos (hp x) (hp (flip i x))).ne']
  ring

lemma energy_sub_const (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) (c : ℝ) :
    energy p (fun x => f x-c)=energy p f := by
  unfold energy
  simp_rw [cond_sub_const p hp f c,sub_sub_sub_cancel_right]

lemma var_center (p : Prior n) (f : Spin n→ℝ) :
    var p (fun x => f x-avg p f)=var p f := by
  unfold var
  rw [avg_center]
  simp only [sub_zero]

end
end SKGap.GaussianStep

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma localization_scalar {den N E r c e s v w : ℝ} (hd : 0<den) (hN : 0<N)
    (H : den*r*N≤den*(c*E+e*N)+N*(s*(v+w*E/N)+1)) :
    (r-(e+(s*v+1)/den))*N≤(c+s*w/den)*E := by
  have he : den*((r-(e+(s*v+1)/den))*N-(c+s*w/den)*E)=
      den*r*N-(den*(c*E+e*N)+N*(s*(v+w*E/N)+1)) := by
    field_simp
    ring
  have hh : den*((r-(e+(s*v+1)/den))*N-(c+s*w/den)*E)≤0 := by
    rw [he]
    linarith
  have hz : (r-(e+(s*v+1)/den))*N-(c+s*w/den)*E ≤ 0 := by
    by_contra hz
    have hm := mul_pos hd (lt_of_not_ge hz)
    linarith
  linarith

lemma centered_localization_bound (p : Prior n) (hp : ∀x,0<p x) (hn : 0<n)
    (f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2)) (hc : avg p f=0)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀k<K,∀h:History n k,h∉B k → driftSquare p (squarePrior p f hf) t h ≤
      W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f) :
    (exp (-2*D*T)-localizationLoss n t W A a b T)*var p f≤
      localizationCost n A a b D L T*energy p f := by
  have hh:=localization_bound p hp f hf ht htn K B G hB hG E hE hprefix hGE
    D W A a b L T hD hW hA ha hb hL hDt hT hsmall hEsmall hmean hcov hterminal
  have hv : var p f=avg p (fun x => (f x)^2) := by rw [var_eq,hc]; ring
  rw [hv] at hh ⊢
  let v:=T*(W*(n:ℝ)+2*A*sqrt (n:ℝ)+4/a)+64*(n:ℝ)^2*T*t
  let w:=T*A*sqrt (n:ℝ)
  have hbody : T*(W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy p f/avg p (fun x => (f x)^2))+4/a)+
      64*(n:ℝ)^2*T*t = v+w*energy p f/avg p (fun x => (f x)^2) := by dsimp [v,w]; ring
  rw [hbody] at hh
  simpa only [localizationLoss,localizationCost,v,w,mul_assoc] using
    localization_scalar (mul_pos hb (by exact_mod_cast hn)) hf hh

theorem poincare_of_history_estimates (p : Prior n) (hp : ∀x,0<p x) (hn : 0<n)
    {t : ℝ} (ht : 0≤t) (htn : 4*(n:ℝ)*t≤1)
    (K : ℕ) (B G : ∀k,Set (History n k))
    (hB : ∀k,MeasurableSet (B k)) (hG : ∀k,MeasurableSet (G k))
    (E : Set (History n K)) (hE : MeasurableSet E)
    (hprefix : ∀k<K,∀h:History n (k+1),h∈G (k+1)→h.1∈G k)
    (hGE : (G K)ᶜ⊆E)
    (D W A a b L T C : ℝ) (hD : 0≤D) (hW : 0≤W) (hA : 0≤A)
    (ha : 0<a) (hb : 0<b) (hL : 0≤L) (hC : 0≤C)
    (hDt : D*t≤1/2) (hT : (K:ℝ)*t=T)
    (hsmall : ∀k<K,eventProbability p t (B k)≤exp (-a*(n:ℝ)))
    (hEsmall : eventProbability p t E≤exp (-b*(n:ℝ)))
    (hmean : ∀(f : Spin n→ℝ) (hf : 0<avg p (fun x => (f x)^2)),∀k<K,∀h:History n k,h∉B k →
      driftSquare p (squarePrior p f hf) t h ≤
        W*(n:ℝ)+A*sqrt (n:ℝ)*(2+energy (posterior p t h) f/avg (posterior p t h) (fun x => (f x)^2)))
    (hcov : ∀(f : Spin n→ℝ),∀k<K,∀h:History n k,h∈G k→
      (∑i,(∑x,posterior p t h x*(f x-avg (posterior p t h) f)*spinValue (x i))^2)≤
        D*(var (posterior p t h) f+energy (posterior p t h) f))
    (hterminal : ∀(f : Spin n→ℝ),∀h:History n K,h∉E→var (posterior p t h) f≤L*energy (posterior p t h) f)
    (hLoss : localizationLoss n t W A a b T≤exp (-2*D*T)/2)
    (hCost : localizationCost n A a b D L T≤C) :
    ∀f : Spin n→ℝ,var p f≤(2*C/exp (-2*D*T))*energy p f := by
  intro f
  by_cases hv : 0<var p f
  · let F:=fun x => f x-avg p f
    have hF : 0<avg p (fun x => (F x)^2) := hv
    have hh:=centered_localization_bound p hp hn F hF (avg_center p f) ht htn K B G hB hG E hE hprefix hGE
      D W A a b L T hD hW hA ha hb hL hDt hT hsmall hEsmall (hmean F hF) (hcov F) (hterminal F)
    dsimp [F] at hh
    rw [var_center,energy_sub_const p hp] at hh
    have hl:=mul_le_mul_of_nonneg_right hLoss hv.le
    have hc:=mul_le_mul_of_nonneg_right hCost (energy_nonneg p f)
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (exp_pos (-2*D*T))).mpr
    nlinarith
  · have hz : var p f=0 := le_antisymm (le_of_not_gt hv) (var_nonneg p f)
    rw [hz]
    exact mul_nonneg (div_nonneg (by positivity) (exp_pos _).le) (energy_nonneg p f)

end
end SKGap.GaussianHistory

namespace SKGap.GaussianHistory
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal NNReal
open GaussianStep
noncomputable section
variable {n : ℕ}

lemma eventProbability_lift (p : Prior n) {t : ℝ} (ht : 0≤t) {k : ℕ}
    (E : Set (History n k)) (hE : MeasurableSet E) :
    eventProbability p t (Prod.fst ⁻¹' E : Set (History n (k+1)))=eventProbability p t E := by
  rw [eventProbability, ← integral_indicator (hE.preimage measurable_fst),
    eventProbability, ← integral_indicator hE]
  have hm : Measurable (E.indicator (fun _=> (1:ℝ))) := measurable_const.indicator hE
  have he (h : History n k) : density p t h*E.indicator (fun _=>(1:ℝ)) h=E.indicator (density p t) h := by
    by_cases hmem : h∈E <;> simp [hmem]
  have hi : Integrable (fun h=>density p t h*E.indicator (fun _=> (1:ℝ)) h) (reference n k) := by
    simpa only [he] using (integrable_density p t k).indicator hE
  have H:=integral_lift p ht _ hm hi
  have he' (h : History n (k+1)) : density p t h*E.indicator (fun _=>(1:ℝ)) h.1=
      (Prod.fst ⁻¹' E).indicator (density p t (k:=k+1)) h := by
    by_cases hmem : h.1∈E <;> simp [hmem]
  simpa only [he,he'] using H

lemma eventProbability_union_le (p : Prior n) {t : ℝ} (_ht : 0≤t) {k : ℕ}
    (E F : Set (History n k)) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    eventProbability p t (E∪F)≤eventProbability p t E+eventProbability p t F := by
  have H := measureReal_union_le (μ := law p t k) E F
  have he (A : Set (History n k)) (hA : MeasurableSet A) :
      (law p t k).real A=eventProbability p t A := by
    rw [Measure.real, ← eventProbability_eq p t A hA, ENNReal.toReal_ofReal (eventProbability_nonneg p t A)]
  simpa only [he _ (hE.union hF),he E hE,he F hF] using H

lemma measurable_goodPrefix (B : ∀k, Set (History n k)) (hB : ∀k,MeasurableSet (B k)) :
    ∀k,MeasurableSet (goodPrefix B k)
  | 0 => (hB 0).compl
  | k+1 => ((measurable_goodPrefix B hB k).preimage measurable_fst).inter (hB (k+1)).compl

lemma goodPrefix_not_bad (B : ∀k, Set (History n k)) :
    ∀k,∀h:History n k,h∈goodPrefix B k→h∉B k
  | 0, _, h => h
  | _+1, _, h => h.2

lemma goodPrefix_previous (B : ∀k, Set (History n k)) (k : ℕ)
    (h : History n (k+1)) (hh : h∈goodPrefix B (k+1)) : h.1∈goodPrefix B k := hh.1

lemma goodPrefix_failure_bound (p : Prior n) {t : ℝ} (ht : 0≤t)
    (B : ∀k,Set (History n k)) (hB : ∀k,MeasurableSet (B k)) :
    ∀k,eventProbability p t (goodPrefix B k)ᶜ ≤ ∑i∈Finset.range (k+1),eventProbability p t (B i)
  | 0 => by simp [goodPrefix]
  | k+1 => by
    have hE : (goodPrefix B (k+1))ᶜ =
        (Prod.fst ⁻¹' (goodPrefix B k)ᶜ) ∪ B (k+1) := by
          ext h
          simp only [goodPrefix,mem_compl_iff,mem_preimage,mem_inter_iff,mem_union]
          tauto
    rw [hE,Finset.sum_range_succ]
    have H : eventProbability p t (Prod.fst ⁻¹' (goodPrefix B k)ᶜ : Set (History n (k+1))) ≤
        ∑i∈Finset.range (k+1),eventProbability p t (B i) := by
      rw [eventProbability_lift p ht _ (measurable_goodPrefix B hB k).compl]
      exact goodPrefix_failure_bound p ht B hB k
    exact (eventProbability_union_le p ht _ _
      ((measurable_goodPrefix B hB k).compl.preimage measurable_fst) (hB (k+1))).trans
        (by linarith)

lemma bad_term_le_sum (p : Prior n) (t : ℝ) (B : ∀k,Set (History n k)) {k K : ℕ}
    (hk : k≤K) : eventProbability p t (B k)≤∑i∈Finset.range (K+1),eventProbability p t (B i) := by
  exact Finset.single_le_sum (fun i _=>eventProbability_nonneg p t (B i)) (by simpa using hk)

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_GridSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.GaussianHistory
open Real Filter
open scoped Topology
noncomputable section

lemma gridSteps_pos (n : ℕ) : 0<gridSteps n := by unfold gridSteps; positivity
lemma gridStep_nonneg {T : ℝ} (hT : 0≤T) (n : ℕ) : 0≤gridStep T n := by
  unfold gridStep
  positivity
lemma grid_total (T : ℝ) (n : ℕ) : (gridSteps n:ℝ)*gridStep T n=T := by
  unfold gridStep
  field_simp [show (gridSteps n:ℝ)≠0 from (Nat.cast_pos.mpr (gridSteps_pos n)).ne']
lemma gridStep_eq (T : ℝ) (n : ℕ) : gridStep T n=T*((n:ℝ)+1)⁻¹^4 := by
  simp only [gridStep,gridSteps,Nat.cast_pow,Nat.cast_add,Nat.cast_one,div_eq_mul_inv,inv_pow]

lemma inv_succ_tendsto : Tendsto (fun n : ℕ=>((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
  apply Tendsto.inv_tendsto_atTop
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

lemma gridStep_tendsto (T : ℝ) : Tendsto (gridStep T) atTop (𝓝 0) := by
  change Tendsto (fun n=>gridStep T n) atTop (𝓝 0)
  simpa only [gridStep_eq,zero_pow (by decide : 4≠0),mul_zero] using
    (tendsto_const_nhds.mul (inv_succ_tendsto.pow 4) :
      Tendsto (fun n : ℕ=>T*((n:ℝ)+1)⁻¹^4) atTop (𝓝 (T*0^4)))

lemma nat_mul_gridStep_tendsto (T : ℝ) :
    Tendsto (fun n : ℕ=>(n:ℝ)*gridStep T n) atTop (𝓝 0) := by
  have H:=(((tendsto_const_nhds (x:=(1:ℝ))).sub inv_succ_tendsto).mul
    (inv_succ_tendsto.pow 3)).const_mul T
  have he (n : ℕ) : (n:ℝ)*gridStep T n=T*(1-((n:ℝ)+1)⁻¹)*((n:ℝ)+1)⁻¹^3 := by
    rw [gridStep_eq]
    field_simp [show (n:ℝ)+1≠0 by positivity]
    ring
  simpa only [he,sub_zero,zero_pow (by decide : 3≠0),mul_zero,mul_assoc] using H

lemma nat_sq_mul_gridStep_tendsto (T : ℝ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^2*gridStep T n) atTop (𝓝 0) := by
  have H:=((((tendsto_const_nhds (x:=(1:ℝ))).sub inv_succ_tendsto).pow 2).mul
    (inv_succ_tendsto.pow 2)).const_mul T
  have he (n : ℕ) : (n:ℝ)^2*gridStep T n=T*(1-((n:ℝ)+1)⁻¹)^2*((n:ℝ)+1)⁻¹^2 := by
    rw [gridStep_eq]
    field_simp [show (n:ℝ)+1≠0 by positivity]
    ring
  simpa only [he,sub_zero,zero_pow (by decide : 2≠0),mul_zero,mul_assoc] using H

lemma nat_inv_tendsto : Tendsto (fun n : ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_natCast_atTop_atTop.inv_tendsto_atTop

lemma sqrt_div_nat_tendsto :
    Tendsto (fun n : ℕ=>sqrt (n:ℝ)/(n:ℝ)) atTop (𝓝 0) := by
  have H := (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  apply H.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hs : 0 < sqrt (n:ℝ) := sqrt_pos.mpr hp
  change (sqrt (n:ℝ))⁻¹ = sqrt (n:ℝ)/(n:ℝ)
  field_simp [hp.ne',hs.ne']
  nlinarith [sq_sqrt hp.le]

lemma localizationLoss_tendsto (T W A a b : ℝ) (hb : b≠0) :
    Tendsto (fun n=>localizationLoss n (gridStep T n) W A a b T) atTop
      (𝓝 (exp (4*T/a)*T*W/b)) := by
  have h1 := (nat_sq_mul_gridStep_tendsto T).const_mul (16*T)
  have h2 := ((tendsto_const_nhds (x:=W)).add ((sqrt_div_nat_tendsto.const_mul (2*A)).add
    (nat_inv_tendsto.const_mul (4/a)))).const_mul T
  have h3 := (nat_mul_gridStep_tendsto T).const_mul (64*T)
  have H := (h1.add ((h2.add h3).const_mul (exp (4*T/a)/b))).add
    (nat_inv_tendsto.const_mul (1/b))
  have H' : Tendsto (fun n : ℕ=>16*T*((n:ℝ)^2*gridStep T n)+
      exp (4*T/a)/b*(T*(W+(2*A*(sqrt (n:ℝ)/(n:ℝ))+4/a*(n:ℝ)⁻¹))+
        64*T*((n:ℝ)*gridStep T n))+1/b*(n:ℝ)⁻¹) atTop
      (𝓝 (exp (4*T/a)*T*W/b)) := by convert H using 1; ring_nf
  apply H'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  unfold localizationLoss
  field_simp
  ring

lemma localizationCost_tendsto (A a b D L T : ℝ) :
    Tendsto (fun n=>localizationCost n A a b D L T) atTop (𝓝 (D*T+L)) := by
  have H := (tendsto_const_nhds (x:=D*T+L)).add (sqrt_div_nat_tendsto.const_mul (exp (4*T/a)*T*A/b))
  convert H using 1
  · ext n
    unfold localizationCost
    ring
  · ring_nf

theorem localization_numeric_choice (D L T a b : ℝ) (hT : 0<T) (hb : 0<b) :
    ∃W : ℝ,0<W ∧ ∀A : ℝ,∀ᶠ n : ℕ in atTop,
      0<n ∧ 4*(n:ℝ)*gridStep T n≤1 ∧ D*gridStep T n≤1/2 ∧
      localizationLoss n (gridStep T n) W A a b T≤exp (-2*D*T)/2 ∧
      localizationCost n A a b D L T≤D*T+L+1 := by
  let W:=exp (-2*D*T)*b/(4*exp (4*T/a)*T)
  have hW : 0<W := by dsimp [W]; positivity
  refine ⟨W,hW,?_⟩
  intro A
  have hw : exp (4*T/a)*T*W/b=exp (-2*D*T)/4 := by
    dsimp [W]
    field_simp
  have hl:=localizationLoss_tendsto T W A a b hb.ne'
  rw [hw] at hl
  have ht:=((nat_mul_gridStep_tendsto T).const_mul 4).eventually_lt_const (by norm_num : (4:ℝ)*0<1)
  have hd:=((gridStep_tendsto T).const_mul D).eventually_lt_const (by norm_num : D*(0:ℝ)<1/2)
  have hloss:=hl.eventually_lt_const (show exp (-2*D*T)/4<exp (-2*D*T)/2 by nlinarith [exp_pos (-2*D*T)])
  have hcost:=(localizationCost_tendsto A a b D L T).eventually_lt_const
    (show D*T+L<D*T+L+1 by linarith)
  filter_upwards [eventually_ge_atTop 1,ht,hd,hloss,hcost] with n hn ht hd hl hc
  exact ⟨by omega,by simpa only [mul_assoc] using ht.le,hd.le,hl.le,hc.le⟩

lemma nat_pow_exp_tendsto {a : ℝ} (ha : 0<a) (k : ℕ) :
    Tendsto (fun n : ℕ=>(n:ℝ)^k*exp (-a*(n:ℝ))) atTop (𝓝 0) := by
  have H := (tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
  have H' := H.const_mul (a^k)⁻¹
  convert H' using 1
  · ext n
    dsimp
    rw [mul_pow]
    field_simp
  · simp

lemma constant_exp_absorb (C : ℝ) {a : ℝ} (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop,C*exp (-a*(n:ℝ))≤exp (-(a/2)*(n:ℝ)) := by
  have H : Tendsto (fun n : ℕ=>C*exp (-(a/2)*(n:ℝ))) atTop (𝓝 0) := by
    simpa only [pow_zero,one_mul,mul_zero] using (nat_pow_exp_tendsto (half_pos ha) 0).const_mul C
  filter_upwards [H.eventually_lt_const zero_lt_one] with n hn
  have he : exp (-a*(n:ℝ))= exp (-(a/2)*(n:ℝ))*exp (-(a/2)*(n:ℝ)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he,← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hn.le (exp_pos _).le).trans_eq (one_mul _)

end
end SKGap.GaussianHistory

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FixedTimeAnnealed
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}
attribute [local instance] OAI.SKGap.ObservationBridge.annealedMatrixMeasurable
local instance annealedMatrixBorel : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma measurableSet_gibbsObservationBad (j A K ε c ρ t : ℝ) (s : Spin n) :
    MeasurableSet (gibbsObservationBad j A K ε c ρ t s) := by
  have hmap : Continuous (fun p : Disorder n × Field n=>
      (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i)) :
      Disorder n × Field n→Matrix (Fin n) (Fin n) ℝ × Field n) :=
    (continuous_coupling.comp continuous_fst).prodMk (by fun_prop)
  have hmmap : Measurable (fun p : Disorder n × Field n=>
      (coupling p.1,(fun i=>t*spinValue (s i)+p.2 i)) :
      Disorder n × Field n→Matrix (Fin n) (Fin n) ℝ × Field n) := hmap.measurable
  exact (measurableSet_literalBadPair j A K ε c ρ).preimage hmmap

end SKGap.ObservationBridge

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_ChannelTranslation
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal
variable {n : ℕ}

lemma channel_pdf_tilt (a x : ℝ) :
    gaussianPDFReal a 1 x=gaussianPDFReal 0 1 x*exp (a*x-a^2/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have he : -(x-a)^2/2= -x^2/2+(a*x-a^2/2) := by ring
  rw [he,exp_add]
  ring

lemma channelReference_tilt (a : Fin n→ℝ) :
    (channelReference n).withDensity
      (fun z=>ENNReal.ofReal (exp ((∑ i,a i*z i)-(∑ i,a i^2)/2))) =
      Measure.pi (fun i=>gaussianReal (a i) 1) := by
  have hp (z : Fin n→ℝ) : (∏ i,gaussianPDFReal (a i) 1 (z i))=
      (∏ i,gaussianPDFReal 0 1 (z i))*exp ((∑ i,a i*z i)-(∑ i,a i^2)/2) := by
    calc
      _ = ∏ i,(gaussianPDFReal 0 1 (z i)*exp (a i*z i-a i^2/2)) :=
        Finset.prod_congr rfl (fun i _=>channel_pdf_tilt _ _)
      _ = _ := by
        rw [Finset.prod_mul_distrib,← exp_sum]
        congr 2
        rw [Finset.sum_sub_distrib,Finset.sum_div]
  unfold channelReference
  rw [GaussianDensity.pi_gaussian_density (fun _ : Fin n=>0) (fun _=>1) (fun _=>one_ne_zero),
    GaussianDensity.pi_gaussian_density a (fun _=>1) (fun _=>one_ne_zero)]
  rw [← withDensity_mul _ (GaussianDensity.measurable_productPDF _ _) (by fun_prop)]
  congr 1
  ext z
  simp only [Pi.mul_apply,hp]
  exact (ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _=>gaussianPDFReal_nonneg 0 1 (z i)))).symm

lemma channel_shift_hasLaw (a : Fin n→ℝ) :
    HasLaw (fun z : Fin n→ℝ=>fun i=>z i+a i)
      (Measure.pi (fun i=>gaussianReal (a i) 1)) (channelReference n) := by
  have hl (i : Fin n) : HasLaw (fun z : Fin n→ℝ=>z i+a i)
      (gaussianReal (a i) 1) (channelReference n) := by
    have hc : HasLaw (fun z : Fin n→ℝ=>z i) (gaussianReal 0 1) (channelReference n) :=
      ⟨(measurable_pi_apply i).aemeasurable,(measurePreserving_eval (fun _ : Fin n=>gaussianReal 0 1) i).map_eq⟩
    simpa only [zero_add] using gaussianReal_add_const hc (a i)
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : Fin n=>aemeasurable_id)).comp
    (fun i=>fun x : ℝ=>x+a i) (fun _=>by fun_prop))

lemma channel_likelihood_tilt {T : ℝ} (hT : 0 ≤ T) (x : Spin n) :
    (channelReference n).withDensity (fun z=>ENNReal.ofReal (gaussianChannelLikelihood T x z))=
      Measure.pi (fun i=>gaussianReal (sqrt T*spinValue (x i)) 1) := by
  have hs : (∑ i,(sqrt T*spinValue (x i))^2)=(n:ℝ)*T := by
    simp only [mul_pow,sq_sqrt hT,spinValue_sq,mul_one,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
  convert channelReference_tilt (fun i=>sqrt T*spinValue (x i)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [hs,gaussianChannelLikelihood]

lemma gaussianChannel_event (g : Disorder n) {T : ℝ} (hT : 0 ≤ T) (B : Set (Fin n→ℝ))
    (hB : MeasurableSet B) :
    gaussianChannelLaw g T B=∑ x,ENNReal.ofReal (mass g 0 x)*
      channelReference n ((fun z : Fin n→ℝ=>fun i=>z i+sqrt T*spinValue (x i)) ⁻¹' B) := by
  rw [gaussianChannelLaw,withDensity_apply _ hB]
  have hd (z : Fin n→ℝ) : ENNReal.ofReal (gaussianChannelDensity g T z)=
      ∑ x,ENNReal.ofReal (mass g 0 x)*ENNReal.ofReal (gaussianChannelLikelihood T x z) := by
    unfold gaussianChannelDensity
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _=>mul_nonneg (mass_nonneg g 0 x) (by unfold gaussianChannelLikelihood; positivity))]
    exact Finset.sum_congr rfl (fun x _=>ENNReal.ofReal_mul (mass_nonneg g 0 x))
  simp only [hd]
  rw [lintegral_finsetSum _ (fun x _=>by unfold gaussianChannelLikelihood; fun_prop)]
  apply Finset.sum_congr rfl
  intro x _
  rw [lintegral_const_mul _ (by unfold gaussianChannelLikelihood; fun_prop)]
  congr 1
  rw [← withDensity_apply _ hB,channel_likelihood_tilt hT]
  exact ((channel_shift_hasLaw (fun i=>sqrt T*spinValue (x i))).map_eq ▸
    Measure.map_apply (by fun_prop) hB)
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_QuenchedHelpers
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.disorderLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
noncomputable section

lemma whp_iff_real (β : ℝ) (P : ∀n,Disorder n→Prop) :
    Whp β P ↔ Tendsto (fun n=>(disorderLaw β n).real {g | ¬P n g}) atTop (𝓝 0) := by
  let (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by unfold disorderLaw; infer_instance
  constructor
  · intro h
    simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp h
  · intro h
    have H:=(ENNReal.continuous_ofReal.tendsto 0).comp h
    change Tendsto (fun n=>disorderLaw β n {g | ¬P n g}) atTop (𝓝 0)
    simpa only [Function.comp_def,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_zero] using H

lemma Whp.mono {β : ℝ} {P Q : ∀n,Disorder n→Prop} (hP : Whp β P)
    (hPQ : ∀ᶠ n : ℕ in atTop,∀g,P n g→Q n g) : Whp β Q := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hP
    (Eventually.of_forall (fun _=>bot_le))
  filter_upwards [hPQ] with n hn
  apply measure_mono
  intro g hg hp
  exact hg (hn g hp)

lemma Whp.and {β : ℝ} {P Q : ∀n,Disorder n→Prop} (hP : Whp β P) (hQ : Whp β Q) :
    Whp β (fun n g=>P n g ∧ Q n g) := by
  classical
  have H:=hP.add hQ
  rw [add_zero] at H
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
    (Eventually.of_forall (fun _=>bot_le))
  apply Eventually.of_forall
  intro n
  have he : {g:Disorder n | ¬(P n g ∧ Q n g)}={g | ¬P n g}∪{g | ¬Q n g} := by
    ext g
    simp only [mem_ofPred_eq,mem_union]
    tauto
  rw [he]
  exact measure_union_le _ _

lemma whp_full_probability {β : ℝ} {P : ∀n,Disorder n→Prop} (hP : Whp β P) :
    Tendsto (fun n=>disorderLaw β n {g | P n g}) atTop (𝓝 1) := by
  classical
  let (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by unfold disorderLaw; infer_instance
  have H := (whp_iff_real β P).mp hP
  have H' := (tendsto_const_nhds (x:=(1:ℝ))).sub H
  rw [sub_zero] at H'
  have ht : Tendsto (fun n=>(disorderLaw β n).real {g | P n g}) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le H' tendsto_const_nhds
    · intro n
      have hs := measureReal_union_le (μ:=disorderLaw β n) {g | P n g} {g | ¬P n g}
      have he : ({g:Disorder n | P n g}∪{g | ¬P n g})=univ := by
        ext g
        simp only [mem_ofPred_eq,mem_union,mem_univ]
        tauto
      rw [he,probReal_univ] at hs
      linarith
    · intro n
      exact measureReal_le_one
  have hh:=(ENNReal.continuous_ofReal.tendsto 1).comp ht
  simpa only [Function.comp_def,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_one] using hh

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_ImplicitCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

lemma vectorNorm_neg (v : Fin n→ℝ) : vectorNorm (-v)=vectorNorm v := by
  exact norm_neg (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))
lemma vectorNorm_sub (u v : Fin n→ℝ) : vectorNorm (u-v)≤vectorNorm u+vectorNorm v := by
  simpa only [sub_eq_add_neg,vectorNorm_neg] using vectorNorm_add u (-v)

end SKGapCutoff.Recipe

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_StaticExperimentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep SKGapCutoff.Recipe SKGapCutoff.Static
noncomputable section
variable {n : ℕ}

lemma halfDiff_sq (f : Spin n→ℝ) (x : Spin n) (i : Fin n) :
    (SKGapCutoff.halfDiff i f x)^2=(f x-f (SKGap.flip i x))^2/4 := by
  rw [SKGapCutoff.halfDiff_as_flip,div_pow,mul_pow,SKGapCutoff.spin_sq]
  norm_num
  rfl

lemma conditionalVariance_eq (p : Prior n) (x : Spin n) (i : Fin n)
    (hp : ∀x,0<p x) :
    conditionalVariance p.mass x i=4*p x*p (SKGap.flip i x)/(p x+p (SKGap.flip i x))^2 := by
  unfold conditionalVariance conditionalMean
  rw [mul_pow,SKGapCutoff.spin_sq,one_mul]
  change 1-((p x-p (SKGap.flip i x))/(p x+p (SKGap.flip i x)))^2=_
  field_simp [(add_pos (hp x) (hp (SKGap.flip i x))).ne']
  ring

lemma varianceEnergy_eq (p : Prior n) (hp : ∀x,0<p x) (f : Spin n→ℝ) :
    varianceEnergy p.mass f=energy p f := by
  simp only [varianceEnergy,Finset.mul_sum,energy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change avg p (fun x=>conditionalVariance p.mass x i*(SKGapCutoff.halfDiff i f x)^2)=_
  rw [avg_flip p i,avg_flip p i]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [conditionalVariance_eq p x i hp,conditionalVariance_eq p (SKGap.flip i x) i hp,
    halfDiff_sq,halfDiff_sq,SKGap.flip_flip,cond_flip]
  unfold GaussianStep.cond
  rw [add_comm (p (SKGap.flip i x)) (p x)]
  field_simp [(add_pos (hp x) (hp (SKGap.flip i x))).ne']
  ring

lemma fieldGibbs_prior (g : Disorder n) (h : Fin n→ℝ) :
    SKGapCutoff.fieldGibbs (coupling g) h=(gibbsPrior g h).mass :=
  SKGapCutoff.fieldGibbs_edge g h

lemma covariance_square_bound {j Aroot ε c r₀ D : ℝ} {g : Disorder n}
    (hD : 0≤D) (H : PosteriorCovarianceProperty j Aroot ε c r₀ D g)
    (h : Fin n→ℝ) (hb : ¬rootBad j Aroot ε c r₀ (coupling g) h) (f : Spin n→ℝ) :
    (∑i,(∑x,gibbsPrior g h x*(f x-avg (gibbsPrior g h) f)*spinValue (x i))^2)≤
      D^2*(var (gibbsPrior g h) f+energy (gibbsPrior g h) f) := by
  have hh:=H h hb f
  rw [fieldGibbs_prior,varianceEnergy_eq _ (mass_pos g h)] at hh
  change SKGapCutoff.Recipe.vectorNorm (centeredSpinCovariance (gibbsPrior g h).mass f) ≤
    D*sqrt (var (gibbsPrior g h) f+energy (gibbsPrior g h) f) at hh
  have hs:=(sq_le_sq₀ (SKGapCutoff.Recipe.vectorNorm_nonneg _)
    (mul_nonneg hD (Real.sqrt_nonneg _))).2 hh
  rw [mul_pow,Real.sq_sqrt (add_nonneg (GaussianStep.var_nonneg _ _) (energy_nonneg _ _)),
    SKGapCutoff.Recipe.vectorNorm_sq] at hs
  exact hs

lemma squareMean_eq (p : Prior n) (f : Spin n→ℝ) (hf : 0<avg p (fun x=>(f x)^2)) :
    squareMean p.mass f=mean (squarePrior p f hf) := rfl

lemma squareMean_one (p : Prior n) : squareMean p.mass (fun _=>1)=mean p := by
  ext i
  simp only [squareMean,squareMass,one_pow,mul_one,p.sum_one,div_one,mean]
  rfl

lemma energy_one (p : Prior n) (hp : ∀x,0<p x) : energy p (fun _=>1)=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro x _
  have hh : GaussianStep.cond p i (fun _=>1) x=1 := by
    simp [GaussianStep.cond,div_self (add_pos (hp x) (hp (SKGap.flip i x))).ne']
  simp only [hh,sub_self,zero_pow (by decide : 2≠0),mul_zero]

lemma stable_mean_difference {j Aroot ε c r₀ ρ C₀ C : ℝ} {g : Disorder n}
    (hn : 0<n) (hAroot : 1≤Aroot)
    (H : StableSquareMeanProperty j c r₀ ρ C₀ C (coupling g))
    (h : Fin n→ℝ) (hb : ¬rootBad j Aroot ε c r₀ (coupling g) h)
    (f : Spin n→ℝ) (hf : 0<avg (gibbsPrior g h) (fun x=>(f x)^2)) :
    SKGapCutoff.Recipe.vectorNorm (mean (squarePrior (gibbsPrior g h) f hf)-mean (gibbsPrior g h))≤
      2*C₀*ρ*sqrt (n:ℝ)+C*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by
  obtain ⟨r,hr,hu,hall⟩:=stableSquareMeanProperty_rootBad hAroot (coupling g) H h hb
  rw [fieldGibbs_prior] at hall
  have h1:=hall f hf
  have h0:=hall (fun _=>1) (by simp only [one_pow,mul_one,(gibbsPrior g h).sum_one];norm_num)
  rw [varianceEnergy_eq _ (mass_pos g h),squareMean_eq _ _ hf] at h1
  rw [varianceEnergy_eq _ (mass_pos g h),energy_one _ (mass_pos g h),squareMean_one] at h0
  have hs : 0 < sqrt (n:ℝ):=sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h1':= (div_le_iff₀ hs).mp h1
  have h0':= (div_le_iff₀ hs).mp h0
  have hh:=SKGapCutoff.Recipe.vectorNorm_sub
    (mean (squarePrior (gibbsPrior g h) f hf)-magnetization r)
    (mean (gibbsPrior g h)-magnetization r)
  rw [sub_sub_sub_cancel_right] at hh
  apply hh.trans
  calc
    _≤(C₀*ρ+C/sqrt (n:ℝ)*(1+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)))*sqrt (n:ℝ)+
      (C₀*ρ+C/sqrt (n:ℝ)*(1+0/(∑x,gibbsPrior g h x*(1:ℝ)^2)))*sqrt (n:ℝ) := add_le_add h1' h0'
    _=_ := by field_simp;ring

lemma drift_square_of_stable_mean {j Aroot ε c r₀ ρ C₀ C : ℝ} {g : Disorder n}
    (hn : 0<n) (hAroot : 1≤Aroot)
    (H : StableSquareMeanProperty j c r₀ ρ C₀ C (coupling g))
    (h : Fin n→ℝ) (hb : ¬rootBad j Aroot ε c r₀ (coupling g) h)
    (f : Spin n→ℝ) (hf : 0<avg (gibbsPrior g h) (fun x=>(f x)^2)) :
    (∑i,(mean (squarePrior (gibbsPrior g h) f hf) i-mean (gibbsPrior g h) i)^2)≤
      (4*C₀*ρ)*(n:ℝ)+(2*C)*sqrt (n:ℝ)*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by
  let v:=mean (squarePrior (gibbsPrior g h) f hf)-mean (gibbsPrior g h)
  have hm:=stable_mean_difference hn hAroot H h hb f hf
  have hu : SKGapCutoff.Recipe.vectorNorm v≤2*sqrt (n:ℝ) := by
    apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
    simp only [←sq]
    rw [SKGapCutoff.Recipe.vectorNorm_sq,mul_pow,sq_sqrt (Nat.cast_nonneg n)]
    simpa only [v,Pi.sub_apply,show (2:ℝ)^2=4 by norm_num] using
      GaussianHistory.mean_difference_square_le (gibbsPrior g h) (squarePrior (gibbsPrior g h) f hf)
  have hh:=mul_le_mul hm hu (SKGapCutoff.Recipe.vectorNorm_nonneg v) ((SKGapCutoff.Recipe.vectorNorm_nonneg v).trans hm)
  have he : (2*C₀*ρ*sqrt (n:ℝ)+C*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)))*(2*sqrt (n:ℝ))=
      (4*C₀*ρ)*(n:ℝ)+(2*C)*sqrt (n:ℝ)*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by
    calc
      _=(4*C₀*ρ)*(sqrt (n:ℝ))^2+(2*C)*sqrt (n:ℝ)*(2+energy (gibbsPrior g h) f/avg (gibbsPrior g h) (fun x=>(f x)^2)) := by ring
      _=_ := by rw [sq_sqrt (Nat.cast_nonneg n)]
  rw [←sq,SKGapCutoff.Recipe.vectorNorm_sq,he] at hh
  exact hh

end
end SKGap.FullMain

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep GaussianHistory ObservationBridge
noncomputable section
variable {n : ℕ}

lemma gaussianChannelLaw_step (g : Disorder n) (t : ℝ) :
    gaussianChannelLaw g t=(GaussianStep.reference n).withDensity
      (fun z=>ENNReal.ofReal (GaussianStep.density (gibbsPrior g 0) t z)) := by
  have hd : gaussianChannelDensity g t=fun z=>GaussianStep.density (gibbsPrior g 0) t z := by
    funext z
    apply Finset.sum_congr rfl
    intro x _
    change mass g 0 x*exp ((∑i,sqrt t*spinValue (x i)*z i)-(n:ℝ)*t/2)=
      mass g 0 x*exp (sqrt t*(∑i,spinValue (x i)*z i)-t*(n:ℝ)/2)
    congr 2
    simp only [Finset.mul_sum,←mul_assoc,mul_comm (n:ℝ) t]
  change (GaussianStep.reference n).withDensity (fun z=>ENNReal.ofReal (gaussianChannelDensity g t z))=_
  rw [hd]

lemma history_field_event (g : Disorder n) {t : ℝ} (ht : 0≤t) (k : ℕ)
    (E : Set (Fin n→ℝ)) (hE : MeasurableSet E) :
    eventProbability (gibbsPrior g 0) t ((GaussianHistory.field t) ⁻¹' E : Set (History n k))=
      (gaussianChannelLaw g ((k:ℝ)*t)).real
        ((fun z : Fin n→ℝ=>fun i=>sqrt ((k:ℝ)*t)*z i) ⁻¹' E) := by
  have hh:=eventProbability_eq (gibbsPrior g 0) t
    ((GaussianHistory.field t) ⁻¹' E : Set (History n k))
    (hE.preimage (continuous_field t k).measurable)
  rw [←Measure.map_apply (continuous_field t k).measurable hE,
    field_law _ ht k,←gaussianChannelLaw_step,
    Measure.map_apply (by fun_prop) hE] at hh
  simpa only [ENNReal.toReal_ofReal (eventProbability_nonneg _ _ _),Measure.real] using
    congrArg ENNReal.toReal hh

attribute [local instance] OAI.SKGap.FullMain.instMeasurableSpaceMatrixFinReal_solutions
local instance instBorelSpaceMatrixFinReal_solutions_rff806f_1 : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩
lemma measurable_rootFields (g : Disorder n) (j A ε c ρ : ℝ) :
    MeasurableSet {h:Fin n→ℝ | rootBad j A ε c ρ (coupling g) h} := by
  have hm : Measurable (fun h => (coupling g,h) : Field n → Matrix (Fin n) (Fin n) ℝ × Field n) :=
    measurable_const.prodMk measurable_id
  change MeasurableSet ((fun h => (coupling g,h) : Field n → Matrix (Fin n) (Fin n) ℝ × Field n) ⁻¹'
    {p : Matrix (Fin n) (Fin n) ℝ × Field n | rootBad j A ε c ρ p.1 p.2})
  exact (measurableSet_rootBad (n:=n) j A ε c ρ).preimage hm

lemma history_root_probability (g : Disorder n) {t : ℝ} (ht : 0≤t) (k : ℕ)
    (j A K ε c ρ : ℝ) (hop : operatorBound K (coupling g)) :
    eventProbability (gibbsPrior g 0) t
      {h:History n k | rootBad j A ε c ρ (coupling g) (GaussianHistory.field t h)}=
      fixedTimeFailure n j A K ε c ρ ((k:ℝ)*t) g := by
  let T:=(k:ℝ)*t
  have hT : 0≤T:=mul_nonneg (Nat.cast_nonneg k) ht
  let E:Set (Fin n→ℝ):={h | rootBad j A ε c ρ (coupling g) h}
  have hE : MeasurableSet E:=measurable_rootFields g j A ε c ρ
  change eventProbability (gibbsPrior g 0) t ((GaussianHistory.field t) ⁻¹' E : Set (History n k))=_
  rw [history_field_event g ht k E hE,Measure.real,gaussianChannel_event _ hT _
    (hE.preimage (by fun_prop))]
  change (∑x,ENNReal.ofReal (mass g 0 x)*_).toReal=(fixedTimeFailureENN j A K ε c ρ T g).toReal
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  unfold conditionalSpinFailure
  have hGB : MeasurableSet ((Prod.mk g) ⁻¹' gibbsObservationBad j A K ε c ρ T x) :=
    (measurableSet_gibbsObservationBad j A K ε c ρ T x).preimage
      (show Measurable (Prod.mk g : Field n→Disorder n × Field n) from measurable_const.prodMk measurable_id)
  rw [←GaussianHistory.map_scaled_reference hT,Measure.map_apply (by fun_prop) hGB]
  congr 1
  ext z
  change rootBad j A ε c ρ (coupling g) (fun i=>sqrt T*(z i+sqrt T*spinValue (x i))) ↔
    operatorBound K (coupling g) ∧ rootBad j A ε c ρ (coupling g) (fun i=>T*spinValue (x i)+sqrt T*z i)
  have he : (fun i=>sqrt T*(z i+sqrt T*spinValue (x i)))=(fun i=>T*spinValue (x i)+sqrt T*z i) := by
    funext i
    calc
      _=(sqrt T)^2*spinValue (x i)+sqrt T*z i:=by ring
      _=_:=by rw [sq_sqrt hT]
  rw [he]
  simp only [hop,true_and]

lemma history_terminal_probability (g : Disorder n) {t : ℝ} (ht : 0≤t) (k : ℕ) :
    eventProbability (gibbsPrior g 0) t
      {h:History n k | ¬∀f:Spin n→ℝ,
        variance g (GaussianHistory.field t h) f≤2*dirichlet g (GaussianHistory.field t h) f}=
      (gaussianChannelLaw g ((k:ℝ)*t)).real
        {z | ¬∀f:Spin n→ℝ,variance g (fun i=>sqrt ((k:ℝ)*t)*z i) f≤
          2*dirichlet g (fun i=>sqrt ((k:ℝ)*t)*z i) f} := by
  exact history_field_event g ht k _ (terminal_goodSet_closed g 2).measurableSet.compl

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ModelLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep GaussianHistory ObservationBridge SKGapCutoff.Recipe SKGapCutoff.Static
noncomputable section
variable {n : ℕ}

theorem poincare_from_model_data (g : Disorder n) (hn : 0<n)
    (j Ar K ε c r₀ ρ C₀ Cmean D₀ W a aT b T : ℝ)
    (hAr : 1≤Ar) (hD₀ : 0≤D₀) (hW : 0≤W) (hCmean : 0≤Cmean)
    (ha : 0<a) (hb : 0<b) (hT : 0<T) (hlead : 4*C₀*ρ≤W)
    (hop : operatorBound K (coupling g))
    (hroot : gridFailure n j Ar K ε c r₀ T g≤exp (-a*(n:ℝ)))
    (hterminal : (gaussianChannelLaw g T).real {z | ¬∀f:Spin n→ℝ,
      variance g (fun i=>sqrt T*z i) f≤2*dirichlet g (fun i=>sqrt T*z i) f}≤exp (-aT*(n:ℝ)))
    (hcov : PosteriorCovarianceProperty j Ar ε c r₀ D₀ g)
    (hmean : StableSquareMeanProperty j c r₀ ρ C₀ Cmean (coupling g))
    (hrare : exp (-a*(n:ℝ))+exp (-aT*(n:ℝ))≤exp (-b*(n:ℝ)))
    (hmesh : 4*(n:ℝ)*gridStep T n≤1)
    (hmeshD : D₀^2*gridStep T n≤1/2)
    (hloss : localizationLoss n (gridStep T n) W (2*Cmean) a b T≤exp (-2*D₀^2*T)/2)
    (hcost : localizationCost n (2*Cmean) a b (D₀^2) 2 T≤D₀^2*T+3) :
    ∀f:Spin n→ℝ,variance g 0 f≤(2*(D₀^2*T+3)/exp (-2*D₀^2*T))*dirichlet g 0 f := by
  let t:=gridStep T n
  have ht : 0≤t:=gridStep_nonneg hT.le n
  let B : ∀k,Set (History n k):=fun k=>{h | rootBad j Ar ε c r₀ (coupling g) (GaussianHistory.field t h)}
  have hB (k : ℕ) : MeasurableSet (B k):=
    (measurable_rootFields g j Ar ε c r₀).preimage (continuous_field t k).measurable
  let F:Set (History n (gridSteps n)):= {h | ¬∀f:Spin n→ℝ,
    variance g (GaussianHistory.field t h) f≤2*dirichlet g (GaussianHistory.field t h) f}
  have hF : MeasurableSet F:=
    ((terminal_goodSet_closed g 2).measurableSet.compl).preimage (continuous_field t (gridSteps n)).measurable
  let E:Set (History n (gridSteps n)):=(goodPrefix B (gridSteps n))ᶜ∪F
  have hE : MeasurableSet E:=(measurable_goodPrefix B hB _).compl.union hF
  have hsum : (∑k∈Finset.range (gridSteps n+1),eventProbability (gibbsPrior g 0) t (B k))=
      gridFailure n j Ar K ε c r₀ T g := by
    apply Finset.sum_congr rfl
    intro k _
    exact history_root_probability g ht k j Ar K ε c r₀ hop
  have hsmall (k : ℕ) (hk : k<gridSteps n) :
      eventProbability (gibbsPrior g 0) t (B k)≤exp (-a*(n:ℝ)) := by
    exact (bad_term_le_sum (gibbsPrior g 0) t B hk.le).trans (hsum.symm ▸ hroot)
  have hFsmall : eventProbability (gibbsPrior g 0) t F≤exp (-aT*(n:ℝ)) := by
    rw [history_terminal_probability g ht (gridSteps n)]
    simpa only [t,grid_total] using hterminal
  have hEsmall : eventProbability (gibbsPrior g 0) t E≤exp (-b*(n:ℝ)) := by
    have hp:=(goodPrefix_failure_bound (gibbsPrior g 0) ht B hB (gridSteps n))
    rw [hsum] at hp
    exact (eventProbability_union_le (gibbsPrior g 0) ht _ _
      (measurable_goodPrefix B hB _).compl hF).trans ((add_le_add (hp.trans hroot) hFsmall).trans hrare)
  have hpfield {k : ℕ} (h : History n k) :
      GaussianHistory.posterior (gibbsPrior g 0) t h=gibbsPrior g (GaussianHistory.field t h) := by
    simpa only [zero_add] using posterior_gibbs_field g 0 t h
  have hD : 0≤D₀^2:=sq_nonneg D₀
  have hconst : 0≤D₀^2*T+3:=by positivity
  have H:=poincare_of_history_estimates (gibbsPrior g 0) (mass_pos g 0) hn ht hmesh
    (gridSteps n) B (goodPrefix B) hB (measurable_goodPrefix B hB) E hE
    (fun k _ h hh=>goodPrefix_previous B k h hh) subset_union_left
    (D₀^2) W (2*Cmean) a b 2 T (D₀^2*T+3) hD hW (by positivity) ha hb (by norm_num) hconst
    hmeshD (grid_total T n) hsmall hEsmall
    (fun f hf k _ h hh=>?_) (fun f k _ h hh=>?_) (fun f h hh=>?_) hloss hcost
  · intro f
    simpa only [gibbsPrior_var,gibbsPrior_energy] using H f
  · have hppos : 0<avg (gibbsPrior g (GaussianHistory.field t h)) (fun x=>(f x)^2) := by
      rw [←hpfield h]
      exact posterior_square_pos (gibbsPrior g 0) f hf t h
    have hm:=drift_square_of_stable_mean hn hAr hmean (GaussianHistory.field t h) hh f hppos
    simp only [driftSquare,GaussianHistory.squarePrior_posterior,hpfield]
    apply hm.trans
    exact add_le_add (mul_le_mul_of_nonneg_right hlead (Nat.cast_nonneg n)) le_rfl
  · rw [hpfield h]
    exact covariance_square_bound hD₀ hcov (GaussianHistory.field t h)
      (goodPrefix_not_bad B k h hh) f
  · rw [hpfield h,gibbsPrior_var,gibbsPrior_energy]
    have hnF : h∉F:=fun hhF=>hh (Or.inr hhF)
    exact (not_not.mp hnF) f

end
end SKGap.FullMain

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SKGap.FullMain
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology BigOperators ENNReal
open GaussianStep GaussianHistory ObservationBridge SKGapCutoff.Recipe SKGapCutoff.Static
noncomputable section

lemma whp_of_measurable_full {β : ℝ} (Ω : ∀n,Set (Disorder n))
    (hΩ : ∀n,MeasurableSet (Ω n))
    (hfull : Tendsto (fun n=>(disorderLaw β n).real (Ω n)) atTop (𝓝 1)) :
    Whp β (fun n g=>g∈Ω n) := by
  apply (whp_iff_real _ _).mpr
  have H:=(tendsto_const_nhds (x:=(1:ℝ))).sub hfull
  simpa only [sub_self,show ∀n,{g:Disorder n | ¬g∈Ω n}=(Ω n)ᶜ from fun _=>rfl,
    probReal_compl_eq_one_sub (hΩ _)] using H

lemma weighted_accuracy {B C₀ r W : ℝ} (hB : 0≤B) (hC₀ : 0≤C₀) (hr : 0 < r) (hW : 0<W) :
    ∃ρ:ℝ,0<ρ ∧ B*ρ < r ∧ 4*C₀*ρ≤W := by
  let ρ:=min (r/(2*(B+1))) (W/(2*(4*C₀+1)))
  have hρ : 0<ρ:=lt_min (by positivity) (by positivity)
  have hleft0 : ρ ≤ r/(2*(B+1)) := min_le_left _ _
  have hleft := (le_div_iff₀ (show 0 < 2*(B+1) by positivity)).mp hleft0
  have hright0 : ρ ≤ W/(2*(4*C₀+1)) := min_le_right _ _
  have hright := (le_div_iff₀ (show 0 < 2*(4*C₀+1) by positivity)).mp hright0
  refine ⟨ρ,hρ,?_,?_⟩
  · nlinarith [mul_nonneg hB hρ.le]
  · nlinarith [mul_nonneg hC₀ hρ.le]

lemma exponential_pair_eventually {a d : ℝ} (ha : 0<a) (hd : 0<d) :
    ∀ᶠ n:ℕ in atTop,exp (-a*(n:ℝ))+exp (-d*(n:ℝ))≤exp (-(min a d/2)*(n:ℝ)) := by
  have hm : 0 < min a d := lt_min ha hd
  filter_upwards [constant_exp_absorb 2 hm] with n hn
  calc
    _≤exp (-(min a d)*(n:ℝ))+exp (-(min a d)*(n:ℝ)) :=
      add_le_add (exp_le_exp.mpr (by
        have H := mul_le_mul_of_nonneg_right (min_le_left a d) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
        nlinarith))
        (exp_le_exp.mpr (by
          have H := mul_le_mul_of_nonneg_right (min_le_right a d) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
          nlinarith))
    _=2*exp (-(min a d)*(n:ℝ)):=by ring
    _≤_:=hn

theorem quenched_poincare {β : ℝ} (hβ : 0<β) (hβ1 : β<1) :
    ∃C:ℝ,0<C ∧ Whp β (fun n g=>∀f:Spin n→ℝ,variance g 0 f≤C*dirichlet g 0 f) := by
  obtain ⟨T,aT,hT,haT,Ω,hΩ,hΩfull,hterminal⟩:=terminal_gap_high_probability hβ
  obtain ⟨Ar,K,ε,c,r₀,a,hAr,hK,hs,hε,hc,hr₀,ha,hroot⟩:=quenched_grid_root_stability hβ hβ1 hT
  obtain ⟨D₀,hD₀,hcov⟩:=quenched_posterior_covariance hβ hβ1 hAr hs hε hc hr₀
  let b:=min a aT/2
  have hb : 0<b:=half_pos (lt_min ha haT)
  obtain ⟨W,hW,hnum⟩:=localization_numeric_choice (D₀^2) 2 T a b hT hb
  let P:=physicalNormBound (β^2)
  let C₀:=(1+(P+3*β^2)/c)*(P+4*β^2)
  have hP : 0≤P:=(physicalNormBound_pos (β^2)).le
  have hC₀ : 0≤C₀:=by dsimp [C₀]; positivity
  obtain ⟨ρ,hρ,hbuffer,hlead⟩:=weighted_accuracy (B:=P+4*β^2) (by positivity) hC₀ hr₀ hW
  obtain ⟨Cmean,hCmean,hmean⟩:=disorder_stable_square_mean hβ hβ1 hc hr₀ ρ hρ hbuffer
  let C:=2*(D₀^2*T+3)/exp (-2*D₀^2*T)
  have hC : 0<C:=by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  have hevents:=(((whp_of_measurable_full Ω hΩ hΩfull).and hroot).and hcov).and
    (show Whp β (fun n g=>StableSquareMeanProperty (β^2) c r₀ ρ C₀ Cmean (coupling g)) from hmean)
  apply hevents.mono
  filter_upwards [hnum (2*Cmean),exponential_pair_eventually ha haT] with n hn hr
  intro g hg
  rcases hg with ⟨⟨⟨hgΩ,hgr⟩,hgc⟩,hgm⟩
  rcases hn with ⟨hn,hmesh,hmeshD,hloss,hcost⟩
  have hcost' : localizationCost n (2*Cmean) a b (D₀^2) 2 T≤D₀^2*T+3 := by
    convert hcost using 1 <;> first | rfl | ring
  exact poincare_from_model_data g hn (β^2) Ar K ε c r₀ ρ C₀ Cmean D₀ W a aT b T
    hAr.le hD₀ hW.le hCmean ha hb hT hlead hgr.1 hgr.2 (hterminal n g hgΩ) hgc hgm hr
    hmesh hmeshD hloss hcost'

end
end SKGap.FullMain

namespace SKGap
open MeasureTheory ProbabilityTheory Filter Real Set
open scoped Topology

theorem sk_main_oai (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) : MainStatement β := by
  obtain ⟨C,hC,hwhp⟩:=FullMain.quenched_poincare hβ0 hβ1
  have hP : Tendsto (fun n:ℕ=>disorderLaw β n (poincareEvent n C)) atTop (𝓝 1):=
    FullMain.whp_full_probability hwhp
  exact ⟨C,hC,hP,gap_probability_of_poincare β C hC hP⟩

end SKGap

end OAI
end

theorem solution : type_of% @OAI.SKGap.sk_main_oai := @OAI.SKGap.sk_main_oai

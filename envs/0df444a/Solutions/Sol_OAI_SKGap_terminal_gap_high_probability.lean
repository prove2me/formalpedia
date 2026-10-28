-- Prove2me | solution 1 for OAI.SKGap.terminal_gap_high_probability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:52:25.901578+00:00
-- url     : https://prove2.me/submissions/da2d5662-49eb-4701-88ca-e525d96fb84f

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_OAIQ072A000
import Theorems.Thm_OAI_SKGap_terminalMatrixData_actual_whp

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

theorem expectation_add (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x + k x) = expectation g h f + expectation g h k := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x - k x) = expectation g h f - expectation g h k := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => f x * c) = expectation g h f * c := by
  simp only [expectation, Finset.sum_mul, mul_assoc]

theorem expectation_const_mul (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => c * f x) = c * expectation g h f := by
  simp only [mul_comm c, expectation_mul_const]

theorem expectation_nonneg (g : Disorder n) (h : Fin n → ℝ) {f : Spin n → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectation g h f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg g h x) (hf x))

theorem dirichlet_nonneg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    0 ≤ dirichlet g h f :=
  Finset.sum_nonneg (fun _ _ => expectation_nonneg g h (fun _ => sq_nonneg _))

end FiniteSpinCalculus

end SKGap

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

lemma matrixOperator_apply (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) (i : ι) :
    matrixOperator M p i = ∑ k, M i k * p k := by
  rfl

lemma matrixQuad_inner (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) :
    matrixQuad M p = inner ℝ p (matrixOperator M p) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, matrixOperator_apply,
    matrixQuad, Finset.sum_mul]
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
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOESubmatrix
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators RealInnerProductSpace
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma continuous_matrixOperator [DecidableEq ι] : Continuous (matrixOperator (ι:=ι)) := by
  let L : Matrix ι ι ℝ →ₗ[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
    { toFun := matrixOperator
      map_add' := by intro A B;ext x i;simp [matrixOperator_apply,Finset.sum_add_distrib,add_mul]
      map_smul' := by intro c A;ext x i;simp [matrixOperator_apply,Finset.mul_sum,mul_assoc] }
  exact L.continuous_of_finiteDimensional

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrixOperator_eq_toEuclideanCLM (M : Matrix ι ι ℝ) :
    matrixOperator M=Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=ι) M := by
  ext x i
  rfl
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOESparse
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
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma supported_quad_eq (M : Matrix ι ι ℝ) (S : Finset ι)
    (w : EuclideanSpace ℝ ι) (hw : ∀ i,i ∉ S → w i=0) :
    matrixQuad M w=matrixQuad (M.submatrix (fun i : S=>i.1) (fun i : S=>i.1))
      (WithLp.toLp 2 (fun i : S=>w i.1)) := by
  change (∑ i,∑ k,w i*M i k*w k)=(∑ i : S,∑ k : S,w i.1*M i.1 k.1*w k.1)
  calc
    _ = ∑ i∈S,∑ k,w i*M i k*w k := (Finset.sum_subset (Finset.subset_univ S) (by
      intro i _ hi
      simp [hw i hi])).symm
    _ = ∑ i : S,∑ k,w i.1*M i.1 k*w k :=
      (Finset.sum_coe_sort S (fun i=>∑ k,w i*M i k*w k)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_coe_sort S (fun k=>w i.1*M i.1 k*w k)]
      exact (Finset.sum_subset (Finset.subset_univ S) (by
        intro k _ hk
        simp [hw k hk])).symm

omit [DecidableEq ι] in
lemma supported_norm_sq_eq (S : Finset ι) (w : EuclideanSpace ℝ ι)
    (hw : ∀ i,i ∉ S → w i=0) :
    ‖WithLp.toLp 2 (fun i : S=>w i.1)‖^2=‖w‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i : S,w i.1^2)=(∑ i,w i^2)
  rw [Finset.sum_coe_sort S (fun i=>w i^2)]
  exact Finset.sum_subset (Finset.subset_univ S) (by intro i _ hi;simp [hw i hi])

lemma supported_quad_le_principal (M : Matrix ι ι ℝ) (S : Finset ι) {ε : ℝ}
    (hM : principalOperatorNorm M S ≤ ε) (w : EuclideanSpace ℝ ι)
    (hw : ∀ i,i ∉ S → w i=0) :
    |⟪w,Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=ι) M w⟫| ≤ ε*‖w‖^2 := by
  rw [← matrixOperator_eq_toEuclideanCLM,← matrixQuad_inner,supported_quad_eq M S w hw,matrixQuad_inner]
  let v := WithLp.toLp 2 (fun i : S=>w i.1)
  calc
    _ ≤ ‖v‖*‖matrixOperator (M.submatrix (fun i : S=>i.1) (fun i : S=>i.1)) v‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖v‖*(principalOperatorNorm M S*‖v‖) :=
      mul_le_mul_of_nonneg_left ((matrixOperator _).le_opNorm v) (norm_nonneg v)
    _ ≤ ‖v‖*(ε*‖v‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hM (norm_nonneg v)) (norm_nonneg v)
    _ = ε*‖w‖^2 := by
      rw [show ‖v‖*(ε*‖v‖)=ε*‖v‖^2 by ring,supported_norm_sq_eq S w hw]
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TAPScalarTaylor
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set

lemma tanh_lipschitz_abs (x y : ℝ) : |tanh x-tanh y| ≤ |x-y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ (univ : Set ℝ)) => (hasDerivAt_tanh z).hasDerivWithinAt)
    (C := 1) (fun z _ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (tanh_sq_lt_one z).le)]
      linarith [sq_nonneg (tanh z)]) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs,one_mul] using hh

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_TanhCubic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set

lemma abs_tanh_le_abs (x : ℝ) : |tanh x| ≤ |x| := by
  simpa only [tanh_zero,sub_zero] using tanh_lipschitz_abs x 0

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalMatrixTransfer
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma conditionalExpectation_flip (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f (flip i x)=conditionalExpectation g h i f x := by
  simp only [conditionalExpectation,flip_flip]
  rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma conditionalExpectation_idem (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (conditionalExpectation g h i f) x=conditionalExpectation g h i f x := by
  unfold conditionalExpectation at *
  rw [flip_flip]
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hd' : weight g h (flip i x)+weight g h x ≠ 0 := by simpa only [add_comm] using hd
  field_simp [hd,hd']
  ring

lemma expectation_flip_average (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (F : Spin n→ℝ) :
    expectation g h F=(1/2)*∑ x,(mass g h x*F x+mass g h (flip i x)*F (flip i x)) := by
  rw [Finset.sum_add_distrib,sum_flip i (fun x=>mass g h x*F x)]
  unfold expectation
  ring

lemma conditionalExpectation_adjoint (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) :
    expectation g h (fun x=>conditionalExpectation g h i f x*k x)=
    expectation g h (fun x=>f x*conditionalExpectation g h i k x) := by
  rw [expectation_flip_average g h i,expectation_flip_average g h i]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [conditionalExpectation_flip,conditionalExpectation_flip]
  unfold mass conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hZ := (partition_pos g h).ne'
  field_simp [hd,hZ]

lemma conditionalExpectation_const (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (x : Spin n) : conditionalExpectation g h i (fun _=>c) x=c := by
  unfold conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  field_simp [hd]

lemma expectation_conditionalExpectation (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) : expectation g h (conditionalExpectation g h i f)=expectation g h f := by
  have he := conditionalExpectation_adjoint g h i f (fun _=>1)
  simpa only [conditionalExpectation_const,mul_one] using he

lemma expectation_projection_square (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>f x*(f x-conditionalExpectation g h i f x)) := by
  have he := conditionalExpectation_adjoint g h i f (conditionalExpectation g h i f)
  simp only [conditionalExpectation_idem] at he
  have hp (x : Spin n) : (f x-conditionalExpectation g h i f x)^2=
      f x*(f x-conditionalExpectation g h i f x)+
      (conditionalExpectation g h i f x*conditionalExpectation g h i f x-
        f x*conditionalExpectation g h i f x) := by ring
  simp_rw [hp]
  rw [expectation_add,expectation_sub,he]
  ring

lemma expectation_sum (g : Disorder n) (h : Fin n→ℝ) {ι : Type*} [Fintype ι]
    (F : ι→Spin n→ℝ) : expectation g h (fun x=>∑ i,F i x)=∑ i,expectation g h (F i) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma heatBathGenerator_form (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>f x*heatBathGenerator g h f x)=dirichlet g h f := by
  unfold heatBathGenerator dirichlet
  simp_rw [Finset.mul_sum]
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (expectation_projection_square g h i f).symm

lemma heatBathGenerator_adjoint (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x*k x)=
      expectation g h (fun x=>f x*heatBathGenerator g h k x) := by
  unfold heatBathGenerator
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [expectation_sum,expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [sub_mul,mul_sub]
  rw [expectation_sub,expectation_sub,conditionalExpectation_adjoint]

lemma conditionalDifference_zero_iff (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) : f x-conditionalExpectation g h i f x=0 ↔ f x=f (flip i x) := by
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hw := (weight_pos g h (flip i x)).ne'
  unfold conditionalExpectation
  rw [sub_eq_zero,eq_div_iff hd]
  constructor
  · intro hh
    have he : weight g h (flip i x)*(f x-f (flip i x))=0 := by nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hw)
  · intro hh
    rw [hh]
    ring

lemma flip_invariant_constant (f : Spin n→ℝ) (hf : ∀ i x,f (flip i x)=f x) :
    ∀ x y,f x=f y := by
  classical
  intro x y
  have hs : ∀ S : Finset (Fin n),f (fun i=>if i∈S then y i else x i)=f x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      let z : Spin n := fun k=>if k∈S then y k else x k
      have he : (fun k=>if k∈insert i S then y k else x k)=Function.update z i (y i) := by
        funext k
        by_cases hk : k=i
        · subst k;simp
        · simp [z,hk]
      rw [he]
      have hz : f (Function.update z i (y i))=f z := by
        by_cases hiy : y i=z i
        · rw [hiy,Function.update_eq_self]
        · have hnot : y i= !(z i) := by
            cases hy : y i <;> cases hz : z i <;> simp_all
          rw [hnot]
          exact hf i z
      exact hz.trans ih
  simpa using (hs Finset.univ).symm

lemma dirichlet_eq_zero_iff (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hh
    have hi : ∀ i,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _=>expectation_nonneg g h (fun _=>sq_nonneg _))).mp hh i (Finset.mem_univ _)
    have hf : ∀ i x,f (flip i x)=f x := by
      intro i x
      have hx : mass g h x*(f x-conditionalExpectation g h i f x)^2=0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun y _=>mul_nonneg (mass_nonneg g h y) (sq_nonneg _))).mp
          (hi i) x (Finset.mem_univ _)
      have hd := (mul_eq_zero.mp hx).resolve_left (mass_pos g h x).ne'
      exact ((conditionalDifference_zero_iff g h i f x).mp (sq_eq_zero_iff.mp hd)).symm
    exact flip_invariant_constant f hf
  · intro hf
    unfold dirichlet
    apply Finset.sum_eq_zero
    intro i _
    have he : ∀ x,f x-conditionalExpectation g h i f x=0 := fun x=>(conditionalDifference_zero_iff g h i f x).mpr (hf x (flip i x))
    simp only [he,zero_pow (by omega : (2:ℕ) ≠ 0)]
    simp [expectation]
end SKGap

end
end

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_SparseQuadratic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Real
open scoped RealInnerProductSpace
namespace SKGap

lemma norm_product_le_sqrt {E : Type*} [SeminormedAddCommGroup E]
    (b c : E) {q η : ℝ} (hq : 0 ≤ q) (hη : 0 ≤ η)
    (hb : ‖b‖^2 ≤ q) (hc : ‖c‖^2 ≤ η*q) : ‖b‖*‖c‖ ≤ sqrt η*q := by
  have hs := sq_sqrt hη
  have hh := mul_le_mul hb hc (sq_nonneg ‖c‖) hq
  have hplus : 0 ≤ sqrt η*q := mul_nonneg (sqrt_nonneg η) hq
  have hnorm : 0 ≤ ‖b‖*‖c‖ := mul_nonneg (norm_nonneg b) (norm_nonneg c)
  apply (sq_le_sq₀ hnorm hplus).mp
  calc
    (‖b‖*‖c‖)^2=‖b‖^2*‖c‖^2 := by ring
    _ ≤ q*(η*q) := hh
    _ = (sqrt η*q)^2 := by rw [mul_pow,hs];ring

lemma sparse_quadratic_split {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E →L[ℝ] E) (b c : E)
    {q η ε M : ℝ} (hq : 0 ≤ q) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hB : ‖B‖ ≤ M) (hb : ‖b‖^2 ≤ q) (hc : ‖c‖^2 ≤ η*q)
    (hs : |⟪b,B b⟫| ≤ ε*q) :
    |⟪b+c,B (b+c)⟫| ≤ (ε+M*(2*sqrt η+η))*q := by
  have hbound (u v : E) : |⟪u,B v⟫| ≤ M*‖u‖*‖v‖ := by
    calc
      _ ≤ ‖u‖*‖B v‖ := abs_real_inner_le_norm u (B v)
      _ ≤ ‖u‖*(‖B‖*‖v‖) := mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg u)
      _ ≤ ‖u‖*(M*‖v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hB (norm_nonneg v)) (norm_nonneg u)
      _ = _ := by ring
  have hprod := norm_product_le_sqrt b c hq hη hb hc
  have hbc : |⟪b,B c⟫| ≤ M*(sqrt η*q) := by
    calc
      _ ≤ M*(‖b‖*‖c‖) := by simpa only [mul_assoc] using hbound b c
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod hM
  have hcb : |⟪c,B b⟫| ≤ M*(sqrt η*q) := by
    calc
      _ ≤ M*(‖b‖*‖c‖) := by simpa only [mul_comm,mul_left_comm,mul_assoc] using hbound c b
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod hM
  have hcc : |⟪c,B c⟫| ≤ M*(η*q) := by
    calc
      _ ≤ M*‖c‖^2 := by simpa only [sq,mul_assoc] using hbound c c
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hM
  rw [map_add,inner_add_left,inner_add_right,inner_add_right]
  calc
    _ ≤ (|⟪b,B b⟫|+|⟪b,B c⟫|)+(|⟪c,B b⟫|+|⟪c,B c⟫|) :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ (ε*q+M*(sqrt η*q))+(M*(sqrt η*q)+M*(η*q)) :=
      add_le_add (add_le_add hs hbc) (add_le_add hcb hcc)
    _ = _ := by ring
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_SparseWeightedForm
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
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_square_le {v z : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    (v*z)^2 ≤ v*z^2 := by
  have hh := mul_le_mul_of_nonneg_left hv1 hv
  have h := mul_le_mul_of_nonneg_right hh (sq_nonneg z)
  nlinarith only [h]

lemma weighted_square_le_small {v z η : ℝ} (hv : 0 ≤ v) (hvη : v ≤ η) :
    (v*z)^2 ≤ η*(v*z^2) := by
  have hh := mul_le_mul_of_nonneg_left hvη hv
  have h := mul_le_mul_of_nonneg_right hh (sq_nonneg z)
  nlinarith only [h]

lemma weighted_sparse_form (B : Matrix ι ι ℝ) (S : Finset ι) (v z : ι→ℝ)
    {η ε M : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (hM : 0 ≤ M)
    (hv : ∀ i,0 ≤ v i) (hv1 : ∀ i,v i ≤ 1) (hsmall : ∀ i,i ∉ S → v i ≤ η)
    (hB : ‖B‖ ≤ M)
    (hs : ∀ w : EuclideanSpace ℝ ι,(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B w⟫| ≤ ε*‖w‖^2) :
    |∑ i,∑ j,B i j*(v i*z i)*(v j*z j)| ≤
      (ε+M*(2*sqrt η+η))*(∑ i,v i*z i^2) := by
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i=>if i ∈ S then v i*z i else 0)
  let c : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i=>if i ∈ S then 0 else v i*z i)
  let q := ∑ i,v i*z i^2
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _=>mul_nonneg (hv i) (sq_nonneg _))
  have hb : ‖b‖^2 ≤ q := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    change (if i ∈ S then v i*z i else 0)^2 ≤ v i*z i^2
    split_ifs
    · exact weighted_square_le (hv i) (hv1 i)
    · exact (by simpa only [zero_pow (by omega : (2:ℕ) ≠ 0)] using mul_nonneg (hv i) (sq_nonneg (z i)))
  have hc : ‖c‖^2 ≤ η*q := by
    rw [EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change (if i ∈ S then 0 else v i*z i)^2 ≤ η*(v i*z i^2)
    split_ifs with hi
    · exact (by simpa only [zero_pow (by omega : (2:ℕ) ≠ 0)] using mul_nonneg hη (mul_nonneg (hv i) (sq_nonneg (z i))))
    · exact weighted_square_le_small (hv i) (hsmall i hi)
  have hsb : |⟪b,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B b⟫| ≤ ε*q := by
    apply (hs b (by intro i hi;change (if i ∈ S then v i*z i else 0)=0;simp [hi])).trans
    exact mul_le_mul_of_nonneg_left hb hε
  have hh := sparse_quadratic_split (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) B) b c hq hη hM
    (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hB) hb hc hsb
  have hbc : b+c=WithLp.toLp 2 (fun i=>v i*z i) := by
    ext i
    change (if i ∈ S then v i*z i else 0)+(if i ∈ S then 0 else v i*z i)=v i*z i
    split_ifs <;> simp
  rw [hbc,Matrix.inner_toEuclideanCLM] at hh
  have he : (WithLp.toLp 2 (fun i=>v i*z i) : EuclideanSpace ℝ ι) ⬝ᵥ
      B *ᵥ (WithLp.toLp 2 (fun i=>v i*z i) : EuclideanSpace ℝ ι)=
      ∑ i,∑ j,B i j*(v i*z i)*(v j*z j) := by
    simp only [dotProduct,Matrix.mulVec]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _;ring
  rwa [he] at hh
end SKGap

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
-- module Solutions.OAIQ072_SK.SKGap_Localization_RareCoordinate
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

lemma gaussian_standard_subgaussian : HasSubgaussianMGF (fun x : ℝ=>x) 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    change mgf id (gaussianReal 0 1) t ≤ _
    rw [mgf_id_gaussianReal]
    simp

lemma gaussian_observation_small {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s=1 ∨ s= -1) :
    (gaussianReal 0 1).real {z : ℝ | |T*s+sqrt T*z| < T/2} ≤ exp (-T/8) := by
  have ht : 0 < sqrt T := sqrt_pos.mpr hT
  have ht2 := sq_sqrt hT.le
  rcases hs with rfl | rfl
  · have hsub : {z : ℝ | |T*1+sqrt T*z| < T/2} ⊆ {z | sqrt T/2 ≤ -z} := by
      intro z hz
      change |T*1+sqrt T*z| < T/2 at hz
      have hz' := (abs_lt.mp hz).2
      have hm : sqrt T/2*sqrt T ≤ -z*sqrt T := by nlinarith only [hz',ht2]
      exact le_of_mul_le_mul_right hm ht
    apply (measureReal_mono hsub (measure_ne_top _ _)).trans
    have hh := gaussian_standard_subgaussian.neg.measure_ge_le (show 0 ≤ sqrt T/2 by positivity)
    have he : -(sqrt T/2)^2/(2*(1:ℝ))= -T/8 := by
      simp only [div_pow,ht2]
      ring
    simpa only [NNReal.coe_one,Pi.neg_apply,he] using hh
  · have hsub : {z : ℝ | |T*(-1)+sqrt T*z| < T/2} ⊆ {z | sqrt T/2 ≤ z} := by
      intro z hz
      change |T*(-1)+sqrt T*z| < T/2 at hz
      have hz' := (abs_lt.mp hz).1
      have hm : sqrt T/2*sqrt T ≤ z*sqrt T := by nlinarith only [hz',ht2]
      exact le_of_mul_le_mul_right hm ht
    apply (measureReal_mono hsub (measure_ne_top _ _)).trans
    have hh := gaussian_standard_subgaussian.measure_ge_le (show 0 ≤ sqrt T/2 by positivity)
    have he : -(sqrt T/2)^2/(2*(1:ℝ))= -T/8 := by
      simp only [div_pow,ht2]
      ring
    simpa only [NNReal.coe_one,he] using hh

variable {ι : Type*} [Fintype ι] {E : ι→Type*} [∀ i,MeasurableSpace (E i)]

lemma rareCount_measurable (B : ∀ i,Set (E i)) (hB : ∀ i,MeasurableSet (B i)) :
    Measurable (rareCount B) := by
  classical
  unfold rareCount
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_const (a:=(1:ℝ))).indicator (hB i)).comp (measurable_pi_apply i)

omit [∀ i,MeasurableSpace (E i)] in
lemma rareCount_bounds (B : ∀ i,Set (E i)) (x : ∀ i,E i) :
    0 ≤ rareCount B x ∧ rareCount B x ≤ Fintype.card ι := by
  classical
  constructor
  · exact Finset.sum_nonneg (fun i _=>by split_ifs <;> norm_num)
  · apply (Finset.sum_le_sum (g:=fun _=>(1:ℝ)) (fun i _=>by split_ifs <;> norm_num)).trans_eq
    simp

lemma rareCount_exp_integral (μ : ∀ i,Measure (E i)) [∀ i,IsProbabilityMeasure (μ i)]
    (B : ∀ i,Set (E i)) (hB : ∀ i,MeasurableSet (B i)) :
    (∫ x,exp (rareCount B x) ∂Measure.pi μ)=∏ i,(1+((μ i).real (B i))*(exp 1-1)) := by
  classical
  have hi (i : ι) : (∫ z,exp (if z∈B i then (1:ℝ) else 0) ∂μ i)=
      1+(μ i).real (B i)*(exp 1-1) := by
    have he : (fun z=>exp (if z∈B i then (1:ℝ) else 0))=
        fun z=>1+(B i).indicator (fun _=>exp 1-1) z := by
      funext z
      by_cases hz : z∈B i <;> simp [hz]
    rw [he,integral_add (integrable_const _) ((integrable_const _).indicator (hB i)),integral_indicator_const _ (hB i)]
    simp
  simp only [rareCount,exp_sum]
  rw [integral_fintype_prod_eq_prod (μ:=μ) (fun i z=>exp (if z∈B i then (1:ℝ) else 0))]
  exact Finset.prod_congr rfl (fun i _=>hi i)

theorem rareCount_tail (μ : ∀ i,Measure (E i)) [∀ i,IsProbabilityMeasure (μ i)]
    (B : ∀ i,Set (E i)) (hB : ∀ i,MeasurableSet (B i))
    {p a : ℝ} (hp : ∀ i,(μ i).real (B i) ≤ p) :
    (Measure.pi μ).real {x | a < rareCount B x} ≤
      exp (-a+(Fintype.card ι:ℝ)*p*(exp 1-1)) := by
  classical
  have hmono : 0 ≤ exp (1:ℝ)-1 := by linarith only [one_le_exp (by norm_num : (0:ℝ) ≤ 1)]
  have hi : Integrable (fun x=>exp (rareCount B x)) (Measure.pi μ) :=
    Integrable.of_bound (rareCount_measurable B hB |>.exp.aestronglyMeasurable)
      (exp (Fintype.card ι:ℝ)) (ae_of_all _ (fun x=>by
        rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (rareCount_bounds B x).2))
  have hm := mul_meas_ge_le_integral_of_nonneg (μ:=Measure.pi μ)
    (ae_of_all _ (fun x=>(exp_pos (rareCount B x)).le)) hi (exp a)
  rw [rareCount_exp_integral μ B hB] at hm
  have hset : {x | a < rareCount B x} ⊆ {x | exp a ≤ exp (rareCount B x)} :=
    fun _ hx=>exp_le_exp.mpr hx.le
  have hh := measureReal_mono hset (measure_ne_top (Measure.pi μ) _)
  have hprod : (∏ i,(1+(μ i).real (B i)*(exp 1-1))) ≤
      exp ((Fintype.card ι:ℝ)*p*(exp 1-1)) := by
    have hp' (i : ι) : 1+(μ i).real (B i)*(exp 1-1) ≤ exp (p*(exp 1-1)) := by
      calc
        _ ≤ 1+p*(exp 1-1) := add_le_add_right (mul_le_mul_of_nonneg_right (hp i) hmono) 1
        _ ≤ _ := by linarith only [add_one_le_exp (p*(exp 1-1))]
    calc
      _ ≤ ∏ _i : ι,exp (p*(exp 1-1)) := Finset.prod_le_prod
        (fun i _=>add_nonneg (by norm_num) (mul_nonneg (measureReal_nonneg) hmono)) (fun i _=>hp' i)
      _ = _ := by rw [Finset.prod_const,Finset.card_univ,← exp_nat_mul];congr 1;ring
  have hm' := (mul_le_mul_of_nonneg_left hh (exp_pos a).le).trans (hm.trans hprod)
  have he : exp (-a+(Fintype.card ι:ℝ)*p*(exp 1-1))=
      exp ((Fintype.card ι:ℝ)*p*(exp 1-1))/exp a := by rw [← exp_sub];congr 1;ring
  rw [he]
  apply (le_div_iff₀ (exp_pos a)).mpr
  simpa only [mul_comm] using hm'
end SKGap

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
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairRationalBounds
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

lemma list_prod_perturb (l : List ℝ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (h : ∀ x∈l,|x-1| ≤ t) :
    |l.prod| ≤ 2^l.length ∧ |l.prod-1| ≤ (2^l.length-1)*t := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx := h x (by simp)
      have hl := ih (fun y hy=>h y (by simp [hy]))
      have hx2 : |x| ≤ 2 := by
        have hh := abs_add_le (x-1) 1
        simp only [sub_add_cancel,abs_one] at hh
        linarith
      have he : x*l.prod-1=(x-1)*l.prod+(l.prod-1) := by ring
      simp only [List.prod_cons,List.length_cons,pow_succ]
      constructor
      · rw [abs_mul]
        exact (mul_le_mul hx2 hl.1 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      · rw [he]
        calc
          _ ≤ |x-1| * |l.prod|+|l.prod-1| := by simpa only [abs_mul] using abs_add_le ((x-1)*l.prod) (l.prod-1)
          _ ≤ t*2^l.length+(2^l.length-1)*t := add_le_add
            (mul_le_mul hx hl.1 (abs_nonneg _) ht) hl.2
          _ = _ := by ring

lemma list_prod_between (l : List ℝ) (h : ∀ x∈l,(1/2:ℝ) ≤ x ∧ x ≤ 2) :
    (1/2:ℝ)^l.length ≤ l.prod ∧ l.prod ≤ (2:ℝ)^l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      have hx := h x (by simp)
      have hl := ih (fun y hy=>h y (by simp [hy]))
      have hl0 : 0 ≤ l.prod := (by positivity : (0:ℝ) ≤ (1/2:ℝ)^l.length).trans hl.1
      simp only [List.prod_cons,List.length_cons,pow_succ]
      constructor
      · exact (by ring : (1/2:ℝ)^l.length*(1/2)=(1/2)*(1/2)^l.length).le.trans
          (mul_le_mul hx.1 hl.1 (by positivity) (by linarith))
      · exact (mul_le_mul hx.2 hl.2 hl0 (by norm_num)).trans_eq (by ring)

lemma pair_factor_control {u z : ℝ} (hu : |u| ≤ 1/4) (hz : |z| ≤ 1) :
    (1/2:ℝ) ≤ 1+u*z ∧ 1+u*z ≤ 2 ∧ |(1+u*z)-1| ≤ |u| := by
  have hh : |u*z| ≤ |u| := by rw [abs_mul];exact (mul_le_mul_of_nonneg_left hz (abs_nonneg u)).trans_eq (mul_one _)
  have hb := abs_le.mp hh
  constructor
  · linarith
  constructor
  · linarith
  simpa only [add_sub_cancel_left] using hh

lemma pair_square_factor_control {u : ℝ} (hu : |u| ≤ 1/4) :
    (1/2:ℝ) ≤ 1-u^2 ∧ 1-u^2 ≤ 2 ∧ |(1-u^2)-1| ≤ |u| := by
  have hs : u^2 ≤ |u| := by nlinarith [sq_abs u,abs_nonneg u]
  have h0 := sq_nonneg u
  constructor
  · linarith
  constructor
  · linarith
  rw [sub_sub_cancel_left,abs_neg,abs_of_nonneg h0]
  exact hs

lemma pairRationalWeight_bounds {a b u x y : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    1/256 ≤ pairRationalWeight a b u x y ∧
    pairRationalWeight a b u x y ≤ 256 ∧
    |pairRationalWeight a b u x y-1| ≤ 1216*|u| := by
  have hab : |a*b| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul ha hb (abs_nonneg b) (by norm_num : (0:ℝ) ≤ 1)
  have hay : |a*y| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul ha hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)
  have hbx : |b*x| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul hb hx (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 1)
  have hxy : |x*y| ≤ 1 := by simpa only [one_mul,abs_mul] using mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 1)
  have h₀ := pair_square_factor_control hu
  have h₁ := pair_factor_control hu hab
  have h₂ := pair_factor_control hu hay
  have h₃ := pair_factor_control hu hbx
  have h₄ := pair_factor_control hu hxy
  let ln : List ℝ := [1-u^2,1-u^2,1+u*(x*y)]
  let ld : List ℝ := [1+u*(a*b),1+u*(a*y),1+u*(a*y),1+u*(b*x),1+u*(b*x)]
  have hn : ∀ z∈ln, (1/2:ℝ) ≤ z ∧ z ≤ 2 := by
    intro z hz
    simp only [ln,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> exact ⟨by grind,by grind⟩
  have hd : ∀ z∈ld, (1/2:ℝ) ≤ z ∧ z ≤ 2 := by
    intro z hz
    simp only [ld,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> exact ⟨by grind,by grind⟩
  have hn' : ∀ z∈ln, |z-1| ≤ |u| := by
    intro z hz
    simp only [ln,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> grind
  have hd' : ∀ z∈ld, |z-1| ≤ |u| := by
    intro z hz
    simp only [ld,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> grind
  have hnb := list_prod_between ln hn
  have hdb := list_prod_between ld hd
  have hnp := (list_prod_perturb ln (abs_nonneg u) (by linarith) hn').2
  have hdp := (list_prod_perturb ld (abs_nonneg u) (by linarith) hd').2
  have hnl : ln.length=3 := rfl
  have hdl : ld.length=5 := rfl
  rw [hnl] at hnb hnp
  rw [hdl] at hdb hdp
  norm_num only at hnb hdb hnp hdp
  have hd0 : 0 < ld.prod := by linarith [hdb.1]
  have he : pairRationalWeight a b u x y=ln.prod/ld.prod := by
    unfold pairRationalWeight ln ld
    simp only [List.prod_cons,List.prod_nil,mul_one]
    congr 1 <;> ring
  rw [he]
  constructor
  · apply (le_div_iff₀ hd0).mpr
    nlinarith [hnb.1,hdb.2]
  constructor
  · apply (div_le_iff₀ hd0).mpr
    nlinarith [hnb.2,hdb.1]
  rw [div_sub_one (ne_of_gt hd0),abs_div,abs_of_pos hd0]
  apply (div_le_iff₀ hd0).mpr
  have hh : |ln.prod-ld.prod| ≤ 38*|u| := by
    have hh := abs_sub_le (ln.prod-1) 0 (ld.prod-1)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    simpa only [sub_sub_sub_cancel_right] using (hh.trans (add_le_add hnp hdp)).trans_eq (by ring)
  have hm := mul_le_mul_of_nonneg_left hdb.1 (show 0 ≤ 1216*|u| by positivity)
  nlinarith only [hh,hm]
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real

lemma abs_mul_le_one_pair {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : |x*y| ≤ 1 := by
  rw [abs_mul]
  exact (mul_le_mul hx hy (abs_nonneg _) (by norm_num)).trans_eq (by ring)

lemma pairK_bounds {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairK a b u-1| ≤ 64*|u| ∧ 9/10 ≤ pairK a b u ∧ pairK a b u ≤ 2 := by
  have hu4 : |u| ≤ 1/4 := by linarith only [hu]
  have hua : |u| ≤ 1 := by linarith only [hu]
  have ha2 : |a^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair ha ha
  have hb2 : |b^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair hb hb
  have h₁ := pair_factor_control hu4 (abs_mul_le_one_pair ha hb)
  have h₂ := pair_factor_control hu4 (show |-u*a^2| ≤ 1 by simpa only [abs_neg,abs_mul] using abs_mul_le_one_pair hua ha2)
  have h₃ := pair_factor_control hu4 (show |-u*b^2| ≤ 1 by simpa only [abs_neg,abs_mul] using abs_mul_le_one_pair hua hb2)
  have he₂ : 1+u*(-u*a^2)=1-u^2*a^2 := by ring
  have he₃ : 1+u*(-u*b^2)=1-u^2*b^2 := by ring
  rw [he₂] at h₂
  rw [he₃] at h₃
  let l : List ℝ := [1+u*(a*b),1-u^2*a^2,1-u^2*b^2]
  have hl : ∀ z∈l,(1/2:ℝ) ≤ z ∧ z ≤ 2 := by
    intro z hz
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> grind
  have hl' : ∀ z∈l,|z-1| ≤ |u| := by
    intro z hz
    simp only [l,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> grind
  have hlen : l.length=3 := rfl
  have hbounds := list_prod_between l hl
  have hperturb := (list_prod_perturb l (abs_nonneg u) hua hl').2
  rw [hlen] at hbounds hperturb
  norm_num only at hbounds hperturb
  have hd : 0 < l.prod := by linarith only [hbounds.1]
  have he : pairK a b u=(1-u^2)/l.prod := by
    unfold pairK l
    simp only [List.prod_cons,List.prod_nil,mul_one]
    congr 1; ring
  have hs : u^2 ≤ |u| := by nlinarith only [sq_abs u,abs_nonneg u,hu]
  have hp : |pairK a b u-1| ≤ 64*|u| := by
    rw [he,div_sub_one hd.ne',abs_div,abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hh : |1-u^2-l.prod| ≤ 8*|u| := by
      have hh := abs_add_le (-u^2) (1-l.prod)
      rw [abs_neg,abs_of_nonneg (sq_nonneg u),abs_sub_comm] at hh
      have he' : 1-u^2-l.prod= -u^2+(1-l.prod) := by ring
      rw [he']
      linarith only [hh,hs,hperturb]
    have hm := mul_le_mul_of_nonneg_left hbounds.1 (show 0 ≤ 64*|u| by positivity)
    nlinarith only [hh,hm]
  refine ⟨hp,?_,?_⟩ <;> have hh := abs_le.mp hp <;> linarith only [hu,hh.1,hh.2]

lemma pairR_bounds {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairR a b u-1| ≤ 5*|u| ∧ 9/10 ≤ pairR a b u := by
  have hua : |u| ≤ 1 := by linarith only [hu]
  have ha2 : |a^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair ha ha
  have hb2 : |b^2| ≤ 1 := by simpa only [pow_two] using abs_mul_le_one_pair hb hb
  have hab := abs_mul_le_one_pair ha hb
  have hab2 := abs_mul_le_one_pair ha2 hb2
  have hz : |a^2*b^2-a^2-b^2| ≤ 3 := by
    have h₁ := abs_sub_le (a^2*b^2) 0 (a^2)
    have h₂ := abs_sub_le (a^2*b^2-a^2) 0 (b^2)
    simp only [sub_zero,zero_sub,abs_neg] at h₁ h₂
    linarith only [h₁,h₂,ha2,hb2,hab2]
  have hs : u^2 ≤ |u| := by nlinarith only [sq_abs u,abs_nonneg u,hu]
  have hu3 : |u^3| ≤ |u| := by
    rw [pow_succ,abs_mul,abs_of_nonneg (sq_nonneg u)]
    have h' := mul_le_mul_of_nonneg_right hs (abs_nonneg u)
    nlinarith only [h',sq_abs u,hs]
  have h₁ : |u*a*b| ≤ |u| := by
    rw [mul_assoc,abs_mul]
    exact (mul_le_mul_of_nonneg_left hab (abs_nonneg u)).trans_eq (mul_one _)
  have h₂ : |u^2*(a^2*b^2-a^2-b^2)| ≤ 3*|u| := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg u)]
    have hh := mul_le_mul_of_nonneg_left hz (sq_nonneg u)
    nlinarith only [hh,hs]
  have h₃ : |u^3*a*b| ≤ |u| := by
    rw [mul_assoc,abs_mul]
    exact (mul_le_mul hu3 hab (abs_nonneg _) (abs_nonneg u)).trans_eq (mul_one _)
  have hp : |pairR a b u-1| ≤ 5*|u| := by
    have hh := abs_add_le (u*a*b) (u^2*(a^2*b^2-a^2-b^2))
    have hh' := abs_sub_le (u*a*b+u^2*(a^2*b^2-a^2-b^2)) 0 (u^3*a*b)
    simp only [sub_zero,zero_sub,abs_neg] at hh'
    have he : pairR a b u-1=u*a*b+u^2*(a^2*b^2-a^2-b^2)-u^3*a*b := by unfold pairR;ring
    rw [he]
    linarith only [hh,hh',h₁,h₂,h₃]
  exact ⟨hp,by have hh := (abs_le.mp hp).1;linarith only [hh,hu]⟩

lemma pairKR_lower {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    1/2 ≤ pairK a b u*pairR a b u := by
  have h₁ := (pairK_bounds ha hb hu).2.1
  have h₂ := (pairR_bounds ha hb hu).2
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_SpinLocalField
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {n : ℕ}

lemma realSpinEnergy_eq (g : Disorder n) (h : Fin n→ℝ) (x : Spin n) :
    realSpinEnergy g h (fun i=>spinValue (x i))=hamiltonian g h x := by
  unfold realSpinEnergy hamiltonian
  congr 1
  congr 1
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _;ring

lemma dot_coupling_single (g : Disorder n) (v : Fin n→ℝ) (i : Fin n) (a : ℝ) :
    v ⬝ᵥ (Matrix.of (coupling g) *ᵥ Pi.single i a)=a*(Matrix.of (coupling g) *ᵥ v) i := by
  rw [Matrix.mulVec_single]
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
  simp only [Pi.smul_apply,op_smul_eq_mul,Matrix.col_apply,Matrix.of_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [coupling_symm g k i]
  ring

lemma realSpinEnergy_update (g : Disorder n) (h v : Fin n→ℝ) (i : Fin n) (a : ℝ) :
    realSpinEnergy g h (Function.update v i a)=realSpinEnergy g h v+
      (a-v i)*(h i+(Matrix.of (coupling g) *ᵥ v) i) := by
  have he : Function.update v i a=v+Pi.single i (a-v i) := by
    funext k
    by_cases hk : k=i
    · subst k;simp
    · simp [hk]
  rw [he]
  unfold realSpinEnergy
  rw [Matrix.mulVec_add,dotProduct_add,add_dotProduct,add_dotProduct,dotProduct_add,
    dot_coupling_single,single_dotProduct,single_dotProduct,dotProduct_single,Matrix.mulVec_single]
  simp only [Pi.smul_apply,op_smul_eq_mul,Matrix.col_apply,Matrix.of_apply,coupling_diag,zero_mul]
  ring

lemma spinValue_update (x : Spin n) (i : Fin n) (b : Bool) :
    (fun k=>spinValue (Function.update x i b k))=Function.update (fun k=>spinValue (x k)) i (spinValue b) := by
  funext k
  by_cases hk : k=i
  · subst k;simp
  · simp [Function.update_of_ne hk]

lemma hamiltonian_update (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    hamiltonian g h (Function.update x i b)=hamiltonian g h x+
      (spinValue b-spinValue (x i))*localField g h i x := by
  rw [← realSpinEnergy_eq,spinValue_update,realSpinEnergy_update,realSpinEnergy_eq]
  rfl

lemma localField_update_self (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    localField g h i (Function.update x i b)=localField g h i x := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=i
  · subst k;simp
  · simp [Function.update_of_ne hk]

lemma localField_update (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (x : Spin n) (b : Bool) :
    localField g h i (Function.update x j b)=localField g h i x+
      coupling g i j*(spinValue b-spinValue (x j)) := by
  unfold localField
  have he : (fun k=>spinValue (Function.update x j b k))=
      (fun k=>spinValue (x k))+Pi.single j (spinValue b-spinValue (x j)) := by
    funext k
    by_cases hk : k=j
    · subst k;simp
    · simp [Function.update_of_ne hk,Pi.single_eq_of_ne hk]
  change h i+(coupling g i ⬝ᵥ (fun k=>spinValue (Function.update x j b k)))=_
  rw [he,dotProduct_add,dotProduct_single]
  exact (add_assoc _ _ _).symm
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

lemma pairMean_explicit (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=((1-a)*(1-b)*F false false+(1-a)*(1+b)*F false true+
      (1+a)*(1-b)*F true false+(1+a)*(1+b)*F true true)/4 := by
  simp only [pairMean,Fintype.sum_bool,pairBaseMass,spinValue,Bool.false_eq_true,
    ite_false,ite_true,mul_neg_one,mul_one]
  ring

lemma pairBaseMass_nonneg {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : Bool) :
    0 ≤ pairBaseMass a b x y := by
  have h₁ := abs_le.mp ha
  have h₂ := abs_le.mp hb
  unfold pairBaseMass
  cases x <;> cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,mul_one,mul_neg_one] <;>
    exact div_nonneg (mul_nonneg (by linarith only [h₁.1,h₁.2]) (by linarith only [h₂.1,h₂.2])) (by norm_num)

lemma pairMean_mono {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    {F G : Bool→Bool→ℝ} (h : ∀ x y,F x y ≤ G x y) : pairMean a b F ≤ pairMean a b G := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (h x y) (pairBaseMass_nonneg ha hb x y)

lemma pairMean_add (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y+G x y)=pairMean a b F+pairMean a b G := by
  simp only [pairMean,mul_add,Finset.sum_add_distrib]
lemma pairMean_sub (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y-G x y)=pairMean a b F-pairMean a b G := by
  simp only [pairMean,mul_sub,Finset.sum_sub_distrib]
lemma pairMean_mul (a b c : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>c*F x y)=c*pairMean a b F := by
  simp only [pairMean,Finset.mul_sum,mul_left_comm]

lemma abs_pairMean_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (F : Bool→Bool→ℝ) : |pairMean a b F| ≤ pairMean a b (fun x y=>|F x y|) := by
  unfold pairMean
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro y _
  rw [abs_mul,abs_of_nonneg (pairBaseMass_nonneg ha hb x y)]

lemma pair_gradient_mean (a b p s r : ℝ) :
    pairMean a b (fun x y=>(p+r*(spinValue y-b))*(s+r*(spinValue x-a)))=p*s := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma pair_gradient_square (a b p r : ℝ) :
    pairMean a b (fun _ y=>(p+r*(spinValue y-b))^2)=p^2+(1-b^2)*r^2 := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma pairMean_swap (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=pairMean b a (fun x y=>F y x) := by
  rw [pairMean_explicit,pairMean_explicit]
  ring

lemma pair_polynomial_cross_mean (a b u c₁ d₁ c₂ d₂ : ℝ) :
    pairMean a b (fun x y=>(spinValue x-a)*(spinValue y-b)*(1-u*spinValue x*spinValue y)*
      (c₁+spinValue y*d₁)*(c₂+spinValue x*d₂))=
      (1-a^2)*(1-b^2)*(d₁*d₂-u*c₁*c₂) := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairCrossIdentity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

lemma pairSign_abs (x : Bool) : |spinValue x|=1 := by cases x <;> norm_num [spinValue]

lemma pairDenominator_pos {u a b : ℝ} (hu : |u| ≤ 1/4) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 < 1+u*a*b := by
  have hh := (pair_factor_control hu (abs_mul_le_one_pair ha hb)).1
  rw [← mul_assoc] at hh
  linarith only [hh]

lemma reciprocal_affine (c d v : ℝ) (y : Bool) (hv : |v| < 1) :
    (c+d*spinValue y)/(1+v*spinValue y)=
      (c-v*d)/(1-v^2)+spinValue y*((d-v*c)/(1-v^2)) := by
  have hv' := abs_lt.mp hv
  have h₁ : 1+v ≠ 0 := by linarith only [hv'.1]
  have h₂ : 1-v ≠ 0 := by linarith only [hv'.2]
  have h₃ : 1-v^2 ≠ 0 := by
    have he : 1-v^2=(1+v)*(1-v) := by ring
    rw [he];exact mul_ne_zero h₁ h₂
  cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,mul_one,mul_neg_one,← sub_eq_add_neg]
  · field_simp [h₂,h₃]
    ring
  · field_simp [h₁,h₃]
    ring

lemma pair_gradient_reciprocal {a b u p r : ℝ} (ha : |a| ≤ 1) (hu : |u| ≤ 1/4) (y : Bool) :
    pairGrad₁ b p r y/(1+u*a*spinValue y)=
      (p-(b+u*a)*r)/(1-u^2*a^2)+
      spinValue y*((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2)) := by
  have hv : |u*a| < 1 := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_left ha (abs_nonneg u)
    nlinarith only [hu,hh]
  have he := reciprocal_affine (p-r*b) r (u*a) y hv
  have hg : pairGrad₁ b p r y =p-r*b+r*spinValue y := by unfold pairGrad₁;ring
  rw [hg,he]
  congr 1
  · congr 1 <;> ring
  · congr 1
    congr 1 <;> ring

lemma pair_cross_coefficient_identity {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-u^2)/(1+u*a*b)*
      (((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2))*
        ((r*(1+u*a*b)-u*b*s)/(1-u^2*b^2))-
        u*((p-(b+u*a)*r)/(1-u^2*a^2))*((s-(a+u*b)*r)/(1-u^2*b^2)))=
      pairCrossPolynomial a b u p s r := by
  have hd₀ := (pairDenominator_pos hu ha hb).ne'
  have hd₁ : 1-u^2*a^2 ≠ 0 := by
    have h₁ := pairDenominator_pos hu ha (by norm_num : |(1:ℝ)| ≤ 1)
    have h₂ := pairDenominator_pos hu ha (by norm_num : |(-1:ℝ)| ≤ 1)
    have he : 1-u^2*a^2=(1+u*a*1)*(1+u*a*(-1)) := by ring
    rw [he];exact mul_ne_zero h₁.ne' h₂.ne'
  have hd₂ : 1-u^2*b^2 ≠ 0 := by
    have h₁ := pairDenominator_pos hu hb (by norm_num : |(1:ℝ)| ≤ 1)
    have h₂ := pairDenominator_pos hu hb (by norm_num : |(-1:ℝ)| ≤ 1)
    have he : 1-u^2*b^2=(1+u*b*1)*(1+u*b*(-1)) := by ring
    rw [he];exact mul_ne_zero h₁.ne' h₂.ne'
  unfold pairCrossPolynomial pairK pairR
  field_simp [hd₀,hd₁,hd₂]
  ring

lemma pair_cross_pointwise (a b u p s r : ℝ) (x y : Bool) :
    pairDensity a b u x y*(pairResidual a u x y*pairGrad₁ b p r y*
      (pairResidual b u y x*pairGrad₂ a s r x))=
    ((1-u^2)/(1+u*a*b))*((spinValue x-a)*(spinValue y-b)*
      (1-u*spinValue x*spinValue y)*(pairGrad₁ b p r y/(1+u*a*spinValue y))*
      (pairGrad₂ a s r x/(1+u*b*spinValue x))) := by
  unfold pairDensity pairResidual
  have he : (1+u*spinValue x*spinValue y)*(1-u*spinValue x*spinValue y)*
      (1-u*spinValue y*spinValue x)=(1-u^2)*(1-u*spinValue x*spinValue y) := by
    cases x <;> cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true] <;> ring
  calc
    _ = ((1+u*spinValue x*spinValue y)*(1-u*spinValue x*spinValue y)*(1-u*spinValue y*spinValue x))*
      ((spinValue x-a)*(spinValue y-b)*pairGrad₁ b p r y*pairGrad₂ a s r x)/
      ((1+u*a*b)*(1+u*a*spinValue y)*(1+u*b*spinValue x)) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
    _ = _ := by
      rw [he]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

lemma pair_cross_exact {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    pairInterMean a b u (fun x y=>pairResidual a u x y*pairGrad₁ b p r y*
      (pairResidual b u y x*pairGrad₂ a s r x))=
      (1-a^2)*(1-b^2)*pairCrossPolynomial a b u p s r := by
  unfold pairInterMean
  simp_rw [pair_cross_pointwise]
  rw [pairMean_mul]
  have hh (x y : Bool) :
      (spinValue x-a)*(spinValue y-b)*(1-u*spinValue x*spinValue y)*
        (pairGrad₁ b p r y/(1+u*a*spinValue y))*
        (pairGrad₂ a s r x/(1+u*b*spinValue x))=
      (spinValue x-a)*(spinValue y-b)*(1-u*spinValue x*spinValue y)*
        ((p-(b+u*a)*r)/(1-u^2*a^2)+spinValue y*((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2)))*
        ((s-(a+u*b)*r)/(1-u^2*b^2)+spinValue x*((r*(1+u*b*a)-u*b*s)/(1-u^2*b^2))) := by
    rw [pair_gradient_reciprocal ha hu]
    change _ * (pairGrad₁ a s r x / _) = _
    rw [pair_gradient_reciprocal hb hu]
  simp_rw [hh]
  rw [pair_polynomial_cross_mean]
  have he : 1+u*b*a=1+u*a*b := by ring
  rw [he]
  calc
    _ = (1-a^2)*(1-b^2)*((1-u^2)/(1+u*a*b)*
      (((r*(1+u*a*b)-u*a*p)/(1-u^2*a^2))*
        ((r*(1+u*a*b)-u*b*s)/(1-u^2*b^2))-
        u*((p-(b+u*a)*r)/(1-u^2*a^2))*((s-(a+u*b)*r)/(1-u^2*b^2)))) := by ring
    _ = _ := by rw [pair_cross_coefficient_identity ha hb hu]
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real

lemma pair_variance_nonneg {a u : ℝ} (ha : |a| ≤ 1) (hu : |u| ≤ 1/4) (y : Bool) :
    0 ≤ pairVariance a u y := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hh := (pair_square_factor_control hu).1
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha2) (by linarith only [hh])) (sq_nonneg _)

lemma pair_density_nonneg {a b u : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hu : |u| ≤ 1/4) (x y : Bool) : 0 ≤ pairDensity a b u x y := by
  exact div_nonneg (pairDenominator_pos hu (pairSign_abs x).le (pairSign_abs y).le).le
    (pairDenominator_pos hu ha hb).le

lemma pair_variance_product (a b u : ℝ) (x y : Bool) :
    pairDensity a b u x y*(pairVariance a u y*pairVariance b u x)=
      (1-a^2)*(1-b^2)*pairRationalWeight a b u (spinValue x) (spinValue y) := by
  unfold pairDensity pairVariance pairRationalWeight
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma pair_weighted_product (a b u p s r : ℝ) :
    pairInterMean a b u (fun x y=>pairVariance a u y*pairGrad₁ b p r y*
      (pairVariance b u x*pairGrad₂ a s r x))=
    (1-a^2)*(1-b^2)*pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x)) := by
  unfold pairInterMean
  rw [← pairMean_mul]
  congr 1
  funext x y
  calc
    _ = (pairDensity a b u x y*(pairVariance a u y*pairVariance b u x))*
      (pairGrad₁ b p r y*pairGrad₂ a s r x) := by ring
    _ = _ := by rw [pair_variance_product];ring

lemma pair_abs_weighted_product {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
      (pairVariance b u x*pairGrad₂ a s r x)|)=
    (1-a^2)*(1-b^2)*pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
      |pairGrad₁ b p r y*pairGrad₂ a s r x|) := by
  unfold pairInterMean
  rw [← pairMean_mul]
  congr 1
  funext x y
  have h₁ := pair_variance_nonneg ha hu y
  have h₂ := pair_variance_nonneg hb hu x
  simp only [abs_mul,abs_of_nonneg h₁,abs_of_nonneg h₂]
  calc
    _ = (pairDensity a b u x y*(pairVariance a u y*pairVariance b u x))*
      (|pairGrad₁ b p r y| * |pairGrad₂ a s r x|) := by ring
    _ = _ := by rw [pair_variance_product];ring

lemma pair_weighted_error {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    |pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x))-p*s| ≤
    1216*|u| * pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|) := by
  have he : p*s=pairMean a b (fun x y=>pairGrad₁ b p r y*pairGrad₂ a s r x) :=
    (pair_gradient_mean a b p s r).symm
  rw [he,← pairMean_sub]
  apply (abs_pairMean_le ha hb _).trans
  rw [← pairMean_mul]
  apply pairMean_mono ha hb
  intro x y
  have hh := (pairRationalWeight_bounds ha hb hu (pairSign_abs x).le (pairSign_abs y).le).2.2
  have ht : pairRationalWeight a b u (spinValue x) (spinValue y)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x)-(pairGrad₁ b p r y*pairGrad₂ a s r x)=
      (pairRationalWeight a b u (spinValue x) (spinValue y)-1)*
      (pairGrad₁ b p r y*pairGrad₂ a s r x) := by ring
  rw [ht,abs_mul]
  exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)

lemma pair_abs_cost_lower {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)/256 ≤
    pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
      (pairVariance b u x*pairGrad₂ a s r x)|) := by
  rw [pair_abs_weighted_product ha hb hu]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hAB : 0 ≤ (1-a^2)*(1-b^2) := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have he : (1-a^2)*(1-b^2)*pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)/256=
      (1-a^2)*(1-b^2)*((1/256)*pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)) := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hAB
  rw [← pairMean_mul]
  apply pairMean_mono ha hb
  intro x y
  exact mul_le_mul_of_nonneg_right
    (pairRationalWeight_bounds ha hb hu (pairSign_abs x).le (pairSign_abs y).le).1 (abs_nonneg _)

lemma pair_density_variance_lower {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) (x y : Bool) :
    (1-a^2)/32 ≤ pairDensity a b u x y*pairVariance a u y := by
  have hn : 1/2 ≤ 1+u*spinValue x*spinValue y := by
    simpa only [mul_assoc] using (pair_factor_control hu (abs_mul_le_one_pair (pairSign_abs x).le (pairSign_abs y).le)).1
  have hs := (pair_square_factor_control hu).1
  have hd₀ := pair_factor_control hu (abs_mul_le_one_pair ha hb)
  have hd₁ := pair_factor_control hu (abs_mul_le_one_pair ha (pairSign_abs y).le)
  have hd02 : 1+u*a*b ≤ 2 := by simpa only [mul_assoc] using hd₀.2.1
  have hd12 : 1+u*a*spinValue y ≤ 2 := by simpa only [mul_assoc] using hd₁.2.1
  have hd10 : 0 ≤ 1+u*a*spinValue y := (pairDenominator_pos hu ha (pairSign_abs y).le).le
  have hd00 := pairDenominator_pos hu ha hb
  have hdd : 0 < (1+u*a*b)*(1+u*a*spinValue y)^2 := mul_pos hd00 (sq_pos_of_pos (pairDenominator_pos hu ha (pairSign_abs y).le))
  have hd : (1+u*a*b)*(1+u*a*spinValue y)^2 ≤ 8 := by
    have hh : (1+u*a*spinValue y)^2 ≤ 4 := by nlinarith only [hd12,hd10]
    nlinarith only [mul_le_mul hd02 hh (sq_nonneg (1+u*a*spinValue y)) (by norm_num : (0:ℝ) ≤ 2)]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hA := sub_nonneg.mpr ha2
  have hn' : 1/4 ≤ (1+u*spinValue x*spinValue y)*(1-u^2) := by
    nlinarith only [mul_le_mul hn hs (by norm_num : (0:ℝ) ≤ 1/2) (by linarith only [hn] : 0 ≤ 1+u*spinValue x*spinValue y)]
  have he : pairDensity a b u x y*pairVariance a u y=
      ((1-a^2)*((1+u*spinValue x*spinValue y)*(1-u^2)))/
      ((1+u*a*b)*(1+u*a*spinValue y)^2) := by
    unfold pairDensity pairVariance
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  apply (le_div_iff₀ hdd).mpr
  have h₁ := mul_le_mul_of_nonneg_left hd (div_nonneg hA (by norm_num : (0:ℝ) ≤ 32))
  have h₂ := mul_le_mul_of_nonneg_left hn' hA
  nlinarith only [h₁,h₂]
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairCrossLower
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real

lemma abs_pair_ps_coefficient {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairK a b u*(-u+u^2*a*b)+u| ≤ 66*u^2 := by
  have hk := pairK_bounds ha hb hu
  have hk0 : 0 ≤ pairK a b u := by linarith only [hk.2.1]
  have he : pairK a b u*(-u+u^2*a*b)+u=
      -(pairK a b u-1)*u+pairK a b u*u^2*(a*b) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_neg,abs_mul,abs_mul,abs_of_nonneg hk0,abs_of_nonneg (sq_nonneg u)]
  have h₁ := mul_le_mul_of_nonneg_right hk.1 (abs_nonneg u)
  have h₂ := mul_le_mul (mul_le_mul_of_nonneg_right hk.2.2 (sq_nonneg u))
    (abs_mul_le_one_pair ha hb) (abs_nonneg (a*b)) (by positivity : (0:ℝ) ≤ 2*u^2)
  nlinarith only [h₁,h₂,sq_abs u]

lemma abs_pair_mixed_coefficient {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    |pairK a b u*u^2*b*(1-a^2)| ≤ 2*u^2 ∧
    |pairK a b u*u^2*a*(1-b^2)| ≤ 2*u^2 := by
  have hk := pairK_bounds ha hb hu
  have hk0 : 0 ≤ pairK a b u := by linarith only [hk.2.1]
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hA : |1-a^2| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr ha2)];linarith [sq_nonneg a]
  have hB : |1-b^2| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hb2)];linarith [sq_nonneg b]
  have hh (x y : ℝ) (hxy : |x*y| ≤ 1) : |pairK a b u*u^2*x*y| ≤ 2*u^2 := by
    rw [mul_assoc (pairK a b u*u^2),abs_mul,abs_mul,abs_of_nonneg hk0,abs_of_nonneg (sq_nonneg u)]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hk.2.2 (sq_nonneg u)) hxy
      (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  exact ⟨hh b (1-a^2) (abs_mul_le_one_pair hb hA),hh a (1-b^2) (abs_mul_le_one_pair ha hB)⟩

lemma mul_lower_from_abs {c x B : ℝ} (hc : |c| ≤ B) : -B*|x| ≤ c*x := by
  have hh := neg_abs_le (c*x)
  rw [abs_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
  linarith only [hh,hm]

lemma pairCrossPolynomial_lower {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    r^2/2-66*u^2*|p*s|-2*u^2*|r*p|-2*u^2*|r*s| ≤
      pairCrossPolynomial a b u p s r+u*(p*s) := by
  have hps := mul_lower_from_abs (x:=p*s) (abs_pair_ps_coefficient ha hb hu)
  have hrp := mul_lower_from_abs (x:=r*p) (abs_pair_mixed_coefficient ha hb hu).1
  have hrs := mul_lower_from_abs (x:=r*s) (abs_pair_mixed_coefficient ha hb hu).2
  have hr := mul_le_mul_of_nonneg_right (pairKR_lower ha hb hu) (sq_nonneg r)
  unfold pairCrossPolynomial
  nlinarith only [hps,hrp,hrs,hr]

lemma pair_young_cost (u r p : ℝ) :
    2*u^2*|r*p| ≤ r^2/4+4*u^4*p^2 := by
  rw [abs_mul]
  have he : (|r|/2-2*u^2*|p|)^2=r^2/4-2*u^2*|r| * |p|+4*u^4*p^2 := by
    ring_nf
    rw [sq_abs r,sq_abs p]
    ring
  nlinarith only [sq_nonneg (|r|/2-2*u^2*|p|),he]

lemma pair_signed_cross_lower {a b u p s r z q : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000)
    (hq : |p*s| ≤ q) (hz : |z-p*s| ≤ 1216*|u| * q) :
    -1282*u^2*q-4*u^4*(p^2+s^2) ≤ pairCrossPolynomial a b u p s r+u*z := by
  have h₁ := pairCrossPolynomial_lower (p:=p) (s:=s) (r:=r) ha hb hu
  have h₂ := pair_young_cost u r p
  have h₃ := pair_young_cost u r s
  have h₄ := mul_le_mul_of_nonneg_left hq (show 0 ≤ 66*u^2 by positivity)
  have hz' : -1216*u^2*q ≤ u*(z-p*s) := by
    have hh := neg_abs_le (u*(z-p*s))
    rw [abs_mul] at hh
    have hm := mul_le_mul_of_nonneg_left hz (abs_nonneg u)
    have he : |u| * (1216*|u| * q)=1216*u^2*q := by
      ring_nf
      rw [sq_abs u]
      ring
    rw [he] at hm
    linarith only [hh,hm]
  nlinarith only [h₁,h₂,h₃,h₄,hz']
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real

lemma pair_energy_lower {a b u p r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*p^2/32 ≤
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hA := sub_nonneg.mpr ha2
  have hB := sub_nonneg.mpr hb2
  have he := pairMean_mono ha hb (fun x y=>mul_le_mul_of_nonneg_right
    (pair_density_variance_lower ha hb hu x y) (sq_nonneg (pairGrad₁ b p r y)))
  simp only [pairMean_mul] at he
  have h₁ : pairMean a b (fun _ y=>(pairGrad₁ b p r y)^2)=p^2+(1-b^2)*r^2 :=
    pair_gradient_square a b p r
  rw [h₁] at he
  have h₂ : pairMean a b (fun x y=>pairDensity a b u x y*pairVariance a u y*(pairGrad₁ b p r y)^2)=
      pairInterMean a b u (fun _x y=>pairVariance a u y*(pairGrad₁ b p r y)^2) := by
    unfold pairInterMean
    congr 1
    funext x y
    ring
  rw [h₂] at he
  have h₃ : (1-a^2)*(1-b^2)*p^2 ≤ (1-a^2)*p^2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-b^2 ≤ 1 by linarith [sq_nonneg b])
      (mul_nonneg hA (sq_nonneg p))
    nlinarith only [hh]
  have h₄ : 0 ≤ (1-a^2)*(1-b^2)*r^2 := mul_nonneg (mul_nonneg hA hB) (sq_nonneg r)
  nlinarith only [he,h₃,h₄]

lemma pairInterMean_swap (a b u : ℝ) (F : Bool→Bool→ℝ) :
    pairInterMean a b u F=pairInterMean b a u (fun x y=>F y x) := by
  unfold pairInterMean
  rw [pairMean_swap]
  congr 1
  funext x y
  unfold pairDensity
  have he : (1+u*spinValue y*spinValue x)/(1+u*a*b)=
      (1+u*spinValue x*spinValue y)/(1+u*b*a) := by congr 1 <;> ring
  rw [he]

lemma pair_second_energy_lower {a b u s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4) :
    (1-a^2)*(1-b^2)*s^2/32 ≤
      pairInterMean a b u (fun x _y=>pairVariance b u x*(pairGrad₂ a s r x)^2) := by
  rw [pairInterMean_swap]
  simpa only [mul_comm (1-a^2) (1-b^2),pairGrad₁,pairGrad₂] using
    (pair_energy_lower (p:=s) (r:=r) hb ha hu)

lemma pairInterMean_add (a b u : ℝ) (F G : Bool→Bool→ℝ) :
    pairInterMean a b u (fun x y=>F x y+G x y)=pairInterMean a b u F+pairInterMean a b u G := by
  unfold pairInterMean
  simp_rw [mul_add]
  exact pairMean_add a b _ _

lemma pairInterMean_nonneg {a b u : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/4)
    {F : Bool→Bool→ℝ} (hF : ∀ x y,0 ≤ F x y) : 0 ≤ pairInterMean a b u F := by
  have hh := pairMean_mono ha hb (fun x y=>mul_nonneg (pair_density_nonneg ha hb hu x y) (hF x y))
  have he : pairMean a b (fun _ _=>(0:ℝ))=0 := by simp [pairMean]
  rwa [he] at hh

lemma pair_signed_bound {a b u p s r : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hu : |u| ≤ 1/1000) :
    -u*pairInterMean a b u (fun x y=>pairVariance a u y*pairGrad₁ b p r y*
        (pairVariance b u x*pairGrad₂ a s r x))-
      400000*u^2*pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
        (pairVariance b u x*pairGrad₂ a s r x)|)-
      400000*u^4*pairInterMean a b u (fun x y=>pairVariance a u y*(pairGrad₁ b p r y)^2+
        pairVariance b u x*(pairGrad₂ a s r x)^2) ≤
    pairInterMean a b u (fun x y=>pairResidual a u x y*pairGrad₁ b p r y*
      (pairResidual b u y x*pairGrad₂ a s r x)) := by
  have hu' : |u| ≤ 1/4 := by linarith only [hu]
  let q := pairMean a b (fun x y=>|pairGrad₁ b p r y*pairGrad₂ a s r x|)
  let z := pairMean a b (fun x y=>pairRationalWeight a b u (spinValue x) (spinValue y)*
    (pairGrad₁ b p r y*pairGrad₂ a s r x))
  have hq : |p*s| ≤ q := by
    have hh := abs_pairMean_le ha hb (fun x y=>pairGrad₁ b p r y*pairGrad₂ a s r x)
    change |pairMean a b (fun x y=>(p+r*(spinValue y-b))*(s+r*(spinValue x-a)))| ≤ q at hh
    rwa [pair_gradient_mean] at hh
  have hl := pair_signed_cross_lower (r:=r) ha hb hu hq (pair_weighted_error ha hb hu')
  have ha2 : a^2 ≤ 1 := by nlinarith only [sq_abs a,abs_nonneg a,ha]
  have hb2 : b^2 ≤ 1 := by nlinarith only [sq_abs b,abs_nonneg b,hb]
  have hAB : 0 ≤ (1-a^2)*(1-b^2) := mul_nonneg (sub_nonneg.mpr ha2) (sub_nonneg.mpr hb2)
  have hl' := mul_le_mul_of_nonneg_left hl hAB
  have hc := pair_abs_cost_lower (p:=p) (s:=s) (r:=r) ha hb hu'
  have h₁ := pair_energy_lower (p:=p) (r:=r) ha hb hu'
  have h₂ := pair_second_energy_lower (s:=s) (r:=r) ha hb hu'
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 1282*256*u^2 by positivity)
  have he' := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (show 0 ≤ 128*u^4 by positivity)
  have habs : 0 ≤ pairInterMean a b u (fun x y=>|pairVariance a u y*pairGrad₁ b p r y*
        (pairVariance b u x*pairGrad₂ a s r x)|) := pairInterMean_nonneg ha hb hu' (fun _ _=>abs_nonneg _)
  have hener : 0 ≤ pairInterMean a b u (fun x y=>pairVariance a u y*(pairGrad₁ b p r y)^2+
        pairVariance b u x*(pairGrad₂ a s r x)^2) := pairInterMean_nonneg ha hb hu'
    (fun x y=>add_nonneg (mul_nonneg (pair_variance_nonneg ha hu' y) (sq_nonneg _))
      (mul_nonneg (pair_variance_nonneg hb hu' x) (sq_nonneg _)))
  have hc'' := mul_nonneg (sq_nonneg u) habs
  have he'' := mul_nonneg (show 0 ≤ u^4 by positivity) hener
  rw [pairInterMean_add] at he'' ⊢
  rw [pair_cross_exact ha hb hu',pair_weighted_product]
  change -u*((1-a^2)*(1-b^2)*z)-_ -_ ≤ _
  change -1282*u^2*q-4*u^4*(p^2+s^2) ≤ pairCrossPolynomial a b u p s r+u*z at hl
  change (1-a^2)*(1-b^2)*(-1282*u^2*q-4*u^4*(p^2+s^2)) ≤
    (1-a^2)*(1-b^2)*(pairCrossPolynomial a b u p s r+u*z) at hl'
  change 1282*256*u^2*((1-a^2)*(1-b^2)*q/256) ≤ _ at hc'
  nlinarith only [hl',hc',he',hc'',he'']
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairBoltzmann
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

lemma exp_spin (t : ℝ) (x : Bool) :
    exp (t*spinValue x)=cosh t*(1+tanh t*spinValue x) := by
  have h : cosh t ≠ 0 := (cosh_pos t).ne'
  cases x
  · simp only [spinValue_false,mul_neg_one,tanh_eq_sinh_div_cosh]
    rw [← cosh_sub_sinh]
    field_simp
    ring
  · simp only [spinValue_true,mul_one,tanh_eq_sinh_div_cosh]
    rw [← cosh_add_sinh]
    field_simp

lemma exp_spin_product (t : ℝ) (x y : Bool) :
    exp (t*spinValue x*spinValue y)=cosh t*(1+tanh t*spinValue x*spinValue y) := by
  cases y
  · simp only [spinValue_false,mul_neg_one]
    have he := exp_spin t (!x)
    simpa only [spinValue_not,mul_neg,neg_mul] using he
  · simpa only [spinValue_true,mul_one] using exp_spin t x

lemma pairBoltzmannWeight_factor (α γ J : ℝ) (x y : Bool) :
    pairBoltzmannWeight α γ J x y=cosh α*cosh γ*cosh J*
      ((1+tanh α*spinValue x)*(1+tanh γ*spinValue y)*(1+tanh J*spinValue x*spinValue y)) := by
  unfold pairBoltzmannWeight
  rw [exp_add,exp_add,exp_spin,exp_spin,exp_spin_product]
  ring

lemma pairBoltzmann_partition (α γ J : ℝ) :
    (∑ x,∑ y,pairBoltzmannWeight α γ J x y)=
      4*cosh α*cosh γ*cosh J*(1+tanh J*tanh α*tanh γ) := by
  simp only [pairBoltzmannWeight_factor,Fintype.sum_bool,spinValue_false,spinValue_true]
  ring

lemma pairBoltzmannMean_eq (α γ J : ℝ) (F : Bool→Bool→ℝ) :
    pairBoltzmannMean α γ J F=pairInterMean (tanh α) (tanh γ) (tanh J) F := by
  unfold pairBoltzmannMean pairInterMean pairMean
  rw [pairBoltzmann_partition]
  simp_rw [pairBoltzmannWeight_factor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  unfold pairBaseMass pairDensity
  have h₁ := (cosh_pos α).ne'
  have h₂ := (cosh_pos γ).ne'
  have h₃ := (cosh_pos J).ne'
  field_simp [h₁,h₂,h₃]

lemma pair_gradients_representation (F : Bool→Bool→ℝ) (a b : ℝ) :
    ∃ p s r : ℝ,
      (∀ y,(F true y-F false y)/2=pairGrad₁ b p r y) ∧
      (∀ x,(F x true-F x false)/2=pairGrad₂ a s r x) := by
  let r := (F true true-F true false-F false true+F false false)/4
  let p := (F true true+F true false-F false true-F false false)/4+b*r
  let s := (F true true-F true false+F false true-F false false)/4+a*r
  refine ⟨p,s,r,?_,?_⟩
  · intro y;cases y <;> simp only [pairGrad₁,spinValue_false,spinValue_true] <;> dsimp [p,r] <;> ring
  · intro x;cases x <;> simp only [pairGrad₂,spinValue_false,spinValue_true] <;> dsimp [s,r] <;> ring

lemma tanh_add_real (a b : ℝ) : tanh (a+b)=(tanh a+tanh b)/(1+tanh a*tanh b) := by
  have h₁ := (cosh_pos a).ne'
  have h₂ := (cosh_pos b).ne'
  have h₃ : cosh a*cosh b+sinh a*sinh b ≠ 0 := by
    rw [← cosh_add]
    exact (cosh_pos (a+b)).ne'
  simp only [tanh_eq_sinh_div_cosh,sinh_add,cosh_add]
  field_simp [h₁,h₂,h₃]

lemma tanh_pair_residual (α J : ℝ) (x y : Bool) :
    spinValue x-tanh (α+J*spinValue y)=pairResidual (tanh α) (tanh J) x y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  unfold pairResidual
  have hd : 1+tanh α*(tanh J*spinValue y) ≠ 0 := by
    have ht : |tanh α*(tanh J*spinValue y)| < 1 := by
      rw [abs_mul,abs_mul,pairSign_abs,mul_one]
      exact (mul_le_mul_of_nonneg_left (abs_tanh_lt_one J).le (abs_nonneg (tanh α))).trans_lt (by simpa using abs_tanh_lt_one α)
    linarith only [(abs_lt.mp ht).1]
  have hd' : 1+tanh J*tanh α*spinValue y ≠ 0 := by
    convert hd using 1 <;> first | rfl | ring
  simp only [← mul_assoc] at hd hd' ⊢
  field_simp [hd,hd']
  cases x <;> simp only [spinValue_false,spinValue_true] <;> ring

lemma tanh_pair_variance (α J : ℝ) (y : Bool) :
    1-tanh (α+J*spinValue y)^2=pairVariance (tanh α) (tanh J) y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  unfold pairVariance
  have hd : 1+tanh α*(tanh J*spinValue y) ≠ 0 := by
    have ht : |tanh α*(tanh J*spinValue y)| < 1 := by
      rw [abs_mul,abs_mul,pairSign_abs,mul_one]
      exact (mul_le_mul_of_nonneg_left (abs_tanh_lt_one J).le (abs_nonneg (tanh α))).trans_lt (by simpa using abs_tanh_lt_one α)
    linarith only [(abs_lt.mp ht).1]
  have hd' : 1+tanh J*tanh α*spinValue y ≠ 0 := by
    convert hd using 1 <;> first | rfl | ring
  simp only [← mul_assoc] at hd hd' ⊢
  field_simp [hd,hd']
  cases y <;> simp only [spinValue_false,spinValue_true] <;> ring

lemma pairBoltzmann_signed_bound (α γ J : ℝ) (F : Bool→Bool→ℝ)
    (hJ : |tanh J| ≤ 1/1000) :
    let g₁ := fun y=>(F true y-F false y)/2;
    let g₂ := fun x=>(F x true-F x false)/2;
    let v₁ := fun y=>1-tanh (α+J*spinValue y)^2;
    let v₂ := fun x=>1-tanh (γ+J*spinValue x)^2;
    -tanh J*pairBoltzmannMean α γ J (fun x y=>v₁ y*g₁ y*(v₂ x*g₂ x))-
      400000*(tanh J)^2*pairBoltzmannMean α γ J (fun x y=>|v₁ y*g₁ y*(v₂ x*g₂ x)|)-
      400000*(tanh J)^4*pairBoltzmannMean α γ J (fun x y=>v₁ y*(g₁ y)^2+v₂ x*(g₂ x)^2) ≤
    pairBoltzmannMean α γ J (fun x y=>(spinValue x-tanh (α+J*spinValue y))*g₁ y*
      ((spinValue y-tanh (γ+J*spinValue x))*g₂ x)) := by
  dsimp only
  obtain ⟨p,s,r,hg₁,hg₂⟩ := pair_gradients_representation F (tanh α) (tanh γ)
  simp_rw [pairBoltzmannMean_eq,tanh_pair_residual,tanh_pair_variance,hg₁,hg₂]
  exact pair_signed_bound (abs_tanh_lt_one α).le (abs_tanh_lt_one γ).le hJ
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma update_true_false (i : Fin n) (x : Spin n) :
    (Function.update x i true=x ∧ Function.update x i false=flip i x) ∨
      (Function.update x i true=flip i x ∧ Function.update x i false=x) := by
  cases hx : x i
  · right
    constructor
    · simp [flip,hx]
    · simpa only [hx] using Function.update_eq_self i x
  · left
    constructor
    · simpa only [hx] using Function.update_eq_self i x
    · simp [flip,hx]

lemma conditionalExpectation_updates (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (∑ b : Bool,weight g h (Function.update x i b)*f (Function.update x i b))/
      (∑ b : Bool,weight g h (Function.update x i b)) := by
  simp only [Fintype.sum_bool]
  rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]
  · rfl
  · unfold conditionalExpectation
    rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma weight_update_factor (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    weight g h (Function.update x i b)=exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
      exp (localField g h i x*spinValue b) := by
  unfold weight
  rw [hamiltonian_update,← exp_add]
  congr 1;ring

lemma conditionalExpectation_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (f (Function.update x i true)+f (Function.update x i false))/2+
        tanh (localField g h i x)*spinGradient i f x := by
  rw [conditionalExpectation_updates]
  simp_rw [weight_update_factor,exp_spin]
  simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one]
  unfold spinGradient
  have h₁ := (exp_pos (hamiltonian g h x-spinValue (x i)*localField g h i x)).ne'
  have h₂ := (cosh_pos (localField g h i x)).ne'
  have he : exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+tanh (localField g h i x)))+
      exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+-tanh (localField g h i x)))=
      2*exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*cosh (localField g h i x) := by ring
  rw [he]
  field_simp [h₁,h₂]
  ring

lemma spin_affine (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    f x=(f (Function.update x i true)+f (Function.update x i false))/2+
      spinValue (x i)*spinGradient i f x := by
  unfold spinGradient
  cases hx : x i
  · have hf : Function.update x i false=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_false,hf];ring
  · have ht : Function.update x i true=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_true,ht];ring

lemma conditionalDifference_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    f x-conditionalExpectation g h i f x=
      (spinValue (x i)-tanh (localField g h i x))*spinGradient i f x := by
  rw [conditionalExpectation_local]
  have he := spin_affine i f x
  linarith only [he]

lemma spinGradient_update (i : Fin n) (f : Spin n→ℝ) (x : Spin n) (b : Bool) :
    spinGradient i f (Function.update x i b)=spinGradient i f x := by
  simp only [spinGradient,Function.update_idem]

lemma conditionalSiteEnergy_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>(1-tanh (localField g h i x)^2)*spinGradient i f x^2) := by
  rw [← expectation_conditionalExpectation g h i]
  congr 1
  funext x
  rw [conditionalExpectation_local]
  simp_rw [conditionalDifference_local,localField_update_self,spinGradient_update]
  simp only [Function.update_self,spinValue_true,spinValue_false,spinGradient]
  simp_rw [Function.update_idem,localField_update_self]
  ring
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairConditioning
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma pairUpdate_overwrite (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b c d : Bool) :
    pairUpdate i j (pairUpdate i j x a b) c d=pairUpdate i j x c d := by
  funext k
  by_cases hj : k=j
  · subst k;simp [pairUpdate]
  · by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · simp [pairUpdate,hj,hi]

lemma pairUpdate_left (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b i=a := by simp [pairUpdate,hij]
lemma pairUpdate_right (i j : Fin n) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b j=b := by simp [pairUpdate]

lemma sum_spin_update (i : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ b : Bool,F (Function.update x i b))=2*∑ x,F x := by
  have he (x : Spin n) : (∑ b : Bool,F (Function.update x i b))=F x+F (flip i x) := by
    simp only [Fintype.sum_bool]
    rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_flip]
  ring

lemma sum_pairUpdate (i j : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ a : Bool,∑ b : Bool,F (pairUpdate i j x a b))=4*∑ x,F x := by
  unfold pairUpdate
  rw [sum_spin_update i (fun x=>∑ b : Bool,F (Function.update x j b)),sum_spin_update]
  ring

lemma pairConditionalMean_update (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) (a b : Bool) :
    pairConditionalMean g h i j F (pairUpdate i j x a b)=pairConditionalMean g h i j F x := by
  simp only [pairConditionalMean,pairUpdate_overwrite i j hij]

lemma pairConditional_partition_pos (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (x : Spin n) :
    0 < ∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b) := by
  simp only [Fintype.sum_bool]
  exact add_pos (add_pos (weight_pos _ _ _) (weight_pos _ _ _))
    (add_pos (weight_pos _ _ _) (weight_pos _ _ _))

lemma expectation_pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) : expectation g h (pairConditionalMean g h i j F)=expectation g h F := by
  have h₁ := sum_pairUpdate i j (fun x=>mass g h x*pairConditionalMean g h i j F x)
  have h₂ := sum_pairUpdate i j (fun x=>mass g h x*F x)
  have he : (∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*
      pairConditionalMean g h i j F (pairUpdate i j x a b))=
      ∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*F (pairUpdate i j x a b) := by
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [pairConditionalMean_update g h i j hij,mass,div_mul_eq_mul_div]
    simp only [← Finset.sum_div,← Finset.sum_mul]
    unfold pairConditionalMean
    rw [mul_div_cancel₀ _ (pairConditional_partition_pos g h i j x).ne']
  unfold expectation
  linarith only [h₁,h₂,he]

lemma pairUpdate_hamiltonian (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (x : Spin n) (a b : Bool) :
    let α := localField g h i x-coupling g i j*spinValue (x j);
    let γ := localField g h j x-coupling g i j*spinValue (x i);
    hamiltonian g h (pairUpdate i j x a b)=
      (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
        coupling g i j*spinValue (x i)*spinValue (x j))+
      (α*spinValue a+γ*spinValue b+coupling g i j*spinValue a*spinValue b) := by
  dsimp only
  unfold pairUpdate
  rw [hamiltonian_update,hamiltonian_update,localField_update,
    Function.update_of_ne (Ne.symm hij),coupling_symm g j i]
  ring

lemma pairUpdate_localField₁ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h i (pairUpdate i j x a b)=
      (localField g h i x-coupling g i j*spinValue (x j))+coupling g i j*spinValue b := by
  unfold pairUpdate
  rw [localField_update,localField_update_self]
  by_cases hij : i=j
  · subst j;simp
  · rw [Function.update_of_ne (Ne.symm hij)]
    ring

lemma pairUpdate_localField₂ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h j (pairUpdate i j x a b)=
      (localField g h j x-coupling g i j*spinValue (x i))+coupling g i j*spinValue a := by
  unfold pairUpdate
  rw [localField_update_self,localField_update,coupling_symm g j i]
  ring

lemma pairUpdate_gradient₁ (i j : Fin n) (hij : i ≠ j) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient i F (pairUpdate i j x a b)=
      (F (pairUpdate i j x true b)-F (pairUpdate i j x false b))/2 := by
  have he (c : Bool) : Function.update (pairUpdate i j x a b) i c=pairUpdate i j x c b := by
    funext k
    by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · by_cases hj : k=j
      · subst k;simp [pairUpdate,hij.symm]
      · simp [pairUpdate,hj,hi]
  simp only [spinGradient,he]
lemma pairUpdate_gradient₂ (i j : Fin n) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient j F (pairUpdate i j x a b)=
      (F (pairUpdate i j x a true)-F (pairUpdate i j x a false))/2 := by
  simp only [spinGradient,pairUpdate,Function.update_idem]

lemma pairConditionalMean_boltzmann (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) :
    pairConditionalMean g h i j F x=
      pairBoltzmannMean (localField g h i x-coupling g i j*spinValue (x j))
        (localField g h j x-coupling g i j*spinValue (x i)) (coupling g i j)
        (fun a b=>F (pairUpdate i j x a b)) := by
  let α := localField g h i x-coupling g i j*spinValue (x j)
  let γ := localField g h j x-coupling g i j*spinValue (x i)
  let C := exp (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
    coupling g i j*spinValue (x i)*spinValue (x j))
  have hC : C ≠ 0 := (exp_pos _).ne'
  have hw (a b : Bool) : weight g h (pairUpdate i j x a b)=C*pairBoltzmannWeight α γ (coupling g i j) a b := by
    unfold weight
    rw [pairUpdate_hamiltonian g h i j hij,exp_add]
    rfl
  unfold pairConditionalMean
  simp_rw [hw,mul_assoc,← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hC]
  rfl
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_PairGibbsBound
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma pairConditional_signed_bound (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (f : Spin n→ℝ) (x : Spin n) (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -tanh (coupling g i j)*pairConditionalMean g h i j
      (fun x=>weightedGradient g h i f x*weightedGradient g h j f x) x-
    400000*tanh (coupling g i j)^2*pairConditionalMean g h i j
      (fun x=>|weightedGradient g h i f x*weightedGradient g h j f x|) x-
    400000*tanh (coupling g i j)^4*pairConditionalMean g h i j
      (fun x=>siteVariance g h i x*spinGradient i f x^2+siteVariance g h j x*spinGradient j f x^2) x ≤
    pairConditionalMean g h i j (fun x=>(f x-conditionalExpectation g h i f x)*
      (f x-conditionalExpectation g h j f x)) x := by
  simp_rw [pairConditionalMean_boltzmann g h i j hij,weightedGradient,siteVariance,
    conditionalDifference_local,pairUpdate_localField₁,pairUpdate_localField₂,
    pairUpdate_gradient₁ i j hij,pairUpdate_gradient₂,pairUpdate_left i j hij,pairUpdate_right]
  exact pairBoltzmann_signed_bound
    (localField g h i x-coupling g i j*spinValue (x j))
    (localField g h j x-coupling g i j*spinValue (x i))
    (coupling g i j) (fun a b=>f (pairUpdate i j x a b)) hc

lemma expectation_mono (g : Disorder n) (h : Fin n→ℝ) {F G : Spin n→ℝ}
    (hFG : ∀ x,F x ≤ G x) : expectation g h F ≤ expectation g h G := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hFG x) (mass_nonneg g h x)

lemma gibbs_pair_signed_bound (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (f : Spin n→ℝ) (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -tanh (coupling g i j)*expectation g h
      (fun x=>weightedGradient g h i f x*weightedGradient g h j f x)-
    400000*tanh (coupling g i j)^2*expectation g h
      (fun x=>|weightedGradient g h i f x*weightedGradient g h j f x|)-
    400000*tanh (coupling g i j)^4*(expectation g h
      (fun x=>siteVariance g h i x*spinGradient i f x^2)+expectation g h
      (fun x=>siteVariance g h j x*spinGradient j f x^2)) ≤
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
      (f x-conditionalExpectation g h j f x)) := by
  have hh := expectation_mono g h (fun x=>pairConditional_signed_bound g h i j hij f x hc)
  simpa only [expectation_sub,expectation_const_mul,expectation_pairConditionalMean g h i j hij,
    expectation_add] using hh
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma siteVariance_pos (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    0 < siteVariance g h i x := by
  unfold siteVariance
  have ht := abs_tanh_lt_one (localField g h i x)
  have hs := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mpr ht
  simp only [sq_abs,one_pow] at hs
  linarith only [hs]
lemma siteVariance_le_one (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    siteVariance g h i x ≤ 1 := sub_le_self _ (sq_nonneg _)

lemma dirichlet_weighted (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=∑ i,expectation g h (fun x=>siteVariance g h i x*spinGradient i f x^2) := by
  unfold dirichlet siteVariance
  simp_rw [conditionalSiteEnergy_local]

lemma symmetric_fourth_cost {ι : Type*} [Fintype ι] (U : ι→ι→ℝ) (D : ι→ℝ) {R : ℝ}
    (hU : ∀ i j,U i j=U j i) (hD : ∀ i,0 ≤ D i)
    (hR : ∀ i,∑ j,U i j^4 ≤ R) :
    (∑ i,∑ j,U i j^4*(D i+D j)) ≤ 2*R*(∑ i,D i) := by
  simp_rw [mul_add,Finset.sum_add_distrib]
  have h₁ : (∑ i,∑ j,U i j^4*D i) ≤ R*∑ i,D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hR i) (hD i)
  have h₂ : (∑ i,∑ j,U i j^4*D j)=(∑ i,∑ j,U i j^4*D i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hU j i]
  rw [h₂]
  linarith only [h₁]

lemma heatBathGenerator_square (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x^2)=
      ∑ i,∑ j,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
        (f x-conditionalExpectation g h j f x)) := by
  simp only [heatBathGenerator,sq,Finset.sum_mul,Finset.mul_sum,expectation_sum]
  rw [Finset.sum_comm]

theorem gibbs_signed_curvature (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) {R : ℝ}
    (hc : ∀ i j,|tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i,∑ j,tanh (coupling g i j)^4 ≤ R) :
    (1-800000*R)*dirichlet g h f-
      expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)*
        weightedGradient g h i f x*weightedGradient g h j f x)-
      400000*expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)^2*
        |weightedGradient g h i f x*weightedGradient g h j f x|) ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2) := by
  let U := fun i j=>tanh (coupling g i j)
  let D := fun i=>expectation g h (fun x=>siteVariance g h i x*spinGradient i f x^2)
  let A := fun i j=>expectation g h (fun x=>weightedGradient g h i f x*weightedGradient g h j f x)
  let B := fun i j=>expectation g h (fun x=>|weightedGradient g h i f x*weightedGradient g h j f x|)
  let X := fun i j=>expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
    (f x-conditionalExpectation g h j f x))
  have hpair (i j : Fin n) : (if i=j then D i else 0)-U i j*A i j-
      400000*U i j^2*B i j-400000*U i j^4*(D i+D j) ≤ X i j := by
    by_cases hij : i=j
    · subst j
      have hX : X i i=D i := by
        dsimp [X,D,siteVariance]
        simp only [← sq,conditionalSiteEnergy_local]
      simp only [U,coupling_diag,tanh_zero,zero_mul,mul_zero,zero_pow (by omega : (2:ℕ) ≠ 0),
        zero_pow (by omega : (4:ℕ) ≠ 0),sub_zero,ite_true,hX,le_refl]
    · simpa only [ite_eq_right hij,zero_sub,neg_mul,U,A,B,D,X] using gibbs_pair_signed_bound g h i j hij f (hc i j)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ)=>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ)=>hpair i j))
  have hcost := symmetric_fourth_cost U D (fun i j=>congrArg tanh (coupling_symm g i j))
    (fun i=>expectation_nonneg g h (fun x=>mul_nonneg (siteVariance_pos g h i x).le (sq_nonneg _))) hR
  have hD : (∑ i,D i)=dirichlet g h f := (dirichlet_weighted g h f).symm
  have hX : (∑ i,∑ j,X i j)=expectation g h (fun x=>heatBathGenerator g h f x^2) :=
    (heatBathGenerator_square g h f).symm
  have hA : expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)*
      weightedGradient g h i f x*weightedGradient g h j f x)=∑ i,∑ j,U i j*A i j := by
    simp only [expectation_sum,mul_assoc,expectation_const_mul,U,A]
  have hB : expectation g h (fun x=>∑ i,∑ j,tanh (coupling g i j)^2*
      |weightedGradient g h i f x*weightedGradient g h j f x|)=∑ i,∑ j,U i j^2*B i j := by
    simp only [expectation_sum,expectation_const_mul,U,B]
  simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true] at hsum
  simp only [← Finset.mul_sum,mul_assoc] at hsum
  rw [hD,hX] at hsum
  rw [hD] at hcost
  rw [hA,hB]
  nlinarith only [hsum,hcost]
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_SmallFieldCount
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

lemma cardinal_small_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h z : ι→ℝ) {t a b : ℝ} (ht : 0 < t)
    (hh : ((Finset.univ.filter (fun i=>|h i| < 2*t)).card:ℝ) ≤ a)
    (hz : (∑ i,z i^2) ≤ t^2*b) :
    ((Finset.univ.filter (fun i=>|h i+z i| < t)).card:ℝ) ≤ a+b := by
  let S := Finset.univ.filter (fun i=>|h i+z i| < t)
  let B := Finset.univ.filter (fun i=>|h i| < 2*t)
  let L := Finset.univ.filter (fun i=>t < |z i|)
  have hsub : S ⊆ B ∪ L := by
    intro i hi
    have hfield : |h i+z i| < t := (Finset.mem_filter.mp hi).2
    by_cases hb : |h i| < 2*t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have he : h i=(h i+z i)+(-z i) := by ring
      have habs := abs_add_le (h i+z i) (-z i)
      rw [← he,abs_neg] at habs
      linarith only [hfield,le_of_not_gt hb,habs]
  have hL : t^2*(L.card:ℝ) ≤ ∑ i,z i^2 := by
    calc
      _ = ∑ _i ∈ L,t^2 := by simp [mul_comm]
      _ ≤ ∑ i ∈ L,z i^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := ((Finset.mem_filter.mp hi).2 : t < |z i|)
        have hs := (sq_le_sq₀ ht.le (abs_nonneg (z i))).mpr hh.le
        simpa only [sq_abs] using hs
      _ ≤ ∑ i,z i^2 := Finset.sum_le_univ_sum_of_nonneg (fun i=>sq_nonneg (z i))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le B L)
  have hcard' : (S.card:ℝ) ≤ (B.card:ℝ)+(L.card:ℝ) := by exact_mod_cast hcard
  have hLb : (L.card:ℝ) ≤ b := by
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp (hL.trans hz)
  exact hcard'.trans (add_le_add hh hLb)

lemma coupling_spin_norm_square (g : Disorder n) {M : ℝ} (hM : 0 ≤ M)
    (hJ : ‖Matrix.of (coupling g)‖ ≤ M) (x : Spin n) :
    (∑ i,(∑ j,coupling g i j*spinValue (x j))^2) ≤ M^2*(n:ℝ) := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i=>spinValue (x i))
  let w := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (Matrix.of (coupling g)) v
  have hv : ‖v‖^2=(n:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i,spinValue (x i)^2)=(n:ℝ)
    simp
  have hw : ‖w‖ ≤ M*‖v‖ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hJ) (norm_nonneg v))
  have hw2 := (sq_le_sq₀ (norm_nonneg w) (mul_nonneg hM (norm_nonneg v))).mpr hw
  rw [mul_pow,hv,EuclideanSpace.real_norm_sq_eq] at hw2
  exact hw2

lemma all_configurations_small_fields (g : Disorder n) (h : Fin n→ℝ) {M t α : ℝ}
    (hM : 0 ≤ M) (ht : 0 < t) (hJ : ‖Matrix.of (coupling g)‖ ≤ M)
    (hB : ((Finset.univ.filter (fun i=>|h i| < 2*t)).card:ℝ) ≤ α*(n:ℝ)/2)
    (hsmall : M^2 ≤ t^2*α/2) :
    ∀ x : Spin n,((Finset.univ.filter (fun i=>|localField g h i x| < t)).card:ℝ) ≤ α*(n:ℝ) := by
  intro x
  have hnorm := coupling_spin_norm_square g hM hJ x
  have hnorm' : (∑ i,(∑ j,coupling g i j*spinValue (x j))^2) ≤ t^2*(α*(n:ℝ)/2) := by
    apply hnorm.trans
    have hh := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n)
    nlinarith only [hh]
  have hc := cardinal_small_sum h (fun i=>∑ j,coupling g i j*spinValue (x j)) ht hB hnorm'
  have he : α*(n:ℝ)/2+α*(n:ℝ)/2=α*(n:ℝ) := by ring
  rw [he] at hc
  exact hc
end SKGap

end
end

section
noncomputable section
namespace SKGap
open scoped RealInnerProductSpace

lemma positive_form_cauchy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫) (u v : E) :
    ⟪u,H v⟫^2 ≤ ⟪u,H u⟫*⟪v,H v⟫ := by
  have hh : ∀ t : ℝ,0 ≤ ⟪v,H v⟫*(t*t)+(2*⟪u,H v⟫)*t+⟪u,H u⟫ := by
    intro t
    have hp := hpos (u+t • v)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right] at hp
    have he : ⟪v,H u⟫=⟪u,H v⟫ := (real_inner_comm (H u) v).trans (hH u v)
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hh
  unfold discrim at hd
  nlinarith only [hd]

lemma curvature_poincare_on_kernel_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫)
    {ρ : ℝ} (hρ : 0 < ρ) (hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫)
    (f : E) (hf : f ∈ (LinearMap.ker H)ᗮ) :
    ρ*⟪f,f⟫ ≤ ⟪f,H f⟫ := by
  have hrange : f ∈ LinearMap.range H := by
    rwa [← hH.orthogonal_range,Submodule.orthogonal_orthogonal] at hf
  obtain ⟨g,rfl⟩ := hrange
  have hc := positive_form_cauchy H hH hpos (H g) g
  have hg := hcurv g
  have hp := hpos (H g)
  have hn : 0 ≤ ⟪H g,H g⟫ := real_inner_self_nonneg
  have hh : ρ*⟪H g,H g⟫^2 ≤ ⟪H g,H (H g)⟫*⟪H g,H g⟫ := by
    calc
      _ ≤ ρ*(⟪H g,H (H g)⟫*⟪g,H g⟫) := mul_le_mul_of_nonneg_left hc hρ.le
      _ = ⟪H g,H (H g)⟫*(ρ*⟪g,H g⟫) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hp
  by_cases hz : ⟪H g,H g⟫=0
  · rw [hz,mul_zero];exact hp
  · have hpos' : 0 < ⟪H g,H g⟫ := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith only [hh,hpos']
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators RealInnerProductSpace
variable {n : ℕ}

lemma gibbsScale_inner (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    ⟪gibbsScale g h f,gibbsScale g h k⟫=expectation g h (fun x=>f x*k x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  unfold dotProduct expectation
  apply Finset.sum_congr rfl
  intro x _
  change sqrt (mass g h x)*k x*(sqrt (mass g h x)*f x)=mass g h x*(f x*k x)
  calc
    _ = sqrt (mass g h x)^2*(f x*k x) := by ring
    _ = _ := by rw [sq_sqrt (mass_nonneg g h x)]

lemma heatBathLinear_const (g : Disorder n) (h : Fin n→ℝ) (c : ℝ) :
    heatBathLinear g h (fun _=>c)=0 := by
  funext x
  simp only [heatBathLinear,heatBathGenerator,LinearMap.coe_mk,AddHom.coe_mk,
    conditionalExpectation_const,sub_self,Finset.sum_const_zero,Pi.zero_apply]

lemma heatBathLinear_kernel (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    heatBathLinear g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hf
    apply (dirichlet_eq_zero_iff g h f).mp
    rw [← heatBathGenerator_form]
    change expectation g h (fun x=>f x*(heatBathLinear g h f) x)=0
    rw [hf]
    simp only [Pi.zero_apply,mul_zero,expectation_const]
  · intro hf
    have he : f=(fun _=>f (fun _=>false)) := funext (fun x=>hf x (fun _=>false))
    rw [he,heatBathLinear_const]

lemma heatBath_curvature_poincare (g : Disorder n) (h : Fin n→ℝ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ f : Spin n→ℝ,ρ*dirichlet g h f ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2)) (f : Spin n→ℝ) :
    ρ*variance g h f ≤ dirichlet g h f := by
  let S := gibbsScale g h
  let H : EuclideanSpace ℝ (Spin n) →ₗ[ℝ] EuclideanSpace ℝ (Spin n) :=
    S.toLinearMap ∘ₗ heatBathLinear g h ∘ₗ S.symm.toLinearMap
  have hHS (k : Spin n→ℝ) : H (S k)=S (heatBathLinear g h k) := by simp [H]
  have hH : H.IsSymmetric := by
    intro u v
    obtain ⟨u,rfl⟩ := S.surjective u
    obtain ⟨v,rfl⟩ := S.surjective v
    rw [hHS,hHS]
    exact (gibbsScale_inner g h _ _).trans ((heatBathGenerator_adjoint g h u v).trans
      (gibbsScale_inner g h _ _).symm)
  have hform (k : Spin n→ℝ) : ⟪S k,H (S k)⟫=dirichlet g h k := by
    rw [hHS,gibbsScale_inner]
    exact heatBathGenerator_form g h k
  have hpos : ∀ v,0 ≤ ⟪v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform]
    exact dirichlet_nonneg g h k
  have hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform,hHS,gibbsScale_inner]
    simpa only [sq,heatBathLinear,LinearMap.coe_mk,AddHom.coe_mk] using hc k
  let f₀ := f-(fun _=>expectation g h f)
  have hm : expectation g h f₀=0 := by
    change expectation g h (fun x=>f x-expectation g h f)=0
    rw [expectation_sub,expectation_const,sub_self]
  have hker : S f₀ ∈ (LinearMap.ker H)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨k,rfl⟩ := S.surjective v
    have hk : heatBathLinear g h k=0 := by
      have hh := LinearMap.mem_ker.mp hv
      rw [hHS] at hh
      exact S.injective (by simpa using hh)
    have hk' := (heatBathLinear_kernel g h k).mp hk
    have he : k=(fun _=>k (fun _=>false)) := funext (fun x=>hk' x (fun _=>false))
    rw [gibbsScale_inner,he,expectation_const_mul,hm,mul_zero]
  have hh := curvature_poincare_on_kernel_orthogonal H hH hpos hρ hcurv (S f₀) hker
  rw [gibbsScale_inner,hform] at hh
  have hd : dirichlet g h f₀=dirichlet g h f := by
    rw [← heatBathGenerator_form,← heatBathGenerator_form]
    have he : heatBathLinear g h f₀=heatBathLinear g h f := by
      simp only [f₀,map_sub,heatBathLinear_const,sub_zero]
    change expectation g h (fun x=>f₀ x*(heatBathLinear g h f₀) x)=_
    rw [he]
    have hz : expectation g h (heatBathLinear g h f)=0 := by
      change expectation g h (fun x=>∑ i,(f x-conditionalExpectation g h i f x))=0
      rw [expectation_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [expectation_sub,expectation_conditionalExpectation,sub_self]
    simp only [f₀,Pi.sub_apply,sub_mul]
    rw [expectation_sub,expectation_const_mul,hz,mul_zero,sub_zero]
    rfl
  rw [hd] at hh
  simpa only [variance,f₀,Pi.sub_apply,sq] using hh
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalDeterministic
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

lemma one_sub_tanh_sq (x : ℝ) : 1-tanh x^2=1/cosh x^2 := by
  rw [tanh_eq_sinh_div_cosh]
  have hc := (cosh_pos x).ne'
  have he := cosh_sq_sub_sinh_sq x
  field_simp
  nlinarith only [he]

lemma variance_tanh_le_cosh {t x : ℝ} (ht : 0 ≤ t) (hx : t ≤ |x|) :
    1-tanh x^2 ≤ 1/cosh t^2 := by
  rw [one_sub_tanh_sq]
  have hcosh : cosh t ≤ cosh x := cosh_le_cosh.mpr (by simpa only [abs_of_nonneg ht] using hx)
  have hs := (sq_le_sq₀ (cosh_pos t).le (cosh_pos x).le).mpr hcosh
  exact one_div_le_one_div_of_le (sq_pos_of_pos (cosh_pos t)) hs

theorem terminal_deterministic (g : Disorder n) (h : Fin n→ℝ) {M t α ε R : ℝ}
    (hM : 0 ≤ M) (ht : 0 < t) (hε : 0 ≤ ε)
    (hJ : ‖Matrix.of (coupling g)‖ ≤ M)
    (hU : ‖terminalU g‖ ≤ M) (hQ : ‖terminalQ g‖ ≤ M)
    (hc : ∀ i j,|tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i,∑ j,tanh (coupling g i j)^4 ≤ R)
    (hsparse : ∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
      ∀ w : EuclideanSpace ℝ (Fin n),(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalU g) w⟫| ≤ ε*‖w‖^2 ∧
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalQ g) w⟫| ≤ ε*‖w‖^2)
    (hB : ((Finset.univ.filter (fun i=>|h i| < 2*t)).card:ℝ) ≤ α*(n:ℝ)/2)
    (hsmall : M^2 ≤ t^2*α/2)
    (hnum : 800000*R+400001*(ε+M*(2*sqrt (1/cosh t^2)+1/cosh t^2)) ≤ 1/2) :
    ∀ f : Spin n→ℝ,variance g h f ≤ 2*dirichlet g h f := by
  have hη : (0:ℝ) ≤ 1/cosh t^2 := by positivity
  have hS := all_configurations_small_fields g h hM ht hJ hB hsmall
  let k := ε+M*(2*sqrt (1/cosh t^2)+1/cosh t^2)
  have hcurv (f : Spin n→ℝ) : (1/2:ℝ)*dirichlet g h f ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2) := by
    let q := fun x=>∑ i,siteVariance g h i x*spinGradient i f x^2
    have hq : expectation g h q=dirichlet g h f := by
      dsimp [q]
      rw [expectation_sum,dirichlet_weighted]
    have hform (x : Spin n) :
        (∑ i,∑ j,tanh (coupling g i j)*weightedGradient g h i f x*weightedGradient g h j f x) ≤ k*q x ∧
        (∑ i,∑ j,tanh (coupling g i j)^2*|weightedGradient g h i f x*weightedGradient g h j f x|) ≤ k*q x := by
      let S := Finset.univ.filter (fun i=>|localField g h i x| < t)
      have hv (i : Fin n) : 0 ≤ siteVariance g h i x := (siteVariance_pos g h i x).le
      have hvsmall (i : Fin n) (hi : i ∉ S) : siteVariance g h i x ≤ 1/cosh t^2 := by
        apply variance_tanh_le_cosh ht.le
        have hi' : ¬|localField g h i x| < t := by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hi
        exact le_of_not_gt hi'
      have hboundU := weighted_sparse_form (terminalU g) S (fun i=>siteVariance g h i x)
        (fun i=>spinGradient i f x) hη hε hM hv (fun i=>siteVariance_le_one g h i x) hvsmall hU
        (fun w hw=>(hsparse S (hS x) w hw).1)
      have hboundQ := weighted_sparse_form (terminalQ g) S (fun i=>siteVariance g h i x)
        (fun i=>|spinGradient i f x|) hη hε hM hv (fun i=>siteVariance_le_one g h i x) hvsmall hQ
        (fun w hw=>(hsparse S (hS x) w hw).2)
      constructor
      · exact (le_abs_self _).trans hboundU
      · simp only [sq_abs] at hboundQ
        have he : (∑ i,∑ j,tanh (coupling g i j)^2*|weightedGradient g h i f x*weightedGradient g h j f x|)=
            ∑ i,∑ j,terminalQ g i j*(siteVariance g h i x*|spinGradient i f x|)*
              (siteVariance g h j x*|spinGradient j f x|) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [terminalQ,Matrix.of_apply,weightedGradient,abs_mul,abs_of_nonneg (hv i),abs_of_nonneg (hv j)]
          ring
        rw [he]
        exact (le_abs_self _).trans hboundQ
    have hu := expectation_mono g h (fun x=>(hform x).1)
    have hq' := expectation_mono g h (fun x=>(hform x).2)
    rw [expectation_const_mul,hq] at hu hq'
    have hl := gibbs_signed_curvature g h f hc hR
    have hd := dirichlet_nonneg g h f
    have hn : 800000*R+400001*k ≤ 1/2 := hnum
    have hh := mul_le_mul_of_nonneg_right hn hd
    nlinarith only [hu,hq',hl,hh]
  intro f
  have hp := heatBath_curvature_poincare g h (by norm_num : (0:ℝ) < 1/2) hcurv f
  linarith only [hp]
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalRates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

lemma terminalEntryScale_tendsto : Tendsto terminalEntryScale atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ=>1/sqrt (sqrt (n:ℝ))) atTop (𝓝 0)
  simpa only [one_div,Function.comp_def] using
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp (tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))))

end SKGap

end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

lemma terminalMatrixData_forms {M α ε : ℝ} (g : Disorder n) (hg : terminalMatrixData M α ε g) :
    ∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
      ∀ w : EuclideanSpace ℝ (Fin n),(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalU g) w⟫| ≤ ε*‖w‖^2 ∧
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalQ g) w⟫| ≤ ε*‖w‖^2 := by
  intro S hS w hw
  exact ⟨supported_quad_le_principal _ _ (hg.2.2.2.2.2 S hS).1 w hw,
    supported_quad_le_principal _ _ (hg.2.2.2.2.2 S hS).2 w hw⟩
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalMatrixMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

lemma continuous_coupling_entry (i k : Fin n) : Continuous (fun g : Disorder n=>coupling g i k) := by
  unfold coupling
  split_ifs <;> fun_prop

lemma continuous_coupling_matrix : Continuous (fun g : Disorder n=>Matrix.of (coupling g)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  exact continuous_coupling_entry i

lemma continuous_tanh_real : Continuous tanh :=
  continuous_iff_continuousAt.mpr (fun x=>(hasDerivAt_tanh x).continuousAt)

lemma continuous_terminalU : Continuous (terminalU (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  exact continuous_tanh_real.comp (continuous_coupling_entry i k)

lemma continuous_terminalQ : Continuous (terminalQ (n:=n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  exact (continuous_tanh_real.comp (continuous_coupling_entry i k)).pow 2

lemma continuous_principalOperatorNorm (S : Finset (Fin n)) :
    Continuous (fun M : Matrix (Fin n) (Fin n) ℝ=>principalOperatorNorm M S) := by
  unfold principalOperatorNorm
  exact (continuous_matrixOperator.comp (by unfold Matrix.submatrix;fun_prop)).norm

lemma terminalMatrixData_measurable (M α ε : ℝ) :
    MeasurableSet {g : Disorder n | terminalMatrixData M α ε g} := by
  classical
  unfold terminalMatrixData
  simp only [ofPred_and,ofPred_forall]
  apply MeasurableSet.inter
    (MeasurableSet.iInter (fun i=>MeasurableSet.iInter (fun k=>measurableSet_le (continuous_coupling_entry i k).abs.measurable measurable_const)))
  apply MeasurableSet.inter (measurableSet_le continuous_coupling_matrix.norm.measurable measurable_const)
  apply MeasurableSet.inter (measurableSet_le continuous_terminalU.norm.measurable measurable_const)
  apply MeasurableSet.inter (measurableSet_le continuous_terminalQ.norm.measurable measurable_const)
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    exact (continuous_finsetSum _ (fun k _=>(continuous_tanh_real.comp (continuous_coupling_entry i k)).pow 4)).measurable
  · apply MeasurableSet.iInter
    intro S
    apply MeasurableSet.iInter
    intro _
    exact (measurableSet_le ((continuous_principalOperatorNorm S).comp continuous_terminalU).measurable measurable_const).inter
      (measurableSet_le ((continuous_principalOperatorNorm S).comp continuous_terminalQ).measurable measurable_const)
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

lemma sparse_parameters {j ε : ℝ} (hj : 0 < j) (hε : 0 < ε) :
    ∃ α l : ℝ,0 < α ∧ α < 1/2 ∧ 0 ≤ l ∧ 2*sqrt (j*α) ≤ ε/6 ∧
      0 < ε^2/(36*π^2*j)-(l*α+log (1+exp (-l))) ∧
      0 < ε/(4*j)-(l*α+log (1+exp (-l))+α*log 2) := by
  let δ := min (ε^2/(72*π^2*j)) (ε/(8*j))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have ht : Tendsto (fun l : ℝ=>log (1+exp (-l))) atTop (𝓝 0) := by
    have hplus : Tendsto (fun l : ℝ=>1+exp (-l)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.add tendsto_exp_neg_atTop_nhds_zero : Tendsto (fun l : ℝ=>1+exp (-l)) atTop (𝓝 (1+0)))
    have h := (continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hplus
    simpa only [Function.comp_def, log_one] using h
  obtain ⟨l,hl,hlδ⟩ := ((eventually_ge_atTop (0:ℝ)).and (ht.eventually (gt_mem_nhds (by linarith only [hδ] : (0:ℝ) < δ/2)))).exists
  let α := min (1/4:ℝ) (min (ε^2/(144*j)) (δ/(2*(l+log 2+1))))
  have hlog : (0:ℝ) ≤ log 2 := log_nonneg (by norm_num)
  have hden : 0 < 2*(l+log 2+1) := by linarith only [hl,hlog]
  have hα : 0 < α := lt_min (by norm_num) (lt_min (by positivity) (div_pos hδ hden))
  have hαmax : α ≤ 1/4 := min_le_left _ _
  have hαedge : α ≤ ε^2/(144*j) := (min_le_right _ _).trans (min_le_left _ _)
  have hαrate : α ≤ δ/(2*(l+log 2+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : α*(l+log 2+1) ≤ δ/2 := by
    have h := (le_div_iff₀ hden).mp hαrate
    nlinarith only [h]
  have hedge : 2*sqrt (j*α) ≤ ε/6 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 144*j)).mp hαedge
    have hs := sq_sqrt (mul_nonneg hj.le hα.le)
    nlinarith only [hm,hs,sqrt_nonneg (j*α),hε]
  refine ⟨α,l,hα,(by linarith only [hαmax]),hl,hedge,?_,?_⟩
  · have hδ1 : δ ≤ ε^2/(72*π^2*j) := min_le_left _ _
    have ha := mul_nonneg hα.le hlog
    have he : ε^2/(36*π^2*j)=2*(ε^2/(72*π^2*j)) := by ring
    rw [he]
    nlinarith only [hδ1,hδ,hprod,hlδ,ha,hα]
  · have hδ2 : δ ≤ ε/(8*j) := min_le_right _ _
    have he : ε/(4*j)=2*(ε/(8*j)) := by ring
    rw [he]
    nlinarith only [hδ2,hδ,hprod,hlδ,hα]
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalHighProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Filter Real
open scoped Topology

lemma tendsto_cosh_real_atTop : Tendsto cosh atTop atTop := by
  have he : Tendsto (fun x : ℝ=>exp x/2) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul,id_eq] using tendsto_exp_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 1/2)
  apply tendsto_atTop_mono _ he
  intro x
  rw [cosh_eq]
  have hp := exp_pos (-x)
  linarith only [hp]

lemma terminalTime_exists {M α ε : ℝ} (_hM : 0 ≤ M) (hα : 0 < α)
    (hε : 400001*ε < 1/4) :
    ∃ T : ℝ,0 < T ∧ M^2 ≤ (T/4)^2*α/2 ∧
      400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2)) ≤ 1/4 ∧
      exp (-T/8)*(exp 1-1) ≤ α/4 := by
  have hT4 : Tendsto (fun T : ℝ=>T/4) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm,one_mul,id_eq] using tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/4)
  have hs : Tendsto (fun T : ℝ=>1/cosh (T/4)^2) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp (tendsto_cosh_real_atTop.comp hT4)
    simpa only [Function.comp_apply,one_div,inv_pow,zero_pow (by decide : (2:ℕ) ≠ 0)] using h.pow 2
  have hsroot := hs.sqrt
  have hsfull : Tendsto (fun T : ℝ=>400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2))) atTop (𝓝 (400001*ε)) := by
    simpa only [sqrt_zero,mul_zero,add_zero] using (((hsroot.const_mul 2).add hs).const_mul M |>.const_add ε |>.const_mul 400001)
  have he : Tendsto (fun T : ℝ=>exp (-T/8)*(exp 1-1)) atTop (𝓝 0) := by
    have hT8 : Tendsto (fun T : ℝ=>T/8) atTop atTop := by
      simpa only [div_eq_mul_inv,mul_comm,one_mul,id_eq] using tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 1/8)
    simpa only [Function.comp_apply,neg_div,zero_mul] using (tendsto_exp_neg_atTop_nhds_zero.comp hT8).mul_const (exp 1-1)
  have ht : ∀ᶠ T : ℝ in atTop,4*sqrt (2*M^2/α)+1 ≤ T := eventually_ge_atTop _
  obtain ⟨T,⟨htT,htnum⟩,htp⟩ := (ht.and (hsfull.eventually (ge_mem_nhds hε))).and
    (he.eventually (ge_mem_nhds (by positivity : (0:ℝ) < α/4))) |>.exists
  refine ⟨T,?_,?_,htnum,htp⟩
  · have hr := sqrt_nonneg (2*M^2/α)
    linarith only [htT,hr]
  · have hr := sqrt_nonneg (2*M^2/α)
    have hsquare := sq_sqrt (by positivity : 0 ≤ 2*M^2/α)
    have hbound : 2*M^2/α ≤ (T/4)^2 := by nlinarith only [hr,hsquare,htT]
    have hmul := (div_le_iff₀ hα).mp hbound
    nlinarith only [hmul]
end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalProbability
attribute [-instance] _root_.OAI.SKGap.GaussianStep.instCoeFunPriorForallSpinReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

lemma spinValue_sign (b : Bool) : spinValue b=1 ∨ spinValue b= -1 := by
  cases b <;> simp

lemma rareCount_field (T : ℝ) (x : Spin n) (z : Fin n→ℝ) :
    rareCount (fun i=>{u : ℝ | |T*spinValue (x i)+sqrt T*u| < T/2}) z=
      ((Finset.univ.filter (fun i=>|observationField T x z i| < T/2)).card:ℝ) := by
  classical
  simp only [rareCount,observationField,Set.mem_ofPred_eq]
  simp only [Finset.sum_boole]
  rfl

lemma observation_smallField_tail {T α : ℝ} (hT : 0 < T)
    (hp : exp (-T/8)*(exp 1-1) ≤ α/4) (x : Spin n) :
    (channelReference n).real {z | α*(n:ℝ)/2 <
      ((Finset.univ.filter (fun i=>|observationField T x z i| < T/2)).card:ℝ)} ≤
        exp (-α*(n:ℝ)/4) := by
  classical
  have hh := rareCount_tail (fun _ : Fin n=>gaussianReal 0 1)
    (fun i=>{u : ℝ | |T*spinValue (x i)+sqrt T*u| < T/2})
    (fun _=>isOpen_lt (by fun_prop) continuous_const |>.measurableSet)
    (a:=α*(n:ℝ)/2) (fun i=>gaussian_observation_small hT (spinValue_sign (x i)))
  simp only [rareCount_field,Fintype.card_fin] at hh
  apply hh.trans
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith only [hm]

theorem terminal_probability_fixedSpin (g : Disorder n) {M T α ε R : ℝ}
    (hM : 0 ≤ M) (hT : 0 < T) (hε : 0 ≤ ε)
    (hJ : ‖Matrix.of (coupling g)‖ ≤ M)
    (hU : ‖terminalU g‖ ≤ M) (hQ : ‖terminalQ g‖ ≤ M)
    (hc : ∀ i j,|tanh (coupling g i j)| ≤ 1/1000)
    (hR : ∀ i,∑ j,tanh (coupling g i j)^4 ≤ R)
    (hsparse : ∀ S : Finset (Fin n),(S.card:ℝ) ≤ α*(n:ℝ) →
      ∀ w : EuclideanSpace ℝ (Fin n),(∀ i,i ∉ S → w i=0) →
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalU g) w⟫| ≤ ε*‖w‖^2 ∧
      |⟪w,Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (terminalQ g) w⟫| ≤ ε*‖w‖^2)
    (hsmall : M^2 ≤ (T/4)^2*α/2)
    (hnum : 800000*R+400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2)) ≤ 1/2)
    (hp : exp (-T/8)*(exp 1-1) ≤ α/4) (x : Spin n) :
    (channelReference n).real {z | ¬∀ f : Spin n→ℝ,
      variance g (observationField T x z) f ≤ 2*dirichlet g (observationField T x z) f} ≤
        exp (-α*(n:ℝ)/4) := by
  apply (measureReal_mono (μ:=channelReference n) ?_ (measure_ne_top _ _)).trans
    (observation_smallField_tail hT hp x)
  intro z hz
  by_contra hn
  change ¬α*(n:ℝ)/2 < ((Finset.univ.filter (fun i=>|observationField T x z i| < T/2)).card:ℝ) at hn
  have hb := le_of_not_gt hn
  apply hz
  apply terminal_deterministic g (observationField T x z) hM (by positivity : 0 < T/4) hε hJ hU hQ hc hR hsparse
    ?_ hsmall hnum
  simpa only [show 2*(T/4)=T/2 by ring] using hb

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Terminal_TerminalChannel
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

lemma channel_field_shift {T : ℝ} (hT : 0 ≤ T) (x : Spin n) (z : Fin n→ℝ) :
    (fun i=>sqrt T*(z i+sqrt T*spinValue (x i)))=observationField T x z := by
  funext i
  simp only [observationField]
  calc
    _ = sqrt T*z i+(sqrt T)^2*spinValue (x i) := by ring
    _ = _ := by rw [sq_sqrt hT];ring

lemma gaussianChannel_terminal_bad (g : Disorder n) {T c : ℝ} (hT : 0 ≤ T)
    (hh : ∀ x : Spin n,(channelReference n).real {z | ¬∀ f : Spin n→ℝ,
      variance g (observationField T x z) f ≤ 2*dirichlet g (observationField T x z) f} ≤ exp (-c*(n:ℝ))) :
    (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
      variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-c*(n:ℝ)) := by
  let B : Set (Fin n→ℝ) := {z | ¬∀ f : Spin n→ℝ,
    variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f}
  have hB : MeasurableSet B :=
    ((terminal_goodSet_closed g 2).measurableSet.compl).preimage (by fun_prop)
  have he := gaussianChannel_event g hT B hB
  have hx (x : Spin n) : channelReference n
      ((fun z : Fin n→ℝ=>fun i=>z i+sqrt T*spinValue (x i)) ⁻¹' B) ≤ ENNReal.ofReal (exp (-c*(n:ℝ))) := by
    have hb : ((fun z : Fin n→ℝ=>fun i=>z i+sqrt T*spinValue (x i)) ⁻¹' B)=
        {z | ¬∀ f : Spin n→ℝ,variance g (observationField T x z) f ≤
          2*dirichlet g (observationField T x z) f} := by
      ext z
      simp only [Set.mem_preimage,B,Set.mem_ofPred_eq,channel_field_shift hT]
    rw [hb]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      (by simpa only [measureReal_def,ENNReal.toReal_ofReal (exp_pos _).le] using hh x)
  have hs : (∑ x : Spin n,ENNReal.ofReal (mass g 0 x))=1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _=>mass_nonneg g 0 x),sum_mass]
    exact ENNReal.ofReal_one
  have hb : gaussianChannelLaw g T B ≤ ENNReal.ofReal (exp (-c*(n:ℝ))) := by
    rw [he]
    calc
      _ ≤ ∑ x,ENNReal.ofReal (mass g 0 x)*ENNReal.ofReal (exp (-c*(n:ℝ))) :=
        Finset.sum_le_sum (fun x _=>by gcongr;exact hx x)
      _ = _ := by rw [← Finset.sum_mul,hs,one_mul]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def,ENNReal.toReal_ofReal (exp_pos _).le] using hr
end SKGap

end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
variable {n : ℕ}

lemma terminalMatrixBound_nonneg {j : ℝ} (hj : 0 ≤ j) : 0 ≤ terminalMatrixBound j := by
  unfold terminalMatrixBound terminalRowBound
  have hlog : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  positivity

lemma terminal_endpoint_from_data {M α ε T : ℝ} (hM : 0 ≤ M) (hT : 0 < T) (hε : 0 ≤ ε)
    (hsmall : M^2 ≤ (T/4)^2*α/2)
    (hnum : 400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2)) ≤ 1/4)
    (hp : exp (-T/8)*(exp 1-1) ≤ α/4)
    (hn₁ : terminalEntryScale n ≤ 1/1000) (hn₂ : 800000*(M*terminalEntryScale n^2) ≤ 1/4)
    (g : Disorder n) (hg : terminalMatrixData M α ε g) :
    (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
      variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-(α/4)*(n:ℝ)) := by
  apply gaussianChannel_terminal_bad g hT.le
  intro x
  have hc (i k : Fin n) : |tanh (coupling g i k)| ≤ 1/1000 :=
    (abs_tanh_le_abs _).trans ((hg.1 i k).trans hn₁)
  have hh := terminal_probability_fixedSpin g hM hT hε hg.2.1 hg.2.2.1 hg.2.2.2.1 hc hg.2.2.2.2.1
    (terminalMatrixData_forms g hg) hsmall (by linarith only [hnum,hn₂]) hp x
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma terminal_numeric_eventually (M : ℝ) : ∀ᶠ n : ℕ in atTop,
    terminalEntryScale n ≤ 1/1000 ∧ 800000*(M*terminalEntryScale n^2) ≤ 1/4 := by
  have ht := (terminalEntryScale_tendsto.pow 2).const_mul M |>.const_mul 800000
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] at ht
  exact (terminalEntryScale_tendsto.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/1000))).and
    (ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/4)))

theorem terminal_gap_high_probability_oai {β : ℝ} (hβ : 0 < β) :
    ∃ T a : ℝ,0 < T ∧ 0 < a ∧ ∃ Ω : (n : ℕ)→Set (Disorder n),
      (∀ n,MeasurableSet (Ω n)) ∧
      Tendsto (fun n=>(disorderLaw β n).real (Ω n)) atTop (𝓝 1) ∧
      ∀ (n : ℕ) (g : Disorder n),g ∈ Ω n →
        (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
          variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-a*(n:ℝ)) := by
  let ε : ℝ := 1/(16*400001)
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨α,l,hα,hαhalf,hl,hedge,h₅,h₆⟩ := sparse_parameters (sq_pos_of_pos hβ) hε
  let M := terminalMatrixBound (β^2)
  have hM : 0 ≤ M := terminalMatrixBound_nonneg (sq_nonneg β)
  obtain ⟨T,hT,hsmall,hnum,hp⟩ := terminalTime_exists hM hα (show 400001*ε < 1/4 by norm_num [ε])
  obtain ⟨N,hN⟩ := eventually_atTop.mp (terminal_numeric_eventually M)
  let Ω : (n : ℕ)→Set (Disorder n) := fun n=>if N ≤ n then {g | terminalMatrixData M α ε g} else ∅
  have hΩ (n : ℕ) : MeasurableSet (Ω n) := by
    dsimp [Ω]
    split_ifs
    · exact terminalMatrixData_measurable M α ε
    · exact MeasurableSet.empty
  refine ⟨T,α/4,hT,(by positivity),Ω,hΩ,?_,?_⟩
  · apply Tendsto.congr' _ (terminalMatrixData_actual_whp hβ hα.le hε hl hedge h₅ h₆)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Ω,ite_eq_left hn]
    rfl
  · intro n g hg
    have hn : N ≤ n := by
      by_contra hn
      simp only [Ω,ite_eq_right hn,Set.mem_empty_iff_false] at hg
    have hd : terminalMatrixData M α ε g := by simpa only [Ω,ite_eq_left hn,Set.mem_ofPred_eq] using hg
    exact terminal_endpoint_from_data hM hT hε.le hsmall hnum hp (hN n hn).1 (hN n hn).2 g hd
end SKGap

end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.terminal_gap_high_probability_oai := @OAI.SKGap.terminal_gap_high_probability_oai

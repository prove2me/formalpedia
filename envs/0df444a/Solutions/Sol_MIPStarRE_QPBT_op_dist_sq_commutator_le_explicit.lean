-- Prove2me | solution 1 for MIPStarRE.QPBT.op_dist_sq_commutator_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:21:09.095061+00:00
-- url     : https://prove2.me/submissions/e0b6c001-9023-4283-b113-fd9af45e87e0

-- Generated proof for MIPStarRE.QPBT.op_dist_sq_commutator_le_explicit.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_joint_marginal_product
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_left_fiber_contraction
import Theorems.Thm_MIPStarRE_QPBT_DistanceCalculus_right_fiber_contraction
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_le_of_le_of_le
import Theorems.Thm_MIPStarRE_QPBT_opFamilyDistSq_mul_left_le

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/Calculus.lean. -/
/-!
# Consistency and state-dependent distance inequalities

This module collects the operator-level part of the state-dependent distance
calculus: the two-sided comparison between consistency defect and distance, the
monotonicity of the distance under products and function-indexed operators, its
triangle inequality and data-processing bound, and the approximate commutation
obtained from a joint projective refinement. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results run from blueprint `fact:agreement` through
`lem:commutation-analysis`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus



















/-- Formalization-only same-question specialization of
`opFamilyDistSq_mul_left_le`, obtained by pushing the question distribution
along the diagonal map. -/
private theorem opFamilyDistSq_mul_left_same_question_le {X α β γ ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → (α × β) → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (C : X → α → γ → _root_.LIDT.MIPStarRE.Quantum.Op ι) (ψ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hC : ∀ x a, (1 - ∑ c : γ, (C x a c)ᴴ * C x a c).PosSemidef)
    (h : _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ ≤ δ) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ
      (fun x (abc : (α × β) × γ) =>
        C x abc.1.1 abc.2 * A x (abc.1.1, abc.1.2))
      (fun x (abc : (α × β) × γ) =>
        C x abc.1.1 abc.2 * B x (abc.1.1, abc.1.2)) ψ ≤ δ := by
  classical
  let μdiag : _root_.LIDT.MIPStarRE.LDT.Distribution (X × X) := μ.map (fun x => (x, x))
  have hbase : _root_.MIPStarRE.QPBT.opFamilyDistSq (μdiag.map Prod.fst) A B ψ ≤ δ := by
    simpa [μdiag, _root_.MIPStarRE.QPBT.opFamilyDistSq, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map] using h
  have hout := _root_.MIPStarRE.QPBT.opFamilyDistSq_mul_left_le μdiag A B C ψ δ hC hbase
  simpa [μdiag, _root_.MIPStarRE.QPBT.opFamilyDistSq, _root_.LIDT.MIPStarRE.LDT.Distribution.avgOver_map] using hout









end MIPStarRE.QPBT

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

























































































/-- Formalization-only auxiliary lemma for Proposition 4.29: state-dependent
operator-family distance is symmetric. -/
theorem opFamilyDistSq_symm {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ B A ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq
  apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
  intro x
  apply Finset.sum_congr rfl
  intro a _
  simp only [_root_.MIPStarRE.QPBT.applyOperatorToState, map_sub, LinearMap.sub_apply]
  rw [norm_sub_rev]

end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/TensorSupport.lean. -/
/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective























/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: compatible projective marginals multiply to the joint effect in
reverse order. -/
theorem joint_marginal_product_rev {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : _root_.LIDT.MIPStarRE.Quantum.Measurement ((α × β) × γ) ι)
    (hM : _root_.MIPStarRE.QPBT.Measurement.IsProjective M)
    (a : α) (b : β) (c : γ) :
    ((M.postprocess (fun abc => (abc.1.1, abc.2))).effect (a, c)) *
        ((M.postprocess (fun abc => abc.1)).effect (a, b)) =
      M.effect ((a, b), c) := by
  have habHerm := _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian
    (M.postprocess (fun abc => abc.1)) (a, b)
  have hacHerm := _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian
    (M.postprocess (fun abc => (abc.1.1, abc.2))) (a, c)
  have hjointHerm := _root_.MIPStarRE.QPBT.DistanceCalculus.measurement_effect_hermitian M ((a, b), c)
  have h := congrArg Matrix.conjTranspose (_root_.MIPStarRE.QPBT.DistanceCalculus.joint_marginal_product M hM a b c)
  rw [Matrix.conjTranspose_mul, hacHerm, habHerm, hjointHerm] at h
  exact h

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: operators placed on opposite tensor factors commute. -/
theorem left_right_commute {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : _root_.LIDT.MIPStarRE.Quantum.Op ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Op ιB) :
    _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) A * _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) B =
      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) B * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) A := by
  rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor,
    _root_.LIDT.MIPStarRE.LDT.rightTensor_mul_leftTensor_eq_opTensor]

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: reindexing an operator family along an equivalence preserves its
distance. -/
theorem opFamilyDistSq_reindex {X α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (e : α ≃ β) (A B : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ =
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ (fun x b => A x (e.symm b))
        (fun x b => B x (e.symm b)) ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact Fintype.sum_equiv e
    (fun a => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
    (fun b => ‖_root_.MIPStarRE.QPBT.applyOperatorToState (A x (e.symm b) - B x (e.symm b)) ψ‖ ^ 2)
    (by intro a; simp)

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: pointwise equal operator families have equal state-dependent
distance. -/
theorem opFamilyDistSq_congr {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B A' B' : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ A' B' ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [hA x a, hB x a]

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: pointwise equal operator differences have equal state-dependent
distance. -/
theorem opFamilyDistSq_congr_sub {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X) (A B A' B' : X → α → _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (h : ∀ x a, A x a - B x a = A' x a - B' x a) :
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ A B ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ A' B' ψ := by
  unfold _root_.MIPStarRE.QPBT.opFamilyDistSq _root_.LIDT.MIPStarRE.LDT.avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [h x a]





end MIPStarRE.QPBT.DistanceCalculus

/-!
# Consistency and state-dependent distance inequalities

This module collects the operator-level part of the state-dependent distance
calculus: the two-sided comparison between consistency defect and distance, the
monotonicity of the distance under products and function-indexed operators, its
triangle inequality and data-processing bound, and the approximate commutation
obtained from a joint projective refinement. The statements retain explicit
constants that the paper absorbs into asymptotic notation.

## References

The source results run from blueprint `fact:agreement` through
`lem:commutation-analysis`, with paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-461`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem solution :
    ∀ {X α β γ ιA ιB : Type*}
      [Fintype α] [DecidableEq α]
      [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
      [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
      (μ : _root_.LIDT.MIPStarRE.LDT.Distribution X)
      (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (α × β) ιA)
      (B : X → _root_.LIDT.MIPStarRE.Quantum.Measurement ((α × β) × γ) ιB)
      (D : X → _root_.LIDT.MIPStarRE.Quantum.Measurement (α × γ) ιA)
      (ψ : EuclideanSpace ℂ (ιA × ιB)) (δ : ℝ),
      (∀ x, _root_.MIPStarRE.QPBT.Measurement.IsProjective (B x)) →
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x ab => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect ab) 1)
        (fun x ab => _root_.MIPStarRE.QPBT.heteroKron 1 (((B x).postprocess
          (fun abc => abc.1)).effect ab)) ψ ≤ δ →
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x ac => _root_.MIPStarRE.QPBT.heteroKron ((D x).effect ac) 1)
        (fun x ac => _root_.MIPStarRE.QPBT.heteroKron 1 (((B x).postprocess
          (fun abc => (abc.1.1, abc.2))).effect ac)) ψ ≤ δ →
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) => _root_.MIPStarRE.QPBT.heteroKron
          (((A x).effect (abc.1.1, abc.1.2)) * ((D x).effect (abc.1.1, abc.2)) -
            ((D x).effect (abc.1.1, abc.2)) * ((A x).effect (abc.1.1, abc.1.2))) 1)
        (fun _ _ => 0) ψ ≤ 16 * δ := by
  intro X α β γ ιA ιB _ _ _ _ _ _ _ _ _ _ μ A B D ψ δ hB hAB hDB
  let AL : X → (α × β) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x ab => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((A x).effect ab)
  let DL : X → (α × γ) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x ac => _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((D x).effect ac)
  let BAB : X → (α × β) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x ab => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA)
      (((B x).postprocess (fun abc => abc.1)).effect ab)
  let BAC : X → (α × γ) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x ac => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA)
      (((B x).postprocess (fun abc => (abc.1.1, abc.2))).effect ac)
  let BJ : X → ((α × β) × γ) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x abc => _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((B x).effect abc)
  let FAD : X → ((α × β) × γ) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x abc => AL x abc.1 * DL x (abc.1.1, abc.2)
  let FDA : X → ((α × β) × γ) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x abc => DL x (abc.1.1, abc.2) * AL x abc.1
  let FMidAD : X → ((α × β) × γ) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x abc => AL x abc.1 * BAC x (abc.1.1, abc.2)
  let FMidDA : X → ((α × β) × γ) → _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB) :=
    fun x abc => DL x (abc.1.1, abc.2) * BAB x abc.1
  have hAB' : _root_.MIPStarRE.QPBT.opFamilyDistSq μ AL BAB ψ ≤ δ := by
    simpa [AL, BAB, _root_.MIPStarRE.QPBT.heteroKron, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.rightTensor] using hAB
  have hDB' : _root_.MIPStarRE.QPBT.opFamilyDistSq μ DL BAC ψ ≤ δ := by
    simpa [DL, BAC, _root_.MIPStarRE.QPBT.heteroKron, _root_.LIDT.MIPStarRE.LDT.leftTensor, _root_.LIDT.MIPStarRE.LDT.rightTensor] using hDB
  have hAL : ∀ x a,
      (1 - ∑ b : β, (AL x (a, b))ᴴ * AL x (a, b)).PosSemidef := by
    intro x a
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.left_fiber_contraction (A x) a
  have hDL : ∀ x a,
      (1 - ∑ c : γ, (DL x (a, c))ᴴ * DL x (a, c)).PosSemidef := by
    intro x a
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.left_fiber_contraction (D x) a
  have hBAB : ∀ x a,
      (1 - ∑ b : β, (BAB x (a, b))ᴴ * BAB x (a, b)).PosSemidef := by
    intro x a
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.right_fiber_contraction
      ((B x).postprocess (fun abc => abc.1)) a
  have hBAC : ∀ x a,
      (1 - ∑ c : γ, (BAC x (a, c))ᴴ * BAC x (a, c)).PosSemidef := by
    intro x a
    exact _root_.MIPStarRE.QPBT.DistanceCalculus.right_fiber_contraction
      ((B x).postprocess (fun abc => (abc.1.1, abc.2))) a
  have hAD_mid_raw := opFamilyDistSq_mul_left_same_question_le μ DL BAC
    (fun x a b => AL x (a, b)) ψ δ hAL hDB'
  have hAD_mid : _root_.MIPStarRE.QPBT.opFamilyDistSq μ FAD FMidAD ψ ≤ δ := by
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_reindex μ (_root_.MIPStarRE.QPBT.DistanceCalculus.swapLast α β γ)] at hAD_mid_raw
    simpa [_root_.MIPStarRE.QPBT.DistanceCalculus.swapLast, FAD, FMidAD] using hAD_mid_raw
  have hmid_AD_joint_raw := opFamilyDistSq_mul_left_same_question_le μ AL BAB
    (fun x a c => BAC x (a, c)) ψ δ hBAC hAB'
  have hmid_AD_joint : _root_.MIPStarRE.QPBT.opFamilyDistSq μ FMidAD BJ ψ ≤ δ := by
    have hcross (x : X) (abc : (α × β) × γ) :
        BAC x (abc.1.1, abc.2) * AL x abc.1 =
          AL x abc.1 * BAC x (abc.1.1, abc.2) :=
      (_root_.MIPStarRE.QPBT.DistanceCalculus.left_right_commute _ _).symm
    have hcollapse (x : X) (abc : (α × β) × γ) :
        BAC x (abc.1.1, abc.2) * BAB x abc.1 = BJ x abc := by
      change _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => (z.1.1, z.2))).effect
              (abc.1.1, abc.2)) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => z.1)).effect abc.1) =
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((B x).effect abc)
      rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
      exact congrArg (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA))
        (_root_.MIPStarRE.QPBT.DistanceCalculus.joint_marginal_product_rev (B x) (hB x)
          abc.1.1 abc.1.2 abc.2)
    simpa only [FMidAD, hcross, hcollapse] using hmid_AD_joint_raw
  have hAD_joint : _root_.MIPStarRE.QPBT.opFamilyDistSq μ FAD BJ ψ ≤ 4 * δ := by
    have h := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le μ FAD FMidAD BJ ψ δ δ
      hAD_mid hmid_AD_joint
    linarith
  have hDA_mid_raw := opFamilyDistSq_mul_left_same_question_le μ AL BAB
    (fun x a c => DL x (a, c)) ψ δ hDL hAB'
  have hDA_mid : _root_.MIPStarRE.QPBT.opFamilyDistSq μ FDA FMidDA ψ ≤ δ := by
    simpa [FDA, FMidDA] using hDA_mid_raw
  have hmid_DA_joint_raw :
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x (acb : (α × γ) × β) => BAB x (acb.1.1, acb.2) * DL x acb.1)
        (fun x (acb : (α × γ) × β) => BAB x (acb.1.1, acb.2) * BAC x acb.1)
        ψ ≤ δ :=
    opFamilyDistSq_mul_left_same_question_le μ DL BAC
      (fun x a b => BAB x (a, b)) ψ δ hBAB hDB'
  have hmid_DA_joint : _root_.MIPStarRE.QPBT.opFamilyDistSq μ FMidDA BJ ψ ≤ δ := by
    have hcross (x : X) (abc : (α × β) × γ) :
        BAB x abc.1 * DL x (abc.1.1, abc.2) =
          DL x (abc.1.1, abc.2) * BAB x abc.1 :=
      (_root_.MIPStarRE.QPBT.DistanceCalculus.left_right_commute _ _).symm
    have hcollapse (x : X) (abc : (α × β) × γ) :
        BAB x abc.1 * BAC x (abc.1.1, abc.2) = BJ x abc := by
      change _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => z.1)).effect abc.1) *
          _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA)
            (((B x).postprocess (fun z => (z.1.1, z.2))).effect
              (abc.1.1, abc.2)) =
        _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA) ((B x).effect abc)
      rw [_root_.LIDT.MIPStarRE.LDT.rightTensor_mul_rightTensor]
      exact congrArg (_root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ιA))
        (_root_.MIPStarRE.QPBT.DistanceCalculus.joint_marginal_product (B x) (hB x)
          abc.1.1 abc.1.2 abc.2)
    have hreindexed : _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) =>
          BAB x abc.1 * DL x (abc.1.1, abc.2))
        (fun x (abc : (α × β) × γ) =>
          BAB x abc.1 * BAC x (abc.1.1, abc.2)) ψ ≤ δ := by
      calc
        _root_.MIPStarRE.QPBT.opFamilyDistSq μ
            (fun x (abc : (α × β) × γ) =>
              BAB x abc.1 * DL x (abc.1.1, abc.2))
            (fun x (abc : (α × β) × γ) =>
              BAB x abc.1 * BAC x (abc.1.1, abc.2)) ψ =
          _root_.MIPStarRE.QPBT.opFamilyDistSq μ
            (fun x (acb : (α × γ) × β) =>
              BAB x (acb.1.1, acb.2) * DL x acb.1)
            (fun x (acb : (α × γ) × β) =>
              BAB x (acb.1.1, acb.2) * BAC x acb.1) ψ := by
            simpa only [_root_.MIPStarRE.QPBT.DistanceCalculus.swapLast_symm_apply] using
              (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_reindex μ (_root_.MIPStarRE.QPBT.DistanceCalculus.swapLast α β γ)
                (fun x (acb : (α × γ) × β) =>
                  BAB x (acb.1.1, acb.2) * DL x acb.1)
                (fun x (acb : (α × γ) × β) =>
                  BAB x (acb.1.1, acb.2) * BAC x acb.1) ψ).symm
        _ ≤ δ := hmid_DA_joint_raw
    calc
      _root_.MIPStarRE.QPBT.opFamilyDistSq μ FMidDA BJ ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ
          (fun x (abc : (α × β) × γ) =>
            BAB x abc.1 * DL x (abc.1.1, abc.2))
          (fun x (abc : (α × β) × γ) =>
            BAB x abc.1 * BAC x (abc.1.1, abc.2)) ψ := by
        exact (_root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_congr μ _ _ FMidDA BJ ψ hcross hcollapse).symm
      _ ≤ δ := hreindexed
  have hDA_joint : _root_.MIPStarRE.QPBT.opFamilyDistSq μ FDA BJ ψ ≤ 4 * δ := by
    have h := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le μ FDA FMidDA BJ ψ δ δ
      hDA_mid hmid_DA_joint
    linarith
  have hjoint_DA : _root_.MIPStarRE.QPBT.opFamilyDistSq μ BJ FDA ψ ≤ 4 * δ := by
    rw [← _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_symm]
    exact hDA_joint
  have hcomm := _root_.MIPStarRE.QPBT.opFamilyDistSq_le_of_le_of_le μ FAD BJ FDA ψ
    (4 * δ) (4 * δ) hAD_joint hjoint_DA
  have hraw : _root_.MIPStarRE.QPBT.opFamilyDistSq μ FAD FDA ψ ≤ 16 * δ := by linarith
  calc
    _root_.MIPStarRE.QPBT.opFamilyDistSq μ
        (fun x (abc : (α × β) × γ) => _root_.MIPStarRE.QPBT.heteroKron
          (((A x).effect abc.1 * (D x).effect (abc.1.1, abc.2)) -
            (D x).effect (abc.1.1, abc.2) * (A x).effect abc.1) 1)
        (fun _ _ => 0) ψ = _root_.MIPStarRE.QPBT.opFamilyDistSq μ FAD FDA ψ := by
      apply _root_.MIPStarRE.QPBT.DistanceCalculus.opFamilyDistSq_congr_sub
      intro x abc
      change _root_.MIPStarRE.QPBT.heteroKron
          ((A x).effect abc.1 * (D x).effect (abc.1.1, abc.2) -
            (D x).effect (abc.1.1, abc.2) * (A x).effect abc.1) 1 - 0 =
        _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((A x).effect abc.1) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((D x).effect (abc.1.1, abc.2)) -
          _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((D x).effect (abc.1.1, abc.2)) *
            _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ιB) ((A x).effect abc.1)
      rw [_root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, _root_.LIDT.MIPStarRE.LDT.leftTensor_mul_leftTensor, sub_zero]
      exact (_root_.LIDT.MIPStarRE.LDT.leftTensor_sub _ _).symm
    _ ≤ 16 * δ := hraw

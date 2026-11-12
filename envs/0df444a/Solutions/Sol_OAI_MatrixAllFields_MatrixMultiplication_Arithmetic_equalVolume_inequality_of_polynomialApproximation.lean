-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.equalVolume_inequality_of_polynomialApproximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:43.958653+00:00
-- url     : https://prove2.me/submissions/b4c57b05-b1f1-4ed8-919a-7709902a81a9

import Mathlib
import Definitions.Def_MatrixFields
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_Arithmetic_rectangular_rpow_omega_le_of_rank_growth

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_ComplexDotPairing
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.sidePermutation_refl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.retarget_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

end Algebra

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

theorem RankAtMost.repeat_batch {S : Tensor K U V W} {k r R B : ℕ}
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hfit : R ≤ B * k) :
    RankAtMost (directSum (fun _ : Fin R => S)) (B * r) := by
  classical
  let f : Fin R → Fin B × Fin k := fun i => finProdFinEquiv.symm (Fin.castLE hfit i)
  have hf : Function.Injective f := finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hfit)
  have hbig := (diagonal_rankAtMost (K := K) (Fin B)).product hbatch
  simp only [Fintype.card_fin] at hbig
  rcases hbig with ⟨a, b, c, heq⟩
  let liftU : (Fin R × U) → Fin B × (Fin k × U) := fun x => ((f x.1).1, (f x.1).2, x.2)
  let liftV : (Fin R × V) → Fin B × (Fin k × V) := fun y => ((f y.1).1, (f y.1).2, y.2)
  let liftW : (Fin R × W) → Fin B × (Fin k × W) := fun z => ((f z.1).1, (f z.1).2, z.2)
  refine ⟨fun i x => a i (liftU x), fun i y => b i (liftV y),
    fun i z => c i (liftW z), ?_⟩
  funext x y z
  change directSum (fun _ : Fin R => S) x y z =
    ∑ i, rankOne (a i) (b i) (c i) (liftU x) (liftV y) (liftW z)
  have hentry := congrFun (congrFun (congrFun heq (liftU x)) (liftV y)) (liftW z)
  rw [← hentry]
  by_cases hxy : x.1 = y.1
  · by_cases hxz : x.1 = z.1
    · have hyz : y.1 = z.1 := hxy.symm.trans hxz
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hyz]
    · have hn : f x.1 ≠ f z.1 := fun h => hxz (hf h)
      have hs : (f x.1).1 ≠ (f z.1).1 ∨ (f x.1).2 ≠ (f z.1).2 := by
        by_cases hfirst : (f x.1).1 = (f z.1).1
        · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
        · exact Or.inl hfirst
      rcases hs with hs | hs <;>
        simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxz, hs]
  · have hn : f x.1 ≠ f y.1 := fun h => hxy (hf h)
    have hs : (f x.1).1 ≠ (f y.1).1 ∨ (f x.1).2 ≠ (f y.1).2 := by
      by_cases hfirst : (f x.1).1 = (f y.1).1
      · exact Or.inr (fun hsecond => hn (Prod.ext hfirst hsecond))
      · exact Or.inl hfirst
    rcases hs with hs | hs <;>
      simp [directSum, Tensor.product, diagonal, liftU, liftV, liftW, hxy, hs]

theorem RankAtMost.batch_substitute [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r b : ℕ}
    (hT : RankAtMost T r)
    (hbatch : RankAtMost (directSum (fun _ : Fin r => S)) b) :
    RankAtMost (Tensor.product T S) b := by
  classical
  rcases hT with ⟨a, c, e, rfl⟩
  let A : (X × U) → (Fin r × U) → K :=
    fun x i => if x.2 = i.2 then a i.1 x.1 else 0
  let B : (Y × V) → (Fin r × V) → K :=
    fun y i => if y.2 = i.2 then c i.1 y.1 else 0
  let C : (Z × W) → (Fin r × W) → K :=
    fun z i => if z.2 = i.2 then e i.1 z.1 else 0
  have heq : Tensor.restrict A B C (directSum (fun _ : Fin r => S)) =
      Tensor.product (fun x y z => ∑ i, rankOne (a i) (c i) (e i) x y z) S := by
    funext x y z
    simp [Tensor.restrict, directSum, Tensor.product, rankOne, A, B, C,
      Fintype.sum_prod_type, ite_and, ite_mul, mul_ite, Finset.sum_mul]
  rw [← heq]
  exact hbatch.restrict A B C

theorem RankAtMost.batch_product [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r B : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r)
    (hfit : R ≤ B * k) : RankAtMost (Tensor.product T S) (B * r) :=
  hT.batch_substitute (hbatch.repeat_batch hfit)

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_TerminalRelabel
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

theorem matrixCoefficients_rank_of_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F] {r : ℕ}
    (hproduct : RankAtMost (product (matrixCoefficients (K := K) A B C)
      (matrixCoefficients D E F)) r) :
    RankAtMost (matrixCoefficients (K := K) (A × D) (B × E) (C × F)) r := by
  have h := hproduct.pullback
    (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  have heq : pullback
      (fun x : (A × D) × (B × E) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      (fun y : (B × E) × (C × F) => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
      (fun z : (C × F) × (A × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      (product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)) =
      matrixCoefficients (K := K) (A × D) (B × E) (C × F) := by
    funext x y z
    exact matrixCoefficients_product x y z
  rw [heq] at h
  exact h

theorem matrixCoefficients_power [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (n : ℕ) (x : (Fin n → A) × (Fin n → B))
    (y : (Fin n → B) × (Fin n → C)) (z : (Fin n → C) × (Fin n → A)) :
    Tensor.power (matrixCoefficients (K := K) A B C) n
      (fun i => (x.1 i, x.2 i)) (fun i => (y.1 i, y.2 i)) (fun i => (z.1 i, z.2 i)) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) x y z := by
  simp only [Tensor.power, matrixCoefficients, Fintype.prod_boole, forall_and, ← funext_iff]

end Tensor






namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

theorem RankAtMost.directSum_pullback {ι X' Y' Z' : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z} {r : ℕ} (h : RankAtMost (directSum T) r)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (directSum (fun i => Tensor.pullback fx fy fz (T i))) r :=
  h.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

theorem directSum_power {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum T) n) =
      directSum (fun f : Fin n → ι =>
        fun x y z => ∏ i, T (f i) (x i) (y i) (z i)) := by
  funext x y z
  change (∏ i, if x.1 i = y.1 i ∧ x.1 i = z.1 i then
      T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      ∏ i, T (x.1 i) (x.2 i) (y.2 i) (z.2 i) else 0
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff]

theorem directSum_const_power {ι : Type*} [DecidableEq ι]
    (T : Tensor K X Y Z) (n : ℕ) :
    pullback (directSumPowerEquiv ι X n) (directSumPowerEquiv ι Y n)
      (directSumPowerEquiv ι Z n) (power (directSum (fun _ : ι => T)) n) =
      directSum (fun _ : Fin n → ι => power T n) :=
  directSum_power (fun _ : ι => T) n

theorem RankAtMost.directSum_const_of_power {ι : Type*} [DecidableEq ι]
    {T : Tensor K X Y Z} {n R : ℕ}
    (h : RankAtMost (Tensor.power (directSum (fun _ : ι => T)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι => Tensor.power T n)) R := by
  have h' := h.pullback (directSumPowerEquiv ι X n)
    (directSumPowerEquiv ι Y n) (directSumPowerEquiv ι Z n)
  rw [Tensor.directSum_const_power] at h'
  exact h'

section Rectangular

variable {A B C : Type*}

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrixCoefficients_directSum_rank_of_power
    {ι : Type*} [DecidableEq ι] {n R : ℕ}
    (h : RankAtMost
      (power (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) n) R) :
    RankAtMost (directSum (fun _ : Fin n → ι =>
      matrixCoefficients (K := K) (Fin n → A) (Fin n → B) (Fin n → C))) R := by
  have h' := h.directSum_const_of_power.directSum_pullback
    (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
    (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
    (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
  have heq : pullback
      (fun x : (Fin n → A) × (Fin n → B) => fun i => (x.1 i, x.2 i))
      (fun y : (Fin n → B) × (Fin n → C) => fun i => (y.1 i, y.2 i))
      (fun z : (Fin n → C) × (Fin n → A) => fun i => (z.1 i, z.2 i))
      (power (matrixCoefficients (K := K) A B C) n) =
      matrixCoefficients (Fin n → A) (Fin n → B) (Fin n → C) := by
    funext x y z
    exact matrixCoefficients_power n x y z
  simpa only [heq] using h'

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end




section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K X Y Z : Type*} [Field K]

theorem RankAtMost.card_le_of_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Tensor K X Y Z} {r : ℕ} (hT : RankAtMost T r)
    (x : ι → X) (y : ι → Y) (z : ι → Z)
    (hidentity : ∀ i j, T (x i) (y i) (z j) = if i = j then 1 else 0) :
    Fintype.card ι ≤ r := by
  rcases hT with ⟨a, b, c, heq⟩
  let L : Matrix ι (Fin r) K := fun i q => a q (x i) * b q (y i)
  let R : Matrix (Fin r) ι K := fun q j => c q (z j)
  have hmul : L * R = (1 : Matrix ι ι K) := by
    funext i j
    change (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = if i = j then 1 else 0
    calc
      (∑ q, (a q (x i) * b q (y i)) * c q (z j)) = T (x i) (y i) (z j) :=
        (congrFun (congrFun (congrFun heq (x i)) (y i)) (z j)).symm
      _ = _ := hidentity i j
  have hle : (1 : Matrix ι ι K).rank ≤ r := by
    rw [← hmul]
    exact (Matrix.rank_mul_le_left L R).trans (by
      simpa only [Fintype.card_fin] using Matrix.rank_le_card_width L)
  simpa only [Matrix.rank_one] using hle

theorem directSum_matrixCoefficients_rank_lower
    {Label A B C : Type*} [Fintype Label] [Fintype A] [Fintype C]
    [DecidableEq Label] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Nonempty B] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : Label => matrixCoefficients (K := K) A B C)) r) :
    Fintype.card Label * (Fintype.card C * Fintype.card A) ≤ r := by
  classical
  let b₀ : B := Classical.choice inferInstance
  have hminor : ∀ i j : Label × (C × A),
      directSum (fun _ : Label => matrixCoefficients (K := K) A B C)
        (i.1, (i.2.2, b₀)) (i.1, (b₀, i.2.1)) j = if i = j then 1 else 0 := by
    intro i j
    simp only [directSum, matrixCoefficients]
    split_ifs <;> simp_all [Prod.ext_iff]
  have hlower := h.card_le_of_identity
    (fun i : Label × (C × A) => (i.1, (i.2.2, b₀)))
    (fun i : Label × (C × A) => (i.1, (b₀, i.2.1)))
    (fun i : Label × (C × A) => i) hminor
  simpa only [Fintype.card_prod] using hlower

theorem directSum_square_rank_lower (k n r : ℕ) (hn : 0 < n)
    (h : RankAtMost (directSum (fun _ : Fin k =>
      matrixCoefficients (K := K) (Fin n) (Fin n) (Fin n))) r) :
    k * n ^ 2 ≤ r := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simpa only [Fintype.card_fin, pow_two] using directSum_matrixCoefficients_rank_lower h

end Tensor
end MatrixMultiplication.Foundation

end




end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ArithmeticExponent
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic
section

theorem admissibleExponent_iff_rectangular_one (F : Type*) [Field F] (τ : ℝ) :
    AdmissibleExponent F τ ↔ RectangularAdmissibleExponent F 1 τ := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    rw [innerSize_one]
    exact hbound n hn
  · intro h ε hε
    obtain ⟨C, hC, hbound⟩ := h ε hε
    refine ⟨C, hC, ?_⟩
    intro n hn
    have hnBound := hbound n hn
    rw [innerSize_one] at hnBound
    exact hnBound

@[simp] theorem rectangularOmega_one (F : Type*) [Field F] :
    rectangularOmega F 1 = omega F := by
  unfold rectangularOmega omega
  congr 1
  ext τ
  exact (admissibleExponent_iff_rectangular_one F τ).symm

end

end MatrixMultiplication.Arithmetic

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ComplexAsymptoticRecurrence
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

theorem affine_recurrence_shifted (x : ℕ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ t, x (t + 1) ≤ a * x t + (a - 1) * c) :
    ∀ t, x t + c ≤ a ^ t * (x 0 + c) := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    calc
      x (t + 1) + c ≤ a * x t + (a - 1) * c + c := add_le_add (hstep t) (le_refl c)
      _ = a * (x t + c) := by ring
      _ ≤ a * (a ^ t * (x 0 + c)) := mul_le_mul_of_nonneg_left ih ha
      _ = a ^ (t + 1) * (x 0 + c) := by rw [pow_succ]; ring

theorem affine_recurrence_bound (x : ℕ → ℝ) (a b : ℝ) (ha : 1 < a) (hb : 0 ≤ b)
    (hstep : ∀ t, x (t + 1) ≤ a * x t + b) :
    ∀ t, x t ≤ a ^ t * (x 0 + b / (a - 1)) := by
  have hpos : 0 < a - 1 := sub_pos.mpr ha
  have hcancel : (a - 1) * (b / (a - 1)) = b := by
    field_simp [ne_of_gt hpos]
  have hshift := affine_recurrence_shifted x a (b / (a - 1)) (by linarith)
    (fun t => by rw [hcancel]; exact hstep t)
  intro t
  have hc : 0 ≤ b / (a - 1) := div_nonneg hb hpos.le
  exact (le_add_of_nonneg_right hc).trans (hshift t)

end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ComplexPolynomialPowerGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open Filter
open scoped Topology

namespace MatrixMultiplication.Foundation

theorem tendsto_affine_mul_geometric_zero (D C : ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hq_one : q < 1) :
    Tendsto (fun n : ℕ => (D * (n : ℝ) + C) * q ^ n) atTop (𝓝 0) := by
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hq hq_one).const_mul D
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq_one).const_mul C
  simpa only [mul_zero, add_zero, add_mul, mul_assoc] using hlinear.add hconstant

theorem power_le_of_eventually_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ᶠ n : ℕ in atTop, a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  by_contra hnot
  have hra : r < a := lt_of_not_ge hnot
  have ha : 0 < a := hr.trans_lt hra
  have hratio : 0 ≤ r / a := div_nonneg hr ha.le
  have hratio_one : r / a < 1 := (div_lt_one ha).2 hra
  have hsmall :=
    (tendsto_affine_mul_geometric_zero D C hratio hratio_one).eventually_lt_const
      (show (0 : ℝ) < 1 from zero_lt_one)
  rcases (h.and hsmall).exists with ⟨n, hbound, hlt⟩
  have hge : (1 : ℝ) ≤ (D * (n : ℝ) + C) * (r / a) ^ n := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos ha n)).2 (by simpa only [one_mul] using hbound)
  exact (not_lt_of_ge hge) hlt

theorem power_le_of_forall_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  apply power_le_of_eventually_pow_le_affine_mul_pow hr
  exact eventually_atTop.2 ⟨1, fun n hn => h n (Nat.zero_lt_one.trans_le hn)⟩

theorem power_le_of_forall_pow_le_linear_mul_pow (D : ℕ) {a r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ ((D * n + 1 : ℕ) : ℝ) * r ^ n) :
    a ≤ r := by
  apply power_le_of_forall_pow_le_affine_mul_pow (D := (D : ℝ)) (C := 1) hr
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h

end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ComplexRectangularASI
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.branchOperation_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFiniteFamily.Execution.step_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_afterC _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.historyTensor_initial _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialExact.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialStep.canonicalize_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.Tensor.sidePermutation_refl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.retarget_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

theorem le_batchCount_mul (R : ℕ) {k : ℕ} (hk : 0 < k) :
    R ≤ batchCount R k * k := by
  have hdiv := Nat.div_add_mod (R + k - 1) k
  have hmod := Nat.mod_lt (R + k - 1) hk
  rw [Nat.mul_comm k ((R + k - 1) / k)] at hdiv
  unfold batchCount
  omega

theorem batchCount_mul_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    batchCount R k * k < R + k := by
  have hmul := Nat.div_mul_le_self (R + k - 1) k
  unfold batchCount
  omega

theorem batchCount_cast_lt (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) < (R : ℝ) / (k : ℝ) + 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmul : (batchCount R k : ℝ) * (k : ℝ) < (R : ℝ) + (k : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (Nat.cast_lt (α := ℝ)).mpr (batchCount_mul_lt R hk)
  calc
    (batchCount R k : ℝ) < ((R : ℝ) + (k : ℝ)) / (k : ℝ) :=
      (lt_div_iff₀ hkR).mpr hmul
    _ = (R : ℝ) / (k : ℝ) + 1 := by rw [add_div, div_self (ne_of_gt hkR)]

theorem batchCount_cast_le (R : ℕ) {k : ℕ} (hk : 0 < k) :
    (batchCount R k : ℝ) ≤ (R : ℝ) / (k : ℝ) + 1 :=
  (batchCount_cast_lt R hk).le

theorem batchCount_mul_cast_le (R r : ℕ) {k : ℕ} (hk : 0 < k) :
    ((batchCount R k * r : ℕ) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
  calc
    ((batchCount R k * r : ℕ) : ℝ) = (batchCount R k : ℝ) * (r : ℝ) := by
      rw [Nat.cast_mul]
    _ ≤ ((R : ℝ) / (k : ℝ) + 1) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right (batchCount_cast_le R hk) (Nat.cast_nonneg r)
    _ = (r : ℝ) / (k : ℝ) * (R : ℝ) + (r : ℝ) := by
      simp only [div_eq_mul_inv]
      ring

theorem batchRank_succ_le_affine {k : ℕ} (hk : 0 < k) (r t : ℕ) :
    (batchRank k r (t + 1) : ℝ) ≤
      (r : ℝ) / (k : ℝ) * (batchRank k r t : ℝ) + (r : ℝ) := by
  rw [batchRank_succ]
  exact batchCount_mul_cast_le (batchRank k r t) r hk

namespace Tensor

variable {K X Y Z U V W A B : Type*} [CommSemiring K]

theorem RankAtMost.batch_product_ceiling [Fintype U] [Fintype V] [Fintype W]
    {T : Tensor K X Y Z} {S : Tensor K U V W} {R k r : ℕ}
    (hT : RankAtMost T R)
    (hbatch : RankAtMost (directSum (fun _ : Fin k => S)) r) (hk : 0 < k) :
    RankAtMost (Tensor.product T S) (batchCount R k * r) :=
  hT.batch_product hbatch (le_batchCount_mul R hk)

end Tensor
end MatrixMultiplication.Foundation

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

namespace Tensor

theorem matrixCoefficients_fin_one_rank {K : Type*} [CommSemiring K] :
    RankAtMost (matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1)) 1 := by
  have heq : matrixCoefficients (K := K) (Fin 1) (Fin 1) (Fin 1) =
      rankOne (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
    funext x y z
    have hxy : x.2 = y.1 := Subsingleton.elim _ _
    have hyz : y.2 = z.1 := Subsingleton.elim _ _
    have hzx : z.2 = x.1 := Subsingleton.elim _ _
    simp [matrixCoefficients, rankOne, hxy, hyz, hzx]
  rw [heq]
  exact rankOne_rankAtMost _ _ _

end Tensor

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Tensor

open MatrixMultiplication.Foundation.Tensor

theorem rectangular_rank_of_injective
    {K A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (matrixCoefficients (K := K) A B C) R)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (matrixCoefficients (K := K) A' B' C') R := by
  have hp := h.pullback (fun x : A' × B' => (f x.1, g x.2))
    (fun y : B' × C' => (g y.1, j y.2))
    (fun z : C' × A' => (j z.1, f z.2))
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext x y z
  simp only [pullback, matrixCoefficients, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_rank_of_injective
    {K ι κ A B C A' B' C' : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq κ]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq A'] [DecidableEq B'] [DecidableEq C'] {R : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) R)
    (e : κ → ι) (he : Function.Injective e)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    RankAtMost (directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) R := by
  have hp := h.pullback
    (fun x : κ × (A' × B') => (e x.1, (f x.2.1, g x.2.2)))
    (fun y : κ × (B' × C') => (e y.1, (g y.2.1, j y.2.2)))
    (fun z : κ × (C' × A') => (e z.1, (j z.2.1, f z.2.2)))
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext x y z
  simp only [pullback, directSum, matrixCoefficients,
    he.eq_iff, hf.eq_iff, hg.eq_iff, hj.eq_iff]

theorem rectangular_directSum_power_rank {K : Type*} [CommSemiring K]
    {a b c L R t : ℕ}
    (h : RankAtMost (power (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) t) R) :
    RankAtMost (directSum (fun _ : Fin (L ^ t) =>
      matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))) R := by
  have hmatrix := matrixCoefficients_directSum_rank_of_power h
  let tags : Fin (L ^ t) ≃ (Fin t → Fin L) := Fintype.equivOfCardEq (by simp)
  let rows : Fin (a ^ t) ≃ (Fin t → Fin a) := Fintype.equivOfCardEq (by simp)
  let inner : Fin (b ^ t) ≃ (Fin t → Fin b) := Fintype.equivOfCardEq (by simp)
  let cols : Fin (c ^ t) ≃ (Fin t → Fin c) := Fintype.equivOfCardEq (by simp)
  exact rectangular_directSum_rank_of_injective hmatrix tags tags.injective
    rows rows.injective inner inner.injective cols cols.injective

theorem rectangular_pow_batchRank {K : Type*} [CommSemiring K]
    {a b c L r : ℕ} (hL : 0 < L)
    (hbatch : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r) :
    ∀ t : ℕ, RankAtMost
      (matrixCoefficients (K := K) (Fin (a ^ t)) (Fin (b ^ t)) (Fin (c ^ t)))
      (batchRank L r t) := by
  intro t
  induction t with
  | zero =>
    simp only [batchRank_zero]
    exact matrixCoefficients_fin_one_rank
  | succ t ih =>
    let rows : Fin (a ^ (t + 1)) ≃ Fin (a ^ t) × Fin a :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let inner : Fin (b ^ (t + 1)) ≃ Fin (b ^ t) × Fin b :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    let cols : Fin (c ^ (t + 1)) ≃ Fin (c ^ t) × Fin c :=
      Fintype.equivOfCardEq (by simp [pow_succ])
    have hp := matrixCoefficients_rank_of_product (ih.batch_product_ceiling hbatch hL)
    have hr := rectangular_rank_of_injective hp
      rows rows.injective inner inner.injective cols cols.injective
    simpa only [batchRank_succ] using hr

theorem rectangular_directSum_cyclic_rank
    {K ι A B C : Type*} [CommSemiring K]
    [DecidableEq ι] [DecidableEq A] [DecidableEq B] [DecidableEq C] {r : ℕ}
    (h : RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r) :
    RankAtMost (directSum (fun _ : ι => matrixCoefficients (K := K) B C A)) r := by
  rcases h with ⟨a, b, c, heq⟩
  refine ⟨b, c, a, ?_⟩
  funext x y z
  have hcyc : directSum (fun _ : ι => matrixCoefficients (K := K) B C A) x y z =
      directSum (fun _ : ι => matrixCoefficients (K := K) A B C) z x y := by
    have htags : (x.1 = y.1 ∧ x.1 = z.1) ↔ (z.1 = x.1 ∧ z.1 = y.1) := by
      constructor
      · rintro ⟨hxy, hxz⟩
        exact ⟨hxz.symm, hxz.symm.trans hxy⟩
      · rintro ⟨hzx, hzy⟩
        exact ⟨hzx.symm.trans hzy, hzx.symm⟩
    simp only [directSum, htags]
    split_ifs
    · exact (matrixCoefficients_cyclic (K := K) x.2 y.2 z.2).symm
    · rfl
  rw [hcyc, congrFun (congrFun (congrFun heq z) x) y]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

theorem rectangular_directSum_rank_lower {K : Type*} [Field K]
    {a b L r : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : RankAtMost (directSum (fun _ : Fin L =>
      matrixCoefficients (K := K) (Fin a) (Fin b) (Fin a))) r) :
    L * a ^ 2 ≤ r ∧ L * (a * b) ≤ r := by
  let : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  let : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  constructor
  · simpa only [Fintype.card_fin, pow_two] using
      directSum_matrixCoefficients_rank_lower h
  · simpa only [Fintype.card_fin] using
      directSum_matrixCoefficients_rank_lower (rectangular_directSum_cyclic_rank h)

end Tensor
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

theorem mul_rpow_third_le_of_cube {u v w r : ℝ} (hv : 0 ≤ v) (hr : 0 ≤ r)
    (h : u ^ 3 * v ^ w ≤ r ^ 3) : u * v ^ (w / 3) ≤ r := by
  have hpow : (v ^ (w / 3)) ^ (3 : ℕ) = v ^ w := by
    rw [← Real.rpow_mul_natCast hv]
    congr 1
    norm_num
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hr
  simpa only [mul_pow, hpow] using h

end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialState
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.finish_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminal.terminalExecution_copies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Arithmetic

variable {F : Type*} [Field F]

theorem equalRectangular_inequality {a b L r : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hbatch : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  by_cases hL0 : L = 0
  · subst L
    simp
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by
    have hbR : (0 : ℝ) < (b : ℝ) :=
      (Real.rpow_pos_of_pos (by exact_mod_cast ha0) k).trans_le hab
    exact_mod_cast hbR
  have hlower := Tensor.rectangular_directSum_rank_lower ha0 hb0 hbatch
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hout : (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) := by exact_mod_cast hlower.1
    simpa only [mul_comm] using hh
  have hin : ((a * b : ℕ) : ℝ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * ((a * b : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlower.2
    simpa only [mul_comm] using hh
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hq : 1 < (r : ℝ) / (L : ℝ) := by nlinarith
  have hcost := affine_recurrence_bound (fun t => (batchRank L r t : ℝ))
    ((r : ℝ) / (L : ℝ)) (r : ℝ) hq (Nat.cast_nonneg r)
    (fun t => batchRank_succ_le_affine hL r t)
  have hbound : (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) / (L : ℝ) := by
    apply rectangular_rpow_omega_le_of_rank_growth
      (C := (batchRank L r 0 : ℝ) + (r : ℝ) / ((r : ℝ) / (L : ℝ) - 1))
      ha hk hab hout hin (batchRank L r)
    · exact Tensor.rectangular_pow_batchRank hL hbatch
    · intro t
      exact (hcost t).trans_eq (mul_comm _ _)
  simpa only [mul_comm] using (le_div_iff₀ hLR).mp hbound

theorem power_le_of_forall_pow_le_square_linear_mul_pow (d : ℕ) {x r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → x ^ n ≤ ((d * n + 1 : ℕ) : ℝ) ^ 2 * r ^ n) :
    x ≤ r := by
  apply power_le_of_forall_pow_le_linear_mul_pow (2 * d) hr
  intro n hn
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr n))
  have he := h (n * 2) (Nat.mul_pos hn (by decide))
  have hcount : d * (n * 2) + 1 = 2 * d * n + 1 := by ring
  simpa only [pow_mul, hcount, mul_pow] using he

theorem equalRectangular_inequality_of_polynomialApproximation
    {a b L r d D : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r d D) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  apply power_le_of_forall_pow_le_square_linear_mul_pow d (Nat.cast_nonneg r)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have h := equalRectangular_inequality hat hk habt
    (Tensor.rectangular_directSum_power_rank (FieldCoefficientExtraction.rank_power P t))
  simpa only [Nat.cast_pow, Nat.cast_mul, mul_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg a)] using h

theorem equalSquare_inequality_of_polynomialApproximation
    {n L r d D : ℕ} (hn : 1 ≤ n)
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin n) (Fin n) (Fin n))) r d D) :
    (L : ℝ) * (n : ℝ) ^ omega F ≤ (r : ℝ) := by
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    apply power_le_of_forall_pow_le_square_linear_mul_pow d (Nat.cast_nonneg r)
    intro t ht
    have hrank := Tensor.rectangular_directSum_power_rank
      (FieldCoefficientExtraction.rank_power P t)
    have hlower := MatrixMultiplication.Foundation.Tensor.directSum_square_rank_lower
      (L ^ t) (1 ^ t) ((d * t + 1) ^ 2 * r ^ t) (by simp) hrank
    have hcast := (Nat.cast_le (α := ℝ)).mpr hlower
    simpa only [one_pow, mul_one, Nat.cast_mul, Nat.cast_pow] using hcast
  · have h := equalRectangular_inequality_of_polynomialApproximation
      (by omega : 2 ≤ n) (by norm_num : (0 : ℝ) ≤ 1)
      (by simp : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ)) P
    simpa only [rectangularOmega_one] using h

theorem equalVolume_inequality_of_polynomialApproximation_oai
    {a b c L r d D : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin c))) r d D) :
    (L : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega F / 3) ≤ (r : ℝ) := by
  let tags : Fin (L ^ 3) ≃ (Fin L × Fin L) × Fin L :=
    Fintype.equivOfCardEq (by simp [pow_succ])
  let indices : Fin (a * b * c) ≃ Fin a × Fin b × Fin c :=
    Fintype.equivOfCardEq (by simp [mul_assoc])
  have Q := P.matrixCoefficients_directSum_symmetrized.matrixCoefficients_directSum_of_injective
    tags tags.injective indices indices.injective
  have h := equalSquare_inequality_of_polynomialApproximation
    (Nat.mul_pos (Nat.mul_pos ha hb) hc) Q
  apply mul_rpow_third_le_of_cube (Nat.cast_nonneg (a * b * c)) (Nat.cast_nonneg r)
  simpa only [Nat.cast_pow] using h

end Arithmetic
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

end MatrixMultiplication.AllFieldFiniteFamily

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.equalVolume_inequality_of_polynomialApproximation_oai.{u_1} := @OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.equalVolume_inequality_of_polynomialApproximation_oai.{u_1}

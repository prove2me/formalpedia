-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.workCapacity_first
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:11:47.148494+00:00
-- url     : https://prove2.me/submissions/753e93c9-28f4-4424-803e-40bb60541642

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Definitions.Def_OAIQ254M006

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

theorem homogeneousEntropy_normalized {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∑ a, p a = 1) :
    homogeneousEntropy p = finiteEntropy p := by
  simp [homogeneousEntropy, hp]

theorem entropyTerm_divide (x m : ℝ) :
    entropyTerm (x / m) = entropyTerm x / m + (x / m) * Real.log m := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hm : m = 0
  · simp [hm]
  rw [entropyTerm, Real.log_div hx hm]
  unfold entropyTerm
  ring

end

end MatrixMultiplication.AllFieldParameters

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters

theorem stageCPriorityLabel_at_part : ∀ distinguished part : Fin 3,
    stageCPriorityLabel distinguished part part = distinguished := by
  decide +kernel

theorem cPriority_at_part {K : ℕ} (h : PartC K) :
    cPriority h h.2 = stageCDistinguished (cShapeParent h) :=
  stageCPriorityLabel_at_part _ _

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_InitialLeafRates
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

theorem entropy_two_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) (p q : ℝ) :
    finiteEntropy (fun i => if i = a then p else if i = b then q else 0) =
      entropyTerm p + entropyTerm q := by
  unfold finiteEntropy
  calc
    _ = ∑ i : A, ((if i = a then entropyTerm p else 0) +
        (if i = b then entropyTerm q else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        simp [hab]
      · by_cases hj : i = b
        · subst i
          simp [hab.symm]
        · simp [hi, hj]
    _ = _ := by simp [Finset.sum_add_distrib]

end

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_NativeLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators

theorem indexedMarginalLaw_mass (support : List Shape) (p : Shape → ℚ)
    (hpos : ∀ u ∈ support, 0 ≤ p u) (htotal : (support.map p).sum = 1)
    (side : Fin 3) (hbound : ∀ u ∈ support, u side < 17) (k : Fin 17) :
    (indexedMarginalLaw support p hpos htotal side hbound).mass k =
      marginal support (fun u => (p u : ℝ)) side k := by
  simp only [indexedMarginalLaw, FiniteLaw.map_mass, RationalLaw.toFiniteLaw_mass,
    indexedRationalLaw, Fin.ext_iff, marginal, List.get_eq_getElem]
  exact Fin.sum_univ_fun_getElem support (fun u : Shape => if u side = k.val then (p u : ℝ) else 0)

theorem stageACapacity_first_entropy (g : Shape) (hg : g ∈ positiveInitial) :
    stageACapacity g 0 = finiteEntropy (stageAMarginalLaw g hg 0).mass := by
  rw [stageACapacity, nativeCapacity_first]
  simp only [Equiv.refl_apply]
  have hm : (stageAMarginalLaw g hg 0).mass =
      marginal (below g) (fun u => (stageALaw g u : ℝ)) 0 := by
    funext k
    exact indexedMarginalLaw_mass _ _ _ _ _ _ k
  rw [← hm]
  exact homogeneousEntropy_normalized _ (stageAMarginalLaw g hg 0).total

theorem stageBCapacity_first_entropy (t : Shape) (ht : t ∈ positiveSecond) :
    stageBCapacity t 0 =
      finiteEntropy (stageBMarginalLaw t ht (stageBPriority t 0)).mass := by
  rw [stageBCapacity, nativeCapacity_first]
  have hm : (stageBMarginalLaw t ht (stageBPriority t 0)).mass =
      marginal (below t) (fun u => (stageBLaw t u : ℝ)) (stageBPriority t 0) := by
    funext k
    exact indexedMarginalLaw_mass _ _ _ _ _ _ k
  rw [← hm]
  exact homogeneousEntropy_normalized _ (stageBMarginalLaw t ht (stageBPriority t 0)).total

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem placedLaw_sideMass {K : ℕ} (w : PlacedWork K) (s : Fin 3)
    (k : Fin 17) :
    JointPopulationRates.sideMass (placedLaw w).mass s k =
      ∑ b : w.1.Branch, if JointPopulation.shapeSide s (branchShape w b) = k
        then (branchProbability w.1 b : ℝ) else 0 := by
  unfold JointPopulationRates.sideMass
  simp only [placedLaw_mass]
  calc
    _ = ∑ u : JointPopulation.Shape, ∑ b : w.1.Branch,
        if branchShape w b = u then
          if JointPopulation.shapeSide s u = k then (branchProbability w.1 b : ℝ) else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : JointPopulation.shapeSide s u = k <;> simp [hu]
    _ = _ := by rw [Finset.sum_comm]; simp

end MatrixMultiplication.AllFieldActiveLaws






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_StageCCapacity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldStageCCapacity

open AllFieldHistory AllFieldParameters MatrixMultiplication.Foundation
open scoped BigOperators

private theorem stageCMarginal_symbolic (t u : Shape) (i : Fin 3) (k : Fin 17) :
    stageCMarginal t u i k = symbolicMarginal u (binaryParameter t u) i k := by
  unfold stageCMarginal symbolicMarginal
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b.val < 2 <;> simp [stageCWeight, hb]

private theorem symbolicMarginal_eq_2_1_1_0 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 2 1 1) d 0 k =
      if (0 : Fin 3) = stageCDistinguished (shape 2 1 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    (first | (simp [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; all_goals first | (norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; done) | rfl | decide) | (norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; done) | norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff])

private theorem symbolicMarginal_eq_2_1_1_1 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 2 1 1) d 1 k =
      if (1 : Fin 3) = stageCDistinguished (shape 2 1 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_2_1_1_2 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 2 1 1) d 2 k =
      if (2 : Fin 3) = stageCDistinguished (shape 2 1 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_2_1_0 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 2 1) d 0 k =
      if (0 : Fin 3) = stageCDistinguished (shape 1 2 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_2_1_1 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 2 1) d 1 k =
      if (1 : Fin 3) = stageCDistinguished (shape 1 2 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    (first | (simp [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; all_goals first | (norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; done) | rfl | decide) | (norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; done) | norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff])

private theorem symbolicMarginal_eq_1_2_1_2 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 2 1) d 2 k =
      if (2 : Fin 3) = stageCDistinguished (shape 1 2 1) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_1_2_0 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 1 2) d 0 k =
      if (0 : Fin 3) = stageCDistinguished (shape 1 1 2) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_1_2_1 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 1 2) d 1 k =
      if (1 : Fin 3) = stageCDistinguished (shape 1 1 2) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [stageCAtom, stageCDistinguished,
      stageCCanonicalAtom, shape, Matrix.cons_val_two,
      Fin.ext_iff] <;> ring

private theorem symbolicMarginal_eq_1_1_2_2 (d : ℝ) (k : Fin 17) :
    symbolicMarginal (shape 1 1 2) d 2 k =
      if (2 : Fin 3) = stageCDistinguished (shape 1 1 2) then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  simp only [symbolicMarginal, Fin.sum_univ_four]
  fin_cases k <;>
    (first | (simp [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; all_goals first | (norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; done) | rfl | decide) | (norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff]; done) | norm_num [stageCAtom, stageCDistinguished, stageCCanonicalAtom, shape, Matrix.cons_val_two, Fin.ext_iff])

private theorem symbolicMarginal_eq (u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (d : ℝ) (i : Fin 3) (k : Fin 17) :
    symbolicMarginal u d i k =
      if i = stageCDistinguished u then
        (if k = 0 then d / 2 else if k = 1 then 1 - d else if k = 2 then d / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0)  := by
  rcases positive_four_shapes u hu hpos with rfl | rfl | rfl <;> fin_cases i
  · exact symbolicMarginal_eq_1_1_2_0 d k
  · exact symbolicMarginal_eq_1_1_2_1 d k
  · exact symbolicMarginal_eq_1_1_2_2 d k
  · exact symbolicMarginal_eq_1_2_1_0 d k
  · exact symbolicMarginal_eq_1_2_1_1 d k
  · exact symbolicMarginal_eq_1_2_1_2 d k
  · exact symbolicMarginal_eq_2_1_1_0 d k
  · exact symbolicMarginal_eq_2_1_1_1 d k
  · exact symbolicMarginal_eq_2_1_1_2 d k

theorem stageCMarginal_eq (t u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (i : Fin 3) (k : Fin 17) :
    stageCMarginal t u i k =
      if i = stageCDistinguished u then
        (if k = 0 then (binaryParameter t u : ℝ) / 2
         else if k = 1 then 1 - (binaryParameter t u : ℝ)
         else if k = 2 then (binaryParameter t u : ℝ) / 2 else 0)
      else (if k = 0 then 1 / 2 else if k = 1 then 1 / 2 else 0) := by
  rw [stageCMarginal_symbolic]
  exact symbolicMarginal_eq u hu hpos _ i k

private theorem entropy_three_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (p q r : ℝ) :
    finiteEntropy (fun i => if i = a then p else if i = b then q
      else if i = c then r else 0) = entropyTerm p + entropyTerm q + entropyTerm r := by
  unfold finiteEntropy
  calc
    _ = ∑ i : A, ((if i = a then entropyTerm p else 0) +
        (if i = b then entropyTerm q else 0) + (if i = c then entropyTerm r else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases ha : i = a
      · subst i
        simp [hab, hac]
      · by_cases hb : i = b
        · subst i
          simp [ha, hbc]
        · by_cases hc : i = c <;> simp [ha, hb, hc, Ne.symm hac, Ne.symm hbc]
    _ = _ := by simp [Finset.sum_add_distrib]

private theorem entropy_distinguished (d : ℚ) :
    finiteEntropy (fun k : Fin 17 =>
      if k = 0 then (d : ℝ) / 2 else if k = 1 then 1 - (d : ℝ)
      else if k = 2 then (d : ℝ) / 2 else 0) = binaryEntropyRate d := by
  rw [entropy_three_points (0 : Fin 17) 1 2 (by decide) (by decide) (by decide)]
  simp only [entropyTerm_divide]
  unfold binaryEntropyRate
  ring

private theorem entropy_other :
    finiteEntropy (fun k : Fin 17 =>
      if k = 0 then (1 / 2 : ℝ) else if k = 1 then 1 / 2 else 0) = Real.log 2 := by
  rw [entropy_two_points (0 : Fin 17) 1 (by decide)]
  simp only [entropyTerm_divide]
  norm_num [entropyTerm]
  ring

theorem stageCMarginal_entropy (t u : Shape) (hu : u ∈ shapes 4)
    (hpos : positive u = true) (i : Fin 3) :
    finiteEntropy (stageCMarginal t u i) =
      if i = stageCDistinguished u then binaryEntropyRate (binaryParameter t u)
      else Real.log 2 := by
  change finiteEntropy (fun k => stageCMarginal t u i k) = _
  simp_rw [stageCMarginal_eq t u hu hpos]
  by_cases hi : i = stageCDistinguished u
  · simp only [hi, ite_true, if_true]
    exact entropy_distinguished _
  · simp only [hi, ite_false, if_false]
    exact entropy_other

theorem stageCMarginal_priority_entropy {K : ℕ} (h : PartC K) (i : Fin 3) :
    finiteEntropy (stageCMarginal (cParameterParent h) (cShapeParent h) (cPriority h i)) =
      if i = h.2 then binaryEntropyRate (binaryParameter (cParameterParent h) (cShapeParent h))
      else Real.log 2 := by
  rw [stageCMarginal_entropy (cParameterParent h) (cShapeParent h)
    (bShape_size h.1.val) h.1.property (cPriority h i)]
  have hi : cPriority h i = stageCDistinguished (cShapeParent h) ↔ i = h.2 := by
    rw [← cPriority_at_part h, Equiv.apply_eq_iff_eq]
  simp only [hi]

end MatrixMultiplication.AllFieldStageCCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ScheduledPositivity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldScheduledYield

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology

theorem workCapacity_stageC {K : ℕ} (h : PartC K) (i : Fin 3) :
    workCapacity (Work.stageC h) i = finiteEntropy
      (AllFieldStageCCapacity.stageCMarginal (cParameterParent h) (cShapeParent h)
        (cPriority h i)) := by
  rw [AllFieldStageCCapacity.stageCMarginal_priority_entropy]
  rfl

end MatrixMultiplication.AllFieldScheduledYield

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_GroupSelectionParameters
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldActiveLaws AllFieldScheduledYield
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem placedLaw_priority_sideMass {K : ℕ} (w : PlacedWork K)
    (i : Fin 3) :
    JointPopulationRates.sideMass (placedLaw w).mass (w.physicalOrder i) =
      canonicalSideMass w.1 (w.1.priority i) := by
  funext k
  rw [placedLaw_sideMass]
  simp only [Fin.ext_iff, branchShape, encodePhysicalShape_side,
    PlacedWork.physicalOrder, Equiv.trans_apply, Equiv.symm_apply_apply,
    canonicalSideMass, branchLaw_mass]

theorem canonicalSideMass_stageA {K : ℕ} (h : InitialPositive K) (s : Fin 3) :
    canonicalSideMass (.stageA h) s =
      (stageAMarginalLaw (initialShape h.val) h.property s).mass := by
  funext k
  rw [show (stageAMarginalLaw (initialShape h.val) h.property s).mass k =
      marginal (below (initialShape h.val))
        (fun u => (stageALaw (initialShape h.val) u : ℝ)) s k from
    indexedMarginalLaw_mass _ _ _ _ _ _ k]
  change (∑ b : ASplit h, if (below (initialShape h.val))[b.val] s = k.val
      then (stageALaw (initialShape h.val) (below (initialShape h.val))[b.val] : ℝ)
      else 0) = _
  exact Fin.sum_univ_fun_getElem _
    (fun u : Shape => if u s = k.val then (stageALaw (initialShape h.val) u : ℝ) else 0)

theorem canonicalSideMass_stageB {K : ℕ} (h : APositive K) (s : Fin 3) :
    canonicalSideMass (.stageB h) s =
      (stageBMarginalLaw (aShape h.val) h.property s).mass := by
  funext k
  rw [show (stageBMarginalLaw (aShape h.val) h.property s).mass k =
      marginal (below (aShape h.val))
        (fun u => (stageBLaw (aShape h.val) u : ℝ)) s k from
    indexedMarginalLaw_mass _ _ _ _ _ _ k]
  change (∑ b : BSplit h, if (below (aShape h.val))[b.val] s = k.val
      then (stageBLaw (aShape h.val) (below (aShape h.val))[b.val] : ℝ)
      else 0) = _
  exact Fin.sum_univ_fun_getElem _
    (fun u : Shape => if u s = k.val then (stageBLaw (aShape h.val) u : ℝ) else 0)

theorem canonicalSideMass_stageC {K : ℕ} (h : PartC K) (s : Fin 3) :
    canonicalSideMass (.stageC h) s =
      AllFieldStageCCapacity.stageCMarginal (cParameterParent h) (cShapeParent h) s := rfl

theorem workCapacity_first_oai {K : ℕ} (w : PlacedWork K) :
    workCapacity w.1 0 = finiteEntropy
      (JointPopulationRates.sideMass (placedLaw w).mass (w.physicalOrder 0)) := by
  rw [placedLaw_priority_sideMass]
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h =>
      rw [canonicalSideMass_stageA]
      exact stageACapacity_first_entropy _ h.property
  | stageB h =>
      rw [canonicalSideMass_stageB]
      exact stageBCapacity_first_entropy _ h.property
  | stageC h =>
      rw [canonicalSideMass_stageC]
      exact workCapacity_stageC h 0

end MatrixMultiplication.AllFieldActiveCapacity

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.workCapacity_first_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.workCapacity_first_oai

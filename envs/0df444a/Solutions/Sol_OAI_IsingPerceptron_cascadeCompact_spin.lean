-- Prove2me | solution 1 for OAI.IsingPerceptron.cascadeCompact_spin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:12:30.232131+00:00
-- url     : https://prove2.me/submissions/e8ecdbca-ea9d-4b1e-9f56-13ca4bfb017a

import Mathlib
import Definitions.Def_OAIQ258001

section
-- module Solutions.OAIQ258_II.IsingPerceptron_CascadeFreshMoments
attribute [-instance] _root_.OAI.InvariantIsing.cavityLabeledLeafKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cascade Fresh Moments. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma unitClip_eq {x : ℝ} (h : x ∈ Icc (0:ℝ) 1) : unitClip x = x := by
  simp only [unitClip,min_eq_right h.2,max_eq_right h.1]

lemma spinArray_compactScalarArray {B : RealArray} (hB : ∀ i j, B i j ∈ Icc (0:ℝ) 1) :
    spinArray (compactScalarArray B) = B := by
  funext i j
  exact unitClip_eq (hB i j)

lemma cascade_patch_mem (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) (i j : ℕ) :
    diagonalPatch 1 (cascadeScalarArray n a σ) i j ∈ Icc (0:ℝ) 1 := by
  unfold diagonalPatch cascadeScalarArray
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ⟨h0.trans (ha (Nat.zero_le _)),(ha (labeledCommonDepth_le n _ _)).trans h1⟩

lemma cascadeCompact_spin_oai (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) :
    spinArray (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) =
      diagonalPatch 1 (cascadeScalarArray n a σ) :=
  spinArray_compactScalarArray (cascade_patch_mem n ha h0 h1 σ)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix Classical





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix

end

end OAI
end

theorem solution : type_of% @OAI.IsingPerceptron.cascadeCompact_spin_oai := @OAI.IsingPerceptron.cascadeCompact_spin_oai

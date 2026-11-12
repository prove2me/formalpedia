-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.localAllowed_entropy_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:48:11.810677+00:00
-- url     : https://prove2.me/submissions/fe6af4b3-cfe8-4024-8893-445500bb4ca3

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_StageCLaw
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators

theorem stageCAtom_exhaustive : ∀ u ∈ shapes 4, positive u = true →
    ∀ v ∈ below u, ∃ i, stageCAtom u i = v := by
  decide +kernel

theorem stageCAtom_middle : ∀ u ∈ shapes 4, positive u = true →
    ∀ i, stageCAtom u i (stageCDistinguished u) = 1 ↔ ¬i.val < 2 := by
  decide +kernel

end MatrixMultiplication.AllFieldHistory

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

theorem entropyTerm_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ entropyTerm p :=
  Real.negMulLog_nonneg hp₀ hp₁

theorem finiteEntropy_nonneg {A : Type*} [Fintype A] (p : A → ℝ)
    (hp₀ : ∀ a, 0 ≤ p a) (hp₁ : ∀ a, p a ≤ 1) : 0 ≤ finiteEntropy p := by
  exact Finset.sum_nonneg fun a _ => entropyTerm_nonneg (hp₀ a) (hp₁ a)

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem mass_le_one (p : FiniteLaw A) (a : A) : p.mass a ≤ 1 := by
  calc
    p.mass a ≤ ∑ b, p.mass b :=
      Finset.single_le_sum (fun b _hb => p.nonneg b) (Finset.mem_univ a)
    _ = 1 := p.total

theorem entropy_nonneg (p : FiniteLaw A) : 0 ≤ finiteEntropy p.mass :=
  finiteEntropy_nonneg p.mass p.nonneg p.mass_le_one

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.JointEntropyMax

theorem entropyTerm_le_crossEntropyTerm {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    entropyTerm q ≤ -q * Real.log p + p - q := by
  by_cases hzero : q = 0
  · simpa [hzero] using hp.le
  have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hqpos)
  rw [Real.log_div hp.ne' hqpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hq
  have hcancel : q * (p / q - 1) = p - q := by
    field_simp
  rw [hcancel] at hmul
  unfold entropyTerm
  linarith

theorem sum_mass_mul_coordinate {A B : Type*} [Fintype A] [Fintype B]
    (p : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    (∑ a, p.mass a * v (f a)) = ∑ b, (p.map f).mass b * v b := by
  classical
  simp_rw [FiniteLaw.map_mass, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

end MatrixMultiplication.JointEntropyMax

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InheritedMaskMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section Windows

variable {P A B : Type*} [Fintype P] [DecidableEq P]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq P] [Fintype B] in
theorem wordPopulation_statistic (w : P → A) (statistic : A → B) (b : B) :
    wordPopulation (statistic ∘ w) b =
      ∑ a with statistic a = b, wordPopulation w a := by
  simpa only [wordPopulation, Fintype.card_subtype, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.comp_apply] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset P)
      (Finset.univ.filter fun a => statistic a = b) w).symm

end Windows

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem Work.parentShape_spec {K : ℕ} (w : Work K) :
    ShapeBounded w.parentShape ∧ shapeTotal w.parentShape = 4 * w.halfLength := by
  cases w with
  | stageA h => exact positiveInitial_shape_spec _ h.property
  | stageB h => exact positiveSecond_shape_spec _ h.property
  | stageC h =>
      exact ⟨mem_shapes_bounded (bShape_size h.1.val) (by omega),
        mem_shapes_total (bShape_size h.1.val)⟩

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMarginalSupport
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.JointMarginalSupport

open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ) (sum : H → ℕ)

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_coordinate_witness (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (s : Fin 3) (i : Positions counts h) :
    ∃ j : Positions counts h,
      shapeSide s ((canonicalTarget counts h).val j) = shapeSide s (w i) := by
  have hp : 0 < wordPopulation (shapeSide s ∘ w) (shapeSide s (w i)) := by
    unfold wordPopulation
    exact Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
  rw [hw.2 s (shapeSide s (w i))] at hp
  obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨j, hj⟩

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_coordinate_support (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (allowed : Fin 3 → Fin 17 → Prop)
    (hallowed : ∀ u, 0 < counts h u → ∀ s, allowed s (shapeSide s u)) :
    ∀ i s, allowed s (shapeSide s (w i)) := by
  intro i s
  obtain ⟨j, hj⟩ := localAllowed_coordinate_witness counts sum h w hw s i
  rw [← hj]
  exact hallowed ((canonicalTarget counts h).val j)
    (symbol_count_pos counts (canonicalTarget counts) h j) s

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_parent_bounds (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (parent : Fin 3 → ℕ)
    (hparent : ∀ u, 0 < counts h u → ∀ s, (shapeSide s u).val ≤ parent s) :
    ∀ i s, (shapeSide s (w i)).val ≤ parent s :=
  localAllowed_coordinate_support counts sum h w hw
    (fun s a => a.val ≤ parent s) hparent

omit [Fintype H] [DecidableEq H] in
theorem localAllowed_positive_reference (h : H) (w : Positions counts h → Shape)
    (hw : localAllowed counts sum h w) (parent : Fin 3 → ℕ) (p : Shape → ℝ)
    (hparent : ∀ u, 0 < counts h u → ∀ s, (shapeSide s u).val ≤ parent s)
    (hp : ∀ u : Shape, u.1.val + u.2.1.val + u.2.2.val = sum h →
      (∀ s, (shapeSide s u).val ≤ parent s) → 0 < p u) :
    ∀ i, 0 < p (w i) := by
  intro i
  exact hp (w i) (hw.1 i) (localAllowed_parent_bounds counts sum h w hw parent hparent i)

end MatrixMultiplication.JointMarginalSupport

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
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

theorem placedLaw_mass_branch {K : ℕ} (w : PlacedWork K) (b : w.1.Branch) :
    (placedLaw w).mass (branchShape w b) = (branchProbability w.1 b : ℝ) :=
  FiniteLaw.map_mass_apply _ _ (branchShape_injective w) b

theorem branchPopulation_cast_rat {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℚ) =
      (population allocation dilation (w.1.source, w.2) : ℚ) *
        branchProbability w.1 b := by
  rcases w with ⟨w, phi⟩
  cases w <;>
    simp only [branchPopulation, Work.child, Work.source, population_cast,
      amount, canonicalAmount, aAmount, bAmount, cAmount, branchProbability] <;> ring

theorem branchPopulation_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (b : w.1.Branch) :
    (branchPopulation allocation dilation w b : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (branchLaw w.1).mass b := by
  rw [branchLaw_mass]
  exact_mod_cast branchPopulation_cast_rat allocation dilation w b

theorem jointCounts_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (population allocation dilation (w.1.source, w.2) : ℝ) *
        (placedLaw w).mass u := by
  simp only [jointCounts, shapeCounts, Nat.cast_sum, placedLaw_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : branchShape w b = u
  · simp only [hb, ite_true, if_true, branchPopulation_cast, branchLaw_mass]
  · simp [hb]

end MatrixMultiplication.AllFieldActiveLaws






namespace MatrixMultiplication.AllFieldGroupTargetRate

open AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem orderCounts_sum (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma) :
    (∑ u, orderCounts allocation m h u) =
      population allocation m (h.val.val.1.source, h.val.val.2) :=
  jointCounts_sum allocation m h.val.val

end MatrixMultiplication.AllFieldGroupTargetRate






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointGibbsApproximation
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.branchLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators Topology
open Filter MatrixMultiplication.Foundation
open MatrixMultiplication.JointEntropyMax

namespace MatrixMultiplication.JointGibbsApproximation

theorem marginalError_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    0 ≤ marginalError p q f v :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)

theorem entropy_le_crossEntropy_of_support {A : Type*} [Fintype A]
    (p q : FiniteLaw A) (hsupport : ∀ a, p.mass a = 0 → q.mass a = 0) :
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) := by
  have hterm (a : A) :
      entropyTerm (q.mass a) ≤ -q.mass a * Real.log (p.mass a) + p.mass a - q.mass a := by
    by_cases hp : p.mass a = 0
    · simp [hp, hsupport a hp]
    · exact entropyTerm_le_crossEntropyTerm
        (lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)) (q.nonneg a)
  calc
    finiteEntropy q.mass ≤
        ∑ a, (-q.mass a * Real.log (p.mass a) + p.mass a - q.mass a) :=
      Finset.sum_le_sum fun a _ => hterm a
    _ = ∑ a, -q.mass a * Real.log (p.mass a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, p.total, q.total]
      ring

private theorem potential_difference_le {A B : Type*} [Fintype A] [Fintype B]
    (p q : FiniteLaw A) (f : A → B) (v : B → ℝ) :
    (∑ a, p.mass a * v (f a)) - (∑ a, q.mass a * v (f a)) ≤
      marginalError p q f v := by
  rw [sum_mass_mul_coordinate p f v, sum_mass_mul_coordinate q f v,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro b _
  calc
    (p.map f).mass b * v b - (q.map f).mass b * v b =
        ((p.map f).mass b - (q.map f).mass b) * v b := by ring
    _ ≤ |((p.map f).mass b - (q.map f).mass b) * v b| := le_abs_self _
    _ = |(q.map f).mass b - (p.map f).mass b| * |v b| := by
      rw [abs_mul, abs_sub_comm]

theorem entropy_le_of_marginal_errors_of_support
    {A X Y Z : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    (p q : FiniteLaw A) (fX : A → X) (fY : A → Y) (fZ : A → Z)
    (u : X → ℝ) (v : Y → ℝ) (w : Z → ℝ) (c : ℝ)
    (hsupport : ∀ a, p.mass a = 0 → q.mass a = 0)
    (hlog : ∀ a, 0 < p.mass a →
      Real.log (p.mass a) = u (fX a) + v (fY a) + w (fZ a) - c) :
    finiteEntropy q.mass ≤ finiteEntropy p.mass +
      marginalError p q fX u + marginalError p q fY v + marginalError p q fZ w := by
  have hexpand (r : FiniteLaw A) (hr : ∀ a, p.mass a = 0 → r.mass a = 0) :
      (∑ a, r.mass a * Real.log (p.mass a)) =
        (∑ a, r.mass a * u (fX a)) + (∑ a, r.mass a * v (fY a)) +
          (∑ a, r.mass a * w (fZ a)) - c := by
    have hterm (a : A) : r.mass a * Real.log (p.mass a) =
        r.mass a * (u (fX a) + v (fY a) + w (fZ a) - c) := by
      by_cases hp : p.mass a = 0
      · simp [hr a hp]
      · rw [hlog a (lt_of_le_of_ne (p.nonneg a) (Ne.symm hp))]
    simp_rw [hterm, mul_sub, mul_add]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, r.total, one_mul]
  have hcross : (∑ a, -q.mass a * Real.log (p.mass a)) =
      finiteEntropy p.mass +
        ((∑ a, p.mass a * u (fX a)) - (∑ a, q.mass a * u (fX a))) +
        ((∑ a, p.mass a * v (fY a)) - (∑ a, q.mass a * v (fY a))) +
        ((∑ a, p.mass a * w (fZ a)) - (∑ a, q.mass a * w (fZ a))) := by
    have hp : finiteEntropy p.mass = -(∑ a, p.mass a * Real.log (p.mass a)) := by
      simp only [finiteEntropy, entropyTerm, neg_mul, Finset.sum_neg_distrib]
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [hp, hexpand p (fun _ h => h), hexpand q hsupport]
    ring
  calc
    finiteEntropy q.mass ≤ ∑ a, -q.mass a * Real.log (p.mass a) :=
      entropy_le_crossEntropy_of_support p q hsupport
    _ = _ := hcross
    _ ≤ _ := add_le_add
      (add_le_add (add_le_add le_rfl (potential_difference_le p q fX u))
        (potential_difference_le p q fY v)) (potential_difference_le p q fZ w)

end MatrixMultiplication.JointGibbsApproximation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointAmbientEntropy
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators Topology
open Filter MatrixMultiplication.Foundation
open MatrixMultiplication.JointPopulation MatrixMultiplication.JointAmbientDegree
open MatrixMultiplication.JointGibbsApproximation

namespace MatrixMultiplication.JointAmbientEntropy

section Empirical

variable {I A B : Type*} [Fintype I]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem empiricalFiniteLaw_map_mass (w : I → A) (hpos : 0 < Fintype.card I)
    (f : A → B) (b : B) :
    ((empiricalFiniteLaw w hpos).map f).mass b =
      (wordPopulation (f ∘ w) b : ℝ) / Fintype.card I := by
  rw [FiniteLaw.map_mass, InheritedMasks.wordPopulation_statistic,
    Nat.cast_sum, Finset.sum_div, Finset.sum_filter]
  simp only [empiricalFiniteLaw_mass]

theorem empiricalFiniteLaw_supported (w : I → A) (hpos : 0 < Fintype.card I)
    (p : FiniteLaw A) (hsupport : ∀ i, 0 < p.mass (w i)) :
    ∀ a, p.mass a = 0 → (empiricalFiniteLaw w hpos).mass a = 0 := by
  intro a ha
  have : IsEmpty {i : I // w i = a} := ⟨fun i => by
    have hp := hsupport i.val
    rw [i.property, ha] at hp
    exact lt_irrefl 0 hp⟩
  simp only [empiricalFiniteLaw_mass, wordPopulation, Fintype.card_of_isEmpty,
    Nat.cast_zero, zero_div]

end Empirical

variable {H : Type*}

theorem canonicalLaw_mass_of_pos (counts : H → Shape → ℕ) (h : H)
    (hpos : 0 < Fintype.card (Positions counts h)) (a : Shape) :
    (canonicalLaw counts h).mass a =
      (counts h a : ℝ) / Fintype.card (Positions counts h) := by
  rw [canonicalLaw, dite_eq_left hpos, empiricalFiniteLaw_mass,
    ((canonicalTarget counts) h).property]

theorem localAllowed_marginal_eq (counts : H → Shape → ℕ) (sum : H → ℕ)
    (h : H) (w : Positions counts h → Shape)
    (hpos : 0 < Fintype.card (Positions counts h))
    (hw : localAllowed counts sum h w) (s : Fin 3) :
    ((empiricalFiniteLaw w hpos).map (shapeSide s)).mass =
      ((canonicalLaw counts h).map (shapeSide s)).mass := by
  rw [canonicalLaw, dite_eq_left hpos]
  funext a
  rw [empiricalFiniteLaw_map_mass, empiricalFiniteLaw_map_mass]
  exact congrArg (fun n : ℕ => (n : ℝ) / Fintype.card (Positions counts h)) (hw.2 s a)

theorem gibbsCap_nonneg (counts : H → Shape → ℕ) (h : H) (p : FiniteLaw Shape)
    (u v w : Fin 17 → ℝ) : 0 ≤ gibbsCap counts h p u v w := by
  exact add_nonneg
    (add_nonneg (add_nonneg p.entropy_nonneg (marginalError_nonneg _ _ _ _))
      (marginalError_nonneg _ _ _ _)) (marginalError_nonneg _ _ _ _)

theorem localAllowed_entropy_le_of_word_support (counts : H → Shape → ℕ) (sum : H → ℕ)
    (h : H) (w : Positions counts h → Shape) (p : FiniteLaw Shape)
    (u v z : Fin 17 → ℝ) (c : ℝ)
    (hsupport : ∀ i, 0 < p.mass (w i))
    (hlog : ∀ a, 0 < p.mass a → Real.log (p.mass a) =
      u (shapeSide 0 a) + v (shapeSide 1 a) + z (shapeSide 2 a) - c)
    (hw : localAllowed counts sum h w) :
    finiteEntropy (fun a => (wordPopulation w a : ℝ) /
      Fintype.card (Positions counts h)) ≤ gibbsCap counts h p u v z := by
  by_cases hpos : 0 < Fintype.card (Positions counts h)
  · have hs := empiricalFiniteLaw_supported w hpos p hsupport
    have hg := entropy_le_of_marginal_errors_of_support p (empiricalFiniteLaw w hpos)
      (shapeSide 0) (shapeSide 1) (shapeSide 2) u v z c hs hlog
    have hx := localAllowed_marginal_eq counts sum h w hpos hw (0 : Fin 3)
    have hy := localAllowed_marginal_eq counts sum h w hpos hw (1 : Fin 3)
    have hz := localAllowed_marginal_eq counts sum h w hpos hw (2 : Fin 3)
    change finiteEntropy (fun a => (wordPopulation w a : ℝ) /
      Fintype.card (Positions counts h)) ≤ _ at hg
    simpa only [gibbsCap, marginalError, hx, hy, hz] using hg
  · have hzero : Fintype.card (Positions counts h) = 0 := Nat.eq_zero_of_not_pos hpos
    simpa only [hzero, Nat.cast_zero, div_zero, finiteEntropy, entropyTerm_zero,
      Finset.sum_const_zero] using gibbsCap_nonneg counts h p u v z

end MatrixMultiplication.JointAmbientEntropy

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupAmbientDegree
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveGibbs

open AllFieldParameters AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem splitCoordinateWeight_pos (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s : Shape) (i : Fin 3) (k : ℕ) :
    0 < splitCoordinateWeight parents data s i k := by
  apply Rat.cast_pos.mpr
  exact weight_positive_of_argument_bound _ (assigned_argument_bound _ data hd _)

theorem splitNormalizer_pos (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s : Shape) (hne : below s ≠ []) :
    0 < splitNormalizer parents data s := by
  apply Rat.cast_pos.mpr
  exact list_sum_map_positive _ _ hne (fun u _ => splitWeight_positive parents data hd s u)

theorem splitWeight_log (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) :
    Real.log (splitWeight parents data s u : ℝ) =
      ∑ i : Fin 3, splitPotential parents data s i (u i) := by
  have hweight (i : Fin 3) : (weight (splitSignature parents data s u i) : ℝ) ≠ 0 :=
    ne_of_gt (splitCoordinateWeight_pos parents data hd s i (u i))
  rw [splitWeight, Rat.cast_prod, Real.log_prod (fun index _ => hweight index)]
  rfl

theorem splitLaw_log (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) (hu : u ∈ below s) :
    Real.log (splitLaw parents data s u : ℝ) =
      (∑ i : Fin 3, splitPotential parents data s i (u i)) -
        splitLogNormalizer parents data s := by
  have hweight : (splitWeight parents data s u : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (splitWeight_positive parents data hd s u)
  have hne : below s ≠ [] := by
    intro he
    simp only [he, List.not_mem_nil] at hu
  have hnormal := ne_of_gt (splitNormalizer_pos parents data hd s hne)
  rw [splitLaw, ite_eq_left hu, Rat.cast_div]
  change Real.log ((splitWeight parents data s u : ℝ) / splitNormalizer parents data s) = _
  rw [Real.log_div hweight hnormal, splitWeight_log parents data hd]
  rfl

theorem splitLaw_log_physical (parents : List Shape) (data : List ℤ)
    (hd : ∀ n ∈ data, |n| ≤ 160000) (s u : Shape) (hu : u ∈ below s)
    (hb : ShapeBounded u) (phi : Placement) :
    Real.log (splitLaw parents data s u : ℝ) =
      physicalPotential parents data s phi 0 (JointPopulation.shapeSide 0 (encodePhysicalShape phi u hb)) +
      physicalPotential parents data s phi 1 (JointPopulation.shapeSide 1 (encodePhysicalShape phi u hb)) +
      physicalPotential parents data s phi 2 (JointPopulation.shapeSide 2 (encodePhysicalShape phi u hb)) -
        splitLogNormalizer parents data s := by
  rw [splitLaw_log parents data hd s u hu]
  have hsum : (∑ i : Fin 3, splitPotential parents data s i (u i)) =
      ∑ i : Fin 3, physicalPotential parents data s phi i
        (JointPopulation.shapeSide i (encodePhysicalShape phi u hb)) := by
    simp only [physicalPotential, encodePhysicalShape_side]
    exact (phi.symm.sum_comp (fun i => splitPotential parents data s i (u i))).symm
  rw [hsum, Fin.sum_univ_three]

theorem placedLaw_positive_has_branch {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw w).mass u) :
    ∃ b : w.1.Branch, branchShape w b = u := by
  by_contra hn
  have hz : (placedLaw w).mass u = 0 := by
    rw [placedLaw_mass]
    apply Finset.sum_eq_zero
    intro b _
    exact ite_eq_right (fun hb => hn ⟨b, hb⟩)
  rw [hz] at hu
  exact lt_irrefl 0 hu

theorem placedLaw_stageA_branch_log {K : ℕ} (h : InitialPositive K)
    (phi : Placement) (b : ASplit h) :
    Real.log ((placedLaw (Work.stageA h, phi)).mass (branchShape (Work.stageA h, phi) b)) =
      physicalPotential positiveInitial tableP (initialShape h.val) phi 0
        (JointPopulation.shapeSide 0 (branchShape (Work.stageA h, phi) b)) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 1
        (JointPopulation.shapeSide 1 (branchShape (Work.stageA h, phi) b)) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 2
        (JointPopulation.shapeSide 2 (branchShape (Work.stageA h, phi) b)) -
      splitLogNormalizer positiveInitial tableP (initialShape h.val) := by
  refine (congrArg Real.log (placedLaw_mass_branch (Work.stageA h, phi) b)).trans ?_
  exact splitLaw_log_physical positiveInitial tableP stageA_table_arguments_bounded
    (initialShape h.val) (aSplit ⟨h, b, false⟩) (aSplit_mem ⟨h, b, false⟩)
    ((Work.stageA h).splitShape_spec b).1 phi

theorem placedLaw_stageB_branch_log {K : ℕ} (h : APositive K)
    (phi : Placement) (b : BSplit h) :
    Real.log ((placedLaw (Work.stageB h, phi)).mass (branchShape (Work.stageB h, phi) b)) =
      physicalPotential positiveSecond tablep (aShape h.val) phi 0
        (JointPopulation.shapeSide 0 (branchShape (Work.stageB h, phi) b)) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 1
        (JointPopulation.shapeSide 1 (branchShape (Work.stageB h, phi) b)) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 2
        (JointPopulation.shapeSide 2 (branchShape (Work.stageB h, phi) b)) -
      splitLogNormalizer positiveSecond tablep (aShape h.val) := by
  refine (congrArg Real.log (placedLaw_mass_branch (Work.stageB h, phi) b)).trans ?_
  exact splitLaw_log_physical positiveSecond tablep stageB_table_arguments_bounded
    (aShape h.val) (bSplit ⟨h, b, false⟩) (bSplit_mem ⟨h, b, false⟩)
    ((Work.stageB h).splitShape_spec b).1 phi

theorem placedLaw_stageA_log {K : ℕ} (h : InitialPositive K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageA h, phi)).mass u) :
    Real.log ((placedLaw (Work.stageA h, phi)).mass u) =
      physicalPotential positiveInitial tableP (initialShape h.val) phi 0 (JointPopulation.shapeSide 0 u) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 1 (JointPopulation.shapeSide 1 u) +
      physicalPotential positiveInitial tableP (initialShape h.val) phi 2 (JointPopulation.shapeSide 2 u) -
      splitLogNormalizer positiveInitial tableP (initialShape h.val) := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch (Work.stageA h, phi) u hu
  exact placedLaw_stageA_branch_log h phi b

theorem placedLaw_stageB_log {K : ℕ} (h : APositive K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageB h, phi)).mass u) :
    Real.log ((placedLaw (Work.stageB h, phi)).mass u) =
      physicalPotential positiveSecond tablep (aShape h.val) phi 0 (JointPopulation.shapeSide 0 u) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 1 (JointPopulation.shapeSide 1 u) +
      physicalPotential positiveSecond tablep (aShape h.val) phi 2 (JointPopulation.shapeSide 2 u) -
      splitLogNormalizer positiveSecond tablep (aShape h.val) := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch (Work.stageB h, phi) u hu
  exact placedLaw_stageB_branch_log h phi b

theorem mem_shapes_of_total (u : Shape) (n : ℕ)
    (h : shapeTotal u = n) : u ∈ shapes n := by
  dsimp [shapeTotal] at h
  simp only [shapes, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨u 0, by omega, u 1, by omega, ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl
  · change n - u 0 - u 1 = u 2
    omega

theorem mem_below_iff (s u : Shape) :
    u ∈ below s ↔ shapeTotal u = shapeTotal s / 2 ∧ ∀ i, u i ≤ s i := by
  constructor
  · intro hu
    exact ⟨below_total hu, below_le hu⟩
  · rintro ⟨ht, hle⟩
    apply List.mem_filter.mpr
    refine ⟨mem_shapes_of_total u _ ht, ?_⟩
    simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc] using
      And.intro (hle 0) (And.intro (hle 1) (hle 2))

theorem splitShape_exhaustive {K : ℕ} (w : Work K)
    (u : Shape) (hu : u ∈ below w.parentShape) :
    ∃ b : w.Branch, w.splitShape b = u := by
  cases w with
  | stageA h =>
      change u ∈ below (initialShape h.val) at hu
      obtain ⟨b, hb⟩ := List.mem_iff_get.mp hu
      exact ⟨b, hb⟩
  | stageB h =>
      change u ∈ below (aShape h.val) at hu
      obtain ⟨b, hb⟩ := List.mem_iff_get.mp hu
      exact ⟨b, hb⟩
  | stageC h =>
      exact stageCAtom_exhaustive _ (bShape_size h.1.val) h.1.property u hu

theorem branchShape_exhaustive {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape)
    (ht : u.1.val + u.2.1.val + u.2.2.val = 2 * w.1.halfLength)
    (hle : ∀ i, (JointPopulation.shapeSide i u).val ≤
      physicalShape w.2 w.1.parentShape i) :
    ∃ b : w.1.Branch, branchShape w b = u := by
  let v : Shape := physicalShape w.2.symm (decodeShape u)
  have hvt : shapeTotal v = 2 * w.1.halfLength := by
    dsimp [v]
    rw [physicalShape_total]
    exact ht
  have hvl : ∀ i, v i ≤ w.1.parentShape i := by
    intro i
    simpa only [v, physicalShape, decodeShape, Equiv.symm_symm,
      Equiv.symm_apply_apply] using hle (w.2 i)
  have hv : v ∈ below w.1.parentShape := by
    apply (mem_below_iff _ _).2
    refine ⟨?_, hvl⟩
    rw [hvt, (w.1.parentShape_spec).2]
    omega
  obtain ⟨b, hb⟩ := splitShape_exhaustive w.1 v hv
  refine ⟨b, ?_⟩
  have hd : decodeShape (branchShape w b) = decodeShape u := by
    rw [branchShape, decode_encodePhysicalShape, hb]
    funext i
    simp only [v, physicalShape, Equiv.symm_symm, Equiv.apply_symm_apply]
  apply Prod.ext
  · exact Fin.ext (congrFun hd 0)
  · apply Prod.ext
    · exact Fin.ext (congrFun hd 1)
    · exact Fin.ext (congrFun hd 2)

theorem placedLaw_stageA_positive {K : ℕ} (h : InitialPositive K) (phi : Placement)
    (u : JointPopulation.Shape) (ht : u.1.val + u.2.1.val + u.2.2.val = 8)
    (hle : ∀ i, (JointPopulation.shapeSide i u).val ≤
      physicalShape phi (initialShape h.val) i) :
    0 < (placedLaw (Work.stageA h, phi)).mass u := by
  obtain ⟨b, rfl⟩ := branchShape_exhaustive (Work.stageA h, phi) u ht hle
  rw [placedLaw_mass_branch]
  exact_mod_cast stageALaw_positive (initialShape h.val) (aSplit ⟨h, b, false⟩)
    (aSplit_mem ⟨h, b, false⟩)

theorem placedLaw_stageB_positive {K : ℕ} (h : APositive K) (phi : Placement)
    (u : JointPopulation.Shape) (ht : u.1.val + u.2.1.val + u.2.2.val = 4)
    (hle : ∀ i, (JointPopulation.shapeSide i u).val ≤
      physicalShape phi (aShape h.val) i) :
    0 < (placedLaw (Work.stageB h, phi)).mass u := by
  obtain ⟨b, rfl⟩ := branchShape_exhaustive (Work.stageB h, phi) u ht hle
  rw [placedLaw_mass_branch]
  exact_mod_cast stageBLaw_positive (aShape h.val) (bSplit ⟨h, b, false⟩)
    (bSplit_mem ⟨h, b, false⟩)

end MatrixMultiplication.AllFieldActiveGibbs

namespace MatrixMultiplication.AllFieldStageCGibbs

open AllFieldParameters AllFieldHistory AllFieldActiveLaws AllFieldActiveGibbs
open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem distinguishedSide_branch {K : ℕ} (h : PartC K) (phi : Placement)
    (b : Fin 4) :
    (shapeSide (distinguishedSide h phi) (branchShape (Work.stageC h, phi) b)).val =
      stageCAtom (cShapeParent h) b (stageCDistinguished (cShapeParent h)) := by
  simp only [distinguishedSide, branchShape, encodePhysicalShape_side,
    Equiv.symm_apply_apply, Work.splitShape, cSplit]

theorem placedLaw_stageC_branch_mass {K : ℕ} (h : PartC K) (phi : Placement)
    (b : Fin 4) :
    (placedLaw (Work.stageC h, phi)).mass (branchShape (Work.stageC h, phi) b) =
      coordinateMass h
        (shapeSide (distinguishedSide h phi) (branchShape (Work.stageC h, phi) b)) := by
  refine (placedLaw_mass_branch (Work.stageC h, phi) b).trans ?_
  change (stageCWeight (cParameterParent h) (cShapeParent h) b : ℝ) = _
  simp only [coordinateMass, distinguishedSide_branch]
  unfold stageCWeight
  have hm := stageCAtom_middle (cShapeParent h) (bShape_size h.1.val) h.1.property b
  by_cases hb : b.val < 2
  · have hn : ¬stageCAtom (cShapeParent h) b (stageCDistinguished (cShapeParent h)) = 1 :=
      fun hmiddle => (hm.mp hmiddle) hb
    simp only [hb, ite_true, if_true, hn, ite_false, if_false]
  · have hx := hm.mpr hb
    simp only [hb, ite_false, if_false, hx, ite_true, if_true]

theorem placedLaw_stageC_mass_of_positive {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    (placedLaw (Work.stageC h, phi)).mass u =
      coordinateMass h (shapeSide (distinguishedSide h phi) u) := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch (Work.stageC h, phi) u hu
  exact placedLaw_stageC_branch_mass h phi b

theorem placedLaw_stageC_mass_on_feasible {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (ht : u.1.val + u.2.1.val + u.2.2.val = 2)
    (hle : ∀ s, (shapeSide s u).val ≤ physicalShape phi (cShapeParent h) s) :
    (placedLaw (Work.stageC h, phi)).mass u =
      coordinateMass h (shapeSide (distinguishedSide h phi) u) := by
  obtain ⟨b, rfl⟩ := branchShape_exhaustive (Work.stageC h, phi) u ht hle
  exact placedLaw_stageC_branch_mass h phi b

theorem sum_physicalPotential {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) :
    (∑ s : Fin 3, physicalPotential h phi s (shapeSide s u)) =
      Real.log (coordinateMass h (shapeSide (distinguishedSide h phi) u)) := by
  simp only [physicalPotential, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]

theorem placedLaw_stageC_log {K : ℕ} (h : PartC K) (phi : Placement)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    Real.log ((placedLaw (Work.stageC h, phi)).mass u) =
      physicalPotential h phi 0 (shapeSide 0 u) +
        physicalPotential h phi 1 (shapeSide 1 u) +
        physicalPotential h phi 2 (shapeSide 2 u) - 0 := by
  rw [placedLaw_stageC_mass_of_positive h phi u hu, ← sum_physicalPotential h phi u,
    Fin.sum_univ_three, sub_zero]

theorem placedLaw_positive_parent_bounds {K : ℕ} (w : PlacedWork K)
    (u : JointPopulation.Shape) (hu : 0 < (placedLaw w).mass u) :
    ∀ s, (shapeSide s u).val ≤ physicalShape w.2 w.1.parentShape s := by
  obtain ⟨b, rfl⟩ := placedLaw_positive_has_branch w u hu
  intro s
  rw [branchShape, encodePhysicalShape_side]
  exact w.1.splitShape_le b (w.2.symm s)

theorem jointCounts_positive_reference {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : 0 < jointCounts allocation dilation w u) : 0 < (placedLaw w).mass u := by
  have hc : (0 : ℝ) < (jointCounts allocation dilation w u : ℝ) := by exact_mod_cast hu
  rw [jointCounts_cast] at hc
  rcases mul_pos_iff.mp hc with hpos | hneg
  · exact hpos.2
  · exact False.elim (not_lt_of_ge (Nat.cast_nonneg _) hneg.1)

theorem localAllowed_positive_reference {Hist : Type*} [Fintype Hist] [DecidableEq Hist]
    (counts : Hist → JointPopulation.Shape → ℕ) (total : Hist → ℕ)
    (hist : Hist) (word : Positions counts hist → JointPopulation.Shape)
    (hw : localAllowed counts total hist word)
    {K : ℕ} (h : PartC K) (phi : Placement) (htotal : total hist = 2)
    (hcounts : ∀ u, 0 < counts hist u → 0 < (placedLaw (Work.stageC h, phi)).mass u) :
    ∀ i, 0 < (placedLaw (Work.stageC h, phi)).mass (word i) := by
  intro i
  have hbounds := JointMarginalSupport.localAllowed_parent_bounds counts total hist word hw
    (physicalShape phi (cShapeParent h))
    (fun u hu => placedLaw_positive_parent_bounds (Work.stageC h, phi) u (hcounts u hu))
  obtain ⟨j, hj⟩ := JointMarginalSupport.localAllowed_coordinate_witness
    counts total hist word hw (distinguishedSide h phi) i
  have hp : 0 < (placedLaw (Work.stageC h, phi)).mass ((canonicalTarget counts hist).val j) :=
    hcounts _ (symbol_count_pos counts (canonicalTarget counts) hist j)
  have ht : (word i).1.val + (word i).2.1.val + (word i).2.2.val = 2 :=
    (hw.1 i).trans htotal
  calc
    0 < (placedLaw (Work.stageC h, phi)).mass ((canonicalTarget counts hist).val j) := hp
    _ = coordinateMass h
        (shapeSide (distinguishedSide h phi) ((canonicalTarget counts hist).val j)) :=
      placedLaw_stageC_mass_of_positive h phi _ hp
    _ = coordinateMass h (shapeSide (distinguishedSide h phi) (word i)) := congrArg _ hj
    _ = (placedLaw (Work.stageC h, phi)).mass (word i) :=
      (placedLaw_stageC_mass_on_feasible h phi (word i) ht (hbounds i)).symm

end MatrixMultiplication.AllFieldStageCGibbs

namespace MatrixMultiplication.AllFieldGroupAmbientDegree

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldGroupTargetRate JointPopulation JointAmbientDegree
open JointAmbientEntropy JointGibbsApproximation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

theorem placedLaw_log {K : ℕ} (w : PlacedWork K) (a : JointPopulation.Shape)
    (ha : 0 < (placedLaw w).mass a) :
    Real.log ((placedLaw w).mass a) = potential w 0 (shapeSide 0 a) +
      potential w 1 (shapeSide 1 a) + potential w 2 (shapeSide 2 a) -
        logNormalizer w := by
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA h => exact AllFieldActiveGibbs.placedLaw_stageA_log h phi a ha
  | stageB h => exact AllFieldActiveGibbs.placedLaw_stageB_log h phi a ha
  | stageC h => exact AllFieldStageCGibbs.placedLaw_stageC_log h phi a ha

theorem localAllowed_positive {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → JointPopulation.Shape → ℕ) (total : H → ℕ) (h : H)
    (word : Positions counts h → JointPopulation.Shape)
    (hw : localAllowed counts total h word) {K : ℕ} (w : PlacedWork K)
    (htotal : total h = 2 * w.1.halfLength)
    (hcounts : ∀ a, 0 < counts h a → 0 < (placedLaw w).mass a) :
    ∀ i, 0 < (placedLaw w).mass (word i) := by
  have hb := fun a ha =>
    AllFieldStageCGibbs.placedLaw_positive_parent_bounds w a (hcounts a ha)
  rcases w with ⟨w, phi⟩
  cases w with
  | stageA a =>
      apply JointMarginalSupport.localAllowed_positive_reference counts total h word hw
        (physicalShape phi (initialShape a.val)) _ hb
      intro u hu hle
      exact AllFieldActiveGibbs.placedLaw_stageA_positive a phi u
        (hu.trans htotal) hle
  | stageB a =>
      apply JointMarginalSupport.localAllowed_positive_reference counts total h word hw
        (physicalShape phi (aShape a.val)) _ hb
      intro u hu hle
      exact AllFieldActiveGibbs.placedLaw_stageB_positive a phi u
        (hu.trans htotal) hle
  | stageC a =>
      exact AllFieldStageCGibbs.localAllowed_positive_reference counts total h word hw
        a phi htotal hcounts

variable {K tick : ℕ} {sigma : Placement}

theorem canonicalLaw_mass_eq (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma)
    (hpos : 0 < Fintype.card (Positions (orderCounts allocation m) h)) :
    (canonicalLaw (orderCounts allocation m) h).mass = (orderLaw h).mass := by
  have hcard : Fintype.card (Positions (orderCounts allocation m) h) =
      population allocation m (h.val.val.1.source, h.val.val.2) := by
    simpa only [Positions, Fintype.card_fin] using orderCounts_sum allocation m h
  funext a
  rw [canonicalLaw_mass_of_pos _ h hpos, hcard]
  change (jointCounts allocation m h.val.val a : ℝ) /
    population allocation m (h.val.val.1.source, h.val.val.2) = _
  rw [jointCounts_cast]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (hcard ▸ hpos).ne')

theorem localAllowed_entropy_le_oai (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma)
    (word : Positions (orderCounts allocation m) h → JointPopulation.Shape)
    (hw : localAllowed (orderCounts allocation m) orderTotal h word) :
    finiteEntropy (fun a => (wordPopulation word a : ℝ) /
      Fintype.card (Positions (orderCounts allocation m) h)) ≤
        finiteEntropy (orderLaw h).mass := by
  by_cases hpos : 0 < Fintype.card (Positions (orderCounts allocation m) h)
  · have hs := localAllowed_positive (orderCounts allocation m) orderTotal h word hw
      h.val.val rfl (fun a ha =>
        AllFieldStageCGibbs.jointCounts_positive_reference allocation m h.val.val a ha)
    have he := localAllowed_entropy_le_of_word_support (orderCounts allocation m)
      orderTotal h word (orderLaw h) (potential h.val.val 0) (potential h.val.val 1)
      (potential h.val.val 2) (logNormalizer h.val.val) hs
      (placedLaw_log h.val.val) hw
    have hc := canonicalLaw_mass_eq allocation m h hpos
    simpa only [gibbsCap, marginalError, FiniteLaw.map_mass, hc, sub_self, abs_zero,
      zero_mul, Finset.sum_const_zero, add_zero] using he
  · have hz := Nat.eq_zero_of_not_pos hpos
    simpa only [hz, Nat.cast_zero, div_zero, finiteEntropy, entropyTerm_zero,
      Finset.sum_const_zero] using (orderLaw h).entropy_nonneg

end MatrixMultiplication.AllFieldGroupAmbientDegree

end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.localAllowed_entropy_le_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.localAllowed_entropy_le_oai

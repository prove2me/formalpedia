-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:21.474474+00:00
-- url     : https://prove2.me/submissions/94f0b080-0bcb-415e-8d10-16d0baa8f21d

import Mathlib
import Definitions.Def_OAIQ254M007
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldActiveCapacity_workCapacity_first
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupNativeDegreeBound_exists_threshold_eventually_counts_le
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_JointMaskedGoodSelection_eventually_exists_good_selection

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointExtractionRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Foundation.Separation

open Filter

theorem log_nat_prod {I : Type*} (s : Finset I) (a : I → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Real.log ((∏ i ∈ s, a i : ℕ) : ℝ) = ∑ i ∈ s, Real.log (a i : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod fun i hi =>
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha i hi))

theorem tendsto_log_nat_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, K i N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  have hsum := tendsto_finsetSum s hpop
  apply hsum.congr
  intro N
  rw [log_nat_prod s (fun i => K i N) (fun i hi => hK i hi N)]
  simp only [div_eq_mul_inv, Finset.sum_mul]

end MatrixMultiplication.Foundation.Separation






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

theorem finiteEntropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : A → B → ℝ) (hq : ∀ a, ∑ b, q a b = 1) :
    finiteEntropy (fun ab : A × B => p ab.1 * q ab.1 ab.2) =
      finiteEntropy p + ∑ a, p a * finiteEntropy (q a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

theorem map_entropy_of_injective (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) : finiteEntropy (p.map f).mass = finiteEntropy p.mass := by
  classical
  have hterm (b : B) : entropyTerm ((p.map f).mass b) =
      ∑ a, if f a = b then entropyTerm (p.mass a) else 0 := by
    by_cases hb : ∃ a, f a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [map_mass_apply p f hf]
      simp [hf.eq_iff]
    · simp [map_mass, not_exists.mp hb]
  unfold finiteEntropy
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp

theorem joint_entropy (p : FiniteLaw A) (q : A → FiniteLaw B) :
    finiteEntropy (p.joint q).mass =
      finiteEntropy p.mass + ∑ a, p.mass a * finiteEntropy (q a).mass :=
  finiteEntropy_chain p.mass (fun a => (q a).mass) (fun a => (q a).total)

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

theorem map_mass_mul_conditional [DecidableEq B]
    (p : FiniteLaw A) (f : A → B) (b : B) (a : A) :
    (p.map f).mass b * (p.conditional f b).mass a =
      if f a = b then p.mass a else 0 := by
  classical
  by_cases hzero : (p.map f).mass b = 0
  · have ha : f a = b → p.mass a = 0 := by
      intro hab
      have hle := p.mass_le_map_mass f a
      rw [hab, hzero] at hle
      exact le_antisymm hle (p.nonneg a)
    rw [hzero, zero_mul]
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ha hab]
    · rw [ite_eq_right hab]
  · simp only [conditional, hzero, ↓reduceDIte]
    by_cases hab : f a = b
    · simpa only [hab, ite_true, if_true] using (mul_div_cancel₀ (p.mass a) hzero)
    · simp only [hab, ite_false, if_false, zero_div, mul_zero]

theorem entropy_eq_map_add_conditional (p : FiniteLaw A) (f : A → B) :
    finiteEntropy p.mass = finiteEntropy (p.map f).mass +
      ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
  classical
  let graph : A → B × A := fun a => (f a, a)
  have hinj : Function.Injective graph := fun _ _ h => congrArg Prod.snd h
  have hmass : ((p.map f).joint (p.conditional f)).mass = (p.map graph).mass := by
    funext ba
    rcases ba with ⟨b, a⟩
    change (p.map f).mass b * (p.conditional f b).mass a = (p.map graph).mass (b, a)
    rw [map_mass_mul_conditional, map_mass, Finset.sum_eq_single a]
    · simp only [graph, Prod.mk.injEq, and_true]
    · intro x _ hxa
      simp only [graph, Prod.mk.injEq, hxa, and_false, ite_false, if_false]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  calc
    finiteEntropy p.mass = finiteEntropy (p.map graph).mass :=
      (p.map_entropy_of_injective graph hinj).symm
    _ = finiteEntropy ((p.map f).joint (p.conditional f)).mass := by rw [hmass]
    _ = _ := (p.map f).joint_entropy (p.conditional f)

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

theorem tendsto_finiteEntropy_of_tendsto {I A : Type*} [Fintype A]
    {l : Filter I} {p : I → A → ℝ} {q : A → ℝ}
    (h : ∀ a, Tendsto (fun i => p i a) l (𝓝 (q a))) :
    Tendsto (fun i => finiteEntropy (p i)) l (𝓝 (finiteEntropy q)) :=
  continuous_finiteEntropy.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

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

theorem map_entropy_le {B : Type*} [Fintype B] (p : FiniteLaw A) (f : A → B) :
    finiteEntropy (p.map f).mass ≤ finiteEntropy p.mass := by
  calc
    finiteEntropy (p.map f).mass ≤ finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy (p.conditional f b).mass :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun b _ =>
        mul_nonneg ((p.map f).nonneg b) ((p.conditional f b).entropy_nonneg))
    _ = finiteEntropy p.mass := (p.entropy_eq_map_add_conditional f).symm

end FiniteLaw
end MatrixMultiplication.Foundation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointCanonicalization.positionEquiv_symm_shape _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

theorem exactWords_card_le (counts : A → ℕ) :
    Fintype.card (ExactWords counts) ≤ (Fintype.card A) ^ (∑ a, counts a) := by
  classical
  calc
    Fintype.card (ExactWords counts) ≤
        Fintype.card (Fin (∑ a, counts a) → A) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = _ := by simp

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulation
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulation

open MatrixMultiplication.Foundation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

theorem target_card : Fintype.card (Target counts) =
    ∏ h, Nat.multinomial Finset.univ (counts h) := by
  simp only [Target, Fintype.card_pi, exactWords_card]

omit [Fintype H] [DecidableEq H] in
theorem target_nonempty : Nonempty (Target counts) := ⟨canonicalTarget counts⟩

end MatrixMultiplication.JointPopulation

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InheritedMaskMargins
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
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

section ClassWords

variable {C : Type*} (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [∀ c, DecidableEq (P c)] in
theorem card_profile [Fintype C] [DecidableEq C] :
    Fintype.card (Profile P A) =
      ∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (A c) := by
  simp [Profile, Fintype.card_pi]

end ClassWords

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitCount
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryMasks.permutationsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualCompatible_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.actualUseful_coarse _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.full_card_localOrbit _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.tripleSide_reorder _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_carried _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.toState_due _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_card_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTickCarry.liftExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialState.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeCapacity.nativeCapacity_first _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
  {P X Y : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
  [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]

omit [∀ c, DecidableEq (P c)] in
theorem card_pairOrbits_le :
    Nat.card (PairOrbit P X Y) ≤
      (∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (X c)) *
      (∏ c, (Fintype.card (P c) + 1) ^ Fintype.card (Y c)) := by
  have : Finite (PairOrbit P X Y) :=
    Finite.of_injective pairOrbitProfile pairOrbitProfile_injective
  let := Fintype.ofFinite (PairOrbit P X Y)
  rw [Nat.card_eq_fintype_card]
  calc
    _ ≤ Fintype.card (PairProfile P X Y) :=
      Fintype.card_le_of_injective pairOrbitProfile pairOrbitProfile_injective
    _ = _ := by
      rw [Fintype.card_prod, InheritedMasks.card_profile, InheritedMasks.card_profile]

omit [∀ c, DecidableEq (P c)] in
theorem card_pairOrbits_le_common_bound (m : ℕ)
    (hm : ∀ c, Fintype.card (P c) ≤ m) :
    Nat.card (PairOrbit P X Y) ≤ (m + 1) ^
      ((∑ c, Fintype.card (X c)) + ∑ c, Fintype.card (Y c)) := by
  refine (card_pairOrbits_le (P := P) (X := X) (Y := Y)).trans ?_
  calc
    _ ≤ (∏ c, (m + 1) ^ Fintype.card (X c)) *
        (∏ c, (m + 1) ^ Fintype.card (Y c)) := by
      apply Nat.mul_le_mul
      · exact Finset.prod_le_prod' fun c _ =>
          Nat.pow_le_pow_left (Nat.add_le_add_right (hm c) 1) _
      · exact Finset.prod_le_prod' fun c _ =>
          Nat.pow_le_pow_left (Nat.add_le_add_right (hm c) 1) _
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem class_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (c : Classes K tick) :
    Fintype.card (Positions allocation m c) ≤
      basePopulationBound (K := K) (tick := tick) allocation * m := by
  have hc : activeCounts allocation 1 c.1 c.2 ≤
      basePopulationBound (K := K) (tick := tick) allocation := by
    unfold basePopulationBound
    exact Finset.single_le_sum
      (fun (d : Classes K tick) _ => Nat.zero_le (activeCounts allocation 1 d.1 d.2))
      (Finset.mem_univ c)
  simp only [Positions, JointCanonicalization.ClassPositions, Fintype.card_fin,
    activeCounts_dilation allocation m]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left m hc

end MatrixMultiplication.AllFieldHistoryOrbitCount

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitCount

open AllFieldHistory AllFieldHistorySupport PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem card_groupLetters {K tick : ℕ} {sigma : Placement}
    (c : GroupClasses K tick sigma) :
    Fintype.card (GroupLetters c) = 7 ^ activeHalfLength c.1.val := by
  simp only [GroupLetters, Fintype.card_fun, Fintype.card_fin]

theorem groupClass_card_le {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    {sigma : Placement} (c : GroupClasses K tick sigma) :
    Fintype.card (GroupPositions allocation m c) ≤
      AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m :=
  AllFieldHistoryOrbitCount.class_card_le allocation m (c.1.val, c.2)

theorem card_groupOrbit_le {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) ≤
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m + 1) ^
        groupDegree K tick sigma := by
  simpa only [GroupOrbit, groupDegree, card_groupLetters, two_mul] using
    (card_pairOrbits_le_common_bound
      (P := GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m)
      (X := GroupLetters (K := K) (tick := tick) (sigma := sigma))
      (Y := GroupLetters (K := K) (tick := tick) (sigma := sigma))
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation * m)
      (groupClass_card_le allocation m))

theorem card_groupOrbit_le_polynomial {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) ≤
      (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation + 1) ^
        groupDegree K tick sigma * (m + 1) ^ groupDegree K tick sigma := by
  refine (card_groupOrbit_le allocation m sigma).trans ?_
  rw [← mul_pow]
  apply Nat.pow_le_pow_left
  nlinarith [Nat.zero_le
    (AllFieldHistoryOrbitCount.basePopulationBound (K := K) (tick := tick) allocation)]

theorem card_groupOrbit_le_polynomial_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) ≤
      groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  unfold groupOrbitPrefactor
  exact_mod_cast card_groupOrbit_le_polynomial (K := K) (tick := tick) allocation m sigma

theorem taggedUsedGroupOrbits_card_le_real {K tick : ℕ}
    (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Finset (Fin 3 × GroupOrbit (K := K) (tick := tick) allocation m sigma)) :
    (s.card : ℝ) ≤ (3 * groupOrbitPrefactor (K := K) (tick := tick) allocation sigma) *
      ((m : ℝ) + 1) ^ groupDegree K tick sigma := by
  have hs : s.card ≤ 3 * Nat.card
      (GroupOrbit (K := K) (tick := tick) allocation m sigma) := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.card_eq_fintype_card] using
      s.card_le_univ
  have hsreal : (s.card : ℝ) ≤ 3 * (Nat.card
      (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := by
    exact_mod_cast hs
  calc
    _ ≤ 3 * (Nat.card (GroupOrbit (K := K) (tick := tick) allocation m sigma) : ℝ) := hsreal
    _ ≤ 3 * (groupOrbitPrefactor (K := K) (tick := tick) allocation sigma *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma) :=
      mul_le_mul_of_nonneg_left (card_groupOrbit_le_polynomial_real allocation m sigma)
        (by norm_num)
    _ = _ := (mul_assoc _ _ _).symm

end MatrixMultiplication.AllFieldGroupOrbitCount

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRates
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

open Filter
open scoped Topology

theorem factorialLogRemainder_succ (n : ℕ) :
    factorialLogRemainder (n + 1) = factorialLogRemainder n + 1 -
      (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  unfold factorialLogRemainder
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  push_cast
  ring

private theorem nat_mul_log_increment_le_one (n : ℕ) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hpos.le
  have heq : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp [hpos.ne']
    ring
  rwa [heq] at hmul

private theorem one_le_succ_mul_log_increment (n : ℕ) (hn : 0 < n) :
    1 ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) - Real.log n) := by
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsucc : 0 < (n : ℝ) + 1 := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hsucc hpos)
  rw [Real.log_div hsucc.ne' hpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hsucc.le
  have heq : ((n : ℝ) + 1) * (1 - (((n : ℝ) + 1) / (n : ℝ))⁻¹) = 1 := by
    rw [inv_div]
    field_simp [hsucc.ne']
    ring
  rwa [heq] at hmul

theorem factorialLogRemainder_nonneg (n : ℕ) : 0 ≤ factorialLogRemainder n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlog := nat_mul_log_increment_le_one n
    rw [factorialLogRemainder_succ]
    linarith

theorem factorialLogRemainder_le_one_add_log_pos (n : ℕ) :
    factorialLogRemainder (n + 1) ≤ 1 + Real.log (n + 1 : ℕ) := by
  induction n with
  | zero => norm_num [factorialLogRemainder]
  | succ n ih =>
    have hlog := one_le_succ_mul_log_increment (n + 1) (Nat.succ_pos n)
    have hstep := factorialLogRemainder_succ (n + 1)
    push_cast at ih hlog hstep ⊢
    nlinarith

theorem factorialLogRemainder_le_one_add_log (n : ℕ) :
    factorialLogRemainder n ≤ 1 + Real.log (n + 1 : ℕ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    refine (factorialLogRemainder_le_one_add_log_pos n).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.le_succ (n + 1)

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (fun a _ => by positivity)] at hlog
  linarith

private theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem log_multinomial_eq_entropy_add_remainder (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  rw [log_multinomial_eq_main_add_remainder, finiteEntropy_nat_normalize counts hD,
    mul_sub, mul_div_cancel₀ _ hD']

theorem log_multinomial_sub_entropy_eq_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  by_cases hD : 0 < ∑ a, counts a
  · rw [log_multinomial_eq_entropy_add_remainder counts hD]
    ring
  · have hzero : (∑ a, counts a) = 0 := Nat.eq_zero_of_not_pos hD
    have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, Nat.multinomial]

theorem abs_log_multinomial_sub_entropy_le (counts : A → ℕ) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  rw [log_multinomial_sub_entropy_eq_remainder]
  have hsum_nonneg : 0 ≤ ∑ a, factorialLogRemainder (counts a) :=
    Finset.sum_nonneg (fun a _ => factorialLogRemainder_nonneg (counts a))
  have heach (a : A) : factorialLogRemainder (counts a) ≤
      1 + Real.log ((∑ b, counts b) + 1 : ℕ) := by
    refine (factorialLogRemainder_le_one_add_log (counts a)).trans ?_
    apply add_le_add le_rfl
    apply Real.log_le_log
    · positivity
    · have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      exact_mod_cast Nat.add_le_add_right hle 1
  calc
    |factorialLogRemainder (∑ a, counts a) - ∑ a, factorialLogRemainder (counts a)| ≤
        |factorialLogRemainder (∑ a, counts a)| +
          |∑ a, factorialLogRemainder (counts a)| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (factorialLogRemainder (∑ a, counts a))
          (-(∑ a, factorialLogRemainder (counts a)))
    _ = factorialLogRemainder (∑ a, counts a) +
        ∑ a, factorialLogRemainder (counts a) := by
      rw [abs_of_nonneg (factorialLogRemainder_nonneg _), abs_of_nonneg hsum_nonneg]
    _ ≤ (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) +
        ∑ _a : A, (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) :=
      add_le_add (factorialLogRemainder_le_one_add_log _)
        (Finset.sum_le_sum (fun a _ => heach a))
    _ = ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem abs_log_multinomial_div_sub_entropy_le (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
  have hD' : (0 : ℝ) < (∑ a, counts a : ℕ) := Nat.cast_pos.mpr hD
  calc
    |Real.log (Nat.multinomial Finset.univ counts : ℝ) / (∑ a, counts a : ℕ) -
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| =
        |(Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))) /
              (∑ a, counts a : ℕ)| := by
      rw [sub_div, mul_div_cancel_left₀ _ hD'.ne']
    _ = |Real.log (Nat.multinomial Finset.univ counts : ℝ) -
          (∑ a, counts a : ℕ) *
            finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| /
              (∑ a, counts a : ℕ) := by
      rw [abs_div, abs_of_pos hD']
    _ ≤ ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts a) + 1 : ℕ)) / (∑ a, counts a : ℕ)) := by
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (abs_log_multinomial_sub_entropy_le counts) hD'.le

private theorem tendsto_one_add_log_succ_div :
    Tendsto (fun n : ℕ => (1 + Real.log (n + 1 : ℕ)) / (n : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconstant : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hshift := Real.tendsto_log_nat_add_one_sub_log.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => (1 : ℝ) / n +
        ((Real.log ((n : ℝ) + 1) - Real.log n) / n + Real.log n / n))
      atTop (𝓝 0) := by
    simpa using hconstant.add (hshift.add hlog)
  apply hsum.congr
  intro n
  push_cast
  ring

theorem tendsto_log_multinomial_div_sub_entropy {I : Type*} {l : Filter I}
    (counts : I → A → ℕ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
          (∑ a, counts i a : ℕ) -
        finiteEntropy (fun a => (counts i a : ℝ) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
  have hbound : Tendsto
      (fun i => ((Fintype.card A : ℝ) + 1) *
        ((1 + Real.log ((∑ a, counts i a) + 1 : ℕ)) / (∑ a, counts i a : ℕ)))
      l (𝓝 0) := by
    simpa using (tendsto_one_add_log_succ_div.comp htotal).const_mul
      ((Fintype.card A : ℝ) + 1)
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [htotal.eventually (eventually_gt_atTop (0 : ℕ))] with i hi
  simpa only [Real.norm_eq_abs] using
    abs_log_multinomial_div_sub_entropy_le (counts i) hi

theorem tendsto_log_multinomial_of_empirical_tendsto {I : Type*} {l : Filter I}
    (counts : I → A → ℕ) (p : A → ℝ)
    (htotal : Tendsto (fun i => ∑ a, counts i a) l atTop)
    (hmass : ∀ a, Tendsto
      (fun i => (counts i a : ℝ) / (∑ b, counts i b : ℕ)) l (𝓝 (p a))) :
    Tendsto
      (fun i => Real.log (Nat.multinomial Finset.univ (counts i) : ℝ) /
        (∑ a, counts i a : ℕ))
      l (𝓝 (finiteEntropy p)) := by
  have herror := tendsto_log_multinomial_div_sub_entropy counts htotal
  have hentropy := tendsto_finiteEntropy_of_tendsto hmass
  simpa only [zero_add, sub_add_cancel] using herror.add hentropy

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitTransport
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitData

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitCount JointPopulation JointCanonicalization
open JointCoarseHashing PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

theorem orbits_card_le (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    (((data allocation m ε sigma).orbits e).card : ℝ) ≤
      (3 * groupOrbitPrefactor (K := K) (tick := tick) allocation sigma) *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma :=
  taggedUsedGroupOrbits_card_le_real allocation m sigma _

end MatrixMultiplication.AllFieldGroupOrbitData

end




end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_GroupDegreeEnvelope
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegreeEnvelope

open AllFieldHistory AllFieldGroupOrbitData Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem eligibility_card_le (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma) :
    ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card ≤
      uniformDegree (K := K) (tick := tick) allocation m width sigma :=
  (le_max_left _ _).trans (Finset.le_sup (f := fun e =>
    max ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card
      (variableDegree (K := K) (tick := tick) allocation m width sigma e)) (Finset.mem_univ e))

theorem competitors_card_le (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m width sigma).orbits e)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v ∈ (data (K := K) (tick := tick) allocation m width sigma).passing e o) :
    ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card ≤
      uniformDegree (K := K) (tick := tick) allocation m width sigma := by
  have hvle := Finset.le_sup (f := fun v =>
    ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card) hv
  have hole := Finset.le_sup (f := fun o =>
    ((data (K := K) (tick := tick) allocation m width sigma).passing e o).sup fun v =>
      ((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card) ho
  have hel := Finset.le_sup (f := fun e =>
    max ((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card
      (variableDegree (K := K) (tick := tick) allocation m width sigma e)) (Finset.mem_univ e)
  exact hvle.trans (hole.trans ((le_max_right _ _).trans hel))

private theorem cast_max_le {a b : ℕ} {R : ℝ}
    (ha : (a : ℝ) ≤ R) (hb : (b : ℝ) ≤ R) : ((max a b : ℕ) : ℝ) ≤ R := by
  rcases le_total a b with hab | hba
  · simpa only [max_eq_right hab] using hb
  · simpa only [max_eq_left hba] using ha

private theorem cast_sup_le {I : Type*} (s : Finset I) (f : I → ℕ)
    {R : ℝ} (hR : 0 ≤ R) (hs : ∀ i ∈ s, (f i : ℝ) ≤ R) :
    ((s.sup f : ℕ) : ℝ) ≤ R := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using hR
  | @insert a s ha ih =>
      intro hs
      rw [Finset.sup_insert]
      exact cast_max_le (hs a (Finset.mem_insert_self a s))
        (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)))

theorem uniformDegree_real_le (allocation : Allocation) (m : ℕ) (width : ℝ)
    (sigma : Placement) {R : ℝ} (hR : 0 ≤ R)
    (heligibility : ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
      (((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤ R)
    (hcompetitors : ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
      ∀ o ∈ (data (K := K) (tick := tick) allocation m width sigma).orbits e,
        ∀ v ∈ (data (K := K) (tick := tick) allocation m width sigma).passing e o,
          (((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card : ℝ) ≤ R) :
    (uniformDegree (K := K) (tick := tick) allocation m width sigma : ℝ) ≤ R := by
  apply cast_sup_le _ _ hR
  intro e _
  apply cast_max_le (heligibility e)
  apply cast_sup_le _ _ hR
  intro o ho
  apply cast_sup_le _ _ hR
  exact hcompetitors e o ho

theorem eventually_log_uniformDegree_le (allocation : Allocation) (width : ℝ)
    (sigma : Placement) {D : ℝ} (hD : 0 ≤ D)
    (hcounts : ∀ᶠ m : ℕ in atTop,
      (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
        (((data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
          Real.exp ((m : ℝ) * D)) ∧
      (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
        ∀ o ∈ (data (K := K) (tick := tick) allocation m width sigma).orbits e,
          ∀ v ∈ (data (K := K) (tick := tick) allocation m width sigma).passing e o,
            (((data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card : ℝ) ≤
              Real.exp ((m : ℝ) * D))) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (uniformDegree (K := K) (tick := tick) allocation m width sigma : ℝ) /
        (m : ℝ) ≤ D := by
  filter_upwards [hcounts, eventually_gt_atTop (0 : ℕ)] with m hm hmp
  by_cases hz : uniformDegree (K := K) (tick := tick) allocation m width sigma = 0
  · simpa only [hz, Nat.cast_zero, Real.log_zero, zero_div] using hD
  have hd : (0 : ℝ) < uniformDegree (K := K) (tick := tick) allocation m width sigma := by
    exact_mod_cast Nat.pos_of_ne_zero hz
  have hb := uniformDegree_real_le (K := K) (tick := tick) allocation m width sigma
    (Real.exp_pos _).le hm.1 hm.2
  have hl := Real.log_le_log hd hb
  rw [Real.log_exp] at hl
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hmp
  exact (div_le_iff₀ hmpos).mpr (by simpa only [mul_comm] using hl)

end MatrixMultiplication.AllFieldGroupDegreeEnvelope

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_multiplicity _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_rankBound _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinishedWitness.witness_volume _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.weightCode_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.shapeValue_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workAmount_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workLotEquiv_symm_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_lot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_relot _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_self _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.workRelot_stage _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.card_tags _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.executionWithWidth_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialFamily.execution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.counts_false _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.bWeight_val _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.history_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inl _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalStatisticLaws.law_inr _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationRates

open MatrixMultiplication.Foundation Filter JointPopulation
open scoped BigOperators Topology

theorem tendsto_log_multinomial_div_of_total_div_zero
    {A : Type*} [Fintype A] [DecidableEq A] (counts : ℕ → A → ℕ)
    (hratio : Tendsto
      (fun n : ℕ => ((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hupperlim : Tendsto
      (fun n : ℕ => (((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ)) *
        Real.log (Fintype.card A : ℝ)) atTop (𝓝 0) := by
    simpa using hratio.mul_const (Real.log (Fintype.card A : ℝ))
  refine squeeze_zero ?_ ?_ hupperlim
  · intro n
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (Nat.succ_le_of_lt (Nat.multinomial_pos Finset.univ (counts n)))
    · exact Nat.cast_nonneg n
  · intro n
    have hcardNat : Nat.multinomial Finset.univ (counts n) ≤
        (Fintype.card A) ^ (∑ a, counts n a) := by
      simpa only [exactWords_card] using exactWords_card_le (counts n)
    have hcard : (Nat.multinomial Finset.univ (counts n) : ℝ) ≤
        (Fintype.card A : ℝ) ^ (∑ a, counts n a) := by
      exact_mod_cast hcardNat
    have hlog : Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) ≤
        ((∑ a, counts n a : ℕ) : ℝ) * Real.log (Fintype.card A : ℝ) := by
      simpa only [Real.log_pow] using
        Real.log_le_log (Nat.cast_pos.mpr (Nat.multinomial_pos Finset.univ (counts n))) hcard
    calc
      Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) / (n : ℝ) ≤
          (((∑ a, counts n a : ℕ) : ℝ) * Real.log (Fintype.card A : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n)
      _ = (((∑ a, counts n a : ℕ) : ℝ) / (n : ℝ)) *
          Real.log (Fintype.card A : ℝ) := by ring

theorem tendsto_log_multinomial_div_of_mass
    {A : Type*} [Fintype A] [DecidableEq A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hmass : 0 ≤ mass)
    (htotal : Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ))
      atTop (𝓝 mass))
    (hempirical : 0 < mass → ∀ a, Tendsto
      (fun n : ℕ => (counts n a : ℝ) / (∑ a, counts n a : ℕ)) atTop (𝓝 (p a))) :
    Tendsto (fun n : ℕ => Real.log (Nat.multinomial Finset.univ (counts n) : ℝ) /
      (n : ℝ)) atTop (𝓝 (mass * finiteEntropy p)) := by
  by_cases hzero : mass = 0
  · subst mass
    simpa only [zero_mul] using tendsto_log_multinomial_div_of_total_div_zero counts htotal
  have hpos : 0 < mass := lt_of_le_of_ne hmass (Ne.symm hzero)
  have htop : Tendsto (fun n => ∑ a, counts n a) atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ)).mp
      (Tendsto.num (tendsto_natCast_atTop_atTop (R := ℝ)) hpos htotal)
  have hlog := tendsto_log_multinomial_of_empirical_tendsto counts p htop (hempirical hpos)
  apply (htotal.mul hlog).congr'
  filter_upwards [htop.eventually (eventually_gt_atTop (0 : ℕ))] with n hn
  have hn' : ((∑ a, counts n a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  rw [div_mul_div_comm,
    mul_comm (n : ℝ) ((∑ a, counts n a : ℕ) : ℝ), mul_div_mul_left _ _ hn']

theorem tendsto_total_div_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ)) atTop (𝓝 mass) := by
  have h := tendsto_finsetSum Finset.univ (fun a _ => hcounts a)
  simpa only [← Finset.sum_div, ← Nat.cast_sum, ← Finset.mul_sum, hp, mul_one] using h

theorem tendsto_empirical_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hmass : 0 < mass) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) (a : A) :
    Tendsto (fun n : ℕ => (counts n a : ℝ) / (∑ a, counts n a : ℕ))
      atTop (𝓝 (p a)) := by
  have htotal := tendsto_total_div_of_coordinate_rates counts mass p hp hcounts
  have h := (hcounts a).div htotal hmass.ne'
  rw [mul_div_cancel_left₀ _ hmass.ne'] at h
  apply h.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  exact div_div_div_cancel_right₀ (Nat.cast_ne_zero.mpr hn) _ _

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem tendsto_log_target_card_div
    (counts : ℕ → H → Shape → ℕ) (mass : H → ℝ) (p : H → Shape → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (htotal : ∀ h, Tendsto (fun n : ℕ => (∑ a, counts n h a : ℕ) / (n : ℝ))
      atTop (𝓝 (mass h)))
    (hempirical : ∀ h, 0 < mass h → ∀ a, Tendsto
      (fun n : ℕ => (counts n h a : ℝ) / (∑ a, counts n h a : ℕ))
        atTop (𝓝 (p h a))) :
    Tendsto (fun n : ℕ => Real.log (Fintype.card (Target (counts n)) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ h, mass h * finiteEntropy (p h))) := by
  simp_rw [target_card]
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun h _ n => Nat.multinomial_pos _ _)
    (fun h _ => tendsto_log_multinomial_div_of_mass
      (fun n => counts n h) (mass h) (p h) (hmass h) (htotal h) (hempirical h))

theorem tendsto_log_target_card_div_of_coordinate_rates
    (counts : ℕ → H → Shape → ℕ) (mass : H → ℝ) (p : H → Shape → ℝ)
    (hmass : ∀ h, 0 ≤ mass h) (hp : ∀ h, ∑ a, p h a = 1)
    (hcounts : ∀ h a, Tendsto (fun n : ℕ => (counts n h a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass h * p h a))) :
    Tendsto (fun n : ℕ => Real.log (Fintype.card (Target (counts n)) : ℝ) / (n : ℝ))
      atTop (𝓝 (∑ h, mass h * finiteEntropy (p h))) := by
  apply tendsto_log_target_card_div counts mass p hmass
  · intro h
    exact tendsto_total_div_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) (hp h) (hcounts h)
  · intro h hpos a
    exact tendsto_empirical_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) hpos (hp h) (hcounts h) a

end MatrixMultiplication.JointPopulationRates






namespace MatrixMultiplication.AllFieldActiveLaws

open AllFieldParameters AllFieldHistory MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

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

theorem population_cast_real {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : History K) :
    (population allocation dilation h : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * (amount allocation h : ℝ) := by
  exact_mod_cast population_cast allocation dilation h

theorem jointCounts_source_cast {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ((amount allocation (w.1.source, w.2) : ℝ) * (placedLaw w).mass u) := by
  rw [jointCounts_cast, population_cast_real, mul_assoc]

theorem populationLength_dilation {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    populationLength (K := K) allocation dilation =
      dilation * populationLength (K := K) allocation 1 := by
  simp only [populationLength, AllFieldPopulationCounts.blockLength, one_mul]

theorem jointCounts_dilation_ratio {K dilation : ℕ} (allocation : Allocation)
    (hd : 0 < dilation) (w : PlacedWork K) (u : JointPopulation.Shape) :
    (jointCounts allocation dilation w u : ℝ) / (dilation : ℝ) =
      ((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u := by
  rw [jointCounts_source_cast, populationLength_dilation, Nat.cast_mul]
  have hd' : (dilation : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  field_simp [hd']

theorem jointCounts_dilation_rate {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (jointCounts allocation dilation w u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) *
        (amount allocation (w.1.source, w.2) : ℝ)) * (placedLaw w).mass u)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (jointCounts_dilation_ratio allocation hd w u).symm

theorem orderMass_nonneg {K tick : ℕ} {sigma : Placement} (allocation : Allocation)
    (h : ActiveOrder K tick sigma) : 0 ≤ orderMass allocation h := by
  unfold orderMass
  exact_mod_cast amount_nonneg allocation (h.val.val.1.source, h.val.val.2)

theorem orderCounts_dilation_rate {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) :
    Tendsto (fun dilation : ℕ => (orderCounts allocation dilation h u : ℝ) /
      (dilation : ℝ)) atTop
      (𝓝 (((populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h) *
        (orderLaw h).mass u)) :=
  jointCounts_dilation_rate allocation h.val.val u

end MatrixMultiplication.AllFieldActiveLaws






namespace MatrixMultiplication.AllFieldGroupTargetRate

open AllFieldHistory AllFieldActiveLaws MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem target_card_pos (allocation : Allocation) (m : ℕ) :
    0 < Fintype.card (JointPopulation.Target
      (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)) :=
  Fintype.card_pos_iff.mpr (JointPopulation.target_nonempty _)

theorem tendsto_log_target_card_div (allocation : Allocation) :
    Tendsto (fun m : ℕ =>
      Real.log (Fintype.card (JointPopulation.Target
        (orderCounts (K := K) (tick := tick) (sigma := sigma) allocation m)) : ℝ) /
          (m : ℝ)) atTop
      (𝓝 (groupEntropyRate (K := K) (tick := tick) (sigma := sigma) allocation)) := by
  apply JointPopulationRates.tendsto_log_target_card_div_of_coordinate_rates
    (fun m => orderCounts allocation m)
    (fun h => (populationLength (K := K) allocation 1 : ℝ) * orderMass allocation h)
    (fun h => (orderLaw h).mass)
  · intro h
    exact mul_nonneg (Nat.cast_nonneg _) (orderMass_nonneg allocation h)
  · intro h
    exact (orderLaw h).total
  · exact orderCounts_dilation_rate allocation

end MatrixMultiplication.AllFieldGroupTargetRate






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointOrdinaryPopulationSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.JointCapacityAlgebra

open scoped BigOperators

theorem total_sub_max_degrees (A X Y Z : ℝ) :
    A - max (A - X) (max (A - Y) (A - Z)) = min X (min Y Z) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem weighted_joint_capacity {H : Type*} [Fintype H]
    (mass entropy : H → ℝ) (capacity : H → Fin 3 → ℝ) :
    (∑ h, mass h * entropy h) -
        max (∑ h, mass h * (entropy h - capacity h 0))
          (max (∑ h, mass h * (entropy h - capacity h 1))
            (∑ h, mass h * (entropy h - capacity h 2))) =
      min (∑ h, mass h * capacity h 0)
        (min (∑ h, mass h * capacity h 1) (∑ h, mass h * capacity h 2)) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  exact total_sub_max_degrees _ _ _ _

end MatrixMultiplication.JointCapacityAlgebra





noncomputable section

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

theorem sideMass_entropy_le (p : FiniteLaw Shape) (s : Fin 3) :
    finiteEntropy (sideMass p.mass s) ≤ finiteEntropy p.mass := by
  simpa only [finiteEntropy, FiniteLaw.map_mass, sideMass] using
    p.map_entropy_le (shapeSide s)

end MatrixMultiplication.JointOrdinaryPopulationSelection

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_ScheduledPositivity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

theorem order_capacity_eq_physical (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) (i : Fin 3) :
    (∑ h : ActiveOrder K tick sigma,
      AllFieldActiveLaws.orderMass allocation h * workCapacity h.val.val.1 i) =
      physicalTickCapacity allocation tick (workCapacity (K := K)) sigma i := by
  rw [physicalTickCapacity_eq_sixth]
  rw [← (canonicalActiveEquivOrder K tick sigma).sum_comp
    (fun h : ActiveOrder K tick sigma =>
      AllFieldActiveLaws.orderMass allocation h * workCapacity h.val.val.1 i)]
  simp only [AllFieldActiveLaws.orderMass, canonicalActiveEquivOrder, amount,
    Rat.cast_div, Rat.cast_ofNat, activeAggregateCapacity,
    PhysicalOrders.aggregateCapacity, workAmount]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  change ((canonicalAmount allocation h.val.source : ℝ) / 6) *
    workCapacity h.val i = (1 / 6 : ℝ) *
      ((canonicalAmount allocation h.val.source : ℝ) * workCapacity h.val i)
  ring

theorem order_capacity_eq_native (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) (i : Fin 3) :
    (∑ h : ActiveOrder K tick sigma,
      AllFieldActiveLaws.orderMass allocation h * workCapacity h.val.val.1 i) =
      (1 / 6 : ℝ) * FiniteSchedule.tickCapacity K nativeLA nativeLB
        (nativeLC (fun j => (allocation.mass j : ℝ))) tick i := by
  rw [order_capacity_eq_physical, physical_order_native_capacity]

theorem order_dilation_capacity (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) (i : Fin 3) :
    (∑ h : ActiveOrder K tick sigma,
      ((populationLength (K := K) allocation 1 : ℝ) *
        AllFieldActiveLaws.orderMass allocation h) * workCapacity h.val.val.1 i) =
      (populationLength (K := K) allocation 1 : ℝ) *
        ((1 / 6 : ℝ) * FiniteSchedule.tickCapacity K nativeLA nativeLB
          (nativeLC (fun j => (allocation.mass j : ℝ))) tick i) := by
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, order_capacity_eq_native]

end MatrixMultiplication.AllFieldScheduledYield

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_GroupSelectionParameters
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
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

theorem order_first_capacity {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) :
    workCapacity h.val.val.1 0 = finiteEntropy
      (JointPopulationRates.sideMass (orderLaw h).mass (sigma 0)) := by
  have hh := workCapacity_first h.val.val
  rw [h.property] at hh
  exact hh

theorem order_entropy_sub_native_degree (K tick : ℕ) (allocation : Allocation)
    (sigma : Placement) :
    orderEntropyRate (K := K) (tick := tick) allocation sigma -
      max (orderNativeDegree (K := K) (tick := tick) allocation sigma 0)
        (max (orderNativeDegree (K := K) (tick := tick) allocation sigma 1)
          (orderNativeDegree (K := K) (tick := tick) allocation sigma 2)) =
      (populationLength (K := K) allocation 1 : ℝ) *
        ((1 / 6 : ℝ) * Staggering.minCapacity
          (FiniteSchedule.tickCapacity K nativeLA nativeLB
            (nativeLC (fun i => (allocation.mass i : ℝ))) tick)) := by
  unfold orderEntropyRate orderNativeDegree
  rw [JointCapacityAlgebra.weighted_joint_capacity]
  simp_rw [order_dilation_capacity, ← mul_assoc]
  exact PhysicalOrders.minCapacity_mul _ _ (by positivity)

end MatrixMultiplication.AllFieldActiveCapacity

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem firstDegree_nonneg (allocation : Allocation) (sigma : Placement) :
    0 ≤ orderNativeDegree (K := K) (tick := tick) allocation sigma 0 := by
  apply Finset.sum_nonneg
  intro h _
  apply mul_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (orderMass_nonneg allocation h)
  · rw [order_first_capacity h]
    exact sub_nonneg.mpr
      (JointOrdinaryPopulationSelection.sideMass_entropy_le (orderLaw h) (sigma 0))

theorem nativeDegree_nonneg (allocation : Allocation) (sigma : Placement) :
    0 ≤ nativeDegree (K := K) (tick := tick) allocation sigma :=
  (firstDegree_nonneg allocation sigma).trans (le_max_left _ _)

theorem targetEntropy_sub_degree (allocation : Allocation) (sigma : Placement) :
    AllFieldGroupTargetRate.groupEntropyRate (K := K) (tick := tick)
      (sigma := sigma) allocation - nativeDegree (K := K) (tick := tick) allocation sigma =
        nativeCapacity (K := K) (tick := tick) allocation :=
  order_entropy_sub_native_degree K tick allocation sigma

theorem selectionHashRate_nonneg (allocation : Allocation) (sigma : Placement)
    {slack : ℝ} (hslack : 0 < slack) :
    0 ≤ selectionHashRate (K := K) (tick := tick) allocation sigma slack := by
  unfold selectionHashRate
  linarith [nativeDegree_nonneg (K := K) (tick := tick) allocation sigma]

theorem selectionHashRate_window_gap (allocation : Allocation) (sigma : Placement)
    {slack : ℝ} (hslack : 0 < slack) :
    nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4 <
      selectionHashRate (K := K) (tick := tick) allocation sigma slack := by
  unfold selectionHashRate
  linarith

theorem selection_exponent (allocation : Allocation) (sigma : Placement) (slack : ℝ) :
    AllFieldGroupTargetRate.groupEntropyRate (K := K) (tick := tick)
      (sigma := sigma) allocation -
        selectionHashRate (K := K) (tick := tick) allocation sigma slack - slack / 2 =
      nativeCapacity (K := K) (tick := tick) allocation - slack := by
  rw [selectionHashRate]
  linarith [targetEntropy_sub_degree (K := K) (tick := tick) allocation sigma]

end MatrixMultiplication.AllFieldGroupSelection

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupSelection
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem data_orbits_card_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement)
    (e : AllFieldGroupOrbitData.Targets (K := K) (tick := tick) allocation m sigma) :
    ((AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m ε sigma).orbits e).card ≤
      orbitPrefactor (K := K) (tick := tick) allocation sigma *
        (m + 1) ^ AllFieldGroupOrbitCount.groupDegree K tick sigma := by
  have hb := AllFieldGroupOrbitData.orbits_card_le allocation m ε sigma e
  unfold orbitPrefactor AllFieldGroupOrbitCount.groupOrbitPrefactor at *
  exact_mod_cast hb

theorem data_coarse_injective (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) :
    Function.Injective
      (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m ε sigma).coarse :=
  AllFieldGroupOrbitData.coarse_injective allocation m sigma

end MatrixMultiplication.AllFieldGroupSelection

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

private theorem selected_of_native_count_bound
    (allocation : Allocation) (sigma : Placement) (width : ℝ)
    {slack : ℝ} (hslack : 0 < slack)
    (hcounts : ∀ᶠ m : ℕ in atTop,
      (∀ e : AllFieldGroupOrbitData.Targets (K := K) (tick := tick) allocation m sigma,
        (((AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
          Real.exp ((m : ℝ) *
            (nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4))) ∧
      (∀ e : AllFieldGroupOrbitData.Targets (K := K) (tick := tick) allocation m sigma,
        ∀ o ∈ (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).orbits e,
          ∀ v ∈ (AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).passing e o,
            (((AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma).competitors e o v).card : ℝ) ≤
              Real.exp ((m : ℝ) *
                (nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4)))) :
    ∀ᶠ m : ℕ in atTop,
      Nonempty (Selected (K := K) (tick := tick) allocation m width sigma slack) := by
  have hD : 0 ≤ nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4 := by
    linarith [nativeDegree_nonneg (K := K) (tick := tick) allocation sigma]
  have hdegree := AllFieldGroupDegreeEnvelope.eventually_log_uniformDegree_le
    allocation width sigma hD hcounts
  have hrate : ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      Real.log (AllFieldGroupDegreeEnvelope.uniformDegree
        (K := K) (tick := tick) allocation m width sigma : ℝ) / (m : ℝ) ≤
          nativeDegree (K := K) (tick := tick) allocation sigma + slack / 4 + η := by
    intro η hη
    filter_upwards [hdegree] with m hm
    linarith
  let : ∀ m : ℕ, Fintype (AllFieldGroupOrbitData.Pos
      (K := K) (tick := tick) allocation m sigma) := fun m => inferInstance
  let : ∀ m : ℕ, Fintype (AllFieldGroupOrbitData.Targets
      (K := K) (tick := tick) allocation m sigma) := fun m => inferInstance
  have hselected := JointMaskedGoodSelection.eventually_exists_good_selection
    (fun m => AllFieldGroupOrbitData.data (K := K) (tick := tick) allocation m width sigma)
    (fun m => data_coarse_injective (K := K) (tick := tick) allocation m width sigma)
    (fun m => AllFieldGroupDegreeEnvelope.uniformDegree (K := K) (tick := tick) allocation m width sigma)
    (orbitPrefactor (K := K) (tick := tick) allocation sigma)
    (AllFieldGroupOrbitCount.groupDegree K tick sigma)
    (fun m => AllFieldGroupDegreeEnvelope.eligibility_card_le (K := K) (tick := tick) allocation m width sigma)
    (fun m => AllFieldGroupDegreeEnvelope.competitors_card_le (K := K) (tick := tick) allocation m width sigma)
    (fun m => data_orbits_card_le (K := K) (tick := tick) allocation m width sigma)
    (selectionHashRate_nonneg (K := K) (tick := tick) allocation sigma hslack)
    (selectionHashRate_window_gap (K := K) (tick := tick) allocation sigma hslack) hrate
    (Eventually.of_forall (AllFieldGroupTargetRate.target_card_pos
      (K := K) (tick := tick) (sigma := sigma) allocation))
    (AllFieldGroupTargetRate.tendsto_log_target_card_div
      (K := K) (tick := tick) (sigma := sigma) allocation)
    (half_pos hslack)
  filter_upwards [hselected] with m hm
  obtain ⟨s, G, hcard, hgood, hdistinct⟩ := hm
  refine ⟨{
    sample := s
    targets := G
    card_targets := ?_
    good := hgood
    distinct_first := hdistinct }⟩
  simpa only [selection_exponent] using hcard

theorem exists_threshold_eventually_selected_oai
    (allocation : Allocation) (sigma : Placement)
    {slack widthMax : ℝ} (hslack : 0 < slack) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          Nonempty (Selected (K := K) (tick := tick) allocation m width sigma slack) := by
  obtain ⟨threshold, hthreshold, hthresholdMax, hcounts⟩ :=
    AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le
      (K := K) (tick := tick) allocation sigma
      (show 0 < slack / 4 by linarith) hwidthMax
  refine ⟨threshold, hthreshold, hthresholdMax, ?_⟩
  intro width hwidth hsmall
  apply selected_of_native_count_bound (K := K) (tick := tick) allocation sigma width hslack
  simpa only [nativeDegree, AllFieldGroupNativeDegreeBound.maxNativeDegree] using
    hcounts width hwidth hsmall

end MatrixMultiplication.AllFieldGroupSelection

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected_oai

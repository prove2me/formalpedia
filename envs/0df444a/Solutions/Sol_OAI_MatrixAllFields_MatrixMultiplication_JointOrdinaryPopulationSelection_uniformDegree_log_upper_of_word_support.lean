-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:54:52.813684+00:00
-- url     : https://prove2.me/submissions/d4f351c2-b4d8-40c3-bd88-a0bc80944011

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRateFormula
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

theorem tendsto_entropyTerm {I : Type*} {l : Filter I} {p : I → ℝ} {q : ℝ}
    (h : Tendsto p l (𝓝 q)) :
    Tendsto (fun i => entropyTerm (p i)) l (𝓝 (entropyTerm q)) :=
  continuous_entropyTerm.continuousAt.tendsto.comp h

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
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointLossCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointLossCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω V I : Type*}

theorem card_filter_exists_le (samples : Finset Ω) (indices : Finset I)
    (event : I → Ω → Prop) :
    (samples.filter (fun ω => ∃ i ∈ indices, event i ω)).card ≤
      ∑ i ∈ indices, (samples.filter (event i)).card := by
  classical
  have heq : samples.filter (fun ω => ∃ i ∈ indices, event i ω) =
      indices.biUnion (fun i => samples.filter (event i)) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hω, i, hi, he⟩
      exact ⟨i, hi, hω, he⟩
    · rintro ⟨i, hi, hω, he⟩
      exact ⟨hω, i, hi, he⟩
  rw [heq]
  exact Finset.card_biUnion_le

end MatrixMultiplication.JointLossCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

theorem exactWords_card_pos (counts : A → ℕ) : 0 < Fintype.card (ExactWords counts) := by
  rw [exactWords_card]
  exact Nat.multinomial_pos Finset.univ counts

end MatrixMultiplication.Foundation





namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

theorem populationWords_card (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) :
    Fintype.card (PopulationWords I counts) = Nat.multinomial Finset.univ counts := by
  rw [Fintype.card_congr (populationWordsEquiv counts h), exactWords_card]

theorem conditionalWords_card (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Fintype.card (ConditionalWords w counts) =
      ∏ a, Nat.multinomial Finset.univ (counts a) := by
  rw [Fintype.card_congr (conditionalWordsEquiv w counts), Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => populationWords_card (counts a) (h a)

theorem conditionalWords_card_pos (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    0 < Fintype.card (ConditionalWords w counts) := by
  rw [conditionalWords_card w counts h]
  exact Finset.prod_pos fun a _ => Nat.multinomial_pos Finset.univ (counts a)

theorem conditionalWords_nonempty (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Nonempty (ConditionalWords w counts) :=
  Fintype.card_pos_iff.mp (conditionalWords_card_pos w counts h)

theorem conditionalWords_nonempty_iff (w : I → A) (counts : A → B → ℕ) :
    Nonempty (ConditionalWords w counts) ↔
      ∀ a, wordPopulation w a = ∑ b, counts a b := by
  constructor
  · rintro ⟨r⟩ a
    calc
      wordPopulation w a =
          ∑ b, wordPopulation (fun i : {i // w i = a} => r.val i.val) b :=
        (wordPopulation_sum _).symm
      _ = ∑ b, counts a b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [wordPopulation_fiber, r.property]
  · exact conditionalWords_nonempty w counts

omit [DecidableEq A] [DecidableEq B] in
theorem multinomial_prod_counts (counts : A × B → ℕ) :
    Nat.multinomial Finset.univ counts =
      Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
        ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b)) := by
  apply Nat.mul_left_cancel (Nat.prod_factorial_pos Finset.univ counts)
  rw [Nat.multinomial_spec]
  symm
  calc
    (∏ ab, (counts ab).factorial) *
        (Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) =
        ((∏ a, ∏ b, (counts (a, b)).factorial) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Fintype.prod_prod_type]
      ac_rfl
    _ = (∏ a, ((∏ b, (counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun b => counts (a, b)))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ a, (∑ b, counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact Nat.multinomial_spec Finset.univ (fun b => counts (a, b))
    _ = (∑ a, ∑ b, counts (a, b)).factorial :=
      Nat.multinomial_spec Finset.univ (fun a => ∑ b, counts (a, b))
    _ = (∑ ab, counts ab).factorial := by rw [Fintype.sum_prod_type]

end MatrixMultiplication.Foundation





noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

theorem pushforwardCounts_sum {A B : Type*} [Fintype A] [Fintype B]
    (counts : A → ℕ) (label : A → B) :
    (∑ b, pushforwardCounts counts label b) = ∑ a, counts a := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  simp

theorem pushforwardCounts_apply {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (hinjective : Function.Injective label)
    (a : A) : pushforwardCounts counts label (label a) = counts a := by
  classical
  simp [pushforwardCounts, hinjective.eq_iff]

theorem pushforwardCounts_sum_pair {A B C : Type*}
    [Fintype A] [Fintype C] (counts : A → ℕ)
    (coarse : A → B) (fine : A → C) (b : B) :
    (∑ c, pushforwardCounts counts (fun a => (coarse a, fine a)) (b, c)) =
      pushforwardCounts counts coarse b := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : coarse a = b
  · simp [Prod.mk.injEq, hab]
  · simp [Prod.mk.injEq, hab]

theorem pushforwardCounts_factorial_prod_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    (∏ b, (pushforwardCounts counts label b).factorial) =
      ∏ a, (counts a).factorial := by
  classical
  have hfactor (b : B) : (pushforwardCounts counts label b).factorial =
      ∏ a, if label a = b then (counts a).factorial else 1 := by
    by_cases hb : ∃ a, label a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [pushforwardCounts_apply counts label hinjective]
      simp [hinjective.eq_iff]
    · simp [pushforwardCounts, not_exists.mp hb]
  simp_rw [hfactor]
  rw [Finset.prod_comm]
  simp

theorem multinomial_pushforwardCounts_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    Nat.multinomial Finset.univ (pushforwardCounts counts label) =
      Nat.multinomial Finset.univ counts := by
  simp only [Nat.multinomial, pushforwardCounts_sum,
    pushforwardCounts_factorial_prod_of_injective counts label hinjective]

end MatrixMultiplication.Foundation






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulation
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

end MatrixMultiplication.Foundation





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointTypeCounts
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_apply _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.joinGroupTargets_on_group _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointTypeCounts

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology

section CoarseFibers

variable {I A B : Type*} [Fintype I] [DecidableEq I]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] [Fintype B] in
private theorem pushforwardCounts_eq_sum (counts : A → ℕ) (f : A → B) (b : B) :
    pushforwardCounts counts f b = ∑ a, if f a = b then counts a else 0 := by
  classical
  dsimp only [pushforwardCounts]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, if_true, ite_false, if_false]

theorem fixedCoarseWords_card (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Fintype.card (FixedCoarseWords counts f k) =
      ∏ b, Nat.multinomial Finset.univ (fun a => if f a = b then counts a else 0) := by
  rw [Fintype.card_congr (fixedCoarseWordsEquiv counts f k)]
  apply conditionalWords_card
  intro b
  rw [← pushforwardCounts_eq_sum]
  exact hk b

theorem fixedCoarseWords_card_pos (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    0 < Fintype.card (FixedCoarseWords counts f k) := by
  rw [fixedCoarseWords_card counts f k hk]
  exact Finset.prod_pos fun b _ => Nat.multinomial_pos _ _

theorem exactWords_card_eq_coarse_mul_fixed (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (pushforwardCounts counts f)) *
        Fintype.card (FixedCoarseWords counts f k) := by
  classical
  have hgraph (b : B) (a : A) :
      pushforwardCounts counts (fun a => (f a, a)) (b, a) =
        if f a = b then counts a else 0 := by
    simp [pushforwardCounts, Prod.mk.injEq, and_comm, ite_and]
  have hinj : Function.Injective (fun a : A => (f a, a)) :=
    fun _ _ h => congrArg Prod.snd h
  have hmain := multinomial_prod_counts
    (pushforwardCounts counts (fun a => (f a, a)))
  rw [multinomial_pushforwardCounts_of_injective counts _ hinj] at hmain
  simp_rw [pushforwardCounts_sum_pair, hgraph] at hmain
  rw [exactWords_card, exactWords_card, fixedCoarseWords_card counts f k hk]
  exact hmain

theorem log_fixedCoarseWords_card (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) =
      Real.log (Nat.multinomial Finset.univ counts : ℝ) -
        Real.log (Nat.multinomial Finset.univ (pushforwardCounts counts f) : ℝ) := by
  have h := congrArg (fun n : ℕ => Real.log (n : ℝ))
    (exactWords_card_eq_coarse_mul_fixed counts f k hk)
  rw [Nat.cast_mul, Real.log_mul] at h
  · simpa only [exactWords_card] using (eq_sub_iff_add_eq.mpr (by linarith :
      Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) +
        Real.log (Fintype.card (ExactWords (pushforwardCounts counts f)) : ℝ) =
          Real.log (Fintype.card (ExactWords counts) : ℝ)))
  · exact_mod_cast (Nat.ne_of_gt (exactWords_card_pos (pushforwardCounts counts f)))
  · exact_mod_cast (Nat.ne_of_gt (fixedCoarseWords_card_pos counts f k hk))

theorem abs_log_fixedCoarseWords_card_sub_entropy_le
    (counts : A → ℕ) (f : A → B) (k : I → B)
    (hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b) :
    |Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) -
      (∑ a, counts a : ℕ) *
        (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) -
          finiteEntropy (fun b => (pushforwardCounts counts f b : ℝ) /
            (∑ a, counts a : ℕ)))| ≤
      ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hA := abs_log_multinomial_sub_entropy_le counts
  have hB := abs_log_multinomial_sub_entropy_le (pushforwardCounts counts f)
  rw [pushforwardCounts_sum] at hB
  rw [log_fixedCoarseWords_card counts f k hk]
  have h := (abs_sub
    (Real.log (Nat.multinomial Finset.univ counts : ℝ) -
      (∑ a, counts a : ℕ) *
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))
    (Real.log (Nat.multinomial Finset.univ (pushforwardCounts counts f) : ℝ) -
      (∑ a, counts a : ℕ) *
        finiteEntropy (fun b => (pushforwardCounts counts f b : ℝ) /
          (∑ a, counts a : ℕ)))).trans (add_le_add hA hB)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1 <;> ring)

theorem card_allowed_over_coarse_le
    (f : A → B) (k : I → B) (allowed : (I → A) → Prop) [DecidablePred allowed]
    (H : ℝ)
    (hcoarse : ∀ w, allowed w → ∀ i, f (w i) = k i)
    (hentropy : ∀ w, allowed w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ H) :
    (Fintype.card {w : I → A // allowed w} : ℝ) ≤
      ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
        Real.exp ((Fintype.card I : ℝ) *
          (H - finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) +
          ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
            (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
  classical
  let S := {w : I → A // allowed w}
  let T := A → Fin (Fintype.card I + 1)
  let E : ℝ := (Fintype.card I : ℝ) *
    (H - finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) +
    ((Fintype.card A : ℝ) + (Fintype.card B : ℝ) + 2) *
      (1 + Real.log (Fintype.card I + 1 : ℕ))
  let profile : S → T := fun w a =>
    ⟨wordPopulation w.val a,
      Nat.lt_succ_of_le (Fintype.card_subtype_le (fun i : I => w.val i = a))⟩
  have hcap (p : T) :
      (Fintype.card {w : S // profile w = p} : ℝ) ≤ Real.exp E := by
    let Fiber := {w : S // profile w = p}
    by_cases hn : Nonempty Fiber
    · let : Nonempty Fiber := hn
      let w : Fiber := Classical.choice hn
      let counts : A → ℕ := wordPopulation w.val.val
      let encode : Fiber → FixedCoarseWords counts f k := fun v =>
        ⟨v.val.val, ⟨fun a => by
          change wordPopulation v.val.val a = wordPopulation w.val.val a
          exact congrArg Fin.val (congrFun (v.property.trans w.property.symm) a),
          hcoarse v.val.val v.val.property⟩⟩
      have hinj : Function.Injective encode := by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : FixedCoarseWords counts f k => z.val) h
      have hk : ∀ b, wordPopulation k b = pushforwardCounts counts f b := by
        have hh := (conditionalWords_nonempty_iff k
          (fun b a => if f a = b then counts a else 0)).mp
            ⟨fixedCoarseWordsEquiv counts f k (encode w)⟩
        intro b
        rw [pushforwardCounts_eq_sum]
        exact hh b
      have htotal : (∑ a, counts a) = Fintype.card I := wordPopulation_sum w.val.val
      have hbound := (abs_le.mp
        (abs_log_fixedCoarseWords_card_sub_entropy_le counts f k hk)).2
      rw [htotal] at hbound
      simp_rw [← hk] at hbound
      have hw := hentropy w.val.val w.val.property
      have hmain := mul_le_mul_of_nonneg_left
        (sub_le_sub_right hw
          (finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)))
        (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ Fintype.card I)
      have hfixed : Real.log (Fintype.card (FixedCoarseWords counts f k) : ℝ) ≤ E := by
        dsimp only [E]
        change (Fintype.card I : ℝ) *
          (finiteEntropy (fun a => (counts a : ℝ) / Fintype.card I) -
            finiteEntropy (fun b => (wordPopulation k b : ℝ) / Fintype.card I)) ≤
          _ at hmain
        linarith
      have hpos : (0 : ℝ) < Fintype.card Fiber := Nat.cast_pos.mpr Fintype.card_pos
      have hlog : Real.log (Fintype.card Fiber : ℝ) ≤ E :=
        (Real.log_le_log hpos
          (Nat.cast_le.mpr (Fintype.card_le_of_injective encode hinj))).trans hfixed
      simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog
    · let : IsEmpty Fiber := ⟨fun w => hn ⟨w⟩⟩
      change (Fintype.card Fiber : ℝ) ≤ Real.exp E
      simpa only [Fintype.card_of_isEmpty, Nat.cast_zero] using (Real.exp_pos E).le
  have hdecomp : Fintype.card S = ∑ p : T, Fintype.card {w : S // profile w = p} := by
    simpa only [Fintype.card_sigma] using
      (Fintype.card_congr (Equiv.sigmaFiberEquiv profile)).symm
  calc
    (Fintype.card S : ℝ) =
        ∑ p : T, (Fintype.card {w : S // profile w = p} : ℝ) := by
      exact_mod_cast hdecomp
    _ ≤ ∑ _p : T, Real.exp E := Finset.sum_le_sum fun p _ => hcap p
    _ = (Fintype.card T : ℝ) * Real.exp E := by simp
    _ = _ := by simp [T, E]

end CoarseFibers

end MatrixMultiplication.JointTypeCounts

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointMarginalSupport
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointAmbientDegree

open MatrixMultiplication.Foundation JointPopulation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*} [Fintype H] [DecidableEq H]
  (counts : H → Shape → ℕ)

omit [Fintype H] [DecidableEq H] in
theorem localWord_injective : Function.Injective (localWord counts) := by
  intro t u he
  apply Prod.ext
  · funext p
    exact congrArg (fun w => (w p.1 p.2).1) he
  · apply Prod.ext
    · funext p
      exact congrArg (fun w => (w p.1 p.2).2.1) he
    · funext p
      exact congrArg (fun w => (w p.1 p.2).2.2) he

theorem localAllowed_of_mem_ambient (sum : H → ℕ)
    (t : JointCoarseHashing.Triple (Position counts))
    (ht : t ∈ ambientSet counts sum) (h : H) :
    localAllowed counts sum h (localWord counts t h) := by
  obtain ⟨hs, hm⟩ := (Finset.mem_filter.mp ht).2
  exact ⟨fun i => hs ⟨h, i⟩, fun s a => hm h s a⟩

omit [Fintype H] [DecidableEq H] in
theorem classBound_eq_exp (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) (h : H) (entropyCap : ℝ) :
    classBound counts s e h entropyCap = Real.exp (classExponent counts s e h entropyCap) := by
  unfold classBound classExponent
  conv_rhs => rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]
  exact mul_comm _ _

omit [Fintype H] [DecidableEq H] in
theorem classExponent_target_eq (s : Fin 3) (e : Target counts) (h : H)
    (entropyCap : ℝ) :
    classExponent counts s (triple counts e) h entropyCap =
      classExponent counts s (triple counts (canonicalTarget counts)) h entropyCap := by
  simp_rw [classExponent, marginal_population_eq counts e (canonicalTarget counts)]

theorem sharedAmbient_card_le (sum : H → ℕ) (s : Fin 3)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h) :
    ((sharedAmbient counts sum s e).card : ℝ) ≤
      ∏ h, classBound counts s e h (entropyCap h) := by
  classical
  let Allowed := fun h (w : Positions counts h → Shape) =>
    localAllowed counts sum h w ∧ ∀ i, shapeSide s (w i) = sideWord counts s e h i
  let Local := fun h => {w : Positions counts h → Shape // Allowed h w}
  let encode : {t // t ∈ sharedAmbient counts sum s e} → ∀ h, Local h := fun t h =>
    ⟨localWord counts t.val h, localAllowed_of_mem_ambient counts sum t.val
      (Finset.mem_filter.mp t.property).1 h,
      fun i => congrFun ((Finset.mem_filter.mp t.property).2 h) i⟩
  have hinj : Function.Injective encode := by
    intro t u he
    apply Subtype.ext
    apply localWord_injective counts
    funext h
    exact congrArg Subtype.val (congrFun he h)
  have hcard : (sharedAmbient counts sum s e).card ≤ ∏ h, Fintype.card (Local h) := by
    simpa only [Fintype.card_coe, Fintype.card_pi] using
      Fintype.card_le_of_injective encode hinj
  have hlocal (h : H) : (Fintype.card (Local h) : ℝ) ≤
      classBound counts s e h (entropyCap h) := by
    exact JointTypeCounts.card_allowed_over_coarse_le (shapeSide s)
      (sideWord counts s e h) (Allowed h) (entropyCap h)
      (fun w hw => hw.2) (fun w hw => hentropy h w hw.1)
  calc
    ((sharedAmbient counts sum s e).card : ℝ) ≤
        ∏ h, (Fintype.card (Local h) : ℝ) := by exact_mod_cast hcard
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun history _ => hlocal history)

omit [Fintype H] [DecidableEq H] in
theorem sharesSide_iff (t e : JointCoarseHashing.Triple (Position counts)) :
    JointCoarseHashing.SharesSide t e ↔ ∃ s : Fin 3, sameSide counts s t e := by
  constructor
  · rintro (hx | hy | hz)
    · refine ⟨0, fun h => ?_⟩
      funext i
      change t.1 ⟨h, i⟩ = e.1 ⟨h, i⟩
      exact congrFun hx.symm ⟨h, i⟩
    · refine ⟨1, fun h => ?_⟩
      funext i
      change t.2.1 ⟨h, i⟩ = e.2.1 ⟨h, i⟩
      exact congrFun hy.symm ⟨h, i⟩
    · refine ⟨2, fun h => ?_⟩
      funext i
      change t.2.2 ⟨h, i⟩ = e.2.2 ⟨h, i⟩
      exact congrFun hz.symm ⟨h, i⟩
  · rintro ⟨s, hs⟩
    fin_cases s
    · apply Or.inl
      funext p
      simpa [sideWord, shapeSide] using (congrFun (hs p.1) p.2).symm
    · apply Or.inr ∘ Or.inl
      funext p
      simpa [sideWord, shapeSide] using (congrFun (hs p.1) p.2).symm
    · apply Or.inr ∘ Or.inr
      funext p
      simpa [sideWord, shapeSide] using (congrFun (hs p.1) p.2).symm

theorem neighbors_card_le_sum (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) :
    (neighbors counts sum e).card ≤ ∑ s : Fin 3, (sharedAmbient counts sum s e).card := by
  classical
  have hsub : neighbors counts sum e ⊆
      (ambientSet counts sum).filter (fun t => ∃ s ∈ (Finset.univ : Finset (Fin 3)),
        sameSide counts s t e) := by
    intro t ht
    obtain ⟨ha, _, hs⟩ := Finset.mem_filter.mp ht
    obtain ⟨s, hs⟩ := (sharesSide_iff counts t e).mp hs
    exact Finset.mem_filter.mpr ⟨ha, s, Finset.mem_univ _, hs⟩
  apply (Finset.card_le_card hsub).trans
  convert JointLossCounts.card_filter_exists_le (ambientSet counts sum) Finset.univ
    (fun side target => sameSide counts side target e) using 1 <;>
    first | rfl | (congr; done) | (congr 2; done) | (simp only [sharedAmbient]; done)

theorem neighbors_card_le (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h) :
    ((neighbors counts sum e).card : ℝ) ≤
      ∑ s : Fin 3, ∏ h, classBound counts s e h (entropyCap h) := by
  calc
    ((neighbors counts sum e).card : ℝ) ≤
        ∑ s : Fin 3, ((sharedAmbient counts sum s e).card : ℝ) := by
      exact_mod_cast neighbors_card_le_sum counts sum e
    _ ≤ _ := Finset.sum_le_sum fun s _ => sharedAmbient_card_le counts sum s e entropyCap hentropy

theorem neighbors_card_le_three_exp (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h)
    (exponent : ℝ)
    (hupper : ∀ s : Fin 3, ∑ h, classExponent counts s e h (entropyCap h) ≤ exponent) :
    ((neighbors counts sum e).card : ℝ) ≤ 3 * Real.exp exponent := by
  have hprod (s : Fin 3) : (∏ h, classBound counts s e h (entropyCap h)) ≤
      Real.exp exponent := by
    simp_rw [classBound_eq_exp]
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.mpr (hupper s)
  calc
    ((neighbors counts sum e).card : ℝ) ≤
        ∑ s : Fin 3, ∏ h, classBound counts s e h (entropyCap h) :=
      neighbors_card_le counts sum e entropyCap hentropy
    _ ≤ ∑ _s : Fin 3, Real.exp exponent := Finset.sum_le_sum fun s _ => hprod s
    _ = _ := by simp

theorem log_neighbors_card_le (sum : H → ℕ)
    (e : JointCoarseHashing.Triple (Position counts)) (entropyCap : H → ℝ)
    (hentropy : ∀ h w, localAllowed counts sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions counts h)) ≤ entropyCap h)
    (exponent : ℝ)
    (hupper : ∀ s : Fin 3, ∑ h, classExponent counts s e h (entropyCap h) ≤ exponent)
    (hne : 0 < (neighbors counts sum e).card) :
    Real.log ((neighbors counts sum e).card : ℝ) ≤ Real.log 3 + exponent := by
  have hb := Real.log_le_log (by exact_mod_cast hne :
      (0 : ℝ) < (neighbors counts sum e).card)
    (neighbors_card_le_three_exp counts sum e entropyCap hentropy exponent hupper)
  simpa only [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] using hb

end MatrixMultiplication.JointAmbientDegree






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointAmbientRateLimit
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

namespace MatrixMultiplication.JointAmbientRateLimit

open MatrixMultiplication.Foundation JointPopulation JointAmbientDegree Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

theorem tendsto_log_succ_div_nat_of_ratio {n : ℕ → ℕ} {mass : ℝ}
    (hsize : Tendsto (fun N => (n N : ℝ) / (N : ℝ)) atTop (𝓝 mass)) :
    Tendsto (fun N => Real.log (n N + 1 : ℕ) / (N : ℝ)) atTop (𝓝 0) := by
  let C : ℝ := |mass| + 2
  have hC : 0 < C := by dsimp [C] <;> positivity
  have hmC : mass < C := by dsimp [C] <;> linarith [le_abs_self mass]
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => Real.log (C + 1) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ =>
      (Real.log (C + 1) + Real.log (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using hc.add hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N =>
      div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n N))))
        (Nat.cast_nonneg _)
  · filter_upwards [(tendsto_order.1 hsize).2 C hmC,
      eventually_ge_atTop (1 : ℕ)] with N hn hN
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
    have hsizeN := (div_lt_iff₀ hNp).mp hn
    have hbound : (n N + 1 : ℕ) ≤ (C + 1) * (N : ℝ) := by
      push_cast
      nlinarith
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (n N + 1 : ℕ)) hbound
    rw [Real.log_mul (by positivity : C + 1 ≠ 0) hNp.ne'] at hl
    exact div_le_div_of_nonneg_right hl hNp.le

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem tendsto_classExponent_div_nat
    (counts : ℕ → H → Shape → ℕ) (s : Fin 3) (h : H)
    (cap : ℕ → ℝ) (mass capRate marginalRate : ℝ)
    (hsize : Tendsto (fun N => (∑ a, counts N h a : ℕ) / (N : ℝ))
      atTop (𝓝 mass))
    (hcap : Tendsto (fun N => ((∑ a, counts N h a : ℕ) / (N : ℝ)) * cap N)
      atTop (𝓝 capRate))
    (hmarginal : Tendsto (fun N =>
      ((∑ a, counts N h a : ℕ) / (N : ℝ)) *
        finiteEntropy (fun a => (wordPopulation
          (sideWord (counts N) s (triple (counts N) (canonicalTarget (counts N))) h) a : ℝ) /
            Fintype.card (Positions (counts N) h))) atTop (𝓝 marginalRate)) :
    Tendsto (fun N =>
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N) /
        (N : ℝ)) atTop (𝓝 (capRate - marginalRate)) := by
  let A : ℝ := (Fintype.card Shape : ℝ) + (Fintype.card (Fin 17) : ℝ) + 2
  have hlog := tendsto_log_succ_div_nat_of_ratio hsize
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htotal := (hcap.sub hmarginal).add
    (((hinv.add hlog).const_mul A).add (hlog.const_mul (Fintype.card Shape : ℝ)))
  simp only [add_zero, mul_zero] at htotal
  convert htotal using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  dsimp only [classExponent, A, Positions]
  simp only [Fintype.card_fin, div_eq_mul_inv]
  ring

omit [DecidableEq H] in
theorem tendsto_sum_classExponent_div_nat
    (counts : ℕ → H → Shape → ℕ) (s : Fin 3)
    (cap : ℕ → H → ℝ) (mass capRate marginalRate : H → ℝ)
    (hsize : ∀ h, Tendsto (fun N => (∑ a, counts N h a : ℕ) / (N : ℝ))
      atTop (𝓝 (mass h)))
    (hcap : ∀ h, Tendsto (fun N => ((∑ a, counts N h a : ℕ) / (N : ℝ)) * cap N h)
      atTop (𝓝 (capRate h)))
    (hmarginal : ∀ h, Tendsto (fun N =>
      ((∑ a, counts N h a : ℕ) / (N : ℝ)) *
        finiteEntropy (fun a => (wordPopulation
          (sideWord (counts N) s (triple (counts N) (canonicalTarget (counts N))) h) a : ℝ) /
            Fintype.card (Positions (counts N) h))) atTop (𝓝 (marginalRate h))) :
    Tendsto (fun N => (∑ h,
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N h)) /
        (N : ℝ)) atTop (𝓝 (∑ h, (capRate h - marginalRate h))) := by
  have hs := tendsto_finsetSum Finset.univ (fun h _ =>
    tendsto_classExponent_div_nat counts s h (fun N => cap N h)
      (mass h) (capRate h) (marginalRate h) (hsize h) (hcap h) (hmarginal h))
  simpa only [Finset.sum_div] using hs

theorem eventually_all_target_degree_upper
    (counts : ℕ → H → Shape → ℕ) (sum : H → ℕ)
    (cap : ℕ → H → ℝ) (sideRate : Fin 3 → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hentropy : ∀ᶠ N in atTop, ∀ h w, localAllowed (counts N) sum h w →
      finiteEntropy (fun a => (wordPopulation w a : ℝ) /
        Fintype.card (Positions (counts N) h)) ≤ cap N h)
    (hrate : ∀ s, Tendsto (fun N => (∑ h,
      classExponent (counts N) s (triple (counts N) (canonicalTarget (counts N))) h (cap N h)) /
        (N : ℝ)) atTop (𝓝 (sideRate s)))
    (hside : ∀ s, sideRate s ≤ D) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, ∀ e : Target (counts N),
      Real.log ((neighbors (counts N) sum (triple (counts N) e)).card : ℝ) / (N : ℝ) ≤
        D + η := by
  have hs : ∀ᶠ N in atTop, ∀ s : Fin 3,
      (∑ h, classExponent (counts N) s
        (triple (counts N) (canonicalTarget (counts N))) h (cap N h)) / (N : ℝ) ≤
          D + η / 2 := by
    rw [Filter.eventually_all]
    intro s
    filter_upwards [(tendsto_order.1 (hrate s)).2 (sideRate s + η / 2) (by linarith)]
      with N hN
    linarith [hside s]
  have hc : Tendsto (fun N : ℕ => Real.log 3 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hentropy, hs, (tendsto_order.1 hc).2 (η / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with N he hs hc hN
  intro e
  by_cases hz : (neighbors (counts N) sum (triple (counts N) e)).card = 0
  · simp only [hz, Nat.cast_zero, Real.log_zero, zero_div]
    linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hupper (s : Fin 3) :
      (∑ h, classExponent (counts N) s (triple (counts N) e) h (cap N h)) ≤
        (N : ℝ) * (D + η / 2) := by
    simp_rw [classExponent_target_eq]
    simpa only [mul_comm] using (div_le_iff₀ hNp).mp (hs s)
  have hb := div_le_div_of_nonneg_right
    (log_neighbors_card_le (counts N) sum (triple (counts N) e) (cap N) he
      ((N : ℝ) * (D + η / 2)) hupper (Nat.pos_of_ne_zero hz)) hNp.le
  rw [add_div, mul_div_cancel_left₀ _ hNp.ne'] at hb
  linarith

end MatrixMultiplication.JointAmbientRateLimit

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode_side _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.rootShape_eq_initialShapeCode _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedExecution_copies _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialHash.selectedTargets_card
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

theorem tendsto_total_div_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => (∑ a, counts n a : ℕ) / (n : ℝ)) atTop (𝓝 mass) := by
  have h := tendsto_finsetSum Finset.univ (fun a _ => hcounts a)
  simpa only [← Finset.sum_div, ← Nat.cast_sum, ← Finset.mul_sum, hp, mul_one] using h

theorem finiteEntropy_scalar {A : Type*} [Fintype A]
    (p : A → ℝ) (mass : ℝ) (hp : ∑ a, p a = 1) :
    finiteEntropy (fun a => mass * p a) = entropyTerm mass + mass * finiteEntropy p := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, one_mul]

theorem weighted_empirical_entropy_eq {A : Type*} [Fintype A]
    (counts : A → ℕ) (scale : ℝ) :
    ((∑ a, counts a : ℕ) / scale) *
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
        finiteEntropy (fun a => (counts a : ℝ) / scale) -
          entropyTerm ((∑ a, counts a : ℕ) / scale) := by
  by_cases hzero : (∑ a, counts a) = 0
  · have hc : ∀ a, counts a = 0 := by
      intro a
      have hle : counts a ≤ ∑ b, counts b :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (counts b)) (Finset.mem_univ a)
      rw [hzero] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp [hc, finiteEntropy]
  have hD : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hzero
  have hsum : (∑ a, (counts a : ℝ) / (∑ a, counts a : ℕ)) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self hD]
  have hfac (a : A) : (counts a : ℝ) / scale =
      ((∑ a, counts a : ℕ) / scale) * ((counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    rw [div_mul_div_comm,
      mul_comm ((∑ a, counts a : ℕ) : ℝ) (counts a : ℝ), mul_div_mul_right _ _ hD]
  have h := finiteEntropy_scalar
    (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))
    ((∑ a, counts a : ℕ) / scale) hsum
  simp_rw [← hfac] at h
  linarith

theorem tendsto_weighted_empirical_entropy_of_coordinate_rates
    {A : Type*} [Fintype A] (counts : ℕ → A → ℕ)
    (mass : ℝ) (p : A → ℝ) (hp : ∑ a, p a = 1)
    (hcounts : ∀ a, Tendsto (fun n : ℕ => (counts n a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p a))) :
    Tendsto (fun n : ℕ => ((∑ a, counts n a : ℕ) / (n : ℝ)) *
      finiteEntropy (fun a => (counts n a : ℝ) / (∑ a, counts n a : ℕ)))
      atTop (𝓝 (mass * finiteEntropy p)) := by
  have htotal := tendsto_total_div_of_coordinate_rates counts mass p hp hcounts
  have h := (tendsto_finiteEntropy_of_tendsto hcounts).sub (tendsto_entropyTerm htotal)
  rw [finiteEntropy_scalar p mass hp, add_sub_cancel_left] at h
  simpa only [weighted_empirical_entropy_eq] using h

theorem sideCounts_total (counts : Shape → ℕ) (s : Fin 3) :
    (∑ a, sideCounts counts s a) = ∑ u, counts u := by
  unfold sideCounts
  rw [Finset.sum_comm]
  simp

theorem sideMass_total (p : Shape → ℝ) (s : Fin 3) :
    (∑ a, sideMass p s a) = ∑ u, p u := by
  unfold sideMass
  rw [Finset.sum_comm]
  simp

theorem tendsto_sideCounts_div_of_coordinate_rates
    (counts : ℕ → Shape → ℕ) (mass : ℝ) (p : Shape → ℝ)
    (hcounts : ∀ u, Tendsto (fun n : ℕ => (counts n u : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * p u))) (s : Fin 3) (a : Fin 17) :
    Tendsto (fun n : ℕ => (sideCounts (counts n) s a : ℝ) / (n : ℝ))
      atTop (𝓝 (mass * sideMass p s a)) := by
  have hfun (n : ℕ) : (sideCounts (counts n) s a : ℝ) / (n : ℝ) =
      ∑ u, if shapeSide s u = a then (counts n u : ℝ) / (n : ℝ) else 0 := by
    unfold sideCounts
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : shapeSide s u = a <;> simp [h]
  simp_rw [hfun]
  rw [sideMass, Finset.mul_sum]
  apply tendsto_finsetSum
  intro u _
  by_cases h : shapeSide s u = a
  · simpa only [h, ite_true, if_true] using hcounts u
  · simp only [h, ite_false, if_false, mul_zero]
    exact tendsto_const_nhds

variable {H : Type*} [Fintype H] [DecidableEq H]

omit [Fintype H] [DecidableEq H] in
theorem target_side_population (counts : H → Shape → ℕ)
    (e : Target counts) (h : H) (s : Fin 3) (a : Fin 17) :
    wordPopulation (sideWord counts s (triple counts e) h) a = sideCounts (counts h) s a := by
  let w : JointTypeCounts.FixedCoarseWords (counts h) (shapeSide s)
      (sideWord counts s (triple counts e) h) :=
    ⟨(e h).val, (e h).property, fun _ => rfl⟩
  exact ((conditionalWords_nonempty_iff
    (sideWord counts s (triple counts e) h)
    (fun b u => if shapeSide s u = b then counts h u else 0)).mp
      ⟨JointTypeCounts.fixedCoarseWordsEquiv _ _ _ w⟩) a

omit [Fintype H] [DecidableEq H] in
theorem tendsto_weighted_target_side_entropy
    (counts : ℕ → H → Shape → ℕ) (e : ∀ n, Target (counts n))
    (mass : H → ℝ) (p : H → Shape → ℝ) (hp : ∀ h, ∑ u, p h u = 1)
    (hcounts : ∀ h u, Tendsto (fun n : ℕ => (counts n h u : ℝ) / (n : ℝ))
      atTop (𝓝 (mass h * p h u))) (h : H) (s : Fin 3) :
    Tendsto (fun n : ℕ => ((∑ u, counts n h u : ℕ) / (n : ℝ)) *
      finiteEntropy (fun a =>
        (wordPopulation (sideWord (counts n) s (triple (counts n) (e n)) h) a : ℝ) /
          (∑ u, counts n h u : ℕ)))
      atTop (𝓝 (mass h * finiteEntropy (sideMass (p h) s))) := by
  have hside := tendsto_weighted_empirical_entropy_of_coordinate_rates
    (fun n => sideCounts (counts n h) s) (mass h) (sideMass (p h) s)
    ((sideMass_total (p h) s).trans (hp h))
    (tendsto_sideCounts_div_of_coordinate_rates (fun n => counts n h)
      (mass h) (p h) (hcounts h) s)
  simpa only [target_side_population, sideCounts_total] using hside

end MatrixMultiplication.JointPopulationRates






end
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

theorem total_mul_canonicalLaw_mass (counts : H → Shape → ℕ) (h : H) (a : Shape) :
    (Fintype.card (Positions counts h) : ℝ) * (canonicalLaw counts h).mass a =
      counts h a := by
  by_cases hpos : 0 < Fintype.card (Positions counts h)
  · rw [canonicalLaw_mass_of_pos counts h hpos]
    exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos))
  · have hzero : Fintype.card (Positions counts h) = 0 := Nat.eq_zero_of_not_pos hpos
    have hsum : ∑ a, counts h a = 0 := by simpa only [Positions, Fintype.card_fin] using hzero
    have ha : counts h a = 0 := by
      have hle : counts h a ≤ ∑ b, counts h b :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      rw [hsum] at hle
      exact Nat.eq_zero_of_le_zero hle
    simp only [hzero, ha, Nat.cast_zero, zero_mul]

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

theorem classScale_nonneg (counts : H → Shape → ℕ) (h : H) (N : ℕ) :
    0 ≤ classScale counts h N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem classScale_mul_canonicalLaw_mass (counts : H → Shape → ℕ) (h : H)
    (N : ℕ) (a : Shape) :
    classScale counts h N * (canonicalLaw counts h).mass a = (counts h a : ℝ) / N := by
  unfold classScale
  calc
    _ = ((Fintype.card (Positions counts h) : ℝ) * (canonicalLaw counts h).mass a) / N := by ring
    _ = _ := by rw [total_mul_canonicalLaw_mass]

theorem classScale_mul_canonicalLaw_map_mass {B : Type*} [Fintype B] [DecidableEq B]
    (counts : H → Shape → ℕ) (h : H) (N : ℕ) (f : Shape → B) (b : B) :
    classScale counts h N * ((canonicalLaw counts h).map f).mass b =
      ∑ a, if f a = b then (counts h a : ℝ) / N else 0 := by
  rw [FiniteLaw.map_mass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : f a = b
  · rw [if_pos ha, if_pos ha]
    exact classScale_mul_canonicalLaw_mass counts h N a
  · rw [if_neg ha, if_neg ha, mul_zero]

theorem classScale_mul_marginalError {B : Type*} [Fintype B] [DecidableEq B]
    (counts : H → Shape → ℕ) (h : H) (N : ℕ) (p : FiniteLaw Shape)
    (f : Shape → B) (v : B → ℝ) :
    classScale counts h N * marginalError p (canonicalLaw counts h) f v =
      ∑ b, |(∑ a, if f a = b then (counts h a : ℝ) / N else 0) -
        classScale counts h N * (p.map f).mass b| * |v b| := by
  unfold marginalError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have habs : classScale counts h N *
      |((canonicalLaw counts h).map f).mass b - (p.map f).mass b| =
      |classScale counts h N * ((canonicalLaw counts h).map f).mass b -
        classScale counts h N * (p.map f).mass b| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (classScale_nonneg counts h N)]
  rw [← mul_assoc, habs, classScale_mul_canonicalLaw_map_mass]

theorem tendsto_classScale (counts : ℕ → H → Shape → ℕ) (h : H)
    (p : FiniteLaw Shape) (mass : ℝ)
    (hcounts : ∀ a, Tendsto (fun N => (counts N h a : ℝ) / N) atTop (𝓝 (mass * p.mass a))) :
    Tendsto (fun N => classScale (counts N) h N) atTop (𝓝 mass) := by
  have hsum := tendsto_finsetSum Finset.univ (fun a _ => hcounts a)
  simpa only [classScale, Positions, Fintype.card_fin, Nat.cast_sum,
    Finset.sum_div, ← Finset.mul_sum, p.total, mul_one] using hsum

theorem tendsto_classScale_mul_marginalError {B : Type*} [Fintype B] [DecidableEq B]
    (counts : ℕ → H → Shape → ℕ) (h : H) (p : FiniteLaw Shape)
    (mass : ℝ) (f : Shape → B) (v : B → ℝ)
    (hcounts : ∀ a, Tendsto (fun N => (counts N h a : ℝ) / N) atTop (𝓝 (mass * p.mass a))) :
    Tendsto (fun N => classScale (counts N) h N *
      marginalError p (canonicalLaw (counts N) h) f v) atTop (𝓝 0) := by
  have htotal := tendsto_classScale counts h p mass hcounts
  have hside (b : B) :
      Tendsto (fun N => ∑ a, if f a = b then (counts N h a : ℝ) / N else 0)
        atTop (𝓝 (mass * (p.map f).mass b)) := by
    have hterm (a : Shape) :
        Tendsto (fun N => if f a = b then (counts N h a : ℝ) / N else 0)
          atTop (𝓝 (if f a = b then mass * p.mass a else 0)) := by
      by_cases ha : f a = b
      · simpa only [ha, ite_true, if_true] using hcounts a
      · simp only [ha, ite_false, if_false]
        exact tendsto_const_nhds
    simpa only [FiniteLaw.map_mass, Finset.mul_sum, mul_ite, mul_zero] using
      tendsto_finsetSum Finset.univ (fun a _ => hterm a)
  have hterm (b : B) :
      Tendsto (fun N => |(∑ a, if f a = b then (counts N h a : ℝ) / N else 0) -
        classScale (counts N) h N * (p.map f).mass b| * |v b|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using
      ((hside b).sub (htotal.mul_const ((p.map f).mass b))).abs.mul_const |v b|
  simpa only [classScale_mul_marginalError, Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun b _ => hterm b)

theorem tendsto_classScale_mul_gibbsCap (counts : ℕ → H → Shape → ℕ) (h : H)
    (p : FiniteLaw Shape) (mass : ℝ) (u v w : Fin 17 → ℝ)
    (hcounts : ∀ a, Tendsto (fun N => (counts N h a : ℝ) / N) atTop (𝓝 (mass * p.mass a))) :
    Tendsto (fun N => classScale (counts N) h N *
      gibbsCap (counts N) h p u v w) atTop (𝓝 (mass * finiteEntropy p.mass)) := by
  have hm := (tendsto_classScale counts h p mass hcounts).mul_const (finiteEntropy p.mass)
  have hx := tendsto_classScale_mul_marginalError counts h p mass (shapeSide 0) u hcounts
  have hy := tendsto_classScale_mul_marginalError counts h p mass (shapeSide 1) v hcounts
  have hz := tendsto_classScale_mul_marginalError counts h p mass (shapeSide 2) w hcounts
  simpa only [gibbsCap, mul_add, add_zero] using ((hm.add hx).add hy).add hz

end MatrixMultiplication.JointAmbientEntropy

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointOrdinaryPopulationSelection
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

namespace MatrixMultiplication.JointOrdinaryPopulationSelection

open MatrixMultiplication.Foundation JointPopulation JointPopulationRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {Hist : Type*} [Fintype Hist] [DecidableEq Hist]

theorem sideMass_entropy_le (p : FiniteLaw Shape) (s : Fin 3) :
    finiteEntropy (sideMass p.mass s) ≤ finiteEntropy p.mass := by
  simpa only [finiteEntropy, FiniteLaw.map_mass, sideMass] using
    p.map_entropy_le (shapeSide s)

omit [DecidableEq Hist] in
theorem sideDegreeRate_nonneg (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape)
    (hmass : ∀ h, 0 ≤ mass h) (s : Fin 3) : 0 ≤ sideDegreeRate mass p s := by
  exact Finset.sum_nonneg fun h _ =>
    mul_nonneg (hmass h) (sub_nonneg.mpr (sideMass_entropy_le (p h) s))

omit [DecidableEq Hist] in
theorem degreeRate_nonneg (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape)
    (hmass : ∀ h, 0 ≤ mass h) : 0 ≤ degreeRate mass p :=
  (sideDegreeRate_nonneg mass p hmass 0).trans (le_max_left _ _)

omit [DecidableEq Hist] in
theorem sideDegreeRate_le (mass : Hist → ℝ) (p : Hist → FiniteLaw Shape) (s : Fin 3) :
    sideDegreeRate mass p s ≤ degreeRate mass p := by
  unfold degreeRate
  fin_cases s
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem uniformDegree_attained (counts : Hist → Shape → ℕ) (sum : Hist → ℕ) :
    ∃ e : Target counts,
      (JointAmbientDegree.neighbors counts sum (triple counts e)).card =
        uniformDegree counts sum := by
  let : Nonempty (Target counts) := target_nonempty counts
  obtain ⟨e, _, he⟩ := Finset.sup_mem_of_nonempty
    (s := Finset.univ)
    (f := fun e : Target counts =>
      (JointAmbientDegree.neighbors counts sum (triple counts e)).card)
    Finset.univ_nonempty
  exact ⟨e, he⟩

theorem uniformDegree_log_upper_of_all_targets
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (B : ℝ)
    (hbound : ∀ᶠ N in atTop, ∀ e : Target (counts N),
      Real.log ((JointAmbientDegree.neighbors (counts N) sum (triple (counts N) e)).card : ℝ) /
        (N : ℝ) ≤ B) :
    ∀ᶠ N in atTop, Real.log (uniformDegree (counts N) sum : ℝ) / (N : ℝ) ≤ B := by
  filter_upwards [hbound] with N hN
  obtain ⟨e, he⟩ := uniformDegree_attained (counts N) sum
  rw [← he]
  exact hN e

omit [DecidableEq Hist] in
theorem tendsto_sum_gibbsExponent
    (counts : ℕ → Hist → Shape → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a))) (s : Fin 3) :
    Tendsto (fun N => (∑ h, JointAmbientDegree.classExponent (counts N) s
      (triple (counts N) (canonicalTarget (counts N))) h
      (JointAmbientEntropy.gibbsCap (counts N) h (p h) (u h) (v h) (w h))) / (N : ℝ))
      atTop (𝓝 (sideDegreeRate mass p s)) := by
  have hsize (h : Hist) := tendsto_total_div_of_coordinate_rates
    (fun N => counts N h) (mass h) (p h).mass (p h).total (hcounts h)
  have hcap (h : Hist) := JointAmbientEntropy.tendsto_classScale_mul_gibbsCap
    counts h (p h) (mass h) (u h) (v h) (w h) (hcounts h)
  have hside (h : Hist) := tendsto_weighted_target_side_entropy counts
    (fun N => canonicalTarget (counts N)) mass (fun h => (p h).mass)
    (fun h => (p h).total) hcounts h s
  have h := JointAmbientRateLimit.tendsto_sum_classExponent_div_nat counts s
    (fun N h => JointAmbientEntropy.gibbsCap (counts N) h (p h) (u h) (v h) (w h))
    mass (fun h => mass h * finiteEntropy (p h).mass)
    (fun h => mass h * finiteEntropy (sideMass (p h).mass s)) hsize
    (fun h => by
      simpa only [JointAmbientEntropy.classScale, Positions, Fintype.card_fin] using hcap h)
    (fun h => by
      simpa only [Positions, Fintype.card_fin] using hside h)
  simpa only [sideDegreeRate, mul_sub] using h

theorem uniformDegree_log_upper_of_word_support_oai
    (counts : ℕ → Hist → Shape → ℕ) (sum : Hist → ℕ) (mass : Hist → ℝ)
    (p : Hist → FiniteLaw Shape) (u v w : Hist → Fin 17 → ℝ) (c : Hist → ℝ)
    (hmass : ∀ h, 0 ≤ mass h)
    (hsupport : ∀ᶠ N in atTop, ∀ h word,
      JointAmbientDegree.localAllowed (counts N) sum h word →
        ∀ i, 0 < (p h).mass (word i))
    (hlog : ∀ h a, 0 < (p h).mass a → Real.log ((p h).mass a) =
      u h (shapeSide 0 a) + v h (shapeSide 1 a) + w h (shapeSide 2 a) - c h)
    (hcounts : ∀ h a, Tendsto (fun N : ℕ => (counts N h a : ℝ) / (N : ℝ))
      atTop (𝓝 (mass h * (p h).mass a)))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N in atTop, Real.log (uniformDegree (counts N) sum : ℝ) / (N : ℝ) ≤
      degreeRate mass p + η := by
  apply uniformDegree_log_upper_of_all_targets counts sum
  apply JointAmbientRateLimit.eventually_all_target_degree_upper counts sum
    (fun N h => JointAmbientEntropy.gibbsCap (counts N) h (p h) (u h) (v h) (w h))
    (sideDegreeRate mass p) (degreeRate mass p) (degreeRate_nonneg mass p hmass)
    _ (tendsto_sum_gibbsExponent counts mass p u v w hcounts)
    (sideDegreeRate_le mass p) η hη
  filter_upwards [hsupport] with N hN
  intro h word hw
  exact JointAmbientEntropy.localAllowed_entropy_le_of_word_support
    (counts N) sum h word (p h) (u h) (v h) (w h) (c h)
    (hN h word hw) (hlog h) hw

end MatrixMultiplication.JointOrdinaryPopulationSelection

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support_oai.{u_1} := @OAI.MatrixAllFields.MatrixMultiplication.JointOrdinaryPopulationSelection.uniformDegree_log_upper_of_word_support_oai.{u_1}

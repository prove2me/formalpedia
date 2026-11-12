-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.exists_window_eventually_count_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:26:19.01183+00:00
-- url     : https://prove2.me/submissions/ceb98fce-b4c2-4556-8954-6cfb5e4f2097

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRates
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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

theorem abs_log_exactWords_card_sub_entropy_le [DecidableEq A] (counts : A → ℕ) :
    |Real.log (Fintype.card (ExactWords counts) : ℝ) -
        (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ))| ≤
      ((Fintype.card A : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  simpa only [exactWords_card] using abs_log_multinomial_sub_entropy_le counts

theorem log_card_le_entropy_of_injective_exactWords [DecidableEq A]
    {O : Type*} [Fintype O] [Nonempty O] (counts : A → ℕ)
    (label : O → ExactWords counts) (hinj : Function.Injective label) :
    Real.log (Fintype.card O : ℝ) ≤
      (∑ a, counts a : ℕ) *
          finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
        ((Fintype.card A : ℝ) + 1) *
          (1 + Real.log ((∑ a, counts a) + 1 : ℕ)) := by
  have hcard := Fintype.card_le_of_injective label hinj
  have hlog : Real.log (Fintype.card O : ℝ) ≤
      Real.log (Fintype.card (ExactWords counts) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr Fintype.card_pos) (by exact_mod_cast hcard)
  have herror := (abs_le.mp (abs_log_exactWords_card_sub_entropy_le counts)).2
  linarith

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

section Incidence

variable {G C B : Type*} [Group G] [MulAction G C] [MulAction G B]
  [MulAction.IsPretransitive G C] [MulAction.IsPretransitive G B]
  [Fintype C] [Fintype B]

theorem invariant_incidence_count
    (R : C → B → Prop) [∀ c b, Decidable (R c b)]
    (hR : ∀ (g : G) (c : C) (b : B), R (g • c) (g • b) ↔ R c b)
    (c₀ : C) (b₀ : B) :
    Fintype.card C * Fintype.card {b : B // R c₀ b} =
      Fintype.card B * Fintype.card {c : C // R c b₀} := by
  classical
  have hrow (c : C) : Fintype.card {b : B // R c b} =
      Fintype.card {b : B // R c₀ b} := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G c c₀
    apply Fintype.card_congr
    exact (MulAction.toPerm (β := B) g).subtypeEquiv (fun b => by
      change R c b ↔ R c₀ (g • b)
      rw [← hg]
      exact (hR g c b).symm)
  have hcol (b : B) : Fintype.card {c : C // R c b} =
      Fintype.card {c : C // R c b₀} := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b b₀
    apply Fintype.card_congr
    exact (MulAction.toPerm (β := C) g).subtypeEquiv (fun c => by
      change R c b ↔ R (g • c) b₀
      rw [← hg]
      exact (hR g c b).symm)
  let swap : (Σ c : C, {b : B // R c b}) ≃
      (Σ b : B, {c : C // R c b}) :=
    { toFun := fun x => ⟨x.2.1, x.1, x.2.2⟩
      invFun := fun x => ⟨x.2.1, x.1, x.2.2⟩
      left_inv := fun ⟨c, b, h⟩ => rfl
      right_inv := fun ⟨b, c, h⟩ => rfl }
  simpa only [Fintype.card_sigma, hrow, hcol, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_id] using Fintype.card_congr swap

theorem invariant_incidence_degree_eq
    (R : C → B → Prop) [∀ c b, Decidable (R c b)]
    (hR : ∀ (g : G) (c : C) (b : B), R (g • c) (g • b) ↔ R c b)
    (c₀ : C) (b₀ : B) :
    (Fintype.card {c : C // R c b₀} : ℝ) =
      (Fintype.card C : ℝ) * Fintype.card {b : B // R c₀ b} /
        Fintype.card B := by
  have : Nonempty B := ⟨b₀⟩
  have hB : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card B))
  apply (eq_div_iff hB).mpr
  have h := invariant_incidence_count R hR c₀ b₀
  exact_mod_cast (by simpa only [Nat.mul_comm] using h.symm)

end Incidence

section FixedClasses

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

theorem fixedClassWords_card (counts : ∀ c, A c → ℕ)
    (hsize : ∀ c, Fintype.card (P c) = ∑ a, counts c a) :
    Fintype.card (FixedClassWords P A counts) =
      ∏ c, Nat.multinomial Finset.univ (counts c) := by
  classical
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  exact (Fintype.card_congr (fixedWordsEquiv (counts c) (hsize c))).trans
    (exactWords_card (counts c))

theorem classExactWords_card (counts : ∀ c, A c → ℕ) :
    Fintype.card (ClassExactWords A counts) =
      ∏ c, Nat.multinomial Finset.univ (counts c) := by
  classical
  simp only [ClassExactWords, Fintype.card_pi, exactWords_card]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] in
theorem fixedClassWords_transitive (counts : ∀ c, A c → ℕ)
    (w v : FixedClassWords P A counts) :
    ∃ e : ∀ c, Equiv.Perm (P c), ∀ c, (w c).val ∘ e c = (v c).val := by
  have he : ∀ c, ∃ e : Equiv.Perm (P c), (w c).val ∘ e = (v c).val := by
    intro c
    apply (samePopulation_iff_permutation (w c).val (v c).val).mp
    intro a
    rw [(w c).property a, (v c).property a]
  choose e he using he
  exact ⟨e, he⟩

theorem log_classExactWords_card (counts : ∀ c, A c → ℕ) :
    Real.log (Fintype.card (ClassExactWords A counts) : ℝ) =
      ∑ c, Real.log (Nat.multinomial Finset.univ (counts c) : ℝ) := by
  rw [classExactWords_card, Nat.cast_prod]
  exact Real.log_prod fun c _ => by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (counts c)))

theorem abs_log_classExactWords_card_sub_entropy_le (counts : ∀ c, A c → ℕ) :
    |Real.log (Fintype.card (ClassExactWords A counts) : ℝ) -
      ∑ c, (∑ a, counts c a : ℕ) *
        finiteEntropy (fun a => (counts c a : ℝ) / (∑ b, counts c b : ℕ))| ≤
      ∑ c, ((Fintype.card (A c) : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts c a) + 1 : ℕ)) := by
  rw [log_classExactWords_card, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun c _ => abs_log_multinomial_sub_entropy_le (counts c))

theorem abs_log_fixedClassWords_card_sub_entropy_le (counts : ∀ c, A c → ℕ)
    (hsize : ∀ c, Fintype.card (P c) = ∑ a, counts c a) :
    |Real.log (Fintype.card (FixedClassWords P A counts) : ℝ) -
      ∑ c, (∑ a, counts c a : ℕ) *
        finiteEntropy (fun a => (counts c a : ℝ) / (∑ b, counts c b : ℕ))| ≤
      ∑ c, ((Fintype.card (A c) : ℝ) + 1) *
        (1 + Real.log ((∑ a, counts c a) + 1 : ℕ)) := by
  rw [fixedClassWords_card P A counts hsize, ← classExactWords_card A counts]
  exact abs_log_classExactWords_card_sub_entropy_le A counts

end FixedClasses

section Windows

theorem card_entropy_bounded_words_le
    {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] (H : ℝ) :
    (Fintype.card {w : I → A //
      finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ H} : ℝ) ≤
      ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
        Real.exp ((Fintype.card I : ℝ) * H +
          ((Fintype.card A : ℝ) + 1) *
            (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
  classical
  let S := {w : I → A //
    finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card I) ≤ H}
  let T := A → Fin (Fintype.card I + 1)
  let E : ℝ := (Fintype.card I : ℝ) * H +
    ((Fintype.card A : ℝ) + 1) *
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
      let encode₀ : Fiber → {v : I → A // ∀ a, wordPopulation v a = counts a} :=
        fun v => ⟨v.val.val, fun a => by
          change wordPopulation v.val.val a = wordPopulation w.val.val a
          exact congrArg Fin.val
            (congrFun (v.property.trans w.property.symm) a)⟩
      have hinj₀ : Function.Injective encode₀ := by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun z : {v : I → A // ∀ a, wordPopulation v a = counts a} => z.val) h
      have hsize : Fintype.card I = ∑ a, counts a :=
        (wordPopulation_sum w.val.val).symm
      let encode : Fiber → ExactWords counts :=
        fun v => fixedWordsEquiv (I := I) counts hsize (encode₀ v)
      have hinj : Function.Injective encode :=
        (fixedWordsEquiv (I := I) counts hsize).injective.comp hinj₀
      have hlog := log_card_le_entropy_of_injective_exactWords counts encode hinj
      have htotal : (∑ a, counts a) = Fintype.card I := hsize.symm
      rw [htotal] at hlog
      have hw : finiteEntropy (fun a => (counts a : ℝ) / Fintype.card I) ≤ H :=
        w.val.property
      have hmain : (Fintype.card I : ℝ) *
          finiteEntropy (fun a => (counts a : ℝ) / Fintype.card I) ≤
          (Fintype.card I : ℝ) * H :=
        mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
      have hlog' : Real.log (Fintype.card Fiber : ℝ) ≤ E := by
        dsimp only [E]
        exact hlog.trans (add_le_add hmain le_rfl)
      have hpos : (0 : ℝ) < Fintype.card Fiber :=
        Nat.cast_pos.mpr Fintype.card_pos
      simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog'
    · let : IsEmpty Fiber := ⟨fun x => hn ⟨x⟩⟩
      change (Fintype.card Fiber : ℝ) ≤ Real.exp E
      simpa only [Fintype.card_of_isEmpty, Nat.cast_zero] using (Real.exp_pos E).le
  have hdecomp : Fintype.card S =
      ∑ p : T, Fintype.card {w : S // profile w = p} := by
    simpa only [Fintype.card_sigma] using
      (Fintype.card_congr (Equiv.sigmaFiberEquiv profile)).symm
  calc
    (Fintype.card S : ℝ) =
        ∑ p : T, (Fintype.card {w : S // profile w = p} : ℝ) := by
      exact_mod_cast hdecomp
    _ ≤ ∑ _p : T, Real.exp E := Finset.sum_le_sum (fun p _ => hcap p)
    _ = (Fintype.card T : ℝ) * Real.exp E := by simp
    _ = ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
        Real.exp ((Fintype.card I : ℝ) * H +
          ((Fintype.card A : ℝ) + 1) *
            (1 + Real.log (Fintype.card I + 1 : ℕ))) := by
      simp [T, E]

theorem card_class_entropy_bounded_words_le
    {C : Type*} [Fintype C] [DecidableEq C] (P A : C → Type*)
    [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] (H : C → ℝ) :
    (Fintype.card (∀ c, {w : P c → A c //
      finiteEntropy (fun a => (wordPopulation w a : ℝ) / Fintype.card (P c)) ≤ H c}) : ℝ) ≤
      ∏ c, ((Fintype.card (P c) : ℝ) + 1) ^ Fintype.card (A c) *
        Real.exp ((Fintype.card (P c) : ℝ) * H c +
          ((Fintype.card (A c) : ℝ) + 1) *
            (1 + Real.log (Fintype.card (P c) + 1 : ℕ))) := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod]
  exact Finset.prod_le_prod (fun c _ => Nat.cast_nonneg _)
    (fun c _ => card_entropy_bounded_words_le (I := P c) (A := A c) (H c))

theorem residual_window_error {mass actual target total targetTotal designated
    targetDesignated η χ : ℝ}
    (hmass : 0 < mass)
    (hactual : mass * actual = total - designated)
    (htarget : mass * target = targetTotal - targetDesignated)
    (htotal : |total - targetTotal| ≤ η)
    (hdesignated : |designated - targetDesignated| ≤ χ) :
    |actual - target| ≤ (η + χ) / mass := by
  apply (le_div_iff₀ hmass).mpr
  calc
    |actual - target| * mass = |mass * (actual - target)| := by
      rw [abs_mul, abs_of_pos hmass, mul_comm]
    _ = |(total - targetTotal) - (designated - targetDesignated)| := by
      rw [mul_sub, hactual, htarget]
      congr 1
      ring
    _ ≤ |total - targetTotal| + |designated - targetDesignated| := abs_sub _ _
    _ ≤ η + χ := add_le_add htotal hdesignated

theorem exists_entropy_window {A : Type*} [Fintype A]
    (p : A → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : A → ℝ,
      (∀ a, |q a - p a| ≤ δ) → |finiteEntropy q - finiteEntropy p| < ε := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    (continuous_finiteEntropy.continuousAt : ContinuousAt finiteEntropy p) ε hε
  refine ⟨δ / 2, half_pos hδ, fun q hq => ?_⟩
  apply hcont
  rw [dist_pi_lt_iff hδ]
  intro a
  rw [Real.dist_eq]
  exact (hq a).trans_lt (half_lt_self hδ)

end Windows

end MatrixMultiplication.JointTypeCounts

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityIncidence
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityIncidence

open MatrixMultiplication.Foundation JointTypeCounts
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Actions

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

attribute [local instance] fixedWordsMulAction

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] in
theorem fixedWordsPretransitive (counts : ∀ c, A c → ℕ) :
    MulAction.IsPretransitive (ClassPerm Pos) (FixedClassWords Pos A counts) := by
  constructor
  intro w v
  obtain ⟨e, he⟩ := fixedClassWords_transitive Pos A counts w v
  refine ⟨fun c => (e c)⁻¹, ?_⟩
  funext c
  apply Subtype.ext
  change (w c).val ∘ (((e c)⁻¹)⁻¹ : Equiv.Perm (Pos c)) = (v c).val
  simpa only [inv_inv] using he c

attribute [local instance] fixedWordsPretransitive

end Actions

attribute [local instance] fixedWordsMulAction fixedWordsPretransitive

section Counts

variable {P U Z A : Type*} [Fintype P] [DecidableEq U] [DecidableEq A]

theorem jointCount_reindex (w : P → U) (z : P → Z) (part : Z → A)
    (e : Equiv.Perm P) (u : U) (a : A) :
    jointCount (w ∘ e) (z ∘ e) part u a = jointCount w z part u a := by
  exact Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

variable [DecidableEq P] [Fintype U] [Fintype A]

omit [DecidableEq P] [Fintype A] in
theorem jointCount_sum_shapes (w : P → U) (z : P → Z) (part : Z → A) (a : A) :
    (∑ u, jointCount w z part u a) = wordPopulation (part ∘ z) a := by
  calc
    (∑ u, jointCount w z part u a) =
        ∑ u, wordPopulation (fun i : {i : P // part (z i) = a} => w i.val) u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [wordPopulation_fiber]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun _ => and_comm)
    _ = wordPopulation (part ∘ z) a := wordPopulation_sum _

omit [DecidableEq P] [Fintype A] in
theorem projected_restrict_population (w : P → U) (z : P → Z) (part : Z → A)
    (d : U → Prop) (a : A) :
    wordPopulation (fun i : {i : P // d (w i)} => part (z i.val)) a =
      ∑ u : {u : U // d u}, jointCount w z part u.val a := by
  let e : {i : {i : P // d (w i)} // part (z i.val) = a} ≃
      Σ u : {u : U // d u}, {i : P // w i = u.val ∧ part (z i) = a} :=
    { toFun := fun i => ⟨⟨w i.val.val, i.val.property⟩,
        ⟨i.val.val, rfl, i.property⟩⟩
      invFun := fun i => ⟨⟨i.2.val, by
        rw [i.2.property.1]
        exact i.1.property⟩, i.2.property.2⟩
      left_inv := by intro i; rfl
      right_inv := by
        rintro ⟨⟨u, hu⟩, i, hi, ha⟩
        cases hi
        rfl }
  simpa only [wordPopulation, Fintype.card_sigma, jointCount] using Fintype.card_congr e

omit [DecidableEq P] [Fintype A] in
theorem residual_population_add_designated (w : P → U) (z : P → Z)
    (part : Z → A) (d : U → Prop) (a : A) :
    wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a +
      ∑ u : {u : U // d u}, jointCount w z part u.val a =
        wordPopulation (part ∘ z) a := by
  have hres :
      wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a =
        ∑ u : {u : U // ¬d u}, jointCount w z part u.val a := by
    convert projected_restrict_population w z part (fun u => ¬d u) a using 1 <;> first | (with_reducible_and_instances rfl) | (congr 1)
    · exact Subsingleton.elim _ _
    · ext u
      simp
  rw [hres, add_comm]
  exact (Fintype.sum_subtype_add_sum_subtype d
    (fun u => jointCount w z part u a)).trans (jointCount_sum_shapes w z part a)

omit [DecidableEq P] [Fintype A] in
theorem projected_population_fixed [Fintype Z] [DecidableEq Z]
    (z : P → Z) (counts : Z → ℕ) (hz : ∀ s, wordPopulation z s = counts s)
    (part : Z → A) (a : A) :
    wordPopulation (part ∘ z) a = ∑ s : {s : Z // part s = a}, counts s.val := by
  have h := (Fintype.card_congr
    (Equiv.sigmaSubtypeFiberEquivSubtype z
      (p := fun i => part (z i) = a) (q := fun s => part s = a)
      (fun _ => Iff.rfl))).symm
  simp only [Fintype.card_sigma] at h
  change wordPopulation (part ∘ z) a =
    ∑ s : {s : Z // part s = a}, wordPopulation z s.val at h
  simpa only [hz] using h

omit [DecidableEq P] [Fintype A] in
theorem residual_projected_window (w : P → U) (z : P → Z) (part : Z → A)
    (d : U → Prop) (counts : U → ℕ) (law : U → A → ℝ)
    (residualLaw totalTarget : A → ℝ) (χ η : ℝ) (a : A)
    (hmass : 0 < Fintype.card {i : P // ¬d (w i)})
    (htotal : |(wordPopulation (part ∘ z) a : ℝ) - totalTarget a| ≤ η)
    (hdesignated : ∀ u, d u →
      |(jointCount w z part u a : ℝ) - (counts u : ℝ) * law u a| ≤
        (counts u : ℝ) * χ)
    (hbalance : (Fintype.card {i : P // ¬d (w i)} : ℝ) * residualLaw a =
      totalTarget a - ∑ u : {u : U // d u}, (counts u.val : ℝ) * law u.val a) :
    |(wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a : ℝ) /
        Fintype.card {i : P // ¬d (w i)} - residualLaw a| ≤
      (η + (∑ u : {u : U // d u}, (counts u.val : ℝ)) * χ) /
        Fintype.card {i : P // ¬d (w i)} := by
  have hm : (0 : ℝ) < Fintype.card {i : P // ¬d (w i)} := Nat.cast_pos.mpr hmass
  have hsplit :
      (wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a : ℝ) =
        wordPopulation (part ∘ z) a -
          ∑ u : {u : U // d u}, (jointCount w z part u.val a : ℝ) := by
    have h := residual_population_add_designated w z part d a
    have h' :
        (wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a : ℝ) +
          ∑ u : {u : U // d u}, (jointCount w z part u.val a : ℝ) =
            wordPopulation (part ∘ z) a := by exact_mod_cast h
    exact eq_sub_of_add_eq h'
  have hd : |(∑ u : {u : U // d u}, (jointCount w z part u.val a : ℝ)) -
      ∑ u : {u : U // d u}, (counts u.val : ℝ) * law u.val a| ≤
        (∑ u : {u : U // d u}, (counts u.val : ℝ)) * χ := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun u _ => hdesignated u.val u.property)
  exact residual_window_error hm (by rwa [mul_div_cancel₀ _ hm.ne'])
    hbalance htotal hd

end Counts

section Groups

variable {P U Z A : Type*} [Fintype P] [DecidableEq P]
  [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A]

omit [Fintype U] [DecidableEq U] in
theorem designatedGroup_eq_some (d : U → Prop) (u v : U) :
    designatedGroup d v = some u ↔ d u ∧ v = u := by
  constructor
  · intro h
    by_cases hv : d v
    · have he : v = u := Option.some.inj (by simpa [designatedGroup, hv] using h)
      exact ⟨he ▸ hv, he⟩
    · simp [designatedGroup, hv] at h
  · rintro ⟨hu, rfl⟩
    simp [designatedGroup, hu]

omit [Fintype U] [DecidableEq U] in
theorem designatedGroup_eq_none (d : U → Prop) (v : U) :
    designatedGroup d v = none ↔ ¬d v := by
  simp [designatedGroup]

omit [DecidableEq P] [Fintype U] in
theorem groupPos_card_some (w : P → U) (d : U → Prop) (u : U) (hu : d u) :
    Fintype.card (GroupPos w d (some u)) = wordPopulation w u := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => by simp [designatedGroup_eq_some, hu]

omit [DecidableEq P] [Fintype U] [DecidableEq U] in
theorem groupPos_card_none (w : P → U) (d : U → Prop) :
    Fintype.card (GroupPos w d none) = Fintype.card {i : P // ¬d (w i)} := by
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight fun i => designatedGroup_eq_none d (w i)

omit [DecidableEq P] [Fintype A] [Fintype U] in
theorem groupProjection_population_some (w : P → U) (d : U → Prop)
    (u : U) (hu : d u) (z : P → Z) (part : Z → A) (a : A) :
    wordPopulation (groupProjection w d (some u) z part) a =
      jointCount w z part u a := by
  apply Fintype.card_congr
  refine (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun i : P => designatedGroup d (w i) = some u)
    (fun i : P => part (z i) = a)).trans ?_
  exact Equiv.subtypeEquivRight fun i => by simp [designatedGroup_eq_some, hu]

omit [DecidableEq P] [Fintype A] [Fintype U] [DecidableEq U] in
theorem groupProjection_population_none (w : P → U) (d : U → Prop)
    (z : P → Z) (part : Z → A) (a : A) :
    wordPopulation (groupProjection w d none z part) a =
      wordPopulation (fun i : {i : P // ¬d (w i)} => part (z i.val)) a := by
  apply Fintype.card_congr
  exact (Equiv.subtypeEquiv
    (Equiv.subtypeEquivRight fun i => designatedGroup_eq_none d (w i)) fun _ => Iff.rfl)

theorem normalized_count_window {x n p χ : ℝ} (hn : 0 < n)
    (h : |x - n * p| ≤ n * χ) : |x / n - p| ≤ χ := by
  apply (mul_le_mul_iff_left₀ hn).mp
  calc
    |x / n - p| * n = |(x / n - p) * n| := by rw [abs_mul, abs_of_pos hn]
    _ = |x - n * p| := by rw [sub_mul, div_mul_cancel₀ _ hn.ne', mul_comm p n]
    _ ≤ n * χ := h
    _ = χ * n := mul_comm _ _

omit [DecidableEq P] in
theorem group_entropy_of_designated_windows
    (w : P → U) (z : P → Z) (part : Z → A) (d : U → Prop)
    (counts : U → ℕ) (hcounts : ∀ u, wordPopulation w u = counts u)
    (law : U → A → ℝ) (residualLaw totalTarget : A → ℝ)
    (χ η : ℝ) (H : Option U → ℝ) (hH : ∀ k, 0 ≤ H k)
    (htotal : ∀ a, |(wordPopulation (part ∘ z) a : ℝ) - totalTarget a| ≤ η)
    (hdesignated : ∀ u, d u → ∀ a,
      |(jointCount w z part u a : ℝ) - (counts u : ℝ) * law u a| ≤
        (counts u : ℝ) * χ)
    (hbalance : ∀ a, (Fintype.card {i : P // ¬d (w i)} : ℝ) * residualLaw a =
      totalTarget a - ∑ u : {u : U // d u}, (counts u.val : ℝ) * law u.val a)
    (hcapDesignated : ∀ u, d u → ∀ q : A → ℝ,
      (∀ a, |q a - law u a| ≤ χ) → finiteEntropy q ≤ H (some u))
    (hcapResidual : ∀ q : A → ℝ,
      (∀ a, |q a - residualLaw a| ≤
        (η + (∑ u : {u : U // d u}, (counts u.val : ℝ)) * χ) /
          Fintype.card {i : P // ¬d (w i)}) → finiteEntropy q ≤ H none)
    (k : Option U) :
    finiteEntropy (fun a => (wordPopulation (groupProjection w d k z part) a : ℝ) /
      Fintype.card (GroupPos w d k)) ≤ H k := by
  by_cases hzero : Fintype.card (GroupPos w d k) = 0
  · simpa only [hzero, Nat.cast_zero, div_zero, finiteEntropy, entropyTerm_zero,
      Finset.sum_const_zero] using hH k
  have hpos : 0 < Fintype.card (GroupPos w d k) := Nat.pos_of_ne_zero hzero
  cases k with
  | some u =>
      obtain ⟨i⟩ := Fintype.card_pos_iff.mp hpos
      have hu : d u := ((designatedGroup_eq_some d u (w i.val)).mp i.property).1
      have hm : 0 < counts u := by
        simpa only [groupPos_card_some w d u hu, hcounts u] using hpos
      apply hcapDesignated u hu
      intro a
      simp only [groupProjection_population_some w d u hu,
        groupPos_card_some w d u hu, hcounts u]
      exact normalized_count_window (Nat.cast_pos.mpr hm) (hdesignated u hu a)
  | none =>
      apply hcapResidual
      intro a
      simp only [groupProjection_population_none, groupPos_card_none]
      exact residual_projected_window w z part d counts law residualLaw totalTarget χ η a
        (by simpa only [groupPos_card_none] using hpos) (htotal a)
        (fun u hu => hdesignated u hu a) (hbalance a)

end Groups

section SideControls

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (part : ∀ c, Pair c → A c) (designated : ∀ c, Shape c → Prop)
  (law : ∀ c, Shape c → A c → ℝ) (χ : ℝ)
  (H : (Σ c, Option (Shape c)) → ℝ) (w : FixedClassWords Pos Shape shapeCounts)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem SideEntropyControl.group_entropy
    (control : SideEntropyControl Pos Shape Pair A shapeCounts pairCounts
      part designated law χ H w)
    (z : FixedClassWords Pos Pair pairCounts)
    (hdesignated : ∀ c u, designated c u → ∀ a,
      |(jointCount (w c).val (z c).val (part c) u a : ℝ) -
        (shapeCounts c u : ℝ) * law c u a| ≤ (shapeCounts c u : ℝ) * χ)
    (g : Σ c, Option (Shape c)) :
    finiteEntropy (fun a =>
      (wordPopulation (groupProjection (w g.1).val (designated g.1) g.2
        (z g.1).val (part g.1)) a : ℝ) /
          Fintype.card (GroupPos (w g.1).val (designated g.1) g.2)) ≤ H g := by
  apply group_entropy_of_designated_windows (w g.1).val (z g.1).val (part g.1)
    (designated g.1) (shapeCounts g.1) (w g.1).property (law g.1)
    (control.residualLaw g.1) (control.totalTarget g.1) χ (control.totalError g.1)
    (fun k => H ⟨g.1, k⟩) (fun k => control.nonneg ⟨g.1, k⟩)
  · intro a
    rw [projected_population_fixed (z g.1).val (pairCounts g.1) (z g.1).property]
    exact control.aggregate_window g.1 a
  · exact hdesignated g.1
  · exact control.mixture_balance g.1
  · exact control.designated_entropy g.1
  · exact control.residual_entropy g.1

end SideControls

section Compatibility

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair Left Right : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
  (designatedLeft designatedRight : ∀ c, Shape c → Prop)
  (leftLaw : ∀ c, Shape c → Left c → ℝ)
  (rightLaw : ∀ c, Shape c → Right c → ℝ) (χ : ℝ)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, Fintype (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] in
theorem designatedCompatibility_permute (g : ClassPerm Pos)
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) :
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ
      (permuteFixedWords Pos Shape shapeCounts g w)
      (permuteFixedWords Pos Pair pairCounts g z) ↔
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z := by
  simp only [DesignatedCompatibility, permuteFixedWords, jointCount_reindex]

omit [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] in
theorem compatibleCandidateCount_eq
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts) :
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) =
      (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) *
        compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
          leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w /
        Fintype.card (FixedClassWords Pos Pair pairCounts) := by
  exact invariant_incidence_degree_eq (G := ClassPerm Pos)
    (DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ)
    (designatedCompatibility_permute Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ) w z

theorem compatibleStatisticCount_le_grouped_entropy
    (w : FixedClassWords Pos Shape shapeCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (hL : ∀ z : FixedClassWords Pos Pair pairCounts,
      DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z →
      ∀ g : Σ c, Option (Shape c),
        finiteEntropy (fun a =>
          (wordPopulation (groupProjection (w g.1).val (designatedLeft g.1) g.2
            (z g.1).val (leftPart g.1)) a : ℝ) /
              Fintype.card (GroupPos (w g.1).val (designatedLeft g.1) g.2)) ≤ HL g)
    (hR : ∀ z : FixedClassWords Pos Pair pairCounts,
      DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
        leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z →
      ∀ g : Σ c, Option (Shape c),
        finiteEntropy (fun a =>
          (wordPopulation (groupProjection (w g.1).val (designatedRight g.1) g.2
            (z g.1).val (rightPart g.1)) a : ℝ) /
              Fintype.card (GroupPos (w g.1).val (designatedRight g.1) g.2)) ≤ HR g) :
    (compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w : ℝ) ≤
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedLeft g.1) g.2) (Left g.1) (HL g)) *
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedRight g.1) g.2) (Right g.1) (HR g)) := by
  let J := Σ c, Option (Shape c)
  let PL : J → Type _ := fun g => GroupPos (w g.1).val (designatedLeft g.1) g.2
  let PR : J → Type _ := fun g => GroupPos (w g.1).val (designatedRight g.1) g.2
  let EL := ∀ g : J, {v : PL g → Left g.1 //
    finiteEntropy (fun a => (wordPopulation v a : ℝ) / Fintype.card (PL g)) ≤ HL g}
  let ER := ∀ g : J, {v : PR g → Right g.1 //
    finiteEntropy (fun a => (wordPopulation v a : ℝ) / Fintype.card (PR g)) ≤ HR g}
  let Row := {z : FixedClassWords Pos Pair pairCounts //
    DesignatedCompatibility Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z}
  let encode : Row → EL × ER := fun z =>
    (fun g => ⟨groupProjection (w g.1).val (designatedLeft g.1) g.2
      (z.val g.1).val (leftPart g.1), hL z.val z.property g⟩,
     fun g => ⟨groupProjection (w g.1).val (designatedRight g.1) g.2
      (z.val g.1).val (rightPart g.1), hR z.val z.property g⟩)
  have hinj : Function.Injective encode := by
    intro x y h
    apply Subtype.ext
    funext c
    apply Subtype.ext
    funext i
    apply hpair c
    apply Prod.ext
    · exact congrArg (fun v : EL × ER =>
        ((v.1 ⟨c, designatedGroup (designatedLeft c) ((w c).val i)⟩).val ⟨i, rfl⟩)) h
    · exact congrArg (fun v : EL × ER =>
        ((v.2 ⟨c, designatedGroup (designatedRight c) ((w c).val i)⟩).val ⟨i, rfl⟩)) h
  have hleft : (Fintype.card EL : ℝ) ≤
      ∏ g : J, wordEntropyBound (PL g) (Left g.1) (HL g) :=
    card_class_entropy_bounded_words_le PL (fun g => Left g.1) HL
  have hright : (Fintype.card ER : ℝ) ≤
      ∏ g : J, wordEntropyBound (PR g) (Right g.1) (HR g) :=
    card_class_entropy_bounded_words_le PR (fun g => Right g.1) HR
  have hcard : (Fintype.card Row : ℝ) ≤ (Fintype.card EL : ℝ) * Fintype.card ER := by
    simpa only [Fintype.card_prod, Nat.cast_mul] using
      (Nat.cast_le.mpr (Fintype.card_le_of_injective encode hinj) :
        (Fintype.card Row : ℝ) ≤ Fintype.card (EL × ER))
  exact hcard.trans (mul_le_mul hleft hright (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans hleft))

theorem compatibleStatisticCount_le_of_controls
    (w : FixedClassWords Pos Shape shapeCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w) :
    (compatibleStatisticCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w : ℝ) ≤
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedLeft g.1) g.2) (Left g.1) (HL g)) *
      (∏ g : Σ c, Option (Shape c), wordEntropyBound
        (GroupPos (w g.1).val (designatedRight g.1) g.2) (Right g.1) (HR g)) := by
  apply compatibleStatisticCount_le_grouped_entropy Pos Shape Pair Left Right
    shapeCounts pairCounts leftPart rightPart designatedLeft designatedRight
    leftLaw rightLaw χ w hpair HL HR
  · intro z hz g
    exact SideEntropyControl.group_entropy Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w controlLeft z hz.1 g
  · intro z hz g
    exact SideEntropyControl.group_entropy Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w controlRight z hz.2 g

theorem compatibleCandidateCount_le_of_controls
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w) :
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
      (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) *
        ((∏ g : Σ c, Option (Shape c), wordEntropyBound
          (GroupPos (w g.1).val (designatedLeft g.1) g.2) (Left g.1) (HL g)) *
        (∏ g : Σ c, Option (Shape c), wordEntropyBound
          (GroupPos (w g.1).val (designatedRight g.1) g.2) (Right g.1) (HR g))) /
        Fintype.card (FixedClassWords Pos Pair pairCounts) := by
  rw [compatibleCandidateCount_eq Pos Shape Pair Left Right shapeCounts pairCounts
    leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w z]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (compatibleStatisticCount_le_of_controls Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ w hpair HL HR
      controlLeft controlRight) (Nat.cast_nonneg _)

end Compatibility

end MatrixMultiplication.JointCompatibilityIncidence

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointAmbientRateLimit
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

end MatrixMultiplication.JointAmbientRateLimit

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityEntropyBound
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitCount.groupOrbitFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons _root_.OAI.MatrixAllFields.MatrixMultiplication.JointAmbientEntropy.empiricalFiniteLaw_mass _root_.OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.candidateEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open MatrixMultiplication.Foundation
open MatrixMultiplication.JointTypeCounts MatrixMultiplication.JointCompatibilityIncidence
open scoped BigOperators

namespace MatrixMultiplication.JointCompatibilityEntropyBound

attribute [local instance] Classical.propDecidable

section ClassCounts

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem fixedClassWords_size (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) (c : C) :
    Fintype.card (Pos c) = ∑ a, counts c a := by
  calc
    Fintype.card (Pos c) = ∑ a, wordPopulation (w c).val a :=
      (wordPopulation_sum (w c).val).symm
    _ = ∑ a, counts c a := Finset.sum_congr rfl fun a _ => (w c).property a

theorem abs_log_card_sub_classEntropy_le (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) :
    |Real.log (Fintype.card (FixedClassWords Pos A counts) : ℝ) -
      classEntropy Pos A counts| ≤ classTypeError Pos A := by
  have hsize := fixedClassWords_size Pos A counts w
  simpa only [classEntropy, classTypeError, ← hsize] using
    abs_log_fixedClassWords_card_sub_entropy_le Pos A counts hsize

theorem fixedClassWords_card_le_exp (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) :
    (Fintype.card (FixedClassWords Pos A counts) : ℝ) ≤
      Real.exp (classEntropy Pos A counts + classTypeError Pos A) := by
  have hpos : 0 < (Fintype.card (FixedClassWords Pos A counts) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨w⟩)
  have h := (abs_le.mp (abs_log_card_sub_classEntropy_le Pos A counts w)).2
  calc
    (Fintype.card (FixedClassWords Pos A counts) : ℝ) =
      Real.exp (Real.log (Fintype.card (FixedClassWords Pos A counts) : ℝ)) :=
        (Real.exp_log hpos).symm
    _ ≤ Real.exp (classEntropy Pos A counts + classTypeError Pos A) :=
      Real.exp_le_exp.mpr (by linarith)

theorem exp_le_fixedClassWords_card (counts : ∀ c, A c → ℕ)
    (w : FixedClassWords Pos A counts) :
    Real.exp (classEntropy Pos A counts - classTypeError Pos A) ≤
      (Fintype.card (FixedClassWords Pos A counts) : ℝ) := by
  have hpos : 0 < (Fintype.card (FixedClassWords Pos A counts) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨w⟩)
  have h := (abs_le.mp (abs_log_card_sub_classEntropy_le Pos A counts w)).1
  calc
    Real.exp (classEntropy Pos A counts - classTypeError Pos A) ≤
      Real.exp (Real.log (Fintype.card (FixedClassWords Pos A counts) : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = (Fintype.card (FixedClassWords Pos A counts) : ℝ) := Real.exp_log hpos

end ClassCounts

section GroupCounts

theorem wordEntropyBound_eq_exp (I A : Type*) [Fintype I] [Fintype A] (H : ℝ) :
    wordEntropyBound I A H =
      Real.exp ((Fintype.card I : ℝ) * H + wordTypeError I A) := by
  unfold wordEntropyBound wordTypeError
  rw [show (Fintype.card I : ℝ) * H +
      (((Fintype.card A : ℝ) + 1) * (1 + Real.log (Fintype.card I + 1 : ℕ)) +
        (Fintype.card A : ℝ) * Real.log (Fintype.card I + 1 : ℕ)) =
      (Fintype.card A : ℝ) * Real.log (Fintype.card I + 1 : ℕ) +
        ((Fintype.card I : ℝ) * H + ((Fintype.card A : ℝ) + 1) *
          (1 + Real.log (Fintype.card I + 1 : ℕ))) by ring]
  conv_rhs => rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  simp only [Nat.cast_add, Nat.cast_one]

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable (counts : ∀ c, Shape c → ℕ)
  (designated : ∀ c, Shape c → Prop)
  (H : (Σ c, Option (Shape c)) → ℝ)
  (w : FixedClassWords Pos Shape counts)

omit [DecidableEq C] [∀ c, DecidableEq (Pos c)] [∀ c, DecidableEq (A c)] in
theorem prod_wordEntropyBound_eq_exp :
    (∏ g : Σ c, Option (Shape c), wordEntropyBound
      (GroupPos (w g.1).val (designated g.1) g.2) (A g.1) (H g)) =
      Real.exp (groupedEntropy Pos Shape counts designated H w +
        groupedTypeError Pos Shape A counts designated w) := by
  simp only [wordEntropyBound_eq_exp, groupedEntropy, groupedTypeError,
    ← Real.exp_sum, Finset.sum_add_distrib]

end GroupCounts

section Compatibility

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair Left Right : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
  (designatedLeft designatedRight : ∀ c, Shape c → Prop)
  (leftLaw : ∀ c, Shape c → Left c → ℝ)
  (rightLaw : ∀ c, Shape c → Right c → ℝ) (χ : ℝ)

theorem compatibleCandidateCount_le_exp
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w) :
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
      Real.exp (compatibilityExponent Pos Shape Pair Left Right shapeCounts pairCounts
        designatedLeft designatedRight HL HR w) := by
  have h := compatibleCandidateCount_le_of_controls Pos Shape Pair Left Right
    shapeCounts pairCounts leftPart rightPart designatedLeft designatedRight
    leftLaw rightLaw χ w z hpair HL HR controlLeft controlRight
  rw [prod_wordEntropyBound_eq_exp, prod_wordEntropyBound_eq_exp] at h
  let E := groupedEntropy Pos Shape shapeCounts designatedLeft HL w +
    groupedTypeError Pos Shape Left shapeCounts designatedLeft w +
    (groupedEntropy Pos Shape shapeCounts designatedRight HR w +
      groupedTypeError Pos Shape Right shapeCounts designatedRight w)
  rw [← Real.exp_add] at h
  have hnum : (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) * Real.exp E ≤
      Real.exp (classEntropy Pos Shape shapeCounts + classTypeError Pos Shape + E) := by
    conv_rhs => rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right
      (fixedClassWords_card_le_exp Pos Shape shapeCounts w) (Real.exp_pos E).le
  calc
    (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
        (Fintype.card (FixedClassWords Pos Shape shapeCounts) : ℝ) * Real.exp E /
          Fintype.card (FixedClassWords Pos Pair pairCounts) := h
    _ ≤ Real.exp (classEntropy Pos Shape shapeCounts + classTypeError Pos Shape + E) /
        Real.exp (classEntropy Pos Pair pairCounts - classTypeError Pos Pair) :=
      div_le_div₀ (Real.exp_pos _).le hnum (Real.exp_pos _)
        (exp_le_fixedClassWords_card Pos Pair pairCounts z)
    _ = Real.exp (compatibilityExponent Pos Shape Pair Left Right shapeCounts pairCounts
        designatedLeft designatedRight HL HR w) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [E, compatibilityExponent]
      ring

theorem log_compatibleCandidateCount_le
    (w : FixedClassWords Pos Shape shapeCounts)
    (z : FixedClassWords Pos Pair pairCounts)
    (hpair : ∀ c, Function.Injective (fun s : Pair c => (leftPart c s, rightPart c s)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (controlLeft : SideEntropyControl Pos Shape Pair Left shapeCounts pairCounts
      leftPart designatedLeft leftLaw χ HL w)
    (controlRight : SideEntropyControl Pos Shape Pair Right shapeCounts pairCounts
      rightPart designatedRight rightLaw χ HR w)
    (hpos : 0 < compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z) :
    Real.log (compatibleCandidateCount Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
      compatibilityExponent Pos Shape Pair Left Right shapeCounts pairCounts
        designatedLeft designatedRight HL HR w := by
  have h := Real.log_le_log (Nat.cast_pos.mpr hpos)
    (compatibleCandidateCount_le_exp Pos Shape Pair Left Right shapeCounts pairCounts
      leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ
      w z hpair HL HR controlLeft controlRight)
  simpa only [Real.log_exp] using h

end Compatibility

end MatrixMultiplication.JointCompatibilityEntropyBound

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityScaling
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

namespace MatrixMultiplication.JointCompatibilityScaling

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {Shape : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]

section Repeated

variable (Pos : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]

omit [DecidableEq C] [∀ c, DecidableEq (Shape c)] [∀ c, DecidableEq (Pos c)] in
theorem classEntropy_repeated (base : ∀ c, Shape c → ℕ) (t : ℕ) (ht : 0 < t)
    (hsize : ∀ c, Fintype.card (Pos c) = t * baseSize base c) :
    classEntropy Pos Shape (fun c a => t * base c a) = (t : ℝ) * baseEntropy base := by
  simp only [classEntropy, baseEntropy, hsize, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [show (fun a => (t : ℝ) * base c a / ((t : ℝ) * baseSize base c)) =
      (fun a => (base c a : ℝ) / baseSize base c) by
    funext a
    exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht))]
  ring

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem groupPos_card_repeated (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c a => t * base c a))
    (g : Σ c, Option (Shape c)) :
    Fintype.card (GroupPos (w g.1).val (d g.1) g.2) =
      t * baseGroupSize base d g := by
  calc
    Fintype.card (GroupPos (w g.1).val (d g.1) g.2) =
        Fintype.card (Σ a : {a : Shape g.1 // designatedGroup (d g.1) a = g.2},
          {i : Pos g.1 // (w g.1).val i = a.val}) :=
      Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype (w g.1).val
        (p := fun i => designatedGroup (d g.1) ((w g.1).val i) = g.2)
        (q := fun a => designatedGroup (d g.1) a = g.2) (fun _ => Iff.rfl)).symm
    _ = t * baseGroupSize base d g := by
      simp only [Fintype.card_sigma]
      change (∑ a : {a : Shape g.1 // designatedGroup (d g.1) a = g.2},
        wordPopulation (w g.1).val a.val) = _
      simp only [(w g.1).property, baseGroupSize, Finset.mul_sum]

omit [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem groupedEntropy_repeated (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (t : ℕ)
    (H : (Σ c, Option (Shape c)) → ℝ)
    (w : FixedClassWords Pos Shape (fun c a => t * base c a)) :
    groupedEntropy Pos Shape (fun c a => t * base c a) d H w =
      (t : ℝ) * baseGroupedEntropy base d H := by
  simp only [JointCompatibilityEntropyBound.groupedEntropy, groupPos_card_repeated, Nat.cast_mul,
    baseGroupedEntropy, Finset.mul_sum, mul_assoc]

end Repeated

omit [DecidableEq C] in
theorem classTypeError_le (Pos A : C → Type*)
    [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (B t : ℕ) (hsize : ∀ c, Fintype.card (Pos c) ≤ t * B) :
    classTypeError Pos A ≤ classErrorCoefficient A * typeErrorFactor B t := by
  simp only [classTypeError, classErrorCoefficient, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold typeErrorFactor
  apply add_le_add le_rfl
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.succ_le_succ (hsize c)

theorem wordTypeError_le (I A : Type*) [Fintype I] [Fintype A]
    (B t : ℕ) (hsize : Fintype.card I ≤ t * B) :
    wordTypeError I A ≤ (2 * (Fintype.card A : ℝ) + 1) * typeErrorFactor B t := by
  have hlog : Real.log (Fintype.card I + 1 : ℕ) ≤ Real.log (t * B + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hsize)
  have h₁ := mul_le_mul_of_nonneg_left (add_le_add_left hlog 1)
    (by positivity : (0 : ℝ) ≤ (Fintype.card A : ℝ) + 1)
  have h₂ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Fintype.card A) :
    (0 : ℝ) ≤ Fintype.card A)
  unfold wordTypeError typeErrorFactor
  nlinarith [show (0 : ℝ) ≤ Fintype.card A from Nat.cast_nonneg _]

omit [DecidableEq C] in
theorem groupedTypeError_le (Pos A : C → Type*)
    [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (counts : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (w : FixedClassWords Pos Shape counts)
    (B t : ℕ) (hsize : ∀ c, Fintype.card (Pos c) ≤ t * B) :
    groupedTypeError Pos Shape A counts d w ≤
      groupErrorCoefficient Shape A * typeErrorFactor B t := by
  simp only [groupedTypeError, groupErrorCoefficient, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro g _
  apply wordTypeError_le
  exact (Fintype.card_subtype_le _).trans (hsize g.1)

theorem tendsto_typeErrorFactor_div (B : ℕ) :
    Tendsto (fun t : ℕ => typeErrorFactor B t / (t : ℝ)) atTop (𝓝 0) := by
  have hratio : Tendsto (fun t : ℕ => ((t * B : ℕ) : ℝ) / (t : ℝ))
      atTop (𝓝 (B : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
    simp only [Nat.cast_mul]
    exact (mul_div_cancel_left₀ (B : ℝ) (Nat.cast_ne_zero.mpr ht)).symm
  have hlog := JointAmbientRateLimit.tendsto_log_succ_div_nat_of_ratio hratio
  have hinv : Tendsto (fun t : ℕ => (1 : ℝ) / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [typeErrorFactor, add_div, add_zero] using hinv.add hlog

theorem tendsto_mul_typeErrorFactor_div (K : ℝ) (B : ℕ) :
    Tendsto (fun t : ℕ => K * typeErrorFactor B t / (t : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_div_assoc, mul_zero] using (tendsto_typeErrorFactor_div B).const_mul K

end MatrixMultiplication.JointCompatibilityScaling

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityRateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityRateLimit

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound JointCompatibilityScaling Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

private theorem exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityRateLimit {K : Type*} [Fintype K]
    (δ : K → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ δ k := by
  classical
  have aux : ∀ s : Finset K, ∃ ε : ℝ, 0 < ε ∧ ∀ k ∈ s, ε ≤ δ k := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert k s hk ih =>
        obtain ⟨ε, hε, hb⟩ := ih
        refine ⟨min (δ k) ε, lt_min (hδ k) hε, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hb j hj)
  obtain ⟨ε, hε, hb⟩ := aux Finset.univ
  exact ⟨ε, hε, fun k => hb k (Finset.mem_univ k)⟩

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape Pair Left Right : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

omit [DecidableEq C] [∀ c, DecidableEq (Pair c)] in
theorem exists_pair_entropy_window (q : ∀ c, Pair c → ℝ)
    {κ ηMax : ℝ} (hκ : 0 < κ) (hηMax : 0 < ηMax) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧ ∀ c (r : Pair c → ℝ),
      (∀ a, |r a - q c a| ≤ η) → finiteEntropy (q c) - κ ≤ finiteEntropy r := by
  have hex : ∀ c, ∃ δ : ℝ, 0 < δ ∧ ∀ r : Pair c → ℝ,
      (∀ a, |r a - q c a| ≤ δ) → |finiteEntropy r - finiteEntropy (q c)| < κ :=
    fun c => exists_entropy_window (q c) hκ
  choose δ hδ hw using hex
  obtain ⟨η₀, hη₀, hsmall⟩ := exists_pos_le_family_inline_MatrixMultiplication_JointCompatibilityRateLimit δ hδ
  refine ⟨min ηMax η₀, lt_min hηMax hη₀, min_le_left _ _, ?_⟩
  intro c r hr
  have h := (abs_lt.mp (hw c r (fun a =>
    (hr a).trans ((min_le_right _ _).trans (hsmall c))))).1
  linarith

omit [Fintype C] [DecidableEq C] in
theorem repeated_positions_card
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) :
    Fintype.card (Pos c) = t * baseSize base c := by
  rw [fixedClassWords_size Pos Shape _ w c]
  simp only [baseSize, Finset.mul_sum]

omit [DecidableEq C] in
theorem repeated_positions_card_le
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u)) (c : C) :
    Fintype.card (Pos c) ≤ t * totalBase base := by
  rw [repeated_positions_card Pos base t w c]
  exact Nat.mul_le_mul_left _
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c))

omit [DecidableEq C] [∀ c, DecidableEq (Pair c)] in
theorem pair_classEntropy_lower
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ) (t : ℕ)
    (pairCounts : ∀ c, Pair c → ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u))
    {η κ : ℝ}
    (hwindow : ∀ c (r : Pair c → ℝ), (∀ a, |r a - q c a| ≤ η) →
      finiteEntropy (q c) - κ ≤ finiteEntropy r)
    (hpair : PairWindow base q Pos pairCounts η) :
    (t : ℝ) * (pairReferenceEntropy base q - (totalBase base : ℝ) * κ) ≤
      classEntropy Pos Pair pairCounts := by
  have hc (c : C) :
      (t : ℝ) * (baseSize base c : ℝ) * (finiteEntropy (q c) - κ) ≤
        (Fintype.card (Pos c) : ℝ) *
          finiteEntropy (fun a => (pairCounts c a : ℝ) / Fintype.card (Pos c)) := by
    by_cases hz : baseSize base c = 0
    · simp only [repeated_positions_card Pos base t w c, hz, mul_zero,
        Nat.cast_zero, zero_mul, le_refl]
    · have he := hwindow c (fun a => (pairCounts c a : ℝ) / Fintype.card (Pos c))
        (hpair c (Nat.pos_of_ne_zero hz))
      have hh := mul_le_mul_of_nonneg_left he
        (mul_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg (baseSize base c)))
      simpa only [repeated_positions_card Pos base t w c, Nat.cast_mul] using hh
  calc
    (t : ℝ) * (pairReferenceEntropy base q - (totalBase base : ℝ) * κ) =
        ∑ c, (t : ℝ) * (baseSize base c : ℝ) * (finiteEntropy (q c) - κ) := by
      simp only [pairReferenceEntropy, totalBase, Nat.cast_sum, Finset.mul_sum,
        Finset.sum_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    _ ≤ classEntropy Pos Pair pairCounts := Finset.sum_le_sum fun c _ => hc c

omit [DecidableEq C] in
theorem compatibilityExponent_le_rate_add
    (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    (t : ℕ) (ht : 0 < t) (pairCounts : ∀ c, Pair c → ℕ)
    (w : FixedClassWords Pos Shape (fun c u => t * base c u))
    {η κ : ℝ}
    (hwindow : ∀ c (r : Pair c → ℝ), (∀ a, |r a - q c a| ≤ η) →
      finiteEntropy (q c) - κ ≤ finiteEntropy r)
    (hpair : PairWindow base q Pos pairCounts η) :
    compatibilityExponent Pos Shape Pair Left Right (fun c u => t * base c u)
      pairCounts designatedLeft designatedRight HL HR w ≤
      (t : ℝ) * (compatibilityRate base q designatedLeft designatedRight HL HR +
        (totalBase base : ℝ) * κ) +
        errorCoefficient Shape Pair Left Right * typeErrorFactor (totalBase base) t := by
  have hsize := repeated_positions_card Pos base t w
  have hsizele := repeated_positions_card_le Pos base t w
  have hs := classEntropy_repeated Pos base t ht hsize
  have hl := groupedEntropy_repeated Pos base designatedLeft t HL w
  have hr := groupedEntropy_repeated Pos base designatedRight t HR w
  have hp := pair_classEntropy_lower Pos base q t pairCounts w hwindow hpair
  have e₁ := classTypeError_le Pos Shape (totalBase base) t hsizele
  have e₂ := classTypeError_le Pos Pair (totalBase base) t hsizele
  have e₃ := groupedTypeError_le Pos Left (fun c u => t * base c u)
    designatedLeft w (totalBase base) t hsizele
  have e₄ := groupedTypeError_le Pos Right (fun c u => t * base c u)
    designatedRight w (totalBase base) t hsizele
  unfold compatibilityExponent
  rw [hs, hl, hr]
  dsimp only [compatibilityRate, projectedReferenceEntropy, baseGroupedEntropy,
    errorCoefficient] at *
  nlinarith

omit [DecidableEq C] in
theorem exists_window_eventually_exponent_le
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    {ε ηMax : ℝ} (hε : 0 < ε) (hηMax : 0 < ηMax) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ t : ℕ in atTop,
        ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
          (pairCounts : ∀ c, Pair c → ℕ)
          (w : FixedClassWords Pos Shape (fun c u => t * base c u)),
          PairWindow base q Pos pairCounts η →
          compatibilityExponent Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts designatedLeft designatedRight HL HR w ≤
            (t : ℝ) * (compatibilityRate base q designatedLeft designatedRight HL HR + ε) := by
  let κ : ℝ := ε / (2 * ((totalBase base : ℝ) + 1))
  have hden : 0 < 2 * ((totalBase base : ℝ) + 1) := by positivity
  have hκ : 0 < κ := div_pos hε hden
  have hκeq : (2 * ((totalBase base : ℝ) + 1)) * κ = ε :=
    mul_div_cancel₀ _ hden.ne'
  have hκbound : (totalBase base : ℝ) * κ ≤ ε / 2 := by
    nlinarith [(Nat.cast_nonneg (totalBase base) : (0 : ℝ) ≤ totalBase base)]
  obtain ⟨η, hη, hηMax', hwindow⟩ := exists_pair_entropy_window q hκ hηMax
  refine ⟨η, hη, hηMax', ?_⟩
  have herr := tendsto_mul_typeErrorFactor_div
    (errorCoefficient Shape Pair Left Right) (totalBase base)
  filter_upwards [(tendsto_order.1 herr).2 (ε / 2) (half_pos hε),
    eventually_ge_atTop (1 : ℕ)] with t he ht
  intro Pos _ _ pairCounts w hp
  have htpos : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht
  have htr : (0 : ℝ) < t := Nat.cast_pos.mpr htpos
  have he' := (div_lt_iff₀ htr).mp he
  have hκ' := mul_le_mul_of_nonneg_left hκbound htr.le
  have hb := compatibilityExponent_le_rate_add (Left := Left) (Right := Right)
    Pos base q designatedLeft designatedRight HL HR t htpos pairCounts w hwindow hp
  nlinarith

theorem exists_window_eventually_count_le_oai
    (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
    (designatedLeft designatedRight : ∀ c, Shape c → Prop)
    (leftLaw : ∀ c, Shape c → Left c → ℝ)
    (rightLaw : ∀ c, Shape c → Right c → ℝ)
    (hparts : ∀ c, Function.Injective (fun a : Pair c => (leftPart c a, rightPart c a)))
    (HL HR : (Σ c, Option (Shape c)) → ℝ)
    {ε ηMax : ℝ} (hε : 0 < ε) (hηMax : 0 < ηMax) :
    ∃ η : ℝ, 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ t : ℕ in atTop,
        ∀ (Pos : C → Type*) [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
          (pairCounts : ∀ c, Pair c → ℕ)
          (w : FixedClassWords Pos Shape (fun c u => t * base c u))
          (z : FixedClassWords Pos Pair pairCounts) (χ : ℝ),
          PairWindow base q Pos pairCounts η →
          SideEntropyControl Pos Shape Pair Left (fun c u => t * base c u) pairCounts
            leftPart designatedLeft leftLaw χ HL w →
          SideEntropyControl Pos Shape Pair Right (fun c u => t * base c u) pairCounts
            rightPart designatedRight rightLaw χ HR w →
          (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) ≤
            Real.exp ((t : ℝ) *
              (compatibilityRate base q designatedLeft designatedRight HL HR + ε)) ∧
          (0 < compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
            pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z →
            Real.log (compatibleCandidateCount Pos Shape Pair Left Right (fun c u => t * base c u)
              pairCounts leftPart rightPart designatedLeft designatedRight leftLaw rightLaw χ z : ℝ) /
              (t : ℝ) ≤ compatibilityRate base q designatedLeft designatedRight HL HR + ε) := by
  obtain ⟨η, hη, hηMax', hbound⟩ := exists_window_eventually_exponent_le
    (Left := Left) (Right := Right) base q designatedLeft designatedRight HL HR hε hηMax
  refine ⟨η, hη, hηMax', ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with t hb ht
  intro Pos _ _ pairCounts w z χ hp hL hR
  have he := hb Pos pairCounts w hp
  have hc := compatibleCandidateCount_le_exp Pos Shape Pair Left Right
    (fun c u => t * base c u) pairCounts leftPart rightPart
    designatedLeft designatedRight leftLaw rightLaw χ w z hparts HL HR hL hR
  refine ⟨hc.trans (Real.exp_le_exp.mpr he), ?_⟩
  intro hpos
  have hl := log_compatibleCandidateCount_le Pos Shape Pair Left Right
    (fun c u => t * base c u) pairCounts leftPart rightPart
    designatedLeft designatedRight leftLaw rightLaw χ w z hparts HL HR hL hR hpos
  have htr : (0 : ℝ) < t :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one ht)
  exact (div_le_iff₀ htr).mpr (by simpa only [mul_comm] using hl.trans he)

end MatrixMultiplication.JointCompatibilityRateLimit

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.exists_window_eventually_count_le_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.exists_window_eventually_count_le_oai.{u_1, u_2, u_3, u_4, u_5, u_6}

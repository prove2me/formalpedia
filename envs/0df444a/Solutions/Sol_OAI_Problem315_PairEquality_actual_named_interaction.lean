-- Prove2me | solution 1 for OAI.Problem315.PairEquality.actual_named_interaction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:12:56.10448+00:00
-- url     : https://prove2.me/submissions/cca0e029-491a-4f01-b9b8-b26ee6cda9c1

import Mathlib
import Definitions.Def_SwitchChain
import Definitions.Def_OAIQWSWC002

section
-- module Solutions.OAIQW_Problem315.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCovariance

variable {α β : Type*} [sectionFintypeα : Fintype α] [Fintype β]

include sectionFintypeα in
theorem rightSliceAverage_span (b : β → ℝ) (p : α → ℝ) (q : β → ℝ)
    (hp : ∀ x, p x = 0 ∨ p x = 1) (g : β → ℝ) (x : α) :
    rightSliceAverage b q (p x) g =
      rightSliceAverage b q 0 g +
        (rightSliceAverage b q 1 g - rightSliceAverage b q 0 g) * p x := by
  have retainedsectionFintypeα := sectionFintypeα
  rcases hp x with h | h <;> rw [h] <;> ring

end Problem315.CrossCovariance

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem315.CrossBlock

open scoped BigOperators

theorem count_two : ∀ r c : Fin 3,
    count 2 r c = if r = 1 then (if c = 1 then 2 else 1) else (if c = 1 then 1 else 0) := by
  decide

theorem count_one : ∀ r c : Fin 3,
    count 1 r c = if r ≤ 1 ∧ c ≤ 1 then 1 else 0 := by
  decide

theorem count_three : ∀ r c : Fin 3,
    count 3 r c = if 1 ≤ r ∧ 1 ≤ c then 1 else 0 := by
  decide

theorem count_zero : ∀ r c : Fin 3,
    count 0 r c = if r = 0 ∧ c = 0 then 1 else 0 := by
  decide

theorem count_four : ∀ r c : Fin 3,
    count 4 r c = if r = 2 ∧ c = 2 then 1 else 0 := by
  decide

theorem total_le_four : ∀ M : Matrix, total M ≤ 4 := by
  decide

theorem count_two_real (r c : Fin 3) :
    (count 2 r c : ℝ) =
      2 - (if r = 1 then 0 else 1) - (if c = 1 then 0 else 1) := by
  rw [count_two]
  by_cases hr : r = 1 <;> by_cases hc : c = 1 <;> norm_num [hr, hc]

end Problem315.CrossBlock

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossCellMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable

variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

theorem sum_cell (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (F : α → β → ℝ) :
    (∑ z : Cell s r c, F z.val.2.1 z.val.2.2) =
      ∑ x, ∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * F x y := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun z : CrossBlock.Matrix × α × β =>
      CrossBlock.total z.1 = s ∧ CrossBlock.row z.1 0 = (r z.2.1).val ∧
        CrossBlock.col z.1 0 = (c z.2.2).val))
    (by intro z; simp)
    (fun z : CrossBlock.Matrix × α × β => F z.2.1 z.2.2)]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_filter]
  simp [CrossBlock.count]

omit [Fintype α] in
theorem offCenter_boolean (r : α → Fin 3) (x : α) :
    offCenter r x = 0 ∨ offCenter r x = 1 := by
  unfold offCenter
  split_ifs <;> simp

theorem sum_first_fiber (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    (∑ z : Cell s r c, if z.val.2.1 = x then g z.val.2.2 else 0) =
      ∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * g y := by
  classical
  rw [sum_cell s r c (fun u y => if u = x then g y else 0)]
  simp only [mul_ite, mul_zero]
  simp

theorem conditionalRight_eq_table (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    conditionalRight s r c x g =
      (∑ y, (CrossBlock.count s (r x) (c y) : ℝ) * g y) /
        (∑ y, (CrossBlock.count s (r x) (c y) : ℝ)) := by
  classical
  unfold conditionalRight
  rw [Finset.sum_filter, sum_first_fiber]
  congr 1
  have h := sum_first_fiber s r c x (fun _ => 1)
  simpa only [Finset.sum_boole, mul_one] using h

theorem conditionalRight_two (r : α → Fin 3) (c : β → Fin 3)
    (x : α) (g : β → ℝ) :
    conditionalRight 2 r c x g =
      CrossCovariance.rightSliceAverage (fun _ : β => 1)
        (offCenter c) (offCenter r x) g := by
  rw [conditionalRight_eq_table]
  unfold CrossCovariance.rightSliceAverage
  simp only [CrossBlock.count_two_real, offCenter, one_mul]

theorem conditionalRight_two_span (r : α → Fin 3) (c : β → Fin 3)
    (g : β → ℝ) :
    ∃ A B : ℝ, ∀ x, conditionalRight 2 r c x g = A + B * offCenter r x := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 0 g,
    CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 1 g -
      CrossCovariance.rightSliceAverage (fun _ : β => 1) (offCenter c) 0 g, ?_⟩
  intro x
  rw [conditionalRight_two]
  exact CrossCovariance.rightSliceAverage_span _ _ _ (offCenter_boolean r) g x

theorem sum_second_fiber (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    (∑ z : Cell s r c, if z.val.2.2 = y then f z.val.2.1 else 0) =
      ∑ x, (CrossBlock.count s (r x) (c y) : ℝ) * f x := by
  classical
  rw [sum_cell s r c (fun x v => if v = y then f x else 0)]
  simp only [mul_ite, mul_zero]
  simp

theorem conditionalLeft_eq_table (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    conditionalLeft s r c y f =
      (∑ x, (CrossBlock.count s (r x) (c y) : ℝ) * f x) /
        (∑ x, (CrossBlock.count s (r x) (c y) : ℝ)) := by
  classical
  unfold conditionalLeft
  rw [Finset.sum_filter, sum_second_fiber]
  congr 1
  have h := sum_second_fiber s r c y (fun _ => 1)
  simpa only [Finset.sum_boole, mul_one] using h

theorem conditionalLeft_two (r : α → Fin 3) (c : β → Fin 3)
    (y : β) (f : α → ℝ) :
    conditionalLeft 2 r c y f =
      CrossCovariance.rightSliceAverage (fun _ : α => 1)
        (offCenter r) (offCenter c y) f := by
  rw [conditionalLeft_eq_table]
  unfold CrossCovariance.rightSliceAverage
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    rw [CrossBlock.count_two_real]
    simp only [offCenter, one_mul]
    ring
  · apply Finset.sum_congr rfl
    intro x _
    rw [CrossBlock.count_two_real]
    simp only [offCenter, one_mul]
    ring

theorem conditionalLeft_two_span (r : α → Fin 3) (c : β → Fin 3)
    (f : α → ℝ) :
    ∃ A B : ℝ, ∀ y, conditionalLeft 2 r c y f = A + B * offCenter c y := by
  refine ⟨CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 0 f,
    CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 1 f -
      CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 0 f, ?_⟩
  intro y
  rw [conditionalLeft_two]
  exact CrossCovariance.rightSliceAverage_span _ _ _ (offCenter_boolean c) f y

end Problem315.CrossCellMoments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.PairFibers

section Partition

variable {α : Type*} [Fintype α]

theorem expectation_mem (R : Setoid α) (f : EuclideanSpace ℝ α) :
    expectation R f ∈ constantSubspace R :=
  (constantSubspace R).starProjection_apply_mem f

theorem expectation_constant (R : Setoid α) (f : EuclideanSpace ℝ α)
    {x y : α} (hxy : R.r x y) : expectation R f x = expectation R f y :=
  expectation_mem R f x y hxy

theorem cell_nonempty (R : Setoid α) (x : α) : (cell R x).Nonempty :=
  ⟨x, (mem_cell R x x).2 (R.refl x)⟩

omit [Fintype α] in
theorem cellIndicator_mem (R : Setoid α) (x : α) :
    cellIndicator R x ∈ constantSubspace R := by
  intro y z hyz
  change (if R.r x y then (1 : ℝ) else 0) = if R.r x z then 1 else 0
  have hiff : R.r x y ↔ R.r x z :=
    ⟨fun h => R.trans h hyz, fun h => R.trans h (R.symm hyz)⟩
  simp only [hiff]

theorem inner_cellIndicator (R : Setoid α) (x : α) (f : EuclideanSpace ℝ α) :
    inner ℝ f (cellIndicator R x) = ∑ y ∈ cell R x, f y := by
  simp [cellIndicator, PiLp.inner_apply, cell, Finset.sum_filter]

theorem expectation_apply (R : Setoid α) (f : EuclideanSpace ℝ α) (x : α) :
    expectation R f x = (∑ y ∈ cell R x, f y) / ((cell R x).card : ℝ) := by
  have hcNat : 0 < (cell R x).card := Finset.card_pos.mpr (cell_nonempty R x)
  have hc : (0 : ℝ) < (cell R x).card := by exact_mod_cast hcNat
  have horth := Submodule.starProjection_inner_eq_zero
    (K := constantSubspace R) f (cellIndicator R x) (cellIndicator_mem R x)
  change inner ℝ (f - expectation R f) (cellIndicator R x) = 0 at horth
  rw [inner_sub_left, inner_cellIndicator, inner_cellIndicator] at horth
  have hsum : (∑ y ∈ cell R x, expectation R f y) =
      (cell R x).card * expectation R f x := by
    calc
      (∑ y ∈ cell R x, expectation R f y) = ∑ _y ∈ cell R x, expectation R f x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (expectation_constant R f ((mem_cell R x y).1 hy)).symm
      _ = _ := by simp
  rw [hsum] at horth
  apply (eq_div_iff (ne_of_gt hc)).2
  nlinarith

end Partition

end Problem315.PairFibers

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossCellConditionalExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments

attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

theorem expectation_factors_key
    {Ω κ : Type*} [Fintype Ω] (key : Ω → κ) (f : EuclideanSpace ℝ Ω) :
    ∃ g : κ → ℝ, PairFibers.expectation (Setoid.ker key) f =
      WithLp.toLp 2 (fun z => g (key z)) := by
  have hf : Function.FactorsThrough
      (fun z => PairFibers.expectation (Setoid.ker key) f z) key := by
    intro x y hxy
    exact PairFibers.expectation_constant (Setoid.ker key) f hxy
  obtain ⟨g,hg⟩ := (Function.factorsThrough_iff _).mp hf
  refine ⟨g, ?_⟩
  ext z
  exact congrFun hg z

theorem expectation_first_right_apply (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (g : β → ℝ) (z : Cell s r c) :
    PairFibers.expectation (firstPartition s r c)
      (WithLp.toLp 2 (fun w : Cell s r c => g w.val.2.2)) z =
        conditionalRight s r c z.val.2.1 g := by
  rw [PairFibers.expectation_apply]
  have hcell : PairFibers.cell (firstPartition s r c) z =
      Finset.univ.filter (fun w : Cell s r c => w.val.2.1 = z.val.2.1) := by
    ext w
    simp only [PairFibers.mem_cell, Finset.mem_filter, Finset.mem_univ, true_and]
    change z.val.2.1 = w.val.2.1 ↔ w.val.2.1 = z.val.2.1
    exact eq_comm
  rw [hcell]
  rfl

theorem expectation_second_left_apply (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (g : α → ℝ) (z : Cell s r c) :
    PairFibers.expectation (secondPartition s r c)
      (WithLp.toLp 2 (fun w : Cell s r c => g w.val.2.1)) z =
        conditionalLeft s r c z.val.2.2 g := by
  rw [PairFibers.expectation_apply]
  have hcell : PairFibers.cell (secondPartition s r c) z =
      Finset.univ.filter (fun w : Cell s r c => w.val.2.2 = z.val.2.2) := by
    ext w
    simp only [PairFibers.mem_cell, Finset.mem_filter, Finset.mem_univ, true_and]
    change z.val.2.2 = w.val.2.2 ↔ w.val.2.2 = z.val.2.2
    exact eq_comm
  rw [hcell]
  rfl

end Problem315.CrossCellMoments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossIndependent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.CrossBlock

theorem count_eq_independent_product (s : ℕ) (hs : s ≠ 2) (r c : Fin 3) :
    (count s r c : ℝ) = independentMargin s r * independentMargin s c := by
  by_cases hsmall : s ≤ 4
  · interval_cases s
    · rw [count_zero]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · rw [count_one]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · exact (hs rfl).elim
    · rw [count_three]
      simp only [independentMargin]
      split_ifs <;> simp_all
    · rw [count_four]
      simp only [independentMargin]
      split_ifs <;> simp_all
  · have hcount : count s r c = 0 := by
      unfold count
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro M hM
      have ht := (Finset.mem_filter.mp hM).2.1
      have hb := total_le_four M
      omega
    have hmargin (t : Fin 3) : independentMargin s t = 0 := by
      match s with
      | 0 | 1 | 2 | 3 | 4 => omega
      | k + 5 => rfl
    rw [hcount, hmargin, hmargin]
    norm_num

end Problem315.CrossBlock

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossCellAffineComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossCellMoments
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [sectionFintypeα : Fintype α] [sectionFintypeβ : Fintype β]

include sectionFintypeα sectionFintypeβ in
theorem count_pos_of_state (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell s r c) : 0 < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) := by
  have retainedsectionFintypeα := sectionFintypeα
  have retainedsectionFintypeβ := sectionFintypeβ
  unfold CrossBlock.count
  apply Finset.card_pos.mpr
  exact ⟨z.val.1, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact z.property⟩

theorem conditionalRight_constant_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (g : β → ℝ) (z : Cell s r c) :
    conditionalRight s r c z.val.2.1 g =
      (∑ y, CrossBlock.independentMargin s (c y) * g y) /
        (∑ y, CrossBlock.independentMargin s (c y)) := by
  have hp : (0 : ℝ) < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) :=
    by exact_mod_cast count_pos_of_state s r c z
  rw [CrossBlock.count_eq_independent_product s hs] at hp
  have ha : CrossBlock.independentMargin s (r z.val.2.1) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp
    exact (lt_irrefl 0 hp)
  rw [conditionalRight_eq_table]
  simp_rw [CrossBlock.count_eq_independent_product s hs, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ ha

theorem conditionalLeft_constant_of_ne_two (s : ℕ) (hs : s ≠ 2)
    (r : α → Fin 3) (c : β → Fin 3) (g : α → ℝ) (z : Cell s r c) :
    conditionalLeft s r c z.val.2.2 g =
      (∑ x, CrossBlock.independentMargin s (r x) * g x) /
        (∑ x, CrossBlock.independentMargin s (r x)) := by
  have hp : (0 : ℝ) < CrossBlock.count s (r z.val.2.1) (c z.val.2.2) :=
    by exact_mod_cast count_pos_of_state s r c z
  rw [CrossBlock.count_eq_independent_product s hs] at hp
  have hb : CrossBlock.independentMargin s (c z.val.2.2) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp
    exact (lt_irrefl 0 hp)
  rw [conditionalLeft_eq_table]
  simp_rw [CrossBlock.count_eq_independent_product s hs]
  have hn : (∑ x, CrossBlock.independentMargin s (r x) *
      CrossBlock.independentMargin s (c z.val.2.2) * g x) =
      (∑ x, CrossBlock.independentMargin s (r x) * g x) *
        CrossBlock.independentMargin s (c z.val.2.2) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hn, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ hb

theorem expectation_first_second_affine (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (f : EuclideanSpace ℝ (Cell s r c)) :
    ∃ a b : ℝ, (s ≠ 2 → b = 0) ∧ ∀ z : Cell s r c,
      PairFibers.expectation (firstPartition s r c)
        (PairFibers.expectation (secondPartition s r c) f) z =
          a + b * offCenter r z.val.2.1 := by
  obtain ⟨g,hg⟩ := expectation_factors_key (fun z : Cell s r c => z.val.2.2) f
  by_cases hs : s = 2
  · subst s
    obtain ⟨a,b,hab⟩ := conditionalRight_two_span r c g
    refine ⟨a,b,fun h => (h rfl).elim, ?_⟩
    intro z
    change PairFibers.expectation (firstPartition 2 r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.2)) f) z = _
    rw [hg, expectation_first_right_apply]
    exact hab z.val.2.1
  · refine ⟨(∑ y, CrossBlock.independentMargin s (c y) * g y) /
      (∑ y, CrossBlock.independentMargin s (c y)), 0, fun _ => rfl, ?_⟩
    intro z
    change PairFibers.expectation (firstPartition s r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.2)) f) z = _
    rw [hg, expectation_first_right_apply, zero_mul, add_zero]
    exact conditionalRight_constant_of_ne_two s hs r c g z

theorem expectation_second_first_affine (s : ℕ) (r : α → Fin 3) (c : β → Fin 3)
    (f : EuclideanSpace ℝ (Cell s r c)) :
    ∃ a b : ℝ, (s ≠ 2 → b = 0) ∧ ∀ z : Cell s r c,
      PairFibers.expectation (secondPartition s r c)
        (PairFibers.expectation (firstPartition s r c) f) z =
          a + b * offCenter c z.val.2.2 := by
  obtain ⟨g,hg⟩ := expectation_factors_key (fun z : Cell s r c => z.val.2.1) f
  by_cases hs : s = 2
  · subst s
    obtain ⟨a,b,hab⟩ := conditionalLeft_two_span r c g
    refine ⟨a,b,fun h => (h rfl).elim, ?_⟩
    intro z
    change PairFibers.expectation (secondPartition 2 r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell 2 r c => z.val.2.1)) f) z = _
    rw [hg, expectation_second_left_apply]
    exact hab z.val.2.2
  · refine ⟨(∑ x, CrossBlock.independentMargin s (r x) * g x) /
      (∑ x, CrossBlock.independentMargin s (r x)), 0, fun _ => rfl, ?_⟩
    intro z
    change PairFibers.expectation (secondPartition s r c)
      (PairFibers.expectation (Setoid.ker (fun z : Cell s r c => z.val.2.1)) f) z = _
    rw [hg, expectation_second_left_apply, zero_mul, add_zero]
    exact conditionalLeft_constant_of_ne_two s hs r c g z

end Problem315.CrossCellMoments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchPairFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

theorem degree_into_eq {n : ℕ} (G H : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (w : Fin n)
    (hdegree : graphDegree G w = graphDegree H w)
    (hout : ∀ v, v ∉ A → (G.Adj w v ↔ H.Adj w v)) :
    (A.filter (G.Adj w)).card = (A.filter (H.Adj w)).card := by
  classical
  let D (X : SimpleGraph (Fin n)) := Finset.univ.filter (X.Adj w)
  have hinter (X : SimpleGraph (Fin n)) :
      D X ∩ A = A.filter (X.Adj w) := by
    ext v
    simp [D, and_comm]
  have hdiff : D G \ A = D H \ A := by
    ext v
    simp only [Finset.mem_sdiff, D, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      exact ⟨(hout v h.2).mp h.1, h.2⟩
    · intro h
      exact ⟨(hout v h.2).mpr h.1, h.2⟩
  have hG := Finset.card_sdiff_add_card_inter (D G) A
  have hH := Finset.card_sdiff_add_card_inter (D H) A
  rw [hinter] at hG hH
  have hcard : (D G).card = (D H).card := hdegree
  rw [hdiff, hcard] at hG
  exact Nat.add_left_cancel (hG.trans hH.symm)

end Problem315.SwitchPairFiber

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.OrthogonalPairResampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315
namespace PairResampling

attribute [local instance] Classical.propDecidable

theorem graphDegree_partition {n : ℕ} (a : Finset (Fin n))
    (G : SimpleGraph (Fin n)) (w : Fin n) :
    (a.filter (G.Adj w)).card + ((Finset.univ \ a).filter (G.Adj w)).card =
      graphDegree G w := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (G.Adj w)) (p := fun v => v ∈ a)
  have heq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∈ a) = a.filter (G.Adj w) := by
    ext v
    simp [and_comm]
  have hneq : (Finset.univ.filter (G.Adj w)).filter (fun v => v ∉ a) =
      (Finset.univ \ a).filter (G.Adj w) := by
    ext v
    simp [and_comm]
  rw [heq, hneq] at h
  exact h

theorem sameFiber_of_fixed_edges {n : ℕ} (a : Finset (Fin n))
    {G H : SimpleGraph (Fin n)}
    (hdeg : ∀ w, graphDegree G w = graphDegree H w)
    (hout : ∀ u ∉ a, ∀ v ∉ a, G.Adj u v ↔ H.Adj u v)
    (hin : ∀ u ∈ a, ∀ v ∈ a, G.Adj u v ↔ H.Adj u v) :
    SameFiber a G H := by
  refine ⟨hout, hin, ?_⟩
  intro w hw
  have hext : (Finset.univ \ a).filter (G.Adj w) =
      (Finset.univ \ a).filter (H.Adj w) := by
    apply Finset.filter_congr
    intro v hv
    exact hout w hw v (Finset.mem_sdiff.mp hv).2
  have hG := graphDegree_partition a G w
  have hH := graphDegree_partition a H w
  rw [hext, hdeg w] at hG
  omega

theorem sameFiber_state_iff {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))
    (G H : GraphState n d) :
    SameFiber a G.val H.val ↔
      (∀ u ∉ a, ∀ v ∉ a, G.val.Adj u v ↔ H.val.Adj u v) ∧
      (∀ u ∈ a, ∀ v ∈ a, G.val.Adj u v ↔ H.val.Adj u v) := by
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ?_⟩
  apply sameFiber_of_fixed_edges a _ h.1 h.2
  intro w
  exact (G.property w).trans (H.property w).symm

variable {n : ℕ} {d : Fin n → ℕ} (a : Finset (Fin n))

theorem expectation_isSymmetric :
    (expectation n d a).toLinearMap.IsSymmetric :=
  (fiberSpace n d a).starProjection_isSymmetric

theorem fluctuation_eq_sub (f : StateSpace n d) :
    fluctuation n d a f = f - expectation n d a f := by
  exact (fiberSpace n d a).starProjection_orthogonal_val f

@[simp] theorem fluctuation_eq_zero_iff (f : StateSpace n d) :
    fluctuation n d a f = 0 ↔ f ∈ fiberSpace n d a := by
  rw [fluctuation_eq_sub, sub_eq_zero, eq_comm, expectation_eq_self_iff]

theorem state_inner (f g : StateSpace n d) :
    ⟪f, g⟫ = ∑ G : GraphState n d, f G * g G := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem fiberStates_nonempty (G : GraphState n d) : (fiberStates a G).Nonempty :=
  ⟨G, self_mem_fiberStates a G⟩

theorem fiberIndicator_mem (G : GraphState n d) :
    fiberIndicator a G ∈ fiberSpace n d a := by
  intro H K hHK
  change (if SameFiber a G.val H.val then (1 : ℝ) else 0) =
    if SameFiber a G.val K.val then 1 else 0
  have hi : SameFiber a G.val H.val ↔ SameFiber a G.val K.val :=
    ⟨fun h => h.trans hHK, fun h => h.trans hHK.symm⟩
  simp only [hi]

theorem expectation_eq_average (f : StateSpace n d) (G : GraphState n d) :
    expectation n d a f G = (∑ H ∈ fiberStates a G, f H) / (fiberStates a G).card := by
  have horth := Submodule.starProjection_inner_eq_zero (K := fiberSpace n d a)
    f (fiberIndicator a G) (fiberIndicator_mem a G)
  change ⟪f - expectation n d a f, fiberIndicator a G⟫ = 0 at horth
  rw [state_inner] at horth
  have hsum : (∑ H ∈ fiberStates a G, (f H - expectation n d a f H)) = 0 := by
    calc
      _ = ∑ H : GraphState n d, (f - expectation n d a f) H * fiberIndicator a G H := by
        unfold fiberStates
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro H hH
        by_cases h : SameFiber a G.val H.val <;> simp [fiberIndicator, h]
      _ = 0 := horth
  have hequal : ∀ H ∈ fiberStates a G, expectation n d a f H = expectation n d a f G := by
    intro H hH
    exact (expectation_mem a f) H G ((mem_fiberStates a G H).mp hH).symm
  have hsconst : (∑ H ∈ fiberStates a G, expectation n d a f H) =
      (fiberStates a G).card * expectation n d a f G := by
    calc
      _ = ∑ _H ∈ fiberStates a G, expectation n d a f G := Finset.sum_congr rfl hequal
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, hsconst] at hsum
  have hcard : (0 : ℝ) < (fiberStates a G).card := by
    exact_mod_cast Finset.card_pos.mpr (fiberStates_nonempty a G)
  apply (eq_div_iff (ne_of_gt hcard)).mpr
  linarith

end PairResampling
end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchInFiber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315

attribute [local instance] Classical.propDecidable

theorem sameFiber_of_same_side {n : ℕ} {d : Fin n → ℕ}
    (A : Finset (Fin n)) (G H : GraphState n d)
    (hsame : ∀ u v, (u ∈ A ↔ v ∈ A) → (G.val.Adj u v ↔ H.val.Adj u v)) :
    PairResampling.SameFiber A G.val H.val := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu v hv
    exact hsame u v (by simp [hu, hv])
  · intro u hu v hv
    exact hsame u v (by simp [hu, hv])
  · intro w hw
    apply SwitchPairFiber.degree_into_eq G.val H.val A w
    · exact (G.property w).trans (H.property w).symm
    · intro v hv
      exact hsame w v (by simp [hw, hv])

end Problem315

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SwitchFlip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.SwitchFlip

variable {n : ℕ} {d : Fin n → ℕ}

 theorem operator_symmetric (p : SwitchProposal n) :
    (operator (d := d) p).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪operator p f, g⟫ = ⟪f, operator p g⟫
  have h := (isometry (d := d) p).inner_map_map f (operator p g)
  change ⟪operator p f, operator p (operator p g)⟫ = ⟪f, operator p g⟫ at h
  simpa only [operator_involutive] using h

 theorem projection_idempotent (p : SwitchProposal n)
    (f : PairResampling.StateSpace n d) : projection p (projection p f) = projection p f := by
  ext G
  simp only [projection_apply, flip_involutive p G]
  ring

 theorem projection_symmetric (p : SwitchProposal n) :
    (projection (d := d) p).toLinearMap.IsSymmetric := by
  intro f g
  change ⟪(1 / 2 : ℝ) • (f - operator p f), g⟫ =
    ⟪f, (1 / 2 : ℝ) • (g - operator p g)⟫
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  have h := operator_symmetric p f g
  change ⟪operator p f, g⟫ = ⟪f, operator p g⟫ at h
  rw [h]

theorem proposal_sameFiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (G : GraphState n d) :
    PairResampling.SameFiber a G.val (proposalState G p).val := by
  apply sameFiber_of_same_side a G (proposalState G p)
  intro u v hside
  have hm : ¬ (removedMatching p).Adj u v := by
    intro h
    have hc := hcross u v (Or.inl h)
    tauto
  have hn : ¬ (addedMatching p).Adj u v := by
    intro h
    have hc := hcross u v (Or.inr h)
    tauto
  by_cases hv : validSwitch G.val p
  · change G.val.Adj u v ↔ (proposalResult G.val p).Adj u v
    rw [proposalResult_of_valid hv]
    change G.val.Adj u v ↔ (G.val.Adj u v ∧ ¬ (removedMatching p).Adj u v) ∨
      (addedMatching p).Adj u v
    simp [hm, hn]
  · change G.val.Adj u v ↔ (proposalResult G.val p).Adj u v
    simp [proposalResult, hv]

theorem flip_sameFiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (G : GraphState n d) :
    PairResampling.SameFiber a G.val (flip p G).val := by
  have hr : SwitchPairFiber.Crosses (reverseProposal p) a := by
    intro u v h
    apply hcross u v
    simpa only [removedMatching_reverse, addedMatching_reverse, or_comm] using h
  by_cases hv : validSwitch G.val p
  · rw [flip_of_valid p G hv]
    exact proposal_sameFiber p a hcross G
  · by_cases hv' : validSwitch G.val (reverseProposal p)
    · rw [flip_of_reverse_valid p G hv']
      exact proposal_sameFiber (reverseProposal p) a hr G
    · simp only [flip, ite_eq_right hv, ite_eq_right hv']
      exact PairResampling.SameFiber.refl a G.val

theorem projection_eq_zero_of_fiber (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d)
    (hf : f ∈ PairResampling.fiberSpace n d a) : projection p f = 0 := by
  ext G
  change projection p f G = 0
  rw [projection_apply, hf G (flip p G) (flip_sameFiber p a hcross G)]
  ring

@[simp] theorem projection_expectation (p : SwitchProposal n) (a : Finset (Fin n))
    (hcross : SwitchPairFiber.Crosses p a) (f : PairResampling.StateSpace n d) :
    projection p (PairResampling.expectation n d a f) = 0 :=
  projection_eq_zero_of_fiber p a hcross _ (PairResampling.expectation_mem a f)

end Problem315.SwitchFlip

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.CrossTogglePairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.CrossToggle

open SwitchFlip

attribute [local instance] Classical.propDecidable

variable {n : ℕ} {d : Fin n → ℕ}

theorem crossProposal_left (i j k l : Fin n) (h : FourDistinct i j k l) :
    SwitchPairFiber.Crosses (crossProposal i j k l h) {i, j} := by
  rcases h with ⟨hij, hik, hil, hjk, hjl, hkl⟩
  intro u v huv
  simp only [crossProposal, removedMatching_fourVertexProposal,
    addedMatching_fourVertexProposal] at huv
  rcases huv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  all_goals simp_all [Ne.symm]

theorem crossProposal_right (i j k l : Fin n) (h : FourDistinct i j k l) :
    SwitchPairFiber.Crosses (crossProposal i j k l h) {k, l} := by
  rcases h with ⟨hij, hik, hil, hjk, hjl, hkl⟩
  intro u v huv
  simp only [crossProposal, removedMatching_fourVertexProposal,
    addedMatching_fourVertexProposal] at huv
  rcases huv with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
    (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  all_goals simp_all [Ne.symm]

end Problem315.CrossToggle

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointFiberCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

private theorem pair_count {n : Nat} (G : SimpleGraph (Fin n))
    (u v w : Fin n) (huv : u ≠ v) :
    (({u, v} : Finset (Fin n)).filter (G.Adj w)).card = edgeBit G u w + edgeBit G v w := by
  rw [Finset.card_filter, Finset.sum_pair huv]
  simp [edgeBit, SimpleGraph.adj_comm]

private theorem outside_pair {n : Nat} (e : Fin 4 ↪ Fin n) (w : Fin n)
    (hw : Outside e w) (a b : Fin 4) : w ∉ ({e a, e b} : Finset (Fin n)) := by
  simp [hw a, hw b]

theorem sameCell_of_leftFiber {n : Nat} (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 0, e 1} G H) : SameCell e G H := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h20 : e 2 ≠ e 0 := e.injective.ne (by decide)
  have h21 : e 2 ≠ e 1 := e.injective.ne (by decide)
  have h30 : e 3 ≠ e 0 := e.injective.ne (by decide)
  have h31 : e 3 ≠ e 1 := e.injective.ne (by decide)
  have h2 : e 2 ∉ ({e 0, e 1} : Finset (Fin n)) := by simp [h20, h21]
  have h3 : e 3 ∉ ({e 0, e 1} : Finset (Fin n)) := by simp [h30, h31]
  constructor
  · intro u v hu hv
    exact h.1 u (outside_pair e u hu 0 1) v (outside_pair e v hv 0 1)
  · exact h.2.1 (e 0) (by simp) (e 1) (by simp)
  · exact h.1 (e 2) h2 (e 3) h3
  · intro w hw
    have hc := h.2.2 w (outside_pair e w hw 0 1)
    simpa only [pair_count G (e 0) (e 1) w h01, pair_count H (e 0) (e 1) w h01] using hc
  · intro w hw
    have h2w := h.1 (e 2) h2 w (outside_pair e w hw 0 1)
    have h3w := h.1 (e 3) h3 w (outside_pair e w hw 0 1)
    rw [(edgeBit_eq_iff G H (e 2) w).mpr h2w, (edgeBit_eq_iff G H (e 3) w).mpr h3w]

theorem sameCell_of_rightFiber {n : Nat} (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 2, e 3} G H) : SameCell e G H := by
  have h23 : e 2 ≠ e 3 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h03 : e 0 ≠ e 3 := e.injective.ne (by decide)
  have h12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  have h13 : e 1 ≠ e 3 := e.injective.ne (by decide)
  have h0 : e 0 ∉ ({e 2, e 3} : Finset (Fin n)) := by simp [h02, h03]
  have h1 : e 1 ∉ ({e 2, e 3} : Finset (Fin n)) := by simp [h12, h13]
  constructor
  · intro u v hu hv
    exact h.1 u (outside_pair e u hu 2 3) v (outside_pair e v hv 2 3)
  · exact h.1 (e 0) h0 (e 1) h1
  · exact h.2.1 (e 2) (by simp) (e 3) (by simp)
  · intro w hw
    have h0w := h.1 (e 0) h0 w (outside_pair e w hw 2 3)
    have h1w := h.1 (e 1) h1 w (outside_pair e w hw 2 3)
    rw [(edgeBit_eq_iff G H (e 0) w).mpr h0w, (edgeBit_eq_iff G H (e 1) w).mpr h1w]
  · intro w hw
    have hc := h.2.2 w (outside_pair e w hw 2 3)
    simpa only [pair_count G (e 2) (e 3) w h23, pair_count H (e 2) (e 3) w h23] using hc

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointFiberCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointEncoding

variable {V : Type*} [Fintype V]

theorem rightAssignment_eq_iff_first_edges
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K) :
    rightAssignment e G H = rightAssignment e G K ↔
      ∀ w, Outside e w → (H.Adj (e 2) w ↔ K.Adj (e 2) w) := by
  constructor
  · intro h w hw
    apply first_edge_iff_of_counts G H K (e 2) (e 3) w
      (hH.rightCount w hw) (hK.rightCount w hw)
    intro hs
    have he := Finset.ext_iff.mp h ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (rightCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro h
    ext w
    simp only [rightAssignment, Finset.mem_filter]
    rw [h w.val w.property]

theorem leftAssignment_eq_iff_first_edges
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K) :
    leftAssignment e G H = leftAssignment e G K ↔
      ∀ w, Outside e w → (H.Adj (e 0) w ↔ K.Adj (e 0) w) := by
  constructor
  · intro h w hw
    apply first_edge_iff_of_counts G H K (e 0) (e 1) w
      (hH.leftCount w hw) (hK.leftCount w hw)
    intro hs
    have he := Finset.ext_iff.mp h ⟨w, hw⟩
    have member : ⟨w, hw⟩ ∈ BinaryAssignments.singletons (leftCounts e G) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
    constructor
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mp (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
    · intro adjacent
      exact (Finset.mem_filter.mp
        (he.mpr (Finset.mem_filter.mpr ⟨member, adjacent⟩))).2
  · intro h
    ext w
    simp only [leftAssignment, Finset.mem_filter]
    rw [h w.val w.property]

theorem right_boundary_eq_of_assignment_eq
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (h : rightAssignment e G H = rightAssignment e G K)
    (w : V) (hw : Outside e w) :
    (H.Adj (e 2) w ↔ K.Adj (e 2) w) ∧
      (H.Adj (e 3) w ↔ K.Adj (e 3) w) := by
  have hfirst := (rightAssignment_eq_iff_first_edges e G H K hH hK).mp h w hw
  refine ⟨hfirst, ?_⟩
  apply (edgeBit_eq_iff H K (e 3) w).mp
  have hbit := (edgeBit_eq_iff H K (e 2) w).mpr hfirst
  have hHcount := hH.rightCount w hw
  have hKcount := hK.rightCount w hw
  omega

theorem left_boundary_eq_of_assignment_eq
    (e : Fin 4 ↪ V) (G H K : SimpleGraph V)
    (hH : SameCell e G H) (hK : SameCell e G K)
    (h : leftAssignment e G H = leftAssignment e G K)
    (w : V) (hw : Outside e w) :
    (H.Adj (e 0) w ↔ K.Adj (e 0) w) ∧
      (H.Adj (e 1) w ↔ K.Adj (e 1) w) := by
  have hfirst := (leftAssignment_eq_iff_first_edges e G H K hH hK).mp h w hw
  refine ⟨hfirst, ?_⟩
  apply (edgeBit_eq_iff H K (e 1) w).mp
  have hbit := (edgeBit_eq_iff H K (e 0) w).mpr hfirst
  have hHcount := hH.leftCount w hw
  have hKcount := hK.leftCount w hw
  omega

variable {n : Nat} {d : Fin n → Nat}

theorem sameFiber_left_iff_rightAssignment_eq
    (e : Fin 4 ↪ Fin n) (G H K : GraphState n d)
    (hH : SameCell e G.val H.val) (hK : SameCell e G.val K.val) :
    PairResampling.SameFiber {e 0, e 1} H.val K.val ↔
      rightAssignment e G.val H.val = rightAssignment e G.val K.val := by
  have he (a b : Fin 4) (h : a ≠ b) : e a ≠ e b := fun heq => h (e.injective heq)
  constructor
  · intro h
    apply (rightAssignment_eq_iff_first_edges e G.val H.val K.val hH hK).mpr
    intro w hw
    exact h.1 (e 2) (by simp [he 2 0 (by decide), he 2 1 (by decide)])
      w (by simp [hw 0, hw 1])
  · intro h
    apply (PairResampling.sameFiber_state_iff {e 0,e 1} H K).mpr
    have hc := hH.symm.trans hK
    have hb := right_boundary_eq_of_assignment_eq e G.val H.val K.val hH hK h
    constructor
    · intro u hu v hv
      obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
      obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
      cases u with
      | inl a =>
        fin_cases a
        · simp at hu
        · simp at hu
        · cases v with
          | inl b =>
            fin_cases b
            · simp at hv
            · simp at hv
            · simp
            · exact hc.rightInternal
          | inr w => exact (hb w.val w.property).1
        · cases v with
          | inl b =>
            fin_cases b
            · simp at hv
            · simp at hv
            · exact (H.val.adj_comm _ _).trans (hc.rightInternal.trans (K.val.adj_comm _ _))
            · simp
          | inr w => exact (hb w.val w.property).2
      | inr u =>
        cases v with
        | inl b =>
          fin_cases b
          · simp at hv
          · simp at hv
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).1.trans (K.val.adj_comm _ _))
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).2.trans (K.val.adj_comm _ _))
        | inr v => exact hc.outer u.val v.val u.property v.property
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact hc.leftInternal
      · exact (H.val.adj_comm _ _).trans (hc.leftInternal.trans (K.val.adj_comm _ _))
      · simp

theorem sameFiber_right_iff_leftAssignment_eq
    (e : Fin 4 ↪ Fin n) (G H K : GraphState n d)
    (hH : SameCell e G.val H.val) (hK : SameCell e G.val K.val) :
    PairResampling.SameFiber {e 2, e 3} H.val K.val ↔
      leftAssignment e G.val H.val = leftAssignment e G.val K.val := by
  have he (a b : Fin 4) (h : a ≠ b) : e a ≠ e b := fun heq => h (e.injective heq)
  constructor
  · intro h
    apply (leftAssignment_eq_iff_first_edges e G.val H.val K.val hH hK).mpr
    intro w hw
    exact h.1 (e 0) (by simp [he 0 2 (by decide), he 0 3 (by decide)])
      w (by simp [hw 2, hw 3])
  · intro h
    apply (PairResampling.sameFiber_state_iff {e 2,e 3} H K).mpr
    have hc := hH.symm.trans hK
    have hb := left_boundary_eq_of_assignment_eq e G.val H.val K.val hH hK h
    constructor
    · intro u hu v hv
      obtain ⟨u, rfl⟩ := (blockEquiv e).surjective u
      obtain ⟨v, rfl⟩ := (blockEquiv e).surjective v
      cases u with
      | inl a =>
        fin_cases a
        · cases v with
          | inl b =>
            fin_cases b
            · simp
            · exact hc.leftInternal
            · simp at hv
            · simp at hv
          | inr w => exact (hb w.val w.property).1
        · cases v with
          | inl b =>
            fin_cases b
            · exact (H.val.adj_comm _ _).trans (hc.leftInternal.trans (K.val.adj_comm _ _))
            · simp
            · simp at hv
            · simp at hv
          | inr w => exact (hb w.val w.property).2
        · simp at hu
        · simp at hu
      | inr u =>
        cases v with
        | inl b =>
          fin_cases b
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).1.trans (K.val.adj_comm _ _))
          · exact (H.val.adj_comm _ _).trans
              ((hb u.val u.property).2.trans (K.val.adj_comm _ _))
          · simp at hv
          · simp at hv
        | inr v => exact hc.outer u.val v.val u.property v.property
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact hc.rightInternal
      · exact (H.val.adj_comm _ _).trans (hc.rightInternal.trans (K.val.adj_comm _ _))
      · simp

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointStateLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding

theorem marginData_eq_iff_subset_eq {α : Type*} [Fintype α]
    {A : Finset α} {q : Nat} (x y : MarginData A q) :
    x = y ↔ x.val.2 = y.val.2 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      have hx := x.property.2
      have hy := y.property.2
      rw [h] at hx
      omega
    · exact h

variable {n : Nat} {d : Fin n → Nat}

theorem sameFiber_left_iff_stateRightData_eq
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H K : StateCell e G) :
    PairResampling.SameFiber {e 0,e 1} H.val.val K.val.val ↔
      stateRightData e G H = stateRightData e G K := by
  rw [marginData_eq_iff_subset_eq, stateRightData_subset, stateRightData_subset]
  exact sameFiber_left_iff_rightAssignment_eq e G H.val K.val H.property K.property

theorem sameFiber_right_iff_stateLeftData_eq
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H K : StateCell e G) :
    PairResampling.SameFiber {e 2,e 3} H.val.val K.val.val ↔
      stateLeftData e G H = stateLeftData e G K := by
  rw [marginData_eq_iff_subset_eq, stateLeftData_subset, stateLeftData_subset]
  exact sameFiber_right_iff_leftAssignment_eq e G H.val K.val H.property K.property

theorem stateCell_of_leftFiber
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G)
    (K : GraphState n d) (h : PairResampling.SameFiber {e 0,e 1} H.val.val K.val) :
    SameCell e G.val K.val :=
  H.property.trans (sameCell_of_leftFiber e H.val.val K.val h)

theorem stateCell_of_rightFiber
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G)
    (K : GraphState n d) (h : PairResampling.SameFiber {e 2,e 3} H.val.val K.val) :
    SameCell e G.val K.val :=
  H.property.trans (sameCell_of_rightFiber e H.val.val K.val h)

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointCrossCellEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFibers
attribute [local instance] Classical.propDecidable

theorem expectation_ker_pullback {α β ι : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (key : β → ι) (f : EuclideanSpace ℝ β) (x : α) :
    expectation (Setoid.ker (key ∘ e)) (WithLp.toLp 2 (fun y => f (e y))) x =
      expectation (Setoid.ker key) f (e x) := by
  classical
  have hcell : (cell (Setoid.ker (key ∘ e)) x).map e.toEmbedding =
      cell (Setoid.ker key) (e x) := by
    ext y
    simp only [Finset.mem_map, mem_cell, Setoid.ker_def, Function.comp_apply,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨e.symm y, by simpa using hy, by simp⟩
  have hcard := congrArg Finset.card hcell
  rw [Finset.card_map] at hcard
  rw [expectation_apply, expectation_apply, hcard]
  congr 1
  rw [← hcell, Finset.sum_map]
  rfl

end Problem315.PairFibers

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_stateLeftData_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : EuclideanSpace ℝ (CrossCell e G)) (H : StateCell e G) :
    PairFibers.expectation (Setoid.ker (stateLeftData e G))
      (WithLp.toLp 2 (fun K => f (stateCellCrossEquiv e G K))) H =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        f (stateCellCrossEquiv e G H) :=
by
  have h := PairFibers.expectation_ker_pullback (stateCellCrossEquiv e G)
    (fun z : CrossCell e G => z.val.2.1) f H
  simpa only [Function.comp_def, stateCellCrossEquiv_left] using h

theorem expectation_stateRightData_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : EuclideanSpace ℝ (CrossCell e G)) (H : StateCell e G) :
    PairFibers.expectation (Setoid.ker (stateRightData e G))
      (WithLp.toLp 2 (fun K => f (stateCellCrossEquiv e G K))) H =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        f (stateCellCrossEquiv e G H) :=
by
  have h := PairFibers.expectation_ker_pullback (stateCellCrossEquiv e G)
    (fun z : CrossCell e G => z.val.2.2) f H
  simpa only [Function.comp_def, stateCellCrossEquiv_right] using h

end Problem315.DisjointMarginal

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_eq_subtype_key {ι : Type*}
    (a : Finset (Fin n)) (C : GraphState n d → Prop) (key : {G // C G} → ι)
    (hclosed : ∀ (H : {G // C G}) (K : GraphState n d),
      SameFiber a H.val.val K.val → C K)
    (hkey : ∀ H K : {G // C G}, SameFiber a H.val.val K.val.val ↔ key H = key K)
    (f : StateSpace n d) (H : {G // C G}) :
    expectation n d a f H.val =
      PairFibers.expectation (Setoid.ker key) (WithLp.toLp 2 (fun K => f K.val)) H := by
  classical
  let emb : {G // C G} ↪ GraphState n d := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (PairFibers.cell (Setoid.ker key) H).map emb = fiberStates a H.val := by
    ext K
    simp only [Finset.mem_map, PairFibers.mem_cell, Setoid.ker_def, mem_fiberStates]
    constructor
    · rintro ⟨L, hL, hLK⟩
      have hrel := (hkey H L).mpr hL
      change L.val = K at hLK
      simpa only [hLK] using hrel
    · intro hK
      refine ⟨⟨K, hclosed H K hK⟩, ?_, rfl⟩
      exact (hkey H ⟨K, hclosed H K hK⟩).mp hK
  rw [expectation_eq_average, PairFibers.expectation_apply, ← hmap,
    Finset.sum_map, Finset.card_map]
  rfl

end Problem315.PairResampling

namespace Problem315.DisjointMarginal
attribute [local instance] Classical.propDecidable
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

theorem expectation_leftPair_eq_stateRightData (e : Fin 4 ↪ Fin n)
    (G : GraphState n d) (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 0, e 1} f H.val =
      PairFibers.expectation (Setoid.ker (stateRightData e G))
        (WithLp.toLp 2 (fun K => f K.val)) H := by
  exact PairResampling.expectation_eq_subtype_key {e 0, e 1}
    (fun K => SameCell e G.val K.val) (stateRightData e G)
    (stateCell_of_leftFiber e G) (sameFiber_left_iff_stateRightData_eq e G) f H

theorem expectation_rightPair_eq_stateLeftData (e : Fin 4 ↪ Fin n)
    (G : GraphState n d) (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 2, e 3} f H.val =
      PairFibers.expectation (Setoid.ker (stateLeftData e G))
        (WithLp.toLp 2 (fun K => f K.val)) H := by
  exact PairResampling.expectation_eq_subtype_key {e 2, e 3}
    (fun K => SameCell e G.val K.val) (stateLeftData e G)
    (stateCell_of_rightFiber e G) (sameFiber_right_iff_stateLeftData_eq e G) f H

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairEqualityProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem active_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    active i j k l G ↔ active i j k l H := by
  have hh := singletonSet_eq_of_key_eq ((sameFiber_iff_key_eq i j hij G.val H.val).mp h)
  unfold active
  rw [hh]

theorem crossTotal_sameFiber (i j k l : Fin n) (hij : i ≠ j)
    {G H : GraphState n d} (h : SameFiber {i,j} G.val H.val) :
    crossTotal i j k l G = crossTotal i j k l H := by
  have hh := (sameFiber_iff_key_eq i j hij G.val H.val).mp h
  exact congrArg₂ (· + ·) (key_count hh k) (key_count hh l)

theorem observable_zero_of_inactive (i j k l : Fin n)
    (hk : Outside i j k) (hl : Outside i j l) (G : GraphState n d)
    (ht : crossTotal i j k l G = 2) (ha : ¬ active i j k l G) :
    observable i k l G = 0 := by
  unfold crossTotal at ht
  simp only [active, mem_singletonSet, hk, hl, true_and] at ha
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1:ℝ) else 0) = 0
  by_cases hik : G.val.Adj i k <;> by_cases hjk : G.val.Adj j k <;>
    by_cases hil : G.val.Adj i l <;> by_cases hjl : G.val.Adj j l <;>
    simp_all [edgeBit, Xor]

theorem centered_zero_of_inactive (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (G : GraphState n d)
    (ht : crossTotal i j k l G = 2) (ha : ¬ active i j k l G) :
    centered i j k l G = 0 := by
  unfold centered
  rw [fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G = 0
  rw [observable_zero_of_inactive i j k l hk hl G ht ha, expectation_eq_average]
  have hz : (∑ H ∈ fiberStates {i,j} G, observable i k l H) = 0 := by
    apply Finset.sum_eq_zero
    intro H hH
    have h := (mem_fiberStates {i,j} G H).mp hH
    apply observable_zero_of_inactive i j k l hk hl H
    · rw [← crossTotal_sameFiber i j k l hij h]
      exact ht
    · exact fun hA => ha ((active_sameFiber i j k l hij h).mpr hA)
  rw [hz]
  simp

theorem expectation_multiply (a : Finset (Fin n)) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d a) :
    expectation n d a (multiply w f) = multiply w (expectation n d a f) := by
  ext G
  rw [expectation_eq_average]
  change (∑ H ∈ fiberStates a G, w H * f H) / _ =
    w G * expectation n d a f G
  rw [expectation_eq_average]
  have heq : (∑ H ∈ fiberStates a G, w H * f H) =
      w G * ∑ H ∈ fiberStates a G, f H := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro H hH
    rw [hw H G ((mem_fiberStates a G H).mp hH).symm]
  rw [heq, mul_div_assoc]

theorem fluctuation_multiply (a : Finset (Fin n)) (w f : StateSpace n d)
    (hw : w ∈ fiberSpace n d a) :
    fluctuation n d a (multiply w f) = multiply w (fluctuation n d a f) := by
  rw [fluctuation_eq_sub, expectation_multiply a w f hw, fluctuation_eq_sub]
  ext G
  change w G * f G - w G * expectation n d a f G =
    w G * (f G - expectation n d a f G)
  ring

theorem multiply_centered_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    multiply w (centered i j k l) ∈ equalitySpace i j k l := by
  intro G
  refine ⟨w G, fun H h => ?_⟩
  change w H * centered i j k l H = _
  rw [hw H G h.symm]
  by_cases ha : active i j k l G
  · simp only [ite_eq_left ha]
  · simp only [ite_eq_right ha, mul_zero]
    by_cases ht : crossTotal i j k l G = 2
    · have hH : crossTotal i j k l H = 2 :=
        (crossTotal_sameFiber i j k l hij h).symm.trans ht
      have hA : ¬ active i j k l H :=
        fun hA => ha ((active_sameFiber i j k l hij h).mpr hA)
      rw [centered_zero_of_inactive i j k l hij hk hl H hH hA, mul_zero]
    · rw [hsupport G ht, zero_mul]

theorem fluctuation_weighted_observable_mem (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l) (w : StateSpace n d)
    (hw : w ∈ fiberSpace n d {i,j})
    (hsupport : ∀ G : GraphState n d, crossTotal i j k l G ≠ 2 → w G = 0) :
    fluctuation n d {i,j} (multiply w (observable i k l)) ∈
      equalitySpace i j k l := by
  rw [fluctuation_multiply _ _ _ hw]
  exact multiply_centered_mem i j k l hij hk hl w hw hsupport

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointEqualityFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

private theorem row_crossCode (e : Fin 4 ↪ Fin n) (H : SimpleGraph (Fin n)) (i : Fin 2) :
    CrossBlock.row (crossCode e H) i =
      edgeBit H (e (leftIndex i)) (e 2) + edgeBit H (e (leftIndex i)) (e 3) := by
  simp only [CrossBlock.row, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq, edgeBit]
  rfl

private theorem col_crossCode (e : Fin 4 ↪ Fin n) (H : SimpleGraph (Fin n)) (j : Fin 2) :
    CrossBlock.col (crossCode e H) j =
      edgeBit H (e 0) (e (rightIndex j)) + edgeBit H (e 1) (e (rightIndex j)) := by
  simp only [CrossBlock.col, Fin.sum_univ_two, CrossBlock.entry, crossCode,
    decide_eq_true_eq, edgeBit]
  rfl

theorem equality_crossTotal_eq (e : Fin 4 ↪ Fin n) (H : GraphState n d) :
    PairEquality.crossTotal (e 0) (e 1) (e 2) (e 3) H =
      CrossBlock.total (crossCode e H.val) := by
  rw [CrossBlock.total_eq_row_add, row_crossCode, row_crossCode]
  change (PairFiber.edgeBit H.val (e 0) (e 2) + PairFiber.edgeBit H.val (e 1) (e 2)) +
      (PairFiber.edgeBit H.val (e 0) (e 3) + PairFiber.edgeBit H.val (e 1) (e 3)) =
    (edgeBit H.val (e 0) (e 2) + edgeBit H.val (e 0) (e 3)) +
      (edgeBit H.val (e 1) (e 2) + edgeBit H.val (e 1) (e 3))
  simp only [PairFiber.edgeBit, edgeBit]
  omega

theorem stateLeftData_margin (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateLeftData e G H).val.1.val = CrossBlock.row (crossCode e H.val.val) 0 := rfl

theorem stateRightData_margin (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    (stateRightData e G H).val.1.val = CrossBlock.col (crossCode e H.val.val) 0 := rfl

theorem stateLeftFlag_eq_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    flag (stateLeftData e G H).val.1 =
      PairEquality.observable (e 0) (e 2) (e 3) H.val := by
  have hmargin := stateLeftData_margin e G H
  have heq : (stateLeftData e G H).val.1 = 1 ↔
      CrossBlock.row (crossCode e H.val.val) 0 = 1 := by
    exact (Fin.ext_iff).trans (by rw [hmargin]; rfl)
  unfold flag
  simp only [heq]
  change (if CrossBlock.row (crossCode e H.val.val) 0 = 1 then (0 : ℝ) else 1) =
    if H.val.val.Adj (e 0) (e 2) ↔ H.val.val.Adj (e 0) (e 3) then 1 else 0
  rw [row_crossCode]
  change (if edgeBit H.val.val (e 0) (e 2) + edgeBit H.val.val (e 0) (e 3) = 1 then (0 : ℝ) else 1) = _
  by_cases h0 : H.val.val.Adj (e 0) (e 2) <;>
    by_cases h1 : H.val.val.Adj (e 0) (e 3) <;>
    simp [edgeBit, h0, h1]

theorem stateRightFlag_eq_observable (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    flag (stateRightData e G H).val.1 =
      PairEquality.observable (e 2) (e 0) (e 1) H.val := by
  have hmargin := stateRightData_margin e G H
  have heq : (stateRightData e G H).val.1 = 1 ↔
      CrossBlock.col (crossCode e H.val.val) 0 = 1 := by
    exact (Fin.ext_iff).trans (by rw [hmargin]; rfl)
  unfold flag
  simp only [heq]
  change (if CrossBlock.col (crossCode e H.val.val) 0 = 1 then (0 : ℝ) else 1) =
    if H.val.val.Adj (e 2) (e 0) ↔ H.val.val.Adj (e 2) (e 1) then 1 else 0
  have hc0 : H.val.val.Adj (e 2) (e 0) ↔ H.val.val.Adj (e 0) (e 2) :=
    H.val.val.adj_comm _ _
  have hc1 : H.val.val.Adj (e 2) (e 1) ↔ H.val.val.Adj (e 1) (e 2) :=
    H.val.val.adj_comm _ _
  rw [hc0,hc1]
  rw [col_crossCode]
  change (if edgeBit H.val.val (e 0) (e 2) + edgeBit H.val.val (e 1) (e 2) = 1 then (0 : ℝ) else 1) = _
  by_cases h0 : H.val.val.Adj (e 0) (e 2) <;>
    by_cases h1 : H.val.val.Adj (e 1) (e 2) <;>
    simp [edgeBit, h0, h1]

theorem stateCell_crossTotal_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    CrossBlock.total (crossCode e H.val.val) = CrossBlock.total (crossCode e G.val) :=
  ((coordinate_degrees_iff e G.val
    (graphStateCellEquiv e G H).matrix (graphStateCellEquiv e G H).left
    (graphStateCellEquiv e G H).right (graphStateCellEquiv e G H).left_subset
    (graphStateCellEquiv e G H).right_subset).mp (graphStateCellEquiv e G H).degrees).1

theorem equality_crossTotal_on_cell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (H : StateCell e G) :
    PairEquality.crossTotal (e 0) (e 1) (e 2) (e 3) H.val =
      CrossBlock.total (crossCode e G.val) := by
  rw [equality_crossTotal_eq, stateCell_crossTotal_eq]

theorem equality_crossTotal_reverse_eq (e : Fin 4 ↪ Fin n) (G : GraphState n d) :
    PairEquality.crossTotal (e 2) (e 3) (e 0) (e 1) G =
      CrossBlock.total (crossCode e G.val) := by
  rw [← equality_crossTotal_eq e G]
  unfold PairEquality.crossTotal PairFiber.edgeBit
  simp only [G.val.adj_comm (e 2) (e 0), G.val.adj_comm (e 3) (e 0),
    G.val.adj_comm (e 2) (e 1), G.val.adj_comm (e 3) (e 1)]
  omega

theorem equality_crossTotal_reverse_on_cell
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (H : StateCell e G) :
    PairEquality.crossTotal (e 2) (e 3) (e 0) (e 1) H.val =
      CrossBlock.total (crossCode e G.val) := by
  rw [equality_crossTotal_reverse_eq, stateCell_crossTotal_eq]

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointGraphAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Problem315.DisjointMarginal
open DisjointEncoding
variable {n : Nat} {d : Fin n → Nat}

theorem left_expectation_eq_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 0,e 1} f H.val =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        (crossCellRestriction e G f) (stateCellCrossEquiv e G H) := by
  rw [expectation_leftPair_eq_stateRightData e G f H]
  have heq : (WithLp.toLp 2 (fun K : StateCell e G => f K.val)) =
      WithLp.toLp 2 (fun K => crossCellRestriction e G f (stateCellCrossEquiv e G K)) := by
    ext K
    change f K.val = crossCellRestriction e G f (stateCellCrossEquiv e G K)
    rw [crossCellRestriction_apply_equiv]
  rw [heq, expectation_stateRightData_crossCell]

theorem right_expectation_eq_crossCell (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (f : PairResampling.StateSpace n d) (H : StateCell e G) :
    PairResampling.expectation n d {e 2,e 3} f H.val =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        (crossCellRestriction e G f) (stateCellCrossEquiv e G H) := by
  rw [expectation_rightPair_eq_stateLeftData e G f H]
  have heq : (WithLp.toLp 2 (fun K : StateCell e G => f K.val)) =
      WithLp.toLp 2 (fun K => crossCellRestriction e G f (stateCellCrossEquiv e G K)) := by
    ext K
    change f K.val = crossCellRestriction e G f (stateCellCrossEquiv e G K)
    rw [crossCellRestriction_apply_equiv]
  rw [heq, expectation_stateLeftData_crossCell]

theorem crossCellRestriction_left_expectation
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    crossCellRestriction e G (PairResampling.expectation n d {e 0,e 1} f) =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
        (crossCellRestriction e G f) := by
  ext z
  have h := left_expectation_eq_crossCell e G f ((stateCellCrossEquiv e G).symm z)
  simpa only [Equiv.apply_symm_apply, crossCellRestriction] using h

theorem crossCellRestriction_right_expectation
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    crossCellRestriction e G (PairResampling.expectation n d {e 2,e 3} f) =
      PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
        (crossCellRestriction e G f) := by
  ext z
  have h := right_expectation_eq_crossCell e G f ((stateCellCrossEquiv e G).symm z)
  simpa only [Equiv.apply_symm_apply, crossCellRestriction] using h

theorem right_left_expectation_cell_affine
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    ∃ A B : ℝ, (CrossBlock.total (crossCode e G.val) ≠ 2 → B = 0) ∧
      ∀ H : StateCell e G,
        PairResampling.expectation n d {e 2,e 3}
          (PairResampling.expectation n d {e 0,e 1} f) H.val =
            A + B * PairEquality.observable (e 0) (e 2) (e 3) H.val := by
  obtain ⟨A,B,hB,hAB⟩ := CrossCellMoments.expectation_first_second_affine
    (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)
    (crossCellRestriction e G f)
  refine ⟨A,B,hB,?_⟩
  intro H
  rw [right_expectation_eq_crossCell, crossCellRestriction_left_expectation]
  have h := hAB (stateCellCrossEquiv e G H)
  change PairFibers.expectation
    (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
    (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
      (crossCellRestriction e G f)) (stateCellCrossEquiv e G H) =
        A + B * flag (stateLeftData e G H).val.1 at h
  rw [stateLeftFlag_eq_observable] at h
  exact h

theorem left_right_expectation_cell_affine
    (e : Fin 4 ↪ Fin n) (G : GraphState n d) (f : PairResampling.StateSpace n d) :
    ∃ A B : ℝ, (CrossBlock.total (crossCode e G.val) ≠ 2 → B = 0) ∧
      ∀ H : StateCell e G,
        PairResampling.expectation n d {e 0,e 1}
          (PairResampling.expectation n d {e 2,e 3} f) H.val =
            A + B * PairEquality.observable (e 2) (e 0) (e 1) H.val := by
  obtain ⟨A,B,hB,hAB⟩ := CrossCellMoments.expectation_second_first_affine
    (CrossBlock.total (crossCode e G.val))
    (fun x : LeftData e G.val => x.val.1) (fun y : RightData e G.val => y.val.1)
    (crossCellRestriction e G f)
  refine ⟨A,B,hB,?_⟩
  intro H
  rw [left_expectation_eq_crossCell, crossCellRestriction_right_expectation]
  have h := hAB (stateCellCrossEquiv e G H)
  change PairFibers.expectation
    (Setoid.ker (fun z : CrossCell e G => z.val.2.2))
    (PairFibers.expectation (Setoid.ker (fun z : CrossCell e G => z.val.2.1))
      (crossCellRestriction e G f)) (stateCellCrossEquiv e G H) =
        A + B * flag (stateRightData e G H).val.1 at h
  rw [stateRightFlag_eq_observable] at h
  exact h

end Problem315.DisjointMarginal

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.DisjointProjectionCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.DisjointEncoding

attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

private theorem pair_count_eq (G : SimpleGraph (Fin n)) (i j w : Fin n)
    (hij : i ≠ j) :
    (({i, j} : Finset (Fin n)).filter (G.Adj w)).card =
      edgeBit G i w + edgeBit G j w := by
  by_cases hi : G.Adj i w <;> by_cases hj : G.Adj j w <;>
    simp [edgeBit, Finset.filter_insert, Finset.filter_singleton,
      G.adj_comm w i, G.adj_comm w j, hi, hj, hij]

theorem sameCell_of_sameFiber_left (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 0, e 1} G H) : SameCell e G H := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have hout (w : Fin n) (hw : Outside e w) : w ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [hw 0, hw 1]
  have h2 : e 2 ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [he 2 0 (by decide), he 2 1 (by decide)]
  have h3 : e 3 ∉ ({e 0, e 1} : Finset (Fin n)) := by
    simp [he 3 0 (by decide), he 3 1 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun u v hu hv => h.1 u (hout u hu) v (hout v hv)
  · exact h.2.1 (e 0) (by simp) (e 1) (by simp)
  · exact h.1 (e 2) h2 (e 3) h3
  · intro w hw
    have hc := h.2.2 w (hout w hw)
    simpa only [pair_count_eq G _ _ _ (he 0 1 (by decide)),
      pair_count_eq H _ _ _ (he 0 1 (by decide))] using hc
  · intro w hw
    rw [(edgeBit_eq_iff G H (e 2) w).mpr (h.1 (e 2) h2 w (hout w hw)),
      (edgeBit_eq_iff G H (e 3) w).mpr (h.1 (e 3) h3 w (hout w hw))]

theorem sameCell_of_sameFiber_right (e : Fin 4 ↪ Fin n)
    (G H : SimpleGraph (Fin n))
    (h : PairResampling.SameFiber {e 2, e 3} G H) : SameCell e G H := by
  have he (a b : Fin 4) (hab : a ≠ b) : e a ≠ e b := fun h => hab (e.injective h)
  have hout (w : Fin n) (hw : Outside e w) : w ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [hw 2, hw 3]
  have h0 : e 0 ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [he 0 2 (by decide), he 0 3 (by decide)]
  have h1 : e 1 ∉ ({e 2, e 3} : Finset (Fin n)) := by
    simp [he 1 2 (by decide), he 1 3 (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun u v hu hv => h.1 u (hout u hu) v (hout v hv)
  · exact h.1 (e 0) h0 (e 1) h1
  · exact h.2.1 (e 2) (by simp) (e 3) (by simp)
  · intro w hw
    rw [(edgeBit_eq_iff G H (e 0) w).mpr (h.1 (e 0) h0 w (hout w hw)),
      (edgeBit_eq_iff G H (e 1) w).mpr (h.1 (e 1) h1 w (hout w hw))]
  · intro w hw
    have hc := h.2.2 w (hout w hw)
    simpa only [pair_count_eq G _ _ _ (he 2 3 (by decide)),
      pair_count_eq H _ _ _ (he 2 3 (by decide))] using hc

end Problem315.DisjointEncoding

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.RankOneInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem315
namespace RankOneInteraction

theorem interaction_lower_bound
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b j h k : E)
    (hid : inner ℝ h k = ‖j‖ ^ 2 + inner ℝ a b) :
    2 * ‖j‖ ^ 2 - ‖a‖ ^ 2 - ‖b‖ ^ 2 ≤ 2 * inner ℝ h k := by
  have hn : 0 ≤ ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    rw [← norm_add_sq_real]
    exact sq_nonneg _
  linarith

theorem norm_sq_le_of_inner_eq_self
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w z : E) (h : inner ℝ z w = inner ℝ w w) : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have hn := sq_nonneg ‖z - w‖
  rw [norm_sub_sq_real, h, real_inner_self_eq_norm_sq] at hn
  nlinarith

theorem projection_norm_sq_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hPi : ∀ z, P (P z) = P z)
    (z : E) : ‖P z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  apply norm_sq_le_of_inner_eq_self
  simpa only [hPi] using (hPs z (P z)).symm

theorem error_norm_sq_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E →ₗ[ℝ] E) (hRs : R.IsSymmetric) (f w : E)
    (hRw : R w = w) (hfw : inner ℝ f w = inner ℝ w w) :
    ‖w‖ ^ 2 ≤ ‖R f‖ ^ 2 := by
  apply norm_sq_le_of_inner_eq_self
  rw [hRs, hRw, hfw]

end RankOneInteraction
end Problem315

end OAI
end

section
-- module Solutions.OAIQW_Problem315.ProjectionRangeInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.ProjectionRangeInteraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_range_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (f : E) :
    ∃ p q j : E, f = P p + Q q + j ∧ P j = 0 ∧ Q j = 0 := by
  let K : Submodule ℝ E := P.range ⊔ Q.range
  let w := K.starProjection f
  let j := f - w
  have hw : w ∈ K := K.starProjection_apply_mem f
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hw
  obtain ⟨p₀, rfl⟩ := hp
  obtain ⟨q₀, rfl⟩ := hq
  have hj : j ∈ Kᗮ := K.sub_starProjection_mem_orthogonal f
  have hPj : P j = 0 := by
    have hm : P j ∈ K := (show P.range ≤ K from le_sup_left) (show P j ∈ P.range from ⟨j, rfl⟩)
    have hz : ⟪j, P j⟫ = 0 := (K.mem_orthogonal' j).mp hj (P j) hm
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hPs, hPi, hz]
  have hQj : Q j = 0 := by
    have hm : Q j ∈ K := (show Q.range ≤ K from le_sup_right) (show Q j ∈ Q.range from ⟨j, rfl⟩)
    have hz : ⟪j, Q j⟫ = 0 := (K.mem_orthogonal' j).mp hj (Q j) hm
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hQs, hQi, hz]
  refine ⟨p₀, q₀, j, ?_, hPj, hQj⟩
  rw [hpq]
  dsimp [j]
  module

theorem exists_correlated_range_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (p : E) :
    ∃ x u : E, P p = P (Q x) + u ∧ P u = u ∧ Q u = 0 := by
  let K := (P.comp Q).range
  let w := K.starProjection (P p)
  let u := P p - w
  have hw : w ∈ K := K.starProjection_apply_mem (P p)
  obtain ⟨x, hx⟩ := hw
  change P (Q x) = w at hx
  have hPw : P w = w := by rw [← hx, hPi]
  have hPu : P u = u := by simp only [u, map_sub, hPi, hPw]
  have hu : u ∈ Kᗮ := K.sub_starProjection_mem_orthogonal (P p)
  have hQu : Q u = 0 := by
    have hm : P (Q u) ∈ K := ⟨u, rfl⟩
    have hz : ⟪u, P (Q u)⟫ = 0 := (K.mem_orthogonal' u).mp hu _ hm
    rw [← hPs, hPu] at hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [hQs, hQi, hz]
  refine ⟨x, u, ?_, hPu, hQu⟩
  rw [hx]
  dsimp [u]
  module

theorem exists_two_projection_decomposition [FiniteDimensional ℝ E]
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (f : E) :
    ∃ p q j u v : E,
      f = P (Q p) + Q (P q) + j + u + v ∧
      P j = 0 ∧ Q j = 0 ∧ P u = u ∧ Q u = 0 ∧ P v = 0 ∧ Q v = v := by
  obtain ⟨p₀,q₀,j,hf,hPj,hQj⟩ := exists_range_decomposition P Q hPs hQs hPi hQi f
  obtain ⟨p,u,hp,hPu,hQu⟩ := exists_correlated_range_decomposition P Q hPs hQs hPi hQi p₀
  obtain ⟨q,v,hq,hQv,hPv⟩ := exists_correlated_range_decomposition Q P hQs hPs hQi hPi q₀
  refine ⟨p,q,j,u,v,?_,hPj,hQj,hPu,hQu,hPv,hQv⟩
  rw [hf,hp,hq]
  module

theorem interaction_of_correlated_error_ranges [FiniteDimensional ℝ E]
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hR : ∀ z, R (Q (P z) - P (Q (P z))) = Q (P z) - P (Q (P z)))
    (hS : ∀ z, S (P (Q z) - Q (P (Q z))) = P (Q z) - Q (P (Q z)))
    (f : E) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪f - P f, f - Q f⟫ := by
  obtain ⟨p,q,j,u,v,hf,hPj,hQj,hPu,hQu,hPv,hQv⟩ :=
    exists_two_projection_decomposition P Q hPs hQs hPi hQi f
  let a := Q (P q) - P (Q (P q))
  let b := P (Q p) - Q (P (Q p))
  have hPa : P a = 0 := by simp only [a, map_sub, hPi, sub_self]
  have hQb : Q b = 0 := by simp only [b, map_sub, hQi, sub_self]
  have hja : ⟪j, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs j (P q), hQj, inner_zero_left,
      ← hPs j (Q (P q)), hPj, inner_zero_left, sub_self]
  have hjb : ⟪j, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs j (Q p), hPj, inner_zero_left,
      ← hQs j (P (Q p)), hQj, inner_zero_left, sub_self]
  have hju : ⟪j, u⟫ = 0 := by rw [← hPu, ← hPs, hPj, inner_zero_left]
  have hjv : ⟪j, v⟫ = 0 := by rw [← hQv, ← hQs, hQj, inner_zero_left]
  have hua : ⟪u, a⟫ = 0 := by rw [← hPu, hPs, hPa, inner_zero_right]
  have hvb : ⟪v, b⟫ = 0 := by rw [← hQv, hQs, hQb, inner_zero_right]
  have huv : ⟪u, v⟫ = 0 := by rw [← hPu, hPs, hPv, inner_zero_right]
  have hva : ⟪v, a⟫ = 0 := by
    simp only [a, inner_sub_right]
    rw [← hQs, hQv, ← hPs, hPv, inner_zero_left,
      ← hPs, hPv, inner_zero_left, sub_self]
  have hub : ⟪u, b⟫ = 0 := by
    simp only [b, inner_sub_right]
    rw [← hPs, hPu, ← hQs, hQu, inner_zero_left,
      ← hQs, hQu, inner_zero_left, sub_self]
  have ha : f - P f = j + a + v := by
    rw [hf]
    simp only [map_add, hPi, hPj, hPu, hPv]
    dsimp [a]
    module
  have hb : f - Q f = j + b + u := by
    rw [hf]
    simp only [map_add, hQi, hQj, hQu, hQv]
    dsimp [b]
    module
  have hfa : ⟪f, a⟫ = ⟪a, a⟫ := by
    have hz : ⟪P f, a⟫ = 0 := by rw [hPs, hPa, inner_zero_right]
    have ht : ⟪f - P f, a⟫ = ⟪a, a⟫ := by
      rw [ha, inner_add_left, inner_add_left, hja, hva, zero_add, add_zero]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hfb : ⟪f, b⟫ = ⟪b, b⟫ := by
    have hz : ⟪Q f, b⟫ = 0 := by rw [hQs, hQb, inner_zero_right]
    have ht : ⟪f - Q f, b⟫ = ⟪b, b⟫ := by
      rw [hb, inner_add_left, inner_add_left, hjb, hub, zero_add, add_zero]
    simpa only [inner_sub_left, hz, sub_zero] using ht
  have hra := RankOneInteraction.error_norm_sq_le R hRs f a (hR q) hfa
  have hsb := RankOneInteraction.error_norm_sq_le S hSs f b (hS p) hfb
  have hGu : G u = 0 := by rw [← hPu, hGP]
  have hGv : G v = 0 := by rw [← hQv, hGQ]
  have hGf : G f = G j := by
    rw [hf]
    simp only [map_add, hGP, hGQ, hGu, hGv, zero_add, add_zero]
  have hg : ‖G f‖ ^ 2 ≤ ‖j‖ ^ 2 := by
    rw [hGf]
    exact RankOneInteraction.projection_norm_sq_le G hGs hGi j
  have hid : ⟪f - P f, f - Q f⟫ = ‖j‖ ^ 2 + ⟪a, b⟫ := by
    rw [ha, hb]
    simp only [inner_add_left, inner_add_right, hjb, hju, hvb,
      show ⟪a, j⟫ = 0 by rw [real_inner_comm, hja],
      show ⟪a, u⟫ = 0 by rw [real_inner_comm, hua],
      show ⟪v, j⟫ = 0 by rw [real_inner_comm, hjv],
      show ⟪v, u⟫ = 0 by rw [real_inner_comm, huv],
      real_inner_self_eq_norm_sq, zero_add, add_zero]
  have hlow := RankOneInteraction.interaction_lower_bound a b j (f - P f) (f - Q f) hid
  linarith

end Problem315.ProjectionRangeInteraction

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairRangeInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairResampling
attribute [local instance] Classical.propDecidable

theorem pair_interaction_of_correlated_ranges
    {n : ℕ} {d : Fin n → ℕ} (a b : Finset (Fin n))
    (G R S : StateSpace n d →L[ℝ] StateSpace n d)
    (hGs : G.toLinearMap.IsSymmetric)
    (hRs : R.toLinearMap.IsSymmetric) (hSs : S.toLinearMap.IsSymmetric)
    (hGi : ∀ f, G (G f) = G f)
    (hGa : ∀ f, G (expectation n d a f) = 0)
    (hGb : ∀ f, G (expectation n d b f) = 0)
    (hR : ∀ f, R (fluctuation n d a (expectation n d b (expectation n d a f))) =
      fluctuation n d a (expectation n d b (expectation n d a f)))
    (hS : ∀ f, S (fluctuation n d b (expectation n d a (expectation n d b f))) =
      fluctuation n d b (expectation n d a (expectation n d b f)))
    (f : StateSpace n d) :
    2 * ‖G f‖ ^ 2 - ‖R f‖ ^ 2 - ‖S f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  apply ProjectionRangeInteraction.interaction_of_correlated_error_ranges
    (expectation n d a).toLinearMap (expectation n d b).toLinearMap
    G.toLinearMap R.toLinearMap S.toLinearMap
    (expectation_isSymmetric a) (expectation_isSymmetric b) hGs hRs hSs
    (expectation_idempotent a) (expectation_idempotent b) hGi hGa hGb
    (fun z => ?_) (fun z => ?_) f |>.trans_eq
      (by simp only [ContinuousLinearMap.coe_coe, fluctuation_eq_sub])
  · simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using hR z
  · simpa only [fluctuation_eq_sub, ContinuousLinearMap.coe_coe] using hS z

end Problem315.PairResampling

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairAffineInteraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem affineFlagImage_of_cellwise {β : Type*}
    (i j k l : Fin n) (key : GraphState n d → β)
    (hkey : ∀ G H : GraphState n d, SameFiber {i,j} G.val H.val → key G = key H)
    (f : StateSpace n d)
    (hcell : ∀ c : β, ∃ A B : ℝ,
      (∀ G : GraphState n d, key G = c → f G = A + B * observable i k l G) ∧
      (∀ G : GraphState n d, key G = c → crossTotal i j k l G ≠ 2 → B = 0)) :
    AffineFlagImage i j k l f := by
  choose A B hformula hsupport using hcell
  let base : StateSpace n d := WithLp.toLp 2 (fun G => A (key G))
  let weight : StateSpace n d := WithLp.toLp 2 (fun G => B (key G))
  refine ⟨base,weight,?_,?_,?_,?_⟩
  · intro G H h
    change A (key G) = A (key H)
    rw [hkey G H h]
  · intro G H h
    change B (key G) = B (key H)
    rw [hkey G H h]
  · intro G hG
    exact hsupport (key G) G rfl hG
  · ext G
    exact hformula (key G) G rfl

theorem fluctuation_mem_of_affineFlagImage
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (f : StateSpace n d) (hf : AffineFlagImage i j k l f) :
    fluctuation n d {i,j} f ∈ equalitySpace i j k l := by
  obtain ⟨base,weight,hbase,hweight,hsupport,rfl⟩ := hf
  rw [map_add, (fluctuation_eq_zero_iff _ _).mpr hbase, zero_add]
  exact fluctuation_weighted_observable_mem i j k l hij hk hl weight hweight hsupport

theorem projection_fixes_fluctuation_of_affineFlagImage
    (i j k l : Fin n) (hij : i ≠ j)
    (hk : Outside i j k) (hl : Outside i j l)
    (f : StateSpace n d) (hf : AffineFlagImage i j k l f) :
    projection i j k l (fluctuation n d {i,j} f) = fluctuation n d {i,j} f :=
  (projection_eq_self_iff _ _ _ _ _).mpr
    (fluctuation_mem_of_affineFlagImage i j k l hij hk hl f hf)

theorem interaction_of_affine_conditional_images
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : Outside i j k) (hl : Outside i j l)
    (hi : Outside k l i) (hj : Outside k l j)
    (G : StateSpace n d →L[ℝ] StateSpace n d)
    (hGs : G.toLinearMap.IsSymmetric) (hGi : ∀ f, G (G f) = G f)
    (hGa : ∀ f, G (expectation n d {i,j} f) = 0)
    (hGb : ∀ f, G (expectation n d {k,l} f) = 0)
    (hBA : ∀ f, AffineFlagImage i j k l
      (expectation n d {k,l} (expectation n d {i,j} f)))
    (hAB : ∀ f, AffineFlagImage k l i j
      (expectation n d {i,j} (expectation n d {k,l} f)))
    (f : StateSpace n d) :
    2 * ‖G f‖ ^ 2 - ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  exact pair_interaction_of_correlated_ranges {i,j} {k,l} G
    (projection i j k l) (projection k l i j) hGs
    (equalitySpace i j k l).starProjection_isSymmetric
    (equalitySpace k l i j).starProjection_isSymmetric
    hGi hGa hGb
    (fun z => projection_fixes_fluctuation_of_affineFlagImage i j k l hij hk hl _ (hBA z))
    (fun z => projection_fixes_fluctuation_of_affineFlagImage k l i j hkl hi hj _ (hAB z)) f

theorem switch_interaction_of_affine_conditional_images
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : Outside i j k) (hl : Outside i j l)
    (hi : Outside k l i) (hj : Outside k l j)
    (p : SwitchProposal n)
    (hpa : SwitchPairFiber.Crosses p {i,j}) (hpb : SwitchPairFiber.Crosses p {k,l})
    (hBA : ∀ f : StateSpace n d, AffineFlagImage i j k l
      (expectation n d {k,l} (expectation n d {i,j} f)))
    (hAB : ∀ f : StateSpace n d, AffineFlagImage k l i j
      (expectation n d {i,j} (expectation n d {k,l} f)))
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection p f‖ ^ 2 -
        ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  exact interaction_of_affine_conditional_images i j k l hij hkl hk hl hi hj
    (SwitchFlip.projection p) (SwitchFlip.projection_symmetric p)
    (SwitchFlip.projection_idempotent p)
    (SwitchFlip.projection_expectation p {i,j} hpa)
    (SwitchFlip.projection_expectation p {k,l} hpb) hBA hAB f

end Problem315.PairEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairActualAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling DisjointEncoding DisjointMarginal
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem right_left_expectation_affine (e : Fin 4 ↪ Fin n)
    (f : StateSpace n d) :
    AffineFlagImage (e 0) (e 1) (e 2) (e 3)
      (expectation n d {e 2,e 3} (expectation n d {e 0,e 1} f)) := by
  apply affineFlagImage_of_cellwise _ _ _ _ (cellIndex e)
    (fun G H h => (cellIndex_eq_iff e G H).mpr
      (sameCell_of_sameFiber_left e G.val H.val h))
  intro c
  induction c using Quotient.inductionOn with
  | h G =>
    obtain ⟨A,B,hB,hAB⟩ := right_left_expectation_cell_affine e G f
    refine ⟨A,B,?_,?_⟩
    · intro H hH
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      exact hAB ⟨H,hcell⟩
    · intro H hH ht
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      apply hB
      rwa [← equality_crossTotal_on_cell e G ⟨H,hcell⟩]

theorem left_right_expectation_affine (e : Fin 4 ↪ Fin n)
    (f : StateSpace n d) :
    AffineFlagImage (e 2) (e 3) (e 0) (e 1)
      (expectation n d {e 0,e 1} (expectation n d {e 2,e 3} f)) := by
  apply affineFlagImage_of_cellwise _ _ _ _ (cellIndex e)
    (fun G H h => (cellIndex_eq_iff e G H).mpr
      (sameCell_of_sameFiber_right e G.val H.val h))
  intro c
  induction c using Quotient.inductionOn with
  | h G =>
    obtain ⟨A,B,hB,hAB⟩ := left_right_expectation_cell_affine e G f
    refine ⟨A,B,?_,?_⟩
    · intro H hH
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      exact hAB ⟨H,hcell⟩
    · intro H hH ht
      have hcell : SameCell e G.val H.val :=
        ((cellIndex_eq_iff e H G).mp hH).symm
      apply hB
      rwa [← equality_crossTotal_reverse_on_cell e G ⟨H,hcell⟩]

theorem actual_switch_interaction (e : Fin 4 ↪ Fin n)
    (p : SwitchProposal n)
    (hpa : SwitchPairFiber.Crosses p {e 0,e 1})
    (hpb : SwitchPairFiber.Crosses p {e 2,e 3})
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection p f‖ ^ 2 -
        ‖projection (e 0) (e 1) (e 2) (e 3) f‖ ^ 2 -
        ‖projection (e 2) (e 3) (e 0) (e 1) f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {e 0,e 1} f,
        fluctuation n d {e 2,e 3} f⟫ := by
  have he (i j : Fin 4) (hij : i ≠ j) : e i ≠ e j :=
    fun h => hij (e.injective h)
  exact switch_interaction_of_affine_conditional_images
    (e 0) (e 1) (e 2) (e 3) (he 0 1 (by decide)) (he 2 3 (by decide))
    ⟨he 2 0 (by decide),he 2 1 (by decide)⟩
    ⟨he 3 0 (by decide),he 3 1 (by decide)⟩
    ⟨he 0 2 (by decide),he 0 3 (by decide)⟩
    ⟨he 1 2 (by decide),he 1 3 (by decide)⟩
    p hpa hpb (right_left_expectation_affine e)
    (left_right_expectation_affine e) f

theorem actual_named_interaction_oai (i j k l : Fin n) (h : FourDistinct i j k l)
    (f : StateSpace n d) :
    2 * ‖SwitchFlip.projection (CrossToggle.crossProposal i j k l h) f‖ ^ 2 -
        ‖projection i j k l f‖ ^ 2 - ‖projection k l i j f‖ ^ 2 ≤
      2 * ⟪fluctuation n d {i,j} f, fluctuation n d {k,l} f⟫ := by
  let e : Fin 4 ↪ Fin n :=
    ⟨![i,j,k,l], by
      rcases h with ⟨hij,hik,hil,hjk,hjl,hkl⟩
      intro x y hxy
      fin_cases x <;> fin_cases y <;>
        simp_all [Ne.symm hij, Ne.symm hik, Ne.symm hil,
          Ne.symm hjk, Ne.symm hjl, Ne.symm hkl]⟩
  exact actual_switch_interaction e (CrossToggle.crossProposal i j k l h)
    (CrossToggle.crossProposal_left i j k l h)
    (CrossToggle.crossProposal_right i j k l h) f

end Problem315.PairEquality

end

end OAI
end

theorem solution : type_of% @OAI.Problem315.PairEquality.actual_named_interaction_oai := @OAI.Problem315.PairEquality.actual_named_interaction_oai

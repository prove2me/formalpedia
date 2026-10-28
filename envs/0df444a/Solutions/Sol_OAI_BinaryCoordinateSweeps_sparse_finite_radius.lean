-- Prove2me | solution 1 for OAI.BinaryCoordinateSweeps.sparse_finite_radius
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T16:03:43.452502+00:00
-- url     : https://prove2.me/submissions/abc0887a-dc58-46b2-97cd-8b51d47d7a49

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000

section
-- module Solutions.OAIB3_Bsw.Compat
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_SumDite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
lemma sum_dite_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : ∀ x, P x → M) :
    (∑ x, if h : P x then f x h else 0) = ∑ x : {x // P x}, f x.val x.property := by
  classical
  have he := (Equiv.Set.sumCompl {x | P x}).sum_comp
    (fun x => if h : P x then f x h else 0)
  rw [Fintype.sum_sum_type] at he
  rw [← he]
  simp only [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inr]
  have hp : (∑ x : {x // P x}, if h : P x.val then f x.val h else 0) =
      ∑ x : {x // P x}, f x.val x.property := by
    apply Finset.sum_congr rfl
    intro x _
    exact dite_eq_left x.property
  have hn : (∑ x : {x // ¬P x}, if h : P x.val then f x.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact dite_eq_right x.property
  exact (congrArg₂ (· + ·) hp hn).trans (add_zero _)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_Basic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section FiniteProbability
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

lemma finiteLaw_nonneg (f : Ω → G) (g : G) : 0 ≤ finiteLaw f g := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma finiteLaw_sum [Nonempty Ω] (f : Ω → G) : ∑ g, finiteLaw f g = 1 := by
  classical
  simp only [finiteLaw]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

end FiniteProbability

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_GridSweepPath
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

theorem pathEvent_nonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    ∃ g : GridChoices bits, pathEvent H g := by
  classical
  let A (j : Fin b) (y : GridOutside bits j) :=
    {k : Fin h // (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i) = y}
  have hp (j : Fin b) (y : GridOutside bits j) :
      ∃ σ : Equiv.Perm (Slot (bits j)), ∀ k : A j y,
        σ (H.position j.castSucc k.val j) = H.position j.succ k.val j := by
    apply Equiv.Perm.exists_extending_pair
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.castSucc
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.succ
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · rw [H.changes_only_stage j k.val i hi, H.changes_only_stage j l.val i hi]
        exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
  choose g hg using hp
  refine ⟨g, ?_⟩
  intro j k
  apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
  simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
  apply Prod.ext
  · exact hg j _ ⟨k, rfl⟩
  · funext i
    exact (H.changes_only_stage j k i.val i.property).symm

lemma lineLaw_pos (d : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : Equiv.Perm (Slot d)) : 0 < lineLaw d z g := by
  have hu : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    exact inv_pos.mpr hc
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hz1) hu)
    (mul_nonneg hz (finiteLaw_nonneg (binarySweep d) g))

lemma gridWeight_pos {b : ℕ} (bits : Fin b → ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : GridChoices bits) : 0 < gridWeight bits z g := by
  apply Finset.prod_pos
  intro j _
  exact Finset.prod_pos (fun y _ => lineLaw_pos (bits j) hz hz1 (g j y))

theorem conditionalNormalizer_pos {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) : 0 < conditionalNormalizer H z := by
  classical
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  apply Finset.sum_pos'
  · intro g' _
    split_ifs
    · exact (gridWeight_pos bits hz hz1 g').le
    · exact le_rfl
  · exact ⟨g, Finset.mem_univ _, by simpa [hg] using gridWeight_pos bits hz hz1 g⟩

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_IndependentHistory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section Assignments
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [Fintype I]

lemma card_assignment_completions (A B : I ↪ X) :
    Fintype.card {σ : Equiv.Perm X // Assigns A B σ} =
      (Fintype.card X - Fintype.card I).factorial := by
  classical
  let eA := Equiv.ofInjective A A.injective
  let eB := Equiv.ofInjective B B.injective
  let e₀ : Set.range A ≃ Set.range B := eA.symm.trans eB
  have ha : Fintype.card (Set.range A) = Fintype.card I := Fintype.card_congr eA.symm
  have hb : Fintype.card (Set.range B) = Fintype.card I := Fintype.card_congr eB.symm
  let e : {σ : Equiv.Perm X // Assigns A B σ} ≃
      {σ : X ≃ X // ∀ x : Set.range A, σ x = e₀ x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro σ
      constructor
      · intro h x
        obtain ⟨i, hi⟩ := x.property
        have hx : x = eA i := Subtype.ext hi.symm
        rw [hx]
        simpa [e₀, eA, eB] using h i
      · intro h i
        simpa [e₀, eA, eB] using h (eA i))
  let c : ↥((Set.range A)ᶜ) ≃ ↥((Set.range B)ᶜ) := Fintype.equivOfCardEq (by
    change Fintype.card {x : X // x ∉ Set.range A} = Fintype.card {x : X // x ∉ Set.range B}
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, ha, hb])
  rw [Fintype.card_congr (e.trans (Equiv.Set.compl e₀)), Fintype.card_equiv c]
  change (Fintype.card {x : X // x ∉ Set.range A}).factorial = _
  rw [Fintype.card_subtype_compl, ha]

lemma uniform_assignment_probability (A B : I ↪ X) :
    (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  classical
  have hn : Fintype.card I ≤ Fintype.card X := Fintype.card_le_of_injective A A.injective
  have hcard : (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) =
      ((Fintype.card X - Fintype.card I).factorial : ℝ) := by
    exact_mod_cast card_assignment_completions A B
  have hsum : (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) *
        (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ := by
    simp [Fintype.card_subtype, Finset.sum_ite]
  rw [hsum, hcard, Fintype.card_perm,
    ← Nat.factorial_mul_descFactorial hn, Nat.cast_mul, mul_inv_rev]
  have hf : (((Fintype.card X - Fintype.card I).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (Fintype.card X - Fintype.card I))
  field_simp

end Assignments

lemma fallingCost_sum {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = ∑ j ∈ Finset.range u, Real.log ((m : ℝ) / (m - j : ℕ)) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hdf : (0 : ℝ) < m.descFactorial u := by exact_mod_cast (Nat.descFactorial_pos.mpr hu)
  have hdiff (j : ℕ) (hj : j ∈ Finset.range u) : (m - j : ℕ) ≠ 0 := by
    simp only [Finset.mem_range] at hj
    omega
  have hlog (j : ℕ) (hj : j ∈ Finset.range u) :
      Real.log ((m : ℝ) / (m - j : ℕ)) = Real.log m - Real.log (m - j : ℕ) :=
    Real.log_div hmp.ne' (by exact_mod_cast hdiff j hj)
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp.ne') hdf.ne', Real.log_pow,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod, Real.log_prod (fun j hj => by exact_mod_cast hdiff j hj)]
  rw [Finset.sum_congr rfl hlog, Finset.sum_sub_distrib]
  simp

lemma fallingCost_nonneg {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) : 0 ≤ fallingCost m u := by
  rw [fallingCost_sum hm hu]
  apply Finset.sum_nonneg
  intro j hj
  have hdiff : (0 : ℝ) < (m - j : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt ((Finset.mem_range.mp hj).trans_le hu))
  apply Real.log_nonneg
  exact (le_div_iff₀ hdiff).mpr (by simp)

lemma prefix_sum_le_of_full_sum_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) (f : ℕ → ℝ)
    (hf : ∀ i < u, ∀ j, u ≤ j → j < m → f i ≤ f j)
    (hfull : ∑ j ∈ Finset.range m, f j ≤ m) :
    ∑ j ∈ Finset.range u, f j ≤ u := by
  have hc : ((m : ℝ) - u) * (∑ i ∈ Finset.range u, f i) ≤
      (u : ℝ) * ∑ j ∈ Finset.Ico u m, f j := by
    calc
      _ = ∑ i ∈ Finset.range u, ∑ _j ∈ Finset.Ico u m, f i := by
        simp [Nat.cast_sub hu, Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f j := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hf i (Finset.mem_range.mp hi) j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      _ = _ := by simp
  have hsplit := Finset.sum_range_add_sum_Ico f hu
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hu0 : (0 : ℝ) ≤ u := by positivity
  nlinarith

lemma fallingCost_le {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) : fallingCost m u ≤ u := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hfull : fallingCost m m ≤ m := by
    have hst := Stirling.le_log_factorial_stirling hm.ne'
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    rw [fallingCost, Nat.descFactorial_self, Real.log_div (pow_ne_zero _ hmp.ne') (by positivity), Real.log_pow]
    linarith
  rw [fallingCost_sum hm hu]
  apply prefix_sum_le_of_full_sum_le hm hu
  · intro i hi j huj hjm
    apply Real.log_le_log
    · exact div_pos hmp (by exact_mod_cast Nat.sub_pos_of_lt (hi.trans_le hu))
    · apply div_le_div_of_nonneg_left hmp.le
      · exact_mod_cast Nat.sub_pos_of_lt hjm
      · exact_mod_cast Nat.sub_le_sub_left (hi.le.trans huj) m
  · rwa [← fallingCost_sum hm le_rfl]

attribute [local instance] Classical.propDecidable

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_AssignmentWeight
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section AssignmentWeights
attribute [local instance] Classical.propDecidable
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

omit [Fintype I] in
lemma assignmentWeight_mono (p q : Equiv.Perm X → ℝ)
    (hpq : ∀ σ, p σ ≤ q σ) (A B : I ↪ X) :
    assignmentWeight p A B ≤ assignmentWeight q A B := by
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · exact hpq σ
  · exact le_rfl

omit [Fintype I] in
lemma assignmentWeight_smul (p : Equiv.Perm X → ℝ) (c : ℝ) (A B : I ↪ X) :
    assignmentWeight (fun σ => c * p σ) A B = c * assignmentWeight p A B := by
  simp only [assignmentWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

lemma assignmentWeight_uniform (A B : I ↪ X) :
    assignmentWeight (fun _ => (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) A B =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ :=
  uniform_assignment_probability A B

lemma assignmentWeight_comparison {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) :
    (1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ ≤
      assignmentWeight p A B ∧
    assignmentWeight p A B ≤
      2 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  constructor
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono (fun _ => (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) p hl A B
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono p (fun _ => 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) hu A B

lemma assignmentWeight_ratio_le {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) :
    assignmentWeight p A' B' / assignmentWeight p A B ≤
      4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A A.injective)
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A' A'.injective)
  have hden := (assignmentWeight_comparison hl hu A B).1
  have hnum := (assignmentWeight_comparison hl hu A' B').2
  have hdp : 0 < assignmentWeight p A B :=
    lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr hi)) hden
  apply (div_le_iff₀ hdp).mpr
  calc
    _ ≤ 2 * (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)⁻¹ := hnum
    _ = (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) *
          ((1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

end AssignmentWeights

attribute [local instance] Classical.propDecidable

lemma lineHoles_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) (y : GridOutside bits j) : lineHoles H j y ≤ 2 ^ bits j := by
  simpa [lineHoles, Slot, Fintype.card_pi] using
    Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective

lemma sum_lineHoles {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) : ∑ y, lineHoles H j y = h := by
  classical
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun k : Fin h => (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i)))
  simpa only [Fintype.card_sigma, Fintype.card_fin, lineHoles] using hh

lemma pathCost_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    0 ≤ pathCost H := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro y _
  exact fallingCost_nonneg (by positivity) (lineHoles_le H j y)

lemma pathCost_le {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H ≤ (b : ℝ) * h := by
  calc
    pathCost H ≤ ∑ j : Fin b, ∑ y, (lineHoles H j y : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro y _
      exact fallingCost_le (by positivity) (lineHoles_le H j y)
    _ = _ := by simp only [← Nat.cast_sum, sum_lineHoles]; simp

lemma pathEvent_iff_assigns {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : pathEvent H g ↔
      ∀ (j : Fin b) (y : GridOutside bits j), Assigns (lineInput H j y) (lineOutput H j y) (g j y) := by
  constructor
  · intro hg j y k
    change g j y (H.position j.castSucc k.val j) = H.position j.succ k.val j
    have he := congrArg (fun x : GridSlot bits => x j) (hg j k.val)
    simpa only [gridLayer, Equiv.trans_apply, Equiv.piSplitAt_apply,
      Equiv.prodCongrLeft_apply, Equiv.piSplitAt_symm_apply, dite_true, eq_self,
      lineInput, lineOutput, Function.Embedding.coeFn_mk, k.property] using he
  · intro hg j k
    apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
    simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
    apply Prod.ext
    · exact hg j _ ⟨k, rfl⟩
    · funext i
      exact (H.changes_only_stage j k i.val i.property).symm

lemma finiteLaw_le_one {Ω G : Type*} [Fintype Ω] [Fintype G] [Nonempty Ω]
    (f : Ω → G) (g : G) : finiteLaw f g ≤ 1 := by
  calc
    _ ≤ ∑ x, finiteLaw f x := Finset.single_le_sum (fun x _ => finiteLaw_nonneg f x) (Finset.mem_univ _)
    _ = 1 := finiteLaw_sum f

lemma linePerturbationRadius_pos (r : ℕ) : 0 < linePerturbationRadius r := by
  unfold linePerturbationRadius
  positivity

lemma lineLaw_comparison (r d : ℕ) (hd : d ≤ 2 * r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) (g : Equiv.Perm (Slot d)) :
    (1 / 2 : ℝ) * uniformLaw (Equiv.Perm (Slot d)) g ≤ lineLaw d z g ∧
      lineLaw d z g ≤ 2 * uniformLaw (Equiv.Perm (Slot d)) g := by
  have hf1 : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  have hzp : z ≤ 1 / 2 := hzr.trans (by
    unfold linePerturbationRadius
    apply one_div_le_one_div_of_le (by norm_num)
    linarith)
  have hfd : (Fintype.card (Equiv.Perm (Slot d)) : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast (show Fintype.card (Equiv.Perm (Slot d)) ≤ (2 ^ (2 * r)).factorial from by
      simp only [Fintype.card_perm, Slot, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Nat.factorial_le (Nat.pow_le_pow_right (by norm_num) hd))
  have hup : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    positivity
  have hzU : z ≤ uniformLaw (Equiv.Perm (Slot d)) g := hzr.trans (by
    unfold linePerturbationRadius uniformLaw
    rw [one_div]
    apply inv_anti₀ (by exact_mod_cast Fintype.card_pos)
    linarith)
  have hB0 : 0 ≤ binaryLaw d g := finiteLaw_nonneg _ _
  have hB1 : binaryLaw d g ≤ 1 := finiteLaw_le_one _ _
  constructor
  · unfold lineLaw
    nlinarith
  · unfold lineLaw
    nlinarith [mul_le_mul_of_nonneg_left hB1 hz]

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_LocalPathWeight
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma fallingCost_formula {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = (u : ℝ) * Real.log m - Real.log (m.descFactorial u : ℕ) := by
  have hmp : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdf : (m.descFactorial u : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hu).ne'
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp) hdf, Real.log_pow]

lemma assignmentWeight_eq_of_card_eq {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (p : Equiv.Perm X → ℝ) (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i)
    (hcard : Fintype.card I = Fintype.card J) : assignmentWeight p A' B' = assignmentWeight p A B := by
  have hsur : Function.Surjective f := by
    by_contra hn
    have hc := Fintype.card_lt_of_injective_not_surjective f f.injective hn
    omega
  have he (σ : Equiv.Perm X) : Assigns A' B' σ ↔ Assigns A B σ := by
    constructor
    · intro hσ i
      simpa only [hA, hB] using hσ (f i)
    · intro hσ j
      obtain ⟨i, rfl⟩ := hsur j
      simpa only [hA, hB] using hσ i
  simp only [assignmentWeight, he]

lemma assignmentWeight_log_ratio_le {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (hm : 0 < Fintype.card X) {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i) :
    Real.log (assignmentWeight p A' B' / assignmentWeight p A B) ≤
      fallingCost (Fintype.card X) (Fintype.card J) - fallingCost (Fintype.card X) (Fintype.card I) -
        ((Fintype.card J : ℝ) - Fintype.card I) * Real.log (Fintype.card X) +
          Real.log 4 * ((Fintype.card J : ℝ) - Fintype.card I) := by
  have hI := Fintype.card_le_of_injective A A.injective
  have hJ := Fintype.card_le_of_injective A' A'.injective
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hI
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hJ
  have wi : 0 < assignmentWeight p A B := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A B).1
  have wj : 0 < assignmentWeight p A' B' := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A' B').1
  by_cases hc : Fintype.card I = Fintype.card J
  · rw [assignmentWeight_eq_of_card_eq p A B A' B' f hA hB hc, div_self wi.ne', Real.log_one, hc]
    simp
  · have hIJ := Fintype.card_le_of_injective f f.injective
    have hgap : (1 : ℝ) ≤ (Fintype.card J : ℝ) - Fintype.card I := by
      have hh : Fintype.card I + 1 ≤ Fintype.card J := by omega
      exact_mod_cast (show (1 : ℤ) ≤ (Fintype.card J : ℤ) - Fintype.card I from by omega)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤ Real.log (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
          (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) :=
        Real.log_le_log (div_pos wj wi) (assignmentWeight_ratio_le hl hu A B A' B')
      _ = Real.log 4 + Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) -
          Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
        rw [Real.log_div (by positivity) hj.ne', Real.log_mul (by norm_num) hi.ne']
      _ ≤ _ := by
        rw [fallingCost_formula hm hI, fallingCost_formula hm hJ]
        nlinarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_Placement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma conditionalWeight_factor {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g else 0) =
      ∏ j, ∏ y, if Assigns (lineInput H j y) (lineOutput H j y) (g j y) then
        lineLaw (bits j) z (g j y) else 0 := by
  classical
  rw [pathEvent_iff_assigns]
  simp only [Fintype.prod_ite_zero]
  split_ifs <;> rfl

lemma sum_prod_grid {b : ℕ} (bits : Fin b → ℕ)
    (f : ∀ j : Fin b, GridOutside bits j → Equiv.Perm (Slot (bits j)) → ℝ) :
    (∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y)) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
  rw [← Fintype.prod_sum (fun (j : Fin b)
    (g : GridOutside bits j → Equiv.Perm (Slot (bits j))) => ∏ y, f j y (g y))]
  apply Finset.prod_congr rfl
  intro j _
  exact (Fintype.prod_sum (f j)).symm

lemma conditionalNormalizer_eq_prod {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) : conditionalNormalizer H z = ∏ j, ∏ y, localPathWeight H z j y := by
  let f (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) : ℝ :=
    if Assigns (lineInput H j y) (lineOutput H j y) σ then lineLaw (bits j) z σ else 0
  have hL : conditionalNormalizer H z =
      ∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y) := by
    unfold conditionalNormalizer
    apply Finset.sum_congr rfl
    intro g _
    rw [conditionalWeight_factor]
  have hR : (∏ j, ∏ y, localPathWeight H z j y) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro y _
    unfold localPathWeight assignmentWeight
    refine Finset.sum_congr ?_ ?_
    · ext σ
      simp only [Finset.mem_univ]
    intro σ _
    unfold f
    split_ifs <;> rfl
  rw [hL, hR]
  exact sum_prod_grid bits f

instance conditionalChoicesNonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    Nonempty (ConditionalChoices H) := by
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  exact ⟨⟨g, hg⟩⟩

lemma conditionalChoiceWeight_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (g : ConditionalChoices H) :
    0 ≤ conditionalChoiceWeight H z g :=
  le_of_lt (div_pos (gridWeight_pos bits hz hz1 g.val) (conditionalNormalizer_pos H hz hz1))

section FiniteBijectionKernel
variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma bijectionKernel_nonneg (w : Ω → ℝ) (e : Ω → A ≃ B)
    (hw : ∀ ω, 0 ≤ w ω) (x : A) (y : B) : 0 ≤ bijectionKernel w e x y := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_rfl

end FiniteBijectionKernel

lemma placementProbability_eq_kernel {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    placementProbability H z x y =
      bijectionKernel (conditionalChoiceWeight H z) (placementBijection H k) x y := by
  unfold placementProbability bijectionKernel
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> rfl

lemma placementProbability_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    0 ≤ placementProbability H z x y := by
  rw [placementProbability_eq_kernel]
  exact bijectionKernel_nonneg _ _ (conditionalChoiceWeight_nonneg H hz hz1) x y

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathExtension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

namespace PathExtension
variable {b h h' : ℕ} {bits : Fin b → ℕ}
  {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma lineInput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineInput H' j y (E.lineEmbedding j y i) = lineInput H j y i := by
  change H'.position j.castSucc (E.labels i.val) j = H.position j.castSucc i.val j
  rw [E.position_eq]

lemma lineOutput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineOutput H' j y (E.lineEmbedding j y i) = lineOutput H j y i := by
  change H'.position j.succ (E.labels i.val) j = H.position j.succ i.val j
  rw [E.position_eq]

end PathExtension

lemma localPathWeight_pos_comparison {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) : 0 < localPathWeight H z j y := by
  unfold localPathWeight
  have hw := @assignmentWeight_comparison (Slot (bits j)) (LinePaths H j y) _ _
    (lineLaw (bits j) z) ?_ ?_ (lineInput H j y) (lineOutput H j y)
  · have hm : 0 < (Nat.descFactorial (Fintype.card (Slot (bits j)))
        (Fintype.card (LinePaths H j y)) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr
        (Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective)
    exact lt_of_lt_of_le (by positivity) hw.1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma lineExtension_log_bound {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) :
    Real.log (localPathWeight H' z j y / localPathWeight H z j y) ≤
      fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
      ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
      Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y) := by
  have he := @assignmentWeight_log_ratio_le (Slot (bits j)) (LinePaths H j y)
    (LinePaths H' j y) _ _ _ Fintype.card_pos (lineLaw (bits j) z)
    ?_ ?_ (lineInput H j y) (lineOutput H j y) (lineInput H' j y) (lineOutput H' j y)
      (E.lineEmbedding j y) (E.lineInput_eq j y) (E.lineOutput_eq j y)
  · simpa only [localPathWeight, lineHoles, Slot, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool] using he
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma log_gridSize {b : ℕ} (bits : Fin b → ℕ) :
    Real.log (gridSize bits : ℝ) = ∑ j, Real.log (2^bits j : ℕ) := by
  unfold gridSize
  rw [Nat.cast_prod, Real.log_prod]
  intro j _
  positivity

lemma sum_lineHoles_sub {b h h' : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (H' : PathFamily bits h') (j : Fin b) :
    ∑ y : GridOutside bits j, ((lineHoles H' j y : ℝ) - lineHoles H j y) = (h' : ℝ) - h := by
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, sum_lineHoles, sum_lineHoles]

lemma pathCost_eq_sum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H = ∑ j, ∑ y, fallingCost (2^bits j) (lineHoles H j y) := rfl

theorem pathExtension_log_ratio {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    Real.log (conditionalNormalizer H' z / conditionalNormalizer H z) ≤
      pathCost H' - pathCost H - ((h' : ℝ) - h) * Real.log (gridSize bits) +
        Real.log 4 * ((h' : ℝ) - h) * b := by
  have hposH := localPathWeight_pos_comparison H hd hz hzr
  have hposH' := localPathWeight_pos_comparison H' hd hz hzr
  rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
  rw [← Finset.prod_div_distrib]
  simp_rw [← Finset.prod_div_distrib]
  rw [Real.log_prod (fun j _ => Finset.prod_ne_zero_iff.mpr (fun y _ =>
    (div_pos (hposH' j y) (hposH j y)).ne'))]
  simp_rw [Real.log_prod (fun y _ => (div_pos (hposH' _ y) (hposH _ y)).ne')]
  calc
    _ ≤ ∑ j, ∑ y,
        (fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
        ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
        Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y)) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun y _ => lineExtension_log_bound E hd hz hzr j y)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
      simp_rw [sum_lineHoles_sub]
      rw [pathCost_eq_sum, pathCost_eq_sum, log_gridSize]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring

lemma pathExtension_event_ratio {b h h' : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H') (z : ℝ) :
    conditionalEventWeight H z (pathEvent H') =
      conditionalNormalizer H' z / conditionalNormalizer H z := by
  unfold conditionalEventWeight conditionalChoiceWeight
  have hdiv (g : ConditionalChoices H) :
      (if pathEvent H' g.val then gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (if pathEvent H' g.val then gridWeight bits z g.val else 0) / conditionalNormalizer H z := by
    split_ifs <;> simp only [zero_div]
  simp_rw [hdiv]
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter (pathEvent H)) (by simp)
    (fun g => if pathEvent H' g then gridWeight bits z g else 0)]
  rw [Finset.sum_filter]
  unfold conditionalNormalizer
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : pathEvent H' g
  · simp only [hg, E.pathEvent_mono hg, ite_true]
  · simp only [hg, ite_false, ite_self]

lemma gridSize_pos {b : ℕ} (bits : Fin b → ℕ) : 0 < gridSize bits := by
  unfold gridSize
  exact Finset.prod_pos (fun j _ => Nat.pow_pos (by norm_num))

theorem pathExtension_probability_bound {b h k r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits (h+k)} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    conditionalEventWeight H z (pathEvent H') ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost H' - pathCost H + Real.log 4 * k * b) := by
  rw [pathExtension_event_ratio E]
  have hp : 0 < conditionalNormalizer H' z / conditionalNormalizer H z := by
    rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
    apply div_pos <;> apply Finset.prod_pos <;> intro j _ <;>
      apply Finset.prod_pos <;> intro y _
    · exact localPathWeight_pos_comparison H' hd hz hzr j y
    · exact localPathWeight_pos_comparison H hd hz hzr j y
  have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have he := pathExtension_log_ratio E hd hz hzr
  simp only [Nat.cast_add, add_sub_cancel_left] at he
  calc
    _ ≤ Real.exp (pathCost H' - pathCost H - (k : ℝ) * Real.log (gridSize bits) +
        Real.log 4 * k * b) := (Real.log_le_iff_le_exp hp).mp he
    _ = _ := by
      rw [Real.rpow_def_of_pos hs, ← Real.exp_add]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ComplementBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h h' : ℕ} {bits : Fin b → ℕ}
variable {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma PathExtension.sum_restrict {V : Type*} [AddCommMonoid V]
    (E : PathExtension H H') (f : ConditionalChoices H' → V) :
    (∑g : ConditionalChoices H,
      if hg : pathEvent H' g.val then f ⟨g.val,hg⟩ else 0) =
      ∑g : ConditionalChoices H',f g := by
  have hL := sum_dite_zero (pathEvent H)
    (fun (g : GridChoices bits) (_ : pathEvent H g) =>
      if hg' : pathEvent H' g then f ⟨g,hg'⟩ else 0)
  have hR := sum_dite_zero (pathEvent H') (fun g hg => f ⟨g,hg⟩)
  refine Eq.trans ?_ (Eq.trans hL.symm (Eq.trans ?_ (Eq.trans hR ?_)))
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hg : pathEvent H' g
    · simp only [hg,E.pathEvent_mono hg,dite_eq_left]
    · simp [hg]
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_Trajectory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma placementProbability_augmentation {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) =
      conditionalEventWeight H z (pathEvent (augmentByChoice H x g)) := by
  unfold placementProbability conditionalEventWeight
  apply Finset.sum_congr rfl
  intro g' _
  simp only [placementEvent_iff_augmentation]

theorem placement_probability_cost {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost (augmentByChoice H x g) - pathCost H + Real.log 4 * k * b) := by
  rw [placementProbability_augmentation]
  exact pathExtension_probability_bound (augmentByChoice_extension H x g) hd hz hzr

lemma realizePlacement_spec {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementBijection H k (realizePlacement H z x y hp) x = y :=
  Classical.choose_spec (placementProbability_pos_has_choice H z x y hp)

theorem placement_probability_cost_of_pos {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementProbability H z x y ≤ (gridSize bits : ℝ) ^ (-(k : ℝ)) *
      Real.exp (placementTransitionCost H z x y - pathCost H + Real.log 4 * k * b) := by
  have he := placement_probability_cost H hd hz hzr x (realizePlacement H z x y hp)
  unfold placementTransitionCost
  rw [dite_eq_left hp]
  rwa [realizePlacement_spec] at he

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_FiniteProductProbability
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

omit [DecidableEq I] [Fintype Ω] in
lemma productWeight_nonneg {p : Ω → ℝ} (hp : ∀ u, 0 ≤ p u) (x : I → Ω) :
    0 ≤ productWeight p x := Finset.prod_nonneg (fun i _ => hp (x i))

lemma productWeight_sum (p : Ω → ℝ) (hp : ∑ u, p u = 1) :
    ∑ x : I → Ω, productWeight p x = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  simp [hp]

omit [DecidableEq I] in
lemma indicator_prod (P : I → Prop) :
    (∏ i, (if P i then (1:ℝ) else 0)) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq I] [Fintype Ω] in
lemma productWeight_split (p : Ω → ℝ) (T : I → Prop) [DecidablePred T]
    (u : {i // T i} → Ω) (v : {i // ¬ T i} → Ω) :
    productWeight p ((Equiv.piEquivPiSubtypeProd T (fun _ => Ω)).symm (u,v)) =
      productWeight p u * productWeight p v := by
  unfold productWeight
  rw [← Fintype.prod_subtype_mul_prod_subtype T]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply,i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp [Equiv.piEquivPiSubtypeProd_symm_apply,i.property]

lemma productProbability_mono {p : Ω → ℝ} (hp : ∀ u, 0 ≤ p u)
    {E F : (I → Ω) → Prop} (h : ∀ x, E x → F x) :
    productProbability p E ≤ productProbability p F := by
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg hp x)
  by_cases hx : E x
  · simp [hx,h x hx]
  · simp [hx]; split_ifs <;> norm_num

lemma productProbability_union_le {J : Type*} [Fintype J] {p : Ω → ℝ}
    (hp : ∀ u, 0 ≤ p u) (E : J → (I → Ω) → Prop) :
    productProbability p (fun x => ∃ j, E j x) ≤ ∑ j, productProbability p (E j) := by
  unfold productProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (productWeight_nonneg hp x)
  by_cases h : ∃ j, E j x
  · obtain ⟨j,hj⟩ := h
    rw [ite_eq_left ⟨j,hj⟩]
    exact (show (1:ℝ) ≤ if E j x then 1 else 0 by simp [hj]).trans
      (Finset.single_le_sum (f:=fun i:J => if E i x then (1:ℝ) else 0) (fun i _ => by split_ifs <;> norm_num) (Finset.mem_univ j))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

theorem depthOne_probability_le {H : Type*} [Fintype H]
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1)
    (R : Ω → Ω → Prop) (ω : ℝ) (_hω : 0 ≤ ω)
    (hR : ∀ v, (∑ u, p u * (if R u v then 1 else 0)) ≤ ω)
    (T : Finset I) (f : T → {i // i ∉ T} ⊕ H) (roots : H → Ω) :
    productProbability p (fun x : I → Ω => ∀ i : T, R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots)) ≤
      ω^T.card := by
  classical
  let : Fintype T := Subtype.fintype (fun i => i ∈ T)
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ T) (fun _ => Ω)
  unfold productProbability
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  have he (u : T → Ω) (v : {i // i ∉ T} → Ω) (i : T) :
      R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots) ↔
        R (u i) ((f i).elim v roots) := by
    cases hf : f i with
    | inl j => simp [e,Equiv.piEquivPiSubtypeProd_symm_apply,i.property,j.property]
    | inr h => simp [e,Equiv.piEquivPiSubtypeProd_symm_apply,i.property]
  change (∑ v : {i // i ∉ T} → Ω, ∑ u : T → Ω,
    productWeight p (e.symm (u,v)) * _) ≤ _
  have hsplit (u : T → Ω) (v : {i // i ∉ T} → Ω) :
      productWeight p (e.symm (u,v)) = productWeight p u * productWeight p v := by
    exact productWeight_split p (fun i => i ∈ T) u v
  simp_rw [hsplit]
  have ht (v : {i // i ∉ T} → Ω) :
      (∑ u : T → Ω, productWeight p u *
        (if ∀ i : T, R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots)
          then 1 else 0)) ≤ ω^T.card := by
    simp_rw [he,← indicator_prod,productWeight,← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (i : T) (u : Ω) => p u * (if R u ((f i).elim v roots) then 1 else 0))]
    simpa using Finset.prod_le_prod (s:=Finset.univ) (fun i _ => Finset.sum_nonneg (fun u _ =>
      mul_nonneg (hp u) (by split_ifs <;> norm_num))) (fun i _ => hR ((f i).elim v roots))
  calc
    _ = ∑ v : {i // i ∉ T} → Ω, productWeight p v *
        (∑ u : T → Ω, productWeight p u *
          (if ∀ i : T, R (e.symm (u,v) i) ((f i).elim (fun j : {i // i ∉ T} => e.symm (u,v) j.val) roots)
            then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc, mul_left_comm]
      congr 2
      simp only [he]
    _ ≤ ∑ v : {i // i ∉ T} → Ω, productWeight p v * ω^T.card :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (ht v) (productWeight_nonneg hp v))
    _ = ω^T.card := by rw [← Finset.sum_mul,productWeight_sum p hp1,one_mul]

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_SharingWitness
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I H : Type*} [Fintype I] [Fintype H] [DecidableEq I]

theorem sharing_witness (G : SimpleGraph I) (R : I → H → Prop) :
    let S := Finset.univ.filter (fun i => (∃ j, G.Adj i j) ∨ ∃ h, R i h)
    ∃ T : Finset I, T ⊆ S ∧ S.card ≤ 2*T.card ∧
      ∀ i ∈ T, (∃ j, j ∉ T ∧ G.Adj i j) ∨ ∃ h, R i h := by
  classical
  intro S
  obtain ⟨A,hA⟩ := G.maximumIndepSet_exists
  have hm := hA.isMaximalIndepSet A
  have hi := (G.isIndepSet_iff).mp hm.1
  have hn (i : I) (hiA : i ∉ A) : ∃ j ∈ A, G.Adj i j := by
    by_contra! h
    have hins : G.IsIndepSet (insert i (A : Set I)) := by
      apply G.isIndepSet_iff.mpr
      intro x hx y hy hxy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact h y hy
      · exact fun hadj => h x hx hadj.symm
      · exact hi hx hy hxy
    have hj := hm.2 hins (Set.subset_insert i (A : Set I)) (Set.mem_insert i (A : Set I))
    exact hiA hj
  have hcard := Finset.card_sdiff_add_card_inter S A
  by_cases hc : (S \ A).card ≤ (S ∩ A).card
  · refine ⟨S ∩ A,Finset.inter_subset_left,by omega,?_⟩
    intro i hiT
    obtain ⟨hiS, hiA⟩ := Finset.mem_inter.mp hiT
    obtain hiS | hiS := (Finset.mem_filter.mp hiS).2
    · obtain ⟨j,hij⟩ := hiS
      refine Or.inl ⟨j,?_,hij⟩
      intro hj
      exact hi hiA (Finset.mem_inter.mp hj).2 (G.ne_of_adj hij) hij
    · exact Or.inr hiS
  · refine ⟨S \ A,Finset.sdiff_subset,by omega,?_⟩
    intro i hiT
    obtain ⟨j,hj,hij⟩ := hn i (Finset.mem_sdiff.mp hiT).2
    exact Or.inl ⟨j,fun hjT => (Finset.mem_sdiff.mp hjT).2 hj,hij⟩

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_SharingProbability
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I H Ω : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype Ω]

omit [Fintype Ω] in
lemma sharing_depthOne (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first)
    (roots : H → Ω) (x : I → Ω) (w : ℕ) (hw : w ≤ (incidentSet R roots x).card) :
    ∃ T : Finset I, w ≤ 2*T.card ∧
      ∃ f : T → {i // i ∉ T} ⊕ H, ∀ i : T,
        R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots) := by
  classical
  obtain ⟨T,_,hc,hT⟩ := sharing_witness (sharingGraph R hs x) (fun i h => R (x i) (roots h))
  have hc' : (incidentSet R roots x).card ≤ 2*T.card := by
    convert hc using 1
    congr 1
    ext i
    simp only [incidentSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

  refine ⟨T,hw.trans hc',?_⟩
  have hp (i : T) : ∃ a : {i // i ∉ T} ⊕ H,
      R (x i) (a.elim (fun j : {i // i ∉ T} => x j.val) roots) := by
    obtain ⟨j,hj,hij⟩ | ⟨h,hi⟩ := hT i i.property
    · exact ⟨Sum.inl ⟨j,hj⟩,hij.2⟩
    · exact ⟨Sum.inr h,hi⟩
  choose f hf using hp
  exact ⟨f,hf⟩

theorem sharing_probability_le
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (hp1 : ∑ u, p u = 1)
    (R : Ω → Ω → Prop)
    (hs : ∀ ⦃first second⦄, R first second → R second first) (roots : H → Ω)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hR : ∀ v, (∑ u, p u * (if R u v then 1 else 0)) ≤ ω)
    (w : ℕ) (hsmall : ((Fintype.card I + Fintype.card H : ℕ) : ℝ)*ω ≤ 1) :
    productProbability p (fun x : I → Ω => w ≤ (incidentSet R roots x).card) ≤
      (2:ℝ)^Fintype.card I *
        (((Fintype.card I + Fintype.card H : ℕ):ℝ)*ω)^((w+1)/2) := by
  classical
  let E (T : Finset I) (f : T → {i // i ∉ T} ⊕ H) (x : I → Ω) :=
    ∀ i : T, R (x i) ((f i).elim (fun j : {i // i ∉ T} => x j.val) roots)
  let r : ℝ := ((Fintype.card I + Fintype.card H : ℕ):ℝ)*ω
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) hω
  have hT (T : Finset I) : productProbability p (fun x => w ≤ 2*T.card ∧ ∃ f, E T f x) ≤
      r^((w+1)/2) := by
    by_cases hc : w ≤ 2*T.card
    · have h1 := productProbability_union_le hp (E T)
      have h2 : (∑ f, productProbability p (E T f)) ≤
          (Fintype.card (T → {i // i ∉ T} ⊕ H) : ℝ)*ω^T.card := by
        simpa [E] using Finset.sum_le_sum (s:=Finset.univ) (fun f _ => depthOne_probability_le p hp hp1 R ω hω hR T f roots)
      have hd : Fintype.card ({i // i ∉ T} ⊕ H) ≤ Fintype.card I + Fintype.card H := by
        rw [Fintype.card_sum]
        exact Nat.add_le_add_right (Fintype.card_subtype_le _) _
      have h3 : (Fintype.card (T → {i // i ∉ T} ⊕ H) : ℝ)*ω^T.card ≤ r^T.card := by
        rw [Fintype.card_fun,Fintype.card_coe,Nat.cast_pow]
        dsimp [r]
        rw [mul_pow]
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hω _)
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hd) _
      have he : (w+1)/2 ≤ T.card := by omega
      simpa only [hc,true_and] using h1.trans (h2.trans (h3.trans
        (pow_le_pow_of_le_one hr hsmall he)))
    · simp only [hc,false_and,productProbability,ite_false,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hr _
  calc
    _ ≤ productProbability p (fun x => ∃ T : Finset I, w ≤ 2*T.card ∧ ∃ f, E T f x) :=
      productProbability_mono hp (fun x hx => sharing_depthOne R hs roots x w hx)
    _ ≤ ∑ T : Finset I, productProbability p (fun x => w ≤ 2*T.card ∧ ∃ f, E T f x) :=
      productProbability_union_le hp _
    _ ≤ ∑ T : Finset I, r^((w+1)/2) := Finset.sum_le_sum (fun T _ => hT T)
    _ = _ := by simp [r,Fintype.card_finset]

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_UniformFiniteProbability
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {Ω V W : Type*} [Fintype Ω] [Fintype V] [Fintype W]

lemma uniformWeight_nonneg (u : Ω) : 0 ≤ uniformWeight u := by
  unfold uniformWeight; positivity

lemma uniformWeight_sum [Nonempty Ω] : ∑ u : Ω, uniformWeight u = 1 := by
  simp [uniformWeight,ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω)]

lemma finiteProbability_union {T : Type*} [Fintype T]
    (p : Ω → ℝ) (hp : ∀ u, 0 ≤ p u) (E : T → Ω → Prop) :
    finiteProbability p (fun u => ∃ t, E t u) ≤ ∑ t, finiteProbability p (E t) := by
  unfold finiteProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (hp u)
  by_cases h : ∃ t, E t u
  · obtain ⟨t,ht⟩ := h
    rw [ite_eq_left ⟨t,ht⟩]
    exact (show (1:ℝ) ≤ if E t u then 1 else 0 by simp [ht]).trans
      (Finset.single_le_sum (f:=fun t:T => if E t u then (1:ℝ) else 0)
        (fun t _ => by split_ifs <;> norm_num) (Finset.mem_univ t))
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun t _ => by split_ifs <;> norm_num)

lemma uniform_projection_probability [Nonempty W] (e : Ω ≃ V × W) (v : V) :
    finiteProbability uniformWeight (fun u => (e u).1 = v) = 1 / Fintype.card V := by
  classical
  unfold finiteProbability uniformWeight
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type,Fintype.card_congr e,Fintype.card_prod]
  have hW : (Fintype.card W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  simp [Nat.cast_mul]

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
namespace Sparse
variable {b : ℕ} {bits : Fin b → ℕ}

lemma independentPosition_changes (z : GridSlot bits × GridSlot bits) (j i : Fin b) (h : i≠j) :
    independentPosition z j.succ i=independentPosition z j.castSucc i := by
  have hn : i.val≠j.val := fun he => h (Fin.ext he)
  simp only [independentPosition,Fin.val_succ,Fin.val_castSucc]
  have he : i.val<j.val+1 ↔ i.val<j.val := by omega
  simp only [he]

lemma independentPosition_of_path (x : Fin (b+1) → GridSlot bits)
    (h : ∀(j i : Fin b), i≠j → x j.succ i=x j.castSucc i) (t : Fin (b+1)) :
    independentPosition (x 0,x (Fin.last b)) t=x t := by
  funext i
  exact (trajectory_coordinates x h t i).symm

lemma independentPosition_uniform (t : Fin (b+1)) (v : GridSlot bits) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      independentPosition z t=v)=1/gridSize bits := by
  have hh := uniform_projection_probability (endpointSwap (bits:=bits) t) v
  convert hh using 1 <;> simp only [endpointSwap,Equiv.coe_fn_mk,card_gridSlot]

lemma shareVertex_symmetric :
    ∀ ⦃first second⦄, shareVertex (bits:=bits) first second → shareVertex second first := by
  rintro z w ⟨t,ht⟩
  exact ⟨t,ht.symm⟩

lemma shareVertex_probability (w : GridSlot bits × GridSlot bits) :
    finiteProbability uniformWeight (fun z => shareVertex (bits:=bits) z w) ≤
      (b+1:ℝ)/gridSize bits := by
  have hh := finiteProbability_union uniformWeight uniformWeight_nonneg
    (fun (t : Fin (b+1)) (z : GridSlot bits × GridSlot bits) =>
      independentPosition z t=independentPosition w t)
  simp_rw [independentPosition_uniform] at hh
  simpa only [shareVertex,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_add,Nat.cast_one,mul_one_div] using hh

theorem independent_trajectory_sharing {k h : ℕ}
    (roots : Fin h → GridSlot bits × GridSlot bits) (w : ℕ)
    (hs : ((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits) ≤ 1) :
    productProbability uniformWeight (fun z : Fin k → GridSlot bits × GridSlot bits =>
      w ≤ (incidentSet shareVertex roots z).card) ≤
      (2:ℝ)^k * (((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((w+1)/2) := by
  have hh := sharing_probability_le (I:=Fin k) uniformWeight uniformWeight_nonneg uniformWeight_sum
    shareVertex shareVertex_symmetric roots ((b+1:ℝ)/gridSize bits) (by positivity)
    (fun v => shareVertex_probability v) w (by simpa only [Fintype.card_fin] using hs)
  simpa only [Fintype.card_fin] using hh

lemma independent_line_uniform (j : Fin b) (y : GridOutside bits j) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      (fun i : {i : Fin b // i≠j} => independentPosition z j.castSucc i)=y)=
      1/Fintype.card (GridOutside bits j) := by
  exact uniform_projection_probability (endpointLineEquiv j) y

lemma finiteProbability_mem {Ω L : Type*} [Fintype Ω] [Fintype L] [DecidableEq L]
    (p : Ω → ℝ) (f : Ω → L) (S : Finset L) :
    finiteProbability p (fun u => f u∈S)=∑l∈S, finiteProbability p (fun u => f u=l) := by
  unfold finiteProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.mul_sum]
  congr 1
  simp only [eq_comm,Finset.sum_ite_eq']
  by_cases h : f u∈S <;> simp only [h,ite_true,ite_false]

lemma independent_line_set_uniform (j : Fin b) (S : Finset (GridOutside bits j)) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      (fun i : {i : Fin b // i≠j} => independentPosition z j.castSucc i)∈S)=
      S.card/Fintype.card (GridOutside bits j) := by
  rw [finiteProbability_mem]
  simp_rw [independent_line_uniform]
  simp [div_eq_mul_inv]

end Sparse
end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointEvents
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open Sparse

variable {b h : ℕ} {bits : Fin b → ℕ}

lemma endpoint_gridLayer_iff (g : GridChoices bits) (e : GridSlot bits × GridSlot bits) (j : Fin b) :
    gridLayer bits g j (independentPosition e j.castSucc)=independentPosition e j.succ ↔
      g j (endpointLine e j) (e.1 j)=e.2 j := by
  unfold endpointLine
  constructor
  · intro he
    have hh := congrFun he j
    simpa only [gridLayer_at,endpointLine,independentPosition,Fin.val_castSucc,
      Fin.val_succ,lt_self_iff_false,ite_false,Nat.lt_succ_self,ite_true] using hh
  · intro he
    funext i
    by_cases hi : i=j
    · subst i
      simpa only [gridLayer_at,endpointLine,independentPosition,Fin.val_castSucc,
        Fin.val_succ,lt_self_iff_false,ite_false,Nat.lt_succ_self,ite_true] using he
    · rw [gridLayer_other bits g j i hi]
      exact (independentPosition_changes e j i hi).symm

lemma gridSweep_endpoint_iff (g : GridChoices bits) (e : GridSlot bits × GridSlot bits) :
    gridSweep bits g e.1=e.2 ↔ ∀j, g j (endpointLine e j) (e.1 j)=e.2 j := by
  constructor
  · intro he j
    have hp (t : Fin (b+1)) : gridPartialSweep bits g t e.1=independentPosition e t := by
      have hh := independentPosition_of_path (fun t => gridPartialSweep bits g t e.1)
        (gridPartialSweep_changes bits g e.1) t
      simpa only [gridPartialSweep_zero,Equiv.Perm.one_apply,gridPartialSweep_last,he] using hh.symm
    apply (endpoint_gridLayer_iff g e j).mp
    rw [← hp j.castSucc,← hp j.succ,gridPartialSweep_succ,Equiv.Perm.mul_apply]
  · intro he
    have hh := chronological_trajectory b (gridLayer bits g) (independentPosition e)
      (fun j => (endpoint_gridLayer_iff g e j).mpr (he j))
    simpa only [independentPosition_zero,independentPosition_last,gridSweep] using hh

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma restrictPlacement_event (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (A : Finset (Fin k)) (g : ConditionalChoices H) :
    placementBijection H (Fintype.card A) g (restrictPlacement H x A)=restrictPlacement H y A ↔
      ∀i ∈ A, gridSweep bits g.val (x i).val=(y i).val := by
  constructor
  · intro he i hi
    have hh := congrArg (fun q => (q (Fintype.equivFin A ⟨i,hi⟩)).val) he
    change gridSweep bits g.val (x ((Fintype.equivFin A).symm
      (Fintype.equivFin A ⟨i,hi⟩)).val).val =
      (y ((Fintype.equivFin A).symm (Fintype.equivFin A ⟨i,hi⟩)).val).val at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · intro he
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact he _ ((Fintype.equivFin A).symm i).property

lemma endpointProbability_conditional {I : Type*} [Fintype I] [DecidableEq I]
    (z : ℝ) (A : Finset I) (e : I → GridSlot bits × GridSlot bits) :
    endpointProbability H z A e =
      conditionalEventWeight H z (fun g => ∀i ∈ A, gridSweep bits g (e i).1=(e i).2) := by
  unfold endpointProbability endpointMass conditionalEventWeight conditionalChoiceWeight
  have hh (g : ConditionalChoices H) :
      (if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then gridWeight bits z g.val else 0) /
        conditionalNormalizer H z := by split_ifs <;> simp
  have hR : (∑g : ConditionalChoices H,
      if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (∑g : ConditionalChoices H, if ∀i ∈ A, gridSweep bits g.val (e i).1=(e i).2 then
        gridWeight bits z g.val else 0) / conditionalNormalizer H z := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    exact hh g
  refine Eq.trans ?_ (Eq.trans hR.symm ?_)
  · congr 1
    have hs := sum_dite_zero (pathEvent H) (fun g _ =>
      if ∀i ∈ A, gridSweep bits g (e i).1=(e i).2 then gridWeight bits z g else 0)
    refine Eq.trans ?_ (hs.trans ?_)
    · apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp_all
    · apply Finset.sum_congr (by ext sample; simp)
      intro g _
      rfl
  · apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> rfl

theorem endpointProbability_placement (z : ℝ)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    endpointProbability H z A (fun i => ((x i).val,(y i).val)) =
      placementProbability H z (restrictPlacement H x A) (restrictPlacement H y A) := by
  rw [endpointProbability_conditional]
  unfold conditionalEventWeight placementProbability
  apply Finset.sum_congr rfl
  intro g _
  simp only [restrictPlacement_event]
  split_ifs <;> rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_ConditionalCentered
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Sparse

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma conditionalGroupLaw_expectation {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (z : ℝ) (f : Equiv.Perm (FreeSlot H 0) → W) :
    (∑a, conditionalGroupLaw H z a • f a) =
      ∑g : ConditionalChoices H, conditionalChoiceWeight H z g • f (remainingPerm H g.val g.property) := by
  unfold conditionalGroupLaw
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [ite_smul,zero_smul]
  simp

lemma partialKernel_event (g : ConditionalChoices H) (A : Finset (Fin k))
    (x y : Placement H k 0) :
    subPlacement A (movePlacement (remainingPerm H g.val g.property) x)=subPlacement A y ↔
      ∀i∈A, gridSweep bits g.val (x i).val=((placementIdentification H k y i).val) := by
  constructor
  · intro he i hi
    have hh := congrArg (fun u => u ⟨i,hi⟩) he
    have he' : remainingPerm H g.val g.property (x i)=y i := hh
    have ht := congrArg (freeIdentification H) he'
    change (freeIdentification H) ((freeIdentification H).symm
      (remainingBijection H g.val g.property (x i)))=(freeIdentification H) (y i) at ht
    rw [Equiv.apply_symm_apply] at ht
    exact congrArg Subtype.val ht
  · intro he
    apply Function.Embedding.ext
    intro i
    change (freeIdentification H).symm (remainingBijection H g.val g.property (x i.val))=y i.val
    apply (freeIdentification H).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact he i.val i.property

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseAmplitude
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma placementProbability_uniform_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    (gridSize bits : ℝ)^k * placementProbability H z x y ≤
      Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hp := placementProbability_nonneg H hz hz1 x y
  by_cases hp0 : placementProbability H z x y=0
  · rw [hp0,mul_zero]; exact (Real.exp_pos _).le
  have hp' : 0<placementProbability H z x y := lt_of_le_of_ne hp (Ne.symm hp0)
  have hb := placement_probability_cost_of_pos H hd hz hzr x y hp'
  have hc : placementTransitionCost H z x y ≤ (b:ℝ)*(h+k) := by
    unfold placementTransitionCost
    rw [dite_eq_left hp']
    simpa only [Nat.cast_add] using pathCost_le
      (augmentByChoice H x (realizePlacement H z x y hp'))
  have hpow : (gridSize bits:ℝ)^k * (gridSize bits:ℝ)^(-(k:ℝ))=1 := by
    rw [Real.rpow_neg hs.le,Real.rpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ hs.ne')
  calc
    _ ≤ (gridSize bits:ℝ)^k * ((gridSize bits:ℝ)^(-(k:ℝ)) *
        Real.exp (placementTransitionCost H z x y-pathCost H+Real.log 4*k*b)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hs.le _)
    _ = Real.exp (placementTransitionCost H z x y-pathCost H+Real.log 4*k*b) := by
      rw [← mul_assoc,hpow,one_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [pathCost_nonneg H])

lemma endpointProbability_scaled_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H z A (fun i => ((x i).val,(y i).val)) ≤
      Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  rw [endpointProbability_placement]
  have hb := placementProbability_uniform_bound H hd hz hzr hz1
    (restrictPlacement H x A) (restrictPlacement H y A)
  simp only [Fintype.card_coe] at hb
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  have hk : (A.card:ℝ) ≤ k := by exact_mod_cast (show A.card ≤ k from (by simpa only [Fintype.card_fin] using A.card_le_univ))
  have hl : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hbk := mul_le_mul_of_nonneg_left hk (show (0:ℝ)≤b by positivity)
  have hbkl := mul_le_mul_of_nonneg_left hbk hl
  nlinarith

lemma alternatingSubsetSum_abs_le {I : Type*} [DecidableEq I] (U : Finset I)
    (s : ℝ) (p : Finset I → ℝ) (C : ℝ)
    (hp : ∀ A ⊆ U, 0 ≤ s^A.card*p A ∧ s^A.card*p A ≤ C) :
    |alternatingSubsetSum U s p|≤(2:ℝ)^U.card*C := by
  unfold alternatingSubsetSum
  calc
    _ ≤ ∑A ∈ U.powerset, |(-1:ℝ)^(U.card-A.card)*s^A.card*p A| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_A ∈ U.powerset, C := by
      apply Finset.sum_le_sum
      intro A hA
      rw [mul_assoc,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
        abs_of_nonneg (hp A (Finset.mem_powerset.mp hA)).1]
      exact (hp A (Finset.mem_powerset.mp hA)).2
    _ = _ := by simp

theorem centeredEndpointKernel_amplitude (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    |(gridSize bits:ℝ)^k * centeredEndpointKernel H z (fun i => ((x i).val,(y i).val))| ≤
      (2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b) := by
  unfold centeredEndpointKernel
  simp only [Fintype.card_fin]
  rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ (by exact_mod_cast (gridSize_pos bits).ne'),
    one_pow,one_mul]
  have hb := alternatingSubsetSum_abs_le Finset.univ (gridSize bits)
    (fun A => endpointProbability H z A (fun i => ((x i).val,(y i).val)))
    (Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b)) (by
      intro A _
      constructor
      · rw [endpointProbability_placement]
        exact mul_nonneg (by positivity) (placementProbability_nonneg H hz hz1 _ _)
      · exact endpointProbability_scaled_bound H hd hz hzr hz1 x y A)
  simpa only [Finset.card_univ,Fintype.card_fin] using hb

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {P Ω I : Type*} [Fintype P] [Fintype Ω] [Fintype I] [DecidableEq I]

lemma productProbability_uniform (E : (I → Ω) → Prop) :
    productProbability uniformWeight E=finiteProbability uniformWeight E := by
  unfold productProbability finiteProbability productWeight uniformWeight
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fun,Nat.cast_pow,one_div,inv_pow]

lemma sum_injective_le (f : P → Ω) (hi : Function.Injective f) (w : Ω → ℝ)
    (hw : ∀u, 0≤w u) : ∑i, w (f i) ≤ ∑u, w u := by
  classical
  rw [← Finset.sum_image (fun x _ y _ hxy => hi hxy)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u _ _ => hw u)

end BinaryCoordinateSweeps.Sparse
namespace BinaryCoordinateSweeps
open Sparse

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma placementEndpointArray_injective : Function.Injective (placementEndpointArray (k:=k) H) := by
  intro x y he
  apply Prod.ext
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun z => (z i).1) he
  · apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact congrArg (fun z => (z i).2) he

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ConditionalSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma continuous_lineLaw (d : ℕ) (g : Equiv.Perm (Slot d)) :
    Continuous (fun z => lineLaw d z g) := by
  unfold lineLaw
  fun_prop

lemma continuous_gridWeight (g : GridChoices bits) : Continuous (fun z => gridWeight bits z g) := by
  unfold gridWeight
  exact continuous_finsetProd _ (fun j _ => continuous_finsetProd _ (fun y _ => continuous_lineLaw _ _))

lemma continuous_conditionalNormalizer : Continuous (conditionalNormalizer H) := by
  unfold conditionalNormalizer
  apply continuous_finsetSum
  intro g _
  split_ifs
  · exact continuous_gridWeight g
  · exact continuous_const

lemma continuousAt_conditionalChoiceWeight (g : ConditionalChoices H) :
    ContinuousAt (fun z => conditionalChoiceWeight H z g) 0 :=
  (continuous_gridWeight g.val).continuousAt.div (continuous_conditionalNormalizer H).continuousAt
    (conditionalNormalizer_pos H (le_refl 0) (by norm_num)).ne'

lemma continuousAt_conditionalGroupLaw (a : Equiv.Perm (FreeSlot H 0)) :
    ContinuousAt (fun z => conditionalGroupLaw H z a) 0 := by
  unfold conditionalGroupLaw
  apply tendsto_finsetSum
  intro g _
  split_ifs
  · exact continuousAt_conditionalChoiceWeight H g
  · exact continuousAt_const

lemma continuousAt_endpointProbability {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (e : I → GridSlot bits × GridSlot bits) :
    ContinuousAt (fun z => endpointProbability H z A e) 0 := by
  simp_rw [endpointProbability_conditional]
  unfold conditionalEventWeight
  apply tendsto_finsetSum
  intro g _
  split_ifs
  · exact continuousAt_conditionalChoiceWeight H g
  · exact continuousAt_const

lemma continuousAt_centeredEndpointKernel {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → GridSlot bits × GridSlot bits) :
    ContinuousAt (fun z => centeredEndpointKernel H z e) 0 := by
  unfold centeredEndpointKernel alternatingSubsetSum
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum
  intro A _
  exact continuousAt_const.mul (continuousAt_endpointProbability H A e)

lemma continuousAt_centeredEndpointHS (k : ℕ) :
    ContinuousAt (fun z => ∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) 0 := by
  apply tendsto_finsetSum
  intro x _
  apply tendsto_finsetSum
  intro y _
  exact (continuousAt_centeredEndpointKernel H _).pow 2

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_AssignmentSign
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]

lemma realSign_swap {u v : X} (huv : u≠v) : realSign (Equiv.swap u v) = -1 := by
  simp [realSign,Equiv.Perm.sign_swap huv]

omit [Fintype I] [Fintype X] in
lemma assigns_swap_left (A B : I ↪ X) {u v : X}
    (hu : u∉Set.range B) (hv : v∉Set.range B) (σ : Equiv.Perm X) :
    Assigns A B (Equiv.swap u v*σ) ↔ Assigns A B σ := by
  have hf (i : I) : Equiv.swap u v (B i)=B i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact hu ⟨i,he⟩
    · intro he; exact hv ⟨i,he⟩
  constructor
  · intro hh i
    apply (Equiv.swap u v).injective
    exact (hh i).trans (hf i).symm
  · intro hh i
    change Equiv.swap u v (σ (A i))=B i
    rw [hh i,hf]

omit [Fintype I] in
theorem sum_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then realSign σ else 0) = 0 := by
  classical
  let f (σ : Equiv.Perm X) := if Assigns A B σ then realSign σ else 0
  have ht (σ : Equiv.Perm X) : f (Equiv.swap u v*σ) = -f σ := by
    dsimp [f]
    rw [assigns_swap_left A B hu hv,map_mul,realSign_swap huv]
    split_ifs <;> ring
  have he := Equiv.sum_comp (Equiv.mulLeft (Equiv.swap u v)) f
  change (∑σ, f (Equiv.swap u v*σ))=∑σ,f σ at he
  simp_rw [ht] at he
  rw [Finset.sum_neg_distrib] at he
  dsimp [f] at he
  linarith

omit [Fintype I] in
lemma uniform_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then
      uniformLaw (Equiv.Perm X) σ * realSign σ else 0) = 0 := by
  have ht (σ : Equiv.Perm X) :
      (if Assigns A B σ then uniformLaw (Equiv.Perm X) σ*realSign σ else 0) =
      (Fintype.card (Equiv.Perm X):ℝ)⁻¹*(if Assigns A B σ then realSign σ else 0) := by
    split_ifs <;> simp [uniformLaw]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_sign_assigns_zero A B huv hu hv,mul_zero]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_FallingMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
open Polynomial

lemma fallingMoment_pos {m h n : ℕ} (hm : 0 < m) (hn : h+n ≤ m) :
    0 < fallingMoment m h n := by
  apply div_pos (pow_pos (Nat.cast_pos.mpr hm) _)
  exact Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (by omega))

lemma fallingMoment_succ {m h n : ℕ} (hn : h+n < m) :
    ((m:ℝ)-h-n) * fallingMoment m h (n+1) = m * fallingMoment m h n := by
  have hh : h ≤ m := by omega
  have hi : n ≤ m-h := by omega
  have hd : ((m-h).descFactorial n : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hi))
  have hc : ((m:ℝ)-h-n) ≠ 0 := by
    have hh' : (h:ℝ)+n < m := by exact_mod_cast hn
    exact ne_of_gt (by linarith)
  simp only [fallingMoment,Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_sub hh,
    Nat.cast_sub hi,pow_succ]
  field_simp

lemma lineMoment_monomial (m h n : ℕ) (c : ℝ) :
    lineMoment m h (monomial n c) = c * fallingMoment m h n := by
  simp [lineMoment,Polynomial.lsum_apply,Polynomial.sum_monomial_index,mul_comm]

lemma lineMoment_X_pow (m h n : ℕ) :
    lineMoment m h (X^n) = fallingMoment m h n := by
  simpa only [one_mul,monomial_one_right_eq_X_pow] using lineMoment_monomial m h n 1

lemma stein_apply (m h : ℕ) (P : ℝ[X]) :
    stein m h P = C ((m:ℝ)-h)*X*P - X^2*derivative P - C (m:ℝ)*P := rfl

lemma lineMoment_stein_monomial {m h n : ℕ} (hn : h+n < m) (c : ℝ) :
    lineMoment m h (stein m h (monomial n c)) = 0 := by
  rw [stein_apply,mul_assoc,X_mul_monomial,C_mul_monomial,derivative_monomial,
    X_pow_mul_monomial,C_mul_monomial]
  simp only [LinearMap.map_sub,lineMoment_monomial]
  have hh := fallingMoment_succ hn
  cases n with
  | zero => simp only [Nat.cast_zero,mul_zero,zero_mul,sub_zero] at *; linear_combination c * hh
  | succ n => simp only [Nat.add_sub_cancel] at *; linear_combination c * hh

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma lineLaw_zero (d : ℕ) (σ : Equiv.Perm (Slot d)) :
    lineLaw d 0 σ = (Fintype.card (Equiv.Perm (Slot d)):ℝ)⁻¹ := by
  simp only [lineLaw, sub_zero, one_mul, zero_mul, add_zero, uniformLaw]

lemma assignmentWeight_uniform_of_eq {X I : Type*} [Fintype X] [Fintype I]
    (p : Equiv.Perm X → ℝ) (hp : ∀σ, p σ=((Fintype.card X).factorial:ℝ)⁻¹)
    (A B : I ↪ X) :
    assignmentWeight p A B = ((Fintype.card X).descFactorial (Fintype.card I):ℝ)⁻¹ := by
  have he : p = fun _ => (Fintype.card (Equiv.Perm X):ℝ)⁻¹ := by
    funext σ
    rw [hp]
    simp only [Fintype.card_perm]
  rw [he]
  exact assignmentWeight_uniform A B

lemma localPathWeight_zero (j : Fin b) (y : GridOutside bits j) :
    localPathWeight H 0 j y = ((2^bits j).descFactorial (lineHoles H j y):ℝ)⁻¹ := by
  have hp (σ : Equiv.Perm (Slot (bits j))) :
      lineLaw (bits j) 0 σ=((Fintype.card (Slot (bits j))).factorial:ℝ)⁻¹ := by
    rw [lineLaw_zero]
    simp only [Fintype.card_perm]
  have hw := assignmentWeight_uniform_of_eq _ hp (lineInput H j y) (lineOutput H j y)
  have hc : Fintype.card (Slot (bits j))=2^bits j := by
    simp only [Slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  have hh : Fintype.card (LinePaths H j y)=lineHoles H j y := by
    unfold lineHoles LinePaths
    congr!
  rw [hc,hh] at hw
  exact hw

lemma card_fin_sum_pred {a c : ℕ} (P : Fin (a+c) → Prop) :
    Fintype.card {i // P i} = Fintype.card {i : Fin a // P (i.castAdd c)} +
      Fintype.card {i : Fin c // P (i.natAdd a)} := by
  have he := Fintype.card_congr ((finSumFinEquiv.symm).subtypeEquiv
    (p := P) (q := fun i : Fin a ⊕ Fin c => P (finSumFinEquiv i))
    (fun _ => by simp))
  change Fintype.card {i : Fin (a+c) // P i} =
    Fintype.card {i : Fin a ⊕ Fin c // P (finSumFinEquiv i)} at he
  rw [he,Fintype.card_congr (Equiv.subtypeSum (p := fun i : Fin a ⊕ Fin c => P (finSumFinEquiv i))),
    Fintype.card_sum]
  rfl

lemma lineHoles_augment (x : Placement H k 0) (g : ConditionalChoices H)
    (j : Fin b) (y : GridOutside bits j) :
    lineHoles (augmentByChoice H x g) j y = lineHoles H j y + trackedLineCount H x g j y := by
  unfold lineHoles
  have he := card_fin_sum_pred (fun i : Fin (h+k) =>
    (fun a : {a : Fin b // a≠j} => (augmentByChoice H x g).position j.castSucc i a)=y)
  trans Fintype.card {i : Fin h // (fun a : {a : Fin b // a≠j} =>
    (augmentByChoice H x g).position j.castSucc (i.castAdd k) a)=y} +
    Fintype.card {i : Fin k // (fun a : {a : Fin b // a≠j} =>
    (augmentByChoice H x g).position j.castSucc (i.natAdd h) a)=y}
  · convert he using 1 <;> congr!
  congr 1
  · apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    change (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc
      (Fin.append (H.position 0) (fun i => (x i).val) (i.castAdd k)) a)=y ↔ _
    rw [Fin.append_left,gridPartialSweep_path H g.val g.property]
  · unfold trackedLineCount
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    change (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc
      (Fin.append (H.position 0) (fun i => (x i).val) (i.natAdd h)) a)=y ↔ _
    rw [Fin.append_right]

lemma uniform_extension_ratio {m a c : ℕ} (ha : a ≤ m) :
    ((m.descFactorial (a+c):ℝ)⁻¹ / (m.descFactorial a:ℝ)⁻¹) =
      ((m-a).descFactorial c:ℝ)⁻¹ := by
  have he := Nat.descFactorial_mul_descFactorial (show a≤a+c by omega) (n:=m)
  simp only [Nat.add_sub_cancel_left] at he
  rw [← he,Nat.cast_mul,mul_inv_rev,div_inv_eq_mul]
  have hn : (m.descFactorial a:ℝ)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr ha).ne'
  field_simp

theorem placementProbability_zero_factor (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H 0 x (placementBijection H k g x) =
      ∏j, ∏y : GridOutside bits j,
        ((2^bits j-lineHoles H j y).descFactorial (trackedLineCount H x g j y):ℝ)⁻¹ := by
  rw [placementProbability_augmentation,pathExtension_event_ratio (augmentByChoice_extension H x g),
    conditionalNormalizer_eq_prod,conditionalNormalizer_eq_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro y _
  rw [localPathWeight_zero,localPathWeight_zero,lineHoles_augment]
  exact uniform_extension_ratio (lineHoles_le H j y)

lemma sum_trackedLineCount (x : Placement H k 0) (g : ConditionalChoices H) (j : Fin b) :
    ∑y : GridOutside bits j, trackedLineCount H x g j y=k := by
  have he := Fintype.card_sigma (α := fun y : GridOutside bits j => {i : Fin k //
    (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc (x i).val a)=y})
  unfold trackedLineCount
  rw [← he]
  trans Fintype.card (Fin k)
  · exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun i : Fin k =>
      fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc (x i).val a))
  · exact Fintype.card_fin k

theorem placementProbability_zero_scaled (x : Placement H k 0) (g : ConditionalChoices H) :
    (gridSize bits:ℝ)^k * placementProbability H 0 x (placementBijection H k g x) =
      ∏j, ∏y : GridOutside bits j,
        Sparse.fallingMoment (2^bits j) (lineHoles H j y) (trackedLineCount H x g j y) := by
  rw [placementProbability_zero_factor]
  have he : (gridSize bits:ℝ)^k = ∏j, ∏y : GridOutside bits j,
      ((2^bits j:ℕ):ℝ)^trackedLineCount H x g j y := by
    simp_rw [Finset.prod_pow_eq_pow_sum,sum_trackedLineCount]
    rw [Finset.prod_pow]
    congr 1
    simp only [gridSize,Nat.cast_prod,Nat.cast_pow]
  rw [he,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Finset.prod_mul_distrib]
  rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_CenteredLineMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
open Polynomial

lemma lineMoment_stein (m h : ℕ) (P : ℝ[X]) (hp : h+P.natDegree < m) :
    lineMoment m h (stein m h P) = 0 := by
  let L := (lineMoment m h).comp (stein m h)
  change L P = 0
  conv_lhs => rw [← P.sum_monomial_eq]
  simp only [Polynomial.sum_def,map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  exact lineMoment_stein_monomial (show h+n < m from lt_of_le_of_lt
    (Nat.add_le_add_left (le_natDegree_of_ne_zero (mem_support_iff.mp hn)) h) hp) _

lemma lineMoment_C_mul (m h : ℕ) (a : ℝ) (P : ℝ[X]) :
    lineMoment m h (C a * P) = a * lineMoment m h P := by
  rw [← smul_eq_C_mul,map_smul,smul_eq_mul]

@[simp] lemma centeredLineMoment_zero (m h v : ℕ) :
    centeredLineMoment m h 0 v = fallingMoment m h v := by
  simp only [centeredLineMoment,pow_zero,mul_one,lineMoment_X_pow]

lemma X_derivative_X_pow (v : ℕ) :
    (X:ℝ[X]) * derivative (X^v) = C (v:ℝ) * X^v := by
  cases v with
  | zero => simp
  | succ v => simp only [derivative_X_pow, Nat.add_sub_cancel]; ring

lemma stein_centered (m h u v : ℕ) :
    stein m h (X^v*(X-1)^(u+1)) =
      C ((m:ℝ)-h-v-u-1) * (X^v*(X-1)^(u+2)) -
      C ((h:ℝ)+v+2*u+2) * (X^v*(X-1)^(u+1)) -
      C ((u:ℝ)+1) * (X^v*(X-1)^u) := by
  rw [stein_apply,derivative_mul]
  have hv := X_derivative_X_pow v
  have hd : derivative ((X-1)^(u+1) : ℝ[X]) = C ((u:ℝ)+1)*(X-1)^u := by
    simp [derivative_pow,derivative_sub,Nat.cast_add]
  rw [hd]
  have he : (X:ℝ[X])^2 * (derivative (X^v)*(X-1)^(u+1)) =
      C (v:ℝ)*X^(v+1)*(X-1)^(u+1) := by
    rw [show (X:ℝ[X])^2 * (derivative (X^v)*(X-1)^(u+1)) =
      X * (X*derivative (X^v))*(X-1)^(u+1) from by ring,hv,pow_succ]
    ring
  rw [mul_add,he]
  simp only [map_sub,map_add,map_mul,map_one,C_ofNat,pow_succ]
  ring

lemma centeredLineMoment_recurrence {m h u v : ℕ} (hu : h+v+u+1 < m) :
    ((m:ℝ)-h-v-u-1) * centeredLineMoment m h (u+2) v =
      ((h:ℝ)+v+2*u+2) * centeredLineMoment m h (u+1) v +
      ((u:ℝ)+1) * centeredLineMoment m h u v := by
  have hp : (X^v*(X-1)^(u+1) : ℝ[X]).natDegree ≤ v+(u+1) := by
    apply natDegree_mul_le.trans
    simp only [natDegree_pow,natDegree_X,mul_one]
    exact Nat.add_le_add_left (by simpa using
      (Nat.mul_le_mul_left (u+1) (natDegree_X_sub_C_le (1:ℝ)))) v
  have hs := lineMoment_stein m h (X^v*(X-1)^(u+1)) (by omega)
  rw [stein_centered] at hs
  simp only [LinearMap.map_sub,lineMoment_C_mul] at hs
  change _ * centeredLineMoment m h (u+2) v -
    _ * centeredLineMoment m h (u+1) v - _ * centeredLineMoment m h u v = 0 at hs
  linarith

lemma centeredLineMoment_one {m h v : ℕ} (hv : h+v < m) :
    ((m:ℝ)-h-v) * centeredLineMoment m h 1 v =
      ((h:ℝ)+v) * fallingMoment m h v := by
  have he : centeredLineMoment m h 1 v =
      fallingMoment m h (v+1) - fallingMoment m h v := by
    rw [centeredLineMoment,pow_one,mul_sub,mul_one,← pow_succ,map_sub,
      lineMoment_X_pow,lineMoment_X_pow]
  rw [he]
  have hh := fallingMoment_succ hv
  linear_combination hh

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_LightLineBound
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

lemma fallingMoment_le_two_pow {m h v : ℕ} (hm : 0 < m)
    (hl : (h:ℝ)+v ≤ (m:ℝ)/2) : fallingMoment m h v ≤ (2:ℝ)^v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hmr : (0:ℝ) < m := Nat.cast_pos.mpr hm
    have hv : h+v < m := by exact_mod_cast (show (h:ℝ)+v < m by push_cast at hl; linarith)
    have hi := ih (by push_cast at hl; linarith)
    have hn := (fallingMoment_pos hm (Nat.le_of_lt hv)).le
    have hn' := (fallingMoment_pos hm (by exact_mod_cast (show (h:ℝ)+(v+1) ≤ m by push_cast at hl; linarith))).le
    have hs := fallingMoment_succ hv
    have hd : (m:ℝ)/2 ≤ (m:ℝ)-h-v := by push_cast at hl; linarith
    have ha := mul_le_mul_of_nonneg_right hd hn'
    have hb := mul_le_mul_of_nonneg_left hi hmr.le
    rw [pow_succ]
    nlinarith

lemma light_real_lt {m h n : ℕ} {η : ℝ} (hm : 0 < m) (hη : η ≤ 1/4)
    (hl : (h:ℝ)+n ≤ m*η) : h+n < m := by
  have hp : (0:ℝ) < m := Nat.cast_pos.mpr hm
  exact_mod_cast (show (h:ℝ)+n < m by nlinarith)

theorem centeredLineMoment_light {m h u v : ℕ} {η : ℝ}
    (hm : 0 < m) (hη0 : 0 ≤ η) (hη : η ≤ 1/4)
    (hl : (h:ℝ)+u+v ≤ m*η) :
    0 ≤ centeredLineMoment m h u v ∧
      centeredLineMoment m h u v ≤ (2:ℝ)^v * (4*Real.sqrt η)^u := by
  have hmr : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hr0 : 0 ≤ 4*Real.sqrt η := by positivity
  have hr2 : 4*Real.sqrt η ≤ 2 := by
    have hs := Real.sq_sqrt hη0
    have hs0 := Real.sqrt_nonneg η
    nlinarith
  have hrsq : (4*Real.sqrt η)^2 = 16*η := by rw [mul_pow,Real.sq_sqrt hη0]; norm_num
  have hetr : η ≤ 4*Real.sqrt η := by nlinarith [Real.sq_sqrt hη0,Real.sqrt_nonneg η]
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero =>
      rw [centeredLineMoment_zero,pow_zero,mul_one]
      have hv : h+v ≤ m := Nat.le_of_lt (light_real_lt hm hη (by simpa using hl))
      exact ⟨(fallingMoment_pos hm hv).le,fallingMoment_le_two_pow hm (by nlinarith)⟩
    | succ u =>
      cases u with
      | zero =>
        have hb := fallingMoment_le_two_pow hm (show (h:ℝ)+v ≤ m/2 by push_cast at hl; nlinarith)
        have hv : h+v < m := light_real_lt hm hη (by push_cast at hl; linarith)
        have hbn := (fallingMoment_pos hm (Nat.le_of_lt hv)).le
        have he := centeredLineMoment_one hv
        have hd : 0 < (m:ℝ)-h-v := by
          have hv' : (h:ℝ)+v < m := by exact_mod_cast hv
          linarith
        have hp : 0 ≤ centeredLineMoment m h 1 v := by
          apply nonneg_of_mul_nonneg_right (by rw [he]; positivity) hd
        refine ⟨hp,?_⟩
        rw [pow_one]
        have ha : (m:ℝ)/2 ≤ (m:ℝ)-h-v := by push_cast at hl; nlinarith
        have hc : (h:ℝ)+v ≤ m*η := by push_cast at hl; linarith
        have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ (h:ℝ)+v by positivity)
        have hc' := mul_le_mul_of_nonneg_right hc (show (0:ℝ) ≤ 2^v by positivity)
        have ha' := mul_le_mul_of_nonneg_right ha hp
        have hr : 2*η ≤ 4*Real.sqrt η := by nlinarith [Real.sq_sqrt hη0,Real.sqrt_nonneg η]
        have hr' := mul_le_mul_of_nonneg_left hr (show 0 ≤ (m:ℝ)*(2:ℝ)^v by positivity)
        nlinarith
      | succ u =>
        have hu1 := ih (u+1) (by omega) (by push_cast at hl ⊢; linarith)
        have hu0 := ih u (by omega) (by push_cast at hl ⊢; linarith)
        have hv : h+v+u+1 < m := by
          have hh : (h:ℝ)+(v+u+1) ≤ m*η := by push_cast at hl; linarith
          have ht := light_real_lt (h := h) (n := v+u+1) hm hη (by simpa only [Nat.cast_add,Nat.cast_one] using hh)
          omega
        have he := centeredLineMoment_recurrence hv
        have hd : 0 < (m:ℝ)-h-v-u-1 := by
          have hv' : (h:ℝ)+v+u+1 < m := by exact_mod_cast hv
          linarith
        have hp : 0 ≤ centeredLineMoment m h (u+2) v := by
          apply nonneg_of_mul_nonneg_right (by
            rw [he]
            exact add_nonneg (mul_nonneg (by positivity) hu1.1)
              (mul_nonneg (by positivity) hu0.1)) hd
        refine ⟨hp,?_⟩
        have ha : (m:ℝ)/2 ≤ (m:ℝ)-h-v-u-1 := by push_cast at hl; nlinarith
        have hc : (h:ℝ)+v+2*u+2 ≤ 2*m*η := by
          have hhv : (0:ℝ) ≤ h+v := by positivity
          push_cast at hl
          linarith
        have hc0 : 0 ≤ (h:ℝ)+v+2*u+2 := by positivity
        have hb : (u:ℝ)+1 ≤ m*η := by
          have hhv : (0:ℝ) ≤ h+v := by positivity
          push_cast at hl
          linarith
        have ha' := mul_le_mul_of_nonneg_right ha hp
        have hc' := mul_le_mul hc hu1.2 hu1.1 (by positivity : 0 ≤ 2*(m:ℝ)*η)
        have hb' := mul_le_mul hb hu0.2 hu0.1 (by positivity : 0 ≤ (m:ℝ)*η)
        have hr : 4*η*(4*Real.sqrt η)+2*η ≤ (4*Real.sqrt η)^2 := by
          rw [hrsq]
          nlinarith
        have hr' := mul_le_mul_of_nonneg_left hr
          (show 0 ≤ (m:ℝ)/2*((2:ℝ)^v*(4*Real.sqrt η)^u) by positivity)
        simp only [pow_succ] at hc' ⊢
        nlinarith

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

variable {L : Type*} [Fintype L]

lemma multilineMoment_monomial (m h : L → ℕ) (n : L →₀ ℕ) :
    multilineMoment m h (MvPolynomial.monomial n 1) =
      ∏ l, fallingMoment (m l) (h l) (n l) := by
  exact (MvPolynomial.basisMonomials L ℝ).constr_basis ℝ _ n

lemma multiline_prod_X (n : L → ℕ) :
    (∏ l, (MvPolynomial.X l : MvPolynomial L ℝ) ^ n l) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm n) 1 := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  change (∏ l, MvPolynomial.X l ^ (Finsupp.equivFunOnFinite.symm n) l) = _
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro l _ hl
  have hz := Finsupp.notMem_support_iff.mp hl
  change n l = 0 at hz
  change (MvPolynomial.X l : MvPolynomial L ℝ)^n l = 1
  rw [hz,pow_zero]

theorem multilineMoment_factor (m h : L → ℕ) (P : L → Polynomial ℝ) :
    multilineMoment m h (∏ l, Polynomial.aeval (MvPolynomial.X l) (P l)) =
      ∏ l, lineMoment (m l) (h l) (P l) := by
  let f : MultilinearMap ℝ (fun _ : L => Polynomial ℝ) ℝ :=
    (multilineMoment m h).compMultilinearMap
      ((MultilinearMap.mkPiAlgebra ℝ L (MvPolynomial L ℝ)).compLinearMap
        (fun l => (Polynomial.aeval (MvPolynomial.X l)).toLinearMap))
  let g : MultilinearMap ℝ (fun _ : L => Polynomial ℝ) ℝ :=
    (MultilinearMap.mkPiAlgebra ℝ L ℝ).compLinearMap (fun l => lineMoment (m l) (h l))
  have he : f = g := by
    apply Module.Basis.ext_multilinear (fun _ : L => Polynomial.basisMonomials ℝ)
    intro n
    change multilineMoment m h (∏ l, Polynomial.aeval (MvPolynomial.X l)
      (Polynomial.basisMonomials ℝ (n l))) =
        ∏ l, lineMoment (m l) (h l) (Polynomial.basisMonomials ℝ (n l))
    simp only [Polynomial.coe_basisMonomials,Polynomial.aeval_monomial,map_one,one_mul,
      lineMoment_monomial]
    rw [multiline_prod_X,multilineMoment_monomial]
    rfl
  exact congrArg (fun a => a P) he

lemma multilineMoment_centered (m h u v : L → ℕ) :
    multilineMoment m h (∏ l, (MvPolynomial.X l : MvPolynomial L ℝ)^v l *
      (MvPolynomial.X l-1)^u l) =
        ∏ l, centeredLineMoment (m l) (h l) (u l) (v l) := by
  change multilineMoment m h _ = ∏ l, lineMoment (m l) (h l)
    (Polynomial.X^v l * (Polynomial.X-1)^u l)
  rw [← multilineMoment_factor]
  apply congrArg (multilineMoment m h)
  apply Finset.prod_congr rfl
  intro l _
  rw [map_mul,map_pow,map_pow,map_sub,map_one,Polynomial.aeval_X]

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_OccurrenceMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

lemma sum_occurrences (f : A → L) : ∑ l, occurrences f l = Fintype.card A := by
  simpa only [occurrences,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
    (Fintype.sum_fiberwise' f (fun _ : L => (1:ℕ)))

lemma prod_occurrences {R : Type*} [CommMonoid R] (f : A → L) (x : L → R) :
    (∏ a, x (f a)) = ∏ l, x l ^ occurrences f l := by
  simpa only [occurrences,Finset.prod_const,Finset.card_univ] using
    (Fintype.prod_fiberwise' f x).symm

lemma occurrenceMoment_eq (m h : L → ℕ) (f : A → L) (g : B → L) :
    multilineMoment m h ((∏ a, ((MvPolynomial.X (f a) : MvPolynomial L ℝ)-1)) *
      ∏ b, MvPolynomial.X (g b)) =
        ∏ l, centeredLineMoment (m l) (h l) (occurrences f l) (occurrences g l) := by
  rw [prod_occurrences (R := MvPolynomial L ℝ) f (fun l => MvPolynomial.X l-1), prod_occurrences (R := MvPolynomial L ℝ) g MvPolynomial.X,
    ← Finset.prod_mul_distrib]
  calc
    _ = multilineMoment m h (∏ l, (MvPolynomial.X l : MvPolynomial L ℝ)^occurrences g l *
        (MvPolynomial.X l-1)^occurrences f l) :=
      congrArg (multilineMoment m h) (Finset.prod_congr rfl (fun l _ => mul_comm _ _))
    _ = _ := multilineMoment_centered m h _ _

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_RemainingSign
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma realSign_ne_zero {X : Type*} [Fintype X] [DecidableEq X] (g : Equiv.Perm X) :
    realSign g≠0 := by
  simp [realSign]

lemma realSign_inv {X : Type*} [Fintype X] [DecidableEq X] (f : Equiv.Perm X) :
    realSign f⁻¹=(realSign f)⁻¹ := by
  have hm : realSign f⁻¹*realSign f=1 := by rw [←map_mul,inv_mul_cancel,map_one]
  calc
    realSign f⁻¹ = (realSign f⁻¹*realSign f)*(realSign f)⁻¹ := by
      rw [mul_assoc,mul_inv_cancel₀ (realSign_ne_zero f),mul_one]
    _ = _ := by rw [hm,one_mul]

lemma remaining_relative_realSign (g g₀ : ConditionalChoices H) :
    realSign ((remainingPerm H g₀.val g₀.property)⁻¹*remainingPerm H g.val g.property)=
      realSign ((gridSweep bits g₀.val)⁻¹*gridSweep bits g.val) := by
  let f := (gridSweep bits g₀.val)⁻¹*gridSweep bits g.val
  have hfix (i : Fin h) : f (H.position 0 i)=H.position 0 i := by
    change (gridSweep bits g₀.val).symm (gridSweep bits g.val (H.position 0 i))=_
    rw [gridSweep_path H g.val g.property,←gridSweep_path H g₀.val g₀.property,
      Equiv.symm_apply_apply]
  have hp (x : GridSlot bits) : f x∉Set.range (H.position 0) ↔ x∉Set.range (H.position 0) := by
    constructor
    · intro hx hi; obtain ⟨i,rfl⟩ := hi; exact hx ⟨i,hfix i |>.symm⟩
    · intro hx hi; obtain ⟨i,hi⟩ := hi
      exact hx ⟨i,f.injective ((hfix i).trans hi)⟩
  have hs := Equiv.Perm.sign_subtypePerm f (p := fun x => x∉Set.range (H.position 0)) hp (by
    intro x hx hi; obtain ⟨i,rfl⟩ := hi; exact hx (hfix i))
  have he : Equiv.Perm.subtypePerm f hp =
      (remainingPerm H g₀.val g₀.property)⁻¹*remainingPerm H g.val g.property := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change f x.val =
      (gridSweep bits g₀.val).symm
        ((freeIdentification H) ((freeIdentification H).symm
          ((remainingBijection H g.val g.property) x))).val
    rw [Equiv.apply_symm_apply]
    rfl
  rw [he] at hs
  convert congrArg (fun u : ℤˣ => ((u:ℤ):ℝ)) hs using 1
  · unfold realSign; dsimp; congr 3
    congr 1; exact Subsingleton.elim _ _
  · rfl

theorem remaining_realSign_factor (g g₀ : ConditionalChoices H) :
    realSign (remainingPerm H g.val g.property) =
      (realSign (remainingPerm H g₀.val g₀.property)/realSign (gridSweep bits g₀.val))*
        realSign (gridSweep bits g.val) := by
  have he := remaining_relative_realSign H g g₀
  simp only [map_mul,realSign_inv] at he
  have h₀ := realSign_ne_zero (remainingPerm H g₀.val g₀.property)
  have h₁ := realSign_ne_zero (gridSweep bits g₀.val)
  field_simp [h₀,h₁] at he ⊢
  nlinarith [he]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseNumerics
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Asymptotics

namespace BinaryCoordinateSweeps.Sparse

lemma nat_pow_le_exp_of_le {x A : ℝ} (hx : 0≤x) (h : x≤Real.exp A) (n : ℕ) :
    x^n≤Real.exp ((n:ℝ)*A) := by
  simpa only [←Real.exp_nat_mul] using pow_le_pow_left₀ hx h n

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseReduction
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Sparse

lemma outside_card_mul_axis {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :
    Fintype.card (GridOutside bits j)*2^bits j=gridSize bits := by
  have he := Fintype.card_congr (Equiv.piSplitAt j (fun i => Slot (bits i)))
  change Fintype.card (GridSlot bits)=Fintype.card (Slot (bits j) × GridOutside bits j) at he
  have hs : Fintype.card (Slot (bits j))=2^bits j := by simp [Slot]
  have hg : Fintype.card (GridSlot bits)=gridSize bits := by simp [GridSlot,gridSize,Slot]
  simpa only [Fintype.card_prod,hs,hg,mul_comm] using he.symm

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_FewSparseBases
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinaryCoordinateSweeps.Sparse

lemma few_eta_good (b : ℕ) {L : ℝ} (hb : b ≤ 16000) (hL : (10:ℝ)^26 ≤ L) :
    Real.exp (-L/160000) ≤ 1/4 ∧
    4*(b:ℝ)*Real.sqrt (Real.exp (-L/160000)) ≤ Real.exp (-L/640000) := by
  have hbR : (b:ℝ) ≤ 16000 := by exact_mod_cast hb
  constructor
  · have hc : (4:ℝ) ≤ Real.exp (L/160000) := by
      apply (show (4:ℝ) ≤ L/160000+1 from by linarith).trans (Real.add_one_le_exp _)
    rw [show -L/160000=-(L/160000) by ring,Real.exp_neg]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hc
  · have hc : 4*(b:ℝ) ≤ Real.exp (L/640000) := by
      apply (show 4*(b:ℝ) ≤ L/640000+1 from by linarith).trans (Real.add_one_le_exp _)
    have hs : Real.sqrt (Real.exp (-L/160000))=Real.exp (-L/320000) := by
      apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _)).mpr
      rw [←Real.exp_add]
      congr 1
      ring
    rw [hs]
    refine (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    ring

lemma few_vertex_base (b h k : ℕ) {s : ℝ} (hs : 0<s) (hb : b ≤ 16000)
    (hL : (10:ℝ)^26 ≤ Real.log s) (hk : ((k+h:ℕ):ℝ) ≤ s^(1599/1600:ℝ)) :
    ((k+h:ℕ):ℝ)*((b+1:ℝ)/s) ≤ Real.exp (-Real.log s/3200) := by
  have hbR : (b+1:ℝ) ≤ 16001 := by exact_mod_cast (by omega : b+1 ≤ 16001)
  have hc : (b+1:ℝ) ≤ Real.exp (Real.log s/3200) := by
    apply (show (b+1:ℝ) ≤ Real.log s/3200+1 from by linarith).trans (Real.add_one_le_exp _)
  have hkE : ((k+h:ℕ):ℝ) ≤ Real.exp ((1599/1600:ℝ)*Real.log s) := by
    simpa only [Real.rpow_def_of_pos hs,mul_comm] using hk
  calc
    _  ≤  Real.exp ((1599/1600:ℝ)*Real.log s)*(Real.exp (Real.log s/3200)/s) := by
      exact mul_le_mul hkE (div_le_div_of_nonneg_right hc hs.le) (by positivity) (by positivity)
    _ = _ := by
      rw [←Real.exp_log hs,←Real.exp_sub,←Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring

lemma few_line_base (u h k : ℕ) {s : ℝ} (hs : 0<s)
    (hL : (10:ℝ)^26 ≤ Real.log s) (hk : ((k+h:ℕ):ℝ) ≤ s^(1599/1600:ℝ))
    (hu : u ≤ k+h) :
    2*(u:ℝ)/(s*Real.exp (-Real.log s/160000)) ≤ Real.exp (-Real.log s/3200) := by
  have huE : (u:ℝ) ≤ Real.exp ((1599/1600:ℝ)*Real.log s) := by
    refine (show (u:ℝ) ≤ ((k+h:ℕ):ℝ) by exact_mod_cast hu).trans ?_
    simpa only [Real.rpow_def_of_pos hs,mul_comm] using hk
  have hc : (2:ℝ) ≤ Real.exp ((49/160000:ℝ)*Real.log s) := by
    apply (show (2:ℝ) ≤ (49/160000:ℝ)*Real.log s+1 from by linarith).trans (Real.add_one_le_exp _)
  calc
    _  ≤  (Real.exp ((49/160000:ℝ)*Real.log s)*Real.exp ((1599/1600:ℝ)*Real.log s))/
        (s*Real.exp (-Real.log s/160000)) := by gcongr
    _ = _ := by
      rw [←Real.exp_log hs,←Real.exp_add,←Real.exp_add,←Real.exp_sub]
      simp only [Real.log_exp]
      congr 1
      ring

lemma adaptive_count_small (O k : ℕ) {s m η : ℝ} (hs : 0<s)
    (hL : (10:ℝ)^26 ≤ Real.log s) (hO : (O+1:ℝ) ≤ 2*s) (hm : 8000000000 ≤ m*η) :
    (O+1:ℝ)^⌊2*(k:ℝ)/(m*η)⌋₊ ≤ Real.exp ((k:ℝ)*Real.log s/2000000000) := by
  have hm0 : 0 < m*η := by linarith
  have hlog0 : 0 ≤ Real.log (O+1:ℝ) := Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 O))
  have hlog : Real.log (O+1:ℝ) ≤ 2*Real.log s := by
    have he := Real.log_le_log (by positivity : (0:ℝ)<O+1) hO
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hs.ne'] at he
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hfloor : (⌊2*(k:ℝ)/(m*η)⌋₊:ℝ) ≤ (k:ℝ)/4000000000 := by
    refine (Nat.floor_le (by positivity)).trans ?_
    apply (div_le_iff₀ hm0).mpr
    have hh := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ k by positivity)
    nlinarith only [hh]
  rw [←Real.exp_log (by positivity : (0:ℝ)<O+1),←Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  calc
    _  ≤  ((k:ℝ)/4000000000)*(2*Real.log s) :=
      mul_le_mul hfloor hlog hlog0 (by positivity)
    _ = _ := by ring

end BinaryCoordinateSweeps.Sparse

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

lemma grid_log_upper {b r : ℕ} {bits : Fin b → ℕ} (hd : ∀j, bits j ≤ 2*r) :
    Real.log (gridSize bits) ≤ (b:ℝ)*(2*(r:ℝ)*Real.log 2) := by
  calc
    _ = ∑j : Fin b, (bits j:ℝ)*Real.log 2 := by
      rw [log_gridSize]
      simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
    _  ≤  ∑_j : Fin b, 2*(r:ℝ)*Real.log 2 := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd j) (Real.log_nonneg (by norm_num))
    _ = _ := by simp

lemma few_axis_eta_large {b r : ℕ} {bits : Fin b → ℕ}
    (hb : b ≤ 16000) (hd : ∀j, r ≤ bits j ∧ bits j ≤ 2*r)
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits)) (j : Fin b) :
    (8000000000:ℝ) ≤ (2^bits j:ℕ)*Real.exp (-Real.log (gridSize bits)/160000) := by
  have hbR : (b:ℝ) ≤ 16000 := by exact_mod_cast hb
  have hr : 0 ≤ (r:ℝ)*Real.log 2 := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hu := grid_log_upper (fun j => (hd j).2)
  have hux := mul_le_mul_of_nonneg_right hbR hr
  have hj := mul_le_mul_of_nonneg_right (show (r:ℝ) ≤ bits j by exact_mod_cast (hd j).1)
    (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
  calc
    _  ≤  Real.log (gridSize bits)/40000+1 := by linarith
    _  ≤  Real.exp (Real.log (gridSize bits)/40000) := Real.add_one_le_exp _
    _  ≤  _ := by
      rw [←Real.exp_log (by positivity : (0:ℝ)<((2^bits j:ℕ):ℝ)),←Real.exp_add]
      apply Real.exp_le_exp.mpr
      simp only [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
      linarith

lemma outside_card_add_one_le {b : ℕ} (bits : Fin b → ℕ) (j : Fin b) :
    (Fintype.card (GridOutside bits j)+1:ℝ) ≤ 2*(gridSize bits:ℝ) := by
  have he := outside_card_mul_axis bits j
  have hp : 1 ≤ 2^bits j := Nat.one_le_pow _ _ (by omega)
  have hle : Fintype.card (GridOutside bits j) ≤ gridSize bits := by nlinarith
  have hg : 1 ≤ gridSize bits := gridSize_pos bits
  exact_mod_cast (show Fintype.card (GridOutside bits j)+1 ≤ 2*gridSize bits from by omega)

lemma few_cutoff_bounds (b k : ℕ) (hb : 1 ≤ b) (hbB : b ≤ 16000) :
    2*((k/4+1)-1+2*b*((k/(8*b)+1)-1)) ≤ k ∧
    (k:ℝ) ≤ 8*(((k/4+1+1)/2:ℕ):ℝ) ∧
    (k:ℝ) ≤ 128000*(k/(8*b)+1:ℕ) := by
  have h1 := Nat.div_mul_le_self k 4
  have h2 := Nat.div_mul_le_self k (8*b)
  have hmod := Nat.mod_lt k (by omega : 0<8*b)
  have he := Nat.mod_add_div k (8*b)
  constructor
  · simp only [Nat.add_sub_cancel]
    nlinarith
  constructor
  · exact_mod_cast (show k ≤ 8*((k/4+1+1)/2) from by omega)
  · have ht : k ≤ (8*b)*(k/(8*b)+1) := by nlinarith
    have hh := ht.trans (Nat.mul_le_mul_right _ (show 8*b ≤ 128000 from by omega))
    exact_mod_cast hh

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_FewSparseNumerics
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Sparse

lemma sparse_amplitudes_small (b h k : ℕ) {L : ℝ} (hb : b≤16000)
    (hh : (h:ℝ)≤100000*k) (hL : (10:ℝ)^26≤L) :
    ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ))^2≤Real.exp ((k:ℝ)*L/2000000000) ∧
    ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2≤Real.exp ((k:ℝ)*L/2000000000) ∧
    (2:ℝ)^k≤Real.exp ((k:ℝ)*L/2000000000) := by
  have hbR : (b:ℝ)≤16000 := by exact_mod_cast hb
  have h2 : Real.log 2≤2 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)).trans (by norm_num)
  have h4 : Real.log 4≤4 := (Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)).trans (by norm_num)
  have hbK := mul_le_mul_of_nonneg_right hbR (show (0:ℝ)≤k by positivity)
  have hhB := mul_le_mul_of_nonneg_left hh (show (0:ℝ)≤b by positivity)
  have hLK := mul_le_mul_of_nonneg_right hL (show (0:ℝ)≤k by positivity)
  have hp (n : ℕ) : (2:ℝ)^n=Real.exp ((n:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  constructor
  · rw [hp,←Real.exp_add,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h2K := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤(k+k*b:ℕ) by positivity)
    push_cast at h2K ⊢
    nlinarith only [h2K,hhB,hbK,hLK]
  constructor
  · rw [hp,←Real.exp_add,←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h2K := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤k by positivity)
    have h4K := mul_le_mul_of_nonneg_right h4 (show (0:ℝ)≤k*b by positivity)
    norm_num
    nlinarith only [h2K,h4K,hhB,hbK,hLK]
  · rw [hp]
    apply Real.exp_le_exp.mpr
    have h2K := mul_le_mul_of_nonneg_left h2 (show (0:ℝ)≤k by positivity)
    nlinarith only [h2K,hLK]

lemma few_hs_scalar (b h k wv wl : ℕ) {L g v x y : ℝ} (C : Fin b → ℝ)
    (hb : b≤16000) (hk : 1≤k) (hh : (h:ℝ)≤100000*k) (hL : (10:ℝ)^26≤L)
    (htv : (k:ℝ)≤8*(((wv+1)/2:ℕ):ℝ)) (htl : (k:ℝ)≤128000*wl)
    (hg0 : 0≤g) (hg : g≤Real.exp (-L/640000))
    (hv0 : 0≤v) (hv : v≤Real.exp (-L/3200))
    (hx0 : 0≤x) (hx : x≤Real.exp (-L/3200))
    (hy0 : 0≤y) (hy : y≤Real.exp (-L/3200))
    (hC0 : ∀j,0≤C j) (hC : ∀j,C j≤Real.exp ((k:ℝ)*L/2000000000)) :
    ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*g^((k+1)/2))^2+
      ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl))≤
      Real.exp (-(k:ℝ)*L/1000000000000) := by
  have hL0 : 0≤L := (by positivity : (0:ℝ)≤10^26).trans hL
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hbR : (b:ℝ)≤16000 := by exact_mod_cast hb
  have hKL := mul_nonneg (Nat.cast_nonneg k) hL0
  have hkt : (k:ℝ)≤2*(((k+1)/2:ℕ):ℝ) := by exact_mod_cast (show k≤2*((k+1)/2) from by omega)
  obtain ⟨hA,hB,h2⟩ := sparse_amplitudes_small b h k hb hh hL
  have hgpow : (g^((k+1)/2))^2≤Real.exp (-(k:ℝ)*L/1000000000) := by
    have he := nat_pow_le_exp_of_le hg0 hg ((k+1)/2)
    have he2 := pow_le_pow_left₀ (pow_nonneg hg0 _) he 2
    rw [←Real.exp_nat_mul] at he2
    refine he2.trans (Real.exp_le_exp.mpr ?_)
    have ht := mul_le_mul_of_nonneg_right hkt hL0
    norm_num
    nlinarith only [ht,hKL]
  have hpow (a : ℝ) (ha0 : 0≤a) (ha : a≤Real.exp (-L/3200))
      (t : ℕ) (ht : (k:ℝ)≤128000*t) :
      a^t≤Real.exp (-2*(k:ℝ)*L/1000000000) := by
    apply (nat_pow_le_exp_of_le ha0 ha t).trans (Real.exp_le_exp.mpr ?_)
    have he := mul_le_mul_of_nonneg_right ht hL0
    nlinarith only [he,hKL]
  have hlx := hpow x hx0 hx wl htl
  have hly := hpow y hy0 hy wl htl
  have hlv := hpow v hv0 hv ((wv+1)/2) (htv.trans (by nlinarith only [show (0:ℝ)≤(((wv+1)/2:ℕ):ℝ) by positivity]))
  have hgood : ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*g^((k+1)/2))^2 ≤
      Real.exp (-(k:ℝ)*L/2000000000) := by
    rw [mul_pow]
    refine (mul_le_mul hA hgpow (by positivity) (Real.exp_pos _).le).trans_eq ?_
    rw [←Real.exp_add]
    congr 1
    ring
  have hvertex : (2:ℝ)^k*v^((wv+1)/2)≤Real.exp (-(k:ℝ)*L/1000000000) := by
    refine (mul_le_mul h2 hlv (by positivity) (Real.exp_pos _).le).trans ?_
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hKL]
  have hholes : (2:ℝ)^k*x^wl≤Real.exp (-(k:ℝ)*L/1000000000) := by
    refine (mul_le_mul h2 hlx (by positivity) (Real.exp_pos _).le).trans ?_
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hKL]
  have hparticles (j : Fin b) : C j*(2:ℝ)^k*y^wl≤Real.exp (-(k:ℝ)*L/1000000000) := by
    have hc0 := hC0 j
    refine (mul_le_mul (mul_le_mul (hC j) h2 (by positivity) (Real.exp_pos _).le)
      hly (by positivity) (by positivity)).trans_eq ?_
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    ring
  have hevents : (2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl) ≤
      (1+2*b)*Real.exp (-(k:ℝ)*L/1000000000) := by
    refine (add_le_add hvertex (Finset.sum_le_sum (fun j _ => add_le_add hholes (hparticles j)))).trans_eq ?_
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hbad : ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl)) ≤
      (1+2*b)*Real.exp (-(k:ℝ)*L/2000000000) := by
    have hev0 : 0≤ (2:ℝ)^k*v^((wv+1)/2)+∑j : Fin b, ((2:ℝ)^k*x^wl+C j*(2:ℝ)^k*y^wl) := by
      apply add_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro j _
      have hc0 := hC0 j
      positivity
    refine (mul_le_mul hB hevents hev0 (Real.exp_pos _).le).trans_eq ?_
    rw [mul_left_comm,←Real.exp_add]
    congr 1
    ring_nf
  have hcount : 2+2*(b:ℝ)≤Real.exp ((k:ℝ)*L/4000000000) := by
    apply (show 2+2*(b:ℝ)≤(k:ℝ)*L/4000000000+1 from ?_).trans (Real.add_one_le_exp _)
    have hh := mul_le_mul_of_nonneg_right hkR hL0
    nlinarith only [hh,hL,hbR]
  calc
    _ ≤ (2+2*b)*Real.exp (-(k:ℝ)*L/2000000000) := by nlinarith only [hgood,hbad]
    _ ≤ Real.exp ((k:ℝ)*L/4000000000)*Real.exp (-(k:ℝ)*L/2000000000) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ ≤ _ := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hKL]

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathSign
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma realSign_gridLayer {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) (j : Fin b) :
    realSign (gridLayer bits g j)=∏y, realSign (g j y) := by
  simp [gridLayer,realSign,Equiv.Perm.sign_prodCongrLeft,map_prod]

lemma realSign_gridSweep {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    realSign (gridSweep bits g)=∏j, ∏y, realSign (g j y) := by
  simp [gridSweep,map_list_prod,List.map_reverse,List.prod_reverse,
    List.map_ofFn,List.prod_ofFn,realSign_gridLayer]

lemma signed_path_integrand_factor {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g*realSign (gridSweep bits g) else 0) =
      ∏j, ∏y, if Assigns (lineInput H j y) (lineOutput H j y) (g j y) then
        lineLaw (bits j) z (g j y)*realSign (g j y) else 0 := by
  rw [pathEvent_iff_assigns,realSign_gridSweep]
  simp only [Fintype.prod_ite_zero,Finset.prod_mul_distrib,gridWeight]
  split_ifs <;> rfl

lemma signed_path_weight_factor {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0) =
      ∏j, ∏y, ∑σ : Equiv.Perm (Slot (bits j)),
        if Assigns (lineInput H j y) (lineOutput H j y) σ then
          lineLaw (bits j) z σ*realSign σ else 0 := by
  simp_rw [signed_path_integrand_factor H z]
  exact sum_prod_grid bits (fun j y σ =>
    if Assigns (lineInput H j y) (lineOutput H j y) σ then
      lineLaw (bits j) z σ*realSign σ else 0)

theorem signed_path_weight_zero_uniform {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (j : Fin b) (y : GridOutside bits j)
    {u v : Slot (bits j)} (huv : u≠v)
    (hu : u∉Set.range (lineOutput H j y)) (hv : v∉Set.range (lineOutput H j y)) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits 0 g*realSign (gridSweep bits g) else 0)=0 := by
  rw [signed_path_weight_factor]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ y)
  simpa only [lineLaw,sub_zero,one_mul,zero_mul,add_zero] using
    uniform_sign_assigns_zero (lineInput H j y) (lineOutput H j y) huv hu hv

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_SparseSignGeometry
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma two_outside_embedding {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ↪ Y) (h : Fintype.card X+1<Fintype.card Y) :
    ∃u v : Y, u≠v ∧ u∉Set.range e ∧ v∉Set.range e := by
  let S := {y : Y // y∉Set.range e}
  have hc : Fintype.card S=Fintype.card Y-Fintype.card X := by
    dsimp only [S]
    rw [Fintype.card_subtype_compl,Fintype.card_range]
  have hS : 1<Fintype.card S := by omega
  have : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp hS
  obtain ⟨u,v,huv⟩ := exists_pair_ne S
  exact ⟨u.val,v.val,(fun he => huv (Subtype.ext he)),u.property,v.property⟩

lemma exists_line_two_free (j : Fin b)
    (hh : h+Fintype.card (GridOutside bits j)<gridSize bits) :
    ∃y : GridOutside bits j, ∃u v : Slot (bits j), u≠v ∧
      u∉Set.range (lineOutput H j y) ∧ v∉Set.range (lineOutput H j y) := by
  have hfull : Fintype.card (GridOutside bits j)*2^bits j=gridSize bits := by
    have he := Fintype.card_congr (Equiv.piSplitAt j (fun i => Slot (bits i)))
    change Fintype.card (GridSlot bits)=Fintype.card (Slot (bits j) × GridOutside bits j) at he
    have hs : Fintype.card (Slot (bits j))=2^bits j := by simp [Slot]
    have hg : Fintype.card (GridSlot bits)=gridSize bits := by simp [GridSlot,gridSize,Slot]
    simpa only [Fintype.card_prod,hs,hg,mul_comm] using he.symm
  have he : ∃y : GridOutside bits j, lineHoles H j y+1<2^bits j := by
    by_contra hn
    push Not at hn
    have hf := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hn y)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
      mul_one,sum_lineHoles,hfull] at hf
    omega
  obtain ⟨y,hy⟩ := he
  refine ⟨y,?_⟩
  apply two_outside_embedding (lineOutput H j y)
  have hc : Fintype.card (LinePaths H j y)=lineHoles H j y := by
    unfold LinePaths lineHoles
    congr 1
  rw [hc]
  simpa [Slot] using hy

lemma signed_path_weight_zero_few (j : Fin b)
    (hh : h+Fintype.card (GridOutside bits j)<gridSize bits) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits 0 g*realSign (gridSweep bits g) else 0)=0 := by
  obtain ⟨y,u,v,huv,hu,hv⟩ := exists_line_two_free H j hh
  exact signed_path_weight_zero_uniform H j y huv hu hv

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_TensorBounds_SignedPlacement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

section
attribute [local instance] Classical.propDecidable
variable {b h h' k : ℕ} {bits : Fin b → ℕ} {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma PathExtension.signed_restrict_zero (E : PathExtension H H') (z : ℝ)
    (hs : (∑g : GridChoices bits, if pathEvent H' g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0) :
    (∑g : ConditionalChoices H, if pathEvent H' g.val then
      conditionalChoiceWeight H z g*realSign (remainingPerm H g.val g.property) else 0)=0 := by
  obtain ⟨g₀,hg₀⟩ := pathEvent_nonempty H
  let a := realSign (remainingPerm H g₀ hg₀)/realSign (gridSweep bits g₀)
  have hs' : (∑g : ConditionalChoices H', gridWeight bits z g.val*realSign (gridSweep bits g.val))=0 := by
    have he := sum_dite_zero (pathEvent H')
      (fun g _ => gridWeight bits z g*realSign (gridSweep bits g))
    rw [←hs]
    refine Eq.trans ?_ he.symm
    apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _; rfl
  calc
    _ = (a/conditionalNormalizer H z)*
        (∑g : ConditionalChoices H, if pathEvent H' g.val then
          gridWeight bits z g.val*realSign (gridSweep bits g.val) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : pathEvent H' g.val
      · rw [ite_eq_left hg,ite_eq_left hg,remaining_realSign_factor H g ⟨g₀,hg₀⟩]
        dsimp [a,conditionalChoiceWeight]
        ring
      · simp only [ite_eq_right hg,mul_zero]
    _ = (a/conditionalNormalizer H z)*
        (∑g : ConditionalChoices H', gridWeight bits z g.val*realSign (gridSweep bits g.val)) := by
      congr 1
      exact E.sum_restrict (fun g => gridWeight bits z g.val*realSign (gridSweep bits g.val))
    _ = 0 := by rw [hs',mul_zero]

variable (H)

lemma signedPlacementEntry_zero (z : ℝ) (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hs : ∀g₀ : ConditionalChoices H,
      (∑g : GridChoices bits, if pathEvent (augmentByChoice H x g₀) g then
        gridWeight bits z g*realSign (gridSweep bits g) else 0)=0) :
    signedPlacementEntry H z x y=0 := by
  by_cases he : ∃g₀ : ConditionalChoices H, placementBijection H k g₀ x=y
  · obtain ⟨g₀,rfl⟩ := he
    have hz := (augmentByChoice_extension H x g₀).signed_restrict_zero z (hs g₀)
    refine Eq.trans ?_ hz
    unfold signedPlacementEntry
    apply Finset.sum_congr rfl
    intro g _
    simp only [placementEvent_iff_augmentation]
  · unfold signedPlacementEntry
    apply Finset.sum_eq_zero
    intro g _
    exact ite_eq_right (fun hg => he ⟨g,hg⟩)

theorem signedPlacementEntry_zero_few (j : Fin b)
    (hh : h+k+Fintype.card (GridOutside bits j)<gridSize bits)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    signedPlacementEntry H 0 x y=0 :=
  signedPlacementEntry_zero H 0 x y (fun g₀ =>
    signed_path_weight_zero_few (augmentByChoice H x g₀) j hh)

end

open Young Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma signed_partialKernel_conditional (z : ℝ) (A : Finset (Fin k))
    (x y : Placement H k 0) :
    (∑a : Equiv.Perm (FreeSlot H 0), (conditionalGroupLaw H z a*realSign a:ℂ)*partialKernel A a y x)=
      (signedPlacementEntry H z (restrictPlacement H x A)
        (restrictPlacement H (placementIdentification H k y) A):ℂ) := by
  have he := conditionalGroupLaw_expectation H z (fun a => (realSign a:ℂ)*partialKernel A a y x)
  simp only [Complex.real_smul] at he
  simp only [mul_assoc]
  rw [he]
  unfold signedPlacementEntry
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr
  · ext g; simp only [Finset.mem_univ]
  intro g _
  simp only [partialKernel, partialKernel_event H g A x y, restrictPlacement_event]
  split_ifs <;> simp

lemma signed_centeredMatrix_zero (z : ℝ)
    (hh : ∀ l ≤ k, ∀x : Placement H l 0, ∀y : Placement H l (Fin.last b),
      signedPlacementEntry H z x y=0) :
    centeredMatrix (I:=Fin k) (gridSize bits)
      (fun a => (conditionalGroupLaw H z a*realSign a:ℂ))=0 := by
  ext y x
  simp only [centeredMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro A _
  rw [signed_partialKernel_conditional H z A x y]
  have hA : Fintype.card A ≤ k := by simpa using Finset.card_le_univ A
  rw [hh _ hA,Complex.ofReal_zero,mul_zero]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma continuousAt_signedCenteredHS (k : ℕ) : ContinuousAt (signedCenteredHS H k) 0 := by
  unfold signedCenteredHS
  apply tendsto_finsetSum
  intro x _
  apply tendsto_finsetSum
  intro y _
  apply ContinuousAt.pow
  apply ContinuousAt.norm
  simp only [centeredMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply tendsto_finsetSum
  intro A _
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum
  intro g _
  have hc := Complex.continuous_ofReal.continuousAt.comp (continuousAt_conditionalGroupLaw H g)
  exact (hc.mul continuousAt_const).mul continuousAt_const

lemma signedCenteredHS_zero (k : ℕ) (z : ℝ)
    (hh : ∀ l ≤ k, ∀x : Placement H l 0, ∀y : Placement H l (Fin.last b),
      signedPlacementEntry H z x y=0) : signedCenteredHS H k z=0 := by
  unfold signedCenteredHS
  rw [signed_centeredMatrix_zero H z hh]
  simp

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointValidity
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ}

lemma gridPartialSweep_endpoint (g : GridChoices bits) (e : GridSlot bits × GridSlot bits)
    (he : gridSweep bits g e.1=e.2) (t : Fin (b+1)) :
    gridPartialSweep bits g t e.1=independentPosition e t := by
  have hh := independentPosition_of_path (fun t => gridPartialSweep bits g t e.1)
    (gridPartialSweep_changes bits g e.1) t
  simpa only [gridPartialSweep_zero,Equiv.Perm.one_apply,gridPartialSweep_last,he] using hh.symm

lemma path_completion_finite {L : Type*} [Fintype L]
    (pos : Fin (b+1) → L → GridSlot bits) (hi : ∀t, Function.Injective (pos t))
    (hc : ∀j l i, i≠j → pos j.succ l i=pos j.castSucc l i) :
    ∃g : GridChoices bits, ∀j l, gridLayer bits g j (pos j.castSucc l)=pos j.succ l := by
  let K : PathFamily bits (Fintype.card L) :=
    {position := fun t i => pos t ((Fintype.equivFin L).symm i)
     disjoint := fun t => (hi t).comp (Fintype.equivFin L).symm.injective
     changes_only_stage := fun j k i h => hc j _ i h}
  obtain ⟨g,hg⟩ := pathEvent_nonempty K
  refine ⟨g,fun j l => ?_⟩
  have hh := hg j (Fintype.equivFin L l)
  change gridLayer bits g j (pos j.castSucc ((Fintype.equivFin L).symm
    (Fintype.equivFin L l)))=pos j.succ ((Fintype.equivFin L).symm (Fintype.equivFin L l)) at hh
  simpa only [Equiv.symm_apply_apply] using hh

variable {I : Type*} [Fintype I] [DecidableEq I] (H : PathFamily bits h)

omit [Fintype I] [DecidableEq I] in
lemma endpointValid_mono {A B : Finset I} {e : I → GridSlot bits × GridSlot bits}
    (hAB : A⊆B) (he : EndpointValid H B e) : EndpointValid H A e :=
  ⟨fun t i hi a ha => he.1 t i (hAB hi) a (hAB ha),
   fun t i hi k => he.2 t i (hAB hi) k⟩

omit [Fintype I] [DecidableEq I] in
lemma endpointValid_completion (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (he : EndpointValid H A e) :
    ∃g : GridChoices bits, pathEvent H g ∧ ∀i∈A, gridSweep bits g (e i).1=(e i).2 := by
  let pos (t : Fin (b+1)) : Fin h ⊕ A → GridSlot bits :=
    Sum.elim (H.position t) (fun i => independentPosition (e i) t)
  have hi (t) : Function.Injective (pos t) := by
    apply (H.disjoint t).sumElim
    · intro i a hh
      exact Subtype.ext (he.1 t i i.property a a.property hh)
    · intro k i hh
      exact he.2 t i i.property k hh.symm
  have hc (j : Fin b) (l : Fin h ⊕ A) (i : Fin b) (hij : i≠j) :
      pos j.succ l i=pos j.castSucc l i := by
    cases l with
    | inl k => exact H.changes_only_stage j k i hij
    | inr a => exact independentPosition_changes (e a) j i hij
  obtain ⟨g,hg⟩ := path_completion_finite pos hi hc
  refine ⟨g,fun j k => hg j (.inl k),?_⟩
  intro i hi
  apply (gridSweep_endpoint_iff g (e i)).mpr
  intro j
  exact (endpoint_gridLayer_iff g (e i) j).mp (hg j (.inr ⟨i,hi⟩))

lemma endpointValid_of_placement_event {k : ℕ} (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k))
    (g : ConditionalChoices H) (he : ∀i∈A, gridSweep bits g.val (x i).val=(y i).val) :
    EndpointValid H A (fun i => ((x i).val,(y i).val)) := by
  constructor
  · intro t i hi a ha hp
    rw [← gridPartialSweep_endpoint g.val _ (he i hi),
      ← gridPartialSweep_endpoint g.val _ (he a ha)] at hp
    exact x.injective (Subtype.ext ((gridPartialSweep bits g.val t).injective hp))
  · intro t i hi k hp
    rw [← gridPartialSweep_endpoint g.val _ (he i hi),
      ← gridPartialSweep_path H g.val g.property] at hp
    exact (x i).property ⟨k,((gridPartialSweep bits g.val t).injective hp).symm⟩

lemma endpointValid_placement_iff {k : ℕ} (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    EndpointValid H A (fun i => ((x i).val,(y i).val)) ↔
      ∃g : ConditionalChoices H, ∀i∈A, gridSweep bits g.val (x i).val=(y i).val := by
  constructor
  · intro he
    obtain ⟨g,hg,hp⟩ := endpointValid_completion H A _ he
    exact ⟨⟨g,hg⟩,hp⟩
  · rintro ⟨g,hg⟩
    exact endpointValid_of_placement_event H x y A g hg

omit [Fintype I] in
lemma endpointValid_insert (A : Finset I) (e : I → GridSlot bits × GridSlot bits) (i : I)
    (hh : ∀t k, independentPosition (e i) t≠H.position t k)
    (ha : ∀t a, a≠i → independentPosition (e a) t≠independentPosition (e i) t) :
    EndpointValid H (insert i A) e ↔ EndpointValid H A e := by
  constructor
  · exact endpointValid_mono H (Finset.subset_insert _ _)
  · rintro ⟨hp,hq⟩
    constructor
    · intro t a hA c hC hac
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rcases Finset.mem_insert.mp hC with rfl | hC
        · rfl
        · by_contra hne
          exact ha t c (Ne.symm hne) hac.symm
      · rcases Finset.mem_insert.mp hC with rfl | hC
        · by_contra hne
          exact ha t a hne hac
        · exact hp t a hA c hC hac
    · intro t a hA k
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hh t k
      · exact hq t a hA k

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointFactors
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma trackedLineCount_restrict (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (A : Finset (Fin k)) (g : ConditionalChoices H)
    (he : ∀i∈A, gridSweep bits g.val (x i).val=(y i).val)
    (j : Fin b) (l : GridOutside bits j) :
    trackedLineCount H (restrictPlacement H x A) g j l =
      endpointLineCount A (fun i => ((x i).val,(y i).val)) j l := by
  apply Fintype.card_congr
  apply ((Fintype.equivFin A).symm).subtypeEquiv
  intro i
  change (fun a : {a : Fin b // a≠j} => gridPartialSweep bits g.val j.castSucc
    (x ((Fintype.equivFin A).symm i)).val a)=l ↔ _
  rw [gridPartialSweep_endpoint g.val
    ((x ((Fintype.equivFin A).symm i)).val,(y ((Fintype.equivFin A).symm i)).val)
    (he _ ((Fintype.equivFin A).symm i).property)]
  rfl

theorem endpointProbability_zero_scaled (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H 0 A (fun i => ((x i).val,(y i).val)) =
      if EndpointValid H A (fun i => ((x i).val,(y i).val)) then
        ∏j, ∏l : GridOutside bits j,
          fallingMoment (2^bits j) (lineHoles H j l)
            (endpointLineCount A (fun i => ((x i).val,(y i).val)) j l)
      else 0 := by
  by_cases hv : EndpointValid H A (fun i => ((x i).val,(y i).val))
  · rw [ite_eq_left hv]
    obtain ⟨g,hg⟩ := (endpointValid_placement_iff H x y A).mp hv
    have he := (restrictPlacement_event H x y A g).mpr hg
    rw [endpointProbability_placement,← he]
    simpa only [Fintype.card_coe,trackedLineCount_restrict H x y A g hg] using
      placementProbability_zero_scaled H (restrictPlacement H x A) g
  · rw [ite_eq_right hv,endpointProbability_conditional]
    have hz : conditionalEventWeight H 0 (fun g => ∀i∈A,
      gridSweep bits g (x i).val=(y i).val)=0 := by
      unfold conditionalEventWeight
      apply Finset.sum_eq_zero
      intro g _
      rw [ite_eq_right]
      exact fun hg => hv (endpointValid_of_placement_event H x y A g hg)
    rw [hz,mul_zero]

lemma pathLine_occurrences {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) :
    occurrences (fun a : A × Fin b => endpointPathLine e a.1 a.2) ⟨j,y⟩ =
      endpointLineCount A e j y := by
  let : DecidableEq (EndpointLineIndex bits) := Classical.decEq _
  unfold occurrences endpointLineCount
  exact Fintype.card_congr
    {toFun := fun ⟨⟨i,a⟩,ha⟩ => ⟨i,by
       have hj : a=j := congrArg Sigma.fst ha
       subst a
       exact (Sigma.mk.inj ha).2.eq⟩
     invFun := fun a => ⟨(a.val,j),congrArg (Sigma.mk j) a.property⟩
     left_inv := fun ⟨⟨i,a⟩,ha⟩ => by
       have hj : a=j := congrArg Sigma.fst ha
       subst a
       rfl
     right_inv := fun a => rfl}

lemma multilineMoment_X_prod {L A : Type*} [Fintype L] [Fintype A]
    (m h : L → ℕ) (f : A → L) :
    multilineMoment m h (∏a, (MvPolynomial.X (f a) : MvPolynomial L ℝ)) =
      ∏l, fallingMoment (m l) (h l) (occurrences f l) := by
  have hh := occurrenceMoment_eq m h (fun a : Empty => a.elim) f
  simpa only [Finset.univ_eq_empty,Finset.prod_empty,one_mul,occurrences,
    Fintype.card_of_isEmpty,centeredLineMoment_zero] using hh

theorem endpointProbability_zero_polynomial (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H 0 A (fun i => ((x i).val,(y i).val)) =
      if EndpointValid H A (fun i => ((x i).val,(y i).val)) then
        multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
          (fun l => lineHoles H l.1 l.2)
          (∏i : A, ∏j : Fin b, (MvPolynomial.X
            (endpointPathLine (fun i => ((x i).val,(y i).val)) i j) :
            MvPolynomial (EndpointLineIndex bits) ℝ))
      else 0 := by
  rw [endpointProbability_zero_scaled]
  congr 1
  have hp := Fintype.prod_prod_type (fun a : A × Fin b =>
    (MvPolynomial.X (endpointPathLine (fun i => ((x i).val,(y i).val)) a.1 a.2) :
      MvPolynomial (EndpointLineIndex bits) ℝ))
  rw [← hp,multilineMoment_X_prod,Fintype.prod_sigma]
  simp only [pathLine_occurrences]

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I R : Type*} [DecidableEq I] [CommRing R]

omit [DecidableEq I] in
lemma mobiusSum_empty (f : Finset I → R) : mobiusSum ∅ f=f ∅ := by simp [mobiusSum]

omit [DecidableEq I] in
lemma mobiusSum_congr (U : Finset I) (f g : Finset I → R)
    (hfg : ∀A⊆U, f A=g A) : mobiusSum U f=mobiusSum U g := by
  apply Finset.sum_congr rfl
  intro A hA
  rw [hfg A (Finset.mem_powerset.mp hA)]

omit [DecidableEq I] in
lemma mobiusSum_sub (U : Finset I) (f g : Finset I → R) :
    mobiusSum U (fun A => f A-g A)=mobiusSum U f-mobiusSum U g := by
  simp only [mobiusSum,mul_sub,Finset.sum_sub_distrib]

lemma mobiusSum_insert (U : Finset I) (i : I) (hi : i∉U) (f : Finset I → R) :
    mobiusSum (insert i U) f=mobiusSum U (fun A => f (insert i A)-f A) := by
  unfold mobiusSum
  rw [Finset.sum_powerset_insert hi,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hAU := Finset.mem_powerset.mp hA
  have hiA : i∉A := fun ha => hi (hAU ha)
  have hc := Finset.card_le_card hAU
  rw [Finset.card_insert_of_notMem hi,Finset.card_insert_of_notMem hiA]
  rw [show U.card+1-A.card=U.card-A.card+1 by omega,
      show U.card+1-(A.card+1)=U.card-A.card by omega,pow_succ]
  ring

lemma mobiusSum_union (G C : Finset I) (hGC : Disjoint G C) (f : Finset I → R) :
    mobiusSum (G∪C) f=mobiusSum C (fun J => mobiusSum G (fun B => f (J∪B))) := by
  induction C using Finset.induction_on generalizing f with
  | empty => simp only [Finset.union_empty,mobiusSum_empty,Finset.empty_union]
  | @insert i C hi ih =>
    have hiG : i∉G := fun hg => Finset.disjoint_left.mp hGC hg (Finset.mem_insert_self _ _)
    have hGC' : Disjoint G C := hGC.mono_right (Finset.subset_insert _ _)
    have hiU : i∉G∪C := by simp only [Finset.mem_union,not_or]; exact ⟨hiG,hi⟩
    rw [Finset.union_insert,mobiusSum_insert _ _ hiU,mobiusSum_insert _ _ hi]
    rw [ih hGC']
    apply mobiusSum_congr
    intro J _
    rw [← mobiusSum_sub]
    apply mobiusSum_congr
    intro B _
    rw [Finset.insert_union]

variable [Algebra ℝ R]

lemma mobiusSum_linear_product (U : Finset I) (L : R →ₗ[ℝ] ℝ) (X : I → R) (P : R) :
    mobiusSum U (fun A => L (P*∏i∈A, X i))=L (P*∏i∈U, (X i-1)) := by
  induction U using Finset.induction_on generalizing P with
  | empty => simp only [mobiusSum_empty,Finset.prod_empty,mul_one]
  | @insert i U hi ih =>
    rw [mobiusSum_insert _ _ hi,Finset.prod_insert hi]
    trans mobiusSum U (fun A => L ((P*(X i-1))*∏a∈A,X a))
    · apply mobiusSum_congr
      intro A hA
      have hiA : i∉A := fun ha => hi (hA ha)
      rw [Finset.prod_insert hiA,← map_sub]
      congr 1
      ring
    · rw [ih]
      congr 1
      ring

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathTelescope
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

section

lemma prod_sub_one_telescope {R : Type*} [CommRing R] (b : ℕ) (x : Fin b → R) :
    (∏ j, x j)-1 = ∑ j, (x j-1) * ∏ t : Fin b with j<t, x t := by
  induction b with
  | zero => simp
  | succ b ih =>
    simp only [Finset.prod_filter,Fin.prod_univ_succ,Fin.sum_univ_succ,
      Fin.not_lt_zero,ite_false,Fin.succ_pos,ite_true,Fin.succ_lt_succ_iff,one_mul]
    have hs := ih (fun j => x j.succ)
    simp only [Finset.prod_filter] at hs
    rw [← hs]
    ring

variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

omit [Fintype L] in
lemma path_telescope_expansion {b : ℕ} (f : A → Fin b → L) (g : B → L) :
    (∏ a, ((∏ j, (MvPolynomial.X (f a j) : MvPolynomial L ℝ))-1)) *
      (∏ k, MvPolynomial.X (g k)) =
    ∑ c : A → Fin b,
      (∏ a, (MvPolynomial.X (centeredLine f c a)-1)) *
        (∏ k : B ⊕ Suffixes c, MvPolynomial.X (Sum.elim g (suffixLine f c) k)) := by
  simp_rw [prod_sub_one_telescope]
  rw [Fintype.prod_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.prod_mul_distrib,Fintype.prod_sum_type,Fintype.prod_sigma,Sum.elim_inl,Sum.elim_inr,centeredLine,suffixLine]
  have he : ∏ a, ∏ j : Fin b with c a<j, (MvPolynomial.X (f a j) : MvPolynomial L ℝ) =
      ∏ a, ∏ j : {j : Fin b // c a<j}, MvPolynomial.X (f a j) := by
    apply Finset.prod_congr rfl
    intro a _
    exact Finset.prod_subtype _ (by simp) (fun j => MvPolynomial.X (f a j))
  rw [he]
  ring

end

variable {L A B C : Type*} [Fintype L] [Fintype A] [Fintype B] [Fintype C]

omit [Fintype L] in
lemma occurrences_le_of_injective (f : A → L) (g : B → L) (e : A → B)
    (hi : Function.Injective e) (he : ∀ a, g (e a) = f a) (l : L) :
    occurrences f l ≤ occurrences g l := by
  apply Fintype.card_le_of_injective (fun a : {a // f a=l} =>
    (⟨e a, (he a).trans a.property⟩ : {b // g b=l}))
  intro a b h
  exact Subtype.ext (hi (congrArg Subtype.val h))

omit [Fintype L] in
lemma occurrences_sum (f : A → L) (g : B → L) (l : L) :
    occurrences (Sum.elim f g) l = occurrences f l + occurrences g l := by
  have h := Fintype.card_congr (Equiv.subtypeSum (p := fun a : A ⊕ B => Sum.elim f g a=l))
  exact h.trans Fintype.card_sum

variable {b : ℕ}

omit [Fintype A] [Fintype B] in
lemma telescopeInjection_injective (c : A → Fin b) : Function.Injective (telescopeInjection (B:=B) c) := by
  rintro (a | (k | ⟨a,j,hj⟩)) (a' | (k' | ⟨a',j',hj'⟩)) h <;>
    simp only [telescopeInjection,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,
      Sum.inr_ne_inl,Prod.mk.injEq] at h
  · exact congrArg Sum.inl h.1
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (lt_irrefl _ hj')
  · exact congrArg (Sum.inr ∘ Sum.inl) h
  · rcases h with ⟨rfl,rfl⟩
    exact False.elim (lt_irrefl _ hj)
  · rcases h with ⟨rfl,rfl⟩; rfl

omit [Fintype L] in
lemma telescope_occurrences_le (f : A → Fin b → L) (g : B → L) (c : A → Fin b) (l : L) :
    occurrences (centeredLine f c) l +
      occurrences (Sum.elim g (suffixLine f c)) l ≤
      occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) l := by
  rw [← occurrences_sum]
  apply occurrences_le_of_injective _ _ (telescopeInjection c) (telescopeInjection_injective c)
  rintro (a | (k | a)) <;> rfl

lemma card_suffixes_le (c : A → Fin b) : Fintype.card (Suffixes c) ≤ Fintype.card A * b := by
  apply (Fintype.card_le_of_injective (fun a : Suffixes c => (a.1, a.2.val)) ?_).trans_eq
    (by simp)
  intro a a' h
  obtain ⟨a,j,hj⟩ := a
  obtain ⟨a',j',hj'⟩ := a'
  cases h
  rfl

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

lemma fallingMoment_nonneg (m h n : ℕ) : 0≤fallingMoment m h n := by
  unfold fallingMoment
  positivity

lemma fallingMoment_log {m h n : ℕ} (hm : 0 < m) (hn : h+n ≤ m) :
    Real.log (fallingMoment m h n)=fallingCost m (h+n)-fallingCost m h := by
  have hh : h ≤ m := by omega
  have hp : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hnh : n ≤ m-h := by omega
  have hdf : ((m-h).descFactorial n:ℝ)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hnh).ne'
  have hdh : (m.descFactorial h:ℝ)≠0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hh).ne'
  have he : (m-h).descFactorial n * m.descFactorial h=m.descFactorial (h+n) := by
    simpa only [Nat.add_sub_cancel_left] using
      (Nat.descFactorial_mul_descFactorial (show h≤h+n by omega) (n:=m))
  rw [fallingMoment,Real.log_div (pow_ne_zero _ hp) hdf,Real.log_pow,
    fallingCost_formula hm hn,fallingCost_formula hm hh,← he,Nat.cast_mul,
    Real.log_mul hdf hdh,Nat.cast_add]
  ring

lemma fallingMoment_le_exp {m h n : ℕ} (hm : 0 < m) :
    fallingMoment m h n≤Real.exp (h+n) := by
  by_cases hn : h+n ≤ m
  · have hp := fallingMoment_pos hm hn
    rw [← Real.exp_log hp] at ⊢
    apply Real.exp_le_exp.mpr
    rw [fallingMoment_log hm hn]
    have h1 := fallingCost_le hm hn
    have h0 := fallingCost_nonneg hm (show h ≤ m by omega)
    push_cast at h1
    linarith
  · by_cases hn0 : n=0
    · subst n
      simp only [fallingMoment_zero,Nat.cast_zero,add_zero]
      exact Real.one_le_exp (by positivity)
    · have hd : (m-h).descFactorial n=0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp only [fallingMoment,hd,Nat.cast_zero,div_zero]
      exact (Real.exp_pos _).le

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathMomentMixed
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

lemma centeredLineMoment_mixed {m h u v : ℕ} {η : ℝ}
    (hm : 0 < m) (hη0 : 0≤η) (hη : η≤1/4)
    (hl : 0<u → (h:ℝ)+u+v ≤ m*η) :
    0≤centeredLineMoment m h u v ∧
    centeredLineMoment m h u v ≤
      Real.exp ((h:ℝ)+u+v) * 2^v * (4*Real.sqrt η)^u := by
  by_cases hu : u=0
  · subst u
    simp only [centeredLineMoment_zero,pow_zero,mul_one,Nat.cast_zero,add_zero]
    refine ⟨fallingMoment_nonneg _ _ _,(fallingMoment_le_exp hm).trans ?_⟩
    exact le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ (by norm_num))
  · have hb := centeredLineMoment_light hm hη0 hη (hl (Nat.pos_of_ne_zero hu))
    refine ⟨hb.1,hb.2.trans ?_⟩
    have he : 1≤Real.exp ((h:ℝ)+u+v) := Real.one_le_exp (by positivity)
    have hn : 0≤(2:ℝ)^v*(4*Real.sqrt η)^u := by positivity
    simpa only [mul_assoc] using le_mul_of_one_le_left hn he

variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

theorem occurrenceMoment_mixed (m h : L → ℕ) (f : A → L) (g : B → L)
    {η : ℝ} (hm : ∀l, 0 < m l) (hη0 : 0≤η) (hη : η≤1/4)
    (hl : ∀l, 0<occurrences f l → (h l:ℝ)+occurrences f l+occurrences g l ≤ m l*η) :
    let P := ((∏a, ((MvPolynomial.X (f a) : MvPolynomial L ℝ)-1)) *
      ∏b, MvPolynomial.X (g b))
    0 ≤ multilineMoment m h P ∧ multilineMoment m h P ≤
      Real.exp ((∑l, (h l:ℝ)) + Fintype.card A+Fintype.card B) *
        2^Fintype.card B*(4*Real.sqrt η)^Fintype.card A := by
  dsimp only
  rw [occurrenceMoment_eq]
  have hb (l : L) := centeredLineMoment_mixed (hm l) hη0 hη (hl l)
  refine ⟨Finset.prod_nonneg (fun l _ => (hb l).1),?_⟩
  calc
    _ ≤ ∏l, Real.exp ((h l:ℝ)+occurrences f l+occurrences g l) *
        2^occurrences g l * (4*Real.sqrt η)^occurrences f l :=
      Finset.prod_le_prod (fun l _ => (hb l).1) (fun l _ => (hb l).2)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,← Real.exp_sum,
        Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum,
        sum_occurrences,sum_occurrences]
      congr 2
      simp only [Finset.sum_add_distrib,← Nat.cast_sum,sum_occurrences]

theorem pathMoment_mixed {b : ℕ} (m h : L → ℕ) (f : A → Fin b → L) (g : B → L)
    {η : ℝ} (hm : ∀l, 0 < m l) (hη0 : 0≤η) (hη : η≤1/4)
    (hl : ∀a j, (h (f a j):ℝ)+
      occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) (f a j) ≤ m (f a j)*η) :
    let P := (∏a, ((∏j, (MvPolynomial.X (f a j) : MvPolynomial L ℝ))-1)) *
      (∏k, MvPolynomial.X (g k))
    0 ≤ multilineMoment m h P ∧ multilineMoment m h P ≤
      (b:ℝ)^Fintype.card A *
      (Real.exp ((∑l, (h l:ℝ))+Fintype.card A+Fintype.card B+Fintype.card A*b) *
        2^(Fintype.card B+Fintype.card A*b)*(4*Real.sqrt η)^Fintype.card A) := by
  dsimp only
  rw [path_telescope_expansion,map_sum]
  have hb (c : A → Fin b) := occurrenceMoment_mixed m h (centeredLine f c)
    (Sum.elim g (suffixLine f c)) hm hη0 hη (fun l hlu => by
      obtain ⟨a,ha⟩ := (Fintype.card_pos_iff.mp hlu)
      have hn := telescope_occurrences_le f g c l
      have hn' : (occurrences (centeredLine f c) l:ℝ)+
        occurrences (Sum.elim g (suffixLine f c)) l ≤
        occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) l := by exact_mod_cast hn
      have hx := hl a (c a)
      change f a (c a)=l at ha
      rw [ha] at hx
      linarith)
  refine ⟨Finset.sum_nonneg (fun c _ => (hb c).1),?_⟩
  calc
    _ ≤ ∑c : A → Fin b,
      Real.exp ((∑l, (h l:ℝ))+Fintype.card A+Fintype.card B+Fintype.card A*b) *
        2^(Fintype.card B+Fintype.card A*b)*(4*Real.sqrt η)^Fintype.card A := by
      apply Finset.sum_le_sum
      intro c _
      apply (hb c).2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        have hc : (Fintype.card (Suffixes c):ℝ)≤Fintype.card A*b := by
          exact_mod_cast card_suffixes_le c
        simp only [Fintype.card_sum,Nat.cast_add]
        linarith
      · apply pow_le_pow_right₀ (by norm_num)
        simpa using Nat.add_le_add_left (card_suffixes_le c) (Fintype.card B)
      · positivity
      · positivity
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
lemma endpointValid_union_isolated (e : I → GridSlot bits × GridSlot bits)
    (G J : Finset I) (hi : ∀i∈G, vertexIsolated H e i) :
    EndpointValid H (J∪G) e ↔ EndpointValid H J e := by
  induction G using Finset.induction_on with
  | empty => simp only [Finset.union_empty]
  | @insert i G hn ih =>
    rw [Finset.union_insert,endpointValid_insert H _ e i
      (hi i (Finset.mem_insert_self _ _)).1 (hi i (Finset.mem_insert_self _ _)).2]
    exact ih (fun a ha => hi a (Finset.mem_insert_of_mem ha))

lemma endpoint_subset_polynomial (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H 0 A (fun i => ((x i).val,(y i).val)) =
      if EndpointValid H A (fun i => ((x i).val,(y i).val)) then
        multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
          (fun l => lineHoles H l.1 l.2)
          (∏i∈A, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)
      else 0 := by
  rw [endpointProbability_zero_polynomial]
  congr 1
  apply congrArg (multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
    (fun l => lineHoles H l.1 l.2))
  exact Finset.prod_coe_sort A (endpointPathPolynomial (fun i => ((x i).val,(y i).val)))

lemma centeredEndpointKernel_scaled (z : ℝ) (e : I → GridSlot bits × GridSlot bits) :
    (gridSize bits:ℝ)^Fintype.card I * centeredEndpointKernel H z e =
      mobiusSum Finset.univ (fun A => (gridSize bits:ℝ)^A.card * endpointProbability H z A e) := by
  unfold centeredEndpointKernel alternatingSubsetSum mobiusSum
  rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ (show (gridSize bits:ℝ)≠0 by
    exact_mod_cast (gridSize_pos bits).ne'),one_pow,one_mul]
  apply Finset.sum_congr rfl
  intro A _
  ring

theorem centeredEndpointKernel_good_expansion (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (G : Finset (Fin k))
    (hi : ∀i∈G, vertexIsolated H (fun i => ((x i).val,(y i).val)) i) :
    (gridSize bits:ℝ)^k * centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)) =
      mobiusSum (Finset.univ\G) (fun J =>
        if EndpointValid H J (fun i => ((x i).val,(y i).val)) then
          multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
            (fun l => lineHoles H l.1 l.2)
            ((∏i∈G, (endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i-1)) *
              ∏i∈J, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)
        else 0) := by
  have hs := centeredEndpointKernel_scaled H 0 (fun i => ((x i).val,(y i).val))
  simp only [Fintype.card_fin] at hs
  rw [hs]
  conv_lhs => rw [show (Finset.univ : Finset (Fin k))=G∪(Finset.univ\G) by ext i; simp]
  rw [mobiusSum_union _ _ Finset.disjoint_sdiff]
  apply mobiusSum_congr
  intro J hJ
  have hJG : Disjoint J G := (Finset.disjoint_sdiff.symm).mono_left hJ
  trans mobiusSum G (fun A => if EndpointValid H J (fun i => ((x i).val,(y i).val)) then
    multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
      (fun l => lineHoles H l.1 l.2)
      ((∏i∈J, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)*
        ∏i∈A, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i) else 0)
  · apply mobiusSum_congr
    intro A hA
    rw [endpoint_subset_polynomial,endpointValid_union_isolated H _ A J (fun i hiA => hi i (hA hiA))]
    rw [Finset.prod_union (hJG.mono_right hA)]
  · by_cases hv : EndpointValid H J (fun i => ((x i).val,(y i).val))
    · simp only [ite_eq_left hv]
      rw [mobiusSum_linear_product,mul_comm]
    · simp only [ite_eq_right hv,mobiusSum,mul_zero,Finset.sum_const_zero]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointEntryBound
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma Sparse.mobiusSum_abs_le {I : Type*} [DecidableEq I]
    (U : Finset I) (f : Finset I → ℝ) (B : ℝ)
    (hb : ∀A⊆U, |f A|≤B) : |mobiusSum U f|≤(2:ℝ)^U.card*B := by
  unfold mobiusSum
  calc
    _ ≤ ∑A∈U.powerset, |(-1:ℝ)^(U.card-A.card)*f A| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑A∈U.powerset, B := by
      apply Finset.sum_le_sum
      intro A hA
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hb A (Finset.mem_powerset.mp hA)
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma occurrences_injective_le {I J L : Type*} [Fintype I] [Fintype J]
    (f : I → L) (g : J → L) (e : I → J) (hi : Function.Injective e)
    (he : ∀i, g (e i)=f i) (l : L) : occurrences f l≤occurrences g l := by
  apply Fintype.card_le_of_injective
    (fun a : {i // f i=l} => (⟨e a.val,(he a.val).trans a.property⟩ : {j // g j=l}))
  intro a c hac
  exact Subtype.ext (hi (congrArg Subtype.val hac))

lemma endpoint_mixed_occurrences_le (e : Fin k → GridSlot bits × GridSlot bits)
    (G J : Finset (Fin k)) (hd : Disjoint J G) (l : EndpointLineIndex bits) :
    occurrences (Sum.elim (fun a : J × Fin b => endpointPathLine e a.1 a.2)
      (fun a : G × Fin b => endpointPathLine e a.1 a.2)) l ≤
      endpointLineCount Finset.univ e l.1 l.2 := by
  let emb : (J × Fin b) ⊕ (G × Fin b) → ↥(Finset.univ : Finset (Fin k)) × Fin b :=
    Sum.elim (fun a => (⟨a.1.val,Finset.mem_univ _⟩,a.2))
      (fun a => (⟨a.1.val,Finset.mem_univ _⟩,a.2))
  have hi : Function.Injective emb := by
    intro a c hac
    cases a with
    | inl a => cases c with
      | inl c => exact congrArg Sum.inl (Prod.ext (Subtype.ext (congrArg (fun x => x.1.val) hac)) (congrArg (fun v : ↥(Finset.univ : Finset (Fin k)) × Fin b => v.2) hac))
      | inr c =>
        have he : a.1.val=c.1.val := congrArg (fun x => x.1.val) hac
        exact False.elim (Finset.disjoint_left.mp hd a.1.property (he.symm ▸ c.1.property))
    | inr a => cases c with
      | inl c =>
        have he : a.1.val=c.1.val := congrArg (fun x => x.1.val) hac
        exact False.elim (Finset.disjoint_left.mp hd c.1.property (he ▸ a.1.property))
      | inr c => exact congrArg Sum.inr (Prod.ext (Subtype.ext (congrArg (fun x => x.1.val) hac)) (congrArg (fun v : ↥(Finset.univ : Finset (Fin k)) × Fin b => v.2) hac))
  have ht := occurrences_injective_le
    (Sum.elim (fun a : J × Fin b => endpointPathLine e a.1 a.2)
      (fun a : G × Fin b => endpointPathLine e a.1 a.2)) (fun a : ↥(Finset.univ : Finset (Fin k)) × Fin b =>
    endpointPathLine e a.1 a.2) emb hi (fun a => by cases a <;> rfl) l
  rcases l with ⟨j,y⟩
  simpa only [pathLine_occurrences] using ht

lemma endpoint_pathMoment_bound (e : Fin k → GridSlot bits × GridSlot bits)
    (G J : Finset (Fin k)) (hd : Disjoint J G) {η : ℝ} (hη0 : 0≤η) (hη : η≤1/4)
    (hl : ∀i∈G, ∀j, endpointLight H η e (endpointPathLine e i j)) :
    let P := (∏i∈G, (endpointPathPolynomial e i-1))*∏i∈J,endpointPathPolynomial e i
    0 ≤ multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2) P ∧
    multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2) P ≤
      Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*b*Real.sqrt η)^G.card := by
  dsimp only
  have hb := pathMoment_mixed
    (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2)
    (fun i : G => endpointPathLine e i) (fun a : J × Fin b => endpointPathLine e a.1 a.2)
    (η:=η) (fun _ => by positivity) hη0 hη (fun i j => by
      have hn := endpoint_mixed_occurrences_le e G J hd (endpointPathLine e i j)
      have hn' : (occurrences (Sum.elim (fun a : J × Fin b => endpointPathLine e a.1 a.2)
        (fun a : G × Fin b => endpointPathLine e a.1 a.2)) (endpointPathLine e i j):ℝ) ≤
        endpointLineCount Finset.univ e j (endpointLine (e i) j) := by exact_mod_cast hn
      have ht := hl i i.property j
      change (lineHoles H j (endpointLine (e i) j):ℝ)+_≤_ at ht ⊢
      dsimp only [endpointPathLine] at ht hn' ⊢
      linarith only [hn',ht])
  dsimp only at hb
  have hp1 : (∏i : G, ((∏j, (MvPolynomial.X (endpointPathLine e i j) : MvPolynomial (EndpointLineIndex bits) ℝ))-1)) =
      ∏i∈G, (endpointPathPolynomial e i-1) :=
    Finset.prod_coe_sort G (fun i => endpointPathPolynomial e i-1)
  have hp2 : (∏a : J × Fin b, (MvPolynomial.X (endpointPathLine e a.1 a.2) : MvPolynomial (EndpointLineIndex bits) ℝ)) =
      ∏i∈J, endpointPathPolynomial e i :=
    (Fintype.prod_prod_type _).trans (Finset.prod_coe_sort J (endpointPathPolynomial e))
  rw [hp1,hp2] at hb
  simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hc : J.card+G.card≤k := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin k)
  have hg : G.card≤k := by omega
  have hpow : J.card*b+G.card*b≤k*b := by nlinarith
  have hh : (∑l : EndpointLineIndex bits, (lineHoles H l.1 l.2:ℝ))=(b*h:ℕ) := by
    rw [Fintype.sum_sigma]
    simp only [← Nat.cast_sum,sum_lineHoles,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [hh]
  calc
    _ ≤ (b:ℝ)^G.card * (Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*Real.sqrt η)^G.card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        exact_mod_cast (show b*h+G.card+(J.card*b)+G.card*b≤b*h+k+k*b by omega)
      · exact pow_le_pow_right₀ (by norm_num) hpow
      · positivity
      · positivity
    _ = _ := by rw [show 4*(b:ℝ)*Real.sqrt η=b*(4*Real.sqrt η) by ring,mul_pow]; ring

theorem centeredEndpointKernel_good_bound (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (G : Finset (Fin k)) {η : ℝ}
    (hη0 : 0≤η) (hη : η≤1/4)
    (hi : ∀i∈G, vertexIsolated H (fun i => ((x i).val,(y i).val)) i)
    (hl : ∀i∈G, ∀j, endpointLight H η (fun i => ((x i).val,(y i).val))
      (endpointPathLine (fun i => ((x i).val,(y i).val)) i j)) :
    |(gridSize bits:ℝ)^k*centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val))| ≤
      (2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*(4*b*Real.sqrt η)^G.card := by
  rw [centeredEndpointKernel_good_expansion H x y G hi]
  have hc : (Finset.univ\G).card≤k := (Finset.card_le_card (Finset.sdiff_subset)).trans_eq (Finset.card_fin k)
  have hb := mobiusSum_abs_le (Finset.univ\G) (fun J =>
    if EndpointValid H J (fun i => ((x i).val,(y i).val)) then
      multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2)
        ((∏i∈G,(endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i-1))*
          ∏i∈J,endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)
    else 0) (Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*b*Real.sqrt η)^G.card) (fun J hJ => by
      have hd : Disjoint J G := Finset.disjoint_sdiff.symm.mono_left hJ
      have he := endpoint_pathMoment_bound H (fun i => ((x i).val,(y i).val)) G J hd hη0 hη hl
      split_ifs
      · rw [abs_of_nonneg he.1]; exact he.2
      · simp only [abs_zero]; positivity)
  apply hb.trans
  calc
    _ ≤ (2:ℝ)^k*(Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*b*Real.sqrt η)^G.card) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc) (by positivity)
    _ = _ := by rw [pow_add]; ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_SparseOccupancy
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I Ω L : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

theorem occupancy_probability_le [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀u, 0 ≤ p u) (hp1 : ∑u, p u=1)
    (E : Ω → Prop) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hE : finiteProbability p E ≤ δ) (w : ℕ) :
    productProbability p (fun x : I → Ω => w ≤ (Finset.univ.filter (fun i => E (x i))).card) ≤
      (2:ℝ)^Fintype.card I * δ^w := by
  let root : Ω := Classical.choice inferInstance
  have hT (T : Finset I) :
      productProbability p (fun x : I → Ω => w ≤ T.card ∧ ∀i∈T, E (x i)) ≤ δ^w := by
    by_cases h : w ≤ T.card
    · have hb := depthOne_probability_le p hp hp1 (fun u _ => E u) δ hδ
        (fun _ => hE) T (fun _ => Sum.inr ()) (fun _ : Unit => root)
      have he : (fun x : I → Ω => w ≤ T.card ∧ ∀i∈T, E (x i)) =
          (fun x : I → Ω => ∀i : T, E (x i)) := by
        funext x
        simp only [h,true_and,Subtype.forall]
      rw [he]
      exact hb.trans (pow_le_pow_of_le_one hδ hδ1 h)
    · simp only [h,false_and,productProbability,ite_false,mul_zero,Finset.sum_const_zero]
      exact pow_nonneg hδ w
  calc
    _ ≤ productProbability p (fun x : I → Ω => ∃T : Finset I, w ≤ T.card ∧ ∀i∈T, E (x i)) :=
      productProbability_mono hp (fun x hx => ⟨_,hx,fun i hi => (Finset.mem_filter.mp hi).2⟩)
    _ ≤ ∑T : Finset I, productProbability p (fun x : I → Ω => w ≤ T.card ∧ ∀i∈T, E (x i)) :=
      productProbability_union_le hp _
    _ ≤ _ := by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_finset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        using Finset.sum_le_sum (s:=Finset.univ) (fun T _ => hT T)

variable [Fintype L] [DecidableEq L]

omit [Fintype L] [DecidableEq L] in
lemma smallSetEncode_mem {r : ℕ} (S : {S : Finset L // S.card ≤ r}) (l : L) :
    l∈S.val ↔ ∃i, smallSetEncode S i=some l := by
  constructor
  · intro hl
    let j := Fintype.equivFin S.val ⟨l,hl⟩
    have hj : j.val < S.val.card := by simpa using j.isLt
    refine ⟨⟨j.val,lt_of_lt_of_le hj S.property⟩,?_⟩
    simp only [smallSetEncode,dite_eq_left hj]
    have he : (⟨j.val,by simpa using hj⟩ : Fin (Fintype.card S.val))=j := rfl
    rw [he,Equiv.symm_apply_apply]
  · rintro ⟨i,hi⟩
    unfold smallSetEncode at hi
    split_ifs at hi with h
    · cases Option.some.inj hi
      exact ((Fintype.equivFin S.val).symm ⟨i.val,by simpa using h⟩).property

omit [Fintype L] [DecidableEq L] in
lemma smallSetEncode_injective (r : ℕ) : Function.Injective (smallSetEncode (L:=L) (r:=r)) := by
  intro S T h
  apply Subtype.ext
  ext l
  rw [smallSetEncode_mem,smallSetEncode_mem,h]

omit [DecidableEq L] in
lemma smallSet_card_bound (r : ℕ) :
    Fintype.card {S : Finset L // S.card ≤ r} ≤ (Fintype.card L+1)^r := by
  simpa only [Fintype.card_fun,Fintype.card_option,Fintype.card_fin]
    using Fintype.card_le_of_injective _ (smallSetEncode_injective (L:=L) r)

theorem line_sets_occupancy_probability_le [Nonempty Ω]
    (p : Ω → ℝ) (hp : ∀u, 0 ≤ p u) (hp1 : ∑u, p u=1)
    (line : Ω → L) (r w : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmass : ∀S : Finset L, S.card ≤ r → finiteProbability p (fun u => line u∈S) ≤ δ) :
    productProbability p (fun x : I → Ω => ∃S : Finset L, S.card ≤ r ∧
      w ≤ (Finset.univ.filter (fun i => line (x i)∈S)).card) ≤
      ((Fintype.card L+1:ℕ):ℝ)^r * (2:ℝ)^Fintype.card I * δ^w := by
  let E (S : {S : Finset L // S.card ≤ r}) (x : I → Ω) :=
    w ≤ (Finset.univ.filter (fun i => line (x i)∈S.val)).card
  have h1 := productProbability_union_le hp E
  have h2 : (∑S, productProbability p (E S)) ≤
      (Fintype.card {S : Finset L // S.card ≤ r}:ℝ)*((2:ℝ)^Fintype.card I*δ^w) := by
    calc
      _ ≤ ∑ S : {S : Finset L // S.card ≤ r}, ((2:ℝ)^Fintype.card I*δ^w) := by
        apply Finset.sum_le_sum
        intro S _
        convert occupancy_probability_le p hp hp1 (fun u => line u∈S.val) δ hδ hδ1
          (hmass S.val S.property) w (I:=I) using 1
        all_goals try with_reducible_and_instances rfl
        unfold productProbability E
        apply Finset.sum_congr rfl
        intro x _
        congr 2
        apply congrArg (fun t : Finset I => w ≤ t.card)
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      _ = _ := by simp
  have h3 : (Fintype.card {S : Finset L // S.card ≤ r}:ℝ) ≤ ((Fintype.card L+1:ℕ):ℝ)^r := by
    exact_mod_cast smallSet_card_bound (L:=L) r
  have he : (fun x : I → Ω => ∃S : Finset L, S.card ≤ r ∧
      w ≤ (Finset.univ.filter (fun i => line (x i)∈S)).card) = (fun x => ∃S, E S x) := by
    funext x
    simp only [E,Subtype.exists,exists_prop]
  rw [he]
  apply h1.trans (h2.trans _)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right h3 (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hδ w))

end BinaryCoordinateSweeps.Sparse

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointOccupancy
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma card_gridOutside_mul (j : Fin b) :
    Fintype.card (GridOutside bits j)*2^bits j=gridSize bits := by
  have he := Fintype.card_congr (Equiv.piSplitAt j (fun i : Fin b => Slot (bits i)))
  simpa only [Fintype.card_prod,card_gridSlot,Slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.mul_comm] using he.symm

lemma sum_endpointLineCount (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) :
    ∑y, endpointLineCount Finset.univ e j y=k := by
  have he := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun i : ↥(Finset.univ : Finset (Fin k)) => endpointLine (e i) j))
  simpa only [Fintype.card_sigma,Fintype.card_coe,Finset.card_univ,Fintype.card_fin,
    endpointLineCount] using he

lemma heavy_count {L : Type*} [Fintype L] (f : L → ℕ) (τ : ℝ) :
    τ*(Finset.univ.filter (fun l => τ<(f l:ℝ))).card ≤ ∑l, (f l:ℝ) := by
  let S := Finset.univ.filter (fun l => τ<(f l:ℝ))
  calc
    _ = ∑l∈S, τ := by simp [S,mul_comm]
    _ ≤ ∑l∈S, (f l:ℝ) := Finset.sum_le_sum (fun l hl => (Finset.mem_filter.mp hl).2.le)
    _ ≤ ∑l, (f l:ℝ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)

lemma holeHeavy_card (j : Fin b) {η : ℝ} (hη : 0<η) :
    ((holeHeavyLines H j η).card:ℝ) ≤ 2*h/((2^bits j:ℕ)*η) := by
  have hh := heavy_count (lineHoles H j) ((2^bits j:ℕ)*η/2)
  rw [← Nat.cast_sum,sum_lineHoles] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  change (2^bits j:ℕ)*η/2*(holeHeavyLines H j η).card≤(h:ℝ) at hh
  nlinarith

lemma particleHeavy_card (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b)
    {η : ℝ} (hη : 0<η) :
    (particleHeavyLines e j η).card ≤ ⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ := by
  apply Nat.le_floor
  have hh := heavy_count (endpointLineCount Finset.univ e j) ((2^bits j:ℕ)*η/2)
  rw [← Nat.cast_sum,sum_endpointLineCount] at hh
  apply (le_div_iff₀ (by positivity)).mpr
  change (2^bits j:ℕ)*η/2*(particleHeavyLines e j η).card≤(k:ℝ) at hh
  nlinarith

lemma endpoint_not_light (e : Fin k → GridSlot bits × GridSlot bits)
    (j : Fin b) (l : GridOutside bits j) (η : ℝ)
    (hn : ¬endpointLight H η e ⟨j,l⟩) :
    l∈holeHeavyLines H j η ∨ l∈particleHeavyLines e j η := by
  simp only [holeHeavyLines,particleHeavyLines,Finset.mem_filter,Finset.mem_univ,true_and]
  change ¬((lineHoles H j l:ℝ)+endpointLineCount Finset.univ e j l≤(2^bits j:ℕ)*η) at hn
  push Not at hn
  rcases lt_or_ge ((2^bits j:ℕ)*η/2) (lineHoles H j l:ℝ) with hh | hh
  · exact Or.inl hh
  · exact Or.inr (by linarith)

lemma endpoint_line_set_mass (j : Fin b) (S : Finset (GridOutside bits j)) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits => endpointLine z j∈S)=
      (S.card:ℝ)*(2^bits j:ℕ)/gridSize bits := by
  change finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
    (fun i : {i : Fin b // i≠j} => independentPosition z j.castSucc i)∈S)=_
  rw [independent_line_set_uniform]
  have he : (Fintype.card (GridOutside bits j):ℝ)*(2^bits j:ℕ)=gridSize bits := by
    exact_mod_cast card_gridOutside_mul j
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have hm : ((2^bits j:ℕ):ℝ)≠0 := by positivity
  rw [← he]
  field_simp

lemma holeHeavy_mass (j : Fin b) {η : ℝ} (hη : 0<η) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits =>
      endpointLine z j∈holeHeavyLines H j η) ≤ 2*h/((gridSize bits:ℝ)*η) := by
  rw [endpoint_line_set_mass]
  have hh := holeHeavy_card H j hη
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hm : (0:ℝ)<(2^bits j:ℕ) := by positivity
  calc
    _ ≤ (2*h/((2^bits j:ℕ)*η))*(2^bits j:ℕ)/gridSize bits := by gcongr
    _ = _ := by field_simp

lemma small_lines_mass (j : Fin b) {η : ℝ} (hη : 0<η)
    (S : Finset (GridOutside bits j)) (hS : S.card≤⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊) :
    finiteProbability uniformWeight (fun z : GridSlot bits × GridSlot bits => endpointLine z j∈S) ≤
      2*k/((gridSize bits:ℝ)*η) := by
  rw [endpoint_line_set_mass]
  have hnon : 0≤2*(k:ℝ)/((2^bits j:ℕ)*η) := by positivity
  have hh : (S.card:ℝ)≤2*(k:ℝ)/((2^bits j:ℕ)*η) :=
    (Nat.cast_le.mpr hS).trans (Nat.floor_le hnon)
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hm : (0:ℝ)<(2^bits j:ℕ) := by positivity
  calc
    _ ≤ (2*k/((2^bits j:ℕ)*η))*(2^bits j:ℕ)/gridSize bits := by gcongr
    _ = _ := by field_simp

lemma holeHeavy_occupancy_bound (j : Fin b) {η : ℝ} (hη : 0<η)
    (hsmall : 2*h/((gridSize bits:ℝ)*η)≤1) (w : ℕ) :
    productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
      w ≤ (Finset.univ.filter (fun i => endpointLine (e i) j∈holeHeavyLines H j η)).card) ≤
      (2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^w := by
  have he := occupancy_probability_le (I:=Fin k) uniformWeight uniformWeight_nonneg uniformWeight_sum
    (fun z : GridSlot bits × GridSlot bits => endpointLine z j∈holeHeavyLines H j η) _
    (by positivity) hsmall (holeHeavy_mass H j hη) w
  simp only [Fintype.card_fin] at he
  convert he using 1
  congr 1
  funext e
  congr 1
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

lemma particleHeavy_occupancy_bound (j : Fin b) {η : ℝ} (hη : 0<η)
    (hsmall : 2*k/((gridSize bits:ℝ)*η)≤1) (w : ℕ) :
    productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
      w ≤ (Finset.univ.filter (fun i => endpointLine (e i) j∈particleHeavyLines e j η)).card) ≤
      (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
        (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^w := by
  have hb := line_sets_occupancy_probability_le (I:=Fin k) uniformWeight uniformWeight_nonneg uniformWeight_sum
    (fun z : GridSlot bits × GridSlot bits => endpointLine z j) _ w _ (by positivity)
    hsmall (small_lines_mass j hη)
  apply le_trans (b:=productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
    ∃S : Finset (GridOutside bits j), S.card≤⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ ∧
      w≤(Finset.univ.filter (fun i => endpointLine (e i) j∈S)).card))
  · exact productProbability_mono uniformWeight_nonneg (fun e he =>
      ⟨particleHeavyLines e j η,particleHeavy_card e j hη,he⟩)
  · simpa only [Fintype.card_fin] using hb

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_EndpointGood
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
lemma Sparse.productProbability_or_le {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀u, 0≤p u) (E F : (I → Ω) → Prop) :
    productProbability p (fun x => E x ∨ F x) ≤ productProbability p E+productProbability p F := by
  unfold productProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hx := productWeight_nonneg hp x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf,hx]

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma vertexIsolated_of_not_incident (e : Fin k → GridSlot bits × GridSlot bits) (i : Fin k)
    (hi : i∉endpointVertexIncident H e) : vertexIsolated H e i := by
  have hh (a : Fin h) (t : Fin (b+1)) :
      independentPosition (H.position 0 a,H.position (Fin.last b) a) t=H.position t a :=
    independentPosition_of_path (fun t => H.position t a) (fun j i hi => H.changes_only_stage j a i hi) t
  have hn : ¬((∃j,i≠j ∧ shareVertex (e i) (e j)) ∨
      ∃a, shareVertex (e i) (H.position 0 a,H.position (Fin.last b) a)) := by
    simpa only [endpointVertexIncident,incidentSet,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  constructor
  · intro t a he
    exact hn (Or.inr ⟨a,t,he.trans (hh a t).symm⟩)
  · intro t a ha he
    exact hn (Or.inl ⟨a,ha.symm,t,he.symm⟩)

lemma endpointGood_cover (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) :
    k ≤ (endpointGoodSet H η e).card+(endpointVertexIncident H e).card+
      (∑j, (endpointHoleBad H η e j).card)+(∑j, (endpointParticleBad η e j).card) := by
  let G := endpointGoodSet H η e
  let V := endpointVertexIncident H e
  let S := Finset.univ.biUnion (endpointHoleBad H η e)
  let T := Finset.univ.biUnion (endpointParticleBad η e)
  have hc : (Finset.univ : Finset (Fin k))⊆((G∪V)∪S)∪T := by
    intro i _
    by_cases hv : i∈V
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
    by_cases hl : ∀j, endpointLight H η e (endpointPathLine e i j)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,hl⟩)))
    push Not at hl
    obtain ⟨j,hj⟩ := hl
    obtain hh | ht := endpoint_not_light H e j (endpointLine (e i) j) η hj
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩
  have h1 := Finset.card_le_card hc
  have h2 := Finset.card_union_le ((G∪V)∪S) T
  have h3 := Finset.card_union_le (G∪V) S
  have h4 := Finset.card_union_le G V
  have h5 := Finset.card_biUnion_le (s:=Finset.univ) (t:=endpointHoleBad H η e)
  have h6 := Finset.card_biUnion_le (s:=Finset.univ) (t:=endpointParticleBad η e)
  simp only [Finset.card_univ,Fintype.card_fin] at h1
  dsimp [G,V,S,T] at h1 h2 h3 h4
  omega

lemma few_good_implies_bad (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits)
    (wv wl : ℕ) (hb : 2*(wv-1+2*b*(wl-1))≤k)
    (hg : 2*(endpointGoodSet H η e).card<k) :
    wv≤(endpointVertexIncident H e).card ∨
      ∃j, wl≤(endpointHoleBad H η e j).card ∨ wl≤(endpointParticleBad η e j).card := by
  by_contra hn
  push Not at hn
  have hv : (endpointVertexIncident H e).card≤wv-1 := by omega
  have hh : (∑j, (endpointHoleBad H η e j).card)≤b*(wl-1) := by
    calc
      _ ≤ ∑j : Fin b, (wl-1) := Finset.sum_le_sum (fun j _ => by have := (hn.2 j).1; omega)
      _ = _ := by simp
  have ht : (∑j, (endpointParticleBad η e j).card)≤b*(wl-1) := by
    calc
      _ ≤ ∑j : Fin b, (wl-1) := Finset.sum_le_sum (fun j _ => by have := (hn.2 j).2; omega)
      _ = _ := by simp
  have hc := endpointGood_cover H η e
  have hm : 2*b*(wl-1)=b*(wl-1)+b*(wl-1) := by ring
  omega

lemma few_good_probability_bound {η : ℝ} (hη : 0<η) (wv wl : ℕ)
    (hb : 2*(wv-1+2*b*(wl-1))≤k)
    (hv : ((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits)≤1)
    (hh : 2*h/((gridSize bits:ℝ)*η)≤1) (hk : 2*k/((gridSize bits:ℝ)*η)≤1) :
    productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
      2*(endpointGoodSet H η e).card<k) ≤
      (2:ℝ)^k*(((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((wv+1)/2) +
      ∑j : Fin b, ((2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^wl +
        (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
          (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^wl) := by
  let V (e : Fin k → GridSlot bits × GridSlot bits) := wv≤(endpointVertexIncident H e).card
  let B (j : Fin b) (e : Fin k → GridSlot bits × GridSlot bits) :=
    wl≤(endpointHoleBad H η e j).card ∨ wl≤(endpointParticleBad η e j).card
  have h1 := productProbability_mono uniformWeight_nonneg (fun e he => few_good_implies_bad H η e wv wl hb he)
  have h2 := productProbability_or_le uniformWeight uniformWeight_nonneg V (fun e => ∃j, B j e)
  have h3 := productProbability_union_le uniformWeight_nonneg B
  have h4 : productProbability uniformWeight V≤
      (2:ℝ)^k*(((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((wv+1)/2) :=
    independent_trajectory_sharing (fun a => (H.position 0 a,H.position (Fin.last b) a)) wv hv
  have h5 : ∀j, productProbability uniformWeight (B j)≤
      (2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^wl +
        (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
          (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^wl := by
    intro j
    exact (productProbability_or_le uniformWeight uniformWeight_nonneg _ _).trans
      (add_le_add (holeHeavy_occupancy_bound H j hη hh wl) (particleHeavy_occupancy_bound j hη hk wl))
  exact h1.trans (h2.trans (add_le_add h4 (h3.trans (Finset.sum_le_sum (fun j _ => h5 j)))))

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
attribute [local instance] Classical.propDecidable
variable {P Ω : Type*} [Fintype P] [Fintype Ω]

lemma sum_square_le_uniform_split (f : P → Ω) (hi : Function.Injective f)
    (Q : Ω → ℝ) (E : Ω → Prop) (a C B : ℝ) (ha : 0<a)
    (hN : (Fintype.card Ω:ℝ)=a^2)
    (hc : ∀i, ¬E (f i) → |a*Q (f i)|≤C) (hb : ∀i, |a*Q (f i)|≤B) :
    ∑i, (Q (f i))^2 ≤ C^2+B^2*finiteProbability uniformWeight E := by
  have hcard : (Fintype.card Ω:ℝ)≠0 := by rw [hN]; positivity
  have hp : (Fintype.card Ω:ℝ)*finiteProbability uniformWeight E =
      ∑u : Ω, if E u then (1:ℝ) else 0 := by
    unfold finiteProbability uniformWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [← mul_assoc,mul_one_div_cancel hcard,one_mul]
  have hle : a^2*(∑i, (Q (f i))^2) ≤ ∑u : Ω, (C^2+if E u then B^2 else 0) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans
      (sum_injective_le f hi (fun u => C^2+if E u then B^2 else 0)
        (fun u => by split_ifs <;> positivity))
    by_cases hE : E (f i)
    · rw [ite_eq_left hE,← mul_pow]
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
      rw [sq_abs] at hs
      linarith [sq_nonneg C]
    · rw [ite_eq_right hE,add_zero,← mul_pow]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc i hE) 2
  have he : (∑u : Ω, (C^2+if E u then B^2 else 0)) =
      (Fintype.card Ω:ℝ)*(C^2+B^2*finiteProbability uniformWeight E) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_add,mul_left_comm _ (B^2),hp,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  rw [he,hN] at hle
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ha)).mp hle

end BinaryCoordinateSweeps.Sparse
namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

theorem centeredEndpointKernel_few_hs (hd : ∀j, bits j≤2*r) {η : ℝ}
    (hη : 0<η) (hη1 : η≤1/4) (hηb : 4*(b:ℝ)*Real.sqrt η≤1)
    (wv wl : ℕ) (ht : 2*(wv-1+2*b*(wl-1))≤k)
    (hv : ((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits)≤1)
    (hh : 2*h/((gridSize bits:ℝ)*η)≤1) (hk : 2*k/((gridSize bits:ℝ)*η)≤1) :
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) ≤
      ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*(4*b*Real.sqrt η)^((k+1)/2))^2 +
      ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*(((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((wv+1)/2) +
      ∑j : Fin b, ((2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^wl +
        (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
          (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^wl)) := by
  let f := placementEndpointArray (k:=k) H
  let E (e : Fin k → GridSlot bits × GridSlot bits) := 2*(endpointGoodSet H η e).card<k
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hN : (Fintype.card (Fin k → GridSlot bits × GridSlot bits):ℝ)=((gridSize bits:ℝ)^k)^2 := by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,card_gridSlot,Nat.cast_pow,Nat.cast_mul,mul_pow,pow_two]
  have he := sum_square_le_uniform_split f (placementEndpointArray_injective H)
    (centeredEndpointKernel H 0) E ((gridSize bits:ℝ)^k)
    ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*(4*b*Real.sqrt η)^((k+1)/2))
    ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b)) (pow_pos hs _) hN
    (fun xy hE => ?_) (fun xy => centeredEndpointKernel_amplitude H hd (le_refl 0)
      (linePerturbationRadius_pos r).le (by norm_num) xy.1 xy.2)
  · rw [← productProbability_uniform] at he
    have hp := few_good_probability_bound H hη wv wl ht hv hh hk
    have heq : (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
        (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) =
        ∑xy : Placement H k 0 × Placement H k (Fin.last b),
          (centeredEndpointKernel H 0 (f xy))^2 := by
      rw [Fintype.sum_prod_type]
      rfl
    rw [heq]
    exact he.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hp (sq_nonneg _)))
  · have hi : ∀i∈endpointGoodSet H η (f xy), vertexIsolated H (f xy) i := by
      intro i hi
      exact vertexIsolated_of_not_incident H (f xy) i (Finset.mem_filter.mp hi).2.1
    have hl := fun i (hi : i∈endpointGoodSet H η (f xy)) => (Finset.mem_filter.mp hi).2.2
    have hh := centeredEndpointKernel_good_bound H xy.1 xy.2 (endpointGoodSet H η (f xy)) hη.le hη1 hi hl
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_of_le_one (by positivity) hηb
    dsimp [E] at hE
    omega

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_FewSparse
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

section
open Sparse Young Irrep

theorem centeredEndpointHS_few_sparse {b r h k : ℕ} {bits : Fin b → ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ 16000) (hd : ∀j, r ≤ bits j ∧ bits j ≤ 2*r)
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits)) (hk : 1 ≤ k)
    (htail : ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ)) (hh : h ≤ 100000*k)
    (H : PathFamily bits h) :
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) ≤
      Real.exp (-(k:ℝ)*Real.log (gridSize bits)/1000000000000) := by
  let L := Real.log (gridSize bits)
  let η := Real.exp (-L/160000)
  have hs : (0:ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have hL0 : 0 ≤ L := (by positivity : (0:ℝ) ≤ 10^26).trans hL
  obtain ⟨hη1,hg⟩ := few_eta_good b hbB hL
  have hv := few_vertex_base b h k hs hbB hL htail
  have hx := few_line_base h h k hs hL htail (by omega)
  have hy := few_line_base k h k hs hL htail (by omega)
  have he (a : ℝ) (ha : 0 < a) : Real.exp (-L/a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL0) ha.le
  obtain ⟨ht,htv,htl⟩ := few_cutoff_bounds b k hb hbB
  have hbound := centeredEndpointKernel_few_hs H (fun j => (hd j).2)
    (Real.exp_pos (-L/160000)) hη1 (hg.trans (he _ (by norm_num)))
    (k/4+1) (k/(8*b)+1) ht (hv.trans (he _ (by norm_num)))
    (hx.trans (he _ (by norm_num))) (hy.trans (he _ (by norm_num)))
  apply hbound.trans
  apply few_hs_scalar b h k (k/4+1) (k/(8*b)+1)
    (fun j => (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊)
    hbB hk (by exact_mod_cast hh) hL htv htl (by positivity) hg (by positivity) hv
    (by positivity) hx (by positivity) hy (fun _ => by positivity)
  intro j
  convert adaptive_count_small (Fintype.card (GridOutside bits j)) k hs hL
    (outside_card_add_one_le bits j) (few_axis_eta_large hbB hd hL j) using 1
  push_cast
  rfl

end

lemma sparse_tail_le_quarter {s : ℝ} (hs : 0 < s) (hL : (10:ℝ)^26 ≤ Real.log s) :
    s^(1599/1600:ℝ) ≤ s/4 := by
  have hc : (4:ℝ) ≤ Real.exp (Real.log s/1600) :=
    (show (4:ℝ) ≤ Real.log s/1600+1 from by linarith).trans (Real.add_one_le_exp _)
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
  calc
    _ ≤ Real.exp ((1599/1600:ℝ)*Real.log s)*Real.exp (Real.log s/1600) := by
      rw [Real.rpow_def_of_pos hs]
      simpa only [mul_comm (Real.log s)] using mul_le_mul_of_nonneg_left hc
        (Real.exp_pos ((1599/1600:ℝ)*Real.log s)).le
    _ = s := by rw [←Real.exp_add,show (1599/1600:ℝ)*Real.log s+Real.log s/1600=Real.log s by ring,Real.exp_log hs]

lemma few_sparse_sign_geometry {b h k : ℕ} {bits : Fin b → ℕ}
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits))
    (htail : ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ))
    (j : Fin b) (hj : 2 ≤ bits j) :
    h+k+Fintype.card (GridOutside bits j) < gridSize bits := by
  have hs : (0:ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have hquarter := htail.trans (sparse_tail_le_quarter hs hL)
  have ha : 4 ≤ 2^bits j := (show 4=2^2 by norm_num) ▸ Nat.pow_le_pow_right (by omega : 1 ≤ 2) hj
  have ho : 4*Fintype.card (GridOutside bits j) ≤ gridSize bits := by
    have he := outside_card_mul_axis bits j
    nlinarith [Nat.mul_le_mul_left (Fintype.card (GridOutside bits j)) ha]
  have hoR : (4:ℝ)*Fintype.card (GridOutside bits j) ≤ gridSize bits := by exact_mod_cast ho
  have hl : ((h+k+Fintype.card (GridOutside bits j):ℕ):ℝ) < gridSize bits := by
    push_cast at hquarter ⊢
    linarith
  exact_mod_cast hl

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps

lemma sparseEndpointBound_eventually {b r h k : ℕ} {bits : Fin b → ℕ}
    (hb : 1 ≤ b) (hbB : b ≤ 16000) (hr : 2 ≤ r) (hd : ∀j, r ≤ bits j ∧ bits j ≤ 2*r)
    (hL : (10:ℝ)^26 ≤ Real.log (gridSize bits)) (hk : 1 ≤ k)
    (htail : ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ)) (hh : h ≤ 100000*k)
    (H : PathFamily bits h) : ∀ᶠ z in 𝓝 0, sparseEndpointBound H k z := by
  have hbound := centeredEndpointHS_few_sparse hb hbB hd hL hk htail hh H
  have hstrict : (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) <
        Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000) := by
    apply hbound.trans_lt (Real.exp_lt_exp.mpr ?_)
    have hkR : (0:ℝ) < k := by exact_mod_cast hk
    have hKL : 0 < (k:ℝ)*Real.log (gridSize bits) := mul_pos hkR (by linarith)
    linarith
  let j : Fin b := ⟨0,by omega⟩
  have hgeom := few_sparse_sign_geometry hL htail j (hr.trans (hd j).1)
  have hzero : signedCenteredHS H k 0=0 := signedCenteredHS_zero H k 0 (fun l hl x y =>
    signedPlacementEntry_zero_few H j (by omega) x y)
  have hsigned : signedCenteredHS H k 0 < Real.exp (-(k:ℝ)*Real.log (gridSize bits)/2000000000000) := by
    rw [hzero]
    exact Real.exp_pos _
  filter_upwards [(continuousAt_centeredEndpointHS H k).eventually_lt continuousAt_const hstrict,
    (continuousAt_signedCenteredHS H k).eventually_lt continuousAt_const hsigned] with z h1 h2
  exact ⟨h1.le,h2.le⟩

theorem sparse_finite_radius_oai (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℕ, 1 ≤ b → b ≤ 16000 →
      ∀bits : Fin b → ℕ, (∀j, r ≤ bits j ∧ bits j ≤ 2*r) →
      ∀h k : ℕ, h ≤ gridSize bits → k ≤ gridSize bits →
      (10:ℝ)^26 ≤ Real.log (gridSize bits) → 1 ≤ k →
      ((k+h:ℕ):ℝ) ≤ (gridSize bits:ℝ)^(1599/1600:ℝ) → h ≤ 100000*k →
      ∀H : PathFamily bits h, ∀z : ℝ, 0 ≤ z → z ≤ δ → sparseEndpointBound H k z := by
  have hev : ∀ᶠ z : ℝ in 𝓝 0,
      ∀b : Fin 16001, ∀ds : Fin b.val → Fin (2*r+1),
      ∀h : Fin (gridSize (fun j => (ds j).val)+1),
      ∀k : Fin (gridSize (fun j => (ds j).val)+1),
      ∀H : PathFamily (fun j => (ds j).val) h.val,
      (1 ≤ b.val ∧ (∀j, r ≤ (ds j).val) ∧
        (10:ℝ)^26 ≤ Real.log (gridSize (fun j => (ds j).val)) ∧ 1 ≤ k.val ∧
        ((k.val+h.val:ℕ):ℝ) ≤ (gridSize (fun j => (ds j).val):ℝ)^(1599/1600:ℝ) ∧
        h.val ≤ 100000*k.val) → sparseEndpointBound H k.val z := by
    apply eventually_all.mpr
    intro b
    apply eventually_all.mpr
    intro ds
    apply eventually_all.mpr
    intro h
    apply eventually_all.mpr
    intro k
    apply eventually_all.mpr
    intro H
    by_cases hc : 1 ≤ b.val ∧ (∀j, r ≤ (ds j).val) ∧
        (10:ℝ)^26 ≤ Real.log (gridSize (fun j => (ds j).val)) ∧ 1 ≤ k.val ∧
        ((k.val+h.val:ℕ):ℝ) ≤ (gridSize (fun j => (ds j).val):ℝ)^(1599/1600:ℝ) ∧
        h.val ≤ 100000*k.val
    · filter_upwards [sparseEndpointBound_eventually hc.1 (by omega) hr
        (fun j => ⟨hc.2.1 j,by have := (ds j).isLt; omega⟩)
        hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2 H] with z hz
      exact fun _ => hz
    · exact Eventually.of_forall (fun _ h => False.elim (hc h))
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ε/2,by linarith,?_⟩
  intro b hb hbB bits hd h k hh hk hL hk0 htail hholes H z hz hze
  have hdist : dist z 0 < ε := by rw [Real.dist_eq,sub_zero,abs_of_nonneg hz]; linarith
  exact he hdist ⟨b,by omega⟩ (fun j => ⟨bits j,(hd j).2.trans_lt (Nat.lt_succ_self _)⟩)
    ⟨h,by change h < gridSize bits+1; omega⟩ ⟨k,by change k < gridSize bits+1; omega⟩ H ⟨hb,fun j => (hd j).1,hL,hk0,htail,hholes⟩

end BinaryCoordinateSweeps

end

end OAI
end

theorem solution : type_of% @OAI.BinaryCoordinateSweeps.sparse_finite_radius_oai := @OAI.BinaryCoordinateSweeps.sparse_finite_radius_oai

-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.LocalRelation.sound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:18:49.192699+00:00
-- url     : https://prove2.me/submissions/b894aff0-0a84-462d-9ef3-3bb184990a32

import Mathlib
import Definitions.Def_OAIQ053K036

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Linearity
attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.QuadraticSystem.derivative_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLinearity

namespace MetricKMedian.PCP
open Finset

section Linearity
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H] [DecidableEq H]

private theorem sum_point_rejects (f : G → H) :
    (∑ x : G, correctionErrors f x (f x)) = linearityRejects f := by
  classical
  unfold linearityRejects
  rw [card_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  unfold correctionErrors
  rw [card_filter]
  apply sum_congr rfl
  intro y _
  simp only [derivative, ne_eq, sub_eq_iff_eq_add]

theorem corrected_close (f : G → H)
    (hsmall : 6 * linearityRejects f < Fintype.card G * Fintype.card G) :
    Fintype.card G * tableErrors f (corrected f) ≤ 2 * linearityRejects f := by
  classical
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have half (x : G) : 2 * correctionErrors f x (corrected f x) ≤ Fintype.card G := by
    have hb := correction_error_bound f x
    nlinarith
  have bad (x : G) (hx : f x ≠ corrected f x) :
      Fintype.card G ≤ 2 * correctionErrors f x (f x) := by
    have hc : ∀ y : G, (derivative f x y ≠ f x) ∨
        (derivative f x y ≠ corrected f x) ∨ False := by
      intro y
      by_contra h
      push Not at h
      exact hx (h.1.symm.trans h.2.1)
    have hh := card_le_of_three_cover _ _ _ hc
    simp only [filter_false, card_empty, add_zero] at hh
    change Fintype.card G ≤ correctionErrors f x (f x) +
      correctionErrors f x (corrected f x) at hh
    have hh' := half x
    omega
  let B := univ.filter (fun x => f x ≠ corrected f x)
  calc
    _ = ∑ _x ∈ B, Fintype.card G := by simp [tableErrors, B, mul_comm]
    _ ≤ ∑ x ∈ B, 2 * correctionErrors f x (f x) := by
      apply sum_le_sum
      intro x hx
      exact bad x (mem_filter.mp hx).2
    _ ≤ ∑ x : G, 2 * correctionErrors f x (f x) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; omega)
    _ = _ := by rw [← mul_sum, sum_point_rejects]

end Linearity
end MetricKMedian.PCP

end Inline_PCPLinearity

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.QuadraticSystem.derivative_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPFiniteTest

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Rates
variable {S T : Type} [Fintype S] [Fintype T]

theorem testRate_nonneg (p : S → Prop) : 0 ≤ testRate p := by
  classical
  exact expect_nonneg (by intro s _; split_ifs <;> norm_num)

theorem testRate_or_le (p q : S → Prop) :
    testRate (fun s => p s ∨ q s) ≤ testRate p + testRate q := by
  classical
  unfold testRate
  rw [← expect_add_distrib]
  apply expect_le_expect
  intro s _
  by_cases hp : p s <;> by_cases hq : q s <;> simp [hp, hq]

theorem testRate_union_bound {p q r : S → Prop} (h : ∀ s, p s → q s ∨ r s) :
    testRate p ≤ testRate q + testRate r :=
  (testRate_mono h).trans (testRate_or_le q r)

theorem testRate_eq_count (p : S → Prop) [DecidablePred p] :
    testRate p = ((univ.filter p).card : ℝ) / Fintype.card S := by
  classical
  rw [testRate, Fintype.expect_eq_sum_div_card]
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  congr 1
  apply sum_congr rfl
  intro s _
  split_ifs <;> rfl

theorem testRate_prod (p : S → T → Prop) :
    testRate (fun z : S × T => p z.1 z.2) = 𝔼 s, testRate (p s) := by
  classical
  unfold testRate
  rw [← univ_product_univ, expect_product]

theorem testRate_fst (p : S → Prop) [Nonempty T] :
    testRate (fun z : S × T => p z.1) = testRate p := by
  classical
  rw [testRate_prod (fun s (_ : T) => p s)]
  unfold testRate
  simp only [Fintype.expect_const]

theorem testRate_snd (p : T → Prop) [Nonempty S] :
    testRate (fun z : S × T => p z.2) = testRate p := by
  classical
  rw [testRate_prod (fun (_ : S) t => p t)]
  exact Fintype.expect_const _

theorem testRate_fibers_le (p : S → T → Prop) [Nonempty S] (c : ℝ)
    (h : ∀ s, testRate (p s) ≤ c) :
    testRate (fun z : S × T => p z.1 z.2) ≤ c := by
  rw [testRate_prod]
  exact expect_le univ_nonempty (fun s _ => h s)

end Rates

section LinearityRates
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H]
  [DecidableEq H]

theorem linearityRate_eq (f : G → H) :
    linearityRate f = (linearityRejects f : ℝ) / (Fintype.card G : ℝ)^2 := by
  classical
  rw [linearityRate, testRate_eq_count]
  simp only [linearityRejects, Fintype.card_prod, Nat.cast_mul, pow_two]

theorem linearityRate_small (f : G → H) (h : linearityRate f < 1/6) :
    6 * linearityRejects f < Fintype.card G * Fintype.card G := by
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [linearityRate_eq, div_lt_iff₀ (sq_pos_of_pos hn)] at h
  have hh : (6 : ℝ) * linearityRejects f < (Fintype.card G : ℝ) * Fintype.card G := by
    nlinarith
  exact_mod_cast hh

theorem corrective_query_error (f : G → H) (x : G) :
    testRate (fun y => derivative f x y ≠ corrected f x) ≤ 2 * linearityRate f := by
  classical
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [testRate_eq_count, linearityRate_eq]
  change (correctionErrors f x (corrected f x) : ℝ) / Fintype.card G ≤ _
  have hh : (Fintype.card G : ℝ) * correctionErrors f x (corrected f x) ≤
      2 * linearityRejects f := by exact_mod_cast correction_error_bound f x
  calc
    _ = ((Fintype.card G : ℝ) * _) / (Fintype.card G : ℝ)^2 := by
      field_simp
    _ ≤ (2 * linearityRejects f) / (Fintype.card G : ℝ)^2 :=
      div_le_div_of_nonneg_right hh (sq_nonneg _)
    _ = _ := by ring

theorem corrected_distance (f : G → H) (h : linearityRate f < 1/6) :
    testRate (fun x => f x ≠ corrected f x) ≤ 2 * linearityRate f := by
  classical
  have hn : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [testRate_eq_count, linearityRate_eq]
  change (tableErrors f (corrected f) : ℝ) / Fintype.card G ≤ _
  have hh : (Fintype.card G : ℝ) * tableErrors f (corrected f) ≤
      2 * linearityRejects f := by exact_mod_cast corrected_close f (linearityRate_small f h)
  calc
    _ = ((Fintype.card G : ℝ) * _) / (Fintype.card G : ℝ)^2 := by
      field_simp
    _ ≤ (2 * linearityRejects f) / (Fintype.card G : ℝ)^2 :=
      div_le_div_of_nonneg_right hh (sq_nonneg _)
    _ = _ := by ring

end LinearityRates
end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Hadamard
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_add _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_single _root_.OAI.MetricKMedian.PCP.QuadraticSystem.combination_zero _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination _root_.OAI.MetricKMedian.PCP.QuadraticSystem.equationDiscrepancy_single _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_left _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_right _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero _root_.OAI.MetricKMedian.PCP.Walsh.sign_one _root_.OAI.MetricKMedian.PCP.Walsh.sign_sq _root_.OAI.MetricKMedian.PCP.Walsh.sign_zero _root_.OAI.MetricKMedian.PCP.dot_liftQuery _root_.OAI.MetricKMedian.PCP.dot_single _root_.OAI.MetricKMedian.PCP.dot_smul _root_.OAI.MetricKMedian.PCP.dot_sum _root_.OAI.MetricKMedian.PCP.dot_unitForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPHadamard

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Bilinear
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

theorem bilinear_nonzero_rate (b : G →+ (H →+ Bit)) (x : G) (y : H)
    (h : b x y ≠ 0) :
    1/4 ≤ testRate (fun p : G × H => b p.1 p.2 ≠ 0) := by
  classical
  let gy : G →+ Bit :=
    { toFun := fun z => b z y
      map_zero' := by simp
      map_add' := by intros; simp }
  have hg : testRate (fun z => b z y ≠ 0) = 1/2 := linear_nonzero_rate gy x h
  rw [testRate_prod (fun z w => b z w ≠ 0)]
  have hh : (𝔼 z : G, if b z y ≠ 0 then (1/2 : ℝ) else 0) ≤
      𝔼 z : G, testRate (fun w => b z w ≠ 0) := by
    apply expect_le_expect
    intro z _
    by_cases hz : b z y ≠ 0
    · simp only [ite_eq_left hz]
      exact le_of_eq (linear_nonzero_rate (b z) y hz).symm
    · simp only [ite_eq_right hz]
      exact testRate_nonneg _
  have hi : (𝔼 z : G, if b z y ≠ 0 then (1/2 : ℝ) else 0) =
      (1/2) * testRate (fun z => b z y ≠ 0) := by
    unfold testRate
    rw [mul_expect]
    apply expect_congr rfl
    intro z _
    split_ifs <;> norm_num
  rw [hi, hg] at hh
  norm_num at hh ⊢
  exact hh
end Bilinear

section Vectors
variable {V W : Type} [Fintype V] [Fintype W]

theorem linear_representation (f : BitVector V →+ Bit) (x : BitVector V) :
    f x = dot (coordinates f) x := by
  classical
  have hdecomp := congrArg f (univ_sum_single x)
  rw [map_sum] at hdecomp
  rw [← hdecomp]
  unfold dot
  apply sum_congr rfl
  intro i _
  have hs : Pi.single i (x i) = x i • (Pi.single i (1 : Bit)) := by
    rw [← Pi.single_smul]
    simp
  rw [hs, ZMod.map_smul]
  simp only [smul_eq_mul, coordinates]
  ring

omit [Fintype V] [Fintype W] in
theorem multiplication_identifies_tensor (f : BitVector V →+ Bit)
    (g : BitVector W →+ Bit) (h : BitVector (V × W) →+ Bit)
    (hm : ∀ x y, h (tensor x y) = f x * g y) :
    coordinates h = tensor (coordinates f) (coordinates g) := by
  classical
  ext p
  obtain ⟨i,j⟩ := p
  unfold coordinates tensor
  convert hm (Pi.single i 1) (Pi.single j 1) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext ⟨u,v⟩
  by_cases hi : i = u <;> by_cases hj : j = v <;>
    simp [tensor, hi, hj]

end Vectors
end MetricKMedian.PCP

end Inline_PCPHadamard

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Quadratic
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQuadratic

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Quadratic
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

theorem equation_transfer (h : BitVector (V × V) → Bit) :
    testRate (fun t => corrected h (Q.combination t) ≠ dot Q.rhs t) ≤
      Q.equationRate h + 2 * linearityRate h := by
  classical
  let P := fun p : BitVector E × BitVector (V × V) =>
    corrected h (Q.combination p.1) ≠ dot Q.rhs p.1
  let A := fun p : BitVector E × BitVector (V × V) =>
    derivative h (Q.combination p.1) p.2 ≠ dot Q.rhs p.1
  let B := fun p : BitVector E × BitVector (V × V) =>
    derivative h (Q.combination p.1) p.2 ≠ corrected h (Q.combination p.1)
  have hcover : ∀ p, P p → A p ∨ B p := by
    intro p hp
    by_contra hh
    simp only [A, B, not_or, not_not] at hh
    exact hp (hh.2.symm.trans hh.1)
  have hB : testRate B ≤ 2 * linearityRate h :=
    testRate_fibers_le (S := BitVector E) (T := BitVector (V × V))
      (fun t u => derivative h (Q.combination t) u ≠ corrected h (Q.combination t))
      (2 * linearityRate h) (fun t => corrective_query_error h (Q.combination t))
  have hh := testRate_union_bound hcover
  change testRate (fun p : BitVector E × BitVector (V × V) =>
    corrected h (Q.combination p.1) ≠ dot Q.rhs p.1) ≤ _ at hh
  rw [testRate_fst (fun t => corrected h (Q.combination t) ≠ dot Q.rhs t)] at hh
  have hA : testRate A = Q.equationRate h := rfl
  rw [hA] at hh
  linarith

omit [DecidableEq V] in
theorem equation_exact (h : BitVector (V × V) →+ Bit)
    (hr : testRate (fun t => h (Q.combination t) ≠ dot Q.rhs t) < 1/2) :
    ∀ e, h (Q.form e) = Q.rhs e := by
  classical
  intro e
  by_contra he
  have hn : Q.equationDiscrepancy h (Pi.single e 1) ≠ 0 := by
    simpa only [equationDiscrepancy_single, sub_ne_zero] using he
  have hb := linear_nonzero_rate (Q.equationDiscrepancy h) (Pi.single e 1) hn
  have heq : testRate (fun t => Q.equationDiscrepancy h t ≠ 0) =
      testRate (fun t => h (Q.combination t) ≠ dot Q.rhs t) := by
    apply testRate_congr
    intro t
    exact sub_ne_zero
  rw [heq] at hb
  linarith
end QuadraticSystem

theorem multiplication_transfer (f : BitVector V → Bit) (h : BitVector (V × V) → Bit)
    (hf : linearityRate f < 1/6) :
    testRate (fun p : BitVector V × BitVector V =>
      corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2)) ≤
      multiplicationRate f h + 4 * linearityRate f + 2 * linearityRate h := by
  classical
  let P := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    corrected f p.1.1 * corrected f p.1.2 ≠ corrected h (tensor p.1.1 p.1.2)
  let A := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.1 * f p.1.2 ≠ derivative h (tensor p.1.1 p.1.2) p.2
  let B := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.1 ≠ corrected f p.1.1
  let C := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    f p.1.2 ≠ corrected f p.1.2
  let D := fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
    derivative h (tensor p.1.1 p.1.2) p.2 ≠ corrected h (tensor p.1.1 p.1.2)
  have hcover : ∀ p, P p → A p ∨ (B p ∨ (C p ∨ D p)) := by
    intro p hp
    by_contra hh
    simp only [A, B, C, D, not_or, not_not] at hh
    apply hp
    rw [← hh.2.1, ← hh.2.2.1]
    exact hh.1.trans hh.2.2.2
  have hB : testRate B ≤ 2 * linearityRate f := by
    change testRate (fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
      f p.1.1 ≠ corrected f p.1.1) ≤ _
    rw [testRate_fst (fun q : BitVector V × BitVector V =>
      f q.1 ≠ corrected f q.1), testRate_fst (fun x : BitVector V => f x ≠ corrected f x)]
    exact corrected_distance f hf
  have hC : testRate C ≤ 2 * linearityRate f := by
    change testRate (fun p : (BitVector V × BitVector V) × BitVector (V × V) =>
      f p.1.2 ≠ corrected f p.1.2) ≤ _
    rw [testRate_fst (fun q : BitVector V × BitVector V =>
      f q.2 ≠ corrected f q.2), testRate_snd (fun x : BitVector V => f x ≠ corrected f x)]
    exact corrected_distance f hf
  have hD : testRate D ≤ 2 * linearityRate h :=
    testRate_fibers_le (S := BitVector V × BitVector V) (T := BitVector (V × V))
      (fun p u => derivative h (tensor p.1 p.2) u ≠ corrected h (tensor p.1 p.2))
      (2 * linearityRate h) (fun p => corrective_query_error h (tensor p.1 p.2))
  have hp := testRate_union_bound hcover
  have hc := testRate_or_le C D
  have hb := testRate_or_le B (fun p => C p ∨ D p)
  change testRate P ≤ testRate A + testRate (fun p => B p ∨ C p ∨ D p) at hp
  have hP : testRate P = testRate (fun p : BitVector V × BitVector V =>
      corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2)) :=
    testRate_fst (T := BitVector (V × V))
      (fun p : BitVector V × BitVector V =>
        corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2))
  rw [hP] at hp
  have hA : testRate A = multiplicationRate f h := rfl
  rw [hA] at hp
  linarith only [hp, hb, hc, hB, hC, hD]

end Quadratic
end MetricKMedian.PCP

end Inline_PCPQuadratic

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_QuadraticEncoding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.QuadraticSystem.dot_combination _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero _root_.OAI.MetricKMedian.PCP.Walsh.sign_one _root_.OAI.MetricKMedian.PCP.Walsh.sign_sq _root_.OAI.MetricKMedian.PCP.Walsh.sign_zero _root_.OAI.MetricKMedian.PCP.dot_liftQuery _root_.OAI.MetricKMedian.PCP.dot_single
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQuadraticEncoding

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Algebra
variable {I T : Type} [Fintype I] [Fintype T]

theorem bit_mul_self (b : Bit) : b*b = b := by
  rcases bit_cases b with rfl | rfl <;> simp

@[simp] theorem quadratic_diagonal [DecidableEq I] (a : BitVector I) (i : I) :
    dot (tensor a a) (unitForm i i) = a i := by
  simp [tensor, bit_mul_self]
end Algebra

namespace RelationEncoding
variable {I A : Type} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

theorem satisfies_iff (label : A → BitVector I) (z : BitVector (Variable I A)) :
    (system label).Satisfies z ↔
      (∑ a : A, z (.inr a)) = 1 ∧
      (∀ a b : A, a ≠ b → z (.inr a) * z (.inr b) = 0) ∧
      (∀ i : I, z (.inl i) + ∑ a : A, label a i * z (.inr a) = 0) := by
  constructor
  · intro hz
    refine ⟨?_, ?_, ?_⟩
    · simpa [system, tensor, bit_mul_self] using hz (.inl ())
    · intro a b hab
      simpa [system, hab, tensor] using hz (.inr (.inl (a,b)))
    · intro i
      simpa [system, tensor, bit_mul_self] using hz (.inr (.inr i))
  · rintro ⟨hs,hp,hi⟩ q
    rcases q with u | ab | i
    · simpa [system, tensor, bit_mul_self] using hs
    · obtain ⟨a,b⟩ := ab
      by_cases hab : a = b
      · simp [system, hab]
      · simpa [system, hab, tensor] using hp a b hab
    · simpa [system, tensor, bit_mul_self] using hi i

theorem sound (label : A → BitVector I) (z : BitVector (Variable I A))
    (hz : (system label).Satisfies z) : ∃ a, ∀ i, z (.inl i) = label a i := by
  obtain ⟨hs,hp,hi⟩ := (satisfies_iff label z).mp hz
  have hex : ∃ a, z (.inr a) = 1 := by
    by_contra! ha
    have hzero : ∀ a, z (.inr a) = 0 := fun a => (bit_cases _).resolve_right (ha a)
    simp only [hzero, sum_const_zero] at hs
    exact zero_ne_one hs
  obtain ⟨a,ha⟩ := hex
  have hsel : ∀ b, z (.inr b) = if b = a then 1 else 0 := by
    intro b
    by_cases hb : b = a
    · simp [hb, ha]
    · have he := hp a b (Ne.symm hb)
      rw [ha, one_mul] at he
      simpa only [ite_eq_right hb] using he
  refine ⟨a,?_⟩
  intro i
  have he := hi i
  simp only [hsel, mul_ite, mul_one, mul_zero] at he
  simp only [sum_ite_eq', mem_univ, ite_true] at he
  calc
    z (.inl i) = (z (.inl i) + label a i) + label a i := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = label a i := by rw [he, zero_add]

end RelationEncoding
end MetricKMedian.PCP

end Inline_PCPQuadraticEncoding

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Boundary
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.QuadraticSystem.derivative_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBoundary

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Distances
variable {S H : Type} [Fintype S]

theorem table_distance_triangle (f g h : S → H) :
    testRate (fun x => f x ≠ h x) ≤
      testRate (fun x => f x ≠ g x) + testRate (fun x => g x ≠ h x) := by
  apply testRate_union_bound
  intro x hx
  by_contra hh
  push Not at hh
  exact hx (hh.1.trans hh.2)

theorem table_distance_symm (f g : S → H) :
    testRate (fun x => f x ≠ g x) = testRate (fun x => g x ≠ f x) :=
  testRate_congr (fun _ => ne_comm)
end Distances

section Derivative
variable {G H : Type} [AddCommGroup G] [Fintype G] [AddCommGroup H]

theorem derivative_distance (f : G → H) (g : G →+ H) (x : G) :
    testRate (fun y => derivative f x y ≠ g x) ≤
      2 * testRate (fun y => f y ≠ g y) := by
  have hh : testRate (fun y => derivative f x y ≠ g x) ≤
      testRate (fun y => f (x+y) ≠ g (x+y)) +
      testRate (fun y => f y ≠ g y) := by
    apply testRate_union_bound
    intro y hy
    by_contra hh
    push Not at hh
    apply hy
    simp [derivative, hh.1, hh.2]
  have he := testRate_equiv (Equiv.addLeft x) (fun y => f y ≠ g y)
  change testRate (fun y => f (x+y) ≠ g (x+y)) = _ at he
  rw [he] at hh
  linarith only [hh]
end Derivative

section Code
variable {I : Type} [Fintype I] [DecidableEq I]

theorem hadamard_distance (a b : BitVector I) (hab : a ≠ b) :
    testRate (fun x => dot a x ≠ dot b x) = 1/2 := by
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
    by_contra! h
    exact hab (funext h)
  let g : BitVector I →+ Bit := dotHom a - dotHom b
  have hg : g (Pi.single i 1) ≠ 0 := by
    change dot a (Pi.single i 1) - dot b (Pi.single i 1) ≠ 0
    simpa only [dot_single, sub_ne_zero] using hi
  have hh := linear_nonzero_rate g (Pi.single i 1) hg
  have he : testRate (fun x => g x ≠ 0) = testRate (fun x => dot a x ≠ dot b x) := by
    apply testRate_congr
    intro x
    exact sub_ne_zero
  rwa [he] at hh

theorem nearestLabel_min (f : BitVector I → Bit) (a : BitVector I) :
    testRate (fun x => f x ≠ dot (nearestLabel f) x) ≤
      testRate (fun x => f x ≠ dot a x) := (Classical.choose_spec (exists_nearest f)) a

theorem nearestLabel_robust (f : BitVector I → Bit) (a : BitVector I)
    (ha : a ≠ nearestLabel f) :
    1/4 ≤ testRate (fun x => f x ≠ dot a x) := by
  have hdist := hadamard_distance a (nearestLabel f) ha
  have htri := table_distance_triangle (dot a) f (dot (nearestLabel f))
  rw [table_distance_symm (dot a) f, hdist] at htri
  have hmin := nearestLabel_min f a
  linarith only [htri, hmin]
end Code

section Boundary
variable {I V : Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem boundary_transfer (embed : I → V) (f : BitVector V → Bit)
    (u : BitVector I → Bit) (a : BitVector V) :
    testRate (fun x => u x ≠ dot (a ∘ embed) x) ≤
      boundaryRate embed f u + 2 * testRate (fun y => f y ≠ dot a y) := by
  let P := fun p : BitVector I × BitVector V => u p.1 ≠ dot (a ∘ embed) p.1
  let A := fun p : BitVector I × BitVector V =>
    derivative f (liftQuery embed p.1) p.2 ≠ u p.1
  let B := fun p : BitVector I × BitVector V =>
    derivative f (liftQuery embed p.1) p.2 ≠ dot a (liftQuery embed p.1)
  have hcover : ∀ p, P p → A p ∨ B p := by
    intro p hp
    by_contra hh
    simp only [A, B, not_or, not_not, dot_liftQuery] at hh
    exact hp (hh.1.symm.trans hh.2)
  have hb : testRate B ≤ 2 * testRate (fun y => f y ≠ dot a y) :=
    testRate_fibers_le (S := BitVector I) (T := BitVector V)
      (fun x y => derivative f (liftQuery embed x) y ≠ dot a (liftQuery embed x))
      (2 * testRate (fun y => f y ≠ dot a y))
      (fun x => derivative_distance f (dotHom a) (liftQuery embed x))
  have hp := testRate_union_bound hcover
  have hP : testRate P = testRate (fun x => u x ≠ dot (a ∘ embed) x) :=
    testRate_fst (T := BitVector V) (fun x => u x ≠ dot (a ∘ embed) x)
  rw [hP] at hp
  change testRate (fun x => u x ≠ dot (a ∘ embed) x) ≤
    boundaryRate embed f u + testRate B at hp
  linarith only [hp, hb]
end Boundary
end MetricKMedian.PCP

end Inline_PCPBoundary

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Tester
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPTester

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem multiplication_exact (f : BitVector V →+ Bit) (h : BitVector (V × V) →+ Bit)
    (hr : testRate (fun p : BitVector V × BitVector V =>
      f p.1 * f p.2 ≠ h (tensor p.1 p.2)) < 1/4) :
    ∀ x y, h (tensor x y) = f x * f y := by
  intro x y
  by_contra hm
  have hn : multiplicationDiscrepancy f f h x y ≠ 0 := sub_ne_zero.mpr hm
  have hb := bilinear_nonzero_rate (multiplicationDiscrepancy f f h) x y hn
  have he : testRate (fun p : BitVector V × BitVector V =>
      multiplicationDiscrepancy f f h p.1 p.2 ≠ 0) =
      testRate (fun p : BitVector V × BitVector V =>
      f p.1 * f p.2 ≠ h (tensor p.1 p.2)) := by
    apply testRate_congr
    intro p
    change (h (tensor p.1 p.2) - f p.1 * f p.2 ≠ 0) ↔ _
    exact sub_ne_zero.trans ne_comm
  rw [he] at hb
  linarith

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

theorem decode (f : BitVector V → Bit) (h : BitVector (V × V) → Bit)
    (hr : Q.rejectionWeight f h < 1/16) :
    ∃ a : BitVector V, Q.Satisfies a ∧
      testRate (fun x => f x ≠ dot a x) ≤ 2 * linearityRate f := by
  have hn₁ : 0 ≤ linearityRate f := testRate_nonneg _
  have hn₂ : 0 ≤ linearityRate h := testRate_nonneg _
  have hn₃ : 0 ≤ multiplicationRate f h := testRate_nonneg _
  have hn₄ : 0 ≤ Q.equationRate h := testRate_nonneg _
  have hsum : linearityRate f + linearityRate h + multiplicationRate f h +
      Q.equationRate h < 1/16 := hr
  have hf : linearityRate f < 1/6 := by linarith only [hsum, hn₂, hn₃, hn₄]
  have hh : linearityRate h < 1/6 := by linarith only [hsum, hn₁, hn₃, hn₄]
  let F := correctedHom f (linearityRate_small f hf)
  let H := correctedHom h (linearityRate_small h hh)
  have hmul : ∀ x y, H (tensor x y) = F x * F y := by
    apply multiplication_exact F H
    have hb := multiplication_transfer f h hf
    change testRate (fun p : BitVector V × BitVector V =>
      corrected f p.1 * corrected f p.2 ≠ corrected h (tensor p.1 p.2)) < 1/4
    linarith only [hb, hsum, hn₁, hn₂, hn₃, hn₄]
  have heq : ∀ e, H (Q.form e) = Q.rhs e := by
    apply Q.equation_exact H
    have hb := Q.equation_transfer h
    change testRate (fun t => corrected h (Q.combination t) ≠ dot Q.rhs t) < 1/2
    linarith only [hb, hsum, hn₁, hn₂, hn₃, hn₄]
  have hcoords := multiplication_identifies_tensor F F H hmul
  refine ⟨coordinates F, ?_, ?_⟩
  · intro e
    rw [← hcoords, ← linear_representation]
    exact heq e
  · have hd := corrected_distance f hf
    have he : (fun x => dot (coordinates F) x) = corrected f := by
      funext x
      exact (linear_representation F x).symm
    simpa only [he] using hd

end QuadraticSystem
end MetricKMedian.PCP

end Inline_PCPTester

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_LocalReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPLocalReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]

variable (R : Relation K) [DecidablePred (· ∈ R)]

theorem decode (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit)
    (hr : rejectionWeight R f h u v < 1/16) :
    (nearestLabel u, nearestLabel v) ∈ R := by
  have n₁ : 0 ≤ linearityRate f := testRate_nonneg _
  have n₂ : 0 ≤ linearityRate h := testRate_nonneg _
  have n₃ : 0 ≤ multiplicationRate f h := testRate_nonneg _
  have n₄ : 0 ≤ (quadratic R).equationRate h := testRate_nonneg _
  have nL : 0 ≤ boundaryRate (leftEmbed R) f u := testRate_nonneg _
  have nR : 0 ≤ boundaryRate (rightEmbed R) f v := testRate_nonneg _
  have hsum : linearityRate f + linearityRate h + multiplicationRate f h +
      (quadratic R).equationRate h + boundaryRate (leftEmbed R) f u +
      boundaryRate (rightEmbed R) f v < 1/16 := hr
  have hquad : (quadratic R).rejectionWeight f h < 1/16 := by
    change linearityRate f + linearityRate h + multiplicationRate f h +
      (quadratic R).equationRate h < 1/16
    linarith only [hsum, nL, nR]
  obtain ⟨a,ha,hd⟩ := (quadratic R).decode f h hquad
  obtain ⟨p,hp⟩ := RelationEncoding.sound (label R) a ha
  have hleft : a ∘ leftEmbed R = p.val.1 := funext (fun i => hp (.inl i))
  have hright : a ∘ rightEmbed R = p.val.2 := funext (fun i => hp (.inr i))
  have hL : p.val.1 = nearestLabel u := by
    by_contra hL
    have hy := nearestLabel_robust u p.val.1 hL
    have hx := boundary_transfer (leftEmbed R) f u a
    rw [hleft] at hx
    linarith only [hy, hx, hd, hsum, n₁, n₂, n₃, n₄, nL, nR]
  have hR : p.val.2 = nearestLabel v := by
    by_contra hR
    have hy := nearestLabel_robust v p.val.2 hR
    have hx := boundary_transfer (rightEmbed R) f v a
    rw [hright] at hx
    linarith only [hy, hx, hd, hsum, n₁, n₂, n₃, n₄, nL, nR]
  have hpR : (p.val.1, p.val.2) ∈ R := p.property
  simpa only [hL, hR] using hpR

theorem sound_s53_oai (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit)
    (hR : (nearestLabel u, nearestLabel v) ∉ R) :
    1/16 ≤ rejectionWeight R f h u v := by
  by_contra hr
  exact hR (decode R f h u v (lt_of_not_ge hr))

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.LocalRelation.sound_s53_oai := @OAI.MetricKMedian.PCP.LocalRelation.sound_s53_oai

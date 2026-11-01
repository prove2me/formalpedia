-- Prove2me | solution 1 for OAI.MetricKMedian.PCP.AlphabetReduction.padded_complete_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:15:46.570435+00:00
-- url     : https://prove2.me/submissions/eccb50c3-ff6f-48a7-ae02-7482f819ea19

import Mathlib
import Definitions.Def_OAIQ053K036

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_FiniteTest
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
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

theorem testRate_false : testRate (fun _ : S => False) = 0 := by
  classical
  simp [testRate]

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

end Rates

end MetricKMedian.PCP

end Inline_PCPFiniteTest

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Hadamard
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPHadamard

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section Vectors
variable {V W : Type} [Fintype V] [Fintype W]

theorem dot_tensor (a x : BitVector V) (b y : BitVector W) :
    dot (tensor a b) (tensor x y) = dot a x * dot b y := by
  simp only [dot, tensor, Fintype.sum_prod_type, sum_mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

end Vectors
end MetricKMedian.PCP

end Inline_PCPHadamard

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

theorem complete (label : A → BitVector I) (a : A) :
    (system label).Satisfies (witness label a) := by
  rw [satisfies_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro b c hbc
    by_cases hb : b = a <;> by_cases hc : c = a <;>
      simp [hb, hc] at hbc ⊢
  · intro i
    simp [mul_ite, CharTwo.add_self_eq_zero]

end RelationEncoding
end MetricKMedian.PCP

end Inline_PCPQuadraticEncoding

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Tester
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_left _root_.OAI.MetricKMedian.PCP.RelationEncoding.witness_right _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero _root_.OAI.MetricKMedian.PCP.Walsh.sign_one _root_.OAI.MetricKMedian.PCP.Walsh.sign_sq _root_.OAI.MetricKMedian.PCP.Walsh.sign_zero _root_.OAI.MetricKMedian.PCP.dot_liftQuery _root_.OAI.MetricKMedian.PCP.dot_single _root_.OAI.MetricKMedian.PCP.dot_smul _root_.OAI.MetricKMedian.PCP.dot_sum _root_.OAI.MetricKMedian.PCP.dot_unitForm _root_.OAI.MetricKMedian.PCP.quadratic_diagonal
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

namespace QuadraticSystem
variable (Q : QuadraticSystem V E)

theorem complete (a : BitVector V) (ha : Q.Satisfies a) :
    Q.rejectionWeight (dot a) (dot (tensor a a)) = 0 := by
  have hf : linearityRate (dot a) = 0 := by
    convert testRate_false (S := BitVector V × BitVector V) using 1
    all_goals try with_reducible_and_instances rfl
    apply testRate_congr
    intro p
    simp [dot_add_right]
  have hh : linearityRate (dot (tensor a a)) = 0 := by
    convert testRate_false (S := BitVector (V × V) × BitVector (V × V)) using 1
    all_goals try with_reducible_and_instances rfl
    apply testRate_congr
    intro p
    simp [dot_add_right]
  have hm : multiplicationRate (dot a) (dot (tensor a a)) = 0 := by
    convert testRate_false (S := (BitVector V × BitVector V) × BitVector (V × V)) using 1
    all_goals try with_reducible_and_instances rfl
    apply testRate_congr
    intro p
    simp [derivative, dot_add_right, dot_tensor]
  have he : Q.equationRate (dot (tensor a a)) = 0 := by
    convert testRate_false (S := BitVector E × BitVector (V × V)) using 1
    all_goals try with_reducible_and_instances rfl
    apply testRate_congr
    intro p
    have heach : dot (tensor a a) (Q.combination p.1) = dot Q.rhs p.1 := by
      rw [Q.dot_combination]
      change (∑ e, p.1 e * dot (tensor a a) (Q.form e)) = ∑ e, Q.rhs e * p.1 e
      apply sum_congr rfl
      intro e _
      rw [ha e, mul_comm]
    simp [derivative, dot_add_right, heach]
  simp only [rejectionWeight, hf, hh, hm, he, add_zero]
end QuadraticSystem
end MetricKMedian.PCP

end Inline_PCPTester

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_LocalReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleNonempty _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero _root_.OAI.MetricKMedian.PCP.Walsh.sign_one _root_.OAI.MetricKMedian.PCP.Walsh.sign_sq _root_.OAI.MetricKMedian.PCP.Walsh.sign_zero
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

theorem complete (p : Allowed R) :
    ∃ f h, rejectionWeight R f h (dot p.val.1) (dot p.val.2) = 0 := by
  let a := RelationEncoding.witness (label R) p
  let f := dot a
  let h := dot (tensor a a)
  have ha : (quadratic R).Satisfies a := RelationEncoding.complete (label R) p
  have hq := (quadratic R).complete a ha
  have hleft : a ∘ leftEmbed R = p.val.1 := rfl
  have hright : a ∘ rightEmbed R = p.val.2 := rfl
  have hl : boundaryRate (leftEmbed R) f (dot p.val.1) = 0 := by
    unfold boundaryRate
    convert testRate_false (S := BitVector K × BitVector (Vars R)) using 1
    all_goals try with_reducible_and_instances rfl
    apply testRate_congr
    intro q
    simp [f, derivative, dot_add_right, dot_liftQuery, hleft]
  have hr : boundaryRate (rightEmbed R) f (dot p.val.2) = 0 := by
    unfold boundaryRate
    convert testRate_false (S := BitVector K × BitVector (Vars R)) using 1
    all_goals try with_reducible_and_instances rfl
    apply testRate_congr
    intro q
    simp [f, derivative, dot_add_right, dot_liftQuery, hright]
  refine ⟨f,h,?_⟩
  change (quadratic R).rejectionWeight (dot a) (dot (tensor a a)) + _ + _ = 0
  rw [hq, hl, hr]
  norm_num
end LocalRelation
end MetricKMedian.PCP

end Inline_PCPLocalReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_Queries
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.AlphabetReduction.restriction _root_.OAI.MetricKMedian.PCP.FourQuery.map_rejects _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero _root_.OAI.MetricKMedian.PCP.Walsh.sign_one _root_.OAI.MetricKMedian.PCP.Walsh.sign_sq _root_.OAI.MetricKMedian.PCP.Walsh.sign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPQueries

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

theorem testRate_pi_eval {I : Type} [Fintype I] [DecidableEq I]
    (S : I → Type) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (i : I) (p : S i → Prop) :
    testRate (fun s : (i : I) → S i => p (s i)) = testRate p := by
  classical
  calc
    _ = testRate (fun s : S i × ((j : {j // j ≠ i}) → S j.val) => p s.1) :=
      testRate_equiv (Equiv.piSplitAt i S) (fun s => p s.1)
    _ = _ := testRate_fst p

namespace LocalRelation
variable {K : Type} [Fintype K] [DecidableEq K]
variable (R : Relation K) [DecidablePred (· ∈ R)]

theorem packed_rate (f : BitVector (Vars R) → Bit)
    (h : BitVector (Vars R × Vars R) → Bit) (u v : BitVector K → Bit) :
    testRate (fun s => (packed R s).Rejects (assignment R f h u v)) =
      rejectionWeight R f h u v / 6 := by
  classical
  change testRate (fun s : Fin 6 × Pad R =>
    (query R s.1 (s.2 s.1)).Rejects (assignment R f h u v)) = _
  rw [testRate_prod (S := Fin 6) (T := Pad R)
    (fun (i : Fin 6) (s : Pad R) => (query R i (s i)).Rejects (assignment R f h u v))]
  have hm (i : Fin 6) :
      testRate (fun s : Pad R => (query R i (s i)).Rejects (assignment R f h u v)) =
      testRate (fun s : Sample R i => (query R i s).Rejects (assignment R f h u v)) :=
    testRate_pi_eval (Sample R) i
      (fun s : Sample R i => (query R i s).Rejects (assignment R f h u v))
  change (𝔼 i, testRate (fun s : Pad R =>
    (query R i (s i)).Rejects (assignment R f h u v))) = _
  simp_rw [hm]
  rw [Fintype.expect_eq_sum_div_card]
  norm_num only [Fintype.card_fin, Fin.sum_univ_succ, Fin.reduceSucc,
    Finset.sum_empty, add_zero]
  congr 1
  simp only [query, FourQuery.Rejects, firstPos, secondPos, leftPos, rightPos,
    rejectionWeight, QuadraticSystem.rejectionWeight,
    linearityRate, multiplicationRate, QuadraticSystem.equationRate,
    boundaryRate, derivative, add_assoc]
  simp only [Function.comp_def]
  simp only [assignment, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
  simp only [Bool.not_eq_true]
  simp
  apply congrArg₂ (fun x y : ℝ => x + y)
  · apply testRate_congr
    intro s
    exact decide_eq_false_iff_not
  · apply congrArg₂ (fun x y : ℝ => x + y)
    · apply testRate_congr
      intro s
      exact decide_eq_false_iff_not
    · apply congrArg₂ (fun x y : ℝ => x + y)
      · apply testRate_congr
        intro s
        exact decide_eq_false_iff_not
      · apply congrArg₂ (fun x y : ℝ => x + y)
        · apply testRate_congr
          intro s
          exact decide_eq_false_iff_not
        · rfl

end LocalRelation
end MetricKMedian.PCP

end Inline_PCPQueries

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_AlphabetReduction
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited _root_.OAI.MetricKMedian.PCP.Compiler.adviceFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype _root_.OAI.MetricKMedian.PCP.Tableau.queryNonempty
attribute [-simp] _root_.OAI.MetricKMedian.PCP.BinaryCSP.mapLabels_allowed _root_.OAI.MetricKMedian.PCP.CloudCopies.equality_step _root_.OAI.MetricKMedian.PCP.IncidenceReduction.allowed_iff _root_.OAI.MetricKMedian.PCP.Walsh.cayley_step _root_.OAI.MetricKMedian.PCP.Walsh.character_sq _root_.OAI.MetricKMedian.PCP.Walsh.character_zero _root_.OAI.MetricKMedian.PCP.Walsh.coefficient_zero _root_.OAI.MetricKMedian.PCP.Walsh.sign_one _root_.OAI.MetricKMedian.PCP.Walsh.sign_sq _root_.OAI.MetricKMedian.PCP.Walsh.sign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPAlphabetReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]

theorem testRate_eq_zero_iff {S : Type} [Fintype S] (p : S → Prop) :
    testRate p = 0 ↔ ∀ s, ¬ p s := by
  classical
  unfold testRate
  rw [Finset.expect_eq_zero_iff_of_nonneg (by intro s _; split_ifs <;> norm_num)]
  simp

namespace AlphabetReduction
variable (K)

variable {K}
variable (C : BinaryCSP V E (BitVector K))

omit [Fintype V] [Fintype E] in
theorem edge_rate (a : Position C → Bit) (e : E) :
    testRate (fun s : EdgeSample K => ((reduced C).query (e,s)).Rejects a) =
      LocalRelation.rejectionWeight (relation C e) (firstTable C a e) (secondTable C a e)
        (vertexTable C a (C.left e)) (vertexTable C a (C.right e)) / 6 := by
  classical
  let R := relation C e
  let p := fun (i : Fin 6) (s : LocalRelation.Sample R i) =>
    (LocalRelation.query R i s).Rejects (a ∘ localMap C e)
  have hm (i : Fin 6) :
      testRate (fun s : UniversalPad K => p i (s (C.allowed e) i)) =
      testRate (fun s : LocalRelation.Pad R => p i (s i)) :=
    testRate_pi_eval (fun R : Relations K => LocalRelation.Pad (R : LocalRelation.Relation K))
      (C.allowed e) (fun s : LocalRelation.Pad R => p i (s i))
  change testRate (fun s : Fin 6 × UniversalPad K => p s.1 (s.2 (C.allowed e) s.1)) = _
  rw [testRate_prod (S := Fin 6) (T := UniversalPad K)
    (fun (i : Fin 6) (s : UniversalPad K) => p i (s (C.allowed e) i))]
  simp_rw [hm]
  rw [← testRate_prod (S := Fin 6) (T := LocalRelation.Pad R)
    (fun (i : Fin 6) (s : LocalRelation.Pad R) => p i (s i))]
  change testRate (fun s => (LocalRelation.packed R s).Rejects (a ∘ localMap C e)) = _
  rw [restriction]
  exact LocalRelation.packed_rate _ _ _ _ _

omit [Fintype V] [Fintype E] in
theorem complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (reduced C).Satisfies a := by
  classical
  have hh (e : E) := LocalRelation.complete (relation C e)
    ⟨(x (C.left e), x (C.right e)), hx e⟩
  choose f h he using hh
  let a : Position C → Bit := fun p => match p with
    | .inl (v,z) => dot (x v) z
    | .inr ⟨e,.inl z⟩ => f e z
    | .inr ⟨e,.inr z⟩ => h e z
  have hrate (e : E) : testRate (fun s : EdgeSample K =>
      ((reduced C).query (e,s)).Rejects a) = 0 := by
    rw [edge_rate]
    change LocalRelation.rejectionWeight (relation C e) (f e) (h e)
      (dot (x (C.left e))) (dot (x (C.right e))) / 6 = 0
    rw [he e]
    norm_num
  refine ⟨a,?_⟩
  rintro ⟨e,s⟩
  exact (testRate_eq_zero_iff _).mp (hrate e) s
end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPAlphabetReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Machines_VertexMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPVertexMap
namespace MetricKMedian.PCP.BinaryCSP
open scoped Classical

variable {V W E A : Type} [Fintype E] [DecidableEq A]
variable (C : BinaryCSP V E A) (e : V ↪ W)
omit [DecidableEq A]
omit [Fintype E] in
lemma mapVertices_complete [Inhabited A] (a : V → A) (ha : C.Satisfies a) :
    (C.mapVertices e).Satisfies (extendAssignment e a) := by
  intro t
  simpa only [mapVertices,extendAssignment_image] using ha t
end MetricKMedian.PCP.BinaryCSP

end Inline_PCPVertexMap

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_PCP_BinaryReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPBinaryReduction

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace IncidenceReduction
variable {P T : Type} [Fintype T] (C : FourCSP P T)

omit [Fintype T] in
theorem complete (a : P → Bit) (ha : C.Satisfies a) :
    ∃ b, (reduced C).Satisfies b := by
  refine ⟨Sum.elim (fun p (_ : Fin 4) => a p) (fun t => a ∘ (C.query t).address),?_⟩
  rintro ⟨t,j⟩
  apply (allowed_iff C _ _ _).mpr
  refine ⟨?_,rfl⟩
  exact not_not.mp (ha t)

end IncidenceReduction

namespace AlphabetReduction
variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))

omit [Fintype V] [Fintype E] in
theorem binary_complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (binary C).Satisfies a := by
  obtain ⟨a,ha⟩ := complete C x hx
  exact IncidenceReduction.complete (reduced C) a ha

end AlphabetReduction
end MetricKMedian.PCP

end Inline_PCPBinaryReduction

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Amplification_PaddedAlphabet
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPPaddedAlphabet
namespace MetricKMedian.PCP.AlphabetReduction
open Finset
open scoped BigOperators Classical

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
variable (C : BinaryCSP V E (BitVector K))
omit [Fintype V] [Fintype E] in
lemma padded_complete_s53_oai (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (paddedBinary C).Satisfies a := by
  obtain ⟨a,ha⟩ := binary_complete C x hx
  exact ⟨_,(binary C).mapVertices_complete (nodeEmbed C) a ha⟩
end MetricKMedian.PCP.AlphabetReduction

end Inline_PCPPaddedAlphabet

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.PCP.AlphabetReduction.padded_complete_s53_oai := @OAI.MetricKMedian.PCP.AlphabetReduction.padded_complete_s53_oai

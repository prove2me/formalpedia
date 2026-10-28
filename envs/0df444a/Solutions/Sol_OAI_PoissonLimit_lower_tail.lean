-- Prove2me | solution 1 for OAI.PoissonLimit.lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:52:15.205988+00:00
-- url     : https://prove2.me/submissions/7410346b-7ea1-47cb-99ac-22b5850a9166

import Mathlib
import Definitions.Def_OAIQ16Cd000

section
-- module Solutions.OAIQ16_CD.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonConfig
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace PoissonConfig

variable {Ω : Type u_1} [MeasurableSpace Ω]

lemma measurableSet_sigma {β : ℕ → Type u_3} [∀ n, MeasurableSpace (β n)]
    {s : Set (Σ n, β n)} (h : ∀ n, MeasurableSet (Sigma.mk n ⁻¹' s)) :
    MeasurableSet s := by
  exact MeasurableSpace.measurableSet_iInf.mpr h

lemma measurable_sigma {β : ℕ → Type u_4} [∀ n, MeasurableSpace (β n)]
    {Γ : Type u_5} [MeasurableSpace Γ] {f : (Σ n, β n) → Γ}
    (h : ∀ n, Measurable (f ∘ Sigma.mk n)) : Measurable f := by
  intro s hs
  apply measurableSet_sigma
  intro n
  exact h n hs

lemma measurable_count {E : Set Ω} (hE : MeasurableSet E) :
    Measurable (count E) := by
  apply measurable_sigma
  intro n
  change Measurable (fun x : {f : Fin n → Ω // Function.Injective f} =>
    (Finset.univ.filter (fun i => x.val i ∈ E)).card)
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  exact hE.preimage ((measurable_pi_apply i).comp measurable_subtype_coe)

lemma measurable_occupied {E : Set Ω} (hE : MeasurableSet E) :
    Measurable (occupied E) := by
  exact (measurable_of_countable (fun k : ℕ => decide (0 < k))).comp (measurable_count hE)

omit [MeasurableSpace Ω] in
lemma count_zero_iff (E : Set Ω) (x : Config Ω) :
    count E x = 0 ↔ ∀ i, x.2.val i ∉ E := by
  simp [count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

lemma occupied_independent_of_void {μ : Measure Ω} [IsFiniteMeasure μ]
    {P : Measure (Config Ω)} [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
    {C : Type u_9} [Fintype C] (E : C → Set Ω) (hE : ∀ c, MeasurableSet (E c))
    (hd : Pairwise (fun c d => Disjoint (E c) (E d))) :
    iIndepFun (fun c => occupied (E c)) P := by
  let Z (c : C) := {x : Config Ω | count (E c) x = 0}
  have hZ (c : C) : MeasurableSet (Z c) :=
    (measurable_count (hE c)) (measurableSet_singleton 0)
  have hz : iIndepSet Z P := by
    apply (iIndepSet_iff_meas_biInter hZ).mpr
    intro s
    have he : (⋂ c ∈ s, Z c) = {x | count (⋃ c ∈ s, E c) x = 0} := by
      ext x
      simp only [mem_iInter, Z, mem_ofPred_eq, count_zero_iff, mem_iUnion, not_exists]
      aesop
    rw [he, hP.void _ (Finset.measurableSet_biUnion s (fun c _ => hE c)),
      measureReal_biUnion_finset (fun c _ d _ hcd => hd hcd) (fun c _ => hE c),
      ← Finset.sum_neg_distrib, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg
        (fun _ _ => (Real.exp_pos _).le)]
    exact Finset.prod_congr rfl (fun c _ => (hP.void (E c) (hE c)).symm)
  have hi := (hz.iIndepFun_indicator (β := ℕ)).comp
    (fun _ k => decide (k = 0)) (fun _ => measurable_of_countable _)
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  funext c x
  by_cases hx : count (E c) x = 0 <;>
    simp [occupied, Z, hx, Nat.pos_iff_ne_zero]

lemma occupied_prob_of_void {μ : Measure Ω} {P : Measure (Config Ω)}
    [IsProbabilityMeasure P] (hP : HasVoidLaw μ P) {E : Set Ω} (hE : MeasurableSet E) :
    P.real {x | occupied E x = true} = 1 - Real.exp (-μ.real E) := by
  have he : {x | occupied E x = true} = {x | count E x = 0}ᶜ := by
    ext x
    simp only [mem_ofPred_eq, occupied, decide_eq_true_eq, mem_compl_iff, Nat.pos_iff_ne_zero]
  have hm : MeasurableSet {x | count E x = 0} :=
    (measurable_count hE) (measurableSet_singleton 0)
  rw [he, probReal_compl_eq_one_sub hm]
  rw [measureReal_def, hP.void E hE, ENNReal.toReal_ofReal (Real.exp_pos _).le]

end PoissonConfig

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CellMatching
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace CellMatching

variable {I : Type u_1} {J : Type u_2} {C : Type u_3} [Fintype I] [Fintype J]

lemma incidence_equiv (M : Matching I J) (A : I → C → Prop) (B : J → C → Prop)
    (q : Classes M ↪ C) :
    (∀ v, classIncidence M A B v (q v)) ↔
      (∀ i, A i ((expand M q).val.1 i)) ∧ (∀ j, B j ((expand M q).val.2 j)) := by
  constructor
  · intro h
    constructor
    · intro i
      exact (h (Sum.inl i)).1
    · intro j
      by_cases hj : ∃ i, (i,j) ∈ M.val
      · obtain ⟨i, hi⟩ := hj
        have hb := (h (Sum.inl i)).2 j hi
        change B j (q (rightClass M j))
        rwa [rightClass_of_edge M hi]
      · have hj' : ∀ i, (i,j) ∉ M.val := by simpa only [not_exists] using hj
        change B j (q (rightClass M j))
        rw [rightClass_unmatched M j hj']
        exact h (Sum.inr ⟨j,hj'⟩)
  · rintro ⟨hA,hB⟩ (i | j)
    · refine ⟨hA i, ?_⟩
      intro j hij
      have hb := hB j
      change B j (q (rightClass M j)) at hb
      rwa [rightClass_of_edge M hij] at hb
    · have hb := hB j
      change B j (q (rightClass M j)) at hb
      rwa [rightClass_unmatched M j j.property] at hb

variable [Fintype C]

omit [Fintype C] in
lemma expansion_support (M : Matching I J) (q : Classes M ↪ C) :
    support (expand M q).val.1 ∪ support (expand M q).val.2 = support q := by
  ext c
  simp only [support, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i,hi⟩ | ⟨j,hj⟩)
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨rightClass M j, hj⟩
  · rintro ⟨v,hv⟩
    rcases v with i | j
    · exact Or.inl ⟨i,hv⟩
    · right
      refine ⟨j, ?_⟩
      change q (rightClass M j) = c
      simpa only [rightClass_unmatched M j j.property] using hv

omit [Fintype C] in
lemma expansion_weight (M : Matching I J) (q : Classes M ↪ C) (p : C → ℝ) :
    jointWeight p (expand M q).val.1 (expand M q).val.2 = ∏ v, p (q v) := by
  rw [jointWeight, expansion_support, support, Finset.prod_image]
  exact q.injective.injOn

lemma diagram_sum (M : Matching I J) (A : I → C → Prop) (B : J → C → Prop)
    (p : C → ℝ) :
    (∑ fg : ExactPair M C, pairWeight A B p fg.val) =
      ∑ q : Classes M ↪ C, if ∀ v, classIncidence M A B v (q v)
        then ∏ v, p (q v) else 0 := by
  rw [← (diagramEquiv M).sum_comp (fun fg => pairWeight A B p fg.val)]
  apply Finset.sum_congr rfl
  intro q _
  change pairWeight A B p (expand M q).val = _
  simp only [pairWeight, ← incidence_equiv, expansion_weight]

omit [Fintype C] in

lemma support_inter_nonempty_iff (f : I ↪ C) (g : J ↪ C) :
    (support f ∩ support g).Nonempty ↔ (exactMatching f g).val.Nonempty := by
  simp only [Finset.nonempty_iff_ne_empty]
  constructor
  · contrapose!
    intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro c hc
    rcases Finset.mem_inter.mp hc with ⟨hf,hg⟩
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hf
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hg
    have hm : (i,j) ∈ (exactMatching f g).val :=
      (mem_exactMatching f g i j).mpr (hi.trans hj.symm)
    simp only [h, Finset.notMem_empty] at hm
  · contrapose!
    intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨i,j⟩ hm
    have he := (mem_exactMatching f g i j).mp hm
    have hc : f i ∈ support f ∩ support g := Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
       Finset.mem_image.mpr ⟨j, Finset.mem_univ _, he.symm⟩⟩
    simp only [h, Finset.notMem_empty] at hc

omit [Fintype C] in
lemma matching_eq (M : Matching I J) (fg : ExactPair M C) :
    exactMatching fg.val.1 fg.val.2 = M := by
  apply Subtype.ext
  ext ij
  exact (mem_exactMatching _ _ ij.1 ij.2).trans (fg.property ij.1 ij.2)

lemma dependency_diagram_sum (A : I → C → Prop) (B : J → C → Prop) (p : C → ℝ) :
    (∑ fg : (I ↪ C) × (J ↪ C),
      if (support fg.1 ∩ support fg.2).Nonempty then pairWeight A B p fg else 0) =
      ∑ M : Matching I J, if M.val.Nonempty then
        ∑ q : Classes M ↪ C,
          if ∀ v, classIncidence M A B v (q v) then ∏ v, p (q v) else 0
      else 0 := by
  simp only [support_inter_nonempty_iff]
  have h := (allDiagramsEquiv (I := I) (J := J) (C := C)).sum_comp
    (fun mq => if (exactMatching mq.2.val.1 mq.2.val.2).val.Nonempty
      then pairWeight A B p mq.2.val else 0)
  change (∑ fg, if (exactMatching fg.1 fg.2).val.Nonempty
    then pairWeight A B p fg else 0) = _ at h
  rw [h, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro M _
  simp only [matching_eq]
  by_cases hm : M.val.Nonempty
  · simp only [ite_eq_left hm]
    exact diagram_sum M A B p
  · simp only [ite_eq_right hm, Finset.sum_const_zero]

end CellMatching

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MatchingAlgebra
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators

universe u_1 u_2

namespace MatchingAlgebra
variable {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]

lemma prod_edges (M : Finset (I × J)) (f : I → J → ℝ) :
    (∏ i, ∏ j, if (i,j) ∈ M then f i j else 1) =
      ∏ e ∈ M, f e.1 e.2 := by
  rw [← Fintype.prod_prod_type (fun e : I × J => if e ∈ M then f e.1 e.2 else 1)]
  rw [← Finset.prod_filter]
  congr 1
  ext e
  simp

omit [Fintype I] in
lemma leftWeight_factor (M : Finset (I × J))
    (hm : ∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k)
    (a : I → ℝ) (w : I → J → ℝ) (ha : ∀ i, a i ≠ 0) (i : I) :
    leftWeight M a w i = a i * ∏ j, if (i,j) ∈ M then w i j / a i else 1 := by
  by_cases h : ∃ j, (i,j) ∈ M
  · rw [leftWeight, dite_eq_left h]
    have hp : (∏ j, if (i,j) ∈ M then w i j / a i else 1) = w i h.choose / a i := by
      rw [Finset.prod_eq_single h.choose]
      · exact ite_eq_left h.choose_spec
      · intro j _ hj
        apply ite_eq_right
        intro hij
        exact hj (hm i j h.choose hij h.choose_spec)
      · simp
    rw [hp, mul_div_cancel₀ _ (ha i)]
  · rw [leftWeight, dite_eq_right h]
    simp only [not_exists] at h
    simp only [h, ↓reduceIte, Finset.prod_const_one, mul_one]

lemma prod_leftWeight (M : Finset (I × J))
    (hm : ∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k)
    (a : I → ℝ) (w : I → J → ℝ) (ha : ∀ i, a i ≠ 0) :
    (∏ i, leftWeight M a w i) = (∏ i, a i) * ∏ e ∈ M, w e.1 e.2 / a e.1 := by
  simp_rw [leftWeight_factor M hm a w ha]
  rw [Finset.prod_mul_distrib, prod_edges]

lemma prod_unmatched_right (M : Finset (I × J))
    (hm : ∀ i j k, (i,k) ∈ M → (j,k) ∈ M → i = j) (b : J → ℝ) :
    (∏ j, b j) = (∏ j : {j : J // ∀ i, (i,j) ∉ M}, b j.val) *
      ∏ e ∈ M, b e.2 := by
  have hproj : Set.InjOn Prod.snd (M : Set (I × J)) := by
    intro e he f hf h
    apply Prod.ext _ h
    exact hm e.1 f.1 e.2 he (by simpa only [h, Prod.mk.eta, Finset.mem_coe] using hf)
  have hsub : (∏ j : {j : J // ∀ i, (i,j) ∉ M}, b j.val) =
      ∏ j ∈ Finset.univ \ M.image Prod.snd, b j := by
    symm
    apply Finset.prod_subtype
    intro j
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h i him
      exact h ⟨(i,j),him,rfl⟩
    · rintro h ⟨⟨i,k⟩,he,rfl⟩
      exact h i he
  rw [hsub, ← Finset.prod_image hproj]
  exact (Finset.prod_sdiff (Finset.subset_univ _)).symm

lemma normalized_diagram_identity (M : Finset (I × J))
    (hl : ∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k)
    (hr : ∀ i j k, (i,k) ∈ M → (j,k) ∈ M → i = j)
    (a : I → ℝ) (b : J → ℝ) (w : I → J → ℝ)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ j, b j ≠ 0) :
    (∏ i, leftWeight M a w i) * (∏ j : {j : J // ∀ i, (i,j) ∉ M}, b j.val) =
      (∏ i, a i) * (∏ j, b j) * ∏ e ∈ M, w e.1 e.2 / (a e.1 * b e.2) := by
  rw [prod_leftWeight M hl a w ha, prod_unmatched_right M hr b]
  simp_rw [div_mul_eq_div_div, Finset.prod_div_distrib]
  have hp : (∏ e ∈ M, b e.2) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun e _ => hb e.2)
  field_simp
end MatchingAlgebra

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CellCounts
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4

namespace CellCounts

variable {I : Type u_1} {C : Type u_2} [Fintype I] [Fintype C]

theorem sum_assignmentWeight (w : I → C → ℝ) :
    ∑ f, assignmentWeight w f = ∏ i, ∑ c, w i c := by
  exact (Fintype.prod_sum w).symm

omit [Fintype C] in
theorem assignmentWeight_nonneg {w : I → C → ℝ}
    (hw : ∀ i c, 0 ≤ w i c) (f : I → C) : 0 ≤ assignmentWeight w f :=
  Finset.prod_nonneg (fun i _ => hw i (f i))

theorem injectiveSum_le {w : I → C → ℝ} (hw : ∀ i c, 0 ≤ w i c) :
    injectiveSum w ≤ ∏ i, ∑ c, w i c := by
  rw [← sum_assignmentWeight]
  apply Finset.sum_le_sum
  intro f _
  split_ifs
  · rfl
  · exact assignmentWeight_nonneg hw f

omit [Fintype C] in
theorem force_weight (w : I → C → ℝ) (i j : I) (c : C) (f : I → C) :
    assignmentWeight (force w i j c) f =
      if f i = c ∧ f j = c then assignmentWeight w f else 0 := by
  classical
  by_cases h : f i = c ∧ f j = c
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v = i ∨ v = j
    · rcases hv with rfl | rfl <;> simp [force, h.1, h.2]
    · simp [force, hv]
  · rw [ite_eq_right h]
    simp only [not_and_or] at h
    rcases h with hi | hj
    · apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [force, hi]
    · apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [force, hj]

theorem collision_decompose (w : I → C → ℝ) (i j : I) :
    collisionSum w i j = ∑ c, ∏ v, ∑ d, force w i j c v d := by
  classical
  simp_rw [← sum_assignmentWeight, force_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : f i = f j
  · simp [h]
  · simp [ite_and, h, Ne.symm h]

omit [Fintype I] in
theorem sum_force (w : I → C → ℝ) (i j : I) (c : C) (v : I) :
    ∑ d, force w i j c v d = if v = i ∨ v = j then w v c else ∑ d, w v d := by
  classical
  by_cases hv : v = i ∨ v = j <;> simp [force, hv]

theorem prod_erase_two [DecidableEq I] (b : I → ℝ) {i j : I} (hij : i ≠ j) :
    ∏ v, b v = b i * b j * ∏ v ∈ (Finset.univ.erase i).erase j, b v := by
  rw [← Finset.mul_prod_erase _ b (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase _ b (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)]
  ring

theorem collision_formula [DecidableEq I] (w : I → C → ℝ) {i j : I} (hij : i ≠ j) :
    collisionSum w i j = (∑ c, w i c * w j c) *
      ∏ v ∈ (Finset.univ.erase i).erase j, ∑ d, w v d := by
  rw [collision_decompose, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [prod_erase_two (fun v => ∑ d, force w i j c v d) hij]
  simp only [sum_force, true_or, ↓reduceIte, or_true]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  have hi : v ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1
  have hj : v ≠ j := (Finset.mem_erase.mp hv).1
  simp [hi, hj]

omit [Fintype C] in
theorem noninjective_has_pair [LinearOrder I] {f : I → C}
    (hf : ¬ Function.Injective f) : ∃ ij ∈ pairs I, f ij.1 = f ij.2 := by
  classical
  simp only [Function.Injective] at hf
  push Not at hf
  obtain ⟨i, j, he, hn⟩ := hf
  obtain hlt | hgt := lt_or_gt_of_ne hn
  · exact ⟨(i,j), by simp [pairs, hlt], he⟩
  · exact ⟨(j,i), by simp [pairs, hgt], he.symm⟩

theorem collision_union_bound [LinearOrder I] {w : I → C → ℝ}
    (hw : ∀ i c, 0 ≤ w i c) :
    (∏ i, ∑ c, w i c) - injectiveSum w ≤
      ∑ ij ∈ pairs I, collisionSum w ij.1 ij.2 := by
  classical
  rw [← sum_assignmentWeight, injectiveSum, ← Finset.sum_sub_distrib]
  simp only [collisionSum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro f _
  have hnonneg : ∀ ij ∈ pairs I,
      0 ≤ (if f ij.1 = f ij.2 then assignmentWeight w f else 0) := by
    intro ij _
    split_ifs
    · exact assignmentWeight_nonneg hw f
    · rfl
  by_cases hf : Function.Injective f
  · simp only [hf, ↓reduceIte, sub_self]
    exact Finset.sum_nonneg hnonneg
  · simp only [hf, ↓reduceIte, sub_zero]
    obtain ⟨ij, hij, he⟩ := noninjective_has_pair hf
    simpa only [he, ↓reduceIte] using Finset.single_le_sum hnonneg hij

omit [Fintype I] [Fintype C] in

theorem prod_relative_error {J : Type u_4} (s : Finset J) (a b : J → ℝ) (e : ℝ)
    (he : 0 ≤ e) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hba : ∀ i ∈ s, b i ≤ a i)
    (herr : ∀ i ∈ s, a i - b i ≤ e * a i) :
    (∏ i ∈ s, a i) - (∏ i ∈ s, b i) ≤ (s.card : ℝ) * e * ∏ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hb' : ∀ i ∈ s, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hba' : ∀ i ∈ s, b i ≤ a i := fun i hi => hba i (Finset.mem_insert_of_mem hi)
    have ha' : ∀ i ∈ s, 0 ≤ a i := fun i hi => (hb' i hi).trans (hba' i hi)
    have hjb := hb j (Finset.mem_insert_self j s)
    have hja := hjb.trans (hba j (Finset.mem_insert_self j s))
    have h1 := mul_le_mul_of_nonneg_left
      (ih hb' hba' (fun i hi => herr i (Finset.mem_insert_of_mem hi))) hja
    have h2 := mul_le_mul_of_nonneg_right (herr j (Finset.mem_insert_self j s))
      (Finset.prod_nonneg hb')
    have h3 := mul_le_mul_of_nonneg_left (Finset.prod_le_prod hb' hba')
      (mul_nonneg he hja)
    simp only [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, Nat.cast_add,
      Nat.cast_one]
    nlinarith

theorem collision_error [LinearOrder I] (w v : I → C → ℝ) (d e : ℝ)
    (r : I → I → ℝ) (he : 0 ≤ e)
    (hw : ∀ i c, 0 ≤ w i c) (hwv : ∀ i c, w i c ≤ v i c)
    (hrow : ∀ i, (∑ c, v i c) - (∑ c, w i c) ≤ e * ∑ c, v i c)
    (hc : ∀ i j, i ≠ j → (∑ c, w i c * w j c) ≤ d * r i j) :
    0 ≤ (∏ i, ∑ c, v i c) - injectiveSum w ∧
    (∏ i, ∑ c, v i c) - injectiveSum w ≤
      (Fintype.card I : ℝ) * e * (∏ i, ∑ c, v i c) +
      d * ∑ ij ∈ pairs I, r ij.1 ij.2 *
        ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, v u c := by
  classical
  have hv : ∀ i c, 0 ≤ v i c := fun i c => (hw i c).trans (hwv i c)
  have hp : (∏ i, ∑ c, w i c) ≤ ∏ i, ∑ c, v i c :=
    Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun c _ => hw i c))
      (fun i _ => Finset.sum_le_sum (fun c _ => hwv i c))
  refine ⟨sub_nonneg.mpr ((injectiveSum_le hw).trans hp), ?_⟩
  have ht := prod_relative_error (Finset.univ : Finset I)
    (fun i => ∑ c, v i c) (fun i => ∑ c, w i c) e he
    (fun i _ => Finset.sum_nonneg (fun c _ => hw i c))
    (fun i _ => Finset.sum_le_sum (fun c _ => hwv i c)) (fun i _ => hrow i)
  have hu := collision_union_bound hw
  have hc' : (∑ ij ∈ pairs I, collisionSum w ij.1 ij.2) ≤
      d * ∑ ij ∈ pairs I, r ij.1 ij.2 *
        ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, v u c := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ij hij
    have hne : ij.1 ≠ ij.2 := ne_of_lt (Finset.mem_filter.mp hij).2
    rw [collision_formula w hne]
    calc
      _ ≤ (d * r ij.1 ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, w u c :=
        mul_le_mul_of_nonneg_right (hc _ _ hne)
          (Finset.prod_nonneg (fun i _ => Finset.sum_nonneg (fun c _ => hw i c)))
      _ ≤ (d * r ij.1 ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, ∑ c, v u c := by
        apply mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun c _ => hw i c))
            (fun i _ => Finset.sum_le_sum (fun c _ => hwv i c)))
        exact (Finset.sum_nonneg (fun c _ => mul_nonneg (hw _ _) (hw _ _))).trans
          (hc _ _ hne)
      _ = _ := mul_assoc _ _ _
  simp only [Finset.card_univ] at ht
  linarith

omit [Fintype I] [Fintype C] in

theorem occupation_error {a d : ℝ} (ha : 0 ≤ a) (had : a ≤ d) :
    0 ≤ 1 - Real.exp (-a) ∧
    0 ≤ a - (1 - Real.exp (-a)) ∧
    a - (1 - Real.exp (-a)) ≤ a ^ 2 / 2 ∧ a ^ 2 / 2 ≤ d * a / 2 := by
  have hmono : Monotone (fun x : ℝ => 1 - x + x ^ 2 / 2 - Real.exp (-x)) := by
    apply monotone_of_hasDerivAt_nonneg (f' := fun x => x - 1 + Real.exp (-x))
    · intro x
      convert! (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
        (((hasDerivAt_id x).pow 2).div_const 2)).sub
        (((hasDerivAt_id x).neg).exp) using 1; norm_num; ring
    · intro x
      change 0 ≤ x - 1 + Real.exp (-x)
      have h := Real.add_one_le_exp (-x)
      linarith
  have hh := hmono ha
  simp only [neg_zero, Real.exp_zero, sub_zero, zero_pow (by omega : 2 ≠ 0),
    zero_div, add_zero, sub_self] at hh
  have hlin := Real.add_one_le_exp (-a)
  have hexp := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
  have hsq := mul_le_mul_of_nonneg_right had ha
  refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

theorem cell_collision_error [LinearOrder I] (A : I → C → Prop) (a : C → ℝ)
    {d : ℝ} (hd : 0 ≤ d) (ha : ∀ c, 0 ≤ a c) (had : ∀ c, a c ≤ d) :
    let v := slotWeight A a
    let w := slotWeight A (fun c => 1 - Real.exp (-a c))
    let mass := fun i => ∑ c, v i c
    let overlap := fun i j => ∑ c, if A i c ∧ A j c then a c else 0
    0 ≤ (∏ i, mass i) - injectiveSum w ∧
    (∏ i, mass i) - injectiveSum w ≤ d *
      ((Fintype.card I : ℝ) / 2 * (∏ i, mass i) +
        ∑ ij ∈ pairs I, overlap ij.1 ij.2 *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, mass u) := by
  classical
  dsimp only
  have hoc := fun c => occupation_error (ha c) (had c)
  have hw : ∀ i c, 0 ≤ slotWeight A (fun c => 1 - Real.exp (-a c)) i c := by
    intro i c
    unfold slotWeight
    split_ifs
    · exact (hoc c).1
    · rfl
  have hwv : ∀ i c, slotWeight A (fun c => 1 - Real.exp (-a c)) i c ≤
      slotWeight A a i c := by
    intro i c
    unfold slotWeight
    split_ifs
    · linarith [(hoc c).2.1]
    · rfl
  have hrow : ∀ i, (∑ c, slotWeight A a i c) -
      (∑ c, slotWeight A (fun c => 1 - Real.exp (-a c)) i c) ≤
      (d / 2) * ∑ c, slotWeight A a i c := by
    intro i
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    unfold slotWeight
    split_ifs
    · have h := (hoc c).2.2.1.trans (hoc c).2.2.2
      linarith
    · simp
  have hcol : ∀ i j, i ≠ j →
     (∑ c, slotWeight A (fun c => 1 - Real.exp (-a c)) i c *
       slotWeight A (fun c => 1 - Real.exp (-a c)) j c) ≤
      d * ∑ c, if A i c ∧ A j c then a c else 0 := by
    intro i j _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    by_cases hi : A i c <;> by_cases hj : A j c <;>
      simp only [slotWeight, hi, hj, and_self, and_false, false_and,
        ↓reduceIte, mul_zero, zero_mul, le_refl]
    have hpa : 1 - Real.exp (-a c) ≤ a c := by linarith [(hoc c).2.1]
    calc
      _ ≤ a c * a c := mul_self_le_mul_self (hoc c).1 hpa
      _ ≤ d * a c := mul_le_mul_of_nonneg_right (had c) (ha c)
  have h := collision_error (slotWeight A (fun c => 1 - Real.exp (-a c)))
    (slotWeight A a) d (d / 2)
    (fun i j => ∑ c, if A i c ∧ A j c then a c else 0)
    (by positivity) hw hwv hrow hcol
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

lemma injectiveSum_eq_embeddings (w : I → C → ℝ) :
    injectiveSum w = ∑ f : I ↪ C, ∏ i, w i (f i) := by
  classical
  rw [injectiveSum, ← Finset.sum_filter]
  rw [Finset.sum_subtype _ (show ∀ f : I → C, f ∈ Finset.univ.filter Function.Injective ↔ Function.Injective f by simp)]
  exact (Equiv.subtypeInjectiveEquivEmbedding I C).sum_comp
    (fun f => ∏ i, w i (f i))

omit [Fintype C] in
lemma assignmentWeight_slot (A : I → C → Prop) (p : C → ℝ) (f : I → C) :
    assignmentWeight (slotWeight A p) f =
      if ∀ i, A i (f i) then ∏ i, p (f i) else 0 := by
  classical
  by_cases h : ∀ i, A i (f i)
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i _
    exact ite_eq_left (h i)
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

lemma injectiveSum_slot_eq (A : I → C → Prop) (p : C → ℝ) :
    injectiveSum (slotWeight A p) = ∑ f : I ↪ C,
      if ∀ i, A i (f i) then ∏ i, p (f i) else 0 := by
  rw [injectiveSum_eq_embeddings]
  apply Finset.sum_congr rfl
  intro f _
  exact assignmentWeight_slot A p f

end CellCounts

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonMeasureCells
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5

namespace PoissonMeasureCells

open Set MeasureTheory
open scoped ENNReal

variable {Ω : Type u_1} {C : Type u_2} {I : Type u_3} [MeasurableSpace Ω] [Fintype C] [Fintype I]

omit [Fintype I] in
lemma respects_inter (P : Partition Ω C) {F G : Set Ω}
    (hF : Respects P F) (hG : Respects P G) : Respects P (F ∩ G) := by
  intro c
  rcases hF c with hF | hF
  · rcases hG c with hG | hG
    · exact Or.inl (Set.subset_inter hF hG)
    · exact Or.inr (hG.mono_right inter_subset_right)
  · exact Or.inr (hF.mono_right inter_subset_left)

omit [Fintype I] in
lemma mass_eq_sum (μ : Measure Ω) [IsFiniteMeasure μ] (P : Partition Ω C)
    {F : Set Ω} (hF : MeasurableSet F) (hr : Respects P F) :
    μ.real F = ∑ c, if P.cell c ⊆ F then μ.real (P.cell c) else 0 := by
  classical
  have heq : (⋃ c, P.cell c ∩ F) = F := by
    rw [← Set.iUnion_inter, P.cover, Set.univ_inter]
  rw [← heq, measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro c _
    rw [heq]
    by_cases hc : P.cell c ⊆ F
    · rw [ite_eq_left hc, Set.inter_eq_left.mpr hc]
    · rw [ite_eq_right hc, Set.disjoint_iff_inter_eq_empty.mp ((hr c).resolve_left hc)]
      exact measureReal_empty
  · intro c d hcd
    exact (P.disjoint hcd).mono inter_subset_left inter_subset_left
  · intro c
    exact (P.measurable c).inter hF

lemma collision_error (μ : Measure Ω) [IsFiniteMeasure μ] (P : Partition Ω C)
    [LinearOrder I] (F : I → Set Ω) (hF : ∀ i, MeasurableSet (F i))
    (hr : ∀ i, Respects P (F i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ c, μ.real (P.cell c) ≤ δ) :
    0 ≤ (∏ i, μ.real (F i)) - Q μ P F ∧
    (∏ i, μ.real (F i)) - Q μ P F ≤ δ *
      ((Fintype.card I : ℝ)/2 * (∏ i, μ.real (F i)) +
        ∑ ij ∈ CellCounts.pairs I, μ.real (F ij.1 ∩ F ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, μ.real (F u)) := by
  classical
  have hmass (i : I) : (∑ c, CellCounts.slotWeight
      (fun i c => P.cell c ⊆ F i) (fun c => μ.real (P.cell c)) i c) = μ.real (F i) :=
    (mass_eq_sum μ P (hF i) (hr i)).symm
  have hinter (i j : I) : (∑ c, if P.cell c ⊆ F i ∧ P.cell c ⊆ F j
      then μ.real (P.cell c) else 0) = μ.real (F i ∩ F j) := by
    simpa only [Set.subset_inter_iff] using
      (mass_eq_sum μ P ((hF i).inter (hF j)) (respects_inter P (hr i) (hr j))).symm
  have h := CellCounts.cell_collision_error (fun i c => P.cell c ⊆ F i)
    (fun c => μ.real (P.cell c)) hδ (fun _ => measureReal_nonneg) hd
  dsimp only at h
  simpa only [hmass, hinter, Q] using h

end PoissonMeasureCells

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonDiagrams
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PoissonDiagrams
open Set MeasureTheory CellMatching PoissonMeasureCells
open scoped Classical BigOperators
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} {C : Type u_4} [MeasurableSpace Ω] [Fintype I] [Fintype J] [Fintype C]

omit [Fintype C] [MeasurableSpace Ω] in
lemma classSet_left_matched (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω)
    {i : I} {j : J} (hij : (i,j) ∈ M.val) :
    classSet M E F (Sum.inl i) = E i ∩ F j := by
  ext x
  constructor
  · intro h
    exact ⟨h.1,h.2 j hij⟩
  · rintro ⟨hE,hF⟩
    refine ⟨hE, ?_⟩
    intro k hik
    rwa [M.property.1 _ _ _ hik hij]

omit [Fintype C] [MeasurableSpace Ω] in
lemma classSet_left_unmatched (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω)
    {i : I} (hi : ∀ j, (i,j) ∉ M.val) : classSet M E F (Sum.inl i) = E i := by
  ext x
  simp only [classSet, Sum.elim_inl, mem_ofPred_eq, hi, false_implies, implies_true, and_true]

omit [Fintype C] in
lemma classSet_measurable (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (hF : ∀ j, MeasurableSet (F j)) :
    ∀ v, MeasurableSet (classSet M E F v) := by
  rintro (i | j)
  · by_cases hi : ∃ j, (i,j) ∈ M.val
    · rw [classSet_left_matched M E F hi.choose_spec]
      exact (hE i).inter (hF hi.choose)
    · rw [classSet_left_unmatched M E F (by simpa only [not_exists] using hi)]
      exact hE i
  · exact hF j

lemma classSet_respects (P : Partition Ω C) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω) (hE : ∀ i, Respects P (E i))
    (hF : ∀ j, Respects P (F j)) : ∀ v, Respects P (classSet M E F v) := by
  rintro (i | j)
  · by_cases hi : ∃ j, (i,j) ∈ M.val
    · rw [classSet_left_matched M E F hi.choose_spec]
      exact respects_inter P (hE i) (hF hi.choose)
    · rw [classSet_left_unmatched M E F (by simpa only [not_exists] using hi)]
      exact hE i
  · exact hF j

lemma classSet_incidence (P : Partition Ω C) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω) (v : Classes M) (c : C) :
    P.cell c ⊆ classSet M E F v ↔
      classIncidence M (fun i c => P.cell c ⊆ E i) (fun j c => P.cell c ⊆ F j) v c := by
  rcases v with i | j
  · constructor
    · intro h
      refine ⟨fun x hx => (h hx).1, ?_⟩
      intro j hij x hx
      exact (h hx).2 j hij
    · rintro ⟨hE,hF⟩ x hx
      exact ⟨hE hx,fun j hij => hF j hij hx⟩
  · rfl

omit [Fintype C] in
lemma classSet_mass_left (μ : Measure Ω) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω) (i : I) :
    μ.real (classSet M E F (Sum.inl i)) =
      MatchingAlgebra.leftWeight M.val (fun i => μ.real (E i))
        (fun i j => μ.real (E i ∩ F j)) i := by
  unfold MatchingAlgebra.leftWeight
  split_ifs with hi
  · rw [classSet_left_matched M E F hi.choose_spec]
  · rw [classSet_left_unmatched M E F (by simpa only [not_exists] using hi)]

omit [Fintype C] in
lemma classSet_product (μ : Measure Ω) (M : Matching I J)
    (E : I → Set Ω) (F : J → Set Ω)
    (hE : ∀ i, μ.real (E i) ≠ 0) (hF : ∀ j, μ.real (F j) ≠ 0) :
    (∏ v, μ.real (classSet M E F v)) =
      (∏ i, μ.real (E i)) * (∏ j, μ.real (F j)) *
        ∏ ij ∈ M.val, μ.real (E ij.1 ∩ F ij.2) / (μ.real (E ij.1) * μ.real (F ij.2)) := by
  rw [Fintype.prod_sum_type]
  simp_rw [classSet_mass_left]
  exact MatchingAlgebra.normalized_diagram_identity M.val M.property.1 M.property.2
    _ _ _ hE hF

omit [Fintype C] in
lemma diagram_eq_classSet_sum (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω)
    (hE : ∀ i, μ.real (E i) ≠ 0) (hF : ∀ j, μ.real (F j) ≠ 0) :
    diagram μ E F = ∑ M : Matching I J, if M.val.Nonempty then
      ∏ v, μ.real (classSet M E F v) else 0 := by
  rw [diagram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro M _
  by_cases hm : M.val.Nonempty
  · rw [ite_eq_left hm, ite_eq_left hm, classSet_product μ M E F hE hF]
  · rw [ite_eq_right hm, ite_eq_right hm, mul_zero]

lemma dependency_eq_sum_Q (μ : Measure Ω) (P : Partition Ω C)
    (E : I → Set Ω) (F : J → Set Ω) :
    (∑ fg : (I ↪ C) × (J ↪ C), if (support fg.1 ∩ support fg.2).Nonempty then
      pairWeight (fun i c => P.cell c ⊆ E i) (fun j c => P.cell c ⊆ F j)
        (fun c => 1 - Real.exp (-μ.real (P.cell c))) fg else 0) =
      ∑ M : Matching I J, if M.val.Nonempty then Q μ P (classSet M E F) else 0 := by
  rw [dependency_diagram_sum]
  apply Finset.sum_congr rfl
  intro M _
  by_cases hm : M.val.Nonempty
  · rw [ite_eq_left hm, ite_eq_left hm, Q, CellCounts.injectiveSum_slot_eq]
    simp_rw [classSet_incidence]
  · rw [ite_eq_right hm, ite_eq_right hm]

omit [Fintype C] [Fintype J] in

lemma Q_tendsto {T : Type u_5} {l : Filter T} (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : T → Type u_6) [∀ t, Fintype (C t)] (P : ∀ t, Partition Ω (C t))
    (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hr : ∀ t i, Respects (P t) (E i)) {δ : T → ℝ}
    (hδ : ∀ t, 0 ≤ δ t) (hd : ∀ t c, μ.real ((P t).cell c) ≤ δ t)
    (hlim : Filter.Tendsto δ l (nhds 0)) :
    Filter.Tendsto (fun t => Q μ (P t) E) l (nhds (∏ i, μ.real (E i))) := by
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  let B : ℝ := (Fintype.card I : ℝ)/2 * (∏ i, μ.real (E i)) +
        ∑ ij ∈ CellCounts.pairs I, μ.real (E ij.1 ∩ E ij.2) *
          ∏ u ∈ (Finset.univ.erase ij.1).erase ij.2, μ.real (E u)
  have hbound (t : T) := collision_error μ (P t) E hE (hr t) (hδ t) (hd t)
  have herr : Filter.Tendsto (fun t => (∏ i, μ.real (E i)) - Q μ (P t) E) l (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun t => (hbound t).1))
      (Filter.Eventually.of_forall (fun t => (hbound t).2))
    simpa only [zero_mul] using hlim.mul_const B
  have ht := (tendsto_const_nhds (x := ∏ i, μ.real (E i))).sub herr
  simpa only [sub_sub_cancel, sub_zero] using ht

end PoissonDiagrams

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_FiniteJanson
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11

namespace FiniteJanson

variable {V : Type u_1} [Fintype V]

variable {p : V → ℝ}

theorem atom_nonneg (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (x : V → Bool) :
    0 ≤ atom p x := by
  apply Finset.prod_nonneg
  intro v _
  split_ifs <;> linarith [(hp v).1, (hp v).2]

theorem sum_atom (p : V → ℝ) : ∑ x, atom p x = 1 := by
  simp only [atom]
  rw [← Fintype.prod_sum (fun v (b : Bool) => if b then p v else 1 - p v)]
  simp

theorem prob_nonneg (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (A : Set (V → Bool)) :
    0 ≤ prob p A := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact atom_nonneg hp x
  · rfl

@[simp] theorem prob_univ (p : V → ℝ) : prob p Set.univ = 1 := by
  simp [prob, sum_atom]

theorem prob_mono (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    {A B : Set (V → Bool)} (hAB : A ⊆ B) : prob p A ≤ prob p B := by
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : x ∈ A
  · simp [ha, hAB ha]
  · simp only [ha, ↓reduceIte]
    split_ifs
    · exact atom_nonneg hp x
    · rfl

theorem prob_compl (p : V → ℝ) (A : Set (V → Bool)) :
    prob p Aᶜ = 1 - prob p A := by
  have h : prob p A + prob p Aᶜ = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← sum_atom p]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ A <;> simp [hx]
  linarith

theorem prob_inter_compl (p : V → ℝ) (A B : Set (V → Bool)) :
    prob p (A ∩ Bᶜ) = prob p A - prob p (A ∩ B) := by
  have h : prob p (A ∩ B) + prob p (A ∩ Bᶜ) = prob p A := by
    rw [prob, prob, prob, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]
  linarith

theorem atom_lattice (p : V → ℝ) (x y : V → Bool) :
    atom p x * atom p y = atom p (x ⊓ y) * atom p (x ⊔ y) := by
  simp only [atom, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  change (if x v then p v else 1 - p v) * (if y v then p v else 1 - p v) =
    (if x v ⊓ y v then p v else 1 - p v) * (if x v ⊔ y v then p v else 1 - p v)
  cases hx : x v <;> cases hy : y v <;> simp [mul_comm]

theorem prob_eq (p : V → ℝ) (A : Set (V → Bool)) :
    prob p A = ∑ x, atom p x * ind A x := by
  apply Finset.sum_congr rfl
  intro x _
  simp [ind, mul_ite]

omit [Fintype V] in
theorem ind_nonneg (A : Set (V → Bool)) : 0 ≤ ind A := by
  intro x
  simp only [ind, Pi.zero_apply]
  split_ifs <;> norm_num

omit [Fintype V] in
theorem ind_mono {A : Set (V → Bool)} (hA : IsUpperSet A) : Monotone (ind A) := by
  intro x y hxy
  by_cases hx : x ∈ A
  · simp [ind, hx, hA hxy hx]
  · simp only [ind, hx, ↓reduceIte]
    split_ifs <;> norm_num

theorem harris (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    {A B : Set (V → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prob p A * prob p B ≤ prob p (A ∩ B) := by
  have h := fkg (ind A) (ind B) (atom p) (atom_nonneg hp)
    (ind_nonneg A) (ind_nonneg B) (ind_mono hA) (ind_mono hB)
    (fun x y => (atom_lattice p x y).le)
  rw [← prob_eq, ← prob_eq, sum_atom, one_mul] at h
  apply h.trans_eq
  rw [prob_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ind, ha, hb]

theorem harris_opposite (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    {A F : Set (V → Bool)} (hA : IsUpperSet A) (hF : IsLowerSet F) :
    prob p (A ∩ F) ≤ prob p A * prob p F := by
  have h := harris hp hA hF.compl
  rw [prob_compl, prob_inter_compl] at h
  nlinarith

theorem atom_split (p : V → ℝ) (S : Set V) (x : V → Bool) :
    atom p x = atom (fun v : S => p v) (fun v : S => x v) *
      atom (fun v : (Sᶜ : Set V) => p v) (fun v : (Sᶜ : Set V) => x v) := by
  exact (Fintype.prod_subtype_mul_prod_subtype (fun v => v ∈ S)
    (fun v => if x v then p v else 1 - p v)).symm

theorem prob_split (p : V → ℝ) (S : Set V)
    (A : Set (S → Bool)) (B : Set ((Sᶜ : Set V) → Bool)) :
    prob p {x | (fun v : S => x v) ∈ A ∧ (fun v : (Sᶜ : Set V) => x v) ∈ B} =
      prob (fun v : S => p v) A * prob (fun v : (Sᶜ : Set V) => p v) B := by
  let e := Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => Bool)
  calc
    _ = ∑ z : (S → Bool) × ((Sᶜ : Set V) → Bool),
        (if z.1 ∈ A then atom (fun v : S => p v) z.1 else 0) *
        (if z.2 ∈ B then atom (fun v : (Sᶜ : Set V) => p v) z.2 else 0) := by
      apply Fintype.sum_equiv e
      intro x
      simp only [e, Equiv.piEquivPiSubtypeProd_apply, Set.mem_ofPred_eq]
      split_ifs with h hab hb
      · exact atom_split p S x
      · exfalso
        apply hb
        convert h.2
      · exfalso
        apply hab
        convert h.1
      · exfalso
        apply hab
        convert h.1
      · rename_i hh₁ hh₂
        exfalso
        apply h
        constructor
        · convert hh₁
        · convert hh₂
      · simp
      · simp
      · simp
    _ = _ := by
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, prob]
      congr 1 <;> apply Finset.sum_congr (by congr; apply Subsingleton.elim) <;> intro x hx <;> congr 1

theorem prob_independent (p : V → ℝ) (S : Set V)
    {A B : Set (V → Bool)} (hA : Supported S A) (hB : Supported (Sᶜ : Set V) B) :
    prob p (A ∩ B) = prob p A * prob p B := by
  let e := Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => Bool)
  let A' : Set (S → Bool) := {x | e.symm (x, fun _ => false) ∈ A}
  let B' : Set ((Sᶜ : Set V) → Bool) := {x | e.symm (fun _ => false, x) ∈ B}
  have ha (x : V → Bool) : x ∈ A ↔ (fun v : S => x v) ∈ A' := by
    apply hA
    intro v hv
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hv]
  have hb (x : V → Bool) : x ∈ B ↔ (fun v : (Sᶜ : Set V) => x v) ∈ B' := by
    apply hB
    intro v hv
    simp only [Set.mem_compl_iff] at hv
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hv]
  have hab : A ∩ B = {x | (fun v : S => x v) ∈ A' ∧
        (fun v : (Sᶜ : Set V) => x v) ∈ B'} := by
    ext x
    exact and_congr (ha x) (hb x)
  have hae : A = {x | (fun v : S => x v) ∈ A' ∧
        (fun v : (Sᶜ : Set V) => x v) ∈ (Set.univ : Set ((Sᶜ : Set V) → Bool))} := by
    ext x
    simpa using ha x
  have hbe : B = {x | (fun v : S => x v) ∈ (Set.univ : Set (S → Bool)) ∧
        (fun v : (Sᶜ : Set V) => x v) ∈ B'} := by
    ext x
    simpa using hb x
  rw [hab, prob_split, hae, hbe, prob_split, prob_split, prob_univ, prob_univ,
    mul_one, one_mul]

omit [Fintype V] in
theorem occurs_upper (H : Finset V) : IsUpperSet (occurs H) := by
  intro x y hxy hx v hv
  have h := hxy v
  rw [hx v hv] at h
  exact top_le_iff.mp h

omit [Fintype V] in
theorem occurs_supported (H : Finset V) : Supported (H : Set V) (occurs H) := by
  intro x y hxy
  constructor <;> intro h v hv
  · rw [← hxy v hv]
    exact h v hv
  · rw [hxy v hv]
    exact h v hv

omit [Fintype V] in
theorem avoids_lower {ι : Type u_5} (H : ι → Finset V) (s : Finset ι) :
    IsLowerSet (avoids H s) := by
  intro x y hxy hy i hi hx
  exact hy i hi (occurs_upper (H i) hxy hx)

omit [Fintype V] in
theorem avoids_supported_compl {ι : Type u_6} (H : ι → Finset V) (s : Finset ι)
    (K : Finset V) (hs : ∀ i ∈ s, Disjoint K (H i)) :
    Supported (K : Set V)ᶜ (avoids H s) := by
  have he (x y : V → Bool) (hxy : ∀ v ∈ (K : Set V)ᶜ, x v = y v)
      (i : ι) (hi : i ∈ s) : x ∈ occurs (H i) ↔ y ∈ occurs (H i) := by
    apply occurs_supported
    intro v hv
    apply hxy
    exact fun hvK => Finset.disjoint_left.mp (hs i hi) hvK hv
  intro x y hxy
  simp only [avoids, Set.mem_ofPred_eq]
  exact forall_congr' fun i => forall_congr' fun hi => not_congr (he x y hxy i hi)

theorem prob_remove_le {ι : Type u_8} (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) (E : Set (V → Bool)) :
    prob p E - ∑ i ∈ s, prob p (E ∩ occurs (H i)) ≤ prob p (E ∩ avoids H s) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, avoids_insert, ← Set.inter_assoc, prob_inter_compl]
    have hsub : (E ∩ avoids H s) ∩ occurs (H i) ⊆ E ∩ occurs (H i) := by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
    have := prob_mono hp hsub
    linarith

theorem avoidance_step {ι : Type u_9} (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) (a : ι) :
    prob p (avoids H (insert a s)) ≤ prob p (avoids H s) *
      Real.exp (-prob p (occurs (H a)) +
        ∑ i ∈ s.filter (fun i => ¬ Disjoint (H a) (H i)),
          prob p (occurs (H a) ∩ occurs (H i))) := by
  let near := s.filter (fun i => ¬ Disjoint (H a) (H i))
  let far := s.filter (fun i => Disjoint (H a) (H i))
  let F := avoids H far
  let B := occurs (H a)
  let A := avoids H s
  let c := prob p B - ∑ i ∈ near, prob p (B ∩ occurs (H i))
  have hsplit : A = F ∩ avoids H near := by
    ext x
    simp only [A, F, far, near, avoids, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Finset.mem_filter]
    constructor
    · intro h; exact ⟨fun i hi => h i hi.1, fun i hi => h i hi.1⟩
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hd : Disjoint (H a) (H i)
      · exact h₁ i ⟨hi, hd⟩
      · exact h₂ i ⟨hi, hd⟩
  have hsub : A ⊆ F := by rw [hsplit]; exact Set.inter_subset_left
  have hF : IsLowerSet F := avoids_lower H far
  have hB : IsUpperSet B := occurs_upper (H a)
  have hind : prob p (B ∩ F) = prob p B * prob p F := by
    apply prob_independent p (H a : Set V) (occurs_supported (H a))
    apply avoids_supported_compl H far (H a)
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsum : (∑ i ∈ near, prob p ((B ∩ F) ∩ occurs (H i))) ≤
      (∑ i ∈ near, prob p (B ∩ occurs (H i))) * prob p F := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have h := harris_opposite hp (hB.inter (occurs_upper (H i))) hF
    have he : (B ∩ F) ∩ occurs (H i) = (B ∩ occurs (H i)) ∩ F := by
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rwa [he]
  have hlower : c * prob p F ≤ prob p (B ∩ A) := by
    have h := prob_remove_le hp H near (B ∩ F)
    rw [Set.inter_assoc, ← hsplit] at h
    rw [hind] at h
    dsimp [c]
    nlinarith
  have hstep : c * prob p A ≤ prob p (B ∩ A) := by
    by_cases hc : 0 ≤ c
    · exact (mul_le_mul_of_nonneg_left (prob_mono hp hsub) hc).trans hlower
    · have hc' : c ≤ 0 := le_of_not_ge hc
      exact (mul_nonpos_of_nonpos_of_nonneg hc' (prob_nonneg hp A)).trans
        (prob_nonneg hp (B ∩ A))
  have hraw : prob p (avoids H (insert a s)) ≤ prob p A * (1 - c) := by
    rw [avoids_insert, prob_inter_compl]
    change prob p A - prob p (A ∩ B) ≤ prob p A * (1 - c)
    rw [Set.inter_comm A B]
    nlinarith
  have hexp : 1 - c ≤ Real.exp (-c) := by
    have := Real.add_one_le_exp (-c)
    linarith
  apply (hraw.trans (mul_le_mul_of_nonneg_left hexp (prob_nonneg hp A))).trans_eq
  dsimp [A, c, B, near]
  rw [neg_sub, sub_eq_neg_add]

variable {ι : Type u_10}

theorem offCost_symm (p : V → ℝ) (H : ι → Finset V) (i j : ι) :
    offCost p H i j = offCost p H j i := by
  simp only [offCost, eq_comm, disjoint_comm, Set.inter_comm]

theorem offSum_insert (p : V → ℝ) (H : ι → Finset V) (s : Finset ι)
    (a : ι) (ha : a ∉ s) :
    offSum p H (insert a s) = offSum p H s +
      2 * ∑ i ∈ s.filter (fun i => ¬ Disjoint (H a) (H i)),
        prob p (occurs (H a) ∩ occurs (H i)) := by
  have hsum : (∑ i ∈ s, offCost p H a i) =
      ∑ i ∈ s.filter (fun i => ¬ Disjoint (H a) (H i)),
        prob p (occurs (H a) ∩ occurs (H i)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := fun h => ha (h ▸ hi)
    by_cases hd : Disjoint (H a) (H i) <;> simp [offCost, hai, hd]
  simp only [offSum, Finset.sum_insert ha, offCost_self, zero_add,
    Finset.sum_add_distrib]
  rw [show (∑ i ∈ s, offCost p H i a) = ∑ i ∈ s, offCost p H a i by
    apply Finset.sum_congr rfl
    intro i _
    exact offCost_symm p H i a]
  rw [hsum]
  ring

theorem janson_first (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) :
    prob p (avoids H s) ≤ Real.exp (-mean p H s + offSum p H s / 2) := by
  induction s using Finset.induction_on with
  | empty => simp [mean, offSum]
  | @insert a s ha ih =>
    apply (avoidance_step hp H s a).trans
    apply (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, mean_insert p H s a ha, offSum_insert p H s a ha]
    congr 1
    ring

theorem prob_occurs (p : V → ℝ) (H : Finset V) :
    prob p (occurs H) = ∏ v ∈ H, p v := by
  let f (v : V) (b : Bool) : ℝ :=
    if v ∈ H then (if b then p v else 0) else (if b then p v else 1 - p v)
  have he : prob p (occurs H) = ∑ x : V → Bool, ∏ v, f v (x v) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ occurs H
    · rw [ite_eq_left hx]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ H
      · simp [f, hv, hx v hv]
      · simp [f, hv]
    · rw [ite_eq_right hx]
      symm
      apply Finset.prod_eq_zero_iff.mpr
      have hex : ∃ v ∈ H, x v ≠ true := by
        by_contra hn
        apply hx
        intro v hv
        by_contra hxv
        exact hn ⟨v, hv, hxv⟩
      obtain ⟨v, hv, hxv⟩ := hex
      exact ⟨v, Finset.mem_univ v, by simp [f, hv, hxv]⟩
  rw [he, ← Fintype.prod_sum]
  calc
    _ = ∏ v : V, if v ∈ H then p v else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ H <;> simp [f, hv]
    _ = _ := by simp

variable {W : Type u_11} [Fintype W]

theorem atom_sum (p : V → ℝ) (q : W → ℝ) (x : V ⊕ W → Bool) :
    atom (Sum.elim p q) x = atom p (x ∘ Sum.inl) * atom q (x ∘ Sum.inr) := by
  exact Fintype.prod_sum_type _

theorem prob_sum (p : V → ℝ) (q : W → ℝ)
    (A : Set (V → Bool)) (B : Set (W → Bool)) :
    prob (Sum.elim p q) {x | x ∘ Sum.inl ∈ A ∧ x ∘ Sum.inr ∈ B} =
      prob p A * prob q B := by
  let : DecidableEq (V ⊕ W) := fun _ _ => Classical.propDecidable _
  calc
    _ = ∑ z : (V → Bool) × (W → Bool),
        (if z.1 ∈ A then atom p z.1 else 0) *
        (if z.2 ∈ B then atom q z.2 else 0) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow V W Bool)
      intro x
      simp only [Set.mem_ofPred_eq]
      by_cases ha : x ∘ Sum.inl ∈ A <;> by_cases hb : x ∘ Sum.inr ∈ B <;>
        simp [Equiv.sumArrowEquivProdArrow, ha, hb, atom_sum]
    _ = _ := by
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, prob]

omit [Fintype V] in
theorem avoidance_gated_subset (H : ι → Finset V) (s : Finset ι) :
    {x : V ⊕ ι → Bool | x ∘ Sum.inl ∈ avoids H s} ⊆ avoids (gated H) s := by
  intro x hx i hi h
  exact hx i hi ((occurs_gated H i x).mp h).1

theorem prob_avoidance_le_gated [Fintype ι]
    (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (H : ι → Finset V) (s : Finset ι)
    {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    prob p (avoids H s) ≤ prob (Sum.elim p (fun _ : ι => q)) (avoids (gated H) s) := by
  have he : {x : V ⊕ ι → Bool | x ∘ Sum.inl ∈ avoids H s} =
      {x | x ∘ Sum.inl ∈ avoids H s ∧ x ∘ Sum.inr ∈ (Set.univ : Set (ι → Bool))} := by
    ext x; simp
  have hh : prob (Sum.elim p (fun _ : ι => q))
      {x | x ∘ Sum.inl ∈ avoids H s} = prob p (avoids H s) := by
    rw [he, prob_sum, prob_univ, mul_one]
  rw [← hh]
  apply prob_mono _ (avoidance_gated_subset H s)
  intro v
  cases v with
  | inl v => exact hp v
  | inr i => exact hq

theorem prob_gated [Fintype ι] (p : V → ℝ) (q : ℝ) (H : ι → Finset V) (i : ι) :
    prob (Sum.elim p (fun _ : ι => q)) (occurs (gated H i)) = q * prob p (occurs (H i)) := by
  rw [prob_occurs, gated, Finset.prod_union]
  · simp [Finset.prod_map, prob_occurs, mul_comm]
  · simp

theorem prob_gated_pair [Fintype ι] (p : V → ℝ) (q : ℝ) (H : ι → Finset V)
    (i j : ι) (hij : i ≠ j) :
    prob (Sum.elim p (fun _ : ι => q)) (occurs (gated H i) ∩ occurs (gated H j)) =
      q ^ 2 * prob p (occurs (H i) ∩ occurs (H j)) := by
  have he : occurs (gated H i) ∩ occurs (gated H j) =
      {x | x ∘ Sum.inl ∈ occurs (H i) ∩ occurs (H j) ∧
        x ∘ Sum.inr ∈ occurs ({i, j} : Finset ι)} := by
    ext x
    simp only [Set.mem_inter_iff, occurs_gated, Set.mem_ofPred_eq]
    simp only [occurs, Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Function.comp_apply]
    tauto
  rw [he, prob_sum, prob_occurs]
  simp [hij, pow_two, mul_assoc, mul_comm]

omit [Fintype V] in
theorem disjoint_gated (H : ι → Finset V) (i j : ι) (hij : i ≠ j) :
    Disjoint (gated H i) (gated H j) ↔ Disjoint (H i) (H j) := by
  simp [gated, Finset.disjoint_map, Ne.symm hij]

theorem mean_gated [Fintype ι] (p : V → ℝ) (q : ℝ)
    (H : ι → Finset V) (s : Finset ι) :
    mean (Sum.elim p (fun _ : ι => q)) (gated H) s = q * mean p H s := by
  simp only [mean, prob_gated, Finset.mul_sum]

theorem offSum_gated [Fintype ι] (p : V → ℝ) (q : ℝ)
    (H : ι → Finset V) (s : Finset ι) :
    offSum (Sum.elim p (fun _ : ι => q)) (gated H) s = q ^ 2 * offSum p H s := by
  simp only [offSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j; simp
  · simp only [offCost, hij, false_or, disjoint_gated H i j hij]
    split_ifs
    · simp
    · exact prob_gated_pair p q H i j hij

theorem janson_thinned [Fintype ι] (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    prob p (avoids H s) ≤ Real.exp (-q * mean p H s + q ^ 2 * offSum p H s / 2) := by
  apply (prob_avoidance_le_gated hp H s hq).trans
  have hpar : ∀ v, 0 ≤ (Sum.elim p (fun _ : ι => q)) v ∧
      (Sum.elim p (fun _ : ι => q)) v ≤ 1 := by
    intro v
    cases v with
    | inl v => exact hp v
    | inr i => exact hq
  simpa only [mean_gated, offSum_gated, neg_mul] using janson_first hpar (gated H) s

theorem depSum_eq (p : V → ℝ) (H : ι → Finset V) (s : Finset ι)
    (hH : ∀ i ∈ s, (H i).Nonempty) : depSum p H s = mean p H s + offSum p H s := by
  simp only [depSum, mean, offSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hdiag : ¬ Disjoint (H i) (H i) := by
    obtain ⟨v, hv⟩ := hH i hi
    exact fun h => Finset.disjoint_left.mp h hv hv
  have hs : (∑ j ∈ s, if j = i then prob p (occurs (H i)) else 0) =
      prob p (occurs (H i)) := by simp [hi]
  rw [← hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp only [ite_eq_right hdiag, Set.inter_self, offCost, true_or,
      ↓reduceIte, add_zero]
  · simp [offCost, hij, Ne.symm hij]

theorem offSum_nonneg (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (H : ι → Finset V) (s : Finset ι) :
    0 ≤ offSum p H s := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  simp only [offCost]
  split_ifs
  · rfl
  · exact prob_nonneg hp _

theorem janson [Fintype ι] (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) (hH : ∀ i ∈ s, (H i).Nonempty)
    (hm : 0 < mean p H s) :
    mean p H s ≤ depSum p H s ∧
    prob p (avoids H s) ≤ Real.exp (-(mean p H s)^2 / (2 * depSum p H s)) := by
  have he := depSum_eq p H s hH
  have ho := offSum_nonneg hp H s
  have hmd : mean p H s ≤ depSum p H s := by linarith
  have hd : 0 < depSum p H s := hm.trans_le hmd
  refine ⟨hmd, ?_⟩
  let q := mean p H s / depSum p H s
  have hq : 0 ≤ q ∧ q ≤ 1 :=
    ⟨(div_pos hm hd).le, (div_le_one hd).mpr hmd⟩
  apply (janson_thinned hp H s hq).trans
  apply Real.exp_le_exp.mpr
  have hod : offSum p H s ≤ depSum p H s := by linarith
  calc
    -q * mean p H s + q ^ 2 * offSum p H s / 2 ≤
        -q * mean p H s + q ^ 2 * depSum p H s / 2 := by
      gcongr
    _ = -(mean p H s)^2 / (2 * depSum p H s) := by
      dsimp [q]
      field_simp
      ring

end FiniteJanson

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_JansonSampling
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set

universe u_1 u_2 u_3

namespace FiniteJanson

variable {Ω : Type u_1} {V : Type u_2} [MeasurableSpace Ω] [Fintype V]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : V → Ω → Bool}

omit [Fintype V] in
theorem successProb_mem (v : V) :
    0 ≤ successProb P X v ∧ successProb P X v ≤ 1 :=
  ⟨measureReal_nonneg, by
    exact (measureReal_mono (μ := P) (subset_univ _)).trans_eq probReal_univ⟩

theorem joint_atom (hX : ∀ v, Measurable (X v)) (hind : iIndepFun X P)
    (x : V → Bool) :
    P.real {ω | (fun v => X v ω) = x} = atom (successProb P X) x := by
  have he : {ω | (fun v => X v ω) = x} =
      ⋂ v ∈ (Finset.univ : Finset V), X v ⁻¹' {x v} := by
    ext ω
    simp [funext_iff]
  rw [he, measureReal_def, hind.measure_inter_preimage_eq_mul _
    (fun v _ => measurableSet_singleton (x v)), ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro v _
  change P.real (X v ⁻¹' {x v}) = if x v then successProb P X v else 1 - successProb P X v
  cases hx : x v
  · have hc : X v ⁻¹' {false} = {ω | X v ω = true}ᶜ := by
      ext ω
      cases X v ω <;> simp
    rw [hc]
    exact probReal_compl_eq_one_sub ((hX v) (measurableSet_singleton true))
  · rfl

theorem joint_event (hX : ∀ v, Measurable (X v)) (hind : iIndepFun X P)
    (A : Set (V → Bool)) :
    P.real {ω | (fun v => X v ω) ∈ A} = prob (successProb P X) A := by
  classical
  let J : Ω → (V → Bool) := fun ω v => X v ω
  have hJ : Measurable J := Measurable.of_eval hX
  change P.real (J ⁻¹' A) = _
  calc
    P.real (J ⁻¹' A) =
        ∑ x ∈ Finset.univ.filter (fun x => x ∈ A), P.real (J ⁻¹' {x}) := by
      rw [sum_measureReal_preimage_singleton _ (fun x _ =>
        hJ (measurableSet_singleton x))]
      simp
    _ = prob (successProb P X) A := by
      rw [Finset.sum_filter]
      unfold prob
      apply Finset.sum_congr rfl
      intro x _
      split_ifs
      · exact joint_atom hX hind x
      · rfl

theorem janson_of_iIndepFun {ι : Type u_3} [Fintype ι]
    (hX : ∀ v, Measurable (X v)) (hind : iIndepFun X P)
    (H : ι → Finset V) (s : Finset ι) (hH : ∀ i ∈ s, (H i).Nonempty)
    (hm : 0 < mean (successProb P X) H s) :
    mean (successProb P X) H s ≤ depSum (successProb P X) H s ∧
    P.real {ω | ∀ i ∈ s, ¬ ∀ v ∈ H i, X v ω = true} ≤
      Real.exp (-(mean (successProb P X) H s)^2 /
        (2 * depSum (successProb P X) H s)) := by
  have hj := janson (fun v => successProb_mem (P := P) (X := X) v) H s hH hm
  refine ⟨hj.1, ?_⟩
  have he := joint_event hX hind (avoids H s)
  change P.real {ω | (fun v => X v ω) ∈ avoids H s} ≤ _
  rw [he]
  exact hj.2

end FiniteJanson

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonFinite
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace PoissonFinite
open Set MeasureTheory ProbabilityTheory PoissonConfig PoissonMeasureCells CellMatching PoissonDiagrams
open scoped Classical BigOperators
variable {Ω : Type u_1} {A : Type u_2} {C : Type u_3} [MeasurableSpace Ω] [Fintype A] [Fintype C]
variable {I : A → Type u_4} [∀ a, Fintype (I a)]

lemma assignment_mean (P : Partition Ω C) (E : ∀ a, I a → Set Ω) (p : C → ℝ) :
    FiniteJanson.mean p assignmentSupport (validAssignments P E) =
      ∑ a, CellCounts.injectiveSum (CellCounts.slotWeight (fun i c => P.cell c ⊆ E a i) p) := by
  rw [FiniteJanson.mean, validAssignments, Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [CellCounts.injectiveSum_slot_eq]
  apply Finset.sum_congr rfl
  intro f _
  dsimp only [valid]
  rw [FiniteJanson.prob_occurs]
  congr 1
  exact Finset.prod_image f.injective.injOn

lemma assignment_depSum (P : Partition Ω C) (E : ∀ a, I a → Set Ω) (p : C → ℝ) :
    FiniteJanson.depSum p assignmentSupport (validAssignments P E) =
      ∑ a, ∑ b, ∑ fg : (I a ↪ C) × (I b ↪ C),
        if (support fg.1 ∩ support fg.2).Nonempty then
          pairWeight (fun i c => P.cell c ⊆ E a i) (fun j c => P.cell c ⊆ E b j) p fg else 0 := by
  have he : FiniteJanson.depSum p assignmentSupport (validAssignments P E) =
      ∑ f : Assignment I C, ∑ g : Assignment I C,
        if valid P E f ∧ valid P E g then
          if (support f.2 ∩ support g.2).Nonempty then jointWeight p f.2 g.2 else 0 else 0 := by
    rw [FiniteJanson.depSum, validAssignments, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : valid P E f
    · rw [ite_eq_left hf, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : valid P E g
      · simp only [hg, hf, and_self, ite_true]
        rw [← FiniteJanson.occurs_union, FiniteJanson.prob_occurs]
        change (if Disjoint (support f.2) (support g.2) then 0 else jointWeight p f.2 g.2) = _
        by_cases hd : Disjoint (support f.2) (support g.2)
        · have hn : ¬ (support f.2 ∩ support g.2).Nonempty := by
            rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
            exact Finset.not_nonempty_empty
          rw [ite_eq_left hd, ite_eq_right hn]
        · have hn : (support f.2 ∩ support g.2).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr (fun h => hd (Finset.disjoint_iff_inter_eq_empty.mpr h))
          rw [ite_eq_right hd, ite_eq_left hn]
      · rw [ite_eq_right hg, ite_eq_right (by simp only [hg, and_false, not_false_eq_true])]
    · rw [ite_eq_right hf]
      simp only [hf, false_and, ↓reduceIte, Finset.sum_const_zero]
  rw [he, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [Fintype.sum_sigma]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  dsimp only [valid, pairWeight]
  by_cases h : (∀ i, P.cell (f i) ⊆ E a i) ∧ ∀ j, P.cell (g j) ⊆ E b j
  · simp [h]
  · simp [h]

omit [Fintype A] in

lemma witness_of_cell_occupation (P : Partition Ω C) (E : ∀ a, I a → Set Ω)
    (f : Assignment I C) (hf : valid P E f) (x : Config Ω)
    (hx : ∀ c ∈ assignmentSupport f, occupied (P.cell c) x = true) :
    0 < witnessCount (E f.1) x := by
  have hi (i : I f.1) : ∃ j : Fin x.1, x.2.val j ∈ P.cell (f.2 i) := by
    have h := hx (f.2 i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    simp only [occupied, decide_eq_true_eq, count, Finset.card_pos, Finset.filter_nonempty_iff,
      Finset.mem_univ, true_and] at h
    exact h
  choose g hg using hi
  have hginj : Function.Injective g := by
    intro i j hij
    apply f.2.injective
    by_contra hc
    exact Set.disjoint_left.mp (P.disjoint hc) (hg i) (by simpa only [hij] using hg j)
  let w : I f.1 ↪ Fin x.1 := ⟨g,hginj⟩
  apply Finset.card_pos.mpr
  refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro i
  exact hf i (hg i)

theorem finite_cell_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : Measure (Config Ω)) [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
    [∀ a, Nonempty (I a)] (cells : Partition Ω C) (E : ∀ a, I a → Set Ω)
    (hm : 0 < ∑ a, Q μ cells (E a)) :
    (∑ a, Q μ cells (E a)) ≤
      (∑ a, ∑ b, ∑ M : Matching (I a) (I b), if M.val.Nonempty then
        Q μ cells (classSet M (E a) (E b)) else 0) ∧
    P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
      (-(∑ a, Q μ cells (E a))^2 /
        (2 * (∑ a, ∑ b, ∑ M : Matching (I a) (I b), if M.val.Nonempty then
          Q μ cells (classSet M (E a) (E b)) else 0))) := by
  let p : C → ℝ := fun c => 1 - Real.exp (-μ.real (cells.cell c))
  have hp : FiniteJanson.successProb P (fun c => occupied (cells.cell c)) = p := by
    funext c
    exact occupied_prob_of_void hP (cells.measurable c)
  have hmean : FiniteJanson.mean p assignmentSupport (validAssignments cells E) =
      ∑ a, Q μ cells (E a) := assignment_mean cells E p
  have hdep : FiniteJanson.depSum p assignmentSupport (validAssignments cells E) =
      ∑ a, ∑ b, ∑ M : Matching (I a) (I b), if M.val.Nonempty then
        Q μ cells (classSet M (E a) (E b)) else 0 := by
    rw [assignment_depSum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact dependency_eq_sum_Q μ cells (E a) (E b)
  have hj := FiniteJanson.janson_of_iIndepFun
    (fun c => measurable_occupied (cells.measurable c))
    (occupied_independent_of_void hP cells.cell cells.measurable cells.disjoint)
    assignmentSupport (validAssignments cells E)
    (fun f _ => by
      obtain ⟨i⟩ := (inferInstance : Nonempty (I f.1))
      exact ⟨f.2 i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    (by rw [hp,hmean]; exact hm)
  rw [hp,hmean,hdep] at hj
  refine ⟨hj.1, (measureReal_mono (μ := P) ?_).trans hj.2⟩
  intro x hx f hf hocc
  have hvalid : valid cells E f := (Finset.mem_filter.mp hf).2
  have hpos := witness_of_cell_occupation cells E f hvalid x hocc
  rw [hx f.1] at hpos
  exact (lt_irrefl 0 hpos)

end PoissonFinite

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonCells
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2

namespace PoissonCells

variable {Ω : Type u_1} {J : Type u_2} [MeasurableSpace Ω] [Fintype J]

lemma atom_measurable (E : J → Set Ω) (hE : ∀ j, MeasurableSet (E j)) (b : J → Bool) :
    MeasurableSet (atom E b) := by
  classical
  simp only [atom, ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  cases hb : b j
  · convert! (hE j).compl using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq, decide_eq_false_iff_not, mem_compl_iff]
  · convert! hE j using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [mem_ofPred_eq, decide_eq_true_eq]

omit [MeasurableSpace Ω] [Fintype J] in
lemma atom_disjoint (E : J → Set Ω) : Pairwise (fun b c => Disjoint (atom E b) (atom E c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro x hxb hxc
  apply hbc
  funext j
  exact (hxb j).symm.trans (hxc j)

omit [MeasurableSpace Ω] [Fintype J] in
lemma atom_cover (E : J → Set Ω) : (⋃ b, atom E b) = univ := by
  classical
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨fun j => decide (x ∈ E j), fun _ => rfl⟩

omit [MeasurableSpace Ω] [Fintype J] in
lemma atom_respects (E : J → Set Ω) (b : J → Bool) (j : J) :
    atom E b ⊆ E j ∨ Disjoint (atom E b) (E j) := by
  classical
  cases hb : b j
  · right
    apply Set.disjoint_left.mpr
    intro x hx hxj
    have := hx j
    simp [hb, hxj] at this
  · left
    intro x hx
    have := hx j
    simpa [hb] using this

omit [Fintype J] in

lemma exists_small_cover [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ] {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ s : Finset (Set Ω), (∀ U ∈ s, MeasurableSet U ∧ μ U < δ) ∧
      (⋃ U ∈ s, U) = univ := by
  classical
  let := upgradeStandardBorel Ω
  obtain ⟨K, -, hK, hKμ⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := μ) (measure_ne_top μ univ) (ne_of_gt hδ)
  have hx : ∀ x : Ω, ∃ U : Set Ω, x ∈ U ∧ IsOpen U ∧ μ U < δ := by
    intro x
    obtain ⟨U, hxU, hoU, hμU⟩ := ({x} : Set Ω).exists_isOpen_lt_of_lt
      (μ := μ) δ (by simpa using hδ)
    exact ⟨U, hxU (mem_singleton x), hoU, hμU⟩
  choose U hxU hoU hμU using hx
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hoU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩)
  refine ⟨insert Kᶜ (t.image U), ?_, ?_⟩
  · intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · exact ⟨hK.isClosed.measurableSet.compl, by simpa only [Set.sdiff_eq_compl_inter, Set.inter_univ] using hKμ⟩
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hV
      exact ⟨(hoU x).measurableSet, hμU x⟩
  · apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (ht hx)
      exact mem_iUnion₂.mpr ⟨U z, Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨z, hz, rfl⟩), hxz⟩
    · exact mem_iUnion₂.mpr ⟨Kᶜ, Finset.mem_insert_self _ _, hx⟩

lemma exists_fine_partition [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ] (E : J → Set Ω)
    (hE : ∀ j, MeasurableSet (E j)) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ s : Finset (Set Ω),
      (∀ C ∈ s, MeasurableSet C ∧ μ C < δ) ∧
      (s : Set (Set Ω)).PairwiseDisjoint id ∧
      (⋃ C ∈ s, C) = univ ∧
      ∀ j C, C ∈ s → C ⊆ E j ∨ Disjoint C (E j) := by
  classical
  obtain ⟨t, ht, htcover⟩ := exists_small_cover μ hδ
  let A : J ⊕ ↥t → Set Ω := Sum.elim E (fun U => U.val)
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    rcases i with j | U
    · exact hE j
    · exact (ht U.val U.property).1
  let s := Finset.univ.image (atom A)
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    refine ⟨atom_measurable A hA b, ?_⟩
    by_cases hne : (atom A b).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have hxc : x ∈ ⋃ U ∈ t, U := by simp only [htcover, mem_univ]
      obtain ⟨U, hU, hxU⟩ := mem_iUnion₂.mp hxc
      have hs : atom A b ⊆ U := by
        intro y hy
        have hb := hx (Sum.inr ⟨U, hU⟩)
        have hyb := hy (Sum.inr ⟨U, hU⟩)
        apply of_decide_eq_true
        calc
          decide (y ∈ U) = decide (x ∈ U) := hyb.trans hb.symm
          _ = true := by simp only [hxU, decide_true]
      exact (measure_mono hs).trans_lt (ht U hU).2
    · simp only [Set.not_nonempty_iff_eq_empty] at hne
      simpa only [hne, measure_empty] using hδ
  · intro C hC D hD hCD
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hD
    exact atom_disjoint A (fun h => hCD (congrArg (atom A) h))
  · apply eq_univ_of_forall
    intro x
    obtain ⟨b, hxb⟩ := mem_iUnion.mp (show x ∈ ⋃ b, atom A b by rw [atom_cover]; trivial)
    exact mem_iUnion₂.mpr ⟨atom A b, Finset.mem_image.mpr
      ⟨b, Finset.mem_univ _, rfl⟩, hxb⟩
  · intro j C hC
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hC
    exact atom_respects A b (Sum.inl j)

end PoissonCells

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonLimit
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2 u_3

namespace PoissonLimit
open Set MeasureTheory ProbabilityTheory PoissonConfig PoissonMeasureCells CellMatching PoissonDiagrams
open scoped Classical BigOperators ENNReal
variable {Ω : Type u_1} {A : Type u_2} [MeasurableSpace Ω] [Fintype A] [Nonempty A]
variable {I : A → Type u_3} [∀ a, Fintype (I a)] [∀ a, Nonempty (I a)]

omit [Nonempty A] [∀ a, Nonempty (I a)] in
lemma exists_partition_sequence [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (E : ∀ a, I a → Set Ω) (hE : ∀ a i, MeasurableSet (E a i)) :
    ∃ s : ℕ → Finset (Set Ω), ∃ P : ∀ k, Partition Ω ↥(s k),
      (∀ k a i, Respects (P k) (E a i)) ∧
      (∀ k c, μ.real ((P k).cell c) ≤ 1 / ((k : ℝ) + 1)) := by
  have hs (k : ℕ) := PoissonCells.exists_fine_partition μ
    (fun j : Σ a, I a => E j.1 j.2) (fun j => hE j.1 j.2)
    (δ := ENNReal.ofReal (1 / ((k : ℝ) + 1))) (by positivity)
  choose s hm hd hc hr using hs
  let P (k : ℕ) : Partition Ω ↥(s k) := {
    cell := fun c => c.val
    measurable := fun c => (hm k c c.property).1
    disjoint := fun c d hcd => hd k c.property d.property (fun h => hcd (Subtype.ext h))
    cover := by
      ext x
      simpa only [mem_iUnion, Subtype.exists, exists_prop] using
        (iff_of_eq (congrArg (fun S : Set Ω => x ∈ S) (hc k))) }
  refine ⟨s,P, ?_, ?_⟩
  · intro k a i c
    exact hr k ⟨a,i⟩ c c.property
  · intro k c
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm k c c.property).2.le).trans_eq
      (ENNReal.toReal_ofReal (by positivity))

theorem lower_tail_oai [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] [NullSingletonClass μ]
    (P : Measure (Config Ω)) [IsProbabilityMeasure P] (hP : HasVoidLaw μ P)
    (E : ∀ a, I a → Set Ω) (hE : ∀ a i, MeasurableSet (E a i))
    (hpos : ∀ a i, 0 < μ.real (E a i)) :
    (0 < ∑ a, ∑ b, diagram μ (E a) (E b)) ∧
    P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp
      (-(∑ a, ∏ i, μ.real (E a i))^2 /
        (2 * (∑ a, ∑ b, diagram μ (E a) (E b)))) := by
  obtain ⟨s,cells,hr,hd⟩ := exists_partition_sequence μ E hE
  let m (k : ℕ) := ∑ a, Q μ (cells k) (E a)
  let d (k : ℕ) := ∑ a, ∑ b, ∑ M : Matching (I a) (I b),
    if M.val.Nonempty then Q μ (cells k) (classSet M (E a) (E b)) else 0
  let ν := ∑ a, ∏ i, μ.real (E a i)
  let D := ∑ a, ∑ b, diagram μ (E a) (E b)
  have hν : 0 < ν := Finset.sum_pos (fun a _ => Finset.prod_pos (fun i _ => hpos a i))
    Finset.univ_nonempty
  have hm : Filter.Tendsto m Filter.atTop (nhds ν) := by
    apply tendsto_finsetSum
    intro a _
    exact Q_tendsto μ (fun k => ↥(s k)) cells (E a) (hE a) (fun k => hr k a)
      (fun k => by positivity) hd tendsto_one_div_add_atTop_nhds_zero_nat
  have hDform : D = ∑ a, ∑ b, ∑ M : Matching (I a) (I b),
      if M.val.Nonempty then ∏ v, μ.real (classSet M (E a) (E b) v) else 0 := by
    dsimp only [D]
    simp_rw [diagram_eq_classSet_sum μ _ _ (fun i => ne_of_gt (hpos _ i))
      (fun i => ne_of_gt (hpos _ i))]
  have hdt : Filter.Tendsto d Filter.atTop (nhds D) := by
    rw [hDform]
    apply tendsto_finsetSum
    intro a _
    apply tendsto_finsetSum
    intro b _
    apply tendsto_finsetSum
    intro M _
    by_cases hM : M.val.Nonempty
    · simp only [ite_eq_left hM]
      exact Q_tendsto μ (fun k => ↥(s k)) cells (classSet M (E a) (E b))
        (classSet_measurable M (E a) (E b) (hE a) (hE b))
        (fun k => classSet_respects (cells k) M (E a) (E b) (hr k a) (hr k b))
        (fun k => by positivity) hd tendsto_one_div_add_atTop_nhds_zero_nat
    · simp only [ite_eq_right hM]
      exact tendsto_const_nhds
  have hevent : ∀ᶠ k in Filter.atTop, 0 < m k := hm.eventually (eventually_gt_nhds hν)
  have hbd : ∀ᶠ k in Filter.atTop, m k ≤ d k ∧
      P.real {x | ∀ a, witnessCount (E a) x = 0} ≤ Real.exp (-(m k)^2 / (2 * d k)) := by
    filter_upwards [hevent] with k hk
    exact PoissonFinite.finite_cell_bound μ P hP (cells k) E hk
  have hνD : ν ≤ D := le_of_tendsto_of_tendsto hm hdt (hbd.mono fun _ h => h.1)
  have hD : 0 < D := hν.trans_le hνD
  refine ⟨hD, ?_⟩
  have hexp : Filter.Tendsto (fun k => Real.exp (-(m k)^2 / (2*d k))) Filter.atTop
      (nhds (Real.exp (-ν^2/(2*D)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp
      ((hm.pow 2).neg.div (tendsto_const_nhds.mul hdt) (ne_of_gt (mul_pos (by norm_num) hD)))
  exact ge_of_tendsto hexp (hbd.mono fun _ h => h.2)

end PoissonLimit

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PoissonLimit.lower_tail_oai.{u_1, u_2, u_3} := @OAI.PoissonLimit.lower_tail_oai.{u_1, u_2, u_3}

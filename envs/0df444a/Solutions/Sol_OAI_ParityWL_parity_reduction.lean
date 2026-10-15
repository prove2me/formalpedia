-- Prove2me | solution 1 for OAI.ParityWL.parity_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:48:24.818505+00:00
-- url     : https://prove2.me/submissions/44334549-28af-4ee5-bfd5-332ec427af7b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Main.lean:L101-L110
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ParityWL.parity_reduction.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ParityWL_parity_reduction) verbatim and is proved by it.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
import Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan
import Definitions.Def_OAI_Combinatorics_ParityLifts_PureComponents
import Definitions.Def_OAI_Combinatorics_ParityLifts_Main
import Theorems.Thm_OAI_ParityWL_ReducedCutDecomposition_balancedStar
import Theorems.Thm_OAI_ParityWL_WeightedWitness_no_tags
import Theorems.Thm_OAI_ParityWL_choice_of_balancedStar
import Theorems.Thm_OAI_ParityWL_homCount_lift_strict_iff
import Theorems.Thm_OAI_ParityWL_inconsistent_weightedWitness
import Theorems.Thm_OAI_ParityWL_joint_indicator_mem
import Theorems.Thm_OAI_ParityWL_separate_indicator_mem
import Theorems.Thm_OAI_ParityWL_successful_detected
import Theorems.Thm_OAI_ParityWL_template_positive_degree

-- ---- from OAI.Combinatorics.ParityLifts.LiftCounts ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)

end Lifts

section LiftCounts

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

omit [Fintype V] in
lemma solutions_card_eq_of_nonempty (b : A → Bit)
    (h : Nonempty (Solutions T G F τ φ b)) :
    Fintype.card (Solutions T G F τ φ b) =
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) := by
  obtain ⟨v⟩ := h
  exact Fintype.card_congr (homogeneousTranslate T G F τ φ b v)

omit [Fintype V] in
lemma solutions_card_le (b : A → Bit) :
    Fintype.card (Solutions T G F τ φ b) ≤
      Fintype.card (Solutions T G F τ φ (fun _ => 0)) := by
  classical
  by_cases h : Nonempty (Solutions T G F τ φ b)
  · exact (solutions_card_eq_of_nonempty T G F τ φ b h).le
  · have : IsEmpty (Solutions T G F τ φ b) := not_nonempty_iff.mp h
    simp

lemma homCount_lift (b : A → Bit) :
    homCount F (liftGraph T G τ b) =
      ∑ φ : F →g G, Fintype.card (Solutions T G F τ φ b) := by
  classical
  unfold homCount
  rw [Fintype.card_congr (homSolutionsEquiv T G F τ b), Fintype.card_sigma]

/-- Noncancellation for every uncolored homomorphism, not just typed witnesses. -/
theorem homCount_lift_le (b : A → Bit) :
    homCount F (liftGraph T G τ b) ≤ homCount F (liftGraph T G τ (fun _ => 0)) := by
  classical
  rw [homCount_lift T G F τ b, homCount_lift T G F τ (fun _ => 0)]
  exact Finset.sum_le_sum (fun φ _ => solutions_card_le T G F τ φ b)

end LiftCounts

section BinaryDuality

variable {E H : Type} [AddCommGroup E] [Module Bit E] [AddCommGroup H] [Module Bit H]

end BinaryDuality

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.DecompositionCuts ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section DecompositionCuts

open scoped Classical

variable {W : Type} [Fintype W]

variable {F : SimpleGraph W} {t : ℕ}

variable {a : F →g template t}

/-- The helper boundary argument in reduced decomposition-cut form. -/
theorem choice_of_reducedCutDecomposition {C : ChoiceSystem t}
    (φ : F →g baseGraph C)
    (w : WeightedWitness (template t) F ((baseProjection C).comp φ) (starParity t))
    (D : ReducedCutDecomposition F t) (ht : 0 < t) : C.Successful := by
  obtain ⟨s⟩ := D.balancedStar w ht
  exact choice_of_balancedStar C φ w s ht

end DecompositionCuts

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.Witnesses ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section WitnessConverse

open scoped Classical

variable {A W : Type} [Fintype A] [Fintype W]
variable {T : SimpleGraph A} {F : SimpleGraph W} {a : F →g T} {b : A → Bit}

variable {V : Type} [Fintype V] {G : SimpleGraph V} {τ : G →g T} {φ : F →g G}

omit [Fintype V] in
theorem weightedWitness_inconsistent
    (w : WeightedWitness T F (τ.comp φ) b) :
    ¬ Nonempty (Solutions T G F τ φ b) := by
  rintro ⟨z⟩
  exact w.no_tags z.1 z.2.1 z.2.2

theorem homCount_lift_strict_iff_witness :
    homCount F (liftGraph T G τ b) < homCount F (liftGraph T G τ (fun _ => 0)) ↔
      ∃ φ : F →g G, Nonempty (WeightedWitness T F (τ.comp φ) b) := by
  rw [homCount_lift_strict_iff]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, inconsistent_weightedWitness T G F τ φ b hφ⟩
  · rintro ⟨φ, ⟨w⟩⟩
    exact ⟨φ, weightedWitness_inconsistent w⟩

end WitnessConverse

section PositiveWitness

open scoped Classical

variable {t : ℕ} {C : ChoiceSystem t}

end PositiveWitness

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.TagSizes ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section TagSizes

open scoped Classical

variable {I : Type} [Fintype I]

lemma card_tag {A : Type} [Fintype A] (T : SimpleGraph A) (b : A → Bit)
    (a : A) (h : (T.neighborSet a).Nonempty) :
    Fintype.card (Tag T b a) = 2 ^ (Fintype.card (T.neighborSet a) - 1) := by
  classical
  obtain ⟨i, hi⟩ := h
  exact Fintype.card_congr (sumFiberEquiv (⟨i, hi⟩ : T.neighborSet a) (b a)) |>.trans (by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_subtype_eq])

lemma lift_card_eq {A V : Type} [Fintype A] [Fintype V]
    (T : SimpleGraph A) (G : SimpleGraph V) (τ : G →g T) (b c : A → Bit)
    (h : ∀ a, (T.neighborSet a).Nonempty) :
    Fintype.card (LiftVertex T G τ b) = Fintype.card (LiftVertex T G τ c) := by
  simp only [LiftVertex, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro u _
  rw [card_tag T b (τ u) (h _), card_tag T c (τ u) (h _)]

lemma choice_lifts_equal_order {t : ℕ} (ht : 2 ≤ t) (C : ChoiceSystem t) :
    Fintype.card (LiftVertex (template t) (baseGraph C) (baseProjection C) (fun _ => 0)) =
      Fintype.card (LiftVertex (template t) (baseGraph C) (baseProjection C) (starParity t)) :=
  lift_card_eq _ _ _ _ _ (template_positive_degree ht)

lemma card_mainPair (t : ℕ) : Fintype.card (MainPair t) = t.choose 2 := by
  rw [Fintype.card_congr (mainPairEquiv t), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun n => n), Finset.sum_range_id, Nat.choose_two_right]

lemma card_avoid_two {J : Type} [Fintype J] [DecidableEq J] (a b : J) (hab : a ≠ b) :
    Fintype.card {i : J // i ≠ a ∧ i ≠ b} = Fintype.card J - 2 := by
  have he : Fintype.card {i : J // i = a ∨ i = b} = 2 := by
    have h := Fintype.card_coe ({a, b} : Finset J)
    simpa [hab] using h
  have h := Fintype.card_subtype_compl (fun i : J => i = a ∨ i = b)
  simpa only [not_or, he] using h

lemma card_helper (t : ℕ) : Fintype.card (Helper t) = 3 * t.choose 3 := by
  rw [Fintype.card_congr (helperSigmaEquiv t), Fintype.card_sigma]
  have h : ∀ p : MainPair t,
      Fintype.card {i : Fin t // i ≠ p.1.1 ∧ i ≠ p.1.2} = t - 2 := by
    intro p
    simpa using card_avoid_two p.1.1 p.1.2 (ne_of_lt p.2)
  simp_rw [h]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_mainPair]
  simpa only [Nat.mul_comm] using (Nat.choose_succ_right_eq t 2).symm

lemma card_orderedPair {J : Type} [Fintype J] [LinearOrder J] :
    Fintype.card (OrderedPair J) = (Fintype.card J).choose 2 := by
  rw [Fintype.card_congr orderedPairEquiv, card_mainPair]

lemma pairOther_injective {t : ℕ} (i : Fin t) : Function.Injective (pairOther i) := by
  intro p q hpq
  have he := congrArg Subtype.val hpq
  dsimp only [pairOther] at he
  apply Subtype.ext
  apply Subtype.ext
  by_cases hp : i = p.1.1.1 <;> by_cases hq : i = q.1.1.1
  · simp only [dite_eq_left hp, dite_eq_left hq] at he
    exact Prod.ext (hp.symm.trans hq) he
  · simp only [dite_eq_left hp, dite_eq_right hq] at he
    have hq' : i = q.1.1.2 := q.2.resolve_left hq
    have hlt := p.1.2
    have hlt' := q.1.2
    rw [← hp, he] at hlt
    rw [← hq'] at hlt'
    exact (lt_asymm hlt hlt').elim
  · simp only [dite_eq_right hp, dite_eq_left hq] at he
    have hp' : i = p.1.1.2 := p.2.resolve_left hp
    have hlt := p.1.2
    have hlt' := q.1.2
    rw [← hp'] at hlt
    rw [← hq, ← he] at hlt'
    exact (lt_asymm hlt hlt').elim
  · simp only [dite_eq_right hp, dite_eq_right hq] at he
    exact Prod.ext he ((p.2.resolve_left hp).symm.trans (q.2.resolve_left hq))

lemma card_pairsThrough_le {t : ℕ} (i : Fin t) :
    Fintype.card (PairsThrough i) ≤ t - 1 := by
  have h := Fintype.card_le_of_injective _ (pairOther_injective i)
  simpa [Fintype.card_subtype_compl] using h

lemma card_helpersIncident_le {t : ℕ} (i : Fin t) :
    Fintype.card {h : Helper t // helperIncident h i} ≤ 3 * (t - 1).choose 2 := by
  have he : Fintype.card {h : Helper t // i = h.1.1.1.1 ∨ i = h.1.1.1.2} ≤
      (t - 1) * (t - 2) := by
    rw [Fintype.card_congr (helperEndpointEquiv i), Fintype.card_sigma]
    have hc : ∀ p : PairsThrough i,
        Fintype.card {j : Fin t // j ≠ p.1.1.1 ∧ j ≠ p.1.1.2} = t - 2 :=
      fun p => by simpa using card_avoid_two p.1.1.1 p.1.1.2 (ne_of_lt p.1.2)
    simp_rw [hc]
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      Nat.mul_le_mul_right (t - 2) (card_pairsThrough_le i)
  have ht : Fintype.card {h : Helper t // i = h.1.2} = (t - 1).choose 2 := by
    rw [Fintype.card_congr (helperThirdEquiv i), card_orderedPair]
    simp [Fintype.card_subtype_compl]
  have h := Fintype.card_subtype_or
    (fun h : Helper t => i = h.1.1.1.1 ∨ i = h.1.1.1.2)
    (fun h : Helper t => i = h.1.2)
  have h' : Fintype.card {h : Helper t // helperIncident h i} ≤
      (t - 1) * (t - 2) + (t - 1).choose 2 := by
    have h0 : Fintype.card {h : Helper t // helperIncident h i} ≤
        Fintype.card {h : Helper t // i = h.1.1.1.1 ∨ i = h.1.1.1.2} +
          Fintype.card {h : Helper t // i = h.1.2} := by
      have hc := Fintype.card_congr (Equiv.subtypeEquivRight (fun h : Helper t =>
        show helperIncident h i ↔ (i = h.1.1.1.1 ∨ i = h.1.1.1.2) ∨ i = h.1.2
          from or_assoc.symm))
      exact hc.le.trans h
    exact h0.trans (Nat.add_le_add he ht.le)
  have hc := Nat.choose_succ_right_eq (t - 1) 1
  simp only [Nat.choose_one_right, Nat.sub_sub, Nat.reduceAdd] at hc
  omega

lemma template_degree_main_le {t : ℕ} (i : Fin t) :
    Fintype.card ((template t).neighborSet (.inl i)) ≤
      t - 1 + 3 * (t - 1).choose 2 := by
  rw [Fintype.card_congr (templateMainNeighbors i), Fintype.card_sum]
  have h : Fintype.card {j : Fin t // j ≠ i} = t - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [h]
  exact Nat.add_le_add_left (card_helpersIncident_le i) _

lemma template_degree_helper {t : ℕ} (h : Helper t) :
    Fintype.card ((template t).neighborSet (.inr h)) = 3 := by
  let s : Finset (TemplateVertex t) :=
    {.inl h.1.1.1.1, .inl h.1.1.1.2, .inl h.1.2}
  have hs : ∀ v, v ∈ s ↔ v ∈ (template t).neighborSet (.inr h) := by
    intro v
    cases v <;> simp [s, template, templateAdj, helperIncident]
  rw [Fintype.card_of_finset' s hs]
  simp [s, ne_of_lt h.1.1.2, h.2.1.symm, h.2.2.symm]

lemma tag_main_bound {t : ℕ} (ht : 2 ≤ t) (b : TemplateVertex t → Bit)
    (i : Fin t) :
    Fintype.card (Tag (template t) b (.inl i)) ≤
      2 ^ (t - 2 + 3 * (t - 1).choose 2) := by
  rw [card_tag _ _ _ (template_positive_degree ht _)]
  apply Nat.pow_le_pow_right (by omega)
  have h := template_degree_main_le i
  omega

lemma tag_helper_card {t : ℕ} (ht : 2 ≤ t) (b : TemplateVertex t → Bit)
    (h : Helper t) : Fintype.card (Tag (template t) b (.inr h)) = 4 := by
  rw [card_tag _ _ _ (template_positive_degree ht _), template_degree_helper]
  norm_num

lemma choice_lift_order_bound {t : ℕ} (ht : 2 ≤ t) (C : ChoiceSystem t)
    (A : ℕ) (hA : C.SizeAtMost A) (b : TemplateVertex t → Bit) :
    Fintype.card (LiftVertex (template t) (baseGraph C) (baseProjection C) b) ≤
      A * orderFactor t := by
  let q := 2 ^ (t - 2 + 3 * (t - 1).choose 2)
  rw [Fintype.card_sigma]
  change (∑ u : BaseVertex C, Fintype.card (Tag (template t) b (baseType u))) ≤ _
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  change (∑ i : Fin t, ∑ _d : C.Domain i, Fintype.card (Tag (template t) b (.inl i))) +
    (∑ h : Helper t, ∑ _c : C.Label h.1.1, Fintype.card (Tag (template t) b (.inr h))) ≤ _
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc
    _ ≤ (∑ _i : Fin t, A * q) + (∑ _h : Helper t, A * 4) := by
      apply Nat.add_le_add
      · apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul (hA.1 i) (tag_main_bound ht b i)
      · apply Finset.sum_le_sum
        intro h _
        rw [tag_helper_card ht]
        exact Nat.mul_le_mul_right 4 (hA.2 h.1.1)
    _ = A * orderFactor t := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin, card_helper]
      dsimp only [q, orderFactor]
      ring

end TagSizes

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.Detection ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section Detection

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

lemma homCount_card_equiv {U X : Type} [Fintype U] [Fintype X]
    (F : SimpleGraph U) (e : (F →g G) ≃ X) : homCount F G = Fintype.card X := by
  classical
  exact Fintype.card_congr e

end Detection

theorem equivalent_no_choice (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k))
    (h : WLEquivalent (zeroLift C) (starLift C) c k) : ¬ C.Successful := by
  intro hs
  exact (successful_detected k hk c C hs).1 (h (detectionRound c))

theorem pure_equivalent_no_choice (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k))
    (h : PureWLEquivalent (zeroLift C) (starLift C) c k) : ¬ C.Successful := by
  intro hs
  exact (successful_detected k hk c C hs).2 (h (detectionRound c))

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.RankedTrees ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section RankedTrees

open scoped Classical

namespace RankedTree

variable {N : Type} (D : RankedTree N)

variable [Fintype N]

end RankedTree

namespace RankedBagTree

variable {W N : Type} [Fintype W] [Fintype N] {F : SimpleGraph W} {t : ℕ}

end RankedBagTree

/-- Equality for every genuinely decomposed uncolored source. -/
theorem no_choice_equal_decomposed {W N : Type} [Fintype W] [Fintype N]
    {t : ℕ} (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful)
    (F : SimpleGraph W) (D : RankedBagTree (N := N) F.Adj t) :
    homCount F (zeroLift C) = homCount F (starLift C) := by
  apply le_antisymm
  · by_contra h
    have hlt : homCount F (starLift C) < homCount F (zeroLift C) := by omega
    obtain ⟨φ, ⟨w⟩⟩ := homCount_lift_strict_iff_witness.mp hlt
    exact hn (choice_of_reducedCutDecomposition φ w D.toIndexed.toReducedCuts ht)
  · exact homCount_lift_le _ _ _ _ _

end RankedTrees

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.RootedTests ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section RootedTests

open scoped Classical

attribute [instance] RootedTest.vertexFintype RootedTest.nodeFintype

lemma RootedTest.sum_count {k t : ℕ} (F : RootedTest k t)
    {V : Type} [Fintype V] (G : SimpleGraph V) :
    ∑ x : Fin k → V, F.count G x = (Fintype.card (RelationMaps F.relation G) : ℚ) := by
  unfold count
  rw [← Nat.cast_sum, ← Fintype.card_sigma, Fintype.card_congr (F.totalEquiv G)]

lemma relationMaps_loop {A V : Type} [Fintype A] [Fintype V]
    (R : A → A → Prop) (G : SimpleGraph V) {a : A} (ha : R a a) :
    Fintype.card (RelationMaps R G) = 0 := by
  have : IsEmpty (RelationMaps R G) := ⟨fun f => (f.2 a a ha).ne rfl⟩
  exact Fintype.card_eq_zero

lemma no_choice_equal_relation {W N : Type} [Fintype W] [Fintype N]
    {t : ℕ} (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful)
    (R : W → W → Prop) (hs : Std.Symm R) (D : RankedBagTree (N := N) R t) :
    Fintype.card (RelationMaps R (zeroLift C)) = Fintype.card (RelationMaps R (starLift C)) := by
  by_cases hloop : ∃ x, R x x
  · obtain ⟨x, hx⟩ := hloop
    rw [relationMaps_loop R _ hx, relationMaps_loop R _ hx]
  · let F : SimpleGraph W := ⟨R, hs, ⟨fun x hx => hloop ⟨x, hx⟩⟩⟩
    have hz : Fintype.card (RelationMaps R (zeroLift C)) = homCount F (zeroLift C) :=
      (homCount_card_equiv (zeroLift C) F (relationMapsSimpleEquiv F (zeroLift C)).symm).symm
    have ho : Fintype.card (RelationMaps R (starLift C)) = homCount F (starLift C) :=
      (homCount_card_equiv (starLift C) F (relationMapsSimpleEquiv F (starLift C)).symm).symm
    rw [hz, ho]
    exact no_choice_equal_decomposed C ht hn F D

lemma no_choice_equal_rooted_total {k t : ℕ} (F : RootedTest k t)
    (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful) :
    ∑ x, F.count (zeroLift C) x = ∑ x, F.count (starLift C) x := by
  rw [F.sum_count, F.sum_count,
    no_choice_equal_relation C ht hn F.relation F.symmetric F.tree]

end RootedTests

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section FiniteInterpolation

open scoped Classical

lemma count_map_as_sum {X D : Type} [Fintype X] [DecidableEq D] (c : X → D) (d : D) :
    (Multiset.count d (Finset.univ.val.map c) : ℚ) =
      ∑ x : X, if c x = d then (1 : ℚ) else 0 := by
  rw [Multiset.count_map, Finset.sum_boole]
  congr 1
  exact congrArg Multiset.card (by
    apply Multiset.filter_congr
    intro x _
    exact eq_comm)

end FiniteInterpolation

section RefinementOperators

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

end RefinementOperators

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.ColorSpan ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section ColorSpan

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

end ColorSpan

section SpanHistograms

open scoped Classical

variable {V W X Y D : Type} [Fintype V] [Fintype W] [Fintype X] [Fintype Y]
variable (G : SimpleGraph V) (H : SimpleGraph W) {k t : ℕ}
variable (l : X → TuplePair V W k) (r : Y → TuplePair V W k)

lemma sum_eq_of_mem_testSpan
    (hF : ∀ F : RootedTest k t, ∑ x, testEval G H F (l x) = ∑ y, testEval G H F (r y))
    {f : TuplePair V W k → ℚ} (hf : f ∈ testSpan G H k t) :
    ∑ x, f (l x) = ∑ y, f (r y) := by
  refine Submodule.span_induction (p := fun f _ => ∑ x, f (l x) = ∑ y, f (r y))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨F, rfl⟩
    exact hF F
  · simp only [Pi.zero_apply, Finset.sum_const_zero]
  · intro f g _ _ ihf ihg
    simp only [Pi.add_apply, Finset.sum_add_distrib, ihf, ihg]
  · intro a f _ ih
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ih]

lemma histograms_eq_of_tests [DecidableEq D] (c : TuplePair V W k → D)
    (hc : ∀ d, (fun x => if c x = d then (1 : ℚ) else 0) ∈ testSpan G H k t)
    (hF : ∀ F : RootedTest k t, ∑ x, testEval G H F (l x) = ∑ y, testEval G H F (r y)) :
    Finset.univ.val.map (c ∘ l) = Finset.univ.val.map (c ∘ r) := by
  apply Multiset.ext.mpr
  intro d
  have he := sum_eq_of_mem_testSpan G H l r hF (hc d)
  apply Nat.cast_injective (R := ℚ)
  rw [count_map_as_sum, count_map_as_sum]
  exact he

end SpanHistograms

theorem no_choice_equivalent (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k)) (hn : ¬ C.Successful) :
    WLEquivalent (zeroLift C) (starLift C) c k := by
  classical
  intro r
  cases c with
  | joint =>
    exact histograms_eq_of_tests (zeroLift C) (starLift C) Sum.inl Sum.inr
      (pairJoint (zeroLift C) (starLift C) k r)
      (joint_indicator_mem _ _ (t := k+1) le_rfl r)
      (fun F => no_choice_equal_rooted_total F C (by omega) hn)
  | separate =>
    exact histograms_eq_of_tests (zeroLift C) (starLift C) Sum.inl Sum.inr
      (pairSeparate (zeroLift C) (starLift C) k r)
      (separate_indicator_mem _ _ (t := k) le_rfl r)
      (fun F => no_choice_equal_rooted_total F C (by omega) hn)

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.PureComponents ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section InducedBagTree

open scoped Classical

variable {A N : Type} {R : A → A → Prop} {t : ℕ}

end InducedBagTree

section PureComponents

open scoped Classical

variable {k t : ℕ} (F : RootedTest k t)
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)

lemma pureLeft_card [Fintype V] [Fintype W] :
    Fintype.card (PureLeftMaps F G H) =
      ∑ s : ComponentMask F,
        Fintype.card (RelationMaps (fun a b : MaskLeft F s => F.relation a.1 b.1) G) *
        Fintype.card (RelationMaps (fun a b : MaskRight F s => F.relation a.1 b.1) H) := by
  rw [← Fintype.card_congr (componentEquiv F G H), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact Fintype.card_prod _ _

end PureComponents

end ParityWL

end OAI

-- ---- from OAI.Combinatorics.ParityLifts.Main ----
namespace OAI

namespace ParityWL

open scoped BigOperators

section PureTotals

open scoped Classical

variable {k t : ℕ} (F : RootedTest k t)
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)

lemma sum_pureLeft_count [Fintype V] [Fintype W] :
    ∑ x : Fin k → V, F.count (G.sum H) (Sum.inl ∘ x) =
      (Fintype.card (PureLeftMaps F G H) : ℚ) := by
  unfold RootedTest.count
  rw [← Nat.cast_sum, ← Fintype.card_sigma, Fintype.card_congr (pureLeftTotalEquiv F G H)]

lemma count_pureRight_swap [Fintype V] [Fintype W] (x : Fin k → W) :
    F.count (G.sum H) (Sum.inr ∘ x) = F.count (H.sum G) (Sum.inl ∘ x) := by
  have he := Fintype.card_congr (rootedMapsIso F (G.sum H)
    (SimpleGraph.Iso.sumComm : G.sum H ≃g H.sum G) (Sum.inr ∘ x))
  exact congrArg (fun n : ℕ => (n : ℚ)) he

lemma sum_pureRight_count [Fintype V] [Fintype W] :
    ∑ x : Fin k → W, F.count (G.sum H) (Sum.inr ∘ x) =
      (Fintype.card (PureLeftMaps F H G) : ℚ) := by
  simp only [count_pureRight_swap, sum_pureLeft_count]

lemma no_choice_equal_pure_total (C : ChoiceSystem t) (ht : 0 < t) (hn : ¬ C.Successful) :
    ∑ x, F.count ((zeroLift C).sum (starLift C)) (Sum.inl ∘ x) =
      ∑ x, F.count ((zeroLift C).sum (starLift C)) (Sum.inr ∘ x) := by
  rw [sum_pureLeft_count, sum_pureRight_count, pureLeft_card, pureLeft_card]
  apply congrArg (fun n : ℕ => (n : ℚ))
  apply Finset.sum_congr rfl
  intro s _
  have hl := no_choice_equal_relation C ht hn
    (fun a b : MaskLeft F s => F.relation a.1 b.1)
    ⟨fun a b h => F.symmetric.symm a.1 b.1 h⟩ (F.tree.induce (fun a => s.1 a = true))
  have hr := no_choice_equal_relation C ht hn
    (fun a b : MaskRight F s => F.relation a.1 b.1)
    ⟨fun a b h => F.symmetric.symm a.1 b.1 h⟩ (F.tree.induce (fun a => s.1 a = false))
  rw [hl, hr]

end PureTotals

theorem no_choice_pure_equivalent (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k)) (hn : ¬ C.Successful) :
    PureWLEquivalent (zeroLift C) (starLift C) c k := by
  classical
  intro r
  let U := (zeroLift C).sum (starLift C)
  cases c with
  | joint =>
    exact histograms_eq_of_tests U U
      (fun x => Sum.inl (Sum.inl ∘ x)) (fun x => Sum.inr (Sum.inr ∘ x))
      (pairJoint U U k r) (joint_indicator_mem _ _ (t := k+1) le_rfl r)
      (fun F => no_choice_equal_pure_total F C (by omega) hn)
  | separate =>
    exact histograms_eq_of_tests U U
      (fun x => Sum.inl (Sum.inl ∘ x)) (fun x => Sum.inr (Sum.inr ∘ x))
      (pairSeparate U U k r) (separate_indicator_mem _ _ (t := k) le_rfl r)
      (fun F => no_choice_equal_pure_total F C (by omega) hn)

/-- The parity reduction on the explicitly constructed
uncolored simple lifts, including empty choice domains. -/
theorem parity_reduction : ParityReductionStatement := by
  intro k hk c C
  have ht : 2 ≤ bagParameter c k := by cases c <;> simp only [bagParameter] <;> omega
  refine ⟨choice_lifts_equal_order ht C, ?_, ?_, ?_, successful_detected k hk c C⟩
  · intro A _ hA
    exact choice_lift_order_bound ht C A hA (fun _ => 0)
  · exact ⟨equivalent_no_choice k hk c C, no_choice_equivalent k hk c C⟩
  · exact ⟨pure_equivalent_no_choice k hk c C, no_choice_pure_equivalent k hk c C⟩

end ParityWL

end OAI

-- ---- mission target ----
open OAI OAI.ParityWL
open scoped BigOperators

theorem solution : ParityReductionStatement := by
  first
    | exact OAI.ParityWL.parity_reduction
    | (apply OAI.ParityWL.parity_reduction <;> assumption)
    | (intros; apply OAI.ParityWL.parity_reduction <;> assumption)

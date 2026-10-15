-- Prove2me | solution 1 for OAI.Paper320.recursive_joint_one_at
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:25:33.027162+00:00
-- url     : https://prove2.me/submissions/16f88b49-a7f7-4ae4-b991-ce77b96b8fa9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveOne.lean:L72-L135
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.recursive_joint_one_at. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveProfiles ----
namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem NestedFamily.rejects_of_le {h : ℕ} {I : Type}
    {F : Fin h → (I → Bool) → Bool} (hF : NestedFamily F)
    {q q' : Fin h} {x} (hqq : q ≤ q') (hx : F q x = false) :
    F q' x = false := by
  cases h' : F q' x
  · rfl
  · have := hF.accepts_of_le hqq h'
    simp [hx] at this

theorem sensitivityAt_le_sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q : Fin h) (x : I → Bool)
    (hx : F q x = b) : sensitivityAt (F q) x ≤ sideSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hx]

theorem jointSensitivityAt_le_jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) (q q' : Fin h) (x : I → Bool)
    (hqq : q < q') (hx : F q x = b) (hx' : F q' x = b) :
    jointSensitivityAt (F q) (F q') x ≤ jointSensitivity F b := by
  apply Finset.le_sup_of_le (Finset.mem_univ q)
  apply Finset.le_sup_of_le (Finset.mem_univ q')
  apply Finset.le_sup_of_le (Finset.mem_univ x)
  simp [hqq, hx, hx']

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Finite Boolean flips and the exact maximum/witness interfaces for sensitivity. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I J K : Type}

theorem flip_prod_same (x : J × I → Bool) (j : J) (i : I) :
    (fun a => flip x {(j, i)} (j, a)) = flip (fun a => x (j, a)) {i} := by
  funext a
  simp [flip]

theorem flip_prod_other (x : J × I → Bool) {j k : J} (i : I) (hk : k ≠ j) :
    (fun a => flip x {(j, i)} (k, a)) = fun a => x (k, a) := by
  funext a
  simp [flip, hk]

section Finite

variable [Fintype I]

end Finite
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.Tournament ----
namespace OAI

/-! Finite tournaments and the target-constant labeling condition. -/

noncomputable section
open scoped Classical

namespace Paper320

namespace Tournament
variable {k : ℕ} (T : Tournament k)

theorem ne_of_adj {i j : Fin k} (h : T.Adj i j) : i ≠ j := by
  rintro rfl
  exact T.loopless i h

end Tournament

namespace GoodLabeling
variable {k r : ℕ} {T : Tournament k} (A : GoodLabeling T r)

end GoodLabeling
end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveDefinitions ----
namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem gateIndex_antitone {h : ℕ} {q q' : Fin h} (hqq : q ≤ q') :
    gateIndex q' ≤ gateIndex q := by
  exact Fin.rev_le_rev.mpr hqq

theorem gateIndex_strictAnti {h : ℕ} {q q' : Fin h} (hqq : q < q') :
    gateIndex q' < gateIndex q := by
  exact Fin.rev_lt_rev.mpr hqq

theorem rowClause_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    rowClause T label F q x i = true ↔
      (∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
      ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false := by
  simp only [rowClause, decide_eq_true_eq]

theorem recursiveFamily_eq_true_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = true ↔ ∃ i, rowClause T label F q x i = true := by
  simp only [recursiveFamily, decide_eq_true_eq]

theorem recursiveFamily_eq_false_iff {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) :
    recursiveFamily T label F q x = false ↔ ∀ i, rowClause T label F q x i = false := by
  simp [recursiveFamily]

theorem rowClause_nested {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (hF : NestedFamily F) {q q' : Fin h} (hqq : q ≤ q')
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : rowClause T label F q' x i = true) : rowClause T label F q x i = true := by
  rw [rowClause_eq_true_iff] at hi ⊢
  refine ⟨hi.1, fun j hij => ?_⟩
  exact hF.rejects_of_le (gateIndex_antitone hqq) (hi.2 j hij)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveFlips ----
namespace OAI

/-! A raw bit belongs to one child and changes at most one condition of a clause. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursiveChild_flip_same {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) (a : I) :
    recursiveChild (flip x {((j, c), a)}) j c = flip (recursiveChild x j c) {a} :=
  flip_prod_same x (j, c) a

theorem recursiveChild_flip_other {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j j' : Fin k) (c c' : Fin r) (a : I)
    (h : (j', c') ≠ (j, c)) :
    recursiveChild (flip x {((j, c), a)}) j' c' = recursiveChild x j' c' :=
  flip_prod_other x a h

theorem rowClause_eq_of_conditions {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x y : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (ht : ∀ c, F (Fin.last h) (recursiveChild x i c) =
      F (Fin.last h) (recursiveChild y i c))
    (hg : ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) =
      F (gateIndex q) (recursiveChild y j (label i j))) :
    rowClause T label F q x i = rowClause T label F q y i := by
  apply Bool.eq_iff_iff.mpr
  rw [rowClause_eq_true_iff, rowClause_eq_true_iff]
  constructor
  · rintro ⟨hxt, hxg⟩
    exact ⟨fun c => (ht c).symm.trans (hxt c),
      fun j hij => (hg j hij).symm.trans (hxg j hij)⟩
  · rintro ⟨hyt, hyg⟩
    exact ⟨fun c => (ht c).trans (hyt c),
      fun j hij => (hg j hij).trans (hyg j hij)⟩

theorem rowClause_flip_eq {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (ht : j = i → F (Fin.last h) (flip (recursiveChild x j c) {a}) =
      F (Fin.last h) (recursiveChild x j c))
    (hg : T.Adj i j → c = label i j →
      F (gateIndex q) (flip (recursiveChild x j c) {a}) =
        F (gateIndex q) (recursiveChild x j c)) :
    rowClause T label F q (flip x {((j, c), a)}) i = rowClause T label F q x i := by
  apply rowClause_eq_of_conditions
  · intro c'
    by_cases heq : (i, c') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact ht rfl
    · rw [recursiveChild_flip_other x j i c c' a heq]
  · intro j' hij'
    by_cases heq : (j', label i j') = (j, c)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [recursiveChild_flip_same]
      exact hg hij' rfl
    · rw [recursiveChild_flip_other x j j' c (label i j') a heq]

theorem rowClause_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c)) := by
  by_contra hn
  apply hc
  apply rowClause_flip_eq
  · intro hji
    by_contra hne
    exact hn (Or.inl ⟨hji, hne⟩)
  · intro hij hcl
    by_contra hne
    exact hn (Or.inr ⟨hij, hcl, hne⟩)

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveSets ----
namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem card_biUnion_le_mul {J I : Type} [DecidableEq I] (A : Finset J) (B : J → Finset I) (n : ℕ)
    (hn : ∀ j ∈ A, (B j).card ≤ n) : (A.biUnion B).card ≤ A.card * n := by
  calc
    (A.biUnion B).card ≤ ∑ j ∈ A, (B j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ A, n := Finset.sum_le_sum hn
    _ = A.card * n := by simp

theorem rowClause_joint_flip_change {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q q' : Fin h) (x : ((Fin k × Fin r) × I) → Bool)
    (i j : Fin k) (c : Fin r) (a : I)
    (hc : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i)
    (hc' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i) :
    (j = i ∧ F (Fin.last h) (flip (recursiveChild x j c) {a}) ≠
      F (Fin.last h) (recursiveChild x j c)) ∨
    (T.Adj i j ∧ c = label i j ∧
      F (gateIndex q) (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q) (recursiveChild x j c) ∧
      F (gateIndex q') (flip (recursiveChild x j c) {a}) ≠
        F (gateIndex q') (recursiveChild x j c)) := by
  rcases rowClause_flip_change T label F q x i j c a hc with ht | ⟨hij, hcl, hq⟩
  · exact Or.inl ht
  · rcases rowClause_flip_change T label F q' x i j c a hc' with ht | hg
    · exact False.elim ((T.ne_of_adj hij) ht.1.symm)
    · exact Or.inr ⟨hij, hcl, hq, hg.2.2⟩

end Paper320

end

end OAI

-- ---- from OAI.Combinatorics.Sensitivity.RecursiveOne ----
namespace OAI

/-! The two recurrences for inputs at which the parent predicates accept. -/

noncomputable section
open scoped Classical

namespace Paper320

theorem recursive_joint_one_at {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  obtain ⟨i, hi'⟩ := (recursiveFamily_eq_true_iff T label F q' x).mp hx'
  have hi := rowClause_nested T label F hF hqq.le x i hi'
  have hcond := (rowClause_eq_true_iff T label F q x i).mp hi
  have hcond' := (rowClause_eq_true_iff T label F q' x i).mp hi'
  let U := Finset.univ.biUnion fun c => childChanges F (Fin.last h) x i c
  let V := (Finset.univ.filter (T.Adj i)).biUnion fun j =>
    childJointChanges F (gateIndex q') (gateIndex q) x j (label i j)
  have hsub : (Finset.univ.filter fun p =>
      recursiveFamily T label F q (flip x {p}) ≠ recursiveFamily T label F q x ∧
      recursiveFamily T label F q' (flip x {p}) ≠ recursiveFamily T label F q' x) ⊆ U ∪ V := by
    rintro ⟨⟨j, c⟩, a⟩ hp
    have hchange := (Finset.mem_filter.mp hp).2
    have hf : recursiveFamily T label F q (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.1 (hy.trans hx.symm))
    have hf' : recursiveFamily T label F q' (flip x {((j, c), a)}) = false := by
      cases hy : recursiveFamily T label F q' (flip x {((j, c), a)})
      · rfl
      · exact False.elim (hchange.2 (hy.trans hx'.symm))
    have hif := (recursiveFamily_eq_false_iff T label F q _).mp hf i
    have hif' := (recursiveFamily_eq_false_iff T label F q' _).mp hf' i
    have hic : rowClause T label F q (flip x {((j, c), a)}) i ≠ rowClause T label F q x i := by
      simp [hi, hif]
    have hic' : rowClause T label F q' (flip x {((j, c), a)}) i ≠ rowClause T label F q' x i := by
      simp [hi', hif']
    rcases rowClause_joint_flip_change T label F q q' x i j c a hic hic' with
      ⟨rfl, ht⟩ | ⟨hij, rfl, hg, hg'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      exact ⟨c, Finset.mem_univ _, by simpa [childChanges] using ht⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩,
        by simpa [childJointChanges] using And.intro hg' hg⟩
  have hU : U.card ≤ r * sideSensitivity F true := by
    simpa [U] using card_biUnion_le_mul Finset.univ
      (fun c => childChanges F (Fin.last h) x i c) (sideSensitivity F true)
      (fun c _ => by
        rw [childChanges_card]
        exact sensitivityAt_le_sideSensitivity F true _ _ (hcond.1 c))
  have hV : V.card ≤ o * jointSensitivity F false := by
    simpa only [V, ho i] using card_biUnion_le_mul (Finset.univ.filter (T.Adj i))
      (fun j => childJointChanges F (gateIndex q') (gateIndex q) x j (label i j))
      (jointSensitivity F false) (fun j hj => by
        have hij := (Finset.mem_filter.mp hj).2
        rw [childJointChanges_card]
        exact jointSensitivityAt_le_jointSensitivity F false _ _ _
          (gateIndex_strictAnti hqq) (hcond'.2 j hij) (hcond.2 j hij))
  calc
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
        (U ∪ V).card := Finset.card_le_card hsub
    _ ≤ U.card + V.card := Finset.card_union_le _ _
    _ ≤ r * sideSensitivity F true + o * jointSensitivity F false := Nat.add_le_add hU hV
    _ = _ := Nat.add_comm _ _

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical

theorem solution {k r h : ℕ} {I : Type} [Fintype I]
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin (h + 1) → (I → Bool) → Bool) (hF : NestedFamily F) (o : ℕ)
    (ho : ∀ i, (Finset.univ.filter (T.Adj i)).card = o)
    (q q' : Fin h) (hqq : q < q') (x : ((Fin k × Fin r) × I) → Bool)
    (hx : recursiveFamily T label F q x = true)
    (hx' : recursiveFamily T label F q' x = true) :
    jointSensitivityAt (recursiveFamily T label F q) (recursiveFamily T label F q') x ≤
      o * jointSensitivity F false + r * sideSensitivity F true := by
  first
    | exact OAI.Paper320.recursive_joint_one_at T label F hF o ho q q' hqq x hx hx'
    | exact OAI.Paper320.recursive_joint_one_at
    | (apply OAI.Paper320.recursive_joint_one_at <;> assumption)
    | (intros; apply OAI.Paper320.recursive_joint_one_at <;> assumption)

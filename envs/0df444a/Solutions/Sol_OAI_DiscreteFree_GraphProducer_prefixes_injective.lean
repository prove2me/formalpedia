-- Prove2me | solution 1 for OAI.DiscreteFree.GraphProducer.prefixes_injective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:50:10.941711+00:00
-- url     : https://prove2.me/submissions/21a0ab83-68ea-4829-adac-ceee5a5d2157

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/FiniteQuotients.lean:L130-L147
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.GraphProducer.prefixes_injective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients

-- ---- from OAI.Analysis.LipschitzFree.FiniteQuotients ----
namespace OAI

/-!
# Finite permutation representations of balls in free groups
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.GraphProducer

variable (A : Type*) [Finite A] [DecidableEq A]

theorem ballPerm_apply (N : ℕ) (a : A) (g : WordBall A N)
    (h : FreeGroup.norm (FreeGroup.of a * g.val) ≤ N) :
    (ballPerm A N a g).val = FreeGroup.of a * g.val :=
  (exists_ball_perm A N a).choose_spec g h

theorem ballPerm_inv_apply (N : ℕ) (a : A) (g : WordBall A N)
    (h : FreeGroup.norm ((FreeGroup.of a)⁻¹ * g.val) ≤ N) :
    ((ballPerm A N a)⁻¹ g).val = (FreeGroup.of a)⁻¹ * g.val := by
  let y : WordBall A N := ⟨(FreeGroup.of a)⁻¹ * g.val, h⟩
  have hy : FreeGroup.norm (FreeGroup.of a * y.val) ≤ N := by
    simpa [y] using g.property
  have heq : ballPerm A N a y = g := by
    apply Subtype.ext
    simpa [y] using ballPerm_apply A N a y hy
  have hh : (ballPerm A N a)⁻¹ g = y := (ballPerm A N a).symm_apply_eq.mpr heq.symm
  exact congrArg Subtype.val hh

omit [Finite A] [DecidableEq A] in
lemma mk_cons_letter (a : A) (b : Bool) (l : List (A × Bool)) :
    FreeGroup.mk ((a,b) :: l) =
      (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹) * FreeGroup.mk l := by
  cases b <;> rfl

theorem ballRep_word (N : ℕ) (l : List (A × Bool)) (hl : l.length ≤ N) :
    (ballRep A N (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    obtain ⟨a, b⟩ := c
    have hlt : l.length ≤ N := by simpa using (Nat.le_of_succ_le hl)
    have hv := ih hlt
    have hm : FreeGroup.norm (FreeGroup.mk ((a,b)::l)) ≤ N :=
      FreeGroup.norm_mk_le.trans hl
    rw [mk_cons_letter] at hm ⊢
    rw [map_mul]
    change ((ballRep A N (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹))
      (ballRep A N (FreeGroup.mk l) (ballOne A N))).val = _
    change (ballRep A N (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l at hv
    change (FreeGroup.lift (ballPerm A N) (FreeGroup.mk l) (ballOne A N)).val = FreeGroup.mk l at hv
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, map_inv, ballRep,
        FreeGroup.lift_apply_of]
      rw [ballPerm_inv_apply]
      · rw [hv]
      · rw [hv]
        exact hm
    · simp only [↓reduceIte, ballRep, FreeGroup.lift_apply_of]
      rw [ballPerm_apply]
      · rw [hv]
      · rw [hv]
        exact hm

theorem ballRep_apply_one (N : ℕ) (g : FreeGroup A) (hg : FreeGroup.norm g ≤ N) :
    (ballRep A N g (ballOne A N)).val = g := by
  simpa only [FreeGroup.mk_toWord] using ballRep_word A N g.toWord hg

theorem ballRep_injective_on (N : ℕ) :
    Set.InjOn (ballRep A N) {g | FreeGroup.norm g ≤ N} := by
  intro g hg h hh heq
  have := congrArg (fun σ : Equiv.Perm (WordBall A N) => (σ (ballOne A N)).val) heq
  simpa [ballRep_apply_one A N g hg, ballRep_apply_one A N h hh] using this

theorem prefixes_injective (N : ℕ) (l : List (A × Bool))
    (hl : FreeGroup.IsReduced l) (hlen : l.length ≤ N)
    (x : Equiv.Perm (WordBall A N)) :
    Function.Injective (fun i : Fin (l.length + 1) =>
      x * ballRep A N (FreeGroup.mk (l.take i.val))) := by
  intro i j hij
  have ht (t : ℕ) : FreeGroup.norm (FreeGroup.mk (l.take t)) ≤ N :=
    FreeGroup.norm_mk_le.trans (by
      rw [List.length_take]
      exact (min_le_right _ _).trans hlen)
  have heq := ballRep_injective_on A N (ht i.val) (ht j.val) (mul_left_cancel hij)
  have hi : FreeGroup.IsReduced (l.take i.val) := hl.take _
  have hj : FreeGroup.IsReduced (l.take j.val) := hl.take _
  have he := congrArg (fun g : FreeGroup A => g.toWord.length) heq
  simp only [FreeGroup.toWord_mk, hi.reduce_eq, hj.reduce_eq, List.length_take] at he
  apply Fin.ext
  simpa [Nat.min_eq_left (Nat.le_of_lt_succ i.isLt),
    Nat.min_eq_left (Nat.le_of_lt_succ j.isLt)] using he

end DiscreteFree.GraphProducer

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.GraphProducer
open scoped BigOperators ENNReal


theorem solution : type_of% @_root_.OAI.DiscreteFree.GraphProducer.prefixes_injective := @_root_.OAI.DiscreteFree.GraphProducer.prefixes_injective

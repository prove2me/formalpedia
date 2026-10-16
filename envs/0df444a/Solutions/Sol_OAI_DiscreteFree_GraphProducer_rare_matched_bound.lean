-- Prove2me | solution 1 for OAI.DiscreteFree.GraphProducer.rare_matched_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:53:53.637853+00:00
-- url     : https://prove2.me/submissions/de2ee4e3-5a08-4c4c-8175-1bbef3bc1164

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/GraphColoring.lean:L20-L75
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.GraphProducer.rare_matched_bound. The node keeps its source
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
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Theorems.Thm_OAI_DiscreteFree_ColorCounting_colored_roots_bound
import Theorems.Thm_OAI_DiscreteFree_GraphProducer_prefixes_injective
import Theorems.Thm_OAI_DiscreteFree_PortGraph_Matched_exists_based

-- ---- from OAI.Analysis.LipschitzFree.StatePaths ----
namespace OAI

/-!
# Counting finite-state paths with bounded transitions
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section

namespace DiscreteFree.StatePaths
open scoped BigOperators Classical

universe u
variable {S : Type u} (r : S → S → Prop)

theorem card_based_le [Fintype S] (Q : ℕ)
    (hQ : ∀ j, Fintype.card {k : S // r j k} ≤ Q) (j : S) (n : ℕ) :
    Fintype.card (Based r j n) ≤ Q ^ n := by
  induction n generalizing j with
  | zero =>
    change Fintype.card PUnit ≤ 1
    exact Fintype.card_unique.le
  | succ n ih =>
    change Fintype.card (Σ k : {k : S // r j k}, Based r k.val n) ≤ _
    rw [Fintype.card_sigma]
    calc
      (∑ k : {k : S // r j k}, Fintype.card (Based r k.val n)) ≤
          ∑ _k : {k : S // r j k}, Q ^ n := Finset.sum_le_sum (fun k _ => ih k.val)
      _ = Fintype.card {k : S // r j k} * Q ^ n := by simp
      _ ≤ Q * Q ^ n := Nat.mul_le_mul_right _ (hQ j)
      _ = Q ^ (n+1) := (pow_succ' _ _).symm

theorem card_path_le [Fintype S] (Q : ℕ)
    (hQ : ∀ j, Fintype.card {k : S // r j k} ≤ Q) (n : ℕ) :
    Fintype.card (Path r n) ≤ Fintype.card S * Q ^ n := by
  change Fintype.card (Σ j : S, Based r j n) ≤ _
  rw [Fintype.card_sigma]
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (fun j _ => card_based_le r Q hQ j n)

end DiscreteFree.StatePaths

end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.FiniteQuotients ----
namespace OAI

/-!
# Finite permutation representations of balls in free groups
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.GraphProducer

variable (A : Type*) [Finite A] [DecidableEq A]

omit [Finite A] [DecidableEq A] in
lemma mk_cons_letter (a : A) (b : Bool) (l : List (A × Bool)) :
    FreeGroup.mk ((a,b) :: l) =
      (if b then FreeGroup.of a else (FreeGroup.of a)⁻¹) * FreeGroup.mk l := by
  cases b <;> rfl

end DiscreteFree.GraphProducer

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.GraphGirth ----
namespace OAI

/-!
# Cayley graphs with injective bounded reduced walks
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Finite A] [DecidableEq A]

theorem cayley_walk (N : ℕ) (x : Cayley A N) (w : List (A × Bool)) :
    (cayleyGraph A N).walk x w = x * ballRep A N (FreeGroup.mk w) := by
  induction w generalizing x with
  | nil =>
    change x = x * ballRep A N 1
    rw [map_one, mul_one]
  | cons e w ih =>
    rcases e with ⟨a,b⟩
    rw [PortGraph.walk_cons, ih, mk_cons_letter, map_mul, ← mul_assoc]
    rfl

theorem cayley_reduced (N : ℕ) (w : List (A × Bool)) :
    (cayleyGraph A N).Reduced w ↔ FreeGroup.IsReduced w := by
  have he : (fun e f : A × Bool => f ≠ invertPort A e) =
      (fun e f : A × Bool => e.1 = f.1 → e.2 = f.2) := by
    funext e f
    apply propext
    rcases e with ⟨a,b⟩
    rcases f with ⟨c,d⟩
    cases b <;> cases d <;> simp [invertPort, eq_comm]
  change w.IsChain (fun e f => f ≠ invertPort A e) ↔ _
  rw [he]
  rfl

theorem cayley_prefix_injective (N : ℕ) (x : Cayley A N) (w : List (A × Bool))
    (hw : (cayleyGraph A N).Reduced w) (hN : w.length ≤ N) :
    Function.Injective (fun i : Fin (w.length+1) => (cayleyGraph A N).walk x (w.take i.val)) := by
  simp only [cayley_walk]
  exact prefixes_injective A N w ((cayley_reduced A N w).mp hw) hN x

theorem allColorings_walk (C : Type*) (N : ℕ)
    (x : (Cayley A N → C) × Cayley A N) (w : List (A × Bool)) :
    (allColoringsGraph A C N).walk x w = (x.1, (cayleyGraph A N).walk x.2 w) := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih => exact ih _

end DiscreteFree.GraphProducer
end

end

end OAI

-- ---- from OAI.Analysis.LipschitzFree.GraphColoring ----
namespace OAI

/-!
# Rare matched walks and the fixed all-colorings graph sequence
-/

noncomputable section
open scoped BigOperators ENNReal

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A : Type*) [Fintype A] [DecidableEq A]
    (C S : Type*) [Fintype C] [Fintype S]

theorem rare_matched_bound (n N Q H : ℕ) (hnN : n ≤ N)
    (compatible : ((Cayley A N → C) × Cayley A N) → S → Prop)
    (trans : S → S → Prop) (P : S → Finset C)
    (hP : ∀ j, (P j).card ≤ H)
    (hcolor : ∀ z j, compatible z j → z.1 z.2 ∈ P j)
    (hQ : ∀ j, Fintype.card {k : S // trans j k} ≤ Q) :
    Nat.card {z : (Cayley A N → C) × Cayley A N //
        ¬ (allColoringsGraph A C N).Good compatible trans n z} * Nat.card C ^ (n+1) ≤
      Nat.card (A × Bool) ^ n * (Nat.card S * Q ^ n) * H ^ (n+1) *
        Nat.card ((Cayley A N → C) × Cayley A N) := by
  let W := {w : Words (A × Bool) n // (cayleyGraph A N).Reduced w.val}
  let f : Cayley A N → W → Fin (n+1) → Cayley A N :=
    fun x w i => (cayleyGraph A N).walk x (w.val.val.take i.val)
  have hf : ∀ x w, Function.Injective (f x w) := by
    intro x w i j h
    have hi : i.val < w.val.val.length+1 := by rw [w.val.property]; exact i.isLt
    have hj : j.val < w.val.val.length+1 := by rw [w.val.property]; exact j.isLt
    have hw : w.val.val.length ≤ N := by rw [w.val.property]; exact hnN
    have hh := cayley_prefix_injective A N x w.val.val w.property hw
      (show (cayleyGraph A N).walk x (w.val.val.take (⟨i.val, hi⟩ : Fin (w.val.val.length+1)).val) =
        (cayleyGraph A N).walk x (w.val.val.take (⟨j.val, hj⟩ : Fin (w.val.val.length+1)).val) from h)
    exact Fin.ext (congrArg (fun t : Fin (w.val.val.length+1) => t.val) hh)
  let PC : StatePaths.Path trans n → Fin (n+1) → Finset C :=
    fun p i => P (StatePaths.Path.vertex trans p i)
  let B := {z : (Cayley A N → C) × Cayley A N //
    ¬ (allColoringsGraph A C N).Good compatible trans n z}
  let E := {z : (Cayley A N → C) × Cayley A N //
    ∃ w p, ∀ i, z.1 (f z.2 w i) ∈ PC p i}
  have hBE : Nat.card B ≤ Nat.card E := by
    let emb : B → E := fun z => ⟨z.val, by
      have hz := z.property
      simp only [PortGraph.Good, not_forall, not_not] at hz
      obtain ⟨j, w, hw, hr, hm⟩ := hz
      obtain ⟨p, hp⟩ := PortGraph.Matched.exists_based (allColoringsGraph A C N)
        compatible trans hm
      subst n
      refine ⟨⟨⟨w, rfl⟩, hr⟩, ⟨j, p⟩, fun i => ?_⟩
      have hpi := hp i
      rw [allColorings_walk] at hpi
      exact hcolor _ _ hpi⟩
    exact Nat.card_le_card_of_injective emb (by
      intro x y h
      exact Subtype.ext (congrArg (fun z : E => z.val) h))
  have hcount := ColorCounting.colored_roots_bound f hf PC H (fun p i => hP (StatePaths.Path.vertex trans p i))
  simp only [← Nat.card_eq_fintype_card, Nat.card_fin] at hcount
  have hW : Nat.card W ≤ Nat.card (A × Bool) ^ n := by
    have hh := Fintype.card_le_of_injective (fun w : W => w.val) Subtype.val_injective
    rw [Words.card] at hh
    simpa only [← Nat.card_eq_fintype_card] using hh
  have hS := StatePaths.card_path_le trans Q hQ n
  simp only [← Nat.card_eq_fintype_card] at hS
  calc
    _ ≤ Nat.card E * Nat.card C ^ (n+1) := Nat.mul_le_mul_right _ hBE
    _ ≤ Nat.card W * Nat.card (StatePaths.Path trans n) * H ^ (n+1) *
        Nat.card ((Cayley A N → C) × Cayley A N) := hcount
    _ ≤ _ := by gcongr

end DiscreteFree.GraphProducer
end

noncomputable section
namespace DiscreteFree.GraphProducer
open scoped Classical
variable (A C : Type*) [Fintype A] [DecidableEq A] [Fintype C]

variable {S : Type*}

end DiscreteFree.GraphProducer
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.GraphProducer
open scoped BigOperators ENNReal
open scoped Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.GraphProducer.rare_matched_bound := @_root_.OAI.DiscreteFree.GraphProducer.rare_matched_bound

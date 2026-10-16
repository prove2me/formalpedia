-- Prove2me | solution 1 for OAI.TreeEdit.TorusTree.sampledWord_child_mean
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:57:37.483739+00:00
-- url     : https://prove2.me/submissions/381040e1-8e61-45b6-8290-c3d2e766ffe8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/RandomCircle.lean:L302-L341
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.TorusTree.sampledWord_child_mean. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Theorems.Thm_OAI_TreeEdit_FiniteProbability_hom_uniform
import Theorems.Thm_OAI_TreeEdit_Words_cycles_val

-- ---- from OAI.Combinatorics.TreeEdit.FiniteProbability ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

namespace TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

lemma mean_le {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    mean f ≤ mean g := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

lemma mean_mul_const {A : Type*} [Fintype A] (f : A → ℝ) (c : ℝ) :
    mean (fun a => f a * c) = mean f * c := by simp [mean, Finset.sum_mul, mul_assoc]

lemma mean_sum {A I : Type*} [Fintype A] (s : Finset I) (f : I → A → ℝ) :
    mean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, mean (f i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mean_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : B → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  simp only [mean, Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

lemma mean_fiberwise {A B : Type*} [Fintype A] [Fintype B] (f : A → B) (g : B → ℝ) :
    mean (fun a => g (f a)) = ∑ b : B, probability (fun a => f a = b) * g b := by
  have he (a : A) : g (f a) = ∑ b : B, (if f a = b then (1 : ℝ) else 0) * g b := by simp
  simp_rw [probability, ← mean_mul_const]
  rw [← mean_sum]
  apply congrArg mean
  funext a
  exact he a

end TreeEdit.FiniteProbability

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.EditMetric ----
namespace OAI

namespace TreeEdit

universe u v

namespace EditStep

variable {α : Type u} {x y : List α}

protected theorem append_left (h : EditStep x y) (p : List α) :
    EditStep (p ++ x) (p ++ y) := by
  cases h with
  | insert q r a => simpa [List.append_assoc] using EditStep.insert (p ++ q) r a
  | delete q r a => simpa [List.append_assoc] using EditStep.delete (p ++ q) r a
  | substitute q r a b =>
      simpa [List.append_assoc] using EditStep.substitute (p ++ q) r a b

protected theorem append_right (h : EditStep x y) (r : List α) :
    EditStep (x ++ r) (y ++ r) := by
  cases h with
  | insert p q a => simpa [List.append_assoc] using EditStep.insert p (q ++ r) a
  | delete p q a => simpa [List.append_assoc] using EditStep.delete p (q ++ r) a
  | substitute p q a b =>
      simpa [List.append_assoc] using EditStep.substitute p (q ++ r) a b

end EditStep

namespace EditScript

variable {α : Type u} {x y z : List α} {m n : ℕ}

protected theorem append_left (h : EditScript x y n) (p : List α) :
    EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left p) ih

protected theorem append_right (h : EditScript x y n) (p : List α) :
    EditScript (x ++ p) (y ++ p) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right p) ih

end EditScript

variable {α : Type u} {x y z : List α}

theorem ed_append (x y x' y' : List α) :
    ed (x ++ x') (y ++ y') ≤ ed x y + ed x' y' := by
  exact ed_le_of_script
    (((ed_script x y).append_right x').trans ((ed_script x' y').append_left y))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.CircleTree ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

lemma period_pos {I : Type} {g : ℕ} {r : I → ℕ} (hr : ∀ i, 0 < r i)
    (j : Fin g → I) (σ : Equiv.Perm I) : 0 < period r j σ := product_positive _ (fun _ => hr _)

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical
open FiniteProbability

end TreeEdit.TorusTree

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.WordOperations ----
namespace OAI

namespace TreeEdit

universe u v

variable {α : Type u} {x y z : List α}

attribute [local instance] Classical.propDecidable

namespace EditStep

protected lemma map {β : Type*} (f : α → β) (h : EditStep x y) :
    EditStep (x.map f) (y.map f) := by
  cases h with
  | insert p q a => simpa using EditStep.insert (p.map f) (q.map f) (f a)
  | delete p q a => simpa using EditStep.delete (p.map f) (q.map f) (f a)
  | substitute p q a b => simpa using EditStep.substitute (p.map f) (q.map f) (f a) (f b)

end EditStep

namespace EditScript

protected lemma map {β : Type*} (f : α → β) {n : ℕ} (h : EditScript x y n) :
    EditScript (x.map f) (y.map f) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.map f) ih

end EditScript

lemma ed_map {β : Type*} (f : α → β) (x y : List α) : ed (x.map f) (y.map f) ≤ ed x y :=
  ed_le_of_script ((ed_script x y).map f)

lemma ed_flatten_ofFn {n : ℕ} (x y : Fin n → List α) :
    ed (List.ofFn x).flatten (List.ofFn y).flatten ≤ ∑ i, ed (x i) (y i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons, Fin.sum_univ_succ]
    exact (ed_append _ _ _ _).trans (Nat.add_le_add_left (ih _ _) _)

namespace Words

variable {β : Type v} {n : ℕ}

lemma ed_cycles {m T B : ℕ} {β : Fin m → Type*}
    (x y : Fin T → ∀ i, Word (β i) B) :
    ed (cycles x).val (cycles y).val ≤ ∑ a : Fin T, ∑ i : Fin m,
      ed (x a i).val (y a i).val := by
  rw [cycles_val, cycles_val]
  apply (ed_flatten_ofFn _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (ed_flatten_ofFn _ _).trans
  exact Finset.sum_le_sum fun i _ => ed_map (Sigma.mk i) _ _

end Words

namespace Words

variable {β : Type v} {n : ℕ}

end Words

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.RandomCircle ----
namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma mean_comp_hom {A B : Type*} [Fintype A] [Fintype B] [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f) (g : B → ℝ) : mean (g ∘ f) = mean g := by
  change mean (fun a => g (f a)) = mean g
  rw [mean_fiberwise]
  simp_rw [hom_uniform f hf]
  rw [mean, Finset.mul_sum]

lemma mean_translate {A : Type*} [Fintype A] [AddGroup A] (y : A) (f : A → ℝ) :
    mean (fun x => f (x + y)) = mean f := mean_equiv (Equiv.addRight y) f

lemma mapState_diagonal {A B : Type} [AddCommGroup A] [AddCommGroup B] {m : ℕ}
    (f : A →+ B) (h : ℕ) (a : A) :
    mapState (m := m) f h (diagonal (A := A) (m := m) h a) = diagonal (A := B) (m := m) h (f a) := by
  induction h with
  | zero => rfl
  | succ h ih => exact funext fun _ => ih

lemma point_grid {M P : ℕ} [NeZero M] (hP : 0 < P) (hPM : P ∣ M) :
    ZMod.toAddCircle (M / P : ZMod M) = point P := by
  rw [ZMod.toAddCircle_natCast]
  dsimp [point]
  congr 1
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have he : ((M / P : ℕ) : ℝ) * P = M := by exact_mod_cast Nat.div_mul_cancel hPM
  field_simp
  linarith

lemma mean_eval {A : Type*} [Fintype A] [AddCommGroup A]
    {m : ℕ} (i : Fin m) (f : A → ℝ) :
    mean (fun x : Fin m → A => f (x i)) = mean f := by
  exact mean_comp_hom (Pi.evalAddMonoidHom _ i) (fun a => ⟨fun _ => a, rfl⟩) f

lemma sampledWord_succ {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g * s) (h + 1)) (x : State (ZMod M) (g * s) (h + 1)) :
    sampledWord r j T R (h+1) C x = Words.cycles (fun a i =>
      sampledWord r j T R h (C.2 i).2 (x i + a.val • cycle (M := M) r j h C i)) := by
  unfold sampledWord
  simp only [word]
  congr 1
  funext a i
  apply congrArg (word r j T R h (C.2 i).2)
  dsimp [cycle, sample]
  change sample (M := M) (m := g*s) h (x i) +
    diagonal (A := UnitAddCircle) (m := g*s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)) = _
  dsimp only [sample]
  simp only [map_add, map_nsmul, mapState_diagonal, point_grid (period_pos hr j C.1) (hPM C.1), mul_smul]

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma sampledWord_child_mean {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g*s) (h+1)) (i : Fin (g*s)) (z : State (ZMod M) (g*s) h) :
    mean (fun x : State (ZMod M) (g*s) (h+1) =>
      (ed (sampledWord r j T R (h+1) C x).val
        (sampledWord r j T R (h+1) C (x + child (A := ZMod M) h i z)).val : ℝ)) ≤
      T * mean (fun x : State (ZMod M) (g*s) h =>
        (ed (sampledWord r j T R h (C.2 i).2 x).val
          (sampledWord r j T R h (C.2 i).2 (x + z)).val : ℝ)) := by
  let f (x : State (ZMod M) (g*s) h) :=
    (ed (sampledWord r j T R h (C.2 i).2 x).val
      (sampledWord r j T R h (C.2 i).2 (x + z)).val : ℝ)
  have hp (x : State (ZMod M) (g*s) (h+1)) :
      (ed (sampledWord r j T R (h+1) C x).val
        (sampledWord r j T R (h+1) C (x + child (A := ZMod M) h i z)).val : ℝ) ≤
      ∑ a : Fin T, f (x i + a.val • cycle (M := M) r j h C i) := by
    rw [sampledWord_succ r j hr hPM, sampledWord_succ r j hr hPM]
    have hh := Words.ed_cycles (T := T)
      (fun a v => sampledWord r j T R h (C.2 v).2 (x v + a.val • cycle (M := M) r j h C v))
      (fun a v => sampledWord r j T R h (C.2 v).2 ((x + child (A := ZMod M) h i z) v + a.val • cycle (M := M) r j h C v))
    apply (Nat.cast_le (α := ℝ)).mpr hh |>.trans
    simp only [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.sum_eq_single i]
    · simp only [child, Pi.add_apply, AddMonoidHom.single_apply, Pi.single_eq_same]
      change (ed _ (sampledWord r j T R h (C.2 i).2 ((x i + z) + a.val • cycle (M := M) r j h C i)).val : ℝ) ≤ _
      rw [add_right_comm (x i) z]
    · intro v _ hvi
      simp [child, hvi, ed_self]
    · simp
  apply (mean_le hp).trans_eq
  rw [mean_sum]
  calc
    _ = ∑ _a : Fin T, mean f := by
      apply Finset.sum_congr rfl
      intro a _
      exact (mean_eval i (fun y => f (y + a.val • cycle (M := M) r j h C i))).trans (mean_translate _ f)
    _ = _ := by simp [f]

end TreeEdit.TorusTree

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability


theorem solution : type_of% @_root_.OAI.TreeEdit.TorusTree.sampledWord_child_mean := @_root_.OAI.TreeEdit.TorusTree.sampledWord_child_mean

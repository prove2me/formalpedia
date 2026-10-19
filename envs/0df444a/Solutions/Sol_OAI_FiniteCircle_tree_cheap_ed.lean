-- Prove2me | solution 1 for OAI.FiniteCircle.tree_cheap_ed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T15:42:53.057842+00:00
-- url     : https://prove2.me/submissions/68fbe09a-6b3d-441d-9f9d-373edd8934a8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Translations.lean:L122-L193
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.tree_cheap_ed. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations

-- ---- from OAI.Combinatorics.FiniteCircle.Edit ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

theorem append_left (h : EditStep x y) (u : List α) : EditStep (u ++ x) (u ++ y) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc] using EditStep.insert (u ++ p) q a
  | delete p q a => simpa only [List.append_assoc] using EditStep.delete (u ++ p) q a
  | substitute p q a b =>
    simpa only [List.append_assoc] using EditStep.substitute (u ++ p) q a b

theorem append_right (h : EditStep x y) (v : List α) : EditStep (x ++ v) (y ++ v) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.insert p (q ++ v) a
  | delete p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.delete p (q ++ v) a
  | substitute p q a b =>
    simpa only [List.append_assoc, List.cons_append] using EditStep.substitute p (q ++ v) a b

theorem map (h : EditStep x y) (f : α → β) : EditStep (x.map f) (y.map f) := by
  cases h with
  | insert u v a => simpa using EditStep.insert (u.map f) (v.map f) (f a)
  | delete u v a => simpa using EditStep.delete (u.map f) (v.map f) (f a)
  | substitute u v a b => simpa using EditStep.substitute (u.map f) (v.map f) (f a) (f b)
end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

theorem append_left (h : EditScript n x y) (u : List α) : EditScript n (u ++ x) (u ++ y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left u) ih

theorem append_right (h : EditScript n x y) (v : List α) : EditScript n (x ++ v) (y ++ v) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right v) ih

theorem map (h : EditScript n x y) (f : α → β) : EditScript n (x.map f) (y.map f) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.map f) ih

theorem of_sublist {z x : List α} (h : z <+ x) : EditScript (x.length - z.length) x z := by
  induction h with
  | slnil => exact .nil []
  | @cons l₁ l₂ a h ih =>
    have hl := h.length_le
    simpa only [List.nil_append, List.length_cons, show l₂.length + 1 - l₁.length = l₂.length - l₁.length + 1 by omega]
      using EditScript.cons (EditStep.delete [] l₂ a) ih
  | cons_cons a h ih =>
    simpa using ih.append_left [a]

end EditScript

theorem editDistance_triangle {α : Type*} (x y z : List α) :
    editDistance x z ≤ editDistance x y + editDistance y z :=
  editDistance_le_of_script ((editDistance_spec x y).trans (editDistance_spec y z))

theorem editDistance_map_le {α β : Type*} (f : α → β) (x y : List α) :
    editDistance (x.map f) (y.map f) ≤ editDistance x y :=
  editDistance_le_of_script ((editDistance_spec x y).map f)

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Translations ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem editDistance_append_le {α : Type*} (x y x' y' : List α) :
    editDistance (x++y) (x'++y') ≤ editDistance x x' + editDistance y y' := by
  apply editDistance_le_of_script
  exact ((editDistance_spec x x').append_right y).trans ((editDistance_spec y y').append_left x')

theorem editDistance_shifted_rows {α : Type*} (f : ℕ → List α) (N q b : ℕ)
    (hq : q ≤ N) (hf : ∀ a, (f a).length = b) :
    editDistance ((List.range N).flatMap f)
      ((List.range N).flatMap (fun a => f (q+a))) ≤ 2*q*b := by
  let z := (List.range (N-q)).flatMap (fun a => f (q+a))
  have hx : z <+ (List.range N).flatMap f := by
    have he : N = q+(N-q) := by omega
    conv_rhs => rw [he, List.range_add, List.flatMap_append, List.flatMap_map]
    exact List.sublist_append_right _ _
  have hy : z <+ (List.range N).flatMap (fun a => f (q+a)) := by
    have he : N = (N-q)+q := by omega
    conv_rhs => rw [he, List.range_add, List.flatMap_append]
    exact List.sublist_append_left _ _
  have hlen : ∀ a, ((List.range N).flatMap (fun i => f (a+i))).length = N*b := by
    intro a
    simpa only [List.length_range] using length_flatMap_uniform (List.range N) (fun i => f (a+i)) b (fun i _ => hf _)
  have hlx : ((List.range N).flatMap f).length = N*b := by simpa using hlen 0
  have hlz : z.length = (N-q)*b := by
    simpa only [List.length_range] using length_flatMap_uniform (List.range (N-q)) (fun i => f (q+i)) b (fun i _ => hf _)
  have hd := editDistance_le_of_script ((EditScript.of_sublist hx).trans (EditScript.of_sublist hy).symm)
  rw [hlx, hlen, hlz] at hd
  have hab : (N-q)*b+q*b = N*b := by rw [← Nat.add_mul]; congr; omega
  have hh : N*b-(N-q)*b = q*b := by omega
  rw [hh] at hd
  simpa only [two_mul, add_mul] using hd

 theorem editDistance_flatMap_scaled {α β : Type*} (xs : List α) (f g : α → List β)
    (R k : ℕ) (hk : ∀ a ∈ xs, R*editDistance (f a) (g a) ≤ k) :
    R*editDistance (xs.flatMap f) (xs.flatMap g) ≤ xs.length*k := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ht := Nat.mul_le_mul_left R (editDistance_append_le (f a) (xs.flatMap f) (g a) (xs.flatMap g))
    have ha := hk a (by simp)
    have hs := ih (fun a ha => hk a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_cons]
    rw [Nat.mul_add] at ht
    nlinarith

theorem tree_cheap_ed (J Z A : ℕ → Type) [∀ l, AddCommGroup (Z l)]
    {M R : ℕ} (hR : 0 < R) (P L : ℕ → ℕ)
    (tags : ∀ l, List (J (l+1)))
    (tag : ∀ l, J (l+1) → A l → A (l+1))
    (σ : ∀ l, Z l →+ (J l → ZMod M))
    (γ : ∀ l, ℕ → J (l+1) → ZMod M)
    (W : ∀ l, (TreeLeaf J l → ZMod M) → List (A l))
    (hlen : ∀ l v, (W l v).length = L l)
    (hL : ∀ l, L (l+1) = (R*P (l+1))*((tags l).length*L l))
    (hrec : ∀ l v, W (l+1) v = (List.range (R*P (l+1))).flatMap
      (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j))))
    (hCRT : ∀ l z, ∃ q : ℕ, q < P (l+1) ∧ ∀ a j, γ l (q+a) j = σ (l+1) z j+γ l a j)
    (l : ℕ) (v c : TreeLeaf J l → ZMod M) (hc : c ∈ treeCheap J Z σ l) :
    R*editDistance (W l v) (W l (v+c)) ≤ 2*l*L l := by
  classical
  induction l with
  | zero =>
    have hz : c=0 := hc
    simp [hz]
  | succ l ih =>
    obtain ⟨cc,hcc,z,hz⟩ := hc
    let u : TreeLeaf J (l+1) → ZMod M := fun i => v i+cc i.1 i.2
    have hu : R*editDistance (W (l+1) v) (W (l+1) u) ≤ 2*l*L (l+1) := by
      rw [hrec, hrec]
      have hh := editDistance_flatMap_scaled (List.range (R*P (l+1)))
        (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j)))
        (fun a => (tags l).flatMap (fun j => (W l (fun i => u (j,i)+γ l a j)).map (tag l j)))
        R ((tags l).length*(2*l*L l)) (by
          intro a _
          apply editDistance_flatMap_scaled
          intro j _
          have he : (fun i => u (j,i)+γ l a j) = (fun i => v (j,i)+γ l a j)+cc j := by
            funext i
            dsimp [u]
            abel
          rw [he]
          exact (Nat.mul_le_mul_left R (editDistance_map_le _ _ _)).trans
            (ih (fun i => v (j,i)+γ l a j) (cc j) (hcc j)))
      simpa only [List.length_range, hL, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh
    obtain ⟨q,hq,hqγ⟩ := hCRT l z
    let row (a : ℕ) := (tags l).flatMap (fun j => (W l (fun i => u (j,i)+γ l a j)).map (tag l j))
    have hrow : ∀ a, (row a).length = (tags l).length*L l := by
      intro a
      apply length_flatMap_uniform
      intro j _
      simp only [List.length_map, hlen]
    have hshift : W (l+1) (v+c) = (List.range (R*P (l+1))).flatMap (fun a => row (q+a)) := by
      rw [hrec]
      apply List.flatMap_congr
      intro a _
      apply List.flatMap_congr
      intro j _
      congr 2
      funext i
      change v (j,i)+c (j,i)+γ l a j = u (j,i)+γ l (q+a) j
      rw [hz, hqγ]
      dsimp [u]
      abel
    have hqN : q ≤ R*P (l+1) := by
      exact hq.le.trans (Nat.le_mul_of_pos_left _ hR)
    have hs := editDistance_shifted_rows row (R*P (l+1)) q ((tags l).length*L l) hqN hrow
    change editDistance ((List.range (R*P (l+1))).flatMap row) _ ≤ _ at hs
    have hurow : W (l+1) u = (List.range (R*P (l+1))).flatMap row := hrec l u
    rw [← hurow, ← hshift] at hs
    have hs' : R*editDistance (W (l+1) u) (W (l+1) (v+c)) ≤ 2*L (l+1) := by
      apply (Nat.mul_le_mul_left R hs).trans
      rw [hL]
      have hqp := Nat.mul_le_mul_right (R*((tags l).length*L l)) hq.le
      nlinarith
    have ht := Nat.mul_le_mul_left R (editDistance_triangle (W (l+1) v) (W (l+1) u) (W (l+1) (v+c)))
    rw [Nat.mul_add] at ht
    nlinarith

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.tree_cheap_ed := @_root_.OAI.FiniteCircle.tree_cheap_ed

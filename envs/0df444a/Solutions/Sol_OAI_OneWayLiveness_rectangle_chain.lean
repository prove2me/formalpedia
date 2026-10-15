-- Prove2me | solution 1 for OAI.OneWayLiveness.rectangle_chain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:02:05.087057+00:00
-- url     : https://prove2.me/submissions/2498154d-88bb-4794-b80c-23b04f5599a0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/RankLoss.lean:L180-L266
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.rectangle_chain. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Theorems.Thm_OAI_OneWayLiveness_RectangleFrame_rel_mul
import Theorems.Thm_OAI_OneWayLiveness_RectangleFrame_restricted_new
import Theorems.Thm_OAI_OneWayLiveness_rank_drop_step

-- ---- from OAI.Combinatorics.Automata.Rank ----
namespace OAI

namespace OneWayLiveness

namespace Pairing
open scoped Classical
variable {A B C : Type*}

variable [Fintype A] [Fintype B] [Fintype C]

lemma lefts_compose_subset (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    lefts (compose a b) ⊆ lefts a := by
  intro i hi
  obtain ⟨k, hik⟩ := (mem_lefts _ _).mp hi
  obtain ⟨j, hij, _⟩ := a.unique (.inl i)
  rcases j with j | j
  · have hh := compose_left_cap a b hij
    have he := ((compose a b).eq_mate hh).trans ((compose a b).eq_mate hik).symm
    cases he
  · exact (mem_lefts _ _).mpr ⟨j, hij⟩

lemma rank_compose_le_left (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rank (compose a b) ≤ rank a := Finset.card_le_card (lefts_compose_subset a b)
lemma support_compose_subset (a b : Pairing (A ⊕ A)) :
    support (compose a b) ⊆ support a ∪ support b := by
  intro i hi
  by_contra hn
  have ha : a.link (.inl i) (.inr i) := by
    simpa using (Finset.notMem_union.mp hn).1
  have hb : b.link (.inl i) (.inr i) := by
    simpa using (Finset.notMem_union.mp hn).2
  exact (mem_support _ _).mp hi (compose_transversal a b ha hb)

end Pairing

namespace Pairing
open scoped Classical
variable {P : Type*} {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

end Pairing

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Diagram ----
namespace OAI

namespace OneWayLiveness

namespace FiniteWiring
variable {V C : Type*} (G : SimpleGraph V)

end FiniteWiring

namespace Pairing
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

end Pairing

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
lemma support_one : support (1 : Pairing (A ⊕ A)) = ∅ := by
  ext i
  simp [mem_support, identity_link]

lemma rank_mul_le_left (a b : Pairing (A ⊕ A)) : rank (a * b) ≤ rank a :=
  rank_compose_le_left a b
lemma support_mul_subset (a b : Pairing (A ⊕ A)) :
    support (a * b) ⊆ support a ∪ support b := support_compose_subset a b

lemma support_pow_subset (a : Pairing (A ⊕ A)) (n : ℕ) : support (a ^ n) ⊆ support a := by
  induction n with
  | zero => simp only [pow_zero, support_one, Finset.empty_subset]
  | succ n ih =>
    rw [pow_succ]
    exact (support_mul_subset _ _).trans (Finset.union_subset ih (Finset.Subset.refl _))

end Pairing

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Corners ----
namespace OAI

namespace OneWayLiveness

/-- Positive powers in any finite monoid contain an idempotent. -/
lemma exists_idempotent_power {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, 0 < n ∧ a ^ n * a ^ n = a ^ n := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let S : Set M := {x | ∃ n : ℕ, 0 < n ∧ a ^ n = x}
  have hS : S.Nonempty := ⟨a, 1, by omega, pow_one a⟩
  have hmul : ∀ᵉ (x ∈ S) (y ∈ S), x * y ∈ S := by
    rintro x ⟨n, hn, rfl⟩ y ⟨m, hm, rfl⟩
    exact ⟨n + m, by omega, pow_add a n m⟩
  obtain ⟨b, ⟨n, hn, rfl⟩, hb⟩ := exists_idempotent_in_compact_subsemigroup
    (fun _ => continuous_of_discreteTopology) S hS (Set.toFinite S).isCompact hmul
  exact ⟨n, hn, hb⟩

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}
lemma val_pow_pos (x : Corner e he) {n : ℕ} (hn : 0 < n) : (x ^ n).val = x.val ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ x (k+1), pow_succ x.val (k+1), val_mul, ih (by omega)]
end Corner

namespace Corner
variable {M N : Type*} [Monoid M] [Monoid N] {e : M} {he : e * e = e}
    {q : N} {hq : q * q = q}

end Corner

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
    {M : Type*} [Monoid M] (ρ : M →* Pairing (A ⊕ A))
    (e : M) (he : e * e = e)

end Pairing

namespace Corner
variable {M : Type*} [Monoid M] {e f : M} {he : e * e = e} {hf : f * f = f}

end Corner

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Relations ----
namespace OAI

namespace OneWayLiveness

namespace BRel
variable {H : Type*}

end BRel

namespace BRel
variable {H : Type*}
end BRel

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
lemma rel_empty : F.rel ∅ = F.base := by ext x y; simp [base]

lemma rel_idem (E : Set (I × J)) : F.rel E * F.rel E = F.rel E := by
  rw [rel_mul, Set.union_self]
lemma rel_absorb {E D : Set (I × J)} (h : E ⊆ D) :
    F.rel E * F.rel D = F.rel D ∧ F.rel D * F.rel E = F.rel D := by
  rw [rel_mul, rel_mul, Set.union_eq_right.mpr h, Set.union_eq_left.mpr h]
  exact ⟨rfl, rfl⟩

lemma restricted_old (E : Set (I × J)) (K : Set H)
    (hK : ∀ x ∈ K, x ≠ F.hub)
    (hE : ∀ p ∈ E, F.left p.1 ∉ K ∨ F.right p.2 ∉ K) :
    BRel.restrictedId K * F.rel E * BRel.restrictedId K = BRel.restrictedId K := by
  ext x y
  simp only [BRel.mul_restrictedId, BRel.restrictedId_mul, BRel.restrictedId_holds]
  constructor
  · rintro ⟨⟨hx, (⟨hxy, _⟩ | ⟨p, hp, rfl, rfl⟩)⟩, hy⟩
    · exact ⟨hxy, hx⟩
    · exact ((hE p hp).elim (fun h => h hx) (fun h => h hy)).elim
  · rintro ⟨rfl, hx⟩
    exact ⟨⟨hx, Or.inl ⟨rfl, hK x hx⟩⟩, hx⟩

end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

end Corner

namespace BRel
variable {H : Type*}
end BRel

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.RankLoss ----
namespace OAI

namespace OneWayLiveness

namespace RectangleFrame
open scoped Classical
variable {H I J : Type} [Fintype I] [Fintype J]
    (F : RectangleFrame H I J)

lemma retained_ne_hub (i : I) (j : J) (x : H) (hx : x ∈ F.retained i j) : x ≠ F.hub := by
  intro h
  subst x
  exact hx (by simp [deleted])

lemma old_avoids_retained {E : Set (I × J)} {i : I} {j : J} (h : (i,j) ∉ E) :
    ∀ p ∈ E, F.left p.1 ∉ F.retained i j ∨ F.right p.2 ∉ F.retained i j := by
  intro p hp
  simp only [left_mem_retained, right_mem_retained]
  by_contra! hh
  have he : p = (i, j) := Prod.ext hh.1 hh.2
  exact h (he ▸ hp)

end RectangleFrame

open scoped Classical

lemma rectangle_chain {H A M I J : Type} [Fintype H] [Fintype A]
    [Fintype I] [Fintype J] [Monoid M] [Finite M]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ)
    (F : RectangleFrame H I J) (L : ℕ)
    (hL : ∀ i j, rankLoss (Fintype.card (F.retained i j)) = L)
    (hIH : ∀ i j, RankLossAt (Fintype.card (F.retained i j)))
    (e : M) (he : e * e = e) (heφ : φ e = F.base)
    (g : I × J → Corner e he)
    (hg : ∀ p, φ (g p).val = F.rel {p})
    (K : Finset {i // i ∈ Pairing.lefts (ρ e)})
    (hgK : ∀ p, Pairing.support (Pairing.reduceHom ρ e he (g p)) ⊆ K)
    (E : Finset (I × J)) :
    ∃ b : Corner e he, b * b = b ∧ φ b.val = F.rel (E : Set (I × J)) ∧
      Pairing.support (Pairing.reduceHom ρ e he b) ⊆ K ∧
      E.card * L ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by
  classical
  let ρ₀ := Pairing.reduceHom ρ e he
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mul _, ?_, ?_, ?_⟩
    · simpa only [Corner.val_one, Finset.coe_empty, F.rel_empty] using heφ
    · simp only [map_one, Pairing.support_one, Finset.empty_subset]
    · simp
  | @insert p E hp ih =>
    obtain ⟨b, hb, hbφ, hbK, hbound⟩ := ih
    let w : Corner b hb := Corner.sandwich (g p)
    obtain ⟨n, hn, hnidem⟩ := exists_idempotent_power w
    let v := w ^ n
    have hv : v.val * v.val = v.val := congrArg Corner.val hnidem
    have hwφ : φ w.val.val = F.rel ((insert p E : Finset (I × J)) : Set (I × J)) := by
      change φ ((b.val * (g p).val) * b.val) = _
      rw [map_mul, map_mul, hbφ, hg, F.rel_mul, F.rel_mul]
      congr 1
      ext q
      simp only [Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe,
        Finset.mem_insert]
      tauto
    have hvφ : φ v.val.val = F.rel ((insert p E : Finset (I × J)) : Set (I × J)) := by
      dsimp [v]
      rw [Corner.val_pow_pos w hn, Corner.val_pow_pos w.val hn, map_pow, hwφ]
      exact IsIdempotentElem.pow_eq (F.rel_idem _) (Nat.ne_of_gt hn)
    have mulK (a c : Pairing ({i // i ∈ Pairing.lefts (ρ e)} ⊕ {i // i ∈ Pairing.lefts (ρ e)}))
        (ha : Pairing.support a ⊆ K) (hc : Pairing.support c ⊆ K) :
        Pairing.support (a * c) ⊆ K :=
      by
        intro i hi
        have hh := Pairing.support_mul_subset a c hi
        simp only [Finset.mem_union] at hh
        exact hh.elim (fun h => ha h) (fun h => hc h)
    have hwK : Pairing.support (ρ₀ w.val) ⊆ K := by
      change Pairing.support (ρ₀ (b * g p * b)) ⊆ K
      rw [map_mul, map_mul]
      exact mulK _ _ (mulK _ _ hbK (hgK p)) hbK
    have hvK : Pairing.support (ρ₀ v.val) ⊆ K := by
      dsimp [v]
      rw [Corner.val_pow_pos _ hn, map_pow]
      exact (Pairing.support_pow_subset _ _).trans hwK
    let R := F.retained p.1 p.2
    have hR := F.restricted_old (E : Set (I × J)) R (F.retained_ne_hub p.1 p.2)
      (F.old_avoids_retained hp)
    obtain ⟨hPN, hNP⟩ := F.rel_absorb (E := (E : Set (I × J)))
      (D := ((insert p E : Finset (I × J)) : Set (I × J))) (by simp)
    let u : R := ⟨F.left p.1, (F.left_mem_retained _ _ _).mpr rfl⟩
    let z : R := ⟨F.right p.2, (F.right_mem_retained _ _ _).mpr rfl⟩
    have huz : u ≠ z := fun h => F.disjoint p.1 p.2 (congrArg Subtype.val h)
    have him : ∀ i j : R, (F.rel ((insert p E : Finset (I × J)) : Set (I × J))).holds
        i.val j.val ↔ (BRel.addEdge u z).holds i j := by
      simpa only [Finset.coe_insert] using
        F.restricted_new (E : Set (I × J)) R (F.retained_ne_hub p.1 p.2)
          (F.old_avoids_retained hp) p.1 p.2 u.property z.property
    let v' := Corner.flattenEquiv b hb v
    have hv' : v' * v' = v' := by rw [← map_mul, hnidem]
    have hstep := rank_drop_step ρ hρ φ hφ b.val (Corner.val_idempotent b hb) v' hv'
      (F.rel E) (F.rel ((insert p E : Finset (I × J)) : Set (I × J))) hbφ hvφ R hR hPN hNP u z huz him (hIH p.1 p.2)
    rw [hL] at hstep
    have hrb : Pairing.rank (ρ b.val) ≤ Pairing.rank (ρ e) := by
      have hh := Pairing.rank_mul_le_left (ρ e) (ρ b.val)
      rwa [← map_mul, b.left] at hh
    have hrv : Pairing.rank (ρ v.val.val) ≤ Pairing.rank (ρ b.val) := by
      have hh := Pairing.rank_mul_le_left (ρ b.val) (ρ v.val.val)
      have heq : b.val * v.val.val = v.val.val := congrArg Corner.val v.left
      rwa [← map_mul, heq] at hh
    refine ⟨v.val, hv, hvφ, hvK, ?_⟩
    change L ≤ 2 * (Pairing.rank (ρ b.val) - Pairing.rank (ρ v.val.val)) at hstep
    rw [Finset.card_insert_of_notMem hp, Nat.add_mul, one_mul]
    omega

namespace Corner
variable {M : Type*} [Monoid M]
end Corner

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness
open scoped Classical


theorem solution : type_of% @_root_.OAI.OneWayLiveness.rectangle_chain := @_root_.OAI.OneWayLiveness.rectangle_chain

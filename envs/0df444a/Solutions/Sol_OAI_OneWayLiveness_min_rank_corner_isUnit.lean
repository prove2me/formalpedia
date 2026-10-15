-- Prove2me | solution 1 for OAI.OneWayLiveness.min_rank_corner_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:46:45.751947+00:00
-- url     : https://prove2.me/submissions/8a1dad7f-cb41-48ac-ba38-a3f18d48b33a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Corners.lean:L152-L176
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.min_rank_corner_isUnit. The node keeps its source
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
import Theorems.Thm_OAI_OneWayLiveness_Pairing_full_rank_isUnit

-- ---- from OAI.Combinatorics.Automata.Rank ----
namespace OAI

namespace OneWayLiveness

namespace Pairing
open scoped Classical
variable {A B C : Type*}

variable [Fintype A] [Fintype B] [Fintype C]

lemma rank_eq_rights (a : Pairing (A ⊕ B)) : rank a = (rights a).card := by
  simpa only [Fintype.card_coe, rank] using Fintype.card_congr (transversalEquiv a)

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

lemma rights_compose_subset (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rights (compose a b) ⊆ rights b := by
  intro k hk
  obtain ⟨i, hik⟩ := (mem_rights _ _).mp hk
  obtain ⟨j, hkj, _⟩ := b.unique (.inr k)
  rcases j with j | j
  · exact (mem_rights _ _).mpr ⟨j, b.symm hkj⟩
  · have hh := compose_right_cap a b hkj
    have he := ((compose a b).eq_mate hh).trans
      ((compose a b).eq_mate ((compose a b).symm hik)).symm
    cases he

lemma rank_compose_le_left (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rank (compose a b) ≤ rank a := Finset.card_le_card (lefts_compose_subset a b)
lemma rank_compose_le_right (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rank (compose a b) ≤ rank b := by
  rw [rank_eq_rights, rank_eq_rights]
  exact Finset.card_le_card (rights_compose_subset a b)
lemma rank_le_card (a : Pairing (A ⊕ B)) : rank a ≤ Fintype.card A :=
  Finset.card_le_univ _

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
lemma rank_mul_le_right (a b : Pairing (A ⊕ A)) : rank (a * b) ≤ rank b :=
  rank_compose_le_right a b

lemma expand_reduce (e z : Pairing (A ⊕ A)) : expand e (reduce e z) = e * z * e := by
  simp only [expand, reduce, mul_eq_compose, compose_assoc, ← splitLeft_splitRight e]

lemma rank_reduce (e z : Pairing (A ⊕ A)) (hzl : e * z = z) (hzr : z * e = z) :
    rank (reduce e z) = rank z := by
  apply le_antisymm
  · exact (rank_compose_le_left _ _).trans (rank_compose_le_right _ _)
  · have heq : expand e (reduce e z) = z := by rw [expand_reduce, hzl, hzr]
    calc
      rank z = rank (expand e (reduce e z)) := congrArg rank heq.symm
      _ ≤ rank (compose (splitLeft e) (reduce e z)) := rank_compose_le_left _ _
      _ ≤ rank (reduce e z) := rank_compose_le_right _ _

lemma reduce_injective (e : Pairing (A ⊕ A)) {x y : Pairing (A ⊕ A)}
    (hxl : e * x = x) (hxr : x * e = x) (hyl : e * y = y) (hyr : y * e = y)
    (h : reduce e x = reduce e y) : x = y := by
  have hh := congrArg (expand e) h
  simpa only [expand_reduce, hxl, hxr, hyl, hyr] using hh

lemma card_reduced (e : Pairing (A ⊕ A)) : Fintype.card {i // i ∈ lefts e} = rank e :=
  Fintype.card_coe _
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

lemma isUnit_of_injective_map_finite {M N : Type*} [Monoid M] [Monoid N] [Finite M]
    (f : M →* N) (hf : Function.Injective f) (a : M) (ha : IsUnit (f a)) : IsUnit a := by
  obtain ⟨n, hn, hi⟩ := exists_idempotent_power a
  have hp : f (a ^ n) = 1 := by
    have hu : IsUnit (f (a ^ n)) := by rw [map_pow]; exact ha.pow n
    apply (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp
    change f (a ^ n) * f (a ^ n) = f (a ^ n)
    rw [← map_mul, hi]
  have he : a ^ n = 1 := hf (by simpa using hp)
  apply (isUnit_pow_iff (Nat.ne_of_gt hn)).mp
  rw [he]
  exact isUnit_one

namespace Corner
variable {M N : Type*} [Monoid M] [Monoid N] {e : M} {he : e * e = e}
    {q : N} {hq : q * q = q}

end Corner

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
    {M : Type*} [Monoid M] (ρ : M →* Pairing (A ⊕ A))
    (e : M) (he : e * e = e)

lemma reduceHom_injective (hρ : Function.Injective ρ) : Function.Injective (reduceHom ρ e he) := by
  intro x y hxy
  apply Corner.ext
  apply hρ
  apply reduce_injective (ρ e) (by rw [← map_mul, x.left]) (by rw [← map_mul, x.right])
    (by rw [← map_mul, y.left]) (by rw [← map_mul, y.right]) hxy

lemma reduceHom_rank (x : Corner e he) : rank (reduceHom ρ e he x) = rank (ρ x.val) :=
  rank_reduce _ _ (by rw [← map_mul, x.left]) (by rw [← map_mul, x.right])

lemma rank_pow_le (a : Pairing (A ⊕ A)) {n : ℕ} (hn : 0 < n) : rank (a ^ n) ≤ rank a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ]
  exact rank_mul_le_right _ _

end Pairing

/-- Minimum rank over the local identity forces all local unit lifts to be units. -/
lemma min_rank_corner_isUnit {M N A : Type*} [Monoid M] [Monoid N] [Finite M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (f : M →* N) (e : M) (he : e * e = e) (q : N) (hq : q * q = q) (hf : f e = q)
    (hmin : ∀ z : M, z * z = z → f z = q → Pairing.rank (ρ e) ≤ Pairing.rank (ρ z))
    (y : Corner e he) (hy : IsUnit (Corner.mapTo (he := he) (hq := hq) f hf y)) : IsUnit y := by
  obtain ⟨n, hn, hi⟩ := exists_idempotent_power y
  have him : Corner.mapTo (he := he) (hq := hq) f hf (y ^ n) = 1 := by
    apply (IsIdempotentElem.iff_eq_one_of_isUnit ?_).mp
    · change _ * _ = _
      rw [← map_mul, hi]
    · rw [map_pow]
      exact hy.pow n
  have him' : f (y ^ n).val = q := congrArg Corner.val him
  have hlow := hmin (y ^ n).val (Corner.val_idempotent _ hi) him'
  have hbound : Pairing.rank (ρ (y ^ n).val) ≤ Pairing.rank (ρ y.val) := by
    rw [Corner.val_pow_pos y hn, map_pow]
    exact Pairing.rank_pow_le _ hn
  have hEq : Pairing.rank (Pairing.reduceHom ρ e he y) =
      Fintype.card {i // i ∈ Pairing.lefts (ρ e)} := by
    apply le_antisymm (Pairing.rank_le_card _)
    rw [Pairing.reduceHom_rank, Pairing.card_reduced]
    exact hlow.trans hbound
  exact isUnit_of_injective_map_finite (Pairing.reduceHom ρ e he)
    (Pairing.reduceHom_injective ρ e he hρ) y (Pairing.full_rank_isUnit _ hEq)

namespace Corner
variable {M : Type*} [Monoid M] {e f : M} {he : e * e = e} {hf : f * f = f}

end Corner

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness


theorem solution : type_of% @_root_.OAI.OneWayLiveness.min_rank_corner_isUnit := @_root_.OAI.OneWayLiveness.min_rank_corner_isUnit

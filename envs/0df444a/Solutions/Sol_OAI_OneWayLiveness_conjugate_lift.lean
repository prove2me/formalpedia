-- Prove2me | solution 1 for OAI.OneWayLiveness.conjugate_lift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:51:41.415665+00:00
-- url     : https://prove2.me/submissions/4baaba5f-2d66-4c48-a335-066ac221c186

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Relations.lean:L165-L180
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.conjugate_lift. The node keeps its source
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
lemma rank_mul_le_left (a b : Pairing (A ⊕ A)) : rank (a * b) ≤ rank a :=
  rank_compose_le_left a b
lemma rank_mul_le_right (a b : Pairing (A ⊕ A)) : rank (a * b) ≤ rank b :=
  rank_compose_le_right a b

lemma rank_mul_unit (a : Pairing (A ⊕ A)) (u : (Pairing (A ⊕ A))ˣ) :
    rank (a * (u : Pairing (A ⊕ A))) = rank a := by
  apply le_antisymm (rank_mul_le_left _ _)
  have hr := rank_mul_le_left (a * (u : Pairing (A ⊕ A))) (↑u⁻¹)
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hr
lemma rank_unit_mul (u : (Pairing (A ⊕ A))ˣ) (a : Pairing (A ⊕ A)) :
    rank ((u : Pairing (A ⊕ A)) * a) = rank a := by
  apply le_antisymm (rank_mul_le_right _ _)
  have hr := rank_mul_le_right (↑u⁻¹) ((u : Pairing (A ⊕ A)) * a)
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using hr

end Pairing

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
lemma conjugate_addEdge (σ : Equiv.Perm H) (x y : H) :
    (↑(permUnit σ)⁻¹ : BRel H) * addEdge x y * ↑(permUnit σ) = addEdge (σ x) (σ y) := by
  ext u v
  change (∃ k, (∃ j, σ.symm u = j ∧ (j = k ∨ j = x ∧ k = y)) ∧ σ k = v) ↔
    u = v ∨ u = σ x ∧ v = σ y
  constructor
  · rintro ⟨k, ⟨j, hj, hk⟩, hv⟩
    subst j
    rcases hk with hk | ⟨hx, rfl⟩
    · exact Or.inl (by rw [← hk, σ.apply_symm_apply] at hv; exact hv)
    · exact Or.inr ⟨(σ.symm_apply_eq).mp hx, hv.symm⟩
  · rintro (rfl | ⟨rfl, rfl⟩)
    · exact ⟨σ.symm u, ⟨σ.symm u, rfl, Or.inl rfl⟩, σ.apply_symm_apply u⟩
    · exact ⟨y, ⟨x, σ.symm_apply_apply x, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩

lemma exists_perm_pair [Finite H] {x y u v : H} (hxy : x ≠ y) (huv : u ≠ v) :
    ∃ σ : Equiv.Perm H, σ x = u ∧ σ y = v := by
  let f : Bool → H := fun b => if b then y else x
  let g : Bool → H := fun b => if b then v else u
  have hf : Function.Injective f := by
    intro b c h
    cases b <;> cases c <;> simp_all [f, Ne.symm hxy]
  have hg : Function.Injective g := by
    intro b c h
    cases b <;> cases c <;> simp_all [g, Ne.symm huv]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨σ, hσ false, hσ true⟩
end BRel

lemma unit_image_inv {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (u : Mˣ) (v : Nˣ) (h : f (↑u) = (↑v)) : f (↑u⁻¹) = (↑v⁻¹) := by
  have he : Units.map f u = v := Units.ext h
  exact congrArg (fun w : Nˣ => (↑w⁻¹ : N)) he

lemma conjugate_lift {M H A : Type*} [Monoid M] [Finite H] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (f : M →* BRel H) (hl : HasUnitLifts f)
    (a : M) (ha : a * a = a) (x y : H) (hxy : x ≠ y) (hfa : f a = BRel.addEdge x y)
    (u v : H) (huv : u ≠ v) :
    ∃ b : M, b * b = b ∧ f b = BRel.addEdge u v ∧ Pairing.rank (ρ b) = Pairing.rank (ρ a) := by
  obtain ⟨σ, hx, hy⟩ := BRel.exists_perm_pair hxy huv
  obtain ⟨w, hw⟩ := hl (BRel.permUnit σ)
  refine ⟨(↑w⁻¹ : M) * a * (↑w : M), ?_, ?_, ?_⟩
  · calc
      _ = (↑w⁻¹ : M) * (a * ((↑w : M) * ↑w⁻¹) * a) * ↑w := by simp only [mul_assoc]
      _ = (↑w⁻¹ : M) * a * ↑w := by rw [Units.mul_inv, mul_one, ha]
  · rw [map_mul, map_mul, hw, unit_image_inv f w _ hw, hfa, BRel.conjugate_addEdge, hx, hy]
  · rw [map_mul, map_mul]
    change Pairing.rank (((Units.map ρ w⁻¹ : (Pairing (A ⊕ A))ˣ) : Pairing (A ⊕ A)) * ρ a *
      ((Units.map ρ w : (Pairing (A ⊕ A))ˣ) : Pairing (A ⊕ A))) = _
    rw [Pairing.rank_mul_unit, Pairing.rank_unit_mul]

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

end Corner

namespace BRel
variable {H : Type*}
end BRel

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness


theorem solution : type_of% @_root_.OAI.OneWayLiveness.conjugate_lift := @_root_.OAI.OneWayLiveness.conjugate_lift

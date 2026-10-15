-- Prove2me | solution 1 for OAI.OneWayLiveness.Pairing.support_sandwich_subset_marked
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:44:01.917866+00:00
-- url     : https://prove2.me/submissions/a12102b0-48b7-4835-b4f7-3a73cf7888bd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Diagram.lean:L62-L116
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.Pairing.support_sandwich_subset_marked. The node keeps its source
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

-- ---- from OAI.Combinatorics.Automata.Wiring ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace OneWayLiveness

namespace Pairing
variable {P : Type*} (a : Pairing P)
end Pairing

namespace Pairing
variable {P : Type*} (a : Pairing P)

end Pairing

namespace FiniteWiring
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

end FiniteWiring

namespace Pairing
variable {A B C : Type*}

variable [Fintype A] [Fintype B] [Fintype C] (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))

end Pairing

namespace Pairing
variable {P Q : Type*}

variable {A B C D : Type*}

/-- The Boolean equality semantics is faithful even for a single pair. -/
lemma connected_of_color_eq (a : Pairing P) (x y : P)
    (h : ∀ c : P → Bool, a.Compatible c → c x = c y) : a.connected x y := by
  have he := h (a.testColor x) (a.compatible_testColor x)
  rw [testColor_self] at he
  simpa only [testColor, decide_eq_true_eq] using he.symm

lemma link_of_color_eq (a : Pairing P) {x y : P} (hne : x ≠ y)
    (h : ∀ c : P → Bool, a.Compatible c → c x = c y) : a.link x y :=
  (a.connected_of_color_eq x y h).resolve_left hne

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

end Pairing

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Diagram ----
namespace OAI

namespace OneWayLiveness

namespace FiniteWiring
variable {V C : Type*} (G : SimpleGraph V)

/-- Only edge constraints in the starting component are needed. -/
lemma color_eq_of_reachable_from (color : V → C) (s : V)
    (hc : ∀ x y, G.Reachable s x → G.Adj x y → color x = color y)
    {y : V} (h : G.Reachable s y) : color s = color y := by
  obtain ⟨p⟩ := h
  have aux {x y : V} (p : G.Walk x y) (hx : G.Reachable s x) : color x = color y := by
    induction p with
    | nil => rfl
    | @cons x y z h p ih => exact (hc x y hx h).trans (ih (hx.trans h.reachable))
  exact aux p (.refl s)
end FiniteWiring

namespace Pairing
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

/-- Unmarked original identity paths retain their equality constraints
through every supported perturbation of the middle diagram. -/
lemma support_sandwich_subset_marked (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) (J : Finset B) (a : Pairing (B ⊕ B))
    (ha : support a ⊆ J) : support (compose (compose v a) u) ⊆ marked v u J := by
  intro x hx
  by_contra hxm
  have hfix : (compose (compose v a) u).link (.inl x) (.inr x) := by
    apply link_of_color_eq _ Sum.inl_ne_inr
    intro c hc
    let f : A → Bool := fun y => c (.inl y)
    let g : A → Bool := fun y => c (.inr y)
    have hc' : (compose (compose v a) u).Compatible (Sum.elim f g) := by
      have he : Sum.elim f g = c := by funext y; cases y <;> rfl
      simpa only [he] using hc
    obtain ⟨β, hva, hu⟩ := (compose_compatible (compose v a) u f g).mp hc'
    obtain ⟨α, hv, hab⟩ := (compose_compatible v a f β).mp hva
    let col : ((A ⊕ B) ⊕ (B ⊕ A)) → Bool := Sum.elim (Sum.elim f α) (Sum.elim β g)
    have hab_eq (i : B) (hi : i ∉ J) : α i = β i := by
      have hs : i ∉ support a := fun his => hi (ha his)
      have hl : a.link (.inl i) (.inr i) := by simpa only [mem_support, not_not] using hs
      exact hab _ _ hl
    have hedge : ∀ y z, (glueGraph v u).Reachable (outer (.inl x)) y →
        (glueGraph v u).Adj y z → col y = col z := by
      intro y z hy hyz
      rcases y with (i | i) | (i | i) <;>
        rcases z with (j | j) | (j | j)
      · exact hv _ _ hyz
      · exact hv _ _ hyz
      · exact hyz.elim
      · exact hyz.elim
      · exact hv _ _ hyz
      · exact hv _ _ hyz
      · change i = j at hyz
        subst j
        exact hab_eq i (fun hi => hxm ((mem_marked v u J x).mpr ⟨i, hi, hy⟩))
      · exact hyz.elim
      · exact hyz.elim
      · change j = i at hyz
        subst j
        have hreach : (glueGraph v u).Reachable (outer (.inl x)) (.inl (.inr i)) :=
          hy.trans (show (glueGraph v u).Adj (.inr (.inl i)) (.inl (.inr i)) from rfl).reachable
        exact (hab_eq i (fun hi => hxm ((mem_marked v u J x).mpr ⟨i, hi, hreach⟩))).symm
      · exact hu _ _ hyz
      · exact hu _ _ hyz
      · exact hyz.elim
      · exact hyz.elim
      · exact hu _ _ hyz
      · exact hu _ _ hyz
    have hpath : (glueGraph v u).Reachable (outer (.inl x)) (outer (.inr x)) := by
      have hi : (compose v u).link (.inl x) (.inr x) := by
        rw [huv, identity_link]; rfl
      exact hi.2
    exact FiniteWiring.color_eq_of_reachable_from _ col _ hedge hpath
  exact (mem_support _ _).mp hx hfix

end Pairing

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
end Pairing

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.Pairing
open scoped Classical


theorem solution : type_of% @_root_.OAI.OneWayLiveness.Pairing.support_sandwich_subset_marked := @_root_.OAI.OneWayLiveness.Pairing.support_sandwich_subset_marked

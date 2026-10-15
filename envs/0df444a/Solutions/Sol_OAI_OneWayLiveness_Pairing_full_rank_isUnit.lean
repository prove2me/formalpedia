-- Prove2me | solution 1 for OAI.OneWayLiveness.Pairing.full_rank_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:45:18.589586+00:00
-- url     : https://prove2.me/submissions/383b4c39-c9da-44cf-b880-f80d4101c44a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Diagram.lean:L158-L170
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.Pairing.full_rank_isUnit. The node keeps its source
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

-- ---- from OAI.Combinatorics.Automata.Rank ----
namespace OAI

namespace OneWayLiveness

namespace Pairing
open scoped Classical
variable {A B C : Type*}

variable [Fintype A] [Fintype B] [Fintype C]

lemma rank_eq_rights (a : Pairing (A ⊕ B)) : rank a = (rights a).card := by
  simpa only [Fintype.card_coe, rank] using Fintype.card_congr (transversalEquiv a)

end Pairing

namespace Pairing
open scoped Classical
variable {P : Type*} {A B C D : Type*}

lemma flip_flip (a : Pairing (A ⊕ B)) : flip (flip a) = a := by
  ext x y
  simp only [flip_link, Sum.swap_swap]

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
lemma full_rank_isUnit (a : Pairing (A ⊕ A)) (h : rank a = Fintype.card A) : IsUnit a := by
  have hl : lefts a = Finset.univ := Finset.eq_univ_of_card _ h
  have hr : lefts (flip a) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hs : lefts (flip a) = rights a := by
      ext i
      simp only [mem_lefts, mem_rights, flip_link, Sum.swap_inl, Sum.swap_inr]
      exact ⟨fun ⟨j, hj⟩ => ⟨j, a.symm hj⟩, fun ⟨j, hj⟩ => ⟨j, a.symm hj⟩⟩
    rw [hs, ← rank_eq_rights, h]
  refine ⟨⟨a, flip a, ?_, ?_⟩, rfl⟩
  · exact compose_flip_eq_identity a (by simp [hl])
  · change compose (flip a) a = identity A
    simpa only [flip_flip] using compose_flip_eq_identity (flip a) (by simp [hr])

end Pairing

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.Pairing
open scoped Classical


theorem solution : type_of% @_root_.OAI.OneWayLiveness.Pairing.full_rank_isUnit := @_root_.OAI.OneWayLiveness.Pairing.full_rank_isUnit

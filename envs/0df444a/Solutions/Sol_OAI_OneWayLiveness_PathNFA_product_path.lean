-- Prove2me | solution 1 for OAI.OneWayLiveness.PathNFA.product_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:14:05.317984+00:00
-- url     : https://prove2.me/submissions/efee5420-28cb-4875-9a22-cf20b6e62960

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/PathNFA.lean:L90-L116
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.PathNFA.product_path. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Automata_Recognition
import Definitions.Def_OAI_Combinatorics_Automata_PathNFA

-- ---- from OAI.Combinatorics.Automata.PathNFA ----
namespace OAI

namespace OneWayLiveness

namespace NMachineOn
variable {Alpha Q : Type} (M : NMachineOn Alpha Q)
end NMachineOn

namespace PathNFA
variable {H : Type}
/-- A numbered path through a product, extended arbitrarily after its endpoint. -/
lemma product_path (w : List (BRel H)) (a b : H) :
    w.prod.holds a b ↔ ∃ p : ℕ → H, p 0 = a ∧ p w.length = b ∧
      ∀ i (hi : i < w.length), w[i].holds (p i) (p (i+1)) := by
  induction w generalizing a with
  | nil =>
    simp only [List.prod_nil, BRel.one_holds, List.length_nil, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, and_true]
    constructor
    · intro h; exact ⟨fun _ => a,rfl,h⟩
    · rintro ⟨p,hp,hq⟩; exact hp.symm.trans hq
  | cons R w ih =>
    simp only [List.prod_cons, BRel.mul_holds]
    constructor
    · rintro ⟨c,hR,hc⟩
      obtain ⟨p,hp,hb,hs⟩ := (ih c).mp hc
      let q : ℕ → H := fun i => match i with | 0 => a | i+1 => p i
      refine ⟨q,rfl,hb,?_⟩
      intro i hi
      cases i with
      | zero => simpa only [q, List.getElem_cons_zero, hp] using hR
      | succ i => exact hs i (by simpa using hi)
    · rintro ⟨p,hp,hb,hs⟩
      refine ⟨p 1,?_,(ih (p 1)).mpr ⟨fun i => p (i+1),rfl,hb,?_⟩⟩
      · rw [← hp]; exact hs 0 (by simp)
      · intro i hi
        exact hs (i+1) (by simpa using hi)

end PathNFA

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.PathNFA


theorem solution : type_of% @_root_.OAI.OneWayLiveness.PathNFA.product_path := @_root_.OAI.OneWayLiveness.PathNFA.product_path

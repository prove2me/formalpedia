-- Prove2me | solution 1 for OAI.OneWayLiveness.PathNFA.accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:17:30.899067+00:00
-- url     : https://prove2.me/submissions/2b086397-ad11-402e-bb0f-8dbfb3b56c2d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/PathNFA.lean:L192-L237
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.PathNFA.accepts_iff. The node keeps its source
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
import Theorems.Thm_OAI_OneWayLiveness_PathNFA_good_step
import Theorems.Thm_OAI_OneWayLiveness_PathNFA_product_path

-- ---- from OAI.Combinatorics.Automata.PathNFA ----
namespace OAI

namespace OneWayLiveness

namespace NMachineOn
variable {Alpha Q : Type} (M : NMachineOn Alpha Q)
end NMachineOn

namespace PathNFA
variable {H : Type}
lemma scanned_letter_cell (w : List (BRel H)) (i : ℕ) (hi : i < w.length) :
    scanned w ⟨i+1,by omega⟩ = .letter w[i] := by
  simp [scanned, show i+1 < w.length+1 by omega]

lemma accepts_iff (positive : Bool) (w : List (BRel H)) :
    machine.Accepts positive w ↔ BRel.live w := by
  constructor
  · rintro ⟨c,hc,ha⟩
    have hr : Relation.ReflTransGen (machine.Step w) (⟨0,by omega⟩,none) c := by
      cases positive with
      | false => exact hc
      | true => exact hc.to_reflTransGen
    have hg : Good w c := by
      clear hc ha
      induction hr with
      | refl => rfl
      | @tail c d hcd hstep ih => exact good_step w c d ih hstep
    have hac : c.2 = accept := ha
    simpa only [Good,hac] using hg
  · rintro ⟨a,b,hprod⟩
    obtain ⟨p,_hp,_hb,hpath⟩ := (product_path w a b).mp hprod
    let cell (i : ℕ) (hi : i ≤ w.length) : NMachineOn.Config (Q := State H) w :=
      (⟨i+1,by omega⟩,path (p i))
    have reach (i : ℕ) (hi : i ≤ w.length) :
        Relation.ReflTransGen (machine.Step w) (cell 0 (by omega)) (cell i hi) := by
      induction i with
      | zero => exact .refl
      | succ i ih =>
        refine (ih (by omega)).tail ?_
        refine ⟨.right,?_,rfl⟩
        change (path (p (i+1)),.right) ∈ rules (path (p i)) (scanned w ⟨i+1,by omega⟩)
        rw [scanned_letter_cell w i (by omega)]
        exact ⟨p (i+1),rfl,hpath i (by omega)⟩
    have first : machine.Step w (⟨0,by omega⟩,none) (cell 0 (by omega)) := by
      refine ⟨.right,?_,rfl⟩
      change (path (p 0),.right) ∈ rules none (scanned w 0)
      simp only [scanned, Fin.val_zero, ↓reduceDIte]
      exact ⟨p 0,rfl⟩
    let last : NMachineOn.Config (Q := State H) w := (⟨w.length+1,by omega⟩,accept)
    have final : machine.Step w (cell w.length le_rfl) last := by
      refine ⟨.stay,?_,rfl⟩
      change (accept,.stay) ∈ rules (path (p w.length)) (scanned w ⟨w.length+1,by omega⟩)
      rw [(scanned_eq_right_iff _ _).mpr rfl]
      exact Set.mem_singleton _
    have hp : Relation.TransGen (machine.Step w) (⟨0,by omega⟩,none) last :=
      (Relation.TransGen.head' first (reach w.length le_rfl)).tail final
    refine ⟨last,?_,rfl⟩
    cases positive with
    | false => exact hp.to_reflTransGen
    | true => exact hp

end PathNFA

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.PathNFA


theorem solution : type_of% @_root_.OAI.OneWayLiveness.PathNFA.accepts_iff := @_root_.OAI.OneWayLiveness.PathNFA.accepts_iff

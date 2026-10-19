-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.collision_root_slots
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:49:42.539925+00:00
-- url     : https://prove2.me/submissions/cad5eb96-d62e-4f5d-a63d-f719c90855a4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionHistories.lean:L71-L90
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.collision_root_slots. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories

-- ---- from OAI.Combinatorics.HoneycombCorridor.CollisionHistories ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem terminal_previous_mem (g : Germ) (w : List Bool) (hw : w ≠ []) :
    (reverseGerm (terminalGerm g w)).1 ∈ traced g w := by
  induction w generalizing g with
  | nil => contradiction
  | cons b w ih =>
      cases w with
      | nil => simp [terminalGerm,reverseGerm,advance,traced]
      | cons c w =>
          exact List.mem_cons_of_mem _ (ih (advance g b) (by simp))

theorem return_slot_ne_outgoing (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1) :
    (terminalGerm g (b :: w)).2 ≠ outgoingSlot g b := by
  cases w with
  | nil =>
      have h : neighbor g.1 (outgoingSlot g b) = g.1 := hc
      exact (neighbor_ne_self _ _ h).elim
  | cons c w =>
      intro hs
      cases w with
      | nil =>
          exact outgoingSlot_ne (advance g b) c hs
      | cons d w =>
          have hm := terminal_previous_mem (advance (advance g b) c) (d :: w) (by simp)
          have he : (reverseGerm (terminalGerm (advance (advance g b) c) (d :: w))).1 =
              (advance g b).1 := by
            change neighbor (terminalGerm g (b :: c :: d :: w)).1
              (terminalGerm g (b :: c :: d :: w)).2 = _
            rw [hc,hs]
            rfl
          rw [he] at hm
          exact (List.nodup_cons.mp (List.nodup_cons.mp hN).2).1 hm

theorem return_slot_ne_incoming (g : Germ) (w : List Bool) (hw : w ≠ [])
    (hc : (terminalGerm g w).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (terminalGerm g w).2 ≠ g.2 := by
  intro hs
  have hm := terminal_previous_mem g w hw
  have he : reverseGerm (terminalGerm g w) = reverseGerm g := by
    congr 1
    exact Prod.ext hc hs
  rw [he] at hm
  exact hback hm

theorem collision_root_slots (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w)) :
    stemGerm (terminalGerm g (b :: w)) (!b) = g ∧
    advance (terminalGerm g (b :: w)) (!b) = advance g b := by
  have h1 := return_slot_ne_outgoing g b w hN hc
  have h2 := return_slot_ne_incoming g (b :: w) (by simp) hc hback
  let t := terminalGerm g (b :: w)
  have ht : t.1 = g.1 := hc
  change stemGerm t (!b) = g ∧ advance t (!b) = advance g b
  change t.2 ≠ outgoingSlot g b at h1
  change t.2 ≠ g.2 at h2
  rcases g with ⟨v,k⟩
  rcases t with ⟨v',l⟩
  simp only at ht
  subst v'
  fin_cases k <;> fin_cases l <;> cases b <;>
    simp [outgoingSlot] at h1 h2 ⊢ <;>
    simp [stemGerm,unusedSlot,advance,outgoingSlot]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.collision_root_slots := @_root_.OAI.PolynomialVacuumBridge.Corridor.collision_root_slots

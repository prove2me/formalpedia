-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.collisionReverse_leaf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:51:20.411563+00:00
-- url     : https://prove2.me/submissions/f4a1857d-038d-49a6-9c9a-0a4cd59ced53

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionHistories.lean:L217-L234
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.collisionReverse_leaf. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_collision_root_slots

-- ---- from OAI.Combinatorics.HoneycombCorridor.CycleSplice ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem stem_reverse_trace (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    traced (stemGerm g b) (b :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse := by
  have hr := traced_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  change g.1 :: traced (advance (stemGerm g b) b) (reverseTurns w) = _
  rw [stem_reverse,hr]

theorem reverse_loop_terminal (g : Germ) (b : Bool) (w : List Bool)
    (hc : terminalGerm g (b :: w) = g) :
    terminalGerm (reverseLoopGerm g b) ((!b) :: reverseTurns w) =
      reverseLoopGerm g b := by
  have hr := terminalGerm_reverse (advance g b) w
  rw [show terminalGerm (advance g b) w = g from hc] at hr
  simpa only [terminalGerm, reverseLoop_advance, reverseGerm_advance_eq] using hr

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.CollisionHistories ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem reverse_return_trace (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w)) :
    traced g ((!b) :: reverseTurns w) =
      g.1 :: (traced (advance g b) w).reverse ∧
    (terminalGerm g ((!b) :: reverseTurns w)).1 = g.1 := by
  let t := terminalGerm g (b :: w)
  obtain ⟨hs,ha⟩ := collision_root_slots g b w hN hc hback
  have ht : terminalGerm t ((!b) :: w) = t := by
    change terminalGerm (advance t (!b)) w = t
    rw [ha]
    rfl
  have hr := stem_reverse_trace t (!b) w ht
  have he := reverse_loop_terminal t (!b) w ht
  simp only [Bool.not_not] at hr he
  rw [hs,ha,hc] at hr
  constructor
  · exact hr
  · have hrev : advance g (!b) = advance (reverseLoopGerm t (!b)) b := by
      have h1 := stem_reverse t (!b)
      rw [hs] at h1
      exact h1.trans (by simpa using (reverseLoop_advance t (!b)).symm)
    change (terminalGerm (advance g (!b)) (reverseTurns w)).1 = _
    rw [hrev]
    change (terminalGerm (reverseLoopGerm t (!b)) (b :: reverseTurns w)).1 = _
    rw [he]
    exact hc

theorem reverseAt_collision (g : Germ) (v : Vertex) (w : List Bool)
    (hN : (traced g w).Nodup) (hv : v ∈ traced g w)
    (ht : (terminalGerm g w).1 = v)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (traced g (reverseAt g v w)).Perm (traced g w) ∧
    (terminalGerm g (reverseAt g v w)).1 = v := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      by_cases hg : g.1 = v
      · have hc : (terminalGerm g (b :: w)).1 = g.1 := ht.trans hg.symm
        obtain ⟨hr,he⟩ := reverse_return_trace g b w hN hc hback
        simp only [reverseAt,ite_eq_left hg]
        rw [hr]
        exact ⟨List.Perm.cons _ (List.reverse_perm _),he.trans hg⟩
      · have hnt := (List.nodup_cons.mp hN)
        have hvt : v ∈ traced (advance g b) w := by
          simpa only [traced,List.mem_cons,eq_comm (a := v),hg,false_or] using hv
        have hbt : (reverseGerm (advance g b)).1 ∉ traced (advance g b) w := by
          simpa only [reverse_advance_vertex] using hnt.1
        obtain ⟨hp,he⟩ := ih (advance g b) hnt.2 hvt ht hbt
        simp only [reverseAt,ite_eq_right hg,traced,terminalGerm]
        exact ⟨List.Perm.cons _ hp,he⟩

theorem collisionReverse_properties (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (ht : (terminalGerm g w).1 ∈ traced g w)
    (hback : (reverseGerm g).1 ∉ traced g w) :
    (traced g (collisionReverse g w)).Perm (traced g w) ∧
    (terminalGerm g (collisionReverse g w)).1 = (terminalGerm g w).1 ∧
    collisionReverse g (collisionReverse g w) = w := by
  obtain ⟨hp,he⟩ := reverseAt_collision g (terminalGerm g w).1 w hN ht rfl hback
  refine ⟨hp,he,?_⟩
  unfold collisionReverse
  rw [he]
  exact reverseAt_involutive _ _ _

theorem collisionReverse_leaf (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hw : w ∈ leaves D g) (hg : (reverseGerm g).1 ∉ D)
    (ht : (terminalGerm g w).1 ∈ D) :
    collisionReverse g w ∈ leaves D g ∧
    (terminalGerm g (collisionReverse g w)).1 ∈ D ∧
    (∀ v, v ∈ traced g (collisionReverse g w) ↔ v ∈ traced g w) ∧
    collisionReverse g (collisionReverse g w) = w := by
  have hs := (stopped_iff_trace D g w).mp ((mem_leaves_iff D g w).mp hw)
  have hm : (terminalGerm g w).1 ∈ traced g w := hs.2.2.resolve_left (not_not.mpr ht)
  have hb : (reverseGerm g).1 ∉ traced g w := fun h => hg (hs.2.1 _ h)
  obtain ⟨hp,he,hinv⟩ := collisionReverse_properties g w hs.1 hm hb
  refine ⟨(mem_leaves_iff _ _ _).mpr ((stopped_iff_trace _ _ _).mpr ?_),he ▸ ht,
    fun v => hp.mem_iff,hinv⟩
  refine ⟨hp.nodup_iff.mpr hs.1,?_,Or.inr ?_⟩
  · intro v hv
    exact hs.2.1 v (hp.mem_iff.mp hv)
  · rw [he]
    exact hp.mem_iff.mpr hm

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.collisionReverse_leaf := @_root_.OAI.PolynomialVacuumBridge.Corridor.collisionReverse_leaf

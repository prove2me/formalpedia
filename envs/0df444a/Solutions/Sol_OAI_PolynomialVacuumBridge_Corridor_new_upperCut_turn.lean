-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.new_upperCut_turn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:30:55.524103+00:00
-- url     : https://prove2.me/submissions/f60eb57b-b73d-497d-af2a-680a69efcf50

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/ConvexCuts.lean:L131-L152
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.new_upperCut_turn. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_convex_excursion_turn_bound
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_upperCut_convex

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryFlux ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem advance_direction (g : Germ) (b : Bool) :
    (directionCode (advance g b) - directionCode g - turnUnit b) % 6 = 0 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    rfl

theorem terminal_direction (g : Germ) (w : List Bool) :
    (directionCode (terminalGerm g w) - directionCode g - turnUnits w) % 6 = 0 := by
  induction w generalizing g with
  | nil => simp [terminalGerm,turnUnits]
  | cons b w ih =>
    have ha := advance_direction g b
    have ht := ih (advance g b)
    simp only [terminalGerm,turnUnits_cons]
    omega

theorem right_cut_direction_one (v : Vertex) (k : Fin 3) (A : ℤ)
    (hv : boxIndex v 1 < A) (hu : A ≤ boxIndex (neighbor v k) 1) :
    directionCode (neighbor v k,k) = 4 := by
  cases v <;> fin_cases k <;>
    simp [boxIndex,neighbor,directionCode] at * <;> omega

theorem right_cut_direction_two (v : Vertex) (k : Fin 3) (A : ℤ)
    (hv : boxIndex v 2 < A) (hu : A ≤ boxIndex (neighbor v k) 2) :
    directionCode (neighbor v k,k) = 5 := by
  cases v <;> fin_cases k <;>
    simp [boxIndex,neighbor,directionCode] at * <;> omega

theorem convex_source_direction_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (w : List Bool) (hw : w ∈ sourceExits D bottomSource) :
    (directionCode (terminalGerm bottomSource w) = 4 → turnUnits w = -2) ∧
    (directionCode (terminalGerm bottomSource w) = 5 → turnUnits w = -1) := by
  have hb := convex_excursion_turn_bound D hD (bottomSource,w)
    ⟨hg,hg',(mem_sourceExits D bottomSource w).mp hw⟩
  change -3 ≤ turnUnits w ∧ turnUnits w ≤ 3 at hb
  have hm := terminal_direction bottomSource w
  rw [show directionCode bottomSource = 0 from rfl,sub_zero] at hm
  constructor <;> intro h <;> rw [h] at hm <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.ConvexCuts ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem upperCut_subset (D : Finset Vertex) (k : Fin 3) (A : ℤ) : upperCut D k A ⊆ D :=
  Finset.filter_subset _ _

theorem new_exit_terminal_inside (D E : Finset Vertex) (hED : E ⊆ D)
    (g : Germ) (w : List Bool) (hw : w ∈ sourceExits E g \ sourceExits D g) :
    (terminalGerm g w).1 ∈ D := by
  classical
  obtain ⟨he,hd⟩ := Finset.mem_sdiff.mp hw
  obtain ⟨hs,ht⟩ := (mem_sourceExits E g w).mp he
  obtain ⟨hn,hm⟩ := stopped_traced E g w hs
  by_contra hout
  apply hd
  exact (mem_sourceExits D g w).mpr
    ⟨stopped_of_trace D g w hn (fun v hv => hED (hm v hv)) hout,hout⟩

theorem bottomSource_mem_upperCut (D : Finset Vertex) (hg : bottomSource.1 ∈ D)
    (k : Fin 3) (A : ℤ) (hA : 0 < A) : bottomSource.1 ∈ upperCut D k A := by
  apply (mem_upperCut _ _ _ _).mpr
  refine ⟨hg,?_⟩
  fin_cases k <;> simpa [bottomSource,boxIndex] using hA

theorem new_upperCut_direction (D : Finset Vertex) (k : Fin 3) (A : ℤ)
    (hg : bottomSource.1 ∈ upperCut D k A) (w : List Bool)
    (hw : w ∈ sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :
    boxIndex (reverseGerm (terminalGerm bottomSource w)).1 k < A ∧
      A ≤ boxIndex (terminalGerm bottomSource w).1 k := by
  classical
  have he := (mem_sourceExits _ _ _).mp (Finset.mem_sdiff.mp hw).1
  have hn : w ≠ [] := by
    intro h
    exact he.2 (by simpa [h,terminalGerm] using hg)
  have hpred := (stopped_traced _ _ _ he.1).2 _ (reverse_first_mem bottomSource w hn)
  have hu := new_exit_terminal_inside D _ (upperCut_subset D k A) _ _ hw
  exact ⟨((mem_upperCut _ _ _ _).mp hpred).2,by
    by_contra hx
    exact he.2 ((mem_upperCut _ _ _ _).mpr ⟨hu,by omega⟩)⟩

theorem new_upperCut_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (A : ℤ) (hA : 0 < A) (k : Fin 3) (w : List Bool)
    (hw : w ∈ sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :
    (k = 1 → turnUnits w = -2) ∧ (k = 2 → turnUnits w = -1) := by
  have hmem := bottomSource_mem_upperCut D hg k A hA
  obtain ⟨hl,hu⟩ := new_upperCut_direction D k A hmem w hw
  have ht := convex_source_direction_turn _ (upperCut_convex D hD k A) hmem
    (fun hm => hg' (upperCut_subset D k A hm)) w (Finset.mem_sdiff.mp hw).1
  constructor
  · intro hk; subst k
    apply ht.1
    have hd := right_cut_direction_one (reverseGerm (terminalGerm bottomSource w)).1
      (terminalGerm bottomSource w).2 A hl
      (by simpa only [reverseGerm,neighbor_neighbor] using hu)
    simpa only [reverseGerm,neighbor_neighbor] using hd
  · intro hk; subst k
    apply ht.2
    have hd := right_cut_direction_two (reverseGerm (terminalGerm bottomSource w)).1
      (terminalGerm bottomSource w).2 A hl
      (by simpa only [reverseGerm,neighbor_neighbor] using hu)
    simpa only [reverseGerm,neighbor_neighbor] using hd

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.new_upperCut_turn := @_root_.OAI.PolynomialVacuumBridge.Corridor.new_upperCut_turn

-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.mem_lost_upperCut
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:29:19.225242+00:00
-- url     : https://prove2.me/submissions/8052f16e-6de1-419d-acb0-2b4d86927565

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/ConvexCuts.lean:L87-L101
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.mem_lost_upperCut. The node keeps its source
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

-- ---- from OAI.Combinatorics.HoneycombCorridor.ConvexCuts ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem upperCut_subset (D : Finset Vertex) (k : Fin 3) (A : ℤ) : upperCut D k A ⊆ D :=
  Finset.filter_subset _ _

theorem sourceExits_restrict_iff (D E : Finset Vertex) (hED : E ⊆ D)
    (g : Germ) (w : List Bool) (hw : w ∈ sourceExits D g) :
    w ∈ sourceExits E g ↔ ∀ v ∈ traced g w, v ∈ E := by
  obtain ⟨hs,ht⟩ := (mem_sourceExits D g w).mp hw
  constructor
  · intro he
    exact (stopped_traced E g w ((mem_sourceExits E g w).mp he).1).2
  · intro he
    have hn := (stopped_traced D g w hs).1
    have hout : (terminalGerm g w).1 ∉ E := fun hm => ht (hED hm)
    exact (mem_sourceExits E g w).mpr ⟨stopped_of_trace E g w hn he hout,hout⟩

theorem mem_lost_upperCut (D : Finset Vertex) (g : Germ) (k : Fin 3) (A : ℤ)
    (w : List Bool) : w ∈ sourceExits D g \ sourceExits (upperCut D k A) g ↔
      w ∈ sourceExits D g ∧ ∃ v ∈ traced g w, A ≤ boxIndex v k := by
  classical
  simp only [Finset.mem_sdiff]
  by_cases hw : w ∈ sourceExits D g
  · simp only [hw,true_and,sourceExits_restrict_iff D _ (upperCut_subset D k A) g w hw]
    have hm := (stopped_traced D g w ((mem_sourceExits D g w).mp hw).1).2
    simp only [mem_upperCut,not_forall,not_and,not_lt]
    constructor
    · rintro ⟨v,hv,hnot⟩
      exact ⟨v,hv,hnot (hm v hv)⟩
    · rintro ⟨v,hv,hA⟩
      exact ⟨v,hv,fun _ => hA⟩
  · simp [hw]

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.mem_lost_upperCut := @_root_.OAI.PolynomialVacuumBridge.Corridor.mem_lost_upperCut

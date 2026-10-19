-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.star_boundary_cycle_turn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:07:59.331243+00:00
-- url     : https://prove2.me/submissions/b337867b-2511-42b3-afb3-c4e25b70e38b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryCharge.lean:L86-L102
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.star_boundary_cycle_turn. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_box_two_faces
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_integer_bounds_fraction
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_simple_polygon_signed_turn
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_tilingCoordinate_index

-- ---- from OAI.Combinatorics.HoneycombCorridor.Polygons ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem simple_polygon_turning : SimplePolygonTurning := by
  intro g w hne hN hc
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g w hne hN hc
  have hsum := simple_polygon_signed_turn g w hne hN hc p ε hp hpne hε hvals
  rcases hε with rfl | rfl
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

namespace Polygon
end Polygon

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Convexity ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem admissiblyConvex_box (D : Finset Vertex) (hD : AdmissiblyConvex D) :
    ∃ lo hi : Fin 3 → ℤ, ∀ v, v ∈ D ↔ BoxMem lo hi v := by
  obtain ⟨lo,hi,h⟩ := hD
  refine ⟨lo,hi,fun v => ?_⟩
  rw [h]
  apply forall_congr'
  intro k
  obtain ⟨a,ha,ha',he⟩ := tilingCoordinate_index v k
  rw [he]
  exact integer_bounds_fraction _ _ _ _ ha ha'

theorem mem_starFaces (D : Finset Vertex) (a : FaceIndex) :
    a ∈ starFaces D ↔ ∃ v ∈ faceVertices a, v ∈ D := by
  simp only [starFaces,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,
    mem_faceVertices]
  aesop

theorem incident_mem_starFaces {D : Finset Vertex} {v : Vertex} (hv : v ∈ D)
    (k : Fin 3) : leftFace (v,k) ∈ starFaces D := by
  apply (mem_starFaces D _).mpr
  exact ⟨v,(mem_faceVertices _ _).mpr ⟨k,rfl⟩,hv⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.FaceBoundary ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem faceBoundaryWord_length (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    (faceBoundaryWord S g n).length = n := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih => simp [faceBoundaryWord,ih]

theorem faceBoundaryWord_terminal (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    terminalGerm g.val (faceBoundaryWord S g n) = ((faceBoundaryNext S)^[n] g).val := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
    simp only [faceBoundaryWord,terminalGerm,Function.iterate_succ_apply]
    exact ih (faceBoundaryNext S g)

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryCharge ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem star_boundary_outside (D : Finset Vertex) (g : FaceBoundary (starFaces D)) :
    g.val.1 ∉ D := by
  intro hv
  exact g.property.1 (incident_mem_starFaces hv g.val.2)

theorem star_boundary_no_double_negative (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (hg : faceBoundaryTurn (starFaces D) g.val = false) :
    faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val = true := by
  classical
  by_contra hn
  have hn' : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val =
      false := by
    cases he : (faceBoundaryTurn (starFaces D)
      (faceBoundaryNext (starFaces D) g).val) <;> simp_all
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp g.property.2
  have hs_mem := (faceBoundaryTurn_false _ _).mp hn'
  have hs_mem' : leftFace (neighbor g.val.1 (g.val.2+1),g.val.2+2) ∈ starFaces D := by
    simpa [faceBoundaryNext,hg,advance,outgoingSlot,add_assoc] using hs_mem
  obtain ⟨s,hs,hs'⟩ := (mem_starFaces D _).mp hs_mem'
  rcases box_two_faces lo hi g.val.1 r s g.val.2 hr hs ((hbox _).mp hr')
    ((hbox _).mp hs') with h | h
  · exact star_boundary_outside D g ((hbox _).mpr h)
  · apply star_boundary_outside D (faceBoundaryNext (starFaces D) g)
    simpa only [faceBoundaryNext,advance,hg,outgoingSlot,Bool.false_eq_true,ite_false]
      using (hbox _).mpr h

theorem star_boundary_turn_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) :
    boundaryCharge (starFaces D) (faceBoundaryNext (starFaces D) g) -
      boundaryCharge (starFaces D) g ≤ turnUnit (faceBoundaryTurn (starFaces D) g.val) := by
  cases hg : faceBoundaryTurn (starFaces D) g.val
  · have hn := star_boundary_no_double_negative D hD g hg
    simp [boundaryCharge,hg,hn,turnUnit]
  · cases hn : faceBoundaryTurn (starFaces D) (faceBoundaryNext (starFaces D) g).val <;>
      simp [boundaryCharge,hg,hn,turnUnit]

theorem star_boundary_word_charge (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    boundaryCharge (starFaces D) ((faceBoundaryNext (starFaces D))^[n] g) -
      boundaryCharge (starFaces D) g ≤ turnUnits (faceBoundaryWord (starFaces D) g n) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,turnUnits]
  | succ n ih =>
    have h₁ := star_boundary_turn_charge D hD g
    have h₂ := ih (faceBoundaryNext (starFaces D) g)
    simp only [faceBoundaryWord,turnUnits,List.map_cons,List.sum_cons,
      Function.iterate_succ_apply] at *
    omega

theorem star_boundary_cycle_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) (hn : 0 < n)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val) :
    turnUnits (faceBoundaryWord (starFaces D) g n) = 6 := by
  have hne : faceBoundaryWord (starFaces D) g n ≠ [] := by
    intro he
    have hl := faceBoundaryWord_length (starFaces D) g n
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have h := star_boundary_word_charge D hD g n
  have he : ((faceBoundaryNext (starFaces D))^[n] g) = g := by
    apply Subtype.ext
    rwa [faceBoundaryWord_terminal] at hc
  rw [he,sub_self] at h
  rcases simple_polygon_turning g.val _ hne hN hc with h' | h' <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.star_boundary_cycle_turn := @_root_.OAI.PolynomialVacuumBridge.Corridor.star_boundary_cycle_turn

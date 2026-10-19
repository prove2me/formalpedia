-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.contour_flat_trace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:41:29.093075+00:00
-- url     : https://prove2.me/submissions/78f984f3-08c4-441f-8c6a-2c31654fa86b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Incidence.lean:L288-L305
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.contour_flat_trace. The node keeps its source
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

-- ---- from OAI.Combinatorics.HoneycombCorridor.PotentialSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem edge_mem_around (S : Finset FaceIndex) (g : Germ) :
    edgeOf g ∈ cellEdges S ↔ leftFace g ∈ S ∨ rightFace g ∈ S := by
  rw [mem_cellEdges]
  rcases canonicalDart_edgeOf g with h | h
  · rw [h]
  · rw [h,rightFace_reverse]
    change rightFace g ∈ S ∨ leftFace g ∈ S ↔ _
    exact or_comm

theorem flat_along_dart (S : Finset FaceIndex) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges S, f (upEnd e) = f (downEnd e))
    (g : Germ) (h : edgeOf g ∈ cellEdges S) : f (neighbor g.1 g.2) = f g.1 := by
  have he := hf (edgeOf g) h
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [edgeOf,upEnd,downEnd,neighbor] at he ⊢ <;> first | exact he.symm | exact he

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem represented_nonzero_edge_mem (S : Finset FaceIndex) (p : FaceIndex →₀ ℤ)
    (hS : p.support ⊆ S) (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (hg : orientedFlow q g ≠ 0) : edgeOf g ∈ cellEdges S := by
  rw [edge_mem_around]
  have h := hp g
  by_contra hn
  simp only [not_or] at hn
  have hz (a : FaceIndex) (ha : a ∉ S) : p a = 0 := by
    by_contra h
    exact ha (hS (Finsupp.mem_support_iff.mpr h))
  rw [hz _ hn.1,hz _ hn.2,sub_self] at h
  exact hg h

theorem contour_step_mem (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (b : Bool) (h : LocalContour q g b) :
    edgeOf (g.1,outgoingSlot g b) ∈ cellEdges p.support := by
  exact represented_nonzero_edge_mem _ p (Finset.Subset.refl _) q hp _
    (contour_outgoing_nonzero q g b h)

theorem contour_flat_trace (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    ∀ v ∈ traced g w, v ∈ cellVertices p.support ∧ f v = f g.1 := by
  induction w generalizing g with
  | nil => simp [traced]
  | cons b w ih =>
      have hE := contour_step_mem p q hp g b hw.1
      have hV := edge_mem_vertex _ _ hE
      have hs : f (advance g b).1 = f g.1 :=
        flat_along_dart _ f hf (g.1,outgoingSlot g b) hE
      simp only [traced,List.mem_cons]
      intro v hv
      rcases hv with rfl | hv
      · exact ⟨hV,rfl⟩
      · obtain ⟨hv',hf'⟩ := ih (advance g b) hw.2 v hv
        exact ⟨hv',hf'.trans hs⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.contour_flat_trace := @_root_.OAI.PolynomialVacuumBridge.Corridor.contour_flat_trace

-- Prove2me | solution 1 for OAI.CannonEmbeddedArc.Arc.DevelopedFaces.circle_packing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T12:52:54.391878+00:00
-- url     : https://prove2.me/submissions/db2e9334-ae49-490e-a404-9d189e00470f

import Mathlib
import Definitions.Def_OAIQ046C000
import Definitions.Def_OAIQ046C001
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_disk_disjoint_of_interior
import Theorems.Thm_OAI_CannonEmbeddedArc_Arc_DevelopedFaces_univalent_triangles

section
-- module Solutions.OAIQ046_CN.Cannon_PlaneTopology_BoundaryBallCover
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι]
variable {F : ι → Arc ℂ} {d : Faces F}

lemma FacialCycle.pair_edge (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v) :
    ∃ i,Spans (F i) u v := by
  rw [C.vertices] at hu hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl
  all_goals first
    | exact (huv rfl).elim
    | exact ⟨C.e,C.spans_e⟩
    | exact ⟨C.e,C.spans_e.symm⟩
    | exact ⟨C.f,C.spans_f⟩
    | exact ⟨C.f,C.spans_f.symm⟩
    | exact ⟨C.g,C.spans_g⟩
    | exact ⟨C.g,C.spans_g.symm⟩

omit [Fintype ι] in
lemma Spans.developed_length {i : ι} {u v : ℂ} (h : Spans (F i) u v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  rcases h with ⟨h0,h1⟩|⟨h0,h1⟩
  · simpa only [h0,h1] using hlen
  · simpa only [h0,h1,dist_comm,add_comm] using hlen

lemma FacialCycle.developed_length (C : FacialCycle F d) {u v : ℂ}
    (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v)
    (z : ℂ → ℂ) (r : ℂ → ℝ)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=r (F i 0)+r (F i 1)) :
    dist (z u) (z v)=r u+r v := by
  obtain ⟨i,hi⟩:=C.pair_edge hu hv huv
  exact hi.developed_length z r (hlen i)

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry CannonTriangleBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

theorem DevelopedFaces.circle_packing_oai (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3) :
    ∃ z : ℂ → ℂ,
      (∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) ∧
      (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) ∧
      ∀ q,Vertex F q → ∀ v,Vertex F v → q≠v →
        B.radius q+B.radius v≤dist (z q) (z v) := by
  obtain ⟨z,C,O,hz,hlen,hpos,ho,hchain,hdis⟩:=B.univalent_triangles hF Q hQ hK hthree
  refine ⟨z,hz,hlen,?_⟩
  intro q hq v hv hqv
  by_cases hqo : q∈faceVertices F out
  · by_cases hvo : v∈faceVertices F out
    · exact (O.developed_length hqo hvo hqv z B.radius hlen).ge
    · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
        (hchain ℤ) hdis hv hq hvo hqv.symm
      have HH:=(disjoint_ball_ball_iff (B.radius_pos v) (B.radius_pos q)).mp H
      simpa only [add_comm,dist_comm] using HH
  · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
      (hchain ℤ) hdis hq hv hqo hqv
    exact (disjoint_ball_ball_iff (B.radius_pos q) (B.radius_pos v)).mp H

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CannonEmbeddedArc.Arc.DevelopedFaces.circle_packing_oai.{u_1} := @OAI.CannonEmbeddedArc.Arc.DevelopedFaces.circle_packing_oai.{u_1}

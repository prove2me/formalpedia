-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.star_boundary_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T13:11:25.051266+00:00
-- url     : https://prove2.me/submissions/c73948bb-afb2-4676-ae40-2051ba9b2790

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/BoundaryContainment.lean:L150-L214
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.star_boundary_endpoint. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_Polygon_trace_left_potential
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_gradient_injective
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_indicator_row_containment
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_integer_bounds_fraction
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_outside_boundary_germ
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_simple_polygon_signed_turn
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_star_boundary_cycle_turn
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_tilingCoordinate_index

-- ---- from OAI.Combinatorics.HoneycombCorridor.Currents ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem local_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (b : Bool) (hl : LocalContour p g b) :
    directedCurrent q (advance g b) = directedCurrent q g ∧
      ∀ k : Fin 3, directedCurrent q (g.1,k) =
        -directedCurrent q g * (orientedFlow p (g.1,k) : ℚ) := by
  have hz (k : Fin 3) :
      (if k = outgoingSlot g b then (1 : ℤ) else 0) -
        (if k = g.2 then 1 else 0) = 0 → directedCurrent q (g.1,k) = 0 := by
    intro h
    have h0 : orientedFlow p (g.1,k) = 0 := (hl k).trans h
    have he := hs (edgeOf (g.1,k)) ((orientedFlow_zero_iff p _).mp h0)
    simp [directedCurrent,he]
  have hsum := hq g.1
  rw [directedCurrent_advance]
  constructor
  · rcases g with ⟨v,k⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases k <;> cases b <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith
  · intro k
    rw [hl k]
    rcases g with ⟨v,l⟩
    have hz0 := hz 0
    have hz1 := hz 1
    have hz2 := hz 2
    fin_cases l <;> cases b <;> fin_cases k <;>
      simp [outgoingSlot,Fin.sum_univ_succ] at hz0 hz1 hz2 hsum ⊢ <;> linarith

theorem word_contour_current (p : EdgeIndex →₀ ℤ) (q : EdgeIndex → ℚ)
    (hq : ConservedCurrent q) (hs : ∀ e, p e = 0 → q e = 0)
    (g : Germ) (w : List Bool) (hw : WordContour p g w) :
    directedCurrent q (terminalGerm g w) = directedCurrent q g ∧
    ∀ e : EdgeIndex, wordFlow g w e ≠ 0 →
      q e = -directedCurrent q g * (p e : ℚ) := by
  induction w generalizing g with
  | nil => simp [terminalGerm,wordFlow]
  | cons b w ih =>
      obtain ⟨hstep,hlocal⟩ := local_contour_current p q hq hs g b hw.1
      obtain ⟨hend,hedge⟩ := ih (advance g b) hw.2
      constructor
      · exact hend.trans hstep
      · intro e he
        by_cases ht : wordFlow (advance g b) w e ≠ 0
        · simpa only [hstep] using hedge e ht
        · have hd : dartFlow (g.1,outgoingSlot g b) e ≠ 0 := by
            simpa only [wordFlow,Finsupp.add_apply,not_not.mp ht,add_zero] using he
          have heq : e = edgeOf (g.1,outgoingSlot g b) := by
            by_contra h
            exact hd (by simp [dartFlow,h])
          subst e
          have h := hlocal (outgoingSlot g b)
          rcases g with ⟨v,k⟩
          cases v <;>
            simp [directedCurrent,dartSign,edgeOf,orientedFlow_up,orientedFlow_down] at h ⊢ <;>
            linarith

theorem simple_cycle_current_scalar (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (q : EdgeIndex → ℚ) (hq : ConservedCurrent q)
    (hs : ∀ e, wordFlow g w e = 0 → q e = 0) :
    ∃ c : ℚ, ∀ e, q e = c * (wordFlow g w e : ℚ) := by
  refine ⟨-directedCurrent q g,?_⟩
  intro e
  by_cases he : wordFlow g w e = 0
  · simp [hs e he,he]
  · exact (word_contour_current _ q hq hs g w
      (simple_closed_word_contour g w hN hc)).2 e he

theorem directedCurrent_gradient (r : FaceIndex → ℚ) (g : Germ) :
    directedCurrent (faceGradient r) g = r (leftFace g) - r (rightFace g) := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [directedCurrent,faceGradient,dartSign,edgeOf,canonicalDart,upEnd,
      leftFace,rightFace,reverseGerm,neighbor]

theorem gradient_conserved (r : FaceIndex → ℚ) : ConservedCurrent (faceGradient r) := by
  intro v
  simp only [directedCurrent_gradient]
  cases v <;> simp [Fin.sum_univ_succ,leftFace,rightFace,reverseGerm,neighbor] <;> ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.PotentialSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem incident_faces_equal (p : FaceIndex →₀ ℤ) (v : Vertex)
    (hp : ∀ k : Fin 3, p (leftFace (v,k)) = p (rightFace (v,k)))
    (k l : Fin 3) : p (leftFace (v,k)) = p (leftFace (v,l)) := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  cases v <;> fin_cases k <;> fin_cases l <;>
    simp [leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Polygons ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

namespace Polygon
theorem potential_spec (P : Polygon) :
    RepresentsFlow P.potential (wordFlow P.germ P.turns) ∧ P.potential ≠ 0 ∧
    (P.orientation = 1 ∨ P.orientation = -1) ∧
    ∀ a, P.potential a = 0 ∨ P.potential a = P.orientation :=
  P.has_indicator.choose_spec.choose_spec

end Polygon

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.CollisionPhase ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem numeric_unused_face (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    2 * f (k + (if !b then 2 else 1)) = ε - turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    simp [turnUnit] at * <;> omega

theorem contour_unused_face (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    2 * p (leftFace (g.1,unusedSlot g b)) = ε - turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hl (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  exact numeric_unused_face f ε hε (fun l => hvals _) g.2 b hl

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.PolygonGeometry ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem RepresentsFlow.rational {p : FaceIndex →₀ ℤ} {q : EdgeIndex →₀ ℤ}
    (hp : RepresentsFlow p q) : faceGradient (toRatFinsupp p) = toRatFinsupp q := by
  funext e
  have h := hp (canonicalDart e)
  rcases e with ⟨⟨i,j⟩,k⟩
  simp only [canonicalDart,upEnd,orientedFlow_up] at h
  simp only [faceGradient,toRatFinsupp_apply]
  exact_mod_cast h.symm

theorem cycle_potential_support_subset (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p r : FaceIndex →₀ ℤ) (s : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) (hr : RepresentsFlow r s)
    (hs : s.support ⊆ (wordFlow g w).support) : r.support ⊆ p.support := by
  have hq : ConservedCurrent (toRatFinsupp s) := by
    rw [← hr.rational]
    exact gradient_conserved _
  obtain ⟨c,hc'⟩ := simple_cycle_current_scalar g w hN hc (toRatFinsupp s) hq (by
    intro e he
    have haz : s e = 0 := by
      by_contra hz
      have hm := hs (Finsupp.mem_support_iff.mpr hz)
      exact (Finsupp.mem_support_iff.mp hm) he
    simp [haz])
  have he : toRatFinsupp r = c • toRatFinsupp p := by
    apply finite_gradient_injective
    funext e
    have hz := congrFun hp.rational e
    have hy := congrFun hr.rational e
    change faceGradient (toRatFinsupp r) e = _
    rw [hy,hc' e]
    simp only [faceGradient,Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]
    rw [← mul_sub]
    exact congrArg (c * ·) hz.symm
  intro a ha
  rw [Finsupp.mem_support_iff] at ha ⊢
  intro hpz
  have h := congrArg (fun t : FaceIndex →₀ ℚ => t a) he
  simp [hpz] at h
  exact ha h

theorem cycle_potential_support_eq (g h : Germ) (w u : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (hu : (traced h u).Nodup) (hd : terminalGerm h u = h)
    (p r : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (hr : RepresentsFlow r (wordFlow h u))
    (hs : (wordFlow g w).support = (wordFlow h u).support) :
    p.support = r.support := by
  apply Finset.Subset.antisymm
  · exact cycle_potential_support_subset h u hu hd r p (wordFlow g w) hr hp hs.le
  · exact cycle_potential_support_subset g w hw hc p r (wordFlow h u) hp hr hs.ge

namespace Polygon

theorem interiorFaces_of_traversal (P : Polygon) (g : Germ) (w : List Bool)
    (hw : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (hE : (wordFlow g w).support = P.val) (p : FaceIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) : P.interiorFaces = p.support := by
  apply cycle_potential_support_eq P.germ g P.turns w P.traversal.2.1
    P.traversal.2.2.1 hw hc P.potential p P.potential_spec.1 hp
  exact P.traversal.2.2.2.trans hE.symm

end Polygon

namespace Polygon

theorem represents (P : Polygon) : RepresentsFlow P.potential (wordFlow P.germ P.turns) :=
  P.potential_spec.1

theorem off_boundary_zero (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    orientedFlow (wordFlow P.germ P.turns) (v,k) = 0 := by
  apply (orientedFlow_zero_iff _ _).mpr
  by_contra hn
  apply hv
  change v ∈ edgeVertices P.val
  apply (mem_edgeVertices _ _).mpr
  exact ⟨k,by rw [← P.traversal.2.2.2]; exact Finsupp.mem_support_iff.mpr hn⟩

theorem off_boundary_faces (P : Polygon) (v : Vertex) (hv : v ∉ P.vertices) (k : Fin 3) :
    P.potential (leftFace (v,k)) = vertexLevel P.potential v ∧
    P.potential (rightFace (v,k)) = vertexLevel P.potential v := by
  have he (l : Fin 3) : P.potential (leftFace (v,l)) = P.potential (rightFace (v,l)) := by
    have h := P.represents (v,l)
    rw [P.off_boundary_zero v hv l] at h
    omega
  have hl := incident_faces_equal P.potential v he k 0
  exact ⟨hl,(he k).symm.trans hl⟩

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

theorem faceBoundaryWord_traced (S : Finset FaceIndex) (g : FaceBoundary S) (n : ℕ) :
    traced g.val (faceBoundaryWord S g n) =
      List.ofFn (fun i : Fin n => ((faceBoundaryNext S)^[i.val] g).val.1) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,traced]
  | succ n ih =>
    simp only [faceBoundaryWord,traced,List.ofFn_succ,Fin.val_zero,Function.iterate_zero,
      id_eq,Fin.val_succ,Function.iterate_succ_apply]
    congr 1
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

theorem box_face_row_interval_0 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up i₁ j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_1 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down i₁ (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_2 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up (i₁+1) (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_3 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down i₁ j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_4 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.up (i₁+1) j)) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval_5 (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (s : Vertex)
    (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi (.down (i₁+1) (j-1))) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [faceVertices,BoxMem,Fin.forall_fin_succ,boxIndex] <;> omega

theorem box_face_row_interval (lo hi : Fin 3 → ℤ) (i₁ i i₂ j : ℤ)
    (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂) (r s : Vertex)
    (hr : r ∈ faceVertices (i₁,j)) (hs : s ∈ faceVertices (i₂,j))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    ∃ v ∈ faceVertices (i,j), BoxMem lo hi v := by
  simp only [faceVertices,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact box_face_row_interval_0 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_1 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_2 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_3 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_4 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'
  · exact box_face_row_interval_5 lo hi i₁ i i₂ j h₁ h₂ s hs hr' hs'

theorem star_face_row_interval (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (i₁ i i₂ j : ℤ) (h₁ : i₁ ≤ i) (h₂ : i ≤ i₂)
    (hf₁ : (i₁,j) ∈ starFaces D) (hf₂ : (i₂,j) ∈ starFaces D) :
    (i,j) ∈ starFaces D := by
  obtain ⟨lo,hi,hbox⟩ := admissiblyConvex_box D hD
  obtain ⟨r,hr,hr'⟩ := (mem_starFaces D _).mp hf₁
  obtain ⟨s,hs,hs'⟩ := (mem_starFaces D _).mp hf₂
  obtain ⟨v,hv,hv'⟩ := box_face_row_interval lo hi i₁ i i₂ j h₁ h₂ r s hr hs
    ((hbox _).mp hr') ((hbox _).mp hs')
  exact (mem_starFaces D _).mpr ⟨v,hv,(hbox _).mpr hv'⟩

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.BoundaryContainment ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem faceBoundary_local (S : Finset FaceIndex) (g : FaceBoundary S) (k : Fin 3) :
    faceIndicator S (leftFace (g.val.1,k)) - faceIndicator S (rightFace (g.val.1,k)) =
    (if k = outgoingSlot g.val (faceBoundaryTurn S g.val) then 1 else 0) -
      (if k = g.val.2 then 1 else 0) := by
  classical
  rcases g with ⟨⟨v,l⟩,h⟩
  simp only [OnFaceBoundary,rightFace_prev] at h
  by_cases ht : leftFace (v,l+1) ∈ S
  · simp only [faceBoundaryTurn,ht,not_true_eq_false,decide_false]
    fin_cases l <;> fin_cases k <;>
      simp_all [faceIndicator,rightFace_prev,outgoingSlot]
  · simp only [faceBoundaryTurn,ht,not_false_eq_true,decide_true]
    fin_cases l <;> fin_cases k <;>
      simp_all [faceIndicator,rightFace_prev,outgoingSlot]

theorem faceBoundaryWord_local (S : Finset FaceIndex) (g : FaceBoundary S)
    (n : ℕ) (q : EdgeIndex →₀ ℤ)
    (hq : WordContour q g.val (faceBoundaryWord S g n)) :
    ∀ v ∈ traced g.val (faceBoundaryWord S g n), ∀ k : Fin 3,
      orientedFlow q (v,k) = faceIndicator S (leftFace (v,k)) -
        faceIndicator S (rightFace (v,k)) := by
  induction n generalizing g with
  | zero => simp [faceBoundaryWord,traced]
  | succ n ih =>
    intro v hv k
    simp only [faceBoundaryWord,traced,List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (hq.1 k).trans (faceBoundary_local S g k).symm
    · exact ih (faceBoundaryNext S g) hq.2 v hv k

theorem faceBoundaryWord_gradient (S : Finset FaceIndex) (g : FaceBoundary S)
    (n : ℕ) (hN : (traced g.val (faceBoundaryWord S g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord S g n) = g.val)
    (e : EdgeIndex) (he : wordFlow g.val (faceBoundaryWord S g n) e ≠ 0) :
    wordFlow g.val (faceBoundaryWord S g n) e =
      faceIndicator S (leftFace (canonicalDart e)) -
        faceIndicator S (rightFace (canonicalDart e)) := by
  have hv : upEnd e ∈ traced g.val (faceBoundaryWord S g n) := by
    have hm : upEnd e ∈ edgeVertices (wordFlow g.val (faceBoundaryWord S g n)).support := by
      apply Finset.mem_biUnion.mpr
      exact ⟨e,Finsupp.mem_support_iff.mpr he,by simp⟩
    rwa [wordFlow_edgeVertices _ _ hN hc,List.mem_toFinset] at hm
  have h := faceBoundaryWord_local S g n _ (simple_closed_word_contour _ _ hN hc)
    _ hv e.2
  rcases e with ⟨⟨i,j⟩,k⟩
  simpa only [upEnd,canonicalDart,orientedFlow_up] using h

theorem star_boundary_potential_contained (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p
      (wordFlow g.val (faceBoundaryWord (starFaces D) g n)))
    (hval : ∀ a, p a = 0 ∨ p a = 1) : p.support ⊆ starFaces D := by
  apply finite_indicator_row_containment p (starFaces D) hval
  · intro i j he
    have h : wordFlow g.val (faceBoundaryWord (starFaces D) g n) ((i,j),0) ≠ 0 := by
      rw [hp.horizontal]
      exact sub_ne_zero.mpr he
    have he' := faceBoundaryWord_gradient (starFaces D) g n hN hc ((i,j),0) h
    rw [hp.horizontal] at he'
    simpa [canonicalDart,upEnd,leftFace,rightFace,reverseGerm,neighbor] using he'
  · exact star_face_row_interval D hD

theorem contour_unused_advance (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (hl : LocalContour q g false) :
    p (leftFace (advance g true)) = p (leftFace (g.1,unusedSlot g false)) := by
  have h := (hp (g.1,unusedSlot g false)).symm.trans (hl (unusedSlot g false))
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [advance,outgoingSlot,unusedSlot,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

theorem star_boundary_trace_outside (D : Finset Vertex)
    (g : FaceBoundary (starFaces D)) (n : ℕ) :
    ∀ v ∈ traced g.val (faceBoundaryWord (starFaces D) g n), v ∉ D := by
  intro v hv
  rw [faceBoundaryWord_traced,List.mem_ofFn] at hv
  obtain ⟨i,rfl⟩ := hv
  exact star_boundary_outside D _

theorem star_boundary_endpoint (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) (hn : 0 < n)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (hg : faceBoundaryTurn (starFaces D) g.val = false)
    (e : Germ) (w : List Bool) (he : e = advance g.val true)
    (hd : ∀ v ∈ traced e w, v ∈ D)
    (hu : (terminalGerm e w).1 ∉ D)
    (hu' : (reverseGerm (terminalGerm e w)).1 ∈ D) :
    (terminalGerm e w).1 ∈ traced g.val (faceBoundaryWord (starFaces D) g n) := by
  classical
  let W := faceBoundaryWord (starFaces D) g n
  have hne : W ≠ [] := by
    intro hx
    have hl := faceBoundaryWord_length (starFaces D) g n
    change W.length = n at hl
    rw [hx] at hl
    simp only [List.length_nil] at hl
    omega
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ := simple_closed_word_indicator g.val W hne hN hc
  have ht := simple_polygon_signed_turn g.val W hne hN hc p ε hp hpne hε hvals
  have ht' := star_boundary_cycle_turn D hD g n hn hN hc
  have heps : ε = 1 := by change turnUnits W = 6 at ht'; rw [ht'] at ht; omega
  subst ε
  have hpS := star_boundary_potential_contained D hD g n hN hc p hp hvals
  let P : Polygon := ⟨(wordFlow g.val W).support,⟨g.val,W,hne,hN,hc,rfl⟩⟩
  have hPv : P.vertices = (traced g.val W).toFinset :=
    wordFlow_edgeVertices g.val W hN hc
  have hPf : P.interiorFaces = p.support :=
    P.interiorFaces_of_traversal g.val W hN hc rfl p hp
  have hdis : ∀ v ∈ traced e w, v ∉ P.vertices := by
    intro v hv hm
    rw [hPv,List.mem_toFinset] at hm
    exact star_boundary_trace_outside D g n v hm (hd v hv)
  have hlocal : LocalContour (wordFlow g.val W) g.val false := by
    have hh := simple_closed_word_contour g.val W hN hc
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    simpa only [W,faceBoundaryWord,hg,WordContour] using hh.1
  have hused := contour_unused_face p 1 (Or.inl rfl) hvals _ hp g.val false hlocal
  have hpone : p (leftFace e) = 1 := by
    rw [he,contour_unused_advance p _ hp g.val hlocal]
    norm_num [turnUnit] at hused
    omega
  have hstart : P.potential (leftFace e) ≠ 0 := by
    apply Finsupp.mem_support_iff.mp
    change leftFace e ∈ P.interiorFaces
    rw [hPf,Finsupp.mem_support_iff,hpone]
    norm_num
  have hend : P.potential (leftFace (terminalGerm e w)) ≠ 0 := by
    rw [P.trace_left_potential e w hdis]
    exact hstart
  by_contra hout
  have hnot : (terminalGerm e w).1 ∉ P.vertices := by
    simpa only [hPv,List.mem_toFinset] using hout
  have hmiss := (outside_boundary_germ D hD (terminalGerm e w).1
    (terminalGerm e w).2 hu hu').1.1
  have hzero : P.potential (leftFace ((terminalGerm e w).1,(terminalGerm e w).2+1)) = 0 := by
    by_contra hz
    have hm : leftFace ((terminalGerm e w).1,(terminalGerm e w).2+1) ∈ P.interiorFaces :=
      Finsupp.mem_support_iff.mpr hz
    rw [hPf] at hm
    exact hmiss (hpS hm)
  rw [(P.off_boundary_faces _ hnot _).1] at hzero
  apply hend
  exact (P.off_boundary_faces _ hnot _).1.trans hzero

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.star_boundary_endpoint := @_root_.OAI.PolynomialVacuumBridge.Corridor.star_boundary_endpoint

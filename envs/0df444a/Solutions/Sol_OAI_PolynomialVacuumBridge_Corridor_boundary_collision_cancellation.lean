-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.boundary_collision_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:54:31.33098+00:00
-- url     : https://prove2.me/submissions/9a8f2515-2a5a-4ffb-88f4-1cce051bca38

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/CollisionCancellation.lean:L149-L174
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.boundary_collision_cancellation. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_Polygon_trace_left_potential
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_collisionReverse_leaf
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_collision_phase
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_collision_root_slots
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_gradient_injective

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

theorem interior_iff_level (P : Polygon) (v : Vertex) :
    v ∈ P.interior ↔ v ∉ P.vertices ∧ vertexLevel P.potential v ≠ 0 := by
  rw [P.mem_interior,mem_cellVertices]
  constructor
  · rintro ⟨⟨k,hk⟩,hv⟩
    refine ⟨hv,?_⟩
    change leftFace (v,k) ∈ P.potential.support at hk
    rw [Finsupp.mem_support_iff] at hk
    rwa [(P.off_boundary_faces v hv k).1] at hk
  · rintro ⟨hv,hl⟩
    exact ⟨⟨0,Finsupp.mem_support_iff.mpr hl⟩,hv⟩

theorem outside_level_zero (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) (v : Vertex) (hv : v ∉ D) :
    vertexLevel P.potential v = 0 := by
  by_contra hn
  have hb : v ∉ P.vertices := fun h => hv ((mem_polygons D P).mp hP h)
  have hi := (P.interior_iff_level v).mpr ⟨hb,hn⟩
  exact hv (hD P hP hi)

theorem outside_port_potential (P : Polygon) (D : Finset Vertex) (hD : Filled D)
    (hP : P ∈ polygons D) (g : Germ) (hg : (reverseGerm g).1 ∉ D) :
    P.potential (leftFace g) = 0 := by
  have hb : (reverseGerm g).1 ∉ P.vertices :=
    fun h => hg ((mem_polygons D P).mp hP h)
  have he := (P.off_boundary_faces (reverseGerm g).1 hb g.2).2
  have hr : rightFace ((reverseGerm g).1,g.2) = leftFace g := by
    change leftFace (reverseGerm (reverseGerm g)) = _
    rw [reverseGerm_reverseGerm]
  rw [hr] at he
  exact he.trans (P.outside_level_zero D hD hP _ hg)

end Polygon
end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.CollisionCancellation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem polygonOfClosed_vertices (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    (polygonOfClosed g w hne hN hc).vertices = (traced g w).toFinset :=
  wordFlow_edgeVertices g w hN hc

theorem mem_traced_split (g : Germ) (w : List Bool) (v : Vertex) (hv : v ∈ traced g w) :
    ∃ u b t, w = u ++ (b :: t) ∧ (terminalGerm g u).1 = v := by
  induction w generalizing g with
  | nil => simp [traced] at hv
  | cons b w ih =>
      simp only [traced,List.mem_cons] at hv
      rcases hv with hv | hv
      · exact ⟨[],b,w,rfl,hv.symm⟩
      · obtain ⟨u,c,t,he,ht⟩ := ih (advance g b) hv
        exact ⟨b::u,c,t,by simp [he],ht⟩

theorem reverseAt_append (g : Germ) (v : Vertex) (u w : List Bool)
    (hv : v ∉ traced g u) :
    reverseAt g v (u ++ w) = u ++ reverseAt (terminalGerm g u) v w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih =>
      have hg : g.1 ≠ v := fun h => hv (by simp [traced,h])
      have ht : v ∉ traced (advance g b) u := fun h => hv (List.mem_cons_of_mem _ h)
      simp only [List.cons_append,reverseAt,ite_eq_right hg,terminalGerm,ih _ ht]

theorem split_back_not_mem (g : Germ) (u : List Bool) (b : Bool) (w : List Bool)
    (hN : (traced g (u ++ b :: w)).Nodup)
    (hg : (reverseGerm g).1 ∉ traced g (u ++ b :: w)) :
    (reverseGerm (terminalGerm g u)).1 ∉ traced (terminalGerm g u) (b :: w) := by
  cases u with
  | nil => simpa only [List.nil_append,terminalGerm] using hg
  | cons c u =>
      have hm := terminal_previous_mem g (c :: u) (by simp)
      rw [traced_append] at hN
      have hd := (List.nodup_append.mp hN).2.2
      exact fun ht => hd _ hm _ ht rfl

theorem root_collision_cancels (g : Germ) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup)
    (hc : (terminalGerm g (b :: w)).1 = g.1)
    (hback : (reverseGerm g).1 ∉ traced g (b :: w))
    (hz : ∀ (P : Polygon), P.vertices = (traced g (b :: w)).toFinset →
      P.potential (leftFace g) = 0) :
    wordWeight (b :: w) + wordWeight ((!b) :: reverseTurns w) = 0 := by
  let t := terminalGerm g (b :: w)
  obtain ⟨hs,ha⟩ := collision_root_slots g b w hN hc hback
  have htr : traced t ((!b) :: w) = traced g (b :: w) := by
    change t.1 :: traced (advance t (!b)) w = _
    rw [ha,hc]
    rfl
  have hNt : (traced t ((!b) :: w)).Nodup := htr ▸ hN
  have hct : terminalGerm t ((!b) :: w) = t := by
    change terminalGerm (advance t (!b)) w = _
    rw [ha]
    rfl
  let P := polygonOfClosed t ((!b) :: w) (by simp) hNt hct
  have hPv : P.vertices = (traced g (b :: w)).toFinset := by
    rw [polygonOfClosed_vertices,htr]
  have hPz := hz P hPv
  obtain ⟨p,ε,hp,hpne,hε,hvals⟩ :=
    simple_closed_word_indicator t ((!b) :: w) (by simp) hNt hct
  have hPs := P.interiorFaces_of_traversal t ((!b) :: w) hNt hct rfl p hp
  have hpz : p (leftFace g) = 0 := by
    apply Finsupp.notMem_support_iff.mp
    rw [← hPs]
    exact Finsupp.notMem_support_iff.mpr hPz
  have hr := collision_phase t (!b) w p ε hNt hct hp hpne hε hvals
  have he : (t.1,unusedSlot t (!b)) = g := hs
  simp only [Bool.not_not,he,hpz,ite_eq_left] at hr
  exact hr

theorem boundary_collision_pair (D : Finset Vertex) (g : Germ) (w : List Bool)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D)
    (hw : w ∈ leaves D g) (ht : (terminalGerm g w).1 ∈ D) :
    wordWeight w + wordWeight (collisionReverse g w) = 0 := by
  have hstop := (stopped_iff_trace D g w).mp ((mem_leaves_iff D g w).mp hw)
  have hmem : (terminalGerm g w).1 ∈ traced g w :=
    hstop.2.2.resolve_left (not_not.mpr ht)
  obtain ⟨u,b,t,rfl,hroot⟩ := mem_traced_split g w (terminalGerm g w).1 hmem
  have hN := hstop.1
  rw [traced_append] at hN
  have hna := List.nodup_append.mp hN
  have hb : (reverseGerm (terminalGerm g u)).1 ∉ traced (terminalGerm g u) (b :: t) :=
    split_back_not_mem g u b t hstop.1 (fun h => hg (hstop.2.1 _ h))
  have hct : (terminalGerm (terminalGerm g u) (b :: t)).1 = (terminalGerm g u).1 := by
    rw [← terminalGerm_append]
    exact hroot.symm
  have hzero : wordWeight (b :: t) + wordWeight ((!b) :: reverseTurns t) = 0 := by
    apply root_collision_cancels (terminalGerm g u) b t hna.2.1 hct hb
    intro P hPv
    have hPD : P ∈ polygons D := by
      apply (mem_polygons D P).mpr
      rw [hPv]
      intro v hv
      exact hstop.2.1 v (by rw [traced_append]; exact List.mem_append_right _ (List.mem_toFinset.mp hv))
    have hdis : ∀ v ∈ traced g u, v ∉ P.vertices := by
      intro v hv hm
      rw [hPv,List.mem_toFinset] at hm
      exact hna.2.2 _ hv _ hm rfl
    rw [P.trace_left_potential g u hdis]
    exact P.outside_port_potential D hD hPD g hg
  have hnot : (terminalGerm g (u ++ b :: t)).1 ∉ traced g u := by
    intro hm
    apply hna.2.2 _ hm _ _ rfl
    rw [← hroot]
    simp [traced]
  unfold collisionReverse
  rw [reverseAt_append g _ u (b :: t) hnot]
  have he : (terminalGerm g u).1 = (terminalGerm g (u ++ b :: t)).1 := hroot
  simp only [reverseAt,ite_eq_left he,wordWeight_append]
  rw [← mul_add,hzero,mul_zero]

private theorem collision_subsum_zero (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) (S : Finset (List Bool))
    (hS : ∀ w ∈ S, w ∈ leaves D g ∧ (terminalGerm g w).1 ∈ D)
    (hrev : ∀ w ∈ S, collisionReverse g w ∈ S) :
    (∑ w ∈ S, wordWeight w) = 0 := by
  apply Finset.sum_involution (fun w _ => collisionReverse g w)
  · intro w hw
    exact boundary_collision_pair D g w hD hg (hS w hw).1 (hS w hw).2
  · intro w hw hn he
    apply hn
    have h := boundary_collision_pair D g w hD hg (hS w hw).1 (hS w hw).2
    rw [he] at h
    linear_combination (1 / 2 : ℂ) * h
  · exact hrev
  · intro w hw
    exact (collisionReverse_leaf D g w (hS w hw).1 hg (hS w hw).2).2.2.2

theorem boundary_collision_cancellation (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    collisionSum D g = 0 ∧ ∀ v : Vertex,
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D ∧ v ∈ traced g w
        then wordWeight w else 0) = 0 := by
  classical
  constructor
  · unfold collisionSum
    rw [← Finset.sum_filter]
    apply collision_subsum_zero D g hD hg
    · intro w hw
      exact Finset.mem_filter.mp hw
    · intro w hw
      obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
      have h := collisionReverse_leaf D g w hw hg ht
      exact Finset.mem_filter.mpr ⟨h.1,h.2.1⟩
  · intro v
    rw [← Finset.sum_filter]
    apply collision_subsum_zero D g hD hg
    · intro w hw
      have h := Finset.mem_filter.mp hw
      exact ⟨h.1,h.2.1⟩
    · intro w hw
      obtain ⟨hw,ht,hv⟩ := Finset.mem_filter.mp hw
      have h := collisionReverse_leaf D g w hw hg ht
      exact Finset.mem_filter.mpr ⟨h.1,h.2.1,(h.2.2.1 v).mpr hv⟩
end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.boundary_collision_cancellation := @_root_.OAI.PolynomialVacuumBridge.Corridor.boundary_collision_cancellation

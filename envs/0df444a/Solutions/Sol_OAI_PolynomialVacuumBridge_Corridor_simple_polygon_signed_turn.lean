-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.simple_polygon_signed_turn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:46:13.520262+00:00
-- url     : https://prove2.me/submissions/6b4ee237-ce6d-4ac1-beda-13bf28a2bf70

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Polygons.lean:L15-L37
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.simple_polygon_signed_turn. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_cell_euler_of_exact
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_conserved_finite_potential
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_contour_flat_trace
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_gradient_injective
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_nonboundary_cellCurvature
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_potential_supported_on_cycle_cells
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_transpose_incidence_kernel

-- ---- from OAI.Combinatorics.HoneycombCorridor.Currents ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

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

theorem edge_mem_around (S : Finset FaceIndex) (g : Germ) :
    edgeOf g ∈ cellEdges S ↔ leftFace g ∈ S ∨ rightFace g ∈ S := by
  rw [mem_cellEdges]
  rcases canonicalDart_edgeOf g with h | h
  · rw [h]
  · rw [h,rightFace_reverse]
    change rightFace g ∈ S ∨ leftFace g ∈ S ↔ _
    exact or_comm

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem extendOn_support {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) : (extendOn S f).support ⊆ S := by
  intro a ha
  by_contra h
  exact (Finsupp.mem_support_iff.mp ha) (extendOn_apply_not_mem S f a h)

theorem extendOn_injective {α : Type*} [DecidableEq α] (S : Finset α) :
    Function.Injective (extendOn S) := by
  intro f g h
  funext a
  have he := congrArg (fun t : α →₀ ℚ => t a) h
  simpa using he

theorem extendOn_restrict {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α →₀ ℚ) (h : f.support ⊆ S) : extendOn S (fun a => f a) = f := by
  ext a
  by_cases ha : a ∈ S
  · exact extendOn_apply_mem S (fun a => f a) ⟨a,ha⟩
  · rw [extendOn_apply_not_mem S _ a ha]
    by_contra hf
    exact ha (h (Finsupp.mem_support_iff.mpr (Ne.symm hf)))

theorem rationalBoundary_up (q : EdgeIndex →₀ ℚ) (i j : ℤ) :
    rationalBoundary q (.up i j) = q ((i,j),0) + q ((i,j),1) + q ((i,j),2) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      fin_cases k <;>
        simp [rationalBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem rationalBoundary_down (q : EdgeIndex →₀ ℚ) (i j : ℤ) :
    rationalBoundary q (.down i j) =
      -(q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by omega
      fin_cases k <;>
        simp [rationalBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

theorem rationalBoundary_apply (q : EdgeIndex →₀ ℚ) (v : Vertex) :
    rationalBoundary q v = ∑ k : Fin 3, directedCurrent q (v,k) := by
  cases v <;> simp [rationalBoundary_up,rationalBoundary_down,Fin.sum_univ_succ,
    directedCurrent,dartSign,edgeOf] <;> ring

theorem rationalBoundary_eq_zero (q : EdgeIndex →₀ ℚ) :
    rationalBoundary q = 0 ↔ ConservedCurrent q := by
  simp only [ConservedCurrent,← rationalBoundary_apply,DFunLike.ext_iff,Finsupp.zero_apply]

theorem extendOn_eq_sum {α : Type*} [DecidableEq α] (S : Finset α) (f : S → ℚ) :
    extendOn S f = ∑ a : S, Finsupp.single a.1 (f a) := by
  ext a
  by_cases ha : a ∈ S
  · change extendOn S f (⟨a,ha⟩ : S) = _
    rw [extendOn_apply_mem,Finsupp.finsetSum_apply,Finset.sum_eq_single (⟨a,ha⟩ : S)]
    · simp
    · intro b _ hb
      have h : b.1 ≠ a := fun h => hb (Subtype.ext h)
      simp [h]
    · simp
  · rw [extendOn_apply_not_mem S f a ha,Finsupp.finsetSum_apply]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hb : b.1 ≠ a := fun h => ha (h ▸ b.property)
    simp [hb]

theorem incidence_apply (S : Finset FaceIndex) (q : cellEdges S → ℚ)
    (v : cellVertices S) :
    (incidenceMatrix S).mulVec q v = rationalBoundary (extendOn (cellEdges S) q) v := by
  rw [extendOn_eq_sum,map_sum,Finsupp.finsetSum_apply]
  simp only [Matrix.mulVec,dotProduct,incidenceMatrix,rationalBoundary_single,
    Finsupp.sub_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sub_mul,ite_mul,one_mul,zero_mul,eq_comm]

theorem rationalBoundary_support_cells (S : Finset FaceIndex) (q : EdgeIndex →₀ ℚ)
    (hS : q.support ⊆ cellEdges S) : (rationalBoundary q).support ⊆ cellVertices S := by
  intro v hv
  by_contra hV
  apply (Finsupp.mem_support_iff.mp hv)
  rw [rationalBoundary_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hz : q (edgeOf (v,k)) = 0 := by
    by_contra he
    exact hV (edge_mem_vertex S (v,k) (hS (Finsupp.mem_support_iff.mpr he)))
  simp [directedCurrent,hz]

theorem incidence_zero_iff (S : Finset FaceIndex) (q : cellEdges S → ℚ) :
    (incidenceMatrix S).mulVec q = 0 ↔ ConservedCurrent (extendOn (cellEdges S) q) := by
  rw [← rationalBoundary_eq_zero]
  constructor
  · intro h
    ext v
    by_cases hv : v ∈ cellVertices S
    · have he := congrFun h ⟨v,hv⟩
      simpa only [incidence_apply,Pi.zero_apply,Finsupp.zero_apply] using he
    · change rationalBoundary _ v = 0
      by_contra he
      exact hv (rationalBoundary_support_cells S _ (extendOn_support _ _)
        (Finsupp.mem_support_iff.mpr he))
  · intro h
    funext v
    rw [incidence_apply,h]
    rfl

theorem gradient_zero_off_cells (S : Finset FaceIndex) (r : FaceIndex →₀ ℚ)
    (hr : r.support ⊆ S) (e : EdgeIndex) (he : e ∉ cellEdges S) :
    faceGradient r e = 0 := by
  rw [mem_cellEdges,not_or] at he
  have hz (a : FaceIndex) (ha : a ∉ S) : r a = 0 := by
    by_contra h
    exact ha (hr (Finsupp.mem_support_iff.mpr h))
  simp [faceGradient,hz _ he.1,hz _ he.2]

theorem extend_faceBoundary (S : Finset FaceIndex) (f : S → ℚ) :
    (extendOn (cellEdges S) (cellFaceBoundary S f) : EdgeIndex → ℚ) =
      faceGradient (extendOn S f) := by
  funext e
  by_cases he : e ∈ cellEdges S
  · exact extendOn_apply_mem _ _ ⟨e,he⟩
  · rw [extendOn_apply_not_mem _ _ _ he,
      gradient_zero_off_cells S _ (extendOn_support _ _) e he]

theorem cellFaceBoundary_injective (S : Finset FaceIndex) :
    Function.Injective (cellFaceBoundary S) := by
  intro f g h
  apply extendOn_injective S
  apply finite_gradient_injective
  rw [← extend_faceBoundary,← extend_faceBoundary,h]

theorem cellFaceBoundary_range (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0) :
    (cellFaceBoundary p.support).range = (incidenceMatrix p.support).mulVecLin.ker := by
  ext q
  change (∃ f,cellFaceBoundary p.support f = q) ↔ (incidenceMatrix p.support).mulVec q = 0
  rw [incidence_zero_iff]
  constructor
  · rintro ⟨f,rfl⟩
    rw [extend_faceBoundary]
    exact gradient_conserved _
  · intro hq
    obtain ⟨r,hr⟩ := conserved_finite_potential _ hq
    have hS : r.support ⊆ p.support := by
      apply potential_supported_on_cycle_cells g w hN hc p hp hpne r
      intro e he
      rw [hr]
      exact extendOn_apply_not_mem _ _ _ he
    refine ⟨fun a => r a,?_⟩
    funext e
    change faceGradient (extendOn p.support (fun a => r a)) e = q e
    rw [extendOn_restrict _ r hS,hr]
    exact extendOn_apply_mem _ _ e

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

theorem cycle_vertices_nonempty (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) :
    g.1 ∈ cellVertices p.support := by
  obtain ⟨b,w,rfl⟩ := List.exists_cons_of_ne_nil hne
  have h := (simple_closed_word_contour g (b::w) hN hc).1
  exact edge_mem_vertex _ (g.1,outgoingSlot g b) (contour_step_mem p _ hp g b h)

theorem simple_cycle_cell_euler (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0) :
    ((cellVertices p.support).card : ℤ) - (cellEdges p.support).card + p.support.card = 1 := by
  have : Nonempty (cellVertices p.support) :=
    ⟨⟨g.1,cycle_vertices_nonempty g w hne hN hc p hp⟩⟩
  simpa using cell_euler_of_exact (incidenceMatrix p.support) (cellFaceBoundary p.support)
    (cellFaceBoundary_injective _) (cellFaceBoundary_range g w hN hc p hp hpne)
    (transpose_incidence_kernel g w hne hN hc p hp)

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Curvature ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem leftFace_injective (v : Vertex) : Function.Injective (fun k : Fin 3 => leftFace (v,k)) := by
  intro k l h
  cases v <;> fin_cases k <;> fin_cases l <;> simp [leftFace] at h ⊢ <;> omega

theorem faceCount_incidence (S : Finset FaceIndex) (v : Vertex) :
    faceCount S v = ∑ a ∈ S, if v ∈ faceVertices a then (1 : ℤ) else 0 := by
  classical
  have hpair (a : FaceIndex) : (∑ k : Fin 3, if leftFace (v,k) = a then (1 : ℤ) else 0) =
      if v ∈ faceVertices a then 1 else 0 := by
    by_cases hv : v ∈ faceVertices a
    · obtain ⟨k,hk⟩ := (mem_faceVertices v a).mp hv
      rw [ite_eq_left hv,Finset.sum_eq_single k]
      · simp [hk]
      · intro l _ hl
        have hn : leftFace (v,l) ≠ a := fun h => hl (leftFace_injective v (h.trans hk.symm))
        simp [hn]
      · simp
    · rw [ite_eq_right hv]
      apply Finset.sum_eq_zero
      intro k _
      have hn : leftFace (v,k) ≠ a := fun h => hv ((mem_faceVertices v a).mpr ⟨k,h⟩)
      simp [hn]
  simp_rw [← hpair]
  rw [Finset.sum_comm]
  unfold faceCount
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem upEnd_ne_downEnd (e : EdgeIndex) : upEnd e ≠ downEnd e := by
  rcases e with ⟨⟨i,j⟩,k⟩
  fin_cases k <;> simp [upEnd,downEnd,neighbor]

theorem edgeCount_incidence (S : Finset FaceIndex) (v : Vertex) :
    edgeCount S v = ∑ e ∈ cellEdges S,
      ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ) := by
  classical
  have hpair (e : EdgeIndex) : (∑ k : Fin 3, if edgeOf (v,k) = e then (1 : ℤ) else 0) =
      (if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) := by
    rw [Finset.sum_eq_single e.2]
    · simp only [edgeOf_eq_iff]
      by_cases hu : v = upEnd e
      · simp [hu,upEnd_ne_downEnd]
      · by_cases hd : v = downEnd e
        · simp [hd, Ne.symm (upEnd_ne_downEnd e)]
        · simp [hu,hd]
    · intro k _ hk
      have hn : edgeOf (v,k) ≠ e := fun h => hk (by simpa using congrArg Prod.snd h)
      simp [hn]
    · simp
  simp_rw [← hpair]
  rw [Finset.sum_comm]
  unfold edgeCount
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem faceVertices_card (a : FaceIndex) : (faceVertices a).card = 6 := by
  rcases a with ⟨i,j⟩
  simp [faceVertices]

theorem sum_faceCount (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, faceCount S v = 6 * (S.card : ℤ) := by
  classical
  simp_rw [faceCount_incidence]
  rw [Finset.sum_comm]
  have ha (a : FaceIndex) (hma : a ∈ S) :
      (∑ v ∈ cellVertices S, if v ∈ faceVertices a then (1 : ℤ) else 0) = 6 := by
    rw [← Finset.sum_filter]
    have hF : (cellVertices S).filter (fun v => v ∈ faceVertices a) = faceVertices a := by
      ext v
      simp only [Finset.mem_filter,and_iff_right_iff_imp]
      intro hv
      exact Finset.mem_biUnion.mpr ⟨a,hma,hv⟩
    rw [hF]
    simp [faceVertices_card]
  simp_rw [Finset.sum_congr rfl ha]
  simp [mul_comm]

theorem sum_edgeCount (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, edgeCount S v = 2 * ((cellEdges S).card : ℤ) := by
  classical
  simp_rw [edgeCount_incidence]
  rw [Finset.sum_comm]
  have he (e : EdgeIndex) (hme : e ∈ cellEdges S) :
      (∑ v ∈ cellVertices S,
        ((if v = upEnd e then 1 else 0) + (if v = downEnd e then 1 else 0) : ℤ)) = 2 := by
    have hu : upEnd e ∈ cellVertices S :=
      edge_mem_vertex S (canonicalDart e) (by simpa using hme)
    have hd : downEnd e ∈ cellVertices S :=
      edge_mem_neighbor S (canonicalDart e) (by simpa using hme)
    rw [Finset.sum_add_distrib]
    simp [hu,hd]
  simp_rw [Finset.sum_congr rfl he]
  simp [mul_comm]

theorem sum_cellCurvature (S : Finset FaceIndex) :
    ∑ v ∈ cellVertices S, cellCurvature S v =
      6 * ((cellVertices S).card - (cellEdges S).card + (S.card : ℤ)) := by
  simp only [cellCurvature,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.mul_sum,sum_faceCount,sum_edgeCount]
  simp
  ring

theorem numeric_contour_curvature (f : Fin 3 → ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hf : ∀ l, f l = 0 ∨ f l = ε)
    (k : Fin 3) (b : Bool)
    (h : ∀ l : Fin 3, f l - f (l+2) =
      (if l = k + (if b then 2 else 1) then 1 else 0) - (if l = k then 1 else 0)) :
    6 - 3 * (∑ l : Fin 3, if f l ≠ 0 ∨ f (l+2) ≠ 0 then (1 : ℤ) else 0) +
      (∑ l : Fin 3, if f l ≠ 0 then (1 : ℤ) else 0) = ε * turnUnit b := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have hf0 := hf 0
  have hf1 := hf 1
  have hf2 := hf 2
  clear h hf
  rcases hε with rfl | rfl <;> fin_cases k <;> cases b <;>
    rcases hf0 with hf0 | hf0 <;> rcases hf1 with hf1 | hf1 <;>
    rcases hf2 with hf2 | hf2 <;>
    simp only [Fin.sum_univ_succ] at * <;> simp_all [turnUnit]

theorem contour_cellCurvature (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (b : Bool) (hw : LocalContour q g b) :
    cellCurvature p.support g.1 = ε * turnUnit b := by
  let f : Fin 3 → ℤ := fun l => p (leftFace (g.1,l))
  have hlocal (l : Fin 3) : f l - f (l+2) =
      (if l = g.2 + (if b then 2 else 1) then 1 else 0) - (if l = g.2 then 1 else 0) := by
    have h := (hp (g.1,l)).symm.trans (hw l)
    simp only [f,rightFace_prev,outgoingSlot] at h ⊢
    exact h
  have he := numeric_contour_curvature f ε hε (fun l => hvals _) g.2 b hlocal
  unfold cellCurvature edgeCount faceCount
  simp_rw [edge_mem_around,Finsupp.mem_support_iff,rightFace_prev]
  exact he

theorem contour_curvature_sum (p : FaceIndex →₀ ℤ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (hvals : ∀ a, p a = 0 ∨ p a = ε)
    (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    ((traced g w).map (cellCurvature p.support)).sum = ε * turnUnits w := by
  induction w generalizing g with
  | nil => simp [traced,turnUnits]
  | cons b w ih =>
      simp only [traced,List.map_cons,List.sum_cons,turnUnits,List.map_cons,List.sum_cons]
      rw [contour_cellCurvature p ε hε hvals q hp g b hw.1,ih _ hw.2]
      simp only [turnUnits]
      ring

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- from OAI.Combinatorics.HoneycombCorridor.Polygons ----
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem simple_polygon_signed_turn (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (ε : ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (hpne : p ≠ 0) (hε : ε = 1 ∨ ε = -1)
    (hvals : ∀ a, p a = 0 ∨ p a = ε) : ε * turnUnits w = 6 := by
  have hEuler := simple_cycle_cell_euler g w hne hN hc p hp hpne
  have hw := simple_closed_word_contour g w hN hc
  have hsub : (traced g w).toFinset ⊆ cellVertices p.support := by
    intro v hv
    exact (contour_flat_trace p (wordFlow g w) hp (fun _ => 0)
      (by intros; rfl) g w hw v (List.mem_toFinset.mp hv)).1
  have hsum : (∑ v ∈ cellVertices p.support,cellCurvature p.support v) = ε * turnUnits w := by
    calc
      _ = ∑ v ∈ (traced g w).toFinset,cellCurvature p.support v := by
        symm
        apply Finset.sum_subset hsub
        intro v hv hnot
        exact nonboundary_cellCurvature g w hc p hp v hv
          (by simpa only [List.mem_toFinset] using hnot)
      _ = ((traced g w).map (cellCurvature p.support)).sum := List.sum_toFinset _ hN
      _ = _ := contour_curvature_sum p ε hε hvals (wordFlow g w) hp g w hw
  rw [sum_cellCurvature,hEuler,mul_one] at hsum
  exact hsum.symm

namespace Polygon
end Polygon

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.simple_polygon_signed_turn := @_root_.OAI.PolynomialVacuumBridge.Corridor.simple_polygon_signed_turn

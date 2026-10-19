-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.transpose_incidence_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:42:48.571248+00:00
-- url     : https://prove2.me/submissions/00fb9395-af27-4a30-b89a-9fee9bd9ff26

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/Incidence.lean:L315-L362
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.transpose_incidence_kernel. The node keeps its source
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
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_cell_flat_zero_boundary
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_contour_flat_trace

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
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem extendOn_support {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) : (extendOn S f).support ⊆ S := by
  intro a ha
  by_contra h
  exact (Finsupp.mem_support_iff.mp ha) (extendOn_apply_not_mem S f a h)

theorem transpose_incidence_apply (S : Finset FaceIndex) (f : cellVertices S → ℚ)
    (e : cellEdges S) :
    (incidenceMatrix S).transpose.mulVec f e =
      f ⟨upEnd e,cell_upEnd S e⟩ - f ⟨downEnd e,cell_downEnd S e⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incidenceMatrix, sub_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single ⟨upEnd e,cell_upEnd S e⟩]
    · simp
    · intro b _ hb
      have h : b.1 ≠ upEnd e := fun h => hb (Subtype.ext h)
      simp [h]
    · simp
  · rw [Finset.sum_eq_single ⟨downEnd e,cell_downEnd S e⟩]
    · simp
    · intro b _ hb
      have h : b.1 ≠ downEnd e := fun h => hb (Subtype.ext h)
      simp [h]
    · simp

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

theorem transpose_incidence_kernel (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) :
    (incidenceMatrix p.support).transpose.mulVecLin.ker =
      Submodule.span ℚ {(1 : cellVertices p.support → ℚ)} := by
  have hg : g.1 ∈ cellVertices p.support := cycle_vertices_nonempty g w hne hN hc p hp
  ext f
  change (incidenceMatrix p.support).transpose.mulVec f = 0 ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    let fhat := extendOn (cellVertices p.support) f
    have hflat : ∀ e ∈ cellEdges p.support, fhat (upEnd e) = fhat (downEnd e) := by
      intro e he
      have heq := congrFun h ⟨e,he⟩
      rw [transpose_incidence_apply] at heq
      have h1 := cell_upEnd p.support (⟨e,he⟩ : cellEdges p.support)
      have h2 := cell_downEnd p.support (⟨e,he⟩ : cellEdges p.support)
      simpa only [fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left h1,dite_eq_left h2] using
        sub_eq_zero.mp heq
    have htrace := contour_flat_trace p (wordFlow g w) hp fhat hflat g w
      (simple_closed_word_contour g w hN hc)
    let c : ℚ := fhat g.1
    let diff : Vertex →₀ ℚ := extendOn (cellVertices p.support) (fun a => f a - c)
    have hdiff (a : cellVertices p.support) : diff a = f a - c :=
      extendOn_apply_mem _ _ a
    have hd : diff = 0 := by
      apply cell_flat_zero_boundary g w hc p hp diff (extendOn_support _ _)
      · intro e he
        have h1 := cell_upEnd p.support (⟨e,he⟩ : cellEdges p.support)
        have h2 := cell_downEnd p.support (⟨e,he⟩ : cellEdges p.support)
        have he' := congrArg (fun x : ℚ => x-c) (hflat e he)
        simpa only [diff,fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left h1,dite_eq_left h2] using he'
      · intro v hv
        obtain ⟨hv',he⟩ := htrace v hv
        change fhat v = c at he
        have he' : f ⟨v,hv'⟩ = c := by
          simpa only [fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left hv'] using he
        simp only [diff,extendOn,Finsupp.onFinset_apply,dite_eq_left hv',he',sub_self]
    refine ⟨c,?_⟩
    funext a
    have he := congrArg (fun z : Vertex →₀ ℚ => z a) hd
    simp only [diff,extendOn,Finsupp.onFinset_apply,dite_eq_left a.property,Finsupp.zero_apply] at he
    simpa only [Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one] using (sub_eq_zero.mp he).symm
  · rintro ⟨c,rfl⟩
    funext e
    rw [transpose_incidence_apply]
    simp

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.transpose_incidence_kernel := @_root_.OAI.PolynomialVacuumBridge.Corridor.transpose_incidence_kernel

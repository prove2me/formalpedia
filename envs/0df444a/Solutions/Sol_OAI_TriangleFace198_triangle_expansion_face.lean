-- Prove2me | solution 1 for OAI.TriangleFace198.triangle_expansion_face
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:59:03.706711+00:00
-- url     : https://prove2.me/submissions/41b491ae-96f1-4148-a0d5-3a819267cd72

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TriangleFace/Main.lean:L51-L68
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TriangleFace198.triangle_expansion_face.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TriangleFace198_triangle_expansion_face) verbatim and is proved by it.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_TriangleExpansion
import Theorems.Thm_OAI_CanonicalFace198_image_minFace
import Theorems.Thm_OAI_TriangleFace198_expansion_image_eq
import Theorems.Thm_OAI_TriangleFace198_expansion_image_extreme

-- ---- from OAI.Combinatorics.TriangleFace.Labels ----
namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem labels_of_degree_three {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (v : V)
    (hdeg : Fintype.card {e : E // G.Incident v e} = 3) :
    ∃ c : E → Fin 3, LocalLabels G v c := by
  classical
  let q : {e : E // G.Incident v e} ≃ Fin 3 := Fintype.equivFinOfCardEq hdeg
  let c : E → Fin 3 := fun e => if h : G.Incident v e then q ⟨e,h⟩ else 0
  refine ⟨c, ?_⟩
  intro i
  refine ⟨(q.symm i).val, ⟨(q.symm i).property, ?_⟩, ?_⟩
  · simp [c, (q.symm i).property]
  · intro e he
    have hq : q ⟨e,he.1⟩ = i := by simpa [c,he.1] using he.2
    exact congrArg Subtype.val (q.injective (hq.trans (q.apply_symm_apply i).symm))

end TriangleFace198
end

end OAI

-- ---- from OAI.Combinatorics.TriangleFace.AffineMaps ----
namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem restriction_extension (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (x : E → ℝ) :
    oldRestriction (localExtension G c v hc x) = x := rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem localExtension_injective (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) : Function.Injective (localExtension G c v hc) := by
  intro x y h
  exact congrArg (oldRestriction : (E ⊕ Fin 3 → ℝ) →ₗ[ℝ] (E → ℝ)) h

end TriangleFace198
end

end OAI

-- ---- from OAI.Combinatorics.TriangleFace.Main ----
namespace OAI

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem local_face {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) :
    let H := triangleExpansion G c v
    let f := localExtension G c v hc
    let Q := {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1}
    f '' G.polytope = Q ∧
    Convex ℝ Q ∧ IsExtreme ℝ H.polytope Q ∧
    (∀ x, oldRestriction (f x) = x) ∧
    (∀ y ∈ Q, f (oldRestriction y) = y) ∧
    (∀ x e, f x (Sum.inl e) = x e) ∧
    (∀ x i, f x (Sum.inr i) = x (localEdge G c v hc i)) ∧
    (∀ x, (∀ e, x e = (1/3 : ℝ)) → ∀ e, f x e = (1/3 : ℝ)) ∧
    (∀ x ∈ G.polytope, CanonicalFace198.minFace H.polytope (f x) = f '' CanonicalFace198.minFace G.polytope x) := by
  dsimp only
  have him := expansion_image_eq G c v hc
  have hex := expansion_image_extreme G c v hc
  refine ⟨him, ?_, ?_, restriction_extension G c v hc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← him]
    exact (convex_convexHull ℝ (Set.range G.indicator)).linear_image (localExtension G c v hc)
  · rwa [← him]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := him.symm ▸ hy
    rfl
  · intro x e
    rfl
  · intro x i
    rfl
  · intro x hx e
    rcases e with e | i
    · exact hx e
    · exact hx (localEdge G c v hc i)
  · intro x hx
    exact (CanonicalFace198.image_minFace
      (localExtension G c v hc).toAffineMap (localExtension_injective G c v hc)
      (convex_convexHull ℝ (Set.range G.indicator))
      (convex_convexHull ℝ (Set.range (triangleExpansion G c v).indicator)) hex hx).symm

theorem triangle_expansion_face {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (v : V)
    (hdeg : Fintype.card {e : E // G.Incident v e} = 3)
    (_hmatching : Nonempty G.Matching) :
    ∃ (c : E → Fin 3) (hc : LocalLabels G v c),
      let H := triangleExpansion G c v
      let f := localExtension G c v hc
      let Q := {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1}
      f '' G.polytope = Q ∧
      Convex ℝ Q ∧ IsExtreme ℝ H.polytope Q ∧
      (∀ x, oldRestriction (f x) = x) ∧
      (∀ y ∈ Q, f (oldRestriction y) = y) ∧
      (∀ x e, f x (Sum.inl e) = x e) ∧
      (∀ x i, f x (Sum.inr i) = x (localEdge G c v hc i)) ∧
      (∀ x, (∀ e, x e = (1/3 : ℝ)) → ∀ e, f x e = (1/3 : ℝ)) ∧
      (∀ x ∈ G.polytope, CanonicalFace198.minFace H.polytope (f x) = f '' CanonicalFace198.minFace G.polytope x) := by
  obtain ⟨c,hc⟩ := labels_of_degree_three G v hdeg
  exact ⟨c,hc,local_face G c v hc⟩

end TriangleFace198
end

end OAI

-- ---- mission target ----
open OAI OAI.TriangleFace198
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

namespace OAI
namespace TriangleFace198
theorem _root_.solution {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (v : V)
    (hdeg : Fintype.card {e : E // G.Incident v e} = 3)
    (_hmatching : Nonempty G.Matching) :
    ∃ (c : E → Fin 3) (hc : LocalLabels G v c),
      let H := triangleExpansion G c v
      let f := localExtension G c v hc
      let Q := {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1}
      f '' G.polytope = Q ∧
      Convex ℝ Q ∧ IsExtreme ℝ H.polytope Q ∧
      (∀ x, oldRestriction (f x) = x) ∧
      (∀ y ∈ Q, f (oldRestriction y) = y) ∧
      (∀ x e, f x (Sum.inl e) = x e) ∧
      (∀ x i, f x (Sum.inr i) = x (localEdge G c v hc i)) ∧
      (∀ x, (∀ e, x e = (1/3 : ℝ)) → ∀ e, f x e = (1/3 : ℝ)) ∧
      (∀ x ∈ G.polytope, CanonicalFace198.minFace H.polytope (f x) = f '' CanonicalFace198.minFace G.polytope x) := by
  first
    | exact OAI.TriangleFace198.triangle_expansion_face G v hdeg _hmatching
    | exact OAI.TriangleFace198.triangle_expansion_face
    | (apply OAI.TriangleFace198.triangle_expansion_face <;> assumption)
    | (intros; apply OAI.TriangleFace198.triangle_expansion_face <;> assumption)
end TriangleFace198
end OAI

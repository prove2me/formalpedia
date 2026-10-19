-- Prove2me | solution 1 for OAI.Saxl.pieri_strip_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:48:39.086799+00:00
-- url     : https://prove2.me/submissions/faa98395-563d-41ec-8d7e-f5591a7abb13

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StripExtension.lean:L15-L35
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.pieri_strip_surjective. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Theorems.Thm_OAI_Saxl_pieri_strip_restriction
import Theorems.Thm_OAI_Saxl_specht_irreducible

-- ---- from OAI.RepresentationTheory.Saxl.StripExtension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma pieri_strip_surjective {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, Function.Surjective F ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  obtain ⟨F,hF,he⟩ := pieri_strip_restriction s t hs
  let E : Representation.IntertwiningMap
      ((spechtRep t).comp (Equiv.Perm.viaEmbeddingHom (tableauInclusion s t hs.1)))
      (spechtRep s) :=
    { toLinearMap := F
      isIntertwining' := by
        intro h
        apply LinearMap.ext
        intro x
        exact he _ h (fun k => Equiv.Perm.viaEmbedding_apply _ _ k) x }
  have hE : E ≠ 0 := by
    intro hz
    exact hF (congrArg Representation.IntertwiningMap.toLinearMap hz)
  have := specht_irreducible s
  exact ⟨F, (Representation.IsIrreducible.surjective_or_eq_zero E).resolve_right hE, he⟩

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.pieri_strip_surjective := @_root_.OAI.Saxl.pieri_strip_surjective

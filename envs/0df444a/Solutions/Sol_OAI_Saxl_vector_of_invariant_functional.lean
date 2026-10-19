-- Prove2me | solution 1 for OAI.Saxl.vector_of_invariant_functional
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:06:04.400002+00:00
-- url     : https://prove2.me/submissions/79e50813-e7a4-430f-be03-9a55febcef0f

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/YoungRule.lean:L95-L115
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.vector_of_invariant_functional. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Definitions.Def_OAI_RepresentationTheory_Saxl_HorizontalRemoval
import Definitions.Def_OAI_RepresentationTheory_Saxl_YoungRule

-- ---- from OAI.RepresentationTheory.Saxl.YoungRule ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/
/- The actual constructive sufficiency step in Young's rule. No tableau,
Pieri, or representation hypothesis is assumed by this combinatorial theorem. -/
lemma vector_of_invariant_functional {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (l : Module.Dual ℂ (Specht t)) (hl : l ≠ 0)
    (he : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ∀ x, l (spechtRep t g x) = l x) :
    ∃ y : Specht t, y ≠ 0 ∧ ∀ g : Equiv.Perm (Fin n), a ∘ g = a → spechtRep t g y = y := by
  let e := spechtSelfDual t
  refine ⟨e.symm l, ?_, ?_⟩
  · intro hz
    exact hl (e.symm.injective (hz.trans (map_zero _).symm))
  · intro g hg
    have hi : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a := by
      funext i
      have hh := congrFun hg (g⁻¹ i)
      simpa using hh.symm
    have hdual : (spechtRep t).dual g l = l := by
      apply LinearMap.ext
      intro x
      exact he g⁻¹ hi x
    have hh := LinearMap.congr_fun (e.symm.isIntertwining' g) l
    change e.symm ((spechtRep t).dual g l) = spechtRep t g (e.symm l) at hh
    rw [hdual] at hh
    exact hh.symm

/- Young's sufficiency in the exact form needed for the repeated-row quotient:
a dominant Specht has a nonzero invariant functional for a word of the
prescribed content. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.vector_of_invariant_functional := @_root_.OAI.Saxl.vector_of_invariant_functional

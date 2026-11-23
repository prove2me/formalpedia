-- Prove2me | solution 1 for GlobalTheory.GlueModels.exists_of_inl_eq_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:00:47.727723+00:00
-- url     : https://prove2.me/submissions/59d3c859-862b-474a-9e24-b9a3c135649d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GlueModels
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GlueModels
theorem _root_.solution {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] {x : U} {y : V} (h : pushout.inl p q x = pushout.inr p q y) :
    ∃ w : W, p w = x ∧ q w = y := by
  obtain ⟨k, fi, fj, w, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span p q)
    (i := WalkingSpan.left) (j := WalkingSpan.right)).1 h
  rcases fi with _ | _
  · rcases fj with _ | _
  · rcases fj with _ | _
    exact ⟨w, h1, h2⟩
end GlobalTheory.GlueModels

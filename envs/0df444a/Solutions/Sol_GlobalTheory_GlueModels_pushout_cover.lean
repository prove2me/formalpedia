-- Prove2me | solution 1 for GlobalTheory.GlueModels.pushout_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:09.131451+00:00
-- url     : https://prove2.me/submissions/7a1605d5-ccdd-45fb-9eb4-b35cfe1f79ad

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
    [IsOpenImmersion q] (z : (pushout p q : Scheme.{0})) :
    z ∈ Set.range (pushout.inl p q) ∨ z ∈ Set.range (pushout.inr p q) := by
  obtain ⟨i, x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span p q) z
  rcases i with _ | _ | _
  · refine Or.inl ⟨p x, Eq.trans ?_ hx⟩
    exact congrArg (fun g => g x) (colimit.w (span p q) WalkingSpan.Hom.fst)
  · exact Or.inl ⟨x, hx⟩
  · exact Or.inr ⟨x, hx⟩
end GlobalTheory.GlueModels

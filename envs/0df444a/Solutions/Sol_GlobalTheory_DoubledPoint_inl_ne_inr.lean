-- Prove2me | solution 1 for GlobalTheory.DoubledPoint.inl_ne_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:41:26.617392+00:00
-- url     : https://prove2.me/submissions/701a7ff2-d923-4846-8b0c-6506d89e1984

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CorrOfGenericOfIsSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory
universe u
open GlobalTheory.DoubledPoint
variable {X : Scheme.{0}} (U : X.Opens)
namespace GlobalTheory.DoubledPoint
theorem _root_.solution (x : X) (hx : x ∉ U) : pushout.inl U.ι U.ι ≠ pushout.inr U.ι U.ι := by
  intro e
  have h : colimit.ι (span U.ι U.ι) WalkingSpan.left x = colimit.ι (span U.ι U.ι) WalkingSpan.right x :=
    congrArg (fun q : X ⟶ pushout U.ι U.ι => q x) e
  obtain ⟨k, fi, fj, y, h₁, -⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff _).1 h
  rcases fi with _ | _
  · exact nomatch (show WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) from fj)
  · exact hx (by
      have : U.ι y = x := h₁
      rw [← this]
      exact y.2)
end GlobalTheory.DoubledPoint

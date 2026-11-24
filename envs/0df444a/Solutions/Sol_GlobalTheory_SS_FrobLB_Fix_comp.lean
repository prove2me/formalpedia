-- Prove2me | solution 1 for GlobalTheory.SS.FrobLB.Fix.comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:19:15.482537+00:00
-- url     : https://prove2.me/submissions/3a72ee49-e515-4baf-b8f8-b206a5ef0722

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PullPowOfFix

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
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FrobLB
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
namespace GlobalTheory.SS.FrobLB
namespace Fix
theorem _root_.solution {X : Scheme.{0}} {φ ψ : X ⟶ X} {U : X.Opens} {f : Γ(X, U)} {a b : ℕ}
    (h : Fix φ U f a) (h' : Fix ψ U f b) : Fix (φ ≫ ψ) U f (a * b) := by
  obtain ⟨e, h⟩ := h
  obtain ⟨e', h'⟩ := h'
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← e', ← e], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U e'.le e.le, CommRingCat.hom_comp, RingHom.comp_apply, h', map_pow, h,
    pow_mul]
end Fix
end GlobalTheory.SS.FrobLB

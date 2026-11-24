-- Prove2me | solution 1 for GlobalTheory.QuotientGluing.exists_isAffineQuotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:39.541251+00:00
-- url     : https://prove2.me/submissions/94e666af-4cc5-4edd-bf9b-3cdb14392eae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsInvariantSectionMemBasicOpenIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientOfFiniteGroup
import Theorems.Thm_GlobalTheory_QuotientGluing_exists_of_charts
import Theorems.Thm_GlobalTheory_IsInvariantSection_basicOpen_le
import Theorems.Thm_GlobalTheory_exists_isInvariantSection_basicOpen_le
import Theorems.Thm_GlobalTheory_exists_stable_isAffineOpen
import Theorems.Thm_GlobalTheory_specAction_fromSpec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.QuotientGluing
variable {G : Type} [Group G] [Finite G] {X : Scheme.{0}}
namespace GlobalTheory.QuotientGluing
theorem _root_.solution (ρ : G →* Aut X) [OrbitsInAffineOpens ρ] :
    ∃ (X' : Scheme.{0}) (π : X ⟶ X'), IsAffineQuotient ρ π := by
  let 𝒰 : Set X.Opens := {U | IsAffineOpen U ∧ ∀ g, U ≤ (ρ g).hom ⁻¹ᵁ U}
  refine exists_of_charts ρ 𝒰 (fun U hU V hV x hxU hxV ↦ ?_) (fun x ↦ ?_)
    (fun U ↦ Spec Γ(X, U.1)) (fun U ↦ U.2.1.fromSpec) (fun U ↦ U.2.1.opensRange_fromSpec)
    (fun U ↦ U.2.1)
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2; specAction G Γ(X, U.1))
    (fun U ↦ specAction_fromSpec ρ U.2.1 U.2.2)
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2; Spec (.of (FixedPoints.subring Γ(X, U.1) G)))
    (fun U ↦ letI := sectionsAction ρ U.1 U.2.2
      Spec.map (CommRingCat.ofHom (algebraMap (FixedPoints.subring Γ(X, U.1) G) Γ(X, U.1))))
    (fun U ↦ ?_)
  · obtain ⟨t, ht, hx, hle⟩ := exists_isInvariantSection_basicOpen_le hU.1 hU.2 hxU V
      (fun g ↦ hV.2 g hxV)
    exact ⟨_, ⟨hU.1.basicOpen t, ht.basicOpen_le⟩, hx, X.basicOpen_le t, hle⟩
  · obtain ⟨V, h1, h2, h3⟩ := exists_stable_isAffineOpen ρ x
    exact ⟨⟨V, h1, h2⟩, h3⟩
  · let := sectionsAction ρ U.1 U.2.2
    exact isAffineQuotient_spec (FixedPoints.subring Γ(X, U.1) G) Γ(X, U.1)
end GlobalTheory.QuotientGluing

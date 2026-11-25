-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.fractionField_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:06:07.108952+00:00
-- url     : https://prove2.me/submissions/fc8f1f2e-8e74-43e4-b77b-2cd00d260f55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
import Theorems.Thm_GlobalTheory_IsGenericPointHom_fractionField
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_generic_of_isGrpPullback
import Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_isNormalScheme_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (h : SemiAbelianHomExtension) {R K : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {G H : Over (Sp R)}
    [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over (Sp K)} [GrpObj G']
    [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G (spMap (algebraMap R K)) φ) (hψ : IsGrpPullback H' H (spMap (algebraMap R K)) ψ)
    (f : G' ⟶ H') [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left :=
  generic_of_isGrpPullback h (isNormalScheme_spec R) (IsGenericPointHom.fractionField R K) hG hH hφ hψ f
end GlobalTheory.Published.SemiAbelianHomExtension

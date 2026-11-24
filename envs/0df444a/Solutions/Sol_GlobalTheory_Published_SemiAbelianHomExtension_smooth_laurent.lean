-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.smooth_laurent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:40:04.876093+00:00
-- url     : https://prove2.me/submissions/2a94a2b6-1d5a-4ddb-a1c3-c77f3dc129fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
open scoped TensorProduct
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution (R : Type) [CommRing R] : Algebra.Smooth R (AddMonoidAlgebra R (ULift.{0} ℤ)) := by
  have h₁ : Algebra.Smooth (Polynomial R) (LaurentPolynomial R) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial R)
  have h₀ : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
  have : IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
    IsScalarTower.of_algebraMap_eq fun r => (Polynomial.toLaurent_C r).symm
  have h₂ : Algebra.Smooth R (LaurentPolynomial R) := Algebra.Smooth.comp R (Polynomial R) _
  exact Algebra.Smooth.of_equiv (AddMonoidAlgebra.domCongr R R (AddEquiv.ulift (α := ℤ)).symm)
end GlobalTheory.Published.SemiAbelianHomExtension

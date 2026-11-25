-- Prove2me | solution 1 for GlobalTheory.isReduced_algebra_of_smooth_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:02.096176+00:00
-- url     : https://prove2.me/submissions/8e9ed2e5-7c2c-4e76-8fa3-270bafa9aadb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Theorems.Thm_GlobalTheory_isReduced_algebra_of_smooth_of_isNoetherianRing
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A₀ B₀ := Algebra.Smooth.flat A₀ B₀
  have key : _root_.IsReduced (TensorProduct A₀ B₀ A) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun D hD => ?_)
    have : Algebra.FiniteType A₀ D := (Subalgebra.fg_iff_finiteType D).mp hD
    have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A₀ D
    have : _root_.IsReduced D := isReduced_of_injective D.val Subtype.val_injective
    have : _root_.IsReduced (TensorProduct A₀ D B₀) :=
      GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing D (TensorProduct A₀ D B₀)
    exact isReduced_of_injective (Algebra.TensorProduct.comm A₀ B₀ D).toRingHom
      (Algebra.TensorProduct.comm A₀ B₀ D).injective
  exact isReduced_of_injective
    ((Algebra.TensorProduct.comm A₀ A B₀).toRingHom.comp e.toRingHom)
    ((Algebra.TensorProduct.comm A₀ A B₀).injective.comp e.injective)
end GlobalTheory

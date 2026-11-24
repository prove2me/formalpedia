-- Prove2me | solution 1 for GlobalTheory.SameZeroScheme.appLE_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:29.086041+00:00
-- url     : https://prove2.me/submissions/4175f2d3-94a2-4c5b-8451-38831efd6f0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SameZeroScheme
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.SameZeroScheme
theorem _root_.solution {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) :
    (Spec.map φ ≫ hU.fromSpec).appLE V ⊤ (top_le_preimage hU h φ) =
      Y.presheaf.map (homOfLE h).op ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ V := by
    rw [← hU.fromSpec_preimage_self]
    exact fun x hx => h hx
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) hU.fromSpec V ⊤ ⊤ h1 le_top,
    Scheme.ΓSpecIso_inv_naturality]
  have e1 : hU.fromSpec.appLE V ⊤ h1 =
      Y.presheaf.map (homOfLE h).op ≫ (Scheme.ΓSpecIso Γ(Y, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_of_le V h, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    congr 1
  have e2 : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  rw [e1, e2, Category.assoc]
end GlobalTheory.SameZeroScheme

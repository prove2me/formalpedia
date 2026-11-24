-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent.homAt_vecPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:10.637345+00:00
-- url     : https://prove2.me/submissions/b22864b1-2824-47c3-9bdd-4da4585dcf27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SemiAbelianAxisTangent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (d : ℕ)
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent
theorem _root_.solution {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B]
    (f : A →ₐ[S] B) (v : Fin d → A) : homAt x0 f ≫ vecPt x0 d v = vecPt x0 d fun j => f (v j) := by
  apply (vecEquiv _).injective
  have h : vecEquiv _ (homAt x0 f ≫ vecPt x0 d v) = Multiplicative.ofAdd fun j =>
      (spMap (f : A →+* B)).appTop.hom ((vecEquiv _ (vecPt x0 d v)).toAdd j) := rfl
  rw [h, vecPt, vecPt, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  congr 1
  funext j
  exact congrArg (fun q => q.hom (v j))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (f : A →+* B))).symm
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianAxisTangent

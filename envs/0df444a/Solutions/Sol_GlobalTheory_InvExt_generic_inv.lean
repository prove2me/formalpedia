-- Prove2me | solution 1 for GlobalTheory.InvExt.generic_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:49:41.321598+00:00
-- url     : https://prove2.me/submissions/fc6517ae-4689-4e3d-8693-4b419c823e2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_GlobalTheory_InvExt_inv_left_comp
import Theorems.Thm_GlobalTheory_InvExt_isOpenImmersion_a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.InvExt
variable (C : Core)
variable {C}
namespace GlobalTheory.InvExt
theorem _root_.solution {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j) (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left)
    (ha : a₀ ≫ C.a = gPt p ≫ c ≫ τ.f) :
    gPt p ≫ c ≫ (ι[τ.H]).left ≫ τ.f = a₀ ≫ (ι[C.A]).left ≫ C.a := by
  have := isOpenImmersion_a C
  have hinj : Function.Injective ((OO p).subtype.comp τ.j) := Subtype.val_injective.comp τ.j_inj
  let k : FractionRing τ.V →+* PadicAlgCl p := IsFractionRing.lift hinj
  have hk : spMap k ≫ Out.jK τ.V = gPt p ≫ spMap τ.j := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    simp [k]
  let l : Sp (PadicAlgCl p) ⟶ pullback τ.H.hom (Out.jK τ.V) :=
    pullback.lift (gPt p ≫ c) (spMap k) (by rw [Category.assoc, hc, hk])
  have hl : l ≫ pullback.fst _ _ = gPt p ≫ c := pullback.lift_fst _ _ _
  have h1 : l ≫ τ.φ = a₀ := by
    rw [← cancel_mono C.a, Category.assoc, τ.φ_f, reassoc_of% hl, ha]
  have h2 := inv_left_comp τ.φ_cart
  have h3 := inv_left_comp (isGrpPullback_pullback τ.H (Out.jK τ.V))
  have h4 : (ι[(Over.pullback (Out.jK τ.V)).obj τ.H]).left ≫ τ.φ ≫ C.a =
      τ.φ ≫ (ι[C.A]).left ≫ C.a := by
    rw [← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ C.a) h2
  have h5 : (ι[(Over.pullback (Out.jK τ.V)).obj τ.H]).left ≫ pullback.fst τ.H.hom (Out.jK τ.V) ≫ τ.f =
      pullback.fst τ.H.hom (Out.jK τ.V) ≫ (ι[τ.H]).left ≫ τ.f := by
    rw [← Category.assoc, ← Category.assoc]; exact congrArg (· ≫ τ.f) h3
  rw [← h1, Category.assoc, ← h4, τ.φ_f]
  erw [h5]
  rw [reassoc_of% hl]
end GlobalTheory.InvExt

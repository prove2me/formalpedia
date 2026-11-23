-- Prove2me | solution 1 for GlobalTheory.ThickDiv.app_constFn_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:27.022252+00:00
-- url     : https://prove2.me/submissions/bfeb053e-612d-4951-9525-72b87c2173cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DvdOfAppEqZeroOfIsAffineOpen
import Theorems.Thm_GlobalTheory_ThickDiv_thick_appTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickDiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ThickDiv
theorem _root_.solution {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (e : ℕ)
    (X : Over (Spec (CommRingCat.of V))) (W : X.left.Opens) {a : V} (ha : a ∈ I ^ (e + 1)) :
    ((fstG I e X).left.app W).hom (constFn X.hom W a) = 0 := by
  have h0 : ((thick V I e).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) = 0 := by
    rw [thick_appTop, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hc := congrArg (fun φ => (φ.appLE ⊤ ((pullback.fst X.hom (thick V I e)) ⁻¹ᵁ W) (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)) (pullback.condition (f := X.hom) (g := thick V I e))
  have h1 : ((pullback.snd X.hom (thick V I e) ≫ thick V I e).appLE ⊤
      ((pullback.fst X.hom (thick V I e)) ⁻¹ᵁ W) (by simp)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) = 0 := by
    change ((pullback X.hom (thick V I e)).presheaf.map _).hom
      (((pullback.snd X.hom (thick V I e)).app _).hom
        (((thick V I e).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a))) = 0
    rw [h0, map_zero, map_zero]
  have hn := congrArg (fun φ => φ.hom ((X.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a)))
    ((pullback.fst X.hom (thick V I e)).naturality (homOfLE (show W ≤ X.hom ⁻¹ᵁ ⊤ by simp)).op)
  exact hn.trans (hc.trans h1)
end GlobalTheory.ThickDiv

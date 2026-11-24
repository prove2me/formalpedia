-- Prove2me | solution 1 for GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:04:57.801566+00:00
-- url     : https://prove2.me/submissions/a3acea26-dbac-445a-831f-a4efdb220d44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsNormalSchemePullbackSpMapOfAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution
    (halg : ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A]
      [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧
        IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
        IsIntegrallyClosed (Localization.AtPrime Q))
    (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0})
    (g : Y ⟶ Sp F) (hY : GlobalTheory.IsNormalScheme Y) : GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine (GlobalTheory.IsNormalScheme.iff_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 g (spMap c))).mpr ?_
  intro i
  change GlobalTheory.IsNormalScheme (pullback (𝒰.f i ≫ g) (spMap c))
  let R := Y.affineOpenCover.X i
  have hR : GlobalTheory.IsNormalScheme (Spec R) :=
    @GlobalTheory.IsNormalScheme.of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i) hY
  let φ := Spec.preimage (𝒰.f i ≫ g)
  letI : Algebra F R := φ.hom.toAlgebra
  letI : Algebra F K := c.toAlgebra
  have e1 : 𝒰.f i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F R)) :=
    (Spec.map_preimage (𝒰.f i ≫ g)).symm
  have e2 : spMap c = Spec.map (CommRingCat.ofHom (algebraMap F K)) := rfl
  rw [e1, e2]
  refine (GlobalTheory.IsNormalScheme.iff_of_iso (pullbackSpecIso F R K)).mpr ?_
  refine (GlobalTheory.IsNormalScheme.spec_iff _).mpr ?_
  exact halg F K R ((GlobalTheory.IsNormalScheme.spec_iff R).mp hR)
end GlobalTheory

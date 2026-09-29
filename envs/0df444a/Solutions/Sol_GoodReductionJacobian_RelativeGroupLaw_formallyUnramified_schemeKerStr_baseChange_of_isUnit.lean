-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeKerStr_baseChange_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4c2edd70-edb9-50de-9b4a-deebfd5829be

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeKerStr_baseChange_of_isUnit

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeKerStr_baseChange_of_isUnit.GoodReductionJacobian"

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "schemeNsmul schemeKerStr IsCommutative mul baseChange IsCommutative.baseChange formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem formallyUnramified_schemeKerStr_of_isUnit
    {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeKerStr n) := by
  have h : FormallyUnramified (G.schemeNsmul n) :=
    formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing G hcomm n hn
  exact MorphismProperty.pullback_snd (P := @FormallyUnramified) _ _ h

theorem formallyUnramified_schemeKerStr_baseChange_of_isUnit
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [IsLocalRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R')) :
    FormallyUnramified ((G.baseChange ι).schemeKerStr n) :=
  formallyUnramified_schemeKerStr_of_isUnit (G.baseChange ι) (fun t x y => (show (G.baseChange ι).IsCommutative from
    IsCommutative.baseChange ι (fun t x y => hcomm t x y)) t x y) n hn

end GoodReductionJacobian.RelativeGroupLaw

theorem solution
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [IsLocalRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R')) :
    FormallyUnramified ((G.baseChange ι).schemeKerStr n) :=
  GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeKerStr_baseChange_of_isUnit ι G hcomm n hn

end S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeKerStr_baseChange_of_isUnit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeKerStr_baseChange_of_isUnit (solution)

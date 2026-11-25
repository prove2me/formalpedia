-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:19:01.360805+00:00
-- url     : https://prove2.me/submissions/1eec1f31-694a-4e7b-b6ce-6aa583f719ea

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_localization_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
open AlgebraicGeometry CategoryTheory
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {X : Scheme.{u}} {R : CommRingCat.{u}} [IsRegularRing R]
    (f : X ⟶ Spec R) [Smooth f] (x : X) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hsm : (f.appLE ⊤ U (by simp)).hom.Smooth :=
    HasRingHomProperty.appLE @Smooth f inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have : IsRegularRing Γ(Spec R, ⊤) :=
    IsRegularRing.of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  algebraize [(f.appLE ⊤ U (by simp)).hom]
  set P := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hreg : IsRegularLocalRing (Localization.AtPrime P) :=
    isRegularLocalRing_localization_of_smooth Γ(Spec R, ⊤) Γ(X, U) P
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P := hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (R := Γ(X, U)) P.primeCompl
    (Localization.AtPrime P) (X.presheaf.stalk x)).toRingEquiv
end GroundTheory.Arith.SchemeCoh

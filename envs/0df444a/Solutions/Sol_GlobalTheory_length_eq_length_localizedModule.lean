-- Prove2me | solution 1 for GlobalTheory.length_eq_length_localizedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:45.758342+00:00
-- url     : https://prove2.me/submissions/0a93b97e-516a-4200-ab54-75bd98ba39f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {S : Type*} [CommRing S]
namespace GlobalTheory
theorem _root_.solution (T : Submonoid S) (A : Type*) [CommRing A] [Algebra S A]
    [IsLocalization T A] {X X' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup X']
    [Module S X'] [Module A X'] [IsScalarTower S A X'] (f : X →ₗ[S] X') [IsLocalizedModule T f] :
    Module.length A X' = Module.length (Localization T) (LocalizedModule T X) := by
  let e : Localization T ≃ₐ[S] A := IsLocalization.algEquiv T _ _
  letI : Algebra (Localization T) A := e.toRingHom.toAlgebra
  letI : Module (Localization T) X' := Module.compHom X' e.toRingHom
  haveI : IsScalarTower (Localization T) A X' := ⟨fun a b x => mul_smul (e a) b x⟩
  haveI : IsScalarTower S (Localization T) X' := ⟨fun a b x => by
    change e (a • b) • x = a • (e b • x)
    rw [map_smul, smul_assoc]⟩
  rw [← Module.length_eq_of_surjective (S := Localization T) (R := A) (M := X') e.surjective]
  exact (((IsLocalizedModule.iso T f).extendScalarsOfIsLocalization T
    (Localization T)).length_eq).symm
end GlobalTheory

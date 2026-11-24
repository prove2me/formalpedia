-- Prove2me | solution 1 for GlobalTheory.InertiaDVR.perfectField_residueField_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:47:39.643805+00:00
-- url     : https://prove2.me/submissions/256ba2aa-450b-44f7-aec9-6bf23f342aa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardInertiaEqRamificationIdxOfPerfectResidue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory GlobalTheory.InertiaDVR
namespace GlobalTheory.InertiaDVR
theorem _root_.solution (R : Type) [CommRing R] [IsLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)] (p : Ideal R) [p.IsPrime] (hp : p = IsLocalRing.maximalIdeal R) :
    PerfectField p.ResidueField := by
  subst hp
  have hb := Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R)
  let e : IsLocalRing.ResidueField R ≃+* (IsLocalRing.maximalIdeal R).ResidueField :=
    RingEquiv.ofBijective _ hb
  letI : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    e.toRingHom.toAlgebra
  have : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    ⟨fun x => by obtain ⟨y, rfl⟩ := e.surjective x; exact isIntegral_algebraMap⟩
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField R)
end GlobalTheory.InertiaDVR

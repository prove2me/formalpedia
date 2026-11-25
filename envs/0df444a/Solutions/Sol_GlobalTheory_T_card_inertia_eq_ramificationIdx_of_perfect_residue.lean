-- Prove2me | solution 1 for GlobalTheory.T.card_inertia_eq_ramificationIdx_of_perfect_residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:52.318059+00:00
-- url     : https://prove2.me/submissions/fa2c45e9-f378-48cd-9630-efe31a9e5ecc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardInertiaEqRamificationIdxOfPerfectResidue
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardInertiaEqRamificationIdxOfPerfectResidueStatement
import Theorems.Thm_GlobalTheory_InertiaDVR_card_inertia_eq_ramificationIdx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)), Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) = P.asIdeal.ramificationIdx R := by
  first | exact @GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx | exact GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx | (intros; apply GlobalTheory.InertiaDVR.card_inertia_eq_ramificationIdx <;> assumption)
end _root_.GlobalTheory.T

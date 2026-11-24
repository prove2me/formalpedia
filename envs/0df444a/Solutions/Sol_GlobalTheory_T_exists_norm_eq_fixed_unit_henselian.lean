-- Prove2me | solution 1 for GlobalTheory.T.exists_norm_eq_fixed_unit_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:44.756799+00:00
-- url     : https://prove2.me/submissions/5e2b4163-285f-4c06-acce-6a73de8b6630

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsNormEqFixedUnitHenselianStatement
import Theorems.Thm_GlobalTheory_HenselianNorm_exists_norm_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R) [HenselianRing R I] [Finite (R ⧸ I)] (c : R →+* R), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ u, c u = u → IsUnit u → ∃ x, x * c x = u := by
  first | exact @GlobalTheory.HenselianNorm.exists_norm_eq | exact GlobalTheory.HenselianNorm.exists_norm_eq | (intros; apply GlobalTheory.HenselianNorm.exists_norm_eq <;> assumption)
end _root_.GlobalTheory.T

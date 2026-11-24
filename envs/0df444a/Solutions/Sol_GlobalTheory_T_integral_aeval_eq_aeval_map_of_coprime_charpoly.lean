-- Prove2me | solution 1 for GlobalTheory.T.integral_aeval_eq_aeval_map_of_coprime_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:28:20.846124+00:00
-- url     : https://prove2.me/submissions/4dc1d503-0cac-4aed-ae3d-e91d2561a828

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpoly
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Theorems.Thm_GlobalTheory_MaxOrder_isIntegral_aeval_eq_aeval_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ p : K[X], IsIntegral O (aeval γ p) → ∃ r : O[X], aeval γ p = aeval γ (r.map (algebraMap O K)) := by
  first | exact @GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | exact GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map | (intros; apply GlobalTheory.MaxOrder.isIntegral_aeval_eq_aeval_map <;> assumption)
end _root_.GlobalTheory.T

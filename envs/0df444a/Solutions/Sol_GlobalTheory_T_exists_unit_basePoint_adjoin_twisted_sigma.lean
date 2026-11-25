-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:19.237701+00:00
-- url     : https://prove2.me/submissions/695ed515-a023-4a5d-bfab-fd785e2e0da0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigmaStatement
import Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_exists_unit_base


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.UnitBase.exists_unit_base | exact GlobalTheory.UnitLemma.UnitBase.exists_unit_base | (intros; apply GlobalTheory.UnitLemma.UnitBase.exists_unit_base <;> assumption)
end _root_.GlobalTheory.T

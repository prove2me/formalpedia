-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:45.830165+00:00
-- url     : https://prove2.me/submissions/a5e8d7a7-cbb9-4f38-a975-b3c15540ff60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Theorems.Thm_GlobalTheory_UnitAdj_exists_unitary_mul_integral


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
theorem _root_.solution : ∀ {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by
  first | exact @GlobalTheory.UnitAdj.exists_unitary_mul_integral | exact GlobalTheory.UnitAdj.exists_unitary_mul_integral | (intros; apply GlobalTheory.UnitAdj.exists_unitary_mul_integral <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.exists_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:22.877016+00:00
-- url     : https://prove2.me/submissions/ff8c03cf-2261-410e-b5ca-2509198745d7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_exists_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution {a c x : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hx : Valued.v x < 1) {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    ∃ t : K, Valued.v t < 1 ∧ Valued.v ((a * t + c * t ^ 2) - x) < γ := by
  obtain ⟨t, ht, h⟩ := exists_approx ha hc hx (WithZero.log γ).natAbs.succ
  refine ⟨t, ht, lt_of_le_of_lt h ?_⟩
  conv_rhs => rw [← WithZero.exp_log hγ]
  rw [WithZero.exp_lt_exp]
  have := neg_abs_le (WithZero.log γ)
  push_cast
  omega
end GlobalTheory.CompanionTheory.SW.QuadIso

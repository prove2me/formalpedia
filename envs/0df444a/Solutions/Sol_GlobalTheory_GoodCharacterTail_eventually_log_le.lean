-- Prove2me | solution 1 for GlobalTheory.GoodCharacterTail.eventually_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:08:37.761129+00:00
-- url     : https://prove2.me/submissions/cad3774a-571c-4dd7-83a6-df45fc28334b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2IntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TailAndSumBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open GlobalTheory GlobalTheory.GoodCharacterTail
open Formalism.HermitianLattices.GL2PrimeSums
namespace GlobalTheory.GoodCharacterTail
theorem _root_.solution (k δ : ℝ) (hk : 0 < k) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ k * x ^ δ := by
  have h := (isLittleO_log_rpow_atTop hδ).bound hk
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
  exact (le_abs_self _).trans hx
end GlobalTheory.GoodCharacterTail

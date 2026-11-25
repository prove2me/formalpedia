-- Prove2me | solution 1 for GlobalTheory.tensorFourthPower_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:02.68755+00:00
-- url     : https://prove2.me/submissions/2ea1f785-9428-4575-b7b8-e04e957682a5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AlgebraicTheory_StatementNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LocalNormalizationIntegralScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Formalism.L2.AlgTh
namespace GlobalTheory
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] (c : ℂ) (θ : (n → ℂ) → ℂ) :
    Formalism.L2.Th1.H.tens4 (c • θ) = c ^ 4 • Formalism.L2.Th1.H.tens4 θ := by
  funext z
  simp only [Formalism.L2.Th1.H.tens4, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end GlobalTheory

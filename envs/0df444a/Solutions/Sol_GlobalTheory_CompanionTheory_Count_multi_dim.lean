-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Count.multi_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:16.438537+00:00
-- url     : https://prove2.me/submissions/b4a65080-2da9-4848-9f72-3417f803c5be

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultiDimensional
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticeSumDecayBound
import Theorems.Thm_UpperTheory_Reformulated_B_MultiDimensional_multi_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Count
namespace GlobalTheory.CompanionTheory.Count
theorem _root_.solution {P : Type} [Fintype P] (g : P → ℤ → ℝ≥0∞) :
    ∑' x : P → ℤ, ∏ p, g p (x p) ≤ ∏ p, ∑' n, g p n :=
  _root_.UpperTheory.Reformulated.B.MultiDimensional.multi_dim g
end GlobalTheory.CompanionTheory.Count

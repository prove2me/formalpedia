-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.MatrixLie.hasDerivAt_exp_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:27:57.697987+00:00
-- url     : https://prove2.me/submissions/a9e95ffc-c0a7-4d0e-804a-de14264a1bcd

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurveStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtExpMulExpOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_MatrixLie_entry_hasDerivAt_exp_mul_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MatrixLie
namespace GlobalTheory.CompanionTheory.MatrixLie
theorem _root_.solution {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((t : ℂ) • Y))
      (X + Y) 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => entry_hasDerivAt_exp_mul_exp X Y i j
end GlobalTheory.CompanionTheory.MatrixLie

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Dblock.CentreBlocks.pow_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:25:46.400238+00:00
-- url     : https://prove2.me/submissions/3db2ac9b-3822-421a-899f-6c7c1439b39a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MonicFactorCoefficientsIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CapelliPolynomialCoefficientsIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Dblock GlobalTheory.CompanionTheory.Dblock.CentreBlocks
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.Dblock.CentreBlocks
theorem _root_.solution (D : Module.End ℂ V) (Wn : Submodule ℂ V) (hD : ∀ F ∈ Wn, D F ∈ Wn) :
    ∀ n : ℕ, ∀ F ∈ Wn, (D ^ n) F ∈ Wn := by
  intro n
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    rw [pow_succ', Module.End.mul_apply]
    exact hD _ (ih F hF)
end GlobalTheory.CompanionTheory.Dblock.CentreBlocks

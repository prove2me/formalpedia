-- Prove2me | solution 1 for GlobalTheory.DerivAtOrigin.risingFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:11:05.823028+00:00
-- url     : https://prove2.me/submissions/06e35dd5-12d7-4b76-8006-97f367dbf668

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivFormulaOfSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.DerivAtOrigin
namespace GlobalTheory.DerivAtOrigin
theorem _root_.solution {I : Type} [Fintype I] (k : ℕ) (hk : 1 ≤ k) (κ : I → ℕ) :
    risingFactor k κ ≠ 0 := by
  unfold risingFactor
  rw [Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro j _
  have : ((k : ℂ) + j) = ((k + j : ℕ) : ℂ) := by push_cast; ring
  rw [this]
  exact_mod_cast (by omega : k + j ≠ 0)
end GlobalTheory.DerivAtOrigin

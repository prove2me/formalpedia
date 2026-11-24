-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.chainIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:43:56.688305+00:00
-- url     : https://prove2.me/submissions/42b05105-570e-4622-a9e8-c44f0ca85645

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_chain_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.ChainIndep := by
  intro K _ _ _ m k t ψ₀ χ hψ hχ ht
  induction t with
  | zero => rfl
  | succ t ih => rw [chain_step K m k t ψ₀ χ hψ hχ ht, ih (by omega)]
end GlobalTheory.CompanionTheory.TyFin

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.chainUnion_isPat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:47:38.214902+00:00
-- url     : https://prove2.me/submissions/6456c0e1-413a-4868-b5dd-ff994faa0163

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchangeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChainIndependence

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
theorem _root_.solution (m k t : ℕ) : IsPat (chainUnion m k t) := by
  constructor
  · rintro (a | w) <;> simp [chainUnion]
  · rintro (a | w) (b | v) (c | u) <;> simp only [chainUnion, Fin.lt_def] <;> omega
end GlobalTheory.CompanionTheory.TyFin

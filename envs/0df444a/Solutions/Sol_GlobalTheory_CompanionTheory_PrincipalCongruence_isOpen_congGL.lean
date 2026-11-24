-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_congGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:12:20.918339+00:00
-- url     : https://prove2.me/submissions/38ecfb2f-5afd-4b3c-a539-7ba73d16b3e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal
import Theorems.Thm_GlobalTheory_CompanionTheory_PrincipalCongruence_isOpen_congSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrincipalCongruence
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.CompanionTheory.PrincipalCongruence
theorem _root_.solution (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congGL n t) :=
  (isOpen_congSet n ht).preimage Units.continuous_val
end GlobalTheory.CompanionTheory.PrincipalCongruence

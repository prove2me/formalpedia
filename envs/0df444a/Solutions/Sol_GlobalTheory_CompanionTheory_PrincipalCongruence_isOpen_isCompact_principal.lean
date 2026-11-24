-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:29:34.277389+00:00
-- url     : https://prove2.me/submissions/0a637b57-426b-43fe-99e3-42d9013c8637

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenIsCompactPrincipal
import Theorems.Thm_GlobalTheory_CompanionTheory_PrincipalCongruence_isOpen_congGL
import Theorems.Thm_GlobalTheory_CompanionTheory_PrincipalCongruence_isCompact_congGL

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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
    IsOpen {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} ∧
    IsCompact {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} :=
  fun _ _ _ _ _ N _ ht ht1 => ⟨isOpen_congGL (Fin N) ht, isCompact_congGL (Fin N) ht ht1⟩
end GlobalTheory.CompanionTheory.PrincipalCongruence

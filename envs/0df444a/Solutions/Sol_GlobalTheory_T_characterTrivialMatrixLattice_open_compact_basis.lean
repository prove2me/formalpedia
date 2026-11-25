-- Prove2me | solution 1 for GlobalTheory.T.characterTrivialMatrixLattice_open_compact_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:25.808322+00:00
-- url     : https://prove2.me/submissions/e8f4c283-0df9-480a-827e-8af11253574e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AddCharNegEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharacterTrivialMatrixLatticeOpenCompactBasisStatement
import Theorems.Thm_GlobalTheory_LinSchurLatt_latt_open_compact_basis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 → (∀ s : k, s ≠ 0 → IsOpen (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ∧ IsCompact (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k))) ∧ ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∃ s : k, s ≠ 0 ∧ (GlobalTheory.LinSchur.latt ψ0 n d s : Set (Matrix (Fin n) (Fin d) k)) ⊆ W := by
  first | exact @GlobalTheory.LinSchurLatt.latt_open_compact_basis | exact GlobalTheory.LinSchurLatt.latt_open_compact_basis | (intros; apply GlobalTheory.LinSchurLatt.latt_open_compact_basis <;> assumption)
end _root_.GlobalTheory.T

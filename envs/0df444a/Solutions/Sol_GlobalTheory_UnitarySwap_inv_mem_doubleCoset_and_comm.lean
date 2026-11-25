-- Prove2me | solution 1 for GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:26:26.457958+00:00
-- url     : https://prove2.me/submissions/e46a47cc-ee67-4e61-a91f-74305838c610

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_GlobalTheory_UnitarySwap_inv_mem_doubleCoset
import Theorems.Thm_GlobalTheory_UnitarySwap_heckeCommU
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.UnitarySwap
theorem _root_.solution : (∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), IsUnramInv ϖ σ q → J ∈ GLint (Fin n) (intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ g ∈ UJ σ (J : Matrix (Fin n) (Fin n) L), ∃ k₁ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), ∃ k₂ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g⁻¹ = k₁ * g * k₂) ∧ HeckeCommU :=
  ⟨fun _ _ _ _ _ _ _ _ _ hU hJ hh _ hg => inv_mem_doubleCoset hU hJ hh hg, heckeCommU⟩
end GlobalTheory.UnitarySwap

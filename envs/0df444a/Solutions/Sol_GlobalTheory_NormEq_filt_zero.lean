-- Prove2me | solution 1 for GlobalTheory.NormEq.filt_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:08:10.706258+00:00
-- url     : https://prove2.me/submissions/7034b797-eb5c-4998-a96e-940ecaffe28f

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Theorems.Thm_GlobalTheory_NormEq_mem_unitFil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.UG
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) :
    filt h P 0 = ⊤ := by
  ext u; simp [filt, mem_unitFil, piPow]
end GlobalTheory.NormEq

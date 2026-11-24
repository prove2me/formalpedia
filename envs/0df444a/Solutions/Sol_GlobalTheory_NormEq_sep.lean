-- Prove2me | solution 1 for GlobalTheory.NormEq.sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:57:41.7138+00:00
-- url     : https://prove2.me/submissions/0fcc1920-7089-41ac-b01c-f5122a9a2f74

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfMemAllPowers
import Theorems.Thm_GlobalTheory_NormEq_eq_zero_of_forall_mem_piPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.NormEq
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ)
    (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P),
    (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 :=
  fun _ _ _ _ _ _ h P a ha => eq_zero_of_forall_mem_piPow h P a ha
end GlobalTheory.NormEq

-- Prove2me | solution 1 for GlobalTheory.NormEq.mem_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:14:42.954188+00:00
-- url     : https://prove2.me/submissions/e82bbaa4-558a-4843-884d-6f77ee520783

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul

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
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} {h : IsUnramInv ϖ σ q} {P : GlobalTheory.UTr.Csr (sigO σ h.2.1)} {m : ℕ}
    {u : (GlobalTheory.UTr.Alg P)ˣ} : u ∈ filt h P m ↔ (u : GlobalTheory.UTr.Alg P) - 1 ∈ piPow h P m := Iff.rfl
end GlobalTheory.NormEq

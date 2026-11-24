-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.inv_natCast_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:13.57222+00:00
-- url     : https://prove2.me/submissions/e9a11c44-680e-46e2-a997-3a73040d1016

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution (N : ℕ) (S : ℂ) : ((((N : ℝ)⁻¹ : ℝ)) : ℂ) ^ S = (N : ℂ) ^ (-S) := by
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg]
end GlobalTheory.CMVal.Euler

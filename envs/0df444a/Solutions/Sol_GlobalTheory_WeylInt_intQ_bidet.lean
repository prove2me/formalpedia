-- Prove2me | solution 1 for GlobalTheory.WeylInt.intQ_bidet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:16:53.978961+00:00
-- url     : https://prove2.me/submissions/b559f212-a271-4429-9f22-9d21f6570a2b

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriIntegral
import Theorems.Thm_GlobalTheory_WeylInt_intQ_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.WeylInt
open Formalism.GradedWeylDivisibility
namespace GlobalTheory.WeylInt
theorem _root_.solution {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    intQ r n (bideterminant ℤ sz hsz I) = bideterminant ℚ sz hsz I := by
  rw [intQ_apply]
  simp only [bideterminant, initMinor, map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  ext1 i j
  simp
end GlobalTheory.WeylInt

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAntipode.ofFn_prod_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:21:40.429117+00:00
-- url     : https://prove2.me/submissions/6f59ef5a-cba9-4420-8f5e-7b3c1c30c0a5

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAntipode
namespace GlobalTheory.CompanionTheory.CapelliAntipode
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] : ∀ {t : ℕ} (g : Fin t → A),
    (List.ofFn fun k => -g k).prod = ((-1 : ℂ) ^ t) • (List.ofFn g).prod
  | 0, g => by simp
  | t + 1, g => by
    rw [List.ofFn_succ, List.prod_cons, solution (fun k => g k.succ), List.ofFn_succ (f := g),
      List.prod_cons, pow_succ, mul_comm, mul_smul, neg_mul, mul_smul_comm, neg_one_smul]
end GlobalTheory.CompanionTheory.CapelliAntipode

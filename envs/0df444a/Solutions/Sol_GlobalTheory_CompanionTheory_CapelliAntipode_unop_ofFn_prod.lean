-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CapelliAntipode.unop_ofFn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:38.008182+00:00
-- url     : https://prove2.me/submissions/025e5cd7-b825-43ce-88f3-e9cbd7bab06a

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
theorem _root_.solution {A : Type*} [Ring A] : ∀ {t : ℕ} (f : Fin t → Aᵐᵒᵖ),
    MulOpposite.unop (List.ofFn f).prod = (List.ofFn fun i => MulOpposite.unop (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul, solution (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => MulOpposite.unop (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]
end GlobalTheory.CompanionTheory.CapelliAntipode

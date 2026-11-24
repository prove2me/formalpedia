-- Prove2me | solution 1 for GlobalTheory.HeckeTwoMul.wirtWord_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:43:39.813858+00:00
-- url     : https://prove2.me/submissions/f9052240-ecbf-4640-a3f6-67feabf8227c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyMulLeft
import Theorems.Thm_GlobalTheory_HeckeTwoMul_wirt_const_mul
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwoMul
namespace GlobalTheory.HeckeTwoMul
theorem _root_.solution {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (c : ℂ) (g : (Φ → ℂ) → ℂ) :
    wirtWord ws (fun z => c * g z) = fun z => c * wirtWord ws g z := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [wirtWord_cons, wirtWord_cons, ih, wirt_const_mul]
end GlobalTheory.HeckeTwoMul

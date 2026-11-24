-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.wirtWord_const_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:06.207486+00:00
-- url     : https://prove2.me/submissions/d5ba3af6-25d8-479e-be9e-7a0cb499f019

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyOfSigmaOnly
import Theorems.Thm_GlobalTheory_HeckeTwo_wirt_const_fun
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
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (d : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord ws (fun _ : Φ → ℂ => d) = fun _ => if ws = [] then d else 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.wirtWord_cons, ih]
    simp only [reduceCtorEq, if_false]
    exact wirt_const_fun w.1 w.2 _
end GlobalTheory.HeckeTwo

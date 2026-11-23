-- Prove2me | solution 1 for GlobalTheory.posDef_of_posDef_realExt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:28:23.503854+00:00
-- url     : https://prove2.me/submissions/d3161439-e899-45c8-bdb1-e0e44a16a696

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X]
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) : Q.PosDef := by
  intro x hx
  have h := hQ (1 ⊗ₜ x) fun h₀ => hx <| by
    let b := Module.finBasis ℤ X
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    simpa using congrArg (fun v => (b.baseChange ℝ).repr v i) h₀
  simpa using h
end GlobalTheory

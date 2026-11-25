-- Prove2me | solution 1 for GlobalTheory.Nef.OrdCalc.det_adj_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:02:56.1442+00:00
-- url     : https://prove2.me/submissions/20c7e5f1-d2df-45e5-b402-517dc205bd77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]
namespace GlobalTheory.Nef.OrdCalc
theorem _root_.solution (v : Place k F) (n : ℕ) (u : Matrix (Fin n) (Fin n) F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) : v.1 u.det ≤ 1 ∧ ∀ i j, v.1 (u.adjugate i j) ≤ 1 := by
  let M : Matrix (Fin n) (Fin n) v.O := fun i j => ⟨u i j, (Valuation.mem_valuationSubring_iff _ _).2 (hu i j)⟩
  have hM : M.map v.O.subtype = u := by ext i j; rfl
  constructor
  · have e : u.det = ((M.det : v.O) : F) := by
      rw [← hM]; exact (RingHom.map_det v.O.subtype M).symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.det).2
  · intro i j
    have e : u.adjugate i j = ((M.adjugate i j : v.O) : F) := by
      rw [← hM]
      have := congrFun (congrFun (RingHom.map_adjugate v.O.subtype M) i) j
      exact this.symm
    rw [e]
    exact (Valuation.mem_valuationSubring_iff _ _).1 (M.adjugate i j).2
end GlobalTheory.Nef.OrdCalc

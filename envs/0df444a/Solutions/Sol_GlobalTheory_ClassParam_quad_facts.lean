-- Prove2me | solution 1 for GlobalTheory.ClassParam.quad_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:13:28.789239+00:00
-- url     : https://prove2.me/submissions/d86782ab-1a17-4396-b521-3d6822c1f190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution [CharZero F] (h2 : Module.finrank F E = 2) (hc1 : c ≠ 1) :
    (∀ e, c (c e) = e) ∧ ∀ e, c e = e → ∃ a, algebraMap F E a = e := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  refine ⟨fun e => ?_, fun e he => ?_⟩
  · have : c ^ 2 = 1 := hcard ▸ pow_card_eq_one'
    rw [pow_two] at this
    exact AlgEquiv.congr_fun this e
  · refine (IsGalois.mem_range_algebraMap_iff_fixed e).2 fun f => ?_
    by_cases hf : f = 1
    · rw [hf]; rfl
    · rw [(hy f hf).trans (hy c hc1).symm, he]
end GlobalTheory.ClassParam

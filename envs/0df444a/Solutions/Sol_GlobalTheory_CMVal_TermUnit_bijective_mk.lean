-- Prove2me | solution 1 for GlobalTheory.CMVal.TermUnit.bijective_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:08:18.268939+00:00
-- url     : https://prove2.me/submissions/0a5eae29-7a7e-4a97-bdda-90746b9e64ba

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
omit [NumberField E] [Fintype I]
namespace GlobalTheory.CMVal.TermUnit
theorem _root_.solution {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  constructor
  · intro i j hij
    have hj := InfinitePlace.mk_eq_iff.mp hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have e1 : i = k := hk i (hj.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))
    have e2 : j = k := hk j (Or.inl rfl)
    rw [e1, e2]
  · intro w
    obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    show InfinitePlace.mk (φ i) = w
    rcases hi with hi | hi
    · rw [← hi, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq (φ i), ← hi, InfinitePlace.mk_embedding]
end GlobalTheory.CMVal.TermUnit

-- Prove2me | solution 1 for GlobalTheory.IndexNormEmb.card_quot_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:44.224509+00:00
-- url     : https://prove2.me/submissions/a1208593-4da4-41cb-8f0d-a549394fba57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardQuotSpanEqFinsumLogNormEmbeddings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.IndexNormEmb
namespace GlobalTheory.IndexNormEmb
theorem _root_.solution (B : Type) [CommRing B] [IsDomain B] [Module.Free ℤ B] [Module.Finite ℤ B]
    (b : B) (hb : b ≠ 0) : Nat.card (B ⧸ Ideal.span {b}) = (Algebra.norm ℤ b).natAbs := by
  classical
  rw [Algebra.norm_apply]
  let bs := Module.Free.chooseBasis ℤ B
  have := Submodule.natAbs_det_equiv ((Ideal.span {b}).restrictScalars ℤ)
    (bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _))
  rw [show Nat.card (B ⧸ Ideal.span {b}) = Nat.card (B ⧸ (Ideal.span {b}).restrictScalars ℤ) from rfl,
    ← this]
  congr
  refine bs.ext fun i => ?_
  simp
  show ((bs.equiv (Ideal.basisSpanSingleton bs hb) (Equiv.refl _) (bs i) : Ideal.span {b}) : B) = b * bs i
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, Ideal.basisSpanSingleton_apply]
end GlobalTheory.IndexNormEmb

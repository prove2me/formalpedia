-- Prove2me | solution 1 for GlobalTheory.CardLength.lenAt_quot_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:09.413839+00:00
-- url     : https://prove2.me/submissions/f61582ec-7d63-4346-aaea-e2b4a465cae4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LogCardEqFinsumLengthLocalizedMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CardLength
variable {R : Type} [CommRing R]
namespace GlobalTheory.CardLength
theorem _root_.solution (w m : Ideal R) [hw : w.IsMaximal] [hm : m.IsMaximal] (h : w ≠ m) :
    lenAt w (R ⧸ m) = 0 := by
  refine Module.length_eq_zero_iff.2 ((IsLocalizedModule.subsingleton_iff w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl (R ⧸ m))).2 ?_)
  have hnle : ¬ m ≤ w := fun hle => h (hm.eq_of_le hw.ne_top hle).symm
  obtain ⟨s, hsm, hsw⟩ := SetLike.not_le_iff_exists.1 hnle
  intro x
  refine ⟨s, hsw, ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact m.mul_mem_right _ hsm
end GlobalTheory.CardLength

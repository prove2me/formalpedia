-- Prove2me | solution 1 for GlobalTheory.CardGLQuot.isUnit_quot_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:23:24.735467+00:00
-- url     : https://prove2.me/submissions/1fa98a0c-4cdd-4c93-93cc-1bc4240e7d8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardGLRingOfIntegersQuotientProdFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.CardGLQuot
namespace GlobalTheory.CardGLQuot
theorem _root_.solution {A : Type} [CommRing A] {w : Ideal A} (hw : w.IsMaximal) {c : ℕ} (hc : c ≠ 0)
    (x : A ⧸ w ^ c) : IsUnit x ↔ Ideal.Quotient.factor (Ideal.pow_le_self hc) x ≠ 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h ha
    have hU := h.map (Ideal.Quotient.factor (Ideal.pow_le_self hc))
    rw [Ideal.Quotient.factor_mk, (Ideal.Quotient.eq_zero_iff_mem).2 ha] at hU
    haveI := hw.isPrime
    exact not_isUnit_zero hU
  · intro ha
    obtain ⟨y, i, hi, hyx⟩ := hw.exists_inv ha
    have hnil : IsNilpotent (Ideal.Quotient.mk (w ^ c) i) :=
      ⟨c, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.pow_mem_pow hi c⟩
    have hu : IsUnit (Ideal.Quotient.mk (w ^ c) (y * a)) := by
      have := hnil.isUnit_one_sub
      rwa [← map_one (Ideal.Quotient.mk (w ^ c)), ← map_sub,
        show (1 : A) - i = y * a by rw [← hyx]; ring] at this
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
end GlobalTheory.CardGLQuot

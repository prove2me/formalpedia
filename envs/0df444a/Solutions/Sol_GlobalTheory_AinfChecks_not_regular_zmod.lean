-- Prove2me | solution 1 for GlobalTheory.AinfChecks.not_regular_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:04.98846+00:00
-- url     : https://prove2.me/submissions/4f59d0a6-0c49-46a0-873a-e0eb93d7f23f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_NonemptyAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WittVector Ideal ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.AinfChecks
namespace GlobalTheory.AinfChecks
theorem _root_.solution (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : ZMod p)) (_ : IsAdicComplete (span {((p : ℕ) : ZMod p)}) (ZMod p)),
      ¬ RegularStatement p (ZMod p) := by
  have h0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hb : span {((p : ℕ) : ZMod p)} = ⊥ := by rw [h0, span_singleton_eq_bot]
  have i1 : Fact ¬IsUnit ((p : ℕ) : ZMod p) := ⟨by rw [h0]; exact not_isUnit_zero⟩
  have i2 : IsAdicComplete (span {((p : ℕ) : ZMod p)}) (ZMod p) := by rw [hb]; infer_instance
  refine ⟨i1, i2, fun h => ?_⟩
  have hz : (0 : PreTilt (ZMod p) p).untilt = ((p : ℕ) : ZMod p) := by
    have := PreTilt.mk_untilt_eq_coeff_zero (0 : PreTilt (ZMod p) p)
    rw [map_zero (PreTilt.coeff 0), Ideal.Quotient.eq_zero_iff_mem, mem_span_singleton] at this
    exact (zero_dvd_iff.1 (h0 ▸ this)).trans h0.symm
  obtain ⟨-, h2, h3⟩ := h 0 hz
  apply h3
  have h1 := h2 1 (by rw [teichmuller_zero, zero_mul]; exact zero_mem _)
  rw [eq_top_iff_one]
  exact span_mono (by simp) h1
end GlobalTheory.AinfChecks

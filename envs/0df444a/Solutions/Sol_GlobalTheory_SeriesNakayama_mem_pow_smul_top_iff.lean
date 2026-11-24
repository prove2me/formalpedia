-- Prove2me | solution 1 for GlobalTheory.SeriesNakayama.mem_pow_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:45:34.28081+00:00
-- url     : https://prove2.me/submissions/c3142671-59f2-46cb-ad5a-efc629e6ab61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SpanModEquationsLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.SeriesNakayama
namespace GlobalTheory.SeriesNakayama
theorem _root_.solution {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (π : O)
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O M) ↔ ∃ y : M, π ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp
end GlobalTheory.SeriesNakayama

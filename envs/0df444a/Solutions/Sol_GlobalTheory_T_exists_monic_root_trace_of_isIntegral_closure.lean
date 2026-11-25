-- Prove2me | solution 1 for GlobalTheory.T.exists_monic_root_trace_of_isIntegral_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:05.049771+00:00
-- url     : https://prove2.me/submissions/60b2edd9-0dc7-4645-abb8-dd674e61f785

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceMonicOverMvPolynomial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceMonicOverMvPolynomialStatement
import Theorems.Thm_GlobalTheory_trace_monic_over_mvPolynomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K] {ι : Type} (z : ι → K), (∀ i, z i ∈ F) → ∀ (v : K), IsIntegral (Subring.closure (Set.range z)) v → ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧ f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  first | exact @GlobalTheory.trace_monic_over_mvPolynomial | exact GlobalTheory.trace_monic_over_mvPolynomial | (intros; apply GlobalTheory.trace_monic_over_mvPolynomial <;> assumption)
end _root_.GlobalTheory.T

-- Prove2me | solution 1 for GlobalTheory.TraceSumRealEmbeddings.trace_eq_sum_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:38:12.057161+00:00
-- url     : https://prove2.me/submissions/49f650f5-15d9-44eb-98d1-b1dd9d01dcad

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDualIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TraceInfAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceSumRealEmbeddings
open NumberField NumberField.InfinitePlace
namespace GlobalTheory.TraceSumRealEmbeddings
theorem _root_.solution (F : Type) [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ x := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => φ x) (fun σ => σ x) (fun φ => rfl),
      ← trace_eq_sum_embeddings]
    exact (eq_ratCast (algebraMap ℚ ℂ) _).symm
  rw [← Complex.re_sum, ← h2, Complex.ratCast_re]
end GlobalTheory.TraceSumRealEmbeddings

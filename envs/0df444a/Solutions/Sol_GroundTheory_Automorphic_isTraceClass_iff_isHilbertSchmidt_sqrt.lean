-- Prove2me | solution 1 for GroundTheory.Automorphic.isTraceClass_iff_isHilbertSchmidt_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:23:53.917848+00:00
-- url     : https://prove2.me/submissions/0f2f71fd-91a9-463c-b292-dd7d96333a9a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_TraceClass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace GroundTheory.Automorphic
theorem _root_.solution (T : H →L[ℂ] H) :
    IsTraceClass T ↔ IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) := by
  rw [IsTraceClass, traceNorm_eq_hsNormSq, IsHilbertSchmidt]
end GroundTheory.Automorphic

-- Prove2me | solution 1 for GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:54.756836+00:00
-- url     : https://prove2.me/submissions/b02a9283-0723-480b-b194-6e74e372a016

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedAdjoinRootOfSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ReducedAdjoinRootSeparable
namespace GlobalTheory.ReducedAdjoinRootSeparable
theorem _root_.solution {k : Type} [Field k] {f : Polynomial k}
    (hf : f.Separable) : IsReduced (AdjoinRoot f) := by
  have h1 : IsRadical f := isRadical_iff_squarefree_or_zero.2 (Or.inl hf.squarefree)
  have h2 : (Ideal.span {f}).IsRadical := isRadical_iff_span_singleton.1 h1
  exact (Ideal.isRadical_iff_quotient_reduced _).1 h2
end GlobalTheory.ReducedAdjoinRootSeparable

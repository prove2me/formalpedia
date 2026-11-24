-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenProd.glue_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:05.232215+00:00
-- url     : https://prove2.me/submissions/5ae3216a-027c-4614-b5c4-d14aa2bada79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.TraceOpenProd
variable {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
  {a₁ b₁ : R₁} {a₂ b₂ : R₂}
namespace GlobalTheory.QSA.TraceOpenProd
theorem _root_.solution (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : glue (fst x, snd x) = x := by
  ext <;> rfl
end GlobalTheory.QSA.TraceOpenProd

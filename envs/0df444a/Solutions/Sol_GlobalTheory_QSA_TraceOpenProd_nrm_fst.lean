-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenProd.nrm_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:06.034191+00:00
-- url     : https://prove2.me/submissions/f8ac7df5-ae27-4376-8d73-ca2cbb9166e7

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
theorem _root_.solution (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : nrm (fst x) = (nrm x).1 := by
  simp [nrm, fst]
end GlobalTheory.QSA.TraceOpenProd

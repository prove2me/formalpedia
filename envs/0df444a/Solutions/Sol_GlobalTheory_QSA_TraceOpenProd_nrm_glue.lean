-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenProd.nrm_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:45:06.954347+00:00
-- url     : https://prove2.me/submissions/2f8273ce-03bc-47aa-b744-a9bb17d5c394

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
theorem _root_.solution (p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂]) : nrm (glue p) = (nrm p.1, nrm p.2) := by
  ext <;> simp [nrm, glue]
end GlobalTheory.QSA.TraceOpenProd

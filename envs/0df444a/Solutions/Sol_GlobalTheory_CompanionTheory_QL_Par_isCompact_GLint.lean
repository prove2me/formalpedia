-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Par.isCompact_GLint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:20.662037+00:00
-- url     : https://prove2.me/submissions/134a09ce-8451-4852-b6ab-e395e2841d3d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isOpen_GLint
import Theorems.Thm_GlobalTheory_CompanionTheory_QL_Par_isCompact_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Par
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
namespace GlobalTheory.CompanionTheory.QL.Par
theorem _root_.solution (h : LF O ϖ nrm q) (n : ℕ) : IsCompact (GLint O n : Set (GL (Fin n) F)) := by
  haveI : T2Space F := by
    letI := IsTopologicalAddGroup.rightUniformSpace F
    haveI := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have hc := isCompact_int h n
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) F)).isCompact_preimage
    (hc.prod (hc.image MulOpposite.continuous_op))
  refine h2.of_isClosed_subset ((GLint O n).isClosed_of_isOpen (isOpen_GLint h n)) ?_
  intro x hx
  exact ⟨hx.1, _, hx.2, rfl⟩
end GlobalTheory.CompanionTheory.QL.Par

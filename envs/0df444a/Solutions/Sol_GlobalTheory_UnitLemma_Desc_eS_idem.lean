-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.eS_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:14.355434+00:00
-- url     : https://prove2.me/submissions/07576d18-8200-4356-8a68-0de611832e87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_e_mul_eS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  show (∑ i ∈ I, e i) * eS B e I = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [e_mul_eS B he, if_pos hi]
end GlobalTheory.UnitLemma.Desc

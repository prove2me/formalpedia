-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.e_mul_eS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:44.861196+00:00
-- url     : https://prove2.me/submissions/e7f2c7bd-b029-420f-b7fc-dc5d765a7c83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties

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
theorem _root_.solution {e : ι → B.A} (he : OrthogonalIdempotents e) (i : ι) (I : Finset ι) :
    e i * eS B e I = if i ∈ I then e i else 0 := by
  unfold eS; rw [Finset.mul_sum]; split_ifs with h
  · rw [Finset.sum_eq_single i (fun j _ hji => he.ortho (Ne.symm hji)) (fun h' => absurd h h'), (he.idem i).eq]
  · exact Finset.sum_eq_zero fun j hj => he.ortho (fun hij => h (hij ▸ hj))
end GlobalTheory.UnitLemma.Desc

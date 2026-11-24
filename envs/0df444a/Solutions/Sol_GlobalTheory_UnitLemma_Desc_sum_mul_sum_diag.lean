-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.sum_mul_sum_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:59:07.62636+00:00
-- url     : https://prove2.me/submissions/384520d2-0eb7-400e-a99f-929d9885a07b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_mul_eq_zero_of_idem

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
theorem _root_.solution {e : ι → B.A} (he : OrthogonalIdempotents e) (s : Finset ι) (a b : ι → B.A)
    (ha : ∀ i ∈ s, a i * e i = a i) (hb : ∀ i ∈ s, b i * e i = b i) :
    (∑ i ∈ s, a i) * (∑ j ∈ s, b j) = ∑ i ∈ s, a i * b i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact Finset.sum_eq_single i (fun j hj hji => mul_eq_zero_of_idem B he (Ne.symm hji) (ha i hi) (hb j hj))
    (fun h => absurd hi h)
end GlobalTheory.UnitLemma.Desc

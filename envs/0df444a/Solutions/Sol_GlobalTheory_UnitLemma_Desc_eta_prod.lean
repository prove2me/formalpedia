-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.eta_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:52:01.536395+00:00
-- url     : https://prove2.me/submissions/a1ef1d00-77ae-443a-ad5e-ce7e80c3c1db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
import Theorems.Thm_GlobalTheory_UnitLemma_Desc_eta_mul


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
theorem _root_.solution {s : Finset ι} (x : ι → K.E) (hx : ∀ i ∈ s, x i ≠ 0) :
    K.eta (∏ i ∈ s, x i) = ∏ i ∈ s, K.eta (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [UQ.eta, val]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      eta_mul (hx a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]
end GlobalTheory.UnitLemma.Desc

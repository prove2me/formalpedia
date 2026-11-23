-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.mul_eq_zero_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:41.754126+00:00
-- url     : https://prove2.me/submissions/56b0b0b5-73c1-4b4b-89d1-d639195eb775

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
theorem _root_.solution {e : ι → B.A} (he : OrthogonalIdempotents e) {i j : ι} (hij : i ≠ j) {a b : B.A}
    (ha : a * e i = a) (hb : b * e j = b) : a * b = 0 := by
  rw [← ha, ← hb, show a * e i * (b * e j) = a * b * (e i * e j) by ring, he.ortho hij, mul_zero]
end GlobalTheory.UnitLemma.Desc

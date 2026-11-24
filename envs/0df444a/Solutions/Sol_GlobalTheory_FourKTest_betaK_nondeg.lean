-- Prove2me | solution 1 for GlobalTheory.FourKTest.betaK_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:53:40.736276+00:00
-- url     : https://prove2.me/submissions/5803377c-31da-4874-b24c-89452ff7018d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierTransformKProdLocallyConstantCompactSuppo
import Theorems.Thm_GlobalTheory_FourKTest_betaK_apply
import Theorems.Thm_GlobalTheory_FourKTest_betaK_isSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.FourKTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.FourKTest
theorem _root_.solution (A : Et F E) (h : (Algebra.traceForm F A.K).Nondegenerate) : (betaK A).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (betaK A) := by
    intro x hx
    have h1 : x.1 = 0 := h.1 x.1 fun z => by
      have := hx (0, z); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    have h2 : x.2 = 0 := h.1 x.2 fun z => by
      have := hx (z, 0); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    exact Prod.ext h1 h2
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [(betaK_isSymm A).eq]; exact hy x
end GlobalTheory.FourKTest

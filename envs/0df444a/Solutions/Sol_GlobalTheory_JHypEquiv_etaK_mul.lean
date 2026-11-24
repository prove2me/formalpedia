-- Prove2me | solution 1 for GlobalTheory.JHypEquiv.etaK_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:50:18.804777+00:00
-- url     : https://prove2.me/submissions/3e4e462e-75e3-4310-8519-44a0cf4b58b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypUnipotentTorusEquivariance
import Theorems.Thm_GlobalTheory_T_unramifiedValuationParitySign_character_kernel_norms


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JHypEquiv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JHypEquiv
theorem _root_.solution [Unram F E] (A : Et F E) (s : A.Kˣ) (u : A.K) (hu : IsUnit u) :
    A.etaK ((s : A.K) * u) = A.etaK s * A.etaK u := by
  unfold Et.etaK
  rw [map_mul]
  exact (GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms F E).1 _ _ (s.isUnit.map (Algebra.norm F)).ne_zero (hu.map (Algebra.norm F)).ne_zero
end GlobalTheory.JHypEquiv

-- Prove2me | solution 1 for GlobalTheory.JR.Et.psiK_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:58:16.71471+00:00
-- url     : https://prove2.me/submissions/76f50737-057c-4143-9b97-c4b8daa31f13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerSwap
import Theorems.Thm_GlobalTheory_JR_DualLattice_stdChar_continuous


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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.Et
theorem _root_.solution (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (A.psiK ψ) := by
  have h1 : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  exact (DualLattice.stdChar_continuous hψ).comp h1
end GlobalTheory.JR.Et

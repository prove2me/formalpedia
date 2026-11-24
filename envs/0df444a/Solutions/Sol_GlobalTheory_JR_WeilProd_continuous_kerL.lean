-- Prove2me | solution 1 for GlobalTheory.JR.WeilProd.continuous_kerL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:14:14.665795+00:00
-- url     : https://prove2.me/submissions/640f2928-3ef0-4dbb-bbb3-7a2cf48f2121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
import Theorems.Thm_GlobalTheory_JR_DualLattice_stdChar_continuous
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L


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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilProd
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilProd
theorem _root_.solution [U : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) :
    Continuous (fun p : A.L × A.L => A.kerL ψ x p.1 p.2) := by
  have := U.ultraF; have := U.lcF; have := EtMeas.finite_L A
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  let T : A.L →ₗ[F] F :=
    (Algebra.trace F A.K).comp ((LinearMap.mul F A.K x).comp ((Algebra.trace A.K A.L).restrictScalars F))
  have hT : Continuous T := IsModuleTopology.continuous_of_linearMap T
  have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
  exact (DualLattice.stdChar_continuous hψ).comp (hT.comp ((hs.comp continuous_fst).mul continuous_snd))
end GlobalTheory.JR.WeilProd

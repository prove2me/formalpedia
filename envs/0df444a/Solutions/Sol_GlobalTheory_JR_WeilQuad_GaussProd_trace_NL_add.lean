-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.GaussProd.trace_NL_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:46.281886+00:00
-- url     : https://prove2.me/submissions/59f69ae0-2726-4982-a084-3c064164d6cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussIntegralOneMulGaussIntegralNegOneEqOne
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussProd_NL_add
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.GaussProd
open GlobalTheory.JR.WeilQuad.FourierTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad.GaussProd
theorem _root_.solution [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (t u : A.L) :
    Algebra.trace F A.K (x * A.NL (t + u)) =
      Algebra.trace F A.K (x * A.NL t) + Algebra.trace F A.K (x * A.NL u) + beta A x t u := by
  rw [NL_add A hK hL, mul_add, mul_add, map_add, map_add, beta_apply]
end GlobalTheory.JR.WeilQuad.GaussProd

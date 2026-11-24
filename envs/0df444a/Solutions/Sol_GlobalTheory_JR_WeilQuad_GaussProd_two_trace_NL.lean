-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.GaussProd.two_trace_NL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:11.54545+00:00
-- url     : https://prove2.me/submissions/d05504de-455c-4dd4-aea3-081facaadbe2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussIntegralOneMulGaussIntegralNegOneEqOne
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_algMap_inj
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_beta_apply
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


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
theorem _root_.solution [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) (y : A.L) :
    2 * Algebra.trace F A.K (x * A.NL y) = beta A x y y := by
  rw [beta_apply]
  have h : Algebra.trace A.K A.L (star y * y) = A.NL y + A.NL y := by
    apply algMap_inj A hK hL
    rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, map_add, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).1, star_mul, star_star]
    ring
  rw [h, mul_add, map_add, two_mul]
end GlobalTheory.JR.WeilQuad.GaussProd

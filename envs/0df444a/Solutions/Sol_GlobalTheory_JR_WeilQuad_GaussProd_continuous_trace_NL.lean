-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.GaussProd.continuous_trace_NL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:48.081533+00:00
-- url     : https://prove2.me/submissions/e35d42ca-a900-49fe-b06f-a3dadbade4cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussIntegralOneMulGaussIntegralNegOneEqOne
import Theorems.Thm_GlobalTheory_JR_WeilQuad_GaussProd_two_trace_NL
import Theorems.Thm_GlobalTheory_JR_WeilQuad_FourierTest_finite_F_L


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
theorem _root_.solution [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    Continuous fun y : A.L => Algebra.trace F A.K (x * A.NL y) := by
  haveI := finite_F_L A
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hβc : Continuous (fun p : A.L × A.L => beta A x p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left (beta A x)
  have hdiag : Continuous (fun y : A.L => (y, y)) := continuous_id.prodMk continuous_id
  have hcomp : Continuous ((fun p : A.L × A.L => beta A x p.1 p.2) ∘ (fun y : A.L => (y, y))) :=
    hβc.comp hdiag
  have hd : Continuous (fun y : A.L => (2 : F)⁻¹ * beta A x y y) := continuous_const.mul hcomp
  refine hd.congr (fun y => ?_)
  show (2 : F)⁻¹ * beta A x y y = Algebra.trace F A.K (x * A.NL y)
  rw [← two_trace_NL A hK hL x y, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
end GlobalTheory.JR.WeilQuad.GaussProd

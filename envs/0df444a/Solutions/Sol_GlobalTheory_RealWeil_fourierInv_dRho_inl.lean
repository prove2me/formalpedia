-- Prove2me | solution 1 for GlobalTheory.RealWeil.fourierInv_dRho_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:53.312814+00:00
-- url     : https://prove2.me/submissions/03517e6a-3b52-45dd-b32d-120bb6779ee0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inl
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
namespace GlobalTheory.RealWeil
theorem _root_.solution (j : l) (f : Sch l) :
    𝓕⁻ (dRho (Pi.single (Sum.inl j) 1) f) = -dRho (Pi.single (Sum.inr j) 1) (𝓕⁻ f) := by
  rw [dRho_single_inl, fourierInv_lineDerivOp_eq]
  ext x
  have : (fun y : EuclideanSpace ℝ l => y j).HasTemperateGrowth :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).hasTemperateGrowth
  simp [dRho_single_inr, EuclideanSpace.inner_single_right, this, mul_assoc]
end GlobalTheory.RealWeil

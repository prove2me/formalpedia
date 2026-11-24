-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:44:43.833816+00:00
-- url     : https://prove2.me/submissions/7b403ede-13dc-408e-884e-f457f1aa47e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VacuumProjectorRangeAnnihilated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.Mem.Lift.VacAnn
open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
private theorem hasFDerivAt_gau {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w : V) :
    HasFDerivAt (_root_.GlobalTheory.RealWeil.gau : V → ℂ)
      ((-(Real.pi : ℂ) * _root_.GlobalTheory.RealWeil.gau w) • ((Complex.ofRealCLM).comp (innerSL ℝ w))) w := by
  have h1 : HasFDerivAt (fun u : V => ‖u‖ ^ 2) (2 • innerSL ℝ w) w := by
    simpa using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt).comp w h1
  have h3 := (h2.const_mul (-(Real.pi : ℂ) / 2)).cexp
  have hf : (_root_.GlobalTheory.RealWeil.gau : V → ℂ) =
      fun u => Complex.exp (-(Real.pi : ℂ) / 2 * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u; unfold _root_.GlobalTheory.RealWeil.gau; push_cast; ring_nf
  rw [hf]
  refine h3.congr_fderiv ?_
  ext y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  push_cast
  ring
end GlobalTheory.Mem.Lift.VacAnn
end

set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.VacAnn
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
namespace GlobalTheory.Mem.Lift.VacAnn
namespace _root_.GlobalTheory.Mem.Lift.VacAnn
theorem _root_.solution {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w v : V) :
    fderiv ℝ (_root_.GlobalTheory.RealWeil.gau : V → ℂ) w v =
      -(Real.pi : ℂ) * ⟪w, v⟫ * _root_.GlobalTheory.RealWeil.gau w := by
  rw [(hasFDerivAt_gau w).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]
  ring
end _root_.GlobalTheory.Mem.Lift.VacAnn
end GlobalTheory.Mem.Lift.VacAnn

-- Prove2me | solution 1 for GlobalTheory.RealWeil.contDiff_gau
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:53:57.670509+00:00
-- url     : https://prove2.me/submissions/c8dfe87a-7490-4edc-9fda-dc1c52540cc8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowMulNormGauLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ContDiff ℝ ∞ (gau : V → ℂ) := by
  have e : (gau : V → ℂ) = fun u => cexp (-(π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    simp only [gau]
    push_cast
    rfl
  rw [e]
  have hn : ContDiff ℝ ∞ (fun u : V => ‖u‖ ^ 2) := contDiff_norm_sq ℝ
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hn))
end GlobalTheory.RealWeil

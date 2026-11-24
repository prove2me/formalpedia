-- Prove2me | solution 1 for GlobalTheory.T.fourier_comp_coordDilationByHalfExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:09:35.101574+00:00
-- url     : https://prove2.me/submissions/b72472fb-d9d6-4ee8-9643-5731c54317ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FourierCompCoordDilationByHalfExpStatement
import Theorems.Thm_GlobalTheory_HeckePoisson_Dilation_fourier_comp_dil


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ) (l : EuclideanSpace ℂ I), 𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l = (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  first | exact @GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | exact GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil | (intros; apply GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil <;> assumption)
end _root_.GlobalTheory.T

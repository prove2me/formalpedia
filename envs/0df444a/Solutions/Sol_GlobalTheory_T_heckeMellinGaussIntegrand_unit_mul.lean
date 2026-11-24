-- Prove2me | solution 1 for GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:14.17081+00:00
-- url     : https://prove2.me/submissions/97dd512c-3a8b-4caf-a4f4-c931ca1a8e85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMulStatement
import Theorems.Thm_GlobalTheory_HeckeShift_term_unit_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ), GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y = GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  first | exact @GlobalTheory.HeckeShift.term_unit_mul | exact GlobalTheory.HeckeShift.term_unit_mul | (intros; apply GlobalTheory.HeckeShift.term_unit_mul <;> assumption)
end _root_.GlobalTheory.T

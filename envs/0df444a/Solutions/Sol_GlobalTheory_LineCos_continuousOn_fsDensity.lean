-- Prove2me | solution 1 for GlobalTheory.LineCos.continuousOn_fsDensity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:26.871807+00:00
-- url     : https://prove2.me/submissions/7b5209ad-4828-4fc7-9158-7dcabb29829f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
import Theorems.Thm_GlobalTheory_LineCos_lineVec_ne_zero
import Theorems.Thm_GlobalTheory_LineCos_re_hform_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution {d : ℕ} {O : Set (V (d + 1))} {G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ} (s : Bool)
    (hc : ContinuousOn (fun z => G (base z)) O) (hp : ∀ z ∈ O, (G (base z)).PosDef) :
    ContinuousOn (fun z => fsDensity s (G (base z)) (fib z)) O := by
  have he : ∀ i j, ContinuousOn (fun z => G (base z) i j) O := fun i j =>
    (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc)
  have hx : Continuous (fun z : V (d + 1) => fib z) := by
    unfold fib
    fun_prop
  have hw : ∀ i, Continuous (fun z : V (d + 1) => lineVec s (fib z) i) := fun i => by
    cases s
    · fin_cases i
      · exact continuous_const
      · exact hx
    · fin_cases i
      · exact hx
      · exact continuous_const
  have hh : ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))) O := by
    unfold hform
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    exact (((hw i).mul ((Complex.continuous_conj).comp (hw j))).continuousOn).mul (he i j)
  have hdet : ContinuousOn (fun z => (G (base z)).det) O :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine (Complex.continuous_re.comp_continuousOn hdet).div
    (continuousOn_const.mul ((Complex.continuous_re.comp_continuousOn hh).pow 2)) fun z hz => ?_
  exact (mul_pos Real.pi_pos (pow_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) 2)).ne'
end GlobalTheory.LineCos

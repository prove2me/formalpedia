-- Prove2me | solution 1 for GlobalTheory.LineCos.continuousOn_cosSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:51.672985+00:00
-- url     : https://prove2.me/submissions/d8277d5d-227e-49c5-b870-51d63ff7464d

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Theorems.Thm_GlobalTheory_LineCos_re_hform_pos
import Theorems.Thm_GlobalTheory_LineCos_lineVec_ne_zero
import Theorems.Thm_GlobalTheory_LineCos_re_corner_pos

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
open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution {d : ℕ} {O : Set (V (d + 1))} {G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ} (s : Bool)
    (hc : ContinuousOn (fun z => G (base z)) O) (hp : ∀ z ∈ O, (G (base z)).PosDef) :
    ContinuousOn (fun z => cosSq s (G (base z)) (fib z)) O := by
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
  have hh : ∀ (b : V (d + 1) → Fin 2 → ℂ), (∀ j, Continuous fun z => b z j) →
      ContinuousOn (fun z => hform (G (base z)) (lineVec s (fib z)) (b z)) O := fun b hb => by
    unfold hform
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    exact (((hw i).mul ((Complex.continuous_conj).comp (hb j))).continuousOn).mul (he i j)
  have hn : ContinuousOn (fun z => ‖hform (G (base z)) (lineVec s (fib z)) (Pi.single (0 : Fin 2) (1 : ℂ))‖ ^ 2) O :=
    (hh (fun _ => Pi.single (0 : Fin 2) (1 : ℂ)) fun j => continuous_const).norm.pow 2
  have hd : ContinuousOn (fun z => (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re) O :=
    (Complex.continuous_re.comp_continuousOn (hh (fun z => lineVec s (fib z)) hw)).mul (Complex.continuous_re.comp_continuousOn (he 0 0))
  have h0 : ∀ z ∈ O, (hform (G (base z)) (lineVec s (fib z)) (lineVec s (fib z))).re * (G (base z) 0 0).re ≠ 0 :=
    fun z hz => (mul_pos (re_hform_pos (hp z hz) (lineVec_ne_zero s _)) (re_corner_pos (hp z hz))).ne'
  exact hn.div hd h0
end GlobalTheory.LineCos

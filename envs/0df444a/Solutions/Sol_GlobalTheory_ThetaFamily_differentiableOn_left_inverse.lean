-- Prove2me | solution 1 for GlobalTheory.ThetaFamily.differentiableOn_left_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:07.624365+00:00
-- url     : https://prove2.me/submissions/ea6b564b-9ee2-4dab-9676-fc4b826189a6

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_differentiableOn_det_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaFamily
namespace GlobalTheory.ThetaFamily
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : Type} [Fintype n]
    [DecidableEq n] {B : Set V} {M h : V → Matrix n n ℂ} (hM : ∀ i j, DifferentiableOn ℂ (fun b => M b i j) B)
    (hh : ∀ b ∈ B, h b * M b = 1) (i j : n) : DifferentiableOn ℂ (fun b => h b i j) B := by
  have hdet : ∀ {N : V → Matrix n n ℂ}, (∀ i j, DifferentiableOn ℂ (fun b => N b i j) B) →
      DifferentiableOn ℂ (fun b => (N b).det) B := fun {N} hN => by
    exact ReciprocityTheory.MultiplicativeHeights.differentiableOn_det_of (F := fun i j b => N b i j) hN
  have hne : ∀ b ∈ B, (M b).det ≠ 0 := fun b hb => (Matrix.isUnit_det_of_left_inverse (hh b hb)).ne_zero
  refine (((hdet hM).inv hne).mul (hdet (N := fun b => (M b).updateRow j (Pi.single i 1)) fun k l => ?_)).congr
    fun b hb => ?_
  · by_cases hk : k = j
    · simp only [hk, Matrix.updateRow_self]; exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hk]; exact hM k l
  · rw [← Matrix.inv_eq_left_inv (hh b hb), Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
      Ring.inverse_eq_inv', smul_eq_mul]
    rfl
end GlobalTheory.ThetaFamily

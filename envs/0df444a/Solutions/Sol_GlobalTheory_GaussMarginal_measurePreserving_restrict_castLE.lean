-- Prove2me | solution 1 for GlobalTheory.GaussMarginal.measurePreserving_restrict_castLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:59.125436+00:00
-- url     : https://prove2.me/submissions/03248f91-24db-49cf-8d08-06d1102c8c77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianFirstCoordsMeasurePreserving

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
noncomputable section
open GlobalTheory GlobalTheory.GaussMarginal
open Real
namespace GlobalTheory.GaussMarginal
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {N n : ℕ} (h : N ≤ n) :
    MeasurePreserving (fun (y : Fin n → α) (j : Fin N) => y (Fin.castLE h j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hr : Measurable fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  refine ⟨hr, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  have hpre : (fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j)) ⁻¹' univ.pi s =
      univ.pi (Fin.append s fun _ : Fin m => (univ : Set α)) := by
    ext y
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hy i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hy j
      · rw [Fin.append_right]; exact mem_univ _
    · intro hy j
      have := hy (Fin.castAdd m j)
      rwa [Fin.append_left] at this
  rw [hpre, Measure.pi_pi, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]
end GlobalTheory.GaussMarginal

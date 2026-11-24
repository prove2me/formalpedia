-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.measurePreserving_joinEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:47:15.790849+00:00
-- url     : https://prove2.me/submissions/82aee7ff-26e7-4c9e-82a8-f4c2d409d520

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumn
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurePreserving_funUnique_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) :
    MeasurePreserving
      (fun p : ℂ × ({j : α // j ≠ j₀} → ℂ) =>
        (fun j => if h : j = j₀ then p.1 else p.2 ⟨j, h⟩ : α → ℂ))
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      (Measure.pi fun _ : α => (volume : Measure ℂ)) := by
  haveI : Unique {j : α // ¬ j ≠ j₀} :=
    { default := ⟨j₀, by simp⟩
      uniq := fun x => Subtype.ext (by simpa using x.2) }
  have h1 := (measurePreserving_piEquivPiSubtypeProd (fun _ : α => (volume : Measure ℂ))
    (fun j => j ≠ j₀)).symm
  have h2 : MeasurePreserving (MeasurableEquiv.funUnique {j : α // ¬ j ≠ j₀} ℂ).symm
      (volume : Measure ℂ) (Measure.pi fun _ : {j : α // ¬ j ≠ j₀} => (volume : Measure ℂ)) :=
    measurePreserving_funUnique_symm
  have h3 := (MeasurePreserving.id
    (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ))).prod h2
  have h4 : MeasurePreserving (Prod.swap : ℂ × ({j : α // j ≠ j₀} → ℂ) → _)
      ((volume : Measure ℂ).prod (Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)))
      ((Measure.pi fun _ : {j : α // j ≠ j₀} => (volume : Measure ℂ)).prod (volume : Measure ℂ)) :=
    Measure.measurePreserving_swap
  have h5 := h1.comp (h3.comp h4)
  convert h5 using 1
  funext p j
  by_cases h : j = j₀
  · subst h
    simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]
  · simp [MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, h]
end GlobalTheory.CompanionTheory.FSCrofton

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KerAdj.pairing_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:48:30.667639+00:00
-- url     : https://prove2.me/submissions/a520887d-5959-4d95-9281-f8946e499722

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerEqIntegralConjMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KerAdj
namespace GlobalTheory.CompanionTheory.KerAdj
theorem _root_.solution {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    (k : α → α → ℂ) (g f : α → ℂ)
    (h : Integrable (fun p : α × α => conj (g p.1) * k p.1 p.2 * f p.2) (ν.prod ν)) :
    Integrable (fun x => conj (∫ y, conj (k y x) * g y ∂ν) * f x) ν ∧
    Integrable (fun y => conj (g y) * ∫ x, k y x * f x ∂ν) ν ∧
    ∫ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x ∂ν
      = ∫ y, conj (g y) * ∫ x, k y x * f x ∂ν ∂ν := by
  have hL : ∀ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x
      = ∫ y, conj (g y) * k y x * f x ∂ν := by
    intro x
    rw [← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  have hR : ∀ y, conj (g y) * ∫ x, k y x * f x ∂ν
      = ∫ x, conj (g y) * k y x * f x ∂ν := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hL]
    exact h.swap.integral_prod_left
  · simp_rw [hR]
    exact h.integral_prod_left
  · simp_rw [hL, hR]
    exact (integral_integral_swap (f := fun y x => conj (g y) * k y x * f x) h).symm
end GlobalTheory.CompanionTheory.KerAdj

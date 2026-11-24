-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Schur.schur_memLp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:57.233795+00:00
-- url     : https://prove2.me/submissions/56545357-71bc-4436-b9f2-6c7c1a94c926

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchurOpOfSchurL
import Theorems.Thm_GlobalTheory_CompanionTheory_Schur_eLpNorm_two_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Schur
open PositivityTheory.Rg.BcB.E1
variable {α : Type} [MeasurableSpace α] {ν : Measure α}
namespace GlobalTheory.CompanionTheory.Schur
theorem _root_.solution (hS : SchurL) [SFinite ν] (k : α → α → ℂ) (A : ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) (hA : A ≠ ⊤)
    (hr : ∀ x, ∫⁻ y, ‖k x y‖ₑ ∂ν ≤ A) (hc : ∀ y, ∫⁻ x, ‖k x y‖ₑ ∂ν ≤ A)
    (g : α → ℂ) (hg : MemLp g 2 ν) :
    MemLp (fun x => ∫ y, k x y * g y ∂ν) 2 ν ∧
      eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν ∧
      ∀ᵐ x ∂ν, Integrable (fun y => k x y * g y) ν := by
  have hkK : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.enorm
  have hgm : AEMeasurable (fun y => ‖g y‖ₑ) ν := hg.1.enorm
  have key := hS α ν (fun x y => ‖k x y‖ₑ) A (fun y => ‖g y‖ₑ) hkK hgm hr hc
  have hgfin : eLpNorm g 2 ν ≠ ⊤ := hg.2.ne
  have hsq : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν = eLpNorm g 2 ν ^ 2 := (eLpNorm_two_sq g).symm
  have hbound : ∫⁻ x, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 ∂ν ≤ (A * eLpNorm g 2 ν) ^ 2 := by
    rw [mul_pow, ← hsq]; exact key
  have hfin : (A * eLpNorm g 2 ν) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.mul_ne_top hA hgfin)
  have hprod : AEStronglyMeasurable (fun p : α × α => k p.1 p.2 * g p.2) (ν.prod ν) :=
    (hk.stronglyMeasurable.aestronglyMeasurable).mul hg.1.comp_snd
  have hSm : AEStronglyMeasurable (fun x => ∫ y, k x y * g y ∂ν) ν :=
    hprod.integral_prod_right'
  have hhm : AEMeasurable (fun x => ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ν := by
    have : AEMeasurable (fun p : α × α => ‖k p.1 p.2‖ₑ * ‖g p.2‖ₑ) (ν.prod ν) := by
      simpa [enorm_mul] using hprod.enorm
    exact this.lintegral_prod_right'
  have hle : eLpNorm (fun x => ∫ y, k x y * g y ∂ν) 2 ν ≤ A * eLpNorm g 2 ν := by
    refine (ENNReal.pow_right_strictMono two_ne_zero).le_iff_le.1 ?_
    rw [eLpNorm_two_sq]
    refine le_trans (lintegral_mono fun x => ?_) hbound
    refine pow_le_pow_left' ?_ 2
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp [enorm_mul]
  refine ⟨⟨hSm, lt_of_le_of_lt hle (ENNReal.mul_ne_top hA hgfin).lt_top⟩, hle, ?_⟩
  have hae : ∀ᵐ x ∂ν, (∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν) ^ 2 < ⊤ :=
    ae_lt_top' (hhm.pow_const 2) (ne_top_of_le_ne_top hfin hbound)
  filter_upwards [hae] with x hx
  have hxf : ∫⁻ y, ‖k x y‖ₑ * ‖g y‖ₑ ∂ν < ⊤ := by
    refine lt_top_iff_ne_top.2 fun hcon => ?_
    simp [hcon] at hx
  have hkx : Measurable (k x) := hk.of_uncurry_left
  refine ⟨hkx.aestronglyMeasurable.mul hg.1, ?_⟩
  simpa [HasFiniteIntegral, enorm_mul] using hxf
end GlobalTheory.CompanionTheory.Schur

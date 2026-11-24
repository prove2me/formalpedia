-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KernelOperators.comp_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:02.472994+00:00
-- url     : https://prove2.me/submissions/e934c780-92cd-42f6-82c8-3ed966946ede

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CompKey

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KernelOperators
namespace GlobalTheory.CompanionTheory.KernelOperators
theorem _root_.solution (hB : KerBasic) (hR : RowInt) (hL : KernelL2RowsColumns) (hS : SchurInt) (hM : KerMul)
    (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ) (x : X.G) (f : X.G → ℂ)
    (hf : MemLp f 2 X.ν) :
    Integrable (fun z => ker X.Γ φ x z * ∫ y, ker X.Γ ψ z y * f y ∂X.ν) X.ν ∧
    ∫ z, ker X.Γ φ x z * (∫ y, ker X.Γ ψ z y * f y ∂X.ν) ∂X.ν
      = ∫ y, ker X.Γ (cv X.μ φ ψ) x y * f y ∂X.ν := by
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  obtain ⟨A, hA, hrow, hcol⟩ := hR X ψ hψ
  have hmeas : Measurable (Function.uncurry (ker X.Γ ψ)) := (hB X ψ hψ).2.1.measurable
  have hint := hS X.G X.ν (ker X.Γ ψ) A hmeas hA hrow hcol (fun z => ker X.Γ φ x z) f
    ((hL X φ hφ).2 x) hf
  have e1 : ∀ z, ∫ y, ker X.Γ φ x z * ker X.Γ ψ z y * f y ∂X.ν
      = ker X.Γ φ x z * ∫ y, ker X.Γ ψ z y * f y ∂X.ν := by
    intro z
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  constructor
  · have h := hint.integral_prod_left
    simpa only [e1] using h
  · have h := integral_integral_swap
      (f := fun z y => ker X.Γ φ x z * ker X.Γ ψ z y * f y) hint
    simp only [e1] at h
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [integral_mul_const]
    rw [hM X φ ψ hφ hψ x y]
end GlobalTheory.CompanionTheory.KernelOperators

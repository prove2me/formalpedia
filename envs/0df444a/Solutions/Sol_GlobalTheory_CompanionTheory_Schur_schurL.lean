-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Schur.schurL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:54:57.503537+00:00
-- url     : https://prove2.me/submissions/e577d86b-86a5-412b-8a59-dedd102ee37c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_KernelL2RowsColumns
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralWeightedSqLe
import Theorems.Thm_GlobalTheory_CompanionTheory_Schur_lintegral_weighted_sq_le

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Schur
namespace GlobalTheory.CompanionTheory.Schur
theorem _root_.solution : SchurL := by
  intro α _ ν _ k A f hk hf hrow hcol
  have hk1 : ∀ x, Measurable (k x) := fun x => hk.of_uncurry_left
  have hk2 : ∀ y, Measurable fun x => k x y := fun y => hk.of_uncurry_right
  have hgm : Measurable (hf.mk f) := hf.measurable_mk
  set g := hf.mk f with hgdef
  have hfg : f =ᵐ[ν] g := hf.ae_eq_mk
  have e1 : ∀ x, ∫⁻ y, k x y * f y ∂ν = ∫⁻ y, k x y * g y ∂ν := fun x =>
    lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  have e2 : ∫⁻ y, f y ^ 2 ∂ν = ∫⁻ y, g y ^ 2 ∂ν :=
    lintegral_congr_ae (hfg.mono fun y hy => by simp only [hy])
  have hF : Measurable (Function.uncurry fun x y => k x y * g y ^ 2) :=
    hk.mul ((hgm.pow_const 2).comp measurable_snd)
  have hQ : Measurable fun x => ∫⁻ y, k x y * g y ^ 2 ∂ν := hF.lintegral_prod_right'
  simp only [e1, e2]
  calc ∫⁻ x, (∫⁻ y, k x y * g y ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ x, A * ∫⁻ y, k x y * g y ^ 2 ∂ν ∂ν := by
        refine lintegral_mono fun x => ?_
        exact (lintegral_weighted_sq_le ν (k x) g (hk1 x) hgm).trans (by gcongr; exact hrow x)
    _ = A * ∫⁻ x, ∫⁻ y, k x y * g y ^ 2 ∂ν ∂ν := lintegral_const_mul _ hQ
    _ = A * ∫⁻ y, ∫⁻ x, k x y * g y ^ 2 ∂ν ∂ν := by
        rw [lintegral_lintegral_swap hF.aemeasurable]
    _ = A * ∫⁻ y, (∫⁻ x, k x y ∂ν) * g y ^ 2 ∂ν := by
        congr 1
        exact lintegral_congr fun y => lintegral_mul_const _ (hk2 y)
    _ ≤ A * ∫⁻ y, A * g y ^ 2 ∂ν := by
        gcongr with y
        exact hcol y
    _ = A ^ 2 * ∫⁻ y, g y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hgm.pow_const 2), sq, mul_assoc]
end GlobalTheory.CompanionTheory.Schur

-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.monomial_char_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:58:03.587922+00:00
-- url     : https://prove2.me/submissions/64cf4837-9f22-4ca4-aff9-2907e4e3c920

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_mono0_of_lpDim_eq_one
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpChar_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_lpSp
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDim_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpDual_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpChar_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_lpSp
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDim_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpDual_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.WD
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} [IsAlgClosure E Ω]
variable {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (a χ : WD h) (hχ : lpDim χ = 1) : mono0 (lpChar a χ) ↔ mono0 a := by
  have h0 := mono0_of_lpDim_eq_one hχ
  induction a using ind with
  | hP m a =>
  induction χ using ind with
  | hP n b =>
    rw [lpDim_mk] at hχ
    rw [monodromyZero_ofWeilDeligneRepClass_iff] at h0
    rw [lpChar_mk, monodromyZero_ofWeilDeligneRepClass_iff, monodromyZero_ofWeilDeligneRepClass_iff, WDRep.tensor_N, h0, LinearMap.lTensor_zero, add_zero]
    refine ⟨fun h1 => LinearMap.ext fun v => ?_, fun h1 => by rw [h1, LinearMap.rTensor_zero]⟩
    let e : (Fin n → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hχ, finrank_self])
    have h2 := congrArg (fun x => TensorProduct.rid ℂ _ (e.toLinearMap.lTensor _ x))
      (LinearMap.congr_fun h1 (v ⊗ₜ e.symm 1))
    simpa using h2
end GlobalTheory.WeilDeligne.WD

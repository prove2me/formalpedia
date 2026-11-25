-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WDRep.iso_tensor_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:47:52.598976+00:00
-- url     : https://prove2.me/submissions/c8b7d96d-60a1-4e91-8fb8-24a49c69ef9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LpCharCompatibilities
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
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' V'' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
  [AddCommGroup V''] [Module ℂ V''] [FiniteDimensional ℂ V'']
open GlobalTheory.WeilDeligne.WDRep
namespace GlobalTheory.WeilDeligne.WDRep
theorem _root_.solution (a : WDRep h V) (c : WDRep h V') (hN : c.N = 0) (hd : finrank ℂ V' = 1)
    (hρ : ∀ σ, c.ρ σ = 1) : (a.tensor c).Iso a := by
  let f : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq V' ℂ (by simpa using hd)
  refine ⟨(TensorProduct.congr (.refl ℂ V) f).trans (TensorProduct.rid ℂ V), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hρ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hN]
    | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.WeilDeligne.WDRep

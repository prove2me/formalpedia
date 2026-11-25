-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WDRep.charpoly_eq_mul_of_isCompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:02:57.515248+00:00
-- url     : https://prove2.me/submissions/b87db6b8-678c-49dc-ac5a-5bab275077fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_Mono0OfLpDimEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAevalEqSmulOnEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilDeligneInductionPrinciple
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
namespace GlobalTheory.WeilDeligne
namespace WDRep
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V) (U U' : Submodule ℂ V)
    (hU : ∀ σ, ∀ v ∈ U, a.ρ σ v ∈ U) (hU' : ∀ σ, ∀ v ∈ U', a.ρ σ v ∈ U') (hc : IsCompl U U')
    (σ : Weil h) :
    (a.ρ σ).charpoly = ((a.resZero U hU).ρ σ).charpoly * ((a.resZero U' hU').ρ σ).charpoly := by
  rw [← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl U U' hc)]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, rfl⟩ := (Submodule.prodEquivOfIsCompl U U' hc).surjective v
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  simp [Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]
end WDRep
end GlobalTheory.WeilDeligne

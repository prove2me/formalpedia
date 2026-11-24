-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.IsValChar.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:53:42.575814+00:00
-- url     : https://prove2.me/submissions/aa328097-83d2-4810-8d2a-e4d81cf26a7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_levelLe_inv
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_CMVal_hasInfRatio_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Model
namespace IsValChar
theorem _root_.solution {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (h : IsValChar φ s κ 𝔣 Q χ) :
    IsValChar (fun i => ComplexEmbedding.conjugate (φ i)) s κ 𝔣 Q χ⁻¹ := by
  obtain ⟨h1, ⟨h2, h2'⟩, h3, h4⟩ := h
  refine ⟨fun x => ?_, ⟨fun v k => ?_, fun w k => ?_⟩, (hasInfRatio_iff _ _ _).2 fun k => ?_, fun v P hP => ⟨fun hv => ?_, fun hv m => ?_⟩⟩
  · change ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_inv_eq_inv_val, norm_inv, h1 x, inv_one]
  · have h := h2 v k
    unfold Formalism.L2.Host.HChar.resFin at h ⊢
    rw [MonoidHom.finset_prod_apply] at h ⊢
    rw [← inv_eq_one, ← Finset.prod_inv_distrib] at h
    exact h
  · have h := h2' w k
    unfold Formalism.L2.Host.HChar.resInf at h ⊢
    rw [MonoidHom.finset_prod_apply] at h ⊢
    rw [← inv_eq_one, ← Finset.prod_inv_distrib] at h
    exact h
  · change (((χ.inf k)⁻¹ : ℂˣ) : ℂ) = _
    rw [Units.val_inv_eq_inv_val, (hasInfRatio_iff _ _ _).1 h3 k, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← inv_zpow, inv_div]
    simp
  · exact levelLe_inv.2 ((h4 v P hP).1 hv)
  · rw [levelLe_inv]; exact (h4 v P hP).2 hv m
end IsValChar
end GlobalTheory.CMVal.Model

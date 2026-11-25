-- Prove2me | solution 1 for GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:02:16.271452+00:00
-- url     : https://prove2.me/submissions/a9766ad9-12c0-4d52-890b-5c8240782ed2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
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
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_exists_den
import Theorems.Thm_ReciprocityTheory_Gal_primeBelow_smul
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
open GlobalTheory GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
namespace GlobalTheory.InertiaMovesRoot
theorem _root_.solution {σ : Ω ≃ₐ[E] Ω}
    (hσ : ∀ b : IntCl E Ω, σ • b - b ∈ primeBelow (F := E) A) : σ ∈ Ine (F := E) A := by
  have hc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1 :=
    fun b hb => hσ ⟨b, hb.tower_top⟩
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    let b' : IntCl E Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := E) (σ • A) ↔ b' ∈ primeBelow (F := E) A
    rw [primeBelow_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have := hσ (σ⁻¹ • b')
    rw [smul_inv_smul] at this
    exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩
  refine ⟨hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den E A hx
  have hσx : A.valuation (σ x) ≤ 1 := by
    rw [A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hdec, ← A.valuation_le_one_iff]; exact hx
  have key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x := by
    rw [← e, map_mul]; ring
  have hv : A.valuation (s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_sub_lt _ (hc t ht) ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hσx) (hc s hs)
  rwa [map_mul, hs1, one_mul] at hv
end GlobalTheory.InertiaMovesRoot

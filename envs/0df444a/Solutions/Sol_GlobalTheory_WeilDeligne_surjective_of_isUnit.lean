-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.surjective_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:07:45.346636+00:00
-- url     : https://prove2.me/submissions/875719c2-3bfd-45fb-9dd5-672d12e16607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff
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
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {H : Type*} [Group H] [TopologicalSpace H] [CompactSpace H]
    {t : H →* Multiplicative ℤ_[l]} (ht : Continuous t) {σ : H} (hσ : IsUnit (t σ).toAdd) :
    Function.Surjective t := by
  obtain ⟨u, hu⟩ := hσ
  have hc : IsClosed (Set.range fun τ => (↑u⁻¹ : ℤ_[l]) * (t τ).toAdd) :=
    (isCompact_range (continuous_const.mul (continuous_toAdd.comp ht))).isClosed
  have hall : ∀ x : ℤ_[l], x ∈ Set.range fun τ => (↑u⁻¹ : ℤ_[l]) * (t τ).toAdd := fun x =>
    PadicInt.denseRange_natCast.induction_on x hc fun n =>
      ⟨σ ^ n, by simp [← hu, mul_left_comm (↑u⁻¹ : ℤ_[l])]⟩
  intro y
  obtain ⟨τ, hτ⟩ := hall (↑u⁻¹ * y.toAdd)
  exact ⟨τ, Multiplicative.toAdd.injective (by simpa using hτ)⟩
end GlobalTheory.WeilDeligne

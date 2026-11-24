-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.exists_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:53:02.649867+00:00
-- url     : https://prove2.me/submissions/d1524140-db32-41c1-a713-729cfa4c2e8e

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_char_eq_exp
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_hasCoord_ainf
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_psiInf_add
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_char_nontrivial_at_every_place
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution (hF : IsTotallyReal F) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ L : Ainf F →+ ℝ, Continuous L ∧
      (∀ x, psiInf F ψ x = Complex.exp ((L x : ℂ) * Complex.I)) ∧
      ∀ t, (∀ r, L (r * t) = 0) → t = 0 := by
  obtain ⟨-, hc, hw⟩ := GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ
  obtain ⟨L, hL, hx⟩ := (hasCoord_ainf hF).char_eq_exp _ hc (psiInf_add ψ) fun x => hψ.2.1 _
  refine ⟨L, hL, hx, fun t ht => ?_⟩
  funext w
  by_contra h0
  obtain ⟨x, hx0, hx1⟩ := hw w
  let r : Ainf F := fun u => x u * (t u)⁻¹
  have hr : r * t = x := by
    funext u
    show x u * (t u)⁻¹ * t u = x u
    by_cases hu : u = w
    · subst hu
      exact inv_mul_cancel_right₀ h0 _
    · rw [hx0 u hu, zero_mul, zero_mul]
  apply hx1
  have := ht r
  rw [hr] at this
  rw [hx, this]
  simp
end GlobalTheory.CompanionTheory.SelfDualInf

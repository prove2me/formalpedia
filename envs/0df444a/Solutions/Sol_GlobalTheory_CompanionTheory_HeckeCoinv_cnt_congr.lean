-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.cnt_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:37:00.323483+00:00
-- url     : https://prove2.me/submissions/4e74ff51-7445-4359-8f16-e50951d04f54

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution {a b : X} (s t : Γ) : cnt Γ a b = cnt Γ (s • a) (t • b) := by
  refine Nat.card_congr ⟨fun γ => ⟨t * γ.1 * s⁻¹, ?_⟩, fun γ => ⟨t⁻¹ * γ.1 * s, ?_⟩, fun γ => ?_, fun γ => ?_⟩
  · simp [mul_smul, γ.2]
  · rw [mul_smul, mul_smul, γ.2, inv_smul_smul]
  · apply Subtype.ext; simp [mul_assoc]
  · apply Subtype.ext; simp [mul_assoc]
end GlobalTheory.CompanionTheory.HeckeCoinv

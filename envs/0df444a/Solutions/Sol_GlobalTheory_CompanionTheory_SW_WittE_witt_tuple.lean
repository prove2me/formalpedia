-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.witt_tuple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:39:45.807484+00:00
-- url     : https://prove2.me/submissions/ab9cda11-4a41-498a-8aa4-0b7cb8748142

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_form_lin_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_isom_tuple
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_formB_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_mem_UJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittE
namespace GlobalTheory.CompanionTheory.SW.WittE
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X Y : Fin n → Fin M → E), gramE σ J X = gramE σ J Y → (gramE σ J X).det ≠ 0 → ∃ g ∈ UJ (σ : E →+* E) J, ∀ a, (g : Matrix (Fin M) (Fin M) E) *ᵥ X a = Y a := by
  intro F E _ _ _ _ _ σ hcm M J hJ n X Y hG hdet
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    apply τ.injective
    have h := hcm.2.2.2
    simp only [RingHom.coe_coe]
    rw [h, h, star_star]
  have hB : ∀ x y, (σ : E →+* E) (formB (σ : E →+* E) J x y) = formB (σ : E →+* E) J y x :=
    formB_conj _ hσ J hJ.1
  have hgram : ∀ (Z : Fin n → Fin M → E) a b,
      formB (σ : E →+* E) J (Z a) (Z b) = gramE σ J Z a b := fun _ _ _ => rfl
  have hker : ∀ c : Fin n → E, (∀ a, formB (σ : E →+* E) J (X a) (lin X c) = 0) →
      lin X c = 0 ∧ lin Y c = 0 := by
    intro c hc
    have h0 : c = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero hdet
      ext a
      have := hc a
      rw [form_lin_right] at this
      simp only [hgram] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    subst h0
    simp [lin]
  obtain ⟨γ, hγ, hXY⟩ := exists_isom_tuple (formB (σ : E →+* E) J) hσ hB two_ne_zero _ X Y rfl
    (fun a b => by rw [hgram, hgram, hG]) hker
  obtain ⟨g, hg, hgz⟩ := exists_mem_UJ _ J hJ.2 γ hγ
  exact ⟨g, hg, fun a => by rw [hgz, hXY]⟩
end GlobalTheory.CompanionTheory.SW.WittE

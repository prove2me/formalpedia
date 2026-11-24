-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittE.exists_isom_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:00:09.08183+00:00
-- url     : https://prove2.me/submissions/59ca323a-62bc-4b67-a526-c6dcb6618ed2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_IsIsom_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittE_exists_quasiRefl

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
variable {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}
namespace GlobalTheory.CompanionTheory.SW.WittE
theorem _root_.solution (B : V →ₛₗ[σ] V →ₗ[E] E) (hσ : ∀ x, σ (σ x) = x)
    (hB : ∀ x y, σ (B x y) = B y x) (h2 : (2 : E) ≠ 0) (x y : V) (hxy : B x x = B y y)
    (hq : B x x ≠ 0) :
    ∃ γ : V →ₗ[E] V, IsIsom B γ ∧ γ x = y ∧ ∀ z, B x z = 0 → B y z = 0 → γ z = z := by
  by_cases h0 : B (x - y) x = 0
  · have h1 : B (x - -y) x ≠ 0 := by
      intro h1
      apply hq
      simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply] at h0 h1
      have h3 : 2 * B x x = 0 := by linear_combination h0 + h1
      exact (mul_eq_zero.1 h3).resolve_left h2
    have h4 : B (-y - y) (-y) ≠ 0 := by
      have h5 : B (-y - y) (-y) = 2 * B y y := by
        simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply]
        ring
      rw [h5, ← hxy]
      exact mul_ne_zero h2 hq
    obtain ⟨γ₁, i1, e1, f1⟩ := exists_quasiRefl B hσ hB x (-y) (by simpa using hxy) h1
    obtain ⟨γ₂, i2, e2, f2⟩ := exists_quasiRefl B hσ hB (-y) y (by simp) h4
    refine ⟨γ₂ ∘ₗ γ₁, i2.comp i1, ?_, ?_⟩
    · simp [e1, e2]
    · intro z hx hy
      have g1 : γ₁ z = z := f1 z (by simp [hx, hy])
      have g2 : γ₂ z = z := f2 z (by simp [hy])
      simp [g1, g2]
  · obtain ⟨γ, i, e, f⟩ := exists_quasiRefl B hσ hB x y hxy h0
    exact ⟨γ, i, e, fun z hx hy => f z (by simp [hx, hy])⟩
end GlobalTheory.CompanionTheory.SW.WittE

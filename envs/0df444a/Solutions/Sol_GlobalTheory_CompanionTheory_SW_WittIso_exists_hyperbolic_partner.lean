-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittIso.exists_hyperbolic_partner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:13.349519+00:00
-- url     : https://prove2.me/submissions/d7a40443-e9c3-4585-a01b-ae3d3a98d5ac

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryTransitiveOnIsotropicVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_hE_add_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_hE_smul_right
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_hE_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_hE_smul_left
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_hE_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_exists_hE_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittIso
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}
namespace GlobalTheory.CompanionTheory.SW.WittIso
theorem _root_.solution [CharZero E] (hσ : ∀ a, σ (σ a) = a)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0)
    (hxx : hE σ J x x = 0) :
    ∃ x', hE σ J x x' = 1 ∧ hE σ J x' x = 1 ∧ hE σ J x' x' = 0 := by
  obtain ⟨w₀, hw₀⟩ := exists_hE_ne_zero (σ := σ) hdet hx
  obtain ⟨w, hxw⟩ : ∃ w, hE σ J x w = 1 :=
    ⟨(hE σ J x w₀)⁻¹ • w₀, by rw [hE_smul_right, inv_mul_cancel₀ hw₀]⟩
  have hwx : hE σ J w x = 1 := by
    rw [← hE_conj hσ hJ x w, hxw, map_one]
  obtain ⟨t, ht⟩ : ∃ t, t = hE σ J w w := ⟨_, rfl⟩
  have hσt : σ t = t := by
    rw [ht]; exact hE_conj hσ hJ w w
  obtain ⟨c, hc⟩ : ∃ c : E, c = -t / 2 := ⟨_, rfl⟩
  have hσc : σ c = c := by
    have h2 : σ (2 : E) = 2 := map_ofNat σ 2
    rw [hc, map_div₀, map_neg, hσt, h2]
  have h1 : hE σ J x (w + c • x) = 1 := by
    rw [hE_add_right, hE_smul_right, hxx, hxw]; ring
  have h2 : hE σ J (w + c • x) x = 1 := by
    rw [hE_add_left, hE_smul_left, hxx, hwx]; ring
  refine ⟨w + c • x, h1, h2, ?_⟩
  rw [hE_add_left, hE_smul_left, h1, hE_add_right, hE_smul_right, hwx, ← ht, hσc, hc]
  ring
end GlobalTheory.CompanionTheory.SW.WittIso

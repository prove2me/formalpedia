-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:55.262223+00:00
-- url     : https://prove2.me/submissions/7e023d85-3c31-466e-b896-0f6c8c15d720

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_exists_partner
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_finrank_perp
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_selfDualLattice_projection_mem_of_unit_length
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_sigma_invol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HypSplit
namespace GlobalTheory.CompanionTheory.SW.HypSplit
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  intro F E _ _ _ _ _ σ hcm M J hJ x hx hxx
  have hσ := sigma_invol σ hcm
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨y, hxy, hyy⟩ := exists_partner hσ hJ h2 x hx hxx
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 2 := ⟨_, hfr.symm⟩
  obtain ⟨g, J₁, h1, h3⟩ := selfDualLattice_projection_mem_of_unit_length hσ h2 hJ hxx hyy hxy
  exact ⟨M₁, rfl, g, J₁, h1, h3⟩
end GlobalTheory.CompanionTheory.SW.HypSplit

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:26:01.059251+00:00
-- url     : https://prove2.me/submissions/9a04d6bb-5b5b-49ea-8332-e319a942d849

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryTransitiveOnIsotropicVectors
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_exists_hyperbolic_partner
import Theorems.Thm_GlobalTheory_T_witt_extension_global


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
namespace GlobalTheory.CompanionTheory.SW.WittIso
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ x y : Fin M → E, x ≠ 0 → y ≠ 0 → hE σ J x x = 0 → hE σ J y y = 0 →
    ∃ g ∈ UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E) *ᵥ x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x y hx hy hxx hyy
  have hσ : ∀ a, σ (σ a) = a := by
    intro a
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hCM.2.2.2 τ, hCM.2.2.2 τ, star_star]
  obtain ⟨x', h1, h2, h3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hx hxx
  obtain ⟨y', k1, k2, k3⟩ := exists_hyperbolic_partner hσ hJ.1 hJ.2 hy hyy
  have hgram : gramE σ J ![x, x'] = gramE σ J ![y, y'] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramE, hxx, hyy, h1, h2, h3, k1, k2, k3]
  have hdet : (gramE σ J ![x, x']).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [gramE, hxx, h1, h2, h3]
  obtain ⟨g, hg, hgX⟩ := GlobalTheory.T.witt_extension_global F E σ hCM M J hJ 2 ![x, x'] ![y, y'] hgram hdet
  exact ⟨g, hg, by simpa using hgX 0⟩
end GlobalTheory.CompanionTheory.SW.WittIso

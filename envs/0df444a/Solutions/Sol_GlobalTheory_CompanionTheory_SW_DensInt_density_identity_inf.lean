-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DensInt.density_identity_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:42:50.437782+00:00
-- url     : https://prove2.me/submissions/35cf467f-d5ff-41bc-bcda-687ae826395a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivity
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DensInt_density_limit
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramDensity_isContDensityOn_gram
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopK_topTens_props
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_isLocR_Ainf


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DensInt
set_option maxHeartbeats 1000000
namespace GlobalTheory.CompanionTheory.SW.DensInt
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)) (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous φ → Integrable φ μ → (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)) → ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∀ K : Set (HermR (Ainf F) σ n), IsCompact K → K ⊆ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∫ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' K), φ X ∂μ = ∫ S in K, (∫ X, φ X ∂(m S)) ∂ν := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hfib φ hφc hφ hφS hD K hK hKB
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact density_limit μ ν (gramR (Ainf F) σ J) Subtype.val _ m
    (fun ψ h1 h2 => GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram F E σ hσ M J hJ (Ainf F) hR n μ ν m hμ hν hfib ψ h1 h2)
    φ hφc hφ hφS hD K hK hKB
end GlobalTheory.CompanionTheory.SW.DensInt

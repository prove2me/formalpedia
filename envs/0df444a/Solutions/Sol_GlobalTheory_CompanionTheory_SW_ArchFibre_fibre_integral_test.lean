-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:43:52.765372+00:00
-- url     : https://prove2.me/submissions/2b8d310f-7cfb-40cf-af10-b4298f18909d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_fibre_integral
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_isLocR_Ainf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArchFibre
namespace GlobalTheory.CompanionTheory.SW.ArchFibre
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) →
  tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det} →
  Continuous (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  HasCompactSupport (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  (∀ s : Ainf F, ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ s)) = ENNReal.ofReal (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))) ∧
  ENNReal.ofReal (∫ s, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2) := by
  intro F E _ _ _ _ _ σ hσ J hJ d b li hli mi hfib φ hφ hφc hφ0 hφU
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  exact fibre_integral (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1) hσ hJ b li hli.1 mi hfib φ hφ hφc hφ0 hφU
end GlobalTheory.CompanionTheory.SW.ArchFibre

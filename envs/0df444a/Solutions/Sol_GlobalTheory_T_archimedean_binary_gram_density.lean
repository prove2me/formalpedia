-- Prove2me | solution 1 for GlobalTheory.T.archimedean_binary_gram_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:34.042855+00:00
-- url     : https://prove2.me/submissions/4dc2fec7-68a4-4374-82f5-4f32535adfcf

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_fibre_integral_test


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
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
  first | exact @GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | exact GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | (intros; apply GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test <;> assumption)
end _root_.GlobalTheory.T

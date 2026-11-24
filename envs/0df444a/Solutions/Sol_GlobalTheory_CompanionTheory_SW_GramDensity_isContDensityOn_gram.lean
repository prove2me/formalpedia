-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:13:53.030783+00:00
-- url     : https://prove2.me/submissions/bc171648-eeb0-40fd-9cda-06920f7598be

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreDensity_isContDensityOn_fibreIntegral
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring
import Theorems.Thm_GlobalTheory_T_units_open_embedding_local_tensor


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramDensity
namespace GlobalTheory.CompanionTheory.SW.GramDensity
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ φ : (Fin n → Fin M → R ⊗[F] E) → ℂ, Continuous φ → HasCompactSupport φ → IsContDensityOn μ (gramR R σ J) Subtype.val ν {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} φ (fun S => ∫ X, φ X ∂(m S)) ∧ ∀ S, Integrable φ (m S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hfib φ hφ hφc
  have hunits : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have := iB n M
  have := iTR
  have := iLC
  have := iSC
  have := iT2
  obtain ⟨jLC, jSC, jT2, jB, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  have := jLC
  have := jSC
  have := jT2
  have := jB
  obtain ⟨g, hg, hgram⟩ := hlift M J hJ
  have hB : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hdet : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have hset : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp [IsUnit]
    rw [hset]
    exact hunits.isOpen_range.preimage hdet
  have hpre : {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} =
      g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    ext X
    simp [hgram X]
  have hfib' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val
      (g ⁻¹' {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}) ν
      {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m := by
    rw [← hpre]
    exact hfib
  exact GlobalTheory.CompanionTheory.SW.FibreDensity.isContDensityOn_fibreIntegral _ _ _ μ ν (gramR R σ J) g Subtype.val
    Subtype.val_injective hg hgram _ hB m hfib' φ hφ hφc
end GlobalTheory.CompanionTheory.SW.GramDensity

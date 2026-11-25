-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.exists_scale_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:36.28825+00:00
-- url     : https://prove2.me/submissions/2d67124d-9797-4859-b56a-dd0be5ef43c6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_exists_continuous_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_continuous_inv_unitMat
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_locallyCompact_unitMat
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_continuousOn_extend
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_conjT_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_conjT_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_conj_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_sigma_sigma
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarScale
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.HaarScale
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n : ℕ)
    (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure) :
    ∃ B : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ≥0, ContinuousOn B {g | IsUnit g.det} ∧
      ∀ g, IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n,
        (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
          conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g) → ν.map τ = B g • ν := by
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hu : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨iTR, iLC, iSC, iT2, hsig, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  haveI := locallyCompact_unitMat (n := n) hu
  have hs : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  have hcont : ∀ {Q : Type} [TopologicalSpace Q] (G : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E)),
      Continuous G → Continuous (Function.uncurry fun (q : Q) (S : HermR R σ n) =>
        (⟨conjT R σ (G q) * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * G q, conj_mem R hs _ S⟩ : HermR R σ n)) := by
    intro Q _ G hG
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun p : Q × HermR R σ n => conjT R σ (G p.1) :=
      ((hG.comp continuous_fst).matrix_map hsig).matrix_transpose
    have h2 : Continuous fun p : Q × HermR R σ n => (p.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val.comp continuous_snd
    exact (h1.matrix_mul h2).matrix_mul (hG.comp continuous_fst)
  have hinvl : ∀ g h : Matrix (Fin n) (Fin n) (R ⊗[F] E), g * h = 1 → ∀ S : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      conjT R σ h * (conjT R σ g * S * g) * h = S := by
    intro g h hgh S
    have h1 : conjT R σ h * conjT R σ g = 1 := by rw [← conjT_mul, hgh, conjT_one]
    calc conjT R σ h * (conjT R σ g * S * g) * h
        = (conjT R σ h * conjT R σ g) * S * (g * h) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [h1, hgh, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨B, hB, hform⟩ := exists_continuous_scale ν
    (P := {g : Matrix (Fin n) (Fin n) (R ⊗[F] E) // IsUnit g.det})
    (fun g S => ⟨conjT R σ g.1 * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g.1, conj_mem R hs _ S⟩)
    (fun g S => ⟨conjT R σ (g.1)⁻¹ * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * (g.1)⁻¹, conj_mem R hs _ S⟩)
    (hcont _ continuous_subtype_val) (hcont _ (continuous_inv_unitMat hu))
    (fun g S T => Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul]))
    (fun g S => Subtype.ext (hinvl _ _ (Matrix.mul_nonsing_inv _ g.2) _))
    (fun g S => Subtype.ext (hinvl _ _ (Matrix.nonsing_inv_mul _ g.2) _))
  refine ⟨_, continuousOn_extend B hB, fun g hg τ hτ => ?_⟩
  have hτ' : τ = fun S => ⟨conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g, conj_mem R hs _ S⟩ :=
    funext fun S => Subtype.ext (hτ S)
  rw [hτ']
  simpa [hg] using hform ⟨g, hg⟩
end GlobalTheory.CompanionTheory.SW.HaarScale

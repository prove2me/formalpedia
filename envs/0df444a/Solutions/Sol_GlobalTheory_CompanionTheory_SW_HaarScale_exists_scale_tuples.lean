-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HaarScale.exists_scale_tuples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:34:39.404014+00:00
-- url     : https://prove2.me/submissions/7393e755-00ca-4b6c-a90c-ceb7c3df3c96

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
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_rmul_rmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_rmul_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_rmul_add
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
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n M : ℕ)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    ∃ A : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ≥0, ContinuousOn A {g | IsUnit g.det} ∧
      ∀ g, IsUnit g.det → μ.map (fun X => rmul R X g) = A g • μ := by
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  have hu : IsOpenEmbedding (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ R hR
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  haveI := locallyCompact_unitMat (n := n) hu
  have hcont : ∀ {Q : Type} [TopologicalSpace Q] (G : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E)),
      Continuous G → Continuous (Function.uncurry fun (q : Q) (X : Fin n → Fin M → R ⊗[F] E) => rmul R X (G q)) := by
    intro Q _ G hG
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [Function.uncurry_def, rmul]
    refine continuous_finset_sum _ fun c _ => ?_
    have h1 : Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => p.2 c i :=
      (continuous_apply_apply c i).comp continuous_snd
    have h2 : Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => G p.1 c a :=
      (hG.comp continuous_fst).matrix_elem c a
    exact h1.mul h2
  obtain ⟨A, hA, hform⟩ := exists_continuous_scale μ
    (P := {g : Matrix (Fin n) (Fin n) (R ⊗[F] E) // IsUnit g.det})
    (fun g X => rmul R X g.1) (fun g X => rmul R X (g.1)⁻¹)
    (hcont _ continuous_subtype_val) (hcont _ (continuous_inv_unitMat hu))
    (fun g X Y => rmul_add R X Y g.1)
    (fun g X => by rw [rmul_rmul, Matrix.mul_nonsing_inv _ g.2, rmul_one])
    (fun g X => by rw [rmul_rmul, Matrix.nonsing_inv_mul _ g.2, rmul_one])
  refine ⟨_, continuousOn_extend A hA, fun g hg => ?_⟩
  simpa [hg] using hform ⟨g, hg⟩
end GlobalTheory.CompanionTheory.SW.HaarScale

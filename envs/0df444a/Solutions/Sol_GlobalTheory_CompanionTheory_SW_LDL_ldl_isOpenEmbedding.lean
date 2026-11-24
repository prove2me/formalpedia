-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LDL.ldl_isOpenEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:07.364274+00:00
-- url     : https://prove2.me/submissions/9a9aaafd-9a98-4a34-87e2-28437f5f68b4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraPropertiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotent
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_gram_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LDL_oH_isOpenEmbedding
import Theorems.Thm_GlobalTheory_T_tensor_involution_algebra_properties
import Theorems.Thm_GlobalTheory_T_tensor_locally_compact_ring


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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LDL
namespace GlobalTheory.CompanionTheory.SW.LDL
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ n : ℕ, ∃ o : (Fin n → Rˣ) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) → HermR R σ n, IsOpenEmbedding o ∧ ∀ d u, ∀ N : Matrix (Fin n) (Fin n) (R ⊗[F] E), (N = Matrix.of fun i j => if i = j then 1 else if h : i < j then u ⟨(i, j), h⟩ else 0) → (o (d, u) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) N * Matrix.diagonal (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) * N := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ hloc n
  obtain ⟨hTR, hLC, hSC, hT2, hAr, hRed, hU, -⟩ := hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hAr
  haveI := hRed
  obtain ⟨-, -, -, hinv, -, hfix, -⟩ := GlobalTheory.T.tensor_involution_algebra_properties F E σ hcm R
  obtain ⟨hKT, -, -, -, hsc, htr, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := hKT
  have hfr : Module.finrank F E = 2 := hcm.2.2.1
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hιt : ∀ r : R, algebraMap R (R ⊗[F] E) r = r ⊗ₜ[F] (1 : E) := fun r => by
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hι : Continuous (algebraMap R (R ⊗[F] E)) := by
    have e : (algebraMap R (R ⊗[F] E) : R → R ⊗[F] E) = fun r => r • (1 : R ⊗[F] E) :=
      funext fun r => Algebra.algebraMap_eq_smul_one r
    rw [e]
    exact (continuous_id (X := R)).smul (continuous_const (y := (1 : R ⊗[F] E)))
  have hτι : ∀ r : R, sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := fun r => by
    rw [hιt]
    simp [sigR]
  have hfix' : ∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = algebraMap R (R ⊗[F] E) r := fun y hy => by
    obtain ⟨r, hr⟩ := hfix y hy
    exact ⟨r, hr.trans (hιt r).symm⟩
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap F R) 2, ← map_mul]
    norm_num
  have hlι : ∀ r : R, algebraMap F R (1 / 2) *
      Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) r) = r := fun r => by
    have h := Algebra.trace_algebraMap_of_basis
      (Algebra.TensorProduct.basis R (Module.finBasisOfFinrankEq F E hfr)) r
    rw [h]
    simp only [Fintype.card_fin, two_nsmul]
    linear_combination r * h2
  have hlev : Continuous fun y : R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) y := continuous_const.mul htr
  refine ⟨oH (algebraMap R (R ⊗[F] E)) (sigR R σ) hinv hτι n,
    oH_isOpenEmbedding hι hsc hlev hinv hτι hlι hfix' hU n, ?_⟩
  rintro d u N rfl
  have hd : (fun i => ((d i : R) ⊗ₜ[F] (1 : E) : R ⊗[F] E)) =
      fun i => algebraMap R (R ⊗[F] E) (d i) := funext fun i => (hιt _).symm
  rw [hd]
  exact gram_eq _ _ d u
end GlobalTheory.CompanionTheory.SW.LDL

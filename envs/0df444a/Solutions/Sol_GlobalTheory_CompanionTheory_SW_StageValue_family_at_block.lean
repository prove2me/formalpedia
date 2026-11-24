-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StageValue.family_at_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:56.803414+00:00
-- url     : https://prove2.me/submissions/6820aeb8-744f-4e4d-a76e-ecc5ae4c3849

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_vec_one_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_corner_half_trace_block_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_cvec_block
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_schur_block
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_isUnit_det_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageValue
namespace GlobalTheory.CompanionTheory.SW.StageValue
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have hs0 : s0 R ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = algebraMap F R t :=
    corner_half_trace_block_one R t hfr T
  have hsch := schur_block R σ t a T hT hT'
  have hmem : hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
    refine ⟨by rw [hs0]; exact D.htB, ?_⟩
    rw [hsch]
    exact isUnit_det_map R T hdet
  refine ⟨hmem, ?_⟩
  have hc : cvec R t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = 0 := cvec_block R t a T
  unfold fibS
  rw [Set.indicator_of_mem hmem]
  simp only [hs0, D.ha1, hsch, hc, D.hκ1, one_mul, Units.val_one, vec_one_zero]
end GlobalTheory.CompanionTheory.SW.StageValue

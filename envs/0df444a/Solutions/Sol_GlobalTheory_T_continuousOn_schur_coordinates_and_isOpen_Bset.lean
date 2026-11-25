-- Prove2me | solution 1 for GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:46.424318+00:00
-- url     : https://prove2.me/submissions/4b4ce134-d453-48bc-abef-97694aa99b83

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegral
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductIntegralStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__Coord_coords_7539cd3187dc


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → Continuous (fun S : HermR R σ (n + 1) => s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) ∧ ContinuousOn (fun S : HermR R σ (n + 1) => (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ ContinuousOn (fun S : HermR R σ (n + 1) => schur R σ t a S) {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀} ∧ IsOpen (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.Coord.coords <;> assumption)
end _root_.GlobalTheory.T

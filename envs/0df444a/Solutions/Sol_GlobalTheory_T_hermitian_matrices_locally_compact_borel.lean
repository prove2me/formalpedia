-- Prove2me | solution 1 for GlobalTheory.T.hermitian_matrices_locally_compact_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:18:13.843233+00:00
-- url     : https://prove2.me/submissions/baac0ae4-9fc4-4e15-9ea9-03f52b8b2af4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorelStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_herm_top


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ n : ℕ, LocallyCompactSpace (HermR R σ n) ∧ SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) ∧ BorelSpace (HermR R σ n) ∧ ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∃ g : (Fin n → Fin M → R ⊗[F] E) → HermR R σ n, Continuous g ∧ ∀ X, gramR R σ J X = (g X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HermTop.herm_top | exact GlobalTheory.CompanionTheory.SW.HermTop.herm_top | (intros; apply GlobalTheory.CompanionTheory.SW.HermTop.herm_top <;> assumption)
end _root_.GlobalTheory.T

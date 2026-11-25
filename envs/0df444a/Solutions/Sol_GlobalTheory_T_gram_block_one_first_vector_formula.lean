-- Prove2me | solution 1 for GlobalTheory.T.gram_block_one_first_vector_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:54:07.891842+00:00
-- url     : https://prove2.me/submissions/6dfb9d78-888b-49d1-9bd7-29f898c4d698

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramBlockOneFirstVectorFormulaStatement
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_SW_PiLocalization__gramR_vec_fe1b6011dd19


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] (u : R) (c : Fin n → R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 0 = (u ^ 2 * algebraMap F R t) ⊗ₜ[F] (1 : E) ∧ (∀ j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) 0 j.succ = (u ⊗ₜ[F] (algebraMap F E t)) * c j) ∧ ∀ i j : Fin n, gramR R σ (blockOne (algebraMap F E t) J) (vec (u ⊗ₜ[F] (1 : E)) c X) i.succ j.succ = sigR R σ (c i) * inclR R (algebraMap F E t) * c j + gramR R σ J X i j := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramR_vec <;> assumption)
end _root_.GlobalTheory.T

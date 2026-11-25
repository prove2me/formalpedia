-- Prove2me | solution 1 for GlobalTheory.T.block_one_det_hermitian_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:08.575807+00:00
-- url     : https://prove2.me/submissions/4603a319-a66b-4f1d-9820-062ed1ce5c9f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGramStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_block_alg


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg | exact GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg | (intros; apply GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg <;> assumption)
end _root_.GlobalTheory.T

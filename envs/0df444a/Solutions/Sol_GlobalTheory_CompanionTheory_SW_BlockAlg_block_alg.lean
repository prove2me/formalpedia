-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:50:39.337217+00:00
-- url     : https://prove2.me/submissions/d0e5e13e-f7eb-485a-be1c-6b0477c055bc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_det_blockOne
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_gramE_consTup
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_exists_consTup_of_gramE

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.BlockAlg
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by
  intro F E _ _ _ _ _ σ _ M J t
  refine ⟨det_blockOne _ _, ?_, fun n X => gramE_consTup σ J _ X, ?_⟩
  · intro hJ a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simpa [blockOne_succ_succ] using hJ a b
  · intro ht n T Y h0 hY
    have ht' : algebraMap F E t ≠ 0 := by
      simpa using ht
    exact exists_consTup_of_gramE σ J ht' T Y h0 hY
end GlobalTheory.CompanionTheory.SW.BlockAlg

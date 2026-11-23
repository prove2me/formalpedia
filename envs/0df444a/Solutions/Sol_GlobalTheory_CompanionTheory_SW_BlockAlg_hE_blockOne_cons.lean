-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BlockAlg.hE_blockOne_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:56.532704+00:00
-- url     : https://prove2.me/submissions/e90da8f5-d2d4-4685-9718-463187352194

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_blockOne_succ_succ

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
theorem _root_.solution (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t a b : E)
    (x y : Fin M → E) :
    hE σ (blockOne t J) (Fin.cons a x : Fin (M + 1) → E) (Fin.cons b y : Fin (M + 1) → E) =
      σ a * t * b + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, blockOne_zero_zero,
    blockOne_zero_succ, blockOne_succ_zero, blockOne_succ_succ]
  simp
end GlobalTheory.CompanionTheory.SW.BlockAlg

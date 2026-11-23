-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.StabFirst.of_blockGL_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:52.809078+00:00
-- url     : https://prove2.me/submissions/a23eaba0-ab73-4ff7-8be0-455b9cb4279c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_blockOne_right_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.StabFirst
theorem _root_.solution (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) (s : K) {g : GL (Fin M) K}
    (hg : blockGL g ∈ UJ σ (blockOne s J)) : g ∈ UJ σ J := by
  have hg' : cT σ (blockOne 1 (g : Matrix (Fin M) (Fin M) K)) * blockOne s J *
    blockOne 1 (g : Matrix (Fin M) (Fin M) K) = blockOne s J := hg
  rw [cT_blockOne, blockOne_mul, blockOne_mul] at hg'
  exact blockOne_right_injective hg'
end GlobalTheory.CompanionTheory.SW.StabFirst

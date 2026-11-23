-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.wt_ne_zero_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:23:53.246257+00:00
-- url     : https://prove2.me/submissions/8df863ae-e649-4ade-98c1-d57c16e01bb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ClassGroupCoprimeRepresentative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeLSeriesEqSumPrincipalPartialSeries
import Theorems.Thm_GlobalTheory_HeckeStrip_norm_wt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeStrip
variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckeStrip
theorem _root_.solution (φ : I → K →+* ℂ) (n : I → ℤ) {α : 𝓞 K} (hα : α ≠ 0) : wt φ n (α : K) ≠ 0 := by
  have hαK : (α : K) ≠ 0 := fun h => hα (RingOfIntegers.coe_eq_zero_iff.mp h)
  intro h
  have := norm_wt φ n hαK
  rw [h, norm_zero] at this
  exact zero_ne_one this
end GlobalTheory.HeckeStrip

-- Prove2me | solution 1 for GlobalTheory.HoloWirt.clm_single_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:09:24.92983+00:00
-- url     : https://prove2.me/submissions/03e43e56-1437-4e84-88af-779b4200eee3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_WeightTwoSum_dz_apply
import Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub
attribute [local simp] GlobalTheory.WeightTwoSum.dz_apply
attribute [local simp] GlobalTheory.WeightTwoSum.dzbar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.HoloWirt
open Classical
namespace GlobalTheory.HoloWirt
theorem _root_.solution {I : Type} (f : (I → ℂ) →L[ℂ] ℂ) (i : I) :
    f (Pi.single i Complex.I) = Complex.I * f (Pi.single i 1) := by
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_apply, hj]
end GlobalTheory.HoloWirt

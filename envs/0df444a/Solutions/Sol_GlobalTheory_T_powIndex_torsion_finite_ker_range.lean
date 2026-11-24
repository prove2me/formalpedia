-- Prove2me | solution 1 for GlobalTheory.T.powIndex_torsion_finite_ker_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:21:09.221881+00:00
-- url     : https://prove2.me/submissions/67673a43-f2b3-4959-91c6-d77db9f0cbef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionFiniteKerRangeStatement
import Theorems.Thm_GlobalTheory_CNorm_pIdx_pTor_ker_range_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → pTor p g.range ≠ 0 → pIdx p g.ker ≠ 0 ∧ pTor p g.ker ≠ 0 ∧ pIdx p g.range ≠ 0 := by
  first | exact @GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero | exact GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero | (intros; apply GlobalTheory.CNorm.pIdx_pTor_ker_range_ne_zero <;> assumption)
end _root_.GlobalTheory.T

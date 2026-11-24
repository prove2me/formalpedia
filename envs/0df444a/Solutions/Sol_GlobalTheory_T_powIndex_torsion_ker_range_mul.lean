-- Prove2me | solution 1 for GlobalTheory.T.powIndex_torsion_ker_range_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:13.03081+00:00
-- url     : https://prove2.me/submissions/de2eb522-6fd5-4ba4-884d-3607238e2481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_PowIndexTorsionKerRangeMulStatement
import Theorems.Thm_GlobalTheory_CNorm_pIdx_pTor_ker_range


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
theorem _root_.solution : ∀ (p : ℕ) (A A' : Type) [CommGroup A] [CommGroup A'] (g : A →* A'), pIdx p g.ker ≠ 0 → pTor p g.ker ≠ 0 → pIdx p g.range ≠ 0 → pTor p g.range ≠ 0 → pIdx p (⊤ : Subgroup A) ≠ 0 ∧ pTor p (⊤ : Subgroup A) ≠ 0 ∧ pIdx p (⊤ : Subgroup A) * pTor p g.ker * pTor p g.range = pIdx p g.ker * pIdx p g.range * pTor p (⊤ : Subgroup A) := by
  first | exact @GlobalTheory.CNorm.pIdx_pTor_ker_range | exact GlobalTheory.CNorm.pIdx_pTor_ker_range | (intros; apply GlobalTheory.CNorm.pIdx_pTor_ker_range <;> assumption)
end _root_.GlobalTheory.T

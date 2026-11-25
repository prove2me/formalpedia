-- Prove2me | solution 1 for GlobalTheory.exists_pow_smul_eq_add_sub_one_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:56:54.758819+00:00
-- url     : https://prove2.me/submissions/5228bc15-8809-43c9-a20b-b234c5de758c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsXPowSmulEqZeroOfEqXSubOneSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowSmulEqAddSubOneSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S M : Type} [CommRing S] [AddCommGroup M]
    [Module S M] (x : S) (k : ℕ) (y : M) : ∃ w : M, x ^ k • y = y + (x - 1) • w := by
  refine ⟨(∑ j ∈ Finset.range k, x ^ j) • y, ?_⟩
  rw [smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel
end GlobalTheory

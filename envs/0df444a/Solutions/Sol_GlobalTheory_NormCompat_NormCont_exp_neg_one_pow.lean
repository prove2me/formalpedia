-- Prove2me | solution 1 for GlobalTheory.NormCompat.NormCont.exp_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:53.310956+00:00
-- url     : https://prove2.me/submissions/89faf83a-2119-4d98-a9de-016d75d3e9a7

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormCloseToOneOfCloseAbovePlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormCompat GlobalTheory.NormCompat.NormCont
namespace GlobalTheory.NormCompat.NormCont
theorem _root_.solution (k : ℕ) : (WithZero.exp (-1 : ℤ)) ^ k = WithZero.exp (-(k : ℤ)) := by
  rw [← WithZero.exp_nsmul]; simp
end GlobalTheory.NormCompat.NormCont

-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsPerfectoidField.of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:29.841446+00:00
-- url     : https://prove2.me/submissions/18e580ae-3c24-4faf-b6e5-f8bfb1c22a3c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_UntiltPerfectoid
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApprox
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGalois
import Definitions.Def_GroundTheory_PAdicHodge_UntiltGaloisCorr
import Definitions.Def_GroundTheory_PAdicHodge_CompletedAlgClosure
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCharP
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidCriterion
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgClosed
import Definitions.Def_GroundTheory_PAdicHodge_TiltEquiv
import Theorems.Thm_GroundTheory_PAdicHodge_isPerfectoidField_of_isAlgClosed_of_normedAlgebra
import Theorems.Thm_GroundTheory_PAdicHodge_CompletedAlgClosure_norm_embedding
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_charZero_or_charP
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_finiteDimensional_of_charP
import Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_of_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge
namespace IsPerfectoidField
theorem _root_.solution (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  rcases IsPerfectoidField.charZero_or_charP (K := K) p with h0 | hp
  · have := IsPerfectoidField.completeSpace (K := K) p
    have : IsPerfectoidField (CompletedAlgClosure K) p :=
      isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p
    set j := CompletedAlgClosure.embedding K L
    let e : L ≃ₐ[K] j.fieldRange := AlgEquiv.ofInjectiveField j
    have : FiniteDimensional K j.fieldRange := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine IsPerfectoidField.of_ringEquiv p e.symm.toRingEquiv fun y => ?_
    have h1 : ((e (e.symm y) : j.fieldRange) : CompletedAlgClosure K) = j (e.symm y) := rfl
    rw [AlgEquiv.apply_symm_apply] at h1
    change ‖e.symm y‖ = ‖(y : CompletedAlgClosure K)‖
    rw [h1, CompletedAlgClosure.norm_embedding]
  · exact IsPerfectoidField.of_finiteDimensional_of_charP (K := K) p L
end IsPerfectoidField
end GroundTheory.PAdicHodge

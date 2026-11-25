-- Prove2me | solution 1 for MassDataIdxCore.tv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:15.206256+00:00
-- url     : https://prove2.me/submissions/7e03f2e0-8eeb-42bf-a986-3871d10597e8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
import Theorems.Thm_MassDataIdxCore_intM_one
import Theorems.Thm_MassDataIdxCore_firstSplit_tensor_vector
import Theorems.Thm_MassDataIdxCore_secondSplit_tensor_vector
import Theorems.Thm_MassDataIdxCore_mulVec_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n]
variable (θ : T ≃ₐ[K] K × K) (J : Matrix n n T) (P : GL n K)
namespace MassDataIdxCore
theorem _root_.solution (j : n) : tv θ P j ∈ Lat O θ J P := by
  simp only [Lat, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [firstSplit_tensor_vector, mulVec_col]
    have hP : ((P⁻¹ : GL n K) : Matrix n n K) * (P : Matrix n n K) = 1 := by simp
    rw [hP]
    exact fun i => intM_one O i j
  · rw [secondSplit_tensor_vector, Matrix.mulVec_zero]
    exact fun _ => O.zero_mem
end MassDataIdxCore

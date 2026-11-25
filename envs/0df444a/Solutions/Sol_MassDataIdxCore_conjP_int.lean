-- Prove2me | solution 1 for MassDataIdxCore.conjP_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:21.338568+00:00
-- url     : https://prove2.me/submissions/6fb78f24-2277-4e7d-a6b0-e8b226ac2db6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_StRedCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitTensorVector
import Theorems.Thm_MassDataIdxCore_firstSplit_mulVec
import Theorems.Thm_MassDataIdxCore_firstSplit_tensor_vector
import Theorems.Thm_MassDataIdxCore_mulVec_col
import Theorems.Thm_MassDataIdxCore_tv_mem

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
theorem _root_.solution (g : GL n T) (hg : ∀ x, x ∈ Lat O θ J P → (g : Matrix n n T) *ᵥ x ∈ Lat O θ J P) :
    IntM O (conjPrime₂ θ P g) := by
  intro i j
  have h := hg _ (tv_mem O θ J P j)
  simp only [Lat, Set.mem_setOf_eq] at h
  have h1 := h.1
  rw [firstSplit_mulVec, firstSplit_tensor_vector, mulVec_col, mulVec_col] at h1
  have e : conjPrime₂ θ P g i j =
      (((P⁻¹ : GL n K) : Matrix n n K) * ((g : Matrix n n T).map (t1 θ) * (P : Matrix n n K))) i j := by
    rw [conjPrime₂, Matrix.mul_assoc]
  rw [e]
  exact h1 i
end MassDataIdxCore

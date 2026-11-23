-- Prove2me | solution 1 for GlobalTheory.WeilM.ug_rel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:24.244547+00:00
-- url     : https://prove2.me/submissions/e4bb23c8-c1a4-478d-9c9a-2316a16705b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Theorems.Thm_GlobalTheory_WeilM_ugFst_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
namespace GlobalTheory.WeilM
theorem _root_.solution {J : Matrix β β (R × R)} (h : UG (swapA R) J) :
    (ugFst J h).valᵀ * cmp₁ J * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) = cmp₁ J := by
  have hh : ((h : GL β (R × R)) : Matrix β β (R × R))ᵀ * J *
      ((h : GL β (R × R)) : Matrix β β (R × R)).map (swapA R) = J := h.2
  have hm := congrArg (fun M => M.map (RingHom.fst R R)) hh
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at hm
  rw [ugFst_val]
  convert hm using 3
  ext x
  simp [swapA_apply]
end GlobalTheory.WeilM

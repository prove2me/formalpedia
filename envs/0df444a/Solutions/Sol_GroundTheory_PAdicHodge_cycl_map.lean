-- Prove2me | solution 1 for GroundTheory.PAdicHodge.cycl_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:08.880368+00:00
-- url     : https://prove2.me/submissions/18e6d44e-b834-4da5-a4c7-92721c9a5441

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n : ℕ) :
    (cycl p n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cycl p n := by
  rw [cycl, adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (σ y) ^ (p ^ n) = 1
    rw [← map_pow, show y ^ (p ^ n) = 1 from hy, map_one]
  · intro (hx : x ^ (p ^ n) = 1)
    refine ⟨σ.symm x, ?_, by simp⟩
    show (σ.symm x) ^ (p ^ n) = 1
    rw [← map_pow, hx, map_one]
end GroundTheory.PAdicHodge

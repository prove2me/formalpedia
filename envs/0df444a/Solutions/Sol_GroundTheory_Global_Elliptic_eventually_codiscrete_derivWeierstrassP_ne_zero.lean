-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.eventually_codiscrete_derivWeierstrassP_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:43:43.17907+00:00
-- url     : https://prove2.me/submissions/41444bd3-5a5f-4571-84b5-044002fd60a5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_nhdsNE_zero_eval_weierstrassP_ne_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_codiscrete_ne_zero_of_nhdsNE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution :
    ∀ᶠ z in codiscrete ℂ, ℘'[L] z ≠ 0 := by
  apply eventually_codiscrete_ne_zero_of_nhdsNE L.meromorphic_derivWeierstrassP
  have hR : (C 4 * X ^ 3 - C L.g₂ * X - C L.g₃ : ℂ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℂ[X] ↦ p.coeff 3) h
    norm_num [coeff_X, coeff_C] at this
  filter_upwards [eventually_nhdsNE_zero_eval_weierstrassP_ne_zero hR,
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz hzl hz0
  intro h
  have hzL : z ∉ L.lattice := fun hm ↦ hzl ⟨hm, hz0⟩
  have := L.derivWeierstrassP_sq z hzL
  rw [h] at this
  apply hz
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination -this
end GroundTheory.Global.Elliptic

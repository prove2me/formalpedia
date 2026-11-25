-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_logSeries_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:38:46.372322+00:00
-- url     : https://prove2.me/submissions/f72c7b2b-782a-4dc4-b89f-94e81d125a19

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Theorems.Thm_GroundTheory_LocalField_sub_one_le_of_lt
import Theorems.Thm_GroundTheory_LocalField_logSeries_sub_self_mem
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution {r : ℤ} (hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r)
    {x : K} (hx : x ∈ valBall K r) (h : logSeries x = 0) : x = 0 := by
  by_contra hx0
  have hv := normalizedValuation_eq_exp_ord hx0
  have hxa : x ∈ valBall K (ord x) := by rw [mem_valBall, hv]
  have hxa1 : x ∉ valBall K (ord x + 1) := by
    rw [mem_valBall, hv, WithZero.exp_le_exp]; omega
  have hra : r ≤ ord x := by
    rw [mem_valBall, hv, WithZero.exp_le_exp] at hx; omega
  have := logSeries_sub_self_mem p hxa (sub_one_le_of_lt p hr hra)
  rw [h, zero_sub] at this
  exact hxa1 (by simpa using neg_mem this)
end GroundTheory.LocalField

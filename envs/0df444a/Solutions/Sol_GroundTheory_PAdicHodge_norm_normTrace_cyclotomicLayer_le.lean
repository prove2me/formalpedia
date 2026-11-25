-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_normTrace_cyclotomicLayer_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:07:05.801974+00:00
-- url     : https://prove2.me/submissions/49d502b5-0c1a-4116-82c7-219fdd4b8a63

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_mono
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cyclotomicLayer_eq_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_towerVec_mem
import Theorems.Thm_GroundTheory_PAdicHodge_towerCoeff_mem
import Theorems.Thm_GroundTheory_PAdicHodge_eq_sum_towerCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_norm_towerCoeff_le
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {cF : ℝ} (hcF : 0 ≤ cF)
    (hF : ∀ n m : ℕ, stableIndex K ≤ n → n ≤ m → ∀ x ∈ cycl p m,
      ‖normTrace (cycl p n) x‖ ≤ cF * ‖x‖)
    {n m : ℕ} (hn : stableIndex K ≤ n) (hnm : n ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) :
    ‖normTrace (cyclotomicLayer K n) y‖ ≤
      cF * (∑ i, ‖towerVec K i‖ * ‖towerDualVec K i‖) * ‖y‖ := by
  have hexp := eq_sum_towerCoeff K (hn.trans hnm) hy
  have key : normTrace (cyclotomicLayer K n) y =
      ∑ i, towerVec K i * normTrace (cycl p n) (towerCoeff K m y i) := by
    conv_lhs => rw [hexp]
    rw [normTrace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, normTrace_mul_of_mem _ (cyclotomicLayer_mono K hn (towerVec_mem K i)),
      normTrace_cyclotomicLayer_eq_of_mem K hn hnm (towerCoeff_mem K m y i)]
  rw [key, Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have h1 := hF n m hn hnm _ (towerCoeff_mem K m y i)
  have h2 := norm_towerCoeff_le K (hn.trans hnm) hy i
  rw [norm_mul] at h2
  calc ‖towerVec K i‖ * ‖normTrace (cycl p n) (towerCoeff K m y i)‖
      ≤ ‖towerVec K i‖ * (cF * ‖towerCoeff K m y i‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖towerVec K i‖ * (cF * (‖y‖ * ‖towerDualVec K i‖)) := by gcongr
    _ = cF * (‖towerVec K i‖ * ‖towerDualVec K i‖) * ‖y‖ := by ring
end GroundTheory.PAdicHodge

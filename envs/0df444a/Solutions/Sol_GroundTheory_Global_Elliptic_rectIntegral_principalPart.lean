-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_principalPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:52.269752+00:00
-- url     : https://prove2.me/submissions/121ee7cc-21a8-4b91-846b-9e2e401d1eeb

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Theorems.Thm_GroundTheory_Global_Elliptic_notMem_rectBoundary_of_mem_Ioo
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_const_mul
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_finset_sum
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_sub_inv
import Theorems.Thm_GroundTheory_Global_Elliptic_rectIntegral_zpow_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped Interval Real
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution (f : ℂ → ℂ) {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectIntegral (principalPart f p) z w = 2 * π * I * residue f p := by
  have hp : p ∉ rectBoundary z w := notMem_rectBoundary_of_mem_Ioo
    ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
    ⟨(min_le_left _ _).trans_lt h3, h4.trans_le (le_max_right _ _)⟩
  have hne : ∀ u ∈ rectBoundary z w, u ≠ p := fun u hu h ↦ hp (h ▸ hu)
  have hc : ∀ k : ℕ, ContinuousOn (fun u ↦ ((u - p) ^ k)⁻¹) (rectBoundary z w) := fun k u hu ↦
    ((((continuous_id.sub continuous_const).pow k).continuousAt).inv₀
      (pow_ne_zero _ (sub_ne_zero.2 (hne u hu)))).continuousWithinAt
  set n := meromorphicShift f p
  have e : principalPart f p = fun u ↦ ∑ j ∈ Finset.range (n + 1),
      laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹ := rfl
  rw [e, rectIntegral_finset_sum (Finset.range (n + 1))
    (f := fun j u ↦ laurentCoeff f p j * ((u - p) ^ (n + 1 - j))⁻¹)
    (fun j _ ↦ continuousOn_const.mul (hc _))]
  simp_rw [rectIntegral_const_mul]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · rw [Nat.add_sub_cancel_left]
    simp_rw [pow_one]
    rw [rectIntegral_sub_inv h1 h2 h3 h4]
    exact mul_comm _ _
  · intro j hj
    have hj' : j < n := Finset.mem_range.1 hj
    have e2 : (fun u ↦ ((u - p) ^ (n + 1 - j))⁻¹) = fun u ↦ (u - p) ^ (-((n + 1 - j : ℕ) : ℤ)) := by
      funext u
      rw [zpow_neg, zpow_natCast]
    rw [e2, rectIntegral_zpow_sub _ hp, mul_zero]
    omega
end GroundTheory.Global.Elliptic

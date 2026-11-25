-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassP_eq_of_G_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:20:51.542048+00:00
-- url     : https://prove2.me/submissions/2d7ec40d-a0a0-48f8-9769-1ecd2d8363af

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_JInvariantHomothety
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassLaurentCoeff_eq_of_G_eq
import Theorems.Thm_GroundTheory_Global_Elliptic_hasSum_weierstrassP_laurent


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
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {L L' : PeriodPair} {t : ℂ} (ht : t ≠ 0)
    (hG : ∀ k, 2 ≤ k → L'.G (2 * k) = t ^ (2 * k) * L.G (2 * k)) {z : ℂ} (hz0 : z ≠ 0)
    (hz' : ∀ l : L'.lattice, (l : ℂ) ≠ 0 → ‖z‖ < ‖(l : ℂ)‖)
    (hz : ∀ l : L.lattice, (l : ℂ) ≠ 0 → ‖t * z‖ < ‖(l : ℂ)‖) :
    ℘[L'] z = t ^ 2 * ℘[L] (t * z) := by
  have h1 := hasSum_weierstrassP_laurent (L := L') hz'
  have h2 := (hasSum_weierstrassP_laurent (L := L) hz).mul_left (t ^ 2)
  have h3 : HasSum (fun j ↦ weierstrassLaurentCoeff L' j * z ^ j)
      (t ^ 2 * (℘[L] (t * z) - 1 / (t * z) ^ 2)) := by
    have hfun : (fun j ↦ weierstrassLaurentCoeff L' j * z ^ j) =
        fun j ↦ t ^ 2 * (weierstrassLaurentCoeff L j * (t * z) ^ j) := by
      funext j
      rw [weierstrassLaurentCoeff_eq_of_G_eq hG, mul_pow]
      ring
    rw [hfun]
    exact h2
  have e := h1.unique h3
  have e' : t ^ 2 * (1 / (t * z) ^ 2) = 1 / z ^ 2 := by
    field_simp
  linear_combination e - e'
end GroundTheory.Global.Elliptic

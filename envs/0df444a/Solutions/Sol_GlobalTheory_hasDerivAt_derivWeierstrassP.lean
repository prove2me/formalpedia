-- Prove2me | solution 1 for GlobalTheory.hasDerivAt_derivWeierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:13.743892+00:00
-- url     : https://prove2.me/submissions/ce16885a-eb9d-47da-8a45-3be04dc2a2d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_countable_periodLattice
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_eventually_ne_notMem_periodLattice
import Theorems.Thm_GlobalTheory_not_eventually_weierstrassP_eq
import Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  have hd : ∀ z ∉ L.lattice, HasDerivAt ℘'[L] (deriv ℘'[L] z) z := fun z hz ↦
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have h1 : ∀ z ∈ (L.lattice : Set ℂ)ᶜ,
      ℘'[L] z * (deriv ℘'[L] z - (6 * ℘[L] z ^ 2 - L.g₂ / 2)) = 0 := fun z hz ↦ by
    have h2 := (hd z hz).pow 2
    have h3 := ((((hasDerivAt_weierstrassP L hz).pow 3).const_mul 4).sub
      ((hasDerivAt_weierstrassP L hz).const_mul L.g₂)).sub_const L.g₃
    have h4 := h2.unique (h3.congr_of_eventuallyEq (by
      filter_upwards [eventually_notMem_periodLattice L hz] with w hw
      simpa using L.derivWeierstrassP_sq w hw))
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h4
    linear_combination h4 / 2
  have hP := L.analyticOnNhd_weierstrassP
  have hP' := L.analyticOnNhd_derivWeierstrassP
  have h5 := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hP'
    (g := fun z ↦ deriv ℘'[L] z - (6 * ℘[L] z ^ 2 - L.g₂ / 2))
    (fun z hz ↦ by have := hP z hz; have := (hP' z hz).deriv; fun_prop) h1
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_periodLattice L)).2
  rcases h5 with h5 | h5
  · exfalso
    have h6 : Set.EqOn ℘[L] (fun _ ↦ ℘[L] z) (L.lattice : Set ℂ)ᶜ :=
      IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) L.isClosed_lattice.isOpen_compl
        (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_periodLattice L)).2
        L.differentiableOn_weierstrassP (by fun_prop) (fun w hw ↦ by simpa using h5 w hw) hz rfl
    refine not_eventually_weierstrassP_eq L (zero_mem _) (g := fun _ ↦ ℘[L] z) (by fun_prop) ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw using h6 hw
  · rw [← sub_eq_zero.mp (h5 z hz)]
    exact hd z hz
end GlobalTheory

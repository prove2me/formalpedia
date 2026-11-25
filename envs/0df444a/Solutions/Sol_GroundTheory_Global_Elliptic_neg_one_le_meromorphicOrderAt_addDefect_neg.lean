-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.neg_one_le_meromorphicOrderAt_addDefect_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:34.670834+00:00
-- url     : https://prove2.me/submissions/e52bb2d5-4484-40a0-9975-ab8b06e7a175

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_eq_except_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_isEllipticFunction_addDefect
import Theorems.Thm_GroundTheory_Global_Elliptic_addDefect_algebra_neg
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_dslope
import Theorems.Thm_GroundTheory_Global_Elliptic_two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero


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
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (addDefect L w) (-w) := by
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have hpw : AnalyticAt ℂ ℘[L] (-w) := L.analyticOnNhd_weierstrassP _ hw'
  have hdw : AnalyticAt ℂ ℘'[L] (-w) := L.analyticOnNhd_derivWeierstrassP _ hw'
  have hd0 : ℘'[L] w ≠ 0 := fun h ↦
    h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  set U := dslope ℘[L] (-w) with hU
  have hUa : AnalyticAt ℂ U (-w) := analyticAt_dslope hpw
  have hU0 : U (-w) = -℘'[L] w := by
    rw [hU, dslope_same, L.deriv_weierstrassP, L.derivWeierstrassP_neg]
  have hU0' : U (-w) ≠ 0 := by rw [hU0]; exact neg_ne_zero.2 hd0
  set M : ℂ → ℂ := fun z ↦ 4 * U z ^ 2 - (℘'[L] z - ℘'[L] w) ^ 2 with hM
  have hMa : AnalyticAt ℂ M (-w) := by simp only [hM]; fun_prop
  have hM0 : M (-w) = 0 := by simp only [hM, hU0, L.derivWeierstrassP_neg]; ring
  set M₁ := dslope M (-w) with hM₁
  have hM₁a : AnalyticAt ℂ M₁ (-w) := analyticAt_dslope hMa
  have hP0 : AnalyticAt ℂ (fun z ↦ ℘[L - (0 : ℂ)] (z + w)) (-w) := by
    have h : AnalyticAt ℂ ℘[L - (0 : ℂ)] (-w + w) := by
      rw [neg_add_cancel]
      exact L.analyticAt_weierstrassPExcept 0
    exact h.comp (g := ℘[L - (0 : ℂ)]) (f := fun z ↦ z + w) (by fun_prop)
  set H : ℂ → ℂ := fun z ↦ (z - -w) * ℘[L - (0 : ℂ)] (z + w) + (z - -w) * (℘[L] z + ℘[L] w) +
    M₁ z / (4 * U z ^ 2) with hH
  have hHa : AnalyticAt ℂ H (-w) := by
    simp only [hH]
    refine AnalyticAt.add (by fun_prop) (AnalyticAt.div hM₁a (by fun_prop) ?_)
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hU0')
  have hev : (fun z ↦ (z - -w) * addDefect L w z) =ᶠ[𝓝[≠] (-w)] H := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hUa.continuousAt.eventually_ne hU0')] with z hz hUz
    have ht : z - -w ≠ 0 := sub_ne_zero.2 hz
    have ht' : z + w ≠ 0 := by rwa [sub_neg_eq_add] at ht
    have eD : ℘[L] z - ℘[L] w = (z - -w) * U z := by
      have := sub_smul_dslope ℘[L] (-w) z
      rw [smul_eq_mul, L.weierstrassP_neg] at this
      rw [hU]
      exact this.symm
    have eM : M₁ z = (4 * U z ^ 2 - (℘'[L] z - ℘'[L] w) ^ 2) / (z - -w) := by
      have := sub_smul_dslope M (-w) z
      rw [smul_eq_mul, hM0, sub_zero] at this
      rw [eq_div_iff ht, mul_comm, hM₁, this]
    have e1 := weierstrassP_eq_except_zero (L := L) (z + w)
    simp only [addDefect, chordSlope, hH]
    rw [eD, eM, e1]
    exact addDefect_algebra_neg _ _ _ _ _ _ _ ht hUz
  have hord : 0 ≤ meromorphicOrderAt (fun z ↦ (z - -w) * addDefect L w z) (-w) := by
    rw [meromorphicOrderAt_congr hev]
    exact hHa.meromorphicOrderAt_nonneg
  rw [fun_meromorphicOrderAt_mul (by fun_prop) ((isEllipticFunction_addDefect w).1 _),
    meromorphicOrderAt_id_sub_const] at hord
  generalize meromorphicOrderAt (addDefect L w) (-w) = o at hord ⊢
  induction o with
  | top => exact le_top
  | coe n =>
    have : (0 : ℤ) ≤ 1 + n := by exact_mod_cast hord
    exact_mod_cast (by omega : (-1 : ℤ) ≤ n)
end GroundTheory.Global.Elliptic

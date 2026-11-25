-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.deriv_derivWeierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:05.967607+00:00
-- url     : https://prove2.me/submissions/e7956ee6-a8ba-492d-b8a3-bb114825bd24

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_hasDerivAt_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_hasDerivAt_derivWeierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_codiscrete_derivWeierstrassP_ne_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_eventually_nhdsNE_of_eventually_codiscrete


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
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) :
    deriv ℘'[L] z = 6 * ℘[L] z ^ 2 - L.g₂ / 2 := by
  have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have key : ∀ u ∉ L.lattice,
      ℘'[L] u * (2 * deriv ℘'[L] u - (12 * ℘[L] u ^ 2 - L.g₂)) = 0 := by
    intro u hu
    have h1 : HasDerivAt (℘'[L] ^ 2) (2 * ℘'[L] u * deriv ℘'[L] u) u :=
      ((hasDerivAt_derivWeierstrassP hu).pow 2).congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun v ↦ 4 * ℘[L] v ^ 3 - L.g₂ * ℘[L] v - L.g₃)
        ((12 * ℘[L] u ^ 2 - L.g₂) * ℘'[L] u) u := by
      have hp := hasDerivAt_weierstrassP hu
      exact ((((hp.pow 3).const_mul 4).sub (hp.const_mul L.g₂)).sub_const L.g₃).congr_deriv
        (by norm_num; ring)
    have heq : (℘'[L] ^ 2) =ᶠ[𝓝 u]
        (fun v ↦ 4 * ℘[L] v ^ 3 - L.g₂ * ℘[L] v - L.g₃) := by
      filter_upwards [hopen.mem_nhds hu] with v hv
      exact L.derivWeierstrassP_sq v hv
    have := h1.unique (h2.congr_of_eventuallyEq heq)
    linear_combination this
  by_cases h0 : ℘'[L] z = 0
  · set D : ℂ → ℂ := fun u ↦ deriv ℘'[L] u - (6 * ℘[L] u ^ 2 - L.g₂ / 2) with hD
    have hDc : ContinuousAt D z := by
      have h1 := (L.analyticOnNhd_derivWeierstrassP z hz).deriv.continuousAt
      have h2 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
      exact h1.sub (((h2.pow 2).const_mul 6).sub continuousAt_const)
    have hev : ∀ᶠ u in 𝓝[≠] z, D u = 0 := by
      filter_upwards [eventually_nhdsNE_of_eventually_codiscrete
        (eventually_codiscrete_derivWeierstrassP_ne_zero (L := L)) z,
        nhdsWithin_le_nhds (hopen.mem_nhds hz)] with u hu1 hu2
      rcases mul_eq_zero.1 (key u hu2) with h | h
      · exact absurd h hu1
      · simp only [hD]
        linear_combination h / 2
    have hlim := tendsto_nhds_unique (hDc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (hev.mono fun u hu ↦ hu.symm))
    simp only [hD] at hlim
    linear_combination hlim
  · rcases mul_eq_zero.1 (key z hz) with h | h
    · exact absurd h h0
    · linear_combination h / 2
end GroundTheory.Global.Elliptic

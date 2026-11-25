-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.derivWeierstrassP_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:51.141561+00:00
-- url     : https://prove2.me/submissions/fcba7480-5c1e-4bed-8379-85484e8ff485

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_hasDerivAt_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_hasDerivAt_derivWeierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_deriv_derivWeierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_add
import Theorems.Thm_GroundTheory_Global_Elliptic_derivAdd_algebra
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub


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
theorem _root_.solution {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘'[L] (z + w) = -(chordSlope L z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  have hopen : IsOpen {u : ℂ | u ∉ L.lattice ∧ u - w ∉ L.lattice ∧ u + w ∉ L.lattice} := by
    have h := L.isClosed_lattice.isOpen_compl
    exact h.inter ((h.preimage (continuous_sub_right w)).inter
      (h.preimage (continuous_add_right w)))
  have hne : ℘[L] z - ℘[L] w ≠ 0 := fun h ↦
    (sub_mem_or_add_mem_of_weierstrassP_eq hz hw (sub_eq_zero.1 h)).elim hzw hzw'
  have hL : HasDerivAt (fun u ↦ ℘[L] (u + w)) (℘'[L] (z + w)) z :=
    (hasDerivAt_weierstrassP hzw').comp_add_const z w
  have hp := hasDerivAt_weierstrassP hz
  have hd : HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
    rw [← deriv_derivWeierstrassP hz]
    exact hasDerivAt_derivWeierstrassP hz
  have hm : HasDerivAt (fun u ↦ chordSlope L u w)
      (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w) - (℘'[L] z - ℘'[L] w) * ℘'[L] z) /
        (℘[L] z - ℘[L] w) ^ 2) z :=
    (hd.sub_const (℘'[L] w)).div (hp.sub_const (℘[L] w)) hne
  have hR : HasDerivAt (fun u ↦ chordSlope L u w ^ 2 / 4 - ℘[L] u - ℘[L] w)
      (2 * chordSlope L z w * (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w) -
        (℘'[L] z - ℘'[L] w) * ℘'[L] z) / (℘[L] z - ℘[L] w) ^ 2) / 4 - ℘'[L] z) z :=
    ((((hm.pow 2).div_const 4).sub hp).sub_const (℘[L] w)).congr_deriv (by norm_num)
  have heq : (fun u ↦ ℘[L] (u + w)) =ᶠ[𝓝 z]
      (fun u ↦ chordSlope L u w ^ 2 / 4 - ℘[L] u - ℘[L] w) := by
    filter_upwards [hopen.mem_nhds ⟨hz, hzw, hzw'⟩] with u hu
    exact weierstrassP_add hu.1 hw hu.2.1 hu.2.2
  rw [hL.unique (hR.congr_of_eventuallyEq heq), weierstrassP_add hz hw hzw hzw']
  simp only [chordSlope]
  exact derivAdd_algebra _ _ _ _ _ _ hne (L.derivWeierstrassP_sq z hz) (L.derivWeierstrassP_sq w hw)
end GroundTheory.Global.Elliptic

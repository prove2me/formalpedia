-- Prove2me | solution 1 for GlobalTheory.weierstrassP_add_add_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:17.683788+00:00
-- url     : https://prove2.me/submissions/4cb6c989-5a56-4bef-b06d-480e57032008

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk

set_option autoImplicit false
open Filter PeriodPair WeierstrassCurve
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
open Filter PeriodPair WeierstrassCurve
open scoped Topology
variable (L : PeriodPair)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) + ℘[L] (z - w) - 2 * ℘[L] w =
      (6 * ℘[L] w ^ 2 - L.g₂ / 2) / (℘[L] z - ℘[L] w) + ℘'[L] w ^ 2 / (℘[L] z - ℘[L] w) ^ 2 := by
  have hmw : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  have hne' : ℘[L] z ≠ ℘[L] (-w) := by rwa [weierstrassP_neg]
  obtain ⟨h1, -⟩ := weierstrassP_add_and_deriv_add_of_ne L hz hw hne
  obtain ⟨h2, -⟩ := weierstrassP_add_and_deriv_add_of_ne L hz hmw hne'
  rw [weierstrassP_neg, derivWeierstrassP_neg, ← sub_eq_add_neg] at h2
  have ez := derivWeierstrassP_sq L z hz
  have ew := derivWeierstrassP_sq L w hw
  have hsub : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hne
  have hy : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 + (℘[L] z - ℘[L] w) *
      (4 * (℘[L] z ^ 2 + ℘[L] z * ℘[L] w + ℘[L] w ^ 2) - L.g₂) := by
    linear_combination ez - ew
  rw [h1, h2]
  field_simp
  linear_combination 4 * hy
end _root_.GlobalTheory
end GlobalTheory

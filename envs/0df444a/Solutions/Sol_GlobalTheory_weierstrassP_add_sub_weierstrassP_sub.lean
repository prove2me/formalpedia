-- Prove2me | solution 1 for GlobalTheory.weierstrassP_add_sub_weierstrassP_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:15.610651+00:00
-- url     : https://prove2.me/submissions/1e87278a-2903-431a-9e33-ead98ab5ba01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassPAddSubWeierstrassPSub
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
import Theorems.Thm_GlobalTheory_weierstrassP_add
import Theorems.Thm_GlobalTheory_weierstrassP_eq_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (L : PeriodPair) (z w : ℂ) (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (h₁ : z - w ∉ L.lattice) (h₂ : z + w ∉ L.lattice) :
    (L.weierstrassP z - L.weierstrassP w) ^ 2 *
        (L.weierstrassP (z + w) - L.weierstrassP (z - w)) =
      -(L.derivWeierstrassP z * L.derivWeierstrassP w) := by
  have hne : L.weierstrassP z ≠ L.weierstrassP w := by
    rw [Ne, weierstrassP_eq_iff L hz hw]; tauto
  have e1 := (weierstrassP_add L hz hw hne).1
  have e2 := (weierstrassP_add L (w := -w) hz (by simpa using hw) (by simpa using hne)).1
  rw [← sub_eq_add_neg, L.weierstrassP_neg, L.derivWeierstrassP_neg] at e2
  have hd : L.weierstrassP z - L.weierstrassP w ≠ 0 := sub_ne_zero.mpr hne
  rw [e1, e2]
  field_simp
  ring
end GlobalTheory

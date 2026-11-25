-- Prove2me | solution 1 for GlobalTheory.weierstrassP_two_mul_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:17.406578+00:00
-- url     : https://prove2.me/submissions/9bb78803-b5fc-4c6d-9581-f995638796a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassPTwoMulMulSq
import Theorems.Thm_GlobalTheory_derivWeierstrassP_eq_zero_iff
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
open PeriodPair WeierstrassCurve
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice)
    (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) * L.derivWeierstrassP z ^ 2 =
      (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 / 4 -
        2 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 := by
  rw [two_mul z] at h2 ⊢
  have hd : L.derivWeierstrassP z ≠ 0 := (derivWeierstrassP_eq_zero_iff L hz).not.mpr h2
  have hy : L.derivWeierstrassP z / 2 ≠
      (latticeCurve L).toAffine.negY (L.weierstrassP z) (L.derivWeierstrassP z / 2) := by
    intro h
    apply hd
    simp only [Affine.negY, latticeCurve] at h
    linear_combination h
  have h := latticePoint_add L z z
  rw [latticePoint_of_notMem L hz, latticePoint_of_notMem L h2,
    Affine.Point.add_self_of_Y_ne hy, Affine.Point.some.injEq] at h
  have e := h.1
  rw [Affine.slope_of_Y_ne rfl hy] at e
  simp only [Affine.negY, Affine.addX, latticeCurve] at e
  have e2 : L.derivWeierstrassP z / 2 -
      (-(L.derivWeierstrassP z / 2) - 0 * L.weierstrassP z - 0) = L.derivWeierstrassP z := by ring
  rw [e2] at e
  rw [e]
  field_simp
  ring
end GlobalTheory

-- Prove2me | solution 1 for GlobalTheory.map_eq_one_of_pow_eq_one_of_finite_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:58.324797+00:00
-- url     : https://prove2.me/submissions/05f85b01-5f01-43f2-8bc9-068eb9686a91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedTorusExtensionOfPowEqOne
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {H B : Type*} [Group H] [Group B] (φ : H →* B)
    [Finite φ.ker] {n : ℕ} (hn : n.Prime) (h : ∀ x : H, x ^ n = 1 → x = 1) (y : H)
    (hy : φ y ^ n = 1) : φ y = 1 := by
  have hmem : y ^ n ∈ φ.ker := by rw [MonoidHom.mem_ker, map_pow, hy]
  have h1 : IsOfFinOrder (y ^ n) :=
    φ.ker.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨y ^ n, hmem⟩ : φ.ker))
  have h2 : IsOfFinOrder y := h1.of_pow hn.ne_zero
  have h3 : ¬ n ∣ orderOf y := by
    rintro ⟨m, hm⟩
    have h4 : y ^ m = 1 := h _ (by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one])
    have h5 := orderOf_dvd_of_pow_eq_one h4
    have h6 := h2.orderOf_pos
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at h6)
    have h7 := Nat.le_of_dvd hm0 h5
    have h8 := hn.two_le
    nlinarith
  have h9 : orderOf (φ y) ∣ Nat.gcd n (orderOf y) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy) (orderOf_map_dvd φ y)
  rw [(hn.coprime_iff_not_dvd.2 h3).gcd_eq_one] at h9
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h9)
end GlobalTheory

-- Prove2me | solution 1 for GroundTheory.LocalField.IsElementaryAt.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:43.499883+00:00
-- url     : https://prove2.me/submissions/29bbf23c-22ad-4a96-be15-9aefb3a1829a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
variable {G : Type*} [Group G]
variable [Finite G] {p : ℕ}
omit [Finite G]
namespace GroundTheory.LocalField
namespace IsElementaryAt
theorem _root_.solution {H L : Subgroup G} (hH : IsElementaryAt p H) (hLH : L ≤ H) :
    IsElementaryAt p L := by
  obtain ⟨C, P, hCH, hPH, hC, hCp, hP, hcomm, hdec⟩ := hH
  refine ⟨L ⊓ C, L ⊓ P, inf_le_left, inf_le_left, Subgroup.isCyclic_of_le inf_le_right, ?_,
    hP.to_le inf_le_right, fun c hc y hy ↦ hcomm c hc.2 y hy.2, ?_⟩
  · exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right) hCp
  · intro l hl
    obtain ⟨c, hc, y, hy, rfl⟩ := hdec l (hLH hl)
    obtain ⟨j, hj⟩ := hP ⟨y, hy⟩
    have hyj : y ^ p ^ j = 1 := by
      have := congrArg Subtype.val hj
      simpa using this
    have hoc : orderOf c ∣ Nat.card C := by
      rw [← Subgroup.orderOf_mk c hc]
      exact orderOf_dvd_natCard _
    have hcop : (orderOf c).Coprime (p ^ j) :=
      Nat.Coprime.pow_right j (Nat.Coprime.coprime_dvd_left hoc hCp)
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hcy : Commute c y := hcomm c hc y hy
    have hpow : (c * y) ^ (v * ((p ^ j : ℕ) : ℤ)) = c := by
      rw [hcy.mul_zpow, zpow_mul' y, zpow_natCast y, hyj, one_zpow, mul_one,
        show v * ((p ^ j : ℕ) : ℤ) = 1 - u * (orderOf c : ℤ) by rw [← huv]; ring, zpow_sub, zpow_one,
        zpow_mul', zpow_natCast c, pow_orderOf_eq_one, one_zpow, inv_one, mul_one]
    have hcL : c ∈ L := hpow ▸ L.zpow_mem hl _
    have hyL : y ∈ L := by
      have := L.mul_mem (L.inv_mem hcL) hl
      rwa [inv_mul_cancel_left] at this
    exact ⟨c, ⟨hcL, hc⟩, y, ⟨hyL, hy⟩, rfl⟩
end IsElementaryAt
end GroundTheory.LocalField

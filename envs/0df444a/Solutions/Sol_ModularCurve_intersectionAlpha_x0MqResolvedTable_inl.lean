-- Prove2me | solution 1 for ModularCurve.intersectionAlpha_x0MqResolvedTable_inl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/06dc4b36-5e22-568d-99f8-2fe8039bc7b0

import Mathlib
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl

set_option autoImplicit false

p2m_open "MazurRapoportAppendix ModularCurve P2MW.S_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "X0MqComponents x0MqAdj x0MqAdj_symm x0MqResolvedTable DRResolvedModelPackage.chainPos DRResolvedModelPackage"
p2m_open "ModularCurve"

variable {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ)

omit [Fintype node] [DecidableEq node] in
theorem chainPos_zero'' (n : node) : DRResolvedModelPackage.chainPos width n 0 = Sum.inl 0 := by
  simp [DRResolvedModelPackage.chainPos]

omit [Fintype node] [DecidableEq node] in
theorem chainPos_of_pos_of_lt'' (n : node) (d : ℕ) (h0 : d ≠ 0) (hd : d < width n) :
    DRResolvedModelPackage.chainPos width n d = Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩ := by
  simp [DRResolvedModelPackage.chainPos, h0, hd]

omit [Fintype node] [DecidableEq node] in
theorem chainPos_of_le'' (n : node) (d : ℕ) (h0 : d ≠ 0) (hd : width n ≤ d) :
    DRResolvedModelPackage.chainPos width n d = Sum.inl 1 := by
  simp [DRResolvedModelPackage.chainPos, h0, not_lt.mpr hd]

omit [Fintype node] [DecidableEq node] in

theorem chainPos_side_eq_inl_iff (x : node) (hx : 1 ≤ width x) (b j : Fin 2) :
    DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1) = Sum.inl j ↔ (j ≠ b ∧ width x = 1) := by
  by_cases h1 : width x = 1
  · fin_cases b <;> fin_cases j <;>
      simp [h1, chainPos_zero'', chainPos_of_le'' width x 1 one_ne_zero (by omega)]
  · fin_cases b <;> fin_cases j <;>
      simp [h1, chainPos_of_pos_of_lt'' width x 1 one_ne_zero (by omega),
        chainPos_of_pos_of_lt'' width x (width x - 1) (by omega) (by omega)]

omit [Fintype node] in

theorem chainPos_side_eq_inr_iff (x : node) (hx : 1 ≤ width x) (b : Fin 2) (x' : node) (k : Fin (width x' - 1)) :
    DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1) = Sum.inr ⟨x', k⟩ ↔
      (x = x' ∧ ((b = 0 ∧ (k : ℕ) = 0) ∨ (b = 1 ∧ (k : ℕ) = width x' - 2))) := by
  by_cases hxx : x = x'
  · subst hxx
    have hk := k.isLt
    have h1 : ¬ width x = 1 := by omega
    fin_cases b <;>
      simp [chainPos_of_pos_of_lt'' width x 1 one_ne_zero (by omega),
        chainPos_of_pos_of_lt'' width x (width x - 1) (by omega) (by omega), Fin.ext_iff] <;> omega
  · simp only [hxx, false_and, iff_false]
    intro h
    by_cases h1 : width x = 1
    · fin_cases b
      · rw [Fin.zero_eta, if_pos rfl, chainPos_of_le'' width x 1 one_ne_zero (by omega)] at h; exact absurd h Sum.inl_ne_inr
      · simp only [Fin.mk_one, one_ne_zero, if_false] at h
        rw [show width x - 1 = 0 by omega, chainPos_zero''] at h; exact absurd h Sum.inl_ne_inr
    · have key : ∀ d, d ≠ 0 → d < width x → DRResolvedModelPackage.chainPos width x d ≠ Sum.inr ⟨x', k⟩ := by
        intro d hd0 hd h'
        rw [chainPos_of_pos_of_lt'' width x d hd0 hd] at h'
        exact hxx (congrArg Sigma.fst (Sum.inr.inj h'))
      fin_cases b
      · exact key 1 one_ne_zero (by omega) (by simpa using h)
      · exact key (width x - 1) (by omega) (by omega) (by simpa using h)

theorem x0MqAdj_inl_eq (hw : ∀ x, 1 ≤ width x) (b : Fin 2) (F : X0MqComponents width) :
    x0MqAdj width F (Sum.inl b) =
      ∑ x, if F = DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1) then 1 else 0 := by
  rcases F with j | ⟨x', k⟩
  ·
    have hrw : ∀ x, (Sum.inl j = DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1)) ↔
        (j ≠ b ∧ width x = 1) := fun x => by rw [eq_comm, chainPos_side_eq_inl_iff width x (hw x)]
    simp_rw [hrw]
    by_cases hjb : j = b <;> simp [x0MqAdj, hjb, Finset.sum_boole]
  ·
    have hrw : ∀ x, (Sum.inr ⟨x', k⟩ = DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1)) ↔
        (x = x' ∧ ((b = 0 ∧ (k : ℕ) = 0) ∨ (b = 1 ∧ (k : ℕ) = width x' - 2))) := fun x => by
      rw [eq_comm, chainPos_side_eq_inr_iff width x (hw x)]
    simp_rw [hrw]
    rw [Finset.sum_eq_single x' (fun x _ hx => if_neg (fun h => hx h.1)) (by simp)]
    simp only [x0MqAdj, true_and]

theorem sum_mul_x0MqAdj_inl (hw : ∀ x, 1 ≤ width x) (c : X0MqComponents width → ℤ) (b : Fin 2) :
    ∑ F, c F * (x0MqAdj width F (Sum.inl b) : ℤ) =
      ∑ x, c (DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1)) := by
  simp only [x0MqAdj_inl_eq width hw, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_x0MqAdj_inl (hw : ∀ x, 1 ≤ width x) (b : Fin 2) :
    ∑ F, (x0MqAdj width (Sum.inl b) F : ℤ) = Fintype.card node := by
  have h := sum_mul_x0MqAdj_inl width hw (fun _ => 1) b
  simp only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [← h]
  exact Finset.sum_congr rfl fun F _ => by rw [x0MqAdj_symm]

theorem intersectionAlpha_x0MqResolvedTable_inl (hw : ∀ x, 1 ≤ width x) (c : X0MqComponents width → ℤ) (b : Fin 2) :
    intersectionAlpha (x0MqResolvedTable width) c (Sum.inl b) =
      (∑ x, c (DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1))) -
        (Fintype.card node : ℤ) * c (Sum.inl b) := by
  rw [intersectionAlpha_apply]
  have hsplit : ∀ F, c F * (x0MqResolvedTable width).inter F (Sum.inl b) =
      c F * (x0MqAdj width F (Sum.inl b) : ℤ) -
        (if F = Sum.inl b then c F * ∑ j', (x0MqAdj width F j' : ℤ) else 0) := by
    intro F
    simp only [x0MqResolvedTable]
    split_ifs with h
    · subst h; ring
    · ring
  have key : (∑ F, if F = Sum.inl b then c F * ∑ j', (x0MqAdj width F j' : ℤ) else 0) =
      c (Sum.inl b) * ∑ j', (x0MqAdj width (Sum.inl b) j' : ℤ) := by
    rw [Fintype.sum_eq_single (Sum.inl b : X0MqComponents width) (fun F hF => if_neg hF), if_pos rfl]
  rw [Finset.sum_congr rfl fun F _ => hsplit F, Finset.sum_sub_distrib, sum_mul_x0MqAdj_inl width hw, key,
    sum_x0MqAdj_inl width hw]
  ring

end ModularCurve

theorem solution
    {node : Type} [Fintype node] [DecidableEq node] (width : node → ℕ) (hw : ∀ x, 1 ≤ width x)
    (c : X0MqComponents width → ℤ) (b : Fin 2) :
    intersectionAlpha (x0MqResolvedTable width) c (Sum.inl b) =
      (∑ x, c (DRResolvedModelPackage.chainPos width x (if b = 0 then 1 else width x - 1))) -
        (Fintype.card node : ℤ) * c (Sum.inl b) :=
  ModularCurve.intersectionAlpha_x0MqResolvedTable_inl width hw c b

end S_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl
end P2MW
export P2MW.S_ModularCurve_intersectionAlpha_x0MqResolvedTable_inl (solution)

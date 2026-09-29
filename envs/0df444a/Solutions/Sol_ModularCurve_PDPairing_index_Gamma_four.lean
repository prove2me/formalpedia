-- Prove2me | solution 1 for ModularCurve.PDPairing.index_Gamma_four
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/65891cb6-09bd-5348-9455-193185489555

import Definitions.Def_ModularCurve_PDPairing
import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Schreier
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.Module.Hom
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Tactic.Group
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PDPairing_index_Gamma_four

set_option autoImplicit false

open scoped MatrixGroups

section InlinedSAN123

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace Sanov
p2m_open "ModularCurve"

def sanovA : SL(2, ℤ) := ModularGroup.T ^ 2

def sanovB : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by simp [Matrix.det_fin_two_of]⟩

@[scoped simp] theorem coe_sanovA : (↑sanovA : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2; 0, 1] := by
  have h := ModularGroup.coe_T_zpow (2 : ℤ)
  rw [zpow_two] at h
  simpa [sanovA, sq] using h

@[scoped simp] theorem coe_sanovB : (↑sanovB : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2, 1] := rfl

def sanovSubgroup : Subgroup SL(2, ℤ) := Subgroup.closure {sanovA, sanovB}

open scoped Pointwise

example : DistribMulAction SL(2, ℤ) (Fin 2 → ℤ) := inferInstance

theorem smul_apply_0 (m : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    (m • v) 0 = (m : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v 0 + (m : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * v 1 := by
  show ((m : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 0 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem smul_apply_1 (m : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    (m • v) 1 = (m : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * v 0 + (m : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * v 1 := by
  show ((m : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 1 = _
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem coe_sanovA_zpow (n : ℤ) :
    (↑(sanovA ^ n) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2 * n; 0, 1] := by
  induction n using Int.induction_on with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [zpow_add_one, SpecialLinearGroup.coe_mul, ih, coe_sanovA]
    simp only [Matrix.mul_fin_two]; ring_nf
  | pred k ih =>
    rw [zpow_sub_one, SpecialLinearGroup.coe_mul, ih]
    have hAinv : (↑(sanovA⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -2; 0, 1] := by
      rw [SpecialLinearGroup.coe_inv, coe_sanovA, Matrix.adjugate_fin_two]; simp
    rw [hAinv]
    simp only [Matrix.mul_fin_two]; ring_nf

theorem coe_sanovB_zpow (n : ℤ) :
    (↑(sanovB ^ n) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2 * n, 1] := by
  induction n using Int.induction_on with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [zpow_add_one, SpecialLinearGroup.coe_mul, ih, coe_sanovB]
    simp only [Matrix.mul_fin_two]; ring_nf
  | pred k ih =>
    rw [zpow_sub_one, SpecialLinearGroup.coe_mul, ih]
    have hBinv : (↑(sanovB⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -2, 1] := by
      rw [SpecialLinearGroup.coe_inv, coe_sanovB, Matrix.adjugate_fin_two]; simp
    rw [hBinv]
    simp only [Matrix.mul_fin_two]; ring_nf

theorem sanovA_zpow_smul (n : ℤ) (v : Fin 2 → ℤ) :
    (sanovA ^ n • v) 0 = v 0 + 2 * n * v 1 ∧ (sanovA ^ n • v) 1 = v 1 := by
  refine ⟨?_, ?_⟩
  · rw [smul_apply_0, coe_sanovA_zpow]; simp
  · rw [smul_apply_1, coe_sanovA_zpow]; simp

theorem sanovB_zpow_smul (n : ℤ) (v : Fin 2 → ℤ) :
    (sanovB ^ n • v) 0 = v 0 ∧ (sanovB ^ n • v) 1 = 2 * n * v 0 + v 1 := by
  refine ⟨?_, ?_⟩
  · rw [smul_apply_0, coe_sanovB_zpow]; simp
  · rw [smul_apply_1, coe_sanovB_zpow]; simp

def sanovP : Set (Fin 2 → ℤ) := {v | |v 1| < |v 0|}

def sanovQ : Set (Fin 2 → ℤ) := {v | |v 0| < |v 1|}

theorem sanovP_nonempty : sanovP.Nonempty := ⟨![1, 0], by simp [sanovP]⟩
theorem sanovQ_nonempty : sanovQ.Nonempty := ⟨![0, 1], by simp [sanovQ]⟩

theorem disjoint_sanovP_sanovQ : Disjoint sanovP sanovQ := by
  rw [Set.disjoint_left]
  intro v hP hQ
  simp only [sanovP, sanovQ, Set.mem_setOf_eq] at hP hQ
  exact absurd (lt_trans hQ hP) (lt_irrefl _)

theorem sanovA_zpow_smul_sanovQ_subset (n : ℤ) (hn : n ≠ 0) :
    sanovA ^ n • sanovQ ⊆ sanovP := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [sanovQ, Set.mem_setOf_eq] at hv
  simp only [sanovP, Set.mem_setOf_eq, (sanovA_zpow_smul n v).1, (sanovA_zpow_smul n v).2]
  have h1n : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
  have habs : |2 * n * v 1| = 2 * |n| * |v 1| := by
    rw [abs_mul, abs_mul]; norm_num
  have key : |2 * n * v 1| ≤ |v 0 + 2 * n * v 1| + |v 0| := by
    have h := abs_add_le (v 0 + 2 * n * v 1) (-(v 0))
    rw [show v 0 + 2 * n * v 1 + -v 0 = 2 * n * v 1 by ring, abs_neg] at h
    exact h
  calc |v 1| < 2 * |v 1| - |v 0| := by linarith
    _ ≤ 2 * |n| * |v 1| - |v 0| := by nlinarith [abs_nonneg (v 1)]
    _ = |2 * n * v 1| - |v 0| := by rw [habs]
    _ ≤ |v 0 + 2 * n * v 1| := by linarith

theorem sanovB_zpow_smul_sanovP_subset (n : ℤ) (hn : n ≠ 0) :
    sanovB ^ n • sanovP ⊆ sanovQ := by
  rintro _ ⟨v, hv, rfl⟩
  simp only [sanovP, Set.mem_setOf_eq] at hv
  simp only [sanovQ, Set.mem_setOf_eq, (sanovB_zpow_smul n v).1, (sanovB_zpow_smul n v).2]
  have h1n : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
  have habs : |2 * n * v 0| = 2 * |n| * |v 0| := by
    rw [abs_mul, abs_mul]; norm_num
  have key : |2 * n * v 0| ≤ |2 * n * v 0 + v 1| + |v 1| := by
    have h := abs_add_le (2 * n * v 0 + v 1) (-(v 1))
    rw [show 2 * n * v 0 + v 1 + -v 1 = 2 * n * v 0 by ring, abs_neg] at h
    exact h
  calc |v 0| < 2 * |v 0| - |v 1| := by linarith
    _ ≤ 2 * |n| * |v 0| - |v 1| := by nlinarith [abs_nonneg (v 0)]
    _ = |2 * n * v 0| - |v 1| := by rw [habs]
    _ ≤ |2 * n * v 0 + v 1| := by linarith

def sanovFactor (i : Fin 2) : FreeGroup Unit →* SL(2, ℤ) :=
  FreeGroup.lift fun _ => ![sanovA, sanovB] i

def sanovLift : Monoid.CoprodI (fun _ : Fin 2 => FreeGroup Unit) →* SL(2, ℤ) :=
  Monoid.CoprodI.lift sanovFactor

open Monoid in

theorem sanovLift_injective : Function.Injective sanovLift := by
  apply CoprodI.lift_injective_of_ping_pong sanovFactor ?_
    (![sanovP, sanovQ]) ?_ ?_ ?_
  ·
    right
    haveI : Infinite (FreeGroup Unit) :=
      FreeGroup.freeGroupUnitEquivInt.infinite_iff.mpr inferInstance
    refine ⟨0, le_trans ?_ (Cardinal.aleph0_le_mk _)⟩
    exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 3)).le
  ·
    intro i; fin_cases i
    · exact sanovP_nonempty
    · exact sanovQ_nonempty
  ·
    intro i j hij; fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_sanovP_sanovQ
    · exact disjoint_sanovP_sanovQ.symm
    · exact absurd rfl hij
  ·
    intro i j hij h hh
    set n := FreeGroup.freeGroupUnitEquivInt h with hndef
    have hheq : h = FreeGroup.of () ^ n := by
      have := FreeGroup.freeGroupUnitEquivInt.symm_apply_apply h
      rw [← hndef] at this
      exact this.symm
    have hn : n ≠ 0 := fun h0 => hh (by rw [hheq, h0, zpow_zero])
    rw [hheq]
    have hfi : sanovFactor i (FreeGroup.of () ^ n) = (![sanovA, sanovB] i) ^ n := by
      simp [sanovFactor]
    rw [hfi]
    fin_cases i <;> fin_cases j <;> first | (exact absurd rfl hij) | skip
    · exact sanovA_zpow_smul_sanovQ_subset n hn
    · exact sanovB_zpow_smul_sanovP_subset n hn

theorem sanovSubgroup_eq_range : sanovSubgroup = sanovLift.range := by
  apply le_antisymm
  · exact Subgroup.closure_le _ |>.mpr (by
      rintro _ (rfl | rfl)
      · exact ⟨Monoid.CoprodI.of (FreeGroup.of () : FreeGroup Unit) (i := 0), by
          simp [sanovLift, sanovFactor]⟩
      · exact ⟨Monoid.CoprodI.of (FreeGroup.of () : FreeGroup Unit) (i := 1), by
          simp [sanovLift, sanovFactor]⟩)
  · rintro _ ⟨w, rfl⟩
    induction w using Monoid.CoprodI.induction_on with
    | one => simp
    | of i m =>
      rw [sanovLift, Monoid.CoprodI.lift_of]
      set n := FreeGroup.freeGroupUnitEquivInt m with hndef
      have hm : m = FreeGroup.of () ^ n := by
        rw [hndef]; exact (FreeGroup.freeGroupUnitEquivInt.symm_apply_apply m).symm
      have : sanovFactor i m = (![sanovA, sanovB] i) ^ n := by
        rw [hm]; simp [sanovFactor]
      rw [this]
      refine Subgroup.zpow_mem _ ?_ _
      fin_cases i
      · exact Subgroup.subset_closure (Or.inl rfl)
      · exact Subgroup.subset_closure (Or.inr rfl)
    | mul x y hx hy => simpa using sanovSubgroup.mul_mem hx hy

scoped instance sanov_isFreeGroup : IsFreeGroup ↥sanovSubgroup := by
  rw [sanovSubgroup_eq_range]
  exact IsFreeGroup.ofMulEquiv
    ((freeGroupEquivCoprodI (ι := Fin 2)).trans
      (MonoidHom.ofInjective sanovLift_injective))

theorem sanovA_mem_Gamma_two : sanovA ∈ Gamma 2 := by
  rw [Gamma_mem]; simp only [coe_sanovA, Matrix.of_apply]
  decide

theorem sanovB_mem_Gamma_two : sanovB ∈ Gamma 2 := by
  rw [Gamma_mem]; simp only [coe_sanovB, Matrix.of_apply]
  decide

theorem sanovSubgroup_le_Gamma_two : sanovSubgroup ≤ Gamma 2 :=
  Subgroup.closure_le _ |>.mpr (by
    rintro _ (rfl | rfl)
    · exact sanovA_mem_Gamma_two
    · exact sanovB_mem_Gamma_two)

theorem coe_00_mul_mod_four {g h : SL(2, ℤ)} (hg : g ∈ Gamma 2) (hh : h ∈ Gamma 2) :
    (((g * h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4)
      = ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4)
        * ((h : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) := by
  have h01 : (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod 2) = 0 := (Gamma_mem.mp hg).2.1
  have h10 : (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod 2) = 0 := (Gamma_mem.mp hh).2.2.1
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h01 h10
  have hprod : (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod 4)
      * (((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod 4) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast mul_dvd_mul h01 h10
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  rw [hprod, add_zero]

theorem coe_00_mod_four_of_mem_sanov {g : SL(2, ℤ)} (hg : g ∈ sanovSubgroup) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
  induction hg using Subgroup.closure_induction with
  | one => simp
  | mem x hx =>
    rcases hx with rfl | rfl
    · simp [coe_sanovA]
    · simp [coe_sanovB]
  | mul x y hx hy ihx ihy =>
    rw [coe_00_mul_mod_four (sanovSubgroup_le_Gamma_two hx) (sanovSubgroup_le_Gamma_two hy),
      ihx, ihy, one_mul]
  | inv x hx ihx =>
    have hxG2 := sanovSubgroup_le_Gamma_two hx
    have : (((x * x⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
      simp
    rw [coe_00_mul_mod_four hxG2 (Gamma 2 |>.inv_mem hxG2), ihx, one_mul] at this
    exact this

theorem mem_sanov_of_coe_10_eq_zero {g : SL(2, ℤ)} (hg2 : g ∈ Gamma 2)
    (hg4 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1)
    (hc : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) : g ∈ sanovSubgroup := by
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd

  have hdet : a * d = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two, ← ha, ← hb, hc, ← hd] at this
    linarith
  have hau : a = 1 ∨ a = -1 := by
    rcases Int.isUnit_iff.mp ⟨⟨a, d, hdet, by linarith [hdet]⟩, rfl⟩ with h | h
    · left; exact h
    · right; exact h
  have ha1 : a = 1 := by
    rcases hau with h | h
    · exact h
    · exfalso; rw [h] at hg4; exact absurd hg4 (by decide)
  have hd1 : d = 1 := by rw [ha1, one_mul] at hdet; exact hdet
  have hb2 : (2 : ℤ) ∣ b := by
    have := (Gamma_mem.mp hg2).2.1
    rwa [← hb, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  obtain ⟨k, hk⟩ := hb2
  have hg_eq : g = sanovA ^ k := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_sanovA_zpow]
    fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.empty_val']
    · exact ha1
    · rw [show (2 * k : ℤ) = b from hk.symm]; rfl
    · exact hc
    · exact hd1
  rw [hg_eq]
  exact sanovSubgroup.zpow_mem (Subgroup.subset_closure (Or.inl rfl)) k

theorem sanovA_zpow_mul_entries (ε : ℤ) (g : SL(2, ℤ)) :
    ((sanovA ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
      = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + 2 * ε * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
    ((sanovA ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [SpecialLinearGroup.coe_mul, coe_sanovA_zpow, Matrix.mul_apply, Fin.sum_univ_two]
    simp

theorem sanovB_zpow_mul_entries (ε : ℤ) (g : SL(2, ℤ)) :
    ((sanovB ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
      = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
    ((sanovB ^ ε * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = 2 * ε * (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  refine ⟨?_, ?_⟩ <;>
  · simp only [SpecialLinearGroup.coe_mul, coe_sanovB_zpow, Matrix.mul_apply, Fin.sum_univ_two]
    simp

theorem exists_eps_abs_sub_lt {a c : ℤ} (hca : |c| < |a|) (hc : c ≠ 0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ |a - 2 * ε * c| < |a| := by
  have ha : a ≠ 0 := by
    intro h; rw [h, abs_zero] at hca; exact absurd hca (not_lt_of_ge (abs_nonneg c))

  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hc with hc' | hc'
  · exact ⟨1, Or.inl rfl, by
      rw [abs_lt]; simp only [abs_of_neg ha', abs_of_neg hc'] at hca ⊢; omega⟩
  · exact ⟨-1, Or.inr rfl, by
      rw [abs_lt]; simp only [abs_of_neg ha', abs_of_pos hc'] at hca ⊢; omega⟩
  · exact ⟨-1, Or.inr rfl, by
      rw [abs_lt]; simp only [abs_of_pos ha', abs_of_neg hc'] at hca ⊢; omega⟩
  · exact ⟨1, Or.inl rfl, by
      rw [abs_lt]; simp only [abs_of_pos ha', abs_of_pos hc'] at hca ⊢; omega⟩

def sanovMeasure (g : SL(2, ℤ)) : ℕ :=
  (|(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0| + |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0|).natAbs

theorem mem_sanov_of_coe_00_mod_four {g : SL(2, ℤ)} (hg2 : g ∈ Gamma 2)
    (hg4 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1) : g ∈ sanovSubgroup := by
  induction hN : sanovMeasure g using Nat.strong_induction_on generalizing g with
  | _ N IH =>
  subst hN
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  by_cases hc0 : c = 0
  · exact mem_sanov_of_coe_10_eq_zero hg2 hg4 hc0
  have haodd : ¬ (2 : ℤ) ∣ a := by
    intro ⟨k, hk⟩
    have h1 : (a : ZMod 2) = 1 := (Gamma_mem.mp hg2).1
    rw [hk, Int.cast_mul] at h1
    have : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [this, zero_mul] at h1; exact absurd h1 (by decide)
  have hcev : (2 : ℤ) ∣ c := by
    have := (Gamma_mem.mp hg2).2.2.1
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  have hacne : |a| ≠ |c| := by
    intro heq
    rcases abs_eq_abs.mp heq with h | h
    · exact haodd (h ▸ hcev)
    · exact haodd (h ▸ (Dvd.dvd.neg_right hcev))
  have hAmem : sanovA ∈ sanovSubgroup := Subgroup.subset_closure (Or.inl rfl)
  have hBmem : sanovB ∈ sanovSubgroup := Subgroup.subset_closure (Or.inr rfl)
  rcases lt_or_gt_of_ne hacne.symm with hca | hca
  ·
    obtain ⟨ε, _, hlt⟩ := exists_eps_abs_sub_lt hca hc0
    set g' := sanovA ^ (-ε) * g with hg'
    have hg'2 : g' ∈ Gamma 2 := (Gamma 2).mul_mem ((Gamma 2).zpow_mem sanovA_mem_Gamma_two _) hg2
    have ⟨h00, h10⟩ := sanovA_zpow_mul_entries (-ε) g
    have hg'4 : ((g' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
      rw [hg', h00]; push_cast
      obtain ⟨k, hk⟩ := hcev
      have h4 : (4 : ZMod 4) = 0 := by decide
      have hc4 : (c : ZMod 4) = 2 * (k : ZMod 4) := by rw [hk]; push_cast; ring
      calc ((a : ZMod 4) + 2 * (-ε) * c) = (a : ZMod 4) + (-ε * k) * 4 := by
            rw [hc4]; ring
        _ = (a : ZMod 4) := by rw [h4]; ring
        _ = 1 := hg4
    have hmeasure : sanovMeasure g' < sanovMeasure g := by
      unfold sanovMeasure; rw [hg', h00, h10]
      have heq : |a + 2 * -ε * c| = |a - 2 * ε * c| := by ring_nf
      rw [heq]
      refine Int.natAbs_lt_natAbs_of_nonneg_of_lt (by positivity) ?_
      linarith [abs_nonneg c]
    have hg'mem : g' ∈ sanovSubgroup := IH _ hmeasure hg'2 hg'4 rfl
    have heq : g = sanovA ^ ε * g' := by
      rw [hg', ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [heq]; exact sanovSubgroup.mul_mem (sanovSubgroup.zpow_mem hAmem ε) hg'mem
  ·
    have ha0 : a ≠ 0 := fun h => haodd (h ▸ dvd_zero 2)
    obtain ⟨ε, _, hlt⟩ := exists_eps_abs_sub_lt hca ha0
    set g' := sanovB ^ (-ε) * g with hg'
    have hg'2 : g' ∈ Gamma 2 := (Gamma 2).mul_mem ((Gamma 2).zpow_mem sanovB_mem_Gamma_two _) hg2
    have ⟨h00, h10⟩ := sanovB_zpow_mul_entries (-ε) g
    have hg'4 : ((g' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 := by
      rw [hg', h00]; exact hg4
    have hmeasure : sanovMeasure g' < sanovMeasure g := by
      unfold sanovMeasure; rw [hg', h00, h10]
      have heq : |2 * -ε * a + c| = |c - 2 * ε * a| := by
        rw [show 2 * -ε * a + c = c - 2 * ε * a by ring]
      rw [heq]
      refine Int.natAbs_lt_natAbs_of_nonneg_of_lt (by positivity) ?_
      linarith [abs_nonneg a]
    have hg'mem : g' ∈ sanovSubgroup := IH _ hmeasure hg'2 hg'4 rfl
    have heq : g = sanovB ^ ε * g' := by
      rw [hg', ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [heq]; exact sanovSubgroup.mul_mem (sanovSubgroup.zpow_mem hBmem ε) hg'mem

theorem gamma_four_le_gamma_two : Gamma 4 ≤ Gamma 2 := by
  intro g hg
  rw [Gamma_mem] at hg ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hg

  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · first
    | (rw [← map_intCast (ZMod.castHom (by norm_num : (2:ℕ) ∣ 4) (ZMod 2))];
       simp only [h1, h2, h3, h4, map_one, map_zero])

theorem gamma_four_le_sanov : Gamma 4 ≤ sanovSubgroup := by
  intro g hg
  refine mem_sanov_of_coe_00_mod_four (gamma_four_le_gamma_two hg) ?_
  exact (Gamma_mem.mp hg).1

scoped instance sanov_finiteIndex : sanovSubgroup.FiniteIndex :=
  Subgroup.finiteIndex_of_le gamma_four_le_sanov

end ModularCurve.Sanov
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace SanPM
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup ModularCurve.Sanov
open scoped MatrixGroups

def pm (Φ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Φ ∨ -g ∈ Φ}
  one_mem' := Or.inl Φ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Φ.mul_mem ha hb)
    · right
      have h := Φ.mul_mem ha hb
      rwa [mul_neg] at h
    · right
      have h := Φ.mul_mem ha hb
      rwa [neg_mul] at h
    · left
      have h := Φ.mul_mem ha hb
      rwa [neg_mul, mul_neg, neg_neg] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Φ.inv_mem ha)
    · right
      have h := Φ.inv_mem ha
      have hinv : (-a)⁻¹ = -a⁻¹ := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
      rwa [hinv] at h

theorem le_pm (Φ : Subgroup SL(2, ℤ)) : Φ ≤ pm Φ := fun _ hg => Or.inl hg

theorem mem_pm_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : g ∈ pm Φ ↔ g ∈ Φ ∨ -g ∈ Φ := Iff.rfl

theorem neg_one_mem_pm (Φ : Subgroup SL(2, ℤ)) : (-1 : SL(2, ℤ)) ∈ pm Φ :=
  Or.inr (by rw [neg_neg]; exact Φ.one_mem)

theorem neg_mem_pm_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : -g ∈ pm Φ ↔ g ∈ pm Φ := by
  rw [mem_pm_iff, mem_pm_iff, neg_neg]; tauto

theorem neg_one_notMem_sanov : (-1 : SL(2, ℤ)) ∉ sanovSubgroup := by
  intro h
  have h4 := coe_00_mod_four_of_mem_sanov h
  have he : (((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = (3 : ZMod 4) := by
    simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq, Int.cast_neg, Int.cast_one]; decide
  rw [he] at h4; exact absurd h4 (by decide)

theorem neg_one_mem_Gamma_two : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
  rw [Gamma_mem]
  simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, SpecialLinearGroup.coe_one,
    Matrix.one_apply_eq, Int.cast_neg, Int.cast_one]
  decide

theorem coe_00_mod_four_of_mem_Gamma_two {g : SL(2, ℤ)} (hg : g ∈ Gamma 2) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 1 ∨
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4) = 3 := by
  have h2 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 2) = 1 := (Gamma_mem.mp hg).1
  have hcast : (ZMod.castHom (by omega : (2 : ℕ) ∣ 4) (ZMod 2))
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 4)
        = ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod 2) :=
    map_intCast _ _
  rw [h2] at hcast
  have hd : ∀ x : ZMod 4, (ZMod.castHom (by omega : (2 : ℕ) ∣ 4) (ZMod 2)) x = 1 →
      x = 1 ∨ x = 3 := by decide
  exact hd _ hcast

theorem pm_sanov_eq_Gamma_two : pm sanovSubgroup = Gamma 2 := by
  apply le_antisymm
  · rintro g (hg | hg)
    · exact sanovSubgroup_le_Gamma_two hg
    · have h := sanovSubgroup_le_Gamma_two hg
      have : g = -1 * -g := by rw [neg_mul, one_mul, neg_neg]
      rw [this]; exact (Gamma 2).mul_mem neg_one_mem_Gamma_two h
  · intro g hg
    rcases coe_00_mod_four_of_mem_Gamma_two hg with h1 | h3
    · exact Or.inl (mem_sanov_of_coe_00_mod_four hg h1)
    · refine Or.inr (mem_sanov_of_coe_00_mod_four ?_ ?_)
      · have : -g = -1 * g := (neg_one_mul g).symm
        rw [this]; exact (Gamma 2).mul_mem neg_one_mem_Gamma_two hg
      · simp only [SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, h3]; decide

section SanTwo
variable (Φ : Subgroup SL(2, ℤ))

theorem neg_one_notMem_of_le_sanov (hΦ : Φ ≤ sanovSubgroup) : (-1 : SL(2, ℤ)) ∉ Φ :=
  fun h => neg_one_notMem_sanov (hΦ h)

theorem pmSubgroupOf_sanov_eq (hΦ : Φ ≤ sanovSubgroup) :
    (pm Φ).subgroupOf sanovSubgroup = Φ.subgroupOf sanovSubgroup := by
  apply le_antisymm
  · rintro g (hg | hg)
    · exact hg
    · exfalso
      have hgS : (g : SL(2, ℤ)) ∈ sanovSubgroup := g.2
      have hngS : -(g : SL(2, ℤ)) ∈ sanovSubgroup := hΦ hg
      have : (-1 : SL(2, ℤ)) = (-(g : SL(2, ℤ))) * (g : SL(2, ℤ))⁻¹ := by
        rw [neg_mul, mul_inv_cancel]
      exact neg_one_notMem_sanov (this ▸ sanovSubgroup.mul_mem hngS (sanovSubgroup.inv_mem hgS))
  · exact Subgroup.subgroupOf_mono _ (le_pm Φ)

def sanToG2 :
    ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup → ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) :=
  Quotient.map' (Subgroup.inclusion sanovSubgroup_le_Gamma_two) fun a b => by
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    intro h
    simpa using le_pm Φ h

@[scoped simp] theorem sanToG2_mk (g : ↥sanovSubgroup) :
    sanToG2 Φ (QuotientGroup.mk g)
      = QuotientGroup.mk (Subgroup.inclusion sanovSubgroup_le_Gamma_two g) := rfl

theorem sanToG2_injective (hΦ : Φ ≤ sanovSubgroup) : Function.Injective (sanToG2 Φ) := by
  refine Quotient.ind₂' fun a b h => ?_
  rw [sanToG2_mk, sanToG2_mk, QuotientGroup.eq] at h
  rw [QuotientGroup.eq, ← pmSubgroupOf_sanov_eq Φ hΦ]
  exact h

theorem sanToG2_surjective : Function.Surjective (sanToG2 Φ) := by
  refine Quotient.ind' fun c => ?_
  have hc2 : (c : SL(2, ℤ)) ∈ pm sanovSubgroup := by rw [pm_sanov_eq_Gamma_two]; exact c.2
  rcases hc2 with hc | hc
  · exact ⟨QuotientGroup.mk ⟨c, hc⟩, rfl⟩
  · refine ⟨QuotientGroup.mk ⟨-c, hc⟩, ?_⟩
    rw [sanToG2_mk, QuotientGroup.eq]

    have hinv : (-(c : SL(2, ℤ)))⁻¹ = -(c : SL(2, ℤ))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    show (-(c : SL(2, ℤ)))⁻¹ * (c : SL(2, ℤ)) ∈ pm Φ
    rw [hinv, neg_mul, inv_mul_cancel]
    exact neg_one_mem_pm Φ

theorem sanToG2_bijective (hΦ : Φ ≤ sanovSubgroup) : Function.Bijective (sanToG2 Φ) :=
  ⟨sanToG2_injective Φ hΦ, sanToG2_surjective Φ⟩

noncomputable def sanToG2Equiv (hΦ : Φ ≤ sanovSubgroup) :
    ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup ≃ ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) :=
  Equiv.ofBijective _ (sanToG2_bijective Φ hΦ)

theorem sanToG2_smul (s : ↥sanovSubgroup)
    (x : ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup) :
    sanToG2 Φ (s • x)
      = (Subgroup.inclusion sanovSubgroup_le_Gamma_two s) • sanToG2 Φ x := by
  refine x.induction_on fun a => ?_
  show sanToG2 Φ (QuotientGroup.mk (s * a)) = _
  rw [sanToG2_mk, map_mul]; rfl

end SanTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov"

end ModularCurve.PDPairing.SanPM
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace SanThree
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup ModularCurve.Sanov
open scoped MatrixGroups

theorem sanovA_mem : sanovA ∈ sanovSubgroup := Subgroup.subset_closure (Or.inl rfl)
theorem sanovB_mem : sanovB ∈ sanovSubgroup := Subgroup.subset_closure (Or.inr rfl)

noncomputable def sanovEquiv : FreeGroup (Fin 2) ≃* ↥sanovSubgroup :=
  (freeGroupEquivCoprodI (ι := Fin 2)).trans
    ((MonoidHom.ofInjective sanovLift_injective).trans
      (MulEquiv.subgroupCongr sanovSubgroup_eq_range.symm))

theorem coe_sanovEquiv_of (i : Fin 2) :
    ((sanovEquiv (FreeGroup.of i) : ↥sanovSubgroup) : SL(2, ℤ)) = ![sanovA, sanovB] i := by
  have h1 : (freeGroupEquivCoprodI (ι := Fin 2)) (FreeGroup.of i)
      = Monoid.CoprodI.of (i := i) (FreeGroup.of ()) := by
    simp [freeGroupEquivCoprodI_apply]
  show (sanovLift ((freeGroupEquivCoprodI (ι := Fin 2)) (FreeGroup.of i))) = ![sanovA, sanovB] i
  rw [h1]
  simp [sanovLift, sanovFactor]

noncomputable def sanovBasis : FreeGroupBasis (Fin 2) ↥sanovSubgroup :=
  FreeGroupBasis.ofRepr sanovEquiv.symm

@[scoped simp] theorem sanovBasis_apply (i : Fin 2) :
    sanovBasis i = sanovEquiv (FreeGroup.of i) := by
  show sanovEquiv.symm.symm (FreeGroup.of i) = _
  rw [MulEquiv.symm_symm]

theorem coe_sanovBasis (i : Fin 2) :
    ((sanovBasis i : ↥sanovSubgroup) : SL(2, ℤ)) = ![sanovA, sanovB] i := by
  rw [sanovBasis_apply, coe_sanovEquiv_of]

theorem sanovBasis_zero : sanovBasis 0 = ⟨sanovA, sanovA_mem⟩ :=
  Subtype.ext (by rw [coe_sanovBasis]; rfl)

theorem sanovBasis_one : sanovBasis 1 = ⟨sanovB, sanovB_mem⟩ :=
  Subtype.ext (by rw [coe_sanovBasis]; rfl)

theorem closure_sanov_generators_eq_top :
    Subgroup.closure ({⟨sanovA, sanovA_mem⟩, ⟨sanovB, sanovB_mem⟩} : Set ↥sanovSubgroup) = ⊤ := by
  have h := Subgroup.closure_closure_coe_preimage (G := SL(2, ℤ)) (k := {sanovA, sanovB})
  have hset : ({⟨sanovA, sanovA_mem⟩, ⟨sanovB, sanovB_mem⟩} : Set ↥sanovSubgroup) =
      Subtype.val ⁻¹' {sanovA, sanovB} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  rw [hset]; exact h

end ModularCurve.PDPairing.SanThree
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace SanIDX
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup Matrix ModularCurve.Sanov ModularCurve.PDPairing.SanPM
open scoped MatrixGroups ModularGroup

section IndexGammaTwo

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

theorem card_SL2_ZMod_two : Fintype.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by decide

def lowU (r : ℤ) : SL(2, ℤ) := ⟨!![1, 0; r, 1], by simp [Matrix.det_fin_two]⟩

def upE (s : ℤ) : SL(2, ℤ) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem map_lowU_val (x : ZMod 2) :
    ((SLMOD(2) (lowU (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![1, 0; x, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [lowU, Matrix.SpecialLinearGroup.map, ZMod.intCast_cast, ZMod.natCast_val]

theorem map_upE_val (x : ZMod 2) :
    ((SLMOD(2) (upE (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![1, x; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [upE, Matrix.SpecialLinearGroup.map, ZMod.intCast_cast, ZMod.natCast_val]

theorem isUnit_col_of_det_one₂ (g : SpecialLinearGroup (Fin 2) (ZMod 2)) :
    IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0) ∨
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0) := by
  have haux : ∀ a b c d : ZMod 2, a * d - b * c = 1 → IsUnit a ∨ IsUnit c := by decide
  have hdet := g.2; rw [Matrix.det_fin_two] at hdet
  exact haux _ _ _ _ hdet

def liftFn₂ (b c : ZMod 2) : SL(2, ℤ) := lowU ((c).val : ℤ) * upE ((b).val : ℤ)

theorem map_liftFn₂_aux : ∀ a b c d : ZMod 2, a * d - b * c = 1 → IsUnit a →
    ((SLMOD(2) (liftFn₂ b c)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![a, b; c, d] := by
  intro a b c d hdet hu
  simp only [liftFn₂, map_mul, SpecialLinearGroup.coe_mul, map_lowU_val, map_upE_val]
  ext i j; fin_cases i <;> fin_cases j <;>
    · simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_fin_one, Matrix.empty_val']
      revert hdet hu; decide +revert

theorem mem_range_of_isUnit_00₂ (g : SpecialLinearGroup (Fin 2) (ZMod 2))
    (hu : IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0)) :
    g ∈ (SLMOD(2)).range := by
  refine ⟨liftFn₂ ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1)
    ((g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0), ?_⟩
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1
      - (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 1
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 = 1 := by
    have := g.2; rwa [Matrix.det_fin_two] at this
  apply Subtype.ext
  rw [map_liftFn₂_aux _ _ _ _ hdet hu]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem SLMOD_two_surjective : Function.Surjective (SLMOD(2)) := by
  intro g
  rcases isUnit_col_of_det_one₂ g with h0 | h1
  · exact mem_range_of_isUnit_00₂ g h0
  · have hSg : IsUnit (((SLMOD(2) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 2))
        : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0) := by
      have hent : ((SLMOD(2) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 2))
          : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0
          = - (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 := by
        simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, ModularGroup.S]
        simp
      rw [hent]; exact h1.neg
    obtain ⟨y, hy⟩ := mem_range_of_isUnit_00₂ _ hSg
    exact ⟨ModularGroup.S⁻¹ * y, by
      rw [map_mul, hy, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]⟩

theorem index_Gamma_two_eq_six : (Gamma 2).index = 6 := by
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Nat.card_eq_fintype_card]; exact card_SL2_ZMod_two
  rw [show Gamma 2 = (SLMOD(2)).ker from rfl, Subgroup.index_ker,
    (MonoidHom.range_eq_top).mpr SLMOD_two_surjective, ← hcard,
    Nat.card_congr (Subgroup.topEquiv).toEquiv]

end IndexGammaTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"

theorem relIndex_sanov_Gamma_two_eq_two : sanovSubgroup.relIndex (Gamma 2) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨-1, neg_one_mem_Gamma_two⟩, ?_, fun b => ?_⟩
  · intro h
    exact neg_one_notMem_sanov (Subgroup.mem_subgroupOf.mp h)
  · have hbpm : (b : SL(2, ℤ)) ∈ pm sanovSubgroup := by
      rw [pm_sanov_eq_Gamma_two]; exact b.2
    rcases hbpm with hb | hb
    · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
    · refine Or.inl (Subgroup.mem_subgroupOf.mpr ?_)
      show ((b : SL(2, ℤ)) * (-1)) ∈ sanovSubgroup
      rwa [mul_neg, mul_one]

theorem sanov_index_eq_twelve : sanovSubgroup.index = 12 := by
  have h := Subgroup.relIndex_mul_index sanovSubgroup_le_Gamma_two
  rw [relIndex_sanov_Gamma_two_eq_two, index_Gamma_two_eq_six] at h
  omega

end ModularCurve.PDPairing.SanIDX
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"

end
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"

end InlinedSAN123
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"

section InlinedSchreier

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace Schreier
p2m_open "ModularCurve.PDPairing ModularCurve"

variable {G : Type*} [Group G] {V : Type*} [MulAction G V] {ι : Type*}

structure TreeTransversal (a : ι → G) (v₀ : V) where
  t : V → G
  t_smul : ∀ v, t v • v₀ = v
  t_root : t v₀ = 1
  tree : V → ι → Bool
  tree_schreier : ∀ v i, tree v i = true → t (a i • v) = a i * t v
  depth : V → ℕ
  parent : ∀ v, v ≠ v₀ → ∃ u i, depth u < depth v ∧
    ((tree u i = true ∧ a i • u = v) ∨ (tree v i = true ∧ a i • v = u))

namespace TreeTransversal

variable {a : ι → G} {v₀ : V} (T : TreeTransversal a v₀)

theorem t_mem_iff (g : G) (v : V) : (T.t (g • v))⁻¹ * g * T.t v ∈ MulAction.stabilizer G v₀ := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, T.t_smul, inv_smul_eq_iff, T.t_smul]

def x (v : V) (i : ι) : MulAction.stabilizer G v₀ := ⟨(T.t (a i • v))⁻¹ * a i * T.t v, T.t_mem_iff (a i) v⟩

@[scoped simp] theorem coe_x (v : V) (i : ι) : (T.x v i : G) = (T.t (a i • v))⁻¹ * a i * T.t v := rfl

theorem x_eq_one_of_tree (v : V) (i : ι) (h : T.tree v i = true) : T.x v i = 1 := by
  apply Subtype.ext
  rw [coe_x, T.tree_schreier v i h, OneMemClass.coe_one]
  group

def schreierClosure : Subgroup (MulAction.stabilizer G v₀) :=
  Subgroup.closure (Set.range (fun p : V × ι => T.x p.1 p.2))

theorem x_mem_schreierClosure (v : V) (i : ι) : T.x v i ∈ T.schreierClosure :=
  Subgroup.subset_closure ⟨(v, i), rfl⟩

theorem schreierClosure_eq_top (hG : Subgroup.closure (Set.range a) = ⊤) : T.schreierClosure = ⊤ := by

  have key : ∀ g : G, ∀ v : V, (T.t (g • v))⁻¹ * g * T.t v ∈ (T.schreierClosure).map (MulAction.stabilizer G v₀).subtype := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range a) := by rw [hG]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro v
      exact ⟨T.x v i, T.x_mem_schreierClosure v i, rfl⟩
    | one =>
      intro v
      rw [mul_one, one_smul, inv_mul_cancel]
      exact one_mem _
    | mul y z _ _ ihy ihz =>
      intro v
      have h := Subgroup.mul_mem _ (ihy (z • v)) (ihz v)
      rw [mul_smul]
      convert h using 1
      group
    | inv y _ ihy =>
      intro v
      have h := Subgroup.inv_mem _ (ihy (y⁻¹ • v))
      rw [smul_inv_smul] at h
      convert h using 1
      group
  rw [eq_top_iff]
  intro s _
  obtain ⟨s', hs', hs'eq⟩ := key (s : G) v₀
  have hfix : (s : G) • v₀ = v₀ := MulAction.mem_stabilizer_iff.mp s.2
  rw [hfix, T.t_root, inv_one, one_mul, mul_one] at hs'eq
  have : s' = s := Subtype.ext hs'eq
  rw [← this]
  exact hs'

def walkList (v : V) (i : ι) (k : ℕ) : List (MulAction.stabilizer G v₀) :=
  ((List.range k).map (fun j => T.x ((a i) ^ j • v) i)).reverse

theorem walkList_succ (v : V) (i : ι) (k : ℕ) :
    T.walkList v i (k + 1) = T.x ((a i) ^ k • v) i :: T.walkList v i k := by
  simp [walkList, List.range_succ]

theorem coe_prod_walkList (v : V) (i : ι) (k : ℕ) :
    ((T.walkList v i k).prod : G) = (T.t ((a i) ^ k • v))⁻¹ * (a i) ^ k * T.t v := by
  induction k with
  | zero => simp [walkList]
  | succ k ih =>
    rw [walkList_succ, List.prod_cons, Subgroup.coe_mul, ih, coe_x, ← mul_smul, ← pow_succ']
    group

theorem coe_prod_walkList_of_closed (v : V) (i : ι) (k : ℕ) (hk : (a i) ^ k • v = v) :
    ((T.walkList v i k).prod : G) = (T.t v)⁻¹ * (a i) ^ k * T.t v := by
  rw [coe_prod_walkList, hk]

theorem char_prod_walkList {R : Type*} [AddCommMonoid R] (ψ : Additive (MulAction.stabilizer G v₀) →+ R)
    (v : V) (i : ι) (k : ℕ) :
    ψ (Additive.ofMul (T.walkList v i k).prod) = ∑ j ∈ Finset.range k, ψ (Additive.ofMul (T.x ((a i) ^ j • v) i)) := by
  induction k with
  | zero => simp [walkList]
  | succ k ih => rw [walkList_succ, List.prod_cons, ofMul_mul, map_add, ih, Finset.sum_range_succ, add_comm]

section Character

variable {R : Type*} [AddCommGroup R]

abbrev Coef (V R : Type*) [AddCommGroup R] : Type _ := V → Multiplicative R

theorem mulAutArrow_apply_apply' (g : G) (F : Coef V R) (v : V) :
    (mulAutArrow (G := G) (A := V) (M := Multiplicative R) g) F v = F (g⁻¹ • v) := rfl

variable (b : FreeGroupBasis ι G) (T : TreeTransversal (fun i => b i) v₀) (c : V → ι → R)

def letterCoef (i : ι) : Coef V R := fun w => Multiplicative.ofAdd (c ((b i)⁻¹ • w) i)

noncomputable def liftSD : G →* Coef V R ⋊[mulAutArrow] G :=
  b.lift (fun i => ⟨letterCoef b c i, b i⟩)

theorem liftSD_basis (i : ι) : liftSD b c (b i) = ⟨letterCoef b c i, b i⟩ := by
  have h := congrFun (b.lift.symm_apply_apply (fun i => (⟨letterCoef b c i, b i⟩ : Coef V R ⋊[mulAutArrow] G))) i
  exact h

theorem liftSD_right (g : G) : (liftSD b c g).right = g := by
  have hcomp : (SemidirectProduct.rightHom.comp (liftSD b c) : G →* G) = MonoidHom.id G := by
    apply b.ext_hom
    intro i
    show SemidirectProduct.rightHom (liftSD b c (b i)) = b i
    rw [liftSD_basis]
    rfl
  exact DFunLike.congr_fun hcomp g

noncomputable def F (g : G) : Coef V R := (liftSD b c g).left

theorem F_mul (g h : G) (u : V) : F b c (g * h) u = F b c g u * F b c h (g⁻¹ • u) := by
  unfold F
  rw [map_mul, SemidirectProduct.mul_left, liftSD_right]
  rfl

theorem F_one (u : V) : F b c 1 u = 1 := by
  unfold F
  rw [map_one, SemidirectProduct.one_left]
  rfl

theorem F_inv (g : G) (u : V) : F b c g⁻¹ u = (F b c g (g • u))⁻¹ := by
  have h := F_mul b c g⁻¹ g (u)
  rw [inv_mul_cancel, F_one, inv_inv] at h

  exact eq_inv_of_mul_eq_one_left h.symm

theorem F_basis (i : ι) (w : V) : F b c (b i) w = Multiplicative.ofAdd (c ((b i)⁻¹ • w) i) := by
  unfold F
  rw [liftSD_basis]
  rfl

noncomputable def pot (v : V) : R := Multiplicative.toAdd (F b c (T.t v) v)

theorem F_x (v : V) (i : ι) :
    Multiplicative.toAdd (F b c (T.x v i : G) v₀) = c v i + pot b T c v - pot b T c (b i • v) := by
  rw [coe_x, F_mul, F_mul, F_inv, F_basis]

  rw [show ((T.t (b i • v))⁻¹ * b i)⁻¹ • v₀ = v from by
      rw [mul_inv_rev, inv_inv, mul_smul, T.t_smul, inv_smul_smul],
    T.t_smul, inv_inv, T.t_smul, inv_smul_smul]
  simp only [pot, toAdd_mul, toAdd_inv, toAdd_ofAdd]
  abel

theorem pot_root : pot b T c v₀ = 0 := by
  simp [pot, T.t_root, F_one]

theorem pot_tree (hc : ∀ v i, T.tree v i = true → c v i = 0) (v : V) (i : ι) (h : T.tree v i = true) :
    pot b T c (b i • v) = pot b T c v := by
  have hx := F_x b T c v i
  rw [T.x_eq_one_of_tree v i h, OneMemClass.coe_one, F_one, toAdd_one, hc v i h, zero_add] at hx

  exact (sub_eq_zero.mp hx.symm).symm

theorem pot_eq_zero (hc : ∀ v i, T.tree v i = true → c v i = 0) (v : V) : pot b T c v = 0 := by
  induction hn : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = v₀
    · rw [hv]; exact pot_root b T c
    · obtain ⟨u, i, hdu, h⟩ := T.parent v hv
      rcases h with ⟨ht, huv⟩ | ⟨ht, hvu⟩
      · rw [← huv, pot_tree b T c hc u i ht]
        exact ih (T.depth u) (hn ▸ hdu) u rfl
      · rw [← pot_tree b T c hc v i ht, hvu]
        exact ih (T.depth u) (hn ▸ hdu) u rfl

noncomputable def character : Additive (MulAction.stabilizer G v₀) →+ R where
  toFun s := Multiplicative.toAdd (F b c ((Additive.toMul s : MulAction.stabilizer G v₀) : G) v₀)
  map_zero' := by
    show Multiplicative.toAdd (F b c ((1 : MulAction.stabilizer G v₀) : G) v₀) = 0
    rw [OneMemClass.coe_one, F_one, toAdd_one]
  map_add' s s' := by
    show Multiplicative.toAdd (F b c ((Additive.toMul s * Additive.toMul s' : MulAction.stabilizer G v₀) : G) v₀) =
      Multiplicative.toAdd (F b c ((Additive.toMul s : MulAction.stabilizer G v₀) : G) v₀) +
        Multiplicative.toAdd (F b c ((Additive.toMul s' : MulAction.stabilizer G v₀) : G) v₀)
    rw [Subgroup.coe_mul, F_mul]
    have hfix : ((Additive.toMul s : MulAction.stabilizer G v₀) : G)⁻¹ • v₀ = v₀ := by
      rw [inv_smul_eq_iff]
      exact (MulAction.mem_stabilizer_iff.mp (Additive.toMul s).2).symm
    rw [hfix, toAdd_mul]

theorem character_apply (s : MulAction.stabilizer G v₀) :
    character b c (Additive.ofMul s) = Multiplicative.toAdd (F b c (s : G) v₀) := rfl

theorem character_x (hc : ∀ v i, T.tree v i = true → c v i = 0) (v : V) (i : ι) :
    character b c (Additive.ofMul (T.x v i)) = c v i := by
  rw [character_apply, F_x b T c, pot_eq_zero b T c hc, pot_eq_zero b T c hc, add_zero, sub_zero]

theorem exists_character (hc : ∀ v i, T.tree v i = true → c v i = 0) :
    ∃ ψ : Additive (MulAction.stabilizer G v₀) →+ R, ∀ v i, ψ (Additive.ofMul (T.x v i)) = c v i :=
  ⟨character b c, character_x b T c hc⟩

end Character
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree"

end TreeTransversal
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal"

section BFS

variable (a : ι → G) (v₀ : V)

def act (p : ι × Bool) : G := if p.2 then a p.1 else (a p.1)⁻¹

def wprod (l : List (ι × Bool)) : G := (l.map (act a)).prod

theorem wprod_cons (p : ι × Bool) (l : List (ι × Bool)) : wprod a (p :: l) = act a p * wprod a l := by
  simp [wprod]

def ReachN (n : ℕ) (v : V) : Prop := ∃ l : List (ι × Bool), l.length = n ∧ wprod a l • v₀ = v

theorem reachN_zero_iff (v : V) : ReachN a v₀ 0 v ↔ v = v₀ := by
  constructor
  · rintro ⟨l, hl, hv⟩
    rw [List.length_eq_zero_iff] at hl
    subst hl
    simpa [wprod] using hv.symm
  · rintro rfl
    exact ⟨[], rfl, by simp [wprod]⟩

theorem reach_all (hG : Subgroup.closure (Set.range a) = ⊤) (htrans : ∀ v : V, ∃ g : G, g • v₀ = v) (v : V) :
    ∃ n, ReachN a v₀ n v := by

  have key : ∀ g : G, ∀ w : V, (∃ n, ReachN a v₀ n w) ↔ (∃ n, ReachN a v₀ n (g • w)) := by
    intro g
    have hg : g ∈ Subgroup.closure (Set.range a) := by rw [hG]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro w
      constructor
      · rintro ⟨n, l, hl, hw⟩
        exact ⟨n + 1, (i, true) :: l, by simp [hl], by rw [wprod_cons, mul_smul, hw]; rfl⟩
      · rintro ⟨n, l, hl, hw⟩
        refine ⟨n + 1, (i, false) :: l, by simp [hl], ?_⟩
        rw [wprod_cons, mul_smul, hw]
        show (a i)⁻¹ • a i • w = w
        rw [inv_smul_smul]
    | one => intro w; rw [one_smul]
    | mul y z _ _ ihy ihz => intro w; rw [mul_smul, ihz w, ihy (z • w)]
    | inv y _ ihy => intro w; rw [ihy (y⁻¹ • w), smul_inv_smul]
  obtain ⟨g, hg⟩ := htrans v
  rw [← hg, ← key g v₀]
  exact ⟨0, (reachN_zero_iff a v₀ v₀).mpr rfl⟩

variable (hG : Subgroup.closure (Set.range a) = ⊤) (htrans : ∀ v : V, ∃ g : G, g • v₀ = v)

open Classical in

private noncomputable def _root_.ModularCurve.PDPairing.Schreier.depth (v : V) : ℕ := Nat.find (reach_all a v₀ hG htrans v)

p2m_export "ModularCurve.PDPairing.Schreier" "depth"
theorem depth_spec (v : V) : ReachN a v₀ (depth a v₀ hG htrans v) v := by
  classical exact Nat.find_spec (reach_all a v₀ hG htrans v)

theorem depth_le {v : V} {n : ℕ} (h : ReachN a v₀ n v) : depth a v₀ hG htrans v ≤ n := by
  classical exact Nat.find_min' _ h

theorem depth_root : depth a v₀ hG htrans v₀ = 0 :=
  Nat.le_zero.mp (depth_le a v₀ hG htrans ((reachN_zero_iff a v₀ v₀).mpr rfl))

theorem exists_parentStep (v : V) (hv : v ≠ v₀) :
    ∃ q : V × ι × Bool, depth a v₀ hG htrans q.1 < depth a v₀ hG htrans v ∧ act a (q.2.1, q.2.2) • q.1 = v := by
  obtain ⟨l, hl, hlv⟩ := depth_spec a v₀ hG htrans v
  match l, hl, hlv with
  | [], hl, hlv =>
    exfalso
    apply hv
    simpa [wprod] using hlv.symm
  | p :: l', hl, hlv =>
    refine ⟨(wprod a l' • v₀, p.1, p.2), ?_, ?_⟩
    · have hle : depth a v₀ hG htrans (wprod a l' • v₀) ≤ l'.length := depth_le a v₀ hG htrans ⟨l', rfl, rfl⟩
      have : l'.length < depth a v₀ hG htrans v := by rw [← hl]; simp
      exact lt_of_le_of_lt hle this
    · rw [← hlv, wprod_cons, mul_smul]

noncomputable def parentStep (v : V) (hv : v ≠ v₀) :
    {q : V × ι × Bool // depth a v₀ hG htrans q.1 < depth a v₀ hG htrans v ∧ act a (q.2.1, q.2.2) • q.1 = v} :=
  Classical.indefiniteDescription _ (exists_parentStep a v₀ hG htrans v hv)

open Classical in

noncomputable def tBFS (v : V) : G :=
  if hv : v = v₀ then 1
  else
    act a ((parentStep a v₀ hG htrans v hv).1.2.1, (parentStep a v₀ hG htrans v hv).1.2.2) *
      tBFS (parentStep a v₀ hG htrans v hv).1.1
termination_by depth a v₀ hG htrans v
decreasing_by exact (parentStep a v₀ hG htrans v hv).2.1

theorem tBFS_root : tBFS a v₀ hG htrans v₀ = 1 := by
  rw [tBFS, dif_pos rfl]

theorem tBFS_of_ne (v : V) (hv : v ≠ v₀) :
    tBFS a v₀ hG htrans v = act a ((parentStep a v₀ hG htrans v hv).1.2.1, (parentStep a v₀ hG htrans v hv).1.2.2) *
      tBFS a v₀ hG htrans (parentStep a v₀ hG htrans v hv).1.1 := by
  rw [tBFS, dif_neg hv]

theorem tBFS_smul (v : V) : tBFS a v₀ hG htrans v • v₀ = v := by
  induction hn : depth a v₀ hG htrans v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    by_cases hv : v = v₀
    · subst hv; rw [tBFS_root, one_smul]
    · rw [tBFS_of_ne a v₀ hG htrans v hv, mul_smul,
        ih _ (hn ▸ (parentStep a v₀ hG htrans v hv).2.1) _ rfl]
      exact (parentStep a v₀ hG htrans v hv).2.2

open Classical in

noncomputable def treeBFS (v' : V) (i' : ι) : Bool :=
  decide (∃ (v : V) (hv : v ≠ v₀),
    ((parentStep a v₀ hG htrans v hv).1.2.2 = true ∧ (parentStep a v₀ hG htrans v hv).1.1 = v' ∧
        (parentStep a v₀ hG htrans v hv).1.2.1 = i') ∨
    ((parentStep a v₀ hG htrans v hv).1.2.2 = false ∧ v = v' ∧ (parentStep a v₀ hG htrans v hv).1.2.1 = i'))

theorem treeBFS_iff (v' : V) (i' : ι) : treeBFS a v₀ hG htrans v' i' = true ↔ ∃ (v : V) (hv : v ≠ v₀),
    ((parentStep a v₀ hG htrans v hv).1.2.2 = true ∧ (parentStep a v₀ hG htrans v hv).1.1 = v' ∧
        (parentStep a v₀ hG htrans v hv).1.2.1 = i') ∨
    ((parentStep a v₀ hG htrans v hv).1.2.2 = false ∧ v = v' ∧ (parentStep a v₀ hG htrans v hv).1.2.1 = i') := by
  classical
  unfold treeBFS
  rw [decide_eq_true_iff]

theorem child_eqs (v : V) (hv : v ≠ v₀) :
    ((parentStep a v₀ hG htrans v hv).1.2.2 = true →
        tBFS a v₀ hG htrans v =
            a (parentStep a v₀ hG htrans v hv).1.2.1 * tBFS a v₀ hG htrans (parentStep a v₀ hG htrans v hv).1.1 ∧
          a (parentStep a v₀ hG htrans v hv).1.2.1 • (parentStep a v₀ hG htrans v hv).1.1 = v) ∧
    ((parentStep a v₀ hG htrans v hv).1.2.2 = false →
        tBFS a v₀ hG htrans v =
            (a (parentStep a v₀ hG htrans v hv).1.2.1)⁻¹ * tBFS a v₀ hG htrans (parentStep a v₀ hG htrans v hv).1.1 ∧
          a (parentStep a v₀ hG htrans v hv).1.2.1 • v = (parentStep a v₀ hG htrans v hv).1.1) := by
  have ht := tBFS_of_ne a v₀ hG htrans v hv
  have hact := (parentStep a v₀ hG htrans v hv).2.2
  simp only [act] at ht hact
  constructor
  · intro hd
    rw [if_pos hd] at ht hact
    exact ⟨ht, hact⟩
  · intro hd
    have hd' : ¬ ((parentStep a v₀ hG htrans v hv).1.2.2 = true) := by rw [hd]; exact Bool.false_ne_true
    rw [if_neg hd'] at ht hact
    exact ⟨ht, (inv_smul_eq_iff.mp hact).symm⟩

theorem treeBFS_schreier (v' : V) (i' : ι) (h : treeBFS a v₀ hG htrans v' i' = true) :
    tBFS a v₀ hG htrans (a i' • v') = a i' * tBFS a v₀ hG htrans v' := by
  rw [treeBFS_iff] at h
  obtain ⟨v, hv, hcase⟩ := h
  have hce := child_eqs a v₀ hG htrans v hv
  rcases hcase with ⟨hd, hu, hi⟩ | ⟨hd, hvv, hi⟩
  · obtain ⟨ht, hact⟩ := hce.1 hd
    rw [hu, hi] at ht hact
    rw [hact, ht]
  · obtain ⟨ht, hact⟩ := hce.2 hd
    rw [hi] at ht hact
    subst hvv
    rw [hact, ht, mul_inv_cancel_left]

noncomputable def bfsTransversal : TreeTransversal a v₀ where
  t := tBFS a v₀ hG htrans
  t_smul := tBFS_smul a v₀ hG htrans
  t_root := tBFS_root a v₀ hG htrans
  tree := treeBFS a v₀ hG htrans
  tree_schreier := treeBFS_schreier a v₀ hG htrans
  depth := depth a v₀ hG htrans
  parent v hv := by
    refine ⟨(parentStep a v₀ hG htrans v hv).1.1, (parentStep a v₀ hG htrans v hv).1.2.1,
      (parentStep a v₀ hG htrans v hv).2.1, ?_⟩
    have hce := child_eqs a v₀ hG htrans v hv
    cases hd : (parentStep a v₀ hG htrans v hv).1.2.2
    · right
      refine ⟨(treeBFS_iff a v₀ hG htrans _ _).mpr ⟨v, hv, Or.inr ⟨hd, rfl, rfl⟩⟩, (hce.2 hd).2⟩
    · left
      refine ⟨(treeBFS_iff a v₀ hG htrans _ _).mpr ⟨v, hv, Or.inl ⟨hd, rfl, rfl⟩⟩, (hce.1 hd).2⟩

end BFS
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal"

namespace TreeTransversal

variable {a : ι → G} {v₀ : V} (T : TreeTransversal a v₀)

noncomputable def sx (w : V) (p : ι × Bool) : MulAction.stabilizer G v₀ :=
  if p.2 then T.x w p.1 else (T.x ((a p.1)⁻¹ • w) p.1)⁻¹

theorem sx_true (w : V) (i : ι) : T.sx w (i, true) = T.x w i := by simp [sx]

theorem sx_false (w : V) (i : ι) : T.sx w (i, false) = (T.x ((a i)⁻¹ • w) i)⁻¹ := by simp [sx]

theorem coe_sx (w : V) (p : ι × Bool) : (T.sx w p : G) = (T.t (act a p • w))⁻¹ * act a p * T.t w := by
  obtain ⟨i, d⟩ := p
  cases d
  · rw [sx_false, Subgroup.coe_inv, coe_x, smul_inv_smul]
    simp only [act, Bool.false_eq_true, ↓reduceIte]
    group
  · rw [sx_true, coe_x]
    simp [act]

noncomputable def wordWalk (v : V) : List (ι × Bool) → MulAction.stabilizer G v₀
  | [] => 1
  | p :: l => T.sx (wprod a l • v) p * wordWalk v l

theorem wordWalk_nil (v : V) : T.wordWalk v [] = 1 := rfl

theorem wordWalk_cons (v : V) (p : ι × Bool) (l : List (ι × Bool)) :
    T.wordWalk v (p :: l) = T.sx (wprod a l • v) p * T.wordWalk v l := rfl

theorem coe_wordWalk (v : V) (l : List (ι × Bool)) :
    (T.wordWalk v l : G) = (T.t (wprod a l • v))⁻¹ * wprod a l * T.t v := by
  induction l with
  | nil => simp [wordWalk, wprod]
  | cons p l ih => rw [wordWalk_cons, Subgroup.coe_mul, ih, coe_sx, wprod_cons, mul_smul]; group

theorem coe_wordWalk_of_closed (v : V) (l : List (ι × Bool)) (h : wprod a l • v = v) :
    (T.wordWalk v l : G) = (T.t v)⁻¹ * wprod a l * T.t v := by
  rw [coe_wordWalk, h]

theorem char_wordWalk_cons {R : Type*} [AddCommGroup R] (ψ : Additive (MulAction.stabilizer G v₀) →+ R)
    (v : V) (p : ι × Bool) (l : List (ι × Bool)) :
    ψ (Additive.ofMul (T.wordWalk v (p :: l))) = ψ (Additive.ofMul (T.sx (wprod a l • v) p)) + ψ (Additive.ofMul (T.wordWalk v l)) := by
  rw [wordWalk_cons, ofMul_mul, map_add]

theorem char_sx {R : Type*} [AddCommGroup R] (ψ : Additive (MulAction.stabilizer G v₀) →+ R) (w : V) (p : ι × Bool) :
    ψ (Additive.ofMul (T.sx w p)) =
      if p.2 then ψ (Additive.ofMul (T.x w p.1)) else -ψ (Additive.ofMul (T.x ((a p.1)⁻¹ • w) p.1)) := by
  obtain ⟨i, d⟩ := p
  cases d
  · rw [sx_false, ofMul_inv, map_neg]; simp
  · rw [sx_true]; simp

end TreeTransversal
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal"

end ModularCurve.PDPairing.Schreier
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal"

end InlinedSchreier
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

section Aux2CuspTower

set_option autoImplicit false

open MulAction Function

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace CuspTower
p2m_open "ModularCurve.PDPairing ModularCurve"

variable {G : Type*} [Group G] (g : G) (K' K : Subgroup G)

abbrev ACusp : Type _ := Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ K))

def acuspGen (q : ACusp g K) : K :=
  ⟨q.out.out⁻¹ * g ^ minimalPeriod (g • ·) q.out * q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem K g q.out⟩

abbrev InnerOrbit (_hle : K' ≤ K) (q : ACusp g K) : Type _ :=
  Quotient (orbitRel (Subgroup.zpowers (acuspGen g K q)) (K ⧸ K'.subgroupOf K))

variable {K' K}

def towerLift (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) : G :=
  (q.out.out : G) * ((o.out.out : K) : G)

theorem towerLift_mk_K (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    QuotientGroup.mk (s := K) (towerLift g hle q o) = q.out := by
  rw [towerLift, ← QuotientGroup.out_eq' q.out, QuotientGroup.eq]
  simp [(o.out.out : K).2]

def towerFn (hle : K' ≤ K) (p : Σ q : ACusp g K, InnerOrbit g K' K hle q) : ACusp g K' :=
  Quotient.mk _ (QuotientGroup.mk (s := K') (towerLift g hle p.1 p.2))

section Helpers

variable (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
variable (q : ACusp g K) (o : InnerOrbit g K' K hle q)

local notation "m" => minimalPeriod (g • ·) q.out
local notation "p₀" => towerLift g hle q o

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem zpow_smul_towerLift_eq_iff (n : ℤ) :
    g ^ n • QuotientGroup.mk (s := K') p₀ = QuotientGroup.mk (s := K') p₀ ↔
      p₀⁻¹ * g ^ n * p₀ ∈ K' := by
  rw [show g ^ n • QuotientGroup.mk (s := K') p₀ = QuotientGroup.mk (s := K') (g ^ n * p₀) from rfl,
    eq_comm, QuotientGroup.eq]
  constructor
  · intro h; have := h; rwa [show p₀⁻¹ * (g ^ n * p₀) = p₀⁻¹ * g ^ n * p₀ by group] at this
  · intro h; rwa [show p₀⁻¹ * g ^ n * p₀ = p₀⁻¹ * (g ^ n * p₀) by group] at h

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem towerLift_conj_zpow (n : ℤ) :
    p₀⁻¹ * g ^ n * p₀ =
      ((o.out.out : K) : G)⁻¹ * (q.out.out⁻¹ * g ^ n * q.out.out) * ((o.out.out : K) : G) := by
  unfold towerLift; group

omit [K.FiniteIndex] in

theorem conj_pow_mem_K_iff (n : ℕ) :
    q.out.out⁻¹ * g ^ n * q.out.out ∈ K ↔ m ∣ n := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul,
    MulAction.Quotient.mk_smul_out, eq_comm, pow_smul_eq_iff_minimalPeriod_dvd]

omit [K.FiniteIndex] in

theorem conj_pow_eq_acuspGen_pow (j : ℕ) :
    q.out.out⁻¹ * g ^ (m * j) * q.out.out = ((acuspGen g K q : K) : G) ^ j := by
  rw [pow_mul]
  induction j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    simp only [acuspGen]; group

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem acuspGen_pow_smul_eq_iff (j : ℕ) :
    (acuspGen g K q) ^ j • o.out = o.out ↔
      ((o.out.out : K) : G)⁻¹ * ((acuspGen g K q : K) : G) ^ j * ((o.out.out : K) : G) ∈ K' := by
  have h : (o.out.out : K)⁻¹ * (acuspGen g K q) ^ j * o.out.out ∈ K'.subgroupOf K ↔
      (acuspGen g K q) ^ j • o.out = o.out := by
    rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul,
      MulAction.Quotient.mk_smul_out, eq_comm]
  rw [← h, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, InvMemClass.coe_inv]

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem pow_smul_towerLift_eq_iff (n : ℕ) :
    g ^ n • QuotientGroup.mk (s := K') p₀ = QuotientGroup.mk (s := K') p₀ ↔
      ∃ j, n = m * j ∧ (acuspGen g K q) ^ j • o.out = o.out := by
  rw [show (g : G) ^ n = g ^ (n : ℤ) from (zpow_natCast g n).symm,
    zpow_smul_towerLift_eq_iff, towerLift_conj_zpow, zpow_natCast]
  constructor
  · intro h
    have hK : q.out.out⁻¹ * g ^ n * q.out.out ∈ K := by
      have hK' : ((o.out.out : K) : G)⁻¹ * (q.out.out⁻¹ * g ^ n * q.out.out) *
          ((o.out.out : K) : G) ∈ K := hle h
      have := K.mul_mem (K.mul_mem (o.out.out : K).2 hK') (K.inv_mem (o.out.out : K).2)
      simpa [mul_assoc] using this
    obtain ⟨j, hj⟩ := (conj_pow_mem_K_iff g q n).mp hK
    refine ⟨j, hj, ?_⟩
    rw [acuspGen_pow_smul_eq_iff, ← conj_pow_eq_acuspGen_pow g q j, ← hj]
    exact h
  · rintro ⟨j, hj, hfix⟩
    subst hj
    rw [conj_pow_eq_acuspGen_pow g q j]
    exact (acuspGen_pow_smul_eq_iff g hle q o j).mp hfix

omit [K.FiniteIndex] in

theorem conj_zpow_mem_K_iff (n : ℤ) :
    q.out.out⁻¹ * g ^ n * q.out.out ∈ K ↔ (m : ℤ) ∣ n := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul,
    MulAction.Quotient.mk_smul_out, eq_comm, zpow_smul_eq_iff_minimalPeriod_dvd]

omit [K.FiniteIndex] in

theorem conj_zpow_eq_acuspGen_zpow (j : ℤ) :
    q.out.out⁻¹ * g ^ ((m : ℤ) * j) * q.out.out = ((acuspGen g K q : K) : G) ^ j := by
  have h1 : ((acuspGen g K q : K) : G) = q.out.out⁻¹ * g ^ (m : ℤ) * q.out.out := by
    simp [acuspGen, zpow_natCast]
  rw [h1, zpow_mul]
  induction j using Int.induction_on with
  | zero => simp
  | succ k ih => rw [zpow_add_one, zpow_add_one, ← ih]; group
  | pred k ih => rw [zpow_sub_one, zpow_sub_one, ← ih]; group

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem minimalPeriod_zpow_smul (n : ℤ) (x : G ⧸ K') :
    minimalPeriod (g • ·) (g ^ n • x) = minimalPeriod (g • ·) x := by
  have hcomm : ∀ (a : ℕ), g ^ a • g ^ n • x = g ^ n • g ^ a • x := fun a => by
    rw [← mul_smul, ← mul_smul, ← zpow_natCast g a, ← zpow_add, ← zpow_add, add_comm]
  apply Nat.dvd_antisymm <;> rw [← pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [hcomm, (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl]
  · have h := (pow_smul_eq_iff_minimalPeriod_dvd (a := g)
      (b := g ^ n • x) (n := minimalPeriod (g • ·) (g ^ n • x))).mpr dvd_rfl
    rw [hcomm] at h
    exact smul_left_cancel _ h

omit [K'.FiniteIndex] [K.FiniteIndex] in

theorem zpow_smul_mk_eq_mk_iff (n : ℤ) (a b : G) :
    g ^ n • QuotientGroup.mk (s := K') a = QuotientGroup.mk (s := K') b ↔
      b⁻¹ * g ^ n * a ∈ K' := by
  rw [show g ^ n • QuotientGroup.mk (s := K') a = QuotientGroup.mk (s := K') (g ^ n * a) from rfl,
    eq_comm, QuotientGroup.eq, mul_assoc]

end Helpers
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

theorem towerFn_surjective (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    Function.Surjective (towerFn g hle) := by
  intro q'
  set x := q'.out.out with hx

  set q : ACusp g K := Quotient.mk _ (QuotientGroup.mk (s := K) x) with hq

  have hqout : (Quotient.mk _ q.out : ACusp g K) = Quotient.mk _ (QuotientGroup.mk (s := K) x) := by
    rw [Quotient.out_eq]
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at hqout
  obtain ⟨h, hh⟩ := hqout
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hn' : g ^ n • QuotientGroup.mk (s := K) x = q.out := hng ▸ hh
  clear hng hh h
  have hκmem : q.out.out⁻¹ * g ^ n * x ∈ K :=
    (zpow_smul_mk_eq_mk_iff (K' := K) g n x q.out.out).mp (by rw [hn', QuotientGroup.out_eq'])

  set κ : K := ⟨q.out.out⁻¹ * g ^ n * x, hκmem⟩ with hκ
  set o : InnerOrbit g K' K hle q :=
    Quotient.mk _ (QuotientGroup.mk (s := K'.subgroupOf K) κ) with ho
  refine ⟨⟨q, o⟩, ?_⟩

  have hoout : (Quotient.mk _ o.out : InnerOrbit g K' K hle q)
      = Quotient.mk _ (QuotientGroup.mk (s := K'.subgroupOf K) κ) := by
    rw [Quotient.out_eq]
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at hoout
  obtain ⟨h, hh⟩ := hoout
  obtain ⟨j, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hj' : (acuspGen g K q) ^ j • QuotientGroup.mk (s := K'.subgroupOf K) κ = o.out := hng ▸ hh
  clear hng hh h
  have hk'mem : (o.out.out : K)⁻¹ * (acuspGen g K q) ^ j * κ ∈ K'.subgroupOf K := by
    rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq']
    exact hj'.symm

  show Quotient.mk _ (QuotientGroup.mk (s := K') (towerLift g hle q o)) = q'
  rw [← Quotient.out_eq q', Quotient.eq, orbitRel_apply, mem_orbit_iff]
  set mj := (minimalPeriod (g • ·) q.out : ℤ) * j with hmj
  refine ⟨⟨g ^ (mj + n), mj + n, rfl⟩, ?_⟩
  show g ^ (mj + n) • q'.out = QuotientGroup.mk (s := K') (towerLift g hle q o)
  rw [← QuotientGroup.out_eq' q'.out, ← hx, zpow_smul_mk_eq_mk_iff]

  have hkey : q.out.out⁻¹ * g ^ (mj + n) * x
      = ((acuspGen g K q : K) : G) ^ j * (κ : G) := by
    rw [hκ, hmj, ← conj_zpow_eq_acuspGen_zpow g q j]; push_cast; group
  have heq : (towerLift g hle q o)⁻¹ * g ^ (mj + n) * x
      = ((o.out.out : K) : G)⁻¹ * (((acuspGen g K q : K) : G) ^ j * (κ : G)) := by
    unfold towerLift; rw [← hkey]; group
  rw [heq]
  have := Subgroup.mem_subgroupOf.mp hk'mem
  simpa [mul_assoc] using this

theorem towerFn_injective (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    Function.Injective (towerFn g hle) := by
  rintro ⟨q₁, o₁⟩ ⟨q₂, o₂⟩ heq
  rw [towerFn, towerFn, Quotient.eq, orbitRel_apply, mem_orbit_iff] at heq
  obtain ⟨h, hn⟩ := heq
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hn' : g ^ n • QuotientGroup.mk (s := K') (towerLift g hle q₂ o₂)
      = QuotientGroup.mk (s := K') (towerLift g hle q₁ o₁) := hng ▸ hn
  clear hng hn h
  have hmemK' := (zpow_smul_mk_eq_mk_iff g n (towerLift g hle q₂ o₂) (towerLift g hle q₁ o₁)).mp hn'

  set α := q₁.out.out⁻¹ * g ^ n * q₂.out.out with hα
  have hmemK'2 : ((o₁.out.out : K) : G)⁻¹ * α * ((o₂.out.out : K) : G) ∈ K' := by
    have heq : (towerLift g hle q₁ o₁)⁻¹ * g ^ n * towerLift g hle q₂ o₂
        = ((o₁.out.out : K) : G)⁻¹ * α * ((o₂.out.out : K) : G) := by
      unfold towerLift; rw [hα]; group
    rwa [heq] at hmemK'
  clear hmemK'

  have hαK : α ∈ K := by
    have hmemK := hle hmemK'2
    have := K.mul_mem (K.mul_mem (o₁.out.out : K).2 hmemK) (K.inv_mem (o₂.out.out : K).2)
    simpa [mul_assoc] using this
  have hq1out : g ^ n • q₂.out = q₁.out := by
    rw [← QuotientGroup.out_eq' q₂.out, ← QuotientGroup.out_eq' q₁.out,
      zpow_smul_mk_eq_mk_iff (K' := K)]
    exact hαK
  have hqeq : q₁ = q₂ := by
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂, ← hq1out]
    exact Quotient.sound ⟨⟨g ^ n, n, rfl⟩, rfl⟩

  subst hqeq
  have hmj : (minimalPeriod (g • ·) q₁.out : ℤ) ∣ n := (conj_zpow_mem_K_iff g q₁ n).mp hαK
  obtain ⟨j, hj⟩ := hmj
  have hαeq : α = ((acuspGen g K q₁ : K) : G) ^ j := by
    rw [hα, hj, conj_zpow_eq_acuspGen_zpow]
  rw [hαeq] at hmemK'2

  have hoeq : (acuspGen g K q₁) ^ j • o₂.out = o₁.out := by
    rw [← QuotientGroup.out_eq' o₂.out, ← QuotientGroup.out_eq' o₁.out,
      show (acuspGen g K q₁) ^ j • QuotientGroup.mk (s := K'.subgroupOf K) o₂.out.out
        = QuotientGroup.mk (s := K'.subgroupOf K) ((acuspGen g K q₁) ^ j * o₂.out.out) from rfl,
      eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hmemK'2
  congr 1
  rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂, ← hoeq]
  exact Quotient.sound ⟨⟨(acuspGen g K q₁) ^ j, j, rfl⟩, rfl⟩

def towerEquiv (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    (Σ q : ACusp g K, InnerOrbit g K' K hle q) ≃ ACusp g K' :=
  Equiv.ofBijective (towerFn g hle) ⟨towerFn_injective g hle, towerFn_surjective g hle⟩

theorem minimalPeriod_towerLift (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    minimalPeriod (g • ·) (QuotientGroup.mk (s := K') (towerLift g hle q o))
      = minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out := by
  haveI : Finite (G ⧸ K') := K'.finite_quotient_of_finiteIndex
  haveI : Finite (G ⧸ K) := K.finite_quotient_of_finiteIndex
  haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
  set m := minimalPeriod (g • ·) q.out with hm
  set k := minimalPeriod ((acuspGen g K q) • ·) o.out with hk
  apply Nat.dvd_antisymm
  ·
    rw [← pow_smul_eq_iff_minimalPeriod_dvd, pow_smul_towerLift_eq_iff]
    exact ⟨k, rfl, (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl⟩
  ·
    have hper : g ^ (minimalPeriod (g • ·) (QuotientGroup.mk (s := K') (towerLift g hle q o)))
        • QuotientGroup.mk (s := K') (towerLift g hle q o)
        = QuotientGroup.mk (s := K') (towerLift g hle q o) :=
      (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
    obtain ⟨j, hj, hfix⟩ := (pow_smul_towerLift_eq_iff g hle q o _).mp hper
    obtain ⟨l, hl⟩ := (pow_smul_eq_iff_minimalPeriod_dvd).mp hfix
    exact ⟨l, by rw [hj, hl]; ring⟩

theorem acuspGen_towerEquiv_conj (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    ∃ c' : K',
      ((acuspGen g K' (towerEquiv g hle ⟨q, o⟩) : K') : G) =
        (c' : G) *
          (((o.out.out : K) : G)⁻¹ *
            ((acuspGen g K q : K) : G) ^ minimalPeriod ((acuspGen g K q) • ·) o.out *
            ((o.out.out : K) : G)) *
          (c' : G)⁻¹ := by
  haveI : Finite (G ⧸ K') := K'.finite_quotient_of_finiteIndex
  set q' := towerEquiv g hle ⟨q, o⟩ with hq'
  set p₀ := towerLift g hle q o with hp₀

  have hq'mk : q' = Quotient.mk _ (QuotientGroup.mk (s := K') p₀) := by
    rw [hq', towerEquiv, Equiv.ofBijective_apply]; rfl
  have horb : (Quotient.mk _ q'.out : ACusp g K')
      = Quotient.mk _ (QuotientGroup.mk (s := K') p₀) := by
    rw [Quotient.out_eq]; exact hq'mk
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at horb
  obtain ⟨h, hn⟩ := horb
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have hn' : g ^ n • QuotientGroup.mk (s := K') p₀ = q'.out := hng ▸ hn
  clear hng hn h

  have hφ' : (g ^ n * p₀)⁻¹ * q'.out.out ∈ K' := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← hn']; rfl
  set φ' : K' := ⟨(g ^ n * p₀)⁻¹ * q'.out.out, hφ'⟩ with hφ'def
  have hout : q'.out.out = g ^ n * p₀ * (φ' : G) := by
    rw [hφ'def]; simp [mul_assoc]
  refine ⟨⟨(φ' : G)⁻¹, K'.inv_mem φ'.2⟩, ?_⟩

  have hm' : minimalPeriod (g • ·) q'.out
      = minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out := by
    rw [← hn', minimalPeriod_zpow_smul, minimalPeriod_towerLift]

  show q'.out.out⁻¹ * g ^ minimalPeriod (g • ·) q'.out * q'.out.out = _
  rw [hout, hm', ← conj_pow_eq_acuspGen_pow g q (minimalPeriod ((acuspGen g K q) • ·) o.out)]
  have hconj := towerLift_conj_zpow g hle q o
    ((minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out : ℕ) : ℤ)
  rw [zpow_natCast] at hconj
  rw [← hp₀] at hconj
  rw [show ((o.out.out : K) : G)⁻¹ *
      (q.out.out⁻¹ * g ^ (minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out)
        * q.out.out) * ((o.out.out : K) : G)
      = p₀⁻¹ * g ^ (minimalPeriod (g • ·) q.out * minimalPeriod ((acuspGen g K q) • ·) o.out) * p₀
    from hconj.symm]
  group

theorem cusp_tower_abstract (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex] :
    ∃ e : ACusp g K' ≃ Σ q : ACusp g K, InnerOrbit g K' K hle q,
      ∀ (q : ACusp g K) (o : InnerOrbit g K' K hle q),
        ∃ c' : K',
          ((acuspGen g K' (e.symm ⟨q, o⟩) : K') : G) =
            (c' : G) *
              (((o.out.out : K) : G)⁻¹ *
                ((acuspGen g K q : K) : G) ^ minimalPeriod ((acuspGen g K q) • ·) o.out *
                ((o.out.out : K) : G)) *
              (c' : G)⁻¹ := by
  refine ⟨(towerEquiv g hle).symm, ?_⟩
  intro q o
  simpa using acuspGen_towerEquiv_conj g hle q o

end ModularCurve.PDPairing.CuspTower
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

end
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

end Aux2CuspTower
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

section Aux4PDU

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace Period
p2m_export "ModularCurve.Period" "IsParabolicHom parabolicHoms mem_parabolicHoms_iff"
p2m_open "ModularCurve.Period ModularCurve"

variable {Γ : Subgroup SL(2, ℤ)}

theorem IsParabolicHom.apply_T_zpow_eq_zero {A : Type*} [AddCommGroup A] {φ : Additive Γ →+ A}
    (hφ : IsParabolicHom Γ φ) (n : ℤ) (hT : ModularGroup.T ^ n ∈ Γ) :
    φ (Additive.ofMul ⟨ModularGroup.T ^ n, hT⟩) = 0 := by
  refine hφ _ ?_
  have : ((ModularGroup.T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] :=
    ModularGroup.coe_T_zpow n
  rw [this, Matrix.trace_fin_two_of]
  norm_num

theorem IsParabolicHom.apply_neg_one_eq_zero {A : Type*} [AddCommGroup A] {φ : Additive Γ →+ A}
    (hφ : IsParabolicHom Γ φ) (h : (-1 : SL(2, ℤ)) ∈ Γ) :
    φ (Additive.ofMul ⟨-1, h⟩) = 0 := by
  refine hφ _ ?_
  have : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -1 := by
    simp [Matrix.SpecialLinearGroup.coe_neg]
  rw [this]
  simp

end ModularCurve.Period
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
p2m_open "ModularCurve.PDPairing ModularCurve"

section Gamma0Hecke

variable (M : ℕ) (ℓ : ℕ) (A : Type*) [AddCommGroup A]

noncomputable def heckeT0L (R : Type*) [Semiring R] [Module R A] [NeZero ℓ] :
    (Additive ↥(Gamma0 M) →+ A) →ₗ[R] (Additive ↥(Gamma0 M) →+ A) where
  toFun := heckeT0 M ℓ A
  map_add' := (heckeT0 M ℓ A).map_add
  map_smul' r φ := by
    ext g
    simp only [heckeT0_apply, MonoidHom.toAdditiveLeft_apply_apply, AddMonoidHom.smul_apply,
      MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
      MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd,
      Finset.smul_sum, RingHom.id_apply]

end Gamma0Hecke
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

section ParRestrict

p2m_open "ModularCurve.Period P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Period"

theorem trace_conjLowerMat (d : ℕ) (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) :
    ((conjLowerMat d A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  show (conjLowerMat d A h) 0 0 + (conjLowerMat d A h) 1 1 = A 0 0 + A 1 1
  simp [conjLowerMat]

theorem trace_conjUpperMat (ℓ : ℕ) (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    ((conjUpperMat ℓ A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  show (conjUpperMat ℓ A h) 0 0 + (conjUpperMat ℓ A h) 1 1 = A 0 0 + A 1 1
  simp [conjUpperMat]

theorem sq_sub_one_eq_zero_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) : (M - 1) ^ 2 = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  ext i j
  rw [sq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination M 0 0 * htr - hdet
      | linear_combination M 0 1 * htr
      | linear_combination M 1 0 * htr
      | linear_combination M 1 1 * htr - hdet

theorem trace_pow_eq_two_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) (n : ℕ) : (M ^ n).trace = 2 := by
  have hNN : (M - 1) * (M - 1) = 0 := by
    rw [← sq]; exact sq_sub_one_eq_zero_of_trace_eq_two M hdet htr
  have hsplit : (1 : Matrix (Fin 2) (Fin 2) ℤ) + (M - 1) = M := by abel
  have hNM : (M - 1) * M = M - 1 := by
    calc (M - 1) * M = (M - 1) * (1 + (M - 1)) := by rw [hsplit]
      _ = (M - 1) * 1 + (M - 1) * (M - 1) := by rw [mul_add]
      _ = M - 1 := by rw [mul_one, hNN, add_zero]
  have hpow : ∀ m : ℕ, M ^ m = 1 + m • (M - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      calc M ^ (k + 1) = M ^ k * M := pow_succ M k
        _ = (1 + k • (M - 1)) * M := by rw [ih]
        _ = 1 * M + (k • (M - 1)) * M := by rw [add_mul]
        _ = M + k • ((M - 1) * M) := by rw [one_mul, smul_mul_assoc]
        _ = M + k • (M - 1) := by rw [hNM]
        _ = 1 + (k + 1) • (M - 1) := by
            rw [succ_nsmul, ← hsplit]
            abel
  rw [hpow n, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, htr, Matrix.trace_one]
  simp [Fintype.card_fin]

theorem sq_trace_pow_eq_four (A : SL(2, ℤ))
    (hA : ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) (n : ℕ) :
    (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  set M : Matrix (Fin 2) (Fin 2) ℤ := ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M.det = 1 := A.2
  have hcoe : (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = M ^ n := by
    simp [hM]
  rw [hcoe]
  have htr : M.trace = 2 ∨ M.trace = -2 := by
    have h0 : (M.trace - 2) * (M.trace + 2) = 0 := by linear_combination hA
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases htr with h2 | hm2
  · rw [trace_pow_eq_two_of_trace_eq_two M hdet h2 n]; norm_num
  · have hdetneg : (-M).det = 1 := by
      rw [Matrix.det_neg]
      simp [hdet, Fintype.card_fin]
    have htrneg : (-M).trace = 2 := by rw [Matrix.trace_neg, hm2]; ring
    have hkey := trace_pow_eq_two_of_trace_eq_two (-M) hdetneg htrneg n
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_pow] at hkey
      rw [hkey]; norm_num
    · rw [ho.neg_pow, Matrix.trace_neg] at hkey
      have hm : (M ^ n).trace = -2 := by linarith
      rw [hm]; norm_num

variable (R : Type*) [CommRing R] (M M' d : ℕ)

theorem trace_conj_SL (b c : SL(2, ℤ)) :
    ((b⁻¹ * c * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_mul, coe_mul, Matrix.trace_mul_comm, ← mul_assoc, ← coe_mul, mul_inv_cancel,
    coe_one, one_mul]

theorem sq_trace_conj_pow (b γA : ↥(Gamma0 M)) (p : ℕ)
    (hγ : ((γA : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    (((b⁻¹ * γA ^ p * b : ↥(Gamma0 M)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  have hcoe : ((b⁻¹ * γA ^ p * b : ↥(Gamma0 M)) : SL(2, ℤ))
      = ((b : SL(2, ℤ)))⁻¹ * ((γA : SL(2, ℤ))) ^ p * (b : SL(2, ℤ)) := by
    norm_cast
  rw [hcoe, trace_conj_SL]
  exact sq_trace_pow_eq_four γA hγ p

theorem conjL0_parabolic_vanish (ℓ : ℕ) [NeZero ℓ]
    (φ : Additive ↥(Gamma0 M) →+ R) (hφ : φ ∈ parabolicHoms R (Gamma0 M) R)
    (x : ↥(Gamma0HUpper M ℓ))
    (hx : (((x : ↥(Gamma0 M)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    φ (Additive.ofMul (conjL0 M ℓ x)) = 0 := by
  refine hφ _ ?_
  show ((conjUpperMat ℓ ((x : ↥(Gamma0 M)) : SL(2, ℤ)) (dvd_of_mem_Gamma0HUpper M ℓ x)
      : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [trace_conjUpperMat]
  exact hx

theorem pushChar0_parabolic_vanish [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (ψ : Additive ↥(Gamma0 M') →+ R) (hψ : ψ ∈ parabolicHoms R (Gamma0 M') R)
    (e : ↥((iotaDeg0 M M' d hMM' hdd).range))
    (he : (((e : ↥(Gamma0 M)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    pushChar0 M M' d R hMM' hdd ψ (Additive.ofMul e) = 0 := by
  show ψ (Additive.ofMul (((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e)) = 0
  refine hψ _ ?_
  have happ : iotaDeg0 M M' d hMM' hdd (((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e) = (e : ↥(Gamma0 M)) := by
    have h := MulEquiv.apply_symm_apply ((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)) e
    exact congrArg Subtype.val h
  rw [← trace_conjLowerMat d ((((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e : ↥(Gamma0 M')) : SL(2, ℤ))
      (dvd_entry0 M M' d hMM' hdd _)]
  show (((iotaDeg0 M M' d hMM' hdd (((iotaDeg0 M M' d hMM' hdd).ofInjective
      (iotaDeg0_injective M M' d hMM' hdd)).symm e) : ↥(Gamma0 M)) : SL(2, ℤ))
      : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [happ]
  exact he

theorem iDeg0_mem_parabolicHoms [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (φ : Additive ↥(Gamma0 M) →+ R) (hφ : φ ∈ parabolicHoms R (Gamma0 M) R) :
    iDeg0 M M' d R R hMM' hdd φ ∈ parabolicHoms R (Gamma0 M') R := by
  intro γ' hγ'
  show φ (Additive.ofMul (iotaDeg0 M M' d hMM' hdd γ')) = 0
  refine hφ (iotaDeg0 M M' d hMM' hdd γ') ?_
  show ((conjLowerMat d (γ' : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ') : SL(2, ℤ))
      : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [trace_conjLowerMat]
  exact hγ'

theorem jDeg0_mem_parabolicHoms [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (ψ : Additive ↥(Gamma0 M') →+ R) (hψ : ψ ∈ parabolicHoms R (Gamma0 M') R) :
    jDeg0 M M' d R R hMM' hdd ψ ∈ parabolicHoms R (Gamma0 M) R := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (↥(Subgroup.zpowers γ))
      (↥(Gamma0 M) ⧸ (iotaDeg0 M M' d hMM' hdd).range))) := Fintype.ofFinite _
  show Multiplicative.toAdd
      (MonoidHom.transfer
        (AddMonoidHom.toMultiplicativeRight (pushChar0 M M' d R hMM' hdd ψ))
        (Additive.toMul (Additive.ofMul γ))) = 0
  rw [toMul_ofMul, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  exact pushChar0_parabolic_vanish R M M' d hMM' hdd ψ hψ _
    (sq_trace_conj_pow M q.out.out γ _ hγ)

theorem heckeT0_mem_parabolicHoms (ℓ : ℕ) [NeZero ℓ]
    (φ : Additive ↥(Gamma0 M) →+ R) (hφ : φ ∈ parabolicHoms R (Gamma0 M) R) :
    heckeT0 M ℓ R φ ∈ parabolicHoms R (Gamma0 M) R := by
  classical
  intro γ hγ
  haveI : Fintype (Quotient (MulAction.orbitRel (↥(Subgroup.zpowers γ))
      (↥(Gamma0 M) ⧸ Gamma0HUpper M ℓ))) := Fintype.ofFinite _
  show Multiplicative.toAdd
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL0 M ℓ))
        (Additive.toMul (Additive.ofMul γ))) = 0
  rw [toMul_ofMul, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  exact conjL0_parabolic_vanish R M ℓ φ hφ _ (sq_trace_conj_pow M q.out.out γ _ hγ)

def iPar [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    ↥(parabolicHoms R (Gamma0 M) R) →ₗ[R] ↥(parabolicHoms R (Gamma0 M') R) :=
  (iDeg0 M M' d R R hMM' hdd).restrict
    (fun φ hφ => iDeg0_mem_parabolicHoms R M M' d hMM' hdd φ hφ)

noncomputable def jPar [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    ↥(parabolicHoms R (Gamma0 M') R) →ₗ[R] ↥(parabolicHoms R (Gamma0 M) R) :=
  (jDeg0 M M' d R R hMM' hdd).restrict
    (fun ψ hψ => jDeg0_mem_parabolicHoms R M M' d hMM' hdd ψ hψ)

noncomputable def TPar (ℓ : ℕ) [NeZero ℓ] :
    ↥(parabolicHoms R (Gamma0 M) R) →ₗ[R] ↥(parabolicHoms R (Gamma0 M) R) :=
  (heckeT0L M ℓ R R).restrict (fun φ hφ => heckeT0_mem_parabolicHoms R M ℓ φ hφ)

end ParRestrict
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

end ModularCurve.PDPairing
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

end Aux4PDU
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

section Aux2IDX

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace IDX
p2m_open "ModularCurve.PDPairing ModularCurve"

open CongruenceSubgroup Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups ModularGroup

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

theorem card_SL2_ZMod_four : Fintype.card (SpecialLinearGroup (Fin 2) (ZMod 4)) = 48 := by decide

theorem isUnit_col_of_det_aux :
    ∀ a b c d : ZMod 4, a * d - b * c = 1 → IsUnit a ∨ IsUnit c := by decide

theorem isUnit_col_of_det_one (g : SpecialLinearGroup (Fin 2) (ZMod 4)) :
    IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0) ∨
      IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0) := by
  have hdet := g.2; rw [Matrix.det_fin_two] at hdet
  exact isUnit_col_of_det_aux _ _ _ _ hdet

def U (r : ℤ) : SL(2, ℤ) := ⟨!![1, 0; r, 1], by simp [Matrix.det_fin_two]⟩

def E (s : ℤ) : SL(2, ℤ) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem map_U_val (x : ZMod 4) :
    ((SLMOD(4) (U (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![1, 0; x, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [U, Matrix.SpecialLinearGroup.map, ZMod.natCast_val, ZMod.intCast_cast]

theorem map_E_val (x : ZMod 4) :
    ((SLMOD(4) (E (x.val : ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![1, x; 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [E, Matrix.SpecialLinearGroup.map, ZMod.natCast_val, ZMod.intCast_cast]

theorem map_neg_one :
    ((SLMOD(4) (-1 : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![-1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map]

def liftFn (a b c : ZMod 4) : SL(2, ℤ) :=
  U ((c * a).val : ℤ) * (if a = 1 then 1 else -1) * E ((a * b).val : ℤ)

theorem map_liftFn_aux : ∀ a b c d : ZMod 4, a * d - b * c = 1 → IsUnit a →
    ((SLMOD(4) (liftFn a b c)) : Matrix (Fin 2) (Fin 2) (ZMod 4)) = !![a, b; c, d] := by
  intro a b c d hdet hu
  have hmid : ((SLMOD(4) (if a = 1 then (1 : SL(2,ℤ)) else -1))
      : Matrix (Fin 2) (Fin 2) (ZMod 4)) = if a = 1 then !![1,0;0,1] else !![-1,0;0,-1] := by
    split_ifs with h
    · simp [Matrix.one_fin_two]
    · exact map_neg_one
  simp only [liftFn, map_mul, SpecialLinearGroup.coe_mul, map_U_val, map_E_val, hmid]
  split_ifs with h1 <;>
    · ext i j; fin_cases i <;> fin_cases j <;>
        · simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val',
            Matrix.cons_val_fin_one, Matrix.empty_val']
          revert hdet hu h1; decide +revert

theorem mem_range_of_isUnit_00 (g : SpecialLinearGroup (Fin 2) (ZMod 4))
    (hu : IsUnit ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0)) :
    g ∈ (SLMOD(4)).range := by
  refine ⟨liftFn ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0)
    ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 1)
    ((g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0), ?_⟩
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 1
      - (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 1
        * (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0 = 1 := by
    have := g.2; rwa [Matrix.det_fin_two] at this
  apply Subtype.ext
  rw [map_liftFn_aux _ _ _ _ hdet hu]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem SLMOD_four_surjective : Function.Surjective (SLMOD(4)) := by
  intro g
  rcases isUnit_col_of_det_one g with h0 | h1
  · exact (mem_range_of_isUnit_00 g h0)
  · have hSg : IsUnit (((SLMOD(4) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 4))
        : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0) := by
      have : ((SLMOD(4) ModularGroup.S * g : SpecialLinearGroup (Fin 2) (ZMod 4))
          : Matrix (Fin 2) (Fin 2) (ZMod 4)) 0 0
          = - (g : Matrix (Fin 2) (Fin 2) (ZMod 4)) 1 0 := by
        simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.SpecialLinearGroup.map, MonoidHom.coe_mk, OneHom.coe_mk, ModularGroup.S]
        simp
      rw [this]; exact h1.neg
    obtain ⟨y, hy⟩ := mem_range_of_isUnit_00 _ hSg
    exact ⟨ModularGroup.S⁻¹ * y, by rw [map_mul, hy, map_inv, ← mul_assoc, inv_mul_cancel, one_mul]⟩

theorem index_Gamma_four_impl : (Gamma 4).index = 48 := by
  have hcard : Nat.card (SpecialLinearGroup (Fin 2) (ZMod 4)) = 48 := by
    rw [Nat.card_eq_fintype_card]; exact card_SL2_ZMod_four
  rw [show Gamma 4 = (SLMOD(4)).ker from rfl, Subgroup.index_ker,
    (MonoidHom.range_eq_top).mpr SLMOD_four_surjective, ← hcard,
    Nat.card_congr (Subgroup.topEquiv).toEquiv]

end ModularCurve.PDPairing.IDX
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

end Aux2IDX
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

section Aux2T1NAT

section Aux1BaseTwo

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace BaseTwo
p2m_open "ModularCurve.PDPairing ModularCurve"

open Matrix.SpecialLinearGroup ModularGroup CongruenceSubgroup MulAction
open scoped MatrixGroups

abbrev red2 : SL(2, ℤ) →* SL(2, ZMod 2) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

theorem mem_Gamma_two_iff (g : SL(2, ℤ)) : g ∈ Gamma 2 ↔ red2 g = 1 := Gamma_mem'

def g₁ : SL(2, ℤ) := ⟨!![1, 0; -1, 1], by norm_num [Matrix.det_fin_two_of]⟩

def rep : Fin 3 → SL(2, ℤ) := ![1, S, g₁]

def ustd (i : Fin 3) : SL(2, ℤ) := (rep i)⁻¹ * T ^ (2 : ℕ) * rep i

theorem coe_ustd_zero : ((ustd 0 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2; 0, 1] := by decide
theorem coe_ustd_one : ((ustd 1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -2, 1] := by decide
theorem coe_ustd_two : ((ustd 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 2; -2, 3] := by decide

theorem red2_T_sq : red2 T ^ 2 = 1 := by decide

theorem red2_classify (x : SL(2, ZMod 2)) : ∃ j : Fin 2, ∃ i : Fin 3, x = red2 T ^ (j : ℕ) * red2 (rep i) := by
  revert x; decide

theorem red2_distinct (j : Fin 2) (i i' : Fin 3) (h : red2 T ^ (j : ℕ) * red2 (rep i) = red2 (rep i')) :
    i = i' ∧ j = 0 := by
  revert j i i' ; decide

theorem red2_ustd (i : Fin 3) : red2 (ustd i) = 1 := by revert i; decide

theorem red2_conj_T_ne (i : Fin 3) : red2 ((rep i)⁻¹ * T * rep i) ≠ 1 := by revert i; decide

theorem red2_T_zpow (j : ℤ) : ∃ j' : Fin 2, red2 (T ^ j) = red2 T ^ (j' : ℕ) := by
  have h2 : red2 T ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]; exact red2_T_sq
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
  · refine ⟨0, ?_⟩
    rw [map_zpow, zpow_mul, h2, one_zpow]
    simp
  · refine ⟨1, ?_⟩
    rw [map_zpow, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
    simp

theorem decomp (g : SL(2, ℤ)) : ∃ (i : Fin 3) (j : Fin 2) (γ : SL(2, ℤ)), γ ∈ Gamma 2 ∧ g = T ^ (j : ℕ) * rep i * γ := by
  obtain ⟨j, i, h⟩ := red2_classify (red2 g)
  refine ⟨i, j, (T ^ (j : ℕ) * rep i)⁻¹ * g, ?_, by group⟩
  rw [mem_Gamma_two_iff, map_mul, map_inv, map_mul, map_pow, ← h, inv_mul_cancel]

theorem decomp_unique {j j' : ℤ} {i i' : Fin 3} {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) (hγ' : γ' ∈ Gamma 2)
    (h : T ^ j * rep i * γ = T ^ j' * rep i' * γ') : i = i' := by
  have h2 : T ^ (j - j') * rep i * (γ * γ'⁻¹) = rep i' := by
    calc T ^ (j - j') * rep i * (γ * γ'⁻¹) = (T ^ j')⁻¹ * (T ^ j * rep i * γ) * γ'⁻¹ := by group
      _ = rep i' := by rw [h]; group
  have hr := congrArg red2 h2
  obtain ⟨j₂, hj₂⟩ := red2_T_zpow (j - j')
  rw [map_mul, map_mul, (mem_Gamma_two_iff _).mp (Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ hγ')), mul_one,
    hj₂] at hr
  exact (red2_distinct j₂ i i' hr).1

section CuspDefs
variable (Φ : Subgroup SL(2, ℤ))

abbrev Cusp : Type := Quotient (orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Φ))

noncomputable scoped instance [Φ.FiniteIndex] : Fintype (Cusp Φ) := Fintype.ofFinite _

noncomputable def cuspGen (q : Cusp Φ) : Φ :=
  ⟨q.out.out⁻¹ * ModularGroup.T ^ Function.minimalPeriod (ModularGroup.T • ·) q.out * q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem Φ ModularGroup.T q.out⟩
end CuspDefs
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

theorem iterate_smul_coe_eq_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) (n : ℕ) :
    (T • ·)^[n] ((g : SL(2, ℤ)) : SL(2, ℤ) ⧸ Φ) = (g : SL(2, ℤ) ⧸ Φ) ↔ g⁻¹ * T ^ n * g ∈ Φ := by
  rw [smul_iterate_apply, Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, mul_inv_rev,
    show g⁻¹ * (T ^ n)⁻¹ * g = (g⁻¹ * T ^ n * g)⁻¹ by group, inv_mem_iff]

theorem conj_mem_iff_of_decomp (j : ℤ) (i : Fin 3) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) (n : ℕ) :
    (T ^ j * rep i * γ)⁻¹ * T ^ n * (T ^ j * rep i * γ) ∈ Gamma 2 ↔ (rep i)⁻¹ * T ^ n * rep i ∈ Gamma 2 := by
  rw [show (T ^ j * rep i * γ)⁻¹ * T ^ n * (T ^ j * rep i * γ) = γ⁻¹ * ((rep i)⁻¹ * T ^ n * rep i) * γ by group,
    Subgroup.mul_mem_cancel_right _ hγ, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hγ)]

theorem minimalPeriod_eq_two (j : ℤ) (i : Fin 3) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2) :
    Function.minimalPeriod (T • ·) ((T ^ j * rep i * γ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Function.minimalPeriod_eq_prime
  · show (T • ·)^[2] _ = _
    rw [iterate_smul_coe_eq_iff, conj_mem_iff_of_decomp j i hγ, mem_Gamma_two_iff]
    exact red2_ustd i
  · show ¬ ((T • ·)^[1] _ = _)
    rw [iterate_smul_coe_eq_iff, conj_mem_iff_of_decomp j i hγ, mem_Gamma_two_iff, pow_one]
    exact red2_conj_T_ne i

theorem out_decomp (q : Cusp (Gamma 2)) :
    ∃ (i : Fin 3) (j : ℤ) (γ : SL(2, ℤ)), γ ∈ Gamma 2 ∧ q.out.out = T ^ j * rep i * γ := by
  obtain ⟨i, j, γ, hγ, h⟩ := decomp q.out.out
  exact ⟨i, j, γ, hγ, by rw [h, zpow_natCast]⟩

noncomputable def idx (q : Cusp (Gamma 2)) : Fin 3 := (out_decomp q).choose

theorem idx_spec (q : Cusp (Gamma 2)) :
    ∃ (j : ℤ) (γ : SL(2, ℤ)), γ ∈ Gamma 2 ∧ q.out.out = T ^ j * rep (idx q) * γ :=
  (out_decomp q).choose_spec

theorem cusp_eq_of_decomp (q : Cusp (Gamma 2)) {i : Fin 3} {j : ℤ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma 2)
    (h : q.out.out = T ^ j * rep i * γ) :
    q = Quotient.mk _ ((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2) := by
  rw [← Quotient.out_eq q]
  apply Quotient.sound
  show q.out ∈ MulAction.orbit (Subgroup.zpowers T) (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))
  rw [MulAction.mem_orbit_iff]
  refine ⟨⟨T ^ j, Subgroup.zpow_mem_zpowers T j⟩, ?_⟩
  rw [← QuotientGroup.out_eq' q.out, h]
  show ((T ^ j : SL(2, ℤ)) • (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))) = _
  rw [Quotient.smul_coe, smul_eq_mul]
  rw [QuotientGroup.eq, inv_mul_cancel_left]
  exact hγ

theorem idx_injective : Function.Injective idx := by
  intro q q' h
  obtain ⟨j, γ, hγ, hq⟩ := idx_spec q
  obtain ⟨j', γ', hγ', hq'⟩ := idx_spec q'
  rw [cusp_eq_of_decomp q hγ hq, cusp_eq_of_decomp q' hγ' hq', h]

theorem idx_mk (i : Fin 3) : idx (Quotient.mk _ ((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2)) = i := by
  set q : Cusp (Gamma 2) := Quotient.mk _ ((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2) with hq
  obtain ⟨j, γ, hγ, h⟩ := idx_spec q

  have hmem : q.out ∈ MulAction.orbit (Subgroup.zpowers T) (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2)) := by
    have := Quotient.mk_out (s := orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Gamma 2))
      (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))
    exact this
  rw [MulAction.mem_orbit_iff] at hmem
  obtain ⟨⟨t, ht⟩, hts⟩ := hmem
  rw [Subgroup.mem_zpowers_iff] at ht
  obtain ⟨j₀, rfl⟩ := ht
  change ((T ^ j₀ : SL(2, ℤ)) • (((rep i : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma 2))) = _ at hts
  rw [Quotient.smul_coe, smul_eq_mul] at hts

  obtain ⟨⟨γ₀, hγ₀⟩, hout⟩ := QuotientGroup.mk_out_eq_mul (Gamma 2) (T ^ j₀ * rep i)
  rw [hts] at hout

  have := decomp_unique hγ₀ hγ (hout.symm.trans h)
  exact this.symm

theorem idx_surjective : Function.Surjective idx := fun i => ⟨_, idx_mk i⟩

theorem Gamma_two_cusps :
    ∃ e : Cusp (Gamma 2) ≃ Fin 3, ∀ q : Cusp (Gamma 2), ∃ γ : SL(2, ℤ), γ ∈ Gamma 2 ∧
      ((cuspGen (Gamma 2) q : Gamma 2) : SL(2, ℤ)) = γ⁻¹ * ustd (e q) * γ := by
  refine ⟨Equiv.ofBijective idx ⟨idx_injective, idx_surjective⟩, fun q => ?_⟩
  obtain ⟨j, γ, hγ, h⟩ := idx_spec q
  refine ⟨γ, hγ, ?_⟩
  show q.out.out⁻¹ * T ^ Function.minimalPeriod (T • ·) q.out * q.out.out = γ⁻¹ * ustd (idx q) * γ
  have hper : Function.minimalPeriod (T • ·) q.out = 2 := by
    rw [← QuotientGroup.out_eq' q.out, h]
    exact minimalPeriod_eq_two j (idx q) hγ
  rw [hper, h, ustd]
  group

end ModularCurve.PDPairing.BaseTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier"

end Aux1BaseTwo
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace T1
p2m_open "ModularCurve.PDPairing ModularCurve"

open Function MulAction Subgroup ModularCurve.PDPairing.CuspTower

variable {G : Type*} [Group G] {K' K : Subgroup G}

noncomputable scoped instance instFintypeACusp (g : G) (H : Subgroup G) [H.FiniteIndex] :
    Fintype (ACusp g H) := by
  haveI : Finite (G ⧸ H) := H.finite_quotient_of_finiteIndex
  exact Fintype.ofFinite _

variable {A : Type*} [CommGroup A]

theorem map_conj_eq (ϕ : K' →* A) (c v : K') : ϕ (c * v * c⁻¹) = ϕ v := by
  rw [map_mul, map_mul, map_inv, mul_comm (ϕ c), mul_assoc, mul_inv_cancel, mul_one]

noncomputable def innerSummand (g : G) (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    ↥K' :=
  Subgroup.subgroupOfEquivOfLe hle
    ⟨o.out.out⁻¹ * (acuspGen g K q) ^ minimalPeriod ((acuspGen g K q) • ·) o.out * o.out.out,
      QuotientGroup.out_conj_pow_minimalPeriod_mem (K'.subgroupOf K) (acuspGen g K q) o.out⟩

theorem innerSummand_coe (g : G) (hle : K' ≤ K) (q : ACusp g K) (o : InnerOrbit g K' K hle q) :
    ((innerSummand g hle q o : K') : G)
      = ((o.out.out : K) : G)⁻¹ * ((acuspGen g K q : K) : G) ^
          minimalPeriod ((acuspGen g K q) • ·) o.out * ((o.out.out : K) : G) := by
  simp [innerSummand, Subgroup.subgroupOfEquivOfLe]

theorem transfer_eq_prod_sigma (g : G) (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (ϕ : K' →* A) :
    MonoidHom.transfer ϕ g = ∏ q : ACusp g K, ∏ o : InnerOrbit g K' K hle q,
      ϕ (innerSummand g hle q o) := by
  haveI : Finite (G ⧸ K) := K.finite_quotient_of_finiteIndex
  haveI : ∀ q : ACusp g K, Fintype (InnerOrbit g K' K hle q) := fun q => by
    haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
    exact Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    ← Equiv.prod_comp (towerEquiv g hle)]
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr (by congr 1) fun q _ => ?_
  refine Finset.prod_congr (by congr 1; exact Subsingleton.elim _ _) fun o _ => ?_
  obtain ⟨c', hc'⟩ := acuspGen_towerEquiv_conj g hle q o
  rw [← map_conj_eq ϕ c' (innerSummand g hle q o)]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, innerSummand_coe]
  exact hc'

theorem prod_innerSummand_eq_transfer (g : G) (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (ϕ : K' →* A) (q : ACusp g K) :
    haveI : Fintype (InnerOrbit g K' K hle q) := by
      haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
      exact Fintype.ofFinite _
    ∏ o : InnerOrbit g K' K hle q, ϕ (innerSummand g hle q o)
      = MonoidHom.transfer
          (ϕ.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
          (acuspGen g K q) := by
  haveI : Finite (K ⧸ K'.subgroupOf K) := (K'.subgroupOf K).finite_quotient_of_finiteIndex
  haveI : Fintype (InnerOrbit g K' K hle q) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  refine Finset.prod_congr ?_ fun o _ => rfl
  congr 1
  exact Subsingleton.elim _ _

theorem transfer_transfer (g : G) (hle : K' ≤ K) [K'.FiniteIndex] [K.FiniteIndex]
    (ϕ : K' →* A) :
    MonoidHom.transfer
      (MonoidHom.transfer (ϕ.comp (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom) : K →* A) g
    = MonoidHom.transfer ϕ g := by
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
    (H := K) (ϕ := MonoidHom.transfer _) g,
    transfer_eq_prod_sigma g hle ϕ]
  refine Finset.prod_congr (by congr 1) fun q _ =>
    (prod_innerSummand_eq_transfer g hle ϕ q).symm

section NAT

variable {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂] (σ : G₁ ≃* G₂) (L : Subgroup G₂)

def quotCongr : G₁ ⧸ (L.comap σ.toMonoidHom) ≃ G₂ ⧸ L :=
  Quotient.congr σ.toEquiv fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_comap,
      map_mul, map_inv]; rfl

@[scoped simp] theorem quotCongr_mk (a : G₁) :
    quotCongr σ L (QuotientGroup.mk a) = QuotientGroup.mk (σ a) := rfl

theorem quotCongr_smul (h : G₁) (x : G₁ ⧸ (L.comap σ.toMonoidHom)) :
    quotCongr σ L (h • x) = (σ h) • (quotCongr σ L x) := by
  refine x.induction_on fun a => ?_
  show QuotientGroup.mk (s := L) (σ (h * a)) = (σ h) • QuotientGroup.mk (s := L) (σ a)
  rw [map_mul]; rfl

theorem quotCongr_zpow_smul (h : G₁) (n : ℤ) (x : G₁ ⧸ (L.comap σ.toMonoidHom)) :
    quotCongr σ L (h ^ n • x) = (σ h) ^ n • (quotCongr σ L x) := by
  rw [quotCongr_smul, map_zpow]

theorem minimalPeriod_quotCongr (h : G₁) (x : G₁ ⧸ (L.comap σ.toMonoidHom)) :
    minimalPeriod ((σ h) • ·) (quotCongr σ L x) = minimalPeriod (h • ·) x := by
  have hiter : ∀ n : ℕ, (σ h) ^ n • (quotCongr σ L x) = quotCongr σ L (h ^ n • x) := fun n => by
    rw [← map_pow, ← quotCongr_smul]
  apply Nat.dvd_antisymm <;> rw [← pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [hiter]; exact congrArg _ ((pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl)
  · have h' := (pow_smul_eq_iff_minimalPeriod_dvd (a := σ h) (b := quotCongr σ L x)
      (n := minimalPeriod ((σ h) • ·) (quotCongr σ L x))).mpr dvd_rfl
    rw [hiter] at h'; exact (quotCongr σ L).injective h'

def acuspCongr (h : G₁) : ACusp h (L.comap σ.toMonoidHom) ≃ ACusp (σ h) L :=
  Quotient.congr (quotCongr σ L) fun a b => by
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨hh, hn⟩
      obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp hh.2
      have hn' : h ^ n • b = a := hng ▸ hn
      exact ⟨⟨(σ h) ^ n, n, rfl⟩, by
        show (σ h) ^ n • (quotCongr σ L b) = quotCongr σ L a
        rw [← quotCongr_zpow_smul]; exact congrArg _ hn'⟩
    · rintro ⟨hh, hn⟩
      obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp hh.2
      have hn' : (σ h) ^ n • (quotCongr σ L b) = quotCongr σ L a := hng ▸ hn
      refine ⟨⟨h ^ n, n, rfl⟩, (quotCongr σ L).injective ?_⟩
      show quotCongr σ L (h ^ n • b) = quotCongr σ L a
      rw [quotCongr_zpow_smul]; exact hn'

theorem acuspGen_acuspCongr_conj [L.FiniteIndex]
    [(L.comap σ.toMonoidHom).FiniteIndex] (h : G₁) (q' : ACusp h (L.comap σ.toMonoidHom)) :
    ∃ l : L, ((acuspGen (σ h) L (acuspCongr σ L h q') : L) : G₂)
      = (l : G₂)
        * (σ.toMonoidHom.subgroupComap L (acuspGen h (L.comap σ.toMonoidHom) q') : G₂)
        * (l : G₂)⁻¹ := by
  haveI : Finite (G₂ ⧸ L) := L.finite_quotient_of_finiteIndex
  set q := acuspCongr σ L h q' with hq

  have hqc : quotCongr σ L q'.out = QuotientGroup.mk (s := L) (σ q'.out.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q'.out]
    rfl
  have hqmk : q = Quotient.mk _ (quotCongr σ L q'.out) := by
    conv_lhs => rw [hq, ← Quotient.out_eq q', show acuspCongr σ L h ⟦q'.out⟧
      = ⟦quotCongr σ L q'.out⟧ from rfl]
  have horb : (Quotient.mk _ q.out : ACusp (σ h) L)
      = Quotient.mk _ (quotCongr σ L q'.out) := by rw [Quotient.out_eq]; exact hqmk
  rw [Quotient.eq, orbitRel_apply, mem_orbit_iff] at horb
  obtain ⟨hh, hn⟩ := horb
  obtain ⟨n, hng⟩ := Subgroup.mem_zpowers_iff.mp hh.2
  have hn' : (σ h) ^ n • (quotCongr σ L q'.out) = q.out := hng ▸ hn
  clear hng hn hh
  rw [hqc] at hn'

  have hl : q.out.out⁻¹ * ((σ h) ^ n * σ (q'.out.out)) ∈ L := by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']; exact hn'.symm
  refine ⟨⟨_, hl⟩, ?_⟩
  have hm' : minimalPeriod ((σ h) • ·) q.out = minimalPeriod (h • ·) q'.out := by
    rw [← hn']; conv_lhs => rw [← hqc]
    rw [← quotCongr_zpow_smul, minimalPeriod_quotCongr, minimalPeriod_zpow_smul]
  have hscoe : (σ.toMonoidHom.subgroupComap L (acuspGen h (L.comap σ.toMonoidHom) q') : G₂)
      = (σ (q'.out.out))⁻¹ * (σ h) ^ minimalPeriod (h • ·) q'.out * σ (q'.out.out) := by
    show σ _ = _; simp only [acuspGen, map_mul, map_inv, map_pow]
  show q.out.out⁻¹ * (σ h) ^ minimalPeriod ((σ h) • ·) q.out * q.out.out = _
  rw [hm', hscoe, Subgroup.coe_mk]

  group

scoped instance finiteIndex_comap_mulEquiv [hL : L.FiniteIndex] :
    (L.comap σ.toMonoidHom).FiniteIndex :=
  ⟨by rw [L.index_comap_of_surjective σ.surjective]; exact hL.1⟩

theorem transfer_congr [L.FiniteIndex] (χ : ↥L →* A) (h : G₁) :
    MonoidHom.transfer χ (σ h) = MonoidHom.transfer (χ.comp (σ.toMonoidHom.subgroupComap L)) h := by
  haveI : Finite (G₁ ⧸ L.comap σ.toMonoidHom) := (L.comap σ.toMonoidHom).finite_quotient_of_finiteIndex
  haveI : Fintype (ACusp h (L.comap σ.toMonoidHom)) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot (ϕ := χ) (σ h),
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
      (ϕ := χ.comp (σ.toMonoidHom.subgroupComap L)) h,
    ← Equiv.prod_comp (acuspCongr σ L h)]
  refine Finset.prod_congr (by congr 1) fun q' _ => ?_
  obtain ⟨l, hlconj⟩ := acuspGen_acuspCongr_conj σ L h q'
  have heq : acuspGen (σ h) L (acuspCongr σ L h q')
      = l * (σ.toMonoidHom.subgroupComap L (acuspGen h (L.comap σ.toMonoidHom) q')) * l⁻¹ := by
    apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv, hlconj]
  show χ (acuspGen (σ h) L (acuspCongr σ L h q')) = _
  rw [heq, map_conj_eq χ l, MonoidHom.comp_apply]
  rfl

end NAT
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo"

section CoresCores

variable {G : Type*} [Group G] {K H G' : Subgroup G}
variable {R : Type*} [CommRing R]

noncomputable def cores {Φ' Φ : Subgroup G} (h : Φ' ≤ Φ) [Φ'.FiniteIndex]
    (x : Additive Φ' →+ R) : Additive Φ →+ R :=
  MonoidHom.toAdditiveLeft
    (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom))))

theorem subgroupOf_subgroupOf_eq_comap (hHG : H ≤ G') :
    (K.subgroupOf G').subgroupOf (H.subgroupOf G')
      = (K.subgroupOf H).comap (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom := by
  ext x; rfl

scoped instance finiteIndex_comap_equiv (hHG : H ≤ G') (L : Subgroup ↥H) [hL : L.FiniteIndex] :
    (L.comap (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom).FiniteIndex :=
  ⟨by rw [L.index_comap_of_surjective (Subgroup.subgroupOfEquivOfLe hHG).surjective]; exact hL.1⟩

theorem transfer_congr_subgroupOf (hHG : H ≤ G') (L : Subgroup ↥H) [L.FiniteIndex]
    (χ : ↥L →* A) (h : ↥(H.subgroupOf G')) :
    MonoidHom.transfer χ ((Subgroup.subgroupOfEquivOfLe hHG) h)
      = MonoidHom.transfer
          (χ.comp ((Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom.subgroupComap L)) h :=
  transfer_congr (Subgroup.subgroupOfEquivOfLe hHG) L χ h

theorem equiv_comp_coe (hKH : K ≤ H) (hHG : H ≤ G')
    (w : ↥((K.subgroupOf G').subgroupOf (H.subgroupOf G'))) :
    ((Subgroup.subgroupOfEquivOfLe (hKH.trans hHG))
      ((Subgroup.subgroupOfEquivOfLe (Subgroup.subgroupOf_mono G' hKH)) w) : G)
    = ((Subgroup.subgroupOfEquivOfLe hKH)
        (((Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom.subgroupComap (K.subgroupOf H))
          (MulEquiv.subgroupCongr (subgroupOf_subgroupOf_eq_comap hHG) w)) : G) := rfl

theorem cores_cores (hKH : K ≤ H) (hHG : H ≤ G') [K.FiniteIndex] [H.FiniteIndex]
    (x : Additive K →+ R) :
    cores hHG (cores hKH x) = cores (hKH.trans hHG) x := by
  have hle : K.subgroupOf G' ≤ H.subgroupOf G' := Subgroup.subgroupOf_mono G' hKH
  have hchareq :
      (AddMonoidHom.toMultiplicativeRight
        ((cores hKH x).comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom)))
      = MonoidHom.transfer
          ((AddMonoidHom.toMultiplicativeRight
              (x.comp (MonoidHom.toAdditive
                (Subgroup.subgroupOfEquivOfLe (hKH.trans hHG)).toMonoidHom))).comp
            (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom) := by

    ext hh

    set χ := AddMonoidHom.toMultiplicativeRight
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom))
    show MonoidHom.transfer χ ((Subgroup.subgroupOfEquivOfLe hHG) hh) = _
    rw [transfer_congr_subgroupOf hHG (K.subgroupOf H) χ hh]

    congr 1
  have h := transfer_transfer (G := ↥G') (K' := K.subgroupOf G') (K := H.subgroupOf G')
    (A := Multiplicative R)
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer
      (AddMonoidHom.toMultiplicativeRight
        ((cores hKH x).comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe hHG).toMonoidHom))))
    = MonoidHom.toAdditiveLeft (MonoidHom.transfer
        (AddMonoidHom.toMultiplicativeRight
          (x.comp (MonoidHom.toAdditive
            (Subgroup.subgroupOfEquivOfLe (hKH.trans hHG)).toMonoidHom))))
  rw [hchareq]
  exact congrArg _ (MonoidHom.ext fun g' => h g' hle _)

end CoresCores
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo"

end ModularCurve.PDPairing.T1
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo"

end Aux2T1NAT
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace TD
p2m_open "ModularCurve.PDPairing ModularCurve"

section Prim

variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]

variable [IsFreeGroup Φ]

theorem hPrim_mul_of_omega_eq_zero (φ ψ : Additive Φ →+ R) (g g' : Φ) (h0 : omega φ ψ g g' = 0) :
    hPrim φ ψ (g * g') = hPrim φ ψ g + hPrim φ ψ g' := by
  rw [hPrim_mul, h0, sub_zero]

theorem hPrim_inv (φ ψ : Additive Φ →+ R) (g : Φ) : hPrim φ ψ g⁻¹ = - hPrim φ ψ g := by
  have h := hPrim_mul φ ψ g g⁻¹
  rw [mul_inv_cancel, hPrim_one, omega_self_inv, sub_zero] at h
  linear_combination -h

omit [IsFreeGroup Φ] in
theorem omega_inv_right (φ ψ : Additive Φ →+ R) (u g : Φ) : omega φ ψ u g⁻¹ = - omega φ ψ u g := by
  simp only [omega, ofMul_inv, map_neg]
  ring

omit [IsFreeGroup Φ] in
theorem omega_conj_aux (φ ψ : Additive Φ →+ R) (g u : Φ) :
    omega φ ψ g (u * g⁻¹) = - omega φ ψ u g := by
  simp only [omega, ofMul_mul, ofMul_inv, map_add, map_neg]
  ring

theorem hPrim_conj (φ ψ : Additive Φ →+ R) (g u : Φ) :
    hPrim φ ψ (g * u * g⁻¹) = hPrim φ ψ u + 2 * omega φ ψ u g := by
  rw [mul_assoc, hPrim_mul, hPrim_mul, hPrim_inv, omega_conj_aux, omega_inv_right]
  ring

omit [IsFreeGroup Φ] in
theorem omega_eq_zero_of_apply_eq_zero (φ ψ : Additive Φ →+ R) (u : Φ) (hφ : φ (Additive.ofMul u) = 0)
    (hψ : ψ (Additive.ofMul u) = 0) (g : Φ) : omega φ ψ u g = 0 := by
  simp [omega, hφ, hψ]

theorem hPrim_conj_of_apply_eq_zero (φ ψ : Additive Φ →+ R) (u : Φ) (hφ : φ (Additive.ofMul u) = 0)
    (hψ : ψ (Additive.ofMul u) = 0) (g : Φ) : hPrim φ ψ (g * u * g⁻¹) = hPrim φ ψ u := by
  rw [hPrim_conj, omega_eq_zero_of_apply_eq_zero φ ψ u hφ hψ g, mul_zero, add_zero]

omit [IsFreeGroup Φ] in
theorem omega_pow_self (φ ψ : Additive Φ →+ R) (u : Φ) (k : ℕ) : omega φ ψ (u ^ k) u = 0 := by
  simp only [omega, ofMul_pow, map_nsmul, nsmul_eq_mul]
  ring

theorem hPrim_pow (φ ψ : Additive Φ →+ R) (u : Φ) (k : ℕ) : hPrim φ ψ (u ^ k) = k * hPrim φ ψ u := by
  induction k with
  | zero => simp [hPrim_one]
  | succ k ih =>
    rw [pow_succ, hPrim_mul, ih, omega_pow_self]
    push_cast
    ring

theorem hPrim_of (φ ψ : Additive Φ →+ R) (a : IsFreeGroup.Generators Φ) : hPrim φ ψ (IsFreeGroup.of a) = 0 := by
  show (sect φ ψ (IsFreeGroup.of a)).1 = 0
  simp [sect]

theorem hPrim_of_inv (φ ψ : Additive Φ →+ R) (a : IsFreeGroup.Generators Φ) : hPrim φ ψ (IsFreeGroup.of a)⁻¹ = 0 := by
  rw [hPrim_inv, hPrim_of, neg_zero]

omit [IsFreeGroup Φ] in
theorem omega_one_right' (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g 1 = 0 := by
  simp [omega]

omit [IsFreeGroup Φ] in
theorem omega_mul_right' (φ ψ : Additive Φ →+ R) (g a b : Φ) :
    omega φ ψ g (a * b) = omega φ ψ g a + omega φ ψ g b := by
  simp only [omega, ofMul_mul, map_add]
  ring

def pairSum (φ ψ : Additive Φ →+ R) : List Φ → R
  | [] => 0
  | g :: L => (L.map (omega φ ψ g)).sum + pairSum φ ψ L

omit [IsFreeGroup Φ] in
theorem omega_list_prod (φ ψ : Additive Φ →+ R) (g : Φ) (L : List Φ) :
    omega φ ψ g L.prod = (L.map (omega φ ψ g)).sum := by
  induction L with
  | nil => rw [List.prod_nil, omega_one_right', List.map_nil, List.sum_nil]
  | cons a L ih => rw [List.prod_cons, omega_mul_right', ih, List.map_cons, List.sum_cons]

theorem hPrim_list_prod (φ ψ : Additive Φ →+ R) (L : List Φ) (hL : ∀ g ∈ L, hPrim φ ψ g = 0) :
    hPrim φ ψ L.prod = - pairSum φ ψ L := by
  induction L with
  | nil => rw [List.prod_nil, hPrim_one, pairSum, neg_zero]
  | cons g L ih =>
    rw [List.prod_cons, hPrim_mul, hL g (by simp), ih (fun g' hg' => hL g' (by simp [hg'])), omega_list_prod,
      pairSum]
    ring

theorem hPrim_list_prod' (φ ψ : Additive Φ →+ R) (L : List Φ) :
    hPrim φ ψ L.prod = (L.map (hPrim φ ψ)).sum - pairSum φ ψ L := by
  induction L with
  | nil => rw [List.prod_nil, hPrim_one, pairSum, List.map_nil, List.sum_nil, sub_zero]
  | cons g L ih =>
    rw [List.prod_cons, hPrim_mul, ih, omega_list_prod, pairSum, List.map_cons, List.sum_cons]
    ring

end Prim
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

section Orientation

def orientForm (N : Matrix (Fin 2) (Fin 2) ℤ) (y0 y1 : ℤ) : ℤ :=
  N 1 0 * y0 ^ 2 + (N 1 1 - N 0 0) * y0 * y1 - N 0 1 * y1 ^ 2

theorem orientForm_intertwine (a M N : Matrix (Fin 2) (Fin 2) ℤ) (h : M * a = a * N) (y0 y1 : ℤ) :
    orientForm M (a 0 0 * y0 + a 0 1 * y1) (a 1 0 * y0 + a 1 1 * y1) = a.det * orientForm N y0 y1 := by
  have e := fun i j => congrFun (congrFun h i) j
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  simp only [orientForm, Matrix.det_fin_two]
  linear_combination (-(a 1 0 * y0 + a 1 1 * y1) * y0) * h00 + (-(a 1 0 * y0 + a 1 1 * y1) * y1) * h01
    + ((a 0 0 * y0 + a 0 1 * y1) * y0) * h10 + ((a 0 0 * y0 + a 0 1 * y1) * y1) * h11

def IsPosUnipotent (u : Matrix (Fin 2) (Fin 2) ℤ) : Prop := 0 < u 0 1 ∨ (u 0 1 = 0 ∧ u 1 0 < 0)

theorem orientForm_neg_iff (u : Matrix (Fin 2) (Fin 2) ℤ) (htr : u.trace = 2) (hdet : u.det = 1)
    (y0 y1 : ℤ) (hy : (u 0 0 - 1) * y0 + u 0 1 * y1 ≠ 0 ∨ u 1 0 * y0 + (u 1 1 - 1) * y1 ≠ 0) :
    orientForm (u - 1) y0 y1 < 0 ↔ IsPosUnipotent u := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have hαδ : (u 0 0 - 1) + (u 1 1 - 1) = 0 := by linear_combination htr
  have hN : (u 0 0 - 1) * (u 1 1 - 1) - u 0 1 * u 1 0 = 0 := by linear_combination hdet - htr
  have hform : orientForm (u - 1) y0 y1 =
      u 1 0 * y0 ^ 2 + ((u 1 1 - 1) - (u 0 0 - 1)) * y0 * y1 - u 0 1 * y1 ^ 2 := by
    simp [orientForm, Matrix.sub_apply]
  rw [hform]
  by_cases hb : u 0 1 = 0
  ·
    have hα2 : (u 0 0 - 1) ^ 2 = 0 := by
      linear_combination (u 0 0 - 1) * hαδ - hN + (- u 1 0) * hb
    have hα : u 0 0 - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hα2
    have hδ : u 1 1 - 1 = 0 := by linear_combination hαδ - hα
    have hy' : u 1 0 * y0 ≠ 0 := by
      rcases hy with hy | hy
      · exfalso; apply hy; rw [hα, hb]; ring
      · rwa [hδ, zero_mul, add_zero] at hy
    have hγ : u 1 0 ≠ 0 := left_ne_zero_of_mul hy'
    have hy0 : y0 ≠ 0 := right_ne_zero_of_mul hy'
    have hy0sq : 0 < y0 ^ 2 := lt_of_le_of_ne (sq_nonneg y0) (Ne.symm (pow_ne_zero 2 hy0))
    simp only [IsPosUnipotent, hb, lt_self_iff_false, false_or, true_and]
    rw [hα, hδ]
    constructor
    · intro h; nlinarith [hy0sq, h]
    · intro h; nlinarith [hy0sq, h]
  ·
    have ht : (u 0 0 - 1) * y0 + u 0 1 * y1 ≠ 0 := by
      rcases hy with hy | hy
      · exact hy
      · intro h0
        apply hy

        have : u 0 1 * (u 1 0 * y0 + (u 1 1 - 1) * y1) = 0 := by
          linear_combination (-y0) * hN + (u 1 1 - 1) * h0
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' hb
        · exact h'
    have htsq : 0 < ((u 0 0 - 1) * y0 + u 0 1 * y1) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ht))
    have key : u 0 1 * (u 1 0 * y0 ^ 2 + ((u 1 1 - 1) - (u 0 0 - 1)) * y0 * y1 - u 0 1 * y1 ^ 2) =
        - ((u 0 0 - 1) * y0 + u 0 1 * y1) ^ 2 := by
      linear_combination (-(y0 ^ 2)) * hN + ((u 0 0 - 1) * y0 ^ 2 + u 0 1 * y0 * y1) * hαδ
    simp only [IsPosUnipotent, hb, false_and, or_false]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

theorem isPosUnipotent_intertwine (a u u'' : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (h : u'' * a = a * u) (htr : u.trace = 2) (hdet : u.det = 1) (htr'' : u''.trace = 2)
    (hdet'' : u''.det = 1) (hu : u ≠ 1) : IsPosUnipotent u ↔ IsPosUnipotent u'' := by

  have hex : ∃ y0 y1 : ℤ, (u 0 0 - 1) * y0 + u 0 1 * y1 ≠ 0 ∨ u 1 0 * y0 + (u 1 1 - 1) * y1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu
    have e0 := hcon 1 0
    have e1 := hcon 0 1
    simp only [mul_one, mul_zero, add_zero, zero_add] at e0 e1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination e0.1
    · linear_combination e1.1
    · linear_combination e0.2
    · linear_combination e1.2
  obtain ⟨y0, y1, hy⟩ := hex

  have hN : (u'' - 1) * a = a * (u - 1) := by rw [sub_mul, mul_sub, one_mul, mul_one, h]
  have hcov := orientForm_intertwine a (u'' - 1) (u - 1) hN y0 y1

  have hy'' : ((u'' 0 0 - 1) * (a 0 0 * y0 + a 0 1 * y1) + u'' 0 1 * (a 1 0 * y0 + a 1 1 * y1) ≠ 0 ∨
      u'' 1 0 * (a 0 0 * y0 + a 0 1 * y1) + (u'' 1 1 - 1) * (a 1 0 * y0 + a 1 1 * y1) ≠ 0) := by
    have e := fun i j => congrFun (congrFun hN i) j
    have h00 := e 0 0
    have h01 := e 0 1
    have h10 := e 1 0
    have h11 := e 1 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply] at h00 h01 h10 h11
    simp only [Fin.isValue, ↓reduceIte, OfNat.ofNat_ne_one, Fin.zero_eq_one_iff,
      one_ne_zero, sub_zero] at h00 h01 h10 h11

    by_contra hcon
    push Not at hcon
    obtain ⟨c0, c1⟩ := hcon
    set w0 := (u 0 0 - 1) * y0 + u 0 1 * y1 with hw0
    set w1 := u 1 0 * y0 + (u 1 1 - 1) * y1 with hw1
    have k0 : a 0 0 * w0 + a 0 1 * w1 = 0 := by
      rw [hw0, hw1]; linear_combination c0 - y0 * h00 - y1 * h01
    have k1 : a 1 0 * w0 + a 1 1 * w1 = 0 := by
      rw [hw0, hw1]; linear_combination c1 - y0 * h10 - y1 * h11
    have hd : a.det ≠ 0 := ne_of_gt ha
    rw [Matrix.det_fin_two] at hd
    have hw0z : (a 0 0 * a 1 1 - a 0 1 * a 1 0) * w0 = 0 := by
      linear_combination a 1 1 * k0 - a 0 1 * k1
    have hw1z : (a 0 0 * a 1 1 - a 0 1 * a 1 0) * w1 = 0 := by
      linear_combination a 0 0 * k1 - a 1 0 * k0
    rcases hy with hy | hy
    · exact hy ((mul_eq_zero.mp hw0z).resolve_left hd)
    · exact hy ((mul_eq_zero.mp hw1z).resolve_left hd)
  rw [← orientForm_neg_iff u htr hdet y0 y1 hy, ← orientForm_neg_iff u'' htr'' hdet'' _ _ hy'', hcov]
  constructor
  · intro hneg; exact mul_neg_of_pos_of_neg ha hneg
  · intro hneg
    by_contra hcon
    push Not at hcon
    have : 0 ≤ a.det * orientForm (u - 1) y0 y1 := mul_nonneg ha.le hcon
    exact absurd hneg (not_lt.mpr this)

end Orientation
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

section CoresPrimitive

open MulAction

variable {G : Type*} [Group G] (K : Subgroup G) [Fintype (G ⧸ K)] {R : Type*} [CommRing R]
variable (sec : G ⧸ K → G) (hsec : ∀ q : G ⧸ K, (sec q : G ⧸ K) = q)

include hsec in
omit [Fintype (G ⧸ K)] in
theorem gamma_mem (q : G ⧸ K) (g : G) : (sec q)⁻¹ * g * sec (g⁻¹ • q) ∈ K := by
  have h : ((sec q : G) : G ⧸ K) = ((g * sec (g⁻¹ • q) : G) : G ⧸ K) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe, hsec, hsec, smul_inv_smul]
  rw [mul_assoc]
  exact QuotientGroup.eq.mp h

def gam (q : G ⧸ K) (g : G) : K := ⟨(sec q)⁻¹ * g * sec (g⁻¹ • q), gamma_mem K sec hsec q g⟩

omit [Fintype (G ⧸ K)] in
@[scoped simp] theorem coe_gam (q : G ⧸ K) (g : G) :
    ((gam K sec hsec q g : K) : G) = (sec q)⁻¹ * g * sec (g⁻¹ • q) := rfl

omit [Fintype (G ⧸ K)] in

theorem gam_mul (q : G ⧸ K) (g g' : G) :
    gam K sec hsec q (g * g') = gam K sec hsec q g * gam K sec hsec (g⁻¹ • q) g' := by
  apply Subtype.ext
  simp only [coe_gam, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

def coresFun (x : Additive K →+ R) (g : G) : R := ∑ q : G ⧸ K, x (Additive.ofMul (gam K sec hsec q g))

def HFun (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R) (g : G) : R :=
  ∑ q : G ⧸ K, (h' (gam K sec hsec q g) +
    x (Additive.ofMul (gam K sec hsec q g)) * (y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul (sec q))))

theorem HFun_mul (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R)
    (hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (x (Additive.ofMul k) * y (Additive.ofMul (k' : G)) - y (Additive.ofMul (k : G)) * x (Additive.ofMul k')))
    (g g' : G) :
    HFun K sec hsec h' x y (g * g') = HFun K sec hsec h' x y g + HFun K sec hsec h' x y g' -
      (coresFun K sec hsec x g * y (Additive.ofMul g') - y (Additive.ofMul g) * coresFun K sec hsec x g') := by

  have hb : Function.Bijective (fun q : G ⧸ K => g⁻¹ • q) := MulAction.bijective g⁻¹
  have e1 : HFun K sec hsec h' x y g' = ∑ q : G ⧸ K, (h' (gam K sec hsec (g⁻¹ • q) g') +
      x (Additive.ofMul (gam K sec hsec (g⁻¹ • q) g')) *
        (y (Additive.ofMul (sec (g'⁻¹ • g⁻¹ • q))) + y (Additive.ofMul (sec (g⁻¹ • q))))) := by
    rw [HFun]
    exact (hb.sum_comp (fun q => h' (gam K sec hsec q g') +
      x (Additive.ofMul (gam K sec hsec q g')) *
        (y (Additive.ofMul (sec (g'⁻¹ • q))) + y (Additive.ofMul (sec q))))).symm
  have e2 : coresFun K sec hsec x g' = ∑ q : G ⧸ K, x (Additive.ofMul (gam K sec hsec (g⁻¹ • q) g')) := by
    rw [coresFun]
    exact (hb.sum_comp (fun q => x (Additive.ofMul (gam K sec hsec q g')))).symm
  rw [e1, e2]
  simp only [HFun, coresFun]
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)

  rw [gam_mul, hh', ofMul_mul, map_add, mul_inv_rev, mul_smul]

  have y1 : y (Additive.ofMul ((gam K sec hsec q g : K) : G)) =
      - y (Additive.ofMul (sec q)) + y (Additive.ofMul g) + y (Additive.ofMul (sec (g⁻¹ • q))) := by
    simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
  have y2 : y (Additive.ofMul ((gam K sec hsec (g⁻¹ • q) g' : K) : G)) =
      - y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul g') +
        y (Additive.ofMul (sec (g'⁻¹ • g⁻¹ • q))) := by
    simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
  rw [y1, y2]
  ring

theorem coresFun_eq [K.FiniteIndex] (x : Additive K →+ R) (g : G) :
    coresFun K sec hsec x g =
      Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight x) g) := by
  classical
  let T : K.LeftTransversal := ⟨Set.range sec, Subgroup.isComplement_range_left hsec⟩
  rw [MonoidHom.transfer_def _ T g, Subgroup.leftTransversals.diff, toAdd_prod, coresFun]
  have hinst : (K.fintypeQuotientOfFiniteIndex : Fintype (G ⧸ K)) = ‹Fintype (G ⧸ K)› :=
    Subsingleton.elim _ _
  rw [hinst]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [AddMonoidHom.coe_toMultiplicativeRight]
  simp only [Function.comp_apply, toAdd_ofAdd]
  congr 1
  congr 1
  apply Subtype.ext
  simp only [coe_gam]
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul g T q, smul_eq_mul,
    Subgroup.IsComplement.leftQuotientEquiv_apply hsec, Subgroup.IsComplement.leftQuotientEquiv_apply hsec,
    mul_assoc]

include hsec in
omit [Fintype (G ⧸ K)] in
theorem secChange_mem (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K) :
    (sec q)⁻¹ * sec' q ∈ K := by
  have h : ((sec q : G) : G ⧸ K) = ((sec' q : G) : G ⧸ K) := by rw [hsec, hsec']
  exact QuotientGroup.eq.mp h

def kSec (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K) : K :=
  ⟨(sec q)⁻¹ * sec' q, secChange_mem K sec hsec sec' hsec' q⟩

omit [Fintype (G ⧸ K)] in
@[scoped simp] theorem coe_kSec (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K) :
    ((kSec K sec hsec sec' hsec' q : K) : G) = (sec q)⁻¹ * sec' q := rfl

omit [Fintype (G ⧸ K)] in
theorem gam_secChange (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q) (q : G ⧸ K)
    (g : G) :
    gam K sec' hsec' q g =
      (kSec K sec hsec sec' hsec' q)⁻¹ * gam K sec hsec q g * kSec K sec hsec sec' hsec' (g⁻¹ • q) := by
  apply Subtype.ext
  simp only [coe_gam, Subgroup.coe_mul, Subgroup.coe_inv, coe_kSec, mul_inv_rev, inv_inv]
  group

theorem HFun_secChange (sec' : G ⧸ K → G) (hsec' : ∀ q : G ⧸ K, (sec' q : G ⧸ K) = q)
    (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R)
    (hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (x (Additive.ofMul k) * y (Additive.ofMul (k' : G)) - y (Additive.ofMul (k : G)) * x (Additive.ofMul k')))
    (g : G) :
    HFun K sec' hsec' h' x y g = HFun K sec hsec h' x y g +
      2 * y (Additive.ofMul g) * ∑ q : G ⧸ K, x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) := by
  have hb : Function.Bijective (fun q : G ⧸ K => g⁻¹ • q) := MulAction.bijective g⁻¹

  have h1 : h' 1 = 0 := by
    have h := hh' 1 1
    simp only [mul_one, ofMul_one, map_zero, OneMemClass.coe_one, mul_zero, sub_zero, sub_self] at h
    linear_combination -h
  have hinv : ∀ k : K, h' k⁻¹ = - h' k := by
    intro k
    have h := hh' k k⁻¹
    simp only [mul_inv_cancel, h1, ofMul_inv, map_neg, Subgroup.coe_inv, mul_neg,
      sub_neg_eq_add] at h
    linear_combination -h

  set D : G ⧸ K → R := fun q => x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) *
      y (Additive.ofMul ((kSec K sec hsec sec' hsec' q : K) : G)) +
      2 * y (Additive.ofMul (sec q)) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
      h' (kSec K sec hsec sec' hsec' q) with hD
  have hDsum : ∑ q : G ⧸ K, D (g⁻¹ • q) = ∑ q : G ⧸ K, D q := hb.sum_comp D
  have hκsum : ∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) =
      ∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) :=
    hb.sum_comp (fun q => y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)))

  have hpt : ∀ q : G ⧸ K,
      (h' (gam K sec' hsec' q g) + x (Additive.ofMul (gam K sec' hsec' q g)) *
          (y (Additive.ofMul (sec' (g⁻¹ • q))) + y (Additive.ofMul (sec' q)))) =
      (h' (gam K sec hsec q g) + x (Additive.ofMul (gam K sec hsec q g)) *
          (y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul (sec q)))) +
        (y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
          y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) +
          (D (g⁻¹ • q) - D q)) := by
    intro q
    have hs' : ∀ q, y (Additive.ofMul (sec' q)) =
        y (Additive.ofMul (sec q)) + y (Additive.ofMul ((kSec K sec hsec sec' hsec' q : K) : G)) := by
      intro q
      rw [← map_add, ← ofMul_mul, coe_kSec, mul_inv_cancel_left]
    have hyγ : y (Additive.ofMul ((gam K sec hsec q g : K) : G)) =
        - y (Additive.ofMul (sec q)) + y (Additive.ofMul g) + y (Additive.ofMul (sec (g⁻¹ • q))) := by
      simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
    rw [gam_secChange K sec hsec sec' hsec' q g, hh', hh', hinv, hs' q, hs' (g⁻¹ • q)]
    simp only [ofMul_mul, ofMul_inv, map_add, map_neg, Subgroup.coe_mul, Subgroup.coe_inv, hyγ, hD]
    ring
  calc HFun K sec' hsec' h' x y g
      = ∑ q : G ⧸ K, ((h' (gam K sec hsec q g) + x (Additive.ofMul (gam K sec hsec q g)) *
          (y (Additive.ofMul (sec (g⁻¹ • q))) + y (Additive.ofMul (sec q)))) +
        (y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
          y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) +
          (D (g⁻¹ • q) - D q))) := by
        rw [HFun]
        exact Finset.sum_congr rfl (fun q _ => hpt q)
    _ = HFun K sec hsec h' x y g +
        (∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) +
          ∑ q : G ⧸ K, y (Additive.ofMul g) * x (Additive.ofMul (kSec K sec hsec sec' hsec' (g⁻¹ • q))) +
          (∑ q : G ⧸ K, D (g⁻¹ • q) - ∑ q : G ⧸ K, D q)) := by
        rw [HFun]
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = HFun K sec hsec h' x y g +
        2 * y (Additive.ofMul g) * ∑ q : G ⧸ K, x (Additive.ofMul (kSec K sec hsec sec' hsec' q)) := by
        rw [hDsum, hκsum, sub_self, add_zero, ← two_mul, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_assoc]

theorem HFun_transferFunction_eq [K.FiniteIndex] (u : G)
    [Fintype (Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)))]
    (h' : K → R) (x : Additive K →+ R) (y : Additive G →+ R)
    (hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (x (Additive.ofMul k) * y (Additive.ofMul (k' : G)) - y (Additive.ofMul (k : G)) * x (Additive.ofMul k')))
    (hxv : ∀ o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)),
      x (Additive.ofMul (⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩ : K)) = 0) :
    HFun K (Subgroup.transferFunction K u) (Subgroup.coe_transferFunction u) h' x y u =
      ∑ o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)),
        h' ⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩ := by
  classical
  have h1 : h' 1 = 0 := by
    have h := hh' 1 1
    simp only [mul_one, ofMul_one, map_zero, OneMemClass.coe_one, mul_zero, sub_zero, sub_self] at h
    linear_combination -h

  have hval : ∀ (o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)))
      (k : ZMod (Function.minimalPeriod (u • ·) o.out)),
      u * Subgroup.transferFunction K u (u⁻¹ • ((u ^ (ZMod.cast k : ℤ)) • o.out)) =
        if k = 0 then u ^ Function.minimalPeriod (u • ·) o.out * o.out.out
        else u ^ (ZMod.cast k : ℤ) * o.out.out := by
    intro o k
    have h := Subgroup.transferTransversal_apply'' u o k
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, Subgroup.transferTransversal_apply, smul_eq_mul] at h
    exact h
  have hsecval : ∀ (o : Quotient (orbitRel (Subgroup.zpowers u) (G ⧸ K)))
      (k : ZMod (Function.minimalPeriod (u • ·) o.out)),
      Subgroup.transferFunction K u ((u ^ (ZMod.cast k : ℤ)) • o.out) = u ^ (ZMod.cast k : ℤ) * o.out.out := by
    intro o k
    rw [← Subgroup.transferTransversal_apply, Subgroup.transferTransversal_apply']
  rw [HFun]
  rw [← (Subgroup.quotientEquivSigmaZMod K u).symm.sum_comp, ← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Fintype.sum_congr _ _ (fun o => ?_)
  rw [Fintype.sum_eq_single (0 : ZMod (Function.minimalPeriod (u • ·) o.out))]
  ·
    have hγ : gam K (Subgroup.transferFunction K u) (Subgroup.coe_transferFunction u)
        ((Subgroup.quotientEquivSigmaZMod K u).symm ⟨o, 0⟩) u =
        ⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩ := by
      apply Subtype.ext
      simp only [coe_gam, Subgroup.quotientEquivSigmaZMod_symm_apply]
      rw [mul_assoc, hval o 0, if_pos rfl, hsecval o 0]
      simp only [ZMod.cast_zero, zpow_zero, one_mul, mul_assoc]
    rw [hγ, hxv o, zero_mul, add_zero]
  · intro k hk
    have hγ : gam K (Subgroup.transferFunction K u) (Subgroup.coe_transferFunction u)
        ((Subgroup.quotientEquivSigmaZMod K u).symm ⟨o, k⟩) u = 1 := by
      apply Subtype.ext
      simp only [coe_gam, Subgroup.quotientEquivSigmaZMod_symm_apply, OneMemClass.coe_one]
      rw [mul_assoc, hval o k, if_neg hk, hsecval o k, inv_mul_cancel]
    rw [hγ, h1, ofMul_one, map_zero, zero_mul, add_zero]

theorem coresFun_subtype (χ : Additive G →+ R) (g : G) :
    coresFun K sec hsec (χ.comp (MonoidHom.toAdditive K.subtype)) g =
      (Fintype.card (G ⧸ K) : R) * χ (Additive.ofMul g) := by
  have hb : Function.Bijective (fun q : G ⧸ K => g⁻¹ • q) := MulAction.bijective g⁻¹
  have hsum : ∑ q : G ⧸ K, χ (Additive.ofMul (sec (g⁻¹ • q))) = ∑ q : G ⧸ K, χ (Additive.ofMul (sec q)) :=
    hb.sum_comp (fun q => χ (Additive.ofMul (sec q)))
  have hpt : ∀ q : G ⧸ K, (χ.comp (MonoidHom.toAdditive K.subtype)) (Additive.ofMul (gam K sec hsec q g)) =
      - χ (Additive.ofMul (sec q)) + χ (Additive.ofMul g) + χ (Additive.ofMul (sec (g⁻¹ • q))) := by
    intro q
    show χ (Additive.ofMul ((gam K sec hsec q g : K) : G)) = _
    simp only [coe_gam, ofMul_mul, ofMul_inv, map_add, map_neg]
  rw [coresFun, Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end CoresPrimitive
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

section Rows

open MulAction

def IsPar (Φ : Subgroup SL(2, ℤ)) {A : Type*} [AddCommGroup A] (φ : Additive Φ →+ A) : Prop :=
  ∀ γ : Φ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0

variable {R : Type*} [CommRing R]

def parSub (Φ : Subgroup SL(2, ℤ)) (R : Type*) [CommRing R] : Submodule R (Additive Φ →+ R) where
  carrier := {φ | IsPar Φ φ}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    show φ (Additive.ofMul γ) + ψ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    show c • φ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, smul_zero]

theorem monoidHom_SL2Z_eq_one [Invertible (6 : R)] (f : SL(2, ℤ) →* Multiplicative R) : f = 1 := by
  have hS4 : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by decide
  have hST6 : (ModularGroup.S * ModularGroup.T) ^ 6 = (1 : SL(2, ℤ)) := by decide
  have hinv6 : ⅟(6 : R) * 6 = 1 := invOf_mul_self _
  set a : R := Multiplicative.toAdd (f ModularGroup.S) with ha_def
  set b : R := Multiplicative.toAdd (f ModularGroup.T) with hb_def
  have h1 : (4 : R) * a = 0 := by
    have h := congrArg (fun x : SL(2, ℤ) => Multiplicative.toAdd (f x)) hS4
    simp only [map_pow, toAdd_pow, map_one, toAdd_one] at h
    simpa [nsmul_eq_mul] using h
  have h2 : (6 : R) * a + 6 * b = 0 := by
    have h := congrArg (fun x : SL(2, ℤ) => Multiplicative.toAdd (f x)) hST6
    simp only [map_pow, map_mul, toAdd_pow, toAdd_mul, map_one, toAdd_one] at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_add] at h
    linear_combination h
  have ha : a = 0 := by
    linear_combination (9 * ⅟(6 : R) ^ 2) * h1 + (-6 * ⅟(6 : R) * a - a) * hinv6
  have hb : b = 0 := by
    rw [ha, mul_zero, zero_add] at h2
    linear_combination ⅟(6 : R) * h2 + (-b) * hinv6
  have hfS : f ModularGroup.S = 1 := by
    rw [← ofAdd_toAdd (f ModularGroup.S), ← ha_def, ha, ofAdd_zero]
  have hfT : f ModularGroup.T = 1 := by
    rw [← ofAdd_toAdd (f ModularGroup.T), ← hb_def, hb, ofAdd_zero]
  refine MonoidHom.ext (fun g => ?_)
  have hg : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  rw [MonoidHom.one_apply]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hfS
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hfT
  | one => exact map_one f
  | mul x y _ _ hx hy => rw [map_mul, hx, hy, mul_one]
  | inv x _ hx => rw [map_inv, hx, inv_one]

theorem cuspSum_character_eq_zero (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [Invertible (6 : R)]
    (χ : Additive Φ →+ R) : cuspSum Φ (fun g => χ (Additive.ofMul g)) = 0 := by
  classical
  have key := MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot
    (AddMonoidHom.toMultiplicativeRight χ) ModularGroup.T
  have htriv : MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight χ) =
      (1 : SL(2, ℤ) →* Multiplicative R) := monoidHom_SL2Z_eq_one _
  rw [htriv, MonoidHom.one_apply] at key
  have key2 := congrArg Multiplicative.toAdd key
  rw [toAdd_one, toAdd_prod] at key2
  rw [cuspSum]
  refine Eq.trans ?_ key2.symm
  refine Finset.sum_congr rfl (fun q _ => ?_)
  simp [cuspGen]

theorem cuspSum_eq_zero_of_map_mul (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [Invertible (6 : R)]
    (d : Φ → R) (hd : ∀ g g', d (g * g') = d g + d g') : cuspSum Φ d = 0 := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    rw [one_mul] at h
    linear_combination -h
  let χ : Additive Φ →+ R :=
    { toFun := fun x => d (Additive.toMul x)
      map_zero' := hd1
      map_add' := fun x y => hd (Additive.toMul x) (Additive.toMul y) }
  exact cuspSum_character_eq_zero Φ χ

theorem cuspSum_sub (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (f g : Φ → R) :
    cuspSum Φ (f - g) = cuspSum Φ f - cuspSum Φ g := by
  simp [cuspSum, Finset.sum_sub_distrib]

theorem cuspSum_primitive_congr (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [Invertible (6 : R)]
    (f f' : Φ → R) (c : Φ → Φ → R) (hf : ∀ g g', f (g * g') = f g + f g' - c g g')
    (hf' : ∀ g g', f' (g * g') = f' g + f' g' - c g g') : cuspSum Φ f = cuspSum Φ f' := by
  have h := cuspSum_eq_zero_of_map_mul Φ (f - f') (by
    intro g g'
    simp only [Pi.sub_apply, hf, hf']
    ring)
  rwa [cuspSum_sub, sub_eq_zero] at h

theorem pairF_instIndep (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (inst₁ inst₂ : IsFreeGroup Φ) [Invertible (2 : R)] [Invertible (6 : R)] (φ ψ : Additive Φ →+ R) :
    @pairF Φ _ R _ inst₁ _ φ ψ = @pairF Φ _ R _ inst₂ _ φ ψ := by
  unfold pairF
  rw [cuspSum_primitive_congr Φ (@hPrim Φ _ R _ inst₁ φ ψ) (@hPrim Φ _ R _ inst₂ φ ψ) (omega φ ψ)
    (@hPrim_mul Φ _ R _ inst₁ φ ψ) (@hPrim_mul Φ _ R _ inst₂ φ ψ)]

theorem omega_self {Φ : Type*} [Group Φ] (φ : Additive Φ →+ R) (g g' : Φ) : omega φ φ g g' = 0 := by
  simp only [omega]
  ring

theorem pairF_add_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (φ₁ φ₂ ψ : Additive Φ →+ R) :
    pairF Φ (φ₁ + φ₂) ψ = pairF Φ φ₁ ψ + pairF Φ φ₂ ψ := by
  have h := cuspSum_primitive_congr Φ (hPrim (φ₁ + φ₂) ψ) (hPrim φ₁ ψ + hPrim φ₂ ψ)
    (omega (φ₁ + φ₂) ψ) (hPrim_mul _ _) (by
      intro g g'
      simp only [Pi.add_apply, hPrim_mul, omega_add_left]
      ring)
  rw [pairF, pairF, pairF, h, cuspSum_add]
  ring

theorem pairF_smul_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (r : R) (φ ψ : Additive Φ →+ R) :
    pairF Φ (r • φ) ψ = r * pairF Φ φ ψ := by
  have h := cuspSum_primitive_congr Φ (hPrim (r • φ) ψ) (r • hPrim φ ψ)
    (omega (r • φ) ψ) (hPrim_mul _ _) (by
      intro g g'
      simp only [Pi.smul_apply, smul_eq_mul, hPrim_mul, omega_smul_left]
      ring)
  rw [pairF, pairF, h, cuspSum_smul]
  ring

theorem pairF_swap (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (φ ψ : Additive Φ →+ R) : pairF Φ ψ φ = - pairF Φ φ ψ := by
  have h := cuspSum_primitive_congr Φ (hPrim ψ φ) (-hPrim φ ψ)
    (omega ψ φ) (hPrim_mul _ _) (by
      intro g g'
      simp only [Pi.neg_apply, hPrim_mul, omega_swap φ ψ]
      ring)
  have hneg : cuspSum Φ (-hPrim φ ψ) = - cuspSum Φ (hPrim φ ψ) := by
    simp [cuspSum, Finset.sum_neg_distrib]
  rw [pairF, pairF, h, hneg]
  ring

theorem pairF_self (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (φ : Additive Φ →+ R) : pairF Φ φ φ = 0 := by
  have h := cuspSum_eq_zero_of_map_mul Φ (hPrim φ φ) (by
    intro g g'
    rw [hPrim_mul, omega_self, sub_zero])
  rw [pairF, h, mul_zero]

noncomputable def cores {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex]
    (x : Additive Φ' →+ R) : Additive Φ →+ R :=
  MonoidHom.toAdditiveLeft
    (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom))))

def res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) (y : Additive Φ →+ R) : Additive Φ' →+ R :=
  y.comp (MonoidHom.toAdditive (Subgroup.inclusion h))

def IsParabolicElt {Φ : Subgroup SL(2, ℤ)} (v : Φ) : Prop :=
  ((v : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4

theorem cusp_tower (Φ' Φ : Subgroup SL(2, ℤ)) (hle : Φ' ≤ Φ) [Φ.FiniteIndex] [Φ'.FiniteIndex] :
    ∃ e : Cusp Φ' ≃ Σ q : Cusp Φ,
        Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ Φ'.subgroupOf Φ)),
      ∀ (q : Cusp Φ) (o : Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ Φ'.subgroupOf Φ))),
        ∃ c' : Φ',
          ((cuspGen Φ' (e.symm ⟨q, o⟩) : Φ') : SL(2, ℤ)) =
            (c' : SL(2, ℤ)) *
              (((o.out.out : Φ) : SL(2, ℤ))⁻¹ *
                ((cuspGen Φ q : Φ) : SL(2, ℤ)) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out *
                ((o.out.out : Φ) : SL(2, ℤ))) *
              (c' : SL(2, ℤ))⁻¹ := by
  exact ModularCurve.PDPairing.CuspTower.cusp_tower_abstract ModularGroup.T hle

theorem inv_conj_pow {G : Type*} [Group G] (a b : G) (i : ℕ) : (a⁻¹ * b * a) ^ i = a⁻¹ * b ^ i * a := by
  have h := @conj_pow G _ i a⁻¹ b
  simpa using h

theorem trace_conj_T_pow (a : SL(2, ℤ)) (n : ℕ) :
    ((a⁻¹ * ModularGroup.T ^ n * a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mul,
    ← zpow_natCast]
  have h := ModularGroup.coe_T_zpow (n : ℤ)
  rw [show ((ModularGroup.T ^ (n : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (ModularGroup.T ^ (n : ℤ)).1
    from rfl, h, Matrix.trace_fin_two_of]
  ring

theorem trace_conj_pow_cuspGen (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (q : Cusp Φ) (c : SL(2, ℤ)) (m : ℕ) :
    ((c⁻¹ * ((cuspGen Φ q : Φ) : SL(2, ℤ)) ^ m * c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  have hu : ((cuspGen Φ q : Φ) : SL(2, ℤ)) =
      q.out.out⁻¹ * ModularGroup.T ^ (Function.minimalPeriod (ModularGroup.T • ·) q.out) * q.out.out := rfl
  rw [hu, inv_conj_pow, ← pow_mul]
  have e : c⁻¹ * (q.out.out⁻¹ * ModularGroup.T ^ (Function.minimalPeriod (ModularGroup.T • ·) q.out * m) *
      q.out.out) * c = (q.out.out * c)⁻¹ *
        ModularGroup.T ^ (Function.minimalPeriod (ModularGroup.T • ·) q.out * m) * (q.out.out * c) := by
    group
  rw [e]
  exact trace_conj_T_pow _ _

theorem isParabolicElt_cuspGen (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (q : Cusp Φ) :
    IsParabolicElt (cuspGen Φ q) := by
  have h := trace_conj_pow_cuspGen Φ q 1 1
  simp only [inv_one, pow_one, one_mul, mul_one] at h
  unfold IsParabolicElt
  rw [h]
  norm_num

theorem pairF_cores_left {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ.FiniteIndex] [Φ'.FiniteIndex]
    [IsFreeGroup Φ] [IsFreeGroup Φ'] [Invertible (2 : R)]
    [Invertible (6 : R)] (x : Additive Φ' →+ R) (y : Additive Φ →+ R)
    (hx : IsPar Φ' x) (hy : IsPar Φ y) :
    pairF Φ (cores h x) y = pairF Φ' x (res h y) := by
  classical

  set K : Subgroup Φ := Φ'.subgroupOf Φ with hK
  haveI : Fintype (Φ ⧸ K) := Fintype.ofFinite _
  haveI hFq : ∀ u : Φ, Fintype (Quotient (orbitRel (Subgroup.zpowers u) (Φ ⧸ K))) :=
    fun u => Fintype.ofFinite _
  let e : K ≃* Φ' := Subgroup.subgroupOfEquivOfLe h
  let f : Φ' → R := hPrim x (res h y)
  let h' : K → R := fun k => f (e k)
  let xK : Additive K →+ R := x.comp (MonoidHom.toAdditive e.toMonoidHom)

  have hh' : ∀ k k' : K, h' (k * k') = h' k + h' k' -
      (xK (Additive.ofMul k) * y (Additive.ofMul ((k' : Φ))) - y (Additive.ofMul (k : Φ)) * xK (Additive.ofMul k')) := by
    intro k k'
    show f (e (k * k')) = f (e k) + f (e k') - _
    rw [map_mul]
    show hPrim x (res h y) (e k * e k') = _
    rw [hPrim_mul]
    rfl

  have hf_conj : ∀ (c v : Φ'), IsParabolicElt v → f (c * v * c⁻¹) = f v := by
    intro c v hv
    exact hPrim_conj_of_apply_eq_zero x (res h y) v (hx v hv) (hy (Subgroup.inclusion h v) hv) c

  have hcor : ∀ g : Φ, coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q) xK g =
      (cores h x) (Additive.ofMul g) := by
    intro g
    rw [coresFun_eq]
    rfl
  have stepA : cuspSum Φ (hPrim (cores h x) y) =
      cuspSum Φ (HFun K Quotient.out (fun q => QuotientGroup.out_eq' q) h' xK y) := by
    refine cuspSum_primitive_congr Φ _ _ (omega (cores h x) y) (hPrim_mul _ _) ?_
    intro g g'
    rw [HFun_mul K Quotient.out (fun q => QuotientGroup.out_eq' q) h' xK y hh' g g', hcor, hcor]
    rfl

  have stepB : ∀ q : Cusp Φ,
      HFun K Quotient.out (fun q => QuotientGroup.out_eq' q) h' xK y (cuspGen Φ q) =
        ∑ o : Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ K)),
          h' ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out,
            QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩ := by
    intro q
    have hyu : y (Additive.ofMul (cuspGen Φ q)) = 0 := hy _ (isParabolicElt_cuspGen Φ q)
    have hsc := HFun_secChange K (Subgroup.transferFunction K (cuspGen Φ q))
      (Subgroup.coe_transferFunction (cuspGen Φ q)) Quotient.out (fun q => QuotientGroup.out_eq' q)
      h' xK y hh' (cuspGen Φ q)
    rw [hyu, mul_zero, zero_mul, add_zero] at hsc
    rw [hsc]
    refine HFun_transferFunction_eq K (cuspGen Φ q) h' xK y hh' ?_
    intro o

    show x (Additive.ofMul (e ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out *
      o.out.out, QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩)) = 0
    apply hx
    show (( (o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out : Φ) :
      SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, trace_conj_pow_cuspGen]
    norm_num

  obtain ⟨E, hE⟩ := cusp_tower Φ' Φ h
  have stepC : cuspSum Φ' f =
      ∑ q : Cusp Φ, ∑ o : Quotient (orbitRel (Subgroup.zpowers (cuspGen Φ q)) (Φ ⧸ K)),
        h' ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩ := by
    rw [cuspSum, ← E.symm.sum_comp, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun o _ => ?_))
    obtain ⟨c', hc'⟩ := hE q o

    have hv : cuspGen Φ' (E.symm ⟨q, o⟩) =
        c' * e ⟨o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem K (cuspGen Φ q) o.out⟩ * c'⁻¹ := by
      apply Subtype.ext
      rw [hc']
      rfl
    rw [hv, hf_conj]
    ·
      show (( (o.out.out⁻¹ * (cuspGen Φ q) ^ Function.minimalPeriod ((cuspGen Φ q) • ·) o.out * o.out.out : Φ) :
        SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, trace_conj_pow_cuspGen]
      norm_num

  rw [pairF, pairF, stepA, cuspSum, Finset.sum_congr rfl (fun q _ => stepB q), ← stepC]

section PlusMinus
open Matrix Matrix.SpecialLinearGroup ModularGroup

theorem conj_entries (b u : SL(2, ℤ)) (i j : Fin 2) :
    (b * u * b⁻¹) i j = ∑ l, ∑ k, b i k * u k l * (adjugate (b : Matrix (Fin 2) (Fin 2) ℤ)) l j := by
  rw [coe_mul, coe_mul, coe_inv, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]

theorem unipotent_normal_form (u : SL(2, ℤ)) (htr : (u : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) (hu : u ≠ 1) :
    ∃ (b : SL(2, ℤ)) (m : ℤ), m ≠ 0 ∧ u = b⁻¹ * T ^ m * b := by

  have hdet : (u : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := u.2
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet

  have hN : (u 0 0 - 1) * (u 1 1 - 1) - u 0 1 * u 1 0 = 0 := by linear_combination hdet - htr
  have hαδ : (u 0 0 - 1) + (u 1 1 - 1) = 0 := by linear_combination htr

  have hex : ∃ v0 v1 : ℤ, (v0 ≠ 0 ∨ v1 ≠ 0) ∧ (u 0 0 - 1) * v0 + u 0 1 * v1 = 0 ∧
      u 1 0 * v0 + (u 1 1 - 1) * v1 = 0 := by
    by_cases hc : u 0 0 - 1 = 0 ∧ u 1 0 = 0
    ·
      refine ⟨1, 0, Or.inl one_ne_zero, ?_, ?_⟩
      · rw [hc.1]; ring
      · rw [hc.2]; ring
    ·
      refine ⟨u 0 0 - 1, u 1 0, ?_, ?_, ?_⟩
      · by_contra hcon
        push Not at hcon
        exact hc hcon
      · linear_combination (u 0 0 - 1) * hαδ - hN
      · linear_combination (u 1 0) * hαδ
  obtain ⟨v0, v1, hv, hk0, hk1⟩ := hex

  have hg : 0 < Int.gcd v0 v1 := Int.gcd_pos_iff.mpr hv
  obtain ⟨w0, w1, hw, hv0, hv1⟩ := Int.exists_gcd_one hg
  set d : ℤ := (Int.gcd v0 v1 : ℤ) with hd
  have hd0 : d ≠ 0 := by rw [hd]; exact_mod_cast hg.ne'
  have hk0' : (u 0 0 - 1) * w0 + u 0 1 * w1 = 0 := by
    have : d * ((u 0 0 - 1) * w0 + u 0 1 * w1) = 0 := by
      rw [hv0, hv1] at hk0; linear_combination hk0
    exact (mul_eq_zero.mp this).resolve_left hd0
  have hk1' : u 1 0 * w0 + (u 1 1 - 1) * w1 = 0 := by
    have : d * (u 1 0 * w0 + (u 1 1 - 1) * w1) = 0 := by
      rw [hv0, hv1] at hk1; linear_combination hk1
    exact (mul_eq_zero.mp this).resolve_left hd0

  have hcop : IsCoprime w0 w1 := Int.isCoprime_iff_gcd_eq_one.mpr hw
  obtain ⟨a', b', hab⟩ := hcop

  let bM : Matrix (Fin 2) (Fin 2) ℤ := !![a', b'; -w1, w0]
  have hbdet : bM.det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hab
  let b : SL(2, ℤ) := ⟨bM, hbdet⟩

  set w : SL(2, ℤ) := b * u * b⁻¹ with hwdef
  have hb00 : b 0 0 = a' := rfl
  have hb01 : b 0 1 = b' := rfl
  have hb10 : b 1 0 = -w1 := rfl
  have hb11 : b 1 1 = w0 := rfl
  have hadj : adjugate (b : Matrix (Fin 2) (Fin 2) ℤ) = !![w0, -b'; w1, a'] := by
    rw [show (b : Matrix (Fin 2) (Fin 2) ℤ) = !![a', b'; -w1, w0] from rfl, Matrix.adjugate_fin_two_of]
    simp
  have hw00 : w 0 0 = 1 := by
    rw [hwdef, conj_entries]
    simp only [Fin.sum_univ_two, hadj, hb00, hb01, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination a' * hk0' + b' * hk1' + hab
  have hw10 : w 1 0 = 0 := by
    rw [hwdef, conj_entries]
    simp only [Fin.sum_univ_two, hadj, hb10, hb11, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination (-w1) * hk0' + w0 * hk1'
  have hwdet : (w : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := w.2
  rw [Matrix.det_fin_two] at hwdet
  have hw11 : w 1 1 = 1 := by
    have : w 0 0 * w 1 1 - w 0 1 * w 1 0 = 1 := hwdet
    rw [hw00, hw10] at this
    linear_combination this

  have hwT : w = T ^ (w 0 1) := by
    apply Subtype.ext
    rw [show ((T ^ (w 0 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (w 0 1)).1 from rfl, coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · exact hw00
    · rfl
    · exact hw10
    · exact hw11
  refine ⟨b, w 0 1, ?_, ?_⟩
  · intro hm
    apply hu
    have : w = 1 := by rw [hwT, hm, zpow_zero]

    have hu' : u = b⁻¹ * w * b := by rw [hwdef]; group
    rw [hu', this, mul_one, inv_mul_cancel]
  · rw [← hwT, hwdef]
    group

theorem centralizer_T_zpow (m : ℤ) (hm : m ≠ 0) (g : SL(2, ℤ)) (hg : g * T ^ m = T ^ m * g) :
    ∃ j : ℤ, g = T ^ j ∨ g = -T ^ j := by

  have e := fun i j => congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) i j) hg
  have hTm : ((T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m; 0, 1] := coe_T_zpow m
  simp only [coe_mul, hTm] at e
  have e00 := e 0 0
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e10 e11

  have hg10 : g 1 0 = 0 := by
    have : m * g 1 0 = 0 := by linear_combination -e00
    exact (mul_eq_zero.mp this).resolve_left hm

  have e01 := e 0 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e01
  have hdiag : g 0 0 = g 1 1 := by
    have : m * (g 0 0 - g 1 1) = 0 := by linear_combination e01
    linear_combination (mul_eq_zero.mp this).resolve_left hm
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.2
  rw [Matrix.det_fin_two, hg10, mul_zero, sub_zero, ← hdiag] at hdet

  have hsq : g 0 0 * g 0 0 = 1 := hdet
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · refine ⟨g 0 1, Or.inl ?_⟩
    have h11 : g 1 1 = 1 := by rw [← hdiag]; exact h1
    apply Subtype.ext
    rw [show ((T ^ (g 0 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (g 0 1)).1 from rfl, coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simp
    · simpa using hg10
    · simpa using h11
  · refine ⟨-(g 0 1), Or.inr ?_⟩
    have h11 : g 1 1 = -1 := by rw [← hdiag]; exact h1
    apply Subtype.ext
    rw [coe_neg, show ((T ^ (-(g 0 1)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (-(g 0 1))).1 from rfl,
      coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simp
    · simpa using hg10
    · simpa using h11

theorem T_zpow_intertwine (m m' : ℤ) (hm : m ≠ 0) (g : SL(2, ℤ)) (hg : g * T ^ m = T ^ m' * g) :
    m = m' ∧ ∃ j : ℤ, g = T ^ j ∨ g = -T ^ j := by
  have e := fun i j => congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) i j) hg
  have hTm : ((T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m; 0, 1] := coe_T_zpow m
  have hTm' : ((T ^ m' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, m'; 0, 1] := coe_T_zpow m'
  simp only [coe_mul, hTm, hTm'] at e
  have e00 := e 0 0
  have e01 := e 0 1
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e11

  have hg10 : g 1 0 = 0 := by
    have : m * g 1 0 = 0 := by linear_combination e11
    exact (mul_eq_zero.mp this).resolve_left hm
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := g.2
  rw [Matrix.det_fin_two, hg10, mul_zero, sub_zero] at hdet

  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hmm : m = m' := by
      have : g 0 0 * m = m' * g 1 1 := by linear_combination e01
      rw [h0, h1] at this; linear_combination this
    refine ⟨hmm, g 0 1, Or.inl ?_⟩
    apply Subtype.ext
    rw [show ((T ^ (g 0 1) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (g 0 1)).1 from rfl, coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h0
    · simp
    · simpa using hg10
    · simpa using h1
  · have hmm : m = m' := by
      have : g 0 0 * m = m' * g 1 1 := by linear_combination e01
      rw [h0, h1] at this; linear_combination -this
    refine ⟨hmm, -(g 0 1), Or.inr ?_⟩
    apply Subtype.ext
    rw [coe_neg, show ((T ^ (-(g 0 1)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (-(g 0 1))).1 from rfl,
      coe_T_zpow]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h0
    · simp
    · simpa using hg10
    · simpa using h1

private def _root_.ModularCurve.PDPairing.TD.pm (Φ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Φ ∨ -g ∈ Φ}
  one_mem' := Or.inl Φ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Φ.mul_mem ha hb)
    · right
      have h := Φ.mul_mem ha hb
      rwa [mul_neg] at h
    · right
      have h := Φ.mul_mem ha hb
      rwa [neg_mul] at h
    · left
      have h := Φ.mul_mem ha hb
      rwa [neg_mul, mul_neg, neg_neg] at h
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Φ.inv_mem ha)
    · right
      have h := Φ.inv_mem ha
      have hinv : (-a)⁻¹ = -a⁻¹ := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
      rwa [hinv] at h

p2m_export "ModularCurve.PDPairing.TD" "pm"
theorem le_pm (Φ : Subgroup SL(2, ℤ)) : Φ ≤ pm Φ := fun _ hg => Or.inl hg

theorem mem_pm_iff (Φ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : g ∈ pm Φ ↔ g ∈ Φ ∨ -g ∈ Φ := Iff.rfl

theorem sanPM_pm_eq (Φ : Subgroup SL(2, ℤ)) : ModularCurve.PDPairing.SanPM.pm Φ = pm Φ := rfl

scoped instance pm_finiteIndex (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] : (pm Φ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pm Φ)

def cuspOf (Δ : Subgroup SL(2, ℤ)) (b : SL(2, ℤ)) : Cusp Δ :=
  Quotient.mk (MulAction.orbitRel (Subgroup.zpowers T) (SL(2, ℤ) ⧸ Δ)) (b : SL(2, ℤ) ⧸ Δ)

theorem cuspOf_T_zpow_mul (Δ : Subgroup SL(2, ℤ)) (j : ℤ) (b : SL(2, ℤ)) : cuspOf Δ (T ^ j * b) = cuspOf Δ b := by
  apply Quotient.sound
  show ((T ^ j * b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) ∈ MulAction.orbit (Subgroup.zpowers T) ((b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ)
  rw [MulAction.mem_orbit_iff]
  exact ⟨⟨T ^ j, Subgroup.zpow_mem_zpowers T j⟩, rfl⟩

theorem cuspOf_mul_mem (Δ : Subgroup SL(2, ℤ)) (b δ : SL(2, ℤ)) (hδ : δ ∈ Δ) : cuspOf Δ (b * δ) = cuspOf Δ b := by
  unfold cuspOf
  rw [QuotientGroup.mk_mul_of_mem b hδ]

theorem cuspOf_neg (Δ : Subgroup SL(2, ℤ)) (hΔ : (-1 : SL(2, ℤ)) ∈ Δ) (b : SL(2, ℤ)) : cuspOf Δ (-b) = cuspOf Δ b := by
  rw [← mul_neg_one]
  exact cuspOf_mul_mem Δ b (-1) hΔ

theorem cuspOf_out (Δ : Subgroup SL(2, ℤ)) (q : Cusp Δ) : cuspOf Δ q.out.out = q := by
  unfold cuspOf
  rw [QuotientGroup.out_eq', Quotient.out_eq]

theorem minimalPeriod_T_zpow_smul (Δ : Subgroup SL(2, ℤ)) (i : ℤ) (x : SL(2, ℤ) ⧸ Δ) :
    Function.minimalPeriod (T • ·) (T ^ i • x) = Function.minimalPeriod (T • ·) x := by
  have key : ∀ n : ℕ, (T ^ n • (T ^ i • x) = T ^ i • x) ↔ (T ^ n • x = x) := by
    intro n
    rw [smul_smul, show T ^ n * T ^ i = T ^ i * T ^ n from by
      rw [← zpow_natCast]; exact zpow_mul_comm T (n : ℤ) i, ← smul_smul]
    exact (MulAction.injective (T ^ i)).eq_iff
  apply Nat.dvd_antisymm
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, key, MulAction.pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, ← key, MulAction.pow_smul_eq_iff_minimalPeriod_dvd]

theorem cuspOf_out_out (Δ : Subgroup SL(2, ℤ)) (b : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Δ ∧ ∃ i : ℤ, (cuspOf Δ b).out.out = T ^ i * b * δ ∧
      Function.minimalPeriod (T • ·) (cuspOf Δ b).out =
        Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) := by
  have h1 : (cuspOf Δ b).out ∈ MulAction.orbit (Subgroup.zpowers T) (b : SL(2, ℤ) ⧸ Δ) := by
    rw [← MulAction.orbitRel_apply]
    exact Quotient.exact ((Quotient.out_eq (cuspOf Δ b)).trans rfl)
  rw [MulAction.mem_orbit_iff] at h1
  obtain ⟨⟨t, ht⟩, hx⟩ := h1
  rw [Subgroup.mem_zpowers_iff] at ht
  obtain ⟨i, rfl⟩ := ht
  have hx' : (cuspOf Δ b).out = ((T ^ i * b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) := by
    rw [← hx]; rfl
  have h2 : ((T ^ i * b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Δ) = ((cuspOf Δ b).out.out : SL(2, ℤ) ⧸ Δ) := by
    rw [QuotientGroup.out_eq', hx']
  have h3 := QuotientGroup.eq.mp h2
  refine ⟨(T ^ i * b)⁻¹ * (cuspOf Δ b).out.out, h3, i, ?_, ?_⟩
  · group
  · rw [hx']
    show Function.minimalPeriod (T • ·) (T ^ i • (b : SL(2, ℤ) ⧸ Δ)) = _
    exact minimalPeriod_T_zpow_smul Δ i _

theorem cuspGen_cuspOf (Δ : Subgroup SL(2, ℤ)) [Δ.FiniteIndex] (b : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Δ ∧ ((cuspGen Δ (cuspOf Δ b) : Δ) : SL(2, ℤ)) =
      δ⁻¹ * (b⁻¹ * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * b) * δ := by
  obtain ⟨δ, hδ, i, hc, hm⟩ := cuspOf_out_out Δ b
  refine ⟨δ, hδ, ?_⟩
  show (cuspOf Δ b).out.out⁻¹ * T ^ Function.minimalPeriod (T • ·) (cuspOf Δ b).out * (cuspOf Δ b).out.out = _
  rw [hm, hc]
  have hcomm : T ^ (-i) * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * T ^ i =
      T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) := by
    rw [← zpow_natCast, ← zpow_add, ← zpow_add]
    congr 1
    ring
  calc (T ^ i * b * δ)⁻¹ * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * (T ^ i * b * δ)
      = δ⁻¹ * (b⁻¹ * (T ^ (-i) * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * T ^ i) * b) * δ := by
        group
    _ = δ⁻¹ * (b⁻¹ * T ^ Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ Δ) * b) * δ := by rw [hcomm]

noncomputable def pmRep (Φ : Subgroup SL(2, ℤ)) (g : pm Φ) : Φ := by
  classical
  exact if h : (g : SL(2, ℤ)) ∈ Φ then ⟨g, h⟩ else ⟨-(g : SL(2, ℤ)), g.2.resolve_left h⟩

theorem trace_intertwine (a V V'' : Matrix (Fin 2) (Fin 2) ℤ) (ha : a.det ≠ 0) (h : a * V = V'' * a) :
    V''.trace = V.trace := by
  have e := fun i j => congrFun (congrFun h i) j
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at ha
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  have key : (a 0 0 * a 1 1 - a 0 1 * a 1 0) * ((V'' 0 0 + V'' 1 1) - (V 0 0 + V 1 1)) = 0 := by
    linear_combination (-(a 1 1)) * h00 + (a 1 0) * h01 + (a 0 1) * h10 + (-(a 0 0)) * h11
  have := (mul_eq_zero.mp key).resolve_left ha
  linear_combination this

theorem pmRep_parabolic {Φ : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] (q : Cusp (pm Φ)) :
    IsParabolicElt (pmRep Φ (cuspGen (pm Φ) q)) := by
  classical
  have h2 : (((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 :=
    isParabolicElt_cuspGen (pm Φ) q
  unfold IsParabolicElt pmRep
  split_ifs with h
  · exact h2
  · show ((-((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [coe_neg, Matrix.trace_neg, neg_sq]
    exact h2

theorem cancel_det {a M M' : Matrix (Fin 2) (Fin 2) ℤ} (ha : a.det ≠ 0) (h : a * M = a * M') : M = M' := by
  have h0 : a * (M - M') = 0 := by rw [Matrix.mul_sub, h, sub_self]
  have h2 : a.det • (M - M') = 0 := by
    calc a.det • (M - M') = (a.det • (1 : Matrix (Fin 2) (Fin 2) ℤ)) * (M - M') := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = adjugate a * a * (M - M') := by rw [Matrix.adjugate_mul]
      _ = adjugate a * (a * (M - M')) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [h0, Matrix.mul_zero]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left ha)

theorem cancel_det_right {a M M' : Matrix (Fin 2) (Fin 2) ℤ} (ha : a.det ≠ 0) (h : M * a = M' * a) : M = M' := by
  have h0 : (M - M') * a = 0 := by rw [Matrix.sub_mul, h, sub_self]
  have h2 : a.det • (M - M') = 0 := by
    calc a.det • (M - M') = (M - M') * (a.det • (1 : Matrix (Fin 2) (Fin 2) ℤ)) := by
          rw [Matrix.mul_smul, Matrix.mul_one]
      _ = (M - M') * (a * adjugate a) := by rw [Matrix.mul_adjugate]
      _ = (M - M') * a * adjugate a := (Matrix.mul_assoc _ _ _).symm
      _ = 0 := by rw [h0, Matrix.zero_mul]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_left ha)

theorem intertwine_pow (a : Matrix (Fin 2) (Fin 2) ℤ) (u w : SL(2, ℤ))
    (h : a * (u : Matrix (Fin 2) (Fin 2) ℤ) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a) (n : ℕ) :
    a * ((u ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((w ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, coe_mul, coe_mul, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

theorem intertwine_inv (a : Matrix (Fin 2) (Fin 2) ℤ) (u w : SL(2, ℤ))
    (h : a * (u : Matrix (Fin 2) (Fin 2) ℤ) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a) :
    a * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  have hu : (u : Matrix (Fin 2) (Fin 2) ℤ) * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hw : ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (w : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [← coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  calc a * ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (w : Matrix (Fin 2) (Fin 2) ℤ) * a *
          ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [hw, Matrix.one_mul]
    _ = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (a * (u : Matrix (Fin 2) (Fin 2) ℤ)) *
          ((u⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [h, Matrix.mul_assoc _ _ a]
    _ = ((w⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hu, Matrix.mul_one]

theorem intertwine_zpow (a : Matrix (Fin 2) (Fin 2) ℤ) (u w : SL(2, ℤ))
    (h : a * (u : Matrix (Fin 2) (Fin 2) ℤ) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a) (k : ℤ) :
    a * ((u ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((w ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  rcases k with (n | n)
  · rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]; exact intertwine_pow a u w h n
  · rw [zpow_negSucc, zpow_negSucc]; exact intertwine_inv a _ _ (intertwine_pow a u w h (n + 1))

theorem T_zpow_ne_neg_T_zpow (i j : ℤ) : (T ^ i : SL(2, ℤ)) ≠ -T ^ j := by
  intro h
  have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp only [coe_neg, Matrix.neg_apply] at this
  rw [show ((T ^ i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ i).1 from rfl,
    show ((T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ j).1 from rfl, coe_T_zpow, coe_T_zpow] at this
  simp at this

theorem T_zpow_injective (i j : ℤ) (h : (T ^ i : SL(2, ℤ)) = T ^ j) : i = j := by
  have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
  rw [show ((T ^ i : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ i).1 from rfl,
    show ((T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ j).1 from rfl, coe_T_zpow, coe_T_zpow] at this
  simpa using this

theorem neg_mem_pm {Φ : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} (hg : g ∈ pm Φ) : -g ∈ pm Φ := by
  rcases hg with h | h
  · right; rwa [neg_neg]
  · left; exact h

theorem neg_one_mem_pm (Φ : Subgroup SL(2, ℤ)) : (-1 : SL(2, ℤ)) ∈ pm Φ := Or.inr (by rw [neg_neg]; exact Φ.one_mem)

theorem pmRep_spec (Φ : Subgroup SL(2, ℤ)) (g : pm Φ) :
    ((pmRep Φ g : Φ) : SL(2, ℤ)) = g ∨ ((pmRep Φ g : Φ) : SL(2, ℤ)) = -(g : SL(2, ℤ)) := by
  classical
  unfold pmRep
  split_ifs with h
  · left; rfl
  · right; rfl

theorem pmRep_unique {Φ : Subgroup SL(2, ℤ)} (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (g : pm Φ) (x : Φ)
    (hx : (x : SL(2, ℤ)) = g ∨ (x : SL(2, ℤ)) = -(g : SL(2, ℤ))) : x = pmRep Φ g := by

  have key : ∀ y z : Φ, ((y : SL(2, ℤ)) = z ∨ (y : SL(2, ℤ)) = -(z : SL(2, ℤ))) → y = z := by
    intro y z hyz
    rcases hyz with h | h
    · exact Subtype.ext h
    · exfalso
      apply hΦ
      have : (y : SL(2, ℤ)) * (z : SL(2, ℤ))⁻¹ = -1 := by rw [h, neg_mul, mul_inv_cancel]
      rw [← this]
      exact Φ.mul_mem y.2 (Φ.inv_mem z.2)
  apply key
  rcases hx with h1 | h1 <;> rcases pmRep_spec Φ g with h2 | h2
  · left; rw [h1, h2]
  · right; rw [h1, h2, neg_neg]
  · right; rw [h1, h2]
  · left; rw [h1, h2]

theorem pmRep_conj {Φ : Subgroup SL(2, ℤ)} (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (δ x : pm Φ) :
    pmRep Φ (δ⁻¹ * x * δ) = (pmRep Φ δ)⁻¹ * pmRep Φ x * pmRep Φ δ := by
  symm
  apply pmRep_unique hΦ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rcases pmRep_spec Φ δ with hd | hd <;> rcases pmRep_spec Φ x with hx | hx <;> rw [hd, hx]
  · left; rfl
  · right; simp [mul_neg, neg_mul]
  · left
    have hinv : (-(δ : SL(2, ℤ)))⁻¹ = -(δ : SL(2, ℤ))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
    rw [hinv]; simp [mul_neg, neg_mul]
  · right
    have hinv : (-(δ : SL(2, ℤ)))⁻¹ = -(δ : SL(2, ℤ))⁻¹ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
    rw [hinv]; simp [mul_neg, neg_mul]

noncomputable def pmLift {Φ Φ'' : Subgroup SL(2, ℤ)} (e : Φ ≃* Φ'') (g : pm Φ) : SL(2, ℤ) := by
  classical
  exact if h : (g : SL(2, ℤ)) ∈ Φ then ((e ⟨g, h⟩ : Φ'') : SL(2, ℤ))
    else -((e ⟨-(g : SL(2, ℤ)), g.2.resolve_left h⟩ : Φ'') : SL(2, ℤ))

theorem pmLift_mem {Φ Φ'' : Subgroup SL(2, ℤ)} (e : Φ ≃* Φ'') (g : pm Φ) : pmLift e g ∈ pm Φ'' := by
  classical
  unfold pmLift
  split_ifs with h
  · exact Or.inl (e ⟨g, h⟩).2
  · right; rw [neg_neg]; exact (e _).2

theorem pmLift_intertwine {Φ Φ'' : Subgroup SL(2, ℤ)} (e : Φ ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) (g : pm Φ) :
    a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = ((pmLift e g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
  classical
  unfold pmLift
  split_ifs with h
  · exact he ⟨g, h⟩
  · have h1 := he ⟨-(g : SL(2, ℤ)), g.2.resolve_left h⟩
    simp only [coe_neg, Matrix.mul_neg] at h1
    rw [coe_neg, Matrix.neg_mul, ← h1, neg_neg]

theorem pmRep_pmLift {Φ Φ'' : Subgroup SL(2, ℤ)} (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'') (g : pm Φ) :
    pmRep Φ'' ⟨pmLift e g, pmLift_mem e g⟩ = e (pmRep Φ g) := by
  classical
  symm
  apply pmRep_unique hΦ''
  show ((e (pmRep Φ g) : Φ'') : SL(2, ℤ)) = pmLift e g ∨ ((e (pmRep Φ g) : Φ'') : SL(2, ℤ)) = -pmLift e g
  unfold pmRep pmLift
  split_ifs with h
  · left; rfl
  · right; rw [neg_neg]

theorem minimalPeriod_T_pos (Δ : Subgroup SL(2, ℤ)) [Δ.FiniteIndex] (x : SL(2, ℤ) ⧸ Δ) :
    0 < Function.minimalPeriod (T • ·) x := by
  exact Function.minimalPeriod_pos_of_mem_periodicPts ((MulAction.injective T).mem_periodicPts x)

theorem centralizer_cuspGen_pm (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (q : Cusp (pm Φ)) (z : SL(2, ℤ))
    (hz : z ∈ pm Φ) (hcomm : z * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) = ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * z) :
    ∃ k : ℤ, z = ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) ^ k ∨ z = -((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) ^ k := by
  set c : SL(2, ℤ) := q.out.out with hcdef
  set m : ℕ := Function.minimalPeriod (T • ·) q.out with hmdef
  have hu : ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) = c⁻¹ * T ^ m * c := rfl
  have hm : 0 < m := minimalPeriod_T_pos (pm Φ) q.out
  have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'

  have hg : (c * z * c⁻¹) * T ^ (m : ℤ) = T ^ (m : ℤ) * (c * z * c⁻¹) := by
    have hT : T ^ (m : ℤ) = c * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * c⁻¹ := by rw [hu, zpow_natCast]; group
    rw [hT]
    calc c * z * c⁻¹ * (c * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * c⁻¹)
        = c * (z * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ))) * c⁻¹ := by group
      _ = c * (((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * z) * c⁻¹ := by rw [hcomm]
      _ = c * ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) * c⁻¹ * (c * z * c⁻¹) := by group
  obtain ⟨j, hj⟩ := centralizer_T_zpow (m : ℤ) hmz (c * z * c⁻¹) hg

  have hmem : c⁻¹ * T ^ j * c ∈ pm Φ := by
    rcases hj with h | h
    · have : c⁻¹ * T ^ j * c = z := by rw [← h]; group
      rw [this]; exact hz
    · have : c⁻¹ * T ^ j * c = -z := by
        rw [show z = c⁻¹ * (c * z * c⁻¹) * c from by group, h]
        simp [mul_neg, neg_mul]
      rw [this]; exact neg_mem_pm hz
  have hfix : T ^ j • q.out = q.out := by
    have hc : (c : SL(2, ℤ) ⧸ pm Φ) = q.out := QuotientGroup.out_eq' q.out
    rw [← hc, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have : (T ^ j * c)⁻¹ * c = (c⁻¹ * T ^ j * c)⁻¹ := by group
    rw [this]
    exact (pm Φ).inv_mem hmem
  have hdvd : (m : ℤ) ∣ j := (MulAction.zpow_smul_eq_iff_minimalPeriod_dvd).mp hfix
  obtain ⟨k, hk⟩ := hdvd
  have hpow : c⁻¹ * T ^ j * c = ((cuspGen (pm Φ) q : pm Φ) : SL(2, ℤ)) ^ k := by
    rw [hu, hk, zpow_mul, zpow_natCast]
    have := @conj_zpow SL(2, ℤ) _ k c⁻¹ (T ^ m)
    simp only [inv_inv] at this
    exact this.symm
  refine ⟨k, ?_⟩
  rcases hj with h | h
  · left
    rw [← hpow, ← h]; group
  · right
    rw [← hpow]
    have : z = c⁻¹ * (c * z * c⁻¹) * c := by group
    rw [this, h]
    simp [mul_neg, neg_mul]

theorem hat_spec {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (_hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (_hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) (q : Cusp (pm Φ)) :
    ∃ (b : SL(2, ℤ)) (m' : ℤ), 0 < m' ∧ pmLift e (cuspGen (pm Φ) q) = b⁻¹ * T ^ m' * b ∧
      (Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ pm Φ'') : ℤ) = m' := by
  set u : pm Φ := cuspGen (pm Φ) q with hudef
  set c : SL(2, ℤ) := q.out.out with hcdef
  set m : ℕ := Function.minimalPeriod (T • ·) q.out with hmdef
  have hu : ((u : pm Φ) : SL(2, ℤ)) = c⁻¹ * T ^ m * c := rfl
  have hm : 0 < m := minimalPeriod_T_pos (pm Φ) q.out
  set w : SL(2, ℤ) := pmLift e u with hwdef
  have hint : a * ((u : pm Φ) : SL(2, ℤ)) = (w : Matrix (Fin 2) (Fin 2) ℤ) * a := pmLift_intertwine e a he u

  have htru : (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    have h := trace_conj_pow_cuspGen (pm Φ) q 1 1
    simpa using h
  have htrw : (w : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [trace_intertwine a _ _ (ne_of_gt ha) hint]; exact htru
  have hTm_ne : (T ^ m : SL(2, ℤ)) ≠ 1 := by
    intro h
    have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1) h
    rw [← zpow_natCast, show ((T ^ (m : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ (m : ℤ)).1 from rfl,
      coe_T_zpow] at this
    simp at this
    omega
  have hu_ne : ((u : pm Φ) : SL(2, ℤ)) ≠ 1 := by
    rw [hu]; intro h
    apply hTm_ne
    calc (T ^ m : SL(2, ℤ)) = c * (c⁻¹ * T ^ m * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hw_ne : w ≠ 1 := by
    intro h
    apply hu_ne
    apply Subtype.ext
    have h1 : a * (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = a * ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [hint, h, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
    exact cancel_det (ne_of_gt ha) h1

  obtain ⟨b, m', hm'0, hwb⟩ := unipotent_normal_form w htrw hw_ne

  have hposT : ∀ n : ℤ, IsPosUnipotent ((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ↔ 0 < n := by
    intro n
    rw [show ((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ n).1 from rfl, coe_T_zpow]
    simp [IsPosUnipotent]

  have hcu : (c : Matrix (Fin 2) (Fin 2) ℤ) * (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((T ^ (m : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * c := by
    rw [← coe_mul, ← coe_mul, hu, zpow_natCast]
    congr 1; group
  have htrT : ∀ n : ℤ, (((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).trace = 2 := by
    intro n
    rw [show ((T ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ n).1 from rfl, coe_T_zpow,
      Matrix.trace_fin_two_of]; ring
  have hupos : IsPosUnipotent (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    have key := isPosUnipotent_intertwine (c : Matrix (Fin 2) (Fin 2) ℤ)
      (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ((T ^ (m : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (by rw [c.2]; exact one_pos) hcu.symm htru (u : SL(2, ℤ)).2 (htrT _) (T ^ (m : ℤ)).2
      (fun h => hu_ne (Subtype.ext h))
    rw [key, hposT]
    exact_mod_cast hm
  have hwpos : IsPosUnipotent (w : Matrix (Fin 2) (Fin 2) ℤ) := by
    have key := isPosUnipotent_intertwine a (((u : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (w : Matrix (Fin 2) (Fin 2) ℤ) ha hint.symm htru (u : SL(2, ℤ)).2 htrw w.2 (fun h => hu_ne (Subtype.ext h))
    exact key.mp hupos
  have hm'pos : 0 < m' := by

    have hbw : (b : Matrix (Fin 2) (Fin 2) ℤ) * (w : Matrix (Fin 2) (Fin 2) ℤ) =
        ((T ^ m' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * b := by
      rw [← coe_mul, ← coe_mul, hwb]; congr 1; group
    have key := isPosUnipotent_intertwine (b : Matrix (Fin 2) (Fin 2) ℤ)
      (w : Matrix (Fin 2) (Fin 2) ℤ) ((T ^ m' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (by rw [b.2]; exact one_pos)
      hbw.symm htrw w.2 (htrT _) (T ^ m').2 (fun h => hw_ne (Subtype.ext h))
    exact (hposT m').mp (key.mp hwpos)
  refine ⟨b, m', hm'pos, hwb, ?_⟩

  set n : ℕ := Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ pm Φ'') with hndef
  have hwmem : w ∈ pm Φ'' := pmLift_mem e u

  have h1 : (n : ℤ) ∣ m' := by
    rw [← MulAction.zpow_smul_eq_iff_minimalPeriod_dvd, MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have : (T ^ m' * b)⁻¹ * b = (b⁻¹ * T ^ m' * b)⁻¹ := by group
    rw [this, ← hwb]
    exact (pm Φ'').inv_mem hwmem

  have hzmem : b⁻¹ * T ^ n * b ∈ pm Φ'' := by
    have hfix : T ^ n • (b : SL(2, ℤ) ⧸ pm Φ'') = (b : SL(2, ℤ) ⧸ pm Φ'') :=
      (MulAction.pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq] at hfix
    have : (T ^ n * b)⁻¹ * b = (b⁻¹ * T ^ n * b)⁻¹ := by group
    rw [this] at hfix
    exact (Subgroup.inv_mem_iff _).mp hfix
  set z : pm Φ'' := ⟨b⁻¹ * T ^ n * b, hzmem⟩ with hzdef
  set z₀ : Φ'' := pmRep Φ'' z with hz₀def
  set y : Φ := e.symm z₀ with hydef
  have hz₀ : ((z₀ : Φ'') : SL(2, ℤ)) = b⁻¹ * T ^ n * b ∨ ((z₀ : Φ'') : SL(2, ℤ)) = -(b⁻¹ * T ^ n * b) :=
    pmRep_spec Φ'' z

  have hcommz : ((z₀ : Φ'') : SL(2, ℤ)) * w = w * ((z₀ : Φ'') : SL(2, ℤ)) := by
    have base : (b⁻¹ * T ^ n * b) * (b⁻¹ * T ^ m' * b) = (b⁻¹ * T ^ m' * b) * (b⁻¹ * T ^ n * b) := by
      rw [← zpow_natCast]
      calc b⁻¹ * T ^ (n : ℤ) * b * (b⁻¹ * T ^ m' * b) = b⁻¹ * (T ^ (n : ℤ) * T ^ m') * b := by group
        _ = b⁻¹ * (T ^ m' * T ^ (n : ℤ)) * b := by rw [zpow_mul_comm]
        _ = b⁻¹ * T ^ m' * b * (b⁻¹ * T ^ (n : ℤ) * b) := by group
    rw [hwb]
    rcases hz₀ with h | h <;> rw [h]
    · exact base
    · rw [neg_mul, mul_neg, base]

  have hy : a * ((y : Φ) : SL(2, ℤ)) = (((z₀ : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
    have := he y
    rw [hydef, MulEquiv.apply_symm_apply] at this
    rw [hydef]; exact this
  have hcommy : ((y : Φ) : SL(2, ℤ)) * ((u : pm Φ) : SL(2, ℤ)) = ((u : pm Φ) : SL(2, ℤ)) * ((y : Φ) : SL(2, ℤ)) := by
    apply Subtype.ext
    apply cancel_det (ne_of_gt ha)
    rw [coe_mul, coe_mul, ← Matrix.mul_assoc, hy, Matrix.mul_assoc, hint, ← Matrix.mul_assoc, ← coe_mul, hcommz,
      coe_mul, Matrix.mul_assoc, ← hy, ← Matrix.mul_assoc, ← hint, Matrix.mul_assoc]
  obtain ⟨k, hk⟩ := centralizer_cuspGen_pm Φ q ((y : Φ) : SL(2, ℤ)) (le_pm Φ y.2) hcommy

  have hwk : a * (((u : pm Φ) : SL(2, ℤ)) ^ k : SL(2, ℤ)) = ((w ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a :=
    intertwine_zpow a _ _ hint k
  have hz₀wk : ((z₀ : Φ'') : SL(2, ℤ)) = w ^ k ∨ ((z₀ : Φ'') : SL(2, ℤ)) = -w ^ k := by
    rcases hk with h | h
    · left
      apply Subtype.ext
      apply cancel_det_right (ne_of_gt ha)
      rw [← hy, h, hwk]
    · right
      apply Subtype.ext
      apply cancel_det_right (ne_of_gt ha)
      rw [← hy, h, coe_neg, coe_neg, Matrix.mul_neg, hwk, Matrix.neg_mul]

  have hwkb : w ^ k = b⁻¹ * T ^ (m' * k) * b := by
    rw [hwb, zpow_mul]
    have := @conj_zpow SL(2, ℤ) _ k b⁻¹ (T ^ m')
    simp only [inv_inv] at this
    exact this
  have hnk : (n : ℤ) = m' * k := by
    rcases hz₀ with h1' | h1' <;> rcases hz₀wk with h2 | h2
    ·
      apply T_zpow_injective
      rw [zpow_natCast]
      have : b⁻¹ * T ^ n * b = b⁻¹ * T ^ (m' * k) * b := by rw [← h1', h2, hwkb]
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (b⁻¹ * T ^ (m' * k) * b) * b⁻¹ := by rw [this]
        _ = T ^ (m' * k) := by group
    · exfalso
      apply T_zpow_ne_neg_T_zpow (n : ℤ) (m' * k)
      rw [zpow_natCast]
      have : b⁻¹ * T ^ n * b = -(b⁻¹ * T ^ (m' * k) * b) := by rw [← h1', h2, hwkb]
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (-(b⁻¹ * T ^ (m' * k) * b)) * b⁻¹ := by rw [this]
        _ = -T ^ (m' * k) := by simp [mul_neg, neg_mul]; group
    · exfalso
      apply T_zpow_ne_neg_T_zpow (n : ℤ) (m' * k)
      rw [zpow_natCast]
      have : -(b⁻¹ * T ^ n * b) = b⁻¹ * T ^ (m' * k) * b := by rw [← h1', h2, hwkb]
      have this' : b⁻¹ * T ^ n * b = -(b⁻¹ * T ^ (m' * k) * b) := by rw [← this, neg_neg]
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (-(b⁻¹ * T ^ (m' * k) * b)) * b⁻¹ := by rw [this']
        _ = -T ^ (m' * k) := by simp [mul_neg, neg_mul]; group
    · apply T_zpow_injective
      rw [zpow_natCast]
      have : -(b⁻¹ * T ^ n * b) = -(b⁻¹ * T ^ (m' * k) * b) := by rw [← h1', h2, hwkb]
      have this' : b⁻¹ * T ^ n * b = b⁻¹ * T ^ (m' * k) * b := neg_injective this
      calc (T ^ n : SL(2, ℤ)) = b * (b⁻¹ * T ^ n * b) * b⁻¹ := by group
        _ = b * (b⁻¹ * T ^ (m' * k) * b) * b⁻¹ := by rw [this']
        _ = T ^ (m' * k) := by group
  have h2 : m' ∣ (n : ℤ) := ⟨k, hnk⟩
  have hnpos : (0 : ℤ) < n := by exact_mod_cast minimalPeriod_T_pos (pm Φ'') (b : SL(2, ℤ) ⧸ pm Φ'')
  exact Int.dvd_antisymm hnpos.le hm'pos.le h1 h2

theorem hat_roundtrip {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a a' : Matrix (Fin 2) (Fin 2) ℤ) (_ha : 0 < a.det) (_ha' : 0 < a'.det)
    (_he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (_he' : ∀ g : Φ'', a' * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a')
    (q : Cusp (pm Φ)) (b : SL(2, ℤ)) (m' : ℤ)
    (hwb : pmLift e (cuspGen (pm Φ) q) = b⁻¹ * T ^ m' * b)
    (hn : (Function.minimalPeriod (T • ·) (b : SL(2, ℤ) ⧸ pm Φ'') : ℤ) = m')
    (b₂ : SL(2, ℤ)) (m₂ : ℤ) (hm₂ : 0 < m₂)
    (hwb₂ : pmLift e.symm (cuspGen (pm Φ'') (cuspOf (pm Φ'') b)) = b₂⁻¹ * T ^ m₂ * b₂) :
    cuspOf (pm Φ) b₂ = q ∧ ∃ cc : Φ'', pmRep Φ'' (cuspGen (pm Φ'') (cuspOf (pm Φ'') b)) =
      cc * e (pmRep Φ (cuspGen (pm Φ) q)) * cc⁻¹ := by
  set u : pm Φ := cuspGen (pm Φ) q with hudef
  set c : SL(2, ℤ) := q.out.out with hcdef
  set m : ℕ := Function.minimalPeriod (T • ·) q.out with hmdef
  have hu : ((u : pm Φ) : SL(2, ℤ)) = c⁻¹ * T ^ m * c := rfl
  have hm : 0 < m := minimalPeriod_T_pos (pm Φ) q.out

  obtain ⟨δ, hδ, hgen⟩ := cuspGen_cuspOf (pm Φ'') b
  have hgen' : ((cuspGen (pm Φ'') (cuspOf (pm Φ'') b) : pm Φ'') : SL(2, ℤ)) = δ⁻¹ * pmLift e u * δ := by
    rw [hgen, hwb, ← zpow_natCast, hn]
  set u'' : pm Φ'' := cuspGen (pm Φ'') (cuspOf (pm Φ'') b) with hu''def
  have hu''eq : u'' = (⟨δ, hδ⟩ : pm Φ'')⁻¹ * ⟨pmLift e u, pmLift_mem e u⟩ * ⟨δ, hδ⟩ := Subtype.ext hgen'

  have hrep : pmRep Φ'' u'' = (pmRep Φ'' ⟨δ, hδ⟩)⁻¹ * e (pmRep Φ u) * pmRep Φ'' ⟨δ, hδ⟩ := by
    rw [hu''eq, pmRep_conj hΦ'', pmRep_pmLift hΦ'' e u]
  refine ⟨?_, (pmRep Φ'' ⟨δ, hδ⟩)⁻¹, by rw [hrep, inv_inv]⟩

  have hrep₂ : pmRep Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ = e.symm (pmRep Φ'' u'') :=
    pmRep_pmLift hΦ e.symm u''
  rw [hrep, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at hrep₂
  set φ : Φ := e.symm (pmRep Φ'' ⟨δ, hδ⟩) with hφdef

  have hX : ((pmRep Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ : Φ) : SL(2, ℤ)) =
      (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ ∨
      ((pmRep Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ : Φ) : SL(2, ℤ)) =
      -((φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ) := by
    rw [hrep₂]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rcases pmRep_spec Φ u with h2 | h2 <;> rw [h2]
    · left; rfl
    · right; simp [mul_neg, neg_mul]
  have hw₂cases : pmLift e.symm u'' = (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ ∨
      pmLift e.symm u'' = -((φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ) := by
    rcases pmRep_spec Φ ⟨pmLift e.symm u'', pmLift_mem e.symm u''⟩ with h1 | h1 <;> rcases hX with h3 | h3
    · left; exact h1.symm.trans h3
    · right; exact h1.symm.trans h3
    · right
      have h4 : -pmLift e.symm u'' = _ := h1.symm.trans h3
      rw [← neg_neg (pmLift e.symm u''), h4]
    · left
      have h4 : -pmLift e.symm u'' = _ := h1.symm.trans h3
      exact neg_injective h4
  have htrconj : (((φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [hu]
    have : (φ : SL(2, ℤ))⁻¹ * (c⁻¹ * T ^ m * c) * φ = (c * φ)⁻¹ * T ^ m * (c * φ) := by group
    rw [this]; exact trace_conj_T_pow _ _
  have htrb₂ : ((b₂⁻¹ * T ^ m₂ * b₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [coe_mul, coe_mul, Matrix.trace_mul_cycle, ← coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul,
      show ((T ^ m₂ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (T ^ m₂).1 from rfl, coe_T_zpow,
      Matrix.trace_fin_two_of]
    ring
  have htrw₂ : ((pmLift e.symm u'' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
    rw [hwb₂]; exact htrb₂
  have hw₂eq : pmLift e.symm u'' = (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) * φ := by
    rcases hw₂cases with h | h
    · exact h
    · exfalso
      have := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ).trace) h
      simp only [coe_neg, Matrix.trace_neg] at this
      rw [htrw₂, htrconj] at this
      norm_num at this

  have hrig : (c * φ * b₂⁻¹) * T ^ m₂ = T ^ (m : ℤ) * (c * φ * b₂⁻¹) := by
    have h1 : b₂⁻¹ * T ^ m₂ * b₂ = (c * (φ : SL(2, ℤ)))⁻¹ * T ^ (m : ℤ) * (c * φ) := by
      rw [← hwb₂, hw₂eq, hu, zpow_natCast]; group
    calc c * φ * b₂⁻¹ * T ^ m₂ = c * φ * (b₂⁻¹ * T ^ m₂ * b₂) * b₂⁻¹ := by group
      _ = c * φ * ((c * (φ : SL(2, ℤ)))⁻¹ * T ^ (m : ℤ) * (c * φ)) * b₂⁻¹ := by rw [h1]
      _ = T ^ (m : ℤ) * (c * φ * b₂⁻¹) := by group
  obtain ⟨_, j, hj⟩ := T_zpow_intertwine m₂ (m : ℤ) (ne_of_gt hm₂) (c * φ * b₂⁻¹) hrig

  have hφmem : ((φ : Φ) : SL(2, ℤ)) ∈ pm Φ := le_pm Φ φ.2
  have hq : cuspOf (pm Φ) (c * φ) = q := by
    rw [cuspOf_mul_mem (pm Φ) c φ hφmem]
    exact cuspOf_out (pm Φ) q
  rcases hj with h | h
  · have hb₂ : b₂ = T ^ (-j) * (c * φ) := by
      calc b₂ = (c * φ * b₂⁻¹)⁻¹ * (c * φ) := by group
        _ = (T ^ j)⁻¹ * (c * φ) := by rw [h]
        _ = T ^ (-j) * (c * φ) := by rw [zpow_neg]
    rw [hb₂, cuspOf_T_zpow_mul, hq]
  · have hb₂ : b₂ = -(T ^ (-j) * (c * φ)) := by
      have hinv : (-(T ^ j : SL(2, ℤ)))⁻¹ = -(T ^ j)⁻¹ := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
      calc b₂ = (c * φ * b₂⁻¹)⁻¹ * (c * φ) := by group
        _ = (-(T ^ j))⁻¹ * (c * φ) := by rw [h]
        _ = -(T ^ (-j) * (c * φ)) := by rw [hinv, zpow_neg, neg_mul]
    rw [hb₂, cuspOf_neg (pm Φ) (neg_one_mem_pm Φ), cuspOf_T_zpow_mul, hq]

theorem cusp_pm_transport {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) :
    ∃ β : Cusp (pm Φ) ≃ Cusp (pm Φ''), ∀ q : Cusp (pm Φ), ∃ c : Φ'',
      pmRep Φ'' (cuspGen (pm Φ'') (β q)) = c * e (pmRep Φ (cuspGen (pm Φ) q)) * c⁻¹ := by
  classical

  have hane : a.det ≠ 0 := ne_of_gt ha
  have he' : ∀ g : Φ'', adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * adjugate a := by
    intro g
    have h := he (e.symm g)
    rw [MulEquiv.apply_symm_apply] at h

    have h2 : a.det • ((((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * adjugate a) =
        a.det • (adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
      calc a.det • ((((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * adjugate a)
          = (a.det • (1 : Matrix (Fin 2) (Fin 2) ℤ)) * ((((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
              adjugate a) := by rw [Matrix.smul_mul, Matrix.one_mul]
        _ = adjugate a * (a * (((e.symm g : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * adjugate a := by
              rw [← Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = adjugate a * (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a) * adjugate a := by rw [h]
        _ = adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (a * adjugate a) := by
              rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
        _ = a.det • (adjugate a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
              rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
    exact ((smul_right_injective (Matrix (Fin 2) (Fin 2) ℤ) hane) h2).symm
  have ha' : 0 < (adjugate a).det := by
    rw [Matrix.det_adjugate]; simpa using ha

  have S := fun q => hat_spec hΦ hΦ'' e a ha he q
  have S' := fun q'' => hat_spec hΦ'' hΦ e.symm (adjugate a) ha' he' q''
  choose bq mq hmq hwq hnq using S
  choose bq' mq' hmq' hwq' hnq' using S'
  have he'' : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e.symm.symm g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := by
    intro g; rw [MulEquiv.symm_symm]; exact he g
  refine ⟨⟨fun q => cuspOf (pm Φ'') (bq q), fun q'' => cuspOf (pm Φ) (bq' q''), ?_, ?_⟩, ?_⟩
  · intro q
    exact (hat_roundtrip hΦ hΦ'' e a (adjugate a) ha ha' he he' q (bq q) (mq q) (hwq q) (hnq q)
      (bq' (cuspOf (pm Φ'') (bq q))) (mq' _) (hmq' _) (hwq' _)).1
  · intro q''
    have hr := hat_roundtrip hΦ'' hΦ e.symm (adjugate a) a ha' ha he' he'' q'' (bq' q'') (mq' q'') (hwq' q'')
      (hnq' q'') (bq (cuspOf (pm Φ) (bq' q''))) (mq _) (hmq _) (by rw [MulEquiv.symm_symm]; exact hwq _)
    exact hr.1
  · intro q
    exact (hat_roundtrip hΦ hΦ'' e a (adjugate a) ha ha' he he' q (bq q) (mq q) (hwq q) (hnq q)
      (bq' (cuspOf (pm Φ'') (bq q))) (mq' _) (hmq' _) (hwq' _)).2

theorem cuspSum_eq_two_mul_sum_pm (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] (hΦ : (-1 : SL(2, ℤ)) ∉ Φ)
    (F : Φ → R) (hF_conj : ∀ (c v : Φ), IsParabolicElt v → F (c * v * c⁻¹) = F v)
    (hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → F (v ^ k) = k * F v) :
    cuspSum Φ F = 2 * ∑ q : Cusp (pm Φ), F (pmRep Φ (cuspGen (pm Φ) q)) := by
  classical
  set K : Subgroup (pm Φ) := Φ.subgroupOf (pm Φ) with hK
  haveI : Fintype (pm Φ ⧸ K) := Fintype.ofFinite _
  haveI hFq : ∀ u : pm Φ, Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u) (pm Φ ⧸ K))) :=
    fun _ => Fintype.ofFinite _

  have sgn : ∀ y z : Φ, ((y : SL(2, ℤ)) = z ∨ (y : SL(2, ℤ)) = -(z : SL(2, ℤ))) → y = z := by
    intro y z hyz
    rcases hyz with h | h
    · exact Subtype.ext h
    · exfalso
      apply hΦ
      have : (y : SL(2, ℤ)) * (z : SL(2, ℤ))⁻¹ = -1 := by rw [h, neg_mul, mul_inv_cancel]
      rw [← this]
      exact Φ.mul_mem y.2 (Φ.inv_mem z.2)

  have hidx : K.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨-1, neg_one_mem_pm Φ⟩, fun b => ?_⟩
    simp only [hK, Subgroup.mem_subgroupOf, Subgroup.coe_mul, mul_neg, mul_one]
    rcases b.2 with hb | hb
    · right
      refine ⟨hb, fun hnb => hΦ ?_⟩
      have : (-(b : SL(2, ℤ))) * (b : SL(2, ℤ))⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel]
      rw [← this]; exact Φ.mul_mem hnb (Φ.inv_mem hb)
    · left
      refine ⟨hb, fun hb' => hΦ ?_⟩
      have : (-(b : SL(2, ℤ))) * (b : SL(2, ℤ))⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel]
      rw [← this]; exact Φ.mul_mem hb (Φ.inv_mem hb')
  have hcard : Fintype.card (pm Φ ⧸ K) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]; exact hidx
  obtain ⟨E, hE⟩ := cusp_tower Φ (pm Φ) (le_pm Φ)
  rw [cuspSum, ← E.symm.sum_comp, ← Finset.univ_sigma_univ, Finset.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  set u : pm Φ := cuspGen (pm Φ) q with hudef

  have htrk : ∀ (O : SL(2, ℤ)) (k : ℕ),
      ((O⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * O : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
    intro O k
    rw [trace_conj_pow_cuspGen (pm Φ) q O k]; norm_num
  have hupow : ∀ k : ℕ, ((u : pm Φ) : SL(2, ℤ)) ^ k = ((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k ∨
      ((u : pm Φ) : SL(2, ℤ)) ^ k = -((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k := by
    intro k
    rcases pmRep_spec Φ u with h | h
    · left; rw [h]
    · have hu' : ((u : pm Φ) : SL(2, ℤ)) = -((pmRep Φ u : Φ) : SL(2, ℤ)) := by rw [h, neg_neg]
      rw [hu', neg_pow]
      rcases neg_one_pow_eq_or SL(2, ℤ) k with h1 | h1
      · left; rw [h1, one_mul]
      · right; rw [h1, neg_one_mul]
  have hparpow : ∀ k : ℕ, IsParabolicElt ((pmRep Φ u : Φ) ^ k) := by
    intro k
    unfold IsParabolicElt
    have h4 := htrk 1 k
    simp only [inv_one, one_mul, mul_one] at h4
    rw [Subgroup.coe_pow]
    rcases hupow k with h | h
    · rw [← h]; exact h4
    · have : ((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k = -(((u : pm Φ) : SL(2, ℤ)) ^ k) := by rw [h, neg_neg]
      rw [this, coe_neg, Matrix.trace_neg, neg_sq]; exact h4
  have step1 : ∀ o : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (pm Φ ⧸ K)),
      F (cuspGen Φ (E.symm ⟨q, o⟩)) = (Function.minimalPeriod (u • ·) o.out : R) * F (pmRep Φ u) := by
    intro o
    obtain ⟨c', hc'⟩ := hE q o
    set k : ℕ := Function.minimalPeriod (u • ·) o.out with hkdef
    set O : pm Φ := o.out.out with hOdef
    have hvmem : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) ∈ Φ := by
      have h := QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    set v : Φ := ⟨_, hvmem⟩ with hvdef
    have hgen : cuspGen Φ (E.symm ⟨q, o⟩) = c' * v * c'⁻¹ := by
      apply Subtype.ext
      rw [hc']
      rfl
    have hvpar : IsParabolicElt v := htrk O k

    set φ : Φ := pmRep Φ O with hφdef
    have hconj : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) =
        (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * φ := by
      rcases pmRep_spec Φ O with h | h
      · rw [h]
      · have hO : ((O : pm Φ) : SL(2, ℤ)) = -(φ : SL(2, ℤ)) := by rw [h, neg_neg]
        have hinv : (-(φ : SL(2, ℤ)))⁻¹ = -(φ : SL(2, ℤ))⁻¹ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
        rw [hO, hinv, neg_mul, neg_mul, mul_neg, neg_neg]
    have hv : v = φ⁻¹ * (pmRep Φ u) ^ k * φ := by
      apply sgn
      simp only [hvdef, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hconj]
      rcases hupow k with h | h
      · left; rw [h]
      · right; rw [h]; simp [mul_neg, neg_mul]
    rw [hgen, hF_conj c' v hvpar, hv]
    have h2 := hF_conj φ⁻¹ ((pmRep Φ u) ^ k) (hparpow k)
    rw [inv_inv] at h2
    rw [h2, hF_pow _ k (pmRep_parabolic q)]
  rw [Finset.sum_congr rfl (fun o _ => step1 o), ← Finset.sum_mul]
  congr 1

  have step2' : ∑ o : Quotient (MulAction.orbitRel (Subgroup.zpowers u) (pm Φ ⧸ K)),
      (Function.minimalPeriod (u • ·) o.out : ℕ) = Fintype.card (pm Φ ⧸ K) := by
    rw [Fintype.card_congr (MulAction.selfEquivSigmaOrbits (Subgroup.zpowers u) (pm Φ ⧸ K)), Fintype.card_sigma]
    refine Finset.sum_congr rfl (fun o _ => ?_)
    rw [MulAction.minimalPeriod_eq_card]
    exact Fintype.card_congr (Equiv.refl _)
  have step2 := step2'.trans hcard
  have := congrArg (fun n : ℕ => (n : R)) step2
  simpa [Nat.cast_sum] using this

end PlusMinus
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

theorem cuspSum_transport {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (f : Φ'' → R) (hf_conj : ∀ (c v : Φ''), IsParabolicElt v → f (c * v * c⁻¹) = f v)
    (hf_pow : ∀ (v : Φ'') (k : ℕ), IsParabolicElt v → f (v ^ k) = k * f v) :
    cuspSum Φ (f ∘ e) = cuspSum Φ'' f := by

  have hpar : ∀ v : Φ, IsParabolicElt v → IsParabolicElt (e v) := by
    intro v hv
    unfold IsParabolicElt at hv ⊢
    rw [trace_intertwine a _ _ (ne_of_gt ha) (he v)]
    exact hv
  have hF_conj : ∀ (c v : Φ), IsParabolicElt v → (f ∘ e) (c * v * c⁻¹) = (f ∘ e) v := by
    intro c v hv
    show f (e (c * v * c⁻¹)) = f (e v)
    rw [map_mul, map_mul, map_inv]
    exact hf_conj (e c) (e v) (hpar v hv)
  have hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → (f ∘ e) (v ^ k) = k * (f ∘ e) v := by
    intro v k hv
    show f (e (v ^ k)) = k * f (e v)
    rw [map_pow]
    exact hf_pow (e v) k (hpar v hv)
  rw [cuspSum_eq_two_mul_sum_pm Φ hΦ (f ∘ e) hF_conj hF_pow, cuspSum_eq_two_mul_sum_pm Φ'' hΦ'' f hf_conj hf_pow]
  congr 1
  obtain ⟨β, hβ⟩ := cusp_pm_transport hΦ hΦ'' e a ha he
  rw [← β.sum_comp]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  obtain ⟨c, hc⟩ := hβ q
  show f (e (pmRep Φ (cuspGen (pm Φ) q))) = f (pmRep Φ'' (cuspGen (pm Φ'') (β q)))
  rw [hc, hf_conj]
  exact hpar _ (pmRep_parabolic q)

theorem omega_comp {Φ Φ'' : Type*} [Group Φ] [Group Φ''] (e : Φ →* Φ'') (φ ψ : Additive Φ'' →+ R)
    (g g' : Φ) :
    omega (φ.comp (MonoidHom.toAdditive e)) (ψ.comp (MonoidHom.toAdditive e)) g g' =
      omega φ ψ (e g) (e g') := rfl

theorem pairF_transport {Φ Φ'' : Subgroup SL(2, ℤ)} [Φ.FiniteIndex] [Φ''.FiniteIndex] [IsFreeGroup Φ]
    [IsFreeGroup Φ''] [Invertible (2 : R)] [Invertible (6 : R)]
    (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hΦ'' : (-1 : SL(2, ℤ)) ∉ Φ'') (e : Φ ≃* Φ'')
    (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Φ, a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (φ ψ : Additive Φ'' →+ R) (hφ : IsPar Φ'' φ) (hψ : IsPar Φ'' ψ) :
    pairF Φ (φ.comp (MonoidHom.toAdditive e.toMonoidHom)) (ψ.comp (MonoidHom.toAdditive e.toMonoidHom)) =
      pairF Φ'' φ ψ := by
  have step1 : cuspSum Φ (hPrim (φ.comp (MonoidHom.toAdditive e.toMonoidHom))
      (ψ.comp (MonoidHom.toAdditive e.toMonoidHom))) = cuspSum Φ (hPrim φ ψ ∘ e) := by
    refine cuspSum_primitive_congr Φ _ _
      (omega (φ.comp (MonoidHom.toAdditive e.toMonoidHom)) (ψ.comp (MonoidHom.toAdditive e.toMonoidHom)))
      (hPrim_mul _ _) ?_
    intro g g'
    show hPrim φ ψ (e (g * g')) = hPrim φ ψ (e g) + hPrim φ ψ (e g') - _
    rw [map_mul, hPrim_mul]
    rfl
  have step2 : cuspSum Φ (hPrim φ ψ ∘ e) = cuspSum Φ'' (hPrim φ ψ) := by
    refine cuspSum_transport hΦ hΦ'' e a ha he (hPrim φ ψ) ?_ ?_
    · intro c v hv
      exact hPrim_conj_of_apply_eq_zero φ ψ v (hφ v hv) (hψ v hv) c
    · intro v k _
      exact hPrim_pow φ ψ v k
  rw [pairF, pairF, step1, step2]

theorem isPar_res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) (y : Additive Φ →+ R) (hy : IsPar Φ y) :
    IsPar Φ' (res h y) := by
  intro γ hγ
  exact hy (Subgroup.inclusion h γ) hγ

theorem cores_res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (a : Additive Φ →+ R) :
    cores h (res h a) = ((Φ'.relIndex Φ : ℕ) : R) • a := by
  classical
  haveI : Fintype (Φ ⧸ Φ'.subgroupOf Φ) := Fintype.ofFinite _
  apply AddMonoidHom.ext
  intro g'

  obtain ⟨g, rfl⟩ : ∃ g : Φ, Additive.ofMul g = g' := ⟨Additive.toMul g', rfl⟩
  have key := coresFun_eq (Φ'.subgroupOf Φ) (Quotient.out) (fun q => QuotientGroup.out_eq' q)
    (a.comp (MonoidHom.toAdditive (Φ'.subgroupOf Φ).subtype)) g
  rw [coresFun_subtype] at key
  have hcard : (Fintype.card (Φ ⧸ Φ'.subgroupOf Φ) : R) = ((Φ'.relIndex Φ : ℕ) : R) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  rw [AddMonoidHom.smul_apply, smul_eq_mul, ← hcard, key, cores]
  rfl

theorem pairF_res_res {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ.FiniteIndex] [Φ'.FiniteIndex]
    [IsFreeGroup Φ] [IsFreeGroup Φ'] [Invertible (2 : R)] [Invertible (6 : R)]
    (a b : Additive Φ →+ R) (ha : IsPar Φ a) (hb : IsPar Φ b) :
    pairF Φ' (res h a) (res h b) = ((Φ'.relIndex Φ : ℕ) : R) * pairF Φ a b := by
  rw [← pairF_smul_left, ← cores_res h a]
  exact (pairF_cores_left h (res h a) b (isPar_res h a ha) hb).symm

example (Λ₁ Λ₂ Γ : Subgroup SL(2, ℤ)) [IsFreeGroup Λ₂] : IsFreeGroup ↥(Γ ⊓ Λ₁ ⊓ Λ₂) := inferInstance

theorem pairD_indep (Λ₁ Λ₂ : Subgroup SL(2, ℤ)) [Λ₁.FiniteIndex] [Λ₂.FiniteIndex] [IsFreeGroup Λ₁]
    [IsFreeGroup Λ₂] (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] [Invertible (2 : R)] [Invertible (6 : R)]
    [Invertible (((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R)] [Invertible (((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R)]
    [Invertible (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R)]
    (φ ψ : Additive Γ →+ R) (hφ : IsPar Γ φ) (hψ : IsPar Γ ψ) :
    pairD Λ₁ Γ φ ψ = pairD Λ₂ Γ φ ψ := by

  have h1 : Γ ⊓ Λ₁ ⊓ Λ₂ ≤ Γ ⊓ Λ₁ := inf_le_left
  have h2 : Γ ⊓ Λ₁ ⊓ Λ₂ ≤ Γ ⊓ Λ₂ := le_inf (le_trans inf_le_left inf_le_left) inf_le_right
  haveI : IsFreeGroup ↥(Γ ⊓ Λ₁ ⊓ Λ₂) := inferInstance
  have hpar1 : ∀ χ : Additive Γ →+ R, IsPar Γ χ → IsPar (Γ ⊓ Λ₁) (resInf Λ₁ Γ χ) :=
    fun χ hχ γ hγ => hχ _ hγ
  have hpar2 : ∀ χ : Additive Γ →+ R, IsPar Γ χ → IsPar (Γ ⊓ Λ₂) (resInf Λ₂ Γ χ) :=
    fun χ hχ γ hγ => hχ _ hγ

  have hres : ∀ χ : Additive Γ →+ R, res h1 (resInf Λ₁ Γ χ) = res h2 (resInf Λ₂ Γ χ) := by
    intro χ; rfl
  have e1 := pairF_res_res h1 (resInf Λ₁ Γ φ) (resInf Λ₁ Γ ψ) (hpar1 φ hφ) (hpar1 ψ hψ)
  have e2 := pairF_res_res h2 (resInf Λ₂ Γ φ) (resInf Λ₂ Γ ψ) (hpar2 φ hφ) (hpar2 ψ hψ)
  rw [hres φ, hres ψ] at e1

  have hN1 : ((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₁)) * ((Γ ⊓ Λ₁).relIndex Γ) = (Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ :=
    Subgroup.relIndex_mul_relIndex (Γ ⊓ Λ₁ ⊓ Λ₂) (Γ ⊓ Λ₁) Γ h1 inf_le_left
  have hN2 : ((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₂)) * ((Γ ⊓ Λ₂).relIndex Γ) = (Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ :=
    Subgroup.relIndex_mul_relIndex (Γ ⊓ Λ₁ ⊓ Λ₂) (Γ ⊓ Λ₂) Γ h2 inf_le_left
  unfold pairD
  set m₁ : R := (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₁) : ℕ) : R) with hm₁
  set m₂ : R := (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex (Γ ⊓ Λ₂) : ℕ) : R) with hm₂
  have hN1' : m₁ * (((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) = (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) := by
    rw [hm₁, ← Nat.cast_mul, hN1]
  have hN2' : m₂ * (((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) = (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) := by
    rw [hm₂, ← Nat.cast_mul, hN2]
  have hiN : ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) = 1 :=
    invOf_mul_self _
  set P₁ := pairF (Γ ⊓ Λ₁) (resInf Λ₁ Γ φ) (resInf Λ₁ Γ ψ) with hP₁
  set P₂ := pairF (Γ ⊓ Λ₂) (resInf Λ₂ Γ φ) (resInf Λ₂ Γ ψ) with hP₂
  set P := pairF (Γ ⊓ Λ₁ ⊓ Λ₂) (res h2 (resInf Λ₂ Γ φ)) (res h2 (resInf Λ₂ Γ ψ)) with hP

  have k1 : (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁) = P := by
    calc (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁)
        = m₁ * ((((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * ⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R)) * P₁ := by
          rw [← hN1']; ring
      _ = m₁ * P₁ := by rw [mul_invOf_self, mul_one]
      _ = P := e1.symm
  have k2 : (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂) = P := by
    calc (((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂)
        = m₂ * ((((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * ⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R)) * P₂ := by
          rw [← hN2']; ring
      _ = m₂ * P₂ := by rw [mul_invOf_self, mul_one]
      _ = P := e2.symm
  calc ⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁
      = ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) *
          ((((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₁).relIndex Γ : ℕ) : R) * P₁)) := by
        rw [← mul_assoc, hiN, one_mul]
    _ = ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P := by rw [k1]
    _ = ⅟(((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) *
          ((((Γ ⊓ Λ₁ ⊓ Λ₂).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂)) := by rw [k2]
    _ = ⅟(((Γ ⊓ Λ₂).relIndex Γ : ℕ) : R) * P₂ := by rw [← mul_assoc, hiN, one_mul]

end Rows
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

section CDS3Group

open CongruenceSubgroup MulAction Function

variable {R : Type*} [CommRing R]

noncomputable def orbitTransl {G X : Type*} [Group G] [MulAction G X] (g u u' : G) (hu : u' = g⁻¹ * u * g) :
    Quotient (orbitRel (Subgroup.zpowers u') X) ≃ Quotient (orbitRel (Subgroup.zpowers u) X) :=
  Quotient.congr (MulAction.toPerm g) fun a b => by
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    have hpow : ∀ n : ℤ, u' ^ n = g⁻¹ * u ^ n * g := fun n => by
      rw [hu]
      have := @conj_zpow G _ n g⁻¹ u
      simpa using this
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp s.2
      refine ⟨⟨u ^ n, Subgroup.zpow_mem_zpowers u n⟩, ?_⟩
      show u ^ n • g • b = g • a
      have hs' : u' ^ n • b = a := hn ▸ hs
      rw [← hs', hpow, mul_smul, mul_smul, smul_inv_smul]
    · rintro ⟨s, hs⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp s.2
      refine ⟨⟨u' ^ n, Subgroup.zpow_mem_zpowers u' n⟩, ?_⟩
      show u' ^ n • b = a
      have hs' : u ^ n • g • b = g • a := hn ▸ hs
      rw [hpow, mul_smul, mul_smul, hs', inv_smul_smul]

theorem orbitTransl_mk {G X : Type*} [Group G] [MulAction G X] (g u u' : G) (hu : u' = g⁻¹ * u * g) (x : X) :
    orbitTransl g u u' hu (Quotient.mk _ x) = Quotient.mk _ (g • x) := rfl

theorem minimalPeriod_transl {G X : Type*} [Group G] [MulAction G X] (g u u' : G) (hu : u' = g⁻¹ * u * g) (x : X) :
    minimalPeriod (u • ·) (g • x) = minimalPeriod (u' • ·) x := by
  have hiter : ∀ n : ℕ, u ^ n • g • x = g • (u' ^ n • x) := fun n => by
    rw [hu, inv_conj_pow, mul_smul, mul_smul, smul_inv_smul]
  apply Nat.dvd_antisymm <;> rw [← pow_smul_eq_iff_minimalPeriod_dvd]
  · rw [hiter]; exact congrArg _ ((pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl)
  · have h' := (pow_smul_eq_iff_minimalPeriod_dvd (a := u) (b := g • x)
      (n := minimalPeriod (u • ·) (g • x))).mpr dvd_rfl
    rw [hiter] at h'
    exact smul_left_cancel g h'

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex]

omit [Φ.FiniteIndex] in

theorem conj_pow_minimalPeriod_mem (u p : ↥(Gamma 2)) :
    ((p⁻¹ * u ^ minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p : ↥(Gamma 2)) : SL(2, ℤ)) ∈ pm Φ := by
  have h := (pow_smul_eq_iff_minimalPeriod_dvd (a := u) (b := ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))
    (n := minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))).mpr dvd_rfl
  rw [Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, Subgroup.mem_subgroupOf] at h

  rw [← Subgroup.inv_mem_iff]
  convert h using 1
  push_cast
  group

noncomputable def faceVal (F : Φ → R) (u p : ↥(Gamma 2)) : R :=
  F (pmRep Φ ⟨_, conj_pow_minimalPeriod_mem Φ u p⟩)

theorem sq_trace_neg (M : Matrix (Fin 2) (Fin 2) ℤ) : (-M).trace ^ 2 = M.trace ^ 2 := by
  rw [Matrix.trace_neg, neg_sq]

theorem sq_trace_conj_pow_SL (b a : SL(2, ℤ)) (k : ℕ) (ha : ((a : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    ((b⁻¹ * a ^ k * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  exact sq_trace_pow_eq_four a ha k

omit [Φ.FiniteIndex] in
theorem isParabolicElt_pmRep (x : pm Φ) (hx : (((x : pm Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) :
    IsParabolicElt (pmRep Φ x) := by
  unfold IsParabolicElt
  rcases pmRep_spec Φ x with h | h
  · rw [h]; exact hx
  · rw [h, Matrix.SpecialLinearGroup.coe_neg, sq_trace_neg]; exact hx

variable {Φ}

omit [Φ.FiniteIndex] [CommRing R] in

theorem faceVal_eq_of_same_orbit (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (F : Φ → R)
    (hF_conj : ∀ (c v : Φ), IsParabolicElt v → F (c * v * c⁻¹) = F v)
    (u : ↥(Gamma 2)) (hu : (((u : ↥(Gamma 2)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4)
    (p p' : ↥(Gamma 2))
    (h : ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈ orbit (Subgroup.zpowers u) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) :
    faceVal Φ F u p' = faceVal Φ F u p := by
  rw [mem_orbit_iff] at h
  obtain ⟨s, hs⟩ := h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp s.2
  have hs' : u ^ j • ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := hj ▸ hs

  have hk : minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [← hs']
    exact ModularCurve.PDPairing.CuspTower.minimalPeriod_zpow_smul u j _

  have hφ : (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)) ∈ pm Φ := by
    rw [Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, Subgroup.mem_subgroupOf] at hs'
    exact hs'
  set k := minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) with hkdef
  set φ : pm Φ := ⟨_, hφ⟩ with hφdef
  set X : pm Φ := ⟨_, conj_pow_minimalPeriod_mem Φ u p⟩ with hXdef
  have hX' : (⟨_, conj_pow_minimalPeriod_mem Φ u p'⟩ : pm Φ) = φ⁻¹ * X * φ := by
    apply Subtype.ext
    show (((p'⁻¹ * u ^ minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p' : ↥(Gamma 2)) : SL(2, ℤ))) =
      ((((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)))⁻¹ *
        ((p⁻¹ * u ^ minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p : ↥(Gamma 2)) : SL(2, ℤ)) *
        (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ))
    rw [hk]
    push_cast
    rw [← zpow_natCast]
    group
  unfold faceVal
  rw [hX', pmRep_conj hΦ φ X]
  have hpar : IsParabolicElt (pmRep Φ X) := by
    apply isParabolicElt_pmRep
    show ((((p⁻¹ * u ^ k * p : ↥(Gamma 2)) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    push_cast
    exact sq_trace_conj_pow_SL _ _ _ hu
  have := hF_conj (pmRep Φ φ)⁻¹ (pmRep Φ X) hpar
  rw [inv_inv] at this
  exact this

variable (Φ)

theorem ustd_mem (i : Fin 3) : ModularCurve.PDPairing.BaseTwo.ustd i ∈ Gamma 2 :=
  (ModularCurve.PDPairing.BaseTwo.mem_Gamma_two_iff _).mpr (ModularCurve.PDPairing.BaseTwo.red2_ustd i)

def U (i : Fin 3) : ↥(Gamma 2) := ⟨ModularCurve.PDPairing.BaseTwo.ustd i, ustd_mem i⟩

theorem sq_trace_U (i : Fin 3) : (((U i : ↥(Gamma 2)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  fin_cases i
  · show ((ModularCurve.PDPairing.BaseTwo.ustd 0 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_zero]; simp [Matrix.trace_fin_two_of]
  · show ((ModularCurve.PDPairing.BaseTwo.ustd 1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_one]; simp [Matrix.trace_fin_two_of]
  · show ((ModularCurve.PDPairing.BaseTwo.ustd 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
    rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_two]; simp [Matrix.trace_fin_two_of]

theorem Gamma_two_cusps_TD :
    ∃ e : Cusp (Gamma 2) ≃ Fin 3, ∀ q : Cusp (Gamma 2), ∃ γ : SL(2, ℤ), γ ∈ Gamma 2 ∧
      ((cuspGen (Gamma 2) q : Gamma 2) : SL(2, ℤ)) = γ⁻¹ * ModularCurve.PDPairing.BaseTwo.ustd (e q) * γ :=
  ModularCurve.PDPairing.BaseTwo.Gamma_two_cusps

abbrev OrbitU (i : Fin 3) : Type := Quotient (orbitRel (Subgroup.zpowers (U i)) (↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))

theorem cuspSum_eq_two_mul_sum_orbitU (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hle : Φ ≤ Gamma 2) [Invertible (6 : R)]
    (F : Φ → R) (hF_conj : ∀ (c v : Φ), IsParabolicElt v → F (c * v * c⁻¹) = F v)
    (hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → F (v ^ k) = k * F v) :
    cuspSum Φ F = 2 * ∑ i : Fin 3, ∑ O : OrbitU Φ i, faceVal Φ F (U i) O.out.out := by
  have hle' : pm Φ ≤ Gamma 2 := by
    intro g hg
    rcases hg with hg | hg
    · exact hle hg
    · have := hle hg
      have h1 : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
        rw [Gamma_mem]; decide
      simpa using Subgroup.mul_mem _ h1 this
  rw [cuspSum_eq_two_mul_sum_pm Φ hΦ F hF_conj hF_pow]
  congr 1

  obtain ⟨e₁, he₁⟩ := cusp_tower (pm Φ) (Gamma 2) hle'
  obtain ⟨e₂, he₂⟩ := Gamma_two_cusps_TD
  rw [Fintype.sum_equiv e₁ _ (fun qo => F (pmRep Φ (cuspGen (pm Φ) (e₁.symm qo)))) (fun q => by simp),
    Fintype.sum_sigma]

  have inner : ∀ q₂ : Cusp (Gamma 2),
      ∑ o, F (pmRep Φ (cuspGen (pm Φ) (e₁.symm ⟨q₂, o⟩))) = ∑ O : OrbitU Φ (e₂ q₂), faceVal Φ F (U (e₂ q₂)) O.out.out := by
    intro q₂
    obtain ⟨γ, hγ, hgen⟩ := he₂ q₂
    set g : ↥(Gamma 2) := ⟨γ, hγ⟩ with hgdef
    have hu : cuspGen (Gamma 2) q₂ = g⁻¹ * U (e₂ q₂) * g := Subtype.ext (by rw [hgen]; rfl)

    have step1 : ∀ o, F (pmRep Φ (cuspGen (pm Φ) (e₁.symm ⟨q₂, o⟩))) = faceVal Φ F (cuspGen (Gamma 2) q₂) o.out.out := by
      intro o
      obtain ⟨c', hc'⟩ := he₁ q₂ o

      set X : pm Φ := ⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ with hXdef
      have hk : minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) o.out =
          minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
        rw [QuotientGroup.out_eq']
      have hcg : cuspGen (pm Φ) (e₁.symm ⟨q₂, o⟩) = (c'⁻¹)⁻¹ * X * c'⁻¹ := by
        apply Subtype.ext
        rw [hc', inv_inv, hXdef]
        push_cast
        rw [hk]
      rw [hcg, pmRep_conj hΦ c'⁻¹ X]
      have hpar : IsParabolicElt (pmRep Φ X) := by
        apply isParabolicElt_pmRep
        show ((((o.out.out⁻¹ * cuspGen (Gamma 2) q₂ ^ _ * o.out.out : ↥(Gamma 2)) : SL(2, ℤ))) :
          Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
        push_cast
        rw [trace_conj_pow_cuspGen]; norm_num
      have := hF_conj (pmRep Φ c'⁻¹)⁻¹ (pmRep Φ X) hpar
      rw [inv_inv] at this
      rw [this]
      rfl
    simp_rw [step1]

    have hpt : ∀ o, faceVal Φ F (cuspGen (Gamma 2) q₂) o.out.out =
        faceVal Φ F (U (e₂ q₂)) ((orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu) o).out.out := by
      intro o

      have hkper := minimalPeriod_transl g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu
        ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))
      rw [Quotient.smul_coe, smul_eq_mul] at hkper
      have hpw : ∀ k : ℕ, cuspGen (Gamma 2) q₂ ^ k = g⁻¹ * U (e₂ q₂) ^ k * g := fun k => by
        rw [hu, inv_conj_pow]
      have hX : (⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ : pm Φ) =
          ⟨_, conj_pow_minimalPeriod_mem Φ (U (e₂ q₂)) (g * o.out.out)⟩ := by
        apply Subtype.ext
        dsimp only
        rw [hkper, hpw]
        push_cast
        group
      have hval : faceVal Φ F (cuspGen (Gamma 2) q₂) o.out.out = faceVal Φ F (U (e₂ q₂)) (g * o.out.out) := by
        unfold faceVal
        rw [hX]
      rw [hval]

      have hτ := orbitTransl_mk (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu o.out
      rw [Quotient.out_eq] at hτ
      have h1 : Quotient.mk (orbitRel (Subgroup.zpowers (U (e₂ q₂))) (↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))
          (g • o.out) =
          Quotient.mk _ ((orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂))
            (cuspGen (Gamma 2) q₂) hu o).out) :=
        hτ.symm.trans (Quotient.out_eq _).symm
      have h2 : g • o.out ∈ orbit (Subgroup.zpowers (U (e₂ q₂)))
          ((orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂))
            (cuspGen (Gamma 2) q₂) hu o).out) :=
        Quotient.exact h1
      have hcoe : (((g * o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) = g • o.out := by
        rw [← smul_eq_mul, ← Quotient.smul_coe, QuotientGroup.out_eq']
      apply faceVal_eq_of_same_orbit hΦ F hF_conj (U (e₂ q₂)) (sq_trace_U (e₂ q₂))
      rw [hcoe, QuotientGroup.out_eq']
      exact h2

    refine Finset.sum_equiv (orbitTransl (X := ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) g (U (e₂ q₂))
      (cuspGen (Gamma 2) q₂) hu) (fun o => ?_) (fun o _ => hpt o)
    simp only [Finset.mem_univ]
  simp_rw [inner]
  exact Fintype.sum_equiv e₂ (fun q₂ => ∑ O : OrbitU Φ (e₂ q₂), faceVal Φ F (U (e₂ q₂)) O.out.out)
    (fun i => ∑ O : OrbitU Φ i, faceVal Φ F (U i) O.out.out) (fun q₂ => rfl)

end CDS3Group
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

section CDS3ParFace

open CongruenceSubgroup MulAction Function ModularGroup

variable {R : Type*} [CommRing R]
variable (Φ : Subgroup SL(2, ℤ))

theorem char_conj (ψ : Additive Φ →+ R) (c v : Φ) :
    ψ (Additive.ofMul (c * v * c⁻¹)) = ψ (Additive.ofMul v) := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]; abel

theorem char_conj' (ψ : Additive Φ →+ R) (c v : Φ) :
    ψ (Additive.ofMul (c⁻¹ * v * c)) = ψ (Additive.ofMul v) := by
  rw [ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]; abel

theorem char_pow (ψ : Additive Φ →+ R) (v : Φ) (k : ℕ) :
    ψ (Additive.ofMul (v ^ k)) = (k : R) * ψ (Additive.ofMul v) := by
  rw [ofMul_pow, map_nsmul, nsmul_eq_mul]

theorem char_zpow (ψ : Additive Φ →+ R) (v : Φ) (k : ℤ) :
    ψ (Additive.ofMul (v ^ k)) = (k : R) * ψ (Additive.ofMul v) := by
  rw [ofMul_zpow, map_zsmul, zsmul_eq_mul]

theorem inv_conj_zpow {G : Type*} [Group G] (a b : G) (i : ℤ) : (a⁻¹ * b * a) ^ i = a⁻¹ * b ^ i * a := by
  have h := @conj_zpow G _ i a⁻¹ b
  simpa using h

theorem conj_conj_zpow {G : Type*} [Group G] (δ b X : G) (j : ℤ) :
    δ * (δ⁻¹ * (b⁻¹ * X * b) * δ) ^ j * δ⁻¹ = b⁻¹ * X ^ j * b := by
  rw [show δ⁻¹ * (b⁻¹ * X * b) * δ = (b * δ)⁻¹ * X * (b * δ) by group, inv_conj_zpow]
  group

variable [Φ.FiniteIndex]

theorem exists_eq_conj_cuspGen_zpow (γ : Φ) (htr : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2)
    (hγ : γ ≠ 1) : ∃ (q : Cusp Φ) (δ : Φ) (j : ℤ), γ = δ * cuspGen Φ q ^ j * δ⁻¹ := by
  have hγ' : (γ : SL(2, ℤ)) ≠ 1 := fun h => hγ (Subtype.ext h)
  obtain ⟨b, m, _hm, hγb⟩ := unipotent_normal_form γ htr hγ'

  have hfix : T ^ m • ((b : SL(2, ℤ)) : SL(2, ℤ) ⧸ Φ) = (b : SL(2, ℤ) ⧸ Φ) := by
    rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
    have : (T ^ m * b)⁻¹ * b = (γ : SL(2, ℤ))⁻¹ := by rw [hγb]; group
    rw [this]
    exact Φ.inv_mem γ.2
  obtain ⟨j, hj⟩ := (MulAction.zpow_smul_eq_iff_minimalPeriod_dvd).mp hfix
  obtain ⟨δ, hδ, hcg⟩ := cuspGen_cuspOf Φ b
  refine ⟨cuspOf Φ b, ⟨δ, hδ⟩, j, Subtype.ext ?_⟩
  push_cast
  rw [hcg, hγb, hj, zpow_mul, zpow_natCast, conj_conj_zpow]

theorem char_eq_zero_of_trace_two (ψ : Additive Φ →+ R) (hcusp : ∀ q : Cusp Φ, ψ (Additive.ofMul (cuspGen Φ q)) = 0)
    (γ : Φ) (htr : ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2) : ψ (Additive.ofMul γ) = 0 := by
  by_cases hγ : γ = 1
  · rw [hγ, ofMul_one, map_zero]
  obtain ⟨q, δ, j, h⟩ := exists_eq_conj_cuspGen_zpow Φ γ htr hγ
  rw [h, char_conj, char_zpow, hcusp, mul_zero]

theorem isPar_of_cuspGen [Invertible (2 : R)] (ψ : Additive Φ →+ R)
    (hcusp : ∀ q : Cusp Φ, ψ (Additive.ofMul (cuspGen Φ q)) = 0) : IsPar Φ ψ := by
  intro γ hγ
  have hsq : (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace - 2) *
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace + 2) = 0 := by
    linear_combination hγ
  rcases mul_eq_zero.mp hsq with h | h
  · exact char_eq_zero_of_trace_two Φ ψ hcusp γ (by linarith)
  · have hneg : ((-(γ : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]; linarith
    have h2 : (((γ ^ 2 : Φ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
      have := trace_pow_eq_two_of_trace_eq_two _ (-(γ : SL(2, ℤ))).2 hneg 2
      rw [Matrix.SpecialLinearGroup.coe_neg, neg_sq] at this
      rw [Subgroup.coe_pow, Matrix.SpecialLinearGroup.coe_pow]
      exact this
    have h0 := char_eq_zero_of_trace_two Φ ψ hcusp (γ ^ 2) h2
    rw [char_pow, Nat.cast_ofNat] at h0
    calc ψ (Additive.ofMul γ) = ⅟(2 : R) * (2 * ψ (Additive.ofMul γ)) := by
          rw [← mul_assoc, invOf_mul_self, one_mul]
      _ = 0 := by rw [h0, mul_zero]

variable {Φ}

theorem cuspGen_eq_conj_pmRep_pow (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (Q : Cusp Φ) :
    ∃ (qbar : Cusp (pm Φ)) (c : Φ) (k : ℕ), cuspGen Φ Q = c * pmRep Φ (cuspGen (pm Φ) qbar) ^ k * c⁻¹ := by

  have sgn : ∀ y z : Φ, ((y : SL(2, ℤ)) = z ∨ (y : SL(2, ℤ)) = -(z : SL(2, ℤ))) → y = z := by
    intro y z hyz
    rcases hyz with h | h
    · exact Subtype.ext h
    · exfalso
      apply hΦ
      have : (y : SL(2, ℤ)) * (z : SL(2, ℤ))⁻¹ = -1 := by rw [h, neg_mul, mul_inv_cancel]
      rw [← this]
      exact Φ.mul_mem y.2 (Φ.inv_mem z.2)
  obtain ⟨E, hE⟩ := cusp_tower Φ (pm Φ) (le_pm Φ)

  have key : ∀ (q : Cusp (pm Φ))
      (o : Quotient (orbitRel (Subgroup.zpowers (cuspGen (pm Φ) q)) (pm Φ ⧸ Φ.subgroupOf (pm Φ)))),
      ∃ (c : Φ) (k : ℕ), cuspGen Φ (E.symm ⟨q, o⟩) = c * pmRep Φ (cuspGen (pm Φ) q) ^ k * c⁻¹ := by
    intro q
    set u : pm Φ := cuspGen (pm Φ) q with hudef
    intro o
    obtain ⟨c', hc'⟩ := hE q o
    set k : ℕ := minimalPeriod (u • ·) o.out with hkdef
    set O : pm Φ := o.out.out with hOdef
    have htrk : ∀ (O' : SL(2, ℤ)) (k' : ℕ),
        ((O'⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k' * O' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
      intro O' k'
      rw [trace_conj_pow_cuspGen (pm Φ) q O' k']; norm_num
    have hupow : ∀ k' : ℕ, ((u : pm Φ) : SL(2, ℤ)) ^ k' = ((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k' ∨
        ((u : pm Φ) : SL(2, ℤ)) ^ k' = -((pmRep Φ u : Φ) : SL(2, ℤ)) ^ k' := by
      intro k'
      rcases pmRep_spec Φ u with h | h
      · left; rw [h]
      · have hu' : ((u : pm Φ) : SL(2, ℤ)) = -((pmRep Φ u : Φ) : SL(2, ℤ)) := by rw [h, neg_neg]
        rw [hu', neg_pow]
        rcases neg_one_pow_eq_or SL(2, ℤ) k' with h1 | h1
        · left; rw [h1, one_mul]
        · right; rw [h1, neg_one_mul]
    have hvmem : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) ∈ Φ := by
      have h := QuotientGroup.out_conj_pow_minimalPeriod_mem (Φ.subgroupOf (pm Φ)) u o.out
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h
    set v : Φ := ⟨_, hvmem⟩ with hvdef
    have hgen : cuspGen Φ (E.symm ⟨q, o⟩) = c' * v * c'⁻¹ := by
      apply Subtype.ext
      rw [hc']
      rfl
    set φ : Φ := pmRep Φ O with hφdef
    have hconj : ((O : pm Φ) : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * (O : SL(2, ℤ)) =
        (φ : SL(2, ℤ))⁻¹ * ((u : pm Φ) : SL(2, ℤ)) ^ k * φ := by
      rcases pmRep_spec Φ O with h | h
      · rw [h]
      · have hO : ((O : pm Φ) : SL(2, ℤ)) = -(φ : SL(2, ℤ)) := by rw [h, neg_neg]
        have hinv : (-(φ : SL(2, ℤ)))⁻¹ = -(φ : SL(2, ℤ))⁻¹ := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [neg_mul, mul_neg, neg_neg, mul_inv_cancel]
        rw [hO, hinv, neg_mul, neg_mul, mul_neg, neg_neg]
    have hv : v = φ⁻¹ * (pmRep Φ u) ^ k * φ := by
      apply sgn
      simp only [hvdef, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hconj]
      rcases hupow k with h | h
      · left; rw [h]
      · right; rw [h]; simp [mul_neg, neg_mul]
    refine ⟨c' * φ⁻¹, k, ?_⟩
    rw [hgen, hv, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
    rfl
  obtain ⟨c, k, h⟩ := key (E Q).1 (E Q).2
  rw [Sigma.eta, E.symm_apply_apply] at h
  exact ⟨(E Q).1, c, k, h⟩

omit [Φ.FiniteIndex] in

theorem pm_le_Gamma_two (hle : Φ ≤ Gamma 2) : pm Φ ≤ Gamma 2 := by
  intro g hg
  rcases hg with hg | hg
  · exact hle hg
  · have := hle hg
    have h1 : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
      rw [Gamma_mem]; decide
    simpa using Subgroup.mul_mem _ h1 this

theorem cuspGen_pm_eq_conj_faceElt (hle' : pm Φ ≤ Gamma 2) (qbar : Cusp (pm Φ)) :
    ∃ (i : Fin 3) (p : ↥(Gamma 2)) (δ : pm Φ),
      cuspGen (pm Φ) qbar = δ⁻¹ * ⟨_, conj_pow_minimalPeriod_mem Φ (U i) p⟩ * δ := by
  obtain ⟨e₁, he₁⟩ := cusp_tower (pm Φ) (Gamma 2) hle'
  obtain ⟨e₂, he₂⟩ := Gamma_two_cusps_TD
  have hc0 := he₁ (e₁ qbar).1 (e₁ qbar).2
  clear he₁
  rw [Sigma.eta, e₁.symm_apply_apply] at hc0
  obtain ⟨c', hc'⟩ := hc0
  set q₂ : Cusp (Gamma 2) := (e₁ qbar).1 with hq₂
  set o := (e₁ qbar).2 with ho
  obtain ⟨γ, hγ, hgen⟩ := he₂ q₂
  set g : ↥(Gamma 2) := ⟨γ, hγ⟩ with hgdef
  have hu : cuspGen (Gamma 2) q₂ = g⁻¹ * U (e₂ q₂) * g := Subtype.ext (by rw [hgen]; rfl)
  have hk : minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) o.out =
      minimalPeriod ((cuspGen (Gamma 2) q₂) • ·) ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [QuotientGroup.out_eq']
  have hcg : cuspGen (pm Φ) qbar = (c'⁻¹)⁻¹ * ⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ * c'⁻¹ := by
    apply Subtype.ext
    rw [hc', inv_inv]
    push_cast
    rw [hk]
  have hkper := minimalPeriod_transl g (U (e₂ q₂)) (cuspGen (Gamma 2) q₂) hu
    ((o.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))
  rw [Quotient.smul_coe, smul_eq_mul] at hkper
  have hpw : ∀ k : ℕ, cuspGen (Gamma 2) q₂ ^ k = g⁻¹ * U (e₂ q₂) ^ k * g := fun k => by rw [hu, inv_conj_pow]
  have hX : (⟨_, conj_pow_minimalPeriod_mem Φ (cuspGen (Gamma 2) q₂) o.out.out⟩ : pm Φ) =
      ⟨_, conj_pow_minimalPeriod_mem Φ (U (e₂ q₂)) (g * o.out.out)⟩ := by
    apply Subtype.ext
    dsimp only
    rw [hkper, hpw]
    push_cast
    group
  exact ⟨e₂ q₂, g * o.out.out, c'⁻¹, by rw [hcg, hX]⟩

omit [Φ.FiniteIndex] in

theorem faceElt_conj_of_same_orbit (u p p' : ↥(Gamma 2))
    (h : ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈
      orbit (Subgroup.zpowers u) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) :
    ∃ φ : pm Φ, (⟨_, conj_pow_minimalPeriod_mem Φ u p'⟩ : pm Φ) = φ⁻¹ * ⟨_, conj_pow_minimalPeriod_mem Φ u p⟩ * φ := by
  rw [mem_orbit_iff] at h
  obtain ⟨s, hs⟩ := h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp s.2
  have hs' : u ^ j • ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := hj ▸ hs
  have hk : minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [← hs']
    exact ModularCurve.PDPairing.CuspTower.minimalPeriod_zpow_smul u j _
  have hφ : (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)) ∈ pm Φ := by
    rw [Quotient.smul_coe, QuotientGroup.eq, smul_eq_mul, Subgroup.mem_subgroupOf] at hs'
    exact hs'
  refine ⟨⟨_, hφ⟩, Subtype.ext ?_⟩
  show (((p'⁻¹ * u ^ minimalPeriod (u • ·) ((p' : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p' : ↥(Gamma 2)) : SL(2, ℤ))) =
    ((((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ)))⁻¹ *
      ((p⁻¹ * u ^ minimalPeriod (u • ·) ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) * p : ↥(Gamma 2)) : SL(2, ℤ)) *
      (((u ^ j * p)⁻¹ * p' : ↥(Gamma 2)) : SL(2, ℤ))
  rw [hk]
  push_cast
  rw [← zpow_natCast]
  group

theorem isPar_of_faceElt [Invertible (2 : R)] (hΦ : (-1 : SL(2, ℤ)) ∉ Φ) (hle : Φ ≤ Gamma 2)
    (ψ : Additive Φ →+ R) (rep : ∀ i : Fin 3, OrbitU Φ i → ↥(Gamma 2))
    (hrep : ∀ (i : Fin 3) (O : OrbitU Φ i),
      Quotient.mk _ (((rep i O : ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = O)
    (hface : ∀ (i : Fin 3) (O : OrbitU Φ i),
      ψ (Additive.ofMul (pmRep Φ ⟨_, conj_pow_minimalPeriod_mem Φ (U i) (rep i O)⟩)) = 0) :
    IsPar Φ ψ := by
  apply isPar_of_cuspGen
  intro Q
  obtain ⟨qbar, c, k, hQ⟩ := cuspGen_eq_conj_pmRep_pow hΦ Q
  rw [hQ, char_conj, char_pow]
  obtain ⟨i, p, δ, hqbar⟩ := cuspGen_pm_eq_conj_faceElt (pm_le_Gamma_two hle) qbar
  rw [hqbar, pmRep_conj hΦ δ, char_conj']
  have h1 : Quotient.mk (orbitRel (Subgroup.zpowers (U i)) (↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)))
      ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) =
      Quotient.mk _ (((rep i (Quotient.mk _ ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) :
        ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
    rw [hrep]
  have hmem : ((p : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈
      orbit (Subgroup.zpowers (U i)) (((rep i (Quotient.mk _ ((p : ↥(Gamma 2)) :
        ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2))) : ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) :=
    Quotient.exact h1
  obtain ⟨φ, hφ⟩ := faceElt_conj_of_same_orbit (Φ := Φ) (U i) (rep i _) p hmem
  rw [hφ, pmRep_conj hΦ φ, char_conj', hface, mul_zero]

end CDS3ParFace
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

end ModularCurve.PDPairing.TD
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace Schreier
p2m_open "ModularCurve.PDPairing ModularCurve"

variable {G : Type*} [Group G] {ι : Type*} (a : ι → G)

theorem wprod_nil : wprod a [] = 1 := by simp [wprod]

theorem wprod_append (l l' : List (ι × Bool)) : wprod a (l ++ l') = wprod a l * wprod a l' := by
  simp [wprod, List.map_append, List.prod_append]

theorem wprod_replicate (p : ι × Bool) (k : ℕ) : wprod a (List.replicate k p) = act a p ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, wprod_nil, pow_zero]
  | succ k ih => rw [List.replicate_succ, wprod_cons, ih, ← pow_succ']

theorem wprod_flatten_replicate (l : List (ι × Bool)) (k : ℕ) :
    wprod a (List.replicate k l).flatten = wprod a l ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, wprod_nil, pow_zero]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, wprod_append, ih, ← pow_succ']

end ModularCurve.PDPairing.Schreier
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

namespace ModularCurve
p2m_export "ModularCurve" "PDPairing.coresAdd PDPairing.conjUpperMat PDPairing.conjUpperMat_apply_10 PDPairing.conjLowerMat PDPairing.conjLowerMat_conjUpperMat PDPairing.dvd_entry0 PDPairing.iotaDeg0 PDPairing.iDeg0 PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 PDPairing.iotaDeg0_injective PDPairing.pushChar0 PDPairing.jDeg0 PDPairing.Gamma0Upper PDPairing.mem_Gamma0Upper PDPairing.Gamma0HUpper PDPairing.dvd_of_mem_Gamma0HUpper PDPairing.conjL0 PDPairing.heckeT0 PDPairing.heckeT0_apply PDPairing.pairF PDPairing.pairD PDPairing.pairZFun PDPairing.pairZFun_swap PDPairing.pairZ PDPairing.pairZ_apply"
namespace PDPairing
p2m_export "ModularCurve.PDPairing" "transfer_mul toMultiplicativeRight_add toAdditiveLeft_mul coresAdd conjUpperMat conjUpperMat_apply_10 conjLowerMat conjLowerMat_conjUpperMat dvd_entry0 iotaDeg0 iDeg0 Gamma_subgroupOf_le_range_iotaDeg0 iotaDeg0_injective pushChar0 jDeg0 Gamma0Upper mem_Gamma0Upper Gamma0HUpper dvd_of_mem_Gamma0HUpper conjL0 heckeT0 heckeT0_apply omega omega_one_left omega_self_inv omega_swap sect hPrim hPrim_mul hPrim_one hPrim_unique hPrim_of omega_add_left omega_smul_left Cusp cuspGen cuspSum cuspSum_add cuspSum_smul pairF resInf pairD pairZFun pairZFun_swap pairZ pairZ_apply"
namespace TD
p2m_open "ModularCurve.PDPairing ModularCurve"

section GlueA

open CongruenceSubgroup MulAction Function ModularGroup ModularCurve.Sanov ModularCurve.PDPairing.SanPM ModularCurve.PDPairing.SanThree ModularCurve.PDPairing.Schreier

variable {R : Type*} [CommRing R]

theorem minimalPeriod_semiconj {X Y : Type*} (e : X → Y) (he : Injective e) (f : X → X) (g : Y → Y)
    (h : ∀ x, e (f x) = g (e x)) (x : X) : minimalPeriod g (e x) = minimalPeriod f x := by
  rw [minimalPeriod_eq_minimalPeriod_iff]
  intro n
  have hiter : ∀ m : ℕ, (g^[m]) (e x) = e ((f^[m]) x) := by
    intro m
    induction m generalizing x with
    | zero => rfl
    | succ m ih => rw [iterate_succ_apply, iterate_succ_apply, ← h, ih]
  unfold IsPeriodicPt IsFixedPt
  rw [hiter]
  exact ⟨fun hx => he hx, fun hx => congrArg e hx⟩

variable (Φ : Subgroup SL(2, ℤ))

abbrev VΦ : Type := ↥sanovSubgroup ⧸ Φ.subgroupOf sanovSubgroup

noncomputable abbrev sanL : Fin 2 → ↥sanovSubgroup := fun i => sanovBasis i

theorem range_sanL : Set.range sanL = {⟨sanovA, sanovA_mem⟩, ⟨sanovB, sanovB_mem⟩} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl sanovBasis_zero
    · exact Or.inr sanovBasis_one
  · rintro (rfl | rfl)
    · exact ⟨0, sanovBasis_zero⟩
    · exact ⟨1, sanovBasis_one⟩

theorem closure_range_sanL : Subgroup.closure (Set.range sanL) = ⊤ := by
  rw [range_sanL]; exact closure_sanov_generators_eq_top

def v0 : VΦ Φ := ((1 : ↥sanovSubgroup) : VΦ Φ)

theorem sanov_transitive (v : VΦ Φ) : ∃ g : ↥sanovSubgroup, g • v0 Φ = v := by
  induction v using QuotientGroup.induction_on with
  | H g => exact ⟨g, by rw [v0, Quotient.smul_coe, smul_eq_mul, mul_one]⟩

noncomputable def treeT : TreeTransversal sanL (v0 Φ) :=
  bfsTransversal sanL (v0 Φ) closure_range_sanL (sanov_transitive Φ)

theorem stabilizer_v0 : stabilizer (↥sanovSubgroup) (v0 Φ) = Φ.subgroupOf sanovSubgroup :=
  stabilizer_quotient _

noncomputable def stabEquiv (hΦs : Φ ≤ sanovSubgroup) : ↥(stabilizer (↥sanovSubgroup) (v0 Φ)) ≃* Φ :=
  (MulEquiv.subgroupCongr (stabilizer_v0 Φ)).trans (Subgroup.subgroupOfEquivOfLe hΦs)

theorem coe_stabEquiv (hΦs : Φ ≤ sanovSubgroup) (x : stabilizer (↥sanovSubgroup) (v0 Φ)) :
    ((stabEquiv Φ hΦs x : Φ) : SL(2, ℤ)) = (((x : stabilizer (↥sanovSubgroup) (v0 Φ)) : ↥sanovSubgroup) : SL(2, ℤ)) := rfl

def faceRound : Fin 3 → List (Fin 2 × Bool)
  | 0 => [(0, true)]
  | 1 => [(1, false)]
  | 2 => [(0, false), (1, true)]

def faceWord (i : Fin 3) (k : ℕ) : List (Fin 2 × Bool) := (List.replicate k (faceRound i)).flatten

noncomputable def faceGen (i : Fin 3) : ↥sanovSubgroup := wprod sanL (faceRound i)

theorem wprod_faceWord (i : Fin 3) (k : ℕ) : wprod sanL (faceWord i k) = faceGen i ^ k :=
  wprod_flatten_replicate sanL (faceRound i) k

theorem faceGen_zero : faceGen 0 = sanovBasis 0 := by
  simp only [faceGen, faceRound, wprod, act, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    ↓reduceIte]

theorem faceGen_one : faceGen 1 = (sanovBasis 1)⁻¹ := by
  simp only [faceGen, faceRound, wprod, act, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.false_eq_true, ↓reduceIte]

theorem faceGen_two : faceGen 2 = (sanovBasis 0)⁻¹ * sanovBasis 1 := by
  simp only [faceGen, faceRound, wprod, act, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    Bool.false_eq_true, ↓reduceIte]

theorem coe_faceGen_zero : ((faceGen 0 : ↥sanovSubgroup) : SL(2, ℤ)) = sanovA := by
  rw [faceGen_zero, sanovBasis_zero]

theorem coe_faceGen_one : ((faceGen 1 : ↥sanovSubgroup) : SL(2, ℤ)) = sanovB⁻¹ := by
  rw [faceGen_one, Subgroup.coe_inv, sanovBasis_one]

theorem coe_faceGen_two : ((faceGen 2 : ↥sanovSubgroup) : SL(2, ℤ)) = sanovA⁻¹ * sanovB := by
  rw [faceGen_two, Subgroup.coe_mul, Subgroup.coe_inv, sanovBasis_zero, sanovBasis_one]

noncomputable def faceLen (i : Fin 3) (v : VΦ Φ) : ℕ := minimalPeriod ((faceGen i) • ·) v

theorem faceWord_closed (i : Fin 3) (v : VΦ Φ) : wprod sanL (faceWord i (faceLen Φ i v)) • v = v := by
  rw [wprod_faceWord]
  exact (pow_smul_eq_iff_minimalPeriod_dvd).mpr dvd_rfl

noncomputable def faceElt (i : Fin 3) (v : VΦ Φ) : stabilizer (↥sanovSubgroup) (v0 Φ) :=
  (treeT Φ).wordWalk v (faceWord i (faceLen Φ i v))

theorem coe_faceElt (i : Fin 3) (v : VΦ Φ) :
    ((faceElt Φ i v : stabilizer (↥sanovSubgroup) (v0 Φ)) : ↥sanovSubgroup) =
      ((treeT Φ).t v)⁻¹ * faceGen i ^ faceLen Φ i v * (treeT Φ).t v := by
  rw [faceElt, TreeTransversal.coe_wordWalk_of_closed _ _ _ (faceWord_closed Φ i v), wprod_faceWord]

noncomputable def gOf : Fin 3 → ↥sanovSubgroup
  | 0 => 1
  | 1 => 1
  | 2 => sanovBasis 0

noncomputable def pOf (i : Fin 3) (v : VΦ Φ) : ↥(Gamma 2) :=
  Subgroup.inclusion sanovSubgroup_le_Gamma_two (gOf i * (treeT Φ).t v)

theorem mk_t (v : VΦ Φ) : (((treeT Φ).t v : ↥sanovSubgroup) : VΦ Φ) = v := by
  have h : (treeT Φ).t v • (((1 : ↥sanovSubgroup)) : VΦ Φ) = v := (treeT Φ).t_smul v
  rw [Quotient.smul_coe, smul_eq_mul, mul_one] at h
  exact h

def β2 : VΦ Φ → ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) := sanToG2 Φ

theorem β2_mk (g : ↥sanovSubgroup) :
    β2 Φ (g : VΦ Φ) = ((Subgroup.inclusion sanovSubgroup_le_Gamma_two g : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) :=
  rfl

theorem β2_smul (g : ↥sanovSubgroup) (x : VΦ Φ) :
    β2 Φ (g • x) = (Subgroup.inclusion sanovSubgroup_le_Gamma_two g) • β2 Φ x :=
  sanToG2_smul Φ g x

theorem β2_injective (hΦs : Φ ≤ sanovSubgroup) : Injective (β2 Φ) := sanToG2_injective Φ hΦs

theorem β2_surjective : Surjective (β2 Φ) := sanToG2_surjective Φ

noncomputable def β2Equiv (hΦs : Φ ≤ sanovSubgroup) : VΦ Φ ≃ ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2) :=
  Equiv.ofBijective (β2 Φ) ⟨β2_injective Φ hΦs, β2_surjective Φ⟩

theorem mk_pOf (i : Fin 3) (v : VΦ Φ) :
    ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = β2 Φ (gOf i • v) := by
  conv_rhs => rw [← mk_t Φ v, Quotient.smul_coe, smul_eq_mul, β2_mk]
  rfl

theorem coe_U_zero : ((U 0 : ↥(Gamma 2)) : SL(2, ℤ)) = sanovA := by
  apply Subtype.ext
  show ((ModularCurve.PDPairing.BaseTwo.ustd 0 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
  rw [ModularCurve.PDPairing.BaseTwo.coe_ustd_zero, coe_sanovA]

theorem coe_U_one : ((U 1 : ↥(Gamma 2)) : SL(2, ℤ)) = sanovB⁻¹ := by
  show ModularCurve.PDPairing.BaseTwo.ustd 1 = sanovB⁻¹
  decide

theorem coe_U_two : ((U 2 : ↥(Gamma 2)) : SL(2, ℤ)) = -(sanovA * (sanovA⁻¹ * sanovB) * sanovA⁻¹) := by
  show ModularCurve.PDPairing.BaseTwo.ustd 2 = -(sanovA * (sanovA⁻¹ * sanovB) * sanovA⁻¹)
  decide

def negOneG2 : ↥(Gamma 2) := ⟨-1, by rw [Gamma_mem]; decide⟩

theorem negOneG2_smul (x : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) : negOneG2 • x = x := by
  induction x using QuotientGroup.induction_on with
  | H q =>
    have hmem : negOneG2 ∈ (pm Φ).subgroupOf (Gamma 2) := by
      rw [Subgroup.mem_subgroupOf]; exact neg_one_mem_pm Φ
    have hcomm : negOneG2 * q = q * negOneG2 :=
      Subtype.ext (by show (-1 : SL(2, ℤ)) * q = q * (-1 : SL(2, ℤ)); rw [neg_one_mul, mul_neg_one])
    rw [Quotient.smul_coe, smul_eq_mul, hcomm, QuotientGroup.mk_mul_of_mem q hmem]

theorem coe_pOf_zero (v : VΦ Φ) : ((pOf Φ 0 v : ↥(Gamma 2)) : SL(2, ℤ)) = (((treeT Φ).t v : ↥sanovSubgroup) : SL(2, ℤ)) := by
  show (((gOf 0 * (treeT Φ).t v : ↥sanovSubgroup)) : SL(2, ℤ)) = _
  rw [show gOf 0 = 1 from rfl, one_mul]

theorem coe_pOf_one (v : VΦ Φ) : ((pOf Φ 1 v : ↥(Gamma 2)) : SL(2, ℤ)) = (((treeT Φ).t v : ↥sanovSubgroup) : SL(2, ℤ)) := by
  show (((gOf 1 * (treeT Φ).t v : ↥sanovSubgroup)) : SL(2, ℤ)) = _
  rw [show gOf 1 = 1 from rfl, one_mul]

theorem coe_pOf_two (v : VΦ Φ) :
    ((pOf Φ 2 v : ↥(Gamma 2)) : SL(2, ℤ)) = sanovA * (((treeT Φ).t v : ↥sanovSubgroup) : SL(2, ℤ)) := by
  show (((gOf 2 * (treeT Φ).t v : ↥sanovSubgroup)) : SL(2, ℤ)) = _
  rw [show gOf 2 = sanovBasis 0 from rfl, Subgroup.coe_mul, sanovBasis_zero]

theorem U_smul_β2 (i : Fin 3) (y : VΦ Φ) :
    U i • β2 Φ (gOf i • y) = β2 Φ (gOf i • (faceGen i • y)) := by
  fin_cases i
  ·
    have hU : U 0 = Subgroup.inclusion sanovSubgroup_le_Gamma_two (sanovBasis 0) :=
      Subtype.ext (by rw [coe_U_zero, sanovBasis_zero]; rfl)
    show U 0 • β2 Φ ((1 : ↥sanovSubgroup) • y) = β2 Φ ((1 : ↥sanovSubgroup) • (faceGen 0 • y))
    rw [one_smul, one_smul, faceGen_zero, hU, β2_smul]
  · have hU : U 1 = Subgroup.inclusion sanovSubgroup_le_Gamma_two (sanovBasis 1)⁻¹ :=
      Subtype.ext (by rw [coe_U_one, map_inv, Subgroup.coe_inv, sanovBasis_one]; rfl)
    show U 1 • β2 Φ ((1 : ↥sanovSubgroup) • y) = β2 Φ ((1 : ↥sanovSubgroup) • (faceGen 1 • y))
    rw [one_smul, one_smul, faceGen_one, hU, β2_smul]
  ·
    have hU : U 2 = negOneG2 * Subgroup.inclusion sanovSubgroup_le_Gamma_two (sanovBasis 0 * faceGen 2 * (sanovBasis 0)⁻¹) := by
      apply Subtype.ext
      rw [coe_U_two]
      show _ = (-1 : SL(2, ℤ)) * ((sanovBasis 0 * faceGen 2 * (sanovBasis 0)⁻¹ : ↥sanovSubgroup) : SL(2, ℤ))
      push_cast
      rw [coe_faceGen_two, sanovBasis_zero, neg_one_mul]
    show U 2 • β2 Φ (sanovBasis 0 • y) = β2 Φ (sanovBasis 0 • (faceGen 2 • y))
    rw [hU, mul_smul, negOneG2_smul, ← β2_smul, smul_smul, smul_smul, mul_assoc (sanovBasis 0 * faceGen 2),
      inv_mul_cancel, mul_one]

theorem minimalPeriod_pOf (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (v : VΦ Φ) :
    minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = faceLen Φ i v := by
  rw [mk_pOf]
  have hinj : Injective (fun y : VΦ Φ => β2 Φ (gOf i • y)) :=
    fun y₁ y₂ h => smul_left_cancel (gOf i) (β2_injective Φ hΦs h)
  exact minimalPeriod_semiconj (fun y : VΦ Φ => β2 Φ (gOf i • y)) hinj ((faceGen i) • ·) ((U i) • ·)
    (fun y => (U_smul_β2 Φ i y).symm) v

theorem pmRep_faceElt (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (v : VΦ Φ) :
    pmRep Φ ⟨_, conj_pow_minimalPeriod_mem Φ (U i) (pOf Φ i v)⟩ = stabEquiv Φ hΦs (faceElt Φ i v) := by
  have hΦ : (-1 : SL(2, ℤ)) ∉ Φ := neg_one_notMem_of_le_sanov Φ hΦs
  symm
  apply pmRep_unique hΦ

  show ((stabEquiv Φ hΦs (faceElt Φ i v) : Φ) : SL(2, ℤ)) =
      (((pOf Φ i v)⁻¹ * U i ^ minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) *
        pOf Φ i v : ↥(Gamma 2)) : SL(2, ℤ)) ∨
    ((stabEquiv Φ hΦs (faceElt Φ i v) : Φ) : SL(2, ℤ)) =
      -(((pOf Φ i v)⁻¹ * U i ^ minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) *
        pOf Φ i v : ↥(Gamma 2)) : SL(2, ℤ))
  rw [coe_stabEquiv, coe_faceElt, minimalPeriod_pOf Φ hΦs]
  fin_cases i
  · left
    push_cast
    rw [coe_faceGen_zero, coe_U_zero, coe_pOf_zero]
  · left
    push_cast
    rw [coe_faceGen_one, coe_U_one, coe_pOf_one]
  ·
    rcases neg_one_pow_eq_or SL(2, ℤ) (faceLen Φ 2 v) with h1 | h1
    · left
      push_cast
      rw [coe_faceGen_two, coe_U_two, coe_pOf_two, neg_pow, h1, one_mul, conj_pow, mul_inv_rev]
      generalize (sanovA⁻¹ * sanovB) ^ faceLen Φ 2 v = X
      group
    · right
      push_cast
      rw [coe_faceGen_two, coe_U_two, coe_pOf_two, neg_pow, h1, neg_one_mul, conj_pow, mul_neg, neg_mul, neg_neg,
        mul_inv_rev]
      generalize (sanovA⁻¹ * sanovB) ^ faceLen Φ 2 v = X
      group

noncomputable def vOf (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (O : OrbitU Φ i) : VΦ Φ :=
  (gOf i)⁻¹ • (β2Equiv Φ hΦs).symm O.out

theorem mk_pOf_vOf (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (O : OrbitU Φ i) :
    Quotient.mk _ (((pOf Φ i (vOf Φ hΦs i O) : ↥(Gamma 2))) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) = O := by
  rw [mk_pOf, vOf, smul_inv_smul]
  have h : β2 Φ ((β2Equiv Φ hΦs).symm O.out) = O.out := (β2Equiv Φ hΦs).apply_symm_apply O.out
  rw [h]
  exact Quotient.out_eq O

theorem par_faceElt (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (hpar : IsPar Φ ψ) (i : Fin 3) (v : VΦ Φ) :
    ψ (Additive.ofMul (stabEquiv Φ hΦs (faceElt Φ i v))) = 0 := by
  rw [← pmRep_faceElt Φ hΦs]
  apply hpar
  apply isParabolicElt_pmRep
  show ((((pOf Φ i v)⁻¹ * U i ^ minimalPeriod ((U i) • ·) ((pOf Φ i v : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) *
    pOf Φ i v : ↥(Gamma 2)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  push_cast
  exact sq_trace_conj_pow_SL _ _ _ (sq_trace_U i)

variable [Φ.FiniteIndex]

theorem isPar_of_faces [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R)
    (hψ : ∀ (i : Fin 3) (v : VΦ Φ), ψ (Additive.ofMul (stabEquiv Φ hΦs (faceElt Φ i v))) = 0) : IsPar Φ ψ := by
  have hΦ : (-1 : SL(2, ℤ)) ∉ Φ := neg_one_notMem_of_le_sanov Φ hΦs
  have hle : Φ ≤ Gamma 2 := hΦs.trans sanovSubgroup_le_Gamma_two
  refine isPar_of_faceElt hΦ hle ψ (fun i O => pOf Φ i (vOf Φ hΦs i O)) (fun i O => mk_pOf_vOf Φ hΦs i O) ?_
  intro i O
  rw [pmRep_faceElt Φ hΦs]
  exact hψ i _

end GlueA
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section GlueB

open CongruenceSubgroup MulAction Function ModularGroup ModularCurve.Sanov ModularCurve.PDPairing.SanPM ModularCurve.PDPairing.SanThree ModularCurve.PDPairing.Schreier

variable {R : Type*} [CommRing R]
variable (Φ : Subgroup SL(2, ℤ))

noncomputable def edgeVal (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (v : VΦ Φ) (i : Fin 2) : R :=
  ψ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).x v i)))

theorem edgeVal_tree (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (v : VΦ Φ) (i : Fin 2)
    (h : (treeT Φ).tree v i = true) : edgeVal Φ hΦs ψ v i = 0 := by
  rw [edgeVal, (treeT Φ).x_eq_one_of_tree v i h, map_one, ofMul_one, map_zero]

theorem edgeVal_add (hΦs : Φ ≤ sanovSubgroup) (ψ ψ' : Additive Φ →+ R) :
    edgeVal Φ hΦs (ψ + ψ') = edgeVal Φ hΦs ψ + edgeVal Φ hΦs ψ' := by
  funext v i; rfl

theorem edgeVal_smul (hΦs : Φ ≤ sanovSubgroup) (r : R) (ψ : Additive Φ →+ R) :
    edgeVal Φ hΦs (r • ψ) = r • edgeVal Φ hΦs ψ := by
  funext v i; rfl

def treeKer : Submodule R (VΦ Φ → Fin 2 → R) where
  carrier := {c | ∀ v i, (treeT Φ).tree v i = true → c v i = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro c c' hc hc' v i h
    show c v i + c' v i = 0
    rw [hc v i h, hc' v i h, add_zero]
  smul_mem' := by
    intro r c hc v i h
    show r • c v i = 0
    rw [hc v i h, smul_zero]

theorem eq_zero_of_edgeVal (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (h : edgeVal Φ hΦs ψ = 0) : ψ = 0 := by

  have hgen : ∀ s : stabilizer (↥sanovSubgroup) (v0 Φ), ψ (Additive.ofMul (stabEquiv Φ hΦs s)) = 0 := by
    intro s
    have hs : s ∈ (treeT Φ).schreierClosure := by
      rw [(treeT Φ).schreierClosure_eq_top closure_range_sanL]; exact Subgroup.mem_top s
    induction hs using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨v, i⟩, rfl⟩ := hy
      have := congrFun (congrFun h v) i
      exact this
    | one => rw [map_one, ofMul_one, map_zero]
    | mul y z _ _ ihy ihz => rw [map_mul, ofMul_mul, map_add, ihy, ihz, add_zero]
    | inv y _ ihy => rw [map_inv, ofMul_inv, map_neg, ihy, neg_zero]
  ext g
  have := hgen ((stabEquiv Φ hΦs).symm (Additive.toMul g))
  rw [MulEquiv.apply_symm_apply] at this
  exact this

noncomputable def charOfEdge (hΦs : Φ ≤ sanovSubgroup) (c : VΦ Φ → Fin 2 → R) : Additive Φ →+ R :=
  (TreeTransversal.character sanovBasis c).comp (MonoidHom.toAdditive (stabEquiv Φ hΦs).symm.toMonoidHom)

theorem edgeVal_charOfEdge (hΦs : Φ ≤ sanovSubgroup) (c : VΦ Φ → Fin 2 → R)
    (hc : ∀ v i, (treeT Φ).tree v i = true → c v i = 0) : edgeVal Φ hΦs (charOfEdge Φ hΦs c) = c := by
  funext v i
  show TreeTransversal.character sanovBasis c
      (Additive.ofMul ((stabEquiv Φ hΦs).symm (stabEquiv Φ hΦs ((treeT Φ).x v i)))) = c v i
  rw [MulEquiv.symm_apply_apply]
  exact TreeTransversal.character_x sanovBasis (treeT Φ) c hc v i

theorem edgeVal_injective (hΦs : Φ ≤ sanovSubgroup) : Injective (edgeVal (R := R) Φ hΦs) := by
  intro ψ ψ' h
  have h0 : edgeVal Φ hΦs (ψ - ψ') = 0 := by
    funext v i
    show ψ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).x v i))) - ψ' (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).x v i))) = 0
    rw [sub_eq_zero]
    exact congrFun (congrFun h v) i
  exact sub_eq_zero.mp (eq_zero_of_edgeVal Φ hΦs _ h0)

noncomputable def edgeCoordFun (hΦs : Φ ≤ sanovSubgroup) : (Additive Φ →+ R) →ₗ[R] treeKer (R := R) Φ where
  toFun ψ := ⟨edgeVal Φ hΦs ψ, fun v i h => edgeVal_tree Φ hΦs ψ v i h⟩
  map_add' ψ ψ' := Subtype.ext (edgeVal_add Φ hΦs ψ ψ')
  map_smul' r ψ := Subtype.ext (edgeVal_smul Φ hΦs r ψ)

theorem edgeCoordFun_bijective (hΦs : Φ ≤ sanovSubgroup) : Bijective (edgeCoordFun (R := R) Φ hΦs) := by
  constructor
  · intro ψ ψ' h
    exact edgeVal_injective Φ hΦs (congrArg Subtype.val h)
  · intro c
    refine ⟨charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R), Subtype.ext ?_⟩
    exact edgeVal_charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R) (fun v i h => c.2 v i h)

noncomputable def edgeCoord (hΦs : Φ ≤ sanovSubgroup) : (Additive Φ →+ R) ≃ₗ[R] treeKer (R := R) Φ :=
  LinearEquiv.ofBijective (edgeCoordFun Φ hΦs) (edgeCoordFun_bijective Φ hΦs)

theorem edgeCoord_apply (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) :
    ((edgeCoord Φ hΦs ψ : treeKer (R := R) Φ) : VΦ Φ → Fin 2 → R) = edgeVal Φ hΦs ψ := rfl

noncomputable def sval (c : VΦ Φ → Fin 2 → R) (w : VΦ Φ) (p : Fin 2 × Bool) : R :=
  if p.2 then c w p.1 else -c ((sanL p.1)⁻¹ • w) p.1

noncomputable def walkSum (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) : List (Fin 2 × Bool) → R
  | [] => 0
  | p :: l => sval Φ c (wprod sanL l • v) p + walkSum c v l

theorem walkSum_add (c c' : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    walkSum Φ (c + c') v l = walkSum Φ c v l + walkSum Φ c' v l := by
  induction l with
  | nil => simp [walkSum]
  | cons p l ih =>
    simp only [walkSum, ih]
    obtain ⟨i, d⟩ := p
    cases d <;> simp [sval] <;> ring

theorem walkSum_smul (r : R) (c : VΦ Φ → Fin 2 → R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    walkSum Φ (r • c) v l = r * walkSum Φ c v l := by
  induction l with
  | nil => simp [walkSum]
  | cons p l ih =>
    simp only [walkSum, ih]
    obtain ⟨i, d⟩ := p
    cases d <;> simp [sval] <;> ring

theorem char_wordWalk_eq_walkSum (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    ψ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).wordWalk v l))) = walkSum Φ (edgeVal Φ hΦs ψ) v l := by
  induction l with
  | nil =>
    show ψ (Additive.ofMul (stabEquiv Φ hΦs 1)) = 0
    rw [map_one, ofMul_one, map_zero]
  | cons p l ih =>
    rw [TreeTransversal.wordWalk_cons, map_mul, ofMul_mul, map_add, ih]
    show _ + _ = sval Φ (edgeVal Φ hΦs ψ) (wprod sanL l • v) p + walkSum Φ (edgeVal Φ hΦs ψ) v l
    congr 1
    obtain ⟨i, d⟩ := p
    cases d
    · rw [TreeTransversal.sx_false, map_inv, ofMul_inv, map_neg]
      simp only [sval, Bool.false_eq_true, ↓reduceIte]
      rfl
    · rw [TreeTransversal.sx_true]
      simp only [sval, ↓reduceIte]
      rfl

theorem char_faceElt_eq_walkSum (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) (i : Fin 3) (v : VΦ Φ) :
    ψ (Additive.ofMul (stabEquiv Φ hΦs (faceElt Φ i v))) = walkSum Φ (edgeVal Φ hΦs ψ) v (faceWord i (faceLen Φ i v)) :=
  char_wordWalk_eq_walkSum Φ hΦs ψ v _

variable [Φ.FiniteIndex]

theorem isPar_iff_walkSum [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) (ψ : Additive Φ →+ R) :
    IsPar Φ ψ ↔ ∀ (i : Fin 3) (v : VΦ Φ), walkSum Φ (edgeVal Φ hΦs ψ) v (faceWord i (faceLen Φ i v)) = 0 := by
  constructor
  · intro h i v
    rw [← char_faceElt_eq_walkSum]
    exact par_faceElt Φ hΦs ψ h i v
  · intro h
    apply isPar_of_faces Φ hΦs ψ
    intro i v
    rw [char_faceElt_eq_walkSum]
    exact h i v

def parKer : Submodule R (VΦ Φ → Fin 2 → R) where
  carrier := {c | (∀ v i, (treeT Φ).tree v i = true → c v i = 0) ∧
    ∀ (i : Fin 3) (v : VΦ Φ), walkSum Φ c v (faceWord i (faceLen Φ i v)) = 0}
  zero_mem' := ⟨fun _ _ _ => rfl, fun i v => by
    have := walkSum_smul Φ (0 : R) (0 : VΦ Φ → Fin 2 → R) v (faceWord i (faceLen Φ i v))
    rwa [zero_smul, zero_mul] at this⟩
  add_mem' := by
    rintro c c' ⟨hc1, hc2⟩ ⟨hc1', hc2'⟩
    refine ⟨fun v i h => ?_, fun i v => ?_⟩
    · show c v i + c' v i = 0
      rw [hc1 v i h, hc1' v i h, add_zero]
    · rw [walkSum_add, hc2, hc2', add_zero]
  smul_mem' := by
    rintro r c ⟨hc1, hc2⟩
    refine ⟨fun v i h => ?_, fun i v => ?_⟩
    · show r • c v i = 0
      rw [hc1 v i h, smul_zero]
    · rw [walkSum_smul, hc2, mul_zero]

noncomputable def parCoordFun [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) : ↥(parSub Φ R) →ₗ[R] parKer (R := R) Φ where
  toFun ψ := ⟨edgeVal Φ hΦs (ψ : Additive Φ →+ R),
    ⟨fun v i h => edgeVal_tree Φ hΦs _ v i h, (isPar_iff_walkSum Φ hΦs (ψ : Additive Φ →+ R)).mp ψ.2⟩⟩
  map_add' ψ ψ' := Subtype.ext (edgeVal_add Φ hΦs (ψ : Additive Φ →+ R) (ψ' : Additive Φ →+ R))
  map_smul' r ψ := Subtype.ext (edgeVal_smul Φ hΦs r (ψ : Additive Φ →+ R))

theorem parCoordFun_bijective [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) : Bijective (parCoordFun (R := R) Φ hΦs) := by
  constructor
  · intro ψ ψ' h
    exact Subtype.ext (edgeVal_injective Φ hΦs (congrArg Subtype.val h))
  · intro c
    have hc1 : ∀ v i, (treeT Φ).tree v i = true → (c : VΦ Φ → Fin 2 → R) v i = 0 := fun v i h => c.2.1 v i h
    have hc2 : ∀ (i : Fin 3) (v : VΦ Φ), walkSum Φ (c : VΦ Φ → Fin 2 → R) v (faceWord i (faceLen Φ i v)) = 0 :=
      fun i v => c.2.2 i v
    have hpar : IsPar Φ (charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R)) := by
      rw [isPar_iff_walkSum Φ hΦs, edgeVal_charOfEdge Φ hΦs _ hc1]
      exact hc2
    exact ⟨⟨charOfEdge Φ hΦs (c : VΦ Φ → Fin 2 → R), hpar⟩, Subtype.ext (edgeVal_charOfEdge Φ hΦs _ hc1)⟩

noncomputable def parCoord [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) : ↥(parSub Φ R) ≃ₗ[R] parKer (R := R) Φ :=
  LinearEquiv.ofBijective (parCoordFun Φ hΦs) (parCoordFun_bijective Φ hΦs)

theorem parCoord_apply [Invertible (2 : R)] (hΦs : Φ ≤ sanovSubgroup) (ψ : ↥(parSub Φ R)) :
    ((parCoord Φ hΦs ψ : parKer (R := R) Φ) : VΦ Φ → Fin 2 → R) = edgeVal Φ hΦs (ψ : Additive Φ →+ R) := rfl

end GlueB
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section PairSumIndexed

variable {Γg : Type*} [Group Γg] {R : Type*} [CommRing R]

theorem omega_comm (φ ψ : Additive Γg →+ R) (g h : Γg) : omega φ ψ h g = - omega φ ψ g h := by
  simp only [omega]
  ring

theorem pairSum_eq_sum_fin (φ ψ : Additive Γg →+ R) (L : List Γg) :
    pairSum φ ψ L = ∑ a : Fin L.length, ∑ b : Fin L.length, if a < b then omega φ ψ L[a.1] L[b.1] else 0 := by
  induction L with
  | nil => simp [pairSum]
  | cons g L ih =>
    rw [pairSum, ih]
    show _ = ∑ a : Fin (L.length + 1), ∑ b : Fin (L.length + 1), if a < b then omega φ ψ (g :: L)[a.1] (g :: L)[b.1] else 0
    rw [Fin.sum_univ_succ]
    congr 1
    ·
      rw [Fin.sum_univ_succ]
      simp only [lt_self_iff_false, ↓reduceIte, zero_add, Fin.succ_pos, Fin.val_succ, List.getElem_cons_succ,
        Fin.val_zero, List.getElem_cons_zero]
      exact (Fin.sum_univ_fun_getElem L (omega φ ψ g)).symm
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [Fin.sum_univ_succ]
      simp only [Fin.not_lt_zero, ↓reduceIte, zero_add, Fin.succ_lt_succ_iff, Fin.val_succ, List.getElem_cons_succ]

theorem omega_mul_left' (φ ψ : Additive Γg →+ R) (a b g : Γg) :
    omega φ ψ (a * b) g = omega φ ψ a g + omega φ ψ b g := by
  simp only [omega, ofMul_mul, map_add]
  ring

theorem pairSum_append (φ ψ : Additive Γg →+ R) (L₁ L₂ : List Γg) :
    pairSum φ ψ (L₁ ++ L₂) = pairSum φ ψ L₁ + pairSum φ ψ L₂ + omega φ ψ L₁.prod L₂.prod := by
  induction L₁ with
  | nil => simp [pairSum, omega_one_left]
  | cons g L₁ ih =>
    rw [List.cons_append, pairSum, ih, pairSum, List.prod_cons, omega_mul_left', List.map_append, List.sum_append,
      ← omega_list_prod φ ψ g L₂]
    ring

theorem pairSum_reverse (φ ψ : Additive Γg →+ R) (L : List Γg) : pairSum φ ψ L.reverse = - pairSum φ ψ L := by
  induction L with
  | nil => simp [pairSum]
  | cons g L ih =>
    rw [List.reverse_cons, pairSum_append, ih]
    simp only [pairSum, List.map_nil, List.sum_nil, List.prod_cons, List.prod_nil, mul_one, add_zero]
    rw [omega_comm, omega_list_prod, List.map_reverse, List.sum_reverse]
    ring

end PairSumIndexed
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section GlueC

open CongruenceSubgroup MulAction Function ModularGroup ModularCurve.Sanov ModularCurve.PDPairing.SanPM ModularCurve.PDPairing.SanThree ModularCurve.PDPairing.Schreier

variable {R : Type*} [CommRing R]
variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex]

omit [Φ.FiniteIndex] in

theorem faceVal_pOf [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (i : Fin 3) (v : VΦ Φ) :
    faceVal Φ (hPrim φ ψ) (U i) (pOf Φ i v) = hPrim φ ψ (stabEquiv Φ hΦs (faceElt Φ i v)) := by
  rw [← pmRep_faceElt Φ hΦs]
  rfl

omit [Φ.FiniteIndex] in

theorem mk_pOf_vOf_mem_orbit (hΦs : Φ ≤ sanovSubgroup) (i : Fin 3) (O : OrbitU Φ i) :
    ((pOf Φ i (vOf Φ hΦs i O) : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) ∈
      orbit (Subgroup.zpowers (U i)) ((O.out.out : ↥(Gamma 2)) : ↥(Gamma 2) ⧸ (pm Φ).subgroupOf (Gamma 2)) := by
  rw [QuotientGroup.out_eq', ← orbitRel_apply]
  apply Quotient.exact
  rw [Quotient.out_eq]
  exact mk_pOf_vOf Φ hΦs i O

theorem pairF_eq_sum_faceElt [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (hΦs : Φ ≤ sanovSubgroup)
    (φ ψ : Additive Φ →+ R) (hφ : IsPar Φ φ) (hψ : IsPar Φ ψ) :
    pairF Φ φ ψ = ∑ i : Fin 3, ∑ O : OrbitU Φ i, hPrim φ ψ (stabEquiv Φ hΦs (faceElt Φ i (vOf Φ hΦs i O))) := by
  have hΦ : (-1 : SL(2, ℤ)) ∉ Φ := neg_one_notMem_of_le_sanov Φ hΦs
  have hle : Φ ≤ Gamma 2 := hΦs.trans sanovSubgroup_le_Gamma_two
  have hF_conj : ∀ (c v : Φ), IsParabolicElt v → hPrim φ ψ (c * v * c⁻¹) = hPrim φ ψ v :=
    fun c v hv => hPrim_conj_of_apply_eq_zero φ ψ v (hφ v hv) (hψ v hv) c
  have hF_pow : ∀ (v : Φ) (k : ℕ), IsParabolicElt v → hPrim φ ψ (v ^ k) = k * hPrim φ ψ v :=
    fun v k _ => hPrim_pow φ ψ v k
  unfold pairF
  rw [cuspSum_eq_two_mul_sum_orbitU Φ hΦ hle (hPrim φ ψ) hF_conj hF_pow, ← mul_assoc, invOf_mul_self, one_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun O _ => ?_
  rw [← faceVal_pOf Φ hΦs φ ψ i (vOf Φ hΦs i O)]
  exact (faceVal_eq_of_same_orbit hΦ (hPrim φ ψ) hF_conj (U i) (sq_trace_U i) _ _ (mk_pOf_vOf_mem_orbit Φ hΦs i O)).symm

noncomputable def letters (hΦs : Φ ≤ sanovSubgroup) (v : VΦ Φ) : List (Fin 2 × Bool) → List Φ
  | [] => []
  | p :: l => stabEquiv Φ hΦs ((treeT Φ).sx (wprod sanL l • v) p) :: letters hΦs v l

omit [Φ.FiniteIndex] in
theorem prod_letters (hΦs : Φ ≤ sanovSubgroup) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    (letters Φ hΦs v l).prod = stabEquiv Φ hΦs ((treeT Φ).wordWalk v l) := by
  induction l with
  | nil => rw [letters, List.prod_nil, TreeTransversal.wordWalk_nil, map_one]
  | cons p l ih => rw [letters, List.prod_cons, ih, TreeTransversal.wordWalk_cons, map_mul]

omit [Φ.FiniteIndex] in
theorem length_letters (hΦs : Φ ≤ sanovSubgroup) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    (letters Φ hΦs v l).length = l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [letters, ih]

omit [Φ.FiniteIndex] in

theorem char_letter (hΦs : Φ ≤ sanovSubgroup) (χ : Additive Φ →+ R) (w : VΦ Φ) (p : Fin 2 × Bool) :
    χ (Additive.ofMul (stabEquiv Φ hΦs ((treeT Φ).sx w p))) = sval Φ (edgeVal Φ hΦs χ) w p := by
  obtain ⟨i, d⟩ := p
  cases d
  · rw [TreeTransversal.sx_false, map_inv, ofMul_inv, map_neg]
    simp only [sval, Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [TreeTransversal.sx_true]
    simp only [sval, ↓reduceIte]
    rfl

omit [Φ.FiniteIndex] in

theorem omega_letter (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (w w' : VΦ Φ) (p p' : Fin 2 × Bool) :
    omega φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx w p)) (stabEquiv Φ hΦs ((treeT Φ).sx w' p')) =
      sval Φ (edgeVal Φ hΦs φ) w p * sval Φ (edgeVal Φ hΦs ψ) w' p' -
        sval Φ (edgeVal Φ hΦs ψ) w p * sval Φ (edgeVal Φ hΦs φ) w' p' := by
  rw [omega, char_letter, char_letter, char_letter, char_letter]

omit [Φ.FiniteIndex] in

theorem hPrim_letter_false [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (w : VΦ Φ) (i : Fin 2) :
    hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx w (i, false))) =
      - hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx ((sanL i)⁻¹ • w) (i, true))) := by
  rw [TreeTransversal.sx_false, TreeTransversal.sx_true, map_inv, hPrim_inv]

omit [Φ.FiniteIndex] in

theorem hPrim_letter_tree [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (w : VΦ Φ) (i : Fin 2)
    (h : (treeT Φ).tree w i = true) : hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).sx w (i, true))) = 0 := by
  rw [TreeTransversal.sx_true, (treeT Φ).x_eq_one_of_tree w i h, map_one, hPrim_one]

omit [Φ.FiniteIndex] in

theorem hPrim_wordWalk [IsFreeGroup Φ] (hΦs : Φ ≤ sanovSubgroup) (φ ψ : Additive Φ →+ R) (v : VΦ Φ) (l : List (Fin 2 × Bool)) :
    hPrim φ ψ (stabEquiv Φ hΦs ((treeT Φ).wordWalk v l)) =
      ((letters Φ hΦs v l).map (hPrim φ ψ)).sum - pairSum φ ψ (letters Φ hΦs v l) := by
  rw [← prod_letters, hPrim_list_prod']

theorem pairF_eq_sum_letters [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (hΦs : Φ ≤ sanovSubgroup)
    (φ ψ : Additive Φ →+ R) (hφ : IsPar Φ φ) (hψ : IsPar Φ ψ) :
    pairF Φ φ ψ = ∑ i : Fin 3, ∑ O : OrbitU Φ i,
      ((((letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O)))).map (hPrim φ ψ)).sum -
        pairSum φ ψ (letters Φ hΦs (vOf Φ hΦs i O) (faceWord i (faceLen Φ i (vOf Φ hΦs i O)))))) := by
  rw [pairF_eq_sum_faceElt Φ hΦs φ ψ hφ hψ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun O _ => ?_
  exact hPrim_wordWalk Φ hΦs φ ψ _ _

end GlueC
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

theorem pairD_swap (Λ Γ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ] [Γ.FiniteIndex] {R : Type*} [CommRing R]
    [Invertible (2 : R)] [Invertible (6 : R)] [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : R)]
    (φ ψ : Additive Γ →+ R) : pairD Λ Γ ψ φ = - pairD Λ Γ φ ψ := by
  unfold pairD
  rw [pairF_swap, mul_neg]

section Assembly

open CongruenceSubgroup

variable {R : Type*} [CommRing R]

private theorem _root_.ModularCurve.PDPairing.TD.cores_cores {K H G' : Subgroup SL(2, ℤ)} (hKH : K ≤ H) (hHG : H ≤ G') [K.FiniteIndex] [H.FiniteIndex]
    (x : Additive K →+ R) :
    cores hHG (cores hKH x) = cores (hKH.trans hHG) x :=
  ModularCurve.PDPairing.T1.cores_cores hKH hHG x

p2m_export "ModularCurve.PDPairing.TD" "cores_cores"
theorem pairF_zero_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] (ψ : Additive Φ →+ R) : pairF Φ 0 ψ = 0 := by
  have h := pairF_smul_left Φ (0 : R) (0 : Additive Φ →+ R) ψ
  rwa [zero_smul, zero_mul] at h

theorem pairF_sum_left (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] [IsFreeGroup Φ] [Invertible (2 : R)]
    [Invertible (6 : R)] {ι : Type*} (S : Finset ι) (f : ι → Additive Φ →+ R) (ψ : Additive Φ →+ R) :
    pairF Φ (∑ i ∈ S, f i) ψ = ∑ i ∈ S, pairF Φ (f i) ψ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pairF_zero_left]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairF_add_left, ih]

def normConj {Φ Γ' : Subgroup SL(2, ℤ)}
    (hnorm : ∀ (s : Γ') (g : Φ), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Φ) (s : Γ') : Φ ≃* Φ where
  toFun g := ⟨(s : SL(2, ℤ))⁻¹ * g * s, by simpa using hnorm s⁻¹ g⟩
  invFun g := ⟨(s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹, hnorm s g⟩
  left_inv g := Subtype.ext (by group)
  right_inv g := Subtype.ext (by group)
  map_mul' g g' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_normConj {Φ Γ' : Subgroup SL(2, ℤ)}
    (hnorm : ∀ (s : Γ') (g : Φ), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Φ) (s : Γ') (g : Φ) :
    ((normConj hnorm s g : Φ) : SL(2, ℤ)) = (s : SL(2, ℤ))⁻¹ * g * s := rfl

theorem pairF_res_cores_normal {Φ Γ' : Subgroup SL(2, ℤ)} (hΦΓ : Φ ≤ Γ') [Φ.FiniteIndex] [Γ'.FiniteIndex]
    [IsFreeGroup Φ] [Invertible (2 : R)] [Invertible (6 : R)] (hΦ1 : (-1 : SL(2, ℤ)) ∉ Φ)
    (hnorm : ∀ (s : Γ') (g : Φ), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Φ)
    (z : Additive Φ →+ R) (y : Additive Γ' →+ R) (hz : IsPar Φ z) (hy : IsPar Γ' y) :
    pairF Φ (res hΦΓ (cores hΦΓ z)) (res hΦΓ y) = (Φ.relIndex Γ' : R) * pairF Φ z (res hΦΓ y) := by
  classical
  set K : Subgroup Γ' := Φ.subgroupOf Γ' with hK
  haveI : Fintype (Γ' ⧸ K) := Fintype.ofFinite _
  let eK : K ≃* Φ := Subgroup.subgroupOfEquivOfLe hΦΓ
  let xK : Additive K →+ R := z.comp (MonoidHom.toAdditive eK.toMonoidHom)
  have hcor : ∀ g : Γ', (cores hΦΓ z) (Additive.ofMul g) =
      coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q) xK g := by
    intro g; rw [coresFun_eq]; rfl

  have htriv : ∀ (g : Φ) (q : Γ' ⧸ K), (Subgroup.inclusion hΦΓ g)⁻¹ • q = q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H s =>
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.eq]
      rw [hK, Subgroup.mem_subgroupOf]
      have h := hnorm s⁻¹ g
      simp only [Subgroup.coe_inv, inv_inv] at h
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using h

  have hsum : res hΦΓ (cores hΦΓ z) =
      ∑ q : Γ' ⧸ K, z.comp (MonoidHom.toAdditive (normConj hnorm (Quotient.out q)).toMonoidHom) := by
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
    rw [AddMonoidHom.finsetSum_apply]
    show (cores hΦΓ z) (Additive.ofMul (Subgroup.inclusion hΦΓ g)) = _
    rw [hcor, coresFun]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    show z (Additive.ofMul (eK (gam K Quotient.out (fun q => QuotientGroup.out_eq' q) q (Subgroup.inclusion hΦΓ g)))) =
      z (Additive.ofMul (normConj hnorm q.out g))
    congr 2
    apply Subtype.ext
    show (((gam K Quotient.out (fun q => QuotientGroup.out_eq' q) q (Subgroup.inclusion hΦΓ g) : K) : Γ') :
      SL(2, ℤ)) = _
    rw [coe_gam, htriv, coe_normConj]
    rfl
  rw [hsum, pairF_sum_left]
  have hterm : ∀ q : Γ' ⧸ K,
      pairF Φ (z.comp (MonoidHom.toAdditive (normConj hnorm q.out).toMonoidHom)) (res hΦΓ y) =
        pairF Φ z (res hΦΓ y) := by
    intro q
    set s : Γ' := q.out
    have hy' : (res hΦΓ y).comp (MonoidHom.toAdditive (normConj hnorm s).toMonoidHom) = res hΦΓ y := by
      refine AddMonoidHom.ext fun g => ?_
      obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
      show y (Additive.ofMul (Subgroup.inclusion hΦΓ (normConj hnorm s g))) =
        y (Additive.ofMul (Subgroup.inclusion hΦΓ g))
      have : Subgroup.inclusion hΦΓ (normConj hnorm s g) = s⁻¹ * Subgroup.inclusion hΦΓ g * s :=
        Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]; rfl)
      rw [this, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
      ring
    have ht := pairF_transport hΦ1 hΦ1 (normConj hnorm s)
      (((s : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos)
      (fun g => by
        rw [coe_normConj]
        have h1 : ((s : SL(2, ℤ)))⁻¹ * (g : SL(2, ℤ)) = ((s : SL(2, ℤ))⁻¹ * g * s) * (s : SL(2, ℤ))⁻¹ := by group
        have h2 := congrArg (fun M : SL(2, ℤ) => (M : Matrix (Fin 2) (Fin 2) ℤ)) h1
        simpa only [Matrix.SpecialLinearGroup.coe_mul] using h2)
      z (res hΦΓ y) hz (isPar_res hΦΓ y hy)
    rw [hy'] at ht
    exact ht
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

@[reducible]
noncomputable def invertibleOfDvd48 [Invertible (2 : R)] [Invertible (6 : R)] (n : ℕ) (hn : n ∣ 48) :
    Invertible (n : R) := by
  have hk : 48 = n * (48 / n) := (Nat.mul_div_cancel' hn).symm
  set k : ℕ := 48 / n
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self _
  have h6 : (6 : R) * ⅟6 = 1 := mul_invOf_self _
  have h48 : (48 : R) * (⅟(2 : R) ^ 3 * ⅟(6 : R)) = 1 := by
    linear_combination (6 * ⅟(6 : R) * (4 * ⅟(2 : R) ^ 2 + 2 * ⅟(2 : R) + 1)) * h2 + h6
  have hnk : (n : R) * k = 48 := by
    have h := congrArg (fun t : ℕ => (t : R)) hk
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    exact h.symm
  have key : (n : R) * ((k : R) * (⅟(2 : R) ^ 3 * ⅟(6 : R))) = 1 := by rw [← mul_assoc, hnk, h48]
  exact ⟨(k : R) * (⅟(2 : R) ^ 3 * ⅟(6 : R)), by rw [mul_comm]; exact key, key⟩

theorem relIndex_inf_Gamma4_dvd (Γ' : Subgroup SL(2, ℤ)) :
    (Γ' ⊓ Gamma 4).relIndex Γ' ∣ (Gamma 4).index := by
  haveI := Gamma_normal 4
  rw [inf_comm, Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_dvd_index_of_normal _ _

private theorem _root_.ModularCurve.PDPairing.TD.index_Gamma_four_impl : (Gamma 4).index = 48 := by
  exact ModularCurve.PDPairing.IDX.index_Gamma_four_impl

p2m_export "ModularCurve.PDPairing.TD" "index_Gamma_four_impl"
noncomputable scoped instance invertibleRelIndexInfGammaFour [Invertible (2 : R)] [Invertible (6 : R)]
    (Γ' : Subgroup SL(2, ℤ)) : Invertible (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) :=
  invertibleOfDvd48 _ (index_Gamma_four_impl ▸ relIndex_inf_Gamma4_dvd Γ')

theorem diag_intertwine (d : ℤ) (g g' : Matrix (Fin 2) (Fin 2) ℤ) (h00 : g' 0 0 = g 0 0) (h01 : g' 0 1 = d * g 0 1)
    (h10 : d * g' 1 0 = g 1 0) (h11 : g' 1 1 = g 1 1) :
    !![d, 0; 0, 1] * g = g' * !![d, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01, h10, h11, mul_comm]

section Aux4Trace
open Matrix Matrix.SpecialLinearGroup

theorem sq_sub_one_eq_zero_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) : (M - 1) ^ 2 = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  ext i j
  rw [sq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    first
      | linear_combination M 0 0 * htr - hdet
      | linear_combination M 0 1 * htr
      | linear_combination M 1 0 * htr
      | linear_combination M 1 1 * htr - hdet

theorem trace_pow_eq_two_of_trace_eq_two (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hdet : M.det = 1) (htr : M.trace = 2) (n : ℕ) : (M ^ n).trace = 2 := by
  have hNN : (M - 1) * (M - 1) = 0 := by
    rw [← sq]; exact sq_sub_one_eq_zero_of_trace_eq_two M hdet htr
  have hsplit : (1 : Matrix (Fin 2) (Fin 2) ℤ) + (M - 1) = M := by abel
  have hNM : (M - 1) * M = M - 1 := by
    calc (M - 1) * M = (M - 1) * (1 + (M - 1)) := by rw [hsplit]
      _ = (M - 1) * 1 + (M - 1) * (M - 1) := by rw [mul_add]
      _ = M - 1 := by rw [mul_one, hNN, add_zero]
  have hpow : ∀ m : ℕ, M ^ m = 1 + m • (M - 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      calc M ^ (k + 1) = M ^ k * M := pow_succ M k
        _ = (1 + k • (M - 1)) * M := by rw [ih]
        _ = 1 * M + (k • (M - 1)) * M := by rw [add_mul]
        _ = M + k • ((M - 1) * M) := by rw [one_mul, smul_mul_assoc]
        _ = M + k • (M - 1) := by rw [hNM]
        _ = 1 + (k + 1) • (M - 1) := by
            rw [succ_nsmul, ← hsplit]
            abel
  rw [hpow n, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, htr, Matrix.trace_one]
  simp [Fintype.card_fin]

theorem sq_trace_pow_eq_four (A : SL(2, ℤ))
    (hA : ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4) (n : ℕ) :
    (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 := by
  set M : Matrix (Fin 2) (Fin 2) ℤ := ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) with hM
  have hdet : M.det = 1 := A.2
  have hcoe : (((A ^ n : SL(2, ℤ)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = M ^ n := by
    simp [hM]
  rw [hcoe]
  have htr : M.trace = 2 ∨ M.trace = -2 := by
    have h0 : (M.trace - 2) * (M.trace + 2) = 0 := by linear_combination hA
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases htr with h2 | hm2
  · rw [trace_pow_eq_two_of_trace_eq_two M hdet h2 n]; norm_num
  · have hdetneg : (-M).det = 1 := by
      rw [Matrix.det_neg]
      simp [hdet, Fintype.card_fin]
    have htrneg : (-M).trace = 2 := by rw [Matrix.trace_neg, hm2]; ring
    have hkey := trace_pow_eq_two_of_trace_eq_two (-M) hdetneg htrneg n
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_pow] at hkey
      rw [hkey]; norm_num
    · rw [ho.neg_pow, Matrix.trace_neg] at hkey
      have hm : (M ^ n).trace = -2 := by linarith
      rw [hm]; norm_num

variable (R : Type*) [CommRing R] (M M' d : ℕ)

theorem trace_conj_SL (b c : SL(2, ℤ)) :
    ((b⁻¹ * c * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = ((c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_mul, coe_mul, Matrix.trace_mul_comm, ← mul_assoc, ← coe_mul, mul_inv_cancel,
    coe_one, one_mul]

end Aux4Trace
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

theorem cores_smul {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (r : R) (x : Additive Φ' →+ R) :
    cores h (r • x) = r • cores h x := by
  classical
  set K : Subgroup Φ := Φ'.subgroupOf Φ with hK
  haveI : Fintype (Φ ⧸ K) := Fintype.ofFinite _
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨g, rfl⟩ : ∃ g₀ : Φ, Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
  have e1 : (cores h (r • x)) (Additive.ofMul g) = coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q)
      ((r • x).comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom)) g := by
    rw [coresFun_eq]; rfl
  have e2 : (cores h x) (Additive.ofMul g) = coresFun K Quotient.out (fun q => QuotientGroup.out_eq' q)
      (x.comp (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe h).toMonoidHom)) g := by
    rw [coresFun_eq]; rfl
  rw [AddMonoidHom.smul_apply, e1, e2, coresFun, coresFun, smul_eq_mul, Finset.mul_sum]
  rfl

theorem isPar_cores {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (x : Additive Φ' →+ R)
    (hx : IsPar Φ' x) : IsPar Φ (cores h x) := by
  classical
  intro u hu
  set K : Subgroup Φ := Φ'.subgroupOf Φ with hK
  haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers u) (Φ ⧸ K))) := Fintype.ofFinite _
  let e : K ≃* Φ' := Subgroup.subgroupOfEquivOfLe h
  let xK : Additive K →+ R := x.comp (MonoidHom.toAdditive e.toMonoidHom)
  show Multiplicative.toAdd (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight xK) u) = 0
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, toAdd_prod]
  refine Finset.sum_eq_zero (fun o _ => ?_)
  show x (Additive.ofMul (e ⟨o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem K u o.out⟩)) = 0
  apply hx
  show ((((o.out.out⁻¹ * u ^ Function.minimalPeriod (u • ·) o.out * o.out.out : Φ)) : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, trace_conj_SL]
  exact sq_trace_pow_eq_four (u : SL(2, ℤ)) hu _

theorem isPar_comp_equiv {Γ' Φ'' : Subgroup SL(2, ℤ)} (e : Γ' ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ)
    (ha : a.det ≠ 0)
    (he : ∀ g : Γ', a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (x' : Additive Γ' →+ R) (hx' : IsPar Γ' x') :
    IsPar Φ'' (x'.comp (MonoidHom.toAdditive e.symm.toMonoidHom)) := by
  intro g hg
  show x' (Additive.ofMul (e.symm g)) = 0
  apply hx'
  have h1 := he (e.symm g)
  rw [MulEquiv.apply_symm_apply] at h1
  rw [← trace_intertwine a _ _ ha h1]
  exact hg

theorem isPar_comp_equiv' {Γ' Φ'' : Subgroup SL(2, ℤ)} (e : Γ' ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ)
    (ha : a.det ≠ 0)
    (he : ∀ g : Γ', a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (y : Additive Φ'' →+ R) (hy : IsPar Φ'' y) :
    IsPar Γ' (y.comp (MonoidHom.toAdditive e.toMonoidHom)) := by
  intro g hg
  show y (Additive.ofMul (e g)) = 0
  apply hy
  rw [trace_intertwine a _ _ ha (he g)]
  exact hg

theorem res_res {Φ₁ Φ₂ Φ₃ : Subgroup SL(2, ℤ)} (h₁₂ : Φ₁ ≤ Φ₂) (h₂₃ : Φ₂ ≤ Φ₃) (y : Additive Φ₃ →+ R) :
    res h₁₂ (res h₂₃ y) = res (h₁₂.trans h₂₃) y :=
  AddMonoidHom.ext fun _ => rfl

theorem res_smul {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) (r : R) (y : Additive Φ →+ R) :
    res h (r • y) = r • res h y :=
  AddMonoidHom.ext fun _ => rfl

theorem neg_one_not_mem_Gamma_four : (-1 : SL(2, ℤ)) ∉ Gamma 4 := by
  intro h
  rw [Gamma_mem] at h
  have h00 := h.1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq, Int.cast_neg, Int.cast_one] at h00
  revert h00
  decide

theorem pairD_cores_transport [Invertible (2 : R)] [Invertible (6 : R)] [IsFreeGroup ↥(Gamma 4)]
    {Γ' Γ'' Φ'' P Q : Subgroup SL(2, ℤ)} [Γ'.FiniteIndex] [Γ''.FiniteIndex] [Φ''.FiniteIndex]
    [(Γ' ⊓ Gamma 4 ⊓ P).FiniteIndex] [(Φ'' ⊓ Gamma 4 ⊓ Q).FiniteIndex]
    (hΦ : Φ'' ≤ Γ'') (e : Γ' ≃* Φ'') (a : Matrix (Fin 2) (Fin 2) ℤ) (ha : 0 < a.det)
    (he : ∀ g : Γ', a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e g : Φ'') : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a)
    (hP : ∀ g : Γ', (g : SL(2, ℤ)) ∈ Gamma 4 → ((g : SL(2, ℤ)) ∈ P ↔ ((e g : Φ'') : SL(2, ℤ)) ∈ Gamma 4))
    (hQ : ∀ h : Φ'', (h : SL(2, ℤ)) ∈ Gamma 4 → ((h : SL(2, ℤ)) ∈ Q ↔ ((e.symm h : Γ') : SL(2, ℤ)) ∈ Gamma 4))
    [Invertible (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R)] [Invertible (((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R)]
    [Invertible (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R)]
    [Invertible (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R)]
    (x' : Additive Γ' →+ R) (y : Additive Γ'' →+ R) (hx' : IsPar Γ' x') (hy : IsPar Γ'' y) :
    pairD (Gamma 4) Γ'' (cores hΦ (x'.comp (MonoidHom.toAdditive e.symm.toMonoidHom))) y =
      pairD (Gamma 4) Γ' x' ((res hΦ y).comp (MonoidHom.toAdditive e.toMonoidHom)) := by
  classical
  haveI hΔn := Gamma_normal 4
  have hΔ1 : (-1 : SL(2, ℤ)) ∉ Gamma 4 := neg_one_not_mem_Gamma_four

  have hΦΓ : Γ'' ⊓ Gamma 4 ≤ Γ'' := inf_le_left
  have h₃ : Φ'' ⊓ Gamma 4 ≤ Φ'' := inf_le_left
  have h₃Φ : Φ'' ⊓ Gamma 4 ≤ Γ'' ⊓ Gamma 4 := inf_le_inf_right (Gamma 4) hΦ
  have h₃Γ : Φ'' ⊓ Gamma 4 ≤ Γ'' := h₃.trans hΦ
  have h₁' : Γ' ⊓ Gamma 4 ≤ Γ' := inf_le_left
  have hΦ₁ : Γ' ⊓ Gamma 4 ⊓ P ≤ Γ' ⊓ Gamma 4 := inf_le_left
  have hΦ₁Γ : Γ' ⊓ Gamma 4 ⊓ P ≤ Γ' := hΦ₁.trans h₁'
  have h₂₃ : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Φ'' ⊓ Gamma 4 := inf_le_left
  have h₂'' : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Φ'' := h₂₃.trans h₃
  have h₂Γ : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Γ'' := h₂''.trans hΦ
  haveI : IsFreeGroup ↥(Γ' ⊓ Gamma 4 ⊓ P) :=
    IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe (hΦ₁.trans inf_le_right : Γ' ⊓ Gamma 4 ⊓ P ≤ Gamma 4))
  haveI : IsFreeGroup ↥(Φ'' ⊓ Gamma 4 ⊓ Q) :=
    IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe (h₂₃.trans inf_le_right : Φ'' ⊓ Gamma 4 ⊓ Q ≤ Gamma 4))
  have hane : a.det ≠ 0 := ne_of_gt ha

  set x'' : Additive Φ'' →+ R := x'.comp (MonoidHom.toAdditive e.symm.toMonoidHom) with hx''def
  have hx'' : IsPar Φ'' x'' := isPar_comp_equiv e a hane he x' hx'
  set y' : Additive Γ' →+ R := (res hΦ y).comp (MonoidHom.toAdditive e.toMonoidHom) with hy'def
  have hy' : IsPar Γ' y' := isPar_comp_equiv' e a hane he (res hΦ y) (isPar_res hΦ y hy)

  set PP : R := pairF (Φ'' ⊓ Gamma 4) (res h₃ x'') (res h₃Γ y) with hPP

  have hm_eq : x'' = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) • cores h₃ (res h₃ x'') := by
    rw [cores_res h₃ x'', smul_smul, invOf_mul_self, one_smul]
  have hL1 : cores hΦ x'' = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) •
      cores hΦΓ (cores h₃Φ (res h₃ x'')) := by
    conv_lhs => rw [hm_eq]
    rw [cores_smul, cores_cores h₃ hΦ, ← cores_cores h₃Φ hΦΓ]
  have hz : IsPar (Γ'' ⊓ Gamma 4) (cores h₃Φ (res h₃ x'')) := isPar_cores h₃Φ _ (isPar_res h₃ x'' hx'')
  have hnorm : ∀ (s : Γ'') (g : ↥(Γ'' ⊓ Gamma 4)),
      (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Γ'' ⊓ Gamma 4 := fun s g =>
    ⟨Γ''.mul_mem (Γ''.mul_mem s.2 g.2.1) (Γ''.inv_mem s.2), hΔn.conj_mem _ g.2.2 _⟩
  have hΦ1 : (-1 : SL(2, ℤ)) ∉ Γ'' ⊓ Gamma 4 := fun h => hΔ1 h.2
  have hLHS : pairD (Gamma 4) Γ'' (cores hΦ x'') y = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) * PP := by
    show ⅟(((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R) *
        pairF (Γ'' ⊓ Gamma 4) (res hΦΓ (cores hΦ x'')) (res hΦΓ y) = _
    rw [hL1, res_smul, pairF_smul_left, pairF_res_cores_normal hΦΓ hΦ1 hnorm _ y hz hy,
      pairF_cores_left h₃Φ (res h₃ x'') (res hΦΓ y) (isPar_res h₃ x'' hx'') (isPar_res hΦΓ y hy), res_res, hPP]
    have hn : ⅟(((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R) * (((Γ'' ⊓ Gamma 4).relIndex Γ'' : ℕ) : R) = 1 :=
      invOf_mul_self _
    linear_combination (⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) *
      pairF (Φ'' ⊓ Gamma 4) (res h₃ x'') (res h₃Γ y)) * hn

  have memP : ∀ g : ↥(Γ' ⊓ Gamma 4 ⊓ P), ((e ⟨g, g.2.1.1⟩ : Φ'') : SL(2, ℤ)) ∈ Φ'' ⊓ Gamma 4 ⊓ Q := by
    intro g
    have hg4 : ((e ⟨g, g.2.1.1⟩ : Φ'') : SL(2, ℤ)) ∈ Gamma 4 := (hP ⟨g, g.2.1.1⟩ g.2.1.2).mp g.2.2
    exact ⟨⟨(e ⟨g, g.2.1.1⟩).2, hg4⟩,
      (hQ (e ⟨g, g.2.1.1⟩) hg4).mpr (by rw [MulEquiv.symm_apply_apply]; exact g.2.1.2)⟩
  have memQ : ∀ h : ↥(Φ'' ⊓ Gamma 4 ⊓ Q), ((e.symm ⟨h, h.2.1.1⟩ : Γ') : SL(2, ℤ)) ∈ Γ' ⊓ Gamma 4 ⊓ P := by
    intro h
    have hh4 : ((e.symm ⟨h, h.2.1.1⟩ : Γ') : SL(2, ℤ)) ∈ Gamma 4 := (hQ ⟨h, h.2.1.1⟩ h.2.1.2).mp h.2.2
    exact ⟨⟨(e.symm ⟨h, h.2.1.1⟩).2, hh4⟩,
      (hP (e.symm ⟨h, h.2.1.1⟩) hh4).mpr (by rw [MulEquiv.apply_symm_apply]; exact h.2.1.2)⟩
  let e₁ : ↥(Γ' ⊓ Gamma 4 ⊓ P) ≃* ↥(Φ'' ⊓ Gamma 4 ⊓ Q) :=
    { toFun := fun g => ⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), memP g⟩
      invFun := fun h => ⟨(e.symm ⟨h, h.2.1.1⟩ : SL(2, ℤ)), memQ h⟩
      left_inv := fun g => by
        apply Subtype.ext
        show ((e.symm ⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), (e ⟨g, g.2.1.1⟩).2⟩ : Γ') : SL(2, ℤ)) = g
        rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
      right_inv := fun h => by
        apply Subtype.ext
        show ((e ⟨(e.symm ⟨h, h.2.1.1⟩ : SL(2, ℤ)), (e.symm ⟨h, h.2.1.1⟩).2⟩ : Φ'') : SL(2, ℤ)) = h
        rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
      map_mul' := fun g g' => by
        apply Subtype.ext
        calc ((e ⟨(g * g' : ↥(Γ' ⊓ Gamma 4 ⊓ P)), (g * g').2.1.1⟩ : Φ'') : SL(2, ℤ))
            = ((e (⟨g, g.2.1.1⟩ * ⟨g', g'.2.1.1⟩) : Φ'') : SL(2, ℤ)) := rfl
          _ = ((e ⟨g, g.2.1.1⟩ * e ⟨g', g'.2.1.1⟩ : Φ'') : SL(2, ℤ)) := by rw [map_mul]
          _ = (e ⟨g, g.2.1.1⟩ : SL(2, ℤ)) * (e ⟨g', g'.2.1.1⟩ : SL(2, ℤ)) := rfl }
  have he₁ : ∀ g : ↥(Γ' ⊓ Gamma 4 ⊓ P), a * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((e₁ g : ↥(Φ'' ⊓ Gamma 4 ⊓ Q)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * a := fun g => he ⟨g, g.2.1.1⟩
  have hΦ₁1 : (-1 : SL(2, ℤ)) ∉ Γ' ⊓ Gamma 4 ⊓ P := fun h => hΔ1 h.1.2
  have hΦ₂1 : (-1 : SL(2, ℤ)) ∉ Φ'' ⊓ Gamma 4 ⊓ Q := fun h => hΔ1 h.1.2

  have hT := pairF_transport hΦ₁1 hΦ₂1 e₁ a ha he₁ (res h₂'' x'') (res h₂Γ y)
    (isPar_res h₂'' x'' hx'') (isPar_res h₂Γ y hy)
  have hxe : (res h₂'' x'').comp (MonoidHom.toAdditive e₁.toMonoidHom) = res hΦ₁Γ x' := by
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Γ' ⊓ Gamma 4 ⊓ P), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
    show x' (Additive.ofMul (e.symm ⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), (memP g).1.1⟩)) =
      x' (Additive.ofMul ⟨g, g.2.1.1⟩)
    rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  have hye : (res h₂Γ y).comp (MonoidHom.toAdditive e₁.toMonoidHom) = res hΦ₁Γ y' := by
    refine AddMonoidHom.ext fun g => ?_
    obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Γ' ⊓ Gamma 4 ⊓ P), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
    show y (Additive.ofMul (⟨(e ⟨g, g.2.1.1⟩ : SL(2, ℤ)), h₂Γ (memP g)⟩ : Γ'')) =
      y (Additive.ofMul (Subgroup.inclusion hΦ (e ⟨g, g.2.1.1⟩)))
    rfl
  rw [hxe, hye] at hT

  have hR1 := pairF_res_res hΦ₁ (res h₁' x') (res h₁' y') (isPar_res h₁' x' hx') (isPar_res h₁' y' hy')
  rw [res_res, res_res] at hR1

  have hR3 := pairF_res_res h₂₃ (res h₃ x'') (res h₃Γ y) (isPar_res h₃ x'' hx'') (isPar_res h₃Γ y hy)
  rw [res_res, res_res] at hR3

  have hRHS : pairD (Gamma 4) Γ' x' y' =
      ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * (⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
        ((((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) * PP)) := by
    show ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * pairF (Γ' ⊓ Gamma 4) (res h₁' x') (res h₁' y') = _
    congr 1
    have hm₁ : ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
        (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) = 1 := invOf_mul_self _
    rw [← hR3, ← hT, hR1, ← mul_assoc, hm₁, one_mul]

  have hmap : (Φ'' ⊓ Gamma 4 ⊓ Q).subgroupOf Φ'' = ((Γ' ⊓ Gamma 4 ⊓ P).subgroupOf Γ').map (e : Γ' →* Φ'') := by
    ext h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hh
      refine ⟨e.symm h, ?_, MulEquiv.apply_symm_apply e h⟩
      rw [Subgroup.mem_subgroupOf]
      exact memQ ⟨h, hh⟩
    · rintro ⟨g, hg, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hg
      exact memP ⟨g, hg⟩
  have hidx : (Γ' ⊓ Gamma 4 ⊓ P).relIndex Γ' = (Φ'' ⊓ Gamma 4 ⊓ Q).relIndex Φ'' := by
    rw [Subgroup.relIndex, Subgroup.relIndex, hmap]
    exact (Subgroup.index_map_equiv ((Γ' ⊓ Gamma 4 ⊓ P).subgroupOf Γ') e).symm
  have key : ((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4)) * ((Γ' ⊓ Gamma 4).relIndex Γ') =
      ((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4)) * ((Φ'' ⊓ Gamma 4).relIndex Φ'') := by
    rw [Subgroup.relIndex_mul_relIndex (Γ' ⊓ Gamma 4 ⊓ P) (Γ' ⊓ Gamma 4) Γ' hΦ₁ h₁',
      Subgroup.relIndex_mul_relIndex (Φ'' ⊓ Gamma 4 ⊓ Q) (Φ'' ⊓ Gamma 4) Φ'' h₂₃ h₃, hidx]
  have hcast : (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) =
      (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) * (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by
    have h := congrArg (fun t : ℕ => (t : R)) key
    simpa only [Nat.cast_mul] using h
  have step : ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
      (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by
    have hA : ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) = 1 :=
      invOf_mul_self _
    have hB : ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
        (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) = 1 := invOf_mul_self _
    have hC : (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) * ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) = 1 :=
      mul_invOf_self _
    calc ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R)
        = ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          (((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) *
            ((((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) * ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R)) := by
            rw [hC, mul_one]
      _ = ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          ((((Φ'' ⊓ Gamma 4 ⊓ Q).relIndex (Φ'' ⊓ Gamma 4) : ℕ) : R) * (((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R)) *
            ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by ring
      _ = ⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * ⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
          ((((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R)) *
            ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by rw [hcast]
      _ = (⅟(((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R) * (((Γ' ⊓ Gamma 4).relIndex Γ' : ℕ) : R)) *
          (⅟(((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R) *
            (((Γ' ⊓ Gamma 4 ⊓ P).relIndex (Γ' ⊓ Gamma 4) : ℕ) : R)) *
            ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by ring
      _ = ⅟(((Φ'' ⊓ Gamma 4).relIndex Φ'' : ℕ) : R) := by rw [hA, hB, one_mul, one_mul]
  rw [hLHS, hRHS, ← mul_assoc, ← mul_assoc, step]

theorem hecke_coset_symm (N : ℕ) (ℓ : ℕ) (hℓN : Nat.Coprime ℓ N) :
    ∃ γ₁ γ₂ : SL(2, ℤ), γ₁ ∈ Gamma0 N ∧ γ₂ ∈ Gamma0 N ∧
      (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by

  obtain ⟨u, v, huv⟩ : IsCoprime (ℓ : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr hℓN

  refine ⟨⟨!![(ℓ : ℤ) * u, v; -(N : ℤ), 1], ?_⟩, ⟨!![(ℓ : ℤ), -v; (N : ℤ), u], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · rw [Gamma0_mem]
    show (((-(N : ℤ)) : ℤ) : ZMod N) = 0
    simp
  · rw [Gamma0_mem]
    show (((N : ℤ) : ℤ) : ZMod N) = 0
    simp
  · show (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(ℓ : ℤ) * u, v; -(N : ℤ), 1] * !![1, 0; 0, (ℓ : ℤ)] * !![(ℓ : ℤ), -v; (N : ℤ), u]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (ℓ : ℤ) * huv
        | linear_combination (-(ℓ : ℤ)) * huv
        | linear_combination huv
        | linear_combination (-1 : ℤ) * huv
        | ring1

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section DescentPerfect

open CongruenceSubgroup

variable {R : Type*} [CommRing R]

theorem cores_add {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] (x y : Additive Φ' →+ R) :
    cores h (x + y) = cores h x + cores h y := by
  unfold cores
  rw [AddMonoidHom.add_comp, toMultiplicativeRight_add, transfer_mul,
    toAdditiveLeft_mul]

noncomputable def coresPar {Φ' Φ : Subgroup SL(2, ℤ)} (h : Φ' ≤ Φ) [Φ'.FiniteIndex] :
    ↥(parSub Φ' R) →ₗ[R] ↥(parSub Φ R) where
  toFun ψ := ⟨cores h (ψ : Additive Φ' →+ R), isPar_cores h _ ψ.2⟩
  map_add' _ _ := Subtype.ext (cores_add h _ _)
  map_smul' r _ := Subtype.ext (cores_smul h r _)

theorem pairD_perfect (Λ Γ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ] [Γ.FiniteIndex] [Λ.Normal]
    (hΛ1 : (-1 : SL(2, ℤ)) ∉ Λ) [Invertible (2 : R)] [Invertible (6 : R)]
    [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : R)]
    (hF : ∀ l' : ↥(parSub (Γ ⊓ Λ) R) →ₗ[R] R, ∃! φ₀' : ↥(parSub (Γ ⊓ Λ) R), ∀ ψ' : ↥(parSub (Γ ⊓ Λ) R),
      pairF (Γ ⊓ Λ) (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R) (ψ' : Additive ↥(Γ ⊓ Λ) →+ R) = l' ψ')
    (l : ↥(parSub Γ R) →ₗ[R] R) :
    ∃! φ₀ : ↥(parSub Γ R), ∀ ψ : ↥(parSub Γ R), pairD Λ Γ (φ₀ : Additive Γ →+ R) (ψ : Additive Γ →+ R) = l ψ := by
  have hΦΓ : Γ ⊓ Λ ≤ Γ := inf_le_left
  have hΦ1 : (-1 : SL(2, ℤ)) ∉ Γ ⊓ Λ := fun h => hΛ1 h.2
  have hnorm : ∀ (s : Γ) (g : ↥(Γ ⊓ Λ)), (s : SL(2, ℤ)) * g * (s : SL(2, ℤ))⁻¹ ∈ Γ ⊓ Λ := fun s g =>
    ⟨Γ.mul_mem (Γ.mul_mem s.2 g.2.1) (Γ.inv_mem s.2), Subgroup.Normal.conj_mem inferInstance _ g.2.2 _⟩
  have hinv : ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) = 1 := invOf_mul_self _

  let l' : ↥(parSub (Γ ⊓ Λ) R) →ₗ[R] R := ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • (l.comp (coresPar hΦΓ))
  have hl' : ∀ ψ' : ↥(parSub (Γ ⊓ Λ) R),
      l' ψ' = ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * l ⟨cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R), isPar_cores hΦΓ _ ψ'.2⟩ :=
    fun ψ' => rfl
  obtain ⟨φ₀', hφ₀', huniq'⟩ := hF l'
  refine ⟨⟨cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R), isPar_cores hΦΓ _ φ₀'.2⟩, ?_, ?_⟩
  · intro ψ
    show ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) *
        pairF (Γ ⊓ Λ) (res hΦΓ (cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R))) (res hΦΓ (ψ : Additive Γ →+ R)) = l ψ
    rw [pairF_res_cores_normal hΦΓ hΦ1 hnorm _ _ φ₀'.2 ψ.2, ← mul_assoc, hinv, one_mul,
      hφ₀' ⟨res hΦΓ (ψ : Additive Γ →+ R), isPar_res hΦΓ _ ψ.2⟩, hl']
    have hc : (⟨cores hΦΓ (res hΦΓ (ψ : Additive Γ →+ R)), isPar_cores hΦΓ _ (isPar_res hΦΓ _ ψ.2)⟩ : ↥(parSub Γ R)) =
        (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • ψ :=
      Subtype.ext (cores_res hΦΓ (ψ : Additive Γ →+ R))
    rw [hc, map_smul, smul_eq_mul, ← mul_assoc, hinv, one_mul]
  · intro φ₁ hφ₁

    have key : ∀ ψ' : ↥(parSub (Γ ⊓ Λ) R),
        pairF (Γ ⊓ Λ) (⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • res hΦΓ (φ₁ : Additive Γ →+ R))
          (ψ' : Additive ↥(Γ ⊓ Λ) →+ R) = l' ψ' := by
      intro ψ'
      have h2 := hφ₁ ⟨cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R), isPar_cores hΦΓ _ ψ'.2⟩
      have h3 : pairF (Γ ⊓ Λ) (res hΦΓ (φ₁ : Additive Γ →+ R)) (res hΦΓ (cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R))) =
          (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * pairF (Γ ⊓ Λ) (res hΦΓ (φ₁ : Additive Γ →+ R)) ψ' := by
        rw [pairF_swap, pairF_res_cores_normal hΦΓ hΦ1 hnorm _ _ ψ'.2 φ₁.2, pairF_swap, mul_neg, neg_neg]
      rw [pairF_smul_left, hl', ← h2]
      show _ = ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * (⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) *
        pairF (Γ ⊓ Λ) (res hΦΓ (φ₁ : Additive Γ →+ R)) (res hΦΓ (cores hΦΓ (ψ' : Additive ↥(Γ ⊓ Λ) →+ R))))
      rw [h3, ← mul_assoc (⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R)) (((Γ ⊓ Λ).relIndex Γ : ℕ) : R), hinv, one_mul]
    have hres : (⟨⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • res hΦΓ (φ₁ : Additive Γ →+ R),
        (parSub (Γ ⊓ Λ) R).smul_mem _ (isPar_res hΦΓ _ φ₁.2)⟩ : ↥(parSub (Γ ⊓ Λ) R)) = φ₀' := huniq' _ key
    apply Subtype.ext
    show (φ₁ : Additive Γ →+ R) = cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R)
    have h4 : cores hΦΓ (res hΦΓ (φ₁ : Additive Γ →+ R)) = (((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • (φ₁ : Additive Γ →+ R) :=
      cores_res hΦΓ _
    have h5 : cores hΦΓ (φ₀' : Additive ↥(Γ ⊓ Λ) →+ R) =
        ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) • cores hΦΓ (res hΦΓ (φ₁ : Additive Γ →+ R)) := by
      rw [← hres, ← cores_smul]
    rw [h5, h4, smul_smul, hinv, one_smul]

end DescentPerfect
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section Inst

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Period"

variable {R : Type*} [CommRing R]

theorem transfer_eq_of_eq {G A : Type*} [Group G] [CommGroup A] {K₁ K₂ : Subgroup G} [K₁.FiniteIndex]
    [K₂.FiniteIndex] (hK : K₁ = K₂) (χ₁ : K₁ →* A) (χ₂ : K₂ →* A)
    (hχ : ∀ (g : G) (h₁ : g ∈ K₁) (h₂ : g ∈ K₂), χ₁ ⟨g, h₁⟩ = χ₂ ⟨g, h₂⟩) :
    MonoidHom.transfer χ₁ = MonoidHom.transfer χ₂ := by
  subst hK
  have : χ₁ = χ₂ := MonoidHom.ext fun x => hχ x x.2 x.2
  subst this
  rfl

section InstPD3

variable (M M' d : ℕ) [NeZero M] [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)

def PhiDeg : Subgroup SL(2, ℤ) := ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd).range).map (Gamma0 M).subtype

omit [NeZero M] [NeZero M'] in
theorem PhiDeg_le : PhiDeg M M' d hMM' hdd ≤ Gamma0 M := Subgroup.map_subtype_le _

noncomputable def eDeg : ↥(Gamma0 M') ≃* ↥(PhiDeg M M' d hMM' hdd) :=
  (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd)).trans
    (Subgroup.equivMapOfInjective _ (Gamma0 M).subtype (Gamma0 M).subtype_injective)

omit [NeZero M] [NeZero M'] in
theorem coe_eDeg (g : ↥(Gamma0 M')) :
    ((eDeg M M' d hMM' hdd g : ↥(PhiDeg M M' d hMM' hdd)) : SL(2, ℤ)) =
      ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) := by
  show ((Subgroup.equivMapOfInjective _ (Gamma0 M).subtype (Gamma0 M).subtype_injective
    (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd) g) : ↥(PhiDeg M M' d hMM' hdd)) :
      SL(2, ℤ)) = _
  rw [Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_subtype, MonoidHom.ofInjective_apply]

omit [NeZero M] [NeZero M'] in
theorem iotaDeg0_entries (g : ↥(Gamma0 M')) :
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 0 0 = (g : SL(2, ℤ)) 0 0 ∧
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 0 1 = (g : SL(2, ℤ)) 0 1 * d ∧
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 1 0 = (g : SL(2, ℤ)) 1 0 / d ∧
    ((ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g : ↥(Gamma0 M)) : SL(2, ℤ)) 1 1 = (g : SL(2, ℤ)) 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [ModularCurve.PDPairing.iotaDeg0, ModularCurve.PDPairing.conjLowerMat]

omit [NeZero M] [NeZero M'] in

theorem eDeg_intertwine (g : ↥(Gamma0 M')) :
    !![(d : ℤ), 0; 0, 1] * ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (((eDeg M M' d hMM' hdd g : ↥(PhiDeg M M' d hMM' hdd)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        !![(d : ℤ), 0; 0, 1] := by
  rw [coe_eDeg]
  obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries M M' d hMM' hdd g
  refine diag_intertwine d _ _ e00 (by rw [e01, mul_comm]) ?_ e11
  rw [e10]
  exact Int.mul_ediv_cancel' (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)

omit [NeZero M] [NeZero M'] in

theorem iDeg0_eq (y : Additive ↥(Gamma0 M) →+ R) :
    ModularCurve.PDPairing.iDeg0 M M' d R R hMM' hdd y =
      (res (PhiDeg_le M M' d hMM' hdd) y).comp (MonoidHom.toAdditive (eDeg M M' d hMM' hdd).toMonoidHom) := by
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Gamma0 M'), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
  show y (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g)) =
    y (Additive.ofMul (Subgroup.inclusion (PhiDeg_le M M' d hMM' hdd) (eDeg M M' d hMM' hdd g)))
  have : ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd g =
      Subgroup.inclusion (PhiDeg_le M M' d hMM' hdd) (eDeg M M' d hMM' hdd g) :=
    Subtype.ext (coe_eDeg M M' d hMM' hdd g).symm
  rw [this]

omit [NeZero M] in

theorem Gamma_le_PhiDeg : Gamma (M' * d) ≤ PhiDeg M M' d hMM' hdd := by
  intro g hg
  have hg0 : g ∈ Gamma0 M := by
    rw [Gamma0_mem]
    rw [Gamma_mem] at hg
    obtain ⟨_, _, h10, _⟩ := hg
    have hdvd : ((M' * d : ℕ) : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    refine dvd_trans ?_ hdvd
    have hM : (M : ℤ) ∣ (M' : ℤ) := by exact_mod_cast hMM'
    exact dvd_trans hM (by push_cast; exact Dvd.intro _ rfl)
  have hr := ModularCurve.PDPairing.Gamma_subgroupOf_le_range_iotaDeg0 M M' d hMM' hdd
    (show (⟨g, hg0⟩ : ↥(Gamma0 M)) ∈ (Gamma (M' * d)).subgroupOf (Gamma0 M) from hg)
  exact ⟨⟨g, hg0⟩, hr, rfl⟩

scoped instance PhiDeg_finiteIndex : (PhiDeg M M' d hMM' hdd).FiniteIndex :=
  haveI : NeZero (M' * d) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne d)⟩
  Subgroup.finiteIndex_of_le (Gamma_le_PhiDeg M M' d hMM' hdd)

omit [NeZero M] in

theorem jDeg0_eq (x' : Additive ↥(Gamma0 M') →+ R) :
    ModularCurve.PDPairing.jDeg0 M M' d R R hMM' hdd x' =
      cores (PhiDeg_le M M' d hMM' hdd) (x'.comp (MonoidHom.toAdditive (eDeg M M' d hMM' hdd).symm.toMonoidHom)) := by
  have hK : (PhiDeg M M' d hMM' hdd).subgroupOf (Gamma0 M) = (ModularCurve.PDPairing.iotaDeg0 M M' d hMM' hdd).range :=
    Subgroup.comap_map_eq_self_of_injective (Gamma0 M).subtype_injective _
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 M M' d R hMM' hdd x'))) =
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      ((x'.comp (MonoidHom.toAdditive (eDeg M M' d hMM' hdd).symm.toMonoidHom)).comp
        (MonoidHom.toAdditive (Subgroup.subgroupOfEquivOfLe (PhiDeg_le M M' d hMM' hdd)).toMonoidHom))))
  congr 1
  refine transfer_eq_of_eq hK.symm _ _ (fun g h₁ h₂ => ?_)

  show Multiplicative.ofAdd (x' (Additive.ofMul
      ((MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd)).symm ⟨g, h₁⟩))) =
    Multiplicative.ofAdd (x' (Additive.ofMul ((eDeg M M' d hMM' hdd).symm
      (Subgroup.subgroupOfEquivOfLe (PhiDeg_le M M' d hMM' hdd) ⟨g, h₂⟩))))
  congr 3
  apply ModularCurve.PDPairing.iotaDeg0_injective M M' d hMM' hdd
  apply Subtype.ext
  rw [MonoidHom.apply_ofInjective_symm]
  have h3 := coe_eDeg M M' d hMM' hdd ((eDeg M M' d hMM' hdd).symm
    (Subgroup.subgroupOfEquivOfLe (PhiDeg_le M M' d hMM' hdd) ⟨g, h₂⟩))
  rw [MulEquiv.apply_symm_apply] at h3
  rw [← h3]
  rfl

end InstPD3
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

theorem relIndex_Gamma0_four_mul_dvd_four (M' d : ℕ) [NeZero M'] [NeZero d] (hd : d ∣ M') :
    (Gamma0 M' ⊓ Gamma 4 ⊓ Gamma0 (4 * d)).relIndex (Gamma0 M' ⊓ Gamma 4) ∣ 4 := by
  classical
  haveI : NeZero (4 * d) := ⟨mul_ne_zero four_ne_zero (NeZero.ne d)⟩
  have h4d : ((4 * d : ℕ) : ℤ) = 4 * (d : ℤ) := by push_cast; ring
  have hdM : (d : ℤ) ∣ (M' : ℤ) := by exact_mod_cast hd
  have hc : ∀ g : ↥(Gamma0 M' ⊓ Gamma 4), (d : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := fun g =>
    dvd_trans hdM ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.2.1))
  have hmul : ∀ g g' : ↥(Gamma0 M' ⊓ Gamma 4),
      ((4 * d : ℕ) : ℤ) ∣ ((g * g' : ↥(Gamma0 M' ⊓ Gamma 4)) : SL(2, ℤ)) 1 0 -
        ((g : SL(2, ℤ)) 1 0 + (g' : SL(2, ℤ)) 1 0) := by
    intro g g'
    have ha' : (4 : ℤ) ∣ (g' : SL(2, ℤ)) 0 0 - 1 := by
      have h := (Gamma_mem.mp g'.2.2).1
      have h' : (((g' : SL(2, ℤ)) 0 0 : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by rw [h, Int.cast_one]
      exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 4).mp h')
    have hd₀ : (4 : ℤ) ∣ (g : SL(2, ℤ)) 1 1 - 1 := by
      have h := (Gamma_mem.mp g.2.2).2.2.2
      have h' : (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by rw [h, Int.cast_one]
      exact dvd_sub_comm.mp ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 4).mp h')
    have hprod : ((g * g' : ↥(Gamma0 M' ⊓ Gamma 4)) : SL(2, ℤ)) 1 0 =
        (g : SL(2, ℤ)) 1 0 * (g' : SL(2, ℤ)) 0 0 + (g : SL(2, ℤ)) 1 1 * (g' : SL(2, ℤ)) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hprod, h4d]
    have e : (g : SL(2, ℤ)) 1 0 * (g' : SL(2, ℤ)) 0 0 + (g : SL(2, ℤ)) 1 1 * (g' : SL(2, ℤ)) 1 0 -
        ((g : SL(2, ℤ)) 1 0 + (g' : SL(2, ℤ)) 1 0) =
      (g : SL(2, ℤ)) 1 0 * ((g' : SL(2, ℤ)) 0 0 - 1) + ((g : SL(2, ℤ)) 1 1 - 1) * (g' : SL(2, ℤ)) 1 0 := by ring
    rw [e]
    refine dvd_add ?_ ?_
    · rw [mul_comm (4 : ℤ)]; exact mul_dvd_mul (hc g) ha'
    · exact mul_dvd_mul hd₀ (hc g')
  let f : ↥(Gamma0 M' ⊓ Gamma 4) →* Multiplicative (ZMod (4 * d)) :=
    { toFun := fun g => Multiplicative.ofAdd ((((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (4 * d)))
      map_one' := by simp
      map_mul' := fun g g' => by
        rw [← ofAdd_add, ← Int.cast_add]
        congr 1
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact dvd_sub_comm.mp (hmul g g') }
  have hker : (Gamma0 M' ⊓ Gamma 4 ⊓ Gamma0 (4 * d)).subgroupOf (Gamma0 M' ⊓ Gamma 4) = f.ker := by
    ext g
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf]
    show (g : SL(2, ℤ)) ∈ Gamma0 M' ⊓ Gamma 4 ∧ (g : SL(2, ℤ)) ∈ Gamma0 (4 * d) ↔
      Multiplicative.ofAdd ((((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (4 * d))) = 1
    rw [Gamma0_mem, ofAdd_eq_one]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  have hrange : f.range ≤ Subgroup.zpowers (Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d))) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨k, hk⟩ := hc g
    refine ⟨k, ?_⟩
    show Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d)) ^ k =
      Multiplicative.ofAdd ((((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod (4 * d)))
    rw [hk, ← ofAdd_zsmul, zsmul_eq_mul, Int.cast_mul]
    exact congrArg Multiplicative.ofAdd (mul_comm _ _)
  have hcard : Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d)))) = 4 := by
    rw [Nat.card_zpowers, orderOf_ofAdd_eq_addOrderOf, Int.cast_natCast,
      ZMod.addOrderOf_coe d (mul_ne_zero four_ne_zero (NeZero.ne d)), Nat.gcd_eq_right (dvd_mul_left d 4),
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne d))]
  calc Nat.card f.range ∣ Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (((d : ℤ)) : ZMod (4 * d)))) :=
        Subgroup.card_dvd_of_le hrange
    _ = 4 := hcard

theorem pairD_jDeg0_iDeg0 [Invertible (2 : R)] [Invertible (6 : R)] [IsFreeGroup ↥(Gamma 4)]
    (M M' d : ℕ) [NeZero M] [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M)
    (x' : Additive ↥(Gamma0 M') →+ R) (y : Additive ↥(Gamma0 M) →+ R)
    (hx' : IsParabolicHom (Gamma0 M') x') (hy : IsParabolicHom (Gamma0 M) y) :
    pairD (Gamma 4) (Gamma0 M) (ModularCurve.PDPairing.jDeg0 M M' d R R hMM' hdd x') y =
      pairD (Gamma 4) (Gamma0 M') x' (ModularCurve.PDPairing.iDeg0 M M' d R R hMM' hdd y) := by
  haveI : NeZero (4 * d) := ⟨mul_ne_zero four_ne_zero (NeZero.ne d)⟩

  haveI : Invertible (((Gamma0 M' ⊓ Gamma 4 ⊓ Gamma0 (4 * d)).relIndex (Gamma0 M' ⊓ Gamma 4) : ℕ) : R) :=
    invertibleOfDvd48 _ (dvd_trans (relIndex_Gamma0_four_mul_dvd_four M' d
      (dvd_trans hdd (Nat.div_dvd_of_dvd hMM'))) (by norm_num))
  haveI : (ModularCurve.PDPairing.Gamma0Upper (4 * d)).FiniteIndex := inferInstance

  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hP : ∀ g : ↥(Gamma0 M'), (g : SL(2, ℤ)) ∈ Gamma 4 →
      ((g : SL(2, ℤ)) ∈ Gamma0 (4 * d) ↔
        ((eDeg M M' d hMM' hdd g : ↥(PhiDeg M M' d hMM' hdd)) : SL(2, ℤ)) ∈ Gamma 4) := by
    intro g hg4
    obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries M M' d hMM' hdd g
    rw [coe_eDeg, Gamma0_mem, Gamma_mem, e00, e01, e10, e11, ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [Gamma_mem] at hg4
    obtain ⟨h00, h01, h10, h11⟩ := hg4
    have hb : ((((g : SL(2, ℤ)) 0 1 * d : ℤ)) : ZMod 4) = 0 := by push_cast; rw [h01, zero_mul]
    constructor
    · intro hc
      refine ⟨h00, hb, ?_, h11⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [Int.dvd_div_iff_mul_dvd (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)]
      have : ((4 * d : ℕ) : ℤ) = (d : ℤ) * 4 := by push_cast; ring
      rwa [this] at hc
    · rintro ⟨-, -, hc, -⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_div_iff_mul_dvd (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)] at hc
      have : ((4 * d : ℕ) : ℤ) = (d : ℤ) * 4 := by push_cast; ring
      rwa [this]
  have hQ : ∀ h : ↥(PhiDeg M M' d hMM' hdd), (h : SL(2, ℤ)) ∈ Gamma 4 →
      ((h : SL(2, ℤ)) ∈ ModularCurve.PDPairing.Gamma0Upper (4 * d) ↔
        (((eDeg M M' d hMM' hdd).symm h : ↥(Gamma0 M')) : SL(2, ℤ)) ∈ Gamma 4) := by
    intro h hh4
    obtain ⟨g, rfl⟩ : ∃ g, eDeg M M' d hMM' hdd g = h := ⟨(eDeg M M' d hMM' hdd).symm h, MulEquiv.apply_symm_apply _ _⟩
    rw [MulEquiv.symm_apply_apply]
    obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries M M' d hMM' hdd g
    rw [coe_eDeg, Gamma_mem, e00, e01, e10, e11] at hh4
    obtain ⟨h00, h01, h10, h11⟩ := hh4
    rw [coe_eDeg, ModularCurve.PDPairing.mem_Gamma0Upper, Gamma_mem, e01, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h4d : ((4 * d : ℕ) : ℤ) = 4 * (d : ℤ) := by push_cast; ring
    have hc4 : (((g : SL(2, ℤ)) 1 0 : ℤ) : ZMod 4) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
      rw [Int.dvd_div_iff_mul_dvd (ModularCurve.PDPairing.dvd_entry0 M M' d hMM' hdd g)] at h10
      exact dvd_trans (dvd_mul_left _ _) h10
    rw [h4d]
    constructor
    · intro hb
      refine ⟨h00, ?_, hc4, h11⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact (mul_dvd_mul_iff_right hd0).mp hb
    · rintro ⟨-, hb, -, -⟩
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hb
      exact mul_dvd_mul hb (dvd_refl _)
  have hdet : 0 < (!![(d : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]
    simp only [mul_one, mul_zero, sub_zero]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  rw [jDeg0_eq, iDeg0_eq]
  exact pairD_cores_transport (Γ' := Gamma0 M') (Γ'' := Gamma0 M) (Φ'' := PhiDeg M M' d hMM' hdd)
    (P := Gamma0 (4 * d)) (Q := ModularCurve.PDPairing.Gamma0Upper (4 * d)) (PhiDeg_le M M' d hMM' hdd) (eDeg M M' d hMM' hdd)
    !![(d : ℤ), 0; 0, 1] hdet (eDeg_intertwine M M' d hMM' hdd) hP hQ x' y hx' hy

section InstPD2

variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

omit [NeZero N] [NeZero ℓ] in
theorem Gamma0_mul_le : Gamma0 (N * ℓ) ≤ Gamma0 N := by
  intro g hg
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg ⊢
  exact dvd_trans (by push_cast; exact Dvd.intro _ rfl) hg

omit [NeZero ℓ] in
theorem mul_div_eq : N * ℓ / N = ℓ := Nat.mul_div_cancel_left ℓ (Nat.pos_of_ne_zero (NeZero.ne N))

omit [NeZero ℓ] in
theorem dvd_mul_div : ℓ ∣ N * ℓ / N := by rw [mul_div_eq]

omit [NeZero N] [NeZero ℓ] in

theorem iDeg0_one_eq_res (φ : Additive ↥(Gamma0 N) →+ R) :
    ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ = res (Gamma0_mul_le N ℓ) φ := by
  refine AddMonoidHom.ext fun g => ?_
  obtain ⟨g, rfl⟩ : ∃ g₀ : ↥(Gamma0 (N * ℓ)), Additive.ofMul g₀ = g := ⟨Additive.toMul g, rfl⟩
  show φ (Additive.ofMul (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g)) =
    φ (Additive.ofMul (Subgroup.inclusion (Gamma0_mul_le N ℓ) g))
  have : ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g = Subgroup.inclusion (Gamma0_mul_le N ℓ) g := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g
    fin_cases i <;> fin_cases j
    · simpa using e00
    · simpa using e01
    · simpa using e10
    · simpa using e11
  rw [this]

theorem heckeT0_eq_jDeg0 (φ : Additive ↥(Gamma0 N) →+ R) :
    ModularCurve.PDPairing.heckeT0 N ℓ R φ =
      ModularCurve.PDPairing.jDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) (res (Gamma0_mul_le N ℓ) φ) := by

  have hmemNℓ : ∀ (h : ↥(Gamma0 N)) (hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1),
      ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb ∈ Gamma0 (N * ℓ) := by
    intro h hb
    rw [Gamma0_mem, ModularCurve.PDPairing.conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hN : (N : ℤ) ∣ (h : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h.2)
    push_cast
    exact mul_dvd_mul hN (dvd_refl _)
  have hιU : ∀ (h : ↥(Gamma0 N)) (hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1),
      ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
        ⟨ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb, hmemNℓ h hb⟩ = h := by
    intro h hb
    apply Subtype.ext
    exact ModularCurve.PDPairing.conjLowerMat_conjUpperMat ℓ (h : SL(2, ℤ)) hb
      (by rw [ModularCurve.PDPairing.conjUpperMat_apply_10]; exact dvd_mul_left _ _)
  have hK : ModularCurve.PDPairing.Gamma0HUpper N ℓ = (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)).range := by
    ext h
    constructor
    · intro hh
      have hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1 := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨h, hh⟩
      exact ⟨_, hιU h hb⟩
    · rintro ⟨g, rfl⟩
      show ((ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g : ↥(Gamma0 N)) : SL(2, ℤ)) ∈
        ModularCurve.PDPairing.Gamma0Upper ℓ
      rw [ModularCurve.PDPairing.mem_Gamma0Upper, (iotaDeg0_entries N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g).2.1,
        Int.cast_mul]
      simp
  show MonoidHom.toAdditiveLeft (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (ModularCurve.PDPairing.conjL0 N ℓ))) =
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 N (N * ℓ) ℓ R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) (res (Gamma0_mul_le N ℓ) φ))))
  congr 1
  refine transfer_eq_of_eq hK _ _ (fun h h₁ h₂ => ?_)
  show Multiplicative.ofAdd (φ (Additive.ofMul (ModularCurve.PDPairing.conjL0 N ℓ ⟨h, h₁⟩))) =
    Multiplicative.ofAdd (φ (Additive.ofMul (Subgroup.inclusion (Gamma0_mul_le N ℓ)
      ((MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ))).symm
        ⟨h, h₂⟩))))
  congr 3
  have hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1 := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨h, h₁⟩
  have hg₀ : (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ)
      (dvd_mul_div N ℓ))).symm ⟨h, h₂⟩ = ⟨ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb, hmemNℓ h hb⟩ := by
    apply ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
    apply Subtype.ext
    rw [MonoidHom.apply_ofInjective_symm, hιU h hb]
  rw [hg₀]
  rfl

theorem transfer_comp_equiv_rel {G G' A : Type*} [Group G] [Group G'] [CommGroup A] (σ : G ≃* G')
    (L : Subgroup G) (L' : Subgroup G') [L.FiniteIndex] [L'.FiniteIndex] (hL : ∀ g, g ∈ L ↔ σ g ∈ L')
    (χ : L →* A) (χ' : L' →* A) (hχ : ∀ (g : G) (h : g ∈ L) (h' : σ g ∈ L'), χ ⟨g, h⟩ = χ' ⟨σ g, h'⟩) :
    (MonoidHom.transfer χ').comp σ.toMonoidHom = MonoidHom.transfer χ := by
  have hK : L'.comap σ.toMonoidHom = L := by
    ext g
    rw [Subgroup.mem_comap]
    exact (hL g).symm
  ext g
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ModularCurve.PDPairing.T1.transfer_congr σ L' χ' g]
  revert g
  rw [← MonoidHom.ext_iff]
  exact transfer_eq_of_eq hK _ _ (fun g h₁ h₂ => (hχ g h₂ h₁).symm)

theorem comp_conj_eq {G A : Type*} [Group G] [CommGroup A] (f : G →* A) (γ : G) :
    f.comp (MulAut.conj γ).toMonoidHom = f := by
  ext g
  show f (γ * g * γ⁻¹) = f g
  rw [map_mul, map_mul, map_inv, mul_comm (f γ) (f g), mul_assoc, mul_inv_cancel, mul_one]

omit [NeZero N] [NeZero ℓ] in
theorem iotaDeg0_one_eq (g : ↥(Gamma0 (N * ℓ))) :
    ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g = Subgroup.inclusion (Gamma0_mul_le N ℓ) g := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) g
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

theorem D_mul_iotaDeg0 (k : ↥(Gamma0 (N * ℓ))) :
    !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (((ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) k :
        ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      ((k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] := by
  obtain ⟨e00, e01, e10, e11⟩ := iotaDeg0_entries N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) k
  have hc : (ℓ : ℤ) * ((k : SL(2, ℤ)) 1 0 / ℓ) = (k : SL(2, ℤ)) 1 0 :=
    Int.mul_ediv_cancel' (ModularCurve.PDPairing.dvd_entry0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) k)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, e00, e01, e10, e11, hc, mul_comm]

omit [NeZero ℓ] in

theorem conjUpperMat_mul_D (h : SL(2, ℤ)) (hb : (ℓ : ℤ) ∣ h 0 1) :
    ((ModularCurve.PDPairing.conjUpperMat ℓ h hb : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] =
      !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hb' : (h : SL(2, ℤ)) 0 1 / ℓ * ℓ = (h : SL(2, ℤ)) 0 1 := Int.ediv_mul_cancel hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularCurve.PDPairing.conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hb', mul_comm]

omit [NeZero ℓ] in

theorem entries_of_intertwine (X Y : Matrix (Fin 2) (Fin 2) ℤ)
    (h : X * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * Y) :
    Y 0 1 = X 0 1 * ℓ ∧ X 1 0 = ℓ * Y 1 0 := by
  have e := fun i j => congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M i j) h
  have e01 := e 0 1
  have e10 := e 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  exact ⟨e01.symm, e10⟩

theorem coset_transport (γ₁ γ₂ g₀ g : SL(2, ℤ))
    (hcoset : (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ))
    (h : !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (g₀ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)]) :
    ((γ₁⁻¹ * g₀ * γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] =
      !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  have hDD' : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] = (ℓ : ℤ) • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hD'smul : ∀ M : Matrix (Fin 2) (Fin 2) ℤ, M * ((ℓ : ℤ) • 1) = ((ℓ : ℤ) • 1) * M := by
    intro M; rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hdetD : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ]

  have e1 : (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] = !![(ℓ : ℤ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
    apply cancel_det hdetD
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hDD', ← Matrix.mul_assoc, hDD', hD'smul]

  have hx : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ₁⁻¹ * g₀ * γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1; group
  have hy : ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1; group
  have hdet1 : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero
  have hdet2 : (γ₂ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero
  apply cancel_det hdet1
  apply cancel_det_right hdet2
  calc (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (((γ₁⁻¹ * g₀ * γ₁ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)]) *
        (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)
      = (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] *
          (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)) := by
          rw [← Matrix.mul_assoc, hx]; simp only [Matrix.mul_assoc]
    _ = (g₀ : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] := by rw [← hcoset]
    _ = !![(ℓ : ℤ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℤ) := e1
    _ = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) *
          (g : Matrix (Fin 2) (Fin 2) ℤ) := by rw [← hcoset]
    _ = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] *
          ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
          simp only [Matrix.mul_assoc, hy]

theorem Gamma0HUpper_eq_range :
    ModularCurve.PDPairing.Gamma0HUpper N ℓ = (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)).range := by
  have hmemNℓ : ∀ (h : ↥(Gamma0 N)) (hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1),
      ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb ∈ Gamma0 (N * ℓ) := by
    intro h hb
    rw [Gamma0_mem, ModularCurve.PDPairing.conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hN : (N : ℤ) ∣ (h : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp h.2)
    push_cast
    exact mul_dvd_mul hN (dvd_refl _)
  ext h
  constructor
  · intro hh
    have hb : (ℓ : ℤ) ∣ (h : SL(2, ℤ)) 0 1 := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨h, hh⟩
    refine ⟨⟨ModularCurve.PDPairing.conjUpperMat ℓ (h : SL(2, ℤ)) hb, hmemNℓ h hb⟩, Subtype.ext ?_⟩
    exact ModularCurve.PDPairing.conjLowerMat_conjUpperMat ℓ (h : SL(2, ℤ)) hb
      (by rw [ModularCurve.PDPairing.conjUpperMat_apply_10]; exact dvd_mul_left _ _)
  · rintro ⟨g, rfl⟩
    show ((ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g : ↥(Gamma0 N)) : SL(2, ℤ)) ∈
      ModularCurve.PDPairing.Gamma0Upper ℓ
    rw [ModularCurve.PDPairing.mem_Gamma0Upper, (iotaDeg0_entries N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) g).2.1,
      Int.cast_mul]
    simp

omit [NeZero N] [NeZero ℓ] in

theorem mem_range_iotaDeg0_one (g : ↥(Gamma0 N)) :
    g ∈ (ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _)).range ↔ (g : SL(2, ℤ)) ∈ Gamma0 (N * ℓ) := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [iotaDeg0_one_eq]
    exact k.2
  · intro hg
    exact ⟨⟨g, hg⟩, by rw [iotaDeg0_one_eq]; rfl⟩

theorem jDeg0_iDeg0_symm (hℓN : Nat.Coprime ℓ N) (ψ : Additive ↥(Gamma0 N) →+ R) :
    ModularCurve.PDPairing.jDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) ψ) =
      ModularCurve.PDPairing.jDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ) := by
  obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hcoset⟩ := hecke_coset_symm N ℓ hℓN
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩

  have hdetD : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ]
  let ιℓ := ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
  let ι₁ := ModularCurve.PDPairing.iotaDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _)
  let σ : ↥(Gamma0 N) ≃* ↥(Gamma0 N) := MulAut.conj (⟨γ₂, hγ₂⟩ : ↥(Gamma0 N))
  have hσ : ∀ g : ↥(Gamma0 N), ((σ g : ↥(Gamma0 N)) : SL(2, ℤ)) = γ₂ * g * γ₂⁻¹ := fun g => rfl

  have hA : ∀ g : ↥(Gamma0 N), g ∈ ι₁.range ↔ σ g ∈ ιℓ.range := by
    intro g
    rw [mem_range_iotaDeg0_one, ← Gamma0HUpper_eq_range]
    constructor
    · intro hg

      have h1 := coset_transport ℓ γ₁ γ₂ _ _ hcoset (D_mul_iotaDeg0 N ℓ ⟨g, hg⟩)
      show ((σ g : ↥(Gamma0 N)) : SL(2, ℤ)) ∈ ModularCurve.PDPairing.Gamma0Upper ℓ
      rw [ModularCurve.PDPairing.mem_Gamma0Upper, hσ, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have e01 := (entries_of_intertwine ℓ _ _ h1).1
      exact ⟨_, by rw [e01, mul_comm]⟩
    · intro hh
      have hb : (ℓ : ℤ) ∣ ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ))) 0 1 := by
        have := ModularCurve.PDPairing.dvd_of_mem_Gamma0HUpper N ℓ ⟨σ g, hh⟩
        rwa [hσ] at this

      have h3 := conjUpperMat_mul_D ℓ (γ₂ * g * γ₂⁻¹) hb

      have hDD' : (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * !![(ℓ : ℤ), 0; 0, 1] = (ℓ : ℤ) • 1 := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      have hdet1 : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
        rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero
      have hdetD' : (!![(ℓ : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]; simp [NeZero.ne ℓ]
      set g' : SL(2, ℤ) := ModularCurve.PDPairing.conjUpperMat ℓ (γ₂ * g * γ₂⁻¹) hb with hg'
      have h4 : !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
          ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] := by
        apply cancel_det_right hdet1
        apply cancel_det_right hdetD
        apply cancel_det_right (a := (γ₂ : Matrix (Fin 2) (Fin 2) ℤ))
          (by rw [Matrix.SpecialLinearGroup.det_coe]; exact one_ne_zero)
        have hx : ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) =
            (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (g' : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]; congr 1; group
        have hy : ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) =
            (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul]; congr 1; group
        calc !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
              (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)
            = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * ((g' : Matrix (Fin 2) (Fin 2) ℤ) *
                !![(1 : ℤ), 0; 0, (ℓ : ℤ)]) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
                rw [Matrix.mul_assoc (!![(1 : ℤ), 0; 0, (ℓ : ℤ)]), hx]; simp only [Matrix.mul_assoc]
          _ = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] *
                ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by rw [h3]
          _ = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)] *
                (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)) * (g : Matrix (Fin 2) (Fin 2) ℤ) := by
                simp only [Matrix.mul_assoc, hy]
          _ = !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * !![(ℓ : ℤ), 0; 0, 1] * (g : Matrix (Fin 2) (Fin 2) ℤ) := by rw [← hcoset]
          _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * (!![(1 : ℤ), 0; 0, (ℓ : ℤ)] * !![(ℓ : ℤ), 0; 0, 1]) := by
                rw [hDD', Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
          _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *
                !![1, 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ)) := by rw [← hcoset, Matrix.mul_assoc]
          _ = (g : Matrix (Fin 2) (Fin 2) ℤ) * !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *
                !![(1 : ℤ), 0; 0, (ℓ : ℤ)] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by simp only [Matrix.mul_assoc]

      have hmem : (γ₁ * g' * γ₁⁻¹ : SL(2, ℤ)) ∈ Gamma0 N := by
        refine (Gamma0 N).mul_mem ((Gamma0 N).mul_mem hγ₁ ?_) ((Gamma0 N).inv_mem hγ₁)
        have : ModularCurve.PDPairing.conjUpperMat ℓ (γ₂ * g * γ₂⁻¹) hb ∈ Gamma0 (N * ℓ) := by
          rw [Gamma0_mem, ModularCurve.PDPairing.conjUpperMat_apply_10, ZMod.intCast_zmod_eq_zero_iff_dvd]
          have hN : (N : ℤ) ∣ ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ))) 1 0 := by
            have := Gamma0_mem.mp (σ g).2
            rw [hσ] at this
            exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
          push_cast
          exact mul_dvd_mul hN (dvd_refl _)
        exact Gamma0_mul_le N ℓ this
      have e10 := (entries_of_intertwine ℓ _ _ h4.symm).2
      rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hN' : (N : ℤ) ∣ ((γ₁ * g' * γ₁⁻¹ : SL(2, ℤ))) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hmem)
      rw [e10]
      push_cast
      rw [mul_comm (N : ℤ) (ℓ : ℤ)]
      exact mul_dvd_mul (dvd_refl _) hN'

  show MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 N (N * ℓ) ℓ R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) ψ)))) =
    MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight
      (ModularCurve.PDPairing.pushChar0 N (N * ℓ) 1 R (dvd_mul_right N ℓ) (one_dvd _)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ))))
  congr 1

  rw [← transfer_comp_equiv_rel σ ι₁.range ιℓ.range hA _ _ ?hχ, comp_conj_eq]
  case hχ =>
    intro g h₁ hℓ'

    show Multiplicative.ofAdd (ψ (Additive.ofMul (ιℓ ((MonoidHom.ofInjective
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _))).symm ⟨g, h₁⟩)))) =
      Multiplicative.ofAdd (ψ (Additive.ofMul (ι₁ ((MonoidHom.ofInjective
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ))).symm ⟨σ g, hℓ'⟩))))
    congr 1
    set k := (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _))).symm
      ⟨g, h₁⟩ with hk
    set k' := (MonoidHom.ofInjective (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ)
      (dvd_mul_div N ℓ))).symm ⟨σ g, hℓ'⟩ with hk'
    have hkg : ((k : ↥(Gamma0 (N * ℓ))) : SL(2, ℤ)) = (g : SL(2, ℤ)) := by
      have e := MonoidHom.apply_ofInjective_symm
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _)) ⟨g, h₁⟩
      rw [← hk, iotaDeg0_one_eq] at e
      exact congrArg (fun x : ↥(Gamma0 N) => (x : SL(2, ℤ))) e
    have hk'σ : ιℓ k' = σ g := by
      have e := MonoidHom.apply_ofInjective_symm
        (ModularCurve.PDPairing.iotaDeg0_injective N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ)) ⟨σ g, hℓ'⟩
      rw [← hk'] at e
      exact e

    have hF1 := D_mul_iotaDeg0 N ℓ k
    rw [hkg] at hF1
    have hT := coset_transport ℓ γ₁ γ₂ _ _ hcoset hF1
    have hF1' := D_mul_iotaDeg0 N ℓ k'
    have hk'mat : (((ιℓ k' : ↥(Gamma0 N)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        ((γ₂ * g * γ₂⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by rw [hk'σ, hσ]
    rw [hk'mat] at hF1'

    have hkk : ((k' : ↥(Gamma0 (N * ℓ))) : SL(2, ℤ)) = γ₁⁻¹ * ((ιℓ k : ↥(Gamma0 N)) : SL(2, ℤ)) * γ₁ := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      have := cancel_det_right hdetD (hF1'.symm.trans hT.symm)
      rw [this]

    have : ι₁ k' = (⟨γ₁, hγ₁⟩ : ↥(Gamma0 N))⁻¹ * ιℓ k * ⟨γ₁, hγ₁⟩ := by
      apply Subtype.ext
      rw [iotaDeg0_one_eq]
      exact hkk
    rw [this, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel

end InstPD2
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

theorem pairD_hecke_selfAdjoint [Invertible (2 : R)] [Invertible (6 : R)] [IsFreeGroup ↥(Gamma 4)]
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ ψ : Additive ↥(Gamma0 N) →+ R) (hφ : IsParabolicHom (Gamma0 N) φ) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.heckeT0 N ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 N) φ (ModularCurve.PDPairing.heckeT0 N ℓ R ψ) := by
  haveI : NeZero (N * ℓ) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  have hcop : Nat.Coprime ℓ N := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN
  have hpar1 : ∀ χ : Additive ↥(Gamma0 N) →+ R, IsParabolicHom (Gamma0 N) χ →
      IsParabolicHom (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) χ) :=
    fun χ hχ => ModularCurve.PDPairing.iDeg0_mem_parabolicHoms R N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) χ hχ
  have hparℓ : ∀ χ : Additive ↥(Gamma0 N) →+ R, IsParabolicHom (Gamma0 N) χ →
      IsParabolicHom (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) χ) :=
    fun χ hχ => ModularCurve.PDPairing.iDeg0_mem_parabolicHoms R N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) χ hχ
  have hL : pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.heckeT0 N ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ) := by
    rw [heckeT0_eq_jDeg0 N ℓ φ, ← iDeg0_one_eq_res N ℓ φ,
      pairD_jDeg0_iDeg0 N (N * ℓ) ℓ (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) _ ψ (hpar1 φ hφ) hψ]
  have hR : pairD (Gamma 4) (Gamma0 N) φ (ModularCurve.PDPairing.heckeT0 N ℓ R ψ) =
      pairD (Gamma 4) (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ) := by
    rw [heckeT0_eq_jDeg0 N ℓ ψ, ← iDeg0_one_eq_res N ℓ ψ, jDeg0_iDeg0_symm N ℓ hcop ψ,
      pairD_swap (Gamma 4) (Gamma0 N)
        (ModularCurve.PDPairing.jDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _)
          (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ)) φ,
      pairD_jDeg0_iDeg0 N (N * ℓ) 1 (dvd_mul_right N ℓ) (one_dvd _) _ φ (hparℓ ψ hψ) hφ,
      pairD_swap (Gamma 4) (Gamma0 (N * ℓ)) (ModularCurve.PDPairing.iDeg0 N (N * ℓ) 1 R R (dvd_mul_right N ℓ) (one_dvd _) φ)
        (ModularCurve.PDPairing.iDeg0 N (N * ℓ) ℓ R R (dvd_mul_right N ℓ) (dvd_mul_div N ℓ) ψ), neg_neg]
  exact hL.trans hR.symm

theorem isPar_iff_isParabolicHom (Γ' : Subgroup SL(2, ℤ)) (φ : Additive Γ' →+ R) :
    IsPar Γ' φ ↔ IsParabolicHom Γ' φ := Iff.rfl

end Inst
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section JointInhabitants

p2m_open "CongruenceSubgroup P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov ModularCurve.Period P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Period"

noncomputable scoped instance isFreeGroup_Gamma_four : IsFreeGroup ↥(Gamma 4) :=
  IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe gamma_four_le_sanov)

noncomputable scoped instance invertibleTwoRat : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
noncomputable scoped instance invertibleSixRat : Invertible (6 : ℚ) := invertibleOfNonzero (by norm_num)

theorem isParabolicHom_zero (Γ : Subgroup SL(2, ℤ)) : IsParabolicHom Γ (0 : Additive Γ →+ ℚ) :=
  fun _ _ => rfl

theorem jointInhabitant_PD2 :
    pairD (Gamma 4) (Gamma0 11) (ModularCurve.PDPairing.heckeT0 11 2 ℚ 0) 0 = pairD (Gamma 4) (Gamma0 11) 0 (ModularCurve.PDPairing.heckeT0 11 2 ℚ 0) :=
  pairD_hecke_selfAdjoint (R := ℚ) 11 2 Nat.prime_two (by norm_num) 0 0 (isParabolicHom_zero _) (isParabolicHom_zero _)

theorem jointInhabitant_PD3 :
    pairD (Gamma 4) (Gamma0 11) (ModularCurve.PDPairing.jDeg0 11 22 2 ℚ ℚ (by norm_num) (by norm_num) 0) 0 =
      pairD (Gamma 4) (Gamma0 22) 0 (ModularCurve.PDPairing.iDeg0 11 22 2 ℚ ℚ (by norm_num) (by norm_num) 0) :=
  pairD_jDeg0_iDeg0 (R := ℚ) 11 22 2 (by norm_num) (by norm_num) 0 0 (isParabolicHom_zero _) (isParabolicHom_zero _)

end JointInhabitants
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section ShapeDiff

p2m_open "CongruenceSubgroup P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov ModularCurve.Period P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Period"

variable {R : Type*} [CommRing R] [Invertible (2 : R)] [Invertible (6 : R)]

theorem neZero_left_of_mul (N q' : ℕ) [h : NeZero (N * q')] : NeZero N :=
  ⟨fun hN => h.out (by rw [hN, zero_mul])⟩

theorem dvd_mul_div_left (N q' : ℕ) [NeZero N] : q' ∣ N * q' / N :=
  ⟨1, by rw [Nat.mul_div_cancel_left q' (Nat.pos_of_ne_zero (NeZero.ne N)), mul_one]⟩

theorem P2_of_PD2_upper (N q' ℓ : ℕ) [NeZero (N * q')] [NeZero ℓ] (hℓ : ℓ.Prime) (hℓNq : ¬ ℓ ∣ N * q')
    (φ ψ : Additive ↥(Gamma0 (N * q')) →+ R)
    (hφ : IsParabolicHom (Gamma0 (N * q')) φ) (hψ : IsParabolicHom (Gamma0 (N * q')) ψ) :
    pairD (Gamma 4) (Gamma0 (N * q')) (ModularCurve.PDPairing.heckeT0 (N * q') ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 (N * q')) φ (ModularCurve.PDPairing.heckeT0 (N * q') ℓ R ψ) :=
  pairD_hecke_selfAdjoint (N * q') ℓ hℓ hℓNq φ ψ hφ hψ

theorem P2_of_PD2_lower (N q' ℓ : ℕ) [NeZero (N * q')] [NeZero ℓ] (hℓ : ℓ.Prime) (hℓNq : ¬ ℓ ∣ N * q')
    (φ ψ : Additive ↥(Gamma0 N) →+ R)
    (hφ : IsParabolicHom (Gamma0 N) φ) (hψ : IsParabolicHom (Gamma0 N) ψ) :
    haveI := neZero_left_of_mul N q'
    pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.heckeT0 N ℓ R φ) ψ =
      pairD (Gamma 4) (Gamma0 N) φ (ModularCurve.PDPairing.heckeT0 N ℓ R ψ) := by
  haveI := neZero_left_of_mul N q'
  exact pairD_hecke_selfAdjoint N ℓ hℓ (fun h => hℓNq (dvd_mul_of_dvd_left h q')) φ ψ hφ hψ

theorem P3_of_PD3_iota0 (N q' : ℕ) [NeZero (N * q')] [NeZero q']
    (x' : Additive ↥(Gamma0 (N * q')) →+ R) (y : Additive ↥(Gamma0 N) →+ R)
    (hx' : IsParabolicHom (Gamma0 (N * q')) x') (hy : IsParabolicHom (Gamma0 N) y) :
    haveI := neZero_left_of_mul N q'
    pairD (Gamma 4) (Gamma0 N) (ModularCurve.PDPairing.jDeg0 N (N * q') 1 R R (dvd_mul_right N q') (one_dvd _) x') y =
      pairD (Gamma 4) (Gamma0 (N * q')) x'
        (ModularCurve.PDPairing.iDeg0 N (N * q') 1 R R (dvd_mul_right N q') (one_dvd _) y) := by
  haveI := neZero_left_of_mul N q'
  exact pairD_jDeg0_iDeg0 N (N * q') 1 (dvd_mul_right N q') (one_dvd _) x' y hx' hy

theorem P3_of_PD3_iota1 (N q' : ℕ) [NeZero (N * q')] [NeZero q']
    (x' : Additive ↥(Gamma0 (N * q')) →+ R) (y : Additive ↥(Gamma0 N) →+ R)
    (hx' : IsParabolicHom (Gamma0 (N * q')) x') (hy : IsParabolicHom (Gamma0 N) y) :
    haveI := neZero_left_of_mul N q'
    pairD (Gamma 4) (Gamma0 N)
        (ModularCurve.PDPairing.jDeg0 N (N * q') q' R R (dvd_mul_right N q') (dvd_mul_div_left N q') x') y =
      pairD (Gamma 4) (Gamma0 (N * q')) x'
        (ModularCurve.PDPairing.iDeg0 N (N * q') q' R R (dvd_mul_right N q') (dvd_mul_div_left N q') y) := by
  haveI := neZero_left_of_mul N q'
  exact pairD_jDeg0_iDeg0 N (N * q') q' (dvd_mul_right N q') (dvd_mul_div_left N q') x' y hx' hy

end ShapeDiff
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section DefPDInhabitants

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Period"

noncomputable example :
    parabolicHoms ℤ (Gamma0 11) ℤ →ₗ[ℤ] parabolicHoms ℤ (Gamma0 11) ℤ →ₗ[ℤ] ℤ :=
  ModularCurve.PDPairing.pairZ 11

theorem defpd_inhabitant_pairZ :
    ModularCurve.PDPairing.pairZ 11 ⟨0, Submodule.zero_mem _⟩ ⟨0, Submodule.zero_mem _⟩ =
      ModularCurve.PDPairing.pairZFun 11 0 0 := rfl

theorem defpd_inhabitant_pairZFun : ∃ z : ℤ, ModularCurve.PDPairing.pairZFun 11 0 0 = z := ⟨_, rfl⟩

theorem defpd_inhabitant_pairD :
    ∃ r : ℚ, ModularCurve.PDPairing.pairD (Gamma 4) (Gamma0 11) (0 : Additive ↥(Gamma0 11) →+ ℚ) 0 = r :=
  ⟨_, rfl⟩

theorem defpd_inhabitant_pairF :
    ∃ r : ℚ, ModularCurve.PDPairing.pairF (Gamma 4) (0 : Additive ↥(Gamma 4) →+ ℚ) 0 = r := ⟨_, rfl⟩

noncomputable example : (Additive ↥(Gamma0 11) →+ ℤ) →+ (Additive ↥(Gamma0 11) →+ ℤ) :=
  ModularCurve.PDPairing.heckeT0 11 2 ℤ

noncomputable example : (Additive ↥(Gamma0 11) →+ ℤ) →ₗ[ℤ] (Additive ↥(Gamma0 22) →+ ℤ) :=
  ModularCurve.PDPairing.iDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num)

noncomputable example : (Additive ↥(Gamma0 22) →+ ℤ) →ₗ[ℤ] (Additive ↥(Gamma0 11) →+ ℤ) :=
  ModularCurve.PDPairing.jDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num)

theorem defpd_inhabitant_heckeT0 : ModularCurve.PDPairing.heckeT0 11 2 ℤ 0 = 0 := map_zero _
theorem defpd_inhabitant_iDeg0 :
    ModularCurve.PDPairing.iDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num) 0 = 0 := map_zero _
theorem defpd_inhabitant_jDeg0 :
    ModularCurve.PDPairing.jDeg0 11 22 2 ℤ ℤ (by norm_num) (by norm_num) 0 = 0 := map_zero _

example : Module ℤ ↥(parabolicHoms ℤ (Gamma0 11) ℤ) := inferInstance
example : AddCommGroup ↥(parabolicHoms ℤ (Gamma0 11) ℤ) := inferInstance

end DefPDInhabitants
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section CastLayer

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Period"

variable {R : Type*} [CommRing R]

def castChar {G : Type*} [MulOneClass G] {A B : Type*} [AddZeroClass A] [AddZeroClass B] (f : A →+ B)
    (φ : Additive G →+ A) : Additive G →+ B :=
  f.comp φ

@[scoped simp] theorem castChar_apply {G : Type*} [MulOneClass G] {A B : Type*} [AddZeroClass A] [AddZeroClass B]
    (f : A →+ B) (φ : Additive G →+ A) (x : Additive G) : castChar f φ x = f (φ x) := rfl

section PrimCast

variable {Φ : Type*} [Group Φ] {S : Type*} [CommRing S]

theorem omega_castChar (f : R →+* S) (φ ψ : Additive Φ →+ R) (g g' : Φ) :
    omega (castChar f.toAddMonoidHom φ) (castChar f.toAddMonoidHom ψ) g g' = f (omega φ ψ g g') := by
  simp only [omega, castChar_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_sub, map_mul]

variable [IsFreeGroup Φ]

theorem hPrim_castChar (f : R →+* S) (φ ψ : Additive Φ →+ R) (g : Φ) :
    hPrim (castChar f.toAddMonoidHom φ) (castChar f.toAddMonoidHom ψ) g = f (hPrim φ ψ g) := by
  symm
  refine hPrim_unique _ _ (fun g => f (hPrim φ ψ g)) ?_ ?_ g
  · intro g g'
    beta_reduce
    rw [hPrim_mul, omega_castChar, map_sub, map_add]
  · intro a
    beta_reduce
    rw [hPrim_of, map_zero]

end PrimCast
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

theorem cuspSum_map (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {S : Type*} [CommRing S] (f : R →+* S) (h : Φ → R) :
    cuspSum Φ (fun g => f (h g)) = f (cuspSum Φ h) := by
  unfold cuspSum
  rw [map_sum]

theorem isParabolicHom_castChar {Γ : Subgroup SL(2, ℤ)} {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) {φ : Additive Γ →+ A} (hφ : IsParabolicHom Γ φ) : IsParabolicHom Γ (castChar f φ) :=
  fun γ hγ => by rw [castChar_apply, hφ γ hγ, map_zero]

theorem coresAdd_castChar {G : Type*} [Group G] (K : Subgroup G) [K.FiniteIndex] {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] (f : A →+ B) (φ : Additive ↥K →+ A) :
    ModularCurve.PDPairing.coresAdd K (castChar f φ) = castChar f (ModularCurve.PDPairing.coresAdd K φ) := by
  ext g
  simp only [ModularCurve.PDPairing.coresAdd, MonoidHom.toAdditiveLeft_apply_apply, castChar_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

theorem heckeT0_castChar (M ℓ : ℕ) [NeZero ℓ] {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B)
    (φ : Additive ↥(Gamma0 M) →+ A) :
    ModularCurve.PDPairing.heckeT0 M ℓ B (castChar f φ) = castChar f (ModularCurve.PDPairing.heckeT0 M ℓ A φ) := by
  ext g
  simp only [ModularCurve.PDPairing.heckeT0_apply, MonoidHom.toAdditiveLeft_apply_apply, castChar_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod, MonoidHom.comp_apply,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, map_sum]

theorem iDeg0_castChar (M M' d : ℕ) [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) {A B : Type*} [CommRing A]
    [CommRing B] (f : A →+ B) (φ : Additive ↥(Gamma0 M) →+ A) :
    ModularCurve.PDPairing.iDeg0 M M' d B B hMM' hdd (castChar f φ) =
      castChar f (ModularCurve.PDPairing.iDeg0 M M' d A A hMM' hdd φ) := by
  ext; rfl

theorem jDeg0_castChar (M M' d : ℕ) [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) {A B : Type*}
    [CommRing A] [CommRing B] (f : A →+ B) (φ : Additive ↥(Gamma0 M') →+ A) :
    ModularCurve.PDPairing.jDeg0 M M' d B B hMM' hdd (castChar f φ) =
      castChar f (ModularCurve.PDPairing.jDeg0 M M' d A A hMM' hdd φ) := by
  show ModularCurve.PDPairing.coresAdd _ (ModularCurve.PDPairing.pushChar0 M M' d B hMM' hdd (castChar f φ)) =
    castChar f (ModularCurve.PDPairing.coresAdd _ (ModularCurve.PDPairing.pushChar0 M M' d A hMM' hdd φ))
  rw [← coresAdd_castChar]
  rfl

abbrev ratChar {G : Type*} [MulOneClass G] (φ : Additive G →+ ℤ) : Additive G →+ ℚ :=
  castChar (Int.castRingHom ℚ).toAddMonoidHom φ

theorem pairZFun_cast [IsFreeGroup ↥(Gamma 4)] (N : ℕ) [NeZero N] (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    ((ModularCurve.PDPairing.pairZFun N φ ψ : ℤ) : ℚ) =
      96 * pairD (Gamma 4) (Gamma0 N) (ratChar φ) (ratChar ψ) := by
  have hn : (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) ∣ 48 := index_Gamma_four_impl ▸ relIndex_inf_Gamma4_dvd (Gamma0 N)
  have hn0 : (((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : ℚ) ≠ 0 := by
    have : (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) ≠ 0 := fun h => by rw [h] at hn; exact absurd hn (by decide)
    exact_mod_cast this
  have hres : ∀ χ : Additive ↥(Gamma0 N) →+ ℤ,
      resInf (Gamma 4) (Gamma0 N) (ratChar χ) = castChar (Int.castRingHom ℚ).toAddMonoidHom (resInf (Gamma 4) (Gamma0 N) χ) :=
    fun χ => rfl
  have hprim : hPrim (resInf (Gamma 4) (Gamma0 N) (ratChar φ)) (resInf (Gamma 4) (Gamma0 N) (ratChar ψ)) =
      fun g => (Int.castRingHom ℚ) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) g) := by
    funext g
    rw [hres, hres, hPrim_castChar]
  unfold ModularCurve.PDPairing.pairZFun pairD pairF
  rw [hprim, cuspSum_map, invOf_eq_inv, invOf_eq_inv, Int.cast_mul, Int.cast_natCast, Nat.cast_div hn hn0]
  simp only [eq_intCast, Nat.cast_ofNat]
  field_simp
  ring

theorem pairZFun_heckeT0_comm [IsFreeGroup ↥(Gamma 4)] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ.Prime)
    (hℓN : ¬ ℓ ∣ N) (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) (hφ : IsParabolicHom (Gamma0 N) φ)
    (hψ : IsParabolicHom (Gamma0 N) ψ) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.heckeT0 N ℓ ℤ φ) ψ =
      ModularCurve.PDPairing.pairZFun N φ (ModularCurve.PDPairing.heckeT0 N ℓ ℤ ψ) := by
  apply Int.cast_injective (α := ℚ)
  rw [pairZFun_cast, pairZFun_cast]
  unfold ratChar
  rw [← heckeT0_castChar, ← heckeT0_castChar]
  congr 1
  exact pairD_hecke_selfAdjoint N ℓ hℓ hℓN _ _ (isParabolicHom_castChar _ hφ) (isParabolicHom_castChar _ hψ)

theorem pairZFun_jDeg0_iDeg0 [IsFreeGroup ↥(Gamma 4)] (N N' d : ℕ) [NeZero N] [NeZero N'] [NeZero d]
    (hNN' : N ∣ N') (hdd : d ∣ N' / N) (x' : Additive ↥(Gamma0 N') →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ)
    (hx' : IsParabolicHom (Gamma0 N') x') (hy : IsParabolicHom (Gamma0 N) y) :
    ModularCurve.PDPairing.pairZFun N (ModularCurve.PDPairing.jDeg0 N N' d ℤ ℤ hNN' hdd x') y =
      ModularCurve.PDPairing.pairZFun N' x' (ModularCurve.PDPairing.iDeg0 N N' d ℤ ℤ hNN' hdd y) := by
  apply Int.cast_injective (α := ℚ)
  rw [pairZFun_cast, pairZFun_cast]
  unfold ratChar
  rw [← jDeg0_castChar, ← iDeg0_castChar]
  congr 1
  exact pairD_jDeg0_iDeg0 N N' d hNN' hdd _ _ (isParabolicHom_castChar _ hx') (isParabolicHom_castChar _ hy)

end CastLayer
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

section B12

p2m_open "CongruenceSubgroup ModularCurve.Period P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Period"

def sixInt : Subring ℚ where
  carrier := {q | ∃ (k : ℕ) (m : ℤ), q = m / 6 ^ k}
  mul_mem' := by
    rintro a b ⟨k, m, rfl⟩ ⟨k', m', rfl⟩
    refine ⟨k + k', m * m', ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  one_mem' := ⟨0, 1, by norm_num⟩
  add_mem' := by
    rintro a b ⟨k, m, rfl⟩ ⟨k', m', rfl⟩
    refine ⟨k + k', m * 6 ^ k' + m' * 6 ^ k, ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  zero_mem' := ⟨0, 0, by norm_num⟩
  neg_mem' := by
    rintro a ⟨k, m, rfl⟩
    exact ⟨k, -m, by push_cast; ring⟩

theorem mem_sixInt_iff (q : ℚ) : q ∈ sixInt ↔ ∃ (k : ℕ) (m : ℤ), q = m / 6 ^ k := Iff.rfl

theorem intCast_mem_sixInt (m : ℤ) : (m : ℚ) ∈ sixInt := ⟨0, m, by norm_num⟩

def intToSix : ℤ →+* ↥sixInt := (Int.castRingHom ↥sixInt)

theorem coe_intToSix (m : ℤ) : ((intToSix m : ↥sixInt) : ℚ) = m := by
  simp [intToSix]

theorem coe_two_sixInt : ((2 : ↥sixInt) : ℚ) = 2 := map_ofNat sixInt.subtype 2
theorem coe_six_sixInt : ((6 : ↥sixInt) : ℚ) = 6 := map_ofNat sixInt.subtype 6

noncomputable scoped instance invertibleTwoSix : Invertible (2 : ↥sixInt) where
  invOf := ⟨1 / 2, 1, 3, by norm_num⟩
  invOf_mul_self := Subtype.ext (by push_cast; rw [coe_two_sixInt]; norm_num)
  mul_invOf_self := Subtype.ext (by push_cast; rw [coe_two_sixInt]; norm_num)

noncomputable scoped instance invertibleSixSix : Invertible (6 : ↥sixInt) where
  invOf := ⟨1 / 6, 1, 1, by norm_num⟩
  invOf_mul_self := Subtype.ext (by push_cast; rw [coe_six_sixInt]; norm_num)
  mul_invOf_self := Subtype.ext (by push_cast; rw [coe_six_sixInt]; norm_num)

theorem int_dvd_of_sixInt_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (x : ℤ) (a : ↥sixInt)
    (h : (x : ↥sixInt) = (p : ↥sixInt) * a) : (p : ℤ) ∣ x := by
  obtain ⟨k, m, hm⟩ := a.2
  have hq : (x : ℚ) = p * (m / 6 ^ k) := by
    have := congrArg (fun t : ↥sixInt => (t : ℚ)) h
    push_cast at this
    rw [this, ← hm]
  have hZ : x * 6 ^ k = p * m := by
    have h6 : (6 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp at hq
    exact_mod_cast hq
  have hp2 : ¬ (p ∣ 2) := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hp3 : ¬ (p ∣ 3) := fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
  have hcop6 : Nat.Coprime p 6 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.coprime_mul_iff_right]
    exact ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hp2, (Nat.Prime.coprime_iff_not_dvd hp).mpr hp3⟩
  have hcop : IsCoprime (p : ℤ) ((6 : ℤ) ^ k) := by
    apply IsCoprime.pow_right
    exact_mod_cast (Nat.isCoprime_iff_coprime.mpr hcop6)
  have hdvd : (p : ℤ) ∣ x * 6 ^ k := ⟨m, by rw [hZ]⟩
  exact hcop.dvd_of_dvd_mul_right hdvd

scoped instance : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

example (N : ℕ) [NeZero N] : Group.FG ↥(Gamma0 N) := inferInstance

theorem exists_common_denominator {G : Type*} [Group G] [Group.FG G] (ψ : Additive G →+ ↥sixInt) :
    ∃ k : ℕ, ∀ g : G, ∃ m : ℤ, ((ψ (Additive.ofMul g) : ↥sixInt) : ℚ) * 6 ^ k = m := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)

  have hden : ∀ g : G, ∃ k : ℕ, ∃ m : ℤ, ((ψ (Additive.ofMul g) : ↥sixInt) : ℚ) * 6 ^ k = m := by
    intro g
    obtain ⟨k, m, hm⟩ := (ψ (Additive.ofMul g)).2
    exact ⟨k, m, by rw [hm]; field_simp⟩
  classical
  choose kf mf hmf using hden
  obtain ⟨s, rfl⟩ := hfin.exists_finset_coe
  refine ⟨s.sum kf, ?_⟩

  have key : ∀ g ∈ Subgroup.closure (s : Set G), ∃ m : ℤ, ((ψ (Additive.ofMul g) : ↥sixInt) : ℚ) * 6 ^ (s.sum kf) = m := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      have hle : kf x ≤ s.sum kf := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨mf x * 6 ^ d, ?_⟩
      rw [hd, pow_add, ← mul_assoc, hmf x]
      push_cast
      ring
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨mx, hx⟩ := ihx
      obtain ⟨my, hy⟩ := ihy
      refine ⟨mx + my, ?_⟩
      rw [ofMul_mul, map_add, Subring.coe_add, add_mul, hx, hy]
      push_cast
      ring
    | inv x _ ihx =>
      obtain ⟨mx, hx⟩ := ihx
      refine ⟨-mx, ?_⟩
      rw [ofMul_inv, map_neg, Subring.coe_neg, neg_mul, hx]
      push_cast
      ring
  intro g
  exact key g (by rw [hS]; exact Subgroup.mem_top g)

theorem exists_common_denominator' {G : Type*} [Group G] [Group.FG G] (ψ : Additive G →+ ↥sixInt) :
    ∃ k : ℕ, ∀ g : G, ∃ m : ℤ, (6 : ↥sixInt) ^ k * ψ (Additive.ofMul g) = (m : ↥sixInt) := by
  obtain ⟨k, hk⟩ := exists_common_denominator ψ
  refine ⟨k, fun g => ?_⟩
  obtain ⟨m, hm⟩ := hk g
  refine ⟨m, Subtype.ext ?_⟩
  push_cast
  rw [coe_six_sixInt, mul_comm]
  exact_mod_cast hm

theorem coe_96_sixInt : ((96 : ↥sixInt) : ℚ) = 96 := map_ofNat sixInt.subtype 96

noncomputable scoped instance invertible96Six : Invertible (96 : ↥sixInt) where
  invOf := ⟨1 / 96, 5, 81, by norm_num⟩
  invOf_mul_self := Subtype.ext (by push_cast; rw [coe_96_sixInt]; norm_num)
  mul_invOf_self := Subtype.ext (by push_cast; rw [coe_96_sixInt]; norm_num)

theorem natCast_ne_zero_sixInt (p : ℕ) (hp : p ≠ 0) : (p : ↥sixInt) ≠ 0 := by
  exact_mod_cast hp

section PairDLin

variable (Λ Γ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ] [Γ.FiniteIndex] {S : Type*} [CommRing S]
  [Invertible (2 : S)] [Invertible (6 : S)] [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : S)]

theorem pairD_add_left (φ₁ φ₂ ψ : Additive Γ →+ S) :
    pairD Λ Γ (φ₁ + φ₂) ψ = pairD Λ Γ φ₁ ψ + pairD Λ Γ φ₂ ψ := by
  unfold pairD
  rw [show resInf Λ Γ (φ₁ + φ₂) = resInf Λ Γ φ₁ + resInf Λ Γ φ₂ from rfl, pairF_add_left, mul_add]

theorem pairD_smul_left (r : S) (φ ψ : Additive Γ →+ S) : pairD Λ Γ (r • φ) ψ = r * pairD Λ Γ φ ψ := by
  unfold pairD
  rw [show resInf Λ Γ (r • φ) = r • resInf Λ Γ φ from rfl, pairF_smul_left]
  ring

theorem pairD_add_right (φ ψ₁ ψ₂ : Additive Γ →+ S) :
    pairD Λ Γ φ (ψ₁ + ψ₂) = pairD Λ Γ φ ψ₁ + pairD Λ Γ φ ψ₂ := by
  rw [pairD_swap, pairD_add_left, neg_add, ← pairD_swap, ← pairD_swap]

theorem pairD_smul_right (r : S) (φ ψ : Additive Γ →+ S) : pairD Λ Γ φ (r • ψ) = r * pairD Λ Γ φ ψ := by
  rw [pairD_swap, pairD_smul_left, pairD_swap]
  ring

noncomputable def pairDRight (φ : Additive Γ →+ S) : ↥(parSub Γ S) →ₗ[S] S where
  toFun ψ := pairD Λ Γ φ (ψ : Additive Γ →+ S)
  map_add' ψ₁ ψ₂ := by
    show pairD Λ Γ φ ((ψ₁ : Additive Γ →+ S) + ψ₂) = _
    rw [pairD_add_right]
  map_smul' r ψ := by
    show pairD Λ Γ φ (r • (ψ : Additive Γ →+ S)) = _
    rw [pairD_smul_right, smul_eq_mul]
    rfl

@[scoped simp] theorem pairDRight_apply (φ : Additive Γ →+ S) (ψ : ↥(parSub Γ S)) :
    pairDRight Λ Γ φ ψ = pairD Λ Γ φ (ψ : Additive Γ →+ S) := rfl

end PairDLin
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

theorem pairZFun_castR [IsFreeGroup ↥(Gamma 4)] (N : ℕ) [NeZero N] {S : Type*} [CommRing S] [Invertible (2 : S)]
    [Invertible (6 : S)] (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    ((ModularCurve.PDPairing.pairZFun N φ ψ : ℤ) : S) =
      96 * pairD (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom φ)
        (castChar (Int.castRingHom S).toAddMonoidHom ψ) := by
  have hn : (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) ∣ 48 := index_Gamma_four_impl ▸ relIndex_inf_Gamma4_dvd (Gamma0 N)
  have h1 : ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * ((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) =
      48 := by rw [← Nat.cast_mul, Nat.div_mul_cancel hn, Nat.cast_ofNat]
  have hA : ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) =
      48 * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) := by
    calc ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S)
        = ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) *
            ((((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S)) := by
          rw [mul_invOf_self, mul_one]
      _ = 48 * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) := by rw [← mul_assoc, h1]
  have hB : (96 : S) * ⅟(2 : S) = 48 := by
    rw [show (96 : S) = 48 * 2 by norm_num, mul_assoc, mul_invOf_self, mul_one]
  have hres : ∀ χ : Additive ↥(Gamma0 N) →+ ℤ,
      resInf (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom χ) =
        castChar (Int.castRingHom S).toAddMonoidHom (resInf (Gamma 4) (Gamma0 N) χ) :=
    fun χ => rfl
  have hprim : hPrim (resInf (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom φ))
      (resInf (Gamma 4) (Gamma0 N) (castChar (Int.castRingHom S).toAddMonoidHom ψ)) =
      fun g => (Int.castRingHom S) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) g) := by
    funext g
    rw [hres, hres, hPrim_castChar]
  unfold ModularCurve.PDPairing.pairZFun pairD pairF
  rw [hprim, cuspSum_map, Int.cast_mul, Int.cast_natCast, hA]
  simp only [eq_intCast]
  set c : S := ((cuspSum (Gamma0 N ⊓ Gamma 4) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ)) : ℤ) : S)
  calc 48 * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * c
      = (96 * ⅟(2 : S)) * ⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * c := by rw [hB]
    _ = 96 * (⅟(((Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : S) * (⅟(2 : S) * c)) := by ring

theorem isPar_castChar_of_mem {Γ' : Subgroup SL(2, ℤ)} {A : Type*} [CommRing A] (f : ℤ →+ A)
    (x : ↥(parabolicHoms ℤ Γ' ℤ)) : IsPar Γ' (castChar f (x : Additive Γ' →+ ℤ)) :=
  (isPar_iff_isParabolicHom Γ' _).mpr (isParabolicHom_castChar f ((mem_parabolicHoms_iff).mp x.2))

theorem exists_eq_smul_of_dvd_apply {Γ' : Subgroup SL(2, ℤ)} (p : ℤ) (hp : p ≠ 0) (x : ↥(parabolicHoms ℤ Γ' ℤ))
    (h : ∀ g : Γ', p ∣ (x : Additive Γ' →+ ℤ) (Additive.ofMul g)) :
    ∃ x' : ↥(parabolicHoms ℤ Γ' ℤ), x = p • x' := by
  classical
  choose c hc using h
  let y : Additive Γ' →+ ℤ :=
    { toFun := fun g => c (Additive.toMul g)
      map_zero' := by
        have h0 := hc 1
        rw [ofMul_one, map_zero] at h0
        have : c 1 = 0 := by
          rcases mul_eq_zero.mp h0.symm with h' | h'
          · exact absurd h' hp
          · exact h'
        simpa using this
      map_add' := by
        intro a b
        apply mul_left_cancel₀ hp
        have ha := hc (Additive.toMul a)
        have hb := hc (Additive.toMul b)
        have hab := hc (Additive.toMul (a + b))
        simp only [ofMul_toMul] at ha hb hab
        rw [mul_add, ← ha, ← hb, ← hab, map_add] }
  have hy : ∀ g : Γ', (x : Additive Γ' →+ ℤ) (Additive.ofMul g) = p * y (Additive.ofMul g) := fun g => hc g
  have hypar : IsParabolicHom Γ' y := by
    intro γ hγ
    have hx0 : (x : Additive Γ' →+ ℤ) (Additive.ofMul γ) = 0 := (mem_parabolicHoms_iff.mp x.2) γ hγ
    have := hy γ
    rw [hx0] at this
    rcases mul_eq_zero.mp this.symm with h' | h'
    · exact absurd h' hp
    · exact h'
  refine ⟨⟨y, mem_parabolicHoms_iff.mpr hypar⟩, Subtype.ext (AddMonoidHom.ext fun g => ?_)⟩
  rw [Submodule.coe_smul, AddMonoidHom.smul_apply, smul_eq_mul]
  exact hy (Additive.toMul g)

theorem P1_of_wall [IsFreeGroup ↥(Gamma 4)] (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hwall : ∀ l' : ↥(parSub (Gamma0 N ⊓ Gamma 4) ↥sixInt) →ₗ[↥sixInt] ↥sixInt,
      ∃! φ₀' : ↥(parSub (Gamma0 N ⊓ Gamma 4) ↥sixInt), ∀ ψ' : ↥(parSub (Gamma0 N ⊓ Gamma 4) ↥sixInt),
        pairF (Gamma0 N ⊓ Gamma 4) (φ₀' : Additive ↥(Gamma0 N ⊓ Gamma 4) →+ ↥sixInt)
          (ψ' : Additive ↥(Gamma0 N ⊓ Gamma 4) →+ ↥sixInt) = l' ψ') :
    (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x') ∧
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ,
        (∀ x : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
          ∃ y' : parabolicHoms ℤ (Gamma0 N) ℤ, y = (p : ℤ) • y') := by
  classical
  haveI : (Gamma 4).Normal := Gamma_normal 4
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpA : (p : ↥sixInt) ≠ 0 := natCast_ne_zero_sixInt p hp.ne_zero

  have hperf := fun l => pairD_perfect (R := ↥sixInt) (Gamma 4) (Gamma0 N) neg_one_not_mem_Gamma_four hwall l
  set ι : ℤ →+ ↥sixInt := (Int.castRingHom ↥sixInt).toAddMonoidHom with hιdef

  have left : ∀ x : parabolicHoms ℤ (Gamma0 N) ℤ,
      (∀ y : parabolicHoms ℤ (Gamma0 N) ℤ, (p : ℤ) ∣ ModularCurve.PDPairing.pairZ N x y) →
        ∃ x' : parabolicHoms ℤ (Gamma0 N) ℤ, x = (p : ℤ) • x' := by
    intro x hx
    set xA : ↥(parSub (Gamma0 N) ↥sixInt) := ⟨castChar ι (x : Additive ↥(Gamma0 N) →+ ℤ), isPar_castChar_of_mem ι x⟩
      with hxAdef

    have hvals : ∀ z : ↥(parSub (Gamma0 N) ↥sixInt),
        ∃ a : ↥sixInt, 96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z = p * a := by
      intro z
      obtain ⟨k, hk⟩ := exists_common_denominator' (G := ↥(Gamma0 N)) (z : Additive ↥(Gamma0 N) →+ ↥sixInt)
      choose m hm using hk

      let y : Additive ↥(Gamma0 N) →+ ℤ :=
        { toFun := fun g => m (Additive.toMul g)
          map_zero' := by
            have h0 := hm 1
            rw [ofMul_one, map_zero, mul_zero] at h0
            exact_mod_cast (by simpa using h0.symm : ((m 1 : ℤ) : ↥sixInt) = 0)
          map_add' := by
            intro a b
            have ha := hm (Additive.toMul a)
            have hb := hm (Additive.toMul b)
            have hab := hm (Additive.toMul (a + b))
            simp only [ofMul_toMul] at ha hb hab
            rw [map_add, mul_add, ha, hb] at hab
            rw [toMul_add]
            exact_mod_cast hab.symm }
      have hy : castChar ι y = (6 : ↥sixInt) ^ k • (z : Additive ↥(Gamma0 N) →+ ↥sixInt) := by
        refine AddMonoidHom.ext fun g => ?_
        rw [castChar_apply, AddMonoidHom.smul_apply, smul_eq_mul]
        show ι (m (Additive.toMul g)) = 6 ^ k * (z : Additive ↥(Gamma0 N) →+ ↥sixInt) g
        have := hm (Additive.toMul g)
        simp only [ofMul_toMul] at this
        rw [this, hιdef]
        simp
      have hypar : IsParabolicHom (Gamma0 N) y := by
        intro γ hγ
        have hz : (z : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul γ) = 0 :=
          (show IsPar (Gamma0 N) (z : Additive ↥(Gamma0 N) →+ ↥sixInt) from z.2) γ hγ
        have := hm γ
        rw [hz, mul_zero] at this
        exact_mod_cast (show ((m γ : ℤ) : ↥sixInt) = 0 from this.symm)

      obtain ⟨c, hc⟩ := hx ⟨y, mem_parabolicHoms_iff.mpr hypar⟩
      have hcast := pairZFun_castR (S := ↥sixInt) N (x : Additive ↥(Gamma0 N) →+ ℤ) y
      rw [ModularCurve.PDPairing.pairZ_apply] at hc
      rw [hc] at hcast

      have hsc : 96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt)
          ((6 : ↥sixInt) ^ k • (z : Additive ↥(Gamma0 N) →+ ↥sixInt)) = p * (c : ↥sixInt) := by
        rw [← hιdef] at hcast
        rw [← hy]
        exact_mod_cast hcast.symm
      rw [pairD_smul_right] at hsc
      refine ⟨⅟(6 : ↥sixInt) ^ k * c, ?_⟩
      calc 96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z
          = (⅟(6 : ↥sixInt) ^ k * (6 : ↥sixInt) ^ k) *
              (96 * pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z) := by
            rw [← mul_pow, invOf_mul_self, one_pow, one_mul]
        _ = ⅟(6 : ↥sixInt) ^ k * (96 * ((6 : ↥sixInt) ^ k *
              pairD (Gamma 4) (Gamma0 N) (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) z)) := by ring
        _ = ⅟(6 : ↥sixInt) ^ k * (p * c) := by rw [hsc]
        _ = p * (⅟(6 : ↥sixInt) ^ k * c) := by ring

    choose μf hμf using hvals
    let μ' : ↥(parSub (Gamma0 N) ↥sixInt) →ₗ[↥sixInt] ↥sixInt :=
      { toFun := μf
        map_add' := by
          intro z₁ z₂
          apply mul_left_cancel₀ hpA
          rw [mul_add, ← hμf, ← hμf, ← hμf, Submodule.coe_add, pairD_add_right, mul_add]
        map_smul' := by
          intro r z
          apply mul_left_cancel₀ hpA
          rw [RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hμf, ← hμf, Submodule.coe_smul, pairD_smul_right]
          ring }

    obtain ⟨x', hx', -⟩ := hperf μ'
    have hrep : ∀ z : ↥(parSub (Gamma0 N) ↥sixInt),
        pairD (Gamma 4) (Gamma0 N) (((p : ↥sixInt) • x' : ↥(parSub (Gamma0 N) ↥sixInt)) : Additive ↥(Gamma0 N) →+ ↥sixInt) z =
          pairD (Gamma 4) (Gamma0 N) (((96 : ↥sixInt) • xA : ↥(parSub (Gamma0 N) ↥sixInt)) : Additive ↥(Gamma0 N) →+ ↥sixInt) z := by
      intro z
      rw [Submodule.coe_smul, Submodule.coe_smul, pairD_smul_left, pairD_smul_left, hx' z]
      exact (hμf z).symm
    have huniq := (hperf (pairDRight (Gamma 4) (Gamma0 N)
      (((96 : ↥sixInt) • xA : ↥(parSub (Gamma0 N) ↥sixInt)) : Additive ↥(Gamma0 N) →+ ↥sixInt))).unique
      (y₁ := (p : ↥sixInt) • x') (y₂ := (96 : ↥sixInt) • xA)
      (fun z => by rw [pairDRight_apply]; exact hrep z) (fun z => by rw [pairDRight_apply])

    have hdiv : ∀ g : ↥(Gamma0 N), (p : ℤ) ∣ (x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g) := by
      intro g
      have hg := congrArg (fun t : ↥(parSub (Gamma0 N) ↥sixInt) => (t : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul g)) huniq
      simp only [Submodule.coe_smul, AddMonoidHom.smul_apply, smul_eq_mul] at hg

      have hxA : (xA : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul g) = ι ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g)) := rfl
      rw [hxA, hιdef] at hg
      apply int_dvd_of_sixInt_dvd p hp hp5 _ (⅟(96 : ↥sixInt) * (x' : Additive ↥(Gamma0 N) →+ ↥sixInt) (Additive.ofMul g))
      have : ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g) : ↥sixInt) =
          ⅟(96 : ↥sixInt) * (96 * ((x : Additive ↥(Gamma0 N) →+ ℤ) (Additive.ofMul g) : ↥sixInt)) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
      rw [this]
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, eq_intCast] at hg
      rw [← hg]
      ring
    exact exists_eq_smul_of_dvd_apply (p : ℤ) hp0 x hdiv
  refine ⟨left, ?_⟩

  intro y hy
  apply left y
  intro z
  have hswap : ModularCurve.PDPairing.pairZ N y z = - ModularCurve.PDPairing.pairZ N z y := by
    rw [ModularCurve.PDPairing.pairZ_apply, ModularCurve.PDPairing.pairZ_apply, ModularCurve.PDPairing.pairZFun_swap]
  rw [hswap]
  exact (dvd_neg).mpr (hy z)

end B12
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

end ModularCurve.PDPairing.TD
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"
p2m_reactivate "P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.Sanov P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanPM P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.SanThree P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier.TreeTransversal P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.Schreier P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.BaseTwo P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.T1 P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD"

theorem solution : (CongruenceSubgroup.Gamma 4).index = 48 :=
  ModularCurve.PDPairing.IDX.index_Gamma_four_impl

end S_ModularCurve_PDPairing_index_Gamma_four
end P2MW
export P2MW.S_ModularCurve_PDPairing_index_Gamma_four (solution)

-- Prove2me | solution 1 for ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/53bd0787-f131-5365-a273-19138f9c364c

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
p2m_open_scoped "MatrixGroups ModularForm P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm OnePoint"

namespace ModularForm
p2m_export "ModularForm" "rec ext heckeMatrix heckeDiagMatrix heckeU heckeT heckeU_def heckeT_eq_heckeU_add"
p2m_open "ModularForm"

namespace HeckeGamma1

@[scoped simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧ g' 1 1 = g 1 1 - g 1 0 * j' ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = p * g 1 1 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = e ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = e ∧ g' 1 1 = g 1 1 ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0, p * g 0 1; e, g 1 1], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section reindex

variable {p : ℕ} [NeZero p]

theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ Finset.range p, F j = ∑ x : ZMod p, F x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

theorem heckeU_eq_sum_zmod (k : ℤ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

end reindex

section heckeT

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[scoped simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[scoped simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

theorem heckeT_eq_sum_onePoint [NeZero p] (k : ℤ) (f : ℍ → ℂ) :
    heckeT k p f = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x := by
  rw [heckeT_eq_heckeU_add, heckeU_eq_sum_zmod, add_comm]
  exact (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] heckeRep p x)).symm

variable [Fact p.Prime]

variable (p) in

def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) - ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)
          = 1 by linear_combination this]
      exact one_ne_zero)

@[scoped simp] theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[scoped simp] theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

def wt (N p : ℕ) (x : OnePoint (ZMod p)) : ZMod N := x.elim (p : ZMod N) (fun _ => 1)

@[scoped simp] theorem wt_infty {N : ℕ} : wt N p ∞ = (p : ZMod N) := rfl

@[scoped simp] theorem wt_coe {N : ℕ} (j : ZMod p) : wt N p j = 1 := rfl

theorem isUnit_wt {N : ℕ} (hpN : ¬ p ∣ N) (x : OnePoint (ZMod p)) : IsUnit (wt N p x) := by
  induction x using OnePoint.rec with
  | infty => exact ZMod.isUnit_prime_of_not_dvd Fact.out hpN
  | coe j => exact isUnit_one

theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 N)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      ((g' 1 1 : ℤ) : ZMod N) * wt N p x = wt N p (redMatrix p g • x) ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨hgA, hgD, hgC⟩ := (CongruenceSubgroup.Gamma1_mem N g).mp hg
  have hgN : (N : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using hgC)
  have hgD' : ((g 1 1 : ℤ) : ZMod N) = 1 := by simpa using hgD
  have hgC' : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using hgC
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    ·
      rw [if_pos (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      obtain ⟨g', hg', hd', hmul⟩ := heckeDiagMatrix_mul_of_eq' hp g e he
      refine ⟨g', ?_, ?_, hmul⟩
      · rw [hg']
        have hcop : IsCoprime (N : ℤ) (p : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm
        exact hcop.dvd_of_dvd_mul_left (he ▸ hgN)
      · rw [hd', hgD', wt_infty, one_mul]
    ·
      rw [if_neg (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0
        with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      obtain ⟨g', hg', hd', hmul⟩ := heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
      refine ⟨g', hg' ▸ hgN, ?_, hmul⟩
      rw [hd', wt_infty, wt_coe]
      have : ((g 1 1 : ℤ) : ZMod N) = ((g 1 0 : ℤ) : ZMod N) * (y.val : ℤ) + (p : ℤ) * e := by
        have := congrArg (Int.cast : ℤ → ZMod N) (show g 1 1 = g 1 0 * y.val + p * e by linear_combination he)
        push_cast at this ⊢
        exact this
      rw [hgD', hgC', zero_mul, zero_add] at this
      push_cast at this
      rw [mul_comm]
      exact this.symm
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0
    ·
      rw [if_pos h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      obtain ⟨g', hg', hd', hmul⟩ := heckeMatrix_mul_of_eq' hp g j.val e he
      refine ⟨g', hg' ▸ hgN, ?_, hmul⟩
      rw [hd', wt_infty, wt_coe, mul_one]
      push_cast
      rw [hgD', mul_one]
    ·
      rw [if_neg h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
        (redMatrix p g 1 0 * j + redMatrix p g 1 1) with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
            = redMatrix p g 1 0 * j + redMatrix p g 1 1 by
              rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
          hy, div_mul_cancel₀ _ h, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
        ring
      obtain ⟨g', hg', hd', hmul⟩ := heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)
      refine ⟨g', hg' ▸ dvd_mul_of_dvd_right hgN _, ?_, hmul⟩
      rw [hd', wt_coe, wt_coe, mul_one]
      push_cast
      rw [hgD', hgC', zero_mul, sub_zero]

variable {N : ℕ} (k : ℤ)

def lift (σ : SL(2, ℤ)) (x : OnePoint (ZMod p)) : SL(2, ℤ) := x.elim σ (fun _ => 1)

@[scoped simp] theorem lift_infty (σ : SL(2, ℤ)) : lift (p := p) σ ∞ = σ := rfl

@[scoped simp] theorem lift_coe (σ : SL(2, ℤ)) (j : ZMod p) : lift σ (j : OnePoint (ZMod p)) = 1 := rfl

theorem lift_mem (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (x : OnePoint (ZMod p)) :
    lift σ x ∈ CongruenceSubgroup.Gamma0 N := by
  induction x using OnePoint.rec with
  | infty => exact hσ
  | coe j => exact one_mem _

theorem lift_apply_one_one (σ : SL(2, ℤ)) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p) (x : OnePoint (ZMod p)) :
    (((lift σ x) 1 1 : ℤ) : ZMod N) = wt N p x := by
  induction x using OnePoint.rec with
  | infty => exact hσp
  | coe j => simp

theorem sum_eq (f : ℍ → ℂ) (σ : SL(2, ℤ)) :
    heckeU k p f + (f ∣[k] mapGL ℝ σ) ∣[k] heckeDiagMatrix p
      = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [heckeU_eq_sum_zmod, add_comm, ← SlashAction.slash_mul]
  refine Eq.trans ?_
    (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x))).symm
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change f ∣[k] heckeMatrix p j.val = f ∣[k] (mapGL ℝ (lift σ (j : OnePoint (ZMod p))) * heckeRep p j)
  rw [lift_coe, map_one, one_mul, heckeRep_coe]

theorem d_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ CongruenceSubgroup.Gamma0 N)
    (h₂ : γ₂ ∈ CongruenceSubgroup.Gamma0 N) :
    (((γ₁ * γ₂) 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N) := by
  have := map_mul (CongruenceSubgroup.Gamma0Map N) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using CongruenceSubgroup.Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
  push_cast at this
  rw [hc] at this
  linear_combination this

theorem mem_Gamma1_of_d_eq_one {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hd : ((γ 1 1 : ℤ) : ZMod N) = 1) : γ ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
  exact ⟨by simpa using ha, by simpa using hd, by simpa using CongruenceSubgroup.Gamma0_mem.mp hγ⟩

theorem isUnit_p (hpN : ¬ p ∣ N) : IsUnit (p : ZMod N) :=
  ZMod.isUnit_prime_of_not_dvd Fact.out hpN

theorem sum_slash_mapGL (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 N) :
    (∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] (mapGL ℝ g)
      = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [SlashAction.sum_slash]
  calc ∑ x : OnePoint (ZMod p), (f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] mapGL ℝ g
      = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ (redMatrix p g • x))
          * heckeRep p (redMatrix p g • x)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hd', hmul⟩ := heckeRep_mul hpN g hg x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N :=
          CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg')

        set D : SL(2, ℤ) := lift σ x * g' * (lift σ (redMatrix p g • x))⁻¹ with hD
        have hDmem0 : D ∈ CongruenceSubgroup.Gamma0 N :=
          mul_mem (mul_mem (lift_mem σ hσ x) hg'N) (inv_mem (lift_mem σ hσ _))
        have hDd : ((D 1 1 : ℤ) : ZMod N) = 1 := by

          have hprod : D * lift σ (redMatrix p g • x) = lift σ x * g' := by
            rw [hD, inv_mul_cancel_right]
          have h1 := congrArg (fun γ : SL(2, ℤ) => ((γ 1 1 : ℤ) : ZMod N)) hprod
          rw [d_mul hDmem0 (lift_mem σ hσ _), d_mul (lift_mem σ hσ x) hg'N,
            lift_apply_one_one σ hσp, lift_apply_one_one σ hσp, mul_comm (wt N p x), hd'] at h1

          have hu : IsUnit (wt N p (redMatrix p g • x)) := isUnit_wt hpN _
          exact hu.mul_left_injective (h1.trans (one_mul _).symm)
        have hDmem : D ∈ CongruenceSubgroup.Gamma1 N := mem_Gamma1_of_d_eq_one hDmem0 hDd
        have hfactor : mapGL ℝ (lift σ x) * heckeRep p x * mapGL ℝ g
            = mapGL ℝ D * (mapGL ℝ (lift σ (redMatrix p g • x)) * heckeRep p (redMatrix p g • x)) := by
          rw [mul_assoc, hmul, ← mul_assoc, ← map_mul, hD, ← mul_assoc, ← map_mul,
            inv_mul_cancel_right]
        rw [← SlashAction.slash_mul, hfactor, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hDmem)]
    _ = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) :=
        Equiv.sum_comp (MulAction.toPerm (redMatrix p g))
          (fun x ↦ f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x))

end heckeT

end HeckeGamma1
p2m_reactivate "P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm.HeckeGamma1"

end ModularForm
p2m_reactivate "P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm.HeckeGamma1 P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm"

end
p2m_reactivate "P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm.HeckeGamma1 P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm"

open scoped MatrixGroups _root_.ModularForm _root_.P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm in
open _root_.ModularForm _root_.P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.ModularForm ModularForm.HeckeGamma1 in
theorem solution
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (ModularForm.heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ))
        ∣[k] ModularForm.heckeDiagMatrix p) ∣[k] γ
      = ModularForm.heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ))
        ∣[k] ModularForm.heckeDiagMatrix p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  rw [sum_eq k f σ]
  exact sum_slash_mapGL k hpN f hf σ hσ hσp g hg

end S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
end P2MW
export P2MW.S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 (solution)

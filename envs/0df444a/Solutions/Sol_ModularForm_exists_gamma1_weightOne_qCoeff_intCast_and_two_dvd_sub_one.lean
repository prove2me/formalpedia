-- Prove2me | solution 1 for ModularForm.exists_gamma1_weightOne_qCoeff_intCast_and_two_dvd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/2d08e96b-7fc6-5f38-8d78-cca4730d68ec

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
import Theorems.Thm_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma1_weightOne_qCoeff_intCast_and_two_dvd_sub_one

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace LiftA2

open UpperHalfPlane

noncomputable def eps (z : ℂ) : ℤ := if z = 1 then 1 else if z = -1 then -1 else 0

theorem eps_one : eps 1 = 1 := by simp [eps]

theorem eps_neg_one : eps (-1) = -1 := by
  have : (-1 : ℂ) ≠ 1 := by norm_num
  simp [eps, this]

theorem eps_of_ne {z : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) : eps z = 0 := by simp [eps, h1, h2]

theorem sum_pow_two_mul_add_one (z : ℂ) (n : ℕ) (hz : z ^ (2 * n) = 1) :
    ∑ j ∈ Finset.range n, z ^ (2 * j + 1) = (n : ℂ) * (eps z : ℂ) := by
  have hrw : ∑ j ∈ Finset.range n, z ^ (2 * j + 1) = z * ∑ j ∈ Finset.range n, (z ^ 2) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, pow_succ, mul_comm]
  rw [hrw]
  by_cases h1 : z = 1
  · subst h1; simp [eps_one]
  by_cases h2 : z = -1
  · subst h2
    rw [eps_neg_one]
    simp only [even_two, Even.neg_pow, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast; ring
  · have hz2 : z ^ 2 ≠ 1 := fun h => by
      rcases sq_eq_one_iff.mp h with h | h
      · exact h1 h
      · exact h2 h
    rw [geom_sum_eq hz2, ← pow_mul, hz, sub_self, zero_div, mul_zero, eps_of_ne h1 h2]
    simp

theorem sum_pow_two_mul_add_one' (z : ℂ) (n : ℕ) (hz : z ^ (2 * n) = 1 ∨ z = 0) :
    ∑ j ∈ Finset.range n, z ^ (2 * j + 1) = (n : ℂ) * (eps z : ℂ) := by
  rcases hz with hz | rfl
  · exact sum_pow_two_mul_add_one z n hz
  · rw [eps_of_ne (by norm_num) (by norm_num)]
    simp

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods (N : ℕ) : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 N)]
  exact AddSubgroup.mem_zmultiples 1

section
variable {N : ℕ} {k : ℤ}

theorem analytic (f : ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    AnalyticAt ℂ (cuspFunction 1 (⇑f : UpperHalfPlane → ℂ)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods N)

theorem qCoeff_add' (f g : ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (m : ℕ) :
    ModularFormClass.qCoeff ((⇑f : UpperHalfPlane → ℂ) + ⇑g) m =
      ModularFormClass.qCoeff (⇑f) m + ModularFormClass.qCoeff (⇑g) m := by
  unfold ModularFormClass.qCoeff
  rw [qExpansion_add (analytic f) (analytic g), map_add]

theorem qCoeff_smul' (c : ℂ) (f : ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (m : ℕ) :
    ModularFormClass.qCoeff (c • (⇑f : UpperHalfPlane → ℂ)) m = c * ModularFormClass.qCoeff (⇑f) m := by
  unfold ModularFormClass.qCoeff
  rw [qExpansion_smul (analytic f) c, map_smul, smul_eq_mul]

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑(∑ i ∈ s, f i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, (⇑(f i) : UpperHalfPlane → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ModularForm.coe_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ih]

theorem qCoeff_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ModularForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k) (m : ℕ) :
    ModularFormClass.qCoeff (⇑(∑ i ∈ s, f i) : UpperHalfPlane → ℂ) m = ∑ i ∈ s, ModularFormClass.qCoeff (⇑(f i)) m := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold ModularFormClass.qCoeff
    rw [ModularForm.coe_zero, qExpansion_zero, map_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, qCoeff_add', ih]

end

end LiftA2

open LiftA2 in

theorem solution
    (M : ℕ) [NeZero M] (hM : 3 ≤ M) (hM2 : ¬ 2 ∣ M) :
    ∃ (A : ModularForm (CongruenceSubgroup.Gamma1 M) 1) (b : ℕ → ℤ),
      (∀ n, ModularFormClass.qCoeff A n = (b n : ℂ)) ∧ (2 : ℤ) ∣ b 0 - 1 ∧ ∀ n, 0 < n → (2 : ℤ) ∣ b n := by
  classical

  obtain ⟨ℓ, hℓp, hℓM⟩ := Nat.exists_prime_and_dvd (show M ≠ 1 by omega)
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  have hℓ2 : ℓ ≠ 2 := fun h => hM2 (h ▸ hℓM)
  have hℓ0 : (ℓ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓp.ne_zero

  obtain ⟨n, χ, hn, hprim, hroot, hodd⟩ :=
    DirichletCharacter.exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum ℓ hℓ2
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'

  have hE : ∀ j : ℕ, ∃ E : ModularForm (Gamma1 ℓ : Subgroup (GL (Fin 2) ℝ)) 1,
      ModularFormClass.qCoeff E 0 =
        -(∑ a ∈ Finset.range ℓ, (a : ℂ) * (χ ^ (2 * j + 1)) (a : ZMod ℓ)) / (2 * ℓ) ∧
      ∀ m : ℕ, 0 < m → ModularFormClass.qCoeff E m = ∑ d ∈ m.divisors, (χ ^ (2 * j + 1)) (d : ZMod ℓ) := by
    intro j
    obtain ⟨E, -, h0, hm⟩ := ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd ℓ (χ ^ (2 * j + 1))
      (hprim j).1 (hprim j).2
    exact ⟨E, h0, hm⟩
  choose E hE0 hEm using hE

  have hle : (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) ≤ (Gamma1 ℓ : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (ModularCurve.Gamma1_le_of_dvd hℓM)

  let c : ℂ := (2 * ℓ : ℂ) / n
  let A : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 1 :=
    c • ∑ j ∈ Finset.range n, ModularCurve.restrictForm hle (E j)
  let b : ℕ → ℤ := fun m =>
    if m = 0 then -(∑ a ∈ Finset.range ℓ, (a : ℤ) * eps (χ (a : ZMod ℓ)))
    else 2 * ℓ * ∑ d ∈ m.divisors, eps (χ (d : ZMod ℓ))
  have hpow : ∀ (j : ℕ) (x : ZMod ℓ), (χ ^ (2 * j + 1)) x = χ x ^ (2 * j + 1) :=
    fun j x => MulChar.pow_apply' χ (by omega) x

  have hsum : ∀ x : ZMod ℓ, ∑ i ∈ Finset.range n, χ x ^ (2 * i + 1) = (n : ℂ) * (eps (χ x) : ℂ) :=
    fun x => sum_pow_two_mul_add_one' (χ x) n (hroot x)
  have hcn : c * (n : ℂ) = 2 * ℓ := by
    simp only [c]; field_simp

  have hA : (⇑A : UpperHalfPlane → ℂ) = c • (⇑(∑ j ∈ Finset.range n, E j) : UpperHalfPlane → ℂ) := by
    show (⇑(c • ∑ j ∈ Finset.range n, ModularCurve.restrictForm hle (E j)) : UpperHalfPlane → ℂ) = _
    rw [show ∀ f : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 1, (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f
      from fun _ => rfl, coe_sum, coe_sum]
    rfl
  refine ⟨A, b, ?_, ?_, ?_⟩
  · intro m
    rw [hA, qCoeff_smul', qCoeff_coe_sum]
    by_cases hm : m = 0
    · subst hm
      simp only [hE0, b, if_pos rfl, hpow]

      have h1 : ∑ i ∈ Finset.range n, -(∑ a ∈ Finset.range ℓ, (a : ℂ) * χ (a : ZMod ℓ) ^ (2 * i + 1)) / (2 * ℓ)
          = -((n : ℂ) * ∑ a ∈ Finset.range ℓ, (a : ℂ) * (eps (χ (a : ZMod ℓ)) : ℂ)) / (2 * ℓ) := by
        rw [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_comm, Finset.mul_sum]
        congr 2
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, hsum]
        ring
      rw [h1]
      push_cast
      rw [show c * (-((n : ℂ) * ∑ a ∈ Finset.range ℓ, (a : ℂ) * (eps (χ (a : ZMod ℓ)) : ℂ)) / (2 * ℓ))
        = -((c * n) / (2 * ℓ) * ∑ a ∈ Finset.range ℓ, (a : ℂ) * (eps (χ (a : ZMod ℓ)) : ℂ)) by ring]
      rw [hcn, div_self (mul_ne_zero two_ne_zero hℓ0), one_mul]
    · simp only [hEm _ m (Nat.pos_of_ne_zero hm), b, if_neg hm, hpow]
      rw [Finset.sum_comm]
      simp only [hsum]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [← mul_assoc, hcn]
  ·
    simp only [b, if_pos rfl]
    obtain ⟨r, hr⟩ := hodd
    have hr' : (∑ a ∈ Finset.range ℓ, (a : ℤ) * eps (χ (a : ZMod ℓ))) = 2 * r + 1 := by
      rw [← hr]
      rfl
    rw [hr']
    exact ⟨-(r + 1), by ring⟩
  · intro m hm
    simp only [b, if_neg hm.ne']
    exact ⟨ℓ * ∑ d ∈ m.divisors, eps (χ (d : ZMod ℓ)), by ring⟩

#print axioms solution

end S_ModularForm_exists_gamma1_weightOne_qCoeff_intCast_and_two_dvd_sub_one
end P2MW
export P2MW.S_ModularForm_exists_gamma1_weightOne_qCoeff_intCast_and_two_dvd_sub_one (solution)

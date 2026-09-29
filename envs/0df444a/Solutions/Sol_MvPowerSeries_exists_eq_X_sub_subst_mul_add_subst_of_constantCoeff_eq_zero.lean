-- Prove2me | solution 1 for MvPowerSeries.exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/cc0149dd-4d07-5a22-9c82-9c423efabf08

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero

set_option autoImplicit false

open MvPowerSeries

namespace P2mTaylorDiv

variable {k : Type*} [CommRing k]

theorem hasSubst_X_zero_zero : HasSubst ![(X 0 : MvPowerSeries (Fin 2) k), 0] :=
  hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)

theorem prod_X_zero_zero (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => ((![(X 0 : MvPowerSeries (Fin 2) k), 0]) s) ^ n) =
      if d 1 = 0 then monomial d (1 : k) else 0 := by
  have h : (d.prod fun s n => ((![(X 0 : MvPowerSeries (Fin 2) k), 0]) s) ^ n) =
      (X 0 : MvPowerSeries (Fin 2) k) ^ (d 0) * (0 : MvPowerSeries (Fin 2) k) ^ (d 1) := by
    simp only [Finsupp.prod_pow, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h]
  split_ifs with h1
  · have hd : Finsupp.single (0 : Fin 2) (d 0) = d := by
      apply Finsupp.ext
      intro i
      fin_cases i
      · simp
      · simp [h1]
    rw [h1, pow_zero, mul_one, X_pow_eq, hd]
  · rw [zero_pow h1, mul_zero]

theorem coeff_subst_X_zero_zero (F : MvPowerSeries (Fin 2) k) (e : Fin 2 →₀ ℕ) :
    coeff e (subst ![(X 0 : MvPowerSeries (Fin 2) k), 0] F) = if e 1 = 0 then coeff e F else 0 := by
  classical
  rw [coeff_subst hasSubst_X_zero_zero F e, finsum_eq_single _ e]
  · rw [prod_X_zero_zero]
    split_ifs with h1
    · rw [coeff_monomial_same, smul_eq_mul, mul_one]
    · rw [map_zero, smul_zero]
  · intro d hd
    rw [prod_X_zero_zero]
    split_ifs with h1
    · rw [coeff_monomial_ne (Ne.symm hd), smul_zero]
    · rw [map_zero, smul_zero]

theorem X_one_dvd_sub_subst (F : MvPowerSeries (Fin 2) k) :
    (X 1 : MvPowerSeries (Fin 2) k) ∣ F - subst ![(X 0 : MvPowerSeries (Fin 2) k), 0] F := by
  rw [X_dvd_iff]
  intro m hm
  rw [map_sub, coeff_subst_X_zero_zero, if_pos hm, sub_self]

theorem subst_subst_X_zero (φ : PowerSeries k) (a : Fin 2 → MvPowerSeries (Fin 2) k) (ha : HasSubst a)
    (h0 : a 0 = X 0) :
    subst a (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ) =
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ := by
  have hc : HasSubst (fun _ : Unit => (X 0 : MvPowerSeries (Fin 2) k)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  rw [PowerSeries.subst_def, subst_comp_subst_apply hc ha]
  congr 1
  funext u
  rw [subst_X ha, h0]

theorem vec2_ext {α : Type*} (a b : Fin 2 → α) (h0 : a 0 = b 0) (h1 : a 1 = b 1) : a = b := by
  funext s
  fin_cases s
  · exact h0
  · exact h1

end P2mTaylorDiv

open P2mTaylorDiv in

theorem solution
    (k : Type*) [CommRing k] (φ : PowerSeries k) (hφ0 : PowerSeries.constantCoeff φ = 0)
    (G : MvPowerSeries (Fin 2) k) :
    ∃ Q : MvPowerSeries (Fin 2) k,
      G = (X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ) * Q +
        MvPowerSeries.subst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ] G := by

  have hP0 : MvPowerSeries.constantCoeff (PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero (by simp) φ hφ0
  have hσ : HasSubst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ + X 1] :=
    hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hP0])
  have hτ : HasSubst ![(X 0 : MvPowerSeries (Fin 2) k), X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ] :=
    hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp [hP0])

  have hτσ : ∀ F : MvPowerSeries (Fin 2) k,
      subst ![(X 0 : MvPowerSeries (Fin 2) k), X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ]
        (subst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ + X 1] F) = F := by
    intro F
    rw [subst_comp_subst_apply hσ hτ]
    have hid : (fun s => subst ![(X 0 : MvPowerSeries (Fin 2) k), X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ]
        ((![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ + X 1]) s)) =
        (X : Fin 2 → MvPowerSeries (Fin 2) k) := by
      apply vec2_ext
      · simp only [Matrix.cons_val_zero]
        rw [subst_X hτ, Matrix.cons_val_zero]
      · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [subst_add hτ, subst_subst_X_zero φ _ hτ rfl, subst_X hτ]
        simp
    rw [hid, subst_self]
    rfl

  have hρσ : ∀ F : MvPowerSeries (Fin 2) k,
      subst ![(X 0 : MvPowerSeries (Fin 2) k), 0]
        (subst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ + X 1] F) =
      subst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ] F := by
    intro F
    rw [subst_comp_subst_apply hσ hasSubst_X_zero_zero]
    congr 1
    apply vec2_ext
    · simp only [Matrix.cons_val_zero]
      rw [subst_X hasSubst_X_zero_zero, Matrix.cons_val_zero]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [subst_add hasSubst_X_zero_zero, subst_subst_X_zero φ _ hasSubst_X_zero_zero rfl,
        subst_X hasSubst_X_zero_zero]
      simp

  have hτρ : ∀ F : MvPowerSeries (Fin 2) k,
      subst ![(X 0 : MvPowerSeries (Fin 2) k), X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ]
        (subst ![(X 0 : MvPowerSeries (Fin 2) k), 0] F) = subst ![(X 0 : MvPowerSeries (Fin 2) k), 0] F := by
    intro F
    rw [subst_comp_subst_apply hasSubst_X_zero_zero hτ]
    congr 1
    apply vec2_ext
    · simp only [Matrix.cons_val_zero]
      rw [subst_X hτ, Matrix.cons_val_zero]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← coe_substAlgHom hτ]
      exact map_zero _

  obtain ⟨H₁, hH₁⟩ := X_one_dvd_sub_subst
    (subst ![(X 0 : MvPowerSeries (Fin 2) k), PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ + X 1] G)
  refine ⟨subst ![(X 0 : MvPowerSeries (Fin 2) k), X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ] H₁, ?_⟩
  have key := congrArg
    (subst ![(X 0 : MvPowerSeries (Fin 2) k), X 1 - PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) k) φ])
    (eq_add_of_sub_eq' hH₁)
  rw [hτσ, subst_add hτ, subst_mul hτ, subst_X hτ, hτρ, hρσ] at key
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at key
  exact key.trans (add_comm _ _)

end S_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero
end P2MW
export P2MW.S_MvPowerSeries_exists_eq_X_sub_subst_mul_add_subst_of_constantCoeff_eq_zero (solution)

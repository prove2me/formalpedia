-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_powMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a919ccad-5b44-54f5-95ee-32c4bcf10a9e

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_powMap_injective

set_option autoImplicit false

open MvPowerSeries

namespace GaussPencil
namespace L9

variable {W : Type*} [CommRing W]

noncomputable def ij (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[scoped simp] theorem ij_zero (a b : ℕ) : ij a b 0 = a := by simp [ij]
@[scoped simp] theorem ij_one (a b : ℕ) : ij a b 1 = b := by simp [ij]

theorem eq_ij (d : Fin 2 →₀ ℕ) : d = ij (d 0) (d 1) := by
  ext i; fin_cases i <;> simp

theorem ij_injective {a b a' b' : ℕ} (h : ij a b = ij a' b') : a = a' ∧ b = b' := by
  have h0 := congrArg (fun d => d 0) h
  have h1 := congrArg (fun d => d 1) h
  simp only [ij_zero, ij_one] at h0 h1
  exact ⟨h0, h1⟩

theorem smul_ij (e a b : ℕ) : e • ij a b = ij (e * a) (e * b) := by
  ext i; fin_cases i <;> simp [ij]

theorem ij_le_ij_iff {a b a' b' : ℕ} : ij a b ≤ ij a' b' ↔ a ≤ a' ∧ b ≤ b' := by
  constructor
  · intro h; exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨ha, hb⟩ i; fin_cases i <;> simpa

theorem ij_sub_ij (a b a' b' : ℕ) : ij a b - ij a' b' = ij (a - a') (b - b') := by
  ext i; fin_cases i <;> simp [ij]

theorem ij_add_ij (a b a' b' : ℕ) : ij a b + ij a' b' = ij (a + a') (b + b') := by
  ext i; fin_cases i <;> simp [ij, add_comm, add_left_comm]

noncomputable def crossing (c : W) : MvPowerSeries (Fin 2) W := X 0 * X 1 - C c

theorem X_mul_X_eq : (X 0 * X 1 : MvPowerSeries (Fin 2) W) = monomial (ij 1 1) 1 := by
  rw [X_def, X_def, monomial_mul_monomial, one_mul]; rfl

theorem coeff_crossing_mul (c : W) (G : MvPowerSeries (Fin 2) W) (a b : ℕ) :
    coeff (ij a b) (crossing c * G)
      = (if 1 ≤ a ∧ 1 ≤ b then coeff (ij (a - 1) (b - 1)) G else 0) - c * coeff (ij a b) G := by
  rw [crossing, sub_mul, map_sub, X_mul_X_eq, coeff_monomial_mul, coeff_C_mul, one_mul]
  by_cases hab : 1 ≤ a ∧ 1 ≤ b
  · rw [if_pos (ij_le_ij_iff.mpr hab), if_pos hab, ij_sub_ij]
  · rw [if_neg (fun h => hab (ij_le_ij_iff.mp h)), if_neg hab]

variable (π : W) (e : ℕ) (he : e ≠ 0)

theorem eq_crossing_pow_mul_of_expand_eq {F G : MvPowerSeries (Fin 2) W}
    (h : expand e he F = crossing π * G) :
    ∃ A : MvPowerSeries (Fin 2) W, F = crossing (π ^ e) * A := by
  have he1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he

  set g : ℕ → ℕ → W := fun a b => coeff (ij a b) G with hg

  have hrel : ∀ a b : ℕ, coeff (ij a b) (expand e he F)
      = (if 1 ≤ a ∧ 1 ≤ b then g (a - 1) (b - 1) else 0) - π * g a b := by
    intro a b; rw [h, coeff_crossing_mul]

  have hoff : ∀ a b : ℕ, ¬ e ∣ a → coeff (ij a b) (expand e he F) = 0 := by
    intro a b ha
    exact coeff_expand_of_not_dvd e he F (i := 0) (by simpa using ha)

  have hstep : ∀ a b j : ℕ, e ∣ a → 1 ≤ j → j < e → g (a + j - 1) (b + j - 1) = π * g (a + j) (b + j) := by
    intro a b j ha hj hje
    have hndvd : ¬ e ∣ a + j := by
      intro hd
      have : e ∣ j := (Nat.dvd_add_right ha).mp hd
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    have h0 := hrel (a + j) (b + j)
    rw [hoff _ _ hndvd, if_pos ⟨by omega, by omega⟩] at h0
    have h1 : g (a + j - 1) (b + j - 1) - π * g (a + j) (b + j) = 0 := h0.symm
    exact sub_eq_zero.mp h1
  have hchain : ∀ a b : ℕ, e ∣ a → ∀ j : ℕ, j < e → g a b = π ^ j * g (a + j) (b + j) := by
    intro a b ha j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hs := hstep a b (j + 1) ha (by omega) hj
      rw [show a + (j + 1) - 1 = a + j by omega, show b + (j + 1) - 1 = b + j by omega] at hs
      rw [ih (by omega), hs, pow_succ, mul_assoc]

  let A : MvPowerSeries (Fin 2) W := fun d => g (e * d 0 + (e - 1)) (e * d 1 + (e - 1))
  have hA : ∀ a b : ℕ, coeff (ij a b) A = g (e * a + (e - 1)) (e * b + (e - 1)) := by
    intro a b; rw [coeff_apply]; simp [A]
  refine ⟨A, MvPowerSeries.ext fun d => ?_⟩
  rw [eq_ij d]
  set a := d 0
  set b := d 1
  rw [coeff_crossing_mul, ← coeff_expand_smul e he F, smul_ij, hrel]
  simp only [hA]
  congr 1
  · by_cases hab : 1 ≤ a ∧ 1 ≤ b
    · rw [if_pos hab, if_pos ⟨le_trans hab.1 (Nat.le_mul_of_pos_left a (by omega)), le_trans hab.2 (Nat.le_mul_of_pos_left b (by omega))⟩]
      have hea : e ≤ e * a := Nat.le_mul_of_pos_right e hab.1
      have heb : e ≤ e * b := Nat.le_mul_of_pos_right e hab.2
      congr 1
      · rw [Nat.mul_sub, mul_one]; omega
      · rw [Nat.mul_sub, mul_one]; omega
    · rw [if_neg hab, if_neg]
      rintro ⟨h1, h2⟩
      apply hab
      constructor
      · by_contra h; push_neg at h; have : a = 0 := by omega
        rw [this, mul_zero] at h1; omega
      · by_contra h; push_neg at h; have : b = 0 := by omega
        rw [this, mul_zero] at h2; omega
  · rw [hchain (e * a) (e * b) (dvd_mul_right e a) (e - 1) (by omega), ← mul_assoc, ← pow_succ',
      Nat.sub_add_cancel he1]

end GaussPencil.L9
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_powMap_injective.GaussPencil P2MW.S_ModularCurve_UVCrossingModel_exists_powMap_injective.GaussPencil.L9"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_powMap_injective.GaussPencil"

open ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {W : Type*} [CommRing W] (π : W) (e : ℕ) (he : e ≠ 0) :
    ∃ θ : UVCrossingModel W (π ^ e) →ₐ[W] UVCrossingModel W π,
      (∀ F : MvPowerSeries (Fin 2) W, θ (mk (π ^ e) F) = mk π (MvPowerSeries.expand e he F)) ∧
      Function.Injective θ := by
  classical

  let f : MvPowerSeries (Fin 2) W →ₐ[W] UVCrossingModel W π :=
    (Ideal.Quotient.mkₐ W (uvCrossingIdeal W π)).comp (MvPowerSeries.expand e he)
  have hf : ∀ F : MvPowerSeries (Fin 2) W, f F = mk π (MvPowerSeries.expand e he F) := fun F => rfl
  have hgen : f (GaussPencil.L9.crossing (π ^ e)) = 0 := by
    rw [hf]
    show Ideal.Quotient.mk (uvCrossingIdeal W π) _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    have : MvPowerSeries.expand e he (GaussPencil.L9.crossing (π ^ e))
        = (X 0 * X 1 : MvPowerSeries (Fin 2) W) ^ e - (MvPowerSeries.C π) ^ e := by
      rw [GaussPencil.L9.crossing, map_sub, map_mul, MvPowerSeries.expand_X, MvPowerSeries.expand_X,
        MvPowerSeries.expand_C, map_pow, mul_pow]
    rw [this]
    exact sub_dvd_pow_sub_pow _ _ e
  have hI : ∀ a : MvPowerSeries (Fin 2) W, a ∈ uvCrossingIdeal W (π ^ e) → f a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, show (X 0 * X 1 - MvPowerSeries.C (π ^ e) : MvPowerSeries (Fin 2) W)
      = GaussPencil.L9.crossing (π ^ e) from rfl, hgen, mul_zero]
  refine ⟨Ideal.Quotient.liftₐ (uvCrossingIdeal W (π ^ e)) f hI, fun F => rfl, ?_⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨F, rfl⟩ := mk_surjective (π ^ e) z
  have h1 : mk π (MvPowerSeries.expand e he F) = 0 := hz
  have h2 : MvPowerSeries.expand e he F ∈ uvCrossingIdeal W π := by
    have : Ideal.Quotient.mk (uvCrossingIdeal W π) (MvPowerSeries.expand e he F) = 0 := h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  obtain ⟨G, hG⟩ := Ideal.mem_span_singleton'.mp h2
  obtain ⟨A, hA⟩ := GaussPencil.L9.eq_crossing_pow_mul_of_expand_eq π e he
    (F := F) (G := G) (by rw [← hG, mul_comm]; rfl)
  show Ideal.Quotient.mk (uvCrossingIdeal W (π ^ e)) F = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, hA]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end S_ModularCurve_UVCrossingModel_exists_powMap_injective
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_powMap_injective (solution)

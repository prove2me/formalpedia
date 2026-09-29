-- Prove2me | solution 1 for MvPowerSeries.exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/35b43a00-8095-5e64-ace3-fbe65415b481

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul

set_option autoImplicit false

open IsLocalRing

noncomputable section

namespace P2mWs2IF

open MvPowerSeries

variable {W : Type} [CommRing W]

theorem coeff_X_mul' (s : Fin 2) (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    coeff m (X s * f) = if 1 ≤ m s then coeff (m - Finsupp.single s 1) f else 0 := by
  rw [X_def, coeff_monomial_mul]
  simp only [Finsupp.single_le_iff, one_mul]

def form (d : ℕ) (g : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) : W :=
  ∑ i ∈ Finset.range (d + 1), coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) g * p₀ ^ i * p₁ ^ (d - i)

theorem form_add (d : ℕ) (g g' : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    form d (g + g') p₀ p₁ = form d g p₀ p₁ + form d g' p₀ p₁ := by
  simp only [form, map_add, add_mul, Finset.sum_add_distrib]

theorem form_zero (g : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) : form 0 g p₀ p₁ = coeff 0 g := by
  simp [form]

private theorem _root_.P2mWs2IF.single_le_iff (s : Fin 2) (m : Fin 2 →₀ ℕ) : Finsupp.single s 1 ≤ m ↔ 1 ≤ m s := by
  rw [Finsupp.single_le_iff]

p2m_export "P2mWs2IF" "single_le_iff"

theorem form_X0_mul (d : ℕ) (b : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    form (d + 1) (X 0 * b) p₀ p₁ = p₀ * form d b p₀ p₁ := by
  simp only [form]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have h0 : coeff (Finsupp.single (0 : Fin 2) 0 + Finsupp.single (1 : Fin 2) (d + 1 - 0)) (X 0 * b) = 0 := by
    rw [coeff_X_mul', if_neg (by simp)]
  rw [h0, zero_mul, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [coeff_X_mul', if_pos (by simp)]
  have : Finsupp.single (0 : Fin 2) (i + 1) + Finsupp.single (1 : Fin 2) (d + 1 - (i + 1)) - Finsupp.single 0 1 =
      Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i) := by
    ext s; fin_cases s <;> simp
  rw [this, show d + 1 - (i + 1) = d - i from by omega]; ring

theorem form_X1_mul (d : ℕ) (b : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    form (d + 1) (X 1 * b) p₀ p₁ = p₁ * form d b p₀ p₁ := by
  simp only [form]
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hlast : coeff (Finsupp.single (0 : Fin 2) (d + 1) + Finsupp.single (1 : Fin 2) (d + 1 - (d + 1))) (X 1 * b) = 0 := by
    rw [coeff_X_mul', if_neg (by simp)]
  rw [hlast, zero_mul, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_X_mul', if_pos (by simp; omega)]
  have : Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d + 1 - i) - Finsupp.single 1 1 =
      Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i) := by
    ext s; fin_cases s <;> simp; omega
  rw [this, show d + 1 - i = (d - i) + 1 by omega, pow_succ]; ring

theorem mem_span_X_of_coeff_zero (f : MvPowerSeries (Fin 2) W) (hf : coeff 0 f = 0) :
    f ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1} := by
  classical

  let f₀ : MvPowerSeries (Fin 2) W := fun n => coeff (n + Finsupp.single 0 1) f
  let f₁ : MvPowerSeries (Fin 2) W := fun n => if n 0 = 0 then coeff (n + Finsupp.single 1 1) f else 0
  have hdec : f = X 0 * f₀ + X 1 * f₁ := by
    ext m
    rw [map_add, coeff_X_mul', coeff_X_mul']
    by_cases h0 : 1 ≤ m 0
    · rw [if_pos h0]
      have : coeff (m - Finsupp.single 0 1) f₀ = coeff m f := by
        show coeff (m - Finsupp.single 0 1 + Finsupp.single 0 1) f = coeff m f
        rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h0)]
      rw [this]
      by_cases h1 : 1 ≤ m 1
      · rw [if_pos h1]
        have : coeff (m - Finsupp.single 1 1) f₁ = 0 := by
          show (if ((m - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0) = 0 then coeff (m - Finsupp.single 1 1 + Finsupp.single 1 1) f else 0) = 0
          rw [if_neg]; simp; omega
        rw [this, add_zero]
      · rw [if_neg h1, add_zero]
    · rw [if_neg h0, zero_add]
      push Not at h0
      have hm0 : m 0 = 0 := by omega
      by_cases h1 : 1 ≤ m 1
      · rw [if_pos h1]
        show coeff m f = if ((m - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0) = 0 then coeff (m - Finsupp.single 1 1 + Finsupp.single 1 1) f else 0
        rw [if_pos (by simp [hm0]), tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h1)]
      · rw [if_neg h1]
        have : m = 0 := by ext s; fin_cases s <;> simp <;> omega
        rw [this]; exact hf
  rw [hdec]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

end P2mWs2IF

end

open P2mWs2IF in
theorem solution
    (W : Type) [CommRing W] (M : Type) [CommRing M] [IsLocalRing M]
    (Φ : MvPowerSeries (Fin 2) W →+* M) (ρ : W →+* M)
    (hC : ∀ w : W, Φ (MvPowerSeries.C w) = ρ w)
    (v α β : M) (p₀ p₁ : W)
    (hX0 : Φ (MvPowerSeries.X 0) = v * α) (hX1 : Φ (MvPowerSeries.X 1) = v * β)
    (hv : v ∈ maximalIdeal M)
    (hα : α - ρ p₀ ∈ maximalIdeal M) (hβ : β - ρ p₁ ∈ maximalIdeal M)
    (d : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d) :
    ∃ r ∈ maximalIdeal M,
      Φ g = v ^ d * (ρ (∑ i ∈ Finset.range (d + 1),
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i)) g * p₀ ^ i * p₁ ^ (d - i)) + r) := by
  classical

  have hbase : ∀ f : MvPowerSeries (Fin 2) W, ∃ r ∈ maximalIdeal M, Φ f = ρ (MvPowerSeries.coeff 0 f) + r := by
    intro f
    have hmem := mem_span_X_of_coeff_zero (f - MvPowerSeries.C (MvPowerSeries.coeff 0 f)) (by simp)
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    refine ⟨Φ (f - MvPowerSeries.C (MvPowerSeries.coeff 0 f)), ?_, ?_⟩
    · rw [← hab, map_add, map_mul, map_mul, hX0, hX1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hv)) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hv))
    · rw [map_sub, hC]; ring

  suffices key : ∀ (d : ℕ) (g : MvPowerSeries (Fin 2) W),
      g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ d →
      ∃ r ∈ maximalIdeal M, Φ g = v ^ d * (ρ (form d g p₀ p₁) + r) by
    exact key d g hg
  intro d
  induction d with
  | zero =>
    intro g _
    obtain ⟨r, hr, h⟩ := hbase g
    exact ⟨r, hr, by rw [pow_zero, one_mul, form_zero, h]⟩
  | succ d ih =>
    intro g hg
    rw [pow_succ'] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      obtain ⟨c₀, c₁, rfl⟩ := Ideal.mem_span_pair.mp ha
      obtain ⟨r₀, hr₀, h₀⟩ := ih (c₀ * b) (Ideal.mul_mem_left _ _ hb)
      obtain ⟨r₁, hr₁, h₁⟩ := ih (c₁ * b) (Ideal.mul_mem_left _ _ hb)
      refine ⟨(α - ρ p₀) * (ρ (form d (c₀ * b) p₀ p₁) + r₀) + ρ p₀ * r₀ +
        ((β - ρ p₁) * (ρ (form d (c₁ * b) p₀ p₁) + r₁) + ρ p₁ * r₁), ?_, ?_⟩
      · refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hα) (Ideal.mul_mem_left _ _ hr₀))
          (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hβ) (Ideal.mul_mem_left _ _ hr₁))
      · have e : (c₀ * MvPowerSeries.X 0 + c₁ * MvPowerSeries.X 1) * b =
            MvPowerSeries.X 0 * (c₀ * b) + MvPowerSeries.X 1 * (c₁ * b) := by ring
        rw [e, map_add, map_mul Φ (MvPowerSeries.X 0) (c₀ * b), map_mul Φ (MvPowerSeries.X 1) (c₁ * b), hX0, hX1, h₀, h₁,
          form_add, form_X0_mul, form_X1_mul, map_add, map_mul, map_mul, pow_succ]
        ring
    · intro x y hx hy
      obtain ⟨r, hr, h⟩ := hx
      obtain ⟨r', hr', h'⟩ := hy
      exact ⟨r + r', Ideal.add_mem _ hr hr', by rw [map_add, h, h', form_add, map_add]; ring⟩

end S_MvPowerSeries_exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul
end P2MW
export P2MW.S_MvPowerSeries_exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul (solution)

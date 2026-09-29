-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/dff800a8-e1a3-56c4-bb56-5f785deee12e

import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq
set_option autoImplicit false
open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace ALGProof

open MvPowerSeries

variable {W : Type*} [CommRing W]

private noncomputable abbrev e (i : Fin 2) : Fin 2 →₀ ℕ := Finsupp.single i 1

private theorem X_eq_monomial (i : Fin 2) : (X i : MvPowerSeries (Fin 2) W) = monomial (e i) 1 := rfl

private theorem mem_span_C_X_iff (π : W) (i : Fin 2) (f : MvPowerSeries (Fin 2) W) :
    f ∈ Ideal.span ({C π, X i} : Set (MvPowerSeries (Fin 2) W)) ↔ ∀ m : Fin 2 →₀ ℕ, m i = 0 → π ∣ coeff m f := by
  classical
  constructor
  · intro hf m hm
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hf
    have hb : coeff m (b * X i) = 0 := (X_dvd_iff.mp (dvd_mul_left (X i) b)) m hm
    refine ⟨coeff m a, ?_⟩
    rw [map_add, hb, add_zero, coeff_mul_C, mul_comm]
  · intro h

    let g : MvPowerSeries (Fin 2) W := fun m => if hm : m i = 0 then Classical.choose (h m hm) else 0
    have hg : ∀ m : Fin 2 →₀ ℕ, m i = 0 → coeff m f = π * coeff m g := by
      intro m hm
      have : coeff m g = Classical.choose (h m hm) := by
        show g m = _
        simp only [g, dif_pos hm]
      rw [this]
      exact Classical.choose_spec (h m hm)
    have hdvd : (X i : MvPowerSeries (Fin 2) W) ∣ f - C π * g := by
      rw [X_dvd_iff]
      intro m hm
      rw [map_sub, coeff_C_mul, hg m hm, sub_self]
    obtain ⟨r, hr⟩ := hdvd
    refine Ideal.mem_span_pair.mpr ⟨g, r, ?_⟩
    have : f = C π * g + X i * r := by rw [← hr]; ring
    rw [this]; ring

private theorem crossing_mem_span_C_X (π : W) (E : ℕ) (hE : 1 ≤ E) (i : Fin 2) :
    (X 0 : MvPowerSeries (Fin 2) W) * X 1 - C (π ^ E) ∈ Ideal.span ({C π, X i} : Set (MvPowerSeries (Fin 2) W)) := by
  refine sub_mem ?_ ?_
  · fin_cases i
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · obtain ⟨E', rfl⟩ := Nat.exists_eq_add_of_le hE
    rw [pow_add, pow_one, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

private theorem uvCrossingIdeal_le_span_C_X (π : W) (E : ℕ) (hE : 1 ≤ E) (i : Fin 2) :
    uvCrossingIdeal W (π ^ E) ≤ Ideal.span ({C π, X i} : Set (MvPowerSeries (Fin 2) W)) := by
  rw [uvCrossingIdeal, Ideal.span_singleton_le_iff_mem]
  exact crossing_mem_span_C_X π E hE i

private theorem branchIdeal_eq_map (π : W) (E : ℕ) (i : Fin 2) :
    Ideal.span ({const (π ^ E) π, mk (π ^ E) (X i)} : Set (UVCrossingModel W (π ^ E)))
      = (Ideal.span ({C π, X i} : Set (MvPowerSeries (Fin 2) W))).map (mk (π ^ E)) := by
  rw [Ideal.map_span, Set.image_pair]
  rfl

private theorem mk_mem_branchIdeal_iff (π : W) (E : ℕ) (hE : 1 ≤ E) (i : Fin 2) (f : MvPowerSeries (Fin 2) W) :
    mk (π ^ E) f ∈ Ideal.span ({const (π ^ E) π, mk (π ^ E) (X i)} : Set (UVCrossingModel W (π ^ E)))
      ↔ f ∈ Ideal.span ({C π, X i} : Set (MvPowerSeries (Fin 2) W)) := by
  rw [branchIdeal_eq_map]
  exact Ideal.mem_quotient_iff_mem (uvCrossingIdeal_le_span_C_X π E hE i)

private theorem coeff_monomial_one_mul (n m : Fin 2 →₀ ℕ) (φ : MvPowerSeries (Fin 2) W) :
    coeff m (monomial n (1 : W) * φ) = if n ≤ m then coeff (m - n) φ else 0 := by
  classical
  rw [coeff_monomial_mul]
  split_ifs <;> simp

private theorem exists_eq_C_mul_add_X_mul_X_mul (π : W) (f : MvPowerSeries (Fin 2) W)
    (h : ∀ m : Fin 2 →₀ ℕ, (m 0 = 0 ∨ m 1 = 0) → π ∣ coeff m f) :
    ∃ g r : MvPowerSeries (Fin 2) W, f = C π * g + X 0 * X 1 * r := by
  classical
  let g : MvPowerSeries (Fin 2) W := fun m => if hm : (m 0 = 0 ∨ m 1 = 0) then Classical.choose (h m hm) else 0
  let r : MvPowerSeries (Fin 2) W := fun m => coeff (m + e 0 + e 1) f
  have hg1 : ∀ m : Fin 2 →₀ ℕ, (m 0 = 0 ∨ m 1 = 0) → coeff m f = π * coeff m g := by
    intro m hm
    have : coeff m g = Classical.choose (h m hm) := by
      show g m = _
      simp only [g, dif_pos hm]
    rw [this]; exact Classical.choose_spec (h m hm)
  have hg2 : ∀ m : Fin 2 →₀ ℕ, ¬ (m 0 = 0 ∨ m 1 = 0) → coeff m g = 0 := by
    intro m hm
    show g m = 0
    simp only [g, dif_neg hm]
  refine ⟨g, r, ?_⟩
  ext m
  have hXX : (X 0 : MvPowerSeries (Fin 2) W) * X 1 = monomial (e 0 + e 1) 1 := by
    rw [X_eq_monomial, X_eq_monomial, monomial_mul_monomial, one_mul]
  rw [map_add, coeff_C_mul, hXX, coeff_monomial_one_mul]
  by_cases hm : m 0 = 0 ∨ m 1 = 0
  · rw [if_neg, add_zero, hg1 m hm]
    intro hle
    rcases hm with h0 | h1
    · have := hle 0; simp [e, h0] at this
    · have := hle 1; simp [e, h1] at this
  · push Not at hm
    have hmn : e 0 + e 1 ≤ m := by
      intro j
      fin_cases j
      · simp [e]; omega
      · simp [e]; omega
    rw [hg2 m (by push Not; exact hm), mul_zero, zero_add, if_pos hmn]
    show coeff m f = coeff (m - (e 0 + e 1) + e 0 + e 1) f
    rw [add_assoc, tsub_add_cancel_of_le hmn]

end ALGProof

open ALGProof MvPowerSeries in
theorem solution
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E) :
    Ideal.span {const (π ^ E) π, U (π ^ E)} ⊓ Ideal.span {const (π ^ E) π, V (π ^ E)}
        = Ideal.span {const (π ^ E) π} ∧
    (∀ n : ℕ, V (π ^ E) ^ n ∉ Ideal.span {const (π ^ E) π, U (π ^ E)}) ∧
    (∀ n : ℕ, U (π ^ E) ^ n ∉ Ideal.span {const (π ^ E) π, V (π ^ E)}) ∧
    (⨅ n : ℕ, Ideal.span {const (π ^ E) π, U (π ^ E)} ⊔ Ideal.span {V (π ^ E) ^ n})
        = Ideal.span {const (π ^ E) π, U (π ^ E)} ∧
    (⨅ n : ℕ, Ideal.span {const (π ^ E) π, V (π ^ E)} ⊔ Ideal.span {U (π ^ E) ^ n})
        = Ideal.span {const (π ^ E) π, V (π ^ E)} := by
  classical
  have hU : U (π ^ E) = mk (π ^ E) (X 0) := rfl
  have hV : V (π ^ E) = mk (π ^ E) (X 1) := rfl

  have hπ1 : ¬ (π ∣ (1 : W)) := fun h => hπ.not_isUnit (isUnit_of_dvd_one h)

  have hpow : ∀ (i j : Fin 2), i ≠ j → ∀ n : ℕ,
      mk (π ^ E) (X j) ^ n ∉ Ideal.span ({const (π ^ E) π, mk (π ^ E) (X i)} : Set (UVCrossingModel W (π ^ E))) := by
    intro i j hij n hmem
    rw [← map_pow, ALGProof.mk_mem_branchIdeal_iff π E hE i] at hmem
    have h1 := (ALGProof.mem_span_C_X_iff π i _).mp hmem (Finsupp.single j n) (by simp [Finsupp.single_apply, hij.symm])
    rw [show (X j : MvPowerSeries (Fin 2) W) ^ n = monomial (Finsupp.single j n) 1 by
      rw [X_pow_eq], coeff_monomial_same] at h1
    exact hπ1 h1

  have hiInf : ∀ (i j : Fin 2), i ≠ j →
      (⨅ n : ℕ, Ideal.span ({const (π ^ E) π, mk (π ^ E) (X i)} : Set (UVCrossingModel W (π ^ E)))
          ⊔ Ideal.span {mk (π ^ E) (X j) ^ n})
        = Ideal.span {const (π ^ E) π, mk (π ^ E) (X i)} := by
    intro i j hij
    refine le_antisymm ?_ (le_iInf fun n => le_sup_left)
    intro x hx
    obtain ⟨f, rfl⟩ := mk_surjective (π ^ E) x
    rw [ALGProof.mk_mem_branchIdeal_iff π E hE i, ALGProof.mem_span_C_X_iff]
    intro m hm
    have hn := (Submodule.mem_iInf _).mp hx (m j + 1)
    rw [← map_pow] at hn
    obtain ⟨a', ha', b', hb', hab⟩ := Submodule.mem_sup.mp hn
    obtain ⟨a, rfl⟩ := mk_surjective (π ^ E) a'
    rw [ALGProof.mk_mem_branchIdeal_iff π E hE i] at ha'
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hb'
    obtain ⟨c, rfl⟩ := mk_surjective (π ^ E) c'

    have hk : f - a - c * X j ^ (m j + 1) ∈ Ideal.span ({C π, X i} : Set (MvPowerSeries (Fin 2) W)) := by
      apply ALGProof.uvCrossingIdeal_le_span_C_X π E hE i
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      show mk (π ^ E) (f - a - c * X j ^ (m j + 1)) = 0
      rw [map_sub, map_sub, map_mul, ← hab, add_sub_cancel_left, sub_self]
    have hbm : coeff m (c * X j ^ (m j + 1)) = 0 :=
      (X_pow_dvd_iff.mp (dvd_mul_left _ c)) m (Nat.lt_succ_self _)
    have ham := (ALGProof.mem_span_C_X_iff π i a).mp ha' m hm
    have hkm := (ALGProof.mem_span_C_X_iff π i _).mp hk m hm
    rw [map_sub, map_sub, hbm, sub_zero] at hkm
    have : coeff m f = (coeff m f - coeff m a) + coeff m a := by ring
    rw [this]
    exact dvd_add hkm ham

  have hinf : Ideal.span ({const (π ^ E) π, mk (π ^ E) (X 0)} : Set (UVCrossingModel W (π ^ E)))
      ⊓ Ideal.span {const (π ^ E) π, mk (π ^ E) (X 1)} = Ideal.span {const (π ^ E) π} := by
    refine le_antisymm ?_ (le_inf (Ideal.span_mono (by simp)) (Ideal.span_mono (by simp)))
    intro x hx
    obtain ⟨f, rfl⟩ := mk_surjective (π ^ E) x
    obtain ⟨h0, h1⟩ := Submodule.mem_inf.mp hx
    rw [ALGProof.mk_mem_branchIdeal_iff π E hE, ALGProof.mem_span_C_X_iff] at h0 h1
    obtain ⟨g, r, hf⟩ := ALGProof.exists_eq_C_mul_add_X_mul_X_mul π f
      (fun m hm => hm.elim (h0 m) (h1 m))

    obtain ⟨E', hE'⟩ := Nat.exists_eq_add_of_le hE
    have : mk (π ^ E) f = const (π ^ E) π * mk (π ^ E) (g + C (π ^ E') * r) := by
      have hrel : mk (π ^ E) ((X 0 : MvPowerSeries (Fin 2) W) * X 1 - C (π ^ E)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [hf, show const (π ^ E) π = mk (π ^ E) (C π) from rfl, ← map_mul, map_add (mk (π ^ E)),
        map_mul (mk (π ^ E)) (X 0 * X 1), show mk (π ^ E) ((X 0 : MvPowerSeries (Fin 2) W) * X 1)
          = mk (π ^ E) (C (π ^ E)) from (sub_eq_zero.mp (by rw [← map_sub]; exact hrel)), ← map_mul, ← map_add]
      congr 1
      rw [hE', pow_add, pow_one, map_mul]
      ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hU, hV]; exact hinf
  · rw [hU, hV]; exact hpow 0 1 (by decide)
  · rw [hU, hV]; exact hpow 1 0 (by decide)
  · rw [hU, hV]; exact hiInf 0 1 (by decide)
  · rw [hU, hV]; exact hiInf 1 0 (by decide)

end S_ModularCurve_UVCrossingModel_span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_span_inf_span_eq_and_pow_notMem_and_iInf_sup_span_pow_eq (solution)

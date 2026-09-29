-- Prove2me | solution 1 for MvPowerSeries.exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bf2f1722-d154-537e-a18f-fed7ad1d9ab7

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow

set_option autoImplicit false

universe u v

open MvPowerSeries

namespace TCHenselGC7

theorem aux {κ : Type u} [Field κ] (n : ℕ) :
    ∀ {ι : Type v} [Fintype ι] (a b : ι → κ), Fintype.card ι = n →
      (∀ i j : ι, i ≠ j → a i * b j - a j * b i ≠ 0) →
      ∀ f : MvPowerSeries (Fin 2) κ,
        f - ∏ i, (C (a i) * X 0 + C (b i) * X 1) ∈
          (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1) →
        ∃ (L : ι → MvPowerSeries (Fin 2) κ) (w : MvPowerSeries (Fin 2) κ), IsUnit w ∧
          (∀ i, L i - (C (a i) * X 0 + C (b i) * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2) ∧
          f = w * ∏ i, L i := by
  classical
  induction n with
  | zero =>
    intro ι _ a b hcard hab f hf
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    rw [hcard, zero_add, pow_one, Fintype.prod_empty] at hf
    refine ⟨fun i => isEmptyElim i, f, ?_, fun i => isEmptyElim i, by rw [Fintype.prod_empty, mul_one]⟩
    rw [isUnit_iff_constantCoeff]
    have hle : Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} ≤ RingHom.ker constantCoeff := by
      rw [Ideal.span_le]; rintro x hx
      rcases hx with rfl | rfl <;> simp [RingHom.mem_ker, constantCoeff_X]
    have := hle hf
    rw [RingHom.mem_ker, map_sub, constantCoeff_one, sub_eq_zero] at this
    rw [this]; exact isUnit_one
  | succ n ih =>
    intro ι _ a b hcard hab f hf
    haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨i₀⟩ := ‹Nonempty ι›

    let s : Finset ι := Finset.univ.erase i₀
    have hs : Fintype.card ↥s = n := by
      rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]; rfl
    have hsplit : ∀ g : ι → MvPowerSeries (Fin 2) κ, ∏ i, g i = g i₀ * ∏ i : ↥s, g i := by
      intro g
      rw [Finset.prod_coe_sort, Finset.mul_prod_erase _ _ (Finset.mem_univ _)]

    by_cases hab0 : ¬ (a i₀ ≠ 0 ∨ b i₀ ≠ 0)
    · push Not at hab0
      have hall : ∀ j : ι, j = i₀ := by
        intro j; by_contra hj
        exact hab i₀ j (Ne.symm hj) (by rw [hab0.1, hab0.2]; ring)
      haveI : IsEmpty ↥s := ⟨fun i => (Finset.mem_erase.mp i.2).1 (hall i)⟩
      have hℓ0 : C (a i₀) * X 0 + C (b i₀) * X 1 = (0 : MvPowerSeries (Fin 2) κ) := by
        rw [hab0.1, hab0.2]; simp
      have hf2 : f ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 := by
        rw [hsplit (fun i => C (a i) * X 0 + C (b i) * X 1), hℓ0, zero_mul, sub_zero, hcard] at hf
        have hn : n = 0 := by rw [← hs]; exact Fintype.card_eq_zero
        rw [hn] at hf; exact hf
      refine ⟨fun _ => f, 1, isUnit_one, ?_, ?_⟩
      · intro i; rw [hall i, hℓ0, sub_zero]; exact hf2
      · rw [hsplit (fun _ => f), Fintype.prod_empty, mul_one, one_mul]
    push Not at hab0

    have h2 : Fintype.card ↥s + 2 = Fintype.card ι + 1 := by rw [hs, hcard]
    obtain ⟨L₀, f₁, hL₀, hf₁, hff⟩ := MvPowerSeries.exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero (a i₀) (b i₀) hab0 (fun i : ↥s => a i) (fun i : ↥s => b i)
      (fun i => hab i₀ i (Finset.mem_erase.mp i.2).1.symm) f
      (by rw [h2]; rw [hsplit (fun i => C (a i) * X 0 + C (b i) * X 1)] at hf; exact hf)

    obtain ⟨L', w, hw, hL', hf₁'⟩ := ih (fun i : ↥s => a i) (fun i : ↥s => b i) hs
      (fun i j hij => hab i j fun h => hij (Subtype.ext h)) f₁ hf₁
    refine ⟨fun i => if h : i = i₀ then L₀ else L' ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ i⟩⟩, w, hw, ?_, ?_⟩
    · intro i
      by_cases h : i = i₀
      · subst h; simp only [dif_pos]; exact hL₀
      · simp only [dif_neg h]; exact hL' ⟨i, _⟩
    · rw [hsplit, dif_pos rfl, hff, hf₁']
      have : ∀ i : ↥s, (if h : (i : ι) = i₀ then L₀ else L' ⟨i, Finset.mem_erase.mpr ⟨h, Finset.mem_univ (i : ι)⟩⟩) = L' i := by
        intro i
        rw [dif_neg (Finset.mem_erase.mp i.2).1]
      simp_rw [this]; ring

end TCHenselGC7

open TCHenselGC7 in
theorem solution
    {κ : Type u} [Field κ] {ι : Type v} [Fintype ι]
    (a b : ι → κ) (hab : ∀ i j : ι, i ≠ j → a i * b j - a j * b i ≠ 0)
    (f : MvPowerSeries (Fin 2) κ)
    (hf : f - ∏ i, (C (a i) * X 0 + C (b i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1)) :
    ∃ (L : ι → MvPowerSeries (Fin 2) κ) (w : MvPowerSeries (Fin 2) κ), IsUnit w ∧
      (∀ i, L i - (C (a i) * X 0 + C (b i) * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2) ∧
      f = w * ∏ i, L i :=
  aux (Fintype.card ι) a b rfl hab f hf

end S_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow
end P2MW
export P2MW.S_MvPowerSeries_exists_isUnit_mul_prod_eq_of_sub_prod_linear_mem_pow (solution)

-- Prove2me | solution 1 for LLLFactor.Factors.mignotte_step
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T21:45:18.172962+00:00
-- url     : https://prove2.me/submissions/cf0ee284-6934-49bf-b056-5df2c2e88eba

import Definitions.Def_LLLFactor_Factors_Setting
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Polynomial Finset LLLFactor.Factors

namespace MignotteStepProof

lemma polyNorm_nonneg (f : ℤ[X]) : 0 ≤ polyNorm f := Real.sqrt_nonneg _

lemma polyNorm_sq (f : ℤ[X]) :
    polyNorm f ^ 2 = ∑ i ∈ f.support, (f.coeff i : ℝ) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma mahler_le_polyNorm (f : ℤ[X]) :
    (f.map (Int.castRingHom ℂ)).mahlerMeasure ≤ polyNorm f := by
  have h := (f.map (Int.castRingHom ℂ)).mahlerMeasure_le_sqrt_sum_sq_norm_coeff
  simpa [polyNorm, Polynomial.support_map_of_injective f (Int.castRingHom ℂ).injective_int,
    Polynomial.coeff_map, Complex.norm_intCast, Int.cast_abs, sq_abs] using h

lemma divisor_coeff_bound {f g : ℤ[X]} (hf : f ≠ 0) (hg : g ∣ f)
    (m : ℕ) (hm : g.natDegree ≤ m) (i : ℕ) :
    |(g.coeff i : ℝ)| ≤ (m.choose i : ℝ) * polyNorm f := by
  obtain ⟨q, rfl⟩ := hg
  have hq : q ≠ 0 := by intro h; simp [h] at hf
  have hc := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure i
    (g.map (Int.castRingHom ℂ)) (q.map (Int.castRingHom ℂ))
    (Polynomial.one_le_mahlerMeasure_of_ne_zero hq)
  have hd : (g.map (Int.castRingHom ℂ)).natDegree ≤ m :=
    (Polynomial.natDegree_map_le).trans hm
  have hchoose : ((g.map (Int.castRingHom ℂ)).natDegree.choose i : ℝ) ≤ (m.choose i : ℝ) := by
    exact_mod_cast Nat.choose_le_choose i hd
  have hmahler := mahler_le_polyNorm (g * q)
  rw [Polynomial.map_mul] at hmahler
  calc
    |(g.coeff i : ℝ)| = ‖(g.map (Int.castRingHom ℂ)).coeff i‖ := by simp
    _ ≤ _ := hc
    _ ≤ _ := mul_le_mul hchoose hmahler (Polynomial.mahlerMeasure_nonneg _) (by positivity)

lemma mignotte_sq {f g : ℤ[X]} (hf : f ≠ 0) (hg : g ∣ f)
    (m : ℕ) (hm : g.natDegree ≤ m) :
    polyNorm g ^ 2 ≤ ((2 * m).choose m : ℝ) * polyNorm f ^ 2 := by
  have he : polyNorm g ^ 2 = ∑ i ∈ Finset.range (m + 1), (g.coeff i : ℝ) ^ 2 := by
    rw [polyNorm_sq]
    exact g.sum_over_range' (f := fun _ a => (a : ℝ) ^ 2) (by simp) (m + 1) (by omega)
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℝ) * polyNorm f) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := divisor_coeff_bound hf hg m hm i
      have hn : 0 ≤ (m.choose i : ℝ) * polyNorm f := mul_nonneg (by positivity) (polyNorm_nonneg _)
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (g.coeff i : ℝ)) hn).mpr h
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) ^ 2) * polyNorm f ^ 2 := by
      simp only [mul_pow, Finset.sum_mul]
    _ = _ := by
      congr 1
      exact_mod_cast Nat.sum_range_choose_sq m

end MignotteStepProof

theorem solution (f : ℤ[X]) (hf : f ≠ 0) (m : ℕ) (g : ℤ[X]) (hgf : g ∣ f)
    (hgm : g.natDegree ≤ m) :
    polyNorm g ≤ ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * polyNorm f := by
  rw [← Real.sqrt_eq_rpow]
  have h := MignotteStepProof.mignotte_sq hf hgf m hgm
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((2 * m).choose m : ℝ) by positivity)
  have hn := MignotteStepProof.polyNorm_nonneg f
  have hg0 := MignotteStepProof.polyNorm_nonneg g
  have hsn := Real.sqrt_nonneg ((2 * m).choose m : ℝ)
  nlinarith [mul_nonneg hsn hn, mul_pow (Real.sqrt ((2 * m).choose m : ℝ)) (polyNorm f) 2]

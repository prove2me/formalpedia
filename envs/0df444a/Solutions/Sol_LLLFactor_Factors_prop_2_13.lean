-- Prove2me | solution 1 for LLLFactor.Factors.prop_2_13
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:05:18.389417+00:00
-- url     : https://prove2.me/submissions/eabc97d5-25bd-4eb7-8f07-0837171cb07e

import Definitions.Def_LLLFactor_Factors_Setting
import Theorems.Thm_LLLFactor_Factors_prop_2_7
import Theorems.Thm_LLLFactor_Factors_subset_2_19

open Polynomial Finset LLLFactor.Factors

namespace Prop213Proof

lemma polyNorm_nonneg (f : ℤ[X]) : 0 ≤ polyNorm f := Real.sqrt_nonneg _

lemma polyNorm_sq (f : ℤ[X]) :
    polyNorm f ^ 2 = ∑ i ∈ f.support, (f.coeff i : ℝ) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma sum_coeff_sq_le (f : ℤ[X]) (s : Finset ℕ) :
    (∑ i ∈ s, (f.coeff i : ℝ) ^ 2) ≤ polyNorm f ^ 2 := by
  rw [polyNorm_sq]
  calc
    _ ≤ ∑ i ∈ f.support ∪ s, (f.coeff i : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (by intros; positivity)
    _ = _ := (Finset.sum_subset Finset.subset_union_left (by
      intro i _ hi
      simp [Polynomial.notMem_support_iff.mp hi])).symm

lemma one_le_polyNorm {f : ℤ[X]} (hf : f ≠ 0) : 1 ≤ polyNorm f := by
  have hc : (1 : ℝ) ≤ |(f.leadingCoeff : ℝ)| := by
    exact_mod_cast (Int.one_le_abs (Polynomial.leadingCoeff_ne_zero.mpr hf))
  have hs := sum_coeff_sq_le f {f.natDegree}
  simp only [Finset.sum_singleton, coeff_natDegree] at hs
  have hn := polyNorm_nonneg f
  nlinarith [sq_abs (f.leadingCoeff : ℝ)]

lemma polyNorm_pos {f : ℤ[X]} (hf : f ≠ 0) : 0 < polyNorm f :=
  lt_of_lt_of_le zero_lt_one (one_le_polyNorm hf)

lemma coeffVec_zero (m : ℕ) : coeffVec m 0 = 0 := by
  ext i
  simp [coeffVec]

lemma basis_polynomial_ne_zero {p k m : ℕ} {h : ℤ[X]} {b : Fin (m + 1) → ℤ[X]}
    (hb : IsReducedBasisOfL p k h m b) (j : Fin (m + 1)) : b j ≠ 0 := by
  intro hz
  have hn := hb.2.1.ne_zero j
  apply hn
  change coeffVec m (b j) = 0
  rw [hz, coeffVec_zero]

lemma threshold_pow (F P : ℝ) (m n : ℕ) (hF : 0 < F) (hP : 0 < P) (hn : 0 < n) :
    ((P / F ^ m) ^ ((1 : ℝ) / (n : ℝ))) ^ n = P / F ^ m := by
  rw [← Real.rpow_mul_natCast (le_of_lt (div_pos hP (pow_pos hF _)))]
  rw [div_mul_cancel₀ (1 : ℝ) (by exact_mod_cast ne_of_gt hn), Real.rpow_one]

lemma threshold_iff (F P B : ℝ) (m n : ℕ) (hF : 0 < F) (hP : 0 < P)
    (hB : 0 ≤ B) (hn : 0 < n) :
    B < (P / F ^ m) ^ ((1 : ℝ) / (n : ℝ)) ↔ F ^ m * B ^ n < P := by
  have hp := threshold_pow F P m n hF hP hn
  have ht : 0 ≤ (P / F ^ m) ^ ((1 : ℝ) / (n : ℝ)) :=
    Real.rpow_nonneg (le_of_lt (div_pos hP (pow_pos hF _))) _
  have he := Real.rpow_lt_rpow_iff hB ht (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn)
  rw [Real.rpow_natCast, Real.rpow_natCast, hp] at he
  rw [← he, lt_div_iff₀ (pow_pos hF _)]
  exact ⟨fun h => by simpa only [mul_comm] using h, fun h => by simpa only [mul_comm] using h⟩

end Prop213Proof

theorem solution {p k : ℕ} (f h : ℤ[X]) (hS : IsSetting p k f h)
    (m : ℕ) (hm : h.natDegree ≤ m) (h₀ : ℤ[X]) (hh₀ : IsH0 p f h h₀)
    (b : Fin (m + 1) → ℤ[X]) (hb : IsReducedBasisOfL p k h m b)
    (h214 : (2 : ℝ) ^ ((m : ℝ) * (f.natDegree : ℝ) / 2) *
        ((Nat.choose (2 * m) m : ℕ) : ℝ) ^ ((f.natDegree : ℝ) / 2) *
        polyNorm f ^ (m + f.natDegree) < (p : ℝ) ^ (k * h.natDegree)) :
    h₀.natDegree ≤ m ↔
      polyNorm (b ⟨0, Nat.succ_pos m⟩) <
        ((p : ℝ) ^ (k * h.natDegree) / polyNorm f ^ m) ^ ((1 : ℝ) / (f.natDegree : ℝ)) := by
  constructor
  · intro hdeg
    exact subset_2_19 f h hS m hm h₀ hh₀ b hb h214 hdeg ⟨0, Nat.succ_pos m⟩
      (Nat.sub_pos_of_lt (Nat.lt_succ_of_le hdeg))
  · intro hlt
    have hf : f ≠ 0 := by
      intro hz
      have hn := hS.deg_f_pos
      simp [hz] at hn
    have hp : (0 : ℝ) < p := by exact_mod_cast hS.prime.pos
    have hP : (0 : ℝ) < (p : ℝ) ^ (k * h.natDegree) := pow_pos hp _
    have hF := Prop213Proof.polyNorm_pos hf
    have h28 : polyNorm f ^ m * polyNorm (b ⟨0, Nat.succ_pos m⟩) ^ f.natDegree <
        (p : ℝ) ^ (k * h.natDegree) :=
      (Prop213Proof.threshold_iff (polyNorm f) ((p : ℝ) ^ (k * h.natDegree))
        (polyNorm (b ⟨0, Nat.succ_pos m⟩)) m f.natDegree hF hP
        (Prop213Proof.polyNorm_nonneg _) hS.deg_f_pos).mp hlt
    have hdvd : h₀ ∣ b ⟨0, Nat.succ_pos m⟩ :=
      (prop_2_7 f h hS m hm h₀ hh₀ (b ⟨0, Nat.succ_pos m⟩) (hb.1 _) h28).1
    exact (Polynomial.natDegree_le_of_dvd hdvd
      (Prop213Proof.basis_polynomial_ne_zero hb _)).trans (hb.1 _).1

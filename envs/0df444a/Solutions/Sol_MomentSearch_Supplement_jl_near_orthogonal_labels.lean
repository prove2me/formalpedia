-- Prove2me | solution 1 for MomentSearch.Supplement.jl_near_orthogonal_labels
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:21:55.747211+00:00
-- url     : https://prove2.me/submissions/aa66d94e-f2d7-40c6-a380-90ba3e149c7d

import Mathlib
import Theorems.Thm_FoundationsML_DimReduction_johnson_lindenstrauss

open Finset FoundationsML.DimReduction

private def basis {n : ℕ} (a j : Fin n) : ℝ := if a = j then 1 else 0

private lemma basis_dot {n : ℕ} (a b : Fin n) :
    (∑ j, basis a j * basis b j) = (if a = b then 1 else 0) := by
  simp [basis]

private lemma polar {n : ℕ} (u v : Fin n → ℝ) :
    SqNorm (u-v) = SqNorm u + SqNorm v - 2*(∑ j, u j * v j) := by
  unfold SqNorm
  rw [mul_sum,← sum_add_distrib,← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by simp only [Pi.sub_apply]; ring

private lemma basis_norm {n : ℕ} (a : Fin n) : SqNorm (basis a) = 1 := by
  simp [SqNorm,basis,ite_pow]

theorem solution : ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ), 2 ≤ n → ∀ η : ℝ, 0 < η → η < 1 →
    ∃ R : ℕ, (R : ℝ) ≤ A * Real.logb 2 n / η^2 ∧
      ∃ g : Fin n → Fin R → ℝ, ∀ a b,
        |(∑ s, g a s * g b s) - (if a = b then 1 else 0)| ≤ η := by
  classical
  refine ⟨161,by norm_num,?_⟩
  intro n hn η hη hη1
  have nr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have L : 1 ≤ Real.logb 2 n := by
    simpa using (Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0:ℝ)<2) nr)
  have sq : η^2 ≤ 1 := by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη1.le)]
  by_cases small : n < 4
  · refine ⟨n, (le_div_iff₀ (sq_pos_of_pos hη)).mpr ?_,basis,?_⟩
    · have h3 : (n:ℝ) ≤ 3 := by exact_mod_cast (by omega : n ≤ 3)
      nlinarith [mul_le_mul_of_nonneg_left sq (Nat.cast_nonneg n)]
    · intro a b; rw [basis_dot,sub_self,abs_zero]; exact hη.le
  let points : Finset (Fin n → ℝ) := insert 0 (univ.image basis)
  have inj : Function.Injective (basis (n:=n)) := by
    intro a b hab
    by_contra h
    have eq := congrFun hab a
    simp [basis] at eq
    exact h eq.symm
  have fresh : (0 : Fin n → ℝ) ∉ univ.image basis := by
    rintro h
    obtain ⟨a,_,ha⟩ := mem_image.mp h
    have eq := congrFun ha a
    simp [basis] at eq
  have card : points.card = n+1 := by
    simp [points,fresh,card_image_of_injective _ inj]
  let e := η/2
  obtain ⟨f,hf⟩ := johnson_lindenstrauss e (by dsimp [e]; positivity)
    (by dsimp [e]; linarith) (n+1) (by omega) points card
  let R := ⌈20 * Real.log ((n+1:ℕ):ℝ) / e^2⌉₊
  let g (a : Fin n) : Fin R → ℝ := f (basis a) - f 0
  have ln : Real.log ((n+1:ℕ):ℝ) ≤ 2 * Real.logb 2 n := by
    have h := Real.log_le_log (by positivity : 0 < ((n+1:ℕ):ℝ))
      (show ((n+1:ℕ):ℝ) ≤ (n:ℝ)^2 by push_cast; nlinarith [sq_nonneg ((n:ℝ)-2)])
    rw [Real.log_pow] at h
    have eq : Real.log n = Real.logb 2 n * Real.log 2 := by
      rw [Real.logb]; field_simp
    have lt := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      Real.log (n:ℝ) = _ := eq
      _ ≤ Real.logb 2 n * 1 := mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans L)
      _ = _ := mul_one _
  refine ⟨R,?_,g,?_⟩
  · have pos : 0 ≤ 20*Real.log ((n+1:ℕ):ℝ)/e^2 := by
      apply div_nonneg _ (sq_nonneg _)
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n+1)))
    have hc := Nat.ceil_lt_add_one pos
    change (R:ℝ) < _ at hc
    have h := (lt_div_iff₀ (sq_pos_of_pos hη)).mp
      (show (R:ℝ) < (80*Real.log ((n+1:ℕ):ℝ) + η^2)/η^2 by
        convert hc using 1
        dsimp [e]
        field_simp
        ring)
    apply (le_div_iff₀ (sq_pos_of_pos hη)).mpr
    linarith
  · have mem (a : Fin n) : basis a ∈ points := mem_insert_of_mem (mem_image_of_mem _ (mem_univ a))
    have zero_mem : 0 ∈ points := mem_insert_self ..
    have norm (a : Fin n) : 1-e ≤ SqNorm (g a) ∧ SqNorm (g a) ≤ 1+e := by
      simpa [g,basis_norm] using hf _ (mem a) 0 zero_mem
    intro a b
    by_cases hab : a = b
    · subst b
      simp only [if_true]
      have eq : (∑ s, g a s * g a s) = SqNorm (g a) := by simp [SqNorm,pow_two]
      rw [eq,abs_le]
      dsimp [e] at *
      constructor <;> linarith [(norm a).1,(norm a).2]
    · have orig : SqNorm (basis a - basis b) = 2 := by
        rw [polar,basis_norm,basis_norm,basis_dot,if_neg hab]; norm_num
      have dist := hf _ (mem a) _ (mem b)
      rw [orig,show f (basis a) - f (basis b) = g a - g b by dsimp [g]; abel,polar] at dist
      rw [if_neg hab,sub_zero,abs_le]
      have na := norm a
      have nb := norm b
      dsimp [e] at na nb dist
      constructor <;> linarith [dist.1,dist.2,na.1,na.2,nb.1,nb.2]

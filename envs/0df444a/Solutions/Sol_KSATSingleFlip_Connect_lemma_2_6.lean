-- Prove2me | solution 1 for KSATSingleFlip.Connect.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:02:19.39557+00:00
-- url     : https://prove2.me/submissions/922f8b0b-03fa-47db-a668-9c2fd33dd75c

import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_fixed_clause_count
import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_poisson_positive
import Theorems.Thm_KSATSingleFlip_Connect_poisson_zero_count_deterministic
import Theorems.Thm_KSATSingleFlip_Connect_lemma_2_6_size_condition
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution :
  (∀ (A : Type) [MeasurableSpace A] (D : Measure A) [IsProbabilityMeasure D]
      (F : List A → ℝ) (j : ℕ) (hj : 1 ≤ j)
      (hF : Measurable (fun x : Fin j → A => F (List.ofFn x)))
      (L u : ℝ) (hL : 1 ≤ L) (hu : 0 < u)
      (hins : ∀ (xs : List A) (i : ℕ) (z : A), |F (xs.insertIdx i z)-F xs| ≤ L),
      (Measure.pi (fun _ : Fin j => D)) {x | F (List.ofFn x) ≤
        (∫ y, F (List.ofFn y) ∂(Measure.pi (fun _ : Fin j => D)))-u} ≤
      ENNReal.ofReal (Real.exp (-(u^2)/(2*(j:ℝ)*L^2)))) ∧
  (∀ (ν a L : ℝ), 0 ≤ ν → 0 < a → a ≤ 1 → 1 ≤ L →
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∀ (Ω A : Type) [MeasurableSpace Ω] [MeasurableSpace A]
        (P : Measure Ω) [IsProbabilityMeasure P] (D : Measure A) [IsProbabilityMeasure D]
        (N : Ω → ℕ) (hN : Measurable N) (r : ℝ≥0) (hNlaw : Measure.map N P = poissonMeasure r)
        (X : ℕ → Ω → A) (hX : ∀ i, Measurable (X i))
        (hlaw : ∀ j, Measure.map (fun ω (i : Fin j) => X i.val ω) P = Measure.pi (fun _ : Fin j => D))
        (hind : ∀ j, IndepFun N (fun ω (i : Fin j) => X i.val ω) P)
        (F : List A → ℝ) (hF : ∀ j, Measurable (fun x : Fin j → A => F (List.ofFn x)))
        (hrν : (r:ℝ) = ν*(n:ℝ))
        (hbound : ∀ xs, 0 ≤ F xs ∧ F xs ≤ (n:ℝ))
        (hins : ∀ (xs : List A) (i : ℕ) (z : A), |F (xs.insertIdx i z)-F xs| ≤ L),
      P.real {ω | F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ≤
        (∫ ω, F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) ∂P)-a*(n:ℝ)} ≤
        3*Real.exp (-(a^2*(n:ℝ))/(128*(ν+1)*L^2))) := by
  constructor
  · intro A _ D _ F j hj hF L u hL hu hins
    exact KSATSingleFlip.Connect.lemma_2_6_fixed_clause_count j hj D F hF L u hL hu hins
  · intro ν a L hν ha ha1 hL
    obtain ⟨n0,hn0⟩ := exists_nat_gt (16*L^2*ν/a^2+1)
    refine ⟨n0, ?_⟩
    intro n hn Ω A _ _ P _ D _ N hN r hNlaw X hX hlaw hind F hF hrν hbound hins
    have hna : (n0:ℝ) ≤ n := by exact_mod_cast hn
    have hL' : 0 < L := by linarith
    have ha2 : 0 < a^2 := sq_pos_of_pos ha
    have hbase : 0 ≤ 16*L^2*ν/a^2 := by positivity
    have hn' : (0:ℝ) < n := by linarith
    have hsize : 16*L^2*ν ≤ a^2*(n:ℝ) := by
      have hbound' : 16*L^2*ν/a^2 ≤ (n:ℝ) := by linarith
      simpa [mul_comm] using (div_le_iff₀ ha2).mp hbound'
    have hsqrt := KSATSingleFlip.Connect.lemma_2_6_size_condition ν a L n hν ha hL' hn' hsize
    by_cases hr0 : r = 0
    · have hzero : ∀ ω, N ω = 0 → F (List.ofFn (fun i : Fin (N ω) => X i.val ω)) = F [] := by
        intro ω hω
        simp [hω]
      have hz := KSATSingleFlip.Connect.poisson_zero_count_deterministic P N hN
        (by simpa [hr0] using hNlaw) (fun ω => F (List.ofFn (fun i : Fin (N ω) => X i.val ω)))
        (F []) (a*n) (by positivity) hzero
      rw [hz]
      positivity
    · have hrpos : 0 < r := pos_iff_ne_zero.mpr hr0
      exact KSATSingleFlip.Connect.lemma_2_6_poisson_positive P D N hN r hrpos hNlaw X hX hlaw hind F hF
        ν a L n hν ha ha1 hL hn' hrν hsqrt hbound hins

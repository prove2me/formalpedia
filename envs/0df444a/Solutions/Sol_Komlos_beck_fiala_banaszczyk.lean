-- Prove2me | solution 1 for Komlos.beck_fiala_banaszczyk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T07:19:38.986683+00:00
-- url     : https://prove2.me/submissions/5cbb037e-50ec-4ac3-ad92-12df5037a023
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Komlos_model
import Theorems.Thm_Komlos_banaszczyk_bound

open Komlos

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (t n m : ℕ) (A : Fin m → Fin n → ℝ),
      (∀ i j, A i j = 0 ∨ A i j = 1) →
      (∀ j, ({i | A i j = 1} : Finset (Fin m)).card ≤ t) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ i, |∑ j, A i j * ε j| ≤ C * Real.sqrt (t * Real.log (n + 2)) := by
  obtain ⟨C, hC, hB⟩ := banaszczyk_bound
  refine ⟨C, hC, ?_⟩
  intro t n m A h01 hcard
  by_cases ht0 : t = 0
  · subst t
    have hzero : ∀ i j, A i j = 0 := by
      intro i j
      rcases h01 i j with h | h
      · exact h
      · exfalso
        have hi : i ∈ ({i | A i j = 1} : Finset (Fin m)) := by simpa [h]
        have hone : 1 ≤ ({i | A i j = 1} : Finset (Fin m)).card :=
          Finset.one_le_card.mpr ⟨i, hi⟩
        have hz := hcard j
        omega
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro i
      exact Or.inl rfl
    · intro i
      simp [hzero]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht0
    let v : Fin n → EuclideanSpace ℝ (Fin m) :=
      fun j => WithLp.toLp 2 (fun i => A i j / Real.sqrt t)
    have hv : ∀ j, ‖v j‖ ≤ 1 := by
      intro j
      have hsq : ∀ i, (A i j / Real.sqrt t) ^ 2 =
          if A i j = 1 then (1 : ℝ) / t else 0 := by
        intro i
        rcases h01 i j with h | h <;> simp [h, div_pow, Real.sq_sqrt,
          (show (0 : ℝ) ≤ t by positivity), ht0]
      have hnormsq : ‖v j‖ ^ 2 =
          ({x | A x j = 1} : Finset (Fin m)).card / t := by
        rw [EuclideanSpace.real_norm_sq_eq]
        dsimp [v]
        simp_rw [hsq]
        have hterm : ∀ i : Fin m,
            (if A i j = 1 then (1 : ℝ) / t else 0) =
              (if A i j = 1 then (1 : ℝ) else 0) * (1 / t) := by
          intro i
          split_ifs <;> ring
        simp_rw [hterm]
        rw [← Finset.sum_mul, Finset.sum_boole]
        ring
      have hcardj := hcard j
      have ht_real : (0 : ℝ) < t := by exact_mod_cast htpos
      have hcard_real :
          (({x | A x j = 1} : Finset (Fin m)).card : ℝ) ≤ t := by
        exact_mod_cast hcardj
      have hsqle : ‖v j‖ ^ 2 ≤ 1 := by
        rw [hnormsq]
        exact (div_le_iff₀ ht_real).2 (by simpa using hcard_real)
      nlinarith [hsqle, norm_nonneg (v j)]
    obtain ⟨ε, hε, hdisc⟩ := hB n m v hv
    refine ⟨ε, hε, ?_⟩
    intro i
    have hlog : 0 ≤ Real.log (n + 2) := by
      apply Real.log_nonneg
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith
    have ht_real : 0 ≤ (t : ℝ) := by positivity
    have hsqrt_nonneg : 0 ≤ Real.sqrt (t : ℝ) := Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (hdisc i) hsqrt_nonneg
    have hrewrite :
        (∑ j, ε j * v j i) * Real.sqrt t = ∑ j, A i j * ε j := by
      dsimp [v]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      field_simp
    rw [← hrewrite, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      |∑ j, ε j * v j i| * Real.sqrt t =
          Real.sqrt t * |∑ j, ε j * v j i| := by ring
      _ ≤ Real.sqrt t * (C * Real.sqrt (Real.log (n + 2))) := hmul
      _ = C * Real.sqrt (t * Real.log (n + 2)) := by
        rw [Real.sqrt_mul ht_real (Real.log (n + 2))]
        ring

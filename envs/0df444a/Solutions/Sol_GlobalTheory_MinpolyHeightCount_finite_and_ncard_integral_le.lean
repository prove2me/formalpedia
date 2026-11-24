-- Prove2me | solution 1 for GlobalTheory.MinpolyHeightCount.finite_and_ncard_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:34:02.727371+00:00
-- url     : https://prove2.me/submissions/0441e44d-6bdd-47c7-9d1f-193414ed922e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_le_of_fibres_roots
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_natDegree_minpoly_int_le
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_abs_coeff_minpoly_int_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount
variable (K : Type) [Field K] [NumberField K]
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution (R : ℝ) :
    {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.Finite ∧
    (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ) ≤
      Module.finrank ℚ K * (2 * (max R 1 ^ Module.finrank ℚ K *
        (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2)) + 3) ^
          (Module.finrank ℚ K + 1) := by
  classical
  set d := Module.finrank ℚ K with hd
  set M : ℝ := max R 1 ^ d * (d.choose (d / 2) : ℝ) with hM
  set C : ℕ := ⌈M⌉₊ with hC
  set T : Set (Fin (d + 1) → ℤ) :=
    ((Fintype.piFinset fun _ : Fin (d + 1) => Finset.Icc (-(C : ℤ)) C : Finset (Fin (d + 1) → ℤ)) :
      Set (Fin (d + 1) → ℤ)) with hTdef
  set f : K → Fin (d + 1) → ℤ := fun x i => (minpoly ℤ x).coeff i with hfdef
  have hT : T.ncard = (2 * C + 1) ^ (d + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Int.card_Icc,
      Finset.card_univ, Fintype.card_fin]
    congr 1
    omega
  have hmaps : Set.MapsTo f {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R} T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := abs_coeff_minpoly_int_le K hx.1 hx.2 i
    have h2 : (|(minpoly ℤ x).coeff i| : ℝ) ≤ (C : ℝ) := h1.trans (Nat.le_ceil _)
    have h3 : |(minpoly ℤ x).coeff i| ≤ (C : ℤ) := by exact_mod_cast h2
    exact abs_le.mp h3
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps d
    (by
      intro t _
      by_cases h : ∃ x0 ∈ {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}, f x0 = t
      · obtain ⟨x0, hx0, hfx0⟩ := h
        refine ⟨(minpoly ℤ x0).map (algebraMap ℤ K), ((minpoly.monic hx0.1).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hx0.1).natDegree_map]
          exact natDegree_minpoly_int_le K hx0.1
        · intro y hy hfy
          have heq : minpoly ℤ y = minpoly ℤ x0 := by
            ext i
            by_cases hi : i < d + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_minpoly_int_le K hy.1).trans_lt
                (by omega)), coeff_eq_zero_of_natDegree_lt
                ((natDegree_minpoly_int_le K hx0.1).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval ℤ y
      · refine ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hfin, ?_⟩
  have hM0 : 0 ≤ M := by positivity
  have hC' : (C : ℝ) ≤ M + 1 := (Nat.ceil_lt_add_one hM0).le
  rw [hT] at hcard
  calc (({x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ R}.ncard : ℕ) : ℝ)
      ≤ ((d * (2 * C + 1) ^ (d + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (d : ℝ) * (2 * (C : ℝ) + 1) ^ (d + 1) := by push_cast; ring
    _ ≤ (d : ℝ) * (2 * M + 3) ^ (d + 1) := by
      have h23 : 2 * (C : ℝ) + 1 ≤ 2 * M + 3 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h23 _) (by positivity)
end GlobalTheory.MinpolyHeightCount

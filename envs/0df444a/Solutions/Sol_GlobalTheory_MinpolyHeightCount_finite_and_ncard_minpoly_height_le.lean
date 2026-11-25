-- Prove2me | solution 1 for GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:34:15.913539+00:00
-- url     : https://prove2.me/submissions/c0512cb8-3990-4ab4-a788-8ef956e9eea1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_le_of_fibres_roots
import Theorems.Thm_P2M_GlobalTheory_MinpolyHeightCount_exists_ncard_mulHeight__le_8108ec29db74

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
namespace GlobalTheory.MinpolyHeightCount
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B →
      {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧
      (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤
        C * B ^ k := by
  intro F E _ _ _ _ _
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨C₁, k₁, h₁⟩ := exists_ncard_mulHeight₁_le F
  set m := Module.finrank F E with hm
  refine ⟨m * C₁ ^ (m + 1), k₁ * (m + 1), fun B hB => ?_⟩
  obtain ⟨hSfin, hScard⟩ := h₁ B hB
  set S := {c : F | Height.mulHeight₁ c ≤ B} with hSdef
  set X := {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B} with hXdef
  set T : Set (Fin (m + 1) → F) :=
    ((Fintype.piFinset fun _ : Fin (m + 1) => hSfin.toFinset : Finset (Fin (m + 1) → F)) :
      Set (Fin (m + 1) → F)) with hTdef
  set f : E → Fin (m + 1) → F := fun x j => (minpoly F x).coeff j with hfdef
  have hT : T.ncard = S.ncard ^ (m + 1) := by
    rw [hTdef, Set.ncard_coe_finset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Set.ncard_eq_toFinset_card _ hSfin]
  have hmaps : Set.MapsTo f X T := by
    intro x hx
    rw [hTdef, Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Set.Finite.mem_toFinset]
    exact hx j
  obtain ⟨hXfin, hXcard⟩ := finite_and_ncard_le_of_fibres_roots (Finset.finite_toSet _) hmaps m
    (by
      intro t _
      by_cases h : ∃ x0 ∈ X, f x0 = t
      · obtain ⟨x0, -, hfx0⟩ := h
        have hi0 : IsIntegral F x0 := Algebra.IsIntegral.isIntegral x0
        refine ⟨(minpoly F x0).map (algebraMap F E), ((minpoly.monic hi0).map _).ne_zero, ?_, ?_⟩
        · rw [(minpoly.monic hi0).natDegree_map]; exact minpoly.natDegree_le x0
        · intro y _ hfy
          have heq : minpoly F y = minpoly F x0 := by
            ext i
            by_cases hi : i < m + 1
            · exact congrFun (hfy.trans hfx0.symm) ⟨i, hi⟩
            · rw [coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le y).trans_lt (by omega)),
                coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le x0).trans_lt (by omega))]
          rw [eval_map_algebraMap, ← heq]
          exact minpoly.aeval F y
      · exact ⟨1, one_ne_zero, by simp, fun x hx hfx => (h ⟨x, hx, hfx⟩).elim⟩)
  refine ⟨hXfin, ?_⟩
  rw [hT] at hXcard
  have h0 : (0 : ℝ) ≤ (S.ncard : ℝ) := Nat.cast_nonneg _
  calc ((X.ncard : ℕ) : ℝ) ≤ ((m * S.ncard ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast hXcard
    _ = (m : ℝ) * (S.ncard : ℝ) ^ (m + 1) := by push_cast; ring
    _ ≤ (m : ℝ) * (C₁ * B ^ k₁) ^ (m + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hScard _) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring
end GlobalTheory.MinpolyHeightCount

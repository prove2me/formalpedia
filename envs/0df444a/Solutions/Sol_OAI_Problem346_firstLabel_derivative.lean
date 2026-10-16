-- Prove2me | solution 1 for OAI.Problem346.firstLabel_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:57:08.5765+00:00
-- url     : https://prove2.me/submissions/9b8bcaae-0a02-4bd8-996a-551ecc777b27

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/TransferDerivative.lean:L89-L115
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.firstLabel_derivative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Theorems.Thm_OAI_Problem346_firstLabel_step
import Theorems.Thm_OAI_Problem346_flattened_derivative_eq_card_smul

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FirstCounts ----
namespace OAI

open scoped BigOperators

namespace Problem346

theorem firstLabel_zero_eq_t_iff (r m k : ℕ) (hk : k ≤ m) (j : Fin (r + m)) :
    firstLabel r m k (0, j) = some none ↔ k ≤ j.val := by
  simp only [firstLabel_zero]
  split <;> simp_all
  omega

 theorem firstLabelCount_t (r m k : ℕ) (hk : k ≤ m) :
    firstLabelCount r m k (some none) = r + m - k := by
  classical
  rw [firstLabelCount, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hrow : (∑ j : Fin (r + m),
      if Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j =
        (some none : FirstBlock m) then 1 else 0) = 0 := by
    rw [Fin.sum_univ_add]
    simp
  simp only [firstLabel_succ, hrow, Finset.sum_const_zero, add_zero,
    firstLabel_zero_eq_t_iff r m k hk]
  rw [← Finset.card_filter]
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (r + m)))) (fun j => j.val < k)
  rw [Fin.card_filter_val_lt, Nat.min_eq_right (by omega)] at hc
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- The sum-of-indicators count agrees with the cardinality used by polynomial
block-degree statements. -/
theorem firstLabel_card (r m k : ℕ) (c : FirstBlock m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = c)).card =
      firstLabelCount r m k c := by
  classical
  exact Finset.card_filter _ _

theorem firstLabel_card_t (r m k : ℕ) (hk : k ≤ m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = some none)).card = r + m - k := by
  rw [firstLabel_card, firstLabelCount_t r m k hk]

/-- Only unreplaced positions of the distinguished row carry the source label. -/
theorem firstLabel_eq_t_iff (r m k : ℕ) (hk : k ≤ m)
    (p : Fin (r + 1) × Fin (r + m)) :
    firstLabel r m k p = some none ↔ p.1 = 0 ∧ k ≤ p.2.val := by
  rcases p with ⟨i, j⟩
  by_cases hi : i = 0
  · subst i
    simpa using firstLabel_zero_eq_t_iff r m k hk j
  · simp only [firstLabel, hi, ite_false, false_and, iff_false]
    refine Fin.addCases (fun x => ?_) (fun y => ?_) j <;> simp

end Problem346

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.TransferDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- The concrete one-step identity in the first transfer. The source is the
`t` block; its remaining occurrences all lie in the distinguished row. -/
theorem firstLabel_derivative
    (r m k : ℕ) (hk : k < m) (V K : Type*)
    [AddCommGroup V] [Module ℂ V] [Fintype K]
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : K → V)
    (D : Derivation ℂ (MvPolynomial (FirstBlock m × K) ℂ)
      (MvPolynomial (FirstBlock m × K) ℂ))
    (hD : ∀ q j, D (MvPolynomial.X (q,j)) =
      if q = some none then MvPolynomial.X (some (some ⟨k,hk⟩),j) else 0) :
    D (multilinearPolynomial (flattenedForm T) e
        (firstLabel r m k)) =
      ((r+m-k : ℕ) : ℂ) •
        multilinearPolynomial (flattenedForm T) e
          (firstLabel r m (k+1)) := by
  classical
  have hj : firstLabel r m k
      (0, ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩) = some none := by
    simp [firstLabel]
  have hrow : ∀ p, firstLabel r m k p = some none → p.1 = 0 := by
    intro p hp
    exact ((firstLabel_eq_t_iff r m k (Nat.le_of_lt hk) p).mp hp).1
  have h := flattened_derivative_eq_card_smul (r+1) (r+m) V K (FirstBlock m)
    T e (firstLabel r m k) (some none) (some (some ⟨k,hk⟩))
    0 ⟨k, Nat.lt_of_lt_of_le hk (Nat.le_add_left m r)⟩ hj hrow D hD
  rw [firstLabel_card_t r m k (Nat.le_of_lt hk), ← firstLabel_step r m k hk] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.firstLabel_derivative := @_root_.OAI.Problem346.firstLabel_derivative

-- Prove2me | solution 1 for OAI.Problem346.firstPolynomial_zero_of_final
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:59:59.456399+00:00
-- url     : https://prove2.me/submissions/850a7fec-f653-43a1-9588-ace1d3a499f1

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FirstTransfer.lean:L37-L54
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.firstPolynomial_zero_of_final. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Theorems.Thm_OAI_Problem346_PolynomialShift_eq_zero_of_shift_eq_zero
import Theorems.Thm_OAI_Problem346_firstLabel_derivative

-- ---- from OAI.RepresentationTheory.FoulkesHowe.EncodingHomogeneous ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.EncodingDegree

variable {R : Type*} [CommSemiring R]
variable {S K B : Type*} [Fintype S] [DecidableEq S] [Fintype K]

/-- A coefficient expansion has weighted degree given by the sum of the weights
of its assigned vector blocks. The coefficients can be arbitrary. -/
theorem weightedHomogeneous_expansion (c : (S → K) → R) (blocks : S → B)
    (w : B → ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun x : B × K => w x.1)
      (∑ k : S → K, MvPolynomial.C (c k) *
        ∏ i : S, MvPolynomial.X (blocks i, k i))
      (∑ i : S, w (blocks i)) := by
  classical
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro i _
  exact MvPolynomial.isWeightedHomogeneous_X _ _ _

/-- The degree in one block is exactly the number of occurrences of that block. -/
theorem blockHomogeneous_expansion [DecidableEq B]
    (c : (S → K) → R) (blocks : S → B) (b : B) :
    MvPolynomial.IsWeightedHomogeneous
      (fun x : B × K => if x.1 = b then 1 else 0)
      (∑ k : S → K, MvPolynomial.C (c k) *
        ∏ i : S, MvPolynomial.X (blocks i, k i))
      (Finset.univ.filter (fun i => blocks i = b)).card := by
  simpa only [Finset.sum_boole, Nat.cast_id] using
    (weightedHomogeneous_expansion c blocks (fun x => if x = b then 1 else 0))

end Problem346.EncodingDegree

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FirstPolynomial ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- Direct block degrees of every intermediate polynomial, by counting its labels. -/
theorem firstPolynomial_blockHomogeneous {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (k : ℕ) (u : FirstBlock m) :
    PolynomialWeights.IsBlockHomogeneous u (firstPolynomial T e k)
      (Finset.univ.filter (fun p => firstLabel r m k p = u)).card := by
  classical
  let : DecidableEq (Fin (r+1) × Fin (r+m)) := Classical.decEq _
  unfold PolynomialWeights.IsBlockHomogeneous PolynomialWeights.blockWeight
  simpa only [firstPolynomial, multilinearPolynomial] using
    (EncodingDegree.blockHomogeneous_expansion
      (fun z => flattenedForm T (fun p => e (z p))) (firstLabel r m k) u)

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.BackwardCancellation ----
namespace OAI

namespace Problem346

/-- A finite sequence of zero-reflecting transitions can be cancelled backwards. -/
theorem eq_zero_of_backward_chain {M : Type*} [Zero M]
    (P : ℕ → M) (m : ℕ)
    (hstep : ∀ k < m, P (k+1) = 0 → P k = 0)
    (hm : P m = 0) : P 0 = 0 := by
  exact Nat.decreasingInduction (motive := fun k _ => P k = 0)
    (fun k hk => hstep k (by omega)) hm (Nat.zero_le m)

end Problem346

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FirstCounts ----
namespace OAI

open scoped BigOperators

namespace Problem346

theorem firstLabel_zero_eq_t_iff (r m k : ℕ) (hk : k ≤ m) (j : Fin (r + m)) :
    firstLabel r m k (0, j) = some none ↔ k ≤ j.val := by
  simp only [firstLabel_zero]
  split <;> simp_all
  omega

theorem firstLabel_zero_eq_y_iff (r m k : ℕ) (_hk : k ≤ m)
    (j : Fin (r + m)) (y : Fin m) :
    firstLabel r m k (0, j) = some (some y) ↔ j.val = y.val ∧ y.val < k := by
  simp only [firstLabel_zero]
  split
  · simp only [Option.some.injEq, Fin.ext_iff]
    rename_i h
    constructor
    · intro h'
      exact ⟨h', h' ▸ h.1⟩
    · exact fun h' => h'.1
  · rename_i h
    simp only [Option.some.injEq, reduceCtorEq, false_iff]
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

theorem firstLabelCount_y (r m k : ℕ) (hk : k ≤ m) (y : Fin m) :
    firstLabelCount r m k (some (some y)) = r + if y.val < k then 1 else 0 := by
  classical
  rw [firstLabelCount, Fintype.sum_prod_type, Fin.sum_univ_succ]
  have hrow : (∑ j : Fin (r + m),
      if Fin.addCases (fun _ : Fin r => none) (fun j : Fin m => some (some j)) j =
        (some (some y) : FirstBlock m) then 1 else 0) = 1 := by
    rw [Fin.sum_univ_add]
    simp
  simp only [firstLabel_succ, hrow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  let y' : Fin (r + m) := ⟨y.val, by omega⟩
  have hj : ∀ j : Fin (r + m), j.val = y.val ↔ j = y' := by
    intro j
    change j.val = y'.val ↔ j = y'
    exact Fin.ext_iff.symm
  simp only [firstLabel_zero_eq_y_iff r m k hk, hj]
  by_cases hy : y.val < k <;> simp [hy, add_comm]

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

theorem firstLabel_card_y (r m k : ℕ) (hk : k ≤ m) (y : Fin m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = some (some y))).card =
      r + if y.val < k then 1 else 0 := by
  rw [firstLabel_card, firstLabelCount_y r m k hk]

theorem firstLabel_card_y_next (r m k : ℕ) (hk : k < m) :
    (Finset.univ.filter (fun p => firstLabel r m k p = some (some ⟨k, hk⟩))).card = r := by
  rw [firstLabel_card_y r m k (Nat.le_of_lt hk)]
  simp

end Problem346

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.FirstTransfer ----
namespace OAI

noncomputable section

namespace Problem346

universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- Cancel the first transfer sequence from its zero endpoint. The homogeneous
and derivative identities are kept separate from this zero-reflection argument. -/
theorem firstPolynomial_zero_of_chain {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (ht : ∀ k < m, PolynomialWeights.IsBlockHomogeneous (some none)
      (firstPolynomial T e k) (r+m-k))
    (hy : ∀ (k : ℕ) (hk : k < m), PolynomialWeights.IsBlockHomogeneous
      (some (some (⟨k,hk⟩ : Fin m))) (firstPolynomial T e k) r)
    (hD : ∀ (k : ℕ) (hk : k < m),
      PolynomialShift.shift (some none) (some (some (⟨k,hk⟩ : Fin m)))
        (firstPolynomial T e k) = ((r+m-k : ℕ) : ℂ) • firstPolynomial T e (k+1))
    (hm : firstPolynomial T e m = 0) : firstPolynomial T e 0 = 0 := by
  classical
  apply eq_zero_of_backward_chain (firstPolynomial T e) m _ hm
  intro k hk hz
  apply PolynomialShift.eq_zero_of_shift_eq_zero
    (some none) (some (some (⟨k,hk⟩ : Fin m))) (by simp)
    (show r < r+m-k by omega) (ht k hk) (hy k hk)
  rw [hD k hk, hz, smul_zero]

/-- Every terminal-zero polynomial in the concrete first-transfer family is zero
at the initial stage. All degree counts and derivative identities are discharged. -/
theorem firstPolynomial_zero_of_final {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (hm : firstPolynomial T e m = 0) : firstPolynomial T e 0 = 0 := by
  classical
  apply firstPolynomial_zero_of_chain T e _ _ _ hm
  · intro k hk
    simpa only [firstLabel_card_t r m k (Nat.le_of_lt hk)] using
      firstPolynomial_blockHomogeneous T e k (some none)
  · intro k hk
    simpa only [firstLabel_card_y_next r m k hk] using
      firstPolynomial_blockHomogeneous T e k (some (some (⟨k,hk⟩ : Fin m)))
  · intro k hk
    simpa only [firstPolynomial, PolynomialShift.shift_apply] using
      (firstLabel_derivative r m k hk V κ T e
        (PolynomialShift.derivation (some none) (some (some (⟨k,hk⟩ : Fin m))))
        (fun q j => by simp))

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346


theorem solution.{u,v} : type_of% @_root_.OAI.Problem346.firstPolynomial_zero_of_final.{u,v} := @_root_.OAI.Problem346.firstPolynomial_zero_of_final.{u,v}

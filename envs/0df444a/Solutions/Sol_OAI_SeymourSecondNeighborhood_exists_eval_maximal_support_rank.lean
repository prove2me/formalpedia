-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.exists_eval_maximal_support_rank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:09:05.96431+00:00
-- url     : https://prove2.me/submissions/47d5d690-268b-4698-a2df-5f585ffbae69

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankFamily.lean:L45-L93
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.exists_eval_maximal_support_rank. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank
import Theorems.Thm_OAI_SeymourSecondNeighborhood_Bipartite_exists_vertexCover_card_eq_of_isMaximumMatching
import Theorems.Thm_OAI_SeymourSecondNeighborhood_rank_le_vertexCover_card

-- ---- from OAI.Combinatorics.SecondNeighborhood.Matching ----
namespace OAI

namespace SeymourSecondNeighborhood.Bipartite

variable {L R : Type*}

section DecidableEq

variable [DecidableEq L] [DecidableEq R]

end DecidableEq

section Finite

variable [Fintype L] [Fintype R]

theorem exists_maximum_matching (E : L → R → Prop) :
    ∃ M, IsMaximumMatching E M := by
  classical
  let candidates : Finset (Finset (L × R)) := Finset.univ.filter (IsMatching E)
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨M, hM, hmax⟩ := candidates.exists_max_image Finset.card hne
  refine ⟨M, (Finset.mem_filter.mp hM).2, ?_⟩
  intro N hN
  exact hmax N (by simp [candidates, hN])

end Finite

end SeymourSecondNeighborhood.Bipartite

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankMatching ----
namespace OAI

namespace SeymourSecondNeighborhood

open MvPolynomial

variable {R σ m n κ β : Type*}

theorem supportedVariableMatrix_submatrix [CommSemiring R]
    (support : m → n → Prop) (label : m → n → σ)
    (row : κ → m) (col : κ → n) :
    (supportedVariableMatrix (R := R) support label).submatrix row col =
      supportedVariableMatrix (R := R) (fun i j => support (row i) (col j))
        (fun i j => label (row i) (col j)) := by
  classical
  rfl

theorem exists_eval_supportedVariables_eq_one
    [Fintype κ] [DecidableEq κ] [CommSemiring R]
    (support : κ → κ → Prop) (label : κ → κ → σ)
    (hdiag : ∀ i, support i i)
    (hlabel : ∀ i j k l, support i j → support k l →
      label i j = label k l → i = k ∧ j = l) :
    ∃ v : σ → R, (MvPolynomial.eval v).mapMatrix
      (supportedVariableMatrix (R := R) support label) = 1 := by
  classical
  let v : σ → R := fun s => if ∃ k, label k k = s then 1 else 0
  refine ⟨v, ?_⟩
  ext i j
  change MvPolynomial.eval v
    (if support i j then X (label i j) else 0) = (1 : Matrix κ κ R) i j
  rw [Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    have hw : ∃ k, label k k = label i i := ⟨i, rfl⟩
    simp [hdiag i, v, hw]
  · by_cases hs : support i j
    · have hw : ¬ ∃ k, label k k = label i j := by
        rintro ⟨k, hk⟩
        obtain ⟨hki, hkj⟩ := hlabel k k i j (hdiag k) hs hk
        exact hij (hki.symm.trans hkj)
      simp [hs, hij, v, hw]
    · simp [hs, hij]

theorem det_supportedVariables_ne_zero
    [Fintype κ] [DecidableEq κ] [CommRing R] [Nontrivial R]
    (support : κ → κ → Prop) (label : κ → κ → σ)
    (hdiag : ∀ i, support i i)
    (hlabel : ∀ i j k l, support i j → support k l →
      label i j = label k l → i = k ∧ j = l) :
    (supportedVariableMatrix (R := R) support label).det ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_eval_supportedVariables_eq_one
    (R := R) support label hdiag hlabel
  intro hzero
  have h := congrArg Matrix.det hv
  rw [Matrix.det_one, ← RingHom.map_det, hzero, map_zero] at h
  exact zero_ne_one h

theorem det_matchingMinor_ne_zero
    [Fintype κ] [DecidableEq κ] [CommRing R] [Nontrivial R]
    (support : m → n → Prop) (label : m → n → σ)
    (row : κ → m) (col : κ → n)
    (hmatched : ∀ i, support (row i) (col i))
    (hlabel : ∀ i j k l, support (row i) (col j) → support (row k) (col l) →
      label (row i) (col j) = label (row k) (col l) → i = k ∧ j = l) :
    ((supportedVariableMatrix (R := R) support label).submatrix row col).det ≠ 0 := by
  rw [supportedVariableMatrix_submatrix]
  exact det_supportedVariables_ne_zero _ _ hmatched hlabel

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRank ----
namespace OAI

namespace SeymourSecondNeighborhood

open scoped BigOperators

section Evaluation

variable {σ ι K : Type*} [CommRing K] [IsDomain K] [Infinite K]

theorem exists_eval_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ a : σ → K, MvPolynomial.eval a p ≠ 0 := by
  classical
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro a
  have ha : MvPolynomial.eval a p = 0 := by
    by_contra ha
    exact h ⟨a, ha⟩
  simpa only [map_zero] using ha

theorem exists_eval_finset_ne_zero (s : Finset ι) (p : ι → MvPolynomial σ K)
    (hp : ∀ i ∈ s, p i ≠ 0) :
    ∃ a : σ → K, ∀ i ∈ s, MvPolynomial.eval a (p i) ≠ 0 := by
  classical
  have hprod : (∏ i ∈ s, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hprod
  refine ⟨a, ?_⟩
  have heval : (∏ i ∈ s, MvPolynomial.eval a (p i)) ≠ 0 := by
    simpa only [map_prod] using ha
  exact Finset.prod_ne_zero_iff.mp heval

theorem exists_eval_family_ne_zero [Fintype ι] (p : ι → MvPolynomial σ K)
    (hp : ∀ i, p i ≠ 0) :
    ∃ a : σ → K, ∀ i, MvPolynomial.eval a (p i) ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_eval_finset_ne_zero Finset.univ p (fun i _ => hp i)
  exact ⟨a, fun i => ha i (Finset.mem_univ i)⟩

end Evaluation

section Matrices

variable {σ K I J : Type*} [CommRing K]

end Matrices

section SimultaneousDeterminants

variable {σ κ K : Type*} [CommRing K] [IsDomain K] [Infinite K] [Fintype κ]
variable {I : κ → Type*} [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)]

end SimultaneousDeterminants

section SimultaneousRanks

variable {σ κ K : Type*} [Field K] [Infinite K] [Fintype κ]
variable {I J : κ → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]

end SimultaneousRanks

end SeymourSecondNeighborhood

end OAI

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankFamily ----
namespace OAI

namespace SeymourSecondNeighborhood

open Bipartite

theorem rank_le_card_of_maximum_matching
    {I J K : Type*} [Fintype I] [Fintype J] [Field K]
    {support : I → J → Prop} {matching : Finset (I × J)}
    (hmatching : IsMaximumMatching support matching) (D : Matrix I J K)
    (hD : ∀ i j, ¬ support i j → D i j = 0) : D.rank ≤ matching.card := by
  classical
  obtain ⟨rows, cols, hcover, hcard, _, _⟩ :=
    exists_vertexCover_card_eq_of_isMaximumMatching hmatching
  rw [← hcard]
  apply rank_le_vertexCover_card
  intro i j hij
  apply hcover i j
  by_contra hs
  exact hij (hD i j hs)

variable {σ κ τ K : Type*} [Field K] [Infinite K] [Fintype κ] [Fintype τ]
variable {I J : κ → Type*} [∀ k, Fintype (I k)] [∀ k, Fintype (J k)]

theorem exists_eval_maximal_support_rank
    (support : ∀ k, I k → J k → Prop) (label : ∀ k, I k → J k → σ)
    (hlabel : ∀ k i j i' j', support k i j → support k i' j' →
      label k i j = label k i' j' → i = i' ∧ j = j')
    (extra : τ → MvPolynomial σ K) (hextra : ∀ t, extra t ≠ 0) :
    ∃ a : σ → K, (∀ t, MvPolynomial.eval a (extra t) ≠ 0) ∧
      ∀ k (D : Matrix (I k) (J k) K),
        (∀ i j, ¬ support k i j → D i j = 0) →
        D.rank ≤ (evalPolynomialMatrix a
          (supportedVariableMatrix (R := K) (support k) (label k))).rank := by
  classical
  choose matching hmatching using fun k => exists_maximum_matching (support k)
  let row (k : κ) : ↥(matching k) → I k := fun e => e.1.1
  let col (k : κ) : ↥(matching k) → J k := fun e => e.1.2
  let matrix (k : κ) := supportedVariableMatrix (R := K) (support k) (label k)
  let minor (k : κ) := (matrix k).submatrix (row k) (col k)
  have hminor : ∀ k, (minor k).det ≠ 0 := by
    intro k
    apply det_matchingMinor_ne_zero
    · intro e
      exact (hmatching k).1.1 e.1 e.2
    · intro e f g h hef hgh heq
      obtain ⟨heg, hfh⟩ := hlabel k _ _ _ _ hef hgh heq
      exact ⟨Subtype.ext ((hmatching k).1.2.1 e.2 g.2 heg),
        Subtype.ext ((hmatching k).1.2.2 f.2 h.2 hfh)⟩
  let polynomials : Sum κ τ → MvPolynomial σ K :=
    Sum.elim (fun k => (minor k).det) extra
  have hpolynomials : ∀ t, polynomials t ≠ 0 := by
    intro t
    cases t with
    | inl k => exact hminor k
    | inr t => exact hextra t
  obtain ⟨a, ha⟩ := exists_eval_family_ne_zero polynomials hpolynomials
  refine ⟨a, fun t => ha (Sum.inr t), ?_⟩
  intro k D hD
  have hupper : D.rank ≤ (matching k).card :=
    rank_le_card_of_maximum_matching (hmatching k) D hD
  have hdet : ((evalPolynomialMatrix a (matrix k)).submatrix (row k) (col k)).det
      ≠ 0 := by
    rw [← evalPolynomialMatrix_submatrix, det_evalPolynomialMatrix]
    exact ha (Sum.inl k)
  have hlower : (matching k).card ≤ (evalPolynomialMatrix a (matrix k)).rank := by
    calc
      (matching k).card =
          ((evalPolynomialMatrix a (matrix k)).submatrix (row k) (col k)).rank := by
        simpa only [Fintype.card_coe] using (Matrix.rank_of_det_ne_zero hdet).symm
      _ ≤ (evalPolynomialMatrix a (matrix k)).rank :=
        Matrix.rank_submatrix_le _ (row k) (col k)
  exact hupper.trans hlower

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood
open Bipartite


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.exists_eval_maximal_support_rank := @_root_.OAI.SeymourSecondNeighborhood.exists_eval_maximal_support_rank

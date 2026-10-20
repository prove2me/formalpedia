-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.det_blockSupportedVariables_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:03:34.06762+00:00
-- url     : https://prove2.me/submissions/90a01a2e-e6a2-4122-b608-8ad6199561ff

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/GenericRankMatching.lean:L79-L109
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.det_blockSupportedVariables_ne_zero. The node keeps its source
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

-- ---- from OAI.Combinatorics.SecondNeighborhood.GenericRankMatching ----
namespace OAI

namespace SeymourSecondNeighborhood

open MvPolynomial

variable {R σ m n κ β : Type*}

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

theorem det_blockSupportedVariables_ne_zero
    [Fintype κ] [DecidableEq κ] [Fintype β] [LinearOrder β]
    [CommRing R] [IsDomain R]
    (support : κ → κ → Prop) (label : κ → κ → σ) (block : κ → β)
    (hdiag : ∀ i, support i i)
    (hblock : ∀ i j, support i j → block i = block j)
    (hlabel : ∀ i j k l, support i j → support k l → block i = block k →
      label i j = label k l → i = k ∧ j = l) :
    (supportedVariableMatrix (R := R) support label).det ≠ 0 := by
  classical
  let M := supportedVariableMatrix (R := R) support label
  have htri : M.BlockTriangular block := by
    intro i j hji
    have hs : ¬ support i j := by
      intro hs
      exact (ne_of_lt hji) (hblock i j hs).symm
    simp [M, supportedVariableMatrix, hs]
  change M.det ≠ 0
  rw [htri.det_fintype]
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  change (supportedVariableMatrix (R := R)
    (fun i j : { a // block a = b } => support i.val j.val)
    (fun i j : { a // block a = b } => label i.val j.val)).det ≠ 0
  apply det_supportedVariables_ne_zero
  · intro i
    exact hdiag i.val
  · intro i j k l hij hkl heq
    obtain ⟨hik, hjl⟩ := hlabel i.val j.val k.val l.val hij hkl
      (i.property.trans k.property.symm) heq
    exact ⟨Subtype.ext hik, Subtype.ext hjl⟩

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood
open MvPolynomial


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.det_blockSupportedVariables_ne_zero := @_root_.OAI.SeymourSecondNeighborhood.det_blockSupportedVariables_ne_zero

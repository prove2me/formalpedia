-- Prove2me | solution 1 for OAI.LeanBlast.GotsmanLinial.anticommutator_energy_ge_selected
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:16:05.348815+00:00
-- url     : https://prove2.me/submissions/af819b59-e91e-49ae-a3be-f9f4e2531276

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/EdgeRecovery.lean:L111-L152
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.GotsmanLinial.anticommutator_energy_ge_selected. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery

-- ---- from OAI.Combinatorics.GotsmanLinial.EdgeRecovery ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Recovering constant-sign edges from grading energy

The counting argument is separated from construction of the grading matrix.
Its hypotheses are explicit entrywise, total-energy, and distance-energy facts.
No edge-count or anticommutator conclusion is assumed.
-/

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- On an equal-sign pair the anticommutator has four times the squared entry
mass. The diagonal is included as an equal-sign pair. -/
theorem anticommutator_entry_sq_of_same_sign [DecidableEq ι]
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (i j : ι) (hij : h i = h j) :
    ‖(M * Matrix.diagonal (fun i => (h i : ℂ)) +
      Matrix.diagonal (fun i => (h i : ℂ)) * M) i j‖ ^ 2 =
      4 * ‖M i j‖ ^ 2 := by
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [← hij]
  have hfactor : M i j * (h i : ℂ) + (h i : ℂ) * M i j =
      (2 : ℂ) * (h i : ℂ) * M i j := by ring
  rw [hfactor]
  have hnorm : ‖(h i : ℂ)‖ = 1 := by
    rcases hh i with hi | hi <;> simp [hi]
  rw [norm_mul, norm_mul, hnorm]
  norm_num [mul_pow]

/-- The diagonal and a disjoint set of equal-sign neighbor entries contribute
four times their mass to the Hilbert--Schmidt squared norm. -/
theorem anticommutator_energy_ge_selected [DecidableEq ι]
    (ρ : ι → ι → ℕ) (hzero : ∀ i j, ρ i j = 0 → i = j)
    (M : Matrix ι ι ℂ) (h : ι → ℝ) (hh : ∀ i, h i = 1 ∨ h i = -1)
    (s : Finset (ι × ι))
    (hs : s ⊆ distanceShell (fun p : ι × ι => ρ p.1 p.2) 1)
    (hsign : ∀ p ∈ s, h p.1 = h p.2) :
    4 * ((∑ p ∈ distanceShell (fun p : ι × ι => ρ p.1 p.2) 0,
        ‖M p.1 p.2‖ ^ 2) + ∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) ≤
      hsNormSq (M * Matrix.diagonal (fun i => (h i : ℂ)) +
        Matrix.diagonal (fun i => (h i : ℂ)) * M) := by
  classical
  let D := distanceShell (fun p : ι × ι => ρ p.1 p.2) 0
  let T := M * Matrix.diagonal (fun i => (h i : ℂ)) +
    Matrix.diagonal (fun i => (h i : ℂ)) * M
  have hdisj : Disjoint D s := by
    apply Finset.disjoint_left.mpr
    intro p hpD hps
    have h0 : ρ p.1 p.2 = 0 := by simpa only [D, mem_distanceShell] using hpD
    have h1 : ρ p.1 p.2 = 1 := by simpa only [mem_distanceShell] using hs hps
    omega
  have hsame : ∀ p ∈ D ∪ s, h p.1 = h p.2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpD | hps
    · have h0 : ρ p.1 p.2 = 0 := by simpa only [D, mem_distanceShell] using hpD
      rw [hzero _ _ h0]
    · exact hsign p hps
  have hentries : (∑ p ∈ D ∪ s, 4 * ‖M p.1 p.2‖ ^ 2) =
      ∑ p ∈ D ∪ s, ‖T p.1 p.2‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact (anticommutator_entry_sq_of_same_sign M h hh p.1 p.2 (hsame p hp)).symm
  have hsubset : (∑ p ∈ D ∪ s, ‖T p.1 p.2‖ ^ 2) ≤
      ∑ p : ι × ι, ‖T p.1 p.2‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => sq_nonneg ‖T p.1 p.2‖)
  have hsplit : (∑ p ∈ D ∪ s, 4 * ‖M p.1 p.2‖ ^ 2) =
      4 * ((∑ p ∈ D, ‖M p.1 p.2‖ ^ 2) + ∑ p ∈ s, ‖M p.1 p.2‖ ^ 2) := by
    rw [Finset.sum_union hdisj, ← Finset.mul_sum, ← Finset.mul_sum, mul_add]
  rw [← hentries, hsplit] at hsubset
  simpa only [D, T, hsNormSq, Fintype.sum_prod_type] using hsubset

end LeanBlast.GotsmanLinial

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.GotsmanLinial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.GotsmanLinial.anticommutator_energy_ge_selected := @_root_.OAI.LeanBlast.GotsmanLinial.anticommutator_energy_ge_selected

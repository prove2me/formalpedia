-- Prove2me | solution 1 for OAI.GrahamSpherical.weighted_copy_derivation_energy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:17:53.168829+00:00
-- url     : https://prove2.me/submissions/8a9d4e62-25e6-4bc0-afe2-2cb0474224b5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/CopyInvariant.lean:L10-L34
-- (upload_full_project.md Phase 4): solution for node OAI.GrahamSpherical.weighted_copy_derivation_energy. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_GrahamSpherical
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_Model
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_MonochromaticObstruction
import Theorems.Thm_OAI_GrahamSpherical_affine_copy
import Theorems.Thm_OAI_GrahamSpherical_weighted_affine_derivation_energy

-- ---- from OAI.Combinatorics.SphericalRamsey.AffineCopy ----
namespace OAI

noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace GrahamSpherical

/-- Coordinate-square normalization for the derivative-energy calculation. -/
lemma sum_sq_eq_inner {n : ℕ} (A : Point n) :
    (∑ j : Fin n, A j ^ 2) = (inner ℝ (A) (A)) := by
  rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.CopyInvariant ----
namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace GrahamSpherical

/-- All distance-preserving copies, with no affine-form or dimension premise. -/
theorem weighted_copy_derivation_energy {n : ℕ}
    (D : Derivation ℤ ℝ ℝ)
    (hD : D parameter = (1 + parameter ^ 2) / 2)
    (f : witness → Point n) (hf : Isometry f) :
    ∑ i : Label, (weight i : ℝ) *
      derivationEnergy D (f ⟨vertex i, ⟨i, rfl⟩⟩) = 8 := by
  let y : Label → Point n := fun i => f ⟨vertex i, ⟨i, rfl⟩⟩
  have hy : ∀ i j, dist (y i) (y j) = dist (vertex i) (vertex j) := by
    intro i j
    exact hf.dist_eq ⟨vertex i, ⟨i, rfl⟩⟩ ⟨vertex j, ⟨j, rfl⟩⟩
  obtain ⟨z, A, B, hA, hB, _hAB, hform⟩ := affine_copy y hy
  have hAs : ∑ j : Fin n, A j ^ 2 = 1 := (sum_sq_eq_inner A).trans hA
  have hBs : ∑ j : Fin n, B j ^ 2 = 1 := (sum_sq_eq_inner B).trans hB
  have hpoint (i : Label) (j : Fin n) :
      y i j = z j + coordinates i 0 * A j + coordinates i 1 * B j := by
    have h := congrArg (fun x : Point n => x j) (hform i)
    simpa using h
  have henergy (i : Label) : derivationEnergy D (y i) =
      ∑ j : Fin n, (D (z j + coordinates i 0 * A j + coordinates i 1 * B j)) ^ 2 := by
    unfold derivationEnergy
    simp_rw [hpoint]
  change (∑ i : Label, (weight i : ℝ) * derivationEnergy D (y i)) = 8
  simp_rw [henergy]
  exact weighted_affine_derivation_energy D hD z A B hAs hBs

end GrahamSpherical

end

end OAI

-- ---- platform node ----
open OAI OAI.GrahamSpherical
open scoped BigOperators RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.GrahamSpherical.weighted_copy_derivation_energy := @_root_.OAI.GrahamSpherical.weighted_copy_derivation_energy

-- Prove2me | solution 1 for OAI.GrahamSpherical.rounding_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:13:45.339982+00:00
-- url     : https://prove2.me/submissions/588ef347-08af-41e6-9c33-6e7182778acb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/Coloring.lean:L17-L76
-- (upload_full_project.md Phase 4): solution for node OAI.GrahamSpherical.rounding_obstruction. The node keeps its source
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

-- ---- from OAI.Combinatorics.SphericalRamsey.Coloring ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace GrahamSpherical

/-- The actual fifty-residue rounding obstruction. No nonnegativity or
geometric surrogate is required of the twelve input energies. -/
theorem rounding_obstruction (e : (Fin 3 × Fin 4) → ℝ)
    (henergy : ∑ i, (if i.1 = 2 then (-2 : ℝ) else 1) * e i = 8) :
    ∃ i j, (Int.floor (3 * e i)) % 50 ≠ (Int.floor (3 * e j)) % 50 := by
  classical
  by_contra h
  push Not at h
  let f : (Fin 3 × Fin 4) → ℤ := fun i => Int.floor (3 * e i)
  have hr (i : Fin 3 × Fin 4) : f i % 50 = f (0, 0) % 50 := h i (0, 0)
  have heq (i : Fin 3 × Fin 4) : f i = 50 * (f i / 50) + f (0, 0) % 50 := by
    have hi := Int.emod_add_mul_ediv (f i) 50
    rw [hr i] at hi
    omega
  let S : ℤ := f (0, 0) + f (0, 1) + f (0, 2) + f (0, 3) + f (1, 0) + f (1, 1) + f (1, 2) + f (1, 3) - 2 * (f (2, 0) + f (2, 1) + f (2, 2) + f (2, 3))
  let q : (Fin 3 × Fin 4) → ℤ := fun i => f i / 50
  let Q : ℤ := q (0, 0) + q (0, 1) + q (0, 2) + q (0, 3) + q (1, 0) + q (1, 1) + q (1, 2) + q (1, 3) - 2 * (q (2, 0) + q (2, 1) + q (2, 2) + q (2, 3))
  have hdiv : S = 50 * Q := by
    conv_lhs =>
      dsimp [S]
      rw [heq (0, 0), heq (0, 1), heq (0, 2), heq (0, 3), heq (1, 0), heq (1, 1), heq (1, 2), heq (1, 3), heq (2, 0), heq (2, 1), heq (2, 2), heq (2, 3)]
    dsimp [Q, q]
    ring
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.ext_iff] at henergy
  simp only [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl] at henergy
  have hl00 : (f (0, 0) : ℝ) ≤ 3 * e (0, 0) := Int.floor_le _
  have hu00 : 3 * e (0, 0) < (f (0, 0) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl01 : (f (0, 1) : ℝ) ≤ 3 * e (0, 1) := Int.floor_le _
  have hu01 : 3 * e (0, 1) < (f (0, 1) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl02 : (f (0, 2) : ℝ) ≤ 3 * e (0, 2) := Int.floor_le _
  have hu02 : 3 * e (0, 2) < (f (0, 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl03 : (f (0, 3) : ℝ) ≤ 3 * e (0, 3) := Int.floor_le _
  have hu03 : 3 * e (0, 3) < (f (0, 3) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl10 : (f (1, 0) : ℝ) ≤ 3 * e (1, 0) := Int.floor_le _
  have hu10 : 3 * e (1, 0) < (f (1, 0) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl11 : (f (1, 1) : ℝ) ≤ 3 * e (1, 1) := Int.floor_le _
  have hu11 : 3 * e (1, 1) < (f (1, 1) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl12 : (f (1, 2) : ℝ) ≤ 3 * e (1, 2) := Int.floor_le _
  have hu12 : 3 * e (1, 2) < (f (1, 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl13 : (f (1, 3) : ℝ) ≤ 3 * e (1, 3) := Int.floor_le _
  have hu13 : 3 * e (1, 3) < (f (1, 3) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl20 : (f (2, 0) : ℝ) ≤ 3 * e (2, 0) := Int.floor_le _
  have hu20 : 3 * e (2, 0) < (f (2, 0) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl21 : (f (2, 1) : ℝ) ≤ 3 * e (2, 1) := Int.floor_le _
  have hu21 : 3 * e (2, 1) < (f (2, 1) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl22 : (f (2, 2) : ℝ) ≤ 3 * e (2, 2) := Int.floor_le _
  have hu22 : 3 * e (2, 2) < (f (2, 2) : ℝ) + 1 := Int.lt_floor_add_one _
  have hl23 : (f (2, 3) : ℝ) ≤ 3 * e (2, 3) := Int.floor_le _
  have hu23 : 3 * e (2, 3) < (f (2, 3) : ℝ) + 1 := Int.lt_floor_add_one _
  have hSl : (16 : ℝ) < (S : ℝ) := by
    dsimp [S]
    push_cast
    linarith
  have hSu : (S : ℝ) < (32 : ℝ) := by
    dsimp [S]
    push_cast
    linarith
  have hSl' : (16 : ℤ) < S := by exact_mod_cast hSl
  have hSu' : S < (32 : ℤ) := by exact_mod_cast hSu
  omega

end GrahamSpherical

end

end OAI

-- ---- platform node ----
open OAI OAI.GrahamSpherical
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.GrahamSpherical.rounding_obstruction := @_root_.OAI.GrahamSpherical.rounding_obstruction

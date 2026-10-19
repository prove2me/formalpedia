-- Prove2me | solution 1 for OAI.GrahamSpherical.derivation_rotation_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:14:31.400922+00:00
-- url     : https://prove2.me/submissions/4739677f-bd17-45cd-a21b-828f7cdc29b9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/DerivationCoordinates.lean:L11-L30
-- (upload_full_project.md Phase 4): solution for node OAI.GrahamSpherical.derivation_rotation_coordinates. The node keeps its source
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

-- ---- from OAI.Combinatorics.SphericalRamsey.DerivationCoordinates ----
namespace OAI

namespace GrahamSpherical

/-- Only the algebraic quotient rule is used; no continuity or differentiation
of the infinite series defining the parameter is involved. -/
theorem derivation_rotation_coordinates (D : Derivation ℤ ℝ ℝ) (t : ℝ)
    (ht : D t = (1 + t ^ 2) / 2) :
    D ((1 - t ^ 2) / (1 + t ^ 2)) = -(2 * t / (1 + t ^ 2)) ∧
      D (2 * t / (1 + t ^ 2)) = (1 - t ^ 2) / (1 + t ^ 2) := by
  have hden : (1 + t ^ 2 : ℝ) ≠ 0 := by positivity
  have htwo : D (2 : ℝ) = 0 := D.map_natCast 2
  have hpow : D (t ^ 2) = 2 * t * D t := by
    simp [Derivation.leibniz_pow, smul_eq_mul, two_smul]
    ring
  constructor
  · rw [D.leibniz_div, map_sub, map_add, D.map_one_eq_zero, hpow, ht]
    simp only [smul_eq_mul]
    field_simp [hden]
    ring
  · rw [D.leibniz_div, D.leibniz, map_add, D.map_one_eq_zero, htwo, hpow, ht]
    simp only [smul_eq_mul]
    field_simp [hden]
    ring

end GrahamSpherical

end OAI

-- ---- platform node ----
open OAI OAI.GrahamSpherical


theorem solution : type_of% @_root_.OAI.GrahamSpherical.derivation_rotation_coordinates := @_root_.OAI.GrahamSpherical.derivation_rotation_coordinates

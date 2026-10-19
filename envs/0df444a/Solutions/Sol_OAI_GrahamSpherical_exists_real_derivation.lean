-- Prove2me | solution 1 for OAI.GrahamSpherical.exists_real_derivation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T10:20:51.775352+00:00
-- url     : https://prove2.me/submissions/83df6ba8-9da5-4e74-b71e-bf76bb297cd3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SphericalRamsey/RealDerivation.lean:L10-L30
-- (upload_full_project.md Phase 4): solution for node OAI.GrahamSpherical.exists_real_derivation. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_BasisDerivation
import Definitions.Def_OAI_Combinatorics_SphericalRamsey_AlgebraicExtension
import Theorems.Thm_OAI_GrahamSpherical_exists_derivation_adjoin_coordinate

-- ---- from OAI.Combinatorics.SphericalRamsey.RealTranscendenceBasis ----
namespace OAI

noncomputable section
namespace GrahamSpherical

/-- The designated transcendental real is retained in the actual maximal
algebraically independent subset of the real field. -/
theorem exists_real_transcendenceBasis_containing (a : ℝ)
    (ha : Transcendental ℚ a) :
    ∃ B : Set ℝ, a ∈ B ∧ IsTranscendenceBasis ℚ (fun b : B => (b : ℝ)) := by
  have hs : AlgebraicIndepOn ℚ id ({a} : Set ℝ) := by
    exact (algebraicIndependent_singleton_iff
      (R := ℚ) (x := fun b : ({a} : Set ℝ) => (b : ℝ)) ⟨a, by simp⟩).2 ha
  obtain ⟨B, hsub, hB⟩ := exists_isTranscendenceBasis_superset hs
  exact ⟨B, hsub (by simp), hB⟩

end GrahamSpherical

end

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.AlgebraicExtension ----
namespace OAI

namespace GrahamSpherical.AlgebraicExtension

open IntermediateField
open scoped Differential

variable {F K : Type*} [Field F] [Field K] [CharZero F]
  [Algebra F K] [Algebra.IsAlgebraic F K] [Differential F]

attribute [local instance] OAI.GrahamSpherical.AlgebraicExtension.finiteSimple
theorem value_algebraMap (x : F) :
    value (F := F) (algebraMap F K x) = algebraMap F K (Differential.deriv x) := by
  let L : IntermediateField F K := F⟮algebraMap F K x⟯
  rw [value_eq L _ (L.algebraMap_mem x)]
  change ((Differential.deriv (algebraMap F L x) : L) : K) = _
  rw [deriv_algebraMap]
  rfl

omit [Differential F] in
/-- Explicit derivation interface, avoiding any preexisting derivative on the target. -/
theorem exists_extension (D : Derivation ℤ F F) :
    ∃ E : Derivation ℤ K K,
      ∀ x : F, E (algebraMap F K x) = algebraMap F K (D x) := by
  let : Differential F := ⟨D⟩
  exact ⟨(differentialAlgebraic (F := F) (K := K)).deriv, value_algebraMap⟩

end GrahamSpherical.AlgebraicExtension

end OAI

-- ---- from OAI.Combinatorics.SphericalRamsey.RealDerivation ----
namespace OAI

noncomputable section
namespace GrahamSpherical

/-- Prescribe a derivation at any transcendental real, with an arbitrary real
value. The final scalar need not belong to the rational-function subfield. -/
theorem exists_real_derivation (a c : ℝ) (ha : Transcendental ℚ a) :
    ∃ D : Derivation ℤ ℝ ℝ, D a = c := by
  classical
  obtain ⟨B, haB, hB⟩ := exists_real_transcendenceBasis_containing a ha
  let b : B → ℝ := fun x => (x : ℝ)
  let i : B := ⟨a, haB⟩
  let F := IntermediateField.adjoin ℚ (Set.range b)
  let : Algebra.IsAlgebraic F ℝ := hB.isAlgebraic_field
  obtain ⟨δ, hδ⟩ := exists_derivation_adjoin_coordinate b hB.1 i
  obtain ⟨D, hD⟩ := AlgebraicExtension.exists_extension (K := ℝ) δ
  let x : F := ⟨b i, IntermediateField.subset_adjoin ℚ (Set.range b) ⟨i, rfl⟩⟩
  have hδx : δ x = 1 := by
    exact hδ
  have hDa : D a = 1 := by
    have h := hD x
    rw [hδx, map_one] at h
    exact h
  refine ⟨c • D, ?_⟩
  simp [Derivation.smul_apply, hDa]

end GrahamSpherical

end

end OAI

-- ---- platform node ----
open OAI OAI.GrahamSpherical


theorem solution : type_of% @_root_.OAI.GrahamSpherical.exists_real_derivation := @_root_.OAI.GrahamSpherical.exists_real_derivation

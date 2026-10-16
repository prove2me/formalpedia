-- Prove2me | solution 1 for OAI.DiagonalForms.System.comparison_harmonic_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:09:29.166979+00:00
-- url     : https://prove2.me/submissions/346c9c6e-f6e4-47d9-9f4b-83c9b910d74d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiagonalForms.lean:L537-L552
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalForms.System.comparison_harmonic_sum_nonneg. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Theorems.Thm_OAI_DiagonalForms_System_comparison_parallel

-- ---- from OAI.Analysis.DiagonalForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
end DiagonalForms.System

namespace QuantumCalculus
end QuantumCalculus

namespace DiagonalForms.System
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

end DiagonalForms.System

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace DiagonalForms

namespace System

variable {P I J : Type*} (D : System P I J)

theorem comparison_smul {w : P → ℝ} (hw : D.Comparison w) {a : ℝ} (ha : 0 ≤ a) :
    D.Comparison (fun p => a * w p) := by
  intro z s
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [sourceForm, mul_assoc, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hw z s) ha

theorem comparison_zero : D.Comparison (fun _ => 0) := by
  intro z s
  simp [sourceForm]

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem parallel_inv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    parallel x⁻¹ y⁻¹ = (x + y)⁻¹ := by
  unfold parallel
  field_simp
  ring

theorem comparison_harmonic_sum_pos {K : Type*} (s : Finset K) (hs : s.Nonempty)
    {w : K → P → ℝ} {c : K → ℝ}
    (hc : ∀ k ∈ s, 0 < c k) (hwp : ∀ k ∈ s, ∀ p, 0 < w k p)
    (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => (∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert k s hk ih =>
    have hkpos := hc k (Finset.mem_insert_self k s)
    have hkw := hwp k (Finset.mem_insert_self k s)
    have hkc := hw k (Finset.mem_insert_self k s)
    have hcomp : D.Comparison (fun p => (c k / w k p)⁻¹) := by
      simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm] using
        D.comparison_smul hkc (le_of_lt (inv_pos.mpr hkpos))
    by_cases he : s.Nonempty
    · have hcs : ∀ j ∈ s, 0 < c j := fun j hj => hc j (Finset.mem_insert_of_mem hj)
      have hws : ∀ j ∈ s, ∀ p, 0 < w j p := fun j hj => hwp j (Finset.mem_insert_of_mem hj)
      have hcps : ∀ j ∈ s, D.Comparison (w j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
      have hsum (p : P) : 0 < ∑ j ∈ s, c j / w j p :=
        Finset.sum_pos (fun j hj => div_pos (hcs j hj) (hws j hj p)) he
      have hh := D.comparison_parallel hcomp (ih he hcs hws hcps)
        (fun p => inv_pos.mpr (div_pos hkpos (hkw p)))
        (fun p => inv_pos.mpr (hsum p))
      simpa only [Finset.sum_insert hk, parallel_inv (div_pos hkpos (hkw _)) (hsum _)] using hh
    · have hem : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simpa [hem] using hcomp

theorem comparison_harmonic_sum {K : Type*} (s : Finset K)
    {w : K → P → ℝ} {c : K → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (hex : ∃ k ∈ s, 0 < c k)
    (hwp : ∀ k ∈ s, ∀ p, 0 < w k p) (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => (∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  let t := s.filter (fun k => 0 < c k)
  have ht : t.Nonempty := by
    obtain ⟨k, hk, hck⟩ := hex
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hck⟩⟩
  have he (p : P) : (∑ k ∈ t, c k / w k p) = ∑ k ∈ s, c k / w k p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkt
    have hck : c k = 0 := by
      have : ¬ 0 < c k := fun h => hkt (Finset.mem_filter.mpr ⟨hk, h⟩)
      exact le_antisymm (le_of_not_gt this) (hc k hk)
    simp [hck]
  have hh := D.comparison_harmonic_sum_pos t ht
    (fun k hk => (Finset.mem_filter.mp hk).2)
    (fun k hk => hwp k (Finset.mem_filter.mp hk).1)
    (fun k hk => hw k (Finset.mem_filter.mp hk).1)
  simpa only [he] using hh

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem comparison_harmonic_sum_nonneg {K : Type*} (s : Finset K)
    {w : K → P → ℝ} {c : K → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (hwp : ∀ k ∈ s, ∀ p, 0 < w k p)
    (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => (∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  by_cases h : ∃ k ∈ s, 0 < c k
  · exact D.comparison_harmonic_sum s hc h hwp hw
  · have hz : ∀ k ∈ s, c k = 0 := by
      intro k hk
      exact le_antisymm (le_of_not_gt (fun hh => h ⟨k, hk, hh⟩)) (hc k hk)
    have he (p : P) : ∑ k ∈ s, c k / w k p = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [hz k hk]
    simpa only [he, inv_zero] using D.comparison_zero

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

end DiagonalForms.System

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalForms OAI.DiagonalForms.System
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open MeasureTheory


theorem solution : type_of% @_root_.OAI.DiagonalForms.System.comparison_harmonic_sum_nonneg := @_root_.OAI.DiagonalForms.System.comparison_harmonic_sum_nonneg

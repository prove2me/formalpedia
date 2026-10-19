-- Prove2me | solution 2 for OAI.Problem356.Splitting.not_preserving_of_countable_compression
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:16:21.943726+00:00
-- url     : https://prove2.me/submissions/11bca0dc-d277-48d0-bd0d-79102bda1003

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/Splitting.lean:L42-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Splitting.not_preserving_of_countable_compression. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment

-- ---- from OAI.Analysis.CoulombTransport.Splitting ----
namespace OAI

universe uAlpha uIndex

/-!
# The deterministic-selection mass obstruction

A preserving map cannot carry a positive-mass selection set into a target
whose prescribed mass is a strictly smaller multiple of the same reference
mass.  This is the measure-theoretic obstruction in the Coulomb construction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.Splitting

variable {α : Type uAlpha} {ι : Type uIndex} [MeasurableSpace α]

/-- Preservation and a strict compression of the reference mass force the
selected set to have reference measure zero. -/
theorem reference_mass_zero_of_compression
    {μ ν : Measure α} {T : α → α} {S A : Set α} {c d : ℝ≥0∞}
    (hT : Measurable T) (hpres : Measure.map T μ = μ)
    (hA : MeasurableSet A) (hsub : S ⊆ T ⁻¹' A)
    (hsource : μ S = c * ν S) (htarget : μ A = d * ν S)
    (hdc : d < c) (hfinite : ν S ≠ ⊤) : ν S = 0 := by
  by_contra hne
  have hle : c * ν S ≤ d * ν S := calc
    c * ν S = μ S := hsource.symm
    _ ≤ μ (T ⁻¹' A) := measure_mono hsub
    _ = (Measure.map T μ) A := (Measure.map_apply hT hA).symm
    _ = μ A := by rw [hpres]
    _ = d * ν S := htarget
  exact (not_lt_of_ge hle)
    ((ENNReal.mul_lt_mul_iff_left hne hfinite).2 hdc)

/-- No preserving map can implement a countable almost-everywhere selection
whose source and target masses have a uniformly strict reversed ratio. -/
theorem not_preserving_of_countable_compression [Countable ι]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    {T : α → α} {S A : ι → Set α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0)
    (hA : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, S i ⊆ T ⁻¹' A i)
    (hsource : ∀ i, μ (S i) = c * ν (S i))
    (htarget : ∀ i, μ (A i) = d * ν (S i))
    (hdc : d < c)
    (hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i) :
    ¬ (Measurable T ∧ Measure.map T μ = μ) := by
  rintro ⟨hT, hpres⟩
  have hzero : ∀ i, ν (S i) = 0 := fun i =>
    reference_mass_zero_of_compression hT hpres (hA i) (hsub i)
      (hsource i) (htarget i) hdc (measure_ne_top ν (S i))
  have hnull : ν (⋃ i, S i) = 0 := measure_iUnion_null hzero
  have hfull : (⋃ i, S i) =ᵐ[ν] Set.univ := by
    filter_upwards [hcover] with x hx
    apply propext
    change x ∈ ⋃ i, S i ↔ x ∈ Set.univ
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hx
  exact hν ((measure_congr hfull).symm.trans hnull)

end Problem356.Splitting

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Splitting
open MeasureTheory
open scoped ENNReal


theorem solution.{uAlpha,uIndex} : type_of% @_root_.OAI.Problem356.Splitting.not_preserving_of_countable_compression.{uAlpha,uIndex} := @_root_.OAI.Problem356.Splitting.not_preserving_of_countable_compression.{uAlpha,uIndex}

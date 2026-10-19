-- Prove2me | solution 2 for OAI.Problem356.Splitting.no_preserving_branch_selection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:17:47.722652+00:00
-- url     : https://prove2.me/submissions/e11099ab-0253-43f9-a4eb-a99832d74617

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/Splitting.lean:L68-L100
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.Splitting.no_preserving_branch_selection. The node keeps its source
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
import Theorems.Thm_OAI_Problem356_Splitting_not_preserving_of_countable_compression

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

/-- The branch-selection formulation. The hypotheses about selected-set
masses are exactly those supplied by disjoint weighted pushforward
components. No regularity beyond measurability is imposed on the selector. -/
theorem no_preserving_branch_selection [Countable ι] [MeasurableEq α]
    {μ ν : Measure α} [IsFiniteMeasure ν] {B : Set α}
    {H : ι → α → α} {c d : ℝ≥0∞}
    (hν : ν Set.univ ≠ 0) (hB : MeasurableSet B)
    (hfull : ∀ᵐ x ∂ν, x ∈ B)
    (hH : ∀ i, Measurable (H i))
    (himage : ∀ i S, MeasurableSet S → S ⊆ B →
      MeasurableSet (H i '' S))
    (hsource : ∀ S, MeasurableSet S → S ⊆ B → μ S = c * ν S)
    (htarget : ∀ i S, MeasurableSet S → S ⊆ B →
      μ (H i '' S) = d * ν S)
    (hdc : d < c) :
    ¬ ∃ T : α → α, Measurable T ∧ Measure.map T μ = μ ∧
      (∀ᵐ x ∂ν, ∃ i, T x = H i x) := by
  rintro ⟨T, hT, hpres, hselect⟩
  let S : ι → Set α := fun i => B ∩ {x | T x = H i x}
  have hS : ∀ i, MeasurableSet (S i) := fun i =>
    hB.inter (measurableSet_eq_fun hT (hH i))
  have hSB : ∀ i, S i ⊆ B := fun _ => Set.inter_subset_left
  have hsub : ∀ i, S i ⊆ T ⁻¹' (H i '' S i) := by
    intro i x hx
    exact ⟨x, hx, hx.2.symm⟩
  have hcover : ∀ᵐ x ∂ν, ∃ i, x ∈ S i := by
    filter_upwards [hfull, hselect] with x hx hsel
    obtain ⟨i, hi⟩ := hsel
    exact ⟨i, hx, hi⟩
  exact not_preserving_of_countable_compression hν
    (fun i => himage i (S i) (hS i) (hSB i)) hsub
    (fun i => hsource (S i) (hS i) (hSB i))
    (fun i => htarget i (S i) (hS i) (hSB i)) hdc hcover ⟨hT, hpres⟩

end Problem356.Splitting

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.Splitting
open MeasureTheory
open scoped ENNReal


theorem solution.{uAlpha,uIndex} : type_of% @_root_.OAI.Problem356.Splitting.no_preserving_branch_selection.{uAlpha,uIndex} := @_root_.OAI.Problem356.Splitting.no_preserving_branch_selection.{uAlpha,uIndex}

-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.integral_eq_measureReal_box_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:07.602617+00:00
-- url     : https://prove2.me/submissions/a9201e0e-660a-473b-bd93-bcc914904348

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralBoxInvariantEqMeasureRealMulSumReps
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → (∀ y ∉ box n R, F y = 0) → ∫ y, F y ∂(Measure.pi fun _ => ν) = ((Measure.pi fun _ : n => ν).real (box n r) : ℂ) * ∑ b ∈ S, F b := by
  intro k _ _ _ _ _ _ ν hν n _ r R S hS hrep F hF hF0
  classical
  have : ν.IsAddHaarMeasure := hν
  have : SecondCountableTopology k := secondCountable k
  have : SigmaFinite ν := inferInstance
  have : (Measure.pi fun _ : n => ν).IsAddHaarMeasure := inferInstance
  set μ : Measure (n → k) := Measure.pi fun _ => ν
  have hmeas : MeasurableSet (box n r) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball r).measurableSet
  have hfin : μ (box n r) < ⊤ := (isCompact_box r).measure_lt_top

  have key : ∀ y, F y = ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) := by
    intro y
    by_cases hy : y ∈ box n R
    · obtain ⟨b, ⟨hbS, hb⟩, huniq⟩ := hrep y hy
      rw [Finset.sum_eq_single b]
      · rw [Set.indicator_of_mem hb]
        have h := hF (y - b) hb b
        rwa [add_sub_cancel] at h
      · intro b' hb'S hne
        have hnot : y - b' ∉ box n r := fun hmem => hne (huniq b' ⟨hb'S, hmem⟩)
        exact Set.indicator_of_notMem hnot _
      · intro hbn
        exact absurd hbS hbn
    · rw [hF0 y hy]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hmem : y - b ∈ box n r
      · rw [Set.indicator_of_mem hmem]
        have h := hF (y - b) hmem b
        rw [add_sub_cancel] at h
        rw [← h, hF0 y hy]
      · exact Set.indicator_of_notMem hmem _
  have hint : ∀ b ∈ S, Integrable (fun y => (box n r).indicator (fun _ => F b) (y - b)) μ := by
    intro b _
    have h1 : Integrable ((box n r).indicator fun _ : n → k => F b) μ := by
      refine (integrable_indicator_iff hmeas).2 ?_
      exact integrableOn_const hfin.ne
    exact h1.comp_sub_right b
  calc ∫ y, F y ∂μ = ∫ y, ∑ b ∈ S, (box n r).indicator (fun _ => F b) (y - b) ∂μ := by
        congr 1
        funext y
        exact key y
    _ = ∑ b ∈ S, ∫ y, (box n r).indicator (fun _ => F b) (y - b) ∂μ := integral_finsetSum S hint
    _ = ∑ b ∈ S, (μ.real (box n r) : ℂ) * F b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [integral_sub_right_eq_self (fun y => (box n r).indicator (fun _ => F b) y) b,
          integral_indicator_const _ hmeas, Complex.real_smul]
    _ = _ := by rw [Finset.mul_sum]
end GlobalTheory.SplitWeil.FourierPi

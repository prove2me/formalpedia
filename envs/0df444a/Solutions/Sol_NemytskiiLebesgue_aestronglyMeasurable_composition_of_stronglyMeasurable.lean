-- Prove2me | solution 1 for NemytskiiLebesgue.aestronglyMeasurable_composition_of_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:34:59.145336+00:00
-- url     : https://prove2.me/submissions/4b3f120f-680e-46e2-8942-bbc44abdfa2f

module
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Caratheodory

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [TopologicalSpace D]
    {F : Type*} [TopologicalSpace F] [PseudoMetrizableSpace F]
    {f : Ω → D → F} (hf : ∀ x : D, AEStronglyMeasurable (f · x) μ) (hf' : ∀ᵐ ω : Ω ∂μ, Continuous
      (f ω))
    {g : Ω → D} (hg : StronglyMeasurable g) :
    AEStronglyMeasurable (fun ω : Ω => f ω (g ω)) μ := by
  have converg : ∀ᵐ ω : Ω ∂μ, Tendsto (fun n : ℕ => f ω (hg.approx n ω)) atTop (𝓝 (f ω (g ω))) := by
    filter_upwards [hf'] with ω hω using hω.continuousAt.tendsto.comp (hg.tendsto_approx ω)
  have measurabl : ∀ n : ℕ, AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) μ := by
    intro n
    have measurab : ∀ s : Set Ω, MeasurableSet s → AEStronglyMeasurable (fun ω : Ω => f ω
      (hg.approx n ω)) (μ.restrict s) := by
      intro s hs
      have measura : ∀ d : D, AEStronglyMeasurable (f · d) (μ.restrict (s ∩ { ω : Ω | hg.approx n ω
        = d })) :=
        (hf · |>.mono_measure Measure.restrict_le_self)
      have measura' :
        ∀ d ∈ Set.range (hg.approx n),
          AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) (μ.restrict (s ∩ { ω : Ω |
            hg.approx n ω = d })) := by
        intro d hd
        exact
          (measura d).congr
            (eventuallyEq_of_mem
              (ae_restrict_mem (hs.inter ((hg.approx n).measurableSet_fiber d)))
              ↓↓(by simp_all))
      have measur :
        ∀ S : Finset D,
          (∀ d ∈ S, AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) (μ.restrict (         s
            ∩ { ω : Ω | hg.approx n ω = d }))) →
                    AEStronglyMeasurable (fun ω : Ω => f ω (hg.approx n ω)) (μ.restrict (⋃ d ∈ S, s
                      ∩ { ω : Ω | hg.approx n ω = d })) := by
        intro S hS
        classical
        induction S using Finset.induction <;> simp_all
      convert measur (hg.approx n).finite_range.toFinset _ <;> aesop
    simpa using measurab ⊤ MeasurableSet.univ
  exact aestronglyMeasurable_of_tendsto_ae _ measurabl converg
end NemytskiiLebesgue

-- Prove2me | solution 1 for GlobalTheory.InvBilinTest.integral_ite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:31.227622+00:00
-- url     : https://prove2.me/submissions/23ed8b6b-f16a-42b4-b992-8dfd7e76e501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]
open MeasureTheory
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]
omit [T2Space G]
open Classical
namespace GlobalTheory.InvBilinTest
namespace _root_.GlobalTheory.InvBilinTest
theorem _root_.solution (K : Subgroup G) (ho : IsOpen (K : Set G)) (c : ℂ) :
    ∫ g, (if g ∈ K then c else 0) ∂μ = (μ.real K : ℂ) * c := by
  have hm : MeasurableSet (K : Set G) := ho.measurableSet
  have h : (fun g : G => if g ∈ K then c else 0) = (K : Set G).indicator (fun _ => c) := by
    ext g
    simp [Set.indicator_apply]
  rw [h, integral_indicator_const c hm, Complex.real_smul]
end _root_.GlobalTheory.InvBilinTest
end GlobalTheory.InvBilinTest

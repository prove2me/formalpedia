-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.setSecSet_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:41.680828+00:00
-- url     : https://prove2.me/submissions/6fb21a77-2a63-4ddf-9c39-944b32be5658

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxPosDens
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_CxSimple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SetFibreFiniteOfGoodProj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AemeasurableCxPosDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxPosMeas_setCoincide_null

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
open MvPolynomial MeasureTheory Metric Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
  GlobalTheory.CompanionTheory.Ar.Pub.CxComp
open ReciprocityTheory.AnForm.R (conePts)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
namespace GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas
theorem _root_.solution {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hfin : ∀ y, (setFibre S Ψ y).Finite)
    (c : Fin e → ℂ) {r : ℝ} (hr : 0 < r) : (setSecSet S Ψ (ball c r)).Finite := by
  by_contra hinf
  let f := Set.Infinite.natEmbedding _ hinf
  set N : Set (Fin e → ℂ) := ⋃ i : ℕ, ⋃ j : ℕ, ⋃ (_ : i ≠ j),
    {y | y ∈ ball c r ∧ (f i : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y = (f j : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y}
  have hN : volume N = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
    refine setCoincide_null (f i).2 (f j).2 fun h => hij (f.injective (Subtype.ext h))
  have hpos : 0 < volume (ball c r) := measure_ball_pos volume c hr
  obtain ⟨y, hyB, hyN⟩ : ∃ y ∈ ball c r, y ∉ N := by
    by_contra h
    push Not at h
    exact hpos.ne' (measure_mono_null h hN)
  refine (hfin y).not_infinite (Set.infinite_of_injective_forall_mem (f := fun n =>
    (f n : (Fin e → ℂ) → ((k : K) → ι k) → ℂ) y) ?_ fun n => (f n).2.2.2 y hyB)
  intro i j hij
  by_contra h
  exact hyN (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨h, hyB, hij⟩⟩⟩)
end GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas

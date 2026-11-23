-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.measure_tile
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:31.976373+00:00
-- url     : https://prove2.me/submissions/4bee306b-53ec-4f40-a77e-00f23e6c611b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RiemannCore
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G]
namespace GlobalTheory.CompanionTheory.RiemannCore
theorem _root_.solution (μ : Measure G) [μ.IsAddHaarMeasure] {D : Set G} (hD : MeasurableSet D)
    (hD1 : μ D = 1) (R : Finset G) (Λ : AddSubgroup G)
    (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) (l : G) :
    μ (tile D R l) = (R.card : ENNReal) := by
  rw [tile, measure_preimage_add, cell, measure_biUnion_finset]
  · simp [measure_preimage_add, hD1]
  · intro r hr r' hr' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne ?_
    simp only [Set.mem_preimage] at hy hy'
    have e1 : y - r - 0 ∈ D := by
      have : -r + y = y - r - 0 := by abel
      rwa [← this]
    have e2 : y - r' - 0 ∈ D := by
      have : -r' + y = y - r' - 0 := by abel
      rwa [← this]
    have := (ht y).unique (y₁ := (r, 0)) (y₂ := (r', 0)) ⟨hr, Λ.zero_mem, e1⟩ ⟨hr', Λ.zero_mem, e2⟩
    exact congrArg Prod.fst this
  · exact fun r _ => (measurable_const_add (-r)) hD
end GlobalTheory.CompanionTheory.RiemannCore

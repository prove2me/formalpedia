-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QuotVan.measurable_modInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:16.19128+00:00
-- url     : https://prove2.me/submissions/c42a98fc-e4c2-42bd-85e6-893e21f031a0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
import Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_map_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] [T2Space Q]
variable (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [SecondCountableTopology N]
  [SecondCountableTopology M]
namespace GlobalTheory.CompanionTheory.QuotVan
theorem _root_.solution : Measurable (modInv N M) := by
  let ν : Measure N := haar
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : N)
  have hs : IsOpen (interior K) := isOpen_interior
  have hs0 : ν (interior K) ≠ 0 := (hs.measure_pos ν ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have hst : ν (interior K) ≠ ∞ :=
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne
  let F : M × N → N := fun p => conjCE N (p.1 : Q) p.2
  have hF : Continuous F := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun p : M × N => (p.1 : Q) * (p.2 : Q) * (p.1 : Q)⁻¹ := by fun_prop
    exact this
  have hB : MeasurableSet (F ⁻¹' interior K) := (hs.preimage hF).measurableSet
  have hm := measurable_measure_prodMk_left (ν := ν) hB
  have he : modInv N M = fun m => ν (Prod.mk m ⁻¹' (F ⁻¹' interior K)) / ν (interior K) := by
    funext m
    have h := congrArg (fun μ : Measure N => μ (interior K)) (map_conj N M ν m)
    simp only [Measure.smul_apply, smul_eq_mul] at h
    rw [map_apply (map_continuous _).measurable hs.measurableSet] at h
    have h3 : Prod.mk m ⁻¹' (F ⁻¹' interior K) = conjCE N (m : Q) ⁻¹' interior K := rfl
    rw [h3, h, ENNReal.mul_div_cancel_right hs0 hst]
  rw [he]
  exact hm.div_const _
end GlobalTheory.CompanionTheory.QuotVan

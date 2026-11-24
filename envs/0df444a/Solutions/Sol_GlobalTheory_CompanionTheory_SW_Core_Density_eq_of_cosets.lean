-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.eq_of_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:14:05.543281+00:00
-- url     : https://prove2.me/submissions/91447cc5-3032-4590-a7fb-7cfd40fef08e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_isOpen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
variable [IsTopologicalAddGroup V] [T2Space V] [SecondCountableTopology V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution {m m' : Measure V} [IsFiniteMeasure m]
    (hb : ∀ U ∈ 𝓝 (0 : V), ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
      (L : Set V) ⊆ U)
    (hcov : ∀ x : V, ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ x ∈ L)
    (heq : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      m (coset L a) = m' (coset L a)) : m = m' := by
  let S : Set (Set V) := {C | C = ∅ ∨ ∃ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) ∧
    IsOpen (L : Set V) ∧ C = coset L a}
  have hbasis : TopologicalSpace.IsTopologicalBasis S := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ (rfl | ⟨L, a, -, hO, rfl⟩)
      · exact isOpen_empty
      · exact coset_isOpen hO a
    · intro a u hau hu
      have hU : (fun t => t + a) ⁻¹' u ∈ 𝓝 (0 : V) :=
        (hu.preimage (continuous_id.add continuous_const)).mem_nhds (by simpa using hau)
      obtain ⟨L, hK, hO, hLU⟩ := hb _ hU
      refine ⟨coset L a, Or.inr ⟨L, a, hK, hO, rfl⟩, by simp [coset, L.zero_mem], fun x hx => ?_⟩
      simpa using hLU hx
  have hgen : ‹MeasurableSpace V› = MeasurableSpace.generateFrom S :=
    (BorelSpace.measurable_eq).trans hbasis.borel_eq_generateFrom
  have hpi : IsPiSystem S := by
    rintro s hs t ht ⟨c, hcs, hct⟩
    rcases hs with rfl | ⟨L, a, hK, hO, rfl⟩
    · simp at hcs
    rcases ht with rfl | ⟨L', b, hK', hO', rfl⟩
    · simp at hct
    refine Or.inr ⟨L ⊓ L', c, ?_, ?_, ?_⟩
    · rw [AddSubgroup.coe_inf]
      exact hK.inter_right hK'.isClosed
    · rw [AddSubgroup.coe_inf]
      exact hO.inter hO'
    · ext x
      have e1 : x - c = (x - a) - (c - a) := by abel
      have e2 : x - c = (x - b) - (c - b) := by abel
      have e3 : x - a = (x - c) + (c - a) := by abel
      have e4 : x - b = (x - c) + (c - b) := by abel
      have hca : c - a ∈ L := hcs
      have hcb : c - b ∈ L' := hct
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : x - a ∈ L := h1
        have h2' : x - b ∈ L' := h2
        exact ⟨e1 ▸ L.sub_mem h1' hca, e2 ▸ L'.sub_mem h2' hcb⟩
      · rintro ⟨h1, h2⟩
        have h1' : x - c ∈ L := h1
        have h2' : x - c ∈ L' := h2
        exact ⟨show x - a ∈ L from e3 ▸ L.add_mem h1' hca, show x - b ∈ L' from e4 ▸ L'.add_mem h2' hcb⟩
  let T : Set (Set V) := {C | ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    C = coset L 0}
  obtain ⟨T', hT'c, hT'T, hT'u⟩ := TopologicalSpace.isOpen_sUnion_countable T (by
    rintro _ ⟨L, -, hO, rfl⟩
    exact coset_isOpen hO 0)
  have huniv : ⋃₀ T' = Set.univ := by
    rw [hT'u]
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨L, hK, hO, hx⟩ := hcov x
    exact ⟨coset L 0, ⟨L, hK, hO, rfl⟩, by simpa [coset] using hx⟩
  have hne : T'.Nonempty := by
    have : (0 : V) ∈ ⋃₀ T' := huniv ▸ Set.mem_univ _
    obtain ⟨C, hC, -⟩ := this
    exact ⟨C, hC⟩
  obtain ⟨B, hB⟩ := hT'c.exists_eq_range hne
  have hBS : ∀ i, B i ∈ S := fun i => by
    obtain ⟨L, hK, hO, hL⟩ := hT'T (hB ▸ Set.mem_range_self i : B i ∈ T')
    exact Or.inr ⟨L, 0, hK, hO, hL⟩
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion S B hgen hpi ?_ hBS
    (fun i => measure_ne_top _ _) ?_
  · rw [← Set.sUnion_range, ← hB, huniv]
  · rintro _ (rfl | ⟨L, a, hK, hO, rfl⟩)
    · simp
    · exact heq L a hK hO
end GlobalTheory.CompanionTheory.SW.Core.Density

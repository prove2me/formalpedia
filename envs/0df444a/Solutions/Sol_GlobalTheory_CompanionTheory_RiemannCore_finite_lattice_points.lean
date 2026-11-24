-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RiemannCore.finite_lattice_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:48:45.436274+00:00
-- url     : https://prove2.me/submissions/ee54b691-00a2-4fb3-b3ba-0627e2dd942f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_mem_tile
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measurableSet_tile
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_measure_tile
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_tile_disjoint

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
theorem _root_.solution (μ : Measure G) [μ.IsAddHaarMeasure] {D K₀ : Set G}
    (hD : MeasurableSet D) (hK : IsCompact K₀) (hDK : D ⊆ K₀) (hD1 : μ D = 1) (R : Finset G)
    (Λ : AddSubgroup G) (ht : ∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D)
    (x0 : G) {C : Set G} (hC : IsCompact C) : {l : Λ | x0 + (l : G) ∈ C}.Finite := by
  have hR : 1 ≤ R.card := by
    obtain ⟨⟨r, l⟩, ⟨hr, -, -⟩, -⟩ := ht 0
    exact Finset.card_pos.2 ⟨r, hr⟩
  set Q : Set G := (fun p : G × G × G => p.1 - x0 + p.2.1 + p.2.2) '' (C ×ˢ ((R : Set G) ×ˢ K₀))
    with hQ
  have hQc : IsCompact Q :=
    (hC.prod (R.finite_toSet.isCompact.prod hK)).image (by fun_prop)
  let As : {l : Λ // x0 + (l : G) ∈ C} → Set G := fun l => tile D R ((l : Λ) : G)
  have hsub : ⋃ i, As i ⊆ Q := by
    refine Set.iUnion_subset fun l y hy => ?_
    obtain ⟨r, hr, h⟩ := mem_tile.1 hy
    refine ⟨(x0 + ((l : Λ) : G), r, y - r - ((l : Λ) : G)), ⟨l.2, hr, hDK h⟩, ?_⟩
    simp only
    abel
  have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion μ (ε := 1) one_pos (As := As)
    (fun l => measurableSet_tile hD R _)
    (fun l l' hne => tile_disjoint ht (fun h => hne (Subtype.ext h)))
    (ne_top_of_le_ne_top hQc.measure_lt_top.ne (measure_mono hsub))
  have huniv : {i | (1 : ENNReal) ≤ μ (As i)} = Set.univ := by
    refine Set.eq_univ_of_forall fun l => ?_
    show 1 ≤ μ (tile D R _)
    rw [measure_tile μ hD hD1 R Λ ht]
    exact_mod_cast hR
  rw [huniv] at hfin
  exact Set.finite_coe_iff.1 (Set.finite_univ_iff.1 hfin)
end GlobalTheory.CompanionTheory.RiemannCore

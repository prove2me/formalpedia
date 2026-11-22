-- Prove2me | solution 1 for MasulloGRH.exists_isDPrimeSequence_compact_openSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:27:42.872828+00:00
-- url     : https://prove2.me/submissions/99ff10d3-b8fe-469e-ab87-834e32024791

import Mathlib
import Definitions.Def_MasulloGRH_DSequences

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_MasulloGRH_exists_isDPrimeSequence_compact_openSubgroup

open Set

/-- Van Dantzig's theorem: every neighbourhood of the neutral element of a totally disconnected,
locally compact Hausdorff group contains a compact open subgroup. -/
theorem exists_compact_openSubgroup_sub_mem_nhds {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  -- a compact neighbourhood `K ⊆ U` of `1` and a clopen `W` with `1 ∈ W ⊆ K`
  obtain ⟨K, hK, hKU, hKcompact⟩ := local_compact_nhds hU
  obtain ⟨W, hW, hOne, hWK⟩ :=
    (loc_compact_Haus_tot_disc_of_zero_dim (H := G)).mem_nhds_iff.mp hK
  have hW : IsClopen W := hW
  have hWcompact : IsCompact W := hKcompact.of_isClosed_subset hW.isClosed hWK
  -- the stabilizer of `W` for left translation
  let H : Subgroup G := MulAction.stabilizer G W
  have hsubset : (H : Set G) ⊆ W := by
    intro g hg
    have hgW : g • W = W := MulAction.mem_stabilizer_iff.mp hg
    have h1 : g • (1 : G) ∈ g • W := smul_mem_smul_set hOne
    rw [hgW, smul_eq_mul, mul_one] at h1
    exact h1
  -- by the tube lemma, a whole neighbourhood of `1` stabilizes `W`
  let O : Set (G × G) := {p | p.1 * p.2 ∈ W ∧ p.1⁻¹ * p.2 ∈ W}
  have hO : IsOpen O := (hW.isOpen.preimage continuous_mul).inter
    (hW.isOpen.preimage (continuous_fst.inv.mul continuous_snd))
  have honeW : ({1} : Set G) ×ˢ W ⊆ O := by
    rintro ⟨g, w⟩ ⟨hg, hw⟩
    have hg1 : g = 1 := hg
    subst hg1
    change (1 : G) * w ∈ W ∧ (1 : G)⁻¹ * w ∈ W
    rw [inv_one, one_mul]
    exact ⟨hw, hw⟩
  obtain ⟨V, T, hV, _, hOneV, hWT, hVT⟩ :=
    generalized_tube_lemma isCompact_singleton hWcompact hO honeW
  have hHopen : IsOpen (H : Set G) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    refine mem_of_superset (hV.mem_nhds (hOneV (mem_singleton 1))) fun g hg ↦ ?_
    apply MulAction.mem_stabilizer_iff.mpr
    refine subset_antisymm (smul_set_subset_iff.mpr ?_) ?_
    · exact fun w hw ↦ (hVT (mk_mem_prod hg (hWT hw))).1
    · intro w hw
      exact mem_smul_set_iff_inv_smul_mem.mpr (hVT (mk_mem_prod hg (hWT hw))).2
  let J : OpenSubgroup G := ⟨H, hHopen⟩
  exact ⟨J, hWcompact.of_isClosed_subset J.isClosed hsubset, hsubset.trans (hWK.trans hKU)⟩

end Sol_MasulloGRH_exists_isDPrimeSequence_compact_openSubgroup

open MasulloGRH Sol_MasulloGRH_exists_isDPrimeSequence_compact_openSubgroup

theorem solution
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [FirstCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ K : ℕ → OpenSubgroup G, (∀ k, IsCompact (K k : Set G)) ∧
      ∀ C : ℝ, 1 < C → IsDPrimeSequence μ (fun k => (K k : Set G)) C := by
  -- the compact open subgroups form a basis of neighbourhoods of `1`
  have hbasis : (𝓝 (1 : G)).HasBasis (fun H : OpenSubgroup G ↦ IsCompact (H : Set G))
      (fun H ↦ (H : Set G)) := by
    refine ⟨fun W ↦ ⟨fun hW ↦ exists_compact_openSubgroup_sub_mem_nhds hW, ?_⟩⟩
    rintro ⟨H, _, hHW⟩
    exact mem_of_superset H.mem_nhds_one hHW
  -- first countability: a decreasing sequence of them is still a basis
  obtain ⟨K, hcompact, hK⟩ := hbasis.exists_antitone_subbasis
  have hmul (k : ℕ) : (K k : Set G) * (K k : Set G) = (K k : Set G) :=
    (K k).toSubgroup.toSubmonoid.coe_mul_self_eq
  have hdiff (k : ℕ) : (K k : Set G) * (K k : Set G)⁻¹ = (K k : Set G) := by
    rw [show ((K k : Set G))⁻¹ = (K k : Set G) from inv_coe_set, hmul]
  have hpos (k : ℕ) : 0 < μ (K k : Set G) := (K k).isOpen.measure_pos μ ⟨1, (K k).one_mem⟩
  have hfin (k : ℕ) : μ (K k : Set G) < ∞ := (hcompact k).measure_lt_top
  refine ⟨K, hcompact, fun C hC ↦ ⟨?_, fun V hV ↦ hK.mem_iff.mp hV⟩⟩
  refine
    { one_mem := fun k ↦ (K k).one_mem
      nullMeasurable := fun k ↦ (K k).isOpen.measurableSet.nullMeasurableSet
      measure_pos := hpos
      measure_lt_top := hfin
      antitone := fun k ↦ hK.antitone (Nat.le_succ k)
      const_pos := zero_lt_one.trans hC
      doubling := fun k ↦ ?_ }
  rw [hdiff]
  refine ⟨hpos k, ?_⟩
  have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (zero_lt_one.trans hC)).mpr hC
  calc μ (K k : Set G) = 1 * μ (K k : Set G) := (one_mul _).symm
    _ < ENNReal.ofReal C * μ (K k : Set G) :=
      ENNReal.mul_lt_mul_left (hpos k).ne' (hfin k).ne h1

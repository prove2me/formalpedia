-- Prove2me | solution 1 for ModularCurve.XOneP.forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/aae4bcdf-4de8-51ac-a489-4a310f9e1bc7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq

set_option autoImplicit false

namespace ValuationSubring
p2m_export "ValuationSubring" "comap mem_comap nonunits_le_nonunits mem_nonunits_iff_or nonunits nonunits_subset valuation"
p2m_open "ValuationSubring"

variable {K K' : Type*} [Field K] [Field K']

theorem map_mem_nonunits_iff (V : ValuationSubring K') (ι : K →+* K') (f : K) :
    ι f ∈ V.nonunits ↔ f ∈ (V.comap ι).nonunits := by
  rw [mem_nonunits_iff_or, mem_nonunits_iff_or, mem_comap, map_inv₀, map_eq_zero_iff ι ι.injective]

theorem forall_mem_map_mem_nonunits_iff_iff_comap_eq (V : ValuationSubring K') (ι : K →+* K')
    (W₀ W₁ : ValuationSubring K) (hV : V.comap ι = W₀ ∨ V.comap ι = W₁) :
    (∀ f : K, f ∈ W₀ → (ι f ∈ V.nonunits ↔ f ∈ W₀.nonunits)) ↔ V.comap ι = W₀ := by
  constructor
  · intro h
    rcases hV with hV | hV
    · exact hV
    · have key : ∀ f : K, f ∈ W₀ → (f ∈ W₁.nonunits ↔ f ∈ W₀.nonunits) := fun f hf => by
        rw [← h f hf, map_mem_nonunits_iff, hV]
      by_cases hle : W₀ ≤ W₁
      ·
        rw [hV]
        refine le_antisymm ?_ hle
        rw [← nonunits_le_nonunits]
        intro f hf
        exact (key f (nonunits_subset hf)).mpr hf
      · exfalso
        obtain ⟨g, hg0, hg1⟩ := Set.not_subset.mp hle

        have hgu : g ∉ W₀.nonunits := fun hn => hg1 (nonunits_subset ((key g hg0).mpr hn))
        rw [mem_nonunits_iff_or, not_or, not_not] at hgu
        obtain ⟨hgne, hginv⟩ := hgu

        have h1 : g⁻¹ ∈ W₁.nonunits := by
          rw [mem_nonunits_iff_or, inv_inv]; exact Or.inr hg1
        have h2 : g⁻¹ ∈ W₀.nonunits := (key g⁻¹ hginv).mp h1
        rw [mem_nonunits_iff_or, inv_inv] at h2
        rcases h2 with h2 | h2
        · exact hgne (inv_eq_zero.mp h2)
        · exact h2 hg0
  · intro hV f hf
    rw [map_mem_nonunits_iff, hV]

end ValuationSubring

theorem solution
    (A : Type*) [CommRing A] [IsLocalRing A] (L : Type*) [Field L] [Algebra A L]
    (K : IntermediateField L (LaurentSeries L))
    (W₀ W₁ : ValuationSubring ↥K)
    (h4 : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (h6 : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (K' : Type*) [Field K'] (ι : ↥K →+* K') (V : ValuationSubring K')
    (hV : V.comap ι = W₀ ∨ V.comap ι = W₁) :
    (∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (ι f ∈ V.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) ↔
      V.comap ι = W₀ := by
  rw [← ValuationSubring.forall_mem_map_mem_nonunits_iff_iff_comap_eq V ι W₀ W₁ hV]
  constructor
  · intro h f hf
    obtain ⟨x, y, hy, hxy⟩ := (h4 f).mp hf
    rw [h f x y hy hxy, h6 f x y hy hxy]
  · intro h f x y hy hxy
    rw [h f ((h4 f).mpr ⟨x, y, hy, hxy⟩), h6 f x y hy hxy]

end S_ModularCurve_XOneP_forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq
end P2MW
export P2MW.S_ModularCurve_XOneP_forall_gaussPresentation_map_mem_nonunits_iff_iff_comap_eq (solution)

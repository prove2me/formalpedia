-- Prove2me | solution 1 for IsLocalRing.isLocalProartinianAlgebra_adicTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/64b2b233-f15b-5b2e-a610-3331c6ec24bf

import Definitions.Def_Deformations_ProartinianCat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isLocalProartinianAlgebra_adicTopology

universe u

open IsLocalRing Deformation

theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
    (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap 𝒪 R))) :
    letI : TopologicalSpace R := (maximalIdeal R).adicTopology
    IsLocalProartinianAlgebra 𝒪 R := by
  letI : TopologicalSpace R := (maximalIdeal R).adicTopology
  letI : IsTopologicalRing R := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
  letI : IsAdicTopology R := ⟨rfl⟩
  haveI : Finite (ResidueField R) := by
    refine Finite.of_surjective (ResidueField.map (algebraMap 𝒪 R)) fun y => ?_
    obtain ⟨c, hc⟩ := hres y
    exact ⟨residue 𝒪 c, by rw [ResidueField.map_residue]; exact hc⟩
  letI : CompactSpace R := compactSpace_of_finite_residueField
  haveI : IsResidueAlgebra 𝒪 R := ⟨hres⟩
  exact ⟨⟩

end S_IsLocalRing_isLocalProartinianAlgebra_adicTopology
end P2MW
export P2MW.S_IsLocalRing_isLocalProartinianAlgebra_adicTopology (solution)

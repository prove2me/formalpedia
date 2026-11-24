-- Prove2me | solution 2 for GlobalTheory.CompanionTheory.ResKCoords.map_maximalIdeal_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:59.575644+00:00
-- url     : https://prove2.me/submissions/2dc624a5-1294-43a7-a5e0-b400e2b1f4d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RegularSequenceGermsRegularLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ResKCoords
namespace GlobalTheory.CompanionTheory.ResKCoords
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  ext x
  rw [← Ideal.comap_symm, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff e.symm x
end GlobalTheory.CompanionTheory.ResKCoords

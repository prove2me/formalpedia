-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ResKCoords.rsp_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:17:35.032799+00:00
-- url     : https://prove2.me/submissions/3b31d7e7-30d5-41f7-b8b4-fde78ca4615d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RegularSequenceGermsRegularLocal
import Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_map_maximalIdeal_of_ringEquiv

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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (m : ℕ) (r : Fin m → R) (h : FinalTheorems.Rsp R m r) :
    FinalTheorems.Rsp S m (fun i => e (r i)) := by
  refine ⟨?_, h.2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have h1 : Set.range (fun i => e (r i)) = (e : R → S) '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← map_maximalIdeal_of_ringEquiv e, ← h.1]
  exact (Ideal.map_span e (Set.range r)).symm
end GlobalTheory.CompanionTheory.ResKCoords

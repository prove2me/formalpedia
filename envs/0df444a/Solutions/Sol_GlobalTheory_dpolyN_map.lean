-- Prove2me | solution 1 for GlobalTheory.dpolyN_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:07.354796+00:00
-- url     : https://prove2.me/submissions/8655ba9e-cef8-4b54-9856-91353fff3b6b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MapDofNIterate
import Theorems.Thm_GlobalTheory_InvDerCopiesMap_map_DmonN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (d n : ℕ) (F : Fin d → PS S 2 d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) (f : PS S n d), DpolyN (fun i => MvPowerSeries.map ψ (F i)) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) (MvPowerSeries.map ψ f) = MvPowerSeries.map ψ (DpolyN F cp u P f) := by
  intro S S' _ _ ψ d n F κ _ cp u P f
  unfold DpolyN
  rw [Finset.sum_subset (MvPolynomial.support_map_subset ψ P) (fun m _ hm => by
    rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, InvDerCopiesMap.map_DmonN, MvPolynomial.coeff_map]
end GlobalTheory

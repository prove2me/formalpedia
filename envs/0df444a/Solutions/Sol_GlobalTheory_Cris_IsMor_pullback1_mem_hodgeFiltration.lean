-- Prove2me | solution 1 for GlobalTheory.Cris.IsMor.pullback1_mem_hodgeFiltration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:20.394086+00:00
-- url     : https://prove2.me/submissions/037a05ae-1d51-4d90-87d5-f60e31b62305

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_hodgeFiltration_eq_range
import Theorems.Thm_GlobalTheory_Cris_IsMor_cl_pullForm

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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
variable {s : X ⟶ Sp R}
namespace GlobalTheory.Cris
namespace IsMor
theorem _root_.solution {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
    (h : IsMor (dp0 R) s (dp0 R') s' σ φ) {c : FirstDeRham s} (hc : c ∈ F1 s) : h.pull1 c ∈ F1 s' := by
  rw [hodgeFiltration_eq_range] at hc ⊢
  obtain ⟨f, rfl⟩ := hc
  exact ⟨h.pullForm f, h.cl_pullForm f⟩
end IsMor
end GlobalTheory.Cris

-- Prove2me | solution 1 for GlobalTheory.Cris.IsMor.pullback1_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:42.888481+00:00
-- url     : https://prove2.me/submissions/8e6169be-c054-4ab5-9f42-cf4e5662d9e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans


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
variable {γ : DividedPowers I} {γ' : DividedPowers I'} {γ'' : DividedPowers I''}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''}
variable {σ : R →+* R'} {φ : X' ⟶ X}
variable {τ : R' →+* R''} {ψ : X'' ⟶ X'} {ρ : R →+* R''} {χ : X'' ⟶ X}
namespace GlobalTheory.Cris
namespace IsMor
theorem _root_.solution (h : IsMor γ s γ' s' σ φ) (h' : IsMor γ' s' γ'' s'' τ ψ)
    (h'' : IsMor γ s γ'' s'' ρ χ) (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : H1 γ s) :
    h'.pull1 (h.pull1 c) = h''.pull1 c :=
  (h.coef.pullCohomologyOne_comp h'.coef c).symm.trans
    ((h.coef.comp h'.coef).pullCohomologyOne_eq_of_natTrans h''.coef (h.compTrans h' h'' e e')
      (fun _ _ ↦ rfl) c)
end IsMor
end GlobalTheory.Cris

-- Prove2me | solution 1 for GlobalTheory.Cris.IsMor.pullback2_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:37:28.101253+00:00
-- url     : https://prove2.me/submissions/c438f172-840c-46ec-ad97-7a956578b7ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_comp
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_eq_of_natTrans


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
    (h'' : IsMor γ s γ'' s'' ρ χ) (e : ∀ r, τ (σ r) = ρ r) (e' : ψ ≫ φ = χ) (c : H2 γ s) :
    h'.pull2 (h.pull2 c) = h''.pull2 c :=
  (h.coef.pullCohomologyTwo_comp h'.coef c).symm.trans
    ((h.coef.comp h'.coef).pullCohomologyTwo_eq_of_natTrans h''.coef (h.compTrans h' h'' e e')
      (fun _ _ ↦ rfl) c)
end IsMor
end GlobalTheory.Cris

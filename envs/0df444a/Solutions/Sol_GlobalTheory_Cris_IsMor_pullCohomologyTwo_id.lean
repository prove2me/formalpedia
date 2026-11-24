-- Prove2me | solution 1 for GlobalTheory.Cris.IsMor.pullCohomologyTwo_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:01:27.427323+00:00
-- url     : https://prove2.me/submissions/efe53c5b-691a-41f8-bfd2-33ceaa91e0fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_id


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
namespace GlobalTheory.Cris
namespace IsMor
theorem _root_.solution (h : IsMor γ s γ s (RingHom.id R) (𝟙 X)) (c : H2 γ s) : h.pull2 c = c :=
  (h.coef.pullCohomologyTwo_eq_of_natTrans (CoefMap.id _) h.idTrans (fun _ _ ↦ rfl) c).trans
    (CoefMap.pullCohomologyTwo_id c)
end IsMor
end GlobalTheory.Cris

-- Prove2me | solution 1 for GlobalTheory.Cris.Thick.Hom.mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:20.406666+00:00
-- url     : https://prove2.me/submissions/e4006e1e-67de-43d2-90b0-fb30a1e98c6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration

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
open GlobalTheory.Cris.Thick
variable {γ : DividedPowers I} {s : X ⟶ Sp R}
namespace GlobalTheory.Cris.Thick
namespace Hom
theorem _root_.solution {T T' : Thick γ s} (f : T ⟶ T') {b : T.B} (hb : b ∈ T.J) : f.φ b ∈ T'.J := f.dp.1 (Ideal.mem_map_of_mem _ hb)
end Hom
end GlobalTheory.Cris.Thick

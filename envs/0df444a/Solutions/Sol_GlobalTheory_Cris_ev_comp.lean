-- Prove2me | solution 1 for GlobalTheory.Cris.ev_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:06.922504+00:00
-- url     : https://prove2.me/submissions/4c881f24-d55d-4f86-a524-be57ed31a1f6

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
namespace GlobalTheory.Cris
theorem _root_.solution {γ : DividedPowers I} {s : X ⟶ Sp R} (f : Z1 (O γ s)) {T T' T'' : Thick γ s}
    (φ : T ⟶ T') (ψ : T' ⟶ T'') : ev f (φ ≫ ψ) = ψ.φ (ev f φ) + ev f ψ := Z1.comp f φ ψ
end GlobalTheory.Cris

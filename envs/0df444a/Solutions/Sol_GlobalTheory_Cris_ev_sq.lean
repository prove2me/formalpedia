-- Prove2me | solution 1 for GlobalTheory.Cris.ev_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:39.831533+00:00
-- url     : https://prove2.me/submissions/bed7ad29-5c62-474f-90f2-1113a8714ed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_ev_comp

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
theorem _root_.solution {γ : DividedPowers I} {s : X ⟶ Sp R} (f : Z1 (O γ s)) {T₁ T₂ T₃ T₄ : Thick γ s}
    (a : T₁ ⟶ T₂) (p : T₂ ⟶ T₄) (q : T₁ ⟶ T₃) (b : T₃ ⟶ T₄) (h : ∀ c, p.φ (a.φ c) = b.φ (q.φ c)) :
    p.φ (ev f a) + ev f p = b.φ (ev f q) + ev f b := by
  have e : a ≫ p = q ≫ b := Thick.hom_ext fun c ↦ h c
  rw [← ev_comp, ← ev_comp, e]
end GlobalTheory.Cris

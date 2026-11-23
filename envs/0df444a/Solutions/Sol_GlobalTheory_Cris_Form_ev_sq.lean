-- Prove2me | solution 1 for GlobalTheory.Cris.Form.ev_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:39.1568+00:00
-- url     : https://prove2.me/submissions/97615694-d8fd-4326-950e-eca02afffa05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_Cris_ev_sq

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
namespace Form
theorem _root_.solution (f : Form s) {T₁ T₂ T₃ T₄ : Thick (dp0 R) s}
    (a : T₁ ⟶ T₂) (p : T₂ ⟶ T₄) (q : T₁ ⟶ T₃) (b : T₃ ⟶ T₄) (h₁ : T₁.J = ⊥) (h₂ : T₂.J = ⊥)
    (h : ∀ c, p.φ (a.φ c) = b.φ (q.φ c)) : ev f.1 p = b.φ (ev f.1 q) + ev f.1 b := by
  have h0 : ev f.1 a = 0 := f.2 a h₁ h₂
  have e := GlobalTheory.Cris.ev_sq f.1 a p q b h
  rwa [h0, map_zero, zero_add] at e
end Form
end GlobalTheory.Cris

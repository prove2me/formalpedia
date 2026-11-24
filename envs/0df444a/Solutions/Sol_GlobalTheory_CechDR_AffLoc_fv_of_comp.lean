-- Prove2me | solution 1 for GlobalTheory.CechDR.AffLoc.fv_of_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:36.789985+00:00
-- url     : https://prove2.me/submissions/dc48ec58-120e-4e63-9a59-62b725347028

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued

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
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
namespace GlobalTheory.CechDR.AffLoc
theorem _root_.solution (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) {T₁ T₂ T₃ : TT s} (a : T₁ ⟶ T₂)
    (c : T₂ ⟶ T₃) (d : T₁ ⟶ T₃) (h : ∀ x, c.hom.φ (a.hom.φ x) = d.hom.φ x) :
    fv f d = c.hom.φ (fv f a) + fv f c := by
  have e : a ≫ c = d := ObjectProperty.hom_ext _ (Thick.hom_ext h)
  rw [← e]
  exact f.2 a c
end GlobalTheory.CechDR.AffLoc

-- Prove2me | solution 1 for GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:48:26.5618+00:00
-- url     : https://prove2.me/submissions/8b39f1af-0d95-4f24-b531-6d9d1da64413

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGluedStatement
import Theorems.Thm_GlobalTheory_CechDR_AffLoc_fv_eq_sub_of_glued


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)), (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) → ∀ {T T' : TT s} (φ : T ⟶ T') (G : T.obj.B) (G' : T'.obj.B), (∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p) → (∀ p : Pair (pt T'), toSec R T'.obj.B p.1.1 G' = hSec f g T' p) → fv f φ = G' - φ.hom.φ G := by
  first | exact @GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued | exact GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued | (intros; apply GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued <;> assumption)
end _root_.GlobalTheory.T

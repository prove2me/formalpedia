-- Prove2me | solution 1 for GlobalTheory.CechDR.AffLoc.pt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:37.820322+00:00
-- url     : https://prove2.me/submissions/352900ea-38f3-4fc4-93ab-95fa965e171a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp


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
theorem _root_.solution {T T' : TT s} (φ : T ⟶ T') :
    pt T' = spMap (φ.hom.φ : T.obj.B →+* T'.obj.B) ≫ pt T := by
  have e : ((πe T').symm : T'.obj.B₀ →+* T'.obj.B).comp φ.hom.φ₀ =
      (φ.hom.φ : T.obj.B →+* T'.obj.B).comp ((πe T).symm : T.obj.B₀ →+* T.obj.B) := by
    ext b
    obtain ⟨b, rfl⟩ := T.obj.surj b
    change (πe T').symm (φ.hom.φ₀ (T.obj.π b)) = φ.hom.φ ((πe T).symm (πe T b))
    rw [φ.hom.comm, RingEquiv.symm_apply_apply]
    exact (πe T').symm_apply_apply (φ.hom.φ b)
  rw [pt, pt, ← φ.hom.pt, ← Category.assoc, ← spMap_comp, e, spMap_comp, Category.assoc]
end GlobalTheory.CechDR.AffLoc

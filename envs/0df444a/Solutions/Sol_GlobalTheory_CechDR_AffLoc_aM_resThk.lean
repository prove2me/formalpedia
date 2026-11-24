-- Prove2me | solution 1 for GlobalTheory.CechDR.AffLoc.aM_resThk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:33.525473+00:00
-- url     : https://prove2.me/submissions/47fc35a2-f88a-4d33-9eb0-102a87dd46a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CocycleLocalSectionsRestrictCompatibly

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
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh
  GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
namespace GlobalTheory.CechDR.AffLoc
theorem _root_.solution (T : TT s) {p q : Pair (pt T)} (hpq : p ≤ q) :
    aM T q ≫ resThk T hpq = (affF s).map (homOfLE (Pair.le_snd hpq)).op ≫ aM T p :=
  ObjectProperty.hom_ext _ (Thick.hom_ext fun u ↦
    (congrArg (fun t ↦ t.hom u) ((pt T).appLE_map q.2 (homOfLE (Pair.le_fst hpq)).op)).trans
      (congrArg (fun t ↦ t.hom u) ((pt T).map_appLE p.2 (homOfLE (Pair.le_snd hpq)).op)).symm)
end GlobalTheory.CechDR.AffLoc

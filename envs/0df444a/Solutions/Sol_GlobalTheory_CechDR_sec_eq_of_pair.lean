-- Prove2me | solution 1 for GlobalTheory.CechDR.sec_eq_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:03:07.892629+00:00
-- url     : https://prove2.me/submissions/9537267f-a045-4939-b127-871afd4baf1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpen
import Theorems.Thm_GlobalTheory_CechDR_Pair_exists_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.CechDR
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}
namespace GlobalTheory.CechDR
theorem _root_.solution (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens)
    (a b : (OAff s').obj (op W))
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op a = mp (OAff s') (homOfLE hp).op b) :
    a = b := by
  refine TopCat.Presheaf.section_ext X'.sheaf W.1 a b fun x hx ↦ ?_
  obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
  have e : (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom a) =
      (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom b) :=
    congrArg _ (h p hp)
  have k := X'.presheaf.germ_res (homOfLE (show p.1.1.1 ≤ W.1 from hp)) x hxp
  exact (congrArg (fun t ↦ t.hom a) k).symm.trans (e.trans (congrArg (fun t ↦ t.hom b) k))
end GlobalTheory.CechDR

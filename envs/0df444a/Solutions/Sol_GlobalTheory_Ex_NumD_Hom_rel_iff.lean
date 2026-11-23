-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.rel_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:17.885729+00:00
-- url     : https://prove2.me/submissions/0904bfa5-9952-4ecf-8421-8eec6ad38894

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_rel_img

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
namespace GlobalTheory.Ex.NumD.Hom
theorem _root_.solution (g : N.Gt) (g' : N'.Gt) : I.Rel g g' ↔ g' = I.img g := by
  refine ⟨fun h => Gt.ext h.1 (funext fun χ => ?_), fun h => h ▸ I.rel_img g⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  exact mul_right_cancel ((h.2 χ).trans ((I.rel_img g).2 χ).symm)
end GlobalTheory.Ex.NumD.Hom

-- Prove2me | solution 1 for GlobalTheory.UnramifiedEndFlat.flat_stalkSpecializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:29.835805+00:00
-- url     : https://prove2.me/submissions/41e230c3-723e-4c26-98b5-d8fb65b98927

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_iff_comp_germ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.UnramifiedEndFlat
open IsLocalRing
namespace GlobalTheory.UnramifiedEndFlat
theorem _root_.solution {X : Scheme.{0}} {x x' : X} (h : x ⤳ x') :
    (X.presheaf.stalkSpecializes h).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x') isOpen_univ
  rw [flat_iff_comp_germ hU hx', TopCat.Presheaf.germ_stalkSpecializes,
    ← Category.comp_id (X.presheaf.germ U x _), ← flat_iff_comp_germ hU]
  exact RingHom.Flat.id _
end GlobalTheory.UnramifiedEndFlat

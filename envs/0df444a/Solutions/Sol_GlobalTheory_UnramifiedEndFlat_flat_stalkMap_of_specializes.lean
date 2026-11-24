-- Prove2me | solution 1 for GlobalTheory.UnramifiedEndFlat.flat_stalkMap_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:18:34.394413+00:00
-- url     : https://prove2.me/submissions/70cf126c-e0af-46a7-a65a-3b52b848b084

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_iff_comp_germ
import Theorems.Thm_GlobalTheory_UnramifiedEndFlat_flat_stalkSpecializes
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


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
theorem _root_.solution {X Y : Scheme.{0}} (f : X ⟶ Y) {x x' : X} (h : x ⤳ x')
    (hf : (f.stalkMap x').hom.Flat) : (f.stalkMap x).hom.Flat := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx', -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x')) isOpen_univ
  have h' : f x ⤳ f x' := h.map f.continuous
  rw [flat_iff_comp_germ hU (h'.mem_open U.2 hx'),
    ← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hx' h', Category.assoc,
    Scheme.Hom.stalkSpecializes_stalkMap f x x' h, ← flat_iff_comp_germ hU hx']
  exact hf.comp (flat_stalkSpecializes h)
end GlobalTheory.UnramifiedEndFlat

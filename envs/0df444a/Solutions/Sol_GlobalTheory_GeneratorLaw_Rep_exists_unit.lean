-- Prove2me | solution 1 for GlobalTheory.GeneratorLaw.Rep.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:35.852989+00:00
-- url     : https://prove2.me/submissions/57c12dcd-6989-4aba-889a-3fef74e7a3f5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
import Theorems.Thm_GlobalTheory_GeneratorLaw_mem_empty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {X Y Y' : Scheme.{0}} {L : LB X}
namespace GlobalTheory.GeneratorLaw
namespace Rep
theorem _root_.solution (hL : L.IsLB) {F : Vals L Y} (h : Rep L (fun _ _ _ => 1) F) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ Z r z J, Good L z J → gm r z ⊤ a = F Z r z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, hv⟩ := h
  obtain ⟨t', -, h'⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun V _ k => (hs V k).trans (by simp)) t ht
  refine ⟨res (fun y _ => mem_empty PEmpty.elim y) (t'.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  rw [← hv _ _ _ _ hJ, ← h' _ _ _ _ hJ, val_of t' r z J PEmpty.elim fun k => k.elim]
  exact gm_res r z (V := ⊤) _ trivial _
end Rep
end GlobalTheory.GeneratorLaw

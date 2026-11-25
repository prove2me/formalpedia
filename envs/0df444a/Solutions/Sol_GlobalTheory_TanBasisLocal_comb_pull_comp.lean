-- Prove2me | solution 1 for GlobalTheory.TanBasisLocal.comb_pull_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:37:18.338686+00:00
-- url     : https://prove2.me/submissions/4b0fa06a-ac58-43be-8e31-e5f7f80be647

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
import Theorems.Thm_Formalism_L2_Pj_dualMap_comp
import Theorems.Thm_Formalism_L2_Pj_isCombAt_pull
import Theorems.Thm_Formalism_L2_Pj_spMap_comp_ring
import Theorems.Thm_GlobalTheory_SqZero_dualMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory GlobalTheory.TanBasisLocal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.TanBasisLocal
theorem _root_.solution {S A C : Type} [CommRing S] [CommRing A] [CommRing C] {φ : S →+* A} {χ : S →+* C}
    (α : A →+* C) (hα : α.comp φ = χ) {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    {a : Fin m → A}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w)) :
    IsCombAt (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) (fun j => α (a j)) (spMap (dualMap χ) ≫ w) :=
  isCombAt_pull α (by rw [← Category.assoc, spMap_comp_ring, hα])
    (fun j => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα])
    (by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]) ha
end GlobalTheory.TanBasisLocal

-- Prove2me | solution 1 for GlobalTheory.TanBasisLocal.coeff_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:06:22.49111+00:00
-- url     : https://prove2.me/submissions/bc19bd9e-e4d0-4fef-83de-3706989ccbcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsTangentVectorBasisAtPointBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TanBasisLocal
import Theorems.Thm_GlobalTheory_TanBasisLocal_tan_pull
import Theorems.Thm_GlobalTheory_TanBasisLocal_comb_pull_comp
import Theorems.Thm_Formalism_L2_Pj_dualMap_comp
import Theorems.Thm_Formalism_L2_Pj_spMap_comp_ring
import Theorems.Thm_GlobalTheory_Frames_tanBasis_baseChange
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
theorem _root_.solution {S A B C : Type} [CommRing S] [CommRing A] [CommRing B] [CommRing C] {φ : S →+* A}
    {ψ : S →+* B} {χ : S →+* C} (α : A →+* C) (β : B →+* C) (hα : α.comp φ = χ) (hβ : β.comp ψ = χ)
    {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (hw : IsTanAt x w) (hb : TanBasis (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k))
    {a : Fin m → A} {b : Fin m → B}
    (ha : IsCombAt (spMap φ ≫ x) (fun k => spMap (dualMap φ) ≫ v k) a (spMap (dualMap φ) ≫ w))
    (hb' : IsCombAt (spMap ψ ≫ x) (fun k => spMap (dualMap ψ) ≫ v k) b (spMap (dualMap ψ) ≫ w)) :
    (fun j => α (a j)) = fun j => β (b j) := by
  have hB : TanBasis (spMap χ ≫ x) (fun k => spMap (dualMap χ) ≫ v k) := by
    have := GlobalTheory.Frames.tanBasis_baseChange E H Dw l Xo _ _ α _ m _ hb
    have e1 : spMap α ≫ spMap φ ≫ x = spMap χ ≫ x := by rw [← Category.assoc, spMap_comp_ring, hα]
    have e2 : (fun k => spMap (dualMap α) ≫ spMap (dualMap φ) ≫ v k) = fun k => spMap (dualMap χ) ≫ v k :=
      funext fun k => by rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp, hα]
    rw [e1, e2] at this
    exact this
  exact (hB.2 _ (tan_pull χ hw)).unique (comb_pull_comp α hα ha) (comb_pull_comp β hβ hb')
end GlobalTheory.TanBasisLocal

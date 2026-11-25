-- Prove2me | solution 1 for GlobalTheory.CoverGlue.existsUnique_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:02:59.987176+00:00
-- url     : https://prove2.me/submissions/115fd0f4-b9a0-48ce-975b-adccbd8b6aac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
namespace GlobalTheory.CoverGlue
theorem _root_.solution {X Y : Scheme.{0}} {I : Type} {Z : I → Scheme.{0}} (ψ : ∀ i, Z i ⟶ X)
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) (f : ∀ i, Z i ⟶ Y)
    (hf : ∀ i j (T : Scheme.{0}) (x : T ⟶ Z i) (y : T ⟶ Z j), x ≫ ψ i = y ≫ ψ j → x ≫ f i = y ≫ f j) :
    ∃! F : X ⟶ Y, ∀ i, ψ i ≫ F = f i := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers I Z ψ (fun x => by simpa using hc x) hψ
  refine ⟨C.glueMorphisms f fun i j => hf i j _ _ _ pullback.condition, fun i => C.ι_glueMorphisms _ _ i,
    fun F hF => C.hom_ext _ _ fun i => (hF i).trans (C.ι_glueMorphisms f _ i).symm⟩
end GlobalTheory.CoverGlue

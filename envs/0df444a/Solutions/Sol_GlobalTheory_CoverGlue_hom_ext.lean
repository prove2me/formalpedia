-- Prove2me | solution 1 for GlobalTheory.CoverGlue.hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:14.900975+00:00
-- url     : https://prove2.me/submissions/38141464-87d5-4be7-9b23-e19ffa868a56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Theorems.Thm_GlobalTheory_CoverGlue_existsUnique_hom

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
    (hψ : ∀ i, IsOpenImmersion (ψ i)) (hc : ∀ x : X, ∃ i, x ∈ Set.range (ψ i)) {F F' : X ⟶ Y}
    (h : ∀ i, ψ i ≫ F = ψ i ≫ F') : F = F' :=
  (existsUnique_hom ψ hψ hc (fun i => ψ i ≫ F') fun _ _ _ _ _ e => by
    rw [← Category.assoc, e, Category.assoc]).unique h fun _ => rfl
end GlobalTheory.CoverGlue

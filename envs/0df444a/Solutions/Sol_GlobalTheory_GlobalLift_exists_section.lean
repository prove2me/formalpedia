-- Prove2me | solution 1 for GlobalTheory.GlobalLift.exists_section
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:35.081918+00:00
-- url     : https://prove2.me/submissions/274add0b-3199-4e6b-b624-379a27d15cd6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton

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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GlobalLift
open CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
omit [GrpObj A]
namespace GlobalTheory.GlobalLift
theorem _root_.solution {T : Over S} [Subsingleton T.left] {V : T.left.Opens} {p : T.left} (hp : p ∈ V) :
    ∃ h : T ⟶ overRes V, h ≫ overResι V = 𝟙 T := by
  obtain rfl : V = ⊤ := eq_top_iff.2 fun q _ => by rwa [Subsingleton.elim q p]
  exact ⟨Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]), Over.OverMorphism.ext T.left.toIso_inv_ι⟩
end GlobalTheory.GlobalLift

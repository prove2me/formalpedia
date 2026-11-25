-- Prove2me | solution 1 for GlobalTheory.ValGenExtend.isGen_inv_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:58.234534+00:00
-- url     : https://prove2.me/submissions/1610e73c-e0e5-4bdd-a969-b019a7fcedea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.ValGenExtend
namespace GlobalTheory.ValGenExtend
theorem _root_.solution {X : Scheme.{0}} {N : LB X} (t : LB.Gen N) (ht : t.IsGen)
    (g : ∀ a b, Γ(X, N.U a ⊓ N.U b)ˣ) (hg : ∀ a b, g a b = (N.g a b)⁻¹) :
    LB.Gen.IsGen (L := ⟨N.ι, N.U, g⟩) ⟨fun i => (t.s i)⁻¹⟩ := by
  intro a b
  have h : res (inf_le_left : N.U a ⊓ N.U b ≤ _) (t.s a)⁻¹ =
      g a b * res (inf_le_right : N.U a ⊓ N.U b ≤ _) (t.s b)⁻¹ := by
    rw [map_inv, map_inv, ht a b, _root_.mul_inv, hg]
  exact h
end GlobalTheory.ValGenExtend

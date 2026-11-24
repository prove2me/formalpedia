-- Prove2me | solution 1 for GlobalTheory.ToSplit.IsFrame.exists_gen_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:32:59.101835+00:00
-- url     : https://prove2.me/submissions/cade58e4-f08d-4eec-98ac-795d225cbd24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_ToSplit_exists_gen_descent
import Theorems.Thm_GlobalTheory_ToSplit_exists_act
import Theorems.Thm_GlobalTheory_ToSplit_inv_eq_div_mul_inv
import Theorems.Thm_GlobalTheory_ToSplit_IsFrame_trans_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
omit [IsMonHom i]
namespace GlobalTheory.ToSplit
namespace IsFrame
theorem _root_.solution {O : RigLB B} {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ}
    (h : IsFrame q i 0 O u) : ∃ t : LB.Gen O.L, t.IsGen := by
  refine exists_gen_descent q O.L (fun j => (u j)⁻¹) (fun j Z g₁ g₂ z e h₁ h₂ => ?_)
    (fun j j' y h₁ h₂ => ?_)
  · obtain ⟨t, rfl⟩ := exists_act hk e
    rw [map_inv, map_inv, h.1 j Z t g₂ z h₂, ofAdd_zero, map_one, _root_.one_mul]
  · rw [map_inv, map_inv, h.trans_id j j' y h₁ h₂]
    exact inv_eq_div_mul_inv _ _
end IsFrame
end GlobalTheory.ToSplit

-- Prove2me | solution 1 for GlobalTheory.exists_gtDatum_of_splitTorus_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:17:12.486408+00:00
-- url     : https://prove2.me/submissions/150ff97b-9f1b-4282-bc96-cfc4b26e41b8

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
import Theorems.Thm_GlobalTheory_ToSplit_exists_isFrame
import Theorems.Thm_GlobalTheory_ToSplit_IsFrame_exists_gen_zero
import Theorems.Thm_GlobalTheory_ToSplit_IsFrame_exists_iso_add
import Theorems.Thm_GlobalTheory_ToSplit_IsFrame_exists_gen_lam
import Theorems.Thm_GlobalTheory_ToSplit_exists_gtDatum

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
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B], IsAbelianScheme B → ∀ (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∃ (O : X → RigLB B) (h₁ : _) (h₂ : _) (h₃ : _), ∀ hB : IsAbelianScheme B, ∃ d : (SplitExt.mk B hB X O h₁ h₂ h₃).GtDatum G, d.q = q ∧ d.i = i := by
  intro S X _ _ _ G B _ _ _ _ q i _ _ _ _ _ hk
  choose O u hu using ToSplit.exists_isFrame hk
  refine ⟨O, fun χ χ' => (hu χ).exists_iso_add hk (hu χ') (hu (χ + χ')),
    (hu 0).exists_gen_zero hk, fun χ => (hu χ).exists_gen_lam hk, fun hB => ?_⟩
  exact ToSplit.exists_gtDatum (SplitExt.mk B hB X O _ _ _) hk u hu
end GlobalTheory

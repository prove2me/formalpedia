-- Prove2me | solution 1 for GlobalTheory.LieComb.tanExp_tanExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:12.010085+00:00
-- url     : https://prove2.me/submissions/b06ffcbc-3cbc-4c90-89cc-4d62c8e86172

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AwayToAwayRightEqOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_lieExp_congr
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_id isTan_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.LieComb
open GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {n : ℕ} {v : Fin n → (epsR R ⟶ G)}
namespace GlobalTheory.LieComb
theorem _root_.solution (hv : ∀ i, IsTangent (v i)) {m : ℕ} (M : Fin m → Fin n → R)
    (c : Fin m → R) : tanExp (fun i => tanExp v (M i)) c = tanExp v (∑ i, c i • M i) := by
  change _ = (combHom hv (∑ i, c i • M i)).toMul
  rw [map_sum, toMul_sum, tanExp, lieExp]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine (comp_lieExp v _ _ _).trans ?_
  exact lieExp_congr _ (fun j => by
    simp [epsTo, dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inl_mul_inr,
      mul_comm, smul_smul]) _ _
end GlobalTheory.LieComb

-- Prove2me | solution 1 for GlobalTheory.UU.exists_gtDatum_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:35:28.118815+00:00
-- url     : https://prove2.me/submissions/2c5196e7-e6b1-4427-b1cc-08df84948e9f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Statements_LocalTrivialization_LocTrivOfRetraction
import Theorems.Thm_GlobalTheory_exists_gtDatum_of_splitTorus_extension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S S' : Scheme.{0}} {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
theorem _root_.solution [Module.Free ℤ X] [Module.Finite ℤ X] (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ (O : X → RigLB A) (h₁ : _) (h₂ : _) (h₃ : _)
      (Dat : (SplitExt.mk A hA X O h₁ h₂ h₃).GtDatum (splitTorus S X ⊗ A)) (Q : TQ (splitTorus S X ⊗ A) X),
      Q.i = Dat.i := by
  have := hA.comm
  let Q := TQ.prod X A hA
  have := Q.q_affine
  have : QuasiCompact Q.q.left := inferInstance
  obtain ⟨O, h₁, h₂, h₃, h⟩ := exists_gtDatum_of_splitTorus_extension S X _ A hA Q.q Q.i Q.q_hom Q.i_hom Q.q_flat
    Q.q_surj this Q.isKernel
  obtain ⟨d, -, hd⟩ := h hA
  exact ⟨O, h₁, h₂, h₃, d, Q, hd.symm⟩
end GlobalTheory.UU

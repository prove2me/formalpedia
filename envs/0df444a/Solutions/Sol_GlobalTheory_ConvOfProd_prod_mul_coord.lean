-- Prove2me | solution 1 for GlobalTheory.ConvOfProd.prod_mul_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:27:15.119818+00:00
-- url     : https://prove2.me/submissions/f63fab14-4940-43f9-9028-38db945f66ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSubSum
import Theorems.Thm_GlobalTheory_ConvOfProd_over_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.ConvOfProd
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.ConvOfProd
theorem _root_.solution {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {k l m : ℕ} {β ga α : D.X}
    (hα : β + ga = α) {a : SecBT D T k β} {b : SecBT D T l ga} {c : SecBT D T m α} (H : IsProdB a b c) {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left)
    (z : Z) (J) (hJ : Good D.P.L z J) :
    sval c r z J * (val (g.t α) x z J).val =
      sval a r z J * (val (g.t β) x z J).val * (sval b r z J * (val (g.t ga) x z J).val) := by
  subst hα
  let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
  let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
  let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq g x r hr)
  have h₁ := H FinalForm ro z J hJ
  have h₂ := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul β ga) x).trans (val_mul hJ _ _ _))
  have h₃ := val_cub D.cub xo (z := z) hJ (DVR.cP D _ β) (DVR.cP D _ ga) g.pG
  have h₄ : xo ≫ g.pG = ro ≫ snd T D.P.A := Over.OverMorphism.ext hr.symm
  rw [DVR.comp_cP, DVR.comp_cP, h₄] at h₃
  have h₅ := congrArg Units.val ((congrArg (val (g.t (β + ga)) x z J * ·) h₃).symm.trans h₂)
  rw [Units.val_mul, Units.val_mul] at h₅
  refine (congrArg (· * (val (g.t (β + ga)) x z J).val) h₁).trans ?_
  rw [_root_.mul_mul_mul_comm, ← h₅]
  exact (_root_.mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))
end GlobalTheory.ConvOfProd

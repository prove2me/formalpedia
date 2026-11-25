-- Prove2me | solution 1 for GlobalTheory.MulSupp.exists_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:02:07.030051+00:00
-- url     : https://prove2.me/submissions/77116abf-f6dc-417a-8054-724344c555d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProductSupportInSubgroupTheta
import Theorems.Thm_GlobalTheory_MulSupp_val_pull_cub
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_mulSec


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
open GlobalTheory GlobalTheory.MulSupp
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.MulSupp
theorem _root_.solution (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (α β : D.X) (a : SecBT D T k α) (b : SecBT D T l β) :
    ∃ p : SecBT D T (k + l) (α + β), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval p r z J = sval a r z J * sval b r z J * (cubAt D α β (r ≫ (snd T D.P.A).left) z J).val := by
  obtain ⟨p, hp⟩ := exists_sec D.P.isLB (φ' := famφT D T (α + β)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (Fintype.prod_sum_type _)
        (prod_cub (toUnit _ ≫ D.c α) (toUnit _ ≫ D.c β) (snd T D.P.A) h))).trans ?_
      have e₀ : ∀ u, padd D.P.A (snd T D.P.A) u = u * snd T D.P.A :=
        fun u => mul_comm (snd T D.P.A) u
      have e₁ : toUnit (T ⊗ D.P.A) ≫ D.c (α + β) = (toUnit _ ≫ D.c α) * (toUnit _ ≫ D.c β) := by
        rw [D.c_add]; exact MonObj.comp_mul _ _ _
      have e₂ : toUnit (T ⊗ D.P.A) ≫ η[D.P.A] = 1 := rfl
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, famφT, DegPre.famε, e₀, e₁, e₂, Matrix.cons_val]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec a b) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (toUnit _ ≫ D.c α) (lift (toUnit _ ≫ D.c β) (snd T D.P.A))).left) (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)))
  refine ⟨p, fun Z r z J hJ => (hp Z r z J hJ).trans ?_⟩
  exact (H1.SectionArithmetic.sval_mulSec _ _ r z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_mulSec _ _ r z hJ)
    ((sval_genSec _ _ r z hJ).trans (congrArg Units.val (val_pull_cub D α β _ r z hJ))))
end GlobalTheory.MulSupp

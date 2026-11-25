-- Prove2me | solution 1 for GlobalTheory.UU.FEDesc.famFE_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:29:07.148139+00:00
-- url     : https://prove2.me/submissions/d7528ba2-9050-4031-aad8-627af7dd707c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniquePullB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamilyFunctionalEquationFieldChangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpFOfExpT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FiniteExponentBaseChangeField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


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
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.FEDesc
namespace GlobalTheory.UU.FEDesc
theorem _root_.solution {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k n : ℕ) (c : Fin n → F) (s : Raw D F k) (t : Fin n → Raw D F k)
    (h : ∀ (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval (s α) r z J = ∑ i, gs r z ⊤ (scal (fst (TF (R := R) F) D.P.A).left (c i)) * sval (t i α) r z J)
    (ht : ∀ i, DegPre.FamFE D F k (t i)) : DegPre.FamFE D F k s := by
  intro mu α u hu hc
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  rw [h _ _ _ y J hJ, h _ _ _ y J hJ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (ht i mu α u hu hc) _ (𝟙 _) y J hJ, _root_.mul_assoc]
  congr 1
  have e : (DegPre.trF D F mu).left ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D.P.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : DegPre.trF D F mu ≫ fst (TF (R := R) F) D.P.A = _)
  have key : ∀ {Y : Scheme.{0}} (y : Y) (a : Y ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of F)) (x : F), a ≫ p = p →
      gs (𝟙 Y) y ⊤ (scal p x) = gs (𝟙 Y ≫ a) y ⊤ (scal p x) := by
    intro Y y a p x hap
    rw [← gs_pull (𝟙 Y) a y ⊤ trivial]
    conv_lhs => rw [← hap]
    rfl
  exact key y _ _ _ e
end GlobalTheory.UU.FEDesc

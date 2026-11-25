-- Prove2me | solution 1 for GlobalTheory.ConvFE.form_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:17.696195+00:00
-- url     : https://prove2.me/submissions/93616cf9-b054-4443-a51f-d8662ee30a1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdicSumRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConvTermFe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RelationOfFiniteLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecScale
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_prod_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.ConvFE
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (k : ℕ) (α' α : D.X) (b : T ⟶ D.P.A) :
    FormEq (famφT D T α') (DegPre.famε k) (Sum.elim (fun i => (trT D b).left ≫ famφT D T α i) (deltaφT D α' α b))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) := fun U _ h => by
  refine Eq.symm (Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (c := ∏ i, h ((trT D b).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
    (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
      (c := ∏ i, h (famφT D T α' i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_)
  exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)
end GlobalTheory.ConvFE

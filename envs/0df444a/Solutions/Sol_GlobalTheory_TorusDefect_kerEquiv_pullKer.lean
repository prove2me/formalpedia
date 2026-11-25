-- Prove2me | solution 1 for GlobalTheory.TorusDefect.kerEquiv_pullKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:25.044393+00:00
-- url     : https://prove2.me/submissions/6458d4e3-91b6-453a-9256-309985e3e009

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Theorems.Thm_GlobalTheory_TorusDefect_coe_pullKer
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_comp_mem_redKer
import Theorems.Thm_GlobalTheory_SqZero_kerEquiv_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.coe_unitsAddMonoidAlgebraEquiv
attribute [local simp] GlobalTheory.mem_coactionWeightSpace
attribute [local simp] GlobalTheory.trivialCoaction_apply
attribute [local simp] GlobalTheory.tupleCoface_last
attribute [local simp] GlobalTheory.tupleCoface_zero
attribute [local simp] GlobalTheory.tupleContraction_apply
attribute [local simp] P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)
open GlobalTheory GlobalTheory.TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SqZero GlobalTheory.Diag
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
  {C C' : Type} [CommRing C] [Algebra A C] [CommRing C'] [Algebra A C']
variable {G : Over (Spec (CommRingCat.of A))} [GrpObj G] {J : Ideal A}
  {Z : Type} [AddCommGroup Z]
variable [IsCommMonObj G] [Smooth G.hom] {n : ℕ} {v : Fin n → (epsR A ⟶ G)}
namespace GlobalTheory.TorusDefect
theorem _root_.solution (hv : IsLieBasis v) (hJ : J ^ 2 = ⊥) (u : X →+ Y)
    (y : redKer (R := A) G (J.map (algebraMap A (AddMonoidAlgebra A X)))) (i : Fin n) :
    (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul (pullKer G J u y)) i :
      AddMonoidAlgebra A Y) =
      AddMonoidAlgebra.mapDomain u (kerEquiv hv (map_algebraMap_sq hJ) (Additive.ofMul y) i :
        AddMonoidAlgebra A X) := by
  have h := kerEquiv_map hv (map_algebraMap_sq hJ) (map_algebraMap_sq hJ) (mapDomainAlgHom A A u)
    (map_mem_map _) y i
  have e : pullKer G J u y = ⟨spMap (mapDomainAlgHom A A u) ≫ y.1,
      comp_mem_redKer y.2 (mapDomainAlgHom A A u) (map_mem_map _)⟩ := Subtype.ext (coe_pullKer u y)
  rw [e, h]
  simp
end GlobalTheory.TorusDefect

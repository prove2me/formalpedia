-- Prove2me | solution 1 for GlobalTheory.TorusDefect.mem_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:57:14.087264+00:00
-- url     : https://prove2.me/submissions/39928c55-e8a6-4717-9eee-2e83ea9fae34

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
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
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
namespace GlobalTheory.TorusDefect
theorem _root_.solution (J : Ideal A) (b : AddMonoidAlgebra A X) :
    b ∈ J.map (algebraMap A (AddMonoidAlgebra A X)) ↔ ∀ x, b.coeff x ∈ J := by
  constructor
  · intro hb x
    have h0 : b ∈ RingHom.ker (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk J)) := by
      refine (Ideal.map_le_iff_le_comap.2 ?_) hb
      intro a ha
      simp [AddMonoidAlgebra.coe_algebraMap, AddMonoidAlgebra.mapRingHom_single,
        Ideal.Quotient.eq_zero_iff_mem, ha]
    have h1 := congrArg (fun c => c.coeff x) (RingHom.mem_ker.1 h0)
    simpa [AddMonoidAlgebra.coeff_mapRingHom, Ideal.Quotient.eq_zero_iff_mem] using h1
  · intro hb
    rw [← AddMonoidAlgebra.sum_coeff_single b, Finsupp.sum]
    refine Ideal.sum_mem _ fun x _ => ?_
    have hx : single x (b.coeff x) =
        algebraMap A (AddMonoidAlgebra A X) (b.coeff x) * single x 1 := by
      rw [← Algebra.smul_def, AddMonoidAlgebra.smul_single', _root_.mul_one]
    rw [hx]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hb x))
end GlobalTheory.TorusDefect

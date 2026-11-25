-- Prove2me | solution 1 for GlobalTheory.TorusLift.isMonHom_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:58:26.522994+00:00
-- url     : https://prove2.me/submissions/580260a1-e586-406d-8f9d-21bd4ea8fd19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
import Theorems.Thm_GlobalTheory_TorusLift_isMonHom_pullbackComp
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_coe_unitsAddMonoidAlgebraEquiv
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_trivialCoaction_apply
import Theorems.Thm_GlobalTheory_tupleCoface_last
import Theorems.Thm_GlobalTheory_tupleCoface_zero
import Theorems.Thm_GlobalTheory_tupleContraction_apply
import Theorems.Thm_P2M_GlobalTheory_hochschildD__trivialCoaction_d0af9f793cf0
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


section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorusLift
section General
variable {S S' S'' : Scheme.{0}}
private theorem isMonHom_iff_of_conj_iso {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    [MonObj M] [MonObj M'] [MonObj N] [MonObj N'] (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b]
    (ha : IsMonHom a) (hb : IsMonHom b) (g : M ⟶ N) (g' : M' ⟶ N') (hg : g ≫ b = a ≫ g') :
    IsMonHom g ↔ IsMonHom g' := by
  constructor
  · intro h
    have e : g' = (asIso a).inv ≫ g ≫ b := by simp [hg]
    rw [e]
    infer_instance
  · intro h
    have e : g = a ≫ g' ≫ (asIso b).inv := by simp [← reassoc_of% hg]
    rw [e]
    infer_instance
end General
end GlobalTheory.TorusLift
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusLift
variable {S S' S'' : Scheme.{0}}
namespace GlobalTheory.TorusLift
theorem _root_.solution {s : S'' ⟶ S'} {p : S' ⟶ S} {q : S'' ⟶ S} (h : q = s ≫ p)
    {V W : Over S} [GrpObj V] [GrpObj W] (f : V ⟶ W) : IsMonHom ((Over.pullback q).map f) ↔
      IsMonHom ((Over.pullback s).map ((Over.pullback p).map f)) := by
  subst h
  exact isMonHom_iff_of_conj_iso _ _ (isMonHom_pullbackComp s p V) (isMonHom_pullbackComp s p W) _ _
    ((Over.pullbackComp s p).hom.naturality f)
end GlobalTheory.TorusLift

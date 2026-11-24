-- Prove2me | solution 1 for GlobalTheory.AdicSum.sumF_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:40.480626+00:00
-- url     : https://prove2.me/submissions/3b79e422-20eb-46a0-8d6f-1a6751dbccf1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SumFCalculus
import Theorems.Thm_GlobalTheory_AdicSum_sumI_unique
import Theorems.Thm_GlobalTheory_AdicSum_sumI_map
import Theorems.Thm_GlobalTheory_AdicSum_sumI_add
import Theorems.Thm_GlobalTheory_AdicSum_sumI_comp_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
open GlobalTheory GlobalTheory.AdicSum
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AdicSum
namespace _root_.GlobalTheory.AdicSum
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R),
    _root_.ReciprocityTheory.ChartRestriction.G.Out.AdmBase R I → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Ix : Type)
    (x x' : Ix → F) (s s' : F),
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x s' →
      s = s') ∧
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x' s' →
      ∀ c : F, _root_.GlobalTheory.UT.SumF I F (fun i => c * x i + x' i) (c * s + s')) ∧
    ∀ (Jx : Type) (e : Jx → Ix), Function.Injective e → (∀ i, i ∉ Set.range e → x i = 0) →
      (_root_.GlobalTheory.UT.SumF I F (x ∘ e) s ↔
        _root_.GlobalTheory.UT.SumF I F x s) := by
  intro R _ _ I hadm F _ _ Ix x x' s s'
  obtain ⟨hnoeth, -, -, hcomplete⟩ := hadm
  haveI := hnoeth
  haveI := hcomplete
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  refine ⟨fun h h' => _root_.GlobalTheory.AdicSum.sumI_unique (IsAdicComplete.le_jacobson_bot I) h h',
    fun h h' c => ?_, fun Jx e he h0 => _root_.GlobalTheory.AdicSum.sumI_comp_iff he h0⟩
  let f : F →ₗ[R] F :=
    { toFun := fun y => c * y
      map_add' := mul_add c
      map_smul' := fun r y => by
        show c * (algebraMap R (FractionRing R) r • y) = algebraMap R (FractionRing R) r • (c * y)
        exact Algebra.mul_smul_comm _ _ _ }
  exact _root_.GlobalTheory.AdicSum.sumI_add (_root_.GlobalTheory.AdicSum.sumI_map f h) h'
end _root_.GlobalTheory.AdicSum
end GlobalTheory.AdicSum

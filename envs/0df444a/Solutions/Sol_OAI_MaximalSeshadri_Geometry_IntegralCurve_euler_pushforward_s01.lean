-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.IntegralCurve.euler_pushforward_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:11:57.767616+00:00
-- url     : https://prove2.me/submissions/d2157a9e-4812-4d55-98f2-3d86391ab2da

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES004
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_cohomology_zero_above_one_s01

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ClosedPushforwardEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.ClosedPushforward
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.FlasqueCohomology MaximalSeshadri.Frames

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

variable [IsClosedImmersion f]

local instance instHasExtModules_solutions_2_r65b2e2_1 : HasExt.{1} X.Modules := schemeHasExt
attribute [local instance] OAI.MaximalSeshadri.ClosedPushforward.instHasExtModules_solutions_3
theorem euler_pushforward (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) :
    eulerCharacteristic p d ((Scheme.Modules.pushforward f).obj M) =
      eulerCharacteristic (f ≫ p) d M := by
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact (cohomologyEquiv f p M n).finrank_eq.symm

end
end MaximalSeshadri.ClosedPushforward

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

lemma IntegralCurve.euler_two_eq_one (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) :
    eulerCharacteristic (C.embedding ≫ S.structureMap) 2 L.sheaf =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 L.sheaf := by
  have hz : Subsingleton (cohomology L.sheaf 2) := ⟨fun x y =>
    (C.cohomology_zero_above_one_s01 S A hA L 0 x).trans
      (C.cohomology_zero_above_one_s01 S A hA L 0 y).symm⟩
  let := hz
  have hd : cohomologyDimension (C.embedding ≫ S.structureMap) L.sheaf 2 = 0 := by
    simp [cohomologyDimension,Module.finrank_zero_of_subsingleton]
  change (∑ n ∈ Finset.range (2+1), (-1 : ℤ)^n *
    (cohomologyDimension (C.embedding ≫ S.structureMap) L.sheaf n : ℤ)) = _
  rw [Finset.sum_range_succ,hd]
  simp only [Nat.cast_zero,mul_zero,add_zero]
  rfl

lemma IntegralCurve.euler_pushforward_s01_oai (S : Surface) (C : IntegralCurve S)
    (A : LineBundle S.scheme) (hA : A.IsAmple) (L : LineBundle C.scheme) :
    eulerCharacteristic S.structureMap 2 ((Scheme.Modules.pushforward C.embedding).obj L.sheaf) =
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1 L.sheaf := by
  rw [ClosedPushforward.euler_pushforward,C.euler_two_eq_one S A hA]

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.IntegralCurve.euler_pushforward_s01_oai := @OAI.MaximalSeshadri.Geometry.IntegralCurve.euler_pushforward_s01_oai

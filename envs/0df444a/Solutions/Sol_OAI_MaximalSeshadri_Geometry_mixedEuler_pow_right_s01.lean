-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:50.562738+00:00
-- url     : https://prove2.me/submissions/8c8baedf-bacd-4815-97b5-c4f35d20d95d

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_pow_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_curveDegree_eq_mixedEuler_s01

section
-- module Solutions.Q223_SES.Seshadri_Intersection_MixedIntersection
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem mixedEuler_pow_right_s01_oai (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) (n : ℕ) :
    mixedEuler S L (M.pow n) = (n : ℤ)*mixedEuler S L M := by
  classical
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have h₁ := generated_curveDegree_eq_mixedEuler_s01 S L hL M d k s hs v hne hC
  have h₂ := generated_curveDegree_eq_mixedEuler_s01 S L hL (M.pow n) d k s hs v hne hC
  change curveDegree S M C = (d : ℤ)*mixedEuler S L M at h₁
  change curveDegree S (M.pow n) C = (d : ℤ)*mixedEuler S L (M.pow n) at h₂
  rw [curveDegree_pow_s01 S L hL,h₁] at h₂
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply mul_left_cancel₀ hd'
  rw [← h₂]
  ring

end
end MaximalSeshadri.Geometry

end



end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01_oai := @OAI.MaximalSeshadri.Geometry.mixedEuler_pow_right_s01_oai

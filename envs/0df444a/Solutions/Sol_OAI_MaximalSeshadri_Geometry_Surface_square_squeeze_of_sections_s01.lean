-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:43.820963+00:00
-- url     : https://prove2.me/submissions/618f022f-c55d-4024-8b6f-6a06e578b41d

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_power_H0_quadratic_upper_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_power_H2_bounded_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_power_euler_difference_s01

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CohomologyIso
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

variable {X : Scheme.{0}}

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_QuadraticSequence
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.EulerNumerics

lemma periodic_nat_gcd {α : Type*} (f : ℕ → α) (a b : ℕ)
    (ha : Function.Periodic f a) (hb : Function.Periodic f b) :
    Function.Periodic f (Nat.gcd a b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih =>
    by_cases hz : a = 0
    · simpa [hz] using hb
    have hm : Function.Periodic f (b % a) := by
      intro n
      have H := ha.nat_mul (b/a) (n+b%a)
      rw [Nat.cast_id, Nat.add_assoc,Nat.mod_add_div'] at H
      exact H.symm.trans (hb n)
    rw [Nat.gcd_rec]
    exact ih (b%a) (Nat.mod_lt b (Nat.pos_of_ne_zero hz)) a hm ha

lemma periodic_nat_coprime_constant {α : Type*} (f : ℕ → α) (a b : ℕ)
    (hab : Nat.Coprime a b) (ha : Function.Periodic f a)
    (hb : Function.Periodic f b) (n : ℕ) : f n = f 0 := by
  have H := periodic_nat_gcd f a b ha hb
  rw [hab.gcd_eq_one] at H
  simpa only [Nat.cast_id,mul_one] using H.nat_mul_eq n

theorem quadratic_of_coprime_differences (f : ℕ → ℤ) (a b : ℕ)
    (hab : Nat.Coprime a b) (d e c h : ℤ)
    (ha : ∀ n, f (n+a) - f n = (n : ℤ)*d+c)
    (hb : ∀ n, f (n+b) - f n = (n : ℤ)*e+h) (n : ℕ) :
    2*f n = (n : ℤ)*((n : ℤ)-1)*(f 2-2*f 1+f 0) +
      2*(n : ℤ)*(f 1-f 0)+2*f 0 := by
  let g (n : ℕ) := f (n+2)-2*f (n+1)+f n
  have periodic (a : ℕ) (d c : ℤ)
      (ha : ∀ n, f (n+a)-f n = (n : ℤ)*d+c) : Function.Periodic g a := by
    intro n
    have H₀ := ha n
    have H₁ := ha (n+1)
    have H₂ := ha (n+2)
    dsimp [g]
    rw [show n+a+2 = n+2+a by omega,show n+a+1 = n+1+a by omega]
    push_cast at H₁ H₂
    nlinarith
  have hg (n : ℕ) : g n = f 2-2*f 1+f 0 :=
    periodic_nat_coprime_constant g a b hab (periodic a d c ha) (periodic b e h hb) n
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp <;> ring
  | more n hn hn₁ =>
    have H := hg n
    dsimp [g] at H
    push_cast at hn₁ ⊢
    nlinarith

end MaximalSeshadri.EulerNumerics

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceQuadraticEuler
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

lemma Surface.euler_power_one (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf =
      eulerCharacteristic S.structureMap 2 L.sheaf :=
  eulerCharacteristic_iso S.structureMap (moduleTensorRightUnit L.sheaf) 2

lemma Surface.euler_power_second_difference (S : Surface) (L : LineBundle S.scheme) :
    eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf -
      2*eulerCharacteristic S.structureMap 2 (L.pow 1).sheaf +
      eulerCharacteristic S.structureMap 2 (L.pow 0).sheaf = selfIntersection S L := by
  rw [S.euler_power_one]
  rfl

theorem Surface.power_euler_quadratic (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (n : ℕ) :
    2*eulerCharacteristic S.structureMap 2 (L.pow n).sheaf =
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) := by
  classical
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  obtain ⟨a,ha,-,N,s,hs,v,hne,hi,hd⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  obtain ⟨b,hb,hab,N',s',hs',v',hne',hi',hd'⟩ := S.coprime_integral_section_s01 L hL a ha
  let := hi'
  let D : IntegralCurve S := ⟨(sectionIdeal k s' hs' v').subscheme,
      (sectionIdeal k s' hs' v').subschemeι,inferInstance,inferInstance,hd'⟩
  have ha' (m : ℕ) : f (m+a)-f m = (m : ℤ)*curveDegree S L C +
      ((a : ℤ)*curveDegree S L C+eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme)) := by
    have H := generated_power_euler_difference_s01 S L hL L a k s hs v hne hd m
    change f (m+a)-f m = _ at H
    push_cast at H
    linarith
  have hb' (m : ℕ) : f (m+b)-f m = (m : ℤ)*curveDegree S L D +
      ((b : ℤ)*curveDegree S L D+eulerCharacteristic (D.embedding ≫ S.structureMap) 1 (O D.scheme)) := by
    have H := generated_power_euler_difference_s01 S L hL L b k s' hs' v' hne' hd' m
    change f (m+b)-f m = _ at H
    push_cast at H
    linarith
  have H := EulerNumerics.quadratic_of_coprime_differences f a b hab _ _ _ _ ha' hb' n
  have hq := S.euler_power_second_difference L
  have h1 := S.euler_power_one L
  change f 2-2*f 1+f 0 = selfIntersection S L at hq
  change f 1 = _ at h1
  rw [hq,h1] at H
  exact H

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SurfaceTopGrowth
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

lemma surface_euler_expansion (S : Surface) (M : S.scheme.Modules) :
    eulerCharacteristic S.structureMap 2 M =
      (cohomologyDimension S.structureMap M 0 : ℤ) -
      (cohomologyDimension S.structureMap M 1 : ℤ) +
      (cohomologyDimension S.structureMap M 2 : ℤ) := by
  simp [eulerCharacteristic,Finset.sum_range_succ,sub_eq_add_neg]

theorem Surface.power_H0_quadratic_lower (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ B : ℕ, ∀ n : ℕ,
      (n : ℤ)*((n : ℤ)-1)*selfIntersection S L +
      2*(n : ℤ)*(eulerCharacteristic S.structureMap 2 L.sheaf -
        eulerCharacteristic S.structureMap 2 (O S.scheme)) +
      2*eulerCharacteristic S.structureMap 2 (O S.scheme) - 2*B ≤
        2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) := by
  obtain ⟨B,hB⟩ := S.power_H2_bounded_s01 L hL
  refine ⟨B,fun n => ?_⟩
  have hq := S.power_euler_quadratic L hL n
  rw [surface_euler_expansion S (L.pow n).sheaf] at hq
  have hle : (cohomologyDimension S.structureMap (L.pow n).sheaf 2 : ℤ) ≤ B := by
    exact_mod_cast hB n
  have hnonneg : (0 : ℤ) ≤ cohomologyDimension S.structureMap (L.pow n).sheaf 1 := Nat.cast_nonneg _
  linarith

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_PolynomialBounds
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.NefNumerics
lemma quadratic_nonpos_leading (a b c : ℤ)
    (h : ∀ n : ℕ, a*(n:ℤ)^2+b*n+c ≤ 0) : a ≤ 0 := by
  by_contra hn
  have ha : 1 ≤ a := by omega
  let n := (2*|b|+2*|c|+3).toNat
  have he : (n:ℤ) = 2*|b|+2*|c|+3 := Int.toNat_of_nonneg (by positivity)
  have hp : 0 ≤ (n:ℤ) := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_right ha (sq_nonneg (n:ℤ))
  have hb := mul_le_mul_of_nonneg_right (neg_abs_le b) hp
  have hc := neg_abs_le c
  have H := h n
  have hab := abs_nonneg b
  have hac := abs_nonneg c
  nlinarith

end MaximalSeshadri.NefNumerics

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BlowupIntersectionGrowth
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

lemma Surface.power_H0_bounds (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ b c e z : ℤ, ∀ n : ℕ,
      selfIntersection S L*(n:ℤ)^2+b*n+c ≤ 2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ∧
      2*(cohomologyDimension S.structureMap (L.pow n).sheaf 0 : ℤ) ≤ selfIntersection S L*(n:ℤ)^2+e*n+z := by
  obtain ⟨B,hB⟩ := S.power_H0_quadratic_lower L hL
  obtain ⟨C,G,hC⟩ := S.power_H0_quadratic_upper_s01 L hL
  let d := eulerCharacteristic S.structureMap 2 L.sheaf-eulerCharacteristic S.structureMap 2 (O S.scheme)
  let q := selfIntersection S L
  refine ⟨-q+2*d,2*eulerCharacteristic S.structureMap 2 (O S.scheme)-2*B,
    -q+2*d+2*G,2*eulerCharacteristic S.structureMap 2 (O S.scheme)+2*C,fun n => ⟨?_,?_⟩⟩
  · have H := hB n
    dsimp [q,d]
    nlinarith only [H]
  · have H := hC n
    dsimp [q,d]
    nlinarith only [H]

lemma Surface.square_squeeze_of_sections_s01_oai (S T : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple)
    (D : LineBundle T.scheme) (hD : D.IsAmple) (k r : ℕ)
    (hb : ∀ n : ℕ,
      cohomologyDimension T.structureMap (D.pow n).sheaf 0 ≤ cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ∧
      2*cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 ≤
        2*cohomologyDimension T.structureMap (D.pow n).sheaf 0 + r*n*(n+1)) :
    (k:ℤ)^2*selfIntersection S L-r ≤ selfIntersection T D ∧
    selfIntersection T D ≤ (k:ℤ)^2*selfIntersection S L := by
  obtain ⟨b,c,e,z,hS⟩ := S.power_H0_bounds L hL
  obtain ⟨b',c',e',z',hT⟩ := T.power_H0_bounds D hD
  have h₁ := quadratic_nonpos_leading (selfIntersection T D-(k:ℤ)^2*selfIntersection S L)
    (b'-(k:ℤ)*e) (c'-z) (fun n => by
      have H := (hT n).1
      have G := (hS (k*n)).2
      have F : (cohomologyDimension T.structureMap (D.pow n).sheaf 0 : ℤ) ≤
        cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 := by exact_mod_cast (hb n).1
      push_cast at G
      nlinarith only [H,G,F])
  have h₂ := quadratic_nonpos_leading ((k:ℤ)^2*selfIntersection S L-(r:ℤ)-selfIntersection T D)
    ((k:ℤ)*b-r-e') (c-z') (fun n => by
      have H := (hT n).2
      have G := (hS (k*n)).1
      have F : 2*(cohomologyDimension S.structureMap (L.pow (k*n)).sheaf 0 : ℤ) ≤
        2*(cohomologyDimension T.structureMap (D.pow n).sheaf 0 : ℤ)+(r:ℤ)*n*(n+1) := by exact_mod_cast (hb n).2
      push_cast at G
      nlinarith only [H,G,F])
  omega

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.square_squeeze_of_sections_s01_oai

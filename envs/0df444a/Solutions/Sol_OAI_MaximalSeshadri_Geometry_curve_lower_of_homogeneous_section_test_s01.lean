-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:20:13.409715+00:00
-- url     : https://prove2.me/submissions/ea53d7fc-2a6a-4b84-8ccf-75899b053339

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_mixed_degree_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_invertible_ideal_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_etale_line_frame_inside_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_eventually_effective_with_arbitrary_jet_frames_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_pow_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_tensor_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_curveDegree_eq_mixedEuler_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_power_euler_difference_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_twistedIdealPowerInclusion_ideal_s01

section
-- module Solutions.Q223_SES.Seshadri_Blowup_UnequalNefNumerics
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.NefNumerics
noncomputable section
open Set Topology

lemma exists_bounded_rational_perturbation {H r w d E B : ℝ}
    (hH : 0 < H) (hw : 0 < w) (hd : 0 < d) (hE : 0 ≤ E)
    (hsquare : H-r*w^2=0) (hneg : d-w*E<0) :
    ∃ δ s : ℚ, 0 < δ ∧ 0 < s ∧ w < (s:ℝ) ∧ (δ:ℝ)*E < w ∧
      0 < H-r*(s:ℝ)^2-2*(δ:ℝ)*(d-(s:ℝ)*E)+(δ:ℝ)^2*B ∧
      0 < H-(δ:ℝ)*d := by
  have hb : 0 < |B|+1 := by positivity
  have hh : 0 < min (H/(d+1)) (min (-(d-w*E)/(|B|+1)) (w/(E+1))) := by
    exact lt_min (div_pos hH (by linarith))
      (lt_min (div_pos (neg_pos.mpr hneg) hb) (div_pos hw (by linarith)))
  obtain ⟨δ,hδ,hδb⟩ := exists_rat_btwn hh
  have hδd := (lt_div_iff₀ (show 0 < d+1 by linarith)).mp
    (hδb.trans_le (min_le_left _ _))
  have hδB := (lt_div_iff₀ hb).mp
    (hδb.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hδE := (lt_div_iff₀ (show 0 < E+1 by linarith)).mp
    (hδb.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hmul := mul_le_mul_of_nonneg_left (neg_abs_le B) hδ.le
  have hfac : 0 < -2*(d-w*E)+(δ:ℝ)*B := by nlinarith
  have hquad : 0 < -2*(δ:ℝ)*(d-w*E)+(δ:ℝ)^2*B := by
    nlinarith only [mul_pos hδ hfac]
  let f : ℝ → ℝ := fun s => H-r*s^2-2*(δ:ℝ)*(d-s*E)+(δ:ℝ)^2*B
  have hfw : 0 < f w := by dsimp [f]; rw [hsquare]; simpa using hquad
  have hopen : IsOpen {s | 0 < f s} := isOpen_lt continuous_const (by fun_prop)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen w hfw
  obtain ⟨s,hsw,hsε⟩ := exists_rat_btwn (show w<w+ε by linarith)
  have hsball : (s:ℝ) ∈ Metric.ball w ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr hsw)]; linarith
  exact ⟨δ,s,by exact_mod_cast hδ,by exact_mod_cast hw.trans hsw,hsw,
    by linarith,hball hsball,by linarith⟩

lemma rational_positive_common_scale (δ s : ℚ) (hδ : 0 < δ) (hs : 0 < s) :
    ∃ a b m : ℕ, 0 < a ∧ 0 < b ∧ 0 < m ∧
      (b:ℝ) = (a:ℝ)*(δ:ℝ) ∧ (m:ℝ) = (a:ℝ)*(s:ℝ) := by
  have hd : 0 < δ.num := Rat.num_pos.mpr hδ
  have ht : 0 < s.num := Rat.num_pos.mpr hs
  refine ⟨δ.den*s.den,δ.num.toNat*s.den,s.num.toNat*δ.den,
    Nat.mul_pos δ.den_pos s.den_pos,
    Nat.mul_pos (by omega) s.den_pos,
    Nat.mul_pos (by omega) δ.den_pos,?_,?_⟩
  · have he : (δ.num.toNat:ℝ) = (δ.num:ℝ) := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg hd.le]
    rw [Nat.cast_mul,Nat.cast_mul,he,Rat.cast_def]
    have hn : (δ.den:ℝ) ≠ 0 := by exact_mod_cast δ.den_ne_zero
    field_simp
  · have he : (s.num.toNat:ℝ) = (s.num:ℝ) := by
      rw [← Int.cast_natCast,Int.toNat_of_nonneg ht.le]
    rw [Nat.cast_mul,Nat.cast_mul,he,Rat.cast_def]
    have hn : (s.den:ℝ) ≠ 0 := by exact_mod_cast s.den_ne_zero
    field_simp

theorem exists_integral_unequal_perturbation {r : ℕ} (μ : Fin r → ℕ)
    (H d Q : ℤ) (hH : 0 < H) (hr : 0 < r) (hd : 0 < d)
    (hneg : (d:ℝ)-Real.sqrt ((H:ℝ)/r)*(∑ i, μ i : ℕ) < 0) :
    ∃ a b m : ℕ, 0 < a ∧ 0 < b ∧ 0 < m ∧
      (a:ℝ)*Real.sqrt ((H:ℝ)/r) < m ∧
      (∀ i, b*μ i ≤ m) ∧ 0 ≤ (a:ℤ)*H-(b:ℤ)*d ∧
      (∑ i, (m-b*μ i)^2 : ℕ) <
        (a:ℤ)^2*H-2*(a:ℤ)*(b:ℤ)*d+(b:ℤ)^2*Q := by
  let w := Real.sqrt ((H:ℝ)/r)
  let E : ℕ := ∑ i, μ i
  let W : ℕ := ∑ i, (μ i)^2
  have hHr : 0 < (H:ℝ) := by exact_mod_cast hH
  have hrr : 0 < (r:ℝ) := by exact_mod_cast hr
  have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hHr hrr)
  have hsquare : (H:ℝ)-(r:ℝ)*w^2=0 := by
    dsimp [w]; rw [Real.sq_sqrt (div_nonneg hHr.le hrr.le)]; field_simp <;> ring
  obtain ⟨δ,s,hδ,hs,hsw,hδE,hquad,hmix⟩ := exists_bounded_rational_perturbation
    hHr hw (show 0 < (d:ℝ) by exact_mod_cast hd) (Nat.cast_nonneg E) hsquare
    (B := (Q:ℝ)-W) hneg
  obtain ⟨a,b,m,ha,hb,hm,eb,em⟩ := rational_positive_common_scale δ s hδ hs
  have har : 0 < (a:ℝ) := by exact_mod_cast ha
  have hbr : 0 < (b:ℝ) := by exact_mod_cast hb
  have hbm (i : Fin r) : b*μ i ≤ m := by
    have hi : μ i ≤ E := Finset.single_le_sum (fun j _ => Nat.zero_le (μ j)) (Finset.mem_univ i)
    have hE' : (δ:ℝ)*(μ i:ℝ) < (s:ℝ) :=
      (mul_le_mul_of_nonneg_left (show (μ i:ℝ) ≤ (E:ℝ) by exact_mod_cast hi) (show 0 ≤ (δ:ℝ) by exact_mod_cast hδ.le)).trans_lt (hδE.trans hsw)
    have H' := mul_lt_mul_of_pos_left hE' har
    rw [← mul_assoc,← eb,← em] at H'
    exact_mod_cast H'.le
  refine ⟨a,b,m,ha,hb,hm,?_,hbm,?_,?_⟩
  · rw [em]; exact mul_lt_mul_of_pos_left hsw har
  · have hh := mul_pos har hmix
    rw [mul_sub,← mul_assoc,← eb] at hh
    exact_mod_cast hh.le
  · have hsum : ((∑ i, (m-b*μ i)^2 : ℕ):ℝ) =
        (r:ℝ)*(m:ℝ)^2-2*(m:ℝ)*(b:ℝ)*E+(b:ℝ)^2*W := by
      simp only [Nat.cast_sum,Nat.cast_pow,Nat.cast_sub (hbm _),Nat.cast_mul]
      calc
        ∑ i : Fin r, ((m:ℝ)-(b:ℝ)*(μ i:ℝ))^2 =
            ∑ i : Fin r, ((m:ℝ)^2-2*(m:ℝ)*(b:ℝ)*(μ i:ℝ)+(b:ℝ)^2*(μ i:ℝ)^2) := by
          apply Finset.sum_congr rfl; intro i hi; ring
        _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,E,W]
    have hquad' := mul_pos (sq_pos_of_pos har) hquad
    have hh : ((∑ i, (m-b*μ i)^2 : ℕ):ℝ) <
        (a:ℝ)^2*H-2*(a:ℝ)*(b:ℝ)*d+(b:ℝ)^2*Q := by
      rw [hsum,eb,em]
      nlinarith only [hquad']
    exact_mod_cast hh

end
end MaximalSeshadri.NefNumerics

end



end OAI
end

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
-- module Solutions.Q223_SES.Seshadri_Configurations_AffinePointParameters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma affineComplexPoint_factor {X : Scheme} (f : X ⟶ complexBase) (U : X.affineOpens)
    (p : Over.mk (𝟙 complexBase) ⟶ Over.mk f)
    (hp : p.left (fieldPoint ℂ) ∈ U.1) :
    ∃ ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ,
      affineComplexPoint f U ρ = p := by
  let := (openScalars f U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hr : Set.range p.left ⊆ Set.range U.2.fromSpec := by
    rintro _ ⟨z,rfl⟩
    change Spec (CommRingCat.of ℂ) at z
    rw [show z = fieldPoint ℂ from Subsingleton.elim _ _,U.2.range_fromSpec]
    exact hp
  let l := IsOpenImmersion.lift U.2.fromSpec p.left hr
  let q := Spec.preimage l
  have hq : Spec.map q ≫ U.2.fromSpec = p.left := by
    rw [Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ hr
  have hg : CommRingCat.ofHom (openScalars f U.1) ≫ q = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,spec_openScalars,← Category.assoc,hq,Spec.map_id]
    exact p.w
  let ρ : Γ(X,U.1) →ₐ[ℂ] ℂ :=
    { q.hom with commutes' := fun c => CategoryTheory.congr_fun hg c }
  refine ⟨ρ,?_⟩
  apply Over.OverMorphism.ext
  exact hq

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCoefficientOrder
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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

variable {X : Scheme.{0}}

lemma affineCoefficient_change {M : X.Modules} (U : X.affineOpens)
    (e f : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) :
    Associated (affineCoefficient U e s) (affineCoefficient U f s) := by
  unfold affineCoefficient
  rw [coefficient_change e f, map_mul]
  exact associated_unit_mul_right _ _ ((frameChange e f).isUnit.map U.1.topIso.hom.hom)

lemma coefficient_postcompose {Y : Scheme.{0}} {M N : Y.Modules}
    (e : M ≅ O Y) (f : N ≅ O Y) (s : O Y ⟶ M) (a : M ⟶ N) :
    coefficient f (s ≫ a) = coefficient e s * endValue (e.inv ≫ a ≫ f.hom) := by
  unfold coefficient
  rw [← endValue_comp]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_ClosedStalk
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X Y : Scheme}

lemma closedImmersion_stalk_kernel (f : Y ⟶ X) [IsClosedImmersion f]
    (U : X.affineOpens) (y : Y) (hy : f y ∈ U.1) :
    RingHom.ker (f.stalkMap y).hom =
      (f.ker.ideal U).map (X.presheaf.germ U.1 (f y) hy).hom := by
  let V := f ⁻¹ᵁ U.1
  have hV : IsAffineOpen V := U.2.preimage f
  let p := U.2.primeIdealOf ⟨f y,hy⟩
  let q := hV.primeIdealOf ⟨y,hy⟩
  let φ := (f.app U.1).hom
  have hφ : Function.Surjective φ := f.app_surjective U.1 U.2
  have hpq : q.asIdeal.comap φ = p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 V hV le_rfl hy
    simpa [Scheme.Hom.appLE, p, q, φ, V] using congrArg PrimeSpectrum.asIdeal h
  have hmon : p.asIdeal.primeCompl.map φ = q.asIdeal.primeCompl := by
    have hc : p.asIdeal.primeCompl = (q.asIdeal.comap φ).primeCompl := by
      ext a
      simp only [Ideal.mem_primeCompl_iff, hpq]
    rw [hc]
    exact q.asIdeal.map_primeCompl_comap_of_surjective φ hφ
  let : Algebra Γ(X,U.1) (X.presheaf.stalk (f y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f y,hy⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk (f y)) p.asIdeal :=
    U.2.isLocalization_stalk ⟨f y,hy⟩
  let : Algebra Γ(Y,V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y,hy⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk y) q.asIdeal :=
    hV.isLocalization_stalk ⟨y,hy⟩
  have he : (f.stalkMap y).hom =
      IsLocalization.map (Y.presheaf.stalk y) φ (hmon.symm ▸ p.asIdeal.primeCompl.le_comap_map) := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    ext a
    change (f.stalkMap y) (X.presheaf.germ U.1 (f y) hy a) = _
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (IsLocalization.map_eq (S := X.presheaf.stalk (f y))
      (Q := Y.presheaf.stalk y) (g := φ)
      (hmon.symm ▸ p.asIdeal.primeCompl.le_comap_map) a).symm
  rw [he, IsLocalization.ker_map (Y.presheaf.stalk y) φ hmon, Scheme.Hom.ker_apply]
  rfl

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_CurveMultiplicity
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma ideal_le_order_power {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) :
    I ≤ IsLocalRing.maximalIdeal R ^ idealOrder I := by
  by_cases h : idealOrder I = 0
  · simp [h]
  · by_contra hn
    have hh : idealOrder I - 1 ∈ {n : ℕ | ¬ I ≤ IsLocalRing.maximalIdeal R^(n+1)} := by
      simpa only [Set.mem_ofPred_eq,Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr h)] using hn
    have := Nat.sInf_le hh
    change idealOrder I ≤ idealOrder I-1 at this
    omega

theorem IntegralCurve.affine_ideal_le_multiplicity (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) :
    C.embedding.ker.ideal U ≤
      (RingHom.ker ρ) ^ curveMultiplicity S C (affineComplexPoint S.structureMap U ρ) := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  change C.embedding.ker.ideal U ≤ (RingHom.ker ρ)^curveMultiplicity S C p
  unfold curveMultiplicity
  split_ifs with h
  · let q := h.choose
    have hq : C.embedding q = p.image := h.choose_spec
    have hpU : p.image ∈ U.1 := by
      have H := Set.mem_range_self (f := U.2.fromSpec) (⟨RingHom.ker ρ, RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
      rw [U.2.range_fromSpec] at H
      exact H
    have hqu : C.embedding q ∈ U.1 := hq ▸ hpU
    let : Algebra Γ(S.scheme,U.1) (S.scheme.presheaf.stalk (C.embedding q)) :=
      TopCat.Presheaf.algebra_section_stalk S.scheme.presheaf ⟨C.embedding q,hqu⟩
    have hp : RingHom.ker ρ = (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).asIdeal := by
      change (⟨RingHom.ker ρ, RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1)).asIdeal = _
      apply congrArg PrimeSpectrum.asIdeal
      apply U.2.fromSpec.isOpenEmbedding.injective
      change p.image = U.2.fromSpec (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩)
      exact hq.symm.trans (congrArg
        (fun morphism : U.1.toScheme ⟶ S.scheme => morphism ⟨C.embedding q,hqu⟩)
        U.2.isoSpec_hom_fromSpec).symm
    let : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨algebraMap ℂ _ z,ρ.commutes z⟩)
    have : (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).asIdeal.IsPrime :=
      (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).isPrime
    let : IsLocalization.AtPrime (S.scheme.presheaf.stalk (C.embedding q)) (RingHom.ker ρ) := by
      change IsLocalization (RingHom.ker ρ).primeCompl _
      have he : (RingHom.ker ρ).primeCompl = (U.2.isoSpec.hom ⟨C.embedding q,hqu⟩).asIdeal.primeCompl := by
        ext a
        simp only [Ideal.mem_primeCompl_iff,hp]
      rw [he]
      exact U.2.isLocalization_stalk ⟨C.embedding q,hqu⟩
    have H := ideal_le_order_power (RingHom.ker (C.embedding.stalkMap q).hom)
    conv_lhs at H => rw [closedImmersion_stalk_kernel C.embedding U q hqu]
    rw [Ideal.map_le_iff_le_comap] at H
    have E := IsLocalization.AtPrime.under_maximalIdeal_pow (RingHom.ker ρ)
      (S.scheme.presheaf.stalk (C.embedding q))
      (idealOrder (RingHom.ker (C.embedding.stalkMap q).hom))
    change C.embedding.ker.ideal U ≤
      (IsLocalRing.maximalIdeal (S.scheme.presheaf.stalk (C.embedding q))^
        idealOrder (RingHom.ker (C.embedding.stalkMap q).hom)).under Γ(S.scheme,U.1) at H
    rw [E] at H
    exact H
  · simp

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ProperGlobalField
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.constantsInDegreeZero_isIso _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_proper _root_.OAI.MaximalSeshadri.Geometry.projectiveSpaceToSpec_separated _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

instance Surface.isProper_structureMap (surface : Surface) : IsProper surface.structureMap := by
  have constants_bijective : Function.Bijective
      (constantsInDegreeZero surface.embeddingDimension) := by
    constructor
    · intro left right equality
      have polynomial_equality : MvPolynomial.C left =
          (MvPolynomial.C right : MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ) :=
        congrArg Subtype.val equality
      exact MvPolynomial.C_injective _ _ polynomial_equality
    · intro polynomial
      have degree_zero : polynomial.val.totalDegree = 0 :=
        (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr polynomial.property
      refine ⟨polynomial.val.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp degree_zero).symm
  let constantsIso := (RingEquiv.ofBijective
    (constantsInDegreeZero surface.embeddingDimension) constants_bijective).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension)) :=
    constantsIso.isIso_hom
  let polynomialRing := MvPolynomial (Fin (surface.embeddingDimension + 1)) ℂ
  let grading := MvPolynomial.homogeneousSubmodule (Fin (surface.embeddingDimension + 1)) ℂ
  let : Algebra ℂ (grading 0) := SetLike.GradeZero.instAlgebra grading
  let : IsScalarTower ℂ (grading 0) polynomialRing := ⟨fun scalar homogeneous polynomial => by
    change (scalar • (homogeneous : polynomialRing)) * polynomial =
      scalar • ((homogeneous : polynomialRing) * polynomial)
    exact smul_mul_assoc scalar (homogeneous : polynomialRing) polynomial⟩
  let : Algebra.FiniteType (grading 0) polynomialRing :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grading 0) polynomialRing
  have projective_proper : IsProper (Proj.toSpecZero grading) :=
    Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat grading
  let : IsIso (Spec.map
      (CommRingCat.ofHom (constantsInDegreeZero surface.embeddingDimension))) := by
    infer_instance
  have : IsProper (projectiveSpaceToSpec surface.embeddingDimension) := by
    unfold projectiveSpaceToSpec
    exact IsProper.stableUnderComposition.comp_mem _ _ projective_proper inferInstance
  rw [← surface.overComplex]
  infer_instance

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

theorem slope_of_quadratic (f : ℕ → ℤ) (q : ℤ)
    (hf : ∀ n, 2*f n = (n : ℤ)*((n : ℤ)-1)*q +
      2*(n : ℤ)*(f 1-f 0)+2*f 0)
    (a : ℕ) (d c : ℤ) (ha : ∀ n, f (n+a)-f n = (n : ℤ)*d+c) :
    d = (a : ℤ)*q := by
  have H₀ := ha 0
  have H₁ := ha 1
  have F₀ := hf a
  have F₁ := hf (a+1)
  simp only [Nat.cast_zero,zero_mul,zero_add] at H₀
  rw [Nat.add_comm 1 a] at H₁
  push_cast at H₁ F₁
  nlinarith

end MaximalSeshadri.EulerNumerics

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceQuadraticEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.isProper_structureMap _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

theorem generated_curveDegree_eq_power_selfIntersection (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (d : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(S.scheme,⊤))
    (s : σ → (O S.scheme ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (hd : topologicalKrullDim (sectionIdeal k s hs v).subscheme = 1) :
    let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
    curveDegree S L C = (d : ℤ)*selfIntersection S L := by
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
      (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hd⟩
  let f (n : ℕ) := eulerCharacteristic S.structureMap 2 (L.pow n).sheaf
  apply EulerNumerics.slope_of_quadratic f (selfIntersection S L) _ d _
    ((d : ℤ)*curveDegree S L C + eulerCharacteristic (C.embedding ≫ S.structureMap) 1 (O C.scheme))
  · intro n
    have H := generated_power_euler_difference_s01 S L hL L d k s hs v hne hd n
    change f (n+d)-f n = _ at H
    push_cast at H
    linarith
  · intro n
    have H := S.power_euler_quadratic L hL n
    rw [← S.euler_power_one L] at H
    exact H

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfacePositiveSquare
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.isProper_structureMap _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

theorem Surface.selfIntersection_pos (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple) :
    0 < selfIntersection S L := by
  obtain ⟨d,hd,-,N,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have hp := C.ample_degree_positive_s01 S L hL
  have he := generated_curveDegree_eq_power_selfIntersection S L hL d k s hs v hne hC
  change curveDegree S L C = (d : ℤ)*selfIntersection S L at he
  rw [he] at hp
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  nlinarith

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_IdealEquation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma presented_frame_equation (I : X.IdealSheafData) (J : LineBundle X)
    (ι : J.sheaf ⟶ O X) (h : PresentsPullbackIdeal I (𝟙 X) J ι)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    I.ideal U = Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  have H : ((I.comap (𝟙 X)).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← restricted_image_on_chart J ι h U.1.ι ⟨⊤,isAffineOpen_top _⟩ U
        (by simpa only [Scheme.Opens.ι_image_top,Scheme.Hom.id_preimage] using
          (le_rfl : U.1 ≤ U.1))]
    ext r
    change (∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) s = r) ↔
      ∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (op ⊤) s,?_⟩
      have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩
      exact ⟨e.inv.val.app (op ⊤) s,hs⟩
  rw [Scheme.IdealSheafData.comap_id,IdealPullback.comap_ι_top] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

end
end MaximalSeshadri.InvertibleLocal

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_TensorInclusion
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma tensor_inclusion_framed (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.Opens) (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame J M U e f).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (tensorInclusion J M ι) ≫ f.hom =
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) ≫ (tensorUnitTwist M U f).inv := by
  let restrictionFunctor : X.Modules ⥤ U.toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι
  let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  let sourceUnit : moduleTensor X (O X) M.sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let targetUnit : moduleTensor U.toScheme (O U.toScheme) (O U.toScheme) ≅
      O U.toScheme := moduleTensorUnit (O U.toScheme)
  let sourceRestriction : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj J.sheaf)
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U J.sheaf M.sheaf
  let targetRestriction : restrictionFunctor.obj (moduleTensor X (O X) M.sheaf) ≅
      moduleTensor U.toScheme (restrictionFunctor.obj (O X))
        (restrictionFunctor.obj M.sheaf) := moduleTensorRestrict U (O X) M.sheaf
  let tensorMap : moduleTensor X J.sheaf M.sheaf ⟶ moduleTensor X (O X) M.sheaf :=
    moduleTensorMap ι (𝟙 M.sheaf)
  let inclusion : moduleTensor X J.sheaf M.sheaf ⟶ M.sheaf := tensorInclusion J M ι
  let frame : restrictionFunctor.obj (moduleTensor X J.sheaf M.sheaf) ≅
      O U.toScheme := tensorFrame J M U e f
  let twist : O U.toScheme ≅ O U.toScheme := tensorUnitTwist M U f
  let scalar : O U.toScheme ⟶ O U.toScheme :=
    e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom
  have inclusion_eq : inclusion = tensorMap ≫ sourceUnit.hom := rfl
  have naturality : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
      sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
        (𝟙 (restrictionFunctor.obj M.sheaf)) := by
    have naturality' : restrictionFunctor.map tensorMap ≫ targetRestriction.hom =
        sourceRestriction.hom ≫ moduleTensorMap (restrictionFunctor.map ι)
          (restrictionFunctor.map (𝟙 M.sheaf)) :=
      moduleTensorRestrict_natural U ι (𝟙 M.sheaf)
    simpa only [restrictionFunctor.map_id] using naturality'
  change frame.inv ≫ restrictionFunctor.map inclusion ≫ f.hom = scalar ≫ twist.inv
  apply (cancel_mono twist.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have frame_inv : frame.inv =
      (targetUnit.inv ≫ moduleTensorMap (X := U.toScheme) e.inv f.inv) ≫
        sourceRestriction.inv := rfl
  have twist_hom : twist.hom = f.inv ≫
      restrictionFunctor.map sourceUnit.inv ≫ targetRestriction.hom ≫
      moduleTensorMap unitRestriction.hom f.hom ≫ targetUnit.hom := rfl
  rw [frame_inv, twist_hom]
  rw [inclusion_eq, restrictionFunctor.map_comp]
  simp only [Category.assoc, f.hom_inv_id_assoc]
  rw [← restrictionFunctor.map_comp_assoc sourceUnit.hom sourceUnit.inv,
    sourceUnit.hom_inv_id,
    restrictionFunctor.map_id, Category.id_comp]
  rw [← Category.assoc (restrictionFunctor.map tensorMap), naturality]
  simp only [Category.assoc, sourceRestriction.inv_hom_id_assoc]
  rw [← Category.assoc (moduleTensorMap (X := U.toScheme) e.inv f.inv),
    ← moduleTensorMap_comp (X := U.toScheme), Category.comp_id,
    ← Category.assoc (moduleTensorMap (X := U.toScheme) _ _),
    ← moduleTensorMap_comp (X := U.toScheme), f.inv_hom_id]
  have hscalar : moduleTensorMap scalar (𝟙 (O U.toScheme)) ≫ targetUnit.hom =
      targetUnit.hom ≫ scalar := by
    exact (moduleTensorUnit_scalar (X := U.toScheme) scalar (𝟙 (O U.toScheme))).trans
      (congrArg (fun morphism : O U.toScheme ⟶ O U.toScheme =>
        targetUnit.hom ≫ morphism) (Category.comp_id scalar))
  rw [Category.assoc e.inv, hscalar, targetUnit.inv_hom_id_assoc]

theorem tensorInclusion_mono (J M : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι] :
    Mono (tensorInclusion J M ι) := by
  apply ModuleLocal.mono_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  have : CategoryTheory.Limits.PreservesFiniteLimits
      (Scheme.Modules.restrictFunctor U.1.ι) := by
    have : CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.restrictFunctor U.1.ι ⋙ Scheme.Modules.toPresheaf U.1.toScheme) := by
      change CategoryTheory.Limits.PreservesFiniteLimits
        (Scheme.Modules.toPresheaf X ⋙ (Functor.whiskeringLeft _ _ _).obj U.1.ι.opensFunctor.op)
      have : CategoryTheory.Limits.PreservesFiniteLimits
          (Scheme.Modules.toPresheaf X) := inferInstance
      have : CategoryTheory.Limits.PreservesFiniteLimits
          ((Functor.whiskeringLeft _ _ Ab).obj U.1.ι.opensFunctor.op) := inferInstance
      exact CategoryTheory.Limits.comp_preservesFiniteLimits _ _
    exact CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves _
      (Scheme.Modules.toPresheaf U.1.toScheme)
  have hm : Mono ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) := by
    let restrictionFunctor : X.Modules ⥤ U.1.toScheme.Modules :=
      Scheme.Modules.restrictFunctor U.1.ι
    let unitRestriction : restrictionFunctor.obj (O X) ≅ O U.1.toScheme :=
      Scheme.Modules.restrictUnitIso U.1.ι
    let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
    have restricted_mono : Mono (restrictionFunctor.map ι) := inferInstance
    have scalar_mono : Mono ((e.inv ≫ restrictionFunctor.map ι ≫ unitRestriction.hom) ≫
        twist.inv) := inferInstance
    exact (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme => Mono morphism)
      (tensor_inclusion_framed J M ι U.1 e f)).mpr scalar_mono
  exact (mono_comp_iff_of_mono _ f.hom).mp
    ((mono_comp_iff_of_isIso (tensorFrame J M U.1 e f).inv _).mp hm)

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_CurveIdealDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.isProper_structureMap _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

theorem mixedEuler_tensor_right (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M N : LineBundle S.scheme) :
    mixedEuler S L (M.tensor N) = mixedEuler S L M + mixedEuler S L N := by
  classical
  obtain ⟨d,hd,-,n,s,hs,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  have := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k s hs v).subscheme,
    (sectionIdeal k s hs v).subschemeι,inferInstance,inferInstance,hC⟩
  have h₁ := generated_curveDegree_eq_mixedEuler_s01 S L hL M d k s hs v hne hC
  have h₂ := generated_curveDegree_eq_mixedEuler_s01 S L hL N d k s hs v hne hC
  have h₃ := generated_curveDegree_eq_mixedEuler_s01 S L hL (M.tensor N) d k s hs v hne hC
  change curveDegree S M C = (d : ℤ)*mixedEuler S L M at h₁
  change curveDegree S N C = (d : ℤ)*mixedEuler S L N at h₂
  change curveDegree S (M.tensor N) C = (d : ℤ)*mixedEuler S L (M.tensor N) at h₃
  rw [curveDegree_tensor_s01 S L hL,h₁,h₂] at h₃
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply mul_left_cancel₀ hd'
  rw [← h₃]
  ring

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_BivariateSurfaceEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.isProper_structureMap _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

lemma mixedEuler_self (S : Surface) (L : LineBundle S.scheme) :
    mixedEuler S L L = selfIntersection S L := by
  have h := eulerCharacteristic_iso S.structureMap
    (moduleTensorIso (Iso.refl L.sheaf) (moduleTensorRightUnit L.sheaf)) 2
  change eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf =
    eulerCharacteristic S.structureMap 2 (L.tensor L).sheaf at h
  unfold mixedEuler selfIntersection
  change _ = eulerCharacteristic S.structureMap 2 (L.pow 2).sheaf -
    2*eulerCharacteristic S.structureMap 2 L.sheaf +
      eulerCharacteristic S.structureMap 2 (O S.scheme)
  rw [h]
  ring

lemma mixedEuler_twist_pow (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (J : LineBundle S.scheme) (a b : ℕ) :
    mixedEuler S L ((L.pow a).tensor (J.pow b)) =
      (a : ℤ)*selfIntersection S L + (b : ℤ)*mixedEuler S L J := by
  rw [mixedEuler_tensor_right S L hL,mixedEuler_pow_right_s01 S L hL,
    mixedEuler_pow_right_s01 S L hL,mixedEuler_self]

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_PowerIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma idealPowerInclusion_mono (J : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι]
    (n : ℕ) : Mono (idealPowerInclusion J ι n) := by
  induction n with
  | zero => change Mono (𝟙 (O X)); infer_instance
  | succ n ih =>
    let := ih
    let := tensorInclusion_mono J (J.pow n) ι
    change Mono (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)
    infer_instance

lemma affineCoefficient_map {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) (a : M ⟶ N) :
    affineCoefficient U f (s ≫ a) =
      affineCoefficient U e s * affineMapCoefficient U e f a := by
  unfold affineCoefficient affineMapCoefficient
  rw [← map_mul]
  congr 1
  rw [show restrictSection U.1.ι (s ≫ a) = restrictSection U.1.ι s ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map a by
        exact (congrArg (fun morphism =>
          (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫ morphism)
          ((Scheme.Modules.restrictFunctor U.1.ι).map_comp s a)).trans
          (Category.assoc _ _ _).symm]
  exact coefficient_postcompose e f _ _

lemma affineCoefficient_map_order {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) (a : M ⟶ N)
    (I : Ideal Γ(X,U.1)) (u v : ℕ)
    (hs : affineCoefficient U e s ∈ I^u)
    (ha : Ideal.span {affineMapCoefficient U e f a} ≤ I^v) :
    affineCoefficient U f (s ≫ a) ∈ I^(u+v) := by
  rw [affineCoefficient_map U e, pow_add]
  exact Ideal.mul_mem_mul hs (ha (Ideal.subset_span (Set.mem_singleton _)))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_TwistedIdealPower
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.ratioOn_full _root_.OAI.MaximalSeshadri.Projective.ratioOn_self _root_.OAI.MaximalSeshadri.Projective.ratioUnitOn_val _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames

variable {X : Scheme.{0}}

lemma twistedIdealPowerInclusion_mono (L J : LineBundle X) (ι : J.sheaf ⟶ O X)
    [Mono ι] (a b n : ℕ) : Mono (twistedIdealPowerInclusion L J ι a b n) := by
  let := idealPowerInclusion_mono J ι (b*n)
  let := tensorInclusion_mono (J.pow (b*n)) (L.pow (a*n)) (idealPowerInclusion J ι (b*n))
  dsimp [twistedIdealPowerInclusion]
  infer_instance

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineOrderRestriction
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma affineCoefficient_restrict {M : X.Modules} (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) (s : O X ⟶ M) :
    affineCoefficient V (frameOnSmaller e V.1 h) s =
      X.presheaf.map (homOfLE h).op (affineCoefficient U e s) := by
  unfold affineCoefficient
  rw [frameOnSmaller_coefficient]
  change ((X.homOfLE h).appTop ≫ V.1.topIso.hom) _ =
    (U.1.topIso.hom ≫ X.presheaf.map (homOfLE h).op) _
  exact congrArg (fun restriction : Γ(U.1.toScheme, ⊤) ⟶ Γ(X, V.1) =>
    restriction (coefficient e (restrictSection U.1.ι s)))
    (X.restrictFunctorΓ.hom.naturality (homOfLE h).op)

lemma affine_point_germ_power (g : X ⟶ complexBase) (U : X.affineOpens)
    (ρ : letI := (openScalars g U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ)
    (x : X) (hx : x ∈ U.1)
    (he : (affineComplexPoint g U ρ).left (fieldPoint ℂ) = x) (n : ℕ) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n).comap
      (X.presheaf.germ U.1 x hx).hom = (RingHom.ker ρ)^n := by
  let := (openScalars g U.1).toAlgebra
  let : Algebra Γ(X,U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hp : RingHom.ker ρ = (U.2.primeIdealOf ⟨x,hx⟩).asIdeal := by
    change (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(X,U.1)).asIdeal = _
    apply congrArg PrimeSpectrum.asIdeal
    apply U.2.fromSpec.isOpenEmbedding.injective
    change (affineComplexPoint g U ρ).left (fieldPoint ℂ) =
      U.2.fromSpec (U.2.primeIdealOf ⟨x,hx⟩)
    exact he.trans (U.2.fromSpec_primeIdealOf ⟨x,hx⟩).symm
  let : (RingHom.ker ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective _
    (fun z => ⟨algebraMap ℂ _ z,ρ.commutes z⟩)
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker ρ) := by
    change IsLocalization (RingHom.ker ρ).primeCompl _
    have hpc : (RingHom.ker ρ).primeCompl = (U.2.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl := by
      ext element; simp only [Ideal.mem_primeCompl_iff,hp]
    rw [hpc]
    exact U.2.isLocalization_stalk ⟨x,hx⟩
  exact IsLocalization.AtPrime.under_maximalIdeal_pow (RingHom.ker ρ) (X.presheaf.stalk x) n

lemma affineCoefficient_order_restrict_iff (g : X ⟶ complexBase)
    {M : X.Modules} (U V : X.affineOpens) (h : V.1 ≤ U.1)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict V.1.ι ≅ O V.1.toScheme)
    (ρ : letI := (openScalars g U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ)
    (σ : letI := (openScalars g V.1).toAlgebra; Γ(X,V.1) →ₐ[ℂ] ℂ)
    (he : affineComplexPoint g U ρ = affineComplexPoint g V σ)
    (s : O X ⟶ M) (n : ℕ) :
    affineCoefficient U e s ∈ (RingHom.ker ρ)^n ↔
      affineCoefficient V f s ∈ (RingHom.ker σ)^n := by
  let x := (affineComplexPoint g V σ).left (fieldPoint ℂ)
  have hx : x ∈ V.1 := by
    have H := Set.mem_range_self (f := V.2.fromSpec)
      (⟨RingHom.ker σ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(X,V.1))
    rw [V.2.range_fromSpec] at H
    exact H
  have hU := affine_point_germ_power g U ρ x (h hx)
    (congrArg (fun p => p.left (fieldPoint ℂ)) he) n
  have hV := affine_point_germ_power g V σ x hx rfl n
  have hass := affineCoefficient_change V (frameOnSmaller e V.1 h) f s
  rw [← Ideal.mem_iff_of_associated hass]
  rw [affineCoefficient_restrict,← hU,← hV]
  change (X.presheaf.germ U.1 x (h hx)) (affineCoefficient U e s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n ↔
    (X.presheaf.germ V.1 x hx)
      (X.presheaf.map (homOfLE h).op (affineCoefficient U e s)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)^n
  rw [TopCat.Presheaf.germ_res_apply]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Interpolation_AllCurveLowerBound
attribute [-instance] _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem curve_lower_of_homogeneous_section_test_s01_oai (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) {r : ℕ} (hr : 0 < r)
    (p : Configuration S r) (U : S.scheme.affineOpens)
    (eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (htest : ∀ k m : ℕ, 0 < k → 0 < m →
      (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
      ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
          Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
        (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
        ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
          (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
            (RingHom.ker (ρ i))^m) → s = 0)
    (C : IntegralCurve S) :
    Real.sqrt ((selfIntersection S L:ℝ)/r) * (totalMultiplicity S r C p:ℝ) ≤
      (curveDegree S L C:ℝ) := by
  classical
  by_contra hc
  have hneg : (curveDegree S L C:ℝ)-Real.sqrt ((selfIntersection S L:ℝ)/r)*
      (∑ i, curveMultiplicity S C (p.val i):ℕ) < 0 := by
    change ¬ _ ≤ _ at hc
    change _ - _ * (totalMultiplicity S r C p:ℝ) < 0
    linarith
  obtain ⟨J,ι,hJ⟩ := C.invertible_ideal_s01 S
  have hmono : Mono (C := S.scheme.Modules) (X := J.sheaf)
      (Y := structureSheaf S.scheme) ι := hJ.1
  let μ : Fin r → ℕ := fun i => curveMultiplicity S C (p.val i)
  obtain ⟨a,b,m,ha,hb,hm,ham,hbm,hmix,hquad⟩ :=
    NefNumerics.exists_integral_unequal_perturbation μ (selfIntersection S L)
      (curveDegree S L C) (selfIntersection S J) (S.selfIntersection_pos L hL)
        hr (C.ample_degree_positive_s01 S L hL) hneg
  let M := (L.pow a).tensor (J.pow b)
  have hj := C.ideal_mixed_degree_s01 S L hL J ι hJ L
  have hMM : 0 ≤ mixedEuler S L M := by
    dsimp [M]
    rw [mixedEuler_twist_pow S L hL,hj]
    linarith
  have hMQ : (∑ i, (m-b*μ i)^2:ℕ) < selfIntersection S M := by
    dsimp [M]
    rw [S.selfIntersection_twist_pow_s01 L hL,hj]
    nlinarith only [hquad]
  obtain ⟨ρ,hρ,-⟩ := htest a m ha hm ham
  have hpU (i : Fin r) : (p.val i).image ∈ U.1 := by
    rw [← hρ i]
    have H := Set.mem_range_self (f := U.2.fromSpec)
      (⟨RingHom.ker (ρ i),RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
    rw [U.2.range_fromSpec] at H
    exact H
  choose V hpV hVU eJ t het using fun i => S.etale_line_frame_inside_s01 J U.1
    (p.val i).image (hpU i)
  choose σ hσ using fun i => affineComplexPoint_factor S.structureMap (V i) (p.val i) (hpV i)
  obtain ⟨N,hN,hEff⟩ := S.eventually_effective_with_arbitrary_jet_frames_s01 L hL M hMM
    (fun i => m-b*μ i) hMQ V t het σ
  let f (i : Fin r) : (L.pow (a*N)).sheaf.restrict (V i).1.ι ≅ O (V i).1.toScheme :=
    frameOnSmaller (localPowerFrame U.1 eL (a*N)) (V i).1 (hVU i)
  let e (i : Fin r) : (M.pow N).sheaf.restrict (V i).1.ι ≅ O (V i).1.toScheme :=
    twistedIdealPowerFrame L J a b N (V i).1 (eJ i) (f i)
  obtain ⟨s,hs,horders⟩ := hEff N le_rfl e
  let g := twistedIdealPowerInclusion L J ι a b N
  have : Mono g := @twistedIdealPowerInclusion_mono S.scheme L J ι hmono a b N
  have hnonzero : s ≫ g ≠ 0 := by
    intro hh
    apply hs
    apply (cancel_mono g).mp
    simpa using hh
  have hjet (i : Fin r) : affineCoefficient (V i) (f i) (s ≫ g) ∈
      (RingHom.ker (σ i))^(N*m) := by
    have hideal := C.affine_ideal_le_multiplicity S (V i) (σ i)
    rw [hσ i] at hideal
    have hmap : Ideal.span {affineMapCoefficient (V i) (e i) (f i) g} ≤
        (RingHom.ker (σ i))^(b*N*μ i) := by
      refine (twistedIdealPowerInclusion_ideal_s01 L J ι a b N (V i) (eJ i) (f i)).le.trans ?_
      refine (congrArg (fun ideal : Ideal Γ(S.scheme, (V i).1) => ideal^(b*N))
        (InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ
          (V i) (eJ i))).symm.le.trans ?_
      have HH := pow_le_pow_left' hideal (b*N)
      rw [← pow_mul] at HH
      have heq : curveMultiplicity S C (p.val i)*(b*N) = b*N*μ i := by dsimp [μ] <;> ring
      rw [heq] at HH
      exact HH
    have H := affineCoefficient_map_order (V i) (e i) (f i) s g
      (RingHom.ker (σ i)) (N*(m-b*μ i)) (b*N*μ i) (horders i) hmap
    have heq : N*(m-b*μ i)+b*N*μ i = N*m := by
      rw [show b*N*μ i = N*(b*μ i) by ring,← Nat.mul_add,Nat.sub_add_cancel (hbm i)]
    rwa [heq] at H
  have hkm : ((a*N:ℕ):ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < ((N*m:ℕ):ℝ) := by
    have H := mul_lt_mul_of_pos_left ham (show (0:ℝ) < N by exact_mod_cast hN)
    push_cast
    nlinarith only [H]
  obtain ⟨ρ',hρ',hsep⟩ := htest (a*N) (N*m) (Nat.mul_pos ha hN)
    (Nat.mul_pos hN hm) hkm
  apply hnonzero
  apply hsep
  intro i
  exact (affineCoefficient_order_restrict_iff S.structureMap U (V i) (hVU i)
    (localPowerFrame U.1 eL (a*N)) (f i) (ρ' i) (σ i)
      ((hρ' i).trans (hσ i).symm) (s ≫ g) (N*m)).mpr (hjet i)

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01_oai := @OAI.MaximalSeshadri.Geometry.curve_lower_of_homogeneous_section_test_s01_oai

-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:32.32312+00:00
-- url     : https://prove2.me/submissions/7ecf8691-46bd-4e58-a038-bda191eb27d3

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H0_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H1_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_exists_finite_projection_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_lineBundle_cohomology_zero_above_two_s01

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_LaurentPlane
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section

theorem finite_of_clearing {P R N M : Type*} [CommRing P] [CommRing R]
    [AddCommGroup N] [AddCommGroup M] [Module P N] [Module R M]
    [Module.Finite P N] (e : P →+* R) (f : N →+ M)
    (hf : ∀ p n, f (p • n) = e p • f n)
    (hclear : ∀ m : M, ∃ r : R, ∃ n : N, m = r • f n) : Module.Finite R M := by
  classical
  obtain ⟨d,s,hs⟩ := Module.Finite.exists_fin (R := P) (M := N)
  let V := Submodule.span R (Set.range (fun i => f (s i)))
  have image (n : N) : f n ∈ V := by
    have hn : n ∈ Submodule.span P (Set.range s) := hs ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem n hn =>
      obtain ⟨i,rfl⟩ := hn
      exact Submodule.subset_span ⟨i,rfl⟩
    | zero => simp
    | add n m hn hm ih ih' => simpa only [map_add] using V.add_mem ih ih'
    | smul p n hn ih => rw [hf]; exact V.smul_mem (e p) ih
  have hV : V = ⊤ := by
    apply top_unique
    intro m hm
    obtain ⟨r,n,rfl⟩ := hclear m
    exact V.smul_mem r (image n)
  exact Module.Finite.of_fg_top (hV ▸ Submodule.fg_span (Set.finite_range _))

variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module (Ring K) M] [IsScalarTower K (Ring K) M]

theorem quotient_finite [Module.Finite (Ring K) M]
    (A B C : Submodule K M)
    (hA : ∀ z : ℤ × ℤ, 0 ≤ z.2 → ∀ x ∈ A, T (K := K) z • x ∈ A)
    (hB : ∀ z : ℤ × ℤ, 0 ≤ z.1 → ∀ x ∈ B, T (K := K) z • x ∈ B)
    (hC : ∀ z : ℤ × ℤ, z.1 + z.2 ≤ 0 → ∀ x ∈ C, T (K := K) z • x ∈ C)
    (locA : ∀ x : M, ∃ n : ℕ, T (K := K) (0,(n : ℤ)) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, T (K := K) ((n : ℤ),0) • x ∈ B)
    (locC : ∀ x : M, ∃ n : ℕ, T (K := K) (0,-(n : ℤ)) • x ∈ C) :
    Module.Finite K (M ⧸ ((A ⊔ B) ⊔ C)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := Ring K) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  choose c hc using fun i : Fin n => locC (s i)
  let Q := (A ⊔ B) ⊔ C
  let q := Q.mkQ
  let J := (i : Fin n) ×
    (↥(Finset.Icc (-(c i : ℤ) - a i) (b i : ℤ)) ×
     ↥(Finset.Icc (-(c i : ℤ) - b i) (a i : ℤ)))
  let g : J → M ⧸ Q := fun v => q (T (K := K) (v.2.1.val, v.2.2.val) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ × ℤ) : q (T (K := K) z • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z.2
    · have he : z = (z.1, z.2 - a i) + (0, (a i : ℤ)) := by ext <;> simp
      have hm : T (K := K) z • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact hA _ (by dsimp; omega) _ (ha i)
      have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
        ((show A ≤ Q from le_sup_of_le_left le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : (b i : ℤ) ≤ z.1
      · have he : z = (z.1 - b i, z.2) + ((b i : ℤ), 0) := by ext <;> simp
        have hm : T (K := K) z • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact hB _ (by dsimp; omega) _ (hb i)
        have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
          ((show B ≤ Q from le_sup_of_le_left le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · by_cases hzC : z.1 + z.2 ≤ -(c i : ℤ)
        · have he : z = (z.1, z.2 + c i) + (0, -(c i : ℤ)) := by ext <;> simp
          have hm : T (K := K) z • s i ∈ C := by
            rw [he, T_add, mul_smul]
            exact hC _ (by dsimp; omega) _ (hc i)
          have hq : q (T (K := K) z • s i) = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr
            ((show C ≤ Q from le_sup_right) hm)
          rw [hq]; exact W.zero_mem
        · exact Submodule.subset_span
            ⟨⟨i, ⟨⟨z.1, Finset.mem_Icc.mpr (by omega)⟩,
                   ⟨z.2, Finset.mem_Icc.mpr (by omega)⟩⟩⟩, rfl⟩
  have scalar_monomial (i : Fin n) (p : Ring K) : q (p • s i) ∈ W := by
    induction p using AddMonoidAlgebra.induction_on with
    | of z => exact monomial i z
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | smul d p hp =>
      rw [smul_assoc, map_smul]
      exact W.smul_mem d hp
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m, rfl⟩ := Q.mkQ_surjective x
    have hm : m ∈ Submodule.span (Ring K) (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : Ring K, q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro p; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneChartAlgebra
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.LaurentPlane
noncomputable section
variable {K A R : Type*} [CommRing K] [CommRing A] [CommRing R]

lemma map_unit_zpow (f : A →+* R) (a : Aˣ) (n : ℤ) :
    f (a ^ n : Aˣ) = ((Units.map f a) ^ n : Rˣ) := by
  change (((Units.map f.toMonoidHom) (a ^ n) : Rˣ) : R) = _
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) a n)

lemma lift_cone_left (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u) (hy : f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.2) :
    f (↑(x ^ z.1) * y ^ z.2.toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.2 = (z.2.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_right (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : A) (y : Aˣ) (hx : f x = u) (hy : Units.map f y = v)
    (z : ℤ × ℤ) (hz : 0 ≤ z.1) :
    f (x ^ z.1.toNat * ↑(y ^ z.2)) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T, Units.val_mul]
  have he : z.1 = (z.1.toNat : ℤ) := (Int.toNat_of_nonneg hz).symm
  rw [he, zpow_natCast, Units.val_pow_eq_pow_val]
  simp [max_eq_left hz]

lemma lift_cone_top (k : K →+* R) (u v : Rˣ) (f : A →+* R)
    (x : Aˣ) (y : A) (hx : Units.map f x = u * v⁻¹) (hy : f y = ↑(v⁻¹))
    (z : ℤ × ℤ) (hz : z.1 + z.2 ≤ 0) :
    f (↑(x ^ z.1) * y ^ (-(z.1 + z.2)).toNat) = eval k u v (T z) := by
  rw [map_mul, map_pow, map_unit_zpow, hx, hy, eval_T]
  have hn : ((-(z.1 + z.2)).toNat : ℤ) = -(z.1 + z.2) :=
    Int.toNat_of_nonneg (by omega)
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, hn, ← Units.val_mul]
  congr 1
  rw [mul_zpow, mul_assoc, ← zpow_add]
  have he : z.1 + -(z.1 + z.2) = -z.2 := by omega
  rw [he]
  simp

theorem finite_laurent_of_chart {P N M : Type*} [CommRing P]
    [AddCommGroup N] [AddCommGroup M] [Module P N] [Module R M]
    [Module.Finite P N] (k : K →+* R) (u v : Rˣ)
    (e : P →+* Ring K) (F : N →+ M)
    (hF : ∀ p n, F (p • n) = eval k u v (e p) • F n)
    (hclear : ∀ m : M, ∃ d : ℕ, ∃ n : N, (↑u * ↑v : R)^d • m = F n) :
    letI := Module.compHom M (eval k u v)
    Module.Finite (Ring K) M := by
  let := Module.compHom M (eval k u v)
  apply finite_of_clearing e F hF
  intro m
  obtain ⟨d,n,hn⟩ := hclear m
  refine ⟨T (-(d : ℤ),-(d : ℤ)),n,?_⟩
  change m = eval k u v (T (-(d : ℤ),-(d : ℤ))) • F n
  rw [eval_T, ← hn, ← mul_smul]
  have he : ↑(u ^ (-(d : ℤ)) * v ^ (-(d : ℤ))) * (↑u * ↑v : R)^d = 1 := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    suffices u ^ (-(d : ℤ)) * v ^ (-(d : ℤ)) * (u * v)^d = 1 by
      exact congrArg Units.val this
    rw [← mul_zpow, zpow_neg, zpow_natCast]
    exact inv_mul_cancel _
  rw [he, one_smul]

end
end MaximalSeshadri.LaurentPlane

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_AffineLineFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

lemma finite_sections_of_frame {X : Scheme.{0}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) : Module.Finite Γ(X,U) Γ(M,U) := by
  let e' : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := overFrame e
  let j : Over U := Over.mk (𝟙 U)
  let f : Γ(X,U) →ₗ[Γ(X,U)] Γ(M,U) := (e'.inv.val.app (op j)).hom
  have hf : Function.Surjective f := (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation (X.ringCatSheaf.over U) (op j)).mapIso e').inv).surjective
  exact Module.Finite.of_surjective f hf

set_option backward.isDefEq.respectTransparency.types false in
theorem LineBundle.spec_sections_finite {R : CommRingCat.{0}} (L : LineBundle (Spec R)) :
    Module.Finite R ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | Nonempty (L.sheaf.restrict (D r).ι ≅
    structureSheaf (D r).toScheme)}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨⟨MaximalSeshadri.InvertibleLocal.frameOfLE L.sheaf hrU e⟩,hxr⟩⟩
  let M := ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op ⊤))
  let (r : t) : Module R Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Module R
      ((modulesSpecToSheaf.obj L.sheaf).obj.obj (op (PrimeSpectrum.basicOpen r.val)))
  let (r : t) : Module Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    (L.sheaf.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : Algebra R Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| Algebra R
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
  have (r : t) : IsLocalization.Away r.val Γ(Spec R, PrimeSpectrum.basicOpen r.val) :=
    inferInstanceAs <| IsLocalization.Away r.val
      ((Spec.structureSheaf R).presheaf.obj (op (PrimeSpectrum.basicOpen r.val)))
  have (r : t) : IsScalarTower R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    IsScalarTower.of_compHom R Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val)
  let f (r : t) : M →ₗ[R] Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    ((modulesSpecToSheaf.obj L.sheaf).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing L.sheaf).mp inferInstance
  have (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite Γ(Spec R, PrimeSpectrum.basicOpen r.val)
      Γ(L.sheaf, PrimeSpectrum.basicOpen r.val) :=
    finite_sections_of_frame L.sheaf _ r.property.some
  exact Module.Finite.of_localizationSpan' t ht f hfin

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_AffineBundleFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem LineBundle.affine_sections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) Γ(L.sheaf,⊤) := by
  let f := X.isoSpec.inv
  let J := L.restrict f
  let R := Γ(X,⊤)
  let M := (modulesSpecToSheaf.obj J.sheaf).obj.obj (op ⊤)
  let : Module.Finite R M := J.spec_sections_finite
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : M →ₛₗ[σ] Γ(L.sheaf,f ''ᵁ ⊤) := {
    toFun := (L.sheaf.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineLocalizing
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    have := hf
    have := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

theorem LineBundle.affine_openSections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) (OpenSections L.sheaf ⊤) := by
  let : Module Γ(X,⊤) Γ(L.sheaf,⊤) := (L.sheaf.val.obj (op ⊤)).isModule
  have := L.affine_sections_finite
  exact Module.Finite.of_surjective (openTopSections L.sheaf).symm.toLinearMap
    (openTopSections L.sheaf).symm.surjective

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_RestrictionLocalization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

theorem openImmersionTop_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    IsLocalizedModule.Away t (openImmersionTop M f) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have he : X.basicOpen t = f ''ᵁ (⊤ : Y.Opens) :=
    hf.symm.trans (Scheme.Hom.image_top_eq_opensRange f).symm
  let e := (openSectionsCongr M he).trans (restrictedOpenSections M f ⊤).symm
  let g := openRestriction M (X.basicOpen_le t)
  have : IsLocalizedModule.Away t g := affine_openRestriction_localize M t
  have h := IsLocalizedModule.of_linearEquiv (.powers t) g e
  have hp : e.toLinearMap ∘ₗ g = openImmersionTop M f := by
    ext m
    change (restrictedOpenSections M f ⊤).symm
      (openSectionsCongr M he (openRestriction M (X.basicOpen_le t) m)) = _
    rw [openSectionsCongr_restriction]
    rfl
  rwa [hp] at h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_ChartModuleMap
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PlaneModules
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

theorem laurentTower (k : K →+* Γ(Y,⊤)) (u v : Γ(Y,⊤)ˣ) (N : Y.Modules) :
    letI := laurentModule k u v N
    IsScalarTower K (LaurentPlane.Ring K) (Sections k N ⊤) := by
  let := laurentModule k u v N
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change LaurentPlane.eval k u v (algebraMap K (LaurentPlane.Ring K) r) •
    (m : OpenSections N ⊤) = k r • (m : OpenSections N ⊤)
  rw [LaurentPlane.eval_algebraMap]

theorem chartMap_clearing [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (a : Γ(X,⊤)) (ha : f.opensRange = X.basicOpen a) (m : Sections kY N ⊤) :
    ∃ d : ℕ, f.appTop a ^ d • m ∈ (chartMap kX kY f hk M e).range := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let F := chartModuleMap M f e
  let : IsLocalizedModule.Away a F := chartModuleMap_localize M f e a ha
  obtain ⟨d,n,hn⟩ := (inferInstance : IsLocalizedModule.Away a F).surj _ _ m
  refine ⟨d,n,?_⟩
  change f.appTop (a^d) • (m : OpenSections N ⊤) = F n at hn
  change F n = f.appTop a ^ d • (m : OpenSections N ⊤)
  rw [map_pow] at hn
  exact hn.symm

theorem laurent_finite_of_affine [IsAffine X] {P : Type} [CommRing P]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (L : LineBundle X) {N : Y.Modules} (d : L.sheaf.restrict f ≅ N)
    (a b : Γ(X,⊤)) (hopen : f.opensRange = X.basicOpen (a*b))
    (u v : Γ(Y,⊤)ˣ) (hu : f.appTop a = u) (hv : f.appTop b = v)
    (p : P →+* Γ(X,⊤)) (hp : p.Finite) (e : P →+* LaurentPlane.Ring K)
    (he : f.appTop.hom.comp p = (LaurentPlane.eval kY u v).comp e) :
    letI := laurentModule kY u v N
    Module.Finite (LaurentPlane.Ring K) (Sections kY N ⊤) := by
  let := laurentModule kY u v N
  let : Algebra P Γ(X,⊤) := p.toAlgebra
  let : Module.Finite P Γ(X,⊤) := hp
  let : Module P (Sections kX L.sheaf ⊤) := Module.compHom _ p
  let : Module.Finite Γ(X,⊤) (Sections kX L.sheaf ⊤) := L.affine_openSections_finite
  let : IsScalarTower P Γ(X,⊤) (Sections kX L.sheaf ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : Module.Finite P (Sections kX L.sheaf ⊤) := Module.Finite.trans Γ(X,⊤) _
  let F := chartMap kX kY f hk L.sheaf d
  apply LaurentPlane.finite_laurent_of_chart kY u v e F.toAddMonoidHom
  · intro q m
    change F (p q • m) = _
    rw [chartMap_smul]
    exact congrArg (fun c : Γ(Y,⊤) => c • F m) (RingHom.congr_fun he q)
  · intro m
    obtain ⟨n,z,hz⟩ := chartMap_clearing kX kY f hk L.sheaf d (a*b) hopen m
    refine ⟨n,z,?_⟩
    change (↑u * ↑v : Γ(Y,⊤))^n • m = chartMap kX kY f hk L.sheaf d z
    simpa only [map_mul,hu,hv] using hz.symm

lemma chartMap_monomial_mem
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (u v : Γ(Y,⊤)ˣ) (z : ℤ × ℤ)
    (h : ∃ a : Γ(X,⊤), f.appTop a = LaurentPlane.eval kY u v (T z)) :
    letI := laurentModule kY u v N
    ∀ m ∈ (chartMap kX kY f hk M e).range,
      T (K := K) z • m ∈ (chartMap kX kY f hk M e).range := by
  let := laurentModule kY u v N
  rintro m ⟨n,rfl⟩
  obtain ⟨a,ha⟩ := h
  refine ⟨a • n,?_⟩
  change chartMap kX kY f hk M e (a • n) =
    LaurentPlane.eval kY u v (T z) • chartMap kX kY f hk M e n
  rw [chartMap_smul,ha]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlaneCechFinite
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [Field K] {A B C W : Scheme.{0}}

theorem three_chart_quotient_finite [IsAffine A] [IsAffine B] [IsAffine C]
    (kA : K →+* Γ(A,⊤)) (kB : K →+* Γ(B,⊤))
    (kC : K →+* Γ(C,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ A) (b : W ⟶ B) (c : W ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (hka : a.appTop.hom.comp kA = kW) (hkb : b.appTop.hom.comp kB = kW)
    (hkc : c.appTop.hom.comp kC = kW)
    (LA : LineBundle A) (LB : LineBundle B) (LC : LineBundle C) (N : W.Modules)
    (ea : LA.sheaf.restrict a ≅ N) (eb : LB.sheaf.restrict b ≅ N)
    (ec : LC.sheaf.restrict c ≅ N)
    (u v : Γ(W,⊤)ˣ)
    (ax : Γ(A,⊤)ˣ) (ay : Γ(A,⊤)) (bx : Γ(B,⊤)) (by' : Γ(B,⊤)ˣ)
    (cx : Γ(C,⊤)ˣ) (cy : Γ(C,⊤))
    (hax : Units.map a.appTop.hom ax = u) (hay : a.appTop ay = v)
    (hbx : b.appTop bx = u) (hby : Units.map b.appTop.hom by' = v)
    (hcx : Units.map c.appTop.hom cx = u*v⁻¹) (hcy : c.appTop cy = ↑(v⁻¹))
    (ha : a.opensRange = A.basicOpen ay) (hb : b.opensRange = B.basicOpen bx)
    (hc : c.opensRange = C.basicOpen cy)
    (hfin : letI := laurentModule kW u v N
      Module.Finite (LaurentPlane.Ring K) (Sections kW N ⊤)) :
    Module.Finite K (Sections kW N ⊤ ⧸
      (((chartMap kA kW a hka LA.sheaf ea).range ⊔
        (chartMap kB kW b hkb LB.sheaf eb).range) ⊔
        (chartMap kC kW c hkc LC.sheaf ec).range)) := by
  let := laurentModule kW u v N
  let := laurentTower kW u v N
  let := hfin
  apply LaurentPlane.quotient_finite
  · intro z hz
    apply chartMap_monomial_mem kA kW a hka LA.sheaf ea u v z
    exact ⟨_,LaurentPlane.lift_cone_left kW u v a.appTop.hom ax ay hax hay z hz⟩
  · intro z hz
    apply chartMap_monomial_mem kB kW b hkb LB.sheaf eb u v z
    exact ⟨_,LaurentPlane.lift_cone_right kW u v b.appTop.hom bx by' hbx hby z hz⟩
  · intro z hz
    apply chartMap_monomial_mem kC kW c hkc LC.sheaf ec u v z
    exact ⟨_,LaurentPlane.lift_cone_top kW u v c.appTop.hom cx cy hcx hcy z hz⟩
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kA kW a hka LA.sheaf ea ay ha m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T (0,(n : ℤ))) • m ∈ _
    simpa only [eval_T, zpow_zero, one_mul, zpow_natCast, Units.val_pow_eq_pow_val, hay] using hn
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kB kW b hkb LB.sheaf eb bx hb m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T ((n : ℤ),0)) • m ∈ _
    simpa only [eval_T, zpow_zero, mul_one, zpow_natCast, Units.val_pow_eq_pow_val, hbx] using hn
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kC kW c hkc LC.sheaf ec cy hc m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T (0,-(n : ℤ))) • m ∈ _
    rw [eval_T]
    simp only [zpow_zero, one_mul, zpow_neg, zpow_natCast]
    rw [← inv_pow, Units.val_pow_eq_pow_val]
    simpa only [hcy] using hn

end
end MaximalSeshadri.Geometry.BaseSections

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_RestrictionComparison
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomGroup _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleMayerVietoris.tripleG_epi _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

variable [HasExt.{w} (SheafOfModules.{u} R)]

lemma union_ext_zero (U V : Opens X) (M : SheafOfModules.{u} R) (n : ℕ)
    (hU : ∀ x : Ext (freeOpen R U) M (n+1), x = 0)
    (hV : ∀ x : Ext (freeOpen R V) M (n+1), x = 0)
    (hUV : ∀ x : Ext (freeOpen R (U ⊓ V)) M n, x = 0)
    (x : Ext (freeOpen R (U ⊔ V)) M (n+1)) : x = 0 := by
  have hS := shortComplex_shortExact R U V
  have hmid (y : Ext (freeOpen R U ⊞ freeOpen R V) M (n+1)) : y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hS M x (hmid _) (n₀ := n) (by omega)
  have hz0 : z = 0 := hUV z
  rw [hz0, Ext.comp_zero] at hz
  exact hz.symm

end
end MaximalSeshadri.ModuleMayerVietoris


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.BaseSections.baseModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomGroup _root_.OAI.MaximalSeshadri.Geometry.BaseSections.freeBaseHomModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.globalModule _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleMayerVietoris.tripleG_epi _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque ModuleMayerVietoris

variable {X : Scheme.{0}}

lemma openBoundary_surjective (M : X.Modules) (U V : X.Opens) (n : ℕ)
    (hU : ∀ x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule U) M (n+1), x = 0)
    (hV : ∀ x : Ext.{1} (C := X.Modules) (FiniteCoverCohomology.freeOpenModule V) M (n+1), x = 0) :
    Function.Surjective (openBoundary M U V n) := by
  have hmid (y : Ext.{1} (C := X.Modules)
      (FiniteCoverCohomology.freeOpenModule U ⊞ FiniteCoverCohomology.freeOpenModule V)
      M (n+1)) : y = 0 := by
    apply (Ext.biprodAddEquiv (C := X.Modules)).injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  intro x
  exact Ext.contravariant_sequence_exact₃
    (shortComplex_shortExact (X := X.carrier) X.ringCatSheaf U V) M x (hmid _) (n₀ := n) (by omega)

attribute [local instance] OAI.MaximalSeshadri.Geometry.surfaceCechLinear
attribute [local instance] OAI.MaximalSeshadri.Geometry.surfaceCechHasExt
local instance surfaceCechFreeHomGroup_r3a3c87_1 (target : X.Modules) (chart : X.Opens) :
    AddCommGroup ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  Preadditive.homGroup (C := X.Modules) _ _
local instance surfaceCechFreeHomModule_r3a3c87_1 (target : X.Modules) (chart : X.Opens) :
    Module Γ(X,⊤) ((freeOpen X.ringCatSheaf chart : X.Modules) ⟶ target) :=
  sheafHomModule X _ _
theorem tripleSectionBoundary_surjective [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V))
    (hUW : IsAffineOpen (U ⊓ W)) (hVW : IsAffineOpen (V ⊓ W)) :
    Function.Surjective (tripleSectionBoundary M U V W) := by
  apply Function.Surjective.comp
    (openBoundary_surjective M (U ⊔ V) W 1
        (ModuleMayerVietoris.union_ext_zero (X := X.carrier) X.ringCatSheaf U V M 1
        (FiniteCoverCohomology.affine_open_ext_zero U hU M 1)
        (FiniteCoverCohomology.affine_open_ext_zero V hV M 1)
        (FiniteCoverCohomology.affine_open_ext_zero (U ⊓ V) hUV M 0))
      (FiniteCoverCohomology.affine_open_ext_zero W hW M 1))
  apply Function.Surjective.comp (extSourceIso (overlapIso U V W) M 1).surjective
  apply Function.Surjective.comp
    (openBoundary_surjective M (U ⊓ W) (V ⊓ W) 0
      (FiniteCoverCohomology.affine_open_ext_zero (U ⊓ W) hUW M 0)
      (FiniteCoverCohomology.affine_open_ext_zero (V ⊓ W) hVW M 0))
  exact (Ext.linearEquiv₀ (C := X.Modules) (R := Γ(X,⊤))
    (X := FiniteCoverCohomology.freeOpenModule (tripleOpen U V W)) (Y := M)).symm.surjective.comp
      (freeOpenLinearEquiv M (tripleOpen U V W)).symm.surjective

theorem tripleCokernelBoundary_surjective [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V))
    (hUW : IsAffineOpen (U ⊓ W)) (hVW : IsAffineOpen (V ⊓ W)) :
    Function.Surjective (tripleCokernelBoundary M U V W) := by
  intro x
  obtain ⟨y,hy⟩ := tripleSectionBoundary_surjective M U V W hU hV hW hUV hUW hVW x
  exact ⟨(tripleChartImage M U V W).mkQ y,hy⟩

theorem tripleCohomologyTwo_surjective [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V))
    (hUW : IsAffineOpen (U ⊓ W)) (hVW : IsAffineOpen (V ⊓ W))
    (hc : (U ⊔ V) ⊔ W = ⊤) :
    Function.Surjective (tripleCohomologyTwo M U V W hc) := by
  let e : FiniteCoverCohomology.freeOpenModule ((U ⊔ V) ⊔ W) ≅ structureSheaf X :=
    (freeOpenFunctor (X := X.carrier) X.ringCatSheaf).mapIso (eqToIso hc) ≪≫
    FreeOpenUnit.freeTopIso X.ringCatSheaf
  intro x
  obtain ⟨y, hy⟩ := (extSourceIso e M 2).surjective x
  obtain ⟨z, hz⟩ :=
    tripleCokernelBoundary_surjective M U V W hU hV hW hUV hUW hVW y
  refine ⟨z, ?_⟩
  change extSourceIso e M 2 (tripleCokernelBoundary M U V W z) = x
  rw [hz]
  exact hy

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceBaseCech
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.powerSection_isIso _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [Field K] {X : Scheme.{0}}

lemma tripleBaseCohomologyTwo_surjective [IsNoetherian X] (k : K →+* Γ(X,⊤))
    (M : X.Modules) [M.IsQuasicoherent] (U V W : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hUV : IsAffineOpen (U ⊓ V)) (hUW : IsAffineOpen (U ⊓ W))
    (hVW : IsAffineOpen (V ⊓ W)) (hc : (U ⊔ V) ⊔ W = ⊤) :
    Function.Surjective (tripleBaseCohomologyTwo k M U V W hc) := by
  intro x
  obtain ⟨y,hy⟩ := tripleCohomologyTwo_surjective M U V W hU hV hW hUV hUW hVW hc x
  obtain ⟨z,rfl⟩ := (tripleChartImage M U V W).mkQ_surjective y
  refine ⟨(tripleBaseImage k M U V W).mkQ z, ?_⟩
  exact hy

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_ChartCoherence
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {K : Type} [CommRing K] {X : Scheme.{0}}

lemma chartMap_range_coherent (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U) :
    (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
      (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)).range.map
        (chartTop k M W).toLinearMap = (res k M h).range := by
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨chartTop k M U z, (chartTop_nested k M h z).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨_, ⟨(chartTop k M U).symm z,rfl⟩, ?_⟩
    exact (chartTop_nested k M h _).trans
      (congrArg (res k M h) ((chartTop k M U).apply_symm_apply z))

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_SectionMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

end

end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
end MaximalSeshadri.Projective

end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ClosedEmbedding
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma evalAway_constants {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (MaximalSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end
end MaximalSeshadri.Projective

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PencilCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_C _root_.OAI.MaximalSeshadri.Projective.projectiveShiftHom_X
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
open MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K]

lemma affine_evaluation_finite {R : Type} [CommRing R] {Y : Scheme}
    (f : R →+* Γ(Y,⊤)) [IsFinite (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    f.Finite := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have h := g.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.Finite at h
  simpa only [hEq, CommRingCat.hom_ofHom] using h

lemma normalized_evalAway_polyToChart {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))).comp
      (polyToChart i) = eval₂Hom k (fun j : ChartVariables i => a j) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
    change F (chartConstants i r) = k r
    exact RingHom.congr_fun (evalAway_constants k a i hi) r
  · intro j
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
    change F (chartCoordinate i j.val) = a j.val
    have H := evalAway_mk_clear (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (MvPolynomial.X i)) by simpa only [eval₂Hom_X',hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j.val) (by simpa using isHomogeneous_X K j.val)
    simpa only [chartCoordinate, eval₂Hom_X',hi,one_pow,mul_one] using H

theorem finite_sectionsMorphism_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).Finite := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme,⊤) := fun j => coefficient (sectionFrame (s i))
    (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme,⊤))))
  let g := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  let chart := Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i)
    (isHomogeneous_X K i) (show 0 < 1 by decide)
  have : IsOpenImmersion chart := V.map_prop i
  have H : IsPullback g U.ι chart (sectionsMorphism k s hs) := by
    apply IsOpenImmersion.isPullback
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · have hrange : chart.opensRange =
          Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X i) :=
        Proj.opensRange_awayι _ _ (isHomogeneous_X K i) (show 0 < 1 by decide)
      rw [hrange, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsFinite g := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨isAffine_of_isAffineHom g, ?_⟩
  have hf := (@affine_evaluation_finite _ _ U.toScheme f hg).comp (RingHom.Finite.of_surjective
    (polyToChart (R := K) i) (polynomialChartEquiv (R := K) i).symm.surjective)
  rwa [normalized_evalAway_polyToChart k' a i hi] at hf

end
end MaximalSeshadri.Projective
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_PlaneCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Geometry MaximalSeshadri.Frames

variable {σ : Type} {X : Scheme.{0}} {M : X.Modules}

lemma ratioOn_restrict (s : σ → (O X ⟶ M)) (i j : σ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen (s i)) (h : W ≤ U) :
    (X.homOfLE h).appTop (ratioOn s i j U hi) = ratioOn s i j W (h.trans hi) := by
  dsimp only [ratioOn]
  rw [sectionFrameOn_coefficient, sectionFrameOn_coefficient]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

lemma ratioUnitOn_restrict (s : σ → (O X ⟶ M)) (i j : σ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j))
    (h : W ≤ U) :
    Units.map (X.homOfLE h).appTop.hom (ratioUnitOn s i j U hi hj) =
      ratioUnitOn s i j W (h.trans hi) (h.trans hj) := by
  apply Units.ext
  simp only [Units.coe_map, ratioUnitOn_val]
  exact ratioOn_restrict s i j hi h

lemma ratioOn_cocycle (s : σ → (O X ⟶ M)) (i j l : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    ratioOn s i l U hi = ratioOn s i j U hi * ratioOn s j l U hj := by
  have h := coefficient_change (sectionFrameOn (s j) U hj)
    (sectionFrameOn (s i) U hi) (restrictSection U.ι (s l))
  rw [← ratioUnitOn_val s i j U hi hj]
  exact h

lemma ratioUnitOn_cocycle (s : σ → (O X ⟶ M)) (i j l : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j))
    (hl : U ≤ SectionOpens.isoOpen (s l)) :
    ratioUnitOn s i l U hi hl = ratioUnitOn s i j U hi hj * ratioUnitOn s j l U hj hl := by
  apply Units.ext
  simp only [Units.val_mul, ratioUnitOn_val]
  exact ratioOn_cocycle s i j l U hi hj

lemma ratioUnitOn_symm (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) (hj : U ≤ SectionOpens.isoOpen (s j)) :
    ratioUnitOn s j i U hj hi = (ratioUnitOn s i j U hi hj)⁻¹ := by
  change frameChange _ _ = (frameChange _ _)⁻¹
  rfl

lemma ratioOn_basicOpen (s : σ → (O X ⟶ M)) (i j : σ) (U : X.Opens)
    (hi : U ≤ SectionOpens.isoOpen (s i)) :
    U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) = U.toScheme.basicOpen (ratioOn s i j U hi) :=
  preimage_isoOpen (s j) U.ι (sectionFrameOn (s i) U hi)

end
end MaximalSeshadri.Projective

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_PlaneProjectionModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.LaurentPlane MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma finite_plane_chart (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : Fin 3) :
    (MvPolynomial.eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => ratioOn s i j (SectionOpens.isoOpen (s i)) le_rfl)).Finite := by
  have he : (fun j : ChartVariables i => ratioOn s i j (SectionOpens.isoOpen (s i)) le_rfl) =
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) := by
    funext j
    exact ratioOn_full s i j
  rw [he]
  exact (finite_sectionsMorphism_chart k s hs i).2

theorem finite_plane_laurent (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let W := planeTriple s
    letI := laurentModule (W.ι.appTop.hom.comp k) (planeX s) (planeY s) (L.sheaf.restrict W.ι)
    Module.Finite (LaurentPlane.Ring K)
      (Sections (W.ι.appTop.hom.comp k) (L.sheaf.restrict W.ι) ⊤) := by
  let U := SectionOpens.isoOpen (s 0)
  let W := planeTriple s
  let kU := U.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let a := ratioOn s 0 1 U le_rfl
  let b := ratioOn s 0 2 U le_rfl
  let f := X.homOfLE (planeTriple_le s 0)
  let p : MvPolynomial (ChartVariables (0 : Fin 3)) K →+* Γ(U.toScheme,⊤) :=
    MvPolynomial.eval₂Hom kU (fun j => ratioOn s 0 j U le_rfl)
  obtain ⟨hU,hp⟩ := finite_sectionsMorphism_chart k s hs (0 : Fin 3)
  have : IsAffine U.toScheme := hU
  have hp' : p.Finite := finite_plane_chart k s hs 0
  have ho : f.opensRange = U.toScheme.basicOpen (a*b) := by
    rw [Scheme.opensRange_homOfLE]
    change U.ι ⁻¹ᵁ ((SectionOpens.isoOpen (s 1) ⊓ U) ⊓
      (SectionOpens.isoOpen (s 2) ⊓ U)) = _
    simp only [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
    rw [ratioOn_basicOpen s 0 1 U le_rfl, ratioOn_basicOpen s 0 2 U le_rfl]
    exact (Scheme.basicOpen_mul _ _ _).symm
  have ha : f.appTop a = (planeX s : Γ(W.toScheme,⊤)) := by
    rw [planeX, ratioUnitOn_val]
    exact ratioOn_restrict s 0 1 le_rfl (planeTriple_le s 0)
  have hb : f.appTop b = (planeY s : Γ(W.toScheme,⊤)) := by
    rw [planeY, ratioUnitOn_val]
    exact ratioOn_restrict s 0 2 le_rfl (planeTriple_le s 0)
  let e : MvPolynomial (ChartVariables (0 : Fin 3)) K →+* LaurentPlane.Ring K :=
    MvPolynomial.eval₂Hom (algebraMap K _) (fun j => T (if j.val = 1 then (1,0) else (0,1)))
  apply laurent_finite_of_affine kU kW f (nestedBase k (planeTriple_le s 0))
    (L.restrict U.ι) (nestedRestriction L.sheaf (planeTriple_le s 0)) a b ho
    (planeX s) (planeY s) ha hb p hp' e
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, p, e, MvPolynomial.eval₂Hom_C, eval_algebraMap]
    exact RingHom.congr_fun (nestedBase k (planeTriple_le s 0)) r
  · intro j
    simp only [RingHom.comp_apply, p, e, MvPolynomial.eval₂Hom_X']
    have hj : j.val = 1 ∨ j.val = 2 := by
      have h := j.property
      have h' := j.val.isLt
      omega
    rcases hj with hj | hj
    · simp only [hj, ↓reduceIte, eval_T, zpow_one, zpow_zero, mul_one]
      exact ha
    · simp only [hj, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, eval_T,
        zpow_zero, zpow_one, one_mul]
      exact hb

end
end MaximalSeshadri.Projective

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_PlanePairs
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                    
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}} {M : X.Modules}

lemma pairRestriction_basic (s : Fin 3 → (O X ⟶ M)) (i j : Fin 3)
    (U W : X.Opens) (hi : U ≤ SectionOpens.isoOpen (s i)) (h : W ≤ U)
    (he : W = U ⊓ SectionOpens.isoOpen (s j)) :
    (X.homOfLE h).opensRange = U.toScheme.basicOpen (ratioOn s i j U hi) := by
  rw [Scheme.opensRange_homOfLE,he,Scheme.Hom.preimage_inf,
    Scheme.Opens.ι_preimage_self,top_inf_eq]
  exact ratioOn_basicOpen s i j U hi

lemma planeThird_unit (s : Fin 3 → (O X ⟶ M)) :
    ratioUnitOn s 2 1 (planeTriple s) (planeTriple_le s 2) (planeTriple_le s 1) =
      planeX s * (planeY s)⁻¹ := by
  have h := ratioUnitOn_cocycle s 0 2 1 (planeTriple s)
    (planeTriple_le s 0) (planeTriple_le s 2) (planeTriple_le s 1)
  change planeX s = planeY s * _ at h
  calc
    _ = (planeY s)⁻¹ * planeX s := by rw [h, ← mul_assoc, inv_mul_cancel, one_mul]
    _ = _ := mul_comm _ _

theorem finite_plane_cokernel [X.IsSeparated] (k : K →+* Γ(X,⊤))
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    Module.Finite K (Sections k L.sheaf (planeTriple s) ⧸
      tripleBaseImage k L.sheaf (SectionOpens.isoOpen (s 1))
        (SectionOpens.isoOpen (s 2)) (SectionOpens.isoOpen (s 0))) := by
  let U := SectionOpens.isoOpen (s 1)
  let V := SectionOpens.isoOpen (s 2)
  let Z := SectionOpens.isoOpen (s 0)
  let A := U ⊓ Z
  let B := V ⊓ Z
  let C := U ⊓ V
  let W := planeTriple s
  have hU : IsAffineOpen U := (finite_sectionsMorphism_chart k s hs 1).1
  have hV : IsAffineOpen V := (finite_sectionsMorphism_chart k s hs 2).1
  have hZ : IsAffineOpen Z := (finite_sectionsMorphism_chart k s hs 0).1
  let : IsAffine A.toScheme := hU.inf hZ
  let : IsAffine B.toScheme := hV.inf hZ
  let : IsAffine C.toScheme := hU.inf hV
  have hA : W ≤ A := inf_le_left
  have hB : W ≤ B := inf_le_right
  have hC : W ≤ C := inf_le_inf inf_le_left inf_le_left
  let a := X.homOfLE hA
  let b := X.homOfLE hB
  let c := X.homOfLE hC
  let kA := A.ι.appTop.hom.comp k
  let kB := B.ι.appTop.hom.comp k
  let kC := C.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let ea := nestedRestriction L.sheaf hA
  let eb := nestedRestriction L.sheaf hB
  let ec := nestedRestriction L.sheaf hC
  let F := chartMap kA kW a (nestedBase k hA) (L.restrict A.ι).sheaf ea
  let G := chartMap kB kW b (nestedBase k hB) (L.restrict B.ι).sheaf eb
  let H := chartMap kC kW c (nestedBase k hC) (L.restrict C.ι).sheaf ec
  let ax := ratioUnitOn s 0 1 A inf_le_right inf_le_left
  let ay := ratioOn s 0 2 A inf_le_right
  let bx := ratioOn s 0 1 B inf_le_right
  let by' := ratioUnitOn s 0 2 B inf_le_right inf_le_left
  let cx := ratioUnitOn s 2 1 C inf_le_right inf_le_left
  let cy := ratioOn s 2 0 C inf_le_right
  have ha : a.opensRange = A.toScheme.basicOpen ay := by
    apply pairRestriction_basic s 0 2 A W inf_le_right hA
    dsimp only [W,planeTriple,tripleOpen,A,U,V,Z]
    simp only [inf_assoc,inf_left_comm,inf_comm,inf_left_idem]
  have hb : b.opensRange = B.toScheme.basicOpen bx := by
    apply pairRestriction_basic s 0 1 B W inf_le_right hB
    dsimp only [W,planeTriple,tripleOpen,B,U,V,Z]
    simp only [inf_assoc,inf_left_comm,inf_comm,inf_left_idem]
  have hc : c.opensRange = C.toScheme.basicOpen cy := by
    apply pairRestriction_basic s 2 0 C W inf_le_right hC
    dsimp only [W,planeTriple,tripleOpen,C,U,V,Z]
    simp only [inf_assoc,inf_left_comm,inf_comm,inf_left_idem]
  have hax : Units.map a.appTop.hom ax = planeX s :=
    ratioUnitOn_restrict s 0 1 inf_le_right inf_le_left hA
  have hay : a.appTop ay = (planeY s : Γ(W.toScheme,⊤)) := by
    rw [planeY,ratioUnitOn_val]
    exact ratioOn_restrict s 0 2 inf_le_right hA
  have hbx : b.appTop bx = (planeX s : Γ(W.toScheme,⊤)) := by
    rw [planeX,ratioUnitOn_val]
    exact ratioOn_restrict s 0 1 inf_le_right hB
  have hby : Units.map b.appTop.hom by' = planeY s :=
    ratioUnitOn_restrict s 0 2 inf_le_right inf_le_left hB
  have hcx : Units.map c.appTop.hom cx = planeX s * (planeY s)⁻¹ := by
    rw [show Units.map c.appTop.hom cx = ratioUnitOn s 2 1 W
      (planeTriple_le s 2) (planeTriple_le s 1) from
      ratioUnitOn_restrict s 2 1 inf_le_right inf_le_left hC]
    exact planeThird_unit s
  have hcy : c.appTop cy = (↑((planeY s)⁻¹) : Γ(W.toScheme,⊤)) := by
    rw [show c.appTop cy = ratioOn s 2 0 W (planeTriple_le s 2) from
      ratioOn_restrict s 2 0 inf_le_right hC]
    rw [← ratioUnitOn_val s 2 0 W (planeTriple_le s 2) (planeTriple_le s 0),
      ratioUnitOn_symm]
    rfl
  let : Module.Finite K (Sections kW (L.sheaf.restrict W.ι) ⊤ ⧸
      ((F.range ⊔ G.range) ⊔ H.range)) :=
    three_chart_quotient_finite kA kB kC kW a b c (nestedBase k hA)
      (nestedBase k hB) (nestedBase k hC) (L.restrict A.ι) (L.restrict B.ι)
      (L.restrict C.ι) (L.sheaf.restrict W.ι) ea eb ec (planeX s) (planeY s)
      ax ay bx by' cx cy hax hay hbx hby hcx hcy ha hb hc (finite_plane_laurent k s hs L)
  let E := chartTop k L.sheaf W
  have he : ((F.range ⊔ G.range) ⊔ H.range).map E.toLinearMap =
      tripleBaseImage k L.sheaf U V Z := by
    rw [Submodule.map_sup,Submodule.map_sup]
    exact congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·)
      (chartMap_range_coherent k L.sheaf hA) (chartMap_range_coherent k L.sheaf hB))
      (chartMap_range_coherent k L.sheaf hC)
  let q := Submodule.Quotient.equiv ((F.range ⊔ G.range) ⊔ H.range)
    (tripleBaseImage k L.sheaf U V Z) E he
  exact Module.Finite.of_surjective q.toLinearMap q.surjective

end
end MaximalSeshadri.Projective

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FramedMaps
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

@[reassoc]
theorem framedSectionsMorphism_over :
    framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover U hc).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [← Category.assoc, framedSectionsMorphism_local, coordinatesMap_over,
    ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

end
end MaximalSeshadri.Projective


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_SurfaceH2Finite
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
attribute [-simp] _root_.OAI.MaximalSeshadri.Projective.scalarEnd_one _root_.OAI.MaximalSeshadri.Projective.scalarEnd_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_projection_H2_finite [X.IsSeparated] [IsNoetherian X]
    (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Fin 3 → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 2) k
    Module.Finite K (cohomology L.sheaf 2) := by
  let := Module.compHom (cohomology L.sheaf 2) k
  let U := SectionOpens.isoOpen (s 1)
  let V := SectionOpens.isoOpen (s 2)
  let W := SectionOpens.isoOpen (s 0)
  have hU : IsAffineOpen U := (finite_sectionsMorphism_chart k s hs 1).1
  have hV : IsAffineOpen V := (finite_sectionsMorphism_chart k s hs 2).1
  have hW : IsAffineOpen W := (finite_sectionsMorphism_chart k s hs 0).1
  have hc : (U ⊔ V) ⊔ W = ⊤ := by
    apply top_unique
    intro x hx
    have hx' : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx'
    fin_cases i
    · exact Or.inr hi
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
  let : Module.Finite K (Sections k L.sheaf (planeTriple s) ⧸
      tripleBaseImage k L.sheaf U V W) := finite_plane_cokernel k s hs L
  exact Module.Finite.of_surjective (tripleBaseCohomologyTwo k L.sheaf U V W hc)
    (tripleBaseCohomologyTwo_surjective k L.sheaf U V W hU hV hW
      (hU.inf hV) (hU.inf hW) (hV.inf hW) hc)

theorem Surface.H2_finite (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) :
    letI := Module.compHom (cohomology L.sheaf 2) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf 2) := by
  let : S.scheme.IsSeparated := by
    constructor
    have separatedComposite : IsSeparated
        (S.structureMap ≫ Limits.terminal.from (Spec (CommRingCat.of ℂ))) := inferInstance
    simpa using separatedComposite
  obtain ⟨n,hn,s,hs,hf⟩ := S.exists_finite_projection_s01 A hA
  let : IsFinite (sectionsMorphism (baseScalars S.structureMap) s hs) := hf
  exact finite_projection_H2_finite (baseScalars S.structureMap) s hs L

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfaceEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

theorem Surface.cohomology_finite_s01_oai (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (n : ℕ) :
    letI := Module.compHom (cohomology L.sheaf n) (baseScalars S.structureMap)
    Module.Finite ℂ (cohomology L.sheaf n) := by
  cases n with
  | zero => exact S.H0_finite_s01 A hA L
  | succ n => cases n with
    | zero => exact S.H1_finite_s01 A hA L
    | succ n => cases n with
      | zero => exact S.H2_finite A hA L
      | succ n =>
        let := Module.compHom (cohomology L.sheaf (n+3)) (baseScalars S.structureMap)
        let : Subsingleton (cohomology L.sheaf (n+3)) := ⟨fun x y =>
          (S.lineBundle_cohomology_zero_above_two_s01 A hA L n x).trans
            (S.lineBundle_cohomology_zero_above_two_s01 A hA L n y).symm⟩
        infer_instance

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.cohomology_finite_s01_oai

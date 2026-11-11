-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:56.67599+00:00
-- url     : https://prove2.me/submissions/46eb0a96-8a58-407c-8b4c-b1c395c7109f

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_mixed_degree_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_invertible_ideal_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IsBlowup_eventual_ample_power_twist_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_PointBlowup_effective_twist_bound_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_PointBlowup_total_ideal_degree_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_H0_finite_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_blowup_intersections_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_eventual_etale_affine_section_test_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_pointBlowup_exists_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_positive_square_eventually_effective_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_selfIntersection_twist_general_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_seshadri_eq_of_curve_lower_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curve_lower_of_homogeneous_section_test_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_exists_open_jet_configuration_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_power_euler_difference_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_pow_left_general_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_pow_right_general_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_tensor_left_general_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_mixedEuler_tensor_right_general_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_surface_configuration_outside_countable_closed_s01

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri
noncomputable section
open Cardinal

theorem algebraic_of_countable_presentation
    {F E σ : Type} [Field F] [Uncountable F] [Field E] [Algebra F E]
    [Countable σ] (φ : MvPolynomial σ F →ₐ[F] E) (hφ : Function.Surjective φ) :
    Algebra.IsAlgebraic F E := by
  constructor
  intro x
  by_contra hx
  have hLI := (show Transcendental F x from hx).linearIndependent_sub_inv
  have hrank : Module.rank F E ≤ ℵ₀ := by
    calc
      _ ≤ Module.rank F (MvPolynomial σ F) :=
        LinearMap.rank_le_of_surjective φ.toLinearMap hφ
      _ = #(σ →₀ ℕ) := MvPolynomial.rank_eq
      _ ≤ ℵ₀ := Cardinal.mk_le_aleph0
  exact (not_le_of_gt (Cardinal.aleph0_lt_mk (α := F)))
    (hLI.cardinal_le_rank.trans hrank)

theorem point_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [Nontrivial A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ) :
    Nonempty (A →ₐ[F] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let q : A →ₐ[F] A ⧸ m := Ideal.Quotient.mkₐ F m
  let ψ : MvPolynomial σ F →ₐ[F] A ⧸ m := q.comp φ
  have hψ : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp hφ
  let : Algebra.IsAlgebraic F (A ⧸ m) :=
    algebraic_of_countable_presentation ψ hψ
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] F).comp q⟩

theorem point_avoiding_sequence_of_countable_presentation
    {F A σ : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Countable σ]
    (φ : MvPolynomial σ F →ₐ[F] A) (hφ : Function.Surjective φ)
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  classical
  let S : Submonoid A := Submonoid.closure (Set.range a)
  have hcount : (S : Set A).Countable := by
    change ((Submonoid.closure (Set.range a) : Submonoid A) : Set A).Countable
    rw [← FreeMonoid.mrange_lift, MonoidHom.coe_mrange]
    exact Set.countable_range _
  let : Countable S := hcount.to_subtype
  have hden : S ≤ nonZeroDivisors A := by
    apply Submonoid.closure_le.mpr
    rintro b ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (ha n)
  let B := Localization S
  let : IsDomain B := IsLocalization.isDomain_localization hden
  let j : A →ₐ[F] B := IsScalarTower.toAlgHom F A B
  let vals : σ ⊕ S → B := Sum.elim (fun i => j (φ (MvPolynomial.X i)))
    (fun s => IsLocalization.mk' B 1 s)
  let ψ : MvPolynomial (σ ⊕ S) F →ₐ[F] B := MvPolynomial.aeval vals
  have hre : ψ.comp (MvPolynomial.rename Sum.inl) = j.comp φ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ψ, vals]
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq S z
    obtain ⟨p, rfl⟩ := hφ b
    refine ⟨MvPolynomial.rename Sum.inl p * MvPolynomial.X (Sum.inr s), ?_⟩
    rw [map_mul]
    have he := DFunLike.congr_fun hre p
    change ψ (MvPolynomial.rename Sum.inl p) = j (φ p) at he
    rw [he]
    simp only [ψ, MvPolynomial.aeval_X, vals, Sum.elim_inr]
    exact (IsLocalization.mk'_eq_mul_mk'_one _ _).symm
  obtain ⟨g⟩ := point_of_countable_presentation ψ hψ
  refine ⟨g.comp j, fun n => ?_⟩
  let s : S := ⟨a n, Submonoid.subset_closure ⟨n, rfl⟩⟩
  exact ((IsLocalization.map_units B s).map g.toMonoidHom).ne_zero

theorem point_avoiding_sequence
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A]
    (a : ℕ → A) (ha : ∀ n, a n ≠ 0) :
    ∃ f : A →ₐ[F] F, ∀ n, f (a n) ≠ 0 := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType F A)
  exact point_avoiding_sequence_of_countable_presentation φ hφ a ha

end

noncomputable section
open scoped TensorProduct

lemma smooth_positive_dimension_nontrivial_kernel
    {F A : Type} [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    (n : ℕ) (hn : 0 < n) [Algebra.IsStandardSmoothOfRelativeDimension n F A]
    (p : A →ₐ[F] F) : ∃ a : A, a ≠ 0 ∧ p a = 0 := by
  classical
  by_contra h
  have hi : Function.Injective p := by
    intro a b hab
    apply sub_eq_zero.mp
    by_contra hab'
    exact h ⟨a - b, hab', by simp [hab]⟩
  have hs : Function.Surjective p := fun a => ⟨algebraMap F A a, p.commutes a⟩
  let e : A ≃ₐ[F] F := AlgEquiv.ofBijective p ⟨hi, hs⟩
  let : Algebra.FormallyUnramified F A := Algebra.FormallyUnramified.of_equiv e.symm
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := F) (S := A) n
  rw [rank_subsingleton'] at hr
  have : n = 0 := by exact_mod_cast hr.symm
  omega

theorem smooth_affine_uncountable_rational_points
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A]
    (n : ℕ) (hn : 0 < n) [Algebra.IsStandardSmoothOfRelativeDimension n F A] :
    Uncountable (A →ₐ[F] F) := by
  classical
  let : Algebra.IsStandardSmooth F A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let : Algebra.FiniteType F A := inferInstance
  obtain ⟨p, _⟩ := point_avoiding_sequence (F := F) (A := A) (fun _ => 1)
    (fun _ => one_ne_zero)
  let : Nonempty (A →ₐ[F] F) := ⟨p⟩
  apply not_countable_iff.mp
  intro hcount
  let := hcount
  obtain ⟨q, hq⟩ := exists_surjective_nat (A →ₐ[F] F)
  choose a hane ha using fun k => smooth_positive_dimension_nontrivial_kernel n hn (q k)
  obtain ⟨p', hp'⟩ := point_avoiding_sequence (F := F) a hane
  obtain ⟨k, rfl⟩ := hq p'
  exact hp' k (ha k)

theorem rational_kernel_injective {F A : Type} [Field F] [CommRing A] [Algebra F A] :
    Function.Injective (fun p : A →ₐ[F] F => RingHom.ker p.toRingHom) := by
  intro p q h
  ext a
  have hzero : a - algebraMap F A (q a) ∈ RingHom.ker q.toRingHom := by
    simp
  change RingHom.ker p.toRingHom = RingHom.ker q.toRingHom at h
  rw [← h] at hzero
  simpa [sub_eq_zero] using hzero

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

theorem smooth_scheme_uncountable_rational_points
    {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of F))
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n f] :
    ¬ (Set.range fun p : {p : Spec (CommRingCat.of F) ⟶ X // p ≫ f = 𝟙 _} =>
      p.val (fieldPoint F)).Countable := by
  classical
  let x : X := Classical.ofNonempty
  obtain ⟨U, hU, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := f) x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f x := Subsingleton.elim _ _
    simpa only [Scheme.Hom.mem_preimage, hy] using e hxV
  subst U
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let A := Γ(X, V)
  let g : CommRingCat.of F ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ f.appLE ⊤ V e
  have hng : RingHom.IsStandardSmoothOfRelativeDimension n g.hom := by
    let e₀ : F ≃+* Γ(Spec (CommRingCat.of F), ⊤) :=
      RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv)
    have he := RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀
    convert hg.comp he using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  algebraize [g.hom]
  let : Algebra.IsStandardSmoothOfRelativeDimension n F A := hng.toAlgebra
  let : Uncountable (A →ₐ[F] F) := smooth_affine_uncountable_rational_points n hn
  have hmap : Spec.map g = hV.fromSpec ≫ f := by
    dsimp only [g]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hV e
  let p (φ : A →ₐ[F] F) : {p : Spec (CommRingCat.of F) ⟶ X // p ≫ f = 𝟙 _} :=
    ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hV.fromSpec, by
      rw [Category.assoc, ← hmap, ← Spec.map_comp, ← Spec.map_id]
      congr 1
      apply CommRingCat.hom_ext
      exact φ.comp_algebraMap⟩
  have hi : Function.Injective (fun φ : A →ₐ[F] F => (p φ).val (fieldPoint F)) := by
    intro φ ψ h
    apply rational_kernel_injective
    have heq :
        (⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime φ.toRingHom⟩ : PrimeSpectrum A) =
        (⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime ψ.toRingHom⟩ : PrimeSpectrum A) :=
      hV.fromSpec.isOpenEmbedding.injective h
    exact congrArg PrimeSpectrum.asIdeal heq
  intro hcount
  let : Countable (Set.range fun q : {q : Spec (CommRingCat.of F) ⟶ X // q ≫ f = 𝟙 _} =>
      q.val (fieldPoint F)) := hcount.to_subtype
  let j (φ : A →ₐ[F] F) :
      Set.range (fun q : {q : Spec (CommRingCat.of F) ⟶ X // q ≫ f = 𝟙 _} =>
        q.val (fieldPoint F)) := ⟨(p φ).val (fieldPoint F), ⟨p φ, rfl⟩⟩
  have hij : Function.Injective j := by
    intro φ ψ h
    apply hi
    have heq := congrArg (fun z : Set.range (fun q :
      {q : Spec (CommRingCat.of F) ⟶ X // q ≫ f = 𝟙 _} =>
        q.val (fieldPoint F)) => (z : X)) h
    exact heq
  exact not_countable hij.countable

end
end MaximalSeshadri
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_AffinePointParameters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma affineComplexPoint_image_injective {X : Scheme} (f : X ⟶ complexBase)
    (U : X.affineOpens) :
    Function.Injective (fun ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ =>
      (affineComplexPoint f U ρ).left (fieldPoint ℂ)) := by
  let := (openScalars f U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  intro ρ σ h
  apply rational_kernel_injective
  exact congrArg PrimeSpectrum.asIdeal (U.2.fromSpec.isOpenEmbedding.injective h)

end
end MaximalSeshadri.Geometry

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
-- module Solutions.Q223_SES.Seshadri_Intersection_CurveIdealDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

lemma mixedEuler_comm (S : Surface) (L M : LineBundle S.scheme) :
    mixedEuler S L M = mixedEuler S M L := by
  have h := eulerCharacteristic_iso S.structureMap (moduleTensorComm L.sheaf M.sheaf) 2
  unfold mixedEuler
  change eulerCharacteristic S.structureMap 2 (L.tensor M).sheaf =
    eulerCharacteristic S.structureMap 2 (M.tensor L).sheaf at h
  rw [h]
  ring

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Intersection_SurfacePositiveSquare
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
-- module Solutions.Q223_SES.Seshadri_Intersection_BivariateSurfaceEuler
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

end
end MaximalSeshadri.Geometry

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionGermSystem
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

variable {X : Scheme.{0}}

lemma Surface.sections_finite (S : Surface) (L : LineBundle S.scheme) (hL : L.IsAmple)
    (M : LineBundle S.scheme) :
    letI := complexSectionModule S.structureMap M.sheaf
    Module.Finite ℂ (GlobalSections S.scheme M.sheaf) := by
  let := complexSectionModule S.structureMap M.sheaf
  let := Module.compHom (cohomology M.sheaf 0) (baseScalars S.structureMap)
  let := S.H0_finite_s01 L hL M
  let e := Ext.linearEquiv₀ (R := Γ(S.scheme,⊤)) (X := structureSheaf S.scheme) (Y := M.sheaf)
  exact Module.Finite.equiv (show cohomology M.sheaf 0 ≃ₗ[ℂ] GlobalSections S.scheme M.sheaf from
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars S.structureMap r) x })

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_NefPerturbation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.NefNumerics
noncomputable section

lemma negative_boundary_perturbation (H c u v z α : ℤ) (r : ℕ) (w : ℝ)
    (_hH : 0 < H) (_hr : 0 < r) (hw : 0 < w) (hvol : (H:ℝ) = r*w^2)
    (hc : -(r:ℤ) ≤ c) (hneg : (u:ℝ)+w*v < 0)
    (hpos : 0 < (α:ℝ)*H+w*c) :
    ∃ k m b : ℕ, 0 < k ∧ 0 < m ∧ 0 < b ∧ (k:ℝ)*w < m ∧
      0 < (k:ℤ)^2*H+(m:ℤ)^2*c-2*b*((k:ℤ)*u+(m:ℤ)*v)+(b:ℤ)^2*z ∧
      0 ≤ (α:ℤ)*k*H+m*c-b*(α*u+v) := by
  let A : ℝ := -((u:ℝ)+w*v)
  let B : ℝ := (α:ℝ)*H+w*c
  have hA : 0 < A := by dsimp [A] <;> linarith
  have hB : 0 < B := hpos
  let d := min (A/(|(z:ℝ)|+1)) (B/(|(α:ℝ)*u+v|+1)) / 2
  have hz : (0:ℝ) < |(z:ℝ)|+1 := by positivity
  have hy : (0:ℝ) < |(α:ℝ)*u+v|+1 := by positivity
  have hd : 0 < d := div_pos (lt_min (div_pos hA hz) (div_pos hB hy)) (by norm_num)
  have hd₁ : d < A/(|(z:ℝ)|+1) := by
    have hh := min_le_left (A/(|(z:ℝ)|+1)) (B/(|(α:ℝ)*u+v|+1))
    dsimp [d] at *
    linarith
  have hd₂ : d < B/(|(α:ℝ)*u+v|+1) := by
    have hh := min_le_right (A/(|(z:ℝ)|+1)) (B/(|(α:ℝ)*u+v|+1))
    dsimp [d] at *
    linarith
  have hdA : d*(|(z:ℝ)|+1) < A := (lt_div_iff₀ hz).mp hd₁
  have hdB : d*(|(α:ℝ)*u+v|+1) < B := (lt_div_iff₀ hy).mp hd₂
  let F : ℝ × ℝ → ℝ := fun p => H+c*p.1^2-2*p.2*(u+p.1*v)+p.2^2*z
  let G : ℝ × ℝ → ℝ := fun p => (α:ℝ)*H+p.1*c-p.2*(α*u+v)
  have hbase : 0 ≤ (H:ℝ)+c*w^2 := by
    have hcR : -(r:ℝ) ≤ c := by exact_mod_cast hc
    have hh := mul_le_mul_of_nonneg_right hcR (sq_nonneg w)
    nlinarith only [hh,hvol]
  have hf : 0 < F (w,d) := by
    have hh := mul_le_mul_of_nonneg_left (neg_abs_le (z:ℝ)) hd.le
    have hlin : 0 < 2*A+d*z := by nlinarith only [hh,hdA,hA,hd]
    have hp := mul_pos hd hlin
    dsimp [F,A] at *
    nlinarith only [hbase,hp]
  have hg : 0 < G (w,d) := by
    have hh := mul_le_mul_of_nonneg_left (le_abs_self ((α:ℝ)*u+v)) hd.le
    dsimp [G,B] at *
    nlinarith only [hh,hdB,hd]
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hG : Continuous G := by dsimp [G]; fun_prop
  have he : ∀ᶠ p in nhds (w,d), 0 < F p ∧ 0 < G p :=
    (hF.continuousAt.eventually (Ioi_mem_nhds hf)).and
      (hG.continuousAt.eventually (Ioi_mem_nhds hg))
  obtain ⟨ε,hε,heε⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨s,hws,hs⟩ := exists_rat_btwn (show w < w+ε/2 by linarith)
  obtain ⟨t,hdt,ht⟩ := exists_rat_btwn (show d < d+ε/2 by linarith)
  have hst : dist ((s:ℝ),(t:ℝ)) (w,d) < ε := by
    rw [Prod.dist_eq, max_lt_iff,Real.dist_eq,Real.dist_eq,
      abs_of_pos (sub_pos.mpr hws),abs_of_pos (sub_pos.mpr hdt)]
    constructor <;> linarith
  obtain ⟨hFs,hGs⟩ := heε hst
  have hs0 : 0 < s := by exact_mod_cast (hw.trans hws)
  have ht0 : 0 < t := by exact_mod_cast (hd.trans hdt)
  let k := s.den*t.den
  let m := s.num.toNat*t.den
  let b := t.num.toNat*s.den
  have hk : 0 < k := Nat.mul_pos s.den_pos t.den_pos
  have hm : 0 < m := Nat.mul_pos (by have := Rat.num_pos.mpr hs0; omega) t.den_pos
  have hb : 0 < b := Nat.mul_pos (by have := Rat.num_pos.mpr ht0; omega) s.den_pos
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  have em : (m:ℝ) = (k:ℝ)*(s:ℝ) := by
    dsimp [m,k]
    rw [Nat.cast_mul,Nat.cast_mul,← Int.cast_natCast,
      Int.toNat_of_nonneg (Rat.num_pos.mpr hs0).le,Rat.cast_def]
    have hz : (s.den:ℝ) ≠ 0 := by exact_mod_cast s.den_ne_zero
    field_simp
  have eb : (b:ℝ) = (k:ℝ)*(t:ℝ) := by
    dsimp [b,k]
    rw [Nat.cast_mul,Nat.cast_mul,← Int.cast_natCast,
      Int.toNat_of_nonneg (Rat.num_pos.mpr ht0).le,Rat.cast_def]
    have hz : (t.den:ℝ) ≠ 0 := by exact_mod_cast t.den_ne_zero
    field_simp
  refine ⟨k,m,b,hk,hm,hb,?_,?_,?_⟩
  · rw [em]; exact mul_lt_mul_of_pos_left hws hkR
  · have hh := mul_pos (sq_pos_of_pos hkR) hFs
    have hh' : 0 < (k:ℝ)^2*H+(m:ℝ)^2*c-2*b*((k:ℝ)*u+(m:ℝ)*v)+(b:ℝ)^2*z := by
      rw [em,eb]
      dsimp [F] at hh
      nlinarith only [hh]
    exact_mod_cast hh'
  · have hh := mul_pos hkR hGs
    have hh' : 0 ≤ (α:ℝ)*k*H+m*c-b*(α*u+v) := by
      rw [em,eb]
      dsimp [G] at hh
      nlinarith only [hh]
    exact_mod_cast hh'

end
end MaximalSeshadri.NefNumerics

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Blowup_BoundaryNef
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.NefNumerics

theorem PointBlowup.boundaryNef_of_curve_bound (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) {r : ℕ} (hr : 0 < r) {p : Configuration S r}
    (B : PointBlowup S r p)
    (hC : ∀ C : IntegralCurve S,
      Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
        (curveDegree S L C:ℝ)) : B.BoundaryNef L := by
  classical
  let T := B.surface
  let P := L.pullback B.projection
  let H := selfIntersection S L
  let w := Real.sqrt ((H:ℝ)/r)
  have hH : 0 < H := S.selfIntersection_pos L hL
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hw : 0 < w := Real.sqrt_pos.mpr (div_pos hHR hrR)
  have hvol : (H:ℝ) = (r:ℝ)*w^2 := by
    have hh : w^2 = (H:ℝ)/r := Real.sq_sqrt (div_nonneg hHR.le hrR.le)
    have he := (eq_div_iff (ne_of_gt hrR)).mp hh
    nlinarith only [he]
  obtain ⟨J,ι,hJ⟩ := B.isBlowup.1
  obtain ⟨hPP,hPJ,hc,hc0⟩ := S.blowup_intersections_s01 T L hL p B.projection
    B.overComplex B.isBlowup J ι hJ
  let c := selfIntersection T J
  obtain ⟨a,N,ha,hA'⟩ := B.isBlowup.eventual_ample_power_twist_s01 L hL J ι hJ
  obtain ⟨t,ht⟩ := exists_nat_gt (-(w*(c:ℝ))/(H:ℝ))
  let α := a*(max N t+1)
  let A := (P.pow α).tensor J
  have hA : A.IsAmple := hA' (max N t) (le_max_left _ _)
  have hα : t ≤ α := by dsimp [α] <;> nlinarith [le_max_right N t]
  have hpos : 0 < (α:ℝ)*H+w*c := by
    have ht' := (div_lt_iff₀ hHR).mp ht
    have hαR : (t:ℝ) ≤ α := by exact_mod_cast hα
    nlinarith only [ht',mul_le_mul_of_nonneg_right hαR hHR.le]
  intro C
  change 0 ≤ (curveDegree T P C:ℝ)+w*∑ i,(curveDegree T (B.exceptionalIdeal i) C:ℝ)
  rw [← Int.cast_sum,← B.total_ideal_degree_s01 S A hA J ι hJ C]
  by_contra hnot
  have hneg : (curveDegree T P C:ℝ)+w*curveDegree T J C < 0 := lt_of_not_ge hnot
  let u := curveDegree T P C
  let v := curveDegree T J C
  obtain ⟨I,τ,hI⟩ := C.invertible_ideal_s01 T
  have hPI : mixedEuler T P I = -u := C.ideal_mixed_degree_s01 T A hA I τ hI P
  have hJI : mixedEuler T J I = -v := C.ideal_mixed_degree_s01 T A hA I τ hI J
  obtain ⟨k,m,b,hk,hm,hb,hmk,hq,hample⟩ := negative_boundary_perturbation
    H c u v (selfIntersection T I) (α:ℤ) r w hH hr hw hvol hc hneg hpos
  let D := (P.pow k).tensor (J.pow m)
  let M := (D.pow 1).tensor (I.pow b)
  have hJP : mixedEuler T J P = 0 := by rw [mixedEuler_comm]; exact hPJ
  have hAP : mixedEuler T A P = (α:ℤ)*H := by
    change mixedEuler T ((P.pow α).tensor J) P = _
    rw [mixedEuler_tensor_left_general_s01 T A hA,mixedEuler_pow_left_general_s01 T A hA,
      mixedEuler_self,hPP,hJP]
    ring
  have hAJ : mixedEuler T A J = c := by
    change mixedEuler T ((P.pow α).tensor J) J = _
    rw [mixedEuler_tensor_left_general_s01 T A hA,mixedEuler_pow_left_general_s01 T A hA,
      hPJ,mixedEuler_self]
    ring
  have hAI : mixedEuler T A I = -((α:ℤ)*u+v) := by
    change mixedEuler T ((P.pow α).tensor J) I = _
    rw [mixedEuler_tensor_left_general_s01 T A hA,mixedEuler_pow_left_general_s01 T A hA,hPI,hJI]
    ring
  have hAD : mixedEuler T A D = (α:ℤ)*k*H+m*c := by
    change mixedEuler T A ((P.pow k).tensor (J.pow m)) = _
    rw [mixedEuler_tensor_right_general_s01 T A hA,mixedEuler_pow_right_general_s01 T A hA,
      mixedEuler_pow_right_general_s01 T A hA,hAP,hAJ]
    ring
  have hDI : mixedEuler T D I = -((k:ℤ)*u+(m:ℤ)*v) := by
    change mixedEuler T ((P.pow k).tensor (J.pow m)) I = _
    rw [mixedEuler_tensor_left_general_s01 T A hA,mixedEuler_pow_left_general_s01 T A hA,
      mixedEuler_pow_left_general_s01 T A hA,hPI,hJI]
    ring
  have hDD : selfIntersection T D = (k:ℤ)^2*H+(m:ℤ)^2*c := by
    change selfIntersection T ((P.pow k).tensor (J.pow m)) = _
    rw [T.selfIntersection_twist_general_s01 A hA,hPP,hPJ]
    ring
  have hMM : 0 < selfIntersection T M := by
    change 0 < selfIntersection T ((D.pow 1).tensor (I.pow b))
    rw [T.selfIntersection_twist_general_s01 A hA,hDD,hDI]
    convert hq using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  have hAM : 0 ≤ mixedEuler T A M := by
    change 0 ≤ mixedEuler T A ((D.pow 1).tensor (I.pow b))
    rw [mixedEuler_tensor_right_general_s01 T A hA,mixedEuler_pow_right_general_s01 T A hA,
      mixedEuler_pow_right_general_s01 T A hA,hAD,hAI]
    convert hample using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  obtain ⟨n,hn,hs⟩ := T.positive_square_eventually_effective_s01 A hA M hMM hAM
  obtain ⟨s,hs0⟩ := hs n le_rfl
  have hbound := @PointBlowup.effective_twist_bound_s01 S L hL r p B J ι hJ w hw.le hC
    I τ hI.1 k m b n hn s hs0
  have hlt := mul_lt_mul_of_pos_left hmk (mul_pos hw hrR)
  have hv := congrArg (fun z : ℝ => (k:ℝ)*z) hvol
  push_cast at hbound
  nlinarith only [hbound,hlt,hv]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Cohomology_CycleStructures
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MaximalSeshadri.PlaneCech
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
instance cyclesAddCommGroup (A B C : Submodule K M) : AddCommGroup (cycles A B C) :=
  Submodule.addCommGroup _
instance cyclesModule (A B C : Submodule K M) : Module K (cycles A B C) :=
  Submodule.module _
instance cyclesHasQuotient (A B C : Submodule K M) :
    HasQuotient (cycles A B C) (Submodule K (cycles A B C)) :=
  Submodule.hasQuotient
end MaximalSeshadri.PlaneCech

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_Configurations
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {F : Type} [Field F]

theorem exists_distinct_rational_tuple [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left]
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n X.hom] (r : ℕ) :
    ∃ p : Fin r → RationalPoint X, Function.Injective (fun i => rationalImage (p i)) := by
  classical
  have hu := smooth_scheme_uncountable_rational_points X.hom n hn
  let R := Set.range fun p : {p : Spec (CommRingCat.of F) ⟶ X.left // p ≫ X.hom = 𝟙 _} =>
    p.val (fieldPoint F)
  let : Infinite R := (show R.Infinite from fun h => hu h.countable).to_subtype
  let b : ℕ ↪ R := Infinite.natEmbedding R
  choose p hp using (fun k : ℕ => (b k).property)
  refine ⟨fun i => Over.homMk (p i.val).val (p i.val).property, ?_⟩
  intro i j h
  apply Fin.val_injective
  apply b.injective
  apply Subtype.ext
  change (p i.val).val (fieldPoint F) = (p j.val).val (fieldPoint F) at h
  simpa only [hp] using h

end
end MaximalSeshadri

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
-- module Solutions.Q223_SES.Seshadri_Interpolation_VeryGeneralInterpolation
attribute [-instance] _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

theorem Surface.eventual_very_general_interpolation (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ U : S.scheme.affineOpens, ∃ eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
        ∃ Z : ℕ → Set (Configuration S r),
          (∀ n, IsClosed (Z n) ∧ Z n ≠ Set.univ) ∧
          (∃ p : Configuration S r, ∀ n, p ∉ Z n) ∧
          ∀ p : Configuration S r, (∀ n, p ∉ Z n) →
            ∀ k m : ℕ, 0 < k → 0 < m →
            (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
            ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
                Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
              (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
              ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
                (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
                  (RingHom.ker (ρ i))^m) → s = 0 := by
  classical
  obtain ⟨U,eL,t,het,r₀,hr₀,htest⟩ := S.eventual_etale_affine_section_test_s01 L hL
  let := (openScalars S.structureMap U.1).toAlgebra
  refine ⟨U,eL,r₀,hr₀,?_⟩
  intro r hr
  let Good (a : ℕ × ℕ) : Prop := 0 < a.1 ∧ 0 < a.2 ∧
    (a.1:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (a.2:ℝ)
  let Test (a : ℕ × ℕ) (p : Configuration S r) : Prop :=
    ∃ ρ : Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
      (∀ i, affineComplexPoint S.structureMap U (ρ i) = p.val i) ∧
      ∀ s : O S.scheme ⟶ (L.pow a.1).sheaf,
        (∀ i, affineCoefficient U (localPowerFrame U.1 eL a.1) s ∈
          (RingHom.ker (ρ i))^a.2) → s = 0
  have hW (a : ℕ × ℕ) (ha : Good a) :
      ∃ W : (surfacePower S r).left.Opens,
        (∃ p : Configuration S r, tupleImage S r p.val ∈ W) ∧
        ∀ p : Configuration S r, tupleImage S r p.val ∈ W → Test a p := by
    obtain ⟨ρ,hρ,hsep⟩ := htest r hr a.1 a.2 ha.1 ha.2.1 ha.2.2
    let ℓ := affineCoefficientLinear S.structureMap U (localPowerFrame U.1 eL a.1)
    obtain ⟨W,hρW,hW⟩ := @exists_open_jet_configuration_s01 S r U t het _ _
      (complexSectionModule S.structureMap (L.pow a.1).sheaf)
      (S.sections_finite L hL (L.pow a.1)) ℓ a.2 ha.2.1 ρ hsep
    let p : Configuration S r := ⟨fun i => affineComplexPoint S.structureMap U (ρ i), by
      intro i j hij
      apply hρ
      exact affineComplexPoint_image_injective S.structureMap U hij⟩
    exact ⟨W,⟨p,hρW⟩,fun q hq => hW q.val hq⟩
  choose W hmem hTest using hW
  let V (a : ℕ × ℕ) : (surfacePower S r).left.Opens :=
    if h : Good a then W a h else ⊤
  let Z : ℕ → Set (Configuration S r) := fun n =>
    {p | tupleImage S r p.val ∉ V (Nat.unpair n)}
  have hZ (n : ℕ) : IsClosed (Z n) ∧ Z n ≠ Set.univ := by
    constructor
    · have hc : Continuous (fun p : Configuration S r => tupleImage S r p.val) := by
        change @Continuous _ _ (TopologicalSpace.induced Subtype.val
          (TopologicalSpace.induced (tupleImage S r) inferInstance)) _ _
        rw [induced_compose]
        exact continuous_induced_dom
      exact ((V (Nat.unpair n)).isOpen.preimage hc).isClosed_compl
    · intro heq
      by_cases h : Good (Nat.unpair n)
      · obtain ⟨p,hp⟩ := hmem _ h
        have hpZ : p ∈ Z n := heq ▸ Set.mem_univ p
        exact hpZ (by simpa [V,h] using hp)
      · have : IsIntegral (Over.mk S.structureMap).left := S.integral
        have : SmoothOfRelativeDimension 2 (Over.mk S.structureMap).hom := S.smooth
        obtain ⟨q,hq⟩ := exists_distinct_rational_tuple (Over.mk S.structureMap) 2
          (by norm_num) r
        let p : Configuration S r := ⟨q,hq⟩
        have hpZ : p ∈ Z n := heq ▸ Set.mem_univ p
        exact hpZ (by simp [V,h])
  refine ⟨Z,hZ, surface_configuration_outside_countable_closed_s01 S r Z
    (fun n => (hZ n).1) (fun n => (hZ n).2),?_⟩
  intro p hp k m hk hm hkm
  have hab : Good (k,m) := ⟨hk,hm,hkm⟩
  have hpV : tupleImage S r p.val ∈ V (k,m) := by
    have HH := hp (Nat.pair k m)
    simpa only [Z,Nat.unpair_pair,Set.mem_ofPred_eq,not_not] using HH
  exact hTest (k,m) hab p (by simpa [V,hab] using hpV)
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

theorem Surface.eventual_very_general_curve_lower (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      ∃ Z : ℕ → Set (Configuration S r),
        (∀ n, IsClosed (Z n) ∧ Z n ≠ Set.univ) ∧
        (∃ p : Configuration S r, ∀ n, p ∉ Z n) ∧
        ∀ p : Configuration S r, (∀ n, p ∉ Z n) → ∀ C : IntegralCurve S,
          Real.sqrt ((selfIntersection S L:ℝ)/r)*(totalMultiplicity S r C p:ℝ) ≤
            (curveDegree S L C:ℝ) := by
  obtain ⟨U,eL,r₀,hr₀,h⟩ := S.eventual_very_general_interpolation L hL
  refine ⟨r₀,hr₀,fun r hr => ?_⟩
  obtain ⟨Z,hZ,hne,ht⟩ := h r hr
  exact ⟨Z,hZ,hne,fun p hp C => curve_lower_of_homogeneous_section_test_s01 S L hL
    (hr₀.trans_le hr) p U eL (ht p hp) C⟩
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_BaseChangeNatural
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.BaseSections.instAddCommGroupCarrierSections _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.instAddCommGroupCarrierOpenSections _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MaximalSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Geometry MaximalSeshadri.TensorPure

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

@[reassoc] lemma naturality {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map a) ≫
      (iso f U N).hom =
    (iso f U M).hom ≫ (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  ext V x
  change (hom f U N).app V (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) x) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ((hom f U M).app V x)
  rw [hom_app,hom_app]
  exact (CategoryTheory.congr_fun (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op) x).symm

end
end MaximalSeshadri.OpenBaseChange

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                  
section

namespace MaximalSeshadri.Geometry

theorem maximalSeshadriConstants_oai (S : Surface) (L : LineBundle S.scheme)
    (hL : LineBundle.IsAmple S.scheme L) : EventualMaximalSeshadri S L := by
  obtain ⟨r₀,hr₀,h⟩ := S.eventual_very_general_curve_lower L hL
  refine ⟨r₀,hr₀,fun r hr => ?_⟩
  obtain ⟨Z,hZ,hne,hC⟩ := h r hr
  refine ⟨Z,hZ,hne,fun p hp => ?_⟩
  have hrpos : 0 < r := hr₀.trans_le hr
  obtain ⟨B⟩ := S.pointBlowup_exists_s01 L hL r p
  exact ⟨⟨B,B.boundaryNef_of_curve_bound S L hL hrpos (hC p hp)⟩,
    S.seshadri_eq_of_curve_lower_s01 L hL hrpos p (hC p hp)⟩

end MaximalSeshadri.Geometry

end



end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants_oai := @OAI.MaximalSeshadri.Geometry.maximalSeshadriConstants_oai

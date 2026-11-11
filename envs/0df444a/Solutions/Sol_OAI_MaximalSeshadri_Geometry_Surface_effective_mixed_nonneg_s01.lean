-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:33.735046+00:00
-- url     : https://prove2.me/submissions/5cba5758-55d5-4b40-86bb-9f55938f6915

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES009
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ample_degree_positive_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_degree_nonneg_of_restriction_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_IntegralCurve_ideal_mixed_degree_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_Surface_coprime_integral_section_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_tensor_s01
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_generated_curveDegree_eq_mixedEuler_s01

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

end MaximalSeshadri

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_CartierModule
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.InvertibleLocal

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open MaximalSeshadri.Geometry

theorem invertible_of_affine_equations {X : Scheme} (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) :
    InvertiblePullbackIdeal I (𝟙 X) := by
  apply invertible_of_local_equations
  intro x
  obtain ⟨U, hx, r, hr, he⟩ := hI x
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have hreg : IsLeftRegular (e.symm r) := by
    intro a b hab
    apply e.injective
    apply hr.1
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
  refine ⟨U, hx, e.symm r, ⟨hreg, hreg.right_of_commute (fun a => mul_comm _ a)⟩, ?_⟩
  rw [Scheme.IdealSheafData.comap_id, IdealPullback.comap_ι_top, he,
    Ideal.map_span, Set.image_singleton]
  rfl

end
end MaximalSeshadri.InvertibleLocal
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothAffineRefinement
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.Projective.boolChartUnique _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                           

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}}

theorem exists_standard_smooth_affine_inside
    (g : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n g]
    (W : X.Opens) (x : X) (hx : x ∈ W) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g U.1) := by
  obtain ⟨B, hB, V, hV, hxV, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := g) x
  have hBtop : B = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = g x := Subsingleton.elim _ _
    rw [hy]
    exact e hxV
  subst B
  let e₀ : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    RingEquiv.ofBijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension n (openScalars g V) := by
    convert hg.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e₀) using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨⟨X.basicOpen f, hV.basicOpen f⟩, hxf, hfW, ?_⟩
  let : IsLocalization.Away f Γ(X, X.basicOpen f) := hV.isLocalization_basicOpen f
  have hs := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (Γ(X, X.basicOpen f)) f (openScalars g V) hstd
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  exact (openScalars_restrict g (X.basicOpen_le f)).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierSection
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames
variable {X Y : Scheme}

lemma LineBundle.section_coefficient_regular [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) [Nonempty U.1]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    IsRegular (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) := by
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  have he := (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective
  apply he
  change U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) =
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι (0 : O X ⟶ L.sheaf)))
  exact h.trans (by rw [restrictSection_zero, coefficient_zero, map_zero])
end
end MaximalSeshadri.Geometry

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_FramedPullback
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

                                        

namespace MaximalSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

variable {X Y : Scheme.{0}}

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G := Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    have leftSection : uF.inv ≫ F.map s =
        restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) := by
      dsimp only [uF, F, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).inv ≫
          sectionMap) ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map_comp
            (pullbackUnitIso f).inv ((Scheme.Modules.pullback f).map s)).symm)
    have rightSection : uG.inv ≫ G.map s =
        pullbackSection (f ∣_ U) (restrictSection U.ι s) := by
      dsimp only [uG, G, restrictSection, pullbackSection, Iso.trans,
        Functor.mapIso, Functor.comp]
      exact (Category.assoc _ _ _).trans
        (congrArg (fun sectionMap => (pullbackUnitIso (f ∣_ U)).inv ≫ sectionMap)
          ((Scheme.Modules.pullback (f ∣_ U)).map_comp
            (Scheme.Modules.restrictUnitIso U.ι).inv
            ((Scheme.Modules.restrictFunctor U.ι).map s)).symm)
    exact (congrArg (coefficient eF) leftSection).symm.trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) rightSection))
  rw [he', coefficient_pullback]

end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeometricDivision
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
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
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma section_value_naturality {M : X.Modules} (s : O X ⟶ M)
    {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) =
      s.app V (1 : Γ(X,V)) := by
  have ht := CategoryTheory.congr_fun (s.mapPresheaf.naturality (homOfLE h).op)
    (1 : Γ(X,U))
  change s.app V (X.presheaf.map (homOfLE h).op (1 : Γ(X,U))) =
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) at ht
  simpa only [map_one] using ht.symm

lemma section_eq_zero_of_top_value {M : X.Modules} (s : O X ⟶ M)
    (hs : s.app ⊤ (1 : Γ(X,⊤)) = 0) : s = 0 := by
  ext U a
  change Γ(X,U) at a
  change s.app U a = 0
  have h := s.app_smul (r := a) (x := (1 : Γ(X,U)))
  change s.app U (a*1 : Γ(X,U)) = a • s.app U (1 : Γ(X,U)) at h
  rw [mul_one] at h
  rw [h, ← section_value_naturality s (show U ≤ ⊤ from le_top), hs,map_zero,smul_zero]

lemma section_eq_zero_of_local_restrictions {M : X.Modules} (s : O X ⟶ M)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictSection U.ι s = 0) : s = 0 := by
  apply section_eq_zero_of_top_value
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  apply TopCat.Presheaf.section_ext F ⊤ (s.app ⊤ (1 : Γ(X,⊤))) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := hs x
  have hv : s.app U (1 : Γ(X,U)) = 0 := by
    have ht := congrArg (fun q : O U.toScheme ⟶ M.restrict U.ι =>
      q.app ⊤ (1 : Γ(U.toScheme,⊤))) hU
    change s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))) = 0 at ht
    rw [map_one] at ht
    have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
      rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
    suffices h : ∀ V : X.Opens, V = U → s.app V (1 : Γ(X,V)) = 0 →
        s.app U (1 : Γ(X,U)) = 0 from h _ htop ht
    intro V he ht
    subst V
    exact ht
  change M.presheaf.germ ⊤ x hx (s.app ⊤ (1 : Γ(X,⊤))) =
    M.presheaf.germ ⊤ x hx 0
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (show U ≤ ⊤ from le_top)) x hxU]
  rw [section_value_naturality s, hv, map_zero, map_zero]

theorem global_division_of_local_lifts {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (s : O X ⟶ N)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ t : O U.toScheme ⟶ M.restrict U.ι,
        t ≫ (Scheme.Modules.restrictFunctor U.ι).map f = restrictSection U.ι s) :
    ∃! t : O X ⟶ M, t ≫ f = s := by
  have hz : s ≫ cokernel.π f = 0 := by
    apply section_eq_zero_of_local_restrictions
    intro x
    obtain ⟨U,hx,t,ht⟩ := hs x
    refine ⟨U,hx,?_⟩
    have hc : restrictSection U.ι (s ≫ cokernel.π f) =
        restrictSection U.ι s ≫ (Scheme.Modules.restrictFunctor U.ι).map (cokernel.π f) := by
      exact (congrArg (fun morphism :
          (Scheme.Modules.restrictFunctor U.ι).obj (O X) ⟶
            (Scheme.Modules.restrictFunctor U.ι).obj (cokernel f) =>
          (Scheme.Modules.restrictUnitIso U.ι).inv ≫ morphism)
        ((Scheme.Modules.restrictFunctor U.ι).map_comp s (cokernel.π f))).trans
          (Category.assoc _ _ _).symm
    rw [hc, ← ht, Category.assoc, ← Functor.map_comp,cokernel.condition,Functor.map_zero,comp_zero]
  refine ⟨Abelian.monoLift _ s hz,Abelian.monoLift_comp _ s hz,?_⟩
  intro t ht
  apply (cancel_mono f).mp
  rw [ht,Abelian.monoLift_comp]

lemma framed_local_division {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X)
    (f : M ⟶ N) (s : O X ⟶ N)
    (hs : coefficient d s ∈ Ideal.span {endValue (e.inv ≫ f ≫ d.hom)}) :
    ∃ t : O X ⟶ M, t ≫ f = s := by
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hs
  refine ⟨scalarEnd r ≫ e.inv,?_⟩
  apply (cancel_mono d.hom).mp
  apply endValue_injective
  rw [Category.assoc,Category.assoc,endValue_comp,endValue_scalarEnd]
  change r * endValue (e.inv ≫ f ≫ d.hom) = coefficient d s
  rw [mul_comm,← hr]

end
end MaximalSeshadri.Geometry

end


end
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

lemma tensor_inclusion_ideal (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom))} =
    Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let scalar : O U.1.toScheme ⟶ O U.1.toScheme := e.inv ≫
    (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom
  let twist : O U.1.toScheme ≅ O U.1.toScheme := tensorUnitTwist M U.1 f
  have framed : (tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom =
      scalar ≫ twist.inv := tensor_inclusion_framed J M ι U.1 e f
  refine (congrArg (fun morphism : O U.1.toScheme ⟶ O U.1.toScheme =>
    Ideal.span {U.1.topIso.hom (endValue morphism)}) framed).trans ?_
  change Ideal.span {U.1.topIso.hom (endValue (scalar ≫ twist.inv))} =
    Ideal.span {U.1.topIso.hom (endValue scalar)}
  rw [endValue_comp, map_mul, ← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue twist.inv) :=
    (end_isIso_iff twist.inv).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom), Ideal.mul_top]

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierResidual
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.PullbackTensor.line_isIso _root_.OAI.MaximalSeshadri.PullbackTensor.unit_isIso _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.TensorPure.tensorSection_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

variable {X Y : Scheme.{0}}

lemma pullback_zero_coefficient_mem_closed (_p : X ⟶ Spec (CommRingCat.of ℂ))
    (f : Y ⟶ X) [IsClosedImmersion f] (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hs : pullbackSection f s = 0) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    affineCoefficient U e s ∈ f.ker.ideal U := by
  rw [Scheme.Hom.ker_apply]
  change f.app U.1 (affineCoefficient U e s) = 0
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame f U.1 e s
  have hzero : coefficient eF
      (restrictSection (f ⁻¹ᵁ U.1).ι (pullbackSection f s)) = 0 := by
    rw [hs,restrictSection_zero,coefficient_zero]
  rw [he] at hzero
  apply ((ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U.1).topIso.inv).injective)
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top] at hzero
  simpa only [affineCoefficient, Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply,
    map_zero] using hzero

theorem IntegralCurve.divide_section (S : Surface) (C : IntegralCurve S)
    (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (s : O S.scheme ⟶ M.sheaf) (hs : pullbackSection C.embedding s = 0) :
    ∃! q : O S.scheme ⟶ (J.tensor M).sheaf, q ≫ tensorInclusion J M ι = s := by
  let : Mono (C := S.scheme.Modules) (tensorInclusion J M ι) :=
    @tensorInclusion_mono S.scheme J M ι hJ.1
  apply global_division_of_local_lifts
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  apply framed_local_division (tensorFrame J M U.1 e f) f
  have hm := pullback_zero_coefficient_mem_closed S.structureMap C.embedding M s hs U f
  rw [InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ U e,
    ← tensor_inclusion_ideal J M ι U e f,Ideal.mem_span_singleton] at hm
  obtain ⟨a,ha⟩ := hm
  rw [Ideal.mem_span_singleton]
  refine ⟨U.1.topIso.inv a,?_⟩
  have H := congrArg (fun sectionValue => U.1.topIso.inv sectionValue) ha
  simpa only [affineCoefficient,map_mul,U.1.topIso.hom_inv_id_apply] using H

lemma affineCoefficient_tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (q : O X ⟶ (J.tensor M).sheaf) :
    Associated
      (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
        affineCoefficient U (tensorFrame J M U.1 e f) q)
      (affineCoefficient U f (q ≫ tensorInclusion J M ι)) := by
  unfold affineCoefficient
  have hvalue : endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) =
      endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom) *
        endValue (tensorUnitTwist M U.1 f).inv :=
    (congrArg (endValue (X := U.1.toScheme))
      (tensor_inclusion_framed J M ι U.1 e f)).trans
        (endValue_comp _ _)
  rw [show restrictSection U.1.ι (q ≫ tensorInclusion J M ι) =
    restrictSection U.1.ι q ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
      (tensorInclusion J M ι) by
        exact (congrArg (fun morphism => (Scheme.Modules.restrictUnitIso U.1.ι).inv ≫
          morphism) ((Scheme.Modules.restrictFunctor U.1.ι).map_comp q
            (tensorInclusion J M ι))).trans (Category.assoc _ _ _).symm]
  rw [coefficient_postcompose (tensorFrame J M U.1 e f) f,
    hvalue, map_mul, map_mul]
  have hu : IsUnit (U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).inv)) :=
    ((end_isIso_iff _).mp (inferInstance : IsIso (tensorUnitTwist M U.1 f).inv)).map
      U.1.topIso.hom.hom
  rw [show U.1.topIso.hom (coefficient (tensorFrame J M U.1 e f) (restrictSection U.1.ι q)) *
    (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
      U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).inv)) =
    (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
      U.1.topIso.hom (coefficient (tensorFrame J M U.1 e f) (restrictSection U.1.ι q))) *
      U.1.topIso.hom (endValue (tensorUnitTwist M U.1 f).inv) by ring]
  simpa only [mul_one] using (associated_one_iff_isUnit.mpr hu).symm.mul_left
    (U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom)) *
      U.1.topIso.hom (coefficient (tensorFrame J M U.1 e f) (restrictSection U.1.ι q)))

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_GeneratedEtaleCoordinates
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open KaehlerDifferential

section CoordinateBasis
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

theorem formallyUnramified_polynomial_of_basis
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyUnramified (MvPolynomial ι R) S := by
  have hz : KaehlerDifferential.map R (MvPolynomial ι R) S S = 0 := by
    apply b.ext
    intro i
    rw [hb, KaehlerDifferential.map_D]
    change D (MvPolynomial ι R) S
      (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) = 0
    exact Derivation.map_algebraMap _ _
  constructor
  constructor
  intro x y
  obtain ⟨x, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S x
  obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective R (MvPolynomial ι R) S y
  rw [hz]
  rfl

theorem formallySmooth_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallySmooth (MvPolynomial ι R) S := by
  classical
  apply Algebra.FormallySmooth.of_comp_surjective
  intro B _ _ I hI f
  let : Algebra R B := Algebra.compHom B (algebraMap R (MvPolynomial ι R))
  let : IsScalarTower R (MvPolynomial ι R) B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R S I hI (f.restrictScalars R)
  let : Algebra S B := g.toRingHom.toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let correction (i : ι) : I := ⟨algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) -
      g (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)), by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, sub_eq_zero]
    change _ = (Ideal.Quotient.mkₐ R I) (g _)
    rw [← AlgHom.comp_apply, hg]
    exact (f.commutes _).symm⟩
  let d : Derivation R S I := (b.constr S correction).compDer (D R S)
  let g' : S →ₐ[R] B := liftOfDerivationToSquareZero I hI d
  have hcoords (i : ι) : g' (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i)) =
      algebraMap (MvPolynomial ι R) B (MvPolynomial.X i) := by
    change ((b.constr S correction) (D R S (algebraMap _ _ (MvPolynomial.X i))) : B) +
      g (algebraMap _ _ (MvPolynomial.X i)) = _
    rw [← hb, b.constr_basis]
    exact sub_add_cancel _ _
  have hcomm : g'.comp (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) =
      IsScalarTower.toAlgHom R (MvPolynomial ι R) B := by
    apply MvPolynomial.algHom_ext
    exact hcoords
  let lift : S →ₐ[MvPolynomial ι R] B :=
    { g'.toRingHom with commutes' := fun p => AlgHom.congr_fun hcomm p }
  refine ⟨lift, ?_⟩
  ext s
  change Ideal.Quotient.mk I (g' s) = f s
  rw [liftOfDerivationToSquareZero_mk_apply]
  exact AlgHom.congr_fun hg s

theorem formallyEtale_polynomial_of_basis [Algebra.FormallySmooth R S]
    (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (algebraMap (MvPolynomial ι R) S (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) S := by
  let := formallySmooth_polynomial_of_basis b hb
  let := formallyUnramified_polynomial_of_basis b hb
  constructor <;> infer_instance

end CoordinateBasis

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_formallyEtale {σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.FormallyEtale := by
  let φ := MvPolynomial.aeval (R := R) (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let := P.isStandardSmooth
  change Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  apply formallyEtale_polynomial_of_basis P.basisKaehler
  intro i
  rw [P.basisKaehler_apply]
  change D R S (P.val i) = D R S (φ (MvPolynomial.X i))
  simp only [φ, MvPolynomial.aeval_X]

end

noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem presentation_coordinate_etale {ι σ : Type*} [Finite σ] [Finite ι]
    (P : Algebra.SubmersivePresentation R S ι σ) :
    (MvPolynomial.aeval (R := R)
      (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R)
    (fun i : ((Set.range P.map)ᶜ : Set ι) => P.val i)
  have hφ := presentation_coordinate_formallyEtale P
  let : Algebra (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation R S := P.finitePresentation_of_isFinite
  let : Algebra.FinitePresentation (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S := hφ
  change Algebra.Etale (MvPolynomial ((Set.range P.map)ᶜ : Set ι) R) S
  constructor <;> infer_instance

theorem exists_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n R S] :
    ∃ (κ : Type) (_ : Finite κ) (x : κ → S), Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R) x).toRingHom.Etale := by
  classical
  obtain ⟨κ, σ, hσ, hκ, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := n) (R := R) (S := S)
  let : Fintype κ := Fintype.ofFinite κ
  let : Fintype σ := Fintype.ofFinite σ
  refine ⟨((Set.range P.map)ᶜ : Set κ), inferInstance, (fun i => P.val i), ?_,
    presentation_coordinate_etale P⟩
  rw [← hP]
  simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
    Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]

end

end MaximalSeshadri.AlgebraicJets


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtalePointChart
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

lemma etale_aeval_reindex {ι κ : Type} (x : ι → S) (h : (aeval (R := K) x).toRingHom.Etale)
    (e : κ ≃ ι) : (aeval (R := K) (fun i => x (e i))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (renameEquiv K e).toRingEquiv h
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply RingHom.ext
  intro p
  change aeval (fun i => x (e i)) p = aeval x (rename e p)
  exact (aeval_rename e x p).symm

lemma etale_aeval_center {ι : Type} (x : ι → S)
    (h : (aeval (R := K) x).toRingHom.Etale) (ρ : S →ₐ[K] K) :
    (aeval (R := K) (fun i => x i - algebraMap K S (ρ (x i)))).toRingHom.Etale := by
  have he := RingHom.Etale.respectsIso.2 (aeval (R := K) x).toRingHom
    (polynomialTranslate (fun i => ρ (x i))).symm.toRingEquiv h
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  apply ringHom_ext
  · intro c; simp [polynomialTranslate]
  · intro i; simp [polynomialTranslate]

theorem exists_centered_etale_coordinates (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K S] (ρ : S →ₐ[K] K) :
    ∃ x : Fin n → S, (∀ i, ρ (x i) = 0) ∧
      (aeval (R := K) x).toRingHom.Etale := by
  obtain ⟨κ, hκ, x, hcard, hx⟩ := exists_etale_coordinates (R := K) (S := S) n
  let : Fintype κ := Fintype.ofFinite κ
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq (by simpa using hcard)
  let y := fun i : Fin n => x (e.symm i)
  refine ⟨fun i => y i - algebraMap K S (ρ (y i)), ?_,
    etale_aeval_center y (etale_aeval_reindex x hx e.symm) ρ⟩
  intro i
  simp

end

noncomputable section
variable {R : Type*} [CommRing R]

lemma exists_away_map_le (I J p : Ideal R) [p.IsPrime] (hI : I.FG)
    (hle : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ I.map (algebraMap R (Localization.Away s)) ≤
      J.map (algebraMap R (Localization.Away s)) := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hden : ∀ x : t, ∃ s : p.primeCompl, s.val * x.val ∈ J := by
    intro x
    have hx : algebraMap R (Localization.AtPrime p) x.val ∈
        J.map (algebraMap R (Localization.AtPrime p)) :=
      hle (Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span x.property))
    obtain ⟨s, hs, h⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl _ J x.val).mp hx
    exact ⟨⟨s, hs⟩, h⟩
  choose d hd using hden
  let s : p.primeCompl := ∏ x : t, d x
  refine ⟨s.val, s.property, Ideal.map_le_iff_le_comap.mpr ?_⟩
  rw [← ht, Ideal.span_le]
  intro x hx
  have hdiv : d ⟨x, hx⟩ ∣ s := Finset.dvd_prod_of_mem d (Finset.mem_univ _)
  obtain ⟨c, hc⟩ := hdiv
  have hmul : s.val * x ∈ J := by
    have h := J.mul_mem_left c.val (hd ⟨x, hx⟩)
    simpa only [hc, Submonoid.coe_mul, mul_assoc, mul_left_comm] using h
  change algebraMap R (Localization.Away s.val) x ∈
    J.map (algebraMap R (Localization.Away s.val))
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers s.val) _ J x).mpr
  exact ⟨s.val, Submonoid.mem_powers _, hmul⟩

lemma exists_away_map_eq_of_le (I J p : Ideal R) [p.IsPrime] (hI : I.FG)
    (hJI : J ≤ I)
    (heq : I.map (algebraMap R (Localization.AtPrime p)) =
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s : R, s ∉ p ∧ I.map (algebraMap R (Localization.Away s)) =
      J.map (algebraMap R (Localization.Away s)) := by
  obtain ⟨s, hs, hle⟩ := exists_away_map_le I J p hI heq.le
  exact ⟨s, hs, le_antisymm hle (Ideal.map_mono hJI)⟩

end

noncomputable section
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma unramified_map_under_local [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] (q : Ideal S) [q.IsPrime] :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      q.map (algebraMap S (Localization.AtPrime q)) := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyUnramified R Sq := Algebra.FormallyUnramified.comp R S Sq
  let : Algebra.FormallyUnramified Rp Sq :=
    Algebra.FormallyUnramified.of_restrictScalars R Rp Sq
  have hmax : (maximalIdeal Rp).map (algebraMap Rp Sq) = maximalIdeal Sq :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    ← IsLocalization.AtPrime.map_eq_maximalIdeal q Sq] at hmax
  exact hmax

end

end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_SmoothSurfaceDimension
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section

namespace MaximalSeshadri.LocalCurve
noncomputable section

open MvPolynomial
open MaximalSeshadri.AlgebraicJets

theorem two_le_dimension_of_standard_smooth {K S : Type} [Field K] [CommRing S]
    [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 2 K S]
    (ρ : S →ₐ[K] K) : 2 ≤ ringKrullDim S := by
  obtain ⟨x,hx,he⟩ := exists_centered_etale_coordinates 2 ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin 2) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin 2) K) S := he
  let q := RingHom.ker ρ
  have : q.IsPrime := RingHom.ker_isPrime ρ
  have hq : q.under (MvPolynomial (Fin 2) K) = idealOfVars (Fin 2) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  let : (idealOfVars (Fin 2) K).IsPrime := by
    rw [idealOfVars_eq_ker_constantCoeff]
    exact RingHom.ker_isPrime _
  let : q.LiesOver (idealOfVars (Fin 2) K) := ⟨hq.symm⟩
  let P : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {X (0 : Fin 2)}
  let : P.IsPrime := (Ideal.span_singleton_prime (X_ne_zero 0)).mpr X_prime
  have hP : P < idealOfVars (Fin 2) K := by
    refine lt_of_le_of_ne (Ideal.span_le.mpr (by
      rintro _ rfl
      exact Ideal.subset_span ⟨0,rfl⟩)) ?_
    intro H
    have h1 : X (1 : Fin 2) ∈ P := H ▸ Ideal.subset_span ⟨1,rfl⟩
    have hd : (X (0 : Fin 2) : MvPolynomial (Fin 2) K) ∣ X 1 :=
      Ideal.mem_span_singleton.mp h1
    have := X_dvd_X.mp hd
    norm_num at this
  obtain ⟨Q,hQ,hQP,hQL⟩ := Ideal.exists_ideal_lt_liesOver_of_lt q hP
  have := hQP
  have := hQL
  have hbot : (⊥ : Ideal (MvPolynomial (Fin 2) K)) < P := by
    apply bot_lt_iff_ne_bot.mpr
    intro H
    have h0 : X (0 : Fin 2) ∈ P := Ideal.subset_span (by simp)
    rw [H,Ideal.mem_bot] at h0
    exact X_ne_zero 0 h0
  obtain ⟨Q₀,hQ₀,hQ₀P,hQ₀L⟩ := Ideal.exists_ideal_lt_liesOver_of_lt Q hbot
  let l : LTSeries (PrimeSpectrum S) :=
    ((RelSeries.singleton {(a,b) : PrimeSpectrum S × PrimeSpectrum S | a < b} (⟨Q₀,hQ₀P⟩ : PrimeSpectrum S)).snoc
      (⟨Q,hQP⟩ : PrimeSpectrum S) hQ₀).snoc (⟨q,inferInstance⟩ : PrimeSpectrum S) hQ
  simpa only [show l.length = 2 from rfl, Nat.cast_ofNat, ringKrullDim] using
    Order.LTSeries.length_le_krullDim l
end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma Surface.two_le_dimension (S : Surface) : 2 ≤ topologicalKrullDim S.scheme := by
  obtain ⟨U,hxU,hU,hstd⟩ := exists_standard_smooth_affine_inside S.structureMap 2
    ⊤ (Classical.ofNonempty : S.scheme) (by trivial)
  let : Nonempty U.1 := ⟨⟨_,hxU⟩⟩
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) := hstd
  let : Algebra.IsStandardSmooth ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  have : Uncountable ℂ := by
    rw [← Cardinal.aleph0_lt_mk_iff, Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨ρ,-⟩ := point_avoiding_sequence (F := ℂ) (A := Γ(S.scheme,U.1))
    (fun _ => 1) (fun _ => one_ne_zero)
  have hd := LocalCurve.two_le_dimension_of_standard_smooth ρ
  have : IsOpenImmersion U.2.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.2
  have he := U.2.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  change topologicalKrullDim (PrimeSpectrum Γ(S.scheme,U.1)) ≤ _ at he
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at he
  exact hd.trans he
end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_IntegralCurveIdeal
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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

lemma IntegralCurve.affine_ideal_prime (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    (C.embedding.ker.ideal U).IsPrime := by
  have := hne
  rw [Scheme.Hom.ker_apply]
  exact RingHom.ker_isPrime _

lemma IntegralCurve.affine_ideal_not_maximal (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    ¬ (C.embedding.ker.ideal U).IsMaximal := by
  intro hmax
  have := hmax
  have : Smooth S.structureMap := SmoothOfRelativeDimension.smooth 2 S.structureMap
  have : JacobsonSpace C.scheme := LocallyOfFiniteType.jacobsonSpace
    (C.embedding ≫ S.structureMap)
  let I := C.embedding.ker.ideal U
  have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  have he : (Set.range C.embedding) ∩ (U.1 : Set S.scheme) =
      {U.2.fromSpec ⟨I,inferInstance⟩} := by
    rw [← hr,C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus,
      PrimeSpectrum.zeroLocus_eq_singleton]
    exact Set.image_singleton
  obtain ⟨x,hx⟩ := hne
  have hxq : C.embedding x = U.2.fromSpec ⟨I,inferInstance⟩ :=
    Set.mem_singleton_iff.mp (he ▸ ⟨Set.mem_range_self x,hx⟩)
  have hs : (C.embedding ⁻¹ᵁ U.1 : Set C.scheme) = {x} := by
    ext y
    constructor
    · intro hy
      apply Set.mem_singleton_iff.mpr
      apply C.embedding.isEmbedding.injective
      exact (Set.mem_singleton_iff.mp (he ▸ ⟨Set.mem_range_self y,hy⟩)).trans hxq.symm
    · rintro rfl
      exact hx
  have ho : IsOpen ({x} : Set C.scheme) := hs ▸ (C.embedding ⁻¹ᵁ U.1).isOpen
  have hc : IsClosed ({x} : Set C.scheme) :=
    isClosed_singleton_of_isLocallyClosed_singleton ho.isLocallyClosed
  have hu : ({x} : Set C.scheme) = Set.univ := by
    rw [← hc.closure_eq]
    exact (ho.dense (Set.singleton_nonempty x)).closure_eq
  have : Subsingleton C.scheme := ⟨fun y z => by
    have hy : y = x := Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ y)
    have hz : z = x := Set.mem_singleton_iff.mp (hu ▸ Set.mem_univ z)
    exact hy.trans hz.symm⟩
  have hd := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dimension] at hd
  norm_num at hd

lemma IntegralCurve.affine_ideal_ne_bot (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens) (hne : Nonempty (C.embedding ⁻¹ᵁ U.1)) :
    C.embedding.ker.ideal U ≠ ⊥ := by
  intro hzero
  have affineOpen : IsAffineOpen U.1 := U.2
  have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  have he := C.embedding.ker.coe_support_inter U
  rw [hr,← affineOpen.fromSpec_image_zeroLocus,hzero,PrimeSpectrum.zeroLocus_bot] at he
  change Set.range C.embedding ∩ (U.1 : Set S.scheme) =
    affineOpen.fromSpec '' (Set.univ : Set (Spec Γ(S.scheme, U.1))) at he
  rw [Set.image_univ,affineOpen.range_fromSpec] at he
  have hsub : (U.1 : Set S.scheme) ⊆ Set.range C.embedding := fun x hx =>
    (he.symm ▸ hx).1
  obtain ⟨x,hx⟩ := hne
  have hd := U.1.isOpen.dense ⟨C.embedding x,hx⟩
  have hall : Set.range C.embedding = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hd.closure_eq]
    exact closure_minimal hsub C.embedding.isClosedEmbedding.isClosed_range
  have hh : IsHomeomorph C.embedding := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨C.embedding.isEmbedding,Set.range_eq_univ.mp hall⟩
  have heq := hh.topologicalKrullDim_eq C.embedding
  have hdS := S.two_le_dimension
  rw [← heq,C.dimension] at hdS
  norm_num at hdS

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LocalCurvePrincipal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing

theorem principal_of_principal_maximal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (hm : (maximalIdeal R).IsPrincipal) : IsPrincipalIdealRing R := by
  classical
  obtain ⟨t,ht⟩ := hm
  constructor
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    infer_instance
  have hex : ∃ n : ℕ, ¬ I ≤ maximalIdeal R ^ (n+1) := by
    by_contra! H
    apply hI
    apply le_antisymm
    · rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top]
      apply le_iInf
      rintro (_ | n)
      · simp
      · exact H n
    · exact bot_le
  let n := Nat.find hex
  have hle : I ≤ maximalIdeal R ^ n := by
    cases hn : n with
    | zero => simp
    | succ j =>
      have hj : j < Nat.find hex := by change j < n; omega
      exact not_not.mp (Nat.find_min hex hj)
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp (Nat.find_spec hex)
  have hat : t^n ∣ a := by
    have H := hle ha
    rw [ht,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at H
    exact H
  obtain ⟨b,hb⟩ := hat
  have hbu : IsUnit b := by
    by_contra h
    have hbmem : b ∈ maximalIdeal R := h
    apply han
    change a ∉ maximalIdeal R ^ (n+1) at han
    have htn : t^n ∈ maximalIdeal R^n := by
      exact Ideal.pow_mem_pow (by rw [ht]; exact Ideal.subset_span (by simp)) n
    rw [hb]
    exact Ideal.mul_mem_mul htn hbmem
  have he : I = maximalIdeal R^n := by
    apply le_antisymm hle
    rw [ht,Ideal.span_singleton_pow,Ideal.span_le,Set.singleton_subset_iff]
    obtain ⟨u,hu⟩ := hbu
    have H := I.mul_mem_left (↑(u⁻¹) : R) ha
    rw [hb,← hu] at H
    simpa [mul_left_comm,mul_comm,mul_assoc] using H
  rw [he,ht,Ideal.span_singleton_pow]
  infer_instance

end
end MaximalSeshadri.LocalCurve

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_LocalBinaryPrime
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing

theorem prime_principal_of_binary_maximal_of_not_mem {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (a b : R) (hm : maximalIdeal R = Ideal.span {a,b})
    (p : Ideal R) [hp : p.IsPrime] (ha : a ∉ p) : p.IsPrincipal := by
  classical
  let J : Ideal R := Ideal.span {a}
  have hJm : J ≤ maximalIdeal R := by
    rw [hm]
    exact Ideal.span_mono (by simp)
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJm
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let q := Ideal.Quotient.mk J
  let : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hmQ : maximalIdeal (R ⧸ J) = Ideal.span {q b} := by
    rw [← map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective,hm,Ideal.map_span]
    have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp only [Set.image_insert_eq,Set.image_singleton,hqa,Ideal.span_insert_zero]
  let : IsPrincipalIdealRing (R ⧸ J) := principal_of_principal_maximal ⟨q b,hmQ⟩
  obtain ⟨c₀,hc₀⟩ := (inferInstance : (p.map q).IsPrincipal)
  change p.map q = Ideal.span {c₀} at hc₀
  have hc₀mem : c₀ ∈ p.map q := by rw [hc₀]; exact Ideal.subset_span (by simp)
  obtain ⟨c,hcp,hc⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hc₀mem
  have hp_le : p ≤ Ideal.span {c} ⊔ J • p := by
    intro z hz
    have hzq : q z ∈ Ideal.span {c₀} := by
      rw [← hc₀]
      exact Ideal.mem_map_of_mem q hz
    obtain ⟨w₀,hw₀⟩ := Ideal.mem_span_singleton.mp hzq
    obtain ⟨w,hw⟩ := Ideal.Quotient.mk_surjective w₀
    have hdiff : z-c*w ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (z-c*w) = 0
      rw [map_sub,map_mul,hc,hw,hw₀,sub_self]
    obtain ⟨t,ht⟩ := Ideal.mem_span_singleton.mp hdiff
    have hat : a*t ∈ p := ht ▸ p.sub_mem hz (p.mul_mem_right w hcp)
    have htp : t ∈ p := (hp.mem_or_mem hat).resolve_left ha
    have hleft : c*w ∈ Ideal.span {c} := Ideal.mem_span_singleton.mpr ⟨w,rfl⟩
    have hright : a*t ∈ J • p := by
      exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) htp
    have H := Submodule.add_mem_sup hleft hright
    have he : c*w+a*t = z := by linear_combination -ht
    exact he ▸ H
  have hple : p ≤ Ideal.span {c} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian p) (by rw [jacobson_eq_maximalIdeal _ bot_ne_top]; exact hJm) hp_le
  exact ⟨c,le_antisymm hple (Ideal.span_le.mpr (by simpa using hcp))⟩

theorem prime_principal_of_binary_maximal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (a b : R) (hm : maximalIdeal R = Ideal.span {a,b})
    (p : Ideal R) [hp : p.IsPrime] (hne : p ≠ maximalIdeal R) : p.IsPrincipal := by
  by_cases ha : a ∈ p
  · have hb : b ∉ p := by
      intro hb
      apply hne
      apply le_antisymm (le_maximalIdeal hp.ne_top)
      rw [hm,Ideal.span_le,Set.insert_subset_iff,Set.singleton_subset_iff]
      exact ⟨ha,hb⟩
    exact prime_principal_of_binary_maximal_of_not_mem b a
      (hm.trans Ideal.span_pair_comm) p hb
  · exact prime_principal_of_binary_maximal_of_not_mem a b hm p ha
end
end MaximalSeshadri.LocalCurve

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_SmoothCurvePrincipal
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing MvPolynomial
open MaximalSeshadri.AlgebraicJets

attribute [local instance] OAI.MaximalSeshadri.LocalCurve.residueKernelIsPrime
theorem standard_smooth_binary_maximal {K S : Type} [Field K] [CommRing S] [Algebra K S]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K) :
    ∃ a b : Localization.AtPrime (RingHom.ker ρ),
      maximalIdeal (Localization.AtPrime (RingHom.ker ρ)) = Ideal.span {a,b} := by
  obtain ⟨x,hx,he⟩ := exists_centered_etale_coordinates 2 ρ
  let φ := aeval (R := K) x
  let : Algebra (MvPolynomial (Fin 2) K) S := φ.toRingHom.toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.Etale (MvPolynomial (Fin 2) K) S := he
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2 (R := K) (S := S)
  let q := RingHom.ker ρ
  have hp : q.under (MvPolynomial (Fin 2) K) = idealOfVars (Fin 2) K := by
    rw [idealOfVars_eq_ker_constantCoeff]
    have hc : ρ.toRingHom.comp φ.toRingHom = constantCoeff := by
      apply ringHom_ext
      · intro c; simp [φ]
      · intro i; simpa [φ] using hx i
    change RingHom.ker (ρ.toRingHom.comp φ.toRingHom) = _
    rw [hc]
  have H := unramified_map_under_local (R := MvPolynomial (Fin 2) K) q
  rw [hp,IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q),
    Ideal.map_span,← Set.range_comp] at H
  have hr : Set.range ((algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q)) ∘ X) =
      {algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q) (X 0),
       algebraMap (MvPolynomial (Fin 2) K) (Localization.AtPrime q) (X 1)} := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hz
      rcases hz with h | h
      · exact ⟨0,h.symm⟩
      · exact ⟨1,(Set.mem_singleton_iff.mp h).symm⟩
  rw [hr] at H
  exact ⟨_,_,H.symm⟩

theorem spread_principal_prime {S : Type*} [CommRing S] [IsNoetherianRing S]
    (I q : Ideal S) [I.IsPrime] [q.IsPrime]
    (hI : (I.map (algebraMap S (Localization.AtPrime q))).IsPrincipal) :
    ∃ c : S, c ∈ I ∧ ∃ s : S, s ∉ q ∧
      I.map (algebraMap S (Localization.Away s)) =
      Ideal.span {algebraMap S (Localization.Away s) c} := by
  obtain ⟨u,hu⟩ := hI
  have hum : u ∈ I.map (algebraMap S (Localization.AtPrime q)) := by
    rw [hu]; exact Ideal.subset_span (by simp)
  obtain ⟨⟨c,d⟩,hcd⟩ := (IsLocalization.mem_map_algebraMap_iff q.primeCompl
    (Localization.AtPrime q)).mp hum
  have he : I.map (algebraMap S (Localization.AtPrime q)) =
      (Ideal.span {c.val}).map (algebraMap S (Localization.AtPrime q)) := by
    rw [hu,Ideal.map_span,Set.image_singleton,← hcd,
      Ideal.span_singleton_mul_right_unit (IsLocalization.map_units (Localization.AtPrime q) d)]
  obtain ⟨s,hs,hseq⟩ := exists_away_map_eq_of_le I (Ideal.span {c.val}) q
    (Ideal.fg_of_isNoetherianRing I) (Ideal.span_le.mpr (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) he
  exact ⟨c.val,c.property,s,hs,by simpa only [Ideal.map_span,Set.image_singleton] using hseq⟩

theorem standard_smooth_prime_principal_neighborhood {K S : Type} [Field K] [CommRing S]
    [Algebra K S] [Algebra.IsStandardSmoothOfRelativeDimension 2 K S]
    (ρ : S →ₐ[K] K) (I : Ideal S) [hI : I.IsPrime]
    (hle : I ≤ RingHom.ker ρ) (hne : I ≠ RingHom.ker ρ) :
    ∃ c : S, c ∈ I ∧ ∃ s : S, ρ s ≠ 0 ∧
      I.map (algebraMap S (Localization.Away s)) =
      Ideal.span {algebraMap S (Localization.Away s) c} := by
  let : Algebra.IsStandardSmooth K S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2 (R := K) (S := S)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  let q := RingHom.ker ρ
  have hdis : Disjoint (q.primeCompl : Set S) I :=
    Set.disjoint_left.mpr (fun _ hq hi => hq (hle hi))
  let : (I.map (algebraMap S (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) I hI hdis
  obtain ⟨a,b,hm⟩ := standard_smooth_binary_maximal ρ
  have hneq : I.map (algebraMap S (Localization.AtPrime q)) ≠ maximalIdeal (Localization.AtPrime q) := by
    intro H
    apply hne
    have HH := congrArg (Ideal.comap (algebraMap S (Localization.AtPrime q))) H
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)] at HH
    change (I.map _).under S = (q.map _).under S at HH
    rw [IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) hI hdis,
      IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q)
        (inferInstance : q.IsPrime) (Set.disjoint_left.mpr (fun _ hx hy => hx hy))] at HH
    exact HH
  have hp := prime_principal_of_binary_maximal a b hm
    (I.map (algebraMap S (Localization.AtPrime q))) hneq
  obtain ⟨c,hc,s,hs,he⟩ := spread_principal_prime I q hp
  exact ⟨c,hc,s,hs,he⟩
end
end MaximalSeshadri.LocalCurve

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_IntegralCurveCartier
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section

namespace MaximalSeshadri.LocalCurve
noncomputable section

lemma rational_of_maximal {K R : Type} [Field K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R]
    (q : Ideal R) [q.IsMaximal] : ∃ ρ : R →ₐ[K] K, RingHom.ker ρ = q := by
  let : Field (R ⧸ q) := Ideal.Quotient.field q
  let : Module.Finite K (R ⧸ q) := finite_of_finite_type_of_isJacobsonRing K _
  let φ : (R ⧸ q) →ₐ[K] K := IsAlgClosed.lift
  let ρ := φ.comp (Ideal.Quotient.mkₐ K q)
  refine ⟨ρ, ?_⟩
  ext x
  change φ (Ideal.Quotient.mk q x) = 0 ↔ x ∈ q
  change φ.toRingHom (Ideal.Quotient.mk q x) = 0 ↔ x ∈ q
  rw [← map_zero φ.toRingHom, φ.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end
end MaximalSeshadri.LocalCurve

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

lemma IntegralCurve.equation_at_support (S : Surface) (C : IntegralCurve S)
    (x : C.scheme) : ∃ U : S.scheme.affineOpens, C.embedding x ∈ U.1 ∧
      ∃ c : Γ(S.scheme,U.1), IsRegular c ∧ C.embedding.ker.ideal U = Ideal.span {c} := by
  obtain ⟨U,hxU,-,hstd⟩ := exists_standard_smooth_affine_inside S.structureMap 2
    ⊤ (C.embedding x) (by trivial)
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) := hstd
  let : Algebra.IsStandardSmooth ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  let : Nonempty (C.embedding ⁻¹ᵁ U.1) := ⟨⟨x,hxU⟩⟩
  let : Nonempty U.1 := ⟨⟨_,hxU⟩⟩
  let I := C.embedding.ker.ideal U
  let : I.IsPrime := C.affine_ideal_prime S U inferInstance
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have hxrange : C.embedding x ∈ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]; exact hxU
  obtain ⟨p,hp⟩ := hxrange
  have hIp : I ≤ p.asIdeal := by
    have hz : p ∈ PrimeSpectrum.zeroLocus I := by
      have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
        rw [Scheme.Hom.support_ker]
        exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
      have hh : C.embedding x ∈ (C.embedding.ker.support : Set S.scheme) ∩ U.1 :=
        ⟨hr ▸ Set.mem_range_self x,hxU⟩
      rw [C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus] at hh
      obtain ⟨p',hp',he⟩ := hh
      have ep : p' = p := U.2.fromSpec.isOpenEmbedding.injective (he.trans hp.symm)
      subst p'
      exact hp'
    exact hz
  obtain ⟨q,hq,hpq⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let := hq
  obtain ⟨ρ,hρ⟩ := LocalCurve.rational_of_maximal (K := ℂ) q
  have hIq : I ≠ RingHom.ker ρ := by
    rw [hρ]
    intro he
    exact C.affine_ideal_not_maximal S U inferInstance (by change I.IsMaximal; rw [he]; exact hq)
  obtain ⟨c,hc,s,hs,he⟩ := LocalCurve.standard_smooth_prime_principal_neighborhood
    ρ I (hρ.symm ▸ hIp.trans hpq) hIq
  let V : S.scheme.affineOpens := ⟨S.scheme.basicOpen s,U.2.basicOpen s⟩
  have hxV : C.embedding x ∈ V.1 := by
    have hz : p ∈ PrimeSpectrum.basicOpen s := fun hh =>
      hs (show s ∈ RingHom.ker ρ from hρ.symm ▸ hpq hh)
    rw [← U.2.fromSpec_preimage_basicOpen] at hz
    change U.2.fromSpec p ∈ S.scheme.basicOpen s at hz
    rwa [hp] at hz
  let : Nonempty (C.embedding ⁻¹ᵁ V.1) := ⟨⟨x,hxV⟩⟩
  let : Nonempty V.1 := ⟨⟨_,hxV⟩⟩
  let : IsLocalization.Away s Γ(S.scheme,V.1) := U.2.isLocalization_basicOpen s
  let e := IsLocalization.algEquiv (Submonoid.powers s)
    (Localization.Away s) Γ(S.scheme,V.1)
  let c' : Γ(S.scheme,V.1) := algebraMap Γ(S.scheme,U.1) Γ(S.scheme,V.1) c
  have he' : C.embedding.ker.ideal V = Ideal.span {c'} := by
    have H := congrArg (Ideal.map e.toRingHom) he
    rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H
    have comp : e.toRingHom.comp (algebraMap Γ(S.scheme,U.1) (Localization.Away s)) =
        algebraMap Γ(S.scheme,U.1) Γ(S.scheme,V.1) := by
      ext z; exact e.commutes z
    change I.map (e.toRingHom.comp (algebraMap Γ(S.scheme,U.1) (Localization.Away s))) =
      Ideal.span {e (algebraMap Γ(S.scheme,U.1) (Localization.Away s) c)} at H
    rw [comp,e.commutes] at H
    exact (C.embedding.ker.map_ideal_basicOpen U s).symm.trans H
  have hc' : c' ≠ 0 := by
    intro hz
    have H := C.affine_ideal_ne_bot S V inferInstance
    rw [he',hz,Ideal.span_singleton_zero] at H
    exact H rfl
  exact ⟨V,hxV,c',isRegular_iff_ne_zero.mpr hc',he'⟩

theorem IntegralCurve.invertible_ideal (S : Surface) (C : IntegralCurve S) :
    InvertiblePullbackIdeal C.embedding.ker (𝟙 S.scheme) := by
  apply InvertibleLocal.invertible_of_affine_equations
  intro x
  by_cases hx : x ∈ Set.range C.embedding
  · obtain ⟨z,rfl⟩ := hx
    exact C.equation_at_support S z
  · let W : S.scheme.Opens := ⟨(Set.range C.embedding)ᶜ,
      C.embedding.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨U,hU,hxU,hUW⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W from hx)
    have htop : C.embedding.ker.ideal ⟨U,hU⟩ = ⊤ := by
      apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      have hr : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
        rw [Scheme.Hom.support_ker]
        exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
      have hz : hU.fromSpec p ∈ (C.embedding.ker.support : Set S.scheme) ∩ U := by
        rw [C.embedding.ker.coe_support_inter ⟨U,hU⟩,← hU.fromSpec_image_zeroLocus]
        exact ⟨p,hp,rfl⟩
      exact hUW hz.2 (hr ▸ hz.1)
    exact ⟨⟨U,hU⟩,hxU,1,isRegular_one,by rw [htop,Ideal.span_singleton_one]⟩

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
-- module Solutions.Q223_SES.Seshadri_Intersection_EffectiveDegree
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.ProjectiveBertini

theorem Surface.effective_mixed_nonneg_s01_oai (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (M : LineBundle S.scheme)
    (s : O S.scheme ⟶ M.sheaf) (hs : s ≠ 0) : 0 ≤ mixedEuler S L M := by
  classical
  obtain ⟨d,hd,-,N,a,ha,v,hne,hi,hC⟩ := S.coprime_integral_section_s01 L hL 1 (by decide)
  let := hi
  let k := S.structureMap.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let C : IntegralCurve S := ⟨(sectionIdeal k a ha v).subscheme,
    (sectionIdeal k a ha v).subschemeι,inferInstance,inferInstance,hC⟩
  have hdeg (B : LineBundle S.scheme) :
      curveDegree S B C = (d : ℤ)*mixedEuler S L B :=
    generated_curveDegree_eq_mixedEuler_s01 S L hL B d k a ha v hne hC
  obtain ⟨J,ι,hJ⟩ := C.invertible_ideal S
  let := hJ.1
  obtain ⟨x⟩ := (inferInstance : Nonempty C.scheme)
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M (C.embedding x)
  let : Nonempty U.1 := ⟨⟨_,hx⟩⟩
  let : Nonempty (C.embedding ⁻¹ᵁ U.1) := ⟨⟨x,hx⟩⟩
  let : IsNoetherianRing Γ(S.scheme,U.1) := IsLocallyNoetherian.component_noetherian U
  let I := C.embedding.ker.ideal U
  let : I.IsPrime := C.affine_ideal_prime S U inferInstance
  let g := U.1.topIso.hom (endValue (e.inv ≫
    (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
      (Scheme.Modules.restrictUnitIso U.1.ι).hom))
  have hg : g ∈ I := by
    change g ∈ C.embedding.ker.ideal U
    rw [InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ U e]
    exact Ideal.subset_span (Set.mem_singleton g)
  have hterm : ∃ n : ℕ, affineCoefficient U f s ∉ I^n := by
    by_contra! hn
    have hh : affineCoefficient U f s ∈ (⨅ n : ℕ, I^n) :=
      Ideal.mem_iInf.mpr hn
    rw [I.iInf_pow_eq_bot_of_isDomain (Ideal.IsPrime.ne_top inferInstance)] at hh
    exact ((isRegular_iff_ne_zero).mp (M.section_coefficient_regular s hs U f)) hh
  obtain ⟨n,hn⟩ := hterm
  suffices H : ∀ n : ℕ, ∀ B : LineBundle S.scheme,
      ∀ f : B.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∀ s : O S.scheme ⟶ B.sheaf, s ≠ 0 →
      affineCoefficient U f s ∉ I^n → 0 ≤ mixedEuler S L B from H n M f s hs hn
  intro n
  induction n with
  | zero =>
    intro B f t ht hn
    exact (hn (by simp)).elim
  | succ n ih =>
    intro B f t ht hn
    by_cases hz : pullbackSection C.embedding t = 0
    · obtain ⟨q,hq,-⟩ := C.divide_section S J B ι hJ t hz
      have hq0 : q ≠ 0 := by
        intro hzero
        apply ht
        rw [hzero,zero_comp] at hq
        exact hq.symm
      have hqn : affineCoefficient U (tensorFrame J B U.1 e f) q ∉ I^n := by
        intro hh
        apply hn
        have hp : g * affineCoefficient U (tensorFrame J B U.1 e f) q ∈ I^(n+1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul hg hh
        have H := Ideal.mem_of_dvd (I^(n+1))
          (affineCoefficient_tensorInclusion J B ι U e f q).dvd hp
        simpa only [hq] using H
      have hnonneg := ih (J.tensor B) (tensorFrame J B U.1 e f) q hq0 hqn
      rw [mixedEuler_tensor_right S L hL,
        C.ideal_mixed_degree_s01 S L hL J ι hJ L] at hnonneg
      have hp := C.ample_degree_positive_s01 S L hL
      linarith
    · have hnonneg := C.degree_nonneg_of_restriction_s01 S L hL B t hz
      rw [hdeg B] at hnonneg
      have hd' : (0 : ℤ) < d := by exact_mod_cast hd
      nlinarith

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01_oai := @OAI.MaximalSeshadri.Geometry.Surface.effective_mixed_nonneg_s01_oai

-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:10.531938+00:00
-- url     : https://prove2.me/submissions/5ef51ed6-2f82-4360-986e-e168c12169a0

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES003
import Definitions.Def_Q223SES004

section
-- module Solutions.Q223_SES.Seshadri_Bertini_Derivations
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem finiteType_rationalPoint {K A : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [Nontrivial A] [Algebra K A] [Algebra.FiniteType K A] :
    Nonempty (A →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩

theorem finiteType_point_nonvanishing {K A : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (a : A) (ha : a ≠ 0) : ∃ f : A →ₐ[K] K, f a ≠ 0 := by
  let C := Localization.Away a
  have hs : Submonoid.powers a ≤ nonZeroDivisors A := by
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n ha)
  let : IsDomain C := IsLocalization.isDomain_localization hs
  obtain ⟨φ⟩ := finiteType_rationalPoint (K := K) (A := C)
  let j : A →ₐ[K] C := IsScalarTower.toAlgHom K A C
  refine ⟨φ.comp j, ?_⟩
  exact ((IsLocalization.map_units C (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)).map
    φ.toMonoidHom).ne_zero

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri
noncomputable section
open scoped TensorProduct

variable {F A B : Type} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

lemma tensorSpecialize_repr {ι : Type} (b : Module.Basis ι F B)
    (φ : A →ₐ[F] F) (z : A ⊗[F] B) (i : ι) :
    b.repr (tensorSpecialize φ z) i = φ ((b.baseChange A).repr z i) := by
  induction z using OAI.tensorInductionOn with
  | tmul x y => simp [tensorSpecialize, Module.Basis.baseChange_repr_tmul, map_smul, mul_comm]
  | add x y hx hy => simp_all

theorem tensorProduct_isDomain [IsAlgClosed F] 
    [IsDomain A] [IsDomain B] [Algebra.FiniteType F A] : IsDomain (A ⊗[F] B) := by
  classical
  let b := Module.Basis.ofVectorSpace F B
  have hex (z : A ⊗[F] B) (hz : z ≠ 0) :
      ∃ i, (b.baseChange A).repr z i ≠ 0 := by
    by_contra h
    push Not at h
    apply hz
    apply (b.baseChange A).repr.injective
    ext i
    simpa using h i
  let : Nontrivial (A ⊗[F] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F A B
      (algebraMap F A).injective (algebraMap F B).injective
  let : NoZeroDivisors (A ⊗[F] B) := ⟨fun {x y} hxy => by
    by_contra h
    push Not at h
    obtain ⟨i, hi⟩ := hex x h.1
    obtain ⟨j, hj⟩ := hex y h.2
    obtain ⟨ψ, hψ⟩ := BertiniIntegral.finiteType_point_nonvanishing (K := F)
      ((b.baseChange A).repr x i * (b.baseChange A).repr y j) (mul_ne_zero hi hj)
    rw [map_mul, mul_ne_zero_iff] at hψ
    have hx : tensorSpecialize (B := B) ψ x ≠ 0 := by
      intro heq
      have := tensorSpecialize_repr b ψ x i
      rw [heq, map_zero, Finsupp.zero_apply] at this
      exact hψ.1 this.symm
    have hy : tensorSpecialize (B := B) ψ y ≠ 0 := by
      intro heq
      have := tensorSpecialize_repr b ψ y j
      rw [heq, map_zero, Finsupp.zero_apply] at this
      exact hψ.2 this.symm
    have := congrArg (tensorSpecialize (B := B) ψ) hxy
    simp only [map_mul, map_zero, mul_eq_zero, hx, hy, or_self] at this⟩
  exact NoZeroDivisors.to_isDomain _

end
end MaximalSeshadri


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
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

theorem rational_point_outside_countable_closed
    {F A : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A]
    (Z : ℕ → Set (PrimeSpectrum A)) (hclosed : ∀ n, IsClosed (Z n))
    (hproper : ∀ n, Z n ≠ Set.univ) :
    ∃ f : A →ₐ[F] F, ∀ n,
      (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum A) ∉ Z n := by
  classical
  choose I hI using fun n => (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Z n)).mp
    (hclosed n)
  have hIbot (n : ℕ) : I n ≠ ⊥ := by
    intro heq
    apply hproper n
    rw [hI n, heq, PrimeSpectrum.zeroLocus_bot]
  have hex (n : ℕ) : ∃ a, a ∈ I n ∧ a ≠ 0 := by
    by_contra h
    apply hIbot n
    apply le_antisymm _ bot_le
    intro a ha
    simp only [Ideal.mem_bot]
    by_contra hn
    exact h ⟨a, ha, hn⟩
  choose a ha hane using hex
  obtain ⟨f, hf⟩ := point_avoiding_sequence (F := F) a hane
  refine ⟨f, fun n hn => hf n ?_⟩
  rw [hI n] at hn
  exact hn (ha n)

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
-- module Solutions.Q223_SES.Seshadri_Configurations_Configurations
attribute [-instance] _root_.OAI.MaximalSeshadri.AffineBlowup.scheme_isReduced _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.BlowupGluing.scheme_isReduced _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open scoped TensorProduct

variable {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]

omit [Uncountable F] in
lemma affine_pullback_isIntegral {A B : CommRingCat} [IsDomain A] [IsDomain B]
    (f : Spec A ⟶ Spec (CommRingCat.of F))
    (g : Spec B ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] : IsIntegral (pullback f g) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have hft : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp
    (inferInstance : LocallyOfFiniteType (Spec.map φ))
  algebraize [φ.hom, ψ.hom]
  let : IsDomain (A ⊗[F] B) := tensorProduct_isDomain
  exact IsIntegral.of_isIso (pullbackSpecIso F A B).inv

omit [Uncountable F] in
theorem scheme_product_isIntegral {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (CommRingCat.of F)) (g : Y ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] : IsIntegral (pullback f g) := by
  classical
  let C := Scheme.Pullback.openCoverOfLeftRight (nonemptyAffineCover X)
    (nonemptyAffineCover Y) f g
  have hInt (i : C.I₀) : IsIntegral (C.X i) := by
    change IsIntegral (pullback ((nonemptyAffineCover X).f i.1 ≫ f)
      ((nonemptyAffineCover Y).f i.2 ≫ g))
    let : Nonempty i.1.1 := i.1.2.2
    let : Nonempty i.2.1 := i.2.2.2
    let : IsOpenImmersion ((nonemptyAffineCover X).f i.1) := inferInstance
    let : LocallyOfFiniteType ((nonemptyAffineCover X).f i.1) := inferInstance
    let hfcomp : LocallyOfFiniteType ((nonemptyAffineCover X).f i.1 ≫ f) := inferInstance
    exact @affine_pullback_isIntegral F _ _ Γ(X, i.1.1) Γ(Y, i.2.1)
      inferInstance inferInstance ((nonemptyAffineCover X).f i.1 ≫ f)
      ((nonemptyAffineCover Y).f i.2 ≫ g) hfcomp
  let : ∀ i, IsReduced (C.X i) := fun i => by
    let := hInt i
    infer_instance
  let : IsReduced (pullback f g) := IsReduced.of_openCover _ C
  let x : X := Classical.ofNonempty
  let y : Y := Classical.ofNonempty
  obtain ⟨i, a, _⟩ := (nonemptyAffineCover X).exists_eq x
  obtain ⟨j, b, _⟩ := (nonemptyAffineCover Y).exists_eq y
  let c : C.I₀ := (i, j)
  let := hInt c
  have hdx : Dense (Set.range ((nonemptyAffineCover X).f i)) :=
    ((nonemptyAffineCover X).f i).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)
  have hdy : Dense (Set.range ((nonemptyAffineCover Y).f j)) :=
    ((nonemptyAffineCover Y).f j).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty _)
  have hdc : Dense (Set.range (C.f c)) := by
    change Dense (Set.range (pullback.map
      ((nonemptyAffineCover X).f i ≫ f) ((nonemptyAffineCover Y).f j ≫ g)
      f g ((nonemptyAffineCover X).f i) ((nonemptyAffineCover Y).f j)
      (𝟙 _) (Category.comp_id _) (Category.comp_id _)))
    rw [Scheme.Pullback.range_map]
    exact (hdx.preimage (pullback.fst f g).isOpenMap).inter_of_isOpen_left
      (hdy.preimage (pullback.snd f g).isOpenMap)
      (((nonemptyAffineCover X).f i).isOpenEmbedding.isOpen_range.preimage
        (pullback.fst f g).continuous)
  have hic : IsIrreducible (Set.range (C.f c)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := C.X c)).image (C.f c)
        (C.f c).continuous.continuousOn
  let : IrreducibleSpace (pullback f g : Scheme) :=
    (irreducibleSpace_def (pullback f g : Scheme)).mpr (by
      change IsIrreducible (Set.univ : Set (pullback f g : Scheme))
      rw [← hdc.closure_eq]
      exact hic.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

theorem scheme_power_isIntegral {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (n : ℕ) :
    IsIntegral (∏ᶜ (fun _ : Fin n => X)).left := by
  induction n with
  | zero =>
    let : IsIntegral (Over.mk (𝟙 (Spec (CommRingCat.of F)))).left :=
      inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
    exact IsIntegral.of_isIso (overLeftIso (overPowerZeroIso X)).inv
  | succ n hn =>
    let : IsIntegral (∏ᶜ (fun _ : Fin n => X)).left := hn
    let : IsIntegral (pullback X.hom (∏ᶜ (fun _ : Fin n => X)).hom) :=
      scheme_product_isIntegral X.hom _
    let e : (∏ᶜ (fun _ : Fin (n + 1) => X)).left ≅
        pullback X.hom (∏ᶜ (fun _ : Fin n => X)).hom :=
      (overLeftIso (powerSuccIso X n)).trans
      (Over.prodLeftIsoPullback X (∏ᶜ (fun _ : Fin n => X)))
    exact IsIntegral.of_isIso e.inv

theorem scheme_power_locallyOfFiniteType {F : Type} [Field F]
    (X : Over (Spec (CommRingCat.of F))) [LocallyOfFiniteType X.hom] (n : ℕ) :
    LocallyOfFiniteType (∏ᶜ (fun _ : Fin n => X)).hom := by
  induction n with
  | zero =>
    change LocallyOfFiniteType (overLeftIso (overPowerZeroIso X)).hom
    infer_instance
  | succ n hn =>
    let e : (∏ᶜ (fun _ : Fin (n + 1) => X)).left ≅
        pullback X.hom (∏ᶜ (fun _ : Fin n => X)).hom :=
      (overLeftIso (powerSuccIso X n)).trans
      (Over.prodLeftIsoPullback X (∏ᶜ (fun _ : Fin n => X)))
    have he : (∏ᶜ (fun _ : Fin (n + 1) => X)).hom =
        e.hom ≫ pullback.fst _ _ ≫ X.hom := by
      dsimp only [e]
      simp only [Iso.trans_hom, Category.assoc,
        Over.prodLeftIsoPullback_hom_fst_assoc]
      change _ = (powerSuccIso X n).hom.left ≫
        (prod.fst : X ⨯ (∏ᶜ (fun _ : Fin n => X)) ⟶ X).left ≫ X.hom
      rw [Over.w, Over.w]
    let : LocallyOfFiniteType (∏ᶜ (fun _ : Fin n => X)).hom := hn
    rw [he]
    infer_instance

end
end MaximalSeshadri
namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

theorem scheme_rational_point_outside_countable_closed
    {F : Type} [Field F] [IsAlgClosed F] [Uncountable F]
    {X : Scheme} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f]
    (Z : ℕ → Set X) (hclosed : ∀ n, IsClosed (Z n))
    (hproper : ∀ n, Z n ≠ Set.univ) :
    ∃ p : Spec (CommRingCat.of F) ⟶ X,
      p ≫ f = 𝟙 _ ∧ ∀ n, p (fieldPoint F) ∉ Z n := by
  classical
  let x : X := Classical.ofNonempty
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let A := Γ(X, U)
  let i : Spec A ⟶ X := hU.fromSpec
  let g : CommRingCat.of F ⟶ A := Spec.homEquiv (i ≫ f)
  have hg : Spec.map g = i ≫ f := Spec.homEquiv.symm_apply_apply _
  let : LocallyOfFiniteType (Spec.map g) := hg ▸ inferInstance
  have hft : g.hom.FiniteType := HasRingHomProperty.Spec_iff.mp (inferInstance : LocallyOfFiniteType (Spec.map g))
  algebraize [g.hom]
  let Z' : ℕ → Set (PrimeSpectrum A) := fun n => i ⁻¹' Z n
  have hclosed' (n : ℕ) : IsClosed (Z' n) := (hclosed n).preimage i.continuous
  have hproper' (n : ℕ) : Z' n ≠ Set.univ := by
    intro heq
    have hUZ : (U : Set X) ⊆ Z n := by
      rw [← hU.range_fromSpec]
      rintro _ ⟨a, rfl⟩
      have : a ∈ Z' n := heq ▸ Set.mem_univ a
      exact this
    have hd : Dense (U : Set X) := U.isOpen.dense ⟨x, hxU⟩
    apply hproper n
    apply Set.eq_univ_of_univ_subset
    rw [← hd.closure_eq]
    exact (hclosed n).closure_subset_iff.mpr hUZ
  obtain ⟨φ, hφ⟩ := rational_point_outside_countable_closed (F := F) Z' hclosed' hproper'
  let p := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i
  refine ⟨p, ?_, fun n => ?_⟩
  · dsimp [p]
    rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    exact φ.comp_algebraMap
  · change i ((Spec.map (CommRingCat.ofHom φ.toRingHom)) (fieldPoint F)) ∉ Z n
    exact hφ n

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

theorem rationalPoint_image_injective {F : Type} [Field F]
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of F)) (o : Spec (CommRingCat.of F)) :
    Function.Injective
      (fun p : {p : Spec (CommRingCat.of F) ⟶ X // p ≫ f = 𝟙 _} => p.val o) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
  apply Subtype.ext
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective p
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective q
  change (Spec.map φ ≫ X.fromSpecResidueField x) o =
    (Spec.map ψ ≫ X.fromSpecResidueField y) o at hpq
  have hxy : x = y := by simpa only [Scheme.Hom.comp_apply,
    Scheme.fromSpecResidueField_apply] using hpq
  subst y
  change Spec.map φ ≫ X.fromSpecResidueField x ≫ f = 𝟙 _ at hp
  change Spec.map ψ ≫ X.fromSpecResidueField x ≫ f = 𝟙 _ at hq
  let a : CommRingCat.of F ⟶ X.residueField x :=
    Spec.homEquiv (X.fromSpecResidueField x ≫ f)
  have ha : Spec.map a = X.fromSpecResidueField x ≫ f :=
    Spec.homEquiv.symm_apply_apply _
  have hap : a ≫ φ = 𝟙 _ := by
    apply Spec.map_inj.mp
    rw [Spec.map_comp, Spec.map_id, ha]
    exact hp
  have haq : a ≫ ψ = 𝟙 _ := by
    apply Spec.map_inj.mp
    rw [Spec.map_comp, Spec.map_id, ha]
    exact hq
  have has : Function.Surjective a.hom := by
    intro z
    refine ⟨φ.hom z, φ.hom.injective ?_⟩
    exact congrArg (fun k : CommRingCat.of F ⟶ CommRingCat.of F => k.hom (φ.hom z)) hap
  have hφψ : φ = ψ := by
    ext z
    obtain ⟨c, rfl⟩ := has z
    exact (congrArg (fun k : CommRingCat.of F ⟶ CommRingCat.of F => k.hom c) hap).trans
      (congrArg (fun k : CommRingCat.of F ⟶ CommRingCat.of F => k.hom c) haq).symm
  exact congrArg (fun k => (Scheme.SpecToEquivOfField F X).symm ⟨x, k⟩) hφψ

end
end MaximalSeshadri

namespace MaximalSeshadri
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {F : Type} [Field F]

theorem rationalImage_injective (X : Over (Spec (CommRingCat.of F))) :
    Function.Injective (rationalImage (X := X)) := by
  intro p q h
  have hh := rationalPoint_image_injective X.hom (fieldPoint F)
    (a₁ := ⟨p.left, Over.w p⟩) (a₂ := ⟨q.left, Over.w q⟩) h
  apply Over.OverMorphism.ext
  exact congrArg Subtype.val hh

lemma rationalImage_projection (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) (i : Fin r) :
    (Pi.π (fun _ : Fin r => X) i).left (rationalTupleImage X r p) =
      rationalImage (p i) := by
  change ((Pi.lift p).left ≫ (Pi.π (fun _ : Fin r => X) i).left) (fieldPoint F) = _
  rw [← Over.comp_left, Pi.lift_π]
  rfl

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

lemma pairDiagonal_closed (X : Over (Spec (CommRingCat.of F))) [IsSeparated X.hom]
    (r : ℕ) (i j : Fin r) : IsClosed (pairDiagonal X r i j) := by
  exact (pullback.diagonal X.hom).isClosedEmbedding.isClosed_range.preimage
    (pairProjection X r i j).continuous

lemma pairDiagonal_tuple_iff (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) (i j : Fin r) :
    rationalTupleImage X r p ∈ pairDiagonal X r i j ↔
      rationalImage (p i) = rationalImage (p j) := by
  constructor
  · rintro ⟨x, hx⟩
    have hi := congrArg (pullback.fst X.hom X.hom) hx
    have hj := congrArg (pullback.snd X.hom X.hom) hx
    have hfst : (pullback.fst X.hom X.hom) (pairProjection X r i j
        (rationalTupleImage X r p)) = rationalImage (p i) := by
      change (pairProjection X r i j ≫ pullback.fst X.hom X.hom)
        (rationalTupleImage X r p) = _
      simp only [pairProjection, pullback.lift_fst, rationalImage_projection]
    have hsnd : (pullback.snd X.hom X.hom) (pairProjection X r i j
        (rationalTupleImage X r p)) = rationalImage (p j) := by
      change (pairProjection X r i j ≫ pullback.snd X.hom X.hom)
        (rationalTupleImage X r p) = _
      simp only [pairProjection, pullback.lift_snd, rationalImage_projection]
    have hid : (pullback.fst X.hom X.hom) ((pullback.diagonal X.hom) x) = x := by
      change (pullback.diagonal X.hom ≫ pullback.fst X.hom X.hom) x = x
      simp
    have hjd : (pullback.snd X.hom X.hom) ((pullback.diagonal X.hom) x) = x := by
      change (pullback.diagonal X.hom ≫ pullback.snd X.hom X.hom) x = x
      simp
    exact (hfst.symm.trans (hi.symm.trans hid)).trans (hjd.symm.trans (hj.trans hsnd))
  · intro h
    have hp := rationalImage_injective X h
    refine ⟨rationalImage (p i), ?_⟩
    have hm : (Pi.lift p).left ≫ pairProjection X r i j =
        (p i).left ≫ pullback.diagonal X.hom := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pairProjection, pullback.lift_fst,
          pullback.diagonal_fst, Category.comp_id, ← Over.comp_left, Pi.lift_π]
      · simp only [Category.assoc, pairProjection, pullback.lift_snd,
          pullback.diagonal_snd, Category.comp_id, ← Over.comp_left, Pi.lift_π, hp]
    exact (congrArg (fun f : Spec (CommRingCat.of F) ⟶ pullback X.hom X.hom =>
      f (fieldPoint F)) hm).symm

lemma collisionLocus_closed (X : Over (Spec (CommRingCat.of F))) [IsSeparated X.hom]
    (r : ℕ) : IsClosed (collisionLocus X r) := by
  exact isClosed_iUnion_of_finite (fun ij => pairDiagonal_closed X r ij.val.1 ij.val.2)

lemma tuple_not_collision_iff (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (p : Fin r → RationalPoint X) :
    rationalTupleImage X r p ∉ collisionLocus X r ↔
      Function.Injective (fun i => rationalImage (p i)) := by
  constructor
  · intro h i j hij
    by_contra hne
    apply h
    exact Set.mem_iUnion.mpr ⟨⟨(i, j), hne⟩,
      (pairDiagonal_tuple_iff X r p i j).mpr hij⟩
  · intro h hbad
    obtain ⟨⟨⟨i, j⟩, hne⟩, hij⟩ := Set.mem_iUnion.mp hbad
    exact hne (h ((pairDiagonal_tuple_iff X r p i j).mp hij))

lemma collisionLocus_proper [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left]
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n X.hom] (r : ℕ) :
    collisionLocus X r ≠ Set.univ := by
  obtain ⟨p, hp⟩ := exists_distinct_rational_tuple X n hn r
  intro heq
  exact (tuple_not_collision_iff X r p).mpr hp (heq ▸ Set.mem_univ _)

lemma rationalTupleImage_projections (X : Over (Spec (CommRingCat.of F))) (r : ℕ)
    (q : RationalPoint (∏ᶜ (fun _ : Fin r => X))) :
    rationalTupleImage X r (fun i => q ≫ Pi.π _ i) = rationalImage q := by
  have heq : Pi.lift (fun i => q ≫ Pi.π (fun _ : Fin r => X) i) = q := by
    apply Pi.hom_ext
    intro i
    simp
  exact congrArg (fun p : RationalPoint (∏ᶜ (fun _ : Fin r => X)) =>
    p.left (fieldPoint F)) heq

theorem configuration_outside_countable_closed [IsAlgClosed F] [Uncountable F]
    (X : Over (Spec (CommRingCat.of F))) [IsIntegral X.left] [IsSeparated X.hom]
    (n : ℕ) (hn : 0 < n) [SmoothOfRelativeDimension n X.hom] (r : ℕ)
    (Z : ℕ → Set (SchemeConfiguration X r)) (hclosed : ∀ k, IsClosed (Z k))
    (hproper : ∀ k, Z k ≠ Set.univ) :
    ∃ p : SchemeConfiguration X r, ∀ k, p ∉ Z k := by
  classical
  have hex (k : ℕ) : ∃ W : Set (∏ᶜ (fun _ : Fin r => X)).left,
      IsClosed W ∧ (fun p : SchemeConfiguration X r => rationalTupleImage X r p.val) ⁻¹' W = Z k :=
    isClosed_induced_iff.mp (hclosed k)
  choose W hW hWZ using hex
  have hWP (k : ℕ) : W k ≠ Set.univ := by
    intro heq
    apply hproper k
    rw [← hWZ k, heq]
    exact Set.preimage_univ
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth n X.hom
  let Y := ∏ᶜ (fun _ : Fin r => X)
  let : IsIntegral Y.left := scheme_power_isIntegral X r
  let : LocallyOfFiniteType Y.hom := scheme_power_locallyOfFiniteType X r
  let bad : ℕ → Set Y.left := fun k => Nat.casesOn k (collisionLocus X r) W
  have hbc (k : ℕ) : IsClosed (bad k) := by
    cases k with
    | zero => exact collisionLocus_closed X r
    | succ k => exact hW k
  have hbp (k : ℕ) : bad k ≠ Set.univ := by
    cases k with
    | zero => exact collisionLocus_proper X n hn r
    | succ k => exact hWP k
  obtain ⟨q, hq, ha⟩ := scheme_rational_point_outside_countable_closed Y.hom bad hbc hbp
  let q' : RationalPoint Y := Over.homMk q hq
  let p : Fin r → RationalPoint X := fun i => q' ≫ Pi.π _ i
  have hpi : rationalTupleImage X r p = q (fieldPoint F) :=
    rationalTupleImage_projections X r q'
  have hp : Function.Injective (fun i => rationalImage (p i)) := by
    apply (tuple_not_collision_iff X r p).mp
    rw [hpi]
    exact ha 0
  refine ⟨⟨p, hp⟩, fun k hk => ?_⟩
  apply ha (k + 1)
  change q (fieldPoint F) ∈ W k
  rw [← hpi]
  have hmem : (⟨p, hp⟩ : SchemeConfiguration X r) ∈
      (fun p : SchemeConfiguration X r => rationalTupleImage X r p.val) ⁻¹' W k := by
    rw [hWZ k]
    exact hk
  exact hmem

end
end MaximalSeshadri
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

lemma configurationTopology_eq (S : Surface) (r : ℕ) :
    configurationTopology S r =
      schemeConfigurationTopology (Over.mk S.structureMap) r := by
  unfold configurationTopology schemeConfigurationTopology
  change TopologicalSpace.induced Subtype.val
      (TopologicalSpace.induced (tupleImage S r) inferInstance) = _
  rw [induced_compose]
  rfl

theorem surface_configuration_outside_countable_closed_s01_oai
    (S : Surface) (r : ℕ) (Z : ℕ → Set (Configuration S r))
    (hclosed : ∀ k, IsClosed (Z k)) (hproper : ∀ k, Z k ≠ Set.univ) :
    ∃ p : Configuration S r, ∀ k, p ∉ Z k := by
  let : IsIntegral (Over.mk S.structureMap).left := S.integral
  let : SmoothOfRelativeDimension 2 (Over.mk S.structureMap).hom := S.smooth
  let : IsSeparated (Over.mk S.structureMap).hom := S.separated
  have ht := configurationTopology_eq S r
  let T : ℕ → Set (SchemeConfiguration (Over.mk S.structureMap) r) := Z
  have hc : ∀ k, @IsClosed _ (schemeConfigurationTopology (Over.mk S.structureMap) r) (T k) := by
    intro k
    rw [← ht]
    exact hclosed k
  exact configuration_outside_countable_closed (Over.mk S.structureMap) 2 (by norm_num) r T hc hproper

end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed_s01_oai := @OAI.MaximalSeshadri.Geometry.surface_configuration_outside_countable_closed_s01_oai

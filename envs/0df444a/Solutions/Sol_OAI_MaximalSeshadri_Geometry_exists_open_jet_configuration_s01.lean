-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:09.139597+00:00
-- url     : https://prove2.me/submissions/e464a602-021f-4718-8f3a-b07121df2aad

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES003
import Definitions.Def_Q223SES004

section
-- module Solutions.Q223_SES.Seshadri_Configurations_SmoothRationalPoints
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open scoped TensorProduct

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

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Configurations_AffinePointParameters
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma affineComplexPoint_image_injective {X : Scheme} (f : X ⟶ complexBase)
    (U : X.affineOpens) :
    Function.Injective (fun ρ : letI := (openScalars f U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ =>
      (affineComplexPoint f U ρ).left (fieldPoint ℂ)) := by
  let := (openScalars f U.1).toAlgebra
  have : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  intro ρ σ h
  apply rational_kernel_injective
  exact congrArg PrimeSpectrum.asIdeal (U.2.fromSpec.isOpenEmbedding.injective h)

lemma affineMapAlgHom_point {X Y : Scheme}
    (f : X ⟶ complexBase) (g : Y ⟶ complexBase)
    (h : X ⟶ Y) (hh : h ≫ g = f) (U : Y.affineOpens) (V : X.affineOpens)
    (hVU : V.1 ≤ h ⁻¹ᵁ U.1)
    (ρ : letI := (openScalars f V.1).toAlgebra; Γ(X,V.1) →ₐ[ℂ] ℂ) :
    letI := (openScalars f V.1).toAlgebra
    letI := (openScalars g U.1).toAlgebra
    (affineComplexPoint g U (ρ.comp (affineMapAlgHom f g h hh U V hVU))).left =
      (affineComplexPoint f V ρ).left ≫ h := by
  let := (openScalars f V.1).toAlgebra
  let := (openScalars g U.1).toAlgebra
  change Spec.map (CommRingCat.ofHom (ρ.comp (affineMapAlgHom f g h hh U V hVU)).toRingHom) ≫
    U.2.fromSpec = (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ V.2.fromSpec) ≫ h
  rw [show CommRingCat.ofHom (ρ.comp (affineMapAlgHom f g h hh U V hVU)).toRingHom =
    h.appLE U.1 V.1 hVU ≫ CommRingCat.ofHom ρ.toRingHom from rfl,
    Spec.map_comp,Category.assoc,IsAffineOpen.SpecMap_appLE_fromSpec h U.2 V.2 hVU,
    Category.assoc]
end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_PolynomialJets
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.AlgebraicJets

noncomputable section
open MvPolynomial

variable {σ R : Type*} [CommRing R]

lemma jetAugment_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (jetAugment (σ := σ) (R := R) n hn) :=
  fun c => ⟨algebraMap R _ c, by simp⟩

lemma jetAugment_ker (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := R) n hn) =
      (idealOfVars σ R).map (Ideal.Quotient.mk ((idealOfVars σ R) ^ n)) := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.mem_ker, jetAugment_mk,
    Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro h
    exact ⟨p, by rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker], rfl⟩
  · rintro ⟨f, hf, hfp⟩
    have hd : f - p ∈ (idealOfVars σ R) ^ n := Ideal.Quotient.eq.mp hfp
    have hd' := (mem_pow_idealOfVars_iff' n (f - p)).mp hd 0 (by simpa using hn)
    have hf' : constantCoeff f = 0 := by
      rwa [idealOfVars_eq_ker_constantCoeff, RingHom.mem_ker] at hf
    change constantCoeff (f - p) = 0 at hd'
    simpa [map_sub, hf'] using hd'

lemma jetAugment_ker_nilpotent (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker (jetAugment (σ := σ) (R := R) n hn)) := by
  refine ⟨n, ?_⟩
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end

noncomputable section
open MvPolynomial

variable {σ F S B : Type*} [CommRing F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma exists_lift_with_coordinates [CommRing B] [Algebra F B]
    [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (β : MvPolynomial σ F →ₐ[F] B) (α : B →ₐ[F] S)
    (hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
    (hα : Function.Surjective α) (hnil : IsNilpotent (RingHom.ker α)) :
    ∃ τ : S →ₐ[F] B, α.comp τ = AlgHom.id F S ∧
      τ.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) = β := by
  let : Algebra (MvPolynomial σ F) B := β.toRingHom.toAlgebra
  let : IsScalarTower F (MvPolynomial σ F) B :=
    IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  let ap : B →ₐ[MvPolynomial σ F] S :=
    { α.toRingHom with
      commutes' := fun p => AlgHom.congr_fun hαβ p }
  let τ := Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  have hτ := Algebra.FormallySmooth.comp_liftOfSurjective
    (AlgHom.id (MvPolynomial σ F) S) ap hα hnil
  refine ⟨τ.restrictScalars F, ?_, ?_⟩
  · ext s
    exact AlgHom.congr_fun hτ s
  · ext i
    exact τ.commutes (X i)

theorem exists_regular_taylor [Algebra.FormallySmooth (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) :
    ∃ τ : S →ₐ[F] JetAlgebra σ S n,
      (∀ s, jetAugment n hn (τ s) = s) ∧
      (∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
        algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
          Ideal.Quotient.mk _ (X i)) := by
  let T := JetAlgebra σ S n
  let x : σ → S := fun i => algebraMap (MvPolynomial σ F) S (X i)
  let β : MvPolynomial σ F →ₐ[F] T :=
    aeval (fun i => algebraMap S T (x i) + Ideal.Quotient.mk _ (X i))
  let α := (jetAugment (σ := σ) (R := S) n hn).restrictScalars F
  have hαβ : α.comp β = IsScalarTower.toAlgHom F (MvPolynomial σ F) S := by
    ext i
    change jetAugment n hn (β (X i)) = x i
    simp only [β, aeval_X, map_add, jetAugment_mk, constantCoeff_X, add_zero]
    exact (jetAugment (σ := σ) (R := S) n hn).commutes (x i)
  obtain ⟨τ, hτ, hcoord⟩ := exists_lift_with_coordinates β α hαβ
    (jetAugment_surjective n hn) (jetAugment_ker_nilpotent n hn)
  refine ⟨τ, fun s => AlgHom.congr_fun hτ s, ?_⟩
  intro i
  have hi := AlgHom.congr_fun hcoord (X i)
  exact hi.trans (aeval_X _ _)

end

noncomputable section
open MvPolynomial

variable {σ F R S : Type*} [CommRing F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S]

lemma jetAugment_map (φ : R →ₐ[F] S) (n : ℕ) (hn : 0 < n)
    (z : JetAlgebra σ R n) :
    jetAugment n hn (mapJetAlgebra φ n z) = φ (jetAugment n hn z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp [MvPolynomial.constantCoeff_map]

lemma jetAugment_ker_pow (n : ℕ) (hn : 0 < n) :
    RingHom.ker (jetAugment (σ := σ) (R := S) n hn) ^ n = 0 := by
  rw [jetAugment_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_FormalEtale
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma quotient_factor_pow_ker_nilpotent (I : Ideal R) (n : ℕ) (hn : 0 < n) :
    IsNilpotent (RingHom.ker
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne') : R ⧸ I ^ n →ₐ[R] R ⧸ I)) := by
  refine ⟨n, ?_⟩
  change RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn.ne')) ^ n = 0
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
  exact Ideal.map_quotient_self _

theorem quotientBaseMap_pow_bijective [Algebra.FormallyEtale R S]
    (I : Ideal R) (hI : Function.Bijective (quotientBaseMap (S := S) I))
    (n : ℕ) : Function.Bijective (quotientBaseMap (S := S) (I ^ n)) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hR : I ^ 0 = (⊤ : Ideal R) := by simp
    have hS : (I ^ 0).map (algebraMap R S) = (⊤ : Ideal S) := by
      rw [hR, Ideal.map_top]
    let : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr hR
    let : Subsingleton (S ⧸ (I ^ 0).map (algebraMap R S)) :=
      Ideal.Quotient.subsingleton_iff.mpr hS
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  let J := I.map (algebraMap R S)
  let mapn := quotientBaseMap (S := S) (I ^ n)
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) := AlgEquiv.ofBijective (quotientBaseMap I) hI
  let qR : R ⧸ I ^ n →ₐ[R] R ⧸ I := Ideal.Quotient.factorₐ R (Ideal.pow_le_self hn.ne')
  let qS : S ⧸ (I ^ n).map (algebraMap R S) →ₐ[R] S ⧸ J :=
    Ideal.Quotient.factorₐ R (Ideal.map_mono (Ideal.pow_le_self hn.ne'))
  have hqR : Function.Surjective qR := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk (I ^ n) x, rfl⟩
  have hnR : IsNilpotent (RingHom.ker qR) := quotient_factor_pow_ker_nilpotent I n hn
  have hnS : IsNilpotent (RingHom.ker qS) := by
    refine ⟨n, ?_⟩
    change RingHom.ker (Ideal.Quotient.factor
      (Ideal.map_mono (f := algebraMap R S) (Ideal.pow_le_self (I := I) hn.ne'))) ^ n = 0
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  let f : S →ₐ[R] R ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  let g : S →ₐ[R] R ⧸ I ^ n := Algebra.FormallySmooth.liftOfSurjective f qR hqR hnR
  have hg : qR.comp g = f := Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hker : (I ^ n).map (algebraMap R S) ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change g (algebraMap R S x) = 0
    rw [g.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  let inv : S ⧸ (I ^ n).map (algebraMap R S) →ₐ[R] R ⧸ I ^ n :=
    Ideal.Quotient.liftₐ _ g hker
  have hleft : inv.comp mapn = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    ext
  have hmod : qS.comp (mapn.comp g) = qS.comp (Ideal.Quotient.mkₐ R _) := by
    ext x
    have hx := AlgHom.congr_fun hg x
    apply e.symm.injective
    change e.symm (qS (mapn (g x))) = e.symm (Ideal.Quotient.mk J x)
    have hcompat (y : R ⧸ I ^ n) : e.symm (qS (mapn y)) = qR y := by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change e.symm (e (Ideal.Quotient.mk I y)) = Ideal.Quotient.mk I y
      exact e.symm_apply_apply _
    rw [hcompat]
    exact hx
  have hright' : mapn.comp g = Ideal.Quotient.mkₐ R _ :=
    Algebra.FormallyUnramified.lift_unique' qS hnS _ _ hmod
  have hright : mapn.comp inv = AlgHom.id R _ := by
    apply Ideal.Quotient.algHom_ext
    exact hright'
  exact ⟨fun x y h => by
    change mapn x = mapn y at h
    calc
      x = inv (mapn x) := (AlgHom.congr_fun hleft x).symm
      _ = inv (mapn y) := congrArg inv h
      _ = y := AlgHom.congr_fun hleft y,
    fun y => ⟨inv y, AlgHom.congr_fun hright y⟩⟩

end

noncomputable section
open IsLocalRing

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S] [Algebra R S] [IsScalarTower F R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

lemma quotientBaseMap_maximal_bijective
    (hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (ρ : S →ₐ[F] F) :
    Function.Bijective (quotientBaseMap (S := S) (maximalIdeal R)) := by
  have hρ : Function.Surjective ρ := fun c => ⟨algebraMap F S c, by simp⟩
  have hker : RingHom.ker ρ = maximalIdeal S :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ρ hρ)
  constructor
  · intro x y h
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq.mpr
    have hmem : algebraMap R S (x - y) ∈ maximalIdeal S := by
      rw [← hmax]
      have hh := Ideal.Quotient.eq.mp h
      change algebraMap R S x - algebraMap R S y ∈ _ at hh
      simpa only [map_sub] using hh
    have hc : x - y ∈ (maximalIdeal S).comap (algebraMap R S) := hmem
    rwa [maximalIdeal_comap] at hc
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk _ (algebraMap F R (ρ y)), ?_⟩
    apply Ideal.Quotient.eq.mpr
    rw [hmax, ← hker]
    change ρ (algebraMap R S (algebraMap F R (ρ y)) - y) = 0
    rw [← IsScalarTower.algebraMap_apply F R S]
    simp

theorem local_etale_jet_equiv [Algebra.EssFiniteType R S]
    [Algebra.FormallyEtale R S] (ρ : S →ₐ[F] F) (n : ℕ) :
    Nonempty ((R ⧸ (maximalIdeal R) ^ n) ≃ₐ[R]
      (S ⧸ (maximalIdeal S) ^ n)) := by
  have hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hbij := quotientBaseMap_pow_bijective (maximalIdeal R)
    (quotientBaseMap_maximal_bijective hmax ρ) n
  have heq : ((maximalIdeal R) ^ n).map (algebraMap R S) = (maximalIdeal S) ^ n := by
    rw [Ideal.map_pow, hmax]
  exact ⟨(AlgEquiv.ofBijective _ hbij).trans (Ideal.quotientEquivAlgOfEq R heq)⟩

end

noncomputable section
open IsLocalRing

variable {F R S : Type*} [Field F] [CommRing R] [CommRing S]
  [Algebra F R] [Algebra F S] [Algebra R S] [IsScalarTower F R S]

theorem etale_rational_jet_equiv [Algebra.EssFiniteType R S]
    [Algebra.FormallyEtale R S] (ρ : S →ₐ[F] F) (n : ℕ) :
    Nonempty ((R ⧸ ((RingHom.ker ρ).under R) ^ n) ≃ₐ[F]
      (S ⧸ (RingHom.ker ρ) ^ n)) := by
  let q := RingHom.ker ρ
  let p := q.under R
  have hρ : Function.Surjective ρ := fun c => ⟨algebraMap F S c, by simp⟩
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective ρ hρ
  have hp : p = RingHom.ker (ρ.comp (IsScalarTower.toAlgHom F R S)) := rfl
  let : p.IsMaximal := by
    rw [hp]
    exact RingHom.ker_isMaximal_of_surjective _
      (fun c => ⟨algebraMap F R c, by simp⟩)
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  let : Algebra.FormallyEtale R Sq := Algebra.FormallyEtale.comp R S Sq
  let : Algebra.FormallyEtale Rp Sq := Algebra.FormallyEtale.of_restrictScalars (R := R)
  obtain ⟨e⟩ := local_etale_jet_equiv (R := Rp) (S := Sq) (rationalLocalMap ρ) n
  exact ⟨((IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rp n).restrictScalars F).trans
    ((e.restrictScalars F).trans
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow q Sq n).restrictScalars F).symm)⟩

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Field F] [CommRing S] [Algebra F S]

lemma specializeTaylor_augment (n : ℕ) (hn : 0 < n)
    (τ : S →ₐ[F] JetAlgebra σ S n) (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (ρ : S →ₐ[F] F) (s : S) :
    jetAugment n hn (specializeTaylor n τ ρ s) = ρ s := by
  rw [specializeTaylor, AlgHom.comp_apply, jetAugment_map, hτ]

lemma specializeTaylor_ker_le (n : ℕ) (hn : 0 < n)
    (τ : S →ₐ[F] JetAlgebra σ S n) (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (ρ : S →ₐ[F] F) :
    (RingHom.ker ρ)^n ≤ RingHom.ker (specializeTaylor n τ ρ) := by
  rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow]
  apply le_antisymm _ bot_le
  calc
    ((RingHom.ker ρ).map (specializeTaylor n τ ρ))^n ≤
        (RingHom.ker (jetAugment (σ := σ) (R := F) n hn))^n := by
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      intro s hs
      change jetAugment n hn (specializeTaylor n τ ρ s) = 0
      rw [specializeTaylor_augment n hn τ hτ]
      exact hs
    _ = ⊥ := jetAugment_ker_pow n hn

variable [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma specializeTaylor_coordinate (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    (specializeTaylor n τ ρ).comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) =
      (Ideal.Quotient.mkₐ F _).comp (polynomialTranslate
        (fun i => ρ (algebraMap (MvPolynomial σ F) S (X i)))).toAlgHom := by
  ext i
  change mapJetAlgebra ρ n (τ (algebraMap (MvPolynomial σ F) S (X i))) = _
  rw [hcoord, map_add]
  change Ideal.Quotient.mk _ (MvPolynomial.map ρ.toRingHom
    (C (algebraMap (MvPolynomial σ F) S (X i)))) +
    Ideal.Quotient.mk _ (MvPolynomial.map ρ.toRingHom (X i)) = _
  simp [polynomialTranslate, add_comm]

lemma specializeTaylor_surjective (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    Function.Surjective (specializeTaylor n τ ρ) := by
  have h := specializeTaylor_coordinate n τ hcoord ρ
  have hs : Function.Surjective ((specializeTaylor n τ ρ).comp
      (IsScalarTower.toAlgHom F (MvPolynomial σ F) S)) := by
    rw [h]
    exact Ideal.Quotient.mk_surjective.comp (polynomialTranslate _).surjective
  exact Function.Surjective.of_comp hs

theorem regularTaylor_detects_ideal_power [Finite σ] [Algebra.FormallyEtale (MvPolynomial σ F) S]
    [Algebra.EssFiniteType (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) :
    RingHom.ker (specializeTaylor n τ ρ) = (RingHom.ker ρ)^n := by
  classical
  let I := (RingHom.ker ρ)^n
  let ψ : (S ⧸ I) →ₐ[F] JetAlgebra σ F n :=
    Ideal.Quotient.liftₐ I (specializeTaylor n τ ρ)
      (specializeTaylor_ker_le n hn τ hτ ρ)
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨s, hs⟩ := specializeTaylor_surjective n τ hcoord ρ y
    exact ⟨Ideal.Quotient.mk I s, hs⟩
  let x : σ → F := fun i => ρ (algebraMap (MvPolynomial σ F) S (X i))
  have hres : (RingHom.ker ρ).under (MvPolynomial σ F) = RingHom.ker (eval x) := by
    have heq : ρ.toRingHom.comp (algebraMap (MvPolynomial σ F) S) = eval x := by
      apply ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, eval_C]
        change ρ (algebraMap (MvPolynomial σ F) S (algebraMap F (MvPolynomial σ F) c)) = c
        rw [← IsScalarTower.algebraMap_apply F (MvPolynomial σ F) S]
        exact ρ.commutes c
      · intro i
        exact (eval_X (f := x) i).symm
    change RingHom.ker (ρ.toRingHom.comp (algebraMap (MvPolynomial σ F) S)) = _
    rw [heq]
  obtain ⟨e⟩ := etale_rational_jet_equiv (R := MvPolynomial σ F) ρ n
  let e' : (S ⧸ I) ≃ₗ[F] (JetIndex σ n → F) :=
    e.symm.toLinearEquiv.trans
      (((Ideal.quotientEquivAlgOfEq F (congrArg (fun J => J ^ n) hres)).toLinearEquiv).trans
        (polynomialJetEquivAt x n))
  let e'' : JetAlgebra σ F n ≃ₗ[F] (JetIndex σ n → F) := polynomialJetEquiv n
  let : FiniteDimensional F (JetIndex σ n → F) := Module.Finite.pi
  let : FiniteDimensional F (S ⧸ I) := Module.Finite.equiv e'.symm
  let : FiniteDimensional F (JetAlgebra σ F n) := Module.Finite.equiv e''.symm
  have hinj : Function.Injective ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (e'.finrank_eq.trans e''.finrank_eq.symm) (f := ψ.toLinearMap)).mpr hsurj
  apply le_antisymm _ (specializeTaylor_ker_le n hn τ hτ ρ)
  intro s hs
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  change specializeTaylor n τ ρ s = ψ 0
  rw [map_zero]
  exact hs

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]

lemma specializedTaylor_coeff (n : ℕ) (τ : S →ₐ[F] JetAlgebra σ S n)
    (ρ : S →ₐ[F] F) (s : S) (d : JetIndex σ n) :
    polynomialJetEquiv n (specializeTaylor n τ ρ s) d =
      ρ (regularTaylorCoeffs n τ s d) := by
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (τ s)
  change polynomialJetEquiv n (mapJetAlgebra ρ n (τ s)) d =
    ρ (polynomialJetEquiv n (τ s) d)
  rw [← hp, mapJetAlgebra_mk, polynomialJetEquiv_mk, polynomialJetEquiv_mk]
  exact coeff_map _ _ _

variable [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

theorem regularTaylor_vanishing_iff [Algebra.FormallyEtale (MvPolynomial σ F) S]
    [Algebra.EssFiniteType (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n) (τ : S →ₐ[F] JetAlgebra σ S n)
    (hτ : ∀ s, jetAugment n hn (τ s) = s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      algebraMap S (JetAlgebra σ S n) (algebraMap (MvPolynomial σ F) S (X i)) +
        Ideal.Quotient.mk _ (X i)) (ρ : S →ₐ[F] F) (s : S) :
    s ∈ (RingHom.ker ρ)^n ↔ ∀ d, ρ (regularTaylorCoeffs n τ s d) = 0 := by
  rw [← regularTaylor_detects_ideal_power n hn τ hτ hcoord ρ]
  change specializeTaylor n τ ρ s = 0 ↔ _
  rw [← (polynomialJetEquiv (σ := σ) (R := F) n).map_eq_zero_iff]
  rw [funext_iff]
  exact forall_congr' fun d => by rw [specializedTaylor_coeff]; rfl

end

noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]
  [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

theorem exists_regular_jet_coeffs (n : ℕ) (hn : 0 < n) :
    ∃ D : S →ₗ[F] (JetIndex σ n → S),
      ∀ (ρ : S →ₐ[F] F) s, s ∈ (RingHom.ker ρ)^n ↔ ∀ d, ρ (D s d) = 0 := by
  obtain ⟨τ, hτ, hcoord⟩ := exists_regular_taylor (σ := σ) (F := F) (S := S) n hn
  exact ⟨regularTaylorCoeffs n τ, regularTaylor_vanishing_iff n hn τ hτ hcoord⟩

end
end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_JetOpenness
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators
open Set

variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]

lemma isOpen_eval_ne_zero (f : R) :
    @IsOpen (R →ₐ[K] K) (rationalPointTopology K R) {p | p f ≠ 0} := by
  let _ := rationalPointTopology K R
  have hc : Continuous (kernelPoint K R) := continuous_induced_dom
  have heq : {p : R →ₐ[K] K | p f ≠ 0} =
      (kernelPoint K R) ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
    ext p
    simp [kernelPoint, RingHom.mem_ker]
  rw [heq]
  exact (PrimeSpectrum.basicOpen f).isOpen.preimage hc

variable {K R}

lemma injective_mulVec_iff_exists_det {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n K) :
    Function.Injective M.mulVec ↔ ∃ B : Matrix n m K, (B * M).det ≠ 0 := by
  classical
  constructor
  · intro h
    obtain ⟨f, hf⟩ := (Matrix.toLin' M).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr h)
    refine ⟨LinearMap.toMatrix' f, ?_⟩
    have heq := congrArg LinearMap.toMatrix' hf
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] at heq
    rw [heq, Matrix.det_one]
    exact one_ne_zero
  · rintro ⟨B, hB⟩
    have hinj : Function.Injective (B * M).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB))
    intro x y hxy
    apply hinj
    simp only [← Matrix.mulVec_mulVec]
    rw [hxy]

theorem isOpen_injective_evaluation {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (M : Matrix m n R) :
    @IsOpen (R →ₐ[K] K) (rationalPointTopology K R)
      {p | Function.Injective (M.map p).mulVec} := by
  classical
  let _ := rationalPointTopology K R
  have hdet (B : Matrix n m K) (p : R →ₐ[K] K) :
      p ((B.map (algebraMap K R) * M).det) = (B * M.map p).det := by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, Matrix.map_mul]
    congr 2
    ext i j
    exact p.commutes (B i j)
  have heq : {p : R →ₐ[K] K | Function.Injective (M.map p).mulVec} =
      ⋃ B : Matrix n m K, {p : R →ₐ[K] K | p ((B.map (algebraMap K R) * M).det) ≠ 0} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, hdet, injective_mulVec_iff_exists_det]
  rw [heq]
  exact isOpen_iUnion fun B => isOpen_eval_ne_zero K R _

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators
variable {F S V ι : Type*} [Field F] [CommRing S] [Algebra F S]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite ι]

theorem isOpen_regular_linear_test (ℓ : V →ₗ[F] (ι → S)) :
    @IsOpen (S →ₐ[F] F) (rationalPointTopology F S)
      {ρ | ∀ v, (∀ i, ρ (ℓ v i) = 0) → v = 0} := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let b := Module.finBasis F V
  let M : Matrix ι (Fin (Module.finrank F V)) S := fun i j => ℓ (b j) i
  let g (ρ : S →ₐ[F] F) : V →ₗ[F] (ι → F) :=
    LinearMap.pi fun i => ρ.toLinearMap.comp ((LinearMap.proj i).comp ℓ)
  have hmat (ρ : S →ₐ[F] F) : M.map ρ =
      LinearMap.toMatrix' ((g ρ).comp b.equivFun.symm.toLinearMap) := by
    ext i j
    simp [M, g, LinearMap.toMatrix'_apply, Module.Basis.equivFun_symm_apply]
    rfl
  have heq : {ρ : S →ₐ[F] F | ∀ v, (∀ i, ρ (ℓ v i) = 0) → v = 0} =
      {ρ : S →ₐ[F] F | Function.Injective (M.map ρ).mulVec} := by
    ext ρ
    simp only [Set.mem_ofPred_eq]
    rw [hmat]
    change (∀ v, (∀ i, ρ (ℓ v i) = 0) → v = 0) ↔
      Function.Injective (Matrix.toLin' (LinearMap.toMatrix'
        ((g ρ).comp b.equivFun.symm.toLinearMap)))
    rw [Matrix.toLin'_toMatrix']
    constructor
    · intro h
      have hg : Function.Injective (g ρ) := by
        intro v w hvw
        apply sub_eq_zero.mp
        apply h (v - w)
        intro i
        have hi := congrFun hvw i
        change ρ (ℓ v i) = ρ (ℓ w i) at hi
        simpa only [map_sub, Pi.sub_apply, sub_eq_zero] using hi
      exact hg.comp b.equivFun.symm.injective
    · intro h v hv
      have hg : Function.Injective (g ρ) := by
        intro x y hxy
        have hh : b.equivFun x = b.equivFun y := h (by simpa using hxy)
        exact b.equivFun.injective hh
      apply hg
      ext i
      change ρ (ℓ v i) = (g ρ) 0 i
      rw [map_zero]
      exact hv i
  rw [heq]
  exact isOpen_injective_evaluation M

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets

noncomputable section
variable {ι σ F R V : Type*} [Finite ι] [Finite σ] [Field F]
  [CommRing R] [Algebra F R] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra F (S i)]
  [∀ i, Algebra (MvPolynomial σ F) (S i)]
  [∀ i, IsScalarTower F (MvPolynomial σ F) (S i)]
  [∀ i, Algebra.FormallyEtale (MvPolynomial σ F) (S i)]
  [∀ i, Algebra.EssFiniteType (MvPolynomial σ F) (S i)]
include σ

theorem isOpen_multipoint_jet_separation (φ : ∀ i, S i →ₐ[F] R)
    (ℓ : ∀ i, V →ₗ[F] S i) (n : ℕ) (hn : 0 < n) :
    @IsOpen (R →ₐ[F] F) (rationalPointTopology F R)
      {ρ | ∀ v, (∀ i, ℓ i v ∈ (RingHom.ker (ρ.comp (φ i)))^n) → v = 0} := by
  classical
  choose D hD using fun i =>
    exists_regular_jet_coeffs (σ := σ) (F := F) (S := S i) n hn
  let C : V →ₗ[F] ((ι × JetIndex σ n) → R) := LinearMap.pi fun j =>
    (φ j.1).toLinearMap.comp ((LinearMap.proj j.2).comp ((D j.1).comp (ℓ j.1)))
  have heq : {ρ : R →ₐ[F] F | ∀ v,
      (∀ i, ℓ i v ∈ (RingHom.ker (ρ.comp (φ i)))^n) → v = 0} =
      {ρ : R →ₐ[F] F | ∀ v, (∀ j, ρ (C v j) = 0) → v = 0} := by
    ext ρ
    simp only [Set.mem_ofPred_eq]
    apply forall_congr'
    intro v
    apply imp_congr_left
    constructor
    · intro h j
      exact (hD j.1 (ρ.comp (φ j.1)) (ℓ j.1 v)).mp (h j.1) j.2
    · intro h i
      apply (hD i (ρ.comp (φ i)) (ℓ i v)).mpr
      exact fun d => h (i, d)
  rw [heq]
  exact isOpen_regular_linear_test C

end
end MaximalSeshadri.AlgebraicJets

end



end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_JetOpenConfigurations
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

theorem exists_open_jet_configuration_s01_oai (S : Surface) (r : ℕ)
    (U : S.scheme.affineOpens) (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    {A : Type} [AddCommGroup A] [Module ℂ A] [FiniteDimensional ℂ A]
    (ℓ : letI := (openScalars S.structureMap U.1).toAlgebra;
      A →ₗ[ℂ] Γ(S.scheme,U.1))
    (m : ℕ) (hm : 0 < m)
    (p : letI := (openScalars S.structureMap U.1).toAlgebra;
      Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ))
    (hp : ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (p i))^m) → a = 0) :
    ∃ W : (surfacePower S r).left.Opens,
      tupleImage S r (fun i => affineComplexPoint S.structureMap U (p i)) ∈ W ∧
      ∀ q : Fin r → ComplexPoint S, tupleImage S r q ∈ W →
        ∃ ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
          Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ),
          (∀ i, affineComplexPoint S.structureMap U (ρ i) = q i) ∧
          ∀ a, (∀ i, ℓ a ∈ (RingHom.ker (ρ i))^m) → a = 0 := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  let φt := MvPolynomial.aeval (R := ℂ) t
  let := φt.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    IsScalarTower.of_algebraMap_eq fun c => (φt.commutes c).symm
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    RingHom.etale_algebraMap.mp het
  let Q := surfacePower S r
  let pr (i : Fin r) : Q.left ⟶ S.scheme := (Pi.π (fun _ : Fin r => Over.mk S.structureMap) i).left
  have hpr (i : Fin r) : pr i ≫ S.structureMap = Q.hom := Over.w _
  let pp : Fin r → ComplexPoint S := fun i => affineComplexPoint S.structureMap U (p i)
  let x := tupleImage S r pp
  let B : Q.left.Opens := ⟨⋂ i, pr i ⁻¹' (U.1 : Set S.scheme),
    isOpen_iInter_of_finite fun i => U.1.isOpen.preimage (pr i).continuous⟩
  have hxB : x ∈ B := by
    change x ∈ ⋂ i, pr i ⁻¹' (U.1 : Set S.scheme)
    simp only [Set.mem_iInter, Set.mem_preimage]
    intro i
    change ((Pi.lift pp) ≫ Pi.π (fun _ : Fin r => Over.mk S.structureMap) i).left (fieldPoint ℂ) ∈ U.1
    rw [Pi.lift_π]
    change U.2.fromSpec _ ∈ (U.1 : Set S.scheme)
    rw [← U.2.range_fromSpec]
    exact Set.mem_range_self _
  obtain ⟨V,hV,hxV,hVB⟩ := exists_isAffineOpen_mem_and_subset hxB
  let V' : Q.left.affineOpens := ⟨V,hV⟩
  let := (openScalars Q.hom V).toAlgebra
  have hVU (i : Fin r) : V ≤ pr i ⁻¹ᵁ U.1 := fun z hz =>
    Set.mem_iInter.mp (hVB hz) i
  let φ (i : Fin r) := affineMapAlgHom Q.hom S.structureMap (pr i) (hpr i) U V' (hVU i)
  obtain ⟨a,ha⟩ := affineComplexPoint_factor Q.hom V' (Pi.lift pp) hxV
  have hap (i : Fin r) : a.comp (φ i) = p i := by
    apply affineComplexPoint_image_injective S.structureMap U
    have H := affineMapAlgHom_point Q.hom S.structureMap (pr i) (hpr i) U V' (hVU i) a
    rw [ha] at H
    have Hp : (Pi.lift pp).left ≫ pr i = (pp i).left :=
      congrArg Over.Hom.left (Pi.lift_π pp i)
    exact congrArg (fun k : complexBase ⟶ S.scheme => k (fieldPoint ℂ)) (H.trans Hp)
  have hop := isOpen_multipoint_jet_separation (σ := Fin 2)
    (fun _ : Fin r => Γ(S.scheme,U.1)) φ (fun _ => ℓ) m hm
  obtain ⟨D,hD,hDeq⟩ := isOpen_induced_iff.mp hop
  have haD : kernelPoint ℂ Γ(Q.left,V) a ∈ D := by
    change a ∈ (kernelPoint ℂ Γ(Q.left,V)) ⁻¹' D
    rw [hDeq]
    simpa only [Set.mem_ofPred_eq,hap] using hp
  let W : Q.left.Opens := ⟨hV.fromSpec '' D,hV.fromSpec.isOpenEmbedding.isOpenMap D hD⟩
  refine ⟨W,?_,?_⟩
  · refine ⟨kernelPoint ℂ Γ(Q.left,V) a,haD,?_⟩
    exact congrArg (fun k : Over.mk (𝟙 complexBase) ⟶ Over.mk Q.hom =>
      k.left (fieldPoint ℂ)) ha
  · intro q hqW
    obtain ⟨z,hzD,hzq⟩ := hqW
    have hqV : tupleImage S r q ∈ V := by
      rw [← hzq]
      change hV.fromSpec z ∈ (V : Set Q.left)
      rw [← hV.range_fromSpec]
      exact Set.mem_range_self z
    obtain ⟨b,hb⟩ := affineComplexPoint_factor Q.hom V' (Pi.lift q) hqV
    have hbz : kernelPoint ℂ Γ(Q.left,V) b = z := by
      apply hV.fromSpec.isOpenEmbedding.injective
      exact (congrArg (fun k : Over.mk (𝟙 complexBase) ⟶ Over.mk Q.hom =>
        k.left (fieldPoint ℂ)) hb).trans hzq.symm
    have hbD : b ∈ (kernelPoint ℂ Γ(Q.left,V)) ⁻¹' D := by
      change kernelPoint ℂ Γ(Q.left,V) b ∈ D
      rw [hbz]; exact hzD
    rw [hDeq] at hbD
    refine ⟨fun i => b.comp (φ i),?_,hbD⟩
    intro i
    apply Over.OverMorphism.ext
    have H := affineMapAlgHom_point Q.hom S.structureMap (pr i) (hpr i) U V' (hVU i) b
    rw [hb] at H
    exact H.trans (congrArg Over.Hom.left (Pi.lift_π q i))
end
end MaximalSeshadri.Geometry

end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration_s01_oai := @OAI.MaximalSeshadri.Geometry.exists_open_jet_configuration_s01_oai

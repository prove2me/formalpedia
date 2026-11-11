-- Prove2me | solution 1 for OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_hyperplane_of_etale_atlas_with_equations_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:01.855078+00:00
-- url     : https://prove2.me/submissions/b4c6a267-d9b6-411b-aa97-02328f583628

import Mathlib
import Definitions.Def_Q223SES006
import Theorems.Thm_OAI_MaximalSeshadri_BertiniIntegral_etale_generic_hyperplane_section_s01

section
-- module Solutions.Q223_SES.Seshadri_Bertini_CountableSpecialization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Cardinal

theorem field_embedding_over_countable {R F K : Type} [Field R] [Countable R]
    [Field F] [Field K] [Algebra R F] [Algebra R K] [IsAlgClosed K]
    [Uncountable K] (hcard : #F ≤ #K) : Nonempty (F →ₐ[R] K) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R F
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R K
  have hK : #K = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
      (Subtype.val : t → K) ht Cardinal.mk_le_aleph0 Cardinal.aleph0_lt_mk
  have hst : #s ≤ #t := (Cardinal.mk_subtype_le s).trans (hcard.trans_eq hK)
  obtain ⟨e⟩ := (Cardinal.le_def s t).mp hst
  let w : s → K := fun i => (e i : K)
  have hw : AlgebraicIndependent R w := ht.1.comp e e.injective
  let B := Algebra.adjoin R (Set.range (Subtype.val : s → F))
  let f : B →ₐ[R] K := (MvPolynomial.aeval w).comp hs.1.aevalEquiv.symm.toAlgHom
  have hf : Function.Injective f :=
    (algebraicIndependent_iff_injective_aeval.mp hw).comp hs.1.aevalEquiv.symm.injective
  let : Algebra B K := f.toRingHom.toAlgebra
  let : IsScalarTower R B K := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : Module.IsTorsionFree B K := Module.isTorsionFree_iff_algebraMap_injective.mpr hf
  let : Algebra.IsAlgebraic B F := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift : F →ₐ[B] K).restrictScalars R⟩

open scoped TensorProduct

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_CriticalLocus
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Bertini
noncomputable section
open scoped TensorProduct
open KaehlerDifferential

lemma mapBaseChange_injective_formallySmooth
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
  apply (KaehlerDifferential.mapBaseChange R A B).ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  rw [show y = 0 from Subsingleton.elim _ _, map_zero] at hy
  exact hy.symm ▸ Submodule.zero_mem _

variable {K L ι : Type*} [Field K] [Field L] [CharZero K] [Algebra K L]

theorem algebraicIndependent_differentials [Algebra.EssFiniteType K L]
    (v : ι → L) (hv : AlgebraicIndependent K v) :
    LinearIndependent L (fun i => KaehlerDifferential.D K L (v i)) := by
  let A := MvPolynomial ι K
  let F := FractionRing A
  let a : A →ₐ[K] L := MvPolynomial.aeval v
  let b : F →ₐ[K] L := IsFractionRing.liftAlgHom hv
  let : Algebra A L := a.toRingHom.toAlgebra
  let : Algebra F L := b.toRingHom.toAlgebra
  let : IsScalarTower K A L := IsScalarTower.of_algHom a
  let : IsScalarTower K F L := IsScalarTower.of_algHom b
  let : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun x => by
    change a x = IsFractionRing.lift hv (algebraMap A F x)
    exact (IsFractionRing.lift_algebraMap hv x).symm
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp K F L
  let : Algebra.FormallySmooth A F :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallySmooth A L := Algebra.FormallySmooth.comp A F L
  have hinj := mapBaseChange_injective_formallySmooth K A L
  have h := ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange L).linearIndependent
  have h' := h.map' (KaehlerDifferential.mapBaseChange K A L)
    (LinearMap.ker_eq_bot.mpr hinj)
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  simp only [Function.comp_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  change (D K L) (v i) = (mapBaseChange K A L) (1 ⊗ₜ[A] (D K A) (MvPolynomial.X i))
  rw [mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  congr 1
  exact (MvPolynomial.aeval_X v i).symm

end
end MaximalSeshadri.Bertini
namespace MaximalSeshadri.Bertini

noncomputable section
open KaehlerDifferential TensorProduct Algebra

theorem formallySmooth_principal_of_derivation
    {K S : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (f : P.Ring) (hf : Ideal.span ({f} : Set P.Ring) = P.ker)
    (δ : Derivation K P.Ring S) (hδ : δ f = 1) :
    Algebra.FormallySmooth K S := by
  let g : P.Cotangent := Extension.Cotangent.mk ⟨f, hf ▸ Ideal.mem_span_singleton_self f⟩
  let l : P.CotangentSpace →ₗ[S] P.Cotangent :=
    (LinearMap.toSpanSingleton S P.Cotangent g).comp
      (LinearMap.liftBaseChange S δ.liftKaehlerDifferential)
  apply P.formallySmooth_iff_split_injection.mpr
  refine ⟨l, ?_⟩
  have hspan : Submodule.span S (Set.range (fun _ : Unit => g)) = ⊤ := by
    apply Extension.Cotangent.span_eq_top_of_span_eq_ker (fun _ : Unit => f)
    simpa using hf
  apply LinearMap.ext_on_range hspan
  intro i
  simp [l, g, hδ]

end

end MaximalSeshadri.Bertini

end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_DifferentialFrames
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.FrameBertini
noncomputable section
open KaehlerDifferential

theorem exists_differentialFrame (K R : Type*) [CommRing K] [CommRing R]
    [Algebra K R] [Algebra.Smooth K R] :
    ∃ n, Nonempty (DifferentialFrame K R (Fin n)) := by
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R Ω[R⁄K]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  refine ⟨n, ⟨s, fun j => q (Pi.single j 1), ?_⟩⟩
  intro x
  have he := LinearMap.congr_fun hs x
  change q (s x) = x at he
  calc
    _ = q (∑ j, s x j • Pi.single j 1) := by simp only [map_sum, map_smul]
    _ = q (s x) := by rw [← pi_eq_sum_univ']
    _ = x := he

variable {K R A ι κ : Type*} [CommRing K] [CommRing R] [CommRing A]
  [Algebra K R] [Algebra K A] [Algebra R A] [IsScalarTower K R A]
  [Fintype ι] [Fintype κ]

lemma differential_expansion (b : DifferentialFrame K R κ) (x : R) :
    D K A (algebraMap R A x) =
      ∑ j, algebraMap R A (b.coord (D K R x) j) •
        KaehlerDifferential.map K K R A (b.vector j) := by
  have h := congrArg (KaehlerDifferential.map K K R A) (b.sum_coord (D K R x))
  simpa only [map_sum, map_smul, IsScalarTower.algebraMap_smul,
    KaehlerDifferential.map_D] using h.symm

lemma critical_of_coordinates (b : DifferentialFrame K R κ)
    (v : ι → R) (a : ι → A)
    (h : ∀ j, ∑ i, a i * algebraMap R A (b.coord (D K R (v i)) j) = 0) :
    ∑ i, a i • D K A (algebraMap R A (v i)) = 0 := by
  simp_rw [differential_expansion b, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h, zero_smul, Finset.sum_const_zero]

end

noncomputable section
open KaehlerDifferential TensorProduct Algebra
open MaximalSeshadri.Bertini
                                                                               
theorem formallySmooth_principal_of_gradient
    {K S ι : Type*} [CommRing K] [CommRing S] [Algebra K S] [Fintype ι]
    (P : Algebra.Extension K S) [Algebra.FormallySmooth K P.Ring]
    (b : DifferentialFrame K P.Ring ι) (f : P.Ring)
    (hf : Ideal.span ({f} : Set P.Ring) = P.ker)
    (hgrad : Ideal.span (Set.range (fun i =>
      algebraMap P.Ring S (b.coord (D K P.Ring f) i))) = ⊤) :
    Algebra.FormallySmooth K S := by
  have hmem : (1 : S) ∈ Ideal.span (Set.range (fun i =>
      algebraMap P.Ring S (b.coord (D K P.Ring f) i))) := hgrad ▸ (show (1 : S) ∈ (⊤ : Ideal S) from trivial)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  let l : Ω[P.Ring⁄K] →ₗ[P.Ring] S := ∑ i, c i •
    ((Algebra.linearMap P.Ring S).comp ((LinearMap.proj i).comp b.coord))
  apply formallySmooth_principal_of_derivation P f hf (l.compDer (D K P.Ring))
  change l (D K P.Ring f) = 1
  simpa [l, LinearMap.comp_apply, LinearMap.proj_apply] using hc

theorem formallySmooth_quotient_of_gradient
    {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype ι]
    [Algebra.FormallySmooth K R] (b : DifferentialFrame K R ι) (f : R)
    (hgrad : Ideal.span (insert f (Set.range (fun i => b.coord (D K R f) i))) = ⊤) :
    Algebra.FormallySmooth K (R ⧸ Ideal.span ({f} : Set R)) := by
  let I := Ideal.span ({f} : Set R)
  let S := R ⧸ I
  let P : Algebra.Extension K S := Algebra.Extension.ofSurjective
    (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mk_surjective)
  let : Algebra.FormallySmooth K P.Ring := ‹Algebra.FormallySmooth K R›
  have hker : Ideal.span ({f} : Set P.Ring) = P.ker := (Ideal.mk_ker).symm
  have hgrad' : Ideal.span (Set.range (fun i =>
      algebraMap R S (b.coord (D K R f) i))) = ⊤ := by
    have h := congrArg (Ideal.map (Ideal.Quotient.mk I)) hgrad
    have hf : Ideal.Quotient.mk I f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
    simpa only [S, Ideal.Quotient.algebraMap_eq, Ideal.map_span, Set.image_insert_eq, ← Set.range_comp, Function.comp_def, hf,
      Ideal.span_insert_zero, Ideal.map_top] using h
  exact formallySmooth_principal_of_gradient P b f hker hgrad'

end

end MaximalSeshadri.FrameBertini

end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_LinearFamilies
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.LinearBertini
noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K L A ι : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]

theorem parameters_dependent [Algebra.EssFiniteType K L] [Fintype ι]
    (v a : ι → L) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K L (v i) = 0) :
    ¬ AlgebraicIndependent K a := by
  intro ha
  have hd := congrArg (D K L) hzero
  simp only [map_sum, Derivation.leibniz, map_zero, Finset.sum_add_distrib,
    hcritical, zero_add] at hd
  have hi := algebraicIndependent_differentials a ha
  have hz := (Fintype.linearIndependent_iff.mp hi) v hd
  have hbot : Ideal.span (Set.range v) ≤ ⊥ := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hz i
  rw [hunit] at hbot
  exact top_ne_bot (le_antisymm hbot bot_le)

 theorem parameters_polynomial [Algebra.EssFiniteType K L] [Fintype ι]
    (v a : ι → L) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K L (v i) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ MvPolynomial.aeval a p = 0 := by
  have h := parameters_dependent v a hunit hzero hcritical
  classical
  rw [algebraicIndependent_iff] at h
  push Not at h
  obtain ⟨p, hp, hne⟩ := h
  exact ⟨p, hne, hp⟩

variable [CommRing A] [Algebra K A]

lemma parameters_polynomial_image [Algebra.EssFiniteType K L] [Fintype ι]
    [Algebra A L] [IsScalarTower K A L]
    (v a : ι → A) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K A (v i) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      MvPolynomial.aeval (fun i => algebraMap A L (a i)) p = 0 := by
  apply parameters_polynomial (fun i => algebraMap A L (v i))
  · have h := congrArg (Ideal.map (algebraMap A L)) hunit
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, Ideal.map_top] using h
  · simpa only [map_sum, map_mul, map_zero] using congrArg (algebraMap A L) hzero
  · have h := congrArg (KaehlerDifferential.map K K A L) hcritical
    simp only [IsScalarTower.algebraMap_smul]
    simpa only [map_sum, map_smul, KaehlerDifferential.map_D, map_zero] using h

theorem incidence_polynomial [Algebra.FiniteType K A] [Fintype ι]
    (v a : ι → A) (hunit : Ideal.span (Set.range v) = ⊤)
    (hzero : ∑ i, a i * v i = 0)
    (hcritical : ∑ i, a i • D K A (v i) = 0) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ IsNilpotent (MvPolynomial.aeval a p) := by
  classical
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let Q := minimalPrimes A
  let : Fintype Q := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have hf : ∀ q : Q, ∃ p : MvPolynomial ι K,
      p ≠ 0 ∧ MvPolynomial.aeval a p ∈ q.val := by
    intro q
    let : q.val.IsPrime := q.property.isPrime
    let B := A ⧸ q.val
    let F := FractionRing B
    let : Algebra.EssFiniteType B F :=
      Algebra.EssFiniteType.of_isLocalization F (nonZeroDivisors B)
    let : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K B F
    obtain ⟨p, hp, he⟩ := parameters_polynomial_image (L := F) v a hunit hzero hcritical
    refine ⟨p, hp, ?_⟩
    have he' : algebraMap A F (MvPolynomial.aeval a p) = 0 := by
      change (IsScalarTower.toAlgHom K A F) (MvPolynomial.aeval a p) = 0
      rw [MvPolynomial.comp_aeval_apply a (IsScalarTower.toAlgHom K A F)]
      exact he
    have hinj : Function.Injective (algebraMap B F) := IsFractionRing.injective B F
    rw [IsScalarTower.algebraMap_apply A B F] at he'
    have hq : algebraMap A B (MvPolynomial.aeval a p) = 0 :=
      hinj (he'.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  choose p hp hm using hf
  refine ⟨∏ q : Q, p q, Finset.prod_ne_zero_iff.mpr (fun q _ => hp q), ?_⟩
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  let : J.IsPrime := hJ
  obtain ⟨q, hq, hqJ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := J) bot_le
  simp only [map_prod]
  apply (Ideal.IsPrime.prod_mem_iff).mpr
  exact ⟨⟨q, hq⟩, Finset.mem_univ _, hqJ (hm ⟨q, hq⟩)⟩

end
noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

theorem universal_critical_polynomial [Algebra.FiniteType K R]
    (b : DifferentialFrame K R κ) (v : ι → R)
    (hunit : Ideal.span (Set.range v) = ⊤) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial ι R)
          (MvPolynomial ι R ⧸ criticalIdeal b v) (X i)) p) := by
  let T := MvPolynomial ι R
  let A := T ⧸ criticalIdeal b v
  let a : ι → A := fun i => algebraMap T A (X i)
  have hC (r : R) : algebraMap T A (C r) = algebraMap R A r := rfl
  have hzero : ∑ i, a i * algebraMap R A (v i) = 0 := by
    have he : algebraMap T A (universalSection v) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))
    simpa only [universalSection, map_add, map_sum, map_mul,
      hC, a] using he
  have hgrad : ∀ j, ∑ i, a i *
      algebraMap R A (b.coord (D K R (v i)) j) = 0 := by
    intro j
    have he : algebraMap T A (universalGradient b v j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j)))
    simpa only [universalGradient, map_sum, map_mul,
      hC, a] using he
  have hunit' : Ideal.span (Set.range (fun i => algebraMap R A (v i))) = ⊤ := by
    have h := congrArg (Ideal.map (algebraMap R A)) hunit
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, Ideal.map_top] using h
  exact incidence_polynomial (fun i => algebraMap R A (v i)) a hunit' hzero
    (critical_of_coordinates b v a hgrad)

end

noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

omit [CharZero K] in

theorem critical_specialization_eq_top
    (b : DifferentialFrame K R κ) (v : ι → R) (p : MvPolynomial ι K)
    (hp : IsNilpotent (MvPolynomial.aeval (fun i =>
        algebraMap (MvPolynomial ι R)
          (MvPolynomial ι R ⧸ criticalIdeal b v) (X i)) p))
    (t : ι → K) (ht : MvPolynomial.aeval t p ≠ 0) :
    Ideal.span (insert (specializedSection v t)
      (Set.range (specializedGradient b v t))) = ⊤ := by
  classical
  by_contra hne
  let J := Ideal.span (insert (specializedSection v t)
    (Set.range (specializedGradient b v t)))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
  let : M.IsMaximal := hM
  let B := R ⧸ M
  let T := MvPolynomial ι R
  let A := T ⧸ criticalIdeal b v
  let φ : T →ₐ[K] B := (MvPolynomial.aeval (fun i => algebraMap K B (t i))).restrictScalars K
  have hφX (i : ι) : φ (X i) = algebraMap K B (t i) := MvPolynomial.aeval_X _ _
  have hφC (r : R) : φ (C r) = algebraMap R B r := MvPolynomial.aeval_C _ _
  have hφs : φ (universalSection v) = 0 := by
    have he : algebraMap R B (specializedSection v t) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hJM (Ideal.subset_span (Set.mem_insert _ _)))
    simpa only [universalSection, specializedSection, map_add, map_sum, map_mul, hφX, hφC,
      IsScalarTower.algebraMap_apply K R B] using he
  have hφg (j : κ) : φ (universalGradient b v j) = 0 := by
    have he : algebraMap R B (specializedGradient b v t j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (hJM (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))))
    simpa only [universalGradient, specializedGradient, map_sum, map_mul, hφX, hφC,
      IsScalarTower.algebraMap_apply K R B] using he
  have hker : criticalIdeal b v ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro x (rfl | ⟨j, rfl⟩)
    · exact hφs
    · exact hφg j
  let ψ : A →ₐ[K] B := Ideal.Quotient.liftₐ (criticalIdeal b v) φ (fun x hx => hker hx)
  have hspec : IsNilpotent (algebraMap K B (MvPolynomial.aeval t p)) := by
    have h := hp.map ψ
    have hψ (i : ι) : ψ (algebraMap T A (X i)) = algebraMap K B (t i) := by
      change φ (X i) = algebraMap K B (t i)
      exact hφX i
    rw [MvPolynomial.comp_aeval_apply, show (fun i =>
      ψ (algebraMap T A (X i))) = (fun i => algebraMap K B (t i)) from funext hψ] at h
    have he := MvPolynomial.comp_aeval_apply t (Algebra.ofId K B) p
    exact he ▸ h
  exact hspec.not_isUnit ((isUnit_iff_ne_zero.mpr ht).map (algebraMap K B))

end

noncomputable section
open KaehlerDifferential MvPolynomial
open MaximalSeshadri.Bertini MaximalSeshadri.FrameBertini
variable {K R ι κ : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
  [Fintype ι] [Fintype κ]

omit [CharZero K] in
lemma specializedGradient_eq (b : DifferentialFrame K R κ) (v : ι → R)
    (t : ι → K) (j : κ) :
    b.coord (D K R (specializedSection v t)) j = specializedGradient b v t j := by
  simp only [specializedSection, specializedGradient, map_sum,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
    Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]

theorem affine_bertini_smooth [Algebra.Smooth K R]
    (b : DifferentialFrame K R κ) (v : ι → R)
    (hunit : Ideal.span (Set.range v) = ⊤) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨p, hp, hcrit⟩ := universal_critical_polynomial b v hunit
  refine ⟨p, hp, fun t ht => ?_⟩
  have hgrad := critical_specialization_eq_top b v p hcrit t ht
  rw [show specializedGradient b v t = (fun j =>
    b.coord (D K R (specializedSection v t)) j) from
      funext (fun j => (specializedGradient_eq b v t j).symm)] at hgrad
  let : Algebra.FormallySmooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    formallySmooth_quotient_of_gradient b (specializedSection v t) hgrad
  let : Algebra.FinitePresentation K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

end

noncomputable section
open MvPolynomial
open MaximalSeshadri.FrameBertini

theorem affine_bertini {K R ι : Type*} [Field K] [CharZero K] [CommRing R]
    [Algebra K R] [Fintype ι] [Algebra.Smooth K R] (v : ι → R)
    (hunit : Ideal.span (Set.range v) = ⊤) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  obtain ⟨n, ⟨b⟩⟩ := exists_differentialFrame K R
  exact affine_bertini_smooth b v hunit

end
end MaximalSeshadri.LinearBertini

namespace MaximalSeshadri.SchemeBertini
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.LinearBertini

theorem smooth_subscheme_of_affine_quotients
    {K α : Type} [Field K] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, Algebra K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g) (I : X.IdealSheafData)
    [∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j))] :
    Smooth (I.subschemeι ≫ g) := by
  have hOpen (j : α) : IsOpenImmersion (I.subschemeCover.f (U j)) :=
    I.subschemeCover.map_prop (U j)
  let C : I.subscheme.OpenCover := .mkOfCovers α
    (fun j => Spec (CommRingCat.of (Γ(X, (U j).1) ⧸ I.ideal (U j))))
    (fun j => I.subschemeCover.f (U j)) (by
      intro x
      obtain ⟨j, hj⟩ := hcover (I.subschemeι x)
      have hh : x ∈ (I.subschemeCover.f (U j)).opensRange := by
        rw [I.opensRange_subschemeCover_map]
        exact hj
      obtain ⟨y, hy⟩ := hh
      exact ⟨j, y, hy⟩) (by intro j; exact hOpen j)
  let : IsZariskiLocalAtSource (@Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{0}) C
  change ∀ j : α, Smooth (I.subschemeCover.f (U j) ≫ (I.subschemeι ≫ g))
  intro j
  rw [← Category.assoc, I.subschemeCover_map_subschemeι]
  change Smooth (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal (U j))))) ≫
    (U j).2.isoSpec.inv) ≫ (U j).1.ι ≫ g)
  rw [Category.assoc]
  have hu : (U j).2.isoSpec.inv ≫ (U j).1.ι ≫ g = (U j).2.fromSpec ≫ g :=
    (U j).2.isoSpec_inv_ι_assoc g
  rw [hu, ← hOver]
  rw [← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff (P := @Smooth.{0})).mpr
  change RingHom.Smooth ((Ideal.Quotient.mk (I.ideal (U j))).comp
    (algebraMap K Γ(X, (U j).1)))
  exact RingHom.smooth_algebraMap.mpr inferInstance

end
end MaximalSeshadri.SchemeBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_SimultaneousHyperplanes
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
variable {K σ : Type} [Field K]

lemma restrictHyperplaneHom_injective {S T : Subfield K} (h : S ≤ T)
    (f : (MvPolynomial σ T)[X] →ₐ[T] K) (hf : Function.Injective f) :
    Function.Injective (restrictHyperplaneHom h f) :=
  hf.comp (Polynomial.map_injective _ (MvPolynomial.map_injective _ (Subfield.inclusion h).injective))

theorem common_hyperplane_field {ι : Type} [Countable ι]
    (S : ι → Subfield K) (hS : ∀ i, Countable (S i))
    (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧ ∀ i, S i ≤ T := by
  let d : Set K := c ∪ ⋃ i, (S i : Set K)
  have hd : d.Countable := hc.union (Set.countable_iUnion fun i => by
    let := hS i
    exact Set.to_countable _)
  let T := Subfield.closure d
  have hT : Countable T := Cardinal.mk_le_aleph0_iff.mp
    ((Subfield.cardinalMk_closure_le_max _).trans (max_le hd.le_aleph0 le_rfl))
  exact ⟨T, hT, fun _ hx => Subfield.subset_closure (Or.inl hx),
    fun i _ hx => Subfield.subset_closure (Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))⟩

theorem independent_hyperplane_parameters [Fintype σ] [IsAlgClosed K] [Uncountable K]
    (T : Subfield K) [Countable T] :
    ∃ f : (MvPolynomial σ T)[X] →ₐ[T] K, Function.Injective f := by
  let : Countable (MvPolynomial σ T) := AddMonoidAlgebra.coeff_injective.countable
  let : Countable (AddMonoidAlgebra (MvPolynomial σ T) ℕ) :=
    AddMonoidAlgebra.coeff_injective.countable
  let : Countable (MvPolynomial σ T)[X] := Polynomial.toFinsupp_injective.countable
  have hcard : Cardinal.mk (FractionRing (MvPolynomial σ T)[X]) ≤ Cardinal.mk K := by
    rw [Cardinal.mk_fractionRing]
    exact Cardinal.mk_le_aleph0.trans (le_of_lt Cardinal.aleph0_lt_mk)
  obtain ⟨g⟩ := field_embedding_over_countable (R := T) hcard
  refine ⟨g.comp (IsScalarTower.toAlgHom T (MvPolynomial σ T)[X]
    (FractionRing (MvPolynomial σ T)[X])), ?_⟩
  change Function.Injective (fun x : (MvPolynomial σ T)[X] =>
    g (algebraMap (MvPolynomial σ T)[X] (FractionRing (MvPolynomial σ T)[X]) x))
  exact g.injective.comp (IsFractionRing.injective (MvPolynomial σ T)[X] (FractionRing (MvPolynomial σ T)[X]))

end

end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_GenericSmoothness
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

lemma hyperplane_parameter_polynomial_ne_zero {K σ : Type} [Field K]
    (S : Subfield K) (p : MvPolynomial (Option σ) K) (hp : p ≠ 0)
    (hcoeff : (p.coeffs : Set K) ⊆ S)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) (hf : Function.Injective f) :
    MvPolynomial.aeval ((fun o : Option σ => o.elim (f X) (fun i => f (C (MvPolynomial.X i))))) p ≠ 0 := by
  have hrange : p ∈ Set.range (MvPolynomial.map S.subtype) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, hcoeff hx⟩, rfl⟩
  obtain ⟨p₀, rfl⟩ := hrange
  let t : Option σ → K := (fun o : Option σ => o.elim (f X) (fun i => f (C (MvPolynomial.X i))))
  have he : (MvPolynomial.aeval t : MvPolynomial (Option σ) S →ₐ[S] K) =
      f.comp (MvPolynomial.optionEquivLeft S σ).toAlgHom := by
    ext i
    cases i <;> simp [t]
  have hval : MvPolynomial.aeval t (MvPolynomial.map S.subtype p₀) =
      f (MvPolynomial.optionEquivLeft S σ p₀) := by
    rw [show (MvPolynomial.aeval t (MvPolynomial.map S.subtype p₀)) =
      (MvPolynomial.aeval t : MvPolynomial (Option σ) S →ₐ[S] K) p₀ by
        simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
        rfl]
    rw [he]
    rfl
  change MvPolynomial.aeval t (MvPolynomial.map S.subtype p₀) ≠ 0
  rw [hval]
  intro hz
  have hz₀ : p₀ = 0 := (MvPolynomial.optionEquivLeft S σ).injective (hf (by simpa using hz))
  exact hp (by simp [hz₀])

end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem etale_generic_smooth_integral_hyperplane_section {K A ι : Type} {n : ℕ}
    [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [Algebra.Etale (MvPolynomial ι K) A]
    (v : Fin n → A) (i j : Fin n) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b))
    (c : Set K) (hc : c.Countable) :
    ∃ (S : Subfield K), Countable S ∧ c ⊆ S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        IsDomain (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) ∧
        Algebra.Smooth K (A ⧸ Ideal.span {algebraMap K A (f X) -
          ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k}) := by
  classical
  let : Algebra.FormallySmooth K A := Algebra.FormallySmooth.comp K (MvPolynomial ι K) A
  let : Algebra.Smooth K A := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let w : Option (Fin n) → A := fun o => o.elim 1 (fun k => -v k)
  have hw : Ideal.span (Set.range w) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨none, rfl⟩)
  obtain ⟨p, hp, hs⟩ := MaximalSeshadri.LinearBertini.affine_bertini (K := K) w hw
  obtain ⟨S, hS, hcS, hint⟩ := etale_generic_hyperplane_section_s01
    v i j a b hab hvi hvj (c ∪ (p.coeffs : Set K)) (hc.union (show (p.coeffs : Set K).Countable from p.coeffs.countable_toSet))
  refine ⟨S, hS, fun x hx => hcS (Or.inl hx), fun f hf => ⟨hint f hf, ?_⟩⟩
  have hcoeff : (p.coeffs : Set K) ⊆ S := fun _ hx => hcS (Or.inr hx)
  have hn := hyperplane_parameter_polynomial_ne_zero S p hp hcoeff f hf
  let t : Option (Fin n) → K := fun o => o.elim (f X) (fun k => f (C (MvPolynomial.X k)))
  have he : MaximalSeshadri.LinearBertini.specializedSection w t =
      algebraMap K A (f X) - ∑ k, algebraMap K A (f (C (MvPolynomial.X k))) * v k := by
    simp [MaximalSeshadri.LinearBertini.specializedSection, w, t, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  let : Algebra.Smooth K (A ⧸ Ideal.span {MaximalSeshadri.LinearBertini.specializedSection w t}) := hs t hn
  exact Algebra.Smooth.of_equiv (Ideal.quotientEquivAlgOfEq K
    (congrArg (fun x : A => Ideal.span {x}) he))

end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra
variable {K S σ : Type*} [Field K] [CommRing S] [Algebra S K]

lemma permuteHyperplaneHom_injective (e : Option σ ≃ Option σ)
    (f : (MvPolynomial σ S)[X] →ₐ[S] K) (hf : Function.Injective f) :
    Function.Injective (permuteHyperplaneHom e f) :=
  hf.comp (((MvPolynomial.optionEquivLeft S σ).symm.trans
    ((MvPolynomial.renameEquiv S e).trans (MvPolynomial.optionEquivLeft S σ))).injective)

end
noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem simultaneous_reindexed_generic_hyperplane_parameters
    {K σ ι : Type} [Field K] [Countable ι]
    (P : ι → (σ → K) → K → Prop)
    (hP : ∀ i, ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial σ S)[X] →ₐ[S] K, Function.Injective f →
        P i (fun k => f (C (MvPolynomial.X k))) (f X))
    (e : ι → (Option σ ≃ Option σ)) (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧
      ∀ f : (MvPolynomial σ T)[X] →ₐ[T] K, Function.Injective f →
        ∀ i, P i (fun k => f (hyperplaneVariable (e i (some k))))
          (f (hyperplaneVariable (e i none))) := by
  choose S hS hProp using hP
  obtain ⟨T, hT, hcT, hST⟩ := common_hyperplane_field S hS c hc
  refine ⟨T, hT, hcT, fun f hf i => ?_⟩
  let g := restrictHyperplaneHom (hST i) f
  have hg : Function.Injective g := restrictHyperplaneHom_injective (hST i) f hf
  have he := hProp i (permuteHyperplaneHom (e i) g)
    (permuteHyperplaneHom_injective (e i) g hg)
  have hv (o : Option σ) : permuteHyperplaneHom (e i) g (hyperplaneVariable o) =
      f (hyperplaneVariable (e i o)) := by
    rw [permuteHyperplaneHom_variable]
    cases e i o <;> simp only [hyperplaneVariable, Option.elim_none, Option.elim_some]
    · exact restrictHyperplaneHom_X (hST i) f
    · exact restrictHyperplaneHom_CX (hST i) f _
  have hnone := hv none
  have hsome (k : σ) := hv (some k)
  change permuteHyperplaneHom (e i) g X = _ at hnone
  have hfun : (fun k => permuteHyperplaneHom (e i) g (C (MvPolynomial.X k))) =
      (fun k => f (hyperplaneVariable (e i (some k)))) := funext hsome
  rwa [hfun, hnone] at he
end

noncomputable section
open Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem simultaneous_reindexed_smooth_integral_hyperplanes
    {K ι : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable ι] (A σ : ι → Type) [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]
    [∀ j, Algebra K (A j)] [∀ j, Algebra.FiniteType K (A j)]
    [∀ j, Algebra (MvPolynomial (σ j) K) (A j)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) (A j)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) (A j)]
    (v : ∀ j, Fin n → A j) (i₁ i₂ : ι → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) = algebraMap (MvPolynomial (σ j) K) (A j) (MvPolynomial.X (b j)))
    (e : ι → (Option (Fin n) ≃ Option (Fin n)))
    (c : Set K) (hc : c.Countable) :
    ∃ T : Subfield K, Countable T ∧ c ⊆ T ∧
      ∃ f : (MvPolynomial (Fin n) T)[X] →ₐ[T] K, Function.Injective f ∧
        ∀ j, IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) (f (hyperplaneVariable (e j none))) -
          ∑ k, algebraMap K (A j) (f (hyperplaneVariable (e j (some k)))) * v j k}) ∧
          Algebra.Smooth K (A j ⧸ Ideal.span {algebraMap K (A j) (f (hyperplaneVariable (e j none))) -
            ∑ k, algebraMap K (A j) (f (hyperplaneVariable (e j (some k)))) * v j k}) := by
  let P (j : ι) (α : Fin n → K) (β : K) : Prop :=
    IsDomain (A j ⧸ Ideal.span {algebraMap K (A j) β - ∑ k, algebraMap K (A j) (α k) * v j k}) ∧
    Algebra.Smooth K (A j ⧸ Ideal.span {algebraMap K (A j) β - ∑ k, algebraMap K (A j) (α k) * v j k})
  have hP j : ∃ S : Subfield K, Countable S ∧
      ∀ f : (MvPolynomial (Fin n) S)[X] →ₐ[S] K, Function.Injective f →
        P j (fun k => f (C (MvPolynomial.X k))) (f X) := by
    obtain ⟨S, hS, _, h⟩ := etale_generic_smooth_integral_hyperplane_section
      (v j) (i₁ j) (i₂ j) (a j) (b j) (hab j) (hva j) (hvb j)
      (∅ : Set K) Set.countable_empty
    exact ⟨S, hS, h⟩
  obtain ⟨T, hT, hcT, hh⟩ := simultaneous_reindexed_generic_hyperplane_parameters P hP e c hc
  let : Countable T := hT
  obtain ⟨f, hf⟩ := independent_hyperplane_parameters (σ := Fin n) T
  exact ⟨T, hT, hcT, f, hf, hh f hf⟩

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Bertini_IntegralSubschemes
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.nonemptyAffineCover_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory

theorem integral_of_integral_open_cover {X : Scheme} (C : X.OpenCover)
    [∀ i, IsIntegral (C.X i)] (i₀ : C.I₀)
    (hoverlap : ∀ i, (Set.range (C.f i₀) ∩ Set.range (C.f i)).Nonempty) :
    IsIntegral X := by
  let : IsReduced X := IsReduced.of_openCover X C
  have hd : Dense (Set.range (C.f i₀)) := by
    apply dense_iff_inter_open.mpr
    intro V hV hVne
    obtain ⟨x, hx⟩ := hVne
    obtain ⟨i, y, hy⟩ := C.exists_eq x
    have hVpre : ((C.f i) ⁻¹' V).Nonempty := ⟨y, by
      change C.f i y ∈ V
      rw [hy]
      exact hx⟩
    have hOpre : ((C.f i) ⁻¹' Set.range (C.f i₀)).Nonempty := by
      obtain ⟨z, hz₀, hz⟩ := hoverlap i
      obtain ⟨w, rfl⟩ := hz
      exact ⟨w, hz₀⟩
    obtain ⟨w, hwV, hwO⟩ := nonempty_preirreducible_inter
      (hV.preimage (C.f i).continuous)
      ((C.f i₀).isOpenEmbedding.isOpen_range.preimage (C.f i).continuous) hVpre hOpre
    exact ⟨C.f i w, hwV, hwO⟩
  have hi : IsIrreducible (Set.range (C.f i₀)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := C.X i₀)).image (C.f i₀)
        (C.f i₀).continuous.continuousOn
  let : IrreducibleSpace X := (irreducibleSpace_def X).mpr (by
    change IsIrreducible (Set.univ : Set X)
    rw [← hd.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem integral_subscheme_of_affine_quotients {α : Type} (X : Scheme.{0})
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    (I : X.IdealSheafData) [∀ j, IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j))]
    (j₀ : α) (hoverlap : ∀ j, ∃ x : I.subscheme,
      I.subschemeι x ∈ (U j₀).1 ∧ I.subschemeι x ∈ (U j).1) :
    IsIntegral I.subscheme := by
  have hD (j : α) : IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := inferInstance
  have hOpen (j : α) : IsOpenImmersion (I.subschemeCover.f (U j)) :=
    I.subschemeCover.map_prop (U j)
  let : ∀ j, IsOpenImmersion (I.subschemeCover.f (U j)) := hOpen
  let C : I.subscheme.OpenCover := .mkOfCovers α
    (fun j => Spec (CommRingCat.of (Γ(X, (U j).1) ⧸ I.ideal (U j))))
    (fun j => I.subschemeCover.f (U j)) (by
      intro x
      obtain ⟨j, hj⟩ := hcover (I.subschemeι x)
      have hh : x ∈ (I.subschemeCover.f (U j)).opensRange := by
        rw [I.opensRange_subschemeCover_map]
        exact hj
      obtain ⟨y, hy⟩ := hh
      exact ⟨j, y, hy⟩) (by intro j; exact hOpen j)
  let : ∀ j, IsIntegral (C.X j) := fun j => by
    change IsIntegral (Spec (CommRingCat.of (Γ(X, (U j).1) ⧸ I.ideal (U j))))
    exact (affine_isIntegral_iff _).mpr (hD j)
  apply integral_of_integral_open_cover C j₀
  intro j
  let : IsOpenImmersion (I.subschemeCover.f (U j)) := hOpen j
  let : IsOpenImmersion (I.subschemeCover.f (U j₀)) := hOpen j₀
  obtain ⟨x, hx₀, hx⟩ := hoverlap j
  refine ⟨x, ?_, ?_⟩
  · change x ∈ (I.subschemeCover.f (U j₀)).opensRange
    rw [I.opensRange_subschemeCover_map]
    exact hx₀
  · change x ∈ (I.subschemeCover.f (U j)).opensRange
    rw [I.opensRange_subschemeCover_map]
    exact hx

end

noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory

theorem subscheme_meets_affine {X : Scheme.{0}} (I : X.IdealSheafData)
    (U : X.affineOpens) [Nontrivial (Γ(X, U.1) ⧸ I.ideal U)] :
    ∃ x : I.subscheme, I.subschemeι x ∈ U.1 := by
  let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
  obtain ⟨y⟩ := (inferInstance : Nonempty
    (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U))))
  refine ⟨I.subschemeCover.f U y, ?_⟩
  have hx : I.subschemeCover.f U y ∈ (I.subschemeCover.f U).opensRange := ⟨y, rfl⟩
  rw [I.opensRange_subschemeCover_map] at hx
  exact hx

theorem integral_subscheme_of_affine_overlap_quotients {α : Type} (X : Scheme.{0})
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    (I : X.IdealSheafData) [∀ j, IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j))]
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1) :
    IsIntegral I.subscheme := by
  apply integral_subscheme_of_affine_quotients X U hcover I j₀
  intro j
  obtain ⟨x, hx⟩ := subscheme_meets_affine I (U (overlap j))
  exact ⟨x, hleft j hx, hright j hx⟩

end

noncomputable section
open AlgebraicGeometry TopologicalSpace CategoryTheory Polynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

lemma vanishingIdeal_compl_eq_span {X : Scheme} (D : X.Opens)
    (U : X.affineOpens) (f : Γ(X, U.1))
    (hD : U.2.fromSpec ⁻¹ᵁ D = PrimeSpectrum.basicOpen f)
    [IsDomain (Γ(X, U.1) ⧸ Ideal.span {f})] :
    (Scheme.IdealSheafData.vanishingIdeal D.compl).ideal U = Ideal.span {f} := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal
    (U.2.fromSpec ⁻¹' (D.compl : Set X) : Set (PrimeSpectrum Γ(X, U.1))) = Ideal.span {f}
  have hset : (U.2.fromSpec ⁻¹' (D.compl : Set X) : Set (PrimeSpectrum Γ(X, U.1))) =
      PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set Γ(X, U.1))) := by
    rw [PrimeSpectrum.zeroLocus_span]
    have h := congrArg (fun V : (Spec (CommRingCat.of Γ(X, U.1))).Opens =>
      (V : Set (Spec (CommRingCat.of Γ(X, U.1))))) hD
    change U.2.fromSpec ⁻¹' (D : Set X) =
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(X, U.1))) at h
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at h
    have hc := congrArg (fun s : Set (PrimeSpectrum Γ(X, U.1)) => sᶜ) h
    change (U.2.fromSpec ⁻¹' (D : Set X) : Set (PrimeSpectrum Γ(X, U.1)))ᶜ = _
    exact hc.trans (compl_compl _)
  rw [hset, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact ((Ideal.Quotient.isDomain_iff_prime _).mp inferInstance).isRadical.radical

end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] [Fintype σ]

lemma linearEquation_chart (t : σ → R) (i : σ) :
    Away.isLocalizationElem (poly_X_mem (R := R) i) (linearEquation_homogeneous t) =
      ∑ j, chartConstants i (t j) * chartCoordinate i j := by
  apply HomogeneousLocalization.val_injective _
  change (Away.mk _ _ 1 _ _).val = _
  rw [chart_val_mk]
  rw [← HomogeneousLocalization.algebraMap_apply]
  simp only [linearEquation, map_sum, map_mul, pow_one,
    HomogeneousLocalization.algebraMap_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [chart_val_constants, chart_val_coordinate]
  exact mul_assoc _ _ _

lemma hyperplane_chart_preimage (t : σ → R) (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (linearEquation t) =
      PrimeSpectrum.basicOpen (∑ j, chartConstants i (t j) * chartCoordinate i j) := by
  rw [Proj.awayι_preimage_basicOpen _ _ (by decide) (linearEquation_homogeneous t)
    (by decide), linearEquation_chart]

omit [Fintype σ] in
lemma chartCoordinate_self (i : σ) : chartCoordinate (R := R) i i = 1 := by
  apply HomogeneousLocalization.val_injective _
  rw [chart_val_coordinate, HomogeneousLocalization.val_one]
  exact IsLocalization.Away.mul_invSelf (X i)

lemma hyperplane_affine_preimage {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (U : Y.affineOpens) (i : σ) (φ : PolyChart (R := R) i →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h)
    (t : σ → R) :
    U.2.fromSpec ⁻¹ᵁ (h ⁻¹ᵁ Proj.basicOpen (PolyGrade R σ) (linearEquation t)) =
      PrimeSpectrum.basicOpen (∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j)) := by
  rw [← Scheme.Hom.comp_preimage, ← hφ, Scheme.Hom.comp_preimage,
    hyperplane_chart_preimage]
  ext x
  change φ (∑ j, chartConstants i (t j) * chartCoordinate i j) ∉ x.asIdeal ↔
    (∑ j, φ (chartConstants i (t j)) * φ (chartCoordinate i j)) ∉ x.asIdeal
  simp only [map_sum, map_mul]

lemma hyperplane_affine_preimage_reindexed {K : Type} [Field K] {n : ℕ}
    {Y : Scheme} (h : Y ⟶ Proj (PolyGrade K (Option (Fin n))))
    (U : Y.affineOpens) [Algebra K Γ(Y, U.1)]
    (e : Option (Fin n) ≃ Option (Fin n))
    (φ : PolyChart (R := K) (e none) →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option (Fin n))) (X (e none)) (poly_X_mem (e none))
        (by decide) = U.2.fromSpec ≫ h)
    (hK : ∀ c, φ (chartConstants (e none) c) = algebraMap K Γ(Y, U.1) c)
    (t : Option (Fin n) → K) :
    U.2.fromSpec ⁻¹ᵁ (h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n)))
      (linearEquation t)) = PrimeSpectrum.basicOpen
        (algebraMap K Γ(Y, U.1) (t (e none)) -
          ∑ j, algebraMap K Γ(Y, U.1) (t (e (some j))) *
            (-φ (chartCoordinate (e none) (e (some j))))) := by
  rw [hyperplane_affine_preimage h U (e none) φ hφ]
  congr 1
  rw [← e.sum_comp]
  simp only [Fintype.sum_option, hK, chartCoordinate_self, map_one, mul_one,
    mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

end

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R σ : Type u} [CommRing R] [Fintype σ]

omit [Fintype σ] in
                                                                            
lemma projective_affine_constants {Y : Scheme} (h : Y ⟶ Proj (PolyGrade R σ))
    (g : Y ⟶ Spec (CommRingCat.of R)) (hbase : h ≫ projectiveToSpec = g)
    (U : Y.affineOpens) [Algebra R Γ(Y, U.1)]
    (hOver : Spec.map (CommRingCat.ofHom (algebraMap R Γ(Y, U.1))) = U.2.fromSpec ≫ g)
    (i : σ) (φ : PolyChart (R := R) i →+* Γ(Y, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) = U.2.fromSpec ≫ h) :
    ∀ c, φ (chartConstants i c) = algebraMap R Γ(Y, U.1) c := by
  have he : CommRingCat.ofHom (φ.comp (chartConstants i)) =
      CommRingCat.ofHom (algebraMap R Γ(Y, U.1)) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp, ← chart_toSpec,
      ← Category.assoc, hφ, Category.assoc, hbase, hOver]
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom he)

end
end MaximalSeshadri.Projective


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_BertiniEquations
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem smooth_integral_zero_family_with_equations
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (v : ∀ j, Fin n → Γ(X, (U j).1)) (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (D : (Option (Fin n) → K) → X.Opens)
    (hD : ∀ t j, (U j).2.fromSpec ⁻¹ᵁ D t = PrimeSpectrum.basicOpen
      (algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal (D t).compl).subscheme ∧
      Smooth ((Scheme.IdealSheafData.vanishingIdeal (D t).compl).subschemeι ≫ g) ∧
      ∀ j, (Scheme.IdealSheafData.vanishingIdeal (D t).compl).ideal (U j) =
        Ideal.span {algebraMap K Γ(X, (U j).1) (t (e j none)) -
          ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k} := by
  obtain ⟨T, _, hqT, f, hf, hh⟩ := simultaneous_reindexed_smooth_integral_hyperplanes
    (fun j => Γ(X, (U j).1)) σ v i₁ i₂ a b hab hva hvb e
    (q.coeffs : Set K) q.coeffs.countable_toSet
  let t : Option (Fin n) → K := fun o => f (hyperplaneVariable o)
  have hqv : MvPolynomial.aeval t q ≠ 0 := by
    have ht : t = (fun o => o.elim (f Polynomial.X)
        (fun i => f (C (MvPolynomial.X i)))) := by
      funext o
      cases o <;> rfl
    rw [ht]
    exact hyperplane_parameter_polynomial_ne_zero T q hq hqT f hf
  let I := Scheme.IdealSheafData.vanishingIdeal (D t).compl
  have hI (j : α) : I.ideal (U j) = Ideal.span
      {algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k} := by
    let := (hh j).1
    exact vanishingIdeal_compl_eq_span (D t) (U j) _ (hD t j)
  have hDom (j : α) : IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := by
    rw [hI]
    exact (hh j).1
  have hS (j : α) : Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j)) := by
    rw [hI]
    exact (hh j).2
  let : ∀ j, IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := hDom
  let : ∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j)) := hS
  exact ⟨t, hqv,
    integral_subscheme_of_affine_overlap_quotients X U hcover I j₀ overlap hleft hright,
    MaximalSeshadri.SchemeBertini.smooth_subscheme_of_affine_quotients
      X g U hcover hOver I, hI⟩

theorem smooth_integral_hyperplane_of_etale_atlas_with_equations_s01_oai
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
    (hbase : h ≫ projectiveToSpec = g)
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (φ : ∀ j, PolyChart (R := K) (e j none) →+* Γ(X, (U j).1))
    (hφ : ∀ j, Spec.map (CommRingCat.ofHom (φ j)) ≫
      Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X (e j none))
        (poly_X_mem (e j none)) (by decide) = (U j).2.fromSpec ≫ h)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j) (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₁ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₂ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
      ∀ j, (projectiveHyperplane h t).ideal (U j) =
        Ideal.span {∑ k, φ j (chartConstants (e j none) (t k)) *
          φ j (chartCoordinate (e j none) k)} := by
  obtain ⟨t, ht, hI, hS, heq⟩ := smooth_integral_zero_family_with_equations X g U hcover hOver σ
    (fun j k => -φ j (chartCoordinate (e j none) (e j (some k))))
    i₁ i₂ a b hab hva hvb e
    (fun t => h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n))) (linearEquation t))
    (fun t j => hyperplane_affine_preimage_reindexed h (U j) (e j) (φ j) (hφ j)
      (projective_affine_constants h g hbase (U j) (hOver j) _ (φ j) (hφ j)) t)
    j₀ overlap hleft hright q hq

  refine ⟨t, ht, hI, hS, fun j => ?_⟩
  unfold projectiveHyperplane
  rw [heq j]
  congr 1
  rw [← (e j).sum_comp]
  simp only [Fintype.sum_option, chartCoordinate_self, map_one, mul_one,
    projective_affine_constants h g hbase (U j) (hOver j) _ (φ j) (hφ j),
    mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

end
end MaximalSeshadri.BertiniIntegral
end


end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_hyperplane_of_etale_atlas_with_equations_s01_oai := @OAI.MaximalSeshadri.BertiniIntegral.smooth_integral_hyperplane_of_etale_atlas_with_equations_s01_oai

-- Prove2me | solution 1 for OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:15:47.754132+00:00
-- url     : https://prove2.me/submissions/7810234d-c631-439b-bbcb-24fd35c2f0eb

import Mathlib
import Definitions.Def_Q223SES004

section
-- module Solutions.Q223_SES.Seshadri_Analytic_TaylorCoefficients
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter Set

theorem analyticCoefficients_eq_derivative (f : analyticFunctionAlgebra) (a b : ℕ) :
    analyticCoefficients f (a,b) * (a.factorial : ℂ) * (b.factorial : ℂ) =
      iteratedDeriv b (fun z => iteratedDeriv a (fun x => f.val (x,z)) 0) 0 := by
  rw [mixedDeriv_congr_germ _ _ (analyticCoefficients_spec f).2 a b]
  exact (mixedDeriv_at_zero _ (analyticCoefficients_spec f).1 a b).symm

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_FormalSeries
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open PowerSeries Filter

lemma analyticFormal_constantCoeff (f : analyticFunctionAlgebra) :
    constantCoeff (constantCoeff (analyticFormal f)) = f.val (0,0) := by
  have h := analyticCoefficients_eq_derivative f 0 0
  simpa [analyticFormal, biSeries, constantCoeff_mk, iteratedDeriv_zero] using h

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open PowerSeries

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

lemma binaryEquiv_coeff (f : MvPowerSeries (Fin 2) F) (a b : ℕ) :
    coeff a (coeff b (binaryEquiv F f)) =
      MvPowerSeries.coeff (Finsupp.cons b (Finsupp.cons a 0)) f := by
  simp only [binaryEquiv, AlgEquiv.trans_apply, powerSeriesMapEquiv_coeff]
  change MvPowerSeries.coeff 0 (coeff a (MvPowerSeries.finSuccEquiv F 0
    (coeff b (MvPowerSeries.finSuccEquiv F 1 f)))) = _
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, MvPowerSeries.coeff_coeff_finSuccEquiv]

lemma binaryEquiv_constantCoeff (f : MvPowerSeries (Fin 2) F) :
    constantCoeff (constantCoeff (binaryEquiv F f)) = MvPowerSeries.constantCoeff f := by
  have h := binaryEquiv_coeff f 0 0
  simpa using h

end
end MaximalSeshadri.FormalCoordinates


end
end
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

end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_CoordinateJets
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open Filter PowerSeries
open MaximalSeshadri.FormalCoordinates

variable {S : Type*} [CommRing S] [Algebra ℂ S]

lemma analyticTaylor_constantCoeff (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.constantCoeff (analyticTaylor q hq s) = q 0 s := by
  rw [← binaryEquiv_constantCoeff]
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  exact analyticFormal_constantCoeff _

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

omit [Finite σ] in

lemma jetChart_unique [Algebra.FormallyUnramified (MvPolynomial σ F) S]
    (n : ℕ) (hn : 0 < n)
    (τ₁ τ₂ : S →ₐ[F] JetAlgebra σ F n)
    (hc : τ₁.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) =
      τ₂.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S))
    (haug : ∀ s, jetAugment n hn (τ₁ s) = jetAugment n hn (τ₂ s)) : τ₁ = τ₂ := by
  let β := τ₁.comp (IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
  let : Algebra (MvPolynomial σ F) (JetAlgebra σ F n) := β.toRingHom.toAlgebra
  let f₁ : S →ₐ[MvPolynomial σ F] JetAlgebra σ F n :=
    { τ₁.toRingHom with commutes' := fun _ => rfl }
  let f₂ : S →ₐ[MvPolynomial σ F] JetAlgebra σ F n :=
    { τ₂.toRingHom with commutes' := fun p => (AlgHom.congr_fun hc p).symm }
  have heq := Algebra.FormallyUnramified.lift_unique_of_ringHom
    (R := MvPolynomial σ F) (jetAugment (σ := σ) (R := F) n hn).toRingHom
    (jetAugment_ker_nilpotent n hn) f₁ f₂ (RingHom.ext haug)
  apply AlgHom.ext
  intro s
  have hs : f₁ s = f₂ s := AlgHom.congr_fun heq s
  exact hs

lemma formalTrunc_augment (n : ℕ) (hn : 0 < n) (f : MvPowerSeries σ F) :
    jetAugment n hn (formalTrunc n f) = MvPowerSeries.constantCoeff f := by
  change jetAugment n hn (Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f)) = _
  rw [jetAugment_mk, MvPowerSeries.constantCoeff_truncTotal_eq_ite, ite_eq_left hn]

lemma formalTrunc_polynomial (n : ℕ) (p : MvPolynomial σ F) :
    formalTrunc n (p : MvPowerSeries σ F) = Ideal.Quotient.mk _ p :=
  (MvPowerSeries.truncTotalAlgHom σ F n).commutes p

variable [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

theorem formalTaylor_detects_ideal_power
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) (hn : 0 < n) :
    RingHom.ker ((formalTrunc n).comp τ) = (RingHom.ker ρ)^n := by
  obtain ⟨g, hg, hgc⟩ := exists_regular_taylor (σ := σ) (F := F) (S := S) n hn
  have heq : (formalTrunc n).comp τ = specializeTaylor n g ρ := by
    apply jetChart_unique n hn
    · rw [specializeTaylor_coordinate n g hgc ρ]
      ext i
      change formalTrunc n (τ (algebraMap (MvPolynomial σ F) S (X i))) = _
      rw [hcoord]
      have hpoly := formalTrunc_polynomial n
        (C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + X i)
      simpa [polynomialTranslate, add_comm] using hpoly
    · intro s
      rw [AlgHom.comp_apply, formalTrunc_augment n hn, hconst,
        specializeTaylor_augment n hn g hg]
  rw [heq]
  exact regularTaylor_detects_ideal_power n hn g hg hgc ρ

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_FormalAdic
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.FormalAdic
noncomputable section
open IsLocalRing
variable {σ R : Type*} [Finite σ] [CommRing R]

lemma completion_eval_kernel (I : Ideal R) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  ext x
  have h := AdicCompletion.pow_smul_top_eq_ker_eval (M := R) (n := n) hI
  have heval : AdicCompletion.evalₐ I n x = 0 ↔ AdicCompletion.eval I R n x = 0 := by
    let e := Ideal.quotientEquivAlgOfEq R (show (I ^ n • ⊤ : Ideal R) = I ^ n by simp)
    dsimp only [AdicCompletion.evalₐ, AlgHom.comp_apply, AlgHom.ofLinearMap_apply]
    exact map_eq_zero_iff e e.injective
  change AdicCompletion.evalₐ I n x = 0 ↔ _
  rw [heval, ← LinearMap.mem_ker, ← h]
  rw [← Ideal.map_pow]
  simp

lemma trunc_eq_completion_eval (n : ℕ) :
    (MvPowerSeries.truncTotalAlgHom σ R n).toRingHom =
      (AdicCompletion.evalₐ (MvPolynomial.idealOfVars σ R) n).toRingHom.comp
        (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingHom := by
  apply RingHom.ext
  intro f
  change (MvPowerSeries.truncTotalAlgHom σ R n) f =
    AdicCompletion.evalₐ _ n (MvPowerSeries.toAdicCompletion σ R f)
  unfold MvPowerSeries.toAdicCompletion
  erw [AdicCompletion.evalₐ_liftAlgHom]
  intro m n h
  apply AlgHom.ext
  intro p
  simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
    MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) p

omit [Finite σ] in
lemma polynomials_map_vars :
    (MvPolynomial.idealOfVars σ R).map
        (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) =
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.coe_X i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X i, ⟨i, rfl⟩, MvPolynomial.coe_X i⟩

lemma trunc_kernel (n : ℕ) :
    RingHom.ker (MvPowerSeries.truncTotalAlgHom σ R n).toRingHom =
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ n := by
  let e := MvPowerSeries.toAdicCompletionAlgEquiv σ R
  rw [trunc_eq_completion_eval, ← RingHom.comap_ker,
    completion_eval_kernel _ (MvPolynomial.idealOfVars_fg σ R)]
  have he : (algebraMap (MvPolynomial σ R) (AdicCompletion (MvPolynomial.idealOfVars σ R)
      (MvPolynomial σ R))) = e.toRingHom.comp
      (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) := by
    apply RingHom.ext
    intro p
    exact (e.commutes p).symm
  rw [he, ← Ideal.map_map, ← Ideal.map_pow]
  change (Ideal.map e.toRingHom _).comap e.toRingHom = _
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective, polynomials_map_vars]

variable {K : Type*} [Field K]

omit [Finite σ] in
lemma maximalIdeal_eq_ker_constantCoeff :
    maximalIdeal (MvPowerSeries σ K) =
      RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries σ K →+* K) := by
  ext f
  rw [mem_maximalIdeal, mem_nonunits_iff, RingHom.mem_ker, MvPowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not]

lemma maximalIdeal_eq_vars :
    maximalIdeal (MvPowerSeries σ K) =
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ K)) := by
  rw [← pow_one (Ideal.span _), ← trunc_kernel]
  ext f
  rw [maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker, RingHom.mem_ker]
  change _ ↔ Ideal.Quotient.mk _ (MvPowerSeries.truncTotal 1 f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro hf d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    rw [MvPowerSeries.coeff_truncTotal _ hd, hd0]
    exact hf
  · intro hf
    simpa [MvPowerSeries.coeff_truncTotal _ (show (0 : σ →₀ ℕ).degree < 1 by simp)]
      using hf 0 (by simp)

lemma trunc_kernel_maximalIdeal (n : ℕ) :
    RingHom.ker (MvPowerSeries.truncTotalAlgHom σ K n).toRingHom =
      maximalIdeal (MvPowerSeries σ K) ^ n := by
  rw [trunc_kernel, maximalIdeal_eq_vars]

end
end MaximalSeshadri.FormalAdic


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_LocalQuotients
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
open MvPolynomial IsLocalRing
open MaximalSeshadri.FormalAdic MaximalSeshadri.LocalComparison
variable {σ F S : Type*} [Finite σ] [Field F] [CommRing S] [Algebra F S]
  [Algebra (MvPolynomial σ F) S] [IsScalarTower F (MvPolynomial σ F) S]

lemma formalTaylor_surjective_jet
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) : Function.Surjective ((formalTrunc n).comp τ) := by
  have heq : ((formalTrunc n).comp τ).comp
      (IsScalarTower.toAlgHom F (MvPolynomial σ F) S) =
      (Ideal.Quotient.mkₐ F _).comp (polynomialTranslate
        (fun i => ρ (algebraMap (MvPolynomial σ F) S (X i)))).toAlgHom := by
    ext i
    change formalTrunc n (τ (algebraMap (MvPolynomial σ F) S (X i))) = _
    rw [hcoord]
    have hpoly := formalTrunc_polynomial n
      (C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + X i)
    simpa [polynomialTranslate, add_comm] using hpoly
  apply Function.Surjective.of_comp (g := IsScalarTower.toAlgHom F (MvPolynomial σ F) S)
  change Function.Surjective (((formalTrunc n).comp τ).comp
    (IsScalarTower.toAlgHom F (MvPolynomial σ F) S))
  rw [heq]
  exact Ideal.Quotient.mk_surjective.comp (polynomialTranslate _).surjective

lemma formalTaylor_surjective_localJet
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ F) ^ n)).comp τ.toRingHom) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨s, hs⟩ := formalTaylor_surjective_jet ρ τ hcoord n (formalTrunc n y)
  refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
  rw [← trunc_kernel_maximalIdeal, RingHom.mem_ker]
  change formalTrunc n (τ s - y) = 0
  rw [map_sub, sub_eq_zero]
  exact hs

variable [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

lemma formalTaylor_localJet_kernel
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i)
    (n : ℕ) : RingHom.ker
      ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries σ F) ^ n)).comp τ.toRingHom) =
      (RingHom.ker ρ) ^ n := by
  by_cases hn : n = 0
  · simp [hn, ← RingHom.comap_ker, Ideal.mk_ker]
  rw [← RingHom.comap_ker, Ideal.mk_ker, ← trunc_kernel_maximalIdeal,
    RingHom.comap_ker]
  exact formalTaylor_detects_ideal_power ρ τ hconst hcoord n (Nat.pos_of_ne_zero hn)

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_CoordinateEquivalences
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open IsLocalRing

lemma ringEnd_injective_of_surjective {R : Type*} [CommRing R] [IsNoetherianRing R]
    (f : R →+* R) (hs : Function.Surjective f) : Function.Injective f := by
  let K : ℕ →o Ideal R := {
    toFun := fun n => RingHom.ker (f ^ n)
    monotone' := by
      apply monotone_nat_of_le_succ
      intro n x hx
      change (f ^ (n + 1)) x = 0
      rw [pow_succ', RingHom.coe_mul, Function.comp_apply]
      change (f ^ n) x = 0 at hx
      rw [hx, map_zero] }
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (show IsNoetherian R R from inferInstance) K
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, hy⟩ := hs.iterate n x
  have hy' : (f ^ n) y = x := hy
  have hm : y ∈ K (n + 1) := by
    change (f ^ (n + 1)) y = 0
    rw [pow_succ', RingHom.coe_mul, Function.comp_apply, hy']
    exact hx
  rw [← hn (n + 1) (Nat.le_succ n)] at hm
  change (f ^ n) y = 0 at hm
  exact (hy'.symm.trans hm)

variable {σ K : Type*} [Finite σ] [Field K]

local notation "P" => MvPowerSeries σ K
local notation "𝔪" => maximalIdeal P

lemma complete_maximal : IsAdicComplete 𝔪 P := by
  rw [FormalAdic.maximalIdeal_eq_vars]
  infer_instance

lemma map_maximal_eq_of_cotangent (φ : P →ₐ[K] P)
    (hlocal : (𝔪).map φ.toRingHom ≤ 𝔪)
    (htangent : 𝔪 ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2) :
    (𝔪).map φ.toRingHom = 𝔪 := by
  apply le_antisymm hlocal
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
    (IsNoetherian.noetherian 𝔪)
    (show 𝔪 ≤ Ideal.jacobson (⊥ : Ideal P) by
      rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
  simpa only [pow_two, Ideal.smul_eq_mul] using htangent

lemma bijective_of_cotangent (φ : P →ₐ[K] P)
    (hlocal : (𝔪).map φ.toRingHom ≤ 𝔪)
    (htangent : 𝔪 ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2) :
    Function.Bijective φ := by
  let := complete_maximal (σ := σ) (K := K)
  have hm := map_maximal_eq_of_cotangent φ hlocal htangent
  let : IsHausdorff ((𝔪).map φ.toRingHom) P := by
    rw [hm]
    infer_instance
  have hs : Function.Surjective φ := by
    apply surjective_of_mk_map_comp_surjective (I := 𝔪) φ.toRingHom
    intro y
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap K P (MvPowerSeries.constantCoeff f), ?_⟩
    change Ideal.Quotient.mk _ (φ (algebraMap K P _)) = _
    rw [φ.commutes, Ideal.Quotient.eq]
    rw [hm, FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker]
    simp [MvPowerSeries.algebraMap_apply]
  exact ⟨ringEnd_injective_of_surjective φ.toRingHom hs, hs⟩

omit [Finite σ] in

lemma equiv_comap_pow_maximal (e : P ≃ₐ[K] P) (n : ℕ) :
    (𝔪 ^ n).comap e.toRingHom = 𝔪 ^ n := by
  have hm : (𝔪).map e.toRingHom = 𝔪 := by
    apply IsLocalRing.eq_maximalIdeal
    change (Ideal.map e.toRingEquiv 𝔪).IsMaximal
    infer_instance
  calc
    (𝔪 ^ n).comap e.toRingHom = ((𝔪).map e.toRingHom ^ n).comap e.toRingHom :=
      congrArg (fun J : Ideal P => (J ^ n).comap e.toRingHom) hm.symm
    _ = 𝔪 ^ n := by
      rw [← Ideal.map_pow, Ideal.comap_map_of_bijective e.toRingHom e.bijective]

lemma mem_maximal_pow_iff (f : P) (n : ℕ) :
    f ∈ 𝔪 ^ n ↔ ∀ d : σ →₀ ℕ, d.degree < n → MvPowerSeries.coeff d f = 0 := by
  rw [← FormalAdic.trunc_kernel_maximalIdeal, RingHom.mem_ker]
  change Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  constructor <;> intro h d hd
  · simpa only [MvPowerSeries.coeff_truncTotal _ hd] using h d hd
  · simpa only [MvPowerSeries.coeff_truncTotal _ hd] using h d hd

lemma mem_maximal_sq_iff (f : P) :
    f ∈ 𝔪 ^ 2 ↔ MvPowerSeries.constantCoeff f = 0 ∧
      ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) f = 0 := by
  rw [mem_maximal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun i => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ d hd
    by_cases he : d.degree = 0
    · have : d = 0 := (Finsupp.degree_eq_zero_iff d).mp he
      simpa [this] using h0
    · have he : d.degree = 1 := by omega
      obtain ⟨i, rfl⟩ := (Set.ext_iff.mp Finsupp.range_single_one d).mpr he
      exact h1 i

variable [Fintype σ] [DecidableEq σ]

lemma subst_bijective_of_inverse_linear (a : σ → P)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (b : σ → σ → K)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1) (a l) =
      if i = j then 1 else 0) :
    Function.Bijective (MvPowerSeries.substAlgHom (R := K)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)) := by
  classical
  let φ : P →ₐ[K] P := MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero h0)
  have hx (i : σ) : (MvPowerSeries.X i : P) ∈ 𝔪 := by
    rw [FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker]
    simp
  have hlocal : (𝔪).map φ.toRingHom ≤ 𝔪 := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply le_trans (FormalAdic.maximalIdeal_eq_vars (σ := σ) (K := K)).le
    apply Ideal.span_le.mpr
    rintro f ⟨i, rfl⟩
    change φ (MvPowerSeries.X i) ∈ 𝔪
    rw [MvPowerSeries.substAlgHom_X, FormalAdic.maximalIdeal_eq_ker_constantCoeff,
      RingHom.mem_ker]
    exact h0 i
  apply bijective_of_cotangent φ hlocal
  apply le_trans (FormalAdic.maximalIdeal_eq_vars (σ := σ) (K := K)).le
  apply Ideal.span_le.mpr
  rintro f ⟨i, rfl⟩
  let s : P := ∑ l, MvPowerSeries.C (b i l) * a l
  have hs : s ∈ (𝔪).map φ.toRingHom := by
    apply Ideal.sum_mem
    intro l _
    apply Ideal.mul_mem_left
    have h := Ideal.mem_map_of_mem φ.toRingHom (hx l)
    simpa only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_X] using h
  have hd : (MvPowerSeries.X i : P) - s ∈ 𝔪 ^ 2 := by
    rw [mem_maximal_sq_iff]
    constructor
    · simp [s, h0]
    · intro j
      simp only [s, map_sub, map_sum, MvPowerSeries.coeff_C_mul]
      rw [hb]
      simp only [MvPowerSeries.coeff_X]
      simp only [Finsupp.single_left_inj (show (1 : ℕ) ≠ 0 by omega), eq_comm,
        sub_self]
  have hh := Submodule.add_mem
    ((𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2) ((show 𝔪 ^ 2 ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2 from le_sup_right) hd)
      ((show (𝔪).map φ.toRingHom ≤ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2 from le_sup_left) hs)
  change (MvPowerSeries.X i : P) ∈ (𝔪).map φ.toRingHom ⊔ 𝔪 ^ 2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  exact (sub_add_cancel _ _).symm

omit [Finite σ] [Fintype σ] [DecidableEq σ] in

lemma constantCoeff_equiv (e : P ≃ₐ[K] P) (f : P) :
    MvPowerSeries.constantCoeff (e f) = MvPowerSeries.constantCoeff f := by
  have hf : f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈ 𝔪 := by
    rw [FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker]
    simp
  have he : e (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) ∈ 𝔪 := by
    have hh := equiv_comap_pow_maximal e 1
    simp only [pow_one] at hh
    rw [← hh] at hf
    exact hf
  rw [FormalAdic.maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker] at he
  have hc (c : K) : e (MvPowerSeries.C c) = MvPowerSeries.C c := e.commutes c
  simpa only [map_sub, hc, MvPowerSeries.constantCoeff_C, sub_eq_zero] using he

end
end MaximalSeshadri.FormalCoordinates

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open IsLocalRing MvPolynomial
open FormalCoordinates
variable {σ F S : Type*} [Fintype σ] [DecidableEq σ] [Field F]
  [CommRing S] [Algebra F S] [Algebra (MvPolynomial σ F) S]
  [IsScalarTower F (MvPolynomial σ F) S]

local notation "P" => MvPowerSeries σ F

omit [IsScalarTower F (MvPolynomial σ F) S] in

lemma exists_standardized_formalTaylor (ρ : S →ₐ[F] F) (τ : S →ₐ[F] P)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (b : σ → σ → F)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
      (τ (algebraMap (MvPolynomial σ F) S (X l))) = if i = j then 1 else 0) :
    ∃ e : P ≃ₐ[F] P,
      (∀ s, MvPowerSeries.constantCoeff (e.symm (τ s)) = ρ s) ∧
      ∀ i, e.symm (τ (algebraMap (MvPolynomial σ F) S (X i))) =
        MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) +
          MvPowerSeries.X i := by
  let a (i : σ) : P := τ (algebraMap (MvPolynomial σ F) S (X i)) -
    MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i)))
  have ha (i : σ) : MvPowerSeries.constantCoeff (a i) = 0 := by
    simp [a, hconst]
  have hab (i j : σ) : ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1) (a l) =
      if i = j then 1 else 0 := by
    simpa [a, MvPowerSeries.coeff_C] using hb i j
  let φ : P →ₐ[F] P := MvPowerSeries.substAlgHom
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)
  let e : P ≃ₐ[F] P := AlgEquiv.ofBijective φ
    (subst_bijective_of_inverse_linear a ha b hab)
  refine ⟨e, fun s => (constantCoeff_equiv e.symm (τ s)).trans (hconst s), ?_⟩
  intro i
  apply e.injective
  rw [AlgEquiv.apply_symm_apply, map_add]
  have heC (c : F) : e (MvPowerSeries.C c) = MvPowerSeries.C c := e.commutes c
  rw [heC]
  change τ _ = MvPowerSeries.C _ + φ (MvPowerSeries.X i)
  rw [MvPowerSeries.substAlgHom_X]
  dsimp [a]
  ring

variable [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S]

theorem fullRankTaylor_localJet_kernel (ρ : S →ₐ[F] F) (τ : S →ₐ[F] P)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (b : σ → σ → F)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
      (τ (algebraMap (MvPolynomial σ F) S (X l))) = if i = j then 1 else 0)
    (n : ℕ) : RingHom.ker
      ((Ideal.Quotient.mk (maximalIdeal P ^ n)).comp τ.toRingHom) = (RingHom.ker ρ)^n := by
  obtain ⟨e, hec, hex⟩ := exists_standardized_formalTaylor ρ τ hconst b hb
  let τ₀ : S →ₐ[F] P := e.symm.toAlgHom.comp τ
  have hk := formalTaylor_localJet_kernel ρ τ₀ hec hex n
  rw [← RingHom.comap_ker, Ideal.mk_ker] at hk ⊢
  change (maximalIdeal P ^ n).comap τ.toRingHom = _
  rw [← hk]
  change _ = ((maximalIdeal P ^ n).comap e.symm.toRingHom).comap τ.toRingHom
  rw [equiv_comap_pow_maximal]

omit [Algebra.FormallyEtale (MvPolynomial σ F) S]
  [Algebra.EssFiniteType (MvPolynomial σ F) S] in
                                                                     
theorem fullRankTaylor_surjective_localJet (ρ : S →ₐ[F] F) (τ : S →ₐ[F] P)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (b : σ → σ → F)
    (hb : ∀ i j, ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
      (τ (algebraMap (MvPolynomial σ F) S (X l))) = if i = j then 1 else 0)
    (n : ℕ) : Function.Surjective
      ((Ideal.Quotient.mk (maximalIdeal P ^ n)).comp τ.toRingHom) := by
  obtain ⟨e, hec, hex⟩ := exists_standardized_formalTaylor ρ τ hconst b hb
  let τ₀ : S →ₐ[F] P := e.symm.toAlgHom.comp τ
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨s, hs⟩ := formalTaylor_surjective_localJet ρ τ₀ hex n
    (Ideal.Quotient.mk _ (e.symm f))
  refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
  have hh : e.symm (τ s - f) ∈ maximalIdeal P ^ n := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hs
  have hm := equiv_comap_pow_maximal e.symm n
  change τ s - f ∈ (maximalIdeal P ^ n).comap e.symm.toRingHom at hh
  rwa [hm] at hh

end
end MaximalSeshadri.AlgebraicJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_AnalyticFullRank
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology

open AlgebraicJets FormalCoordinates MvPolynomial
variable {S : Type*} [CommRing S] [Algebra ℂ S]

lemma analyticTaylor_coeff_zero (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.coeff (Finsupp.single 0 1) (analyticTaylor q hq s) =
      deriv (fun z => q (0,z) s) 0 := by
  have he : (Finsupp.cons 1 (Finsupp.cons 0 0) : Fin 2 →₀ ℕ) =
      Finsupp.single 0 1 := by
    ext i
    fin_cases i
    · simp
    · change (Finsupp.cons 1 (Finsupp.cons 0 0)) (Fin.succ (0 : Fin 1)) = _
      rw [Finsupp.cons_succ]
      simp
  have h := binaryEquiv_coeff (analyticTaylor q hq s) 0 1
  rw [he] at h
  rw [←h]
  have hb : binaryEquiv ℂ (analyticTaylor q hq s) = analyticFormal (analyticPullback q hq s) := by
    exact (binaryEquiv ℂ).apply_symm_apply _
  rw [hb]
  have hc : PowerSeries.coeff 0 (PowerSeries.coeff 1 (analyticFormal (analyticPullback q hq s))) =
      analyticCoefficients (analyticPullback q hq s) (0,1) := by
    change PowerSeries.coeff _ (PowerSeries.coeff _ (biSeries (analyticCoefficients _))) = _
    simp [biSeries]
  rw [hc]
  have hd := analyticCoefficients_eq_derivative (analyticPullback q hq s) 0 1
  simpa [iteratedDeriv_succ, iteratedDeriv_zero, analyticPullback] using hd

lemma analyticTaylor_coeff_one (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.coeff (Finsupp.single 1 1) (analyticTaylor q hq s) =
      deriv (fun x => q (x,0) s) 0 := by
  have he : (Finsupp.cons 0 (Finsupp.cons 1 0) : Fin 2 →₀ ℕ) =
      Finsupp.single 1 1 := by
    ext i
    fin_cases i
    · simp
    · change (Finsupp.cons 0 (Finsupp.cons 1 0)) (Fin.succ (0 : Fin 1)) = _
      rw [Finsupp.cons_succ]
      simp
  have h := binaryEquiv_coeff (analyticTaylor q hq s) 1 0
  rw [he] at h
  rw [←h]
  have hb : binaryEquiv ℂ (analyticTaylor q hq s) = analyticFormal (analyticPullback q hq s) := by
    exact (binaryEquiv ℂ).apply_symm_apply _
  rw [hb]
  have hc : PowerSeries.coeff 1 (PowerSeries.coeff 0 (analyticFormal (analyticPullback q hq s))) =
      analyticCoefficients (analyticPullback q hq s) (1,0) := by
    change PowerSeries.coeff _ (PowerSeries.coeff _ (biSeries (analyticCoefficients _))) = _
    simp [biSeries]
  rw [hc]
  have hd := analyticCoefficients_eq_derivative (analyticPullback q hq s) 1 0
  simpa [iteratedDeriv_succ, iteratedDeriv_zero, analyticPullback] using hd

lemma analyticTaylor_fullRank
    [Algebra (MvPolynomial (Fin 2) ℂ) S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ))
    (he : HasFDerivAt (fun z =>
      (q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1)),
       q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0)))) (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) :
    ∃ b : Fin 2 → Fin 2 → ℂ, ∀ i j,
      ∑ l, b i l * MvPowerSeries.coeff (Finsupp.single j 1)
        (analyticTaylor q hq (algebraMap (MvPolynomial (Fin 2) ℂ) S (X l))) =
      if i = j then 1 else 0 := by
  have hv : HasDerivAt (fun z : ℂ => ((0 : ℂ),z)) (0,1) 0 :=
    (hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id (0 : ℂ))
  have hh : HasDerivAt (fun z : ℂ => (z,(0 : ℂ))) (1,0) 0 :=
    (hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  have h00 := (he.snd.comp_hasDerivAt (f := fun z : ℂ => ((0 : ℂ),z)) 0 hv).deriv
  have h01 := (he.snd.comp_hasDerivAt (f := fun z : ℂ => (z,(0 : ℂ))) 0 hh).deriv
  have h10 := (he.fst.comp_hasDerivAt (f := fun z : ℂ => ((0 : ℂ),z)) 0 hv).deriv
  have h11 := (he.fst.comp_hasDerivAt (f := fun z : ℂ => (z,(0 : ℂ))) 0 hh).deriv
  change deriv (fun z => q (0,z) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))) 0 = (e (0,1)).2 at h00
  change deriv (fun z => q (z,0) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))) 0 = (e (1,0)).2 at h01
  change deriv (fun z => q (0,z) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1))) 0 = (e (0,1)).1 at h10
  change deriv (fun z => q (z,0) (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1))) 0 = (e (1,0)).1 at h11
  have hfin : (1 : Fin 2) ≠ 0 := by decide
  have hi (z : ℂ × ℂ) : z.1 • e.symm (1,0) + z.2 • e.symm (0,1) = e.symm z := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  refine ⟨fun i l => if i = 0 then
    (if l = 0 then (e.symm (0,1)).2 else (e.symm (1,0)).2)
    else (if l = 0 then (e.symm (0,1)).1 else (e.symm (1,0)).1), ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.sum_univ_two, Fin.mk_zero, Fin.isValue, hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_zero, analyticTaylor_coeff_zero]
    rw [h00,h10]
    simpa [Prod.snd_add, Prod.snd_smul, mul_comm, add_comm] using congrArg Prod.snd (hi (e (0,1)))
  · simp only [Fin.sum_univ_two, Fin.mk_zero, Fin.mk_one, Fin.isValue, hfin, Ne.symm hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_one, analyticTaylor_coeff_one]
    rw [h01,h11]
    simpa [Prod.snd_add, Prod.snd_smul, mul_comm, add_comm] using congrArg Prod.snd (hi (e (1,0)))
  · simp only [Fin.sum_univ_two, Fin.mk_zero, Fin.mk_one, Fin.isValue, hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_zero, analyticTaylor_coeff_zero]
    rw [h00,h10]
    simpa [Prod.fst_add, Prod.fst_smul, mul_comm, add_comm] using congrArg Prod.fst (hi (e (0,1)))
  · simp only [Fin.sum_univ_two, Fin.mk_one, Fin.isValue, hfin, ↓reduceIte]
    rw [analyticTaylor_coeff_one, analyticTaylor_coeff_one]
    rw [h01,h11]
    simpa [Prod.fst_add, Prod.fst_smul, mul_comm, add_comm] using congrArg Prod.fst (hi (e (1,0)))

theorem analyticTaylor_exactJets_s01_oai
    [Algebra (MvPolynomial (Fin 2) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
    [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ))
    (he : HasFDerivAt (fun z =>
      (q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 1)),
       q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (X 0))))
       (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) (n : ℕ) :
    RingHom.ker ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) =
        (RingHom.ker (q 0))^n ∧
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (MvPowerSeries (Fin 2) ℂ)^n)).comp (analyticTaylor q hq).toRingHom) := by
  obtain ⟨b,hb⟩ := analyticTaylor_fullRank q hq e he
  exact ⟨fullRankTaylor_localJet_kernel (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) b hb n,
    fullRankTaylor_surjective_localJet (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) b hb n⟩

end
end MaximalSeshadri.AnalyticCoordinates

end


end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets_s01_oai.{u_1} := @OAI.MaximalSeshadri.AnalyticCoordinates.analyticTaylor_exactJets_s01_oai.{u_1}

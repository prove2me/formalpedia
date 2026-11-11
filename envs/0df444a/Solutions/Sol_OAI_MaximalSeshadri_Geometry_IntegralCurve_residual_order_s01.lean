-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.IntegralCurve.residual_order_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:04.267439+00:00
-- url     : https://prove2.me/submissions/78453c88-0bc4-4e4f-929b-4cf6e35e29cb

import Mathlib
import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_Q223SES006
import Definitions.Def_Q223SES007

section
-- module Solutions.Q223_SES.Compat
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_TaylorCoefficients
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

local instance instHasAntidiagonalExponent_2_r997811_1 : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite
lemma analyticCoefficients_congr (f g : analyticFunctionAlgebra)
    (h : f.val =ᶠ[𝓝 0] g.val) : analyticCoefficients f = analyticCoefficients g := by
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec f).1
    (analyticCoefficients_spec g).1
  exact (analyticCoefficients_spec f).2.symm.trans (h.trans (analyticCoefficients_spec g).2)

lemma analyticFormal_congr (f g : analyticFunctionAlgebra)
    (h : f.val =ᶠ[𝓝 0] g.val) : analyticFormal f = analyticFormal g := by
  exact congrArg biSeries (analyticCoefficients_congr f g h)

lemma analyticFormal_constantCoeff (f : analyticFunctionAlgebra) :
    constantCoeff (constantCoeff (analyticFormal f)) = f.val (0,0) := by
  have h := analyticCoefficients_eq_derivative f 0 0
  simpa [analyticFormal, biSeries, constantCoeff_mk, iteratedDeriv_zero] using h

lemma analyticCoefficients_monomial (f : analyticFunctionAlgebra) (e : Exponent) (c : ℂ)
    (heq : f.val =ᶠ[𝓝 0] (fun q => c * q.1 ^ e.1 * q.2 ^ e.2)) :
    analyticCoefficients f = fun p => if p = e then c else 0 := by
  let d : Exponent → ℂ := fun p => if p = e then c else 0
  have hd : ConvergentSeries d := by
    refine ⟨1, zero_lt_one, ?_⟩
    simp only [AbsolutelyConvergentAt, d, apply_ite, norm_zero, one_pow, mul_one]
    exact (hasSum_ite_eq e ‖c‖).summable
  have hde (x z : ℂ) : seriesEval d x z = c * x ^ e.1 * z ^ e.2 := by
    simp [seriesEval, d, ite_mul]
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec f).1 hd
  filter_upwards [(analyticCoefficients_spec f).2, heq] with q hq hqq
  rw [← hq, hde, hqq]

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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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

lemma analyticFormal_first : analyticFormal analyticFirst = C (X : PowerSeries ℂ) := by
  have hc := analyticCoefficients_monomial analyticFirst (1,0) 1 (by
    apply Filter.Eventually.of_forall
    intro z
    simp [analyticFirst])
  apply biCoeff_injective
  ext e
  change biCoeff (biSeries (analyticCoefficients analyticFirst)) e = _
  rw [biCoeff_biSeries, hc]
  rcases e with ⟨a,b⟩
  by_cases hb : b = 0 <;> simp [biCoeff, coeff_C, coeff_X, hb, Prod.ext_iff]

lemma analyticFormal_second : analyticFormal analyticSecond = (X : BiSeries) := by
  have hc := analyticCoefficients_monomial analyticSecond (0,1) 1 (by
    apply Filter.Eventually.of_forall
    intro z
    simp [analyticSecond])
  apply biCoeff_injective
  ext e
  change biCoeff (biSeries (analyticCoefficients analyticSecond)) e = _
  rw [biCoeff_biSeries, hc]
  rcases e with ⟨a,b⟩
  by_cases hb : b = 1 <;> simp [biCoeff, coeff_X, hb, Prod.ext_iff]

variable {S : Type*} [CommRing S] [Algebra ℂ S]

lemma analyticTaylor_constantCoeff (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) :
    MvPowerSeries.constantCoeff (analyticTaylor q hq s) = q 0 s := by
  rw [← binaryEquiv_constantCoeff]
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply]
  exact analyticFormal_constantCoeff _

lemma analyticTaylor_affineFirst (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) (c : ℂ)
    (hs : ∀ᶠ z in 𝓝 0, q z s = c + z.1) :
    analyticTaylor q hq s = MvPowerSeries.C c + MvPowerSeries.X 1 := by
  apply (binaryEquiv ℂ).injective
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, map_add, binaryEquiv_X_one]
  have heq : analyticFormal (analyticPullback q hq s) =
      analyticFormal (algebraMap ℂ analyticFunctionAlgebra c + analyticFirst) :=
    analyticFormal_congr _ _ hs
  rw [heq, map_add, analyticFormal_first, AlgHom.commutes]
  congr 1
  exact ((binaryEquiv ℂ).commutes c).symm

lemma analyticTaylor_affineSecond (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0) (s : S) (c : ℂ)
    (hs : ∀ᶠ z in 𝓝 0, q z s = c + z.2) :
    analyticTaylor q hq s = MvPowerSeries.C c + MvPowerSeries.X 0 := by
  apply (binaryEquiv ℂ).injective
  simp only [analyticTaylor, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, map_add, binaryEquiv_X_zero]
  have heq : analyticFormal (analyticPullback q hq s) =
      analyticFormal (algebraMap ℂ analyticFunctionAlgebra c + analyticSecond) :=
    analyticFormal_congr _ _ hs
  rw [heq, map_add, analyticFormal_second, AlgHom.commutes]
  congr 1
  exact ((binaryEquiv ℂ).commutes c).symm

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

theorem formalTaylor_injective [IsNoetherianRing S] [IsDomain S]
    (ρ : S →ₐ[F] F) (τ : S →ₐ[F] MvPowerSeries σ F)
    (hconst : ∀ s, MvPowerSeries.constantCoeff (τ s) = ρ s)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial σ F) S (X i)) =
      MvPowerSeries.C (ρ (algebraMap (MvPolynomial σ F) S (X i))) + MvPowerSeries.X i) :
    Function.Injective τ := by
  apply (injective_iff_map_eq_zero τ).mpr
  intro s hs
  have hproper : RingHom.ker ρ ≠ ⊤ := RingHom.ker_ne_top _
  have hmem : s ∈ ⨅ n : ℕ, (RingHom.ker ρ)^n := by
    rw [Ideal.mem_iInf]
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · rw [← formalTaylor_detects_ideal_power ρ τ hconst hcoord n (Nat.pos_of_ne_zero hn)]
      change formalTrunc n (τ s) = 0
      rw [hs, map_zero]
  have hsep : (⨅ n : ℕ, (RingHom.ker ρ)^n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isDomain (I := RingHom.ker ρ) hproper
  rw [hsep] at hmem
  exact hmem

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped Topology
open MaximalSeshadri.AlgebraicJets
variable {S : Type*} [CommRing S] [Algebra ℂ S]
  [Algebra (MvPolynomial (Fin 2) ℂ) S] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S]

omit [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S]
  [Algebra.EssFiniteType (MvPolynomial (Fin 2) ℂ) S] in

lemma analyticTaylor_coordinates
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (hc : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1)) (i : Fin 2) :
    analyticTaylor q hq (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      MvPowerSeries.C (q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i))) +
        MvPowerSeries.X i := by
  fin_cases i
  · apply analyticTaylor_affineSecond
    filter_upwards [hc] with z hz
    simpa using hz 0
  · apply analyticTaylor_affineFirst
    filter_upwards [hc] with z hz
    simpa using hz 1

theorem analyticTaylor_detects_ideal_power
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (hc : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1)) (n : ℕ) (hn : 0 < n) :
    RingHom.ker ((formalTrunc n).comp (analyticTaylor q hq)) = (RingHom.ker (q 0))^n :=
  formalTaylor_detects_ideal_power (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) (analyticTaylor_coordinates q hq hc) n hn

theorem analyticTaylor_injective [IsNoetherianRing S] [IsDomain S]
    (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
    (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0)
    (hc : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1)) :
    Function.Injective (analyticTaylor q hq) :=
  formalTaylor_injective (q 0) (analyticTaylor q hq)
    (analyticTaylor_constantCoeff q hq) (analyticTaylor_coordinates q hq hc)

end
end MaximalSeshadri.AnalyticCoordinates


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
open scoped BigOperators
variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma polynomialDifferential_C (L : ι → E →L[𝕜] 𝕜) (c : 𝕜) (x : E) :
    polynomialDifferential L (C c) x = 0 := by
  ext v
  simp [polynomialDifferential]

lemma polynomialDifferential_add (L : ι → E →L[𝕜] 𝕜) (p q : MvPolynomial ι 𝕜) (x : E) :
    polynomialDifferential L (p + q) x =
      polynomialDifferential L p x + polynomialDifferential L q x := by
  ext v
  simp [polynomialDifferential, add_mul, Finset.sum_add_distrib]

lemma polynomialDifferential_mul (L : ι → E →L[𝕜] 𝕜) (p q : MvPolynomial ι 𝕜) (x : E) :
    polynomialDifferential L (p * q) x =
      eval (fun i => L i x) p • polynomialDifferential L q x +
        eval (fun i => L i x) q • polynomialDifferential L p x := by
  ext v
  simp [polynomialDifferential, Derivation.leibniz, smul_eq_mul, add_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.mul_sum]

lemma polynomialDifferential_X (L : ι → E →L[𝕜] 𝕜) (i : ι) (x : E) :
    polynomialDifferential L (X i) x = L i := by
  classical
  ext v
  simp [polynomialDifferential, pderiv_X, Pi.single_apply, apply_ite, ite_apply]

theorem hasFDerivAt_polynomialEval (L : ι → E →L[𝕜] 𝕜) (p : MvPolynomial ι 𝕜) (x : E) :
    HasFDerivAt (fun y => eval (fun i => L i y) p) (polynomialDifferential L p x) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialDifferential_C] using hasFDerivAt_const (𝕜 := 𝕜) c x
  | add p q hp hq =>
      simpa [polynomialDifferential_add, Pi.add_def] using hp.add hq
  | mul_X p i hp =>
      simpa [polynomialDifferential_mul, polynomialDifferential_X, Pi.mul_def] using
        hp.mul ((L i).hasFDerivAt (x := x))

theorem analyticAt_polynomial_eval (p : MvPolynomial ι 𝕜) (x : ι → 𝕜) :
    AnalyticAt 𝕜 (fun y => eval y p) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using analyticAt_const (𝕜 := 𝕜) (E := ι → 𝕜) (v := c) (x := x)
  | add p q hp hq => simpa [Pi.add_def] using hp.add hq
  | mul_X p i hp =>
      simpa [Pi.mul_def] using hp.mul ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x)

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators Matrix ContDiff
open MvPolynomial
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

omit [DecidableEq σ] in
lemma augmentedPolynomial_hasFDerivAt (P : Algebra.SubmersivePresentation F S ι σ)
    (x : ι → F) : HasFDerivAt (augmentedPolynomial P) (augmentedDerivative P x) x := by
  have h₁ := (hasFDerivAt_pi.mpr fun i : σ =>
    hasFDerivAt_polynomialEval (fun a : ι => ContinuousLinearMap.proj (R := F) a)
      (P.relation i) x)
  have h₂ : HasFDerivAt (fun y : ι → F => fun i : {i : ι // i ∉ Set.range P.map} => y i.val)
      (ContinuousLinearMap.pi fun i : {i : ι // i ∉ Set.range P.map} =>
        ContinuousLinearMap.proj (R := F) i.val) x :=
    hasFDerivAt_pi.mpr fun i => (ContinuousLinearMap.proj (R := F) i.val).hasFDerivAt (x := x)
  apply (h₁.prodMk h₂).congr_fderiv
  ext v
  all_goals simp [augmentedDerivative, augmentedLinear, polynomialDifferential,
    Matrix.mulVec, dotProduct]

omit [DecidableEq σ] in
lemma augmentedPolynomial_analyticAt (P : Algebra.SubmersivePresentation F S ι σ)
    (x : ι → F) : AnalyticAt F (augmentedPolynomial P) x := by
  exact (AnalyticAt.pi fun i => analyticAt_polynomial_eval (P.relation i) x).prod
    (AnalyticAt.pi fun i => (ContinuousLinearMap.proj (R := F) i.val).analyticAt x)

theorem exists_analytic_augmented_inverse
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ ψ : ((σ → F) × ({i : ι // i ∉ Set.range P.map} → F)) → (ι → F),
      ψ (augmentedPolynomial P (fun a => ρ (P.val a))) = (fun a => ρ (P.val a)) ∧
      AnalyticAt F ψ (augmentedPolynomial P (fun a => ρ (P.val a))) ∧
      ∀ᶠ y in nhds (augmentedPolynomial P (fun a => ρ (P.val a))),
        augmentedPolynomial P (ψ y) = y := by
  let x : ι → F := fun a => ρ (P.val a)
  let f := augmentedPolynomial P
  let e' := augmentedDerivativeEquiv P ρ
  have hd : HasFDerivAt f (e' : (ι → F) →L[F] _) x := by
    convert! augmentedPolynomial_hasFDerivAt P x using 1
    all_goals try with_reducible_and_instances rfl
  have hc : ContDiffAt F ω f x := (augmentedPolynomial_analyticAt P x).contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let e := hc.toOpenPartialHomeomorph f hd hn
  let ψ := hc.localInverse hd hn
  refine ⟨ψ, hc.localInverse_apply_image hd hn, (hc.to_localInverse hd hn).analyticAt, ?_⟩
  have hm : f x ∈ e.target := hc.image_mem_toOpenPartialHomeomorph_target hd hn
  filter_upwards [e.open_target.mem_nhds hm] with y hy
  exact e.right_inv hy

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_PointCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
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
variable {F S ι σ : Type*} [CommRing F] [CommRing S] [Algebra F S]

lemma presentationPoint_apply (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (s : S) :
    presentationPoint P x hx s = eval x (P.σ s) := by
  simp [presentationPoint]

lemma presentationPoint_aeval (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (f : MvPolynomial ι F) :
    presentationPoint P x hx (aeval P.val f) = eval x f := by
  have he : (P.quotientEquiv.restrictScalars F).symm (aeval P.val f) =
      Ideal.Quotient.mk P.ker f := by
    apply (P.quotientEquiv.restrictScalars F).injective
    simp
  simp only [presentationPoint, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [he]
  simp

lemma presentationPoint_val (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (i : ι) :
    presentationPoint P x hx (P.val i) = x i := by
  simpa using presentationPoint_aeval P x hx (X i)

lemma presentationPoint_at_point (P : Algebra.Presentation F S ι σ) (ρ : S →ₐ[F] F) :
    presentationPoint P (fun a => ρ (P.val a)) (evaluation_relations P ρ) = ρ := by
  ext s
  obtain ⟨f, rfl⟩ := P.aeval_val_surjective s
  rw [presentationPoint_aeval]
  change aeval (fun a => ρ (P.val a)) f = _
  rw [← MvPolynomial.comp_aeval]
  rfl

end

noncomputable section
open MvPolynomial
open scoped BigOperators Matrix ContDiff
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

theorem exists_analytic_zero_chart
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ γ : ({i : ι // i ∉ Set.range P.map} → F) → (ι → F),
      γ (fun i => ρ (P.val i.val)) = (fun a => ρ (P.val a)) ∧
      AnalyticAt F γ (fun i => ρ (P.val i.val)) ∧
      ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
        (∀ i, eval (γ z) (P.relation i) = 0) ∧ (∀ i, γ z i.val = z i) := by
  obtain ⟨ψ, hbase, han, hinv⟩ := exists_analytic_augmented_inverse P ρ
  have he : augmentedPolynomial P (fun a => ρ (P.val a)) =
      (0, fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)) := by
    ext a
    · exact evaluation_relations P.toPresentation ρ a
    · rfl
  rw [he] at hbase han hinv
  let γ : ({i : ι // i ∉ Set.range P.map} → F) → (ι → F) := fun z => ψ (0, z)
  have hz : AnalyticAt F (fun z : ({i : ι // i ∉ Set.range P.map} → F) =>
      ((0 : σ → F), z)) (fun i => ρ (P.val i.val)) :=
    analyticAt_const.prod analyticAt_id
  refine ⟨γ, hbase, han.comp hz, ?_⟩
  filter_upwards [hz.continuousAt.eventually hinv] with z hz'
  constructor
  · intro i
    exact congrArg (fun y => y.1 i) hz'
  · intro i
    exact congrArg (fun y => y.2 i) hz'

theorem exists_analytic_point_chart
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F),
      q (fun i => ρ (P.val i.val)) = ρ ∧
      (∀ s : S, AnalyticAt F (fun z => q z s) (fun i => ρ (P.val i.val))) ∧
      ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
        ∀ i, q z (P.val i.val) = z i := by
  classical
  obtain ⟨γ, hbase, han, hrel⟩ := exists_analytic_zero_chart P ρ
  let q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F) := fun z =>
    if h : ∀ i, eval (γ z) (P.relation i) = 0 then
      presentationPoint P.toPresentation (γ z) h else ρ
  have heq : ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
      ∀ s, q z s = eval (γ z) (P.σ s) := by
    filter_upwards [hrel] with z hz
    intro s
    simp only [q, dite_eq_left hz.1]
    exact presentationPoint_apply P.toPresentation (γ z) hz.1 s
  refine ⟨q, ?_, ?_, ?_⟩
  · have hzero : ∀ i, eval (γ (fun i => ρ (P.val i.val))) (P.relation i) = 0 := by
      rw [hbase]
      exact evaluation_relations P.toPresentation ρ
    simp only [q, dite_eq_left hzero]
    simpa only [hbase] using presentationPoint_at_point P.toPresentation ρ
  · intro s
    have h := (analyticAt_polynomial_eval (P.σ s) _).comp han
    apply h.congr
    filter_upwards [heq] with z hz
    exact (hz s).symm
  · filter_upwards [hrel] with z hz
    intro i
    simp only [q, dite_eq_left hz.1]
    rw [presentationPoint_val]
    exact hz.2 i

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped Topology ContDiff
open MvPolynomial
variable {ι σ S : Type*} [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra ℂ S]

theorem exists_binary_point_chart
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : {i : ι // i ∉ Set.range P.map} ≃ Fin 2) (ρ : S →ₐ[ℂ] ℂ) :
    ∃ q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : S, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
        q z (P.val (e.symm i)) = ρ (P.val (e.symm i)) +
          (if i = 0 then z.2 else z.1) := by
  obtain ⟨q₀, hbase, han, hc⟩ := exists_analytic_point_chart P ρ
  let α (z : ℂ × ℂ) (i : {i : ι // i ∉ Set.range P.map}) :=
    ρ (P.val i) + (if e i = 0 then z.2 else z.1)
  have hα : AnalyticAt ℂ α 0 := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.add analyticAt_const
    by_cases h : e i = 0
    · simpa only [ite_eq_left h] using (analyticAt_snd (𝕜 := ℂ) (p := (0 : ℂ × ℂ)))
    · simpa only [ite_eq_right h] using (analyticAt_fst (𝕜 := ℂ) (p := (0 : ℂ × ℂ)))
  have hα₀ : α 0 = (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i)) := by
    ext i
    simp [α]
  refine ⟨fun z => q₀ (α z), ?_, ?_, ?_⟩
  · change q₀ (α 0) = ρ
    rw [hα₀, hbase]
  · intro s
    have h : AnalyticAt ℂ (fun z => q₀ z s) (α 0) := by
      rw [hα₀]
      exact han s
    exact h.comp hα
  · have hcp : ∀ᶠ z in 𝓝 (α 0), ∀ i, q₀ z (P.val i.val) = z i := by
      rw [hα₀]
      exact hc
    have hpull := hα.continuousAt.eventually hcp
    filter_upwards [hpull] with z hz
    intro i
    simpa [α] using hz (e.symm i)

end
end MaximalSeshadri.AlgebraicJets


end
end
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

noncomputable section
open KaehlerDifferential
universe u v w
variable {R : Type u} {S : Type v} {ι : Type w}
  [CommRing R] [CommRing S] [Algebra R S]

lemma differentials_span_of_generators (v : ι → S)
    (hv : Function.Surjective (MvPolynomial.aeval (R := R) v)) :
    Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤ := by
  apply top_unique
  rw [← span_range_derivation R S, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  obtain ⟨q, rfl⟩ := hv s
  induction q using MvPolynomial.induction_on with
  | C c =>
      simp only [MvPolynomial.aeval_C, Derivation.map_algebraMap]
      exact Submodule.zero_mem _
  | add f g hf hg =>
      simp only [map_add]
      exact Submodule.add_mem _ hf hg
  | mul_X f i hf =>
      simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
        (Submodule.smul_mem _ _ hf)

theorem exists_local_differential_basis [Algebra.Smooth R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ g : S, g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι)
      (b : Module.Basis κ (Localization.Away g) Ω[Localization.Away g⁄R]),
      ∀ i, b i = D R (Localization.Away g) (algebraMap S (Localization.Away g) (v (a i))) := by
  let w : ι → Ω[Localization.AtPrime p⁄R] :=
    fun i => map R R S (Localization.AtPrime p) (D R S (v i))
  have hw : Submodule.span (Localization.AtPrime p) (Set.range w) = ⊤ := by
    have hh := span_eq_top_of_isLocalizedModule (Localization.AtPrime p) p.primeCompl
      (map R R S (Localization.AtPrime p)) hv
    simpa only [← Set.range_comp, Function.comp_def, w] using hh
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat w hw
  let e : (κ →₀ S) →ₗ[S] Ω[S⁄R] :=
    Finsupp.linearCombination S fun i : κ => D R S (v (a i))
  let l₁ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.AtPrime p) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S (Localization.AtPrime p))
  let l₂ : Ω[S⁄R] →ₗ[S] Ω[Localization.AtPrime p⁄R] := map R R S (Localization.AtPrime p)
  let eₚ : (κ →₀ Localization.AtPrime p) →ₗ[Localization.AtPrime p]
      Ω[Localization.AtPrime p⁄R] :=
    IsLocalizedModule.mapExtendScalars p.primeCompl l₁ l₂ (Localization.AtPrime p) e
  have he : eₚ = b.repr.symm := by
    ext i
    trans IsLocalizedModule.map p.primeCompl l₁ l₂ e (l₁ (Finsupp.single i 1))
    · simp [eₚ, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, e, hb, w]
  have heₚ : Function.Bijective eₚ := he ▸ b.repr.symm.bijective
  have : Finite κ := Module.Finite.finite_basis b
  obtain ⟨g, hg, h⟩ := Module.FinitePresentation.exists_notMem_bijective e p l₁ l₂ heₚ
  let l₁ₜ : (κ →₀ S) →ₗ[S] (κ →₀ Localization.Away g) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap S _)
  let l₂ₜ : Ω[S⁄R] →ₗ[S] Ω[Localization.Away g⁄R] := map R R S (Localization.Away g)
  rw [← IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ₜ l₂ₜ] at h
  let eₜ : (κ →₀ Localization.Away g) →ₗ[Localization.Away g]
      Ω[Localization.Away g⁄R] :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers g) l₁ₜ l₂ₜ (Localization.Away g) e
  refine ⟨g, hg, κ, inferInstance, a, .ofRepr (LinearEquiv.ofBijective eₜ h).symm, ?_⟩
  intro i
  change eₜ (Finsupp.single i 1) = _
  trans IsLocalizedModule.map (Submonoid.powers g) l₁ₜ l₂ₜ e (l₁ₜ (Finsupp.single i 1))
  · simp [eₜ, -IsLocalizedModule.map_apply, l₁ₜ]
  · simp [l₂ₜ, e]

theorem coordinate_map_etale [Algebra.Smooth R S] [Finite ι]
    (v : ι → S) (b : Module.Basis ι S Ω[S⁄R])
    (hb : ∀ i, b i = D R S (v i)) :
    (MvPolynomial.aeval (R := R) v).toRingHom.Etale := by
  let φ := MvPolynomial.aeval (R := R) v
  let : Algebra (MvPolynomial ι R) S := φ.toRingHom.toAlgebra
  let : IsScalarTower R (MvPolynomial ι R) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FinitePresentation (MvPolynomial ι R) S :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ S
  let : Algebra.FormallyEtale (MvPolynomial ι R) S :=
    formallyEtale_polynomial_of_basis b (by
      intro i
      change b i = D R S (φ (MvPolynomial.X i))
      simpa only [φ, MvPolynomial.aeval_X] using hb i)
  change Algebra.Etale (MvPolynomial ι R) S
  constructor <;> infer_instance

theorem exists_local_etale_from_spanning (n : ℕ)
    [IsDomain S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (v : ι → S)
    (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤)
    (p : Ideal S) [p.IsPrime] :
    ∃ (g : S), g ∉ p ∧ ∃ (κ : Type w) (_ : Finite κ) (a : κ → ι),
      Nat.card κ = n ∧
      (MvPolynomial.aeval (R := R)
        (fun i => algebraMap S (Localization.Away g) (v (a i)))).toRingHom.Etale := by
  let : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  obtain ⟨g, hg, κ, hκ, a, b, hb⟩ := exists_local_differential_basis v hv p
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  have hg0 : g ≠ 0 := fun h => hg (h ▸ Ideal.zero_mem p)
  let : IsDomain (Localization.Away g) := Localization.Away.isDomain hg0
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 S (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away g
  let : Algebra.IsStandardSmoothOfRelativeDimension n R (Localization.Away g) := by
    simpa using (Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := S)
      (T := Localization.Away g) (n := n) (m := 0))
  let : Algebra.IsStandardSmooth R (Localization.Away g) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  refine ⟨g, hg, κ, hκ, a, ?_, coordinate_map_etale _ b hb⟩
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := R) (S := Localization.Away g) n
  rw [rank_eq_card_basis b] at hr
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hr

end

noncomputable section
open KaehlerDifferential TensorProduct
variable {R S T ι : Type*} [CommRing R] [CommRing S] [CommRing T]
 [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma differentials_span_of_formallyEtale [Algebra.FormallyEtale S T]
    (v : ι → S) (hv : Submodule.span S (Set.range (fun i => D R S (v i))) = ⊤) :
    Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i)))) = ⊤ := by
  let M := Submodule.span T (Set.range (fun i => D R T (algebraMap S T (v i))))
  have hmem (s : Ω[S⁄R]) : map R R S T s ∈ M := by
    have hh : Submodule.span S (Set.range (fun i => D R S (v i))) ≤
        (M.restrictScalars S).comap (map R R S T) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change map R R S T (D R S (v i)) ∈ M
      rw [map_D]
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [hv] at hh
    exact hh (Submodule.mem_top)
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨z, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale R S T).surjective x
  induction z using OAI.tensorInductionOn with
  | tmul t s =>
      rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
      exact M.smul_mem t (hmem s)
  | add x y hx hy =>
      rw [map_add]
      exact M.add_mem hx hy

end
end MaximalSeshadri.AlgebraicJets


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_EtaleJetCharts
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
open scoped Topology ContDiff
open MvPolynomial MaximalSeshadri.AnalyticCoordinates
variable {ι σ S : Type*} [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra ℂ S]

omit [DecidableEq ι] [DecidableEq σ] in
lemma presentation_binary_formallyEtale
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : ((Set.range P.map)ᶜ : Set ι) ≃ Fin 2) :
    (MvPolynomial.aeval (R := ℂ) (fun i : Fin 2 => P.val (e.symm i))).toRingHom.FormallyEtale := by
  let φ := MvPolynomial.aeval (R := ℂ) (fun i : Fin 2 => P.val (e.symm i))
  let : Algebra (MvPolynomial (Fin 2) ℂ) S := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let := P.isStandardSmooth
  change Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S
  apply formallyEtale_polynomial_of_basis (P.basisKaehler.reindex e)
  intro i
  rw [Module.Basis.reindex_apply, P.basisKaehler_apply]
  change KaehlerDifferential.D ℂ S (P.val (e.symm i)) =
    KaehlerDifferential.D ℂ S (φ (MvPolynomial.X i))
  simp only [φ, MvPolynomial.aeval_X]

theorem presentation_analytic_realization [IsDomain S]
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : ((Set.range P.map)ᶜ : Set ι) ≃ Fin 2) (ρ : S →ₐ[ℂ] ℂ) :
    ∃ (q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ))
      (hq : ∀ s, AnalyticAt ℂ (fun z => q z s) 0),
      q 0 = ρ ∧ Function.Injective (analyticTaylor q hq) ∧
      (∀ n : ℕ, 0 < n → RingHom.ker ((formalTrunc n).comp (analyticTaylor q hq)) =
        (RingHom.ker ρ)^n) ∧
      ∃ U : Set (ℂ × ℂ), IsOpen U ∧ 0 ∈ U ∧ Set.InjOn q U := by
  classical
  let φ := MvPolynomial.aeval (R := ℂ) (fun i : Fin 2 => P.val (e.symm i))
  let : Algebra (MvPolynomial (Fin 2) ℂ) S := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) S :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : Algebra.FormallyEtale (MvPolynomial (Fin 2) ℂ) S :=
    presentation_binary_formallyEtale P e
  let := P.isStandardSmooth
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  let : Algebra.FiniteType (MvPolynomial (Fin 2) ℂ) S :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  obtain ⟨q, hq₀, hq, hc⟩ := exists_binary_point_chart P e ρ
  have hcoords : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) =
      q 0 (algebraMap (MvPolynomial (Fin 2) ℂ) S (MvPolynomial.X i)) +
        (if i = 0 then z.2 else z.1) := by
    filter_upwards [hc] with z hz
    intro i
    change q z (φ (X i)) = q 0 (φ (X i)) + _
    simpa only [φ, MvPolynomial.aeval_X, hq₀] using hz i
  refine ⟨q, hq, hq₀, analyticTaylor_injective q hq hcoords, ?_, ?_⟩
  · intro n hn
    simpa only [hq₀] using analyticTaylor_detects_ideal_power q hq hcoords n hn
  · obtain ⟨U, hU, hopen, hzero⟩ := eventually_nhds_iff.mp hc
    refine ⟨U, hopen, hzero, ?_⟩
    intro z hz w hw heq
    have hx := congrArg (fun f : S →ₐ[ℂ] ℂ => f (P.val (e.symm 1))) heq
    have hy := congrArg (fun f : S →ₐ[ℂ] ℂ => f (P.val (e.symm 0))) heq
    rw [hU z hz 1, hU w hw 1] at hx
    rw [hU z hz 0, hU w hw 0] at hy
    apply Prod.ext
    · simpa using hx
    · simpa using hy

end
end MaximalSeshadri.AlgebraicJets

end


end
end

end OAI
end

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

lemma spec_openScalars (g : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (openScalars g U.1)) = U.2.fromSpec ≫ g := by
  rw [openScalars, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    CommRingCat.ofHom_hom]
  rw [← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) U.2 _

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
-- module Solutions.Q223_SES.Seshadri_Projective_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.Projective

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
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCoefficientOrder
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_IdealEquation
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.LineBundle.finitePresentation _root_.OAI.MaximalSeshadri.Geometry.LineBundle.localGenerators_locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.locallyFree _root_.OAI.MaximalSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_CartierResidual
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

end MaximalSeshadri.AlgebraicJets

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ProjectiveCoordinates
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
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma affine_restriction_etale (U V : X.affineOpens) (e : U.1 ≤ V.1) :
    (X.presheaf.map (homOfLE e).op).hom.Etale := by
  have hU : IsAffineOpen U.1 := U.2
  have hV : IsAffineOpen V.1 := V.2
  have he := hV.map_fromSpec hU (homOfLE e).op
  have : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op) ≫ hV.fromSpec) := by
    rw [he]
    infer_instance
  let : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE e).op)) :=
    IsOpenImmersion.of_comp _ hV.fromSpec
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance

lemma awayToSection_awayι (i : σ) :
    Spec.map (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
      (Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)).fromSpec := by
  let hV := Proj.isAffineOpen_basicOpen (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  rw [← cancel_epi hV.isoSpec.hom, ← Category.assoc, hV.isoSpec_hom]
  change Proj.basicOpenToSpec _ _ ≫ _ = _
  rw [← Proj.basicOpenIsoSpec_hom _ _ (poly_X_mem i) (by decide),
    Proj.awayι, Iso.hom_inv_id_assoc]
  exact hV.toSpecΓ_fromSpec.symm

theorem closed_projective_affine_surjective (h : X ⟶ Proj (PolyGrade K σ))
    [IsClosedImmersion h] (i : σ) :
    ∃ (U : X.affineOpens) (φ : PolyChart (R := K) i →+* Γ(X, U.1)),
      U.1 = h ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ∧
      Function.Surjective φ ∧
      Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
          U.2.fromSpec ≫ h := by
  let V := Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)
  have hV : IsAffineOpen V := Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)
  let U : X.affineOpens := ⟨h ⁻¹ᵁ V, hV.preimage h⟩
  let e := Proj.basicOpenIsoAway (PolyGrade K σ) _ (poly_X_mem i) (by decide)
  let φ : PolyChart (R := K) i →+* Γ(X, U.1) := (h.app V).hom.comp e.hom.hom
  refine ⟨U, φ, rfl, ?_, ?_⟩
  · exact (h.app_surjective V hV).comp (ConcreteCategory.bijective_of_isIso e.hom).surjective
  · change Spec.map (e.hom ≫ h.app V) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    have he : e.hom = Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) := rfl
    rw [he, awayToSection_awayι]
    rw [Scheme.Hom.app_eq_appLE]
    exact hV.SpecMap_appLE_fromSpec h U.2 le_rfl

open KaehlerDifferential MaximalSeshadri.AlgebraicJets

lemma differentials_span_projective_chart {A : Type} [CommRing A] [Algebra K A]
    (i : σ) (φ : PolyChart (R := K) i →+* A) (hφ : Function.Surjective φ)
    (hconst : ∀ c, φ (chartConstants i c) = algebraMap K A c) :
    Submodule.span A (Set.range (fun j : ChartVariables i =>
      D K A (-φ (chartCoordinate i j.1)))) = ⊤ := by
  have he : (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))).toRingHom =
      φ.comp (polyToChart i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.aeval _ (MvPolynomial.C c) = φ (polyToChart i (MvPolynomial.C c))
      rw [MvPolynomial.aeval_C]
      simpa only [polyToChart, MvPolynomial.eval₂Hom_C] using (hconst c).symm
    · intro j
      change MvPolynomial.aeval _ (MvPolynomial.X j) = φ (polyToChart i (MvPolynomial.X j))
      rw [MvPolynomial.aeval_X, polyToChart, MvPolynomial.eval₂Hom_X']
  have hp : Function.Surjective (MvPolynomial.aeval (R := K)
      (fun j : ChartVariables i => φ (chartCoordinate i j.1))) := by
    change Function.Surjective (MvPolynomial.aeval _).toRingHom
    rw [he]
    exact hφ.comp (polynomialChartEquiv (R := K) i).symm.surjective
  have hs := differentials_span_of_generators _ hp
  have hr : Set.range (fun j : ChartVariables i => D K A (-φ (chartCoordinate i j.1))) =
      -(Set.range (fun j : ChartVariables i => D K A (φ (chartCoordinate i j.1)))) := by
    ext x
    simp only [Set.mem_range, Set.mem_neg, map_neg, neg_eq_iff_eq_neg]
  rw [hr, Submodule.span_neg]
  exact hs

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_ProjectiveRefinement
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
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma restrict_projective_factor (h : X ⟶ Proj (PolyGrade K σ))
    (U V : X.affineOpens) (e : U.1 ≤ V.1) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, V.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        V.2.fromSpec ≫ h) :
    Spec.map (CommRingCat.ofHom ((X.presheaf.map (homOfLE e).op).hom.comp φ)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ, ← Category.assoc,
    CommRingCat.ofHom_hom, V.2.map_fromSpec U.2]

lemma etale_aeval_equiv {A B ι : Type} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (v : ι → A)
    (hv : (MvPolynomial.aeval (R := K) v).toRingHom.Etale) :
    (MvPolynomial.aeval (R := K) (fun i => e (v i))).toRingHom.Etale := by
  have hh := RingHom.Etale.respectsIso.1 _ e.toRingEquiv hv
  change (e.toAlgHom.comp (MvPolynomial.aeval (R := K) v)).toRingHom.Etale at hh
  rw [MvPolynomial.comp_aeval] at hh
  exact hh

theorem exists_etale_projective_chart [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (i : σ) (W : X.Opens) (x : X) (hxW : x ∈ W)
    (hxi : h x ∈ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W ∧ C.coord = i := by
  classical
  obtain ⟨V, φ, hV, hsurj, hφ⟩ := closed_projective_affine_surjective h i
  have hxV : x ∈ V.1 := by rwa [hV]
  obtain ⟨U, hxU, hUW, hstd⟩ := exists_standard_smooth_affine_inside g 2
    (W ⊓ V.1) x ⟨hxW, hxV⟩
  have e : U.1 ≤ V.1 := hUW.trans inf_le_right
  let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  let : Algebra K Γ(X, V.1) := (openScalars g V.1).toAlgebra
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  let r : Γ(X, V.1) →+* Γ(X, U.1) := (X.presheaf.map (homOfLE e).op).hom
  let : Algebra Γ(X, V.1) Γ(X, U.1) := r.toAlgebra
  let : IsScalarTower K Γ(X, V.1) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g e).symm
  let : Algebra.Etale Γ(X, V.1) Γ(X, U.1) := affine_restriction_etale U V e
  have hconst := projective_affine_constants h g hbase V (spec_openScalars g V) i φ hφ
  have hspan := differentials_span_projective_chart i φ hsurj hconst
  have hs := differentials_span_of_formallyEtale (T := Γ(X, U.1))
    (fun j : ChartVariables i => -φ (chartCoordinate i j.1)) hspan
  let φU := r.comp φ
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 K Γ(X, U.1) := hstd
  let p : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom ⟨x, hxU⟩
  obtain ⟨f, hfp, κ, hκ, a, hcard, het⟩ := exists_local_etale_from_spanning 2
    (fun j : ChartVariables i => -φU (chartCoordinate i j.1))
    (by simpa only [φU, RingHom.comp_apply, map_neg, RingHom.algebraMap_toAlgebra] using hs) p.asIdeal
  let T : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  have hxf : x ∈ T.1 := by
    have hp : U.2.fromSpec p = x := by
      change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨x, hxU⟩ = x
      rw [U.2.isoSpec_hom_fromSpec]
      rfl
    have hm : p ∈ PrimeSpectrum.basicOpen f := hfp
    rw [← U.2.fromSpec_preimage_basicOpen f] at hm
    change U.2.fromSpec p ∈ X.basicOpen f at hm
    rwa [hp] at hm
  let r' : Γ(X, U.1) →+* Γ(X, T.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra K Γ(X, T.1) := (openScalars g T.1).toAlgebra
  let : IsScalarTower K Γ(X, U.1) Γ(X, T.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g (X.basicOpen_le f)).symm
  let : IsLocalization.Away f Γ(X, T.1) := U.2.isLocalization_basicOpen f
  let ρ := (IsLocalization.algEquiv (Submonoid.powers f)
    (Localization.Away f) Γ(X, T.1)).restrictScalars K
  have het' := etale_aeval_equiv ρ _ het
  let φT := r'.comp φU
  have hφU := restrict_projective_factor h U V e i φ hφ
  refine ⟨{ U := T
            coord := i
            nonempty := ⟨⟨x, hxf⟩⟩
            φ := φT
            factor := restrict_projective_factor h T U (X.basicOpen_le f) i φU hφU
            κ := κ
            finite := hκ
            a := a
            card := hcard
            etale := ?_ }, hxf,
      (X.basicOpen_le f).trans (hUW.trans inf_le_left), rfl⟩
  convert het' using 1
  all_goals try with_reducible_and_instances rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) =
      MvPolynomial.aeval _ (MvPolynomial.C c)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]
    rfl
  · intro k
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X k) =
      MvPolynomial.aeval _ (MvPolynomial.X k)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]
    change -r' (φU (chartCoordinate i (a k).1)) =
      ρ (algebraMap Γ(X, U.1) (Localization.Away f) (-φU (chartCoordinate i (a k).1)))
    rw [← map_neg]
    exact ((IsLocalization.algEquiv (Submonoid.powers f)
      (Localization.Away f) Γ(X, T.1)).commutes
      (-φU (chartCoordinate i (a k).1))).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Projective_FiniteAtlas
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                              

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

lemma projective_standard_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

 theorem exists_etale_projective_neighborhood [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (W : X.Opens) (x : X) (hxW : x ∈ W) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W := by
  have hx : h x ∈ ⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
    rw [projective_standard_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨C, hxC, hCW, _⟩ := exists_etale_projective_chart g h hbase i W x hxW hi
  exact ⟨C, hxC, hCW⟩

end

end MaximalSeshadri.ProjectiveBertini

end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Sheaves_EtaleLineFrame
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini MaximalSeshadri.AlgebraicJets

lemma Surface.etale_line_frame_inside (S : Surface) (J : LineBundle S.scheme)
    (W : S.scheme.Opens) (x : S.scheme) (hx : x ∈ W) :
    ∃ U : S.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ _ : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        ∃ t : Fin 2 → Γ(S.scheme,U.1),
          (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale := by
  classical
  obtain ⟨V,hV,⟨e⟩⟩ := J.locallyRankOne x
  obtain ⟨C,hxC,hC⟩ := @exists_etale_projective_neighborhood ℂ _ S.scheme
    (Fin (S.embeddingDimension + 1)) S.integral S.structureMap S.smooth
    S.embedding S.closedImmersion S.overComplex (V ⊓ W) x ⟨hV,hx⟩
  let := C.finite
  let := Fintype.ofFinite C.κ
  let eκ : Fin 2 ≃ C.κ := (Fintype.equivFinOfCardEq (by simpa only [← Nat.card_eq_fintype_card] using C.card)).symm
  let := (openScalars S.structureMap C.U.1).toAlgebra
  let a : C.κ → Γ(S.scheme,C.U.1) := fun k => -C.φ (MaximalSeshadri.Projective.chartCoordinate C.coord (C.a k).1)
  refine ⟨C.U,hxC,hC.trans inf_le_right,frameOnSmaller e C.U.1 (hC.trans inf_le_left),a ∘ eκ,?_⟩
  exact etale_aeval_reindex a C.etale eκ

end
end MaximalSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtaleRealization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets
open scoped Topology

lemma polynomial_binary_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ (MvPolynomial (Fin 2) ℂ) := by
  let b := KaehlerDifferential.mvPolynomialBasis ℂ (Fin 2)
  have : Algebra.IsStandardSmooth ℂ (MvPolynomial (Fin 2) ℂ) :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential b (by
      rintro _ ⟨i,rfl⟩
      exact ⟨X i, (KaehlerDifferential.mvPolynomialBasis_apply ℂ (Fin 2) i).symm⟩)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [rank_eq_card_basis b]
  simp

end
end MaximalSeshadri.QuadraticJets
end


end
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
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.noetherian _root_.OAI.MaximalSeshadri.Geometry.IntegralCurve.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.compact _root_.OAI.MaximalSeshadri.Geometry.Surface.locallyNoetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.noetherian _root_.OAI.MaximalSeshadri.Geometry.Surface.proper _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms
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
-- module Solutions.Q223_SES.Seshadri_Sheaves_AffineOrderRestriction
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_CurveOrderExact
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

lemma IntegralCurve.point_in_range_of_affine_ideal (S : Surface) (C : IntegralCurve S)
    (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ)
    (h : C.embedding.ker.ideal U ≤ RingHom.ker ρ) :
    (affineComplexPoint S.structureMap U ρ).left (fieldPoint ℂ) ∈ Set.range C.embedding := by
  let q : PrimeSpectrum Γ(S.scheme,U.1) := ⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩
  have hh : U.2.fromSpec q ∈ (C.embedding.ker.support : Set S.scheme) ∩ U.1 := by
    rw [C.embedding.ker.coe_support_inter U,← U.2.fromSpec_image_zeroLocus]
    exact ⟨q,h,rfl⟩
  have he : (C.embedding.ker.support : Set S.scheme) = Set.range C.embedding := by
    rw [Scheme.Hom.support_ker]
    exact C.embedding.isClosedEmbedding.isClosed_range.closure_eq
  exact he ▸ hh.1

theorem IntegralCurve.affine_ideal_not_le_next_multiplicity (S : Surface)
    (C : IntegralCurve S) (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) :
    ¬ C.embedding.ker.ideal U ≤ (RingHom.ker ρ)^
      (curveMultiplicity S C (affineComplexPoint S.structureMap U ρ)+1) := by
  classical
  let := (openScalars S.structureMap U.1).toAlgebra
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  change ¬ C.embedding.ker.ideal U ≤ (RingHom.ker ρ)^(curveMultiplicity S C p+1)
  unfold curveMultiplicity
  split_ifs with h
  · let q := h.choose
    have hq : C.embedding q = p.image := h.choose_spec
    have hpU : p.image ∈ U.1 := by
      have H := Set.mem_range_self (f := U.2.fromSpec)
        (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
      rw [U.2.range_fromSpec] at H
      exact H
    have hqu : C.embedding q ∈ U.1 := hq ▸ hpU
    let : Nonempty U.1 := ⟨⟨_,hpU⟩⟩
    let : Nonempty (C.embedding ⁻¹ᵁ U.1) := ⟨⟨q,hqu⟩⟩
    let : IsNoetherianRing Γ(S.scheme,U.1) := IsLocallyNoetherian.component_noetherian U
    let I := C.embedding.ker.ideal U
    have hI : I ≠ ⊥ := C.affine_ideal_ne_bot S U inferInstance
    have hf : {n : ℕ | ¬ I ≤ (RingHom.ker ρ)^(n+1)}.Nonempty := by
      by_contra hn
      have hn' (n : ℕ) : I ≤ (RingHom.ker ρ)^(n+1) := by
        by_contra hh
        exact hn ⟨n,hh⟩
      apply hI
      apply bot_unique
      intro a ha
      have hall : a ∈ (⨅ n : ℕ, (RingHom.ker ρ)^n) := by
        apply Ideal.mem_iInf.mpr
        intro n
        cases n with
        | zero => simp
        | succ n => exact hn' n ha
      rw [(RingHom.ker ρ).iInf_pow_eq_bot_of_isDomain (RingHom.ker_ne_top _)] at hall
      exact hall
    have he (n : ℕ) : RingHom.ker (C.embedding.stalkMap q).hom ≤
        IsLocalRing.maximalIdeal (S.scheme.presheaf.stalk (C.embedding q))^(n+1) ↔
        I ≤ (RingHom.ker ρ)^(n+1) := by
      rw [closedImmersion_stalk_kernel C.embedding U q hqu,Ideal.map_le_iff_le_comap]
      rw [affine_point_germ_power S.structureMap U ρ (C.embedding q) hqu hq.symm (n+1)]
    have horder : idealOrder (RingHom.ker (C.embedding.stalkMap q).hom) =
        sInf {n : ℕ | ¬ I ≤ (RingHom.ker ρ)^(n+1)} := by
      unfold idealOrder
      congr 1
      ext n
      exact not_congr (he n)
    rw [horder]
    exact Nat.sInf_mem hf
  · simp only [Nat.zero_add,pow_one]
    intro hi
    exact h (C.point_in_range_of_affine_ideal S U ρ hi)

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_LocalAlgebra_ExactPointOrder
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.AnalyticCoordinates

lemma formalTrunc_zero_iff_order (f : MvPowerSeries (Fin 2) ℂ) (n : ℕ) :
    formalTrunc n f = 0 ↔ (n : ℕ∞) ≤ f.order := by
  change Ideal.Quotient.mk _ (MvPowerSeries.truncTotal n f) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h
    apply MvPowerSeries.nat_le_order
    intro d hd
    simpa only [MvPowerSeries.coeff_truncTotal f hd] using h d hd
  · intro h d hd
    rw [MvPowerSeries.coeff_truncTotal f hd]
    apply MvPowerSeries.coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hd) h

lemma taylor_mem_power_iff_order {R : Type} [CommRing R] [Algebra ℂ R]
    (ρ : R →ₐ[ℂ] ℂ) (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hτ : ∀ n : ℕ, 0 < n → RingHom.ker ((formalTrunc n).comp τ) = (RingHom.ker ρ)^n)
    (a : R) (n : ℕ) : a ∈ (RingHom.ker ρ)^n ↔ (n : ℕ∞) ≤ (τ a).order := by
  by_cases hn : n = 0
  · subst n; simp
  · rw [← hτ n (Nat.pos_of_ne_zero hn)]
    change formalTrunc n (τ a) = 0 ↔ _
    exact formalTrunc_zero_iff_order _ _

lemma taylor_cancel_power {R : Type} [CommRing R] [Algebra ℂ R]
    (ρ : R →ₐ[ℂ] ℂ) (τ : R →ₐ[ℂ] MvPowerSeries (Fin 2) ℂ)
    (hτ : ∀ n : ℕ, 0 < n → RingHom.ker ((formalTrunc n).comp τ) = (RingHom.ker ρ)^n)
    (a b : R) (n m : ℕ) (ha : a ∉ (RingHom.ker ρ)^(m+1))
    (hab : a*b ∈ (RingHom.ker ρ)^n) : b ∈ (RingHom.ker ρ)^(n-m) := by
  by_contra hb
  rw [taylor_mem_power_iff_order ρ τ hτ] at ha hb hab
  have ha' := lt_of_not_ge ha
  have hb' := lt_of_not_ge hb
  have hat : (τ a).order ≠ ⊤ := ne_top_of_lt ha'
  have hbt : (τ b).order ≠ ⊤ := ne_top_of_lt hb'
  rw [← ENat.natCast_toNat hat] at ha'
  rw [← ENat.natCast_toNat hbt] at hb'
  have haN : (τ a).order.toNat < m+1 := by exact_mod_cast ha'
  have hbN : (τ b).order.toNat < n-m := by exact_mod_cast hb'
  rw [map_mul,MvPowerSeries.order_mul,← ENat.natCast_toNat hat,
    ← ENat.natCast_toNat hbt,← Nat.cast_add] at hab
  have habN : n ≤ (τ a).order.toNat+(τ b).order.toNat := by exact_mod_cast hab
  omega

theorem standard_smooth_cancel_power {R : Type} [CommRing R] [IsDomain R] [Algebra ℂ R]
    [Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ R]
    (ρ : R →ₐ[ℂ] ℂ) (a b : R) (n m : ℕ)
    (ha : a ∉ (RingHom.ker ρ)^(m+1)) (hab : a*b ∈ (RingHom.ker ρ)^n) :
    b ∈ (RingHom.ker ρ)^(n-m) := by
  classical
  obtain ⟨ι,σ,hσ,hι,P,hP⟩ := Algebra.IsStandardSmoothOfRelativeDimension.out (n := 2) (R := ℂ) (S := R)
  let := hσ
  let := hι
  let := Fintype.ofFinite σ
  let := Fintype.ofFinite ι
  let e : ((Set.range P.map)ᶜ : Set ι) ≃ Fin 2 := Fintype.equivFinOfCardEq (by
    rw [← hP]
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
      Fintype.card_compl_set, Set.card_range_of_injective P.map_inj])
  obtain ⟨q,hq,-,-,hjets,-⟩ := presentation_analytic_realization P e ρ
  exact taylor_cancel_power ρ (analyticTaylor q hq) hjets a b n m ha hab

end
end MaximalSeshadri.Geometry

end


end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Divisors_SectionCurveBound
attribute [-instance] _root_.OAI.MaximalSeshadri.Geometry.Surface.separated _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
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

lemma affineComplexPoint_mem (S : Surface) (U : S.scheme.affineOpens)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) :
    (affineComplexPoint S.structureMap U ρ).left (fieldPoint ℂ) ∈ U.1 := by
  have H := Set.mem_range_self (f := U.2.fromSpec)
    (⟨RingHom.ker ρ,RingHom.ker_isPrime _⟩ : PrimeSpectrum Γ(S.scheme,U.1))
  rwa [U.2.range_fromSpec] at H

lemma Surface.etale_cancel_power (S : Surface) (U : S.scheme.affineOpens)
    (t : Fin 2 → Γ(S.scheme,U.1))
    (het : (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ)
    (a b : Γ(S.scheme,U.1)) (n m : ℕ)
    (ha : a ∉ (RingHom.ker ρ)^(m+1)) (hab : a*b ∈ (RingHom.ker ρ)^n) :
    b ∈ (RingHom.ker ρ)^(n-m) := by
  let := (openScalars S.structureMap U.1).toAlgebra
  let : Nonempty U.1 := ⟨⟨_,affineComplexPoint_mem S U ρ⟩⟩
  let φ := MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t
  let : Algebra (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := φ.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext z
      change openScalars S.structureMap U.1 z = φ (MvPolynomial.C z)
      simp [φ])
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) Γ(S.scheme,U.1) := het
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ (MvPolynomial (Fin 2) ℂ) :=
    MaximalSeshadri.QuadraticJets.polynomial_binary_standardSmooth
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 2) ℂ)
      Γ(S.scheme,U.1) := Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ Γ(S.scheme,U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 2 0 ℂ (MvPolynomial (Fin 2) ℂ) _
  exact standard_smooth_cancel_power ρ a b n m ha hab

lemma IntegralCurve.residual_order_s01_oai (S : Surface) (C : IntegralCurve S)
    (J M : LineBundle S.scheme) (ι : J.sheaf ⟶ O S.scheme)
    (hJ : PresentsPullbackIdeal C.embedding.ker (𝟙 S.scheme) J ι)
    (s : O S.scheme ⟶ M.sheaf) (q : O S.scheme ⟶ (J.tensor M).sheaf)
    (hq : q ≫ tensorInclusion J M ι = s)
    (U : S.scheme.affineOpens) (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (ρ : letI := (openScalars S.structureMap U.1).toAlgebra;
      Γ(S.scheme,U.1) →ₐ[ℂ] ℂ) (n : ℕ)
    (ho : affineCoefficient U f s ∈ (RingHom.ker ρ)^n) :
    ∃ V : S.scheme.affineOpens,
    ∃ e : (J.tensor M).sheaf.restrict V.1.ι ≅ O V.1.toScheme,
    ∃ σ : letI := (openScalars S.structureMap V.1).toAlgebra;
      Γ(S.scheme,V.1) →ₐ[ℂ] ℂ,
      affineComplexPoint S.structureMap V σ = affineComplexPoint S.structureMap U ρ ∧
      affineCoefficient V e q ∈ (RingHom.ker σ)^
        (n-curveMultiplicity S C (affineComplexPoint S.structureMap U ρ)) := by
  let p : ComplexPoint S := affineComplexPoint S.structureMap U ρ
  obtain ⟨V,hp,hVU,e,t,het⟩ := S.etale_line_frame_inside J U.1 p.image
    (affineComplexPoint_mem S U ρ)
  obtain ⟨σ,hσ⟩ := affineComplexPoint_factor S.structureMap V p hp
  let f' := frameOnSmaller f V.1 hVU
  let g := V.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor V.1.ι).map ι ≫
    (Scheme.Modules.restrictUnitIso V.1.ι).hom))
  refine ⟨V,tensorFrame J M V.1 e f',σ,hσ,?_⟩
  apply S.etale_cancel_power V t het σ g _ n (curveMultiplicity S C p)
  · intro hg
    have hh := C.affine_ideal_not_le_next_multiplicity S V σ
    rw [hσ, InvertibleLocal.presented_frame_equation C.embedding.ker J ι hJ V e] at hh
    exact hh (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg))
  · have ho' := (affineCoefficient_order_restrict_iff S.structureMap U V hVU f f' ρ σ
      hσ.symm s n).mp ho
    apply (Ideal.mem_iff_of_associated (affineCoefficient_tensorInclusion J M ι V e f' q)).mpr
    simpa only [hq] using ho'

end
end MaximalSeshadri.Geometry

end


end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.Geometry.IntegralCurve.residual_order_s01_oai := @OAI.MaximalSeshadri.Geometry.IntegralCurve.residual_order_s01_oai

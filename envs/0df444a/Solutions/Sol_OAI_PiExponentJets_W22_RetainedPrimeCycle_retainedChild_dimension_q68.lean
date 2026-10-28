-- Prove2me | solution 1 for OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:14:20.653884+00:00
-- url     : https://prove2.me/submissions/0342355c-a608-4c11-a844-647ef2276539

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A019
import Definitions.Def_OAIQ068A027
import Theorems.Thm_OAI_PiExponentJets_W24_polynomial_prime_pair_dimension_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHilbertDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section OrderLifting

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

theorem exists_chain_lift_last (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b)
    (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton b =>
      obtain ⟨a, ha⟩ := hs b
      exact ⟨RelSeries.singleton _ a, rfl, ha⟩
  | snoc p b hb ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      obtain ⟨a, ha, hab⟩ := hu q.last b (hlast.symm ▸ hb)
      refine ⟨q.snoc a ha, ?_, ?_⟩
      · simp only [RelSeries.snoc_length, hlen]
      · simpa only [RelSeries.last_snoc] using hab

theorem krullDim_le_of_goingUp (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b) :
    Order.krullDim β ≤ Order.krullDim α := by
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, _⟩ := exists_chain_lift_last f hs hu p
  exact hlen ▸ le_iSup (fun q : LTSeries α => (q.length : WithBot ℕ∞)) q

end OrderLifting

section IntegralDimension

variable {A B : Type*} [CommRing A] [CommRing B]

theorem ringKrullDim_eq_of_integral_injective (f : A →+* B)
    (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim B = ringKrullDim A := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hi⟩
  let c : PrimeSpectrum B → PrimeSpectrum A :=
    fun p => ⟨p.asIdeal.comap f, inferInstance⟩
  have hc : StrictMono c := by
    intro p q hpq
    obtain ⟨hpq', x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp (show p.asIdeal < q.asIdeal from hpq)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hpq' ⟨hxq, hxp⟩
      (Algebra.IsIntegral.isIntegral x)
  have hs : Function.Surjective c := by
    intro p
    obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal (⊥ : Ideal B) (by
        change RingHom.ker f ≤ p.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
        exact bot_le)
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
  have hu : ∀ a b, c a < b → ∃ a', a < a' ∧ c a' = b := by
    intro a b hab
    obtain ⟨q, haq, hq, hqb⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime b.asIdeal a.asIdeal hab.le
    refine ⟨⟨q, hq⟩, lt_of_le_of_ne haq ?_, PrimeSpectrum.ext hqb⟩
    intro heq
    have he : c a = b := by
      rw [heq]
      exact PrimeSpectrum.ext hqb
    exact hab.ne he
  exact le_antisymm (Order.krullDim_le_of_strictMono c hc)
    (krullDim_le_of_goingUp c hs hu)

end IntegralDimension

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_finite_normalization_with_dimension :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim R = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨s, g, hg, hfin, ?_⟩
  have hd := ringKrullDim_eq_of_integral_injective g.toRingHom hg hfin.to_isIntegral
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard, Nat.card_fin, zero_add, WithBot.coe_natCast] using hd

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_NormalizationGrowth
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open MvPolynomial

section Substitution

variable {k σ τ : Type*} [CommSemiring k]

theorem totalDegree_aeval_le (F : τ → MvPolynomial σ k) (D : ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ D) (p : MvPolynomial τ k) :
    (aeval F p).totalDegree ≤ p.totalDegree * D := by
  classical
  have hm (d : τ →₀ ℕ) (c : k) :
      (aeval F (monomial d c)).totalDegree ≤ (d.sum fun _ e => e) * D := by
    rw [aeval_monomial, Finsupp.prod]
    calc
      (algebraMap k (MvPolynomial σ k) c *
          ∏ i ∈ d.support, F i ^ d i).totalDegree
          ≤ (∏ i ∈ d.support, F i ^ d i).totalDegree := by
            simpa only [MvPolynomial.algebraMap_eq, totalDegree_C, zero_add] using
              totalDegree_mul (C c) (∏ i ∈ d.support, F i ^ d i)
      _ ≤ ∑ i ∈ d.support, (F i ^ d i).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ d.support, d i * D :=
        Finset.sum_le_sum fun i _ =>
          (totalDegree_pow (F i) (d i)).trans (Nat.mul_le_mul_left _ (hF i))
      _ = (d.sum fun _ e => e) * D := by rw [Finsupp.sum, Finset.sum_mul]
  have he : aeval F p = ∑ d ∈ p.support, aeval F (monomial d (p.coeff d)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  exact totalDegree_finsetSum_le fun d hd =>
    (hm d (p.coeff d)).trans (Nat.mul_le_mul_right D (le_totalDegree hd))

end Substitution

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem normalization_mem_quotientDegreeFiltration {τ : Type*}
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (F : τ → MvPolynomial σ k)
    (hF : ∀ i, Ideal.Quotient.mk I (F i) = g (X i))
    (D : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D)
    (n : ℕ) (p : MvPolynomial τ k) (hp : p.totalDegree ≤ n) :
    g p ∈ quotientDegreeFiltration I (n * D) := by
  have he : (Ideal.Quotient.mkₐ k I).comp (aeval F) = g := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    exact hF i
  refine Submodule.mem_map.mpr ⟨aeval F p,
    (mem_restrictTotalDegree σ _ _).mpr
      ((totalDegree_aeval_le F D hD p).trans (Nat.mul_le_mul_right D hp)), ?_⟩
  exact AlgHom.congr_fun he p

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_FiniteNormalizationGrowth
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W29

open MvPolynomial Submodule
open scoped BigOperators

section CoefficientPieces

variable {k R τ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Fintype τ] {m : ℕ}

omit [Fintype τ] in
lemma mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R)
    (n : ℕ) (r : R) : r ∈ generatorPiece g e n ↔
      ∃ p : Fin m → MvPolynomial τ k,
        (∀ j, (p j).totalDegree ≤ n) ∧ (∑ j, g (p j) * e j) = r := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨fun j => p j, fun j => (mem_restrictTotalDegree τ _ _).mp (p j).property, rfl⟩
  · rintro ⟨p, hp, hpr⟩
    exact ⟨fun j => ⟨p j, (mem_restrictTotalDegree τ _ _).mpr (hp j)⟩, hpr⟩

omit [Fintype τ] in
lemma generatorPiece_mono (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R) :
    Monotone (generatorPiece g e) := by
  intro a b hab r hr
  obtain ⟨p, hp, hpr⟩ := (mem_generatorPiece g e a r).mp hr
  exact (mem_generatorPiece g e b r).mpr ⟨p, fun j => (hp j).trans hab, hpr⟩

lemma finrank_generatorPiece_le (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) :
    Module.finrank k (generatorPiece g e n) ≤
      m * Module.finrank k (restrictTotalDegree τ k n) := by
  calc
    Module.finrank k (generatorPiece g e n) ≤
        Module.finrank k (Fin m → restrictTotalDegree τ k n) :=
      LinearMap.finrank_range_le (boundedCoefficientMap g e n)
    _ = m * Module.finrank k (restrictTotalDegree τ k n) := by
      rw [Module.finrank_pi_fintype]
      simp

omit [Fintype τ] in
lemma mul_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R)
    (x : R) (A : Fin m → Fin m → MvPolynomial τ k) (D : ℕ)
    (hA : ∀ j, x * e j = ∑ l, g (A j l) * e l)
    (hD : ∀ j l, (A j l).totalDegree ≤ D)
    {n : ℕ} {r : R} (hr : r ∈ generatorPiece g e n) :
    x * r ∈ generatorPiece g e (n + D) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (mem_generatorPiece g e n r).mp hr
  apply (mem_generatorPiece g e (n + D) _).mpr
  refine ⟨fun l => ∑ j, p j * A j l, ?_, ?_⟩
  · intro l
    exact totalDegree_finsetSum_le fun j _ =>
      (totalDegree_mul (p j) (A j l)).trans (Nat.add_le_add (hp j) (hD j l))
  · simp only [map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∑ l, g (p j) * g (A j l) * e l) =
          g (p j) * (∑ l, g (A j l) * e l) := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = x * (g (p j) * e j) := by rw [← hA j]; ring

end CoefficientPieces

section FiniteMatrices

variable {k R σ τ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Fintype σ]

theorem finite_multiplication_matrices (g : MvPolynomial τ k →ₐ[k] R)
    (hfin : g.Finite) (x : σ → R) :
    ∃ (m D E : ℕ) (e : Fin m → R)
      (A : σ → Fin m → Fin m → MvPolynomial τ k),
      (∀ i j, x i * e j = ∑ l, g (A i j l) * e l) ∧
      (∀ i j l, (A i j l).totalDegree ≤ D) ∧
      (1 : R) ∈ generatorPiece g e E := by
  classical
  let : Algebra (MvPolynomial τ k) R := g.toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial τ k) R := hfin
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := MvPolynomial τ k) (M := R)
  have hex (r : R) : ∃ p : Fin m → MvPolynomial τ k, ∑ j, g (p j) * e j = r := by
    have hr : r ∈ Submodule.span (MvPolynomial τ k) (Set.range e) := by rw [he]; trivial
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hr
    refine ⟨p, ?_⟩
    change (∑ j, g (p j) * e j) = r at hp
    exact hp
  choose A hA using fun i j => hex (x i * e j)
  obtain ⟨p, hp⟩ := hex 1
  let D := Finset.univ.sup fun i => Finset.univ.sup fun j =>
    Finset.univ.sup fun l => (A i j l).totalDegree
  let E := Finset.univ.sup fun j => (p j).totalDegree
  refine ⟨m, D, E, e, A, fun i j => (hA i j).symm, ?_, ?_⟩
  · intro i j l
    calc
      (A i j l).totalDegree
          ≤ Finset.univ.sup (fun l => (A i j l).totalDegree) :=
            Finset.le_sup (f := fun l => (A i j l).totalDegree) (Finset.mem_univ l)
      _ ≤ Finset.univ.sup (fun j => Finset.univ.sup (fun l => (A i j l).totalDegree)) :=
            Finset.le_sup (f := fun j => Finset.univ.sup
              (fun l => (A i j l).totalDegree)) (Finset.mem_univ j)
      _ ≤ D := Finset.le_sup (f := fun i => Finset.univ.sup
          (fun j => Finset.univ.sup (fun l => (A i j l).totalDegree)))
          (Finset.mem_univ i)
  · exact (mem_generatorPiece g e E 1).mpr
      ⟨p, fun j => Finset.le_sup (f := fun j => (p j).totalDegree)
        (Finset.mem_univ j), hp⟩

end FiniteMatrices

section Propagation

variable {k R σ τ : Type*} [Field k] [CommRing R] [Algebra k R]
  {m D E : ℕ}

lemma variable_pow_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    {n : ℕ} {r : R} (hr : r ∈ generatorPiece g e n) (i : σ) (a : ℕ) :
    r * f (X i) ^ a ∈ generatorPiece g e (n + a * D) := by
  induction a with
  | zero => simpa using hr
  | succ a ih =>
    have h := mul_mem_generatorPiece g e (f (X i)) (A i) D (hA i) (hD i) ih
    have hdeg : n + (a + 1) * D = n + a * D + D := by ring
    rw [hdeg]
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

lemma monomial_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    (h1 : (1 : R) ∈ generatorPiece g e E) (a : σ →₀ ℕ) (c : k) :
    f (monomial a c) ∈ generatorPiece g e (E + (a.sum fun _ e => e) * D) := by
  classical
  induction a using Finsupp.induction with
  | zero =>
    have h := (generatorPiece g e E).smul_mem c h1
    simpa only [Finsupp.sum_zero_index, zero_mul, add_zero, ← C_apply,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.smul_def, mul_one] using h
  | single_add i a b hbi ha ih =>
    have h := variable_pow_mem_generatorPiece g e f A hA hD ih i a
    have hsum : (Finsupp.single i a + b).sum (fun _ e => e) =
        a + b.sum (fun _ e => e) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index (by rfl)]
    have hdeg : E + ((Finsupp.single i a + b).sum fun _ e => e) * D =
        E + (b.sum fun _ e => e) * D + a * D := by
      rw [hsum]
      ring
    rw [hdeg, monomial_single_add, map_mul, map_pow]
    simpa only [mul_comm] using h

lemma polynomial_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    (h1 : (1 : R) ∈ generatorPiece g e E) (p : MvPolynomial σ k) :
    f p ∈ generatorPiece g e (E + p.totalDegree * D) := by
  classical
  have he : f p = ∑ a ∈ p.support, f (monomial a (p.coeff a)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  exact generatorPiece_mono g e
    (Nat.add_le_add_left (Nat.mul_le_mul_right D (le_totalDegree ha)) E)
    (monomial_mem_generatorPiece g e f A hA hD h1 a (p.coeff a))

end Propagation

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem finite_normalization_upper_growth
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I)) (hfin : g.Finite) :
    ∃ C E : ℕ, 0 < C ∧ ∀ n : ℕ,
      Module.finrank k (W24.quotientDegreeFiltration I n) ≤
        C * Module.finrank k (restrictTotalDegree τ k (C * n + E)) := by
  classical
  let f := Ideal.Quotient.mkₐ k I
  obtain ⟨m, D, E, e, A, hA, hD, h1⟩ :=
    finite_multiplication_matrices g hfin (fun i : σ => f (X i))
  let C := max (max m D) 1
  have hmC : m ≤ C := (le_max_left m D).trans (le_max_left _ _)
  have hDC : D ≤ C := (le_max_right m D).trans (le_max_left _ _)
  refine ⟨C, E, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun n => ?_⟩
  have hle : W24.quotientDegreeFiltration I n ≤ generatorPiece g e (C * n + E) := by
    rintro r ⟨p, hp, rfl⟩
    have hpdeg := (mem_restrictTotalDegree σ n p).mp hp
    apply generatorPiece_mono g e
      (show E + p.totalDegree * D ≤ C * n + E by
        have hmul := Nat.mul_le_mul hpdeg hDC
        simpa only [Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_left hmul E)
    exact polynomial_mem_generatorPiece g e f A hA hD h1 p
  calc
    Module.finrank k (W24.quotientDegreeFiltration I n)
        ≤ Module.finrank k (generatorPiece g e (C * n + E)) :=
          Submodule.finrank_mono hle
    _ ≤ m * Module.finrank k (restrictTotalDegree τ k (C * n + E)) :=
      finrank_generatorPiece_le g e _
    _ ≤ C * Module.finrank k (restrictTotalDegree τ k (C * n + E)) :=
      Nat.mul_le_mul_right _ hmC

end PiExponentJets.W29

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CumulativeHilbertSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial DirectSum
open PiExponentJets.W24 PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

variable [Finite σ]

theorem quotientDegreeFiltration_finrank_eq_sum_fin
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j : Fin (n + 1), Module.finrank k (quotientSection I j.val) := by
  rw [← (cumulativeHomogeneousQuotientEquiv I hI n).finrank_eq,
    Module.finrank_directSum]

theorem quotientDegreeFiltration_finrank_eq_sum
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j ∈ Finset.range (n + 1), Module.finrank k (quotientSection I j) := by
  rw [quotientDegreeFiltration_finrank_eq_sum_fin I hI n]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => Module.finrank k (quotientSection I j)) (n + 1)

end PiExponentJets.W25

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHypersurfaceDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem proper_prime_cut_relative_height_eq_one
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (Q.map (Ideal.Quotient.mk P)).height = 1 := by
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hfQ : f ∈ Q :=
    (Ideal.span_singleton_le_iff_mem Q).mp (le_sup_right.trans hQ.1.2)
  have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rwa [Ideal.mk_ker])
  have hne : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h
    have hQP : Q ≤ P := by
      simpa only [Ideal.mk_ker] using
        (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk P)).mp h
    exact hfP (hQP hfQ)
  have hlo : 1 ≤ (Q.map (Ideal.Quotient.mk P)).height := by
    have hlt : (⊥ : Ideal (R ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
      bot_lt_iff_ne_bot.mpr hne
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    simpa only [Ideal.height_bot, zero_add] using h
  exact le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hQ) hlo

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHypersurfaceEquidimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

variable (k σ : Type*) [Field k] [Finite σ]

theorem minimal_prime_hypersurface_dimension
    (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (s : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ P) = ((s + 2 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial σ k ⧸ Q) = ((s + 1 : ℕ) : WithBot ℕ∞) := by
  let : Q.IsPrime := hQ.1.1
  have hd := polynomial_prime_pair_dimension_q68 k σ P Q (le_sup_left.trans hQ.1.2)
  rw [proper_prime_cut_relative_height_eq_one P Q f hfP hQ] at hd
  have he : ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
      ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
    calc
      ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
          1 + ringKrullDim (MvPolynomial σ k ⧸ Q) := add_comm _ _
      _ = ringKrullDim (MvPolynomial σ k ⧸ P) := hd
      _ = ((s + 2 : ℕ) : WithBot ℕ∞) := hdim
      _ = ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
        rw [show s + 2 = (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
  exact ENat.WithBot.add_one_cancel.mp he

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHilbertDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W27

open scoped BigOperators
open Filter Polynomial
open PiExponentJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem prime_quotientSection_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [hP : P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientSection P n) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  let x : quotientSection P n :=
    ⟨Ideal.Quotient.mk P (MvPolynomial.X i ^ n),
      Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ n,
        MvPolynomial.isHomogeneous_X_pow i n, rfl⟩⟩
  refine ⟨x, ?_⟩
  intro hx
  have hx' : Ideal.Quotient.mk P (MvPolynomial.X i ^ n) = 0 :=
    congrArg Subtype.val hx
  exact hi (hP.mem_of_pow_mem n (Ideal.Quotient.eq_zero_iff_mem.mp hx'))

theorem polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 ≤ p.eval (n : ℚ)) :
    0 ≤ p.leadingCoeff := by
  by_cases hd : p.natDegree = 0
  · have he : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hd] using Polynomial.eq_C_of_natDegree_eq_zero hd
    have hconst := hp N le_rfl
    rw [he, Polynomial.eval_C] at hconst
    exact hconst
  · by_contra hneg
    have hneg' : p.leadingCoeff < 0 := lt_of_not_ge hneg
    have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have ht : Tendsto (fun n : ℕ => p.eval (n : ℚ)) atTop atBot :=
      (p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg'.le).comp
        tendsto_natCast_atTop_atTop
    obtain ⟨n, hnN, hn⟩ := ((eventually_ge_atTop N).and
      (ht.eventually_lt_atBot 0)).exists
    exact (not_lt_of_ge (hp n hnN)) hn

theorem polynomial_leadingCoeff_pos_of_eventually_pos
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 < p.eval (n : ℚ)) :
    0 < p.leadingCoeff := by
  have hn := polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N
    (fun n hn => (hp n hn).le)
  have hp0 : p ≠ 0 := by
    intro h
    simpa [h] using hp N le_rfl
  exact lt_of_le_of_ne hn (Polynomial.leadingCoeff_ne_zero.mpr hp0).symm

end PiExponentJets.W27

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_HilbertGrowthComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open Polynomial

theorem natDegree_le_of_eventual_polynomial_le (p q : Polynomial ℚ)
    (hp : 0 < p.leadingCoeff) (N : ℕ)
    (hle : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.natDegree ≤ q.natDegree := by
  by_contra hn
  have hdeg : q.degree < p.degree := degree_lt_degree (Nat.lt_of_not_ge hn)
  have hnonneg := W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (q - p) N (fun n hn => by simpa only [eval_sub] using sub_nonneg.mpr (hle n hn))
  rw [leadingCoeff_sub_of_degree_lt' hdeg] at hnonneg
  exact (not_le_of_gt hp) (neg_nonneg.mp hnonneg)

theorem natDegree_affine_comp_le (p : Polynomial ℚ) (a b : ℚ) :
    (p.comp (C a * X + C b)).natDegree ≤ p.natDegree := by
  have ha : (C a * X + C b : Polynomial ℚ).natDegree ≤ 1 := by
    rw [natDegree_add_C]
    simpa only [natDegree_X] using natDegree_C_mul_le a (X : Polynomial ℚ)
  exact (natDegree_comp_le).trans ((Nat.mul_le_mul_left _ ha).trans_eq (Nat.mul_one _))

theorem natDegree_eq_of_polynomial_growth_bounds
    (q lower upper : Polynomial ℚ) (d : ℕ)
    (hql : 0 < q.leadingCoeff) (hll : 0 < lower.leadingCoeff)
    (hld : lower.natDegree = d) (hud : upper.natDegree ≤ d)
    (a b c e : ℚ) (N : ℕ)
    (hlo : ∀ n : ℕ, N ≤ n → lower.eval (n : ℚ) ≤ q.eval (a * n + b))
    (hup : ∀ n : ℕ, N ≤ n → q.eval (n : ℚ) ≤ upper.eval (c * n + e)) :
    q.natDegree = d := by
  have hlow : lower.natDegree ≤ (q.comp (C a * X + C b)).natDegree :=
    natDegree_le_of_eventual_polynomial_le lower _ hll N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hlo)
  have hupp : q.natDegree ≤ (upper.comp (C c * X + C e)).natDegree :=
    natDegree_le_of_eventual_polynomial_le q _ hql N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hup)
  exact le_antisymm
    (hupp.trans ((natDegree_affine_comp_le upper c e).trans hud))
    (hld ▸ hlow.trans (natDegree_affine_comp_le q a b))

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HilbertPolynomial
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem actualHP_eventually (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = (actualHP I hI).eval (n : ℚ) :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose_spec

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialCumulative
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open Polynomial Finset

theorem powerPrefixPolynomial_eval (d n : ℕ) :
    (powerPrefixPolynomial d).eval (n : ℚ) = ∑ j ∈ range n, (j : ℚ) ^ d := by
  rw [powerPrefixPolynomial, eval_mul, eval_C, eval_sub, eval_C]
  rw [← Polynomial.sum_range_pow_eq_bernoulli_sub n d]
  have hd : (d + 1 : ℚ) ≠ 0 := by positivity
  exact inv_mul_cancel_left₀ hd _

theorem powerPrefixPolynomial_degree_le (d : ℕ) :
    (powerPrefixPolynomial d).natDegree ≤ d + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hj0 : j ≠ 0 := by omega
  simp only [powerPrefixPolynomial, coeff_C_mul, coeff_sub,
    Polynomial.coeff_bernoulli, ite_eq_right (by omega : ¬j ≤ d + 1),
    coeff_C, ite_eq_right hj0, sub_zero, mul_zero]

theorem powerPrefixPolynomial_top_coefficient (d : ℕ) :
    (powerPrefixPolynomial d).coeff (d + 1) = (d + 1 : ℚ)⁻¹ := by
  simp [powerPrefixPolynomial, coeff_C_mul, Polynomial.coeff_bernoulli]

theorem polynomialPrefix_eval (p : Polynomial ℚ) (n : ℕ) :
    (polynomialPrefix p).eval (n : ℚ) = ∑ j ∈ range n, p.eval (j : ℚ) := by
  simp only [polynomialPrefix, eval_finsetSum, eval_mul, eval_C,
    powerPrefixPolynomial_eval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Polynomial.eval_eq_sum_range (p := p) (j : ℚ)).symm

theorem polynomialPrefix_degree_le (p : Polynomial ℚ) :
    (polynomialPrefix p).natDegree ≤ p.natDegree + 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans
    ((powerPrefixPolynomial_degree_le i).trans (by
      have hii := Finset.mem_range.mp hi
      omega))

theorem polynomialPrefix_top_coefficient (p : Polynomial ℚ) :
    (polynomialPrefix p).coeff (p.natDegree + 1) =
      p.leadingCoeff * (p.natDegree + 1 : ℚ)⁻¹ := by
  rw [polynomialPrefix, finsetSum_coeff]
  rw [Finset.sum_eq_single p.natDegree]
  · rw [coeff_C_mul, powerPrefixPolynomial_top_coefficient, coeff_natDegree]
  · intro i hi hne
    have hz : (powerPrefixPolynomial i).coeff (p.natDegree + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((powerPrefixPolynomial_degree_le i).trans_lt (by
        have hii := Finset.mem_range.mp hi
        omega))
    rw [coeff_C_mul, hz, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

theorem polynomialPrefix_natDegree (p : Polynomial ℚ) (hp : p ≠ 0) :
    (polynomialPrefix p).natDegree = p.natDegree + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (polynomialPrefix_degree_le p)
  rw [polynomialPrefix_top_coefficient]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (inv_ne_zero (by positivity))

theorem exists_eventual_cumulative_polynomial
    (values : ℕ → ℕ) (p : Polynomial ℚ) (hp0 : p ≠ 0) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ)) :
    ∃ q : Polynomial ℚ, q.natDegree = p.natDegree + 1 ∧
      ∀ n : ℕ, N ≤ n → q.eval (n : ℚ) =
        ((∑ j ∈ range (n + 1), values j : ℕ) : ℚ) := by
  let c : ℚ := (∑ j ∈ range N, (values j : ℚ)) - (polynomialPrefix p).eval (N : ℚ)
  let q : Polynomial ℚ := (polynomialPrefix p).comp (X + C 1) + C c
  have hsum (m : ℕ) (hm : N ≤ m) :
      (polynomialPrefix p).eval (m : ℚ) + c = ∑ j ∈ range m, (values j : ℚ) := by
    induction m, hm using Nat.le_induction with
    | base => simp [c]
    | succ m hm ih =>
        rw [polynomialPrefix_eval, Finset.sum_range_succ,
          ← polynomialPrefix_eval, hp m hm, Finset.sum_range_succ]
        linarith
  refine ⟨q, ?_, ?_⟩
  · simp only [q, natDegree_add_C, natDegree_comp, natDegree_X, mul_one,
      polynomialPrefix_natDegree p hp0]
  · intro n hn
    simpa only [q, eval_add, eval_comp, eval_X, eval_C, Nat.cast_add, Nat.cast_one,
      Nat.cast_sum] using hsum (n + 1) (by omega)

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialGrowthRanks
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponentJets.W32

theorem card_exponentBall (d n : ℕ) : (exponentBall d n).card = (n + d).choose d := by
  classical
  have hdis : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
      (fun m => (Finset.univ : Finset (Fin d)).finsuppAntidiag m) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have hi' := (Finset.mem_finsuppAntidiag'.mp hai).1
    have hj' := (Finset.mem_finsuppAntidiag'.mp haj).1
    exact hij (hi'.symm.trans hj')
  rw [exponentBall, Finset.card_biUnion hdis]
  simp_rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin]
  exact Nat.sum_range_multichoose n d

theorem finrank_restrictTotalDegree (k : Type*) [Field k] (d n : ℕ) :
    Module.finrank k (MvPolynomial.restrictTotalDegree (Fin d) k n) = (n + d).choose d := by
  classical
  have hs : {a : Fin d →₀ ℕ | a.sum (fun _ e => e) ≤ n} =
      (↑(exponentBall d n) : Set (Fin d →₀ ℕ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_exponentBall]
  change Module.finrank k (MvPolynomial.restrictSupport k
    {a : Fin d →₀ ℕ | a.sum (fun _ e => e) ≤ n}) = _
  rw [hs, ← card_exponentBall]
  let b : Module.Basis (exponentBall d n) k
      (MvPolynomial.restrictSupport k
        (↑(exponentBall d n) : Set (Fin d →₀ ℕ))) :=
    MvPolynomial.basisRestrictSupport k
      (↑(exponentBall d n) : Set (Fin d →₀ ℕ))
  exact Module.finrank_eq_card_finset_basis b

theorem polynomialGrowth_eval_finrank (k : Type*) [Field k] (d n : ℕ) :
    (polynomialGrowth d).eval (n : ℚ) =
      (Module.finrank k (MvPolynomial.restrictTotalDegree (Fin d) k n) : ℚ) := by
  rw [polynomialGrowth_eval, finrank_restrictTotalDegree]

theorem polynomialGrowth_leadingCoeff (d : ℕ) :
    (polynomialGrowth d).leadingCoeff = (d.factorial : ℚ)⁻¹ :=
  Polynomial.leadingCoeff_preHilbertPoly ℚ d 0

theorem polynomialGrowth_leadingCoeff_pos (d : ℕ) :
    0 < (polynomialGrowth d).leadingCoeff := by
  rw [polynomialGrowth_leadingCoeff]
  positivity

theorem scaledPolynomialGrowth_natDegree_le (c d : ℕ) :
    (scaledPolynomialGrowth c d).natDegree ≤ d := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans_eq (polynomialGrowth_natDegree d)

theorem scaledPolynomialGrowth_eval_finrank (k : Type*) [Field k]
    (c d n : ℕ) :
    (scaledPolynomialGrowth c d).eval (n : ℚ) =
      (c : ℚ) * (Module.finrank k
        (MvPolynomial.restrictTotalDegree (Fin d) k n) : ℚ) := by
  rw [scaledPolynomialGrowth, Polynomial.eval_C_mul, polynomialGrowth_eval_finrank k]

end PiExponentJets.W32

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHilbertComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

open MvPolynomial Polynomial Finset
open PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem normalization_binomial_lower_bound (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) (F : Fin s → MvPolynomial σ k)
    (hF : ∀ i, Ideal.Quotient.mk I (F i) = g (MvPolynomial.X i))
    (D : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) (m : ℕ) :
    (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  let L : restrictTotalDegree (Fin s) k m →ₗ[k]
      quotientDegreeFiltration I (D * m) :=
    { toFun := fun p => ⟨g p, by
        simpa only [Nat.mul_comm D m] using
          normalization_mem_quotientDegreeFiltration I g F hF D hD m p
            ((mem_restrictTotalDegree _ _ _).mp p.property)⟩
      map_add' := fun p q => Subtype.ext (g.map_add p q)
      map_smul' := fun c p => Subtype.ext (g.toLinearMap.map_smul c p) }
  rw [← W32.finrank_restrictTotalDegree k s m]
  exact LinearMap.finrank_le_finrank_of_injective (f := L)
    (fun p q h => Subtype.ext (hg (congrArg Subtype.val h)))

theorem normalization_binomial_lower_growth (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) :
    ∃ D : ℕ, 0 < D ∧ ∀ m : ℕ,
      (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  classical
  choose F hF using fun i : Fin s => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let D := max (Finset.univ.sup fun i => (F i).totalDegree) 1
  have hD : ∀ i, (F i).totalDegree ≤ D := fun i =>
    (Finset.le_sup (f := fun j : Fin s => (F j).totalDegree)
      (Finset.mem_univ i)).trans (le_max_left _ _)
  exact ⟨D, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _),
    normalization_binomial_lower_bound s I g hg F hF D hD⟩

theorem prime_quotientDegreeFiltration_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientDegreeFiltration P n) := by
  rw [W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  exact (W27.prime_quotientSection_finrank_pos P i hi 0).trans_le
    (Finset.single_le_sum (s := Finset.range (n + 1)) (a := 0)
      (f := fun j => Module.finrank k (quotientSection P j))
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem prime_hilbert_natDegree_add_one_eq_krullDim
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ)) :
    (p.natDegree + 1 : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  have hpl : 0 < p.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos p N (by
      intro n hn
      rw [hp n hn]
      exact_mod_cast W27.prime_quotientSection_finrank_pos P i hi n)
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp (ne_of_gt hpl)
  obtain ⟨q, hqd, hq⟩ := exists_eventual_cumulative_polynomial
    (fun n => Module.finrank k (quotientSection P n)) p hp0 N hp
  have hqv (n : ℕ) (hn : N ≤ n) :
      q.eval (n : ℚ) = (Module.finrank k (quotientDegreeFiltration P n) : ℚ) := by
    rw [hq n hn, W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  have hql : 0 < q.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos q N (by
      intro n hn
      rw [hqv n hn]
      exact_mod_cast prime_quotientDegreeFiltration_finrank_pos P hP i hi n)
  obtain ⟨s, g, hg, hfin, hdim⟩ :=
    exists_finite_normalization_with_dimension k (MvPolynomial σ k ⧸ P)
  obtain ⟨D, hD, hlo⟩ := normalization_binomial_lower_growth s P g hg
  obtain ⟨C, E, hC, hup⟩ := W29.finite_normalization_upper_growth P g hfin
  have hdeg : q.natDegree = s := natDegree_eq_of_polynomial_growth_bounds
      q (W32.polynomialGrowth s) (W32.scaledPolynomialGrowth C s) s
      hql (W32.polynomialGrowth_leadingCoeff_pos s)
      (W32.polynomialGrowth_natDegree s) (W32.scaledPolynomialGrowth_natDegree_le C s)
      (D : ℚ) 0 (C : ℚ) (E : ℚ) N (by
        intro n hn
        have hDn : N ≤ D * n := hn.trans (by nlinarith)
        rw [add_zero, ← Nat.cast_mul, hqv (D * n) hDn, W32.polynomialGrowth_eval]
        exact_mod_cast hlo n) (by
        intro n hn
        rw [hqv n hn, ← Nat.cast_mul, ← Nat.cast_add,
          W32.scaledPolynomialGrowth_eval_finrank k C s (C * n + E)]
        exact_mod_cast hup n)
  rw [hdim, ← hdeg, hqd]
  norm_cast

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RetainedIntersectionCycles
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

namespace ProjectiveComponent

variable {k : Type u} {σ : Type v} [Field k]

theorem coordinate_not_mem (P : ProjectiveComponent k σ) :
    MvPolynomial.X P.coordinate ∉ P.val := P.property.2.2.choose_spec

end ProjectiveComponent

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_EquidimensionalRetainedCut
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22.RetainedPrimeCycle

attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem retainedChild_dimension_q68_oai
    (C : RetainedPrimeCycle.{u,u,u} k σ) (f : MvPolynomial σ k)
    (havoid : ∀ a, f ∉ (C.component a).val) (s : ℕ)
    (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (a : C.Index)
    (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T) :
    ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ) := by
  obtain ⟨N, hN⟩ := actualHP_eventually (C.component a).val (C.component a).homogeneous
  have hPdim := W24.prime_hilbert_natDegree_add_one_eq_krullDim (C.component a).val
    (C.component a).homogeneous (C.component a).coordinate (C.component a).coordinate_not_mem
    (actualHP (C.component a).val (C.component a).homogeneous) (N+1)
    (fun n hn => (hN n (by omega)).symm)
  have hdim : ringKrullDim (MvPolynomial σ k ⧸ (C.component a).val) = (s+2 : ℕ) := by
    calc
      _ = ((actualHP (C.component a).val (C.component a).homogeneous).natDegree + 1 :
          WithBot ℕ∞) := hPdim.symm
      _ = ((s+2 : ℕ) : WithBot ℕ∞) := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (by rw [hparent a])
  exact W24.minimal_prime_hypersurface_dimension k σ (C.component a).val Q.val f
    (havoid a) (by simpa only [sup_comm] using Q.property.1) s hdim

end PiExponentJets.W22.RetainedPrimeCycle

end OAI
end

theorem solution.{u} : type_of% @OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68_oai.{u} := @OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68_oai.{u}

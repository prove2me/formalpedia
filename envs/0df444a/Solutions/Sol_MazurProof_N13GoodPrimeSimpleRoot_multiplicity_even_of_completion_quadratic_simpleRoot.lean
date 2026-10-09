-- Prove2me | solution 1 for MazurProof.N13GoodPrimeSimpleRoot.multiplicity_even_of_completion_quadratic_simpleRoot
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:56:28.316579+00:00
-- url     : https://prove2.me/submissions/0d218fcd-42be-4ac5-a00b-1e107a54fe12

import Mathlib
import Definitions.Def_MazurN13_L4

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.DedekindDomain.AdicValuation =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.DedekindDomain.AdicValuation =====
section
/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper
-/
/-!

# Adic Completions

If `A` is a valued ring with field of fractions `K` there are two different
complete rings containing `A` one might define, the first is
`𝒪_v = {x ∈ K_v | v x ≤ 1}` (defined in Lean as `adicCompletionIntegers K v`)
and the second is the `v-adic` completion of `A`. In the case when `A` is a
Dedekind domain these definitions give isomorphic topological `A`-algebras.
This file makes some progress towards this.

## Main theorems/defs

* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_integers` : The closure of
    `A` in `K_v` is `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField` : The canonical
  isomorphism `A ⧸ v ≅ 𝓞ᵥ / v`.
* `IsDedekindDomain.HeightOneSpectrum.closureAlgebraMapIntegers_eq_prodIntegers` : If `s` is
    a set of primes of `A`, then the closure of `A` in `∏_{v ∈ s} K_v` is `∏_{v ∈ s} 𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.denseRange_of_prodAlgebraMap` : If `s` is a finite set
    of primes of `A`, then `K` is dense in `∏_{v ∈ s} K_v`.
* We show (as an unnamed instance) `IsDiscreteValuationRing (𝒪[v.adicCompletion K])`
-/
section
namespace IsDedekindDomain.HeightOneSpectrum
section Multiplicative
open scoped WithZero
lemma exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨y, hnz, hyx⟩ := WithZero.exists_ne_zero_and_lt hx
  lift y to Multiplicative ℤ using hnz
  use y.natAbs
  apply lt_of_le_of_lt _ hyx
  rw [← ofAdd_toAdd y, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  change -((Multiplicative.toAdd y).natAbs : ℤ) ≤ Multiplicative.toAdd y
  omega
end Multiplicative
variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsDedekindDomain A] (v : HeightOneSpectrum A)
open scoped WithZero
-- could go in mathlib
-- shortcut instances for next def: needed after mathlib #34045
-- dirty hack because of v4.29
namespace adicCompletion
-- IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
-- shortcut instance for next theorem: needed after mathlib #34045
lemma mem_completionIdeal_pow {n : ℕ} (x : v.adicCompletionIntegers K) :
    x ∈ (v.completionIdeal K) ^ n ↔ Valued.v x.val ≤ ↑(Multiplicative.ofAdd (-(n : ℤ))) := by
  obtain ⟨π, hπ⟩ := exists_uniformizer K v
  unfold completionIdeal
  rw [maximalIdeal_eq_span_uniformizer K v hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hvalπ_pow : (Valued.v π.val) ^ n = (Multiplicative.ofAdd (-n : ℤ)) := by
    rw [hπ]
    norm_num
    norm_cast
    rw [← ofAdd_nsmul, Nat.smul_one_eq_cast]
  constructor
  · rintro ⟨a, rfl⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ofAdd_neg,
      WithZero.coe_inv]
    apply mul_le_of_le_one_of_le a.prop <| le_of_eq hvalπ_pow
  · intro hx
    set a := x.val / (π ^ n) with ha'
    have ha : Valued.v a ≤ 1 := by
      rwa [ha', Valuation.map_div, Valuation.map_pow, hvalπ_pow,
        div_le_one₀ (WithZero.zero_lt_coe _)]
    use ⟨a, ha⟩
    apply Subtype.val_injective
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, ha']
    rw [div_mul_eq_mul_div₀, mul_div_cancel_right₀]
    apply pow_ne_zero n
    norm_cast
    exact uniformizer_ne_zero hπ
end adicCompletion
end IsDedekindDomain.HeightOneSpectrum
end
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeCompletion =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeCompletion =====
section
/-!
# Completion and Hensel interfaces for the N13 good-prime argument

The denominator-prime analysis needs only two local mechanisms.

First, the integer ring inside the adic completion is complete for the
powers of its maximal ideal, hence Henselian.  Mathlib already supplies
the valued-field completion and FLT supplies the exact description of
the maximal-ideal powers; the only missing bridge is the equality
between the inherited valuation topology and the adic topology.

Second, a global integer which becomes a valuation-one factor times a
square in the completion has even multiplicity at the original height-one
prime.  This follows directly from the compatibility of the completion
valuation with the global adic valuation.

For the mixed quadratic regime we also give a non-monic Hensel interface.
It is proved structurally by replacing

`a X² + b X + c`

near an approximate root by the monic polynomial

`Y² + B Y + a C`,

where `B` is the derivative and `C` is the value at the approximate root.
No root enumeration or finite residue-field search is used.
-/
open Filter Polynomial Topology WithZero Multiplicative IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring algebraMap
namespace MazurProof.N13GoodPrimeCompletion
noncomputable section
/-- A simple approximate root of a quadratic lifts in any Henselian pair,
even when the quadratic is not monic. -/
theorem exists_quadratic_root_sub_mem_of_henselian
    {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) [HenselianRing R I]
    (a b c x₀ : R)
    (hroot : a * x₀ ^ 2 + b * x₀ + c ∈ I)
    (hderiv : IsUnit (2 * a * x₀ + b)) :
    ∃ x : R,
      a * x ^ 2 + b * x + c = 0 ∧
        x - x₀ ∈ I := by
  let B := 2 * a * x₀ + b
  let C₀ := a * x₀ ^ 2 + b * x₀ + c
  let g : R[X] :=
    X ^ 2 + Polynomial.C B * X +
      Polynomial.C (a * C₀)
  have hg_monic : g.Monic := by
    dsimp [g]
    exact
      (isMonicOfDegree_add_add_two B
        (a * C₀)).monic
  have hg_zero : g.eval 0 ∈ I := by
    simpa [g, C₀] using
      I.mul_mem_left a hroot
  have hg_deriv :
      IsUnit
        (Ideal.Quotient.mk I
          (g.derivative.eval 0)) := by
    simpa [g, B] using
      hderiv.map (Ideal.Quotient.mk I)
  obtain ⟨y, hyroot, hyI⟩ :=
    HenselianRing.is_henselian
      g hg_monic 0 hg_zero hg_deriv
  have hyI' : y ∈ I := by
    simpa using hyI
  have hyroot' :
      y ^ 2 + B * y + a * C₀ = 0 := by
    simpa [g] using hyroot
  have hBy : IsUnit (B + y) := by
    have hB : IsUnit B := by
      simpa [B] using hderiv
    rcases hB with ⟨u, hu⟩
    have hyJ :
        y ∈ Ideal.jacobson (⊥ : Ideal R) :=
      HenselianRing.jac hyI'
    have hpert :
        IsUnit (y * (↑(u⁻¹) : R) + 1) :=
      (Ideal.mem_jacobson_bot.mp hyJ) _
    have hmul := u.isUnit.mul hpert
    rw [← hu]
    have heq :
        (u : R) *
            (y * (↑(u⁻¹) : R) + 1) =
          y + (u : R) := by
      calc
        (u : R) *
              (y * (↑(u⁻¹) : R) + 1) =
            ((u : R) * (↑(u⁻¹) : R)) * y +
              (u : R) := by
                ring
        _ = y + (u : R) := by
          simp
    rw [heq] at hmul
    simpa [add_comm] using hmul
  let z := -C₀ * (B + y)⁻¹ʳ
  have hyBy :
      y * (B + y) = -(a * C₀) := by
    linear_combination hyroot'
  have haz : a * z = y := by
    calc
      a * z =
          (-(a * C₀)) * (B + y)⁻¹ʳ := by
            simp [z]
            ring
      _ =
          (y * (B + y)) *
            (B + y)⁻¹ʳ := by
              rw [hyBy]
      _ = y := by
        rw [mul_assoc,
          Ring.mul_inverse_cancel _ hBy, mul_one]
  have hzBy : z * (B + y) = -C₀ := by
    calc
      z * (B + y) =
          -C₀ * ((B + y) *
            (B + y)⁻¹ʳ) := by
              simp [z]
              ring
      _ = -C₀ := by
        rw [Ring.mul_inverse_cancel _ hBy,
          mul_one]
  refine ⟨x₀ + z, ?_, ?_⟩
  · calc
      a * (x₀ + z) ^ 2 +
            b * (x₀ + z) + c =
          z * (a * z + B) + C₀ := by
            simp [B, C₀]
            ring
      _ = z * (B + y) + C₀ := by
        rw [haz]
        ring
      _ = 0 := by
        rw [hzBy]
        ring
  · have hzI : z ∈ I :=
      I.mul_mem_right _ (I.neg_mem hroot)
    simpa using hzI
variable {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsDedekindDomain A] (v : HeightOneSpectrum A)
/-- The inherited valuation topology on the integer ring of the adic
completion is the topology defined by powers of its maximal ideal. -/
theorem completionIntegers_isAdic :
    IsAdic (v.completionIdeal K) := by
  letI :
      IsTopologicalRing
        (v.adicCompletionIntegers K) :=
    Subring.instIsTopologicalRing
      (v.adicCompletionIntegers K).toSubring
  rw [isAdic_iff]
  constructor
  · intro n
    obtain ⟨π, hπ⟩ :=
      adicCompletion.exists_uniformizer K v
    have hπ0 :
        (π : v.adicCompletion K) ≠ 0 := by
      exact_mod_cast
        adicCompletion.uniformizer_ne_zero hπ
    have hr :
        Valued.v.restrict
            ((π : v.adicCompletion K) ^ n) ≠
          0 := by
      rw [Valuation.ne_zero_iff]
      exact pow_ne_zero n hπ0
    have hvalπ_pow :
        Valued.v
            ((π : v.adicCompletion K) ^ n) =
          (↑(Multiplicative.ofAdd
            (-(n : ℤ))) : ℤᵐ⁰) := by
      rw [map_pow]
      change Valued.v π.val ^ n = _
      rw [hπ]
      norm_num
      norm_cast
      rw [← ofAdd_nsmul,
        Nat.smul_one_eq_cast]
    have hcont :
        Continuous
          (fun x : v.adicCompletionIntegers K =>
            (x : v.adicCompletion K)) :=
      continuous_subtype_val
    have hopen :=
      (Valued.isOpen_closedBall
        (v.adicCompletion K) hr).preimage hcont
    convert hopen using 1
    ext x
    simp only [Set.mem_preimage,
      Set.mem_setOf_eq]
    change
      (x ∈ (v.completionIdeal K) ^ n) ↔ _
    rw [adicCompletion.mem_completionIdeal_pow]
    rw [Valuation.restrict_le_iff, hvalπ_pow]
    rfl
  · intro s hs
    obtain ⟨u, hu, hus⟩ :=
      (mem_nhds_subtype
        (v.adicCompletionIntegers K :
          Set (v.adicCompletion K))
        (0 : v.adicCompletionIntegers K) s).mp hs
    have hu0 :
        u ∈ 𝓝 (0 : v.adicCompletion K) := by
      simpa using hu
    rw [Valued.mem_nhds_zero] at hu0
    obtain ⟨γ, hγ⟩ := hu0
    have hγ0 :
        MonoidWithZeroHom.ValueGroup₀.embedding
            γ.val ≠
          (0 : ℤᵐ⁰) := by
      intro h
      apply γ.ne_zero
      exact
        MonoidWithZeroHom.ValueGroup₀.embedding_injective
          (h.trans (map_zero _).symm)
    obtain ⟨n, hn⟩ :=
      exists_ofAdd_natCast_lt
        (x :=
          MonoidWithZeroHom.ValueGroup₀.embedding
            γ.val)
        hγ0
    refine ⟨n, fun x hx => hus (hγ ?_)⟩
    change
      Valued.v.restrict
          (x : v.adicCompletion K) <
        γ.val
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact
      (adicCompletion.mem_completionIdeal_pow
          K v x).mp hx
        |>.trans_lt hn
/-- The integer ring in the adic completion is complete for its maximal
ideal topology. -/
theorem completionIntegers_isAdicComplete :
    IsAdicComplete
      (v.completionIdeal K)
      (v.adicCompletionIntegers K) := by
  letI :
      IsUniformAddGroup
        (v.adicCompletionIntegers K) :=
    AddSubgroup.isUniformAddGroup
      (v.adicCompletionIntegers K).toSubring.toAddSubgroup
  apply (completionIntegers_isAdic v).isAdicComplete_iff.mpr
  constructor
  · exact
      @IsClosed.completeSpace_coe _ _
        (inferInstance :
          CompleteSpace (v.adicCompletion K))
        _
        (Valued.isClosed_valuationSubring _)
  · infer_instance
/-- The local integer ring attached to a height-one prime is a Henselian
pair with its maximal ideal. -/
theorem completionIntegers_henselianRing :
    HenselianRing
      (v.adicCompletionIntegers K)
      (v.completionIdeal K) := by
  letI :
      IsAdicComplete
        (v.completionIdeal K)
        (v.adicCompletionIntegers K) :=
    completionIntegers_isAdicComplete v
  infer_instance
/-- If a nonzero global integer becomes a valuation-one factor times a
square in the completion, its multiplicity at the original prime is
even. -/
theorem multiplicity_even_of_completion_eq_val_one_mul_sq
    {a : A} (ha : a ≠ 0)
    (ε z : v.adicCompletion K)
    (hε : Valued.v ε = (1 : ℤᵐ⁰))
    (h :
      (a : v.adicCompletion K) =
        ε * z ^ 2) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {a})) := by
  have hz : z ≠ 0 := by
    rintro rfl
    have hzero :
        (a : v.adicCompletion K) = 0 := by
      simpa using h
    have haC :
        (a : v.adicCompletion K) ≠ 0 := by
      intro h0
      apply ha
      apply IsFractionRing.injective A K
      apply (algebraMap K (v.adicCompletion K)).injective
      rw [map_zero, map_zero, ← IsScalarTower.algebraMap_apply]
      exact h0
    exact haC hzero
  have hvz :
      Valued.v z ≠ (0 : ℤᵐ⁰) := by
    simp [hz]
  have hva :
      Valued.v (a : v.adicCompletion K) =
        WithZero.exp
          (-(multiplicity v.asIdeal
            (Ideal.span {a}) : ℤ)) := by
    rw [v.valuedAdicCompletion_eq_valuation,
      v.valuation_of_algebraMap,
      v.intValuation_eq_exp_neg_multiplicity ha]
  have hvh := congrArg Valued.v h
  rw [map_mul, map_pow, hva, hε, one_mul] at hvh
  rw [← WithZero.exp_log hvz, pow_two,
    ← WithZero.exp_add] at hvh
  have hlog :
      -(multiplicity v.asIdeal
          (Ideal.span {a}) : ℤ) =
        WithZero.log (Valued.v z) +
          WithZero.log (Valued.v z) :=
    WithZero.exp_injective hvh
  apply (Int.even_coe_nat _).mp
  rw [← even_neg]
  exact
    ⟨WithZero.log (Valued.v z), hlog⟩
/-- Unit-times-square form of
`multiplicity_even_of_completion_eq_val_one_mul_sq`. -/
theorem multiplicity_even_of_completion_eq_unit_mul_sq
    {a : A} (ha : a ≠ 0)
    (u : (v.adicCompletionIntegers K)ˣ)
    (z : v.adicCompletion K)
    (h :
      (a : v.adicCompletion K) =
        ((u : v.adicCompletionIntegers K) :
          v.adicCompletion K) * z ^ 2) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {a})) := by
  apply
    multiplicity_even_of_completion_eq_val_one_mul_sq
      v ha
      ((u : v.adicCompletionIntegers K) :
        v.adicCompletion K)
      z
  · exact
      adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
        u.isUnit
  · exact h
end
end MazurProof.N13GoodPrimeCompletion
end

end

-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot =====
section
/-!
# The simple-root branch of the N13 denominator-prime argument

At a height-one prime away from the different, a primitive quadratic
Mumford polynomial has only two possible behaviours at the integral branch
point.  In the simple-root case, Hensel lifting gives an actual nearby root.
The value of the quadratic at the branch point is then the root difference
times a unit.  The same root difference is a square up to a unit by the
Mumford equation and the unit secant slope of the smooth sextic.

This file packages that structural argument over an arbitrary Henselian
pair.  In particular, the denominator-clearing scale is absorbed into the
square root in the fraction field; no denominator prime is enumerated.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring
namespace MazurProof.N13GoodPrimeSimpleRoot
noncomputable section
open N13GoodPrimeCompletion
/-- Elements of a Henselian ideal may be added to a unit without changing
unitness. -/
theorem isUnit_add_of_mem_henselianIdeal
    {R : Type*} [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    {u δ : R} (hu : IsUnit u) (hδ : δ ∈ I) :
    IsUnit (u + δ) := by
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  letI : IsLocalHom q :=
    isLocalHom_of_le_jacobson_bot I HenselianRing.jac
  apply IsUnit.of_map q
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hδ, add_zero]
  exact hu.map q
@[simp] theorem quadratic_eval
    {R : Type*} [CommRing R] (a b c x : R) :
    (quadratic a b c).eval x =
      a * x ^ 2 + b * x + c := by
  simp [quadratic]
/-- A simple approximate root of a quadratic lifts to a root for which the
complementary linear factor is a unit. -/
theorem exists_quadratic_root_with_unit_cofactor
    {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) [HenselianRing R I]
    (a b c x₀ : R)
    (hroot : a * x₀ ^ 2 + b * x₀ + c ∈ I)
    (hderiv : IsUnit (2 * a * x₀ + b)) :
    ∃ r : R,
      a * r ^ 2 + b * r + c = 0 ∧
      r - x₀ ∈ I ∧
      IsUnit (a * (x₀ + r) + b) ∧
      a * x₀ ^ 2 + b * x₀ + c =
        (x₀ - r) * (a * (x₀ + r) + b) := by
  obtain ⟨r, hr, hrx⟩ :=
    exists_quadratic_root_sub_mem_of_henselian
      I a b c x₀ hroot hderiv
  have hperturb :
      a * (r - x₀) ∈ I :=
    I.mul_mem_left a hrx
  have hcofactor :
      IsUnit (a * (x₀ + r) + b) := by
    have heq :
        a * (x₀ + r) + b =
          (2 * a * x₀ + b) + a * (r - x₀) := by
      ring
    rw [heq]
    exact
      isUnit_add_of_mem_henselianIdeal
        I hderiv hperturb
  refine ⟨r, hr, hrx, hcofactor, ?_⟩
  linear_combination hr
/-- Evaluation of the secant recovers the usual difference quotient
identity without division in the coefficient ring. -/
theorem eval_sub_eval_eq_sub_mul_secantAt
    {R : Type*} [CommRing R]
    (p : R[X]) (x y : R) :
    p.eval y - p.eval x =
      (y - x) * (secantAt p x).eval y := by
  have h :=
    congrArg (Polynomial.eval y)
      (Polynomial.modByMonic_add_div p (X - C x))
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X] at h
  change
    p.eval x + (y - x) * (secantAt p x).eval y =
      p.eval y at h
  rw [← h]
  ring
/-- The secant specializes to the derivative on the diagonal. -/
theorem secantAt_eval_self
    {R : Type*} [CommRing R]
    (p : R[X]) (x : R) :
    (secantAt p x).eval x =
      p.derivative.eval x := by
  have h :=
    congrArg (Polynomial.eval x)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
        p x)
  simpa [secantAt] using h
/-- Along one Henselian residue class, the secant slope of a smooth
polynomial remains a unit. -/
theorem secantAt_eval_isUnit_of_sub_mem
    {R : Type*} [CommRing R]
    (I : Ideal R) [HenselianRing R I]
    (p : R[X]) (x y : R)
    (hderiv : IsUnit (p.derivative.eval x))
    (hyx : y - x ∈ I) :
    IsUnit ((secantAt p x).eval y) := by
  obtain ⟨d, hd⟩ :=
    Polynomial.sub_dvd_eval_sub y x (secantAt p x)
  have hdiff :
      (secantAt p x).eval y -
          (secantAt p x).eval x ∈ I := by
    rw [hd]
    exact I.mul_mem_right d hyx
  have hself :
      IsUnit ((secantAt p x).eval x) := by
    rw [secantAt_eval_self]
    exact hderiv
  have heq :
      (secantAt p x).eval y =
        (secantAt p x).eval x +
          ((secantAt p x).eval y -
            (secantAt p x).eval x) := by
    ring
  rw [heq]
  exact
    isUnit_add_of_mem_henselianIdeal
      I hself hdiff
/-- Local simple-root Mumford principle.

If an integral quadratic is small at `x₀` and has unit derivative there,
then its value at `x₀` is a unit times a square in the fraction field.
The polynomial relation is allowed to contain an arbitrary nonzero
homogeneous scale.  That scale enters the square root, rather than the
unit squareclass, which is exactly what removes the artificial denominator
support. -/
theorem quadratic_eval_eq_unit_mul_sq_of_simpleRoot
    {R K : Type*}
    [CommRing R] [Nontrivial R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) [HenselianRing R I]
    (a b c x₀ scale : R)
    (F V W : R[X])
    (hscale : scale ≠ 0)
    (hsmall :
      a * x₀ ^ 2 + b * x₀ + c ∈ I)
    (hquadDeriv :
      IsUnit (2 * a * x₀ + b))
    (hFroot : F.eval x₀ = 0)
    (hFderiv :
      IsUnit (F.derivative.eval x₀))
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    ∃ u : Rˣ, ∃ z : K,
      algebraMap R K
          (a * x₀ ^ 2 + b * x₀ + c) =
        algebraMap R K (u : R) * z ^ 2 := by
  obtain ⟨r, hr, hrx, hlinear, hfactor⟩ :=
    exists_quadratic_root_with_unit_cofactor
      I a b c x₀ hsmall hquadDeriv
  let Q : R :=
    (secantAt F x₀).eval r
  have hQ : IsUnit Q := by
    exact
      secantAt_eval_isUnit_of_sub_mem
        I F x₀ r hFderiv hrx
  have hsecant :
      F.eval r =
        (r - x₀) * Q := by
    have h :=
      eval_sub_eval_eq_sub_mul_secantAt
        F x₀ r
    rw [hFroot, sub_zero] at h
    exact h
  have hrelation_r :=
    congrArg (Polynomial.eval r) hrelation
  simp only [eval_sub, eval_mul, eval_pow, eval_C,
    quadratic_eval, hr, zero_mul] at hrelation_r
  have hcurve :
      scale ^ 2 * ((r - x₀) * Q) =
        (V.eval r) ^ 2 := by
    rw [← hsecant]
    linear_combination hrelation_r
  let lUnit : Rˣ := hlinear.unit
  let qUnit : Rˣ := hQ.unit
  let u : Rˣ := -lUnit * qUnit⁻¹
  let z : K :=
    algebraMap R K (V.eval r) /
      algebraMap R K scale
  refine ⟨u, z, ?_⟩
  have hscaleK :
      algebraMap R K scale ≠ 0 :=
    by
      simpa only [map_zero] using
        (IsFractionRing.injective R K).ne hscale
  have hQK :
      algebraMap R K Q ≠ 0 :=
    (hQ.map (algebraMap R K)).ne_zero
  have hcurveK :=
    congrArg (algebraMap R K) hcurve
  simp only [map_mul, map_pow] at hcurveK
  have huQ_R :
      (u : R) * Q =
        -(a * (x₀ + r) + b) := by
    calc
      (u : R) * Q =
          ((u * qUnit : Rˣ) : R) := by
        simp only [Units.val_mul]
        dsimp only [qUnit]
        rw [hQ.unit_spec]
      _ = ((-lUnit : Rˣ) : R) := by
        rw [show u * qUnit = -lUnit by
          simp [u]]
      _ = -(a * (x₀ + r) + b) := by
        simp only [Units.val_neg]
        dsimp only [lUnit]
        rw [hlinear.unit_spec]
  have huQK :=
    congrArg (algebraMap R K) huQ_R
  simp only [map_mul, map_neg] at huQK
  rw [hfactor]
  simp only [z, map_mul]
  field_simp [hscaleK]
  calc
    algebraMap R K (x₀ - r) *
          algebraMap R K (a * (x₀ + r) + b) *
          algebraMap R K scale ^ 2 =
        -(algebraMap R K scale ^ 2 *
          algebraMap R K (r - x₀) *
          algebraMap R K (a * (x₀ + r) + b)) := by
      simp only [map_sub]
      ring
    _ =
        algebraMap R K scale ^ 2 *
          algebraMap R K (r - x₀) *
          (algebraMap R K (u : R) *
            algebraMap R K Q) := by
      rw [huQK]
      ring
    _ =
        algebraMap R K (u : R) *
          (algebraMap R K scale ^ 2 *
            (algebraMap R K (r - x₀) *
              algebraMap R K Q)) := by
      ring
    _ =
        algebraMap R K (u : R) *
          algebraMap R K (V.eval r) ^ 2 := by
      rw [hcurveK]
/-- Completion form of the simple-root principle: once the global element
is identified with the quadratic evaluation in the local integers, its
height-one multiplicity is even. -/
theorem multiplicity_even_of_completion_quadratic_simpleRoot
    {A K : Type*}
    [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [IsDedekindDomain A]
    (v : HeightOneSpectrum A)
    {global : A} (hglobal_ne : global ≠ 0)
    (a b c x₀ scale :
      v.adicCompletionIntegers K)
    (F V W :
      (v.adicCompletionIntegers K)[X])
    (hglobal :
      algebraMap A (v.adicCompletion K) global =
        ((a * x₀ ^ 2 + b * x₀ + c :
            v.adicCompletionIntegers K) :
          v.adicCompletion K))
    (hscale : scale ≠ 0)
    (hsmall :
      a * x₀ ^ 2 + b * x₀ + c ∈
        v.completionIdeal K)
    (hquadDeriv :
      IsUnit (2 * a * x₀ + b))
    (hFroot : F.eval x₀ = 0)
    (hFderiv :
      IsUnit (F.derivative.eval x₀))
    (hrelation :
      C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {global})) := by
  letI :
      HenselianRing
        (v.adicCompletionIntegers K)
        (v.completionIdeal K) :=
    completionIntegers_henselianRing v
  obtain ⟨u, z, huz⟩ :=
    quadratic_eval_eq_unit_mul_sq_of_simpleRoot
      (R := v.adicCompletionIntegers K)
      (K := v.adicCompletion K)
      (v.completionIdeal K)
      a b c x₀ scale F V W hscale
      hsmall hquadDeriv hFroot hFderiv hrelation
  apply
    multiplicity_even_of_completion_eq_unit_mul_sq
      v hglobal_ne u z
  change
    algebraMap A (v.adicCompletion K) global =
      algebraMap
          (v.adicCompletionIntegers K)
          (v.adicCompletion K) (u :
            v.adicCompletionIntegers K) *
        z ^ 2
  rw [hglobal]
  exact huz
end
end MazurProof.N13GoodPrimeSimpleRoot
end

end

theorem solution : type_of% @MazurProof.N13GoodPrimeSimpleRoot.multiplicity_even_of_completion_quadratic_simpleRoot := @MazurProof.N13GoodPrimeSimpleRoot.multiplicity_even_of_completion_quadratic_simpleRoot

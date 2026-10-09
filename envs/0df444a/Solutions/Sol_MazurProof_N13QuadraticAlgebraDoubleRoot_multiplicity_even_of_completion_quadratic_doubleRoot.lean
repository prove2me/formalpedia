-- Prove2me | solution 1 for MazurProof.N13QuadraticAlgebraDoubleRoot.multiplicity_even_of_completion_quadratic_doubleRoot
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:16:41.186147+00:00
-- url     : https://prove2.me/submissions/b4991a45-ba4d-4b49-be06-e0d947137a4f

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
end
end MazurProof.N13GoodPrimeSimpleRoot
end

end

-- ===== FLT.Assumptions.MazurProof.N13QuadraticAlgebraDoubleRoot =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13QuadraticAlgebraDoubleRoot =====
section
/-!
# The quadratic-algebra double-root principle

The leading-unit double-root branch is controlled by the rank-two algebra
cut out by the Mumford quadratic.  Its distinguished root makes the
quadratic value a norm.  At a double root, the trace and norm of the
correction term are both small, so the smooth-curve secant remains a unit.
Taking norms in the Mumford relation then writes the original quadratic
value as a unit times a square.

This argument is uniform in the prime and absorbs every nonzero
denominator-clearing scale into a fourth power.  It does not enumerate
primes, residue-field elements, or squareclasses.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
namespace MazurProof.N13QuadraticAlgebraDoubleRoot
noncomputable section
open N13GoodPrimeSimpleRoot
theorem omega_quadratic
    {R : Type*} [CommRing R]
    (B C : R) :
    (QuadraticAlgebra.omega : QA R B C) ^ 2 +
        algebraMap R (QA R B C) B *
          QuadraticAlgebra.omega +
        algebraMap R (QA R B C) C = 0 := by
  ext <;> simp [pow_two]
theorem norm_delta
    {R : Type*} [CommRing R]
    (B C x : R) :
    QuadraticAlgebra.norm (delta (B := B) (C := C) x) =
      x ^ 2 + B * x + C := by
  simp [delta, QuadraticAlgebra.norm_def]
  ring
theorem norm_algebraMap_add
    {R : Type*} [CommRing R]
    {B C : R} (r : R) (z : QA R B C) :
    QuadraticAlgebra.norm
        (algebraMap R (QA R B C) r + z) =
      r ^ 2 + r * qtrace z +
        QuadraticAlgebra.norm z := by
  simp [qtrace, QuadraticAlgebra.norm_def]
  ring
theorem qtrace_delta_mul
    {R : Type*} [CommRing R]
    (B C x : R) (z : QA R B C) :
    qtrace (delta (B := B) (C := C) x * z) =
      -(2 * x + B) * z.re +
        ((B + x) * (2 * x + B) -
          2 * (x ^ 2 + B * x + C)) * z.im := by
  simp [qtrace, delta]
  ring
theorem qtrace_delta_mul_mem
    {R : Type*} [CommRing R]
    (I : Ideal R)
    (B C x : R)
    (htrace : 2 * x + B ∈ I)
    (hnorm : x ^ 2 + B * x + C ∈ I)
    (z : QA R B C) :
    qtrace (delta (B := B) (C := C) x * z) ∈ I := by
  rw [qtrace_delta_mul]
  apply I.add_mem
  · exact I.mul_mem_right z.re (I.neg_mem htrace)
  · apply I.mul_mem_right z.im
    exact I.sub_mem
      (I.mul_mem_left (B + x) htrace)
      (I.mul_mem_left 2 hnorm)
theorem norm_delta_mul_mem
    {R : Type*} [CommRing R]
    (I : Ideal R)
    (B C x : R)
    (hnorm : x ^ 2 + B * x + C ∈ I)
    (z : QA R B C) :
    QuadraticAlgebra.norm
        (delta (B := B) (C := C) x * z) ∈ I := by
  rw [map_mul, norm_delta]
  exact I.mul_mem_right _ hnorm
theorem secant_eval_omega_isUnit
    {R : Type*} [CommRing R] [Nontrivial R]
    (I : Ideal R) [HenselianRing R I]
    (B C x : R)
    (htrace : 2 * x + B ∈ I)
    (hnorm : x ^ 2 + B * x + C ∈ I)
    (F : R[X])
    (hFderiv : IsUnit (F.derivative.eval x)) :
    IsUnit
      ((secantAt
          (F.map
            (algebraMap R (QA R B C)))
          (algebraMap R (QA R B C) x)).eval
        (QuadraticAlgebra.omega : QA R B C)) := by
  let xS : QA R B C :=
    algebraMap R (QA R B C) x
  let Q : (QA R B C)[X] :=
    secantAt
      (F.map (algebraMap R (QA R B C))) xS
  let q : QA R B C :=
    Q.eval QuadraticAlgebra.omega
  let q0 : R := F.derivative.eval x
  have hqself :
      Q.eval xS =
        algebraMap R (QA R B C) q0 := by
    dsimp only [Q, xS, q0]
    rw [secantAt_eval_self, derivative_map,
      eval_map_apply]
  obtain ⟨d, hd⟩ :=
    Polynomial.sub_dvd_eval_sub
      (QuadraticAlgebra.omega : QA R B C)
      xS Q
  have hq :
      q =
        algebraMap R (QA R B C) q0 +
          delta (B := B) (C := C) x * d := by
    dsimp only [q]
    rw [hqself] at hd
    change
      Q.eval QuadraticAlgebra.omega -
          algebraMap R (QA R B C) q0 =
        delta (B := B) (C := C) x * d at hd
    linear_combination hd
  have htraceMem :
      qtrace
          (delta (B := B) (C := C) x * d) ∈ I :=
    qtrace_delta_mul_mem I B C x
      htrace hnorm d
  have hnormMem :
      QuadraticAlgebra.norm
          (delta (B := B) (C := C) x * d) ∈ I :=
    norm_delta_mul_mem I B C x hnorm d
  have hperturb :
      q0 *
          qtrace
            (delta (B := B) (C := C) x * d) +
        QuadraticAlgebra.norm
          (delta (B := B) (C := C) x * d) ∈ I :=
    I.add_mem (I.mul_mem_left q0 htraceMem) hnormMem
  have hnormq :
      QuadraticAlgebra.norm q =
        q0 ^ 2 +
          (q0 *
              qtrace
                (delta (B := B) (C := C) x * d) +
            QuadraticAlgebra.norm
              (delta (B := B) (C := C) x * d)) := by
    rw [hq, norm_algebraMap_add]
    ring
  apply
    (QuadraticAlgebra.isUnit_iff_norm_isUnit).mpr
  rw [hnormq]
  exact
    isUnit_add_of_mem_henselianIdeal
      I (hFderiv.pow 2) hperturb
theorem monic_quadratic_eval_eq_unit_mul_sq_of_doubleRoot
    {R K : Type*}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) [HenselianRing R I]
    (B D x scale : R)
    (F V W : R[X])
    (hscale : scale ≠ 0)
    (hsmall : x ^ 2 + B * x + D ∈ I)
    (hdouble : 2 * x + B ∈ I)
    (hFroot : F.eval x = 0)
    (hFderiv : IsUnit (F.derivative.eval x))
    (hrelation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic 1 B D * W) :
    ∃ u : Rˣ, ∃ z : K,
      algebraMap R K (x ^ 2 + B * x + D) =
        algebraMap R K (u : R) * z ^ 2 := by
  let S := QA R B D
  let xS : S := algebraMap R S x
  let t : S := QuadraticAlgebra.omega
  let d : S := delta (B := B) (C := D) x
  let FS : S[X] := F.map (algebraMap R S)
  let Q : S[X] := secantAt FS xS
  let q : S := Q.eval t
  let v : S := eval₂ (algebraMap R S) t V
  have hqUnit : IsUnit q := by
    exact
      secant_eval_omega_isUnit I B D x
        hdouble hsmall F hFderiv
  have hF_t :
      eval₂ (algebraMap R S) t F = d * q := by
    have hsec :=
      eval_sub_eval_eq_sub_mul_secantAt
        FS xS t
    have hFxS :
        FS.eval xS = 0 := by
      dsimp only [FS, xS]
      rw [eval_map_apply, hFroot, map_zero]
    rw [hFxS, sub_zero] at hsec
    simpa only [FS, Q, q, d, t, xS, delta,
      eval_map] using hsec
  have hU_t :
      eval₂ (algebraMap R S) t
          (quadratic 1 B D) = 0 := by
    simp only [quadratic, eval₂_add, eval₂_mul,
      eval₂_pow, eval₂_C, eval₂_X, map_one,
      one_mul]
    change
      (QuadraticAlgebra.omega : QA R B D) ^ 2 +
          algebraMap R (QA R B D) B *
            QuadraticAlgebra.omega +
          algebraMap R (QA R B D) D = 0
    exact omega_quadratic B D
  have hrel :=
    congrArg
      (eval₂ (algebraMap R S) t)
      hrelation
  simp only [eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_C, hU_t, zero_mul] at hrel
  have hcurve :
      algebraMap R S (scale ^ 2) * (d * q) =
        v ^ 2 := by
    rw [← hF_t]
    dsimp only [v]
    linear_combination hrel
  have hnorm :=
    congrArg
      (QuadraticAlgebra.norm :
        QA R B D →* R)
      hcurve
  dsimp only [S] at hnorm
  simp only [map_mul, map_pow,
    QuadraticAlgebra.norm_algebraMap] at hnorm
  change
    (scale ^ 2) ^ 2 *
          (QuadraticAlgebra.norm d *
            QuadraticAlgebra.norm q) =
      QuadraticAlgebra.norm v ^ 2 at hnorm
  have hnormd :
      QuadraticAlgebra.norm d =
        x ^ 2 + B * x + D := by
    exact norm_delta B D x
  rw [hnormd] at hnorm
  let nqUnit : Rˣ :=
    (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp
      hqUnit).unit
  let u : Rˣ := nqUnit⁻¹
  let z : K :=
    algebraMap R K (QuadraticAlgebra.norm v) /
      algebraMap R K (scale ^ 2)
  refine ⟨u, z, ?_⟩
  have hscaleK :
      algebraMap R K (scale ^ 2) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective R K).ne
        (pow_ne_zero 2 hscale)
  have hnq :
      (nqUnit : R) = QuadraticAlgebra.norm q := by
    dsimp only [nqUnit]
    exact
      (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp
        hqUnit).unit_spec
  have hnormK :=
    congrArg (algebraMap R K) hnorm
  simp only [map_mul, map_pow] at hnormK
  change
    algebraMap R K (x ^ 2 + B * x + D) =
      algebraMap R K (u : R) *
        (algebraMap R K (QuadraticAlgebra.norm v) /
          algebraMap R K (scale ^ 2)) ^ 2
  field_simp [hscaleK]
  have hu :
      (u : R) * QuadraticAlgebra.norm q = 1 := by
    rw [← hnq]
    simp [u]
  have huK :=
    congrArg (algebraMap R K) hu
  simp only [map_mul, map_one] at huK
  rw [← hnormK]
  calc
    algebraMap R K (x ^ 2 + B * x + D) *
          algebraMap R K (scale ^ 2) ^ 2 =
        (algebraMap R K scale ^ 2) ^ 2 *
          algebraMap R K (x ^ 2 + B * x + D) := by
      simp only [map_pow]
      ring
    _ =
        (algebraMap R K scale ^ 2) ^ 2 *
          algebraMap R K (x ^ 2 + B * x + D) *
          (algebraMap R K (u : R) *
            algebraMap R K
              (QuadraticAlgebra.norm q)) := by
      rw [huK, mul_one]
    _ =
        algebraMap R K (u : R) *
          ((algebraMap R K scale ^ 2) ^ 2 *
            (algebraMap R K (x ^ 2 + B * x + D) *
              algebraMap R K
                (QuadraticAlgebra.norm q))) := by
      ring
theorem quadratic_eval_eq_unit_mul_sq_of_doubleRoot
    {R K : Type*}
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) [HenselianRing R I]
    (a b c x scale : R)
    (F V W : R[X])
    (hscale : scale ≠ 0)
    (ha : IsUnit a)
    (hsmall : a * x ^ 2 + b * x + c ∈ I)
    (hdouble : 2 * a * x + b ∈ I)
    (hFroot : F.eval x = 0)
    (hFderiv : IsUnit (F.derivative.eval x))
    (hrelation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    ∃ u : Rˣ, ∃ z : K,
      algebraMap R K (a * x ^ 2 + b * x + c) =
        algebraMap R K (u : R) * z ^ 2 := by
  let au : Rˣ := ha.unit
  let ai : R := ↑(au⁻¹)
  let B : R := ai * b
  let D : R := ai * c
  have hau : (au : R) = a := ha.unit_spec
  have hai_a : ai * a = 1 := by
    rw [← hau]
    simp [ai]
  have ha_ai : a * ai = 1 := by
    rw [← hau]
    simp [ai]
  have hmonic_eval :
      x ^ 2 + B * x + D =
        ai * (a * x ^ 2 + b * x + c) := by
    dsimp only [B, D]
    calc
      x ^ 2 + ai * b * x + ai * c =
          (ai * a) * x ^ 2 +
            ai * b * x + ai * c := by
        rw [hai_a, one_mul]
      _ = ai * (a * x ^ 2 + b * x + c) := by
        ring
  have hmonic_small :
      x ^ 2 + B * x + D ∈ I := by
    rw [hmonic_eval]
    exact I.mul_mem_left ai hsmall
  have hmonic_double :
      2 * x + B ∈ I := by
    have h :
        ai * (2 * a * x + b) ∈ I :=
      I.mul_mem_left ai hdouble
    convert h using 1
    dsimp only [B]
    calc
      2 * x + ai * b =
          (ai * a) * (2 * x) + ai * b := by
        rw [hai_a, one_mul]
      _ = ai * (2 * a * x + b) := by
        ring
  have hquadratic :
      quadratic a b c =
        quadratic 1 B D * Polynomial.C a := by
    simp only [quadratic, B, D, Polynomial.C_mul,
      Polynomial.C_1, one_mul]
    have hCai_a :
        Polynomial.C ai * Polynomial.C a = 1 := by
      rw [← Polynomial.C_mul, hai_a,
        Polynomial.C_1]
    have hbterm :
        (Polynomial.C ai * Polynomial.C b * X) *
            Polynomial.C a =
          Polynomial.C b * X := by
      calc
        (Polynomial.C ai * Polynomial.C b * X) *
              Polynomial.C a =
            (Polynomial.C ai * Polynomial.C a) *
              (Polynomial.C b * X) := by
          ring
        _ = Polynomial.C b * X := by
          rw [hCai_a, one_mul]
    have hcterm :
        (Polynomial.C ai * Polynomial.C c) *
            Polynomial.C a =
          Polynomial.C c := by
      calc
        (Polynomial.C ai * Polynomial.C c) *
              Polynomial.C a =
            (Polynomial.C ai * Polynomial.C a) *
              Polynomial.C c := by
          ring
        _ = Polynomial.C c := by
          rw [hCai_a, one_mul]
    calc
      Polynomial.C a * X ^ 2 +
            Polynomial.C b * X + Polynomial.C c =
          X ^ 2 * Polynomial.C a +
            (Polynomial.C ai * Polynomial.C b * X) *
              Polynomial.C a +
            (Polynomial.C ai * Polynomial.C c) *
              Polynomial.C a := by
        rw [hbterm, hcterm]
        ring
      _ =
          (X ^ 2 +
              Polynomial.C ai * Polynomial.C b * X +
              Polynomial.C ai * Polynomial.C c) *
            Polynomial.C a := by
        ring
  have hmonic_relation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic 1 B D *
          (Polynomial.C a * W) := by
    rw [hrelation, hquadratic]
    ring
  obtain ⟨u, z, huz⟩ :=
    monic_quadratic_eval_eq_unit_mul_sq_of_doubleRoot
      (R := R) (K := K)
      I B D x scale F V (Polynomial.C a * W)
      hscale hmonic_small hmonic_double
      hFroot hFderiv hmonic_relation
  refine ⟨au * u, z, ?_⟩
  have horiginal :
      a * x ^ 2 + b * x + c =
        a * (x ^ 2 + B * x + D) := by
    rw [hmonic_eval]
    rw [← mul_assoc, ha_ai, one_mul]
  rw [horiginal, map_mul, huz]
  simp only [Units.val_mul, map_mul, hau]
  ring
theorem multiplicity_even_of_completion_quadratic_doubleRoot
    {A K : Type*}
    [CommRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [IsDedekindDomain A]
    (v :
      IsDedekindDomain.HeightOneSpectrum A)
    {global : A} (hglobal_ne : global ≠ 0)
    (a b c x scale :
      v.adicCompletionIntegers K)
    (F V W :
      (v.adicCompletionIntegers K)[X])
    (hglobal :
      algebraMap A (v.adicCompletion K) global =
        ((a * x ^ 2 + b * x + c :
            v.adicCompletionIntegers K) :
          v.adicCompletion K))
    (hscale : scale ≠ 0)
    (ha : IsUnit a)
    (hsmall :
      a * x ^ 2 + b * x + c ∈
        v.completionIdeal K)
    (hnonsimple :
      ¬ IsUnit (2 * a * x + b))
    (hFroot : F.eval x = 0)
    (hFderiv :
      IsUnit (F.derivative.eval x))
    (hrelation :
      Polynomial.C (scale ^ 2) * F - V ^ 2 =
        quadratic a b c * W) :
    Even
      (multiplicity v.asIdeal
        (Ideal.span {global})) := by
  letI :
      HenselianRing
        (v.adicCompletionIntegers K)
        (v.completionIdeal K) :=
    N13GoodPrimeCompletion.completionIntegers_henselianRing
      v
  have hdouble :
      2 * a * x + b ∈
        v.completionIdeal K := by
    change
      2 * a * x + b ∈
        IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)
    simpa only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using hnonsimple
  obtain ⟨u, z, huz⟩ :=
    quadratic_eval_eq_unit_mul_sq_of_doubleRoot
      (R := v.adicCompletionIntegers K)
      (K := v.adicCompletion K)
      (v.completionIdeal K)
      a b c x scale F V W hscale ha hsmall
      hdouble hFroot hFderiv hrelation
  apply
    N13GoodPrimeCompletion.multiplicity_even_of_completion_eq_unit_mul_sq
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
end MazurProof.N13QuadraticAlgebraDoubleRoot
end

end

theorem solution : type_of% @MazurProof.N13QuadraticAlgebraDoubleRoot.multiplicity_even_of_completion_quadratic_doubleRoot := @MazurProof.N13QuadraticAlgebraDoubleRoot.multiplicity_even_of_completion_quadratic_doubleRoot

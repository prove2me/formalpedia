-- Prove2me | solution 1 for NumberField.Chebotarev.sum_frobeniusPrimePowerWeight
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:26:34.818919+00:00
-- url     : https://prove2.me/submissions/3a27d507-2ff5-481b-b0a1-0fca89962ec4

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Frobenius von Mangoldt coefficients

For a conjugacy class `C` in the Galois group of a finite Galois extension `L / K`, this file
defines the von Mangoldt coefficient and summatory functions restricted to `C`. A prime power
`𝔭 ^ j` belongs to the `C`-fibre when the `j`-th power of the Artin class of `𝔭` is `C`.
Consequently a prime whose Artin class is not `C` can still contribute through a higher power.

The definitions retain only unramified primes: the Artin symbol is never evaluated at a ramified
prime. The exponent-one terms form `frobeniusTheta`; all higher prime powers are dominated by the
unrestricted higher-prime-power weight from the arithmetic Dirichlet-series development, hence
their contribution is `o(x)`.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimePowerSet`: prime powers selected by the powered Artin
  class.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff`: the corresponding nonnegative arithmetic
  function, regrouped by absolute norm.
* `NumberField.Chebotarev.frobeniusPsi` and `NumberField.Chebotarev.frobeniusTheta`: the weighted
  prime-power and prime summatory functions.
* `NumberField.Chebotarev.frobeniusPrimeCount`: the number of primes of norm at most `x`
  whose arithmetic Frobenius class is `C`, with `NumberField.Chebotarev.natCast_frobeniusPrimeCount`
  identifying it with the generic count of `frobeniusPrimeSet`.

## Main results

* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff_rat_natGenerator_pow`: over `ℚ`, the
  coefficient at `p ^ (k + 1)` is the powered Frobenius weight of `𝔭 ^ (k + 1)`, the only ideal
  of that norm.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_range`: `frobeniusPsi` is the inclusive partial sum
  of `frobeniusVonMangoldtCoeff`.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_Icc`: the same sum indexed from `1`.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory`: their
  difference is exactly the contribution from exponents at least two.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_le`: that difference is bounded by
  the unrestricted higher-prime-power tail.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_isLittleO`: this difference is `o(x)`.

The coefficient convention follows Neukirch, *Algebraic Number Theory*, Chapter VII. The
construction reuses Tau Ceti's generic prime-power counting and removal estimates.
-/

 section

namespace NumberField.Chebotarev

open _root_.Filter _root_.TauCeti
open scoped _root_.Asymptotics _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- The powered-class convention follows `TauCetiRoadmap/Chebotarev/Suggested.lean`.


/-- Membership in `frobeniusPrimePowerSet`, unfolded. -/
@[simp]
theorem mem_frobeniusPrimePowerSet_iff {A : IdealPrimePower K}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    A ∈ frobeniusPrimePowerSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
          Algebra.IsUnramifiedAt (𝓞 K) Q,
        artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  Iff.rfl

/-- With an unramifiedness proof fixed, membership in the powered Frobenius fibre is the stated
equality of conjugacy classes. In particular, membership is independent of that proof. -/
theorem mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (C : ConjClasses (L ≃ₐ[K] L)) :
    A ∈ frobeniusPrimePowerSet K L C ↔
      artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hur, h⟩⟩

-- Not `@[simp]`: `mem_frobeniusPrimePowerSet_iff` together with `primePowerBase_ofPrime`,
-- `primePowerExponent_ofPrime` and `ConjClasses.pow_one` already rewrites the left-hand side.




/-- A prime power in the `C`-fibre has weight `log N(𝔭)`. -/
@[simp]
theorem frobeniusPrimePowerWeight_of_mem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∈ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = primePowerWeight A := by
  rw [frobeniusPrimePowerWeight, Set.indicator_of_mem hA]

/-- A prime power whose powered Artin class is `C` contributes its full logarithmic weight.
This exposes the power in the filter: the unpowered Artin class need not equal `C`. -/
theorem frobeniusPrimePowerWeight_of_artinSymbol_pow_eq {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) {C : ConjClasses (L ≃ₐ[K] L)}
    (hC : artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C) :
    frobeniusPrimePowerWeight K L C A = primePowerWeight A :=
  frobeniusPrimePowerWeight_of_mem
    ((mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur C).mpr hC)

/-- A prime power outside the `C`-fibre has weight zero. -/
@[simp]
theorem frobeniusPrimePowerWeight_of_notMem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∉ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = 0 :=
  Set.indicator_of_notMem hA _













































-- The powered filter is exercised here: this is the term a definition filtering on
-- `artinSymbol 𝔭 = C` alone would lose. The order-four configuration is not vacuous —
-- `ConjClasses.mk_ne_mk_of_orderOf_ne` separates the two classes for *every* element of order
-- four, its square having order two, and the cyclic group of order four realises such an element
-- concretely.




















end NumberField.Chebotarev

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Frobenius `ψ` fibres partition Chebyshev's `ψ`

Let `L / K` be a finite Galois extension of number fields with group `G`. A prime power `𝔭 ^ j`
with `𝔭` unramified in `L` lies in the powered Frobenius fibre of exactly one conjugacy class of
`G`, namely `(artinSymbol 𝔭) ^ j`, and a prime power based at a ramified prime lies in none. So the
Frobenius `ψ` functions of all conjugacy classes add up to Chebyshev's `ψ` of `K` with the ramified
primes removed:

```text
∑_C ψ_C(x) + ψ_{ramifiedPrimes K L}(x) = ψ_K(x),
```

and the correction is `O(log x)` because the ramified set is finite.

These identities supply the partition input for the weighted crossing. The later squeeze also
requires the cyclotomic weighted theorem and its consequence `ψ_K(x) / x → 1`.

## Main results

* `NumberField.Chebotarev.sum_frobeniusPrimePowerWeight`: at a single prime power, the Frobenius
  weights of all classes add up to the von Mangoldt weight if the base is unramified, and to `0`
  otherwise.
* `NumberField.Chebotarev.sum_frobeniusPsi_add_primePsi_ramifiedPrimes`: the Frobenius `ψ`
  functions and `ψ` of the ramified primes add up to `ψ_K`.
* `NumberField.Chebotarev.primePsi_univ_sub_sum_frobeniusPsi_isBigO_log`: the Frobenius `ψ`
  functions account for `ψ_K` up to `O(log x)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter XV.
-/

 section

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open _root_.Filter _root_.TauCeti
open scoped _root_.Asymptotics _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical in
variable (K L) in
/-- **The Frobenius weights partition the von Mangoldt weight.** At a prime power `𝔭 ^ j`, the
powered Frobenius weights of all conjugacy classes add up to `log N𝔭` when `𝔭` is unramified in
`L`, the only nonzero term being that of `(artinSymbol 𝔭) ^ j`, and to `0` when `𝔭` ramifies. -/
theorem solution (A : _root_.TauCeti.IdealPrimePower K) :
    ∑ C : _root_.ConjClasses (L ≃ₐ[K] L), _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight K L C A =
      {B : _root_.TauCeti.IdealPrimePower K | primePowerBase B ∉ _root_.NumberField.Chebotarev.ramifiedPrimes K L}.indicator
        _root_.TauCeti.primePowerWeight A := by
  by_cases hA : _root_.TauCeti.primePowerBase A ∈ _root_.NumberField.Chebotarev.ramifiedPrimes K L
  · rw [_root_.Set.indicator_of_notMem (by simpa using hA)]
    refine _root_.Finset.sum_eq_zero fun C _ ↦ _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem ?_
    intro h
    obtain ⟨hur, -⟩ := mem_frobeniusPrimePowerSet_iff.mp h
    exact (_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff _).mp hA hur
  · rw [_root_.Set.indicator_of_mem (by simpa using hA)]
    have hur := not_not.mp ((_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff _).not.mp hA)
    rw [_root_.Finset.sum_eq_single (_root_.NumberField.artinSymbol (_root_.TauCeti.primePowerBase A).asIdeal hur ^ _root_.TauCeti.primePowerExponent A)
      (fun C _ hC ↦ _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem
        fun h ↦ hC ((_root_.NumberField.Chebotarev.mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur C).mp h).symm)
      (fun h ↦ _root_.absurd (_root_.Finset.mem_univ _) h)]
    exact _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_artinSymbol_pow_eq hur _root_.rfl





end NumberField.Chebotarev

end
end

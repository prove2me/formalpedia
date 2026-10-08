-- Prove2me | solution 1 for MazurTransfer.rational_odd_power_of_finite_valuations
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:47:29.713827+00:00
-- url     : https://prove2.me/submissions/c8d1579e-cb34-42ef-98d7-c7a3dc6043b4

import Mathlib


/- Source module: MazurTorsion.NumberTheory.UnramifiedArtin. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The unramified ideal Artin map

This file develops the part of the ideal-theoretic Artin map that follows from
Dedekind factorization and local Frobenius theory.  For a finite Galois
extension of number fields it chooses a prime above every finite prime and
defines the corresponding arithmetic Frobenius.  In an abelian extension the
choice disappears, since Frobenius elements above the same prime are
conjugate.  The local symbols then extend uniquely to a homomorphism from the
group of nonzero fractional ideals.

The construction here is deliberately separate from global reciprocity.  The
two global assertions needed later are that principal ideals lie in the
kernel, and that the resulting Artin map is onto.  Neither assertion is used
in this file.

The divisor equivalence below is the scheme-free Dedekind-domain core of the
construction in Tau Ceti's
`AlgebraicGeometry/WeilDivisor/FractionalIdealDivisor/Basic.lean`; it is
reproved here directly from Mathlib's fractional-ideal factorization API so
this number-theory module does not depend on Picard or Weil-divisor theory.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped IsMulCommutative NumberField nonZeroDivisors Pointwise

namespace NumberTheory.UnramifiedArtin

attribute [local instance] Ideal.Quotient.field

universe u v w w'



section LocalDecompositionGroup

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [IsGaloisGroup G R S] [IsDomain R] [IsDomain S]
variable [Module.Finite R S] [Module.Flat R S]



end LocalDecompositionGroup

section Frobenius

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [IsGalois K L]











end Frobenius

section SemilinearFrobenius

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S]













end SemilinearFrobenius

section FractionalIdeals

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]



/-- The finitely supported multiplicity divisor of an invertible fractional
ideal. -/
noncomputable def fractionalIdealDivisor :
    Additive (FractionalIdeal R⁰ K)ˣ →+ (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Finsupp.ofSupportFinite
    (fun x => FractionalIdeal.count K x (Units.val (Additive.toMul I)))
    (by
      simpa only [Function.support] using Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors (Units.val (Additive.toMul I))))
  map_zero' := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.ofSupportFinite_coe]
    simp only [toMul_zero, Units.val_one, Finsupp.coe_zero, Pi.zero_apply]
    exact FractionalIdeal.count_one K x
  map_add' I J := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.add_apply, Finsupp.ofSupportFinite_coe,
      Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe]
    simp only [toMul_add, Units.val_mul]
    exact FractionalIdeal.count_mul K x (Units.ne_zero _) (Units.ne_zero _)

/-- The coefficient of the fractional-ideal divisor is Mathlib's local
multiplicity. -/
@[simp]
theorem fractionalIdealDivisor_apply
    (I : Additive (FractionalIdeal R⁰ K)ˣ) (x : HeightOneSpectrum R) :
    fractionalIdealDivisor R K I x =
      FractionalIdeal.count K x (Units.val (Additive.toMul I)) := by
  simp only [fractionalIdealDivisor, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finsupp.ofSupportFinite_coe]

/-- A nonzero fractional ideal is recovered from all of its finite-prime
multiplicities. -/
theorem fractionalIdealDivisor_injective :
    Function.Injective (fractionalIdealDivisor R K) := by
  intro I J h
  have hcount : ∀ x,
      FractionalIdeal.count K x (Units.val (Additive.toMul I)) =
        FractionalIdeal.count K x (Units.val (Additive.toMul J)) := by
    intro x
    have hx := DFunLike.congr_fun h x
    simpa using hx
  have hval : Units.val (Additive.toMul I) =
      Units.val (Additive.toMul J) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul I)),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul J))]
    exact finprod_congr fun x => by rw [hcount x]
  exact Additive.toMul.injective (Units.ext hval)

/-- The fractional ideal attached to a finitely supported integer divisor is
nonzero. -/
theorem prod_asIdeal_zpow_ne_zero (D : HeightOneSpectrum R →₀ ℤ) :
    (D.prod fun x e => (x.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun x _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot)

/-- Every finitely supported integer divisor is the divisor of a nonzero
fractional ideal. -/
theorem fractionalIdealDivisor_surjective :
    Function.Surjective (fractionalIdealDivisor R K) := by
  intro D
  refine ⟨Additive.ofMul (Units.mk0
    (D.prod fun x e => (x.asIdeal : FractionalIdeal R⁰ K) ^ e)
    (prod_asIdeal_zpow_ne_zero R K D)), ?_⟩
  apply Finsupp.ext
  intro x
  rw [fractionalIdealDivisor_apply]
  simp only [toMul_ofMul, Units.val_mk0]
  exact FractionalIdeal.count_finsuppProd K x D

/-- Nonzero fractional ideals form the free abelian group on the finite
primes of a Dedekind domain. -/
noncomputable def fractionalIdealDivisorAddEquiv :
    Additive (FractionalIdeal R⁰ K)ˣ ≃+ (HeightOneSpectrum R →₀ ℤ) :=
  AddEquiv.ofBijective (fractionalIdealDivisor R K)
    ⟨fractionalIdealDivisor_injective R K,
      fractionalIdealDivisor_surjective R K⟩

variable {R K}



variable {M : Type w} [CommGroup M]

/-- The multiplicative form of the divisor equivalence for nonzero
fractional ideals. -/
noncomputable def fractionalIdealDivisorMulEquiv :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  (fractionalIdealDivisorAddEquiv R K).toMultiplicativeRight













variable {N : Type w'} [CommGroup N]















end FractionalIdeals

section ClassGroup

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
variable {M : Type w} [CommGroup M]



















end ClassGroup

section Artin

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [IsGalois K L]





end Artin

end NumberTheory.UnramifiedArtin

end


/- Source module: MazurTorsion.NumberTheory.SelmerClassGroup. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Empty-support Selmer groups and ideal-class torsion

For a Dedekind domain `R` with fraction field `K` and a positive natural
number `n`, this file constructs the canonical homomorphism

`K⟮∅, n⟯ → ClassGroup R[n]`.

A representative has principal divisor divisible coefficientwise by `n`.
Dividing that divisor and using the free-abelian description of nonzero
fractional ideals gives an `n`-th root ideal. Its ideal class is independent
of the representative. The construction is formalized first on the preimage
of the Selmer group in `Kˣ`, then descended through actual `n`-th powers.

The kernel is proved to be exactly the image of integral units modulo
`n`-th powers, and the map onto class-group torsion is proved surjective.
Thus this file formalizes the short exact sequence

`Rˣ/(Rˣ)^n → K⟮∅, n⟯ → ClassGroup R[n] → 1`.

This is ideal-theoretic and uses no global reciprocity or class-field-theory
existence theorem. The construction is also proved natural under ring
automorphisms of `R`, acting through the induced automorphisms of `K`, the
empty-support Selmer group, and the ideal class group.
-/


open scoped nonZeroDivisors

namespace IsDedekindDomain.selmerGroup

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The exponent of a principal fractional ideal is the negative logarithm
of the normalized finite-place valuation. -/
theorem count_spanSingleton_eq_neg_valuationLog
    (a : K) (ha : a ≠ 0) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ a) =
      -WithZero.log (v.valuation K a) := by
  let x : Kˣ := Units.mk0 a ha
  let s := IsLocalization.sec R⁰ (x : K)
  have hs : IsLocalization.mk' K s.1 s.2 = x :=
    IsLocalization.mk'_sec K x
  have hI : FractionalIdeal.spanSingleton R⁰ (x : K) =
      FractionalIdeal.spanSingleton R⁰
          ((algebraMap R K) (s.2 : R))⁻¹ *
        (Ideal.span {s.1} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg
    rw [← hs, IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hcount := FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) hI
  have hval := congrArg WithZero.log
    (HeightOneSpectrum.valuationOfNeZeroToFun_eq v x)
  dsimp only [HeightOneSpectrum.valuationOfNeZeroToFun, x, s] at hval hcount ⊢
  simp only [Units.val_mk0] at hval hcount ⊢
  change
    (-((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {(IsLocalization.sec R⁰ a).1})).factors : ℤ) -
      -((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {((IsLocalization.sec R⁰ a).2 : R)})).factors : ℤ)) =
        WithZero.log (v.valuation K a) at hval
  rw [hcount]
  omega

theorem valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  erw [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply,
    ← QuotientGroup.coe_mk', QuotientGroup.map_mk']
  constructor
  · intro h
    have hq := (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.injective
      (h.trans (map_one
        (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative).symm)
    have hm := (QuotientGroup.eq_one_iff
      (v.valuationOfNeZero x)).mp hq
    change Multiplicative.toAdd (v.valuationOfNeZero x) ∈
      AddSubgroup.zmultiples (n : ℤ) at hm
    rw [AddSubgroup.mem_zmultiples_iff] at hm
    rcases hm with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [mul_comm] using hk.symm
  · rintro ⟨k, hk⟩
    have hm : Multiplicative.toAdd (v.valuationOfNeZero x) ∈
        AddSubgroup.zmultiples (n : ℤ) := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨k, by simpa [mul_comm] using hk.symm⟩
    change v.valuationOfNeZero x ∈
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) at hm
    have hq := (QuotientGroup.eq_one_iff
      (v.valuationOfNeZero x)).mpr hm
    have he := congrArg
      (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative hq
    exact he.trans (map_one
      (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative)

open NumberTheory.UnramifiedArtin

/-- The finitely supported divisor of a nonzero field element, obtained from
its principal fractional ideal. -/
noncomputable def principalDivisor :
    Kˣ →* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  (fractionalIdealDivisor R K).toMultiplicativeRight.comp
    (toPrincipalIdeal R K)

@[simp]
theorem principalDivisor_apply (x : Kˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (principalDivisor (R := R) (K := K) x) v =
      -Multiplicative.toAdd (v.valuationOfNeZero x) := by
  have hval := congrArg WithZero.log
    (HeightOneSpectrum.valuationOfNeZero_eq v x)
  change Multiplicative.toAdd (v.valuationOfNeZero x) =
    WithZero.log (v.valuation K (x : K)) at hval
  unfold principalDivisor
  change fractionalIdealDivisor R K
      (Additive.ofMul (toPrincipalIdeal R K x)) v = _
  rw [fractionalIdealDivisor_apply]
  simp only [toMul_ofMul, coe_toPrincipalIdeal]
  rw [count_spanSingleton_eq_neg_valuationLog (x : K) x.ne_zero v]
  exact congrArg Neg.neg hval.symm

/-- Representatives in `Kˣ` whose classes satisfy all empty-support
Selmer local conditions. -/
def preSelmer (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap
    (QuotientGroup.mk'
      (powMonoidHom n : Kˣ →* Kˣ).range)
    (selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n))

/-- Every coefficient of the principal divisor of a pre-Selmer
representative is divisible by `n`. -/
theorem principalDivisor_coeff_dvd (n : ℕ)
    (x : preSelmer (R := R) (K := K) n)
    (v : HeightOneSpectrum R) :
    (n : ℤ) ∣
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) v := by
  have hlocal : v.valuationOfNeZeroMod n
      (QuotientGroup.mk (x : Kˣ)) = 1 :=
    x.property v (Set.notMem_empty v)
  have hv := (valuationOfNeZeroMod_mk_eq_one_iff v n (x : Kˣ)).mp hlocal
  rw [principalDivisor_apply]
  exact dvd_neg.mpr hv

/-- Divide the principal divisor of a pre-Selmer representative
coefficientwise by `n`. -/
noncomputable def rootDivisor (n : ℕ)
    (x : preSelmer (R := R) (K := K) n) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.mapRange (fun z : ℤ => z / (n : ℤ)) (by simp)
    (Multiplicative.toAdd
      (principalDivisor (R := R) (K := K) (x : Kˣ)))

@[simp]
theorem rootDivisor_apply (n : ℕ)
    (x : preSelmer (R := R) (K := K) n)
    (v : HeightOneSpectrum R) :
    rootDivisor (R := R) (K := K) n x v =
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) v / (n : ℤ) := by
  rfl

theorem rootDivisor_one (n : ℕ) :
    rootDivisor (R := R) (K := K) n 1 = 0 := by
  ext v
  simp [rootDivisor]

theorem rootDivisor_mul (n : ℕ)
    (x y : preSelmer (R := R) (K := K) n) :
    rootDivisor (R := R) (K := K) n (x * y) =
      rootDivisor (R := R) (K := K) n x +
        rootDivisor (R := R) (K := K) n y := by
  ext v
  simp only [rootDivisor_apply, Subgroup.coe_mul, map_mul,
    toAdd_mul, Finsupp.add_apply]
  exact Int.add_ediv_of_dvd_left
    (principalDivisor_coeff_dvd (R := R) (K := K) n x v)

/-- Taking the divided divisor is a homomorphism on pre-Selmer
representatives. -/
noncomputable def rootDivisorHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun x := Multiplicative.ofAdd (rootDivisor (R := R) (K := K) n x)
  map_one' := congrArg Multiplicative.ofAdd
    (rootDivisor_one (R := R) (K := K) n)
  map_mul' x y := congrArg Multiplicative.ofAdd
    (rootDivisor_mul (R := R) (K := K) n x y)

/-- The fractional ideal whose divisor is the coefficientwise divided
principal divisor. -/
noncomputable def rootIdealHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      (FractionalIdeal R⁰ K)ˣ :=
  (fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm.toMonoidHom.comp
    (rootDivisorHom (R := R) (K := K) n)

/-- Multiplying the divided divisor by `n` recovers the original principal
divisor. -/
theorem nsmul_rootDivisor (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    n • rootDivisor (R := R) (K := K) n x =
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) := by
  ext v
  have hdvd := principalDivisor_coeff_dvd
    (R := R) (K := K) n x v
  simpa only [Finsupp.smul_apply, rootDivisor_apply, nsmul_eq_mul,
    Nat.cast_ofNat, mul_comm] using Int.ediv_mul_cancel hdvd

/-- The `n`-th power of the selected root ideal is the principal ideal of
the representative. -/
theorem rootIdealHom_pow (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    rootIdealHom (R := R) (K := K) n x ^ n =
      toPrincipalIdeal R K (x : Kˣ) := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  rw [map_pow]
  change (fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n) x))) ^ n = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (n • rootDivisor (R := R) (K := K) n x) =
    principalDivisor (R := R) (K := K) (x : Kˣ)
  rw [nsmul_rootDivisor]
  rfl

/-- On an actual `n`-th power, the selected root ideal is the expected
principal ideal. -/
theorem rootIdealHom_of_pow (n : ℕ) [NeZero n]
    (y : Kˣ)
    (hy : y ^ n ∈ preSelmer (R := R) (K := K) n) :
    rootIdealHom (R := R) (K := K) n ⟨y ^ n, hy⟩ =
      toPrincipalIdeal R K y := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  change fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n) ⟨y ^ n, hy⟩)) = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (rootDivisor (R := R) (K := K) n ⟨y ^ n, hy⟩) =
    principalDivisor (R := R) (K := K) y
  apply Multiplicative.ofAdd.injective
  ext v
  change rootDivisor (R := R) (K := K) n ⟨y ^ n, hy⟩ v =
    Multiplicative.toAdd
      (principalDivisor (R := R) (K := K) y) v
  simp only [rootDivisor_apply, map_pow,
    toAdd_pow, Finsupp.smul_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr (NeZero.ne n))

/-- The class of a principal fractional ideal is trivial. -/
@[simp]
theorem classGroup_mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 := by
  rw [ClassGroup.mk_eq_one_iff]
  exact ⟨x, by
    change ((toPrincipalIdeal R K x : FractionalIdeal R⁰ K) :
      Submodule R K) = R ∙ (x : K)
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩

/-- Map a pre-Selmer representative to the class of its divided root
ideal. -/
noncomputable def preSelmerClassHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →* ClassGroup R :=
  (ClassGroup.mk K).comp (rootIdealHom (R := R) (K := K) n)



/-- Actual `n`-th powers are pre-Selmer representatives. -/
theorem powRange_le_preSelmer (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range ≤
      preSelmer (R := R) (K := K) n := by
  rintro z ⟨y, rfl⟩
  have hq : QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range) (y ^ n) = 1 := by
    apply (QuotientGroup.eq_one_iff (y ^ n)).mpr
    exact ⟨y, rfl⟩
  change QuotientGroup.mk (y ^ n) ∈
    selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)
  rw [hq]
  exact Subgroup.one_mem _

/-- The subgroup of actual `n`-th powers inside the pre-Selmer group. -/
def preSelmerPowers (n : ℕ) :
    Subgroup (preSelmer (R := R) (K := K) n) :=
  ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf
    (preSelmer (R := R) (K := K) n)

/-- Changing a pre-Selmer representative by an actual `n`-th power does
not change the resulting ideal class. -/
theorem preSelmerPowers_le_ker (n : ℕ) [NeZero n] :
    preSelmerPowers (R := R) (K := K) n ≤
      (preSelmerClassHom (R := R) (K := K) n).ker := by
  intro z hz
  rcases hz with ⟨y, hy⟩
  have hyPre : y ^ n ∈ preSelmer (R := R) (K := K) n :=
    powRange_le_preSelmer (R := R) (K := K) n ⟨y, rfl⟩
  have hz_eq : z = (⟨y ^ n, hyPre⟩ :
      preSelmer (R := R) (K := K) n) := by
    apply Subtype.ext
    exact hy.symm
  change preSelmerClassHom (R := R) (K := K) n z = 1
  rw [hz_eq]
  change ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n ⟨y ^ n, hyPre⟩) = 1
  rw [rootIdealHom_of_pow, classGroup_mk_toPrincipalIdeal]

/-- Send a pre-Selmer representative to its class in the empty-support
Selmer group. -/
def preSelmerToSelmer (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), x.property⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

theorem preSelmerToSelmer_surjective (n : ℕ) :
    Function.Surjective (preSelmerToSelmer
      (R := R) (K := K) n) := by
  intro q
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom n : Kˣ →* Kˣ).range (q :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
  have hxPre : x ∈ preSelmer (R := R) (K := K) n := by
    change (QuotientGroup.mk'
      (powMonoidHom n : Kˣ →* Kˣ).range) x ∈
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n)
    exact hx ▸ q.property
  refine ⟨⟨x, hxPre⟩, ?_⟩
  apply Subtype.ext
  exact hx

theorem preSelmerToSelmer_ker (n : ℕ) :
    (preSelmerToSelmer (R := R) (K := K) n).ker =
      preSelmerPowers (R := R) (K := K) n := by
  ext x
  constructor
  · intro hx
    have hq : QuotientGroup.mk (x : Kˣ) = 1 :=
      congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff (x : Kˣ)).mp hq
  · intro hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (x : Kˣ)).mpr hx

/-- The quotient of pre-Selmer representatives by actual powers is the
empty-support Selmer group. -/
noncomputable def preSelmerQuotientEquiv (n : ℕ) :
    preSelmer (R := R) (K := K) n ⧸
        preSelmerPowers (R := R) (K := K) n ≃*
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) :=
  QuotientGroup.liftEquiv
    (preSelmerPowers (R := R) (K := K) n)
    (preSelmerToSelmer_surjective (R := R) (K := K) n)
    (preSelmerToSelmer_ker (R := R) (K := K) n).symm

/-- Descend the root-ideal class homomorphism across actual `n`-th
powers. -/
noncomputable def quotientClassGroupHom (n : ℕ) [NeZero n] :
    preSelmer (R := R) (K := K) n ⧸
        preSelmerPowers (R := R) (K := K) n →* ClassGroup R :=
  QuotientGroup.lift
    (preSelmerPowers (R := R) (K := K) n)
    (preSelmerClassHom (R := R) (K := K) n)
    (preSelmerPowers_le_ker (R := R) (K := K) n)

/-- The canonical homomorphism from the empty-support `n`-Selmer group to
the ideal class group. -/
noncomputable def toClassGroup (n : ℕ) [NeZero n] :
    selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) →*
      ClassGroup R :=
  (quotientClassGroupHom (R := R) (K := K) n).comp
    (preSelmerQuotientEquiv (R := R) (K := K) n).symm.toMonoidHom

/-- Formula for the class-group map on a chosen field representative. -/
theorem toClassGroup_preSelmerToSelmer (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    toClassGroup (R := R) (K := K) n
        (preSelmerToSelmer (R := R) (K := K) n x) =
      preSelmerClassHom (R := R) (K := K) n x := by
  let e := preSelmerQuotientEquiv (R := R) (K := K) n
  have he : e (QuotientGroup.mk x) =
      preSelmerToSelmer (R := R) (K := K) n x := by
    rfl
  change quotientClassGroupHom (R := R) (K := K) n
      (e.symm (preSelmerToSelmer (R := R) (K := K) n x)) = _
  rw [← he, e.symm_apply_apply]
  rfl

















@[simp]
theorem fromUnitLift_mk (n : ℕ) [Fact (0 < n)] (u : Rˣ) :
    @fromUnitLift R _ _ K _ _ _ n _
        (QuotientGroup.mk u) =
      @fromUnit R _ _ K _ _ _ n u := by
  unfold fromUnitLift
  rw [MonoidHom.comp_apply]
  change QuotientGroup.kerLift (@fromUnit R _ _ K _ _ _ n)
      ((QuotientGroup.quotientMulEquivOfEq
        (fromUnit_ker (R := R) (K := K))).symm
          (QuotientGroup.mk u)) = _
  rw [show (QuotientGroup.quotientMulEquivOfEq
      (fromUnit_ker (R := R) (K := K))).symm
        (QuotientGroup.mk u) = QuotientGroup.mk u from rfl,
    QuotientGroup.kerLift_mk]



/-- If the root-ideal class of a pre-Selmer representative is trivial,
then its Selmer class comes from an integral unit. -/
theorem preSelmerToSelmer_mem_fromUnitLift_range_of_class_eq_one
    (n : ℕ) [Fact (0 < n)] [NeZero n]
    (x : preSelmer (R := R) (K := K) n)
    (hx : preSelmerClassHom (R := R) (K := K) n x = 1) :
    preSelmerToSelmer (R := R) (K := K) n x ∈
      (@fromUnitLift R _ _ K _ _ _ n _).range := by
  have hclass : ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n x) = 1 := hx
  have hprincipal := (ClassGroup.mk_eq_one_iff).mp hclass
  obtain ⟨a, haIdeal⟩ :=
    (FractionalIdeal.isPrincipal_iff
      (rootIdealHom (R := R) (K := K) n x :
        FractionalIdeal R⁰ K)).mp hprincipal
  have ha : a ≠ 0 := by
    intro ha
    subst a
    rw [FractionalIdeal.spanSingleton_zero] at haIdeal
    exact Units.ne_zero _ haIdeal
  let y : Kˣ := Units.mk0 a ha
  have hroot : rootIdealHom (R := R) (K := K) n x =
      toPrincipalIdeal R K y := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact haIdeal
  have hpow := rootIdealHom_pow (R := R) (K := K) n x
  rw [hroot, ← map_pow] at hpow
  have hspan : FractionalIdeal.spanSingleton R⁰ ((y : K) ^ n) =
      FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) := by
    simpa only [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val] using
      congrArg Units.val hpow
  obtain ⟨u, hu⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  have hxy : (x : Kˣ) =
      Units.map (algebraMap R K : R →+* K) u * y ^ n := by
    apply Units.ext
    change ((x : Kˣ) : K) = algebraMap R K (u : R) * (y : K) ^ n
    simpa only [Units.smul_def, Algebra.smul_def] using hu.symm
  have hyn : QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range) (y ^ n) = 1 := by
    apply (QuotientGroup.eq_one_iff (y ^ n)).mpr
    exact ⟨y, rfl⟩
  have hsel : preSelmerToSelmer (R := R) (K := K) n x =
      @fromUnit R _ _ K _ _ _ n u := by
    apply Subtype.ext
    change QuotientGroup.mk (x : Kˣ) =
      QuotientGroup.mk
        (Units.map (algebraMap R K : R →+* K) u)
    rw [hxy, QuotientGroup.mk_mul, hyn]
    exact mul_one (QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range)
      (Units.map (algebraMap R K : R →+* K) u))
  refine ⟨QuotientGroup.mk u, ?_⟩
  rw [fromUnitLift_mk]
  exact hsel.symm

/-- Every element of the kernel comes from an integral unit modulo powers. -/
theorem ker_le_fromUnitLift_range (n : ℕ)
    [Fact (0 < n)] [NeZero n] :
    (toClassGroup (R := R) (K := K) n).ker ≤
      (@fromUnitLift R _ _ K _ _ _ n _).range := by
  intro q hq
  obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective
    (R := R) (K := K) n q
  apply preSelmerToSelmer_mem_fromUnitLift_range_of_class_eq_one
    (R := R) (K := K) n x
  change toClassGroup (R := R) (K := K) n
      (preSelmerToSelmer (R := R) (K := K) n x) = 1 at hq
  rwa [toClassGroup_preSelmerToSelmer] at hq














































end

end IsDedekindDomain.selmerGroup

end


/- Source module: MazurTransfer.RationalOddSelmer. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/


/-!
The empty-support rational Selmer group is trivial for every odd exponent.
This generalizes the checked fifth-power calculation in XOneElevenFiveSelmer.
The named downstream consumer is its fifth-power factor of the X₁(11)
five-isogeny descent. The local Kummer comparison and the cyclic-character
factor remain separate obligations.
-/

namespace MazurTransfer

open IsDedekindDomain IsDedekindDomain.selmerGroup

private theorem integerUnitPowerRange_eq_top (n : ℕ) (hn : Odd n) :
    (powMonoidHom n : ℤˣ →* ℤˣ).range = ⊤ := by
  apply top_unique
  intro u _
  rcases Int.units_eq_one_or u with hu | hu
  · subst u
    exact ⟨1, by simp⟩
  · subst u
    refine ⟨-1, ?_⟩
    ext
    change (-1 : ℤ) ^ n = -1
    exact hn.neg_one_pow

theorem rationalOddSelmer_eq_one (n : ℕ) (hn : Odd n)
    (q : selmerGroup (R := ℤ) (K := ℚ)
      (S := (∅ : Set (HeightOneSpectrum ℤ))) (n := n)) :
    q = 1 := by
  letI : Fact (0 < n) := ⟨hn.pos⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn.pos⟩
  letI : Subsingleton (ℤˣ ⧸ (powMonoidHom n : ℤˣ →* ℤˣ).range) := by
    rw [integerUnitPowerRange_eq_top n hn]
    exact QuotientGroup.subsingleton_quotient_top
  have hclass : toClassGroup (R := ℤ) (K := ℚ) n q = 1 :=
    Subsingleton.elim _ _
  have hker : q ∈ (toClassGroup (R := ℤ) (K := ℚ) n).ker :=
    MonoidHom.mem_ker.mpr hclass
  obtain ⟨u, hu⟩ := ker_le_fromUnitLift_range (R := ℤ) (K := ℚ) n hker
  have hu_one : u = 1 := Subsingleton.elim _ _
  subst u
  simpa using hu.symm

theorem rationalOddPower_of_finiteValuations (n : ℕ) (hn : Odd n)
    (a : ℚˣ)
    (ha : ∀ v : HeightOneSpectrum ℤ,
      v.valuationOfNeZeroMod n (QuotientGroup.mk a) = 1) :
    ∃ b : ℚˣ, b ^ n = a := by
  let q : selmerGroup (R := ℤ) (K := ℚ)
      (S := (∅ : Set (HeightOneSpectrum ℤ))) (n := n) :=
    ⟨QuotientGroup.mk a, fun v _ => ha v⟩
  have hq : q = 1 := rationalOddSelmer_eq_one n hn q
  have hmk : QuotientGroup.mk
      (s := (powMonoidHom n : ℚˣ →* ℚˣ).range) a = 1 :=
    congrArg Subtype.val hq
  exact (QuotientGroup.eq_one_iff a).mp hmk

end MazurTransfer

#print axioms MazurTransfer.rationalOddPower_of_finiteValuations

end

theorem solution (n : ℕ) (hn : Odd n) (a : ℚˣ)
    (ha : ∀ v : IsDedekindDomain.HeightOneSpectrum ℤ,
      v.valuationOfNeZeroMod n (QuotientGroup.mk a) = 1) :
    ∃ b : ℚˣ, b ^ n = a := by
  exact MazurTransfer.rationalOddPower_of_finiteValuations n hn a ha

#print axioms solution

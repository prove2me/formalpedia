-- Prove2me | solution 1 for HorizontalPadicL.finiteCorrection_realization_countingTransfer_inverseSeed_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:55:21.1853+00:00
-- url     : https://prove2.me/submissions/d2c55b71-9668-4c88-9eb1-7c4490909ded

import Definitions.Def_KN_PrimePowerPropagationV2
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL.CountingTransfer

open HorizontalPadicL

/-! ### Generic facts about characters -/

/-- Equal characters with level take equal values at natural numbers. -/
lemma apply_natCast_of_eq {χ ψ : DirichletCharacterWithLevel} (h : χ = ψ) (z : ℕ) :
    χ.2 (z : ZMod χ.1.1) = ψ.2 (z : ZMod ψ.1.1) := by
  subst h; rfl

/-- Two elements killed by `n` with equal `a`-th powers, `a` prime to `n`, are equal. -/
lemma eq_of_pow_eq_pow {M : Type*} [Monoid M] {x y : M} {n a : ℕ} [NeZero n]
    (hx : x ^ n = 1) (hy : y ^ n = 1) (ha : Nat.Coprime a n) (hxy : x ^ a = y ^ a) :
    x = y := by
  set u := ZMod.unitOfCoprime a ha
  set b := ((u⁻¹ : (ZMod n)ˣ) : ZMod n).val
  have hab : (a * b : ℕ) ≡ 1 [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val]
    have : ((a : ZMod n)) = (u : ZMod n) := rfl
    rw [this, Units.mul_inv]
  have key : ∀ z : M, z ^ n = 1 → z = (z ^ a) ^ b := fun z hz => by
    have hmod : ∀ j, z ^ j = z ^ (j % n) := fun j => by
      conv_lhs => rw [← Nat.div_add_mod j n, pow_add, pow_mul, hz, one_pow, one_mul]
    rw [← pow_mul, hmod, hab]
    rcases eq_or_ne n 1 with h1 | h1
    · subst h1; rw [pow_one] at hz; rw [hz, Nat.mod_one, pow_zero]
    · rw [Nat.one_mod_eq_one.mpr h1, pow_one]
  rw [key x hx, key y hy, hxy]

/-- A Dirichlet character of odd exponent is even. -/
lemma apply_neg_one_of_odd {n : ℕ} (χ : DirichletCharacter MTT.Qbar n) {k : ℕ} (hk : Odd k)
    (h : χ ^ k = 1) : χ (-1) = 1 := by
  have h2 : χ (-1) ^ 2 = 1 := by rw [sq, ← map_mul, neg_one_mul, neg_neg, map_one]
  have hk' : χ (-1) ^ k = 1 := by
    rw [← MulChar.pow_apply' χ hk.pos.ne', h, MulChar.one_apply isUnit_one.neg]
  obtain ⟨j, rfl⟩ := hk
  rwa [pow_succ, pow_mul, h2, one_pow, one_mul] at hk'

/-- A Dirichlet character agrees with its level change at natural numbers prime to the
larger level. -/
lemma changeLevel_natCast {n m : ℕ} [NeZero m] (χ : DirichletCharacter MTT.Qbar n)
    (hnm : n ∣ m) (z : ℕ) (hz : Nat.Coprime z m) :
    DirichletCharacter.changeLevel hnm χ (z : ZMod m) = χ (z : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hnm (ZMod.unitOfCoprime z hz)
  simpa only [ZMod.coe_unitOfCoprime, ZMod.cast_natCast hnm] using this

/-- Two primitive characters agreeing at all naturals prime to both levels have equal level. -/
lemma level_eq_of_agree {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (φ₁ : DirichletCharacter MTT.Qbar n₁) (φ₂ : DirichletCharacter MTT.Qbar n₂)
    (h₁ : φ₁.IsPrimitive) (h : ∀ z : ℕ, Nat.Coprime z (n₁ * n₂) → φ₁ z = φ₂ z) :
    n₁ ∣ n₂ := by
  have : NeZero (n₁ * n₂) := ⟨mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  have hch : DirichletCharacter.changeLevel (n₁.dvd_mul_right n₂) φ₁ =
      DirichletCharacter.changeLevel (n₂.dvd_mul_left n₁) φ₂ := by
    refine MulChar.ext fun u => ?_
    set z := (u : ZMod (n₁ * n₂)).val with hzdef
    have hz : Nat.Coprime z (n₁ * n₂) := by
      rw [hzdef]
      exact (ZMod.isUnit_iff_coprime _ _).mp (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
    have hu : (u : ZMod (n₁ * n₂)) = (z : ZMod (n₁ * n₂)) := by
      rw [hzdef, ZMod.natCast_zmod_val]
    rw [hu, changeLevel_natCast _ _ z hz, changeLevel_natCast _ _ z hz]
    exact h z hz
  have hgcd := DirichletCharacter.factorsThrough_gcd φ₁ φ₂ hch
  have hc := DirichletCharacter.conductor_dvd_of_mem_conductorSet φ₁ hgcd
  rw [h₁] at hc
  exact Nat.dvd_trans hc (Nat.gcd_dvd_right _ _)

/-! ### Products of the auxiliary primes -/

section Primes

variable {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
  {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
  {η : DirichletCharacterWithLevel}
  (L : SeededHorizontalPrimeDataV3 p ιp f η B)

lemma primeAt_coprime_supportModulus' (A : Finset ℕ) (n : ℕ) (hn : n ∉ A) :
    Nat.Coprime (L.primeAt n) (L.supportModulus A) := by
  rw [SeededHorizontalPrimeDataV3.supportModulus]
  apply Nat.Coprime.prod_right
  intro i hi
  apply (L.primeAt_prime n).coprime_iff_not_dvd.mpr
  intro hd
  have hprimes : L.primeAt i = L.primeAt n :=
    ((L.primeAt_prime i).dvd_iff_eq (L.primeAt_prime n).ne_one).mp hd
  have hin : i = n := L.primeAt_injective hprimes
  exact hn (hin ▸ hi)

lemma primeAt_dvd_supportModulus_iff (S : Finset ℕ) (i : ℕ) :
    L.primeAt i ∣ L.supportModulus S ↔ i ∈ S := by
  refine ⟨fun h => ?_, fun h => Finset.dvd_prod_of_mem _ h⟩
  by_contra hi
  exact (L.primeAt_prime i).one_lt.ne'
    (Nat.Coprime.eq_one_of_dvd (primeAt_coprime_supportModulus' L S i hi) h)

lemma supportModulus_dvd_of_forall (S : Finset ℕ) (c : ℕ)
    (h : ∀ i ∈ S, L.primeAt i ∣ c) : L.supportModulus S ∣ c := by
  induction S using Finset.induction_on with
  | empty => simp [SeededHorizontalPrimeDataV3.supportModulus]
  | insert i S hi ih =>
    rw [SeededHorizontalPrimeDataV3.supportModulus, Finset.prod_insert hi]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (primeAt_coprime_supportModulus' L S i hi)
      (h i (Finset.mem_insert_self i S)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma coprime_supportModulus_of_disjoint {S T : Finset ℕ} (h : Disjoint S T) :
    Nat.Coprime (L.supportModulus S) (L.supportModulus T) :=
  Nat.Coprime.prod_left fun i hi =>
    primeAt_coprime_supportModulus' L T i (Finset.disjoint_left.mp h hi)

lemma supportModulus_union {S T : Finset ℕ} (h : Disjoint S T) :
    L.supportModulus (S ∪ T) = L.supportModulus S * L.supportModulus T :=
  Finset.prod_union h

lemma supportModulus_dvd_of_subset {S T : Finset ℕ} (h : S ⊆ T) :
    L.supportModulus S ∣ L.supportModulus T :=
  Finset.prod_dvd_prod_of_subset _ _ _ h

lemma coprime_supportModulus_of_modEq_one {S : Finset ℕ} {z : ℕ}
    (hz : z ≡ 1 [MOD L.supportModulus S]) : Nat.Coprime z (L.supportModulus S) := by
  rw [Nat.Coprime, Nat.ModEq.gcd_eq hz, Nat.gcd_one_left]

end Primes

/-! ### The support projections at natural numbers -/

lemma unitsMap_unitOfCoprime {n m : ℕ} (h : n ∣ m) (z : ℕ) (hz : Nat.Coprime z m)
    (hz' : Nat.Coprime z n) :
    ZMod.unitsMap h (ZMod.unitOfCoprime z hz) = ZMod.unitOfCoprime z hz' := by
  ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]

section Projections

variable {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
  {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
  {η : DirichletCharacterWithLevel}
  {L : SeededHorizontalPrimeDataV3 p ιp f η B}
  (R : SeededHorizontalProjectionSystemV3 L)

lemma coprime_primeAt_of_coprime {S : Finset ℕ} {z : ℕ}
    (hz : Nat.Coprime z (L.supportModulus S)) {i : ℕ} (hi : i ∈ S) :
    Nat.Coprime z (L.primeAt i) :=
  Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem _ hi) hz

/-- Coordinates of the support projection of a natural number. -/
lemma supportProjection_apply (S : Finset ℕ) (z : ℕ)
    (hz : Nat.Coprime z (L.supportModulus S)) (i : {n : ℕ // n ∈ S}) :
    R.supportProjection S (ZMod.unitOfCoprime z hz) i =
      R.localProjection i.1 (ZMod.unitOfCoprime z (coprime_primeAt_of_coprime hz i.2)) := by
  simp only [SeededHorizontalProjectionSystemV3.supportProjection, MonoidHom.pi_apply,
    MonoidHom.comp_apply]
  exact congrArg (R.localProjection i.1) (unitsMap_unitOfCoprime _ z _ _)

/-- The coordinate of `z` at an auxiliary prime dividing `z - 1` is trivial. -/
lemma localProjection_eq_one {i z : ℕ} (hz : Nat.Coprime z (L.primeAt i))
    (h1 : z ≡ 1 [MOD L.primeAt i]) :
    R.localProjection i (ZMod.unitOfCoprime z hz) = 1 := by
  have : ZMod.unitOfCoprime z hz = 1 := by
    ext
    simp only [ZMod.coe_unitOfCoprime, Units.val_one]
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact h1
  rw [this, map_one]

/-- The coordinate of `z` at an auxiliary prime depends only on `z` modulo that prime. -/
lemma localProjection_congr {i z z' : ℕ} (hz : Nat.Coprime z (L.primeAt i))
    (hz' : Nat.Coprime z' (L.primeAt i)) (h : z ≡ z' [MOD L.primeAt i]) :
    R.localProjection i (ZMod.unitOfCoprime z hz) =
      R.localProjection i (ZMod.unitOfCoprime z' hz') := by
  congr 1
  ext
  simp only [ZMod.coe_unitOfCoprime]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

end Projections

/-! ### Extension by one between horizontal quotients -/

section Extension

variable {p : ℕ} {e : ℕ → ℕ}

/-- Extend an element of the horizontal quotient on `S` by `1` to a superset `T`. -/
def extendOne {S T : Finset ℕ} (_h : S ⊆ T) :
    HorizontalFiniteGroup p e S →* HorizontalFiniteGroup p e T where
  toFun x i := if hi : i.1 ∈ S then x ⟨i.1, hi⟩ else 1
  map_one' := by
    funext i
    by_cases hi : i.1 ∈ S <;> simp [hi]
  map_mul' x y := by
    funext i
    by_cases hi : i.1 ∈ S <;> simp [hi]

lemma extendOne_apply_mem {S T : Finset ℕ} (h : S ⊆ T) (x : HorizontalFiniteGroup p e S)
    (i : {n : ℕ // n ∈ T}) (hi : i.1 ∈ S) : extendOne h x i = x ⟨i.1, hi⟩ := by
  simp [extendOne, hi]

lemma extendOne_apply_not_mem {S T : Finset ℕ} (h : S ⊆ T) (x : HorizontalFiniteGroup p e S)
    (i : {n : ℕ // n ∈ T}) (hi : i.1 ∉ S) : extendOne h x i = 1 := by
  simp [extendOne, hi]

end Extension

/-! ### Realizing a supported character on its actual conductor support -/

section Realization

variable {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
  {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
  {η : DirichletCharacterWithLevel}
  {L : SeededHorizontalPrimeDataV3 p ιp f η B}
  (R : SeededHorizontalCharacterRealizationV3 L)

/-- The realization at level `M_S` is computed by the horizontal character on the support
projection, at every natural number prime to `M_S`. -/
lemma realized_apply_natCast (χ : HorizontalCharacter p L.exponent) (z : ℕ)
    (hz : Nat.Coprime z (L.supportModulus χ.support)) :
    ιp ((R.realized χ).2 (z : ZMod (R.realized χ).1.1)) =
      χ.toMonoidHom (R.projections.supportProjection χ.support (ZMod.unitOfCoprime z hz)) := by
  have hne : NeZero (L.supportModulus χ.support) :=
    ⟨Nat.ne_of_gt (L.supportModulus_pos χ.support)⟩
  have hcop : IsCoprime (z : ℤ) (L.supportModulus χ.support : ℤ) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (by rw [Int.gcd_natCast_natCast]; exact hz)
  have h1 : (R.realized χ).2 (z : ZMod (R.realized χ).1.1) = R.atLevel χ (z : ZMod _) := by
    have := DirichletCharacter.primitiveCharacter_apply_of_isCoprime (R.atLevel χ) hcop
    simp only [Int.cast_natCast] at this
    exact this
  rw [h1, ← R.atLevel_compatibility χ (ZMod.unitOfCoprime z hz), ZMod.coe_unitOfCoprime]

variable {R}

/-- A character supported on primes outside `A`, of exact order `p^m`, is realized by a
horizontal character supported exactly on the indices of its conductor. -/
lemma exists_realization_on_conductor (hR : R.HasExpectedProperties) {A : Finset ℕ} {m : ℕ}
    {ψ : DirichletCharacterWithLevel}
    (hψ : ψ ∈ supportedPrimePowerCharacters L.primeAt A p m) :
    ∃ χ' : HorizontalCharacter p L.exponent,
      Disjoint χ'.support A ∧ L.supportModulus χ'.support = ψ.1.1 ∧
      orderOf χ'.toMonoidHom = p ^ m ∧
      ∀ (z : ℕ) (hz : Nat.Coprime z (L.supportModulus χ'.support)),
        χ'.toMonoidHom (R.projections.supportProjection χ'.support
          (ZMod.unitOfCoprime z hz)) = ιp (ψ.2 z) := by
  obtain ⟨hprim, hord, S', hdisj, hdvd⟩ := hψ
  obtain ⟨χ, hχ⟩ := hR.2.2 ψ hprim ⟨m, hord⟩ ⟨S', hdvd⟩
  have hψZ : NeZero ψ.1.1 := ⟨Nat.ne_of_gt ψ.1.2⟩
  set c := ψ.1.1 with hcdef
  have hc : ψ.2.conductor = c := hprim
  set T := χ.support with hTdef
  set T' := T.filter (fun i => L.primeAt i ∣ c) with hT'def
  set T'' := T.filter (fun i => ¬ L.primeAt i ∣ c) with hT''def
  have hcT : c ∣ L.supportModulus T := by
    have := R.realized_conductor_dvd χ
    rw [hχ, hc] at this
    exact this
  have hT'T'' : L.supportModulus T' * L.supportModulus T'' = L.supportModulus T :=
    Finset.prod_filter_mul_prod_filter_not T _ L.primeAt
  have hdisj' : Disjoint T' T'' := Finset.disjoint_filter_filter_not T T _
  have hM : L.supportModulus T' = c := by
    refine Nat.dvd_antisymm (supportModulus_dvd_of_forall L T' c fun i hi =>
      (Finset.mem_filter.mp hi).2) ?_
    have hcop : Nat.Coprime c (L.supportModulus T'') :=
      Nat.Coprime.prod_right fun i hi => Nat.Coprime.symm
        ((L.primeAt_prime i).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hi).2)
    rw [← hT'T''] at hcT
    exact hcop.dvd_of_dvd_mul_right hcT
  have hT'A : Disjoint T' A := by
    refine Finset.disjoint_left.mpr fun i hi hiA => ?_
    have hiS : i ∈ S' := (primeAt_dvd_supportModulus_iff L S' i).mp
      (Nat.dvd_trans (Finset.mem_filter.mp hi).2 (hc ▸ hdvd))
    exact Finset.disjoint_left.mp hdisj hiS hiA
  have hsub : T' ⊆ T := Finset.filter_subset _ _
  let χ' : HorizontalCharacter p L.exponent :=
    ⟨T', χ.toMonoidHom.comp (extendOne hsub)⟩
  -- The value relation.
  have hrel : ∀ (z : ℕ) (hz : Nat.Coprime z (L.supportModulus T')),
      χ'.toMonoidHom (R.projections.supportProjection T' (ZMod.unitOfCoprime z hz)) =
        ιp (ψ.2 z) := by
    intro z hz
    have hco := coprime_supportModulus_of_disjoint L hdisj'
    obtain ⟨z', hz'1, hz'2⟩ := Nat.chineseRemainder hco z 1
    have hz'T' : Nat.Coprime z' (L.supportModulus T') := by
      rw [Nat.Coprime, Nat.ModEq.gcd_eq hz'1]; exact hz
    have hz'T : Nat.Coprime z' (L.supportModulus T) := by
      rw [← hT'T'']
      exact Nat.Coprime.mul_right hz'T' (coprime_supportModulus_of_modEq_one L hz'2)
    have hext : extendOne hsub (R.projections.supportProjection T' (ZMod.unitOfCoprime z hz)) =
        R.projections.supportProjection T (ZMod.unitOfCoprime z' hz'T) := by
      funext i
      rw [supportProjection_apply R.projections T z' hz'T i]
      by_cases hi : i.1 ∈ T'
      · rw [extendOne_apply_mem hsub _ i hi,
          supportProjection_apply R.projections T' z hz ⟨i.1, hi⟩]
        exact localProjection_congr R.projections _ _
          ((hz'1.of_dvd (Finset.dvd_prod_of_mem L.primeAt hi)).symm)
      · rw [extendOne_apply_not_mem hsub _ i hi]
        have hi'' : i.1 ∈ T'' := Finset.mem_filter.mpr
          ⟨i.2, fun h => hi (Finset.mem_filter.mpr ⟨i.2, h⟩)⟩
        exact (localProjection_eq_one R.projections _
          (hz'2.of_dvd (Finset.dvd_prod_of_mem L.primeAt hi''))).symm
    show χ.toMonoidHom (extendOne hsub _) = _
    rw [hext, ← realized_apply_natCast R χ z' hz'T, apply_natCast_of_eq hχ z']
    congr 2
    rw [ZMod.natCast_eq_natCast_iff]
    have := hz'1
    rwa [hM] at this
  have hχord : orderOf χ.toMonoidHom = p ^ m := by rw [← hR.1 χ, hχ, hord]
  have hord' : orderOf χ'.toMonoidHom = p ^ m := by
    refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_
    · refine MonoidHom.ext fun g => ?_
      show (χ.toMonoidHom.comp (extendOne hsub) ^ p ^ m) g = 1
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, ← hχord,
        pow_orderOf_eq_one, MonoidHom.one_apply]
    · rw [← hord]
      refine orderOf_dvd_of_pow_eq_one (MulChar.ext fun u => ?_)
      set z := (u : ZMod c).val with hzdef
      have hzu : (u : ZMod c) = (z : ZMod c) := by rw [hzdef, ZMod.natCast_zmod_val]
      have hz : Nat.Coprime z (L.supportModulus T') := by
        rw [hM]
        exact (ZMod.isUnit_iff_coprime _ _).mp (by rw [← hzu]; exact u.isUnit)
      rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hzu]
      apply (ιp).injective
      rw [map_pow, ← hrel z hz, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
        MonoidHom.one_apply, map_one]
  exact ⟨χ', hT'A, hM, hord', hrel⟩

end Realization

/-! ### The corrected image of one supported character -/

section Image

variable {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
  {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
  {η : DirichletCharacterWithLevel}
  {L : SeededHorizontalPrimeDataV3 p ιp f η B}
  {R : SeededHorizontalCharacterRealizationV3 L}

/-- The support of the corrected product. -/
abbrev corrSupport (a : ℕ) (χ ξ : HorizontalCharacter p L.exponent) : Finset ℕ :=
  ((χ.powerOnSupport a).mulOnUnion ξ).support

lemma subset_corrSupport_left (a : ℕ) (χ ξ : HorizontalCharacter p L.exponent) :
    χ.support ⊆ corrSupport a χ ξ := Finset.subset_union_left

lemma subset_corrSupport_right (a : ℕ) (χ ξ : HorizontalCharacter p L.exponent) :
    ξ.support ⊆ corrSupport a χ ξ := Finset.subset_union_right

lemma corrected_apply {a : ℕ} (χ ξ : HorizontalCharacter p L.exponent)
    (g : HorizontalFiniteGroup p L.exponent (corrSupport a χ ξ)) :
    ((χ.powerOnSupport a).mulOnUnion ξ).toMonoidHom g =
      χ.toMonoidHom (horizontalRestrictionHom (subset_corrSupport_left a χ ξ) g) ^ a *
        ξ.toMonoidHom (horizontalRestrictionHom (subset_corrSupport_right a χ ξ) g) := rfl

/-- The corrected product of a character supported off `A` with a correction on `A` has order
exactly `p^m`. -/
lemma orderOf_corrected {m a : ℕ} {A : Finset ℕ} (χ ξ : HorizontalCharacter p L.exponent)
    (hχA : Disjoint χ.support A) (hξA : ξ.support ⊆ A)
    (hχ : orderOf χ.toMonoidHom = p ^ m) (hξ : orderOf ξ.toMonoidHom ∣ p ^ m)
    (ha : Nat.Coprime a p) :
    orderOf ((χ.powerOnSupport a).mulOnUnion ξ).toMonoidHom = p ^ m := by
  have hdisj : Disjoint χ.support ξ.support := Finset.disjoint_of_subset_right hξA hχA
  have e1 : χ.toMonoidHom ^ (p ^ m) = 1 := hχ ▸ pow_orderOf_eq_one _
  have e2 : ξ.toMonoidHom ^ (p ^ m) = 1 := orderOf_dvd_iff_pow_eq_one.mp hξ
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one ?_) ?_
  · refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, corrected_apply, mul_pow, ← pow_mul, mul_comm a, pow_mul,
      ← MonoidHom.pow_apply χ.toMonoidHom, e1, ← MonoidHom.pow_apply ξ.toMonoidHom, e2]
    simp
  · set ext := extendOne (p := p) (e := L.exponent) (subset_corrSupport_left a χ ξ)
    have h1 : ∀ h, horizontalRestrictionHom (subset_corrSupport_left a χ ξ) (ext h) = h :=
      fun h => funext fun i => extendOne_apply_mem (subset_corrSupport_left a χ ξ) h ⟨i.1, _⟩ i.2
    have h2 : ∀ h, horizontalRestrictionHom (subset_corrSupport_right a χ ξ) (ext h) = 1 :=
      fun h => funext fun i => extendOne_apply_not_mem (subset_corrSupport_left a χ ξ) h ⟨i.1, _⟩
        (Finset.disjoint_right.mp hdisj i.2)
    have hext : ∀ h, ((χ.powerOnSupport a).mulOnUnion ξ).toMonoidHom (ext h) =
        χ.toMonoidHom h ^ a := fun h => by
      rw [corrected_apply, h1, h2, map_one, mul_one]
    have hpow : χ.toMonoidHom ^
        (a * orderOf ((χ.powerOnSupport a).mulOnUnion ξ).toMonoidHom) = 1 := by
      refine MonoidHom.ext fun h => ?_
      rw [MonoidHom.pow_apply, pow_mul, ← hext, ← MonoidHom.pow_apply, pow_orderOf_eq_one,
        MonoidHom.one_apply, MonoidHom.one_apply]
    have hdvd := hχ ▸ orderOf_dvd_of_pow_eq_one hpow
    exact (Nat.Coprime.pow_left m ha.symm).dvd_of_dvd_mul_left hdvd

variable (hR : R.HasExpectedProperties) {C : Subring ℂ_[p]}
  (μ : HorizontalMeasure C p L.exponent) (hpodd : p ≠ 2) {m : ℕ}
  (hinterp : ∀ χ,
      μ.eval χ ≠ 0 ↔
        let θ := primitiveProductV2 η (R.realized χ)
        @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
          (k / 2 - 1) ≠ 0)
  {A : Finset ℕ} (hcorr : μ.HasFiniteCorrection m A)

include hR hpodd hinterp hcorr in
/-- Every supported character has a nonvanishing corrected twist, of controlled conductor,
whose values away from `A` are a fixed prime-to-`p` power of the original character. -/
lemma exists_corrected_image {ψ : DirichletCharacterWithLevel}
    (hψ : ψ ∈ supportedPrimePowerCharacters L.primeAt A p m) :
    ∃ q : DirichletCharacterWithLevel × ℕ,
      q.1 ∈ seededPrimePowerTwists ι f η p m B ∧ q.2 < p ^ m ∧ Nat.Coprime q.2 p ∧
      (q.1.2.conductor : ℝ) ≤ (L.supportModulus A : ℝ) * (ψ.2.conductor : ℝ) ∧
      ∀ z : ℕ, Nat.Coprime z ψ.1.1 → z ≡ 1 [MOD L.supportModulus A] →
        q.1.2 (z : ZMod q.1.1.1) = ψ.2 (z : ZMod ψ.1.1) ^ q.2 := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨χ', hχA, hM, hord, hrel⟩ := exists_realization_on_conductor hR hψ
  obtain ⟨a, ha, hacop, ξ, hξA, hξord, hne⟩ := hcorr χ' hord hχA
  set Χ := (χ'.powerOnSupport a).mulOnUnion ξ with hΧ
  set θ := R.realized Χ
  have hdisj : Disjoint χ'.support ξ.support := Finset.disjoint_of_subset_right hξA hχA
  have hU : L.supportModulus Χ.support =
      L.supportModulus χ'.support * L.supportModulus ξ.support :=
    supportModulus_union L hdisj
  have hξM : L.supportModulus ξ.support ∣ L.supportModulus A :=
    supportModulus_dvd_of_subset L hξA
  have hΧord : orderOf Χ.toMonoidHom = p ^ m := orderOf_corrected χ' ξ hχA hξA hord hξord hacop
  have hθord : orderOf θ.2 = p ^ m := by rw [hR.1 Χ, hΧord]
  have hψprim : ψ.2.IsPrimitive := hψ.1
  have hψc : ψ.2.conductor = ψ.1.1 := hψprim
  refine ⟨(θ, a), ⟨R.realized_primitive Χ, hθord, ?_, ?_, (hinterp Χ).mp hne⟩, ha, hacop, ?_, ?_⟩
  · refine apply_neg_one_of_odd θ.2 (k := p ^ m) ((hp.odd_of_ne_two hpodd).pow) ?_
    rw [← hθord]; exact pow_orderOf_eq_one _
  · have hB : Nat.Coprime B (L.supportModulus Χ.support) :=
      Nat.Coprime.prod_right fun i _ => (L.primeAt_avoids i).symm
    exact Nat.Coprime.coprime_dvd_right (R.realized_conductor_dvd Χ) hB
  · have h1 : θ.2.conductor ≤ L.supportModulus Χ.support :=
      Nat.le_of_dvd (L.supportModulus_pos _) (R.realized_conductor_dvd Χ)
    have h2 : L.supportModulus ξ.support ≤ L.supportModulus A :=
      Nat.le_of_dvd (L.supportModulus_pos _) hξM
    rw [hU, hM] at h1
    rw [hψc]
    have : θ.2.conductor ≤ L.supportModulus A * ψ.1.1 := by
      calc θ.2.conductor ≤ ψ.1.1 * L.supportModulus ξ.support := h1
        _ ≤ ψ.1.1 * L.supportModulus A := Nat.mul_le_mul_left _ h2
        _ = L.supportModulus A * ψ.1.1 := mul_comm _ _
    exact_mod_cast this
  · intro z hz hzA
    have hzξ : z ≡ 1 [MOD L.supportModulus ξ.support] := hzA.of_dvd hξM
    have hzχ : Nat.Coprime z (L.supportModulus χ'.support) := hM ▸ hz
    have hzU : Nat.Coprime z (L.supportModulus Χ.support) := by
      rw [hU]
      exact Nat.Coprime.mul_right hzχ (coprime_supportModulus_of_modEq_one L hzξ)
    apply (ιp).injective
    rw [map_pow, realized_apply_natCast R Χ z hzU, ← hrel z hzχ]
    set x := R.projections.supportProjection (corrSupport a χ' ξ) (ZMod.unitOfCoprime z hzU)
    have h1 : horizontalRestrictionHom (subset_corrSupport_left a χ' ξ) x =
        R.projections.supportProjection χ'.support (ZMod.unitOfCoprime z hzχ) := by
      funext i
      rw [supportProjection_apply R.projections χ'.support z hzχ i]
      exact supportProjection_apply R.projections (corrSupport a χ' ξ) z hzU ⟨i.1, _⟩
    have h2 : horizontalRestrictionHom (subset_corrSupport_right a χ' ξ) x = 1 := by
      funext i
      refine (supportProjection_apply R.projections (corrSupport a χ' ξ) z hzU ⟨i.1, _⟩).trans ?_
      exact localProjection_eq_one R.projections _
        (hzξ.of_dvd (Finset.dvd_prod_of_mem L.primeAt i.2))
    rw [corrected_apply, h1, h2, map_one, mul_one]

end Image

/-! ### Recovering a character from its corrected image -/

section Fibre

/-- A primitive character killed by `n` stays primitive under a power prime to `n`. -/
lemma isPrimitive_pow {c : ℕ} [NeZero c] {ψ : DirichletCharacter MTT.Qbar c}
    (hprim : ψ.IsPrimitive) {n a : ℕ} [NeZero n] (hn : ψ ^ n = 1) (ha : Nat.Coprime a n) :
    (ψ ^ a).IsPrimitive := by
  set u := ZMod.unitOfCoprime a ha
  set b := ((u⁻¹ : (ZMod n)ˣ) : ZMod n).val
  have hab : (a * b : ℕ) ≡ 1 [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val]
    have : ((a : ZMod n)) = (u : ZMod n) := rfl
    rw [this, Units.mul_inv]
  have hmod : ∀ j, ψ ^ j = ψ ^ (j % n) := fun j => by
    conv_lhs => rw [← Nat.div_add_mod j n, pow_add, pow_mul, hn, one_pow, one_mul]
  have hback : ψ = (ψ ^ a) ^ b := by
    rw [← pow_mul, hmod, hab]
    rcases eq_or_ne n 1 with h1 | h1
    · subst h1; rw [pow_one] at hn; rw [hn, Nat.mod_one, pow_zero]
    · rw [Nat.one_mod_eq_one.mpr h1, pow_one]
  have hc : ψ.conductor = c := hprim
  rw [DirichletCharacter.isPrimitive_def]
  refine Nat.dvd_antisymm ?_ ?_
  · have h0 := DirichletCharacter.conductor_pow_dvd ψ a
    rwa [hc] at h0
  · have h := DirichletCharacter.conductor_pow_dvd (ψ ^ a) b
    rwa [← hback, hc] at h

variable {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
  {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
  {η : DirichletCharacterWithLevel}
  {L : SeededHorizontalPrimeDataV3 p ιp f η B}

lemma coprime_level_supportModulus {A : Finset ℕ} {m : ℕ} {ψ : DirichletCharacterWithLevel}
    (hψ : ψ ∈ supportedPrimePowerCharacters L.primeAt A p m) :
    Nat.Coprime ψ.1.1 (L.supportModulus A) := by
  obtain ⟨hprim, -, S', hdisj, hdvd⟩ := hψ
  have hc : ψ.2.conductor = ψ.1.1 := hprim
  rw [← hc]
  exact Nat.Coprime.coprime_dvd_left hdvd (coprime_supportModulus_of_disjoint L hdisj)

/-- Two supported characters with the same corrected image and the same exponent coincide. -/
lemma eq_of_same_image {A : Finset ℕ} {m : ℕ} {ψ₁ ψ₂ : DirichletCharacterWithLevel}
    (h₁ : ψ₁ ∈ supportedPrimePowerCharacters L.primeAt A p m)
    (h₂ : ψ₂ ∈ supportedPrimePowerCharacters L.primeAt A p m)
    (θ : DirichletCharacterWithLevel) {a : ℕ} (ha : Nat.Coprime a p)
    (hr₁ : ∀ z : ℕ, Nat.Coprime z ψ₁.1.1 → z ≡ 1 [MOD L.supportModulus A] →
      θ.2 (z : ZMod θ.1.1) = ψ₁.2 (z : ZMod ψ₁.1.1) ^ a)
    (hr₂ : ∀ z : ℕ, Nat.Coprime z ψ₂.1.1 → z ≡ 1 [MOD L.supportModulus A] →
      θ.2 (z : ZMod θ.1.1) = ψ₂.2 (z : ZMod ψ₂.1.1) ^ a) :
    ψ₁ = ψ₂ := by
  have hp := (Fact.out : p.Prime)
  have hpm : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hapm : Nat.Coprime a (p ^ m) := Nat.Coprime.pow_right m ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (by simpa using ha)
  have hZ₁ : NeZero ψ₁.1.1 := ⟨Nat.ne_of_gt ψ₁.1.2⟩
  have hZ₂ : NeZero ψ₂.1.1 := ⟨Nat.ne_of_gt ψ₂.1.2⟩
  have hc₁ := coprime_level_supportModulus h₁
  have hc₂ := coprime_level_supportModulus h₂
  have hn₁ : ψ₁.2 ^ (p ^ m) = 1 := h₁.2.1 ▸ pow_orderOf_eq_one _
  have hn₂ : ψ₂.2 ^ (p ^ m) = 1 := h₂.2.1 ▸ pow_orderOf_eq_one _
  -- Agreement of the `a`-th powers away from both levels.
  have hagree : ∀ z : ℕ, Nat.Coprime z (ψ₁.1.1 * ψ₂.1.1) →
      ψ₁.2 (z : ZMod ψ₁.1.1) ^ a = ψ₂.2 (z : ZMod ψ₂.1.1) ^ a := by
    intro z hz
    obtain ⟨z', hz'1, hz'2⟩ :=
      Nat.chineseRemainder (Nat.coprime_mul_iff_left.mpr ⟨hc₁, hc₂⟩) z 1
    have hz'c : Nat.Coprime z' (ψ₁.1.1 * ψ₂.1.1) := by
      rw [Nat.Coprime, Nat.ModEq.gcd_eq hz'1]; exact hz
    have e₁ : (z' : ZMod ψ₁.1.1) = z :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hz'1.of_dvd (Dvd.intro _ rfl))
    have e₂ : (z' : ZMod ψ₂.1.1) = z :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (hz'1.of_dvd (Dvd.intro_left _ rfl))
    rw [← e₁, ← e₂, ← hr₁ z' (Nat.Coprime.coprime_dvd_right (Dvd.intro _ rfl) hz'c) hz'2,
      hr₂ z' (Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) hz'c) hz'2]
  have hp₁ := isPrimitive_pow h₁.1 hn₁ hapm
  have hp₂ := isPrimitive_pow h₂.1 hn₂ hapm
  have hl₁ : ψ₁.1.1 ∣ ψ₂.1.1 := level_eq_of_agree (ψ₁.2 ^ a) (ψ₂.2 ^ a) hp₁ fun z hz => by
    rw [MulChar.pow_apply' _ ha0, MulChar.pow_apply' _ ha0]; exact hagree z hz
  have hl₂ : ψ₂.1.1 ∣ ψ₁.1.1 := level_eq_of_agree (ψ₂.2 ^ a) (ψ₁.2 ^ a) hp₂ fun z hz => by
    rw [MulChar.pow_apply' _ ha0, MulChar.pow_apply' _ ha0]
    exact (hagree z (by rwa [mul_comm])).symm
  have hlev : ψ₁.1 = ψ₂.1 := Subtype.ext (Nat.dvd_antisymm hl₁ hl₂)
  obtain ⟨⟨c₁, hc₁'⟩, φ₁⟩ := ψ₁
  obtain ⟨⟨c₂, hc₂'⟩, φ₂⟩ := ψ₂
  simp only [Subtype.mk.injEq] at hlev
  subst hlev
  refine Sigma.ext rfl (heq_of_eq (MulChar.ext fun u => ?_))
  set z := (u : ZMod c₁).val with hzdef
  have hzu : (u : ZMod c₁) = (z : ZMod c₁) := by rw [hzdef, ZMod.natCast_zmod_val]
  have hz : Nat.Coprime z c₁ :=
    (ZMod.isUnit_iff_coprime _ _).mp (by rw [← hzu]; exact u.isUnit)
  have hzz : Nat.Coprime z (c₁ * c₁) := Nat.Coprime.mul_right hz hz
  rw [hzu]
  refine eq_of_pow_eq_pow (n := p ^ m) ?_ ?_ hapm (hagree z hzz)
  · rw [← MulChar.pow_apply' _ (pow_ne_zero _ hp.ne_zero)]
    simp only at hn₁
    rw [hn₁, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr hz)]
  · rw [← MulChar.pow_apply' _ (pow_ne_zero _ hp.ne_zero)]
    simp only at hn₂
    rw [hn₂, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr hz)]

end Fibre

end HorizontalPadicL.CountingTransfer

open HorizontalPadicL HorizontalPadicL.CountingTransfer in
theorem solution
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B)
    (R : SeededHorizontalCharacterRealizationV3 L)
    (hR : R.HasExpectedProperties)
    {C : Subring ℂ_[p]} (μ : HorizontalMeasure C p L.exponent)
    (hpodd : p ≠ 2) (m : ℕ) (hm : 0 < m)
    (hinterp : ∀ χ,
      μ.eval χ ≠ 0 ↔
        let θ := primitiveProductV2 η (R.realized χ)
        @MTT.criticalLValue ι f.form θ.1.1 ⟨Nat.ne_of_gt θ.1.2⟩ θ.2
          (k / 2 - 1) ≠ 0)
    (A : Finset ℕ) (hcorr : μ.HasFiniteCorrection m A) :
    Nonempty (CharacterCountingTransfer
      (supportedPrimePowerCharacters L.primeAt A p m)
      (seededPrimePowerTwists ι f η p m B)) := by
  have hspec := fun ψ : supportedPrimePowerCharacters L.primeAt A p m =>
    exists_corrected_image hR μ hpodd hinterp hcorr ψ.2
  choose q hqT hqa hqcop hqcond hqrel using hspec
  have hinj : ∀ θ : seededPrimePowerTwists ι f η p m B,
      Set.InjOn (fun ψ => (q ψ).2)
        {ψ | (⟨(q ψ).1, hqT ψ⟩ : seededPrimePowerTwists ι f η p m B) = θ} := by
    intro θ ψ₁ h₁ ψ₂ h₂ ha
    simp only [Set.mem_ofPred_eq] at h₁ h₂
    have hθ : (q ψ₁).1 = (q ψ₂).1 := congrArg Subtype.val (h₁.trans h₂.symm)
    refine Subtype.ext (eq_of_same_image ψ₁.2 ψ₂.2 (q ψ₁).1 (hqcop ψ₁) (hqrel ψ₁) ?_)
    intro z hz hzA
    rw [hθ, hqrel ψ₂ z hz hzA]
    exact congrArg _ ha.symm
  refine ⟨{ map := fun ψ => ⟨(q ψ).1, hqT ψ⟩
            scale := L.supportModulus A
            scale_ge_one := by exact_mod_cast L.supportModulus_pos A
            multiplicity := p ^ m
            multiplicity_pos := pow_pos (Fact.out : p.Prime).pos m
            conductor_bound := fun ψ => hqcond ψ
            fibre_finite := fun θ => ?_
            fibre_card := fun θ => ?_ }⟩
  · refine Set.Finite.of_finite_image ((Set.finite_Iio (p ^ m)).subset ?_) (hinj θ)
    rintro _ ⟨ψ, -, rfl⟩
    exact hqa ψ
  · refine (Set.ncard_le_ncard_of_injOn (fun ψ => (q ψ).2) (fun ψ _ => hqa ψ) (hinj θ)
      (Set.finite_Iio _)).trans ?_
    rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

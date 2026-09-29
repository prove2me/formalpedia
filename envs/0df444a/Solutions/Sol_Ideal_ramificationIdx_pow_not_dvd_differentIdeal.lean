-- Prove2me | solution 1 for Ideal.ramificationIdx_pow_not_dvd_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b9c7afb1-264e-5edb-80b8-6a2ca71b209e

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.KrullDimension.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal

open Module

namespace LinearMap
p2m_export "LinearMap" "coe_comp comp_zero range rank fst_comp_inr snd mul_apply' snd_comp_inl trace_prodMap' inl_apply map_span fst_apply inr fst trace_comp_comm' mk coe_coe pi ext trace prodMap comp_assoc inl comp_apply trace_conj' restrict coe_restrict_apply"
p2m_open "LinearMap"

section TraceAdditivity

variable {F : Type*} [Field F]

theorem trace_prod_eq_trace_fst_add_trace_snd {M N : Type*} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [FiniteDimensional F M] [FiniteDimensional F N]
    (g : (M × N) →ₗ[F] (M × N)) :
    trace F (M × N) g = trace F M (fst F M N ∘ₗ g ∘ₗ inl F M N) +
      trace F N (snd F M N ∘ₗ g ∘ₗ inr F M N) := by
  have hg : g = (fst F M N ∘ₗ g ∘ₗ inl F M N).prodMap (snd F M N ∘ₗ g ∘ₗ inr F M N)
      + inl F M N ∘ₗ ((fst F M N ∘ₗ g ∘ₗ inr F M N) ∘ₗ snd F M N)
      + inr F M N ∘ₗ ((snd F M N ∘ₗ g ∘ₗ inl F M N) ∘ₗ fst F M N) := by
    ext <;> simp [Prod.mk_zero_zero]
  have h1 : trace F (M × N)
      (inl F M N ∘ₗ ((fst F M N ∘ₗ g ∘ₗ inr F M N) ∘ₗ snd F M N)) = 0 := by
    rw [trace_comp_comm', comp_assoc, snd_comp_inl, comp_zero, map_zero]
  have h2 : trace F (M × N)
      (inr F M N ∘ₗ ((snd F M N ∘ₗ g ∘ₗ inl F M N) ∘ₗ fst F M N)) = 0 := by
    rw [trace_comp_comm', comp_assoc, fst_comp_inr, comp_zero, map_zero]
  conv_lhs => rw [hg]
  rw [map_add, map_add, h1, h2, add_zero, add_zero, trace_prodMap']

theorem trace_eq_trace_restrict_add_trace_quotient {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (T : V →ₗ[F] V) (hT : W ≤ W.comap T) :
    trace F V T = trace F W (T.restrict fun _ hx => hT hx) +
      trace F (V ⧸ W) (W.mapQ W T hT) := by
  obtain ⟨W', hW⟩ := W.exists_isCompl
  set e := Submodule.prodEquivOfIsCompl W W' hW with he
  rw [← trace_conj' T e.symm, trace_prod_eq_trace_fst_add_trace_snd]
  congr 1
  · congr 1
    ext w
    have hTw : T (w : V) = ((⟨T w, hT w.2⟩ : W) : V) := rfl
    simp only [coe_comp, Function.comp_apply, inl_apply, fst_apply, LinearEquiv.coe_coe,
      LinearEquiv.conj_apply, LinearEquiv.symm_symm, he, Submodule.coe_prodEquivOfIsCompl',
      ZeroMemClass.coe_zero, add_zero, coe_restrict_apply]
    rw [hTw, Submodule.prodEquivOfIsCompl_symm_apply_left]
  · rw [← trace_conj' (W.mapQ W T hT) (Submodule.quotientEquivOfIsCompl W W' hW)]
    congr 1
    ext w
    simp [he, LinearEquiv.conj_apply]

end TraceAdditivity

end LinearMap

namespace Ideal
p2m_export "Ideal" "map_le_iff_le_comap prime_iff_isPrime Quotient.eq_zero_iff_mem mem_span_singleton IsPrime.ne_top map_span absNorm_span_singleton pi quotientToQuotientRangePowQuotSucc_injective quotientToQuotientRangePowQuotSucc mem_bot span powQuotSuccInclusion_injective mul_le_left liesOver_span_iff quotientToQuotientRangePowQuotSucc_mk powQuotSuccInclusion one_eq_top map_quotient_self IsMaximal Quotient.mk dvd_iff_le Quotient.field mul_mem_left quotEquivOfEq map IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver le_pow_ramificationIdx ext le_of_dvd quotientToQuotientRangePowQuotSucc_surjective LiesOver IsPrime ramificationIdx' eq_prime_pow_mul_coprime IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count finiteQuotientOfFreeOfNeBot under quotientMulEquivQuotientProd comap isPrime_of_prime map_eq_bot_iff_of_injective pow_right_strictAnti Quotient.algebraQuotientOfRamificationIdxNeZero ramificationIdx_bot' Quotient.mk_surjective isCoprime_iff_sup_eq Quotient.algebraQuotientOfLEComap absNorm_dvd_absNorm_of_le map_top"
p2m_open "Ideal"

section GradedTrace

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (P : Ideal S)

attribute [local instance] Ideal.Quotient.field

noncomputable def mulRestrictPowQuot (z : S ⧸ P ^ ramificationIdx' p P)
    (I : Ideal (S ⧸ P ^ ramificationIdx' p P)) : I →ₗ[R ⧸ p] I where
  toFun x := ⟨z * x, I.mul_mem_left z x.2⟩
  map_add' x y := Subtype.ext <| by simp [mul_add]
  map_smul' c x := Subtype.ext <| by simp

@[scoped simp]
theorem mulRestrictPowQuot_apply_coe (z : S ⧸ P ^ ramificationIdx' p P)
    (I : Ideal (S ⧸ P ^ ramificationIdx' p P)) (x : I) :
    (mulRestrictPowQuot p P z I x : S ⧸ P ^ ramificationIdx' p P) = z * x := rfl

attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

variable [p.IsMaximal] [P.IsPrime] [IsDedekindDomain S] [hne : NeZero (ramificationIdx' p P)]

theorem trace_mulRestrictPowQuot_map_pow [Module.Finite (R ⧸ p) (S ⧸ P ^ ramificationIdx' p P)]
    (hP0 : P ≠ ⊥) (z : S) {i k : ℕ} (hik : i + k = ramificationIdx' p P) :
    LinearMap.trace (R ⧸ p) _
      (mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z)
        ((P ^ i).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P)))) =
      k • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P z) := by
  induction k generalizing i with
  | zero =>
    rw [zero_nsmul]
    rw [add_zero] at hik
    subst hik
    have hT0 : mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z)
        ((P ^ ramificationIdx' p P).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P))) = 0 := by
      apply LinearMap.ext
      intro x
      have hx : (x : S ⧸ P ^ ramificationIdx' p P) ∈
          (⊥ : Ideal (S ⧸ P ^ ramificationIdx' p P)) := by
        rw [← Ideal.map_quotient_self (P ^ ramificationIdx' p P)]
        exact x.2
      rw [Ideal.mem_bot] at hx
      exact Subtype.ext (by simp [hx])
    rw [hT0, map_zero]
  | succ k ih =>
    have hi : i < ramificationIdx' p P := by omega

    set W := LinearMap.range (powQuotSuccInclusion p P i) with hW
    set T := mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z)
      ((P ^ i).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P))) with hT
    have hWT : W ≤ W.comap T := by
      rintro _ ⟨y, rfl⟩
      refine ⟨mulRestrictPowQuot p P (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z) _ y, ?_⟩
      ext; rfl
    rw [LinearMap.trace_eq_trace_restrict_add_trace_quotient W T hWT, succ_nsmul]
    congr 1
    ·
      rw [← ih (i := i + 1) (by omega)]
      let φ := LinearEquiv.ofInjective _ (powQuotSuccInclusion_injective p P i)
      rw [← LinearMap.trace_conj' _ φ]
      congr 1
      ext w
      obtain ⟨y, rfl⟩ := φ.surjective w
      simp only [LinearMap.coe_restrict_apply, LinearEquiv.conj_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply]
      simp [φ, T, LinearEquiv.ofInjective_apply]
    ·
      obtain ⟨a, a_mem, a_notMem⟩ := SetLike.exists_of_lt
        (Ideal.pow_right_strictAnti P hP0 (Ideal.IsPrime.ne_top inferInstance)
          (le_refl i.succ))
      let ψ := LinearEquiv.ofBijective (quotientToQuotientRangePowQuotSucc p P a_mem)
        ⟨quotientToQuotientRangePowQuotSucc_injective p P hi a_mem a_notMem,
          quotientToQuotientRangePowQuotSucc_surjective p P hP0 hi a_mem a_notMem⟩
      rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ ψ]
      congr 1
      apply LinearMap.ext
      intro q
      obtain ⟨x, rfl⟩ := ψ.surjective q
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, LinearEquiv.symm_apply_apply]
      have hmk : ∀ y : S, Ideal.Quotient.mk P y = Submodule.Quotient.mk y := fun _ => rfl
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← map_mul, hmk, hmk]
      simp only [ψ, LinearEquiv.ofBijective_apply, quotientToQuotientRangePowQuotSucc_mk,
        Submodule.mapQ_apply]
      congr 1
      apply Subtype.ext
      simp only [T, mulRestrictPowQuot_apply_coe, ← map_mul]
      congr 1
      ring

theorem trace_quotient_pow_ramificationIdx [Module.Finite (R ⧸ p) (S ⧸ P ^ ramificationIdx' p P)]
    (hP0 : P ≠ ⊥) (z : S) :
    Algebra.trace (R ⧸ p) (S ⧸ P ^ ramificationIdx' p P)
        (Ideal.Quotient.mk (P ^ ramificationIdx' p P) z) =
      ramificationIdx' p P • Algebra.trace (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk P z) := by
  rw [← trace_mulRestrictPowQuot_map_pow p P hP0 z (i := 0) (zero_add _), Algebra.trace_apply]

  have htop : ∀ y : S ⧸ P ^ ramificationIdx' p P,
      y ∈ (P ^ 0).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P)) := by
    intro y
    simp [Ideal.one_eq_top, Ideal.map_top]
  let ι : ((P ^ 0).map (Ideal.Quotient.mk (P ^ ramificationIdx' p P))) →ₗ[R ⧸ p]
      (S ⧸ P ^ ramificationIdx' p P) :=
    { toFun := fun x => (x : S ⧸ P ^ ramificationIdx' p P)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : Function.Bijective ι :=
    ⟨fun a b h => Subtype.ext h, fun y => ⟨⟨y, htop y⟩, rfl⟩⟩
  let τ := LinearEquiv.ofBijective ι hι
  rw [← LinearMap.trace_conj' _ τ]
  congr 1
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := τ.surjective y
  simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply]
  rfl

end GradedTrace

end Ideal
p2m_reactivate "P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.Ideal"

section TameDifferent

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

attribute [local instance] Ideal.Quotient.field

p2m_open "Ideal P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.Ideal UniqueFactorizationMonoid"

theorem not_pow_ramificationIdx_dvd_differentIdeal {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ ramificationIdx' p P ∣ differentIdeal A B := by
  classical
  have he0 : ramificationIdx' p P ≠ 0 := by
    rintro h
    simp [h] at he
  haveI : NeZero (ramificationIdx' p P) := ⟨he0⟩
  have hp' : p.map (algebraMap A B) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    exact he0 (Ideal.ramificationIdx_bot' hp (FaithfulSMul.algebraMap_injective A B))
  obtain ⟨Q, hPQ, hQ⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp' inferInstance hPbot]
    at hQ
  have hcop : IsCoprime (P ^ ramificationIdx' p P) Q :=
    (Ideal.isCoprime_iff_sup_eq.mpr hPQ).pow_left
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap (by
      rw [← Ideal.map_le_iff_le_comap, hQ]
      exact Ideal.mul_le_right)
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) (B ⧸ Q)
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ ramificationIdx' p P) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ ramificationIdx' p P) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) _
  have : Module.Finite (A ⧸ p) (B ⧸ P) :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ p) _
  let crt : (B ⧸ p.map (algebraMap A B)) ≃ₐ[A ⧸ p]
      ((B ⧸ P ^ ramificationIdx' p P) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hQ).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ ramificationIdx' p P) Q hcop),
      commutes' := Quotient.ind fun _ ↦ rfl }
  obtain ⟨x, hx⟩ :
      ∃ x : B, Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk P x) ≠ 0 := by
    obtain ⟨y, hy⟩ : ∃ y, Algebra.trace (A ⧸ p) (B ⧸ P) y ≠ 0 := by
      simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  have hx' : Algebra.trace (A ⧸ p) (B ⧸ P ^ ramificationIdx' p P)
      (Ideal.Quotient.mk _ x) ≠ 0 := by
    rw [Ideal.trace_quotient_pow_ramificationIdx p P hPbot x, nsmul_eq_mul]
    exact mul_ne_zero he hx
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (crt.symm (Ideal.Quotient.mk _ x, 0))
  refine not_dvd_differentIdeal_of_intTrace_not_mem A (P ^ ramificationIdx' p P) Q hQ.symm
    y ?_ ?_
  · have := congr((crt $hy).2)
    simp at this
    simpa [crt, Ideal.Quotient.eq_zero_iff_mem] using this
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.trace_quotient_eq_of_isDedekindDomain,
      hy, Algebra.trace_eq_of_algEquiv, Algebra.trace_prod_apply]
    simpa using hx'

theorem emultiplicity_differentIdeal_eq_ramificationIdx_sub_one {p : Ideal A} [p.IsMaximal]
    (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    emultiplicity P (differentIdeal A B) = (ramificationIdx' p P - 1 : ℕ) := by
  have he0 : ramificationIdx' p P ≠ 0 := by
    rintro h
    simp [h] at he
  rw [emultiplicity_eq_coe, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he0)]
  exact ⟨pow_sub_one_dvd_differentIdeal A P _ hp (Ideal.dvd_iff_le.mpr le_pow_ramificationIdx),
    not_pow_ramificationIdx_dvd_differentIdeal A hp P he⟩

theorem count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one [DecidableEq (Ideal B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    (normalizedFactors (differentIdeal A B)).count P = ramificationIdx' p P - 1 := by
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    apply he
    rw [Ideal.ramificationIdx_bot' hp (FaithfulSMul.algebraMap_injective A B), Nat.cast_zero]
  have := emultiplicity_differentIdeal_eq_ramificationIdx_sub_one A hp P he
  rw [emultiplicity_eq_count_normalizedFactors
    ((Ideal.prime_iff_isPrime hPbot).mpr inferInstance).irreducible differentIdeal_ne_bot,
    normalize_eq, Nat.cast_inj] at this
  exact this

theorem not_pow_ramificationIdx_dvd_differentIdeal_of_finite {p : Ideal A} [p.IsMaximal]
    [Finite (A ⧸ p)] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ ramificationIdx' p P ∣ differentIdeal A B :=
  not_pow_ramificationIdx_dvd_differentIdeal A hp P he

theorem count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one_of_finite
    [DecidableEq (Ideal B)] {p : Ideal A} [p.IsMaximal] [Finite (A ⧸ p)] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (he : ((ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    (normalizedFactors (differentIdeal A B)).count P = ramificationIdx' p P - 1 :=
  count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one A hp P he

end TameDifferent
p2m_reactivate "P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.Ideal"

section MinkowskiKill

p2m_open "NumberField P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.NumberField Ideal P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.Ideal NumberField.Ideal UniqueFactorizationMonoid"

attribute [local instance] Ideal.Quotient.field FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

theorem nine_mul_pow_lt_four_mul_pow {m : ℕ} (hm : 2 ≤ m) : 9 * 48 ^ m < 4 * 81 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m _ ih =>
    calc 9 * 48 ^ (m + 1) = 48 * (9 * 48 ^ m) := by ring
      _ < 48 * (4 * 81 ^ m) := by gcongr
      _ ≤ 81 * (4 * 81 ^ m) := by gcongr; norm_num
      _ = 4 * 81 ^ (m + 1) := by ring

namespace NumberField p2m_export "NumberField" "abs_discr_ge IsTotallyComplex IsTotallyComplex.finrank discr mk RingOfIntegers InfinitePlace.nrComplexPlaces InfinitePlace absNorm_differentIdeal RingOfIntegers.rank" end NumberField
p2m_open_scoped "NumberField" in

theorem NumberField.differentIdeal_sq_dvd_span_three (M : Type*) [Field M] [NumberField M]
    (h_unram : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∉ P →
      Algebra.IsUnramifiedAt ℤ P)
    (h_tame : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∈ P →
      ramificationIdx' (Ideal.span {(3 : ℤ)}) P ≤ 2) :
    differentIdeal ℤ (𝓞 M) ^ 2 ∣ (Ideal.span {(3 : ℤ)}).map (algebraMap ℤ (𝓞 M)) := by
  classical
  set p : Ideal ℤ := Ideal.span {(3 : ℤ)} with hp_def
  have hp : p ≠ ⊥ := by simp [p]
  haveI : p.IsMaximal := Int.prime_three.isMaximal_span_singleton
  haveI : Finite (ℤ ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp
  have hJ : p.map (algebraMap ℤ (𝓞 M)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 M))).not.mpr hp
  have hD : differentIdeal ℤ (𝓞 M) ≠ ⊥ := differentIdeal_ne_bot
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hD) hJ,
    Multiset.le_iff_count, normalizedFactors_pow]
  intro P
  rw [Multiset.count_nsmul]
  by_cases hPmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 M))
  swap
  · rw [Multiset.count_eq_zero_of_notMem hPmem, mul_zero]
    exact Nat.zero_le _
  have hPprime : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hPmem)
  have hP0 : P ≠ ⊥ := (prime_of_normalized_factor P hPmem).ne_zero
  haveI : P.IsMaximal := hPprime.isMaximal hP0
  by_cases h3 : (3 : 𝓞 M) ∈ P
  ·
    haveI : P.LiesOver p := (Ideal.liesOver_span_iff hPprime.ne_top Int.prime_three).mpr
      (by simpa using h3)
    have he0 : ramificationIdx' p P ≠ 0 :=
      IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp
    have he2 : ramificationIdx' p P ≤ 2 := h_tame P h3
    have he : ((ramificationIdx' p P : ℕ) : ℤ ⧸ p) ≠ 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p), Ne, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      omega
    rw [count_normalizedFactors_differentIdeal_eq_ramificationIdx_sub_one ℤ hp P he,
      ← IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hJ hPprime hP0]
    omega
  ·
    have hnd : ¬ P ∣ differentIdeal ℤ (𝓞 M) := not_dvd_differentIdeal_iff.mpr (h_unram P h3)
    exact absurd (dvd_of_mem_normalizedFactors hPmem) hnd

p2m_open_scoped "NumberField" in

theorem NumberField.natAbs_discr_sq_dvd_three_pow (M : Type*) [Field M] [NumberField M]
    (h_unram : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∉ P →
      Algebra.IsUnramifiedAt ℤ P)
    (h_tame : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∈ P →
      ramificationIdx' (Ideal.span {(3 : ℤ)}) P ≤ 2) :
    (discr M).natAbs ^ 2 ∣ 3 ^ Module.finrank ℚ M := by
  have h := Ideal.absNorm_dvd_absNorm_of_le
    (Ideal.le_of_dvd (differentIdeal_sq_dvd_span_three M h_unram h_tame))
  rw [map_pow, absNorm_differentIdeal M, Ideal.map_span, Set.image_singleton,
    Ideal.absNorm_span_singleton, Algebra.norm_algebraMap, RingOfIntegers.rank] at h
  simpa using h

p2m_open_scoped "NumberField" in

theorem NumberField.finrank_le_two_of_unramified_outside_three_of_tame (M : Type*) [Field M]
    [NumberField M] [IsTotallyComplex M]
    (h_unram : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∉ P →
      Algebra.IsUnramifiedAt ℤ P)
    (h_tame : ∀ (P : Ideal (𝓞 M)) [P.IsMaximal], (3 : 𝓞 M) ∈ P →
      ramificationIdx' (Ideal.span {(3 : ℤ)}) P ≤ 2) :
    Module.finrank ℚ M ≤ 2 := by
  by_contra! hn
  set m := InfinitePlace.nrComplexPlaces M with hm_def
  have hnm : Module.finrank ℚ M = 2 * m := IsTotallyComplex.finrank M
  have hm : 2 ≤ m := by omega

  have hdvd := natAbs_discr_sq_dvd_three_pow M h_unram h_tame
  rw [hnm, mul_comm, pow_mul] at hdvd
  have hle : (discr M).natAbs ^ 2 ≤ (3 ^ m) ^ 2 := Nat.le_of_dvd (by positivity) hdvd
  have hle' : (discr M).natAbs ≤ 3 ^ m := (Nat.pow_le_pow_iff_left two_ne_zero).mp hle
  have hreal : ((|discr M| : ℤ) : ℝ) ≤ (3 : ℝ) ^ m := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hle'

  have hmink := abs_discr_ge (K := M) (by omega)
  rw [hnm] at hmink
  have hπ : (81 / 16 : ℝ) ≤ (3 * Real.pi / 4) ^ 2 := by
    have h3 : (9 / 4 : ℝ) ≤ 3 * Real.pi / 4 := by linarith [Real.pi_gt_three]
    nlinarith [h3]
  have key : (4 / 9 : ℝ) * (81 / 16) ^ m ≤ (3 : ℝ) ^ m := by
    calc (4 / 9 : ℝ) * (81 / 16) ^ m ≤ (4 / 9) * ((3 * Real.pi / 4) ^ 2) ^ m := by gcongr
      _ = (4 / 9) * (3 * Real.pi / 4) ^ (2 * m) := by rw [pow_mul]
      _ ≤ ((|discr M| : ℤ) : ℝ) := hmink
      _ ≤ 3 ^ m := hreal

  have key' : (4 : ℝ) * 81 ^ m ≤ 9 * 48 ^ m := by
    have := mul_le_mul_of_nonneg_right key (by positivity : (0 : ℝ) ≤ 9 * 16 ^ m)
    calc (4 : ℝ) * 81 ^ m = (4 / 9 * (81 / 16) ^ m) * (9 * 16 ^ m) := by
            rw [div_pow]; field_simp
      _ ≤ 3 ^ m * (9 * 16 ^ m) := this
      _ = 9 * 48 ^ m := by rw [show (48 : ℝ) = 3 * 16 by norm_num, mul_pow]; ring
  have := nine_mul_pow_lt_four_mul_pow hm
  have : ((9 * 48 ^ m : ℕ) : ℝ) < ((4 * 81 ^ m : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at this
  linarith

end MinkowskiKill
p2m_reactivate "P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal.Ideal"

theorem solution (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
    [@Algebra.IsSeparable (FractionRing A) (FractionRing B) _ _
      (FractionRing.liftAlgebra A (FractionRing B))]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((Ideal.ramificationIdx' p P : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ Ideal.ramificationIdx' p P ∣ differentIdeal A B :=
  not_pow_ramificationIdx_dvd_differentIdeal A hp P he

#print axioms solution

end S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal
end P2MW
export P2MW.S_Ideal_ramificationIdx_pow_not_dvd_differentIdeal (solution)

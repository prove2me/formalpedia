-- Prove2me | solution 1 for IsRegularLocalRing.exists_isUnit_pow_eq_mul_of_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/27cee08b-fada-5810-96e0-183b063ec712

import Mathlib
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing
import Theorems.Thm_IsRegularLocalRing_of_etale_of_moduleFinite
import Theorems.Thm_IsRegularLocalRing_adjoinRoot_X_pow_sub_C_of_notMem_sq
import Theorems.Thm_HenselianLocalRing_of_moduleFinite_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_exists_isUnit_pow_eq_mul_of_baseChange
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open IsLocalRing Polynomial
open scoped TensorProduct

namespace L1BRDA

theorem mem_and_notMem_sq_of_etale
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (R' : Type*) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R']
    [Algebra.Etale R R']
    (s : R) (hs : s ∈ maximalIdeal R) (hs2 : s ∉ maximalIdeal R ^ 2) :
    algebraMap R R' s ∈ maximalIdeal R' ∧ algebraMap R R' s ∉ maximalIdeal R' ^ 2 := by
  classical
  haveI : Nontrivial R' := inferInstance
  haveI : FaithfulSMul R R' := inferInstance
  haveI : IsLocalHom (algebraMap R R') := Algebra.IsIntegral.isLocalHom R R'
  haveI : Module.FaithfullyFlat R R' := inferInstance
  have hmap : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' :=
    Algebra.FormallyUnramified.map_maximalIdeal
  refine ⟨?_, fun h2 => hs2 ?_⟩
  · rw [← hmap]; exact Ideal.mem_map_of_mem _ hs
  · rw [← hmap, ← Ideal.map_pow] at h2
    have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := R') (maximalIdeal R ^ 2)
    rw [← this]; exact h2

end L1BRDA

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open IsLocalRing Polynomial

open scoped TensorProduct

universe u v

namespace KFRDDim

open Order

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]

noncomputable def contract (q : PrimeSpectrum B) : PrimeSpectrum A :=
  ⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩

theorem contract_strictMono : StrictMono (contract (A := A) (B := B)) := by
  intro p q hpq
  have hlt : p.asIdeal < q.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal p q).mpr hpq
  haveI := p.isPrime
  have := Ideal.IsIntegral.comap_lt_comap (R := A) hlt
  exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp this

theorem le_dim : ringKrullDim B ≤ ringKrullDim A :=
  krullDim_le_of_strictMono _ contract_strictMono

theorem exists_lift (hinj : Function.Injective (algebraMap A B)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum A)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum B), q.length = n ∧
        q.last.asIdeal.comap (algebraMap A B) = p.last.asIdeal := by
  intro n
  induction n with
  | zero =>
    intro p hp
    haveI := p.last.isPrime
    have hbot : (⊥ : Ideal B).comap (algebraMap A B) ≤ p.last.asIdeal := by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal ⊥ hbot
    exact ⟨RelSeries.singleton _ ⟨Q, hQp⟩, rfl, by simpa using hQ⟩
  | succ n ih =>
    intro p hp
    have hpos : p.length ≠ 0 := by omega
    obtain ⟨q', hq'len, hq'⟩ := ih p.eraseLast (by simp [hp])
    have hrel : p.eraseLast.last < p.last := RelSeries.eraseLast_last_rel_last p hpos
    have hrelI : p.eraseLast.last.asIdeal < p.last.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hrel
    haveI := p.last.isPrime
    haveI := q'.last.isPrime
    have hle : q'.last.asIdeal.comap (algebraMap A B) ≤ p.last.asIdeal := by
      rw [hq']; exact hrelI.le
    obtain ⟨Q, hQge, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal q'.last.asIdeal hle
    have hlt : q'.last < ⟨Q, hQp⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine lt_of_le_of_ne hQge ?_
      intro heq
      apply hrelI.ne
      rw [← hq', ← hQ]
      exact congrArg _ heq
    refine ⟨q'.snoc ⟨Q, hQp⟩ hlt, by simp [hq'len], ?_⟩
    simpa using hQ

theorem dim_le (hinj : Function.Injective (algebraMap A B)) : ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hq, -⟩ := exists_lift hinj p.length p rfl
  exact le_iSup_of_le q (by rw [hq])

end KFRDDim

namespace KFRD

variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] [Module R X]

theorem length_quot_eq_add (S E : Submodule R X) (h : S ≤ E) :
    Module.length R (X ⧸ S) = Module.length R (↥E ⧸ S.comap E.subtype) + Module.length R (X ⧸ E) := by
  let φ : ↥E →ₗ[R] X ⧸ S := S.mkQ.comp E.subtype
  have hker : LinearMap.ker φ = S.comap E.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range φ = E.map S.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have e1 : (↥E ⧸ S.comap E.subtype) ≃ₗ[R] ↥(E.map S.mkQ) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))
  have e2 : ((X ⧸ S) ⧸ E.map S.mkQ) ≃ₗ[R] X ⧸ E := Submodule.quotientQuotientEquivQuotient S E h
  rw [Module.length_eq_add_of_exact (E.map S.mkQ).subtype (E.map S.mkQ).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _), e1.length_eq, e2.length_eq]

theorem length_quotient_maximalIdeal_sq (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.length R (R ⧸ maximalIdeal R ^ 2) = 1 + ((maximalIdeal R).spanFinrank : ℕ∞) := by
  rw [length_quot_eq_add (X := R) (maximalIdeal R ^ 2) (maximalIdeal R) (Ideal.pow_le_self two_ne_zero), add_comm]
  congr 1
  · haveI : IsSimpleModule R (R ⧸ maximalIdeal R) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
    exact Module.length_eq_one R _
  ·
    have hker : Submodule.comap (maximalIdeal R).subtype (maximalIdeal R ^ 2) =
        ((maximalIdeal R) • ⊤ : Submodule R ↥(maximalIdeal R)) := by
      ext x
      rw [Submodule.mem_comap, Submodule.subtype_apply, ← Ideal.toCotangent_eq_zero]
      exact Submodule.Quotient.mk_eq_zero _
    let e : (↥(maximalIdeal R) ⧸ Submodule.comap (maximalIdeal R).subtype (maximalIdeal R ^ 2)) ≃ₗ[R] CotangentSpace R :=
      Submodule.quotEquivOfEq _ _ hker
    rw [e.length_eq, Module.length_eq_of_surjective (S := R) (R := ResidueField R) (M := CotangentSpace R)
      IsLocalRing.residue_surjective, Module.length_eq_finrank, ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]

theorem core (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (B' : Type v) [CommRing B'] [IsLocalRing B'] [IsNoetherianRing B'] [Algebra B B'] [Module.Finite B B'] [FaithfulSMul B B']
    [Algebra.Etale B B'] :
    (maximalIdeal B).spanFinrank = (maximalIdeal B').spanFinrank ∧ ringKrullDim B = ringKrullDim B' := by
  classical
  haveI : Algebra.IsIntegral B B' := inferInstance
  haveI hloc : IsLocalHom (algebraMap B B') := by
    constructor
    intro x hx
    by_contra hnu
    have hxm : x ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hcomax : ((maximalIdeal B').comap (algebraMap B B')).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B')
    have heq : (maximalIdeal B').comap (algebraMap B B') = maximalIdeal B := IsLocalRing.eq_maximalIdeal hcomax
    have : algebraMap B B' x ∈ maximalIdeal B' := by rw [← Ideal.mem_comap, heq]; exact hxm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hx
  have hm : (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' := Algebra.FormallyUnramified.map_maximalIdeal
  constructor
  ·
    have h1 := IsLocalRing.length_baseChange B B' (B ⧸ maximalIdeal B ^ 2)
    have h2 : Module.length B' (B' ⧸ (maximalIdeal B).map (algebraMap B B')) = 1 := by
      rw [hm]
      haveI : IsSimpleModule B' (B' ⧸ maximalIdeal B') :=
        isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal B'))
      exact Module.length_eq_one B' _
    have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := B) B' (maximalIdeal B ^ 2)).toLinearEquiv
    rw [h2, mul_one, ← e.length_eq, Ideal.map_pow, hm, length_quotient_maximalIdeal_sq, length_quotient_maximalIdeal_sq] at h1
    have h4 : ((maximalIdeal B').spanFinrank : ℕ∞) = (maximalIdeal B).spanFinrank :=
      ENat.add_right_injective_of_ne_top ENat.one_ne_top h1
    exact_mod_cast h4.symm
  · exact le_antisymm (KFRDDim.dim_le (FaithfulSMul.algebraMap_injective B B')) KFRDDim.le_dim

theorem ascent (B : Type u) [CommRing B] [IsRegularLocalRing B]
    (B' : Type v) [CommRing B'] [IsLocalRing B'] [Algebra B B'] [Module.Finite B B'] [FaithfulSMul B B']
    [Algebra.Etale B B'] : IsRegularLocalRing B' := by
  haveI : IsNoetherianRing B := inferInstance
  haveI : IsLocalRing B := inferInstance
  haveI : IsNoetherianRing B' := isNoetherian_of_tower B (inferInstance : IsNoetherian B B')
  obtain ⟨hsf, hd⟩ := core B B'
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hsf, ← hd]
  exact le_of_eq ((isRegularLocalRing_iff B).mp inferInstance)

end KFRD

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open IsLocalRing Polynomial

namespace KFRD2

theorem adjoinRoot_X_pow_sub_C_structure
    {R' : Type*} [CommRing R'] [IsRegularLocalRing R'] [IsDomain R'] (hdim : ringKrullDim R' ≤ 2)
    {t : R'} (ht : t ∈ IsLocalRing.maximalIdeal R') (ht2 : t ∉ IsLocalRing.maximalIdeal R' ^ 2) {e : ℕ} (he : 0 < e) :
    let f : Polynomial R' := Polynomial.X ^ e - Polynomial.C t
    IsDomain (AdjoinRoot f) ∧ Prime (AdjoinRoot.root f) ∧
      AdjoinRoot.root f ^ e = algebraMap R' (AdjoinRoot f) t ∧
      ringKrullDim (AdjoinRoot f) ≤ 2 ∧ IsRegularLocalRing (AdjoinRoot f) := by
  intro f
  classical
  haveI : IsNoetherianRing R' := inferInstance
  haveI : IsLocalRing R' := inferInstance
  have hfm : f.Monic := monic_X_pow_sub_C t he.ne'
  have hfdeg : f.natDegree = e := natDegree_X_pow_sub_C

  have ht0 : t ≠ 0 := fun h => ht2 (by rw [h]; exact Ideal.zero_mem _)
  have htirr : Irreducible t := by
    refine ⟨fun hu => (IsLocalRing.mem_maximalIdeal _).mp ht hu, fun a b hab => ?_⟩
    by_contra hnn
    push Not at hnn
    apply ht2
    rw [hab, pow_two]
    exact Ideal.mul_mem_mul ((IsLocalRing.mem_maximalIdeal _).mpr hnn.1) ((IsLocalRing.mem_maximalIdeal _).mpr hnn.2)

  haveI hufd : UniqueFactorizationMonoid R' := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R' hdim
  have heis : f.IsEisensteinAt (maximalIdeal R') := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hfm.leadingCoeff]; exact fun h => (IsLocalRing.maximalIdeal.isMaximal R').ne_top ((Ideal.eq_top_iff_one _).mpr h)
    · intro n hn
      rw [hfdeg] at hn
      show (X ^ e - C t : R'[X]).coeff n ∈ maximalIdeal R'
      rw [coeff_sub, coeff_X_pow, coeff_C]
      by_cases h0 : n = 0
      · subst h0
        rw [if_neg (by omega), if_pos rfl, zero_sub]; exact (maximalIdeal R').neg_mem ht
      · rw [if_neg (by omega), if_neg h0, sub_zero]; exact Ideal.zero_mem _
    · show (X ^ e - C t : R'[X]).coeff 0 ∉ maximalIdeal R' ^ 2
      rw [coeff_sub, coeff_X_pow, coeff_C, if_neg (by omega), if_pos rfl, zero_sub]
      exact fun h => ht2 (by simpa using (maximalIdeal R' ^ 2).neg_mem h)
  have hirr : Irreducible f := heis.irreducible inferInstance hfm.isPrimitive (by rw [hfdeg]; exact he)
  have hprime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  haveI hdom' : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hprime

  obtain ⟨hreg', hdim', -, -⟩ := IsRegularLocalRing.adjoinRoot_X_pow_sub_C_of_notMem_sq (R := R') ht ht2 he

  have hroote : AdjoinRoot.root f ^ e = algebraMap R' (AdjoinRoot f) t := by
    have h0 : f.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) = 0 := AdjoinRoot.eval₂_root f
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    exact h0

  have htprime : Prime t := UniqueFactorizationMonoid.irreducible_iff_prime.mp htirr
  haveI : (Ideal.span {t}).IsPrime := (Ideal.span_singleton_prime ht0).mpr htprime
  haveI : IsDomain (R' ⧸ Ideal.span {t}) := (Ideal.Quotient.isDomain_iff_prime _).mpr inferInstance
  let q : R' →+* R' ⧸ Ideal.span {t} := Ideal.Quotient.mk _
  have hq0 : f.eval₂ q 0 = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow he.ne', zero_sub, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
  let π : AdjoinRoot f →+* R' ⧸ Ideal.span {t} := AdjoinRoot.lift q 0 hq0
  have hπroot : π (AdjoinRoot.root f) = 0 := AdjoinRoot.lift_root hq0
  have hπof : ∀ r : R', π (AdjoinRoot.of f r) = q r := fun r => AdjoinRoot.lift_of hq0
  have hker : RingHom.ker π = Ideal.span {AdjoinRoot.root f} := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z

      have hp : p = X * p.divX + C (p.coeff 0) := (X_mul_divX_add p).symm
      have hz' : q (p.coeff 0) = 0 := by
        rw [hp, map_add, map_mul, AdjoinRoot.mk_X, map_add, map_mul, hπroot, zero_mul, zero_add, AdjoinRoot.mk_C, hπof] at hz
        exact hz
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hz'
      obtain ⟨c, hc⟩ := hz'
      have hroote' : AdjoinRoot.root f ^ e = AdjoinRoot.of f t := by rw [hroote, AdjoinRoot.algebraMap_eq]
      rw [hp, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, hc, map_mul, ← hroote', Ideal.mem_span_singleton]
      refine (Dvd.intro _ rfl).add ?_
      exact Dvd.dvd.mul_right (dvd_pow_self _ he.ne') _
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]; exact hπroot
  have hroot0 : AdjoinRoot.root f ≠ 0 := by
    intro h
    apply ht0
    have : algebraMap R' (AdjoinRoot f) t = 0 := by rw [← hroote, h, zero_pow he.ne']
    refine (AdjoinRoot.of.injective_of_degree_ne_zero (f := f) ?_) (by rwa [map_zero])
    rw [degree_eq_natDegree hfm.ne_zero, hfdeg]; exact_mod_cast he.ne'
  have hrootprime : Prime (AdjoinRoot.root f) := by
    rw [← Ideal.span_singleton_prime hroot0, ← hker]
    exact RingHom.ker_isPrime π
  exact ⟨hdom', hrootprime, hroote, by rw [hdim']; exact hdim, hreg'⟩

theorem quotient_adjoinRoot_span_root_equiv {R : Type*} [CommRing R] (t : R) {e : ℕ} (he : 0 < e) :
    let f : Polynomial R := Polynomial.X ^ e - Polynomial.C t
    Nonempty ((AdjoinRoot f ⧸ Ideal.span {AdjoinRoot.root f}) ≃+* R ⧸ Ideal.span {t}) := by
  intro f
  classical
  let q : R →+* R ⧸ Ideal.span {t} := Ideal.Quotient.mk _
  have hq0 : f.eval₂ q 0 = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow he.ne', zero_sub, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
  let π : AdjoinRoot f →+* R ⧸ Ideal.span {t} := AdjoinRoot.lift q 0 hq0
  have hπroot : π (AdjoinRoot.root f) = 0 := AdjoinRoot.lift_root hq0
  have hπof : ∀ r : R, π (AdjoinRoot.of f r) = q r := fun r => AdjoinRoot.lift_of hq0
  have hroote : AdjoinRoot.root f ^ e = AdjoinRoot.of f t := by
    have h0 : f.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) = 0 := AdjoinRoot.eval₂_root f
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    exact h0
  have hker : RingHom.ker π = Ideal.span {AdjoinRoot.root f} := by
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
      have hp : p = X * p.divX + C (p.coeff 0) := (X_mul_divX_add p).symm
      have hz' : q (p.coeff 0) = 0 := by
        rw [hp, map_add, map_mul, AdjoinRoot.mk_X, map_add, map_mul, hπroot, zero_mul, zero_add, AdjoinRoot.mk_C, hπof] at hz
        exact hz
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hz'
      obtain ⟨c, hc⟩ := hz'
      rw [hp, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, hc, map_mul, ← hroote, Ideal.mem_span_singleton]
      refine (Dvd.intro _ rfl).add ?_
      exact Dvd.dvd.mul_right (dvd_pow_self _ he.ne') _
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]; exact hπroot
  have hsurj : Function.Surjective π := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨AdjoinRoot.of f r, hπof r⟩
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)⟩

end KFRD2

set_option maxHeartbeats 3200000

namespace KFS6

theorem eq_span_of_le_span_of_prime {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    (T : A) (hT : Prime T) (P : Ideal A) [P.IsPrime] (hP0 : P ≠ ⊥) (hle : P ≤ Ideal.span {T}) :
    P = Ideal.span {T} := by
  classical
  refine le_antisymm hle ?_
  rw [Ideal.span_singleton_le_iff_mem]
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0

  have hfin : FiniteMultiplicity T x := FiniteMultiplicity.of_not_isUnit hT.not_unit hx0
  obtain ⟨y, hy, hTy⟩ : ∃ y : A, x = T ^ multiplicity T x * y ∧ ¬ T ∣ y := by
    obtain ⟨y, hy⟩ := pow_multiplicity_dvd T x
    refine ⟨y, hy, fun hdvd => ?_⟩
    have : T ^ (multiplicity T x + 1) ∣ x :=
      calc T ^ (multiplicity T x + 1) = T ^ multiplicity T x * T := pow_succ _ _
        _ ∣ T ^ multiplicity T x * y := mul_dvd_mul_left _ hdvd
        _ = x := hy.symm
    exact hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _) this
  have hyP : y ∉ P := fun h => hTy (Ideal.mem_span_singleton.mp (hle h))
  rw [hy] at hxP
  rcases (Ideal.IsPrime.mem_or_mem ‹P.IsPrime› hxP) with h | h
  · exact Ideal.IsPrime.mem_of_pow_mem ‹P.IsPrime› _ h
  · exact absurd h hyP

theorem exists_prime_comap_span_eq_span
    {B A : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [UniqueFactorizationMonoid B]
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A]
    [Algebra B A] [Module.Finite B A] [FaithfulSMul B A] [Module.Flat B A]
    (T : A) (hT : Prime T) (h0 : (Ideal.span {T}).comap (algebraMap B A) ≠ ⊥) :
    ∃ θ : B, Prime θ ∧ (Ideal.span {T}).comap (algebraMap B A) = Ideal.span {θ} := by
  classical
  haveI hTp : (Ideal.span {T}).IsPrime := (Ideal.span_singleton_prime hT.ne_zero).mpr hT
  set Q : Ideal B := (Ideal.span {T}).comap (algebraMap B A) with hQ
  haveI hQp : Q.IsPrime := Ideal.IsPrime.comap _
  haveI : (Ideal.span {T}).LiesOver Q := ⟨by rw [Ideal.under_def, hQ]⟩

  have hmin : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → P ≤ Q → P = Q := by
    intro P hP hP0 hPQ
    haveI := hP
    obtain ⟨P', hP'le, hP'p, hP'over⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P) (q := Q) (Ideal.span {T}) hPQ
    haveI := hP'p
    have hP'0 : P' ≠ ⊥ := by
      intro h
      apply hP0
      rw [hP'over.over, h, Ideal.under_bot]
    have hP'eq : P' = Ideal.span {T} := eq_span_of_le_span_of_prime T hT P' hP'0 hP'le
    rw [hP'over.over, hP'eq, Ideal.under_def]

  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hxnu : ¬ IsUnit x := fun hu => hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ hxQ hu)
  obtain ⟨p, hp, -, hpQ⟩ : ∃ p : B, Prime p ∧ p ∣ x ∧ p ∈ Q := by

    have key : ∀ (s : Multiset B), (∀ q ∈ s, Prime q) → s.prod ∈ Q → ∃ q ∈ s, q ∈ Q := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _ h; exact absurd (Ideal.eq_top_of_isUnit_mem _ (by simpa using h) isUnit_one) hQp.ne_top
      | cons a s ih =>
        intro hs hprod
        rw [Multiset.prod_cons] at hprod
        rcases hQp.mem_or_mem hprod with ha | hs'
        · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
        · obtain ⟨q, hq, hqQ⟩ := ih (fun q hq => hs q (Multiset.mem_cons_of_mem hq)) hs'
          exact ⟨q, Multiset.mem_cons_of_mem hq, hqQ⟩
    obtain ⟨s, hs, hassoc⟩ := UniqueFactorizationMonoid.exists_prime_factors x hx0
    obtain ⟨u, hu⟩ := hassoc
    have hsprod : s.prod ∈ Q := by
      have : x * (u⁻¹ : Bˣ) = s.prod := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [← this]; exact Ideal.mul_mem_right _ _ hxQ
    obtain ⟨q, hqs, hqQ⟩ := key s hs hsprod
    refine ⟨q, hs q hqs, ?_, hqQ⟩
    rw [← hu]
    exact (Multiset.dvd_prod hqs).mul_right _
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  refine ⟨p, hp, (hmin (Ideal.span {p}) inferInstance ?_ ?_).symm⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero
  · rw [Ideal.span_singleton_le_iff_mem]; exact hpQ

end KFS6

namespace BDescRD

open IsLocalRing

theorem exists_algebraMap_eq_mul_not_dvd_of_etale
    {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A]
    [Module.Finite B A] [FaithfulSMul B A] [Algebra.Etale B A]
    (θ : B) (T : A) (hT : Prime T)
    (hcomap : (Ideal.span {T}).comap (algebraMap B A) = Ideal.span {θ}) :
    ∃ c : A, algebraMap B A θ = T * c ∧ ¬ (T ∣ c) := by
  classical
  set 𝔓 : Ideal A := Ideal.span ({T} : Set A) with h𝔓
  set 𝔭 : Ideal B := Ideal.span ({θ} : Set B) with h𝔭
  haveI h𝔓p : 𝔓.IsPrime := (Ideal.span_singleton_prime hT.ne_zero).mpr hT
  haveI h𝔓𝔭 : 𝔓.LiesOver 𝔭 := ⟨by rw [Ideal.under_def, hcomap]⟩
  haveI h𝔭p : 𝔭.IsPrime := by rw [h𝔓𝔭.over]; exact Ideal.IsPrime.under B 𝔓

  have hθ𝔓 : algebraMap B A θ ∈ 𝔓 := by
    have : θ ∈ 𝔓.comap (algebraMap B A) := by rw [hcomap]; exact Ideal.mem_span_singleton_self θ
    exact this
  obtain ⟨c, hc⟩ : T ∣ algebraMap B A θ := Ideal.mem_span_singleton.mp hθ𝔓
  refine ⟨c, hc, ?_⟩

  haveI : Algebra.FormallyUnramified B A := inferInstance
  haveI : Algebra.FormallyUnramified A (Localization.AtPrime 𝔓) :=
    Algebra.FormallyUnramified.of_isLocalization 𝔓.primeCompl
  haveI hunr : Algebra.IsUnramifiedAt B 𝔓 := Algebra.FormallyUnramified.comp B A (Localization.AtPrime 𝔓)
  letI := Localization.AtPrime.algebraOfLiesOver 𝔭 𝔓
  have hmap : 𝔭.map (algebraMap B (Localization.AtPrime 𝔓)) = maximalIdeal (Localization.AtPrime 𝔓) :=
    ((Algebra.isUnramifiedAt_iff_map_eq B 𝔭 𝔓).mp hunr).2

  have hTmax : algebraMap A (Localization.AtPrime 𝔓) T ∈ maximalIdeal (Localization.AtPrime 𝔓) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self T)
  rw [← hmap, IsScalarTower.algebraMap_eq B A (Localization.AtPrime 𝔓), ← Ideal.map_map, h𝔭,
    Ideal.map_span, Set.image_singleton] at hTmax
  rw [IsLocalization.mem_map_algebraMap_iff 𝔓.primeCompl] at hTmax
  obtain ⟨⟨⟨x, hx⟩, ⟨s, hs⟩⟩, hxs⟩ := hTmax
  simp only at hxs
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx

  rw [← map_mul] at hxs
  obtain ⟨⟨u, hu⟩, hu'⟩ := (IsLocalization.eq_iff_exists 𝔓.primeCompl (Localization.AtPrime 𝔓)).mp hxs
  simp only at hu'

  intro hTc
  obtain ⟨d, rfl⟩ := hTc
  rw [hc] at hu'

  have h1 : T * (u * s) = T * (u * a * T * d) := by
    have := hu'; linear_combination this
  have h2 : u * s = u * a * T * d := mul_left_cancel₀ hT.ne_zero h1
  have h3 : T ∣ u * s := ⟨u * a * d, by rw [h2]; ring⟩
  rcases hT.dvd_or_dvd h3 with h | h
  · exact hu (Ideal.mem_span_singleton.mpr h)
  · exact hs (Ideal.mem_span_singleton.mpr h)

end BDescRD

namespace BDescRD

private theorem aux_unit_mul_pow {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    (θ : B) (hθ : Prime θ) (s : B) (hs : s ≠ 0) (hall : ∀ p : B, Prime p → p ∣ s → θ ∣ p) :
    ∃ (k : ℕ) (v : B), IsUnit v ∧ s = v * θ ^ k := by
  classical
  revert hs hall
  refine UniqueFactorizationMonoid.induction_on_prime s ?_ ?_ ?_
  · intro h; exact absurd rfl h
  · intro u hu _ _; exact ⟨0, u, hu, by simp⟩
  · intro a p ha0 hp ih _ hall
    have hθp : θ ∣ p := hall p hp (dvd_mul_right p a)
    obtain ⟨w, hw⟩ := hθ.associated_of_dvd hp hθp
    obtain ⟨k, v, hv, hav⟩ := ih ha0 (fun q hq hqa => hall q hq (Dvd.dvd.mul_left hqa p))
    exact ⟨k + 1, v * (w : B), hv.mul (Units.isUnit w), by rw [← hw, hav]; ring⟩

theorem exists_isUnit_eq_mul_pow_of_algebraMap_eq
    {B A : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Algebra B A]
    (hloc : IsLocalHom (algebraMap B A))
    (θ : B) (hθ : Prime θ) (T : A) (hT : Prime T)
    (hcomap : (Ideal.span {T}).comap (algebraMap B A) = Ideal.span {θ})
    (c : A) (hc : algebraMap B A θ = T * c) (hTc : ¬ T ∣ c)
    (s : B) (e : ℕ) (w : A) (hw : IsUnit w) (hs : algebraMap B A s = w * T ^ e) :
    ∃ v : B, IsUnit v ∧ s = v * θ ^ e := by
  classical
  haveI := hloc
  have hTu : ¬ IsUnit T := hT.not_unit

  have hs0 : s ≠ 0 := by
    intro h0
    have : w * T ^ e = 0 := by rw [← hs, h0, map_zero]
    rcases mul_eq_zero.mp this with h | h
    · exact hw.ne_zero h
    · exact hT.ne_zero (pow_eq_zero_iff'.mp h).1

  have hdown : ∀ x : B, T ∣ algebraMap B A x → θ ∣ x := by
    intro x hx
    have : x ∈ (Ideal.span ({T} : Set A)).comap (algebraMap B A) := by
      rw [Ideal.mem_comap]; exact Ideal.mem_span_singleton.mpr hx
    rw [hcomap] at this
    exact Ideal.mem_span_singleton.mp this

  have hall : ∀ p : B, Prime p → p ∣ s → θ ∣ p := by
    intro p hp hps
    apply hdown
    by_contra hTq
    set q : A := algebraMap B A p with hq
    have hq0 : q ≠ 0 := fun h => hTq (by rw [h]; exact dvd_zero T)
    have hqdvd : q ∣ w * T ^ e := by rw [← hs, hq]; exact map_dvd (algebraMap B A) hps

    have hallq : ∀ r : A, Prime r → r ∣ q → T ∣ r := by
      intro r hr hrq
      have hr' : r ∣ w * T ^ e := hrq.trans hqdvd
      rcases hr.dvd_or_dvd hr' with h | h
      · exact absurd (isUnit_of_dvd_unit h hw) hr.not_unit
      · have hrT : r ∣ T := hr.dvd_of_dvd_pow h
        exact (hr.associated_of_dvd hT hrT).symm.dvd
    obtain ⟨a, v, hv, hqv⟩ := aux_unit_mul_pow T hT q hq0 hallq
    rcases Nat.eq_zero_or_pos a with ha | ha
    ·
      have hqu : IsUnit q := by rw [hqv, ha, pow_zero, mul_one]; exact hv
      exact hp.not_unit (IsLocalHom.map_nonunit p hqu)
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      exact hTq ⟨v * T ^ a', by rw [hqv]; ring⟩
  obtain ⟨k, v, hv, hsv⟩ := aux_unit_mul_pow θ hθ s hs0 hall

  have hv' : IsUnit (algebraMap B A v) := hv.map _
  have heq : algebraMap B A v * c ^ k * T ^ k = w * T ^ e := by
    rw [← hs, hsv, map_mul, map_pow, hc]; ring
  have hk : k = e := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    ·
      obtain ⟨d, hd⟩ : ∃ d, e = k + (d + 1) := ⟨e - k - 1, by omega⟩
      have h1 : T ^ k * (algebraMap B A v * c ^ k) = T ^ k * (w * T ^ (d + 1)) := by
        have : w * T ^ e = T ^ k * (w * T ^ (d + 1)) := by rw [hd, pow_add]; ring
        rw [← this, ← heq]; ring
      have h2 : algebraMap B A v * c ^ k = w * T ^ (d + 1) := mul_left_cancel₀ (pow_ne_zero k hT.ne_zero) h1
      have h3 : T ∣ algebraMap B A v * c ^ k := ⟨w * T ^ d, by rw [h2]; ring⟩
      rcases hT.dvd_or_dvd h3 with h | h
      · exact hTu (isUnit_of_dvd_unit h hv')
      · exact hTc (hT.dvd_of_dvd_pow h)
    ·
      obtain ⟨d, hd⟩ : ∃ d, k = e + (d + 1) := ⟨k - e - 1, by omega⟩
      have h1 : T ^ e * (algebraMap B A v * c ^ k * T ^ (d + 1)) = T ^ e * w := by
        have : algebraMap B A v * c ^ k * T ^ k = T ^ e * (algebraMap B A v * c ^ k * T ^ (d + 1)) := by
          rw [hd, pow_add, pow_add]; ring
        rw [← this, heq]; ring
      have h2 : algebraMap B A v * c ^ k * T ^ (d + 1) = w := mul_left_cancel₀ (pow_ne_zero e hT.ne_zero) h1
      have h3 : T ∣ w := ⟨algebraMap B A v * c ^ k * T ^ d, by rw [← h2]; ring⟩
      exact hTu (isUnit_of_dvd_unit h3 hw)
  exact ⟨v, hv, by rw [hsv, hk]⟩

end BDescRD

open IsLocalRing Polynomial

namespace L1BRD

theorem henselianLocalRing_of_isAdicComplete (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R := by
  refine HenselianLocalRing.mk fun f hf a₀ h₁ h₂ => ?_
  exact HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _)

set_option maxHeartbeats 3200000 in

theorem exists_unit_pow_mul_algebraMap_eq
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    {B : Type*} [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (e : ℕ) (he : 0 < e) (heB : IsUnit (e : B)) (v : B) (hv : IsUnit v) :
    ∃ (r₀ : Rˣ) (c : B), IsUnit c ∧ c ^ e * algebraMap R B (r₀ : R) = v := by
  classical
  haveI : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete R
  haveI : HenselianLocalRing B := HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R) (S := B)
  haveI : Algebra.IsIntegral R B := inferInstance
  haveI : IsLocalHom (algebraMap R B) := Algebra.IsIntegral.isLocalHom R B
  obtain ⟨r, hr⟩ := hres v

  have hru : IsUnit (algebraMap R B r) := by
    by_contra hnu
    apply (mem_maximalIdeal _).mp ?_ hv
    have : v = (v - algebraMap R B r) + algebraMap R B r := by ring
    rw [this]
    exact Ideal.add_mem _ hr ((mem_maximalIdeal _).mpr hnu)
  obtain ⟨r₀, hr₀⟩ := (IsLocalHom.map_nonunit r hru)

  set w : B := v * algebraMap R B ((r₀⁻¹ : Rˣ) : R) with hw
  have hw1 : w - 1 ∈ maximalIdeal B := by
    have hinv : algebraMap R B r * algebraMap R B ((r₀⁻¹ : Rˣ) : R) = 1 := by
      rw [← map_mul, ← hr₀, Units.mul_inv, map_one]
    have : w - 1 = (v - algebraMap R B r) * algebraMap R B ((r₀⁻¹ : Rˣ) : R) := by
      rw [hw, sub_mul, hinv]
    rw [this]; exact Ideal.mul_mem_right _ _ hr

  have hmonic : (X ^ e - C w : B[X]).Monic := monic_X_pow_sub_C w (Nat.pos_iff_ne_zero.mp he)
  have h1 : Polynomial.eval 1 (X ^ e - C w : B[X]) ∈ maximalIdeal B := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    have : (1 : B) - w = -(w - 1) := by ring
    rw [this]; exact (maximalIdeal B).neg_mem hw1
  have h2 : IsUnit (Polynomial.eval 1 (Polynomial.derivative (X ^ e - C w : B[X]))) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow,
      mul_one]
    exact heB
  obtain ⟨c, hc, hc1⟩ := HenselianLocalRing.is_henselian _ hmonic 1 h1 h2
  have hce : c ^ e = w := by
    have := hc; simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at this; exact this
  have hcu : IsUnit c := by
    by_contra hnu

    have h1m : (1 : B) ∈ maximalIdeal B := by
      have : (1 : B) = c - (c - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ ((mem_maximalIdeal _).mpr hnu) hc1
    exact (mem_maximalIdeal _).mp h1m isUnit_one
  refine ⟨r₀, c, hcu, ?_⟩
  rw [hce, hw, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

end L1BRD

open IsLocalRing Polynomial
open scoped TensorProduct

namespace L1BRDB

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem main_prep
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (hdim : ringKrullDim R ≤ 2)
    (s : R) (hs : s ∈ maximalIdeal R) (hs2 : s ∉ maximalIdeal R ^ 2)
    (e : ℕ) (he : 0 < e)
    (R' : Type*) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R'] [Algebra.Etale R R']
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (u' : R'ˣ)
    (e' : R' ⊗[R] B ≃ₐ[R'] AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) :
    ∃ (ι : B →ₐ[R] AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])), Function.Injective ι ∧
      (∀ b : B, ι b = e' (1 ⊗ₜ b)) ∧
      IsDomain (AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) ∧
      Prime (AdjoinRoot.root (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) ∧
      AdjoinRoot.root (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X]) ^ e =
        algebraMap R' _ ((u' : R') * algebraMap R R' s) ∧
      (letI : Algebra B (AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) := ι.toRingHom.toAlgebra
       Module.Finite B (AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) ∧
       Algebra.Etale B (AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) ∧
       Module.Flat B (AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X]))) ∧
      UniqueFactorizationMonoid B ∧ IsRegularLocalRing B ∧ ringKrullDim B ≤ 2 ∧
      IsRegularLocalRing (AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) ∧
      ringKrullDim (AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) ≤ 2 := by
  classical
  set A' := AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X]) with hA'
  haveI : Nontrivial R' := inferInstance
  haveI : Module.FaithfullyFlat R R' := inferInstance
  haveI : IsNoetherianRing R := inferInstance
  haveI : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim

  haveI : IsLocalRing (R ⊗[R] R') := (Algebra.TensorProduct.lid R R').symm.toRingEquiv.isLocalRing
  haveI : IsDomain R' := by
    have := (Algebra.Etale.isDomain_and_isIntegrallyClosed_tensorProduct_of_isLocalRing (W := R) R R').1
    exact (Algebra.TensorProduct.lid R R').symm.injective.isDomain (Algebra.TensorProduct.lid R R').symm.toRingHom
  haveI hR'reg : IsRegularLocalRing R' := KFRD.ascent R R'
  haveI : IsNoetherianRing R' := inferInstance
  have hdimR' : ringKrullDim R' ≤ 2 := by rw [← (KFRD.core R R').2]; exact hdim

  obtain ⟨hs', hs'2⟩ := L1BRDA.mem_and_notMem_sq_of_etale R' s hs hs2
  have ht : (u' : R') * algebraMap R R' s ∈ maximalIdeal R' := Ideal.mul_mem_left _ _ hs'
  have ht2 : (u' : R') * algebraMap R R' s ∉ maximalIdeal R' ^ 2 := fun h => hs'2 (by
    have := Ideal.mul_mem_left (maximalIdeal R' ^ 2) ((u'⁻¹ : R'ˣ) : R') h
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
  obtain ⟨hA'dom, hTprime, hTe, hdimA', hA'reg⟩ := KFRD2.adjoinRoot_X_pow_sub_C_structure hdimR' ht ht2 he
  haveI := hA'dom
  haveI := hA'reg

  let e'' : B ⊗[R] R' ≃ₐ[R] A' := (Algebra.TensorProduct.comm R B R').trans (e'.restrictScalars R)
  let ι : B →ₐ[R] A' := e''.toAlgHom.comp Algebra.TensorProduct.includeLeft
  have hι : ∀ b : B, ι b = e' (1 ⊗ₜ b) := fun b => by
    show e' (Algebra.TensorProduct.comm R B R' (b ⊗ₜ 1)) = _
    rw [Algebra.TensorProduct.comm_tmul]
  have hιinj : Function.Injective ι := by
    intro b₁ b₂ h
    rw [hι, hι] at h
    exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := R') B (e'.injective h)

  letI algBA : Algebra B A' := ι.toRingHom.toAlgebra
  let eB : B ⊗[R] R' ≃ₐ[B] A' := AlgEquiv.ofRingEquiv (f := e''.toRingEquiv) (fun b => rfl)
  haveI : Module.Finite B A' := Module.Finite.equiv eB.toLinearEquiv
  haveI : Algebra.Etale B A' := Algebra.Etale.of_equiv eB
  haveI : Module.Flat B A' := Module.Flat.of_linearEquiv eB.toLinearEquiv.symm
  haveI : FaithfulSMul B A' := (faithfulSMul_iff_algebraMap_injective B A').mpr hιinj

  haveI hBreg : IsRegularLocalRing B := IsRegularLocalRing.of_etale_of_moduleFinite B A'
  have hdimB : ringKrullDim B ≤ 2 := by rw [(KFRD.core B A').2]; exact hdimA'
  haveI : UniqueFactorizationMonoid B := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two B hdimB
  exact ⟨ι, hιinj, hι, hA'dom, hTprime, hTe, ⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, hBreg, hdimB,
    hA'reg, hdimA'⟩

end L1BRDB

open IsLocalRing Polynomial
open scoped TensorProduct

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsDomain R] [IsAdicComplete (maximalIdeal R) R]
    (hdim : ringKrullDim R ≤ 2)
    (s : R) (hs : s ∈ maximalIdeal R) (hs2 : s ∉ maximalIdeal R ^ 2)
    (e : ℕ) (he : 0 < e) (heR : IsUnit (e : R))
    (R' : Type*) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.Finite R R'] [Module.Free R R'] [Algebra.Etale R R']
    (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (hres : ∀ b : B, ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B)
    (u' : R'ˣ)
    (e' : R' ⊗[R] B ≃ₐ[R'] AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X])) :
    ∃ (u : Rˣ) (θ : B), θ ^ e = algebraMap R B ((u : R) * s) := by
  classical
  set A' := AdjoinRoot (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X]) with hA'
  obtain ⟨ι, hιinj, hι, hA'dom, hT, hTe, hinst, hufd, hBreg, hdimB, hA'reg, hdimA'⟩ :=
    L1BRDB.main_prep hdim s hs hs2 e he R' B u' e'
  letI algBA : Algebra B A' := ι.toRingHom.toAlgebra
  obtain ⟨hfin, het, hflat⟩ := hinst
  haveI := hA'dom; haveI := hufd; haveI := hBreg; haveI := hA'reg; haveI := hfin; haveI := het; haveI := hflat
  haveI : FaithfulSMul B A' := (faithfulSMul_iff_algebraMap_injective B A').mpr hιinj
  haveI : IsNoetherianRing A' := inferInstance
  haveI : UniqueFactorizationMonoid A' := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two A' hdimA'
  have hloc : IsLocalHom (algebraMap B A') := Algebra.IsIntegral.isLocalHom B A'
  set T := AdjoinRoot.root (X ^ e - C ((u' : R') * algebraMap R R' s) : R'[X]) with hTdef
  set sB := algebraMap R B s with hsB

  have hιs : algebraMap B A' sB = algebraMap R' A' (algebraMap R R' s) := by
    show ι (algebraMap R B s) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R R' A']
  have hw : IsUnit (algebraMap R' A' ((u'⁻¹ : R'ˣ) : R')) := (Units.isUnit _).map _
  have hsA : algebraMap B A' sB = algebraMap R' A' ((u'⁻¹ : R'ˣ) : R') * T ^ e := by
    rw [hιs]
    calc algebraMap R' A' (algebraMap R R' s)
        = algebraMap R' A' ((u'⁻¹ : R'ˣ) : R') * (algebraMap R' A' ((u' : R') * algebraMap R R' s)) := by
          rw [← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
      _ = algebraMap R' A' ((u'⁻¹ : R'ˣ) : R') * T ^ e := by rw [← hTe]

  have hs0 : s ≠ 0 := fun h0 => hs2 (by rw [h0]; exact Ideal.zero_mem _)
  have hsB0 : sB ≠ 0 := fun h0 => hs0 ((faithfulSMul_iff_algebraMap_injective R B).mp inferInstance (h0.trans (map_zero _).symm))
  have h0 : (Ideal.span {T}).comap (algebraMap B A') ≠ ⊥ := by
    intro hbot
    apply hsB0
    have : sB ∈ (Ideal.span {T}).comap (algebraMap B A') := by
      rw [Ideal.mem_comap, hsA, Ideal.mem_span_singleton]
      exact dvd_mul_of_dvd_right (dvd_pow_self T (Nat.pos_iff_ne_zero.mp he)) _
    rw [hbot] at this
    exact (Submodule.mem_bot B).mp this
  obtain ⟨θ, hθ, hcomap⟩ := KFS6.exists_prime_comap_span_eq_span (B := B) (A := A') T hT h0

  obtain ⟨c, hc, hTc⟩ := BDescRD.exists_algebraMap_eq_mul_not_dvd_of_etale (B := B) (A := A') θ T hT hcomap
  obtain ⟨v, hv, hsv⟩ := BDescRD.exists_isUnit_eq_mul_pow_of_algebraMap_eq (B := B) (A := A') hloc θ hθ T hT hcomap c hc hTc
    sB e _ hw hsA

  have heB : IsUnit (e : B) := by have := heR.map (algebraMap R B); rwa [map_natCast] at this
  obtain ⟨r₀, d, hd, hdv⟩ := L1BRD.exists_unit_pow_mul_algebraMap_eq (R := R) (B := B) hres e he heB v hv
  refine ⟨r₀⁻¹, d * θ, ?_⟩
  have hr : algebraMap R B ((r₀⁻¹ : Rˣ) : R) * algebraMap R B (r₀ : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, ← hsB, hsv, ← hdv, mul_pow]
  calc d ^ e * θ ^ e = (algebraMap R B ((r₀⁻¹ : Rˣ) : R) * algebraMap R B (r₀ : R)) * (d ^ e * θ ^ e) := by rw [hr, one_mul]
    _ = algebraMap R B ((r₀⁻¹ : Rˣ) : R) * (d ^ e * algebraMap R B (r₀ : R) * θ ^ e) := by ring

end S_IsRegularLocalRing_exists_isUnit_pow_eq_mul_of_baseChange
end P2MW
export P2MW.S_IsRegularLocalRing_exists_isUnit_pow_eq_mul_of_baseChange (solution)

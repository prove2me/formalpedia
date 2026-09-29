-- Prove2me | solution 1 for NumberField.exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6d7f436d-bd0b-52a9-bb5f-2f86040f14d2

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceTransport
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false

namespace CycDepthProof

theorem eq_of_pow_eq_one_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] {Q : Ideal S} [hQ : Q.IsPrime] {k : ℕ}
    (hk : ((k : ℕ) : S) ∉ Q) {u w : S} (hu : u ^ k = 1) (hw : w ^ k = 1) (h : u - w ∈ Q) : u = w := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (by simp)
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  set t := u * w ^ k' with ht
  have htw : t * w = u := by rw [ht, mul_assoc, ← pow_succ, hw, mul_one]
  have htm : t ^ (k' + 1) = 1 := by
    rw [ht, mul_pow, hu, ← pow_mul, mul_comm k', pow_mul, hw, one_pow, mul_one]
  have hwQ : w ∉ Q := fun hwQ => hQ.ne_top ((Ideal.eq_top_iff_one _).2 (hw ▸ Q.pow_mem_of_mem hwQ _ k'.succ_pos))
  have ht1 : t - 1 ∈ Q := by
    have : (t - 1) * w ∈ Q := by rw [sub_mul, one_mul, htw]; exact h
    exact (hQ.mem_or_mem this).resolve_right hwQ
  have hgeom : (∑ i ∈ Finset.range (k' + 1), t ^ i) * (t - 1) = 0 := by rw [geom_sum_mul, htm, sub_self]
  rcases mul_eq_zero.1 hgeom with h0 | h0
  · exfalso
    apply hk
    have h1 : ∀ i, t ^ i - 1 ∈ Q := fun i => by
      have := sub_dvd_pow_sub_pow t 1 i
      rw [one_pow] at this
      exact Q.mem_of_dvd this ht1
    have h2 : ∑ i ∈ Finset.range (k' + 1), (t ^ i - 1) ∈ Q := Q.sum_mem fun i _ => h1 i
    rw [Finset.sum_sub_distrib, h0, Finset.sum_const, Finset.card_range, zero_sub, nsmul_eq_mul, mul_one] at h2
    simpa using Q.neg_mem_iff.1 h2
  · rw [sub_eq_zero] at h0
    rw [← htw, h0, one_mul]

section Cyc

variable (E : Type) [Field E] [NumberField E] (m : ℕ) [NeZero m]

local notation "F'" => CyclotomicField m E

scoped instance instIsGalois : IsGalois E F' := IsCyclotomicExtension.isGalois {m} E F'

scoped instance instIsMulCommutative : IsMulCommutative Gal(F'/E) := IsCyclotomicExtension.isMulCommutative {m} E F'

noncomputable def zi : 𝓞 F' := (IsCyclotomicExtension.zeta_spec m E F').toInteger

theorem zi_spec : IsPrimitiveRoot (zi E m) m := (IsCyclotomicExtension.zeta_spec m E F').toInteger_isPrimitiveRoot

theorem coe_zi : ((zi E m : 𝓞 F') : F') = IsCyclotomicExtension.zeta m E F' := rfl

variable {E m}

theorem pow_eq_pow_of_sub_mem {Q : Ideal (𝓞 F')} [Q.IsPrime] (hmQ : ((m : ℕ) : 𝓞 F') ∉ Q)
    {i j : ℕ} (h : zi E m ^ i - zi E m ^ j ∈ Q) : zi E m ^ i = zi E m ^ j :=
  eq_of_pow_eq_one_of_sub_mem hmQ (by rw [← pow_mul, mul_comm, pow_mul, (zi_spec E m).pow_eq_one, one_pow])
    (by rw [← pow_mul, mul_comm, pow_mul, (zi_spec E m).pow_eq_one, one_pow]) h

theorem coe_smul (σ : Gal(F'/E)) (x : 𝓞 F') : ((σ • x : 𝓞 F') : F') = σ (x : F') := rfl

theorem exists_smul_zi_eq_pow (σ : Gal(F'/E)) : ∃ k : ℕ, σ • zi E m = zi E m ^ k := by
  have h : (σ • zi E m) ^ m = 1 := by rw [← smul_pow', (zi_spec E m).pow_eq_one, smul_one]
  obtain ⟨k, -, hk⟩ := (zi_spec E m).eq_pow_of_pow_eq_one h
  exact ⟨k, hk.symm⟩

theorem eq_one_of_smul_zi (σ : Gal(F'/E)) (h : σ • zi E m = zi E m) : σ = 1 := by
  have h' : σ (IsCyclotomicExtension.zeta m E F') = IsCyclotomicExtension.zeta m E F' := by
    rw [← coe_zi, ← coe_smul, h]
  set hz := IsCyclotomicExtension.zeta_spec m E F' with hhz
  apply hz.autToPow_injective E
  have h1 := hz.autToPow_spec E σ
  have h2 := hz.autToPow_spec E (1 : Gal(F'/E))
  have key : IsCyclotomicExtension.zeta m E F' ^ ((hz.autToPow E σ : (ZMod m)ˣ) : ZMod m).val
      = IsCyclotomicExtension.zeta m E F' ^ ((hz.autToPow E (1 : Gal(F'/E)) : (ZMod m)ˣ) : ZMod m).val := by
    rw [h1, h2, h', AlgEquiv.one_apply]
  exact Units.ext (ZMod.val_injective _ (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) key))

theorem inertia_eq_bot (Q : Ideal (𝓞 F')) [Q.IsPrime] (hmQ : ((m : ℕ) : 𝓞 F') ∉ Q) : Q.inertia Gal(F'/E) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  obtain ⟨k, hk⟩ := exists_smul_zi_eq_pow σ
  have h1 : σ • zi E m - zi E m ∈ Q := hσ (zi E m)
  rw [hk] at h1
  have h2 : zi E m ^ k = zi E m ^ 1 := pow_eq_pow_of_sub_mem hmQ (by rwa [pow_one])
  rw [pow_one] at h2
  exact eq_one_of_smul_zi σ (hk.trans h2)

theorem natCast_not_mem_of_under (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F')) (hw : w.under (𝓞 E) = v)
    (hmv : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal) : ((m : ℕ) : 𝓞 F') ∉ w.asIdeal := by
  subst hw
  intro h
  apply hmv
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, map_natCast]
  exact h

attribute [local instance] Ideal.Quotient.field in

theorem ramificationIdx_eq_one (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F')) (hw : w.under (𝓞 E) = v)
    (hmv : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  have hmQ := natCast_not_mem_of_under v w hw hmv
  haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : (w.under (𝓞 E)).asIdeal.IsMaximal := (w.under (𝓞 E)).isMaximal
  haveI : Algebra.IsSeparable (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal) (𝓞 F' ⧸ w.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (w.under (𝓞 E)).asIdeal w.asIdeal (w.under (𝓞 E)).ne_bot,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (w.under (𝓞 E)).asIdeal w.asIdeal Gal(F'/E),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(F'/E)) (w.under (𝓞 E)).asIdeal w.asIdeal,
    inertia_eq_bot w.asIdeal hmQ, Subgroup.card_bot]

open scoped NumberField.PlaceTransport Pointwise in

theorem stabilizer_le_decomp (w : HeightOneSpectrum (𝓞 F')) :
    MulAction.stabilizer Gal(F'/E) w.asIdeal ≤ NumberField.PlaceDecomp.decomp E F' w := by
  intro σ hσ
  rw [← NumberField.PlaceTransport.stabilizer_eq_decomp]
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  apply HeightOneSpectrum.ext
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map]
  rw [Ideal.pointwise_smul_def] at hσ
  exact hσ

theorem exists_mem_decomp_orderOf_eq (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 F')) (hw : w.under (𝓞 E) = v)
    (hmv : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    ∃ σ : Gal(F'/E), σ ∈ NumberField.PlaceDecomp.decomp E F' w ∧ orderOf σ = orderOf ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : ZMod m) := by
  have hmQ := natCast_not_mem_of_under v w hw hmv
  subst hw
  haveI : w.asIdeal.IsPrime := w.isPrime
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) Gal(F'/E) w.asIdeal
  refine ⟨σ, stabilizer_le_decomp w hσ.mem_stabilizer, ?_⟩
  set N := Nat.card (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal) with hN
  have hfrob : σ • zi E m = zi E m ^ N := by
    have := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hσ (zi_spec E m).pow_eq_one hmQ
    rwa [MulSemiringAction.toAlgHom_apply] at this
  have hfrob' : σ (IsCyclotomicExtension.zeta m E F') = IsCyclotomicExtension.zeta m E F' ^ N := by
    rw [← coe_zi, ← coe_smul, hfrob]
    rfl
  set hz := IsCyclotomicExtension.zeta_spec m E F' with hhz
  have hval : ((hz.autToPow E σ : (ZMod m)ˣ) : ZMod m) = (N : ZMod m) := by
    have h1 := hz.autToPow_spec E σ
    rw [hfrob'] at h1

    have h2 := (hz.isOfFinOrder (NeZero.ne m)).pow_inj_mod.1 h1
    rw [← hz.eq_orderOf] at h2
    rw [← ZMod.natCast_zmod_val ((hz.autToPow E σ : (ZMod m)ˣ) : ZMod m), ZMod.natCast_eq_natCast_iff']
    exact h2
  rw [← orderOf_injective _ (hz.autToPow_injective E) σ, ← orderOf_units, hval]

end Cyc

theorem two_le_card_quot {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    2 ≤ Nat.card (𝓞 E ⧸ v.asIdeal) := by
  haveI : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  exact Finite.one_lt_card

theorem card_quot_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  letI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero _

theorem natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ)
    (hm : Nat.Coprime m (Nat.card (𝓞 E ⧸ v.asIdeal))) : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal := by
  intro h
  have hc : IsCoprime ((m : ℕ) : 𝓞 E) ((Nat.card (𝓞 E ⧸ v.asIdeal) : ℕ) : 𝓞 E) := by
    have := (Nat.isCoprime_iff_coprime.2 hm).map (Int.castRingHom (𝓞 E))
    simpa using this
  obtain ⟨a, b, hab⟩ := hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h) (v.asIdeal.mul_mem_left b (card_quot_mem v))

theorem exists_eq_pow_mul_le {p : ℕ} (hp : p.Prime) {k d : ℕ} (hd : d ∣ p ^ k * (p - 1)) :
    ∃ a b : ℕ, d = p ^ a * b ∧ 0 < b ∧ b ≤ p - 1 := by
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos hd (Nat.mul_pos (pow_pos hp.pos k) hp1)).ne'
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  refine ⟨a, b, rfl, Nat.pos_of_ne_zero (by rintro rfl; exact hb (dvd_zero p)), ?_⟩
  have hcop : Nat.Coprime b (p ^ k) := Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hb))
  have hb' : b ∣ p - 1 := hcop.dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl : b ∣ p ^ a * b).trans hd)
  exact Nat.le_of_dvd hp1 hb'

theorem pow_dvd_of_mul_gt {p : ℕ} (hp : p.Prime) {k d t N : ℕ} (hd : d ∣ p ^ k * (p - 1))
    (hlow : k < t * d) (hk : t * (p - 1) * p ^ N ≤ k) : p ^ N ∣ d := by
  obtain ⟨a, b, rfl, hb0, hb⟩ := exists_eq_pow_mul_le hp hd
  refine (pow_dvd_pow p ?_).trans (Dvd.intro _ rfl)
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at hlow)
  have h1 : t * (p - 1) * p ^ N < t * (p - 1) * p ^ a :=
    calc t * (p - 1) * p ^ N ≤ k := hk
      _ < t * (p ^ a * b) := hlow
      _ ≤ t * (p ^ a * (p - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
      _ = t * (p - 1) * p ^ a := by ring
  have h2 : p ^ N < p ^ a := Nat.lt_of_mul_lt_mul_left h1
  exact ((Nat.pow_lt_pow_iff_right hp.one_lt).1 h2).le

theorem pow_dvd_of_mul_ge {p : ℕ} (hp : p.Prime) {k d D N : ℕ} (hd : d ∣ p ^ k * (p - 1))
    (hlow : p ^ (k - 1) * (p - 1) ≤ D * d) (hk : N + D + 1 ≤ k) : p ^ N ∣ d := by
  obtain ⟨a, b, rfl, hb0, hb⟩ := exists_eq_pow_mul_le hp hd
  refine (pow_dvd_pow p ?_).trans (Dvd.intro _ rfl)
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  by_contra hlt
  push Not at hlt
  have h1 : p ^ (k - 1) * (p - 1) ≤ D * p ^ a * (p - 1) :=
    calc p ^ (k - 1) * (p - 1) ≤ D * (p ^ a * b) := hlow
      _ ≤ D * (p ^ a * (p - 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
      _ = D * p ^ a * (p - 1) := by ring
  have h2 : p ^ (k - 1) ≤ D * p ^ a := Nat.le_of_mul_le_mul_right h1 hp1
  have h3 : D < p ^ D := Nat.lt_pow_self hp.one_lt
  have h4 : D * p ^ a < p ^ (k - 1) :=
    calc D * p ^ a < p ^ D * p ^ a := Nat.mul_lt_mul_of_lt_of_le h3 le_rfl (pow_pos hp.pos _)
      _ = p ^ (D + a) := by rw [pow_add]
      _ ≤ p ^ (k - 1) := Nat.pow_le_pow_right hp.pos (by omega)
  omega

section Unram

variable {E : Type} [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]

theorem not_dvd_card_quot (v : HeightOneSpectrum (𝓞 E)) (hv : ((p : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    ¬ p ∣ Nat.card (𝓞 E ⧸ v.asIdeal) := by
  intro h
  letI := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal)
  letI : Field (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨n, hq, hcard⟩ := FiniteField.card (𝓞 E ⧸ v.asIdeal) (ringChar (𝓞 E ⧸ v.asIdeal))
  rw [Nat.card_eq_fintype_card, hcard] at h
  have hpq : p = ringChar (𝓞 E ⧸ v.asIdeal) := (Nat.prime_dvd_prime_iff_eq hp.out hq).1 (hp.out.dvd_of_dvd_pow h)
  apply hv
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hpq]
  exact ringChar.Nat.cast_ringChar

theorem pow_natCast_not_mem (v : HeightOneSpectrum (𝓞 E)) (hv : ((p : ℕ) : 𝓞 E) ∉ v.asIdeal) (k : ℕ) :
    ((p ^ k : ℕ) : 𝓞 E) ∉ v.asIdeal := by
  intro h
  rw [Nat.cast_pow] at h
  exact hv (v.isPrime.mem_of_pow_mem k h)

scoped instance neZero_pow (k : ℕ) : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.ne_zero⟩

theorem card_units_dvd (k : ℕ) : Nat.card (ZMod (p ^ k))ˣ ∣ p ^ k * (p - 1) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Nat.totient_prime_pow hp.out hk]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow p (Nat.sub_le k 1)) _

theorem orderOf_natCast_dvd {M : ℕ} (hM : ¬ p ∣ M) (k : ℕ) : orderOf ((M : ℕ) : ZMod (p ^ k)) ∣ p ^ k * (p - 1) := by
  have hcop : Nat.Coprime M (p ^ k) := Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hM).symm
  have : ((M : ℕ) : ZMod (p ^ k)) = ((ZMod.unitOfCoprime M hcop : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := (ZMod.coe_unitOfCoprime M hcop).symm
  rw [this, orderOf_units]
  exact (orderOf_dvd_natCard _).trans (card_units_dvd p k)

theorem lt_mul_of_pow_orderOf {M : ℕ} (hM2 : 2 ≤ M) {t : ℕ} (hMt : M < 2 ^ t) (k : ℕ) (hM : ¬ p ∣ M) :
    k < t * orderOf ((M : ℕ) : ZMod (p ^ k)) := by
  set d := orderOf ((M : ℕ) : ZMod (p ^ k)) with hd
  have hd0 : 0 < d := by
    have hcop : Nat.Coprime M (p ^ k) := Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hM).symm
    have : ((M : ℕ) : ZMod (p ^ k)) = ((ZMod.unitOfCoprime M hcop : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := (ZMod.coe_unitOfCoprime M hcop).symm
    rw [hd, this, orderOf_units]
    exact orderOf_pos _
  have h1 : ((M ^ d : ℕ) : ZMod (p ^ k)) = ((1 : ℕ) : ZMod (p ^ k)) := by
    rw [Nat.cast_pow, Nat.cast_one, hd, pow_orderOf_eq_one]
  rw [ZMod.natCast_eq_natCast_iff] at h1
  have h2 : p ^ k ∣ M ^ d - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h1.symm
  have h3 : 2 ≤ M ^ d := by
    calc 2 ≤ M := hM2
      _ = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ d := Nat.pow_le_pow_right (by omega) hd0
  have h4 : p ^ k < M ^ d := by
    have := Nat.le_of_dvd (by omega) h2
    omega
  have h5 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.out.two_le k
  have h6 : M ^ d < (2 ^ t) ^ d := Nat.pow_lt_pow_left hMt hd0.ne'
  rw [← pow_mul] at h6
  have h7 : 2 ^ k < 2 ^ (t * d) := lt_of_le_of_lt h5 (h4.trans h6)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h7

theorem pow_dvd_card_decomp_of_not_mem (N : ℕ) (v : HeightOneSpectrum (𝓞 E)) (hv : ((p : ℕ) : 𝓞 E) ∉ v.asIdeal) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ w : HeightOneSpectrum (𝓞 (CyclotomicField (p ^ k) E)),
      w.under (𝓞 E) = v → p ^ N ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E (CyclotomicField (p ^ k) E) w) := by
  set M := Nat.card (𝓞 E ⧸ v.asIdeal) with hMdef
  have hM2 : 2 ≤ M := two_le_card_quot v
  have hMp : ¬ p ∣ M := not_dvd_card_quot p v hv
  set t := Nat.log 2 M + 1 with ht
  have hMt : M < 2 ^ t := Nat.lt_pow_succ_log_self (by norm_num) M
  refine ⟨t * (p - 1) * p ^ N, fun k hk w hw => ?_⟩
  obtain ⟨σ, hσ, hord⟩ := exists_mem_decomp_orderOf_eq (m := p ^ k) v w hw (pow_natCast_not_mem p v hv k)
  have h1 : orderOf σ ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E (CyclotomicField (p ^ k) E) w) := by
    rw [← Subgroup.orderOf_mk σ hσ]
    exact orderOf_dvd_natCard _
  refine dvd_trans ?_ h1
  rw [hord]
  exact pow_dvd_of_mul_gt hp.out (orderOf_natCast_dvd p hMp k) (lt_mul_of_pow_orderOf p hM2 hMt k hMp) hk

end Unram

section Deg

variable (E : Type) [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]

theorem card_aut_dvd (k : ℕ) : Nat.card (CyclotomicField (p ^ k) E ≃ₐ[E] CyclotomicField (p ^ k) E) ∣ p ^ k * (p - 1) := by
  set hz := IsCyclotomicExtension.zeta_spec (p ^ k) E (CyclotomicField (p ^ k) E) with hhz
  have hinj := hz.autToPow_injective E
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact (Subgroup.card_subgroup_dvd_card _).trans (card_units_dvd p k)

theorem totient_le_finrank_mul_card (k : ℕ) :
    (p ^ k).totient ≤ Module.finrank ℚ E * Nat.card (CyclotomicField (p ^ k) E ≃ₐ[E] CyclotomicField (p ^ k) E) := by
  set C := CyclotomicField (p ^ k) E
  have hz := IsCyclotomicExtension.zeta_spec (p ^ k) E C
  rw [IsGalois.card_aut_eq_finrank, Module.finrank_mul_finrank ℚ E C, ← Polynomial.natDegree_cyclotomic (p ^ k) ℚ,
    Polynomial.cyclotomic_eq_minpoly_rat hz (NeZero.pos _)]
  exact minpoly.natDegree_le _

theorem pow_dvd_card_aut (N k : ℕ) (hk : N + Module.finrank ℚ E + 1 ≤ k) :
    p ^ N ∣ Nat.card (CyclotomicField (p ^ k) E ≃ₐ[E] CyclotomicField (p ^ k) E) := by
  have hk1 : 0 < k := by omega
  refine pow_dvd_of_mul_ge hp.out (card_aut_dvd E p k) ?_ hk
  rw [← Nat.totient_prime_pow hp.out hk1]
  exact totient_le_finrank_mul_card E p k

end Deg

section Ram

variable {E : Type} [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime] (k : ℕ)

local notation "C" => CyclotomicField (p ^ k) E

theorem algebraMap_int_injective : Function.Injective (algebraMap (𝓞 E) (𝓞 C)) := fun x y hxy => by
  apply IsIntegralClosure.algebraMap_injective (𝓞 E) ℤ E
  apply (algebraMap E C).injective
  have := congrArg (algebraMap (𝓞 C) C) hxy
  rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 E) E C, IsScalarTower.algebraMap_apply (𝓞 E) E C] at this

theorem one_sub_zi_mem (w : HeightOneSpectrum (𝓞 C)) (hpw : ((p : ℕ) : 𝓞 C) ∈ w.asIdeal) : 1 - zi E (p ^ k) ∈ w.asIdeal := by
  haveI : w.asIdeal.IsPrime := w.isPrime
  set Q := 𝓞 C ⧸ w.asIdeal
  have h0 : ((p : ℕ) : Q) = 0 := by rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hpw
  have hchar : ringChar Q = p := by
    have hdvd : ringChar Q ∣ p := (ringChar.spec Q p).1 h0
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · exact h1
  haveI : CharP Q p := ringChar.of_eq hchar
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : (Ideal.Quotient.mk w.asIdeal (1 - zi E (p ^ k))) ^ p ^ k = 0 := by
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, (zi_spec E (p ^ k)).pow_eq_one, map_one, sub_self]
  exact pow_eq_zero_iff (pow_ne_zero k hp.out.ne_zero) |>.1 h1

theorem one_sub_zi_pow_dvd (k' : ℕ) (hk : k = k' + 1) : (1 - zi E (p ^ k)) ^ (p ^ k).totient ∣ ((p : ℕ) : 𝓞 C) := by
  have hz := zi_spec E (p ^ k)
  have hprod : ((p : ℕ) : 𝓞 C) = ∏ μ ∈ primitiveRoots (p ^ k) (𝓞 C), (1 - μ) := by
    have h := Polynomial.eval_one_cyclotomic_prime_pow (R := 𝓞 C) (p := p) k'
    rw [← hk, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz, Polynomial.eval_prod] at h
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    exact h.symm
  rw [hprod, ← hz.card_primitiveRoots, ← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro μ hμ
  have hμ' : IsPrimitiveRoot μ (p ^ k) := (mem_primitiveRoots (NeZero.pos _)).1 hμ
  obtain ⟨i, -, rfl⟩ := hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one
  simpa using sub_dvd_pow_sub_pow (1 : 𝓞 C) (zi E (p ^ k)) i

theorem under_int_eq (v : HeightOneSpectrum (𝓞 E)) (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) :
    v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible
    (Int.prime_iff_natAbs_prime.2 (by simpa using hp.out)).irreducible
  refine (Ideal.IsMaximal.eq_of_le inferInstance ?_ ?_).symm
  · exact Ideal.IsPrime.ne_top inferInstance
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap, map_natCast]
    exact hv

theorem natCast_mem_of_under (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 C)) (hw : w.under (𝓞 E) = v)
    (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal) : ((p : ℕ) : 𝓞 C) ∈ w.asIdeal := by
  subst hw
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, map_natCast] at hv
  exact hv

theorem totient_le_finrank_mul_ramificationIdx (k' : ℕ) (hk : k = k' + 1) (v : HeightOneSpectrum (𝓞 E)) (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal)
    (w : HeightOneSpectrum (𝓞 C)) (hw : w.under (𝓞 E) = v) :
    (p ^ k).totient ≤ Module.finrank ℚ E * v.asIdeal.ramificationIdx' w.asIdeal := by
  classical
  have hpw := natCast_mem_of_under p k v w hw hv
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : v.asIdeal.IsPrime := v.isPrime

  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hmapC : Ideal.map (algebraMap ℤ (𝓞 C)) P = Ideal.span {((p : ℕ) : 𝓞 C)} := by
    rw [hP, Ideal.map_span, Set.image_singleton, map_natCast]
  have hp0C : ((p : ℕ) : 𝓞 C) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hmapC0 : Ideal.map (algebraMap ℤ (𝓞 C)) P ≠ ⊥ := by
    rw [hmapC, Ne, Ideal.span_singleton_eq_bot]; exact hp0C

  have hle : Ideal.map (algebraMap ℤ (𝓞 C)) P ≤ w.asIdeal ^ (p ^ k).totient := by
    rw [hmapC, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    obtain ⟨c, hc⟩ := one_sub_zi_pow_dvd (E := E) p k k' hk
    rw [hc]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (one_sub_zi_mem p k w hpw) _)
  have h1 : (p ^ k).totient ≤ P.ramificationIdx' w.asIdeal := by
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapC0 w.isPrime w.ne_bot]
    have hPirr := (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible
    have hdvd : w.asIdeal ^ (p ^ k).totient ∣ Ideal.map (algebraMap ℤ (𝓞 C)) P := Ideal.dvd_iff_le.2 hle
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ w.ne_bot) hmapC0,
      UniqueFactorizationMonoid.normalizedFactors_pow, UniqueFactorizationMonoid.normalizedFactors_irreducible hPirr,
      normalize_eq, Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le] at hdvd
    exact hdvd

  have hmapE0 : Ideal.map (algebraMap (𝓞 E) (𝓞 C)) v.asIdeal ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (algebraMap_int_injective p k)).not.2 v.ne_bot
  have hmapEle : Ideal.map (algebraMap (𝓞 E) (𝓞 C)) v.asIdeal ≤ w.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, ← hw]; exact le_rfl
  have htower := Ideal.ramificationIdx_algebra_tower (p := P) hmapE0 hmapC0 hmapEle

  haveI : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible
    (Int.prime_iff_natAbs_prime.2 (by simpa using hp.out)).irreducible
  haveI : v.asIdeal.LiesOver P := ⟨(under_int_eq p v hv).symm⟩
  have h3 : P.ramificationIdx' v.asIdeal ≤ Module.finrank ℚ E := Ideal.ramificationIdx_le_finrank (𝓞 E) ℚ E v.asIdeal
  calc (p ^ k).totient ≤ P.ramificationIdx' w.asIdeal := h1
    _ = P.ramificationIdx' v.asIdeal * v.asIdeal.ramificationIdx' w.asIdeal := htower
    _ ≤ Module.finrank ℚ E * v.asIdeal.ramificationIdx' w.asIdeal := Nat.mul_le_mul_right _ h3

attribute [local instance] Ideal.Quotient.field in

theorem ramificationIdx_dvd_card_decomp (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 C)) (hw : w.under (𝓞 E) = v) :
    v.asIdeal.ramificationIdx' w.asIdeal ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E C w) ∧
    v.asIdeal.ramificationIdx' w.asIdeal ∣ Nat.card (C ≃ₐ[E] C) := by
  subst hw
  haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨rfl⟩
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : (w.under (𝓞 E)).asIdeal.IsMaximal := (w.under (𝓞 E)).isMaximal
  haveI : Algebra.IsSeparable (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal) (𝓞 C ⧸ w.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hcard : Nat.card ↥(w.asIdeal.inertia Gal(C/E)) = (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (w.under (𝓞 E)).asIdeal w.asIdeal (w.under (𝓞 E)).ne_bot,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx (w.under (𝓞 E)).asIdeal w.asIdeal Gal(C/E)]
    exact Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(C/E)) (w.under (𝓞 E)).asIdeal w.asIdeal
  rw [← hcard]
  exact ⟨Subgroup.card_dvd_of_le ((Ideal.inertia_le_stabilizer _).trans (stabilizer_le_decomp w)), Subgroup.card_subgroup_dvd_card _⟩

theorem pow_dvd_card_decomp_of_mem (N : ℕ) (v : HeightOneSpectrum (𝓞 E)) (hv : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal)
    (hk : N + Module.finrank ℚ E + 1 ≤ k) (w : HeightOneSpectrum (𝓞 C)) (hw : w.under (𝓞 E) = v) :
    p ^ N ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E C w) := by
  obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hdvdD, hdvdG⟩ := ramificationIdx_dvd_card_decomp p k v w hw
  refine dvd_trans (pow_dvd_of_mul_ge hp.out (hdvdG.trans (card_aut_dvd E p k)) ?_ hk) hdvdD
  rw [← Nat.totient_prime_pow hp.out (by omega)]
  exact totient_le_finrank_mul_ramificationIdx p k k' hk' v hv w hw

end Ram

end CycDepthProof
p2m_reactivate "P2MW.S_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv.CycDepthProof"

theorem solution
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) [Fact p.Prime] (N : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      p ^ N ∣ Nat.card (CyclotomicField (p ^ k) E ≃ₐ[E] CyclotomicField (p ^ k) E) ∧
      ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 (CyclotomicField (p ^ k) E)), w.under (𝓞 E) = v →
        p ^ N ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E (CyclotomicField (p ^ k) E) w) := by
  classical
  let kv : HeightOneSpectrum (𝓞 E) → ℕ := fun v =>
    if hv : ((p : ℕ) : 𝓞 E) ∉ v.asIdeal then Classical.choose (CycDepthProof.pow_dvd_card_decomp_of_not_mem p N v hv) else 0
  refine ⟨N + Module.finrank ℚ E + 1 + T.sup kv, fun k hk => ⟨CycDepthProof.pow_dvd_card_aut E p N k (by omega), fun v hvT w hw => ?_⟩⟩
  by_cases hv : ((p : ℕ) : 𝓞 E) ∉ v.asIdeal
  · have hspec := Classical.choose_spec (CycDepthProof.pow_dvd_card_decomp_of_not_mem p N v hv)
    apply hspec k _ w hw
    have h1 : kv v ≤ T.sup kv := Finset.le_sup hvT
    have h2 : kv v = Classical.choose (CycDepthProof.pow_dvd_card_decomp_of_not_mem p N v hv) := dif_pos hv
    omega
  · push Not at hv
    exact CycDepthProof.pow_dvd_card_decomp_of_mem p k N v hv (by omega) w hw

end S_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv
end P2MW
export P2MW.S_NumberField_exists_forall_pow_dvd_natCard_decomp_cyclotomicField_and_dvd_natCard_algEquiv (solution)

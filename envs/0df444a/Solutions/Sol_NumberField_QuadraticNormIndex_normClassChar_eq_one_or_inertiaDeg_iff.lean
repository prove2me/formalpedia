-- Prove2me | solution 1 for NumberField.QuadraticNormIndex.normClassChar_eq_one_or_inertiaDeg_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f1daace3-25e3-541a-966e-754707027db6

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_QuadraticNormIndex_normClassChar_eq_one_or_inertiaDeg_iff

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply
open LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors

noncomputable section

namespace QuadraticNormIndexProof

variable {I : Type*} [CommGroup I] (𝔑 : Subgroup I) {G : Type*} [Group G] (ω : I →* G) (σ : G)

section Transfer

variable {Ip : Type*} [CommGroup Ip] (N : Ip →* I) (ωp : Ip →* G)

private def transferClass (b : Ip) : I ⧸ 𝔑 := ((N b : I) : I ⧸ 𝔑)

variable {𝔑 N ωp σ}

private theorem transferClass_indep (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b b' : Ip} (hb : ωp b = σ) (hb' : ωp b' = σ) :
    transferClass 𝔑 N b = transferClass 𝔑 N b' := by
  unfold transferClass
  rw [QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, hb, hb', inv_mul_cancel])

private theorem transferClass_pow_orderOf (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) :
    transferClass 𝔑 N b ^ orderOf σ = 1 := by
  unfold transferClass
  rw [← QuotientGroup.mk_pow, ← map_pow, QuotientGroup.eq_one_iff]
  exact hker _ (by rw [map_pow, hb, pow_orderOf_eq_one])

private theorem coe_eq_transferClass_zpow (hker : ∀ x, ωp x = 1 → N x ∈ 𝔑) {b : Ip} (hb : ωp b = σ) {P : Ip} {p : I} (hNP : N P = p)
    {d : ℤ} (hd : ωp P = σ ^ d) : ((p : I) : I ⧸ 𝔑) = transferClass 𝔑 N b ^ d := by
  unfold transferClass
  rw [← hNP, ← QuotientGroup.mk_zpow, ← map_zpow, QuotientGroup.eq, ← map_inv, ← map_mul]
  exact hker _ (by rw [map_mul, map_inv, map_zpow, hb, hd, inv_mul_cancel])

private theorem apply_eq_zpow_of_transfer (hcompat : ∀ x, ω (N x) = ωp x) {P : Ip} {p : I} (hNP : N P = p) {d : ℤ} (hd : ωp P = σ ^ d) :
    ω p = σ ^ d := by
  rw [← hNP, hcompat, hd]

end Transfer

section Crossing

variable {Ip Iq Ipq : Type*} [CommGroup Ip] [CommGroup Iq] [CommGroup Ipq]
variable {N : Ip →* I} {ωp : Ip →* G} {N' : Iq →* I} {ωq : Iq →* G}
variable {𝔑 σ}

private theorem transferClass_eq_of_common_norm (hkerp : ∀ x, ωp x = 1 → N x ∈ 𝔑) (hkerq : ∀ x, ωq x = 1 → N' x ∈ 𝔑)
    {bp : Ip} {bq : Iq} (hN : N bp = N' bq) (hbp : ωp bp = σ) (hbq : ωq bq = σ)
    {b : Ip} (hb : ωp b = σ) {b' : Iq} (hb' : ωq b' = σ) : transferClass 𝔑 N b = transferClass 𝔑 N' b' := by
  rw [transferClass_indep hkerp hb hbp, transferClass_indep hkerq hb' hbq]
  unfold transferClass
  rw [hN]

end Crossing

private theorem exists_zpow_of_mem_closure (c : I ⧸ 𝔑) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) :
    ∃ e : ℤ, ω x = σ ^ e ∧ ((x : I) : I ⧸ 𝔑) = c ^ e := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => exact ⟨0, by rw [map_one, zpow_zero], by rw [QuotientGroup.mk_one, zpow_zero]⟩
  | mul y z _ _ ihy ihz =>
    obtain ⟨e, he, he'⟩ := ihy
    obtain ⟨f, hf, hf'⟩ := ihz
    exact ⟨e + f, by rw [map_mul, he, hf, zpow_add], by rw [QuotientGroup.mk_mul, he', hf', zpow_add]⟩
  | inv y _ ihy =>
    obtain ⟨e, he, he'⟩ := ihy
    exact ⟨-e, by rw [map_inv, he, zpow_neg], by rw [QuotientGroup.mk_inv, he', zpow_neg]⟩

private theorem mem_of_ker_of_classes (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) {x : I} (hx : x ∈ Subgroup.closure S) (hω : ω x = 1) :
    x ∈ 𝔑 := by
  obtain ⟨e, he, he'⟩ := exists_zpow_of_mem_closure 𝔑 ω σ c S hS hx

  have hdvd : (orderOf σ : ℤ) ∣ e := orderOf_dvd_iff_zpow_eq_one.mpr (by rw [← he, hω])
  have hce : c ^ e = 1 := by
    obtain ⟨t, rfl⟩ := hdvd
    rw [zpow_mul, zpow_natCast, hc, one_zpow]
  rw [← QuotientGroup.eq_one_iff, he', hce]

private theorem ker_inf_closure_le (c : I ⧸ 𝔑) (hc : c ^ orderOf σ = 1) (S : Set I)
    (hS : ∀ p ∈ S, ∃ d : ℤ, ω p = σ ^ d ∧ ((p : I) : I ⧸ 𝔑) = c ^ d) : ω.ker ⊓ Subgroup.closure S ≤ 𝔑 :=
  fun _ hx => mem_of_ker_of_classes 𝔑 ω σ c hc S hS hx.2 (MonoidHom.mem_ker.mp hx.1)

private theorem ker_inf_closure_le_of_transfer {Ip : Type*} [CommGroup Ip] (S : Set I)
    (N : I → (Ip →* I)) (ωp : I → (Ip →* G)) (P : I → Ip) (d : I → ℤ)
    (hcompat : ∀ p ∈ S, ∀ x, ω (N p x) = ωp p x) (hker : ∀ p ∈ S, ∀ x, ωp p x = 1 → N p x ∈ 𝔑)
    (hNP : ∀ p ∈ S, N p (P p) = p) (hd : ∀ p ∈ S, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ S, ∀ q ∈ S, ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ) :
    ω.ker ⊓ Subgroup.closure S ≤ 𝔑 := by
  by_cases hS : S.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hS
    obtain ⟨b₀, -, -, hb₀⟩ := hcross p₀ hp₀ p₀ hp₀
    refine ker_inf_closure_le 𝔑 ω σ (transferClass 𝔑 (N p₀) b₀) (transferClass_pow_orderOf (hker p₀ hp₀) hb₀) S ?_
    intro p hp
    obtain ⟨bp, bq, hN, hbp⟩ := hcross p₀ hp₀ p hp

    have hbq : ωp p bq = σ := by rw [← hcompat p hp, ← hN, hcompat p₀ hp₀, hbp]
    refine ⟨d p, apply_eq_zpow_of_transfer ω (hcompat p hp) (hNP p hp) (hd p hp), ?_⟩
    rw [transferClass_eq_of_common_norm (hker p₀ hp₀) (hker p hp) hN hbp hbq hb₀ hbq]
    exact coe_eq_transferClass_zpow (hker p hp) hbq (hNP p hp) (hd p hp)
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, Subgroup.closure_empty, inf_bot_eq]
    exact bot_le

section Carriers

variable (K : Type*) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K))

private theorem primeCarrier_mem (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ 𝔣) :
    primeCarrier K 𝔣 v hv ∈ primeCarriers K 𝔣 :=
  ⟨v, hv, rfl⟩

open Classical in
private def carrierOrOne (v : HeightOneSpectrum (𝓞 K)) : ↥(coprimeToModulus K 𝔣) :=
  if hv : v.asIdeal ∣ 𝔣 then 1 else primeCarrier K 𝔣 v hv

private theorem carrierOrOne_mem_closure (v : HeightOneSpectrum (𝓞 K)) :
    carrierOrOne K 𝔣 v ∈ Subgroup.closure (primeCarriers K 𝔣) := by
  unfold carrierOrOne
  split_ifs with hv
  · exact one_mem _
  · exact Subgroup.subset_closure (primeCarrier_mem K 𝔣 v hv)

open Classical in
private theorem val_carrierOrOne_zpow (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (((carrierOrOne K 𝔣 v ^ n : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
      = if v.asIdeal ∣ 𝔣 then 1 else (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ n := by
  rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  unfold carrierOrOne
  split_ifs with hv
  · rw [OneMemClass.coe_one, Units.val_one, one_zpow]
  · rw [primeCarrier, primeUnit_val]

private theorem raySymbolHom_carrierOrOne (I : ↥(coprimeToModulus K 𝔣)) : raySymbolHom K 𝔣 (carrierOrOne K 𝔣) I = I := by
  apply Subtype.ext
  apply Units.ext
  rw [raySymbolHom_apply]
  unfold raySymbol
  have hfin := hasFiniteMulSupport_raySymbol_factors K (carrierOrOne K 𝔣)
    ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)

  let φ : ↥(coprimeToModulus K 𝔣) →* FractionalIdeal ((𝓞 K)⁰) K :=
    (Units.coeHom (FractionalIdeal ((𝓞 K)⁰) K)).comp (coprimeToModulus K 𝔣).subtype
  show φ (∏ᶠ v, carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v
      ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)) = φ I
  rw [MonoidHom.map_finprod φ hfin]
  conv_rhs => rw [show φ I = ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ))]
  refine finprod_congr fun v => ?_
  rw [show φ (carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K))
      = (((carrierOrOne K 𝔣 v ^ FractionalIdeal.count K v ((I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K)
          : ↥(coprimeToModulus K 𝔣)) : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) from rfl,
    val_carrierOrOne_zpow]
  split_ifs with hv
  · rw [I.2 v hv, zpow_zero]
  · rfl

private theorem closure_primeCarriers_eq_top : Subgroup.closure (primeCarriers K 𝔣) = ⊤ := by
  rw [eq_top_iff]
  intro I _
  rw [← raySymbolHom_carrierOrOne K 𝔣 I, raySymbolHom_apply]
  unfold raySymbol
  exact finprod_induction (· ∈ Subgroup.closure (primeCarriers K 𝔣)) (one_mem _) (fun _ _ => mul_mem)
    fun v => zpow_mem (carrierOrOne_mem_closure K 𝔣 v) _

end Carriers

private theorem fracRelNormUnit_primeUnit' (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    (w : HeightOneSpectrum (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 k)) (h𝔭w : w.asIdeal.under (𝓞 k) = 𝔭.asIdeal) :
    HeckeCharacter.fracRelNormUnit k E (primeUnit E w) = primeUnit k 𝔭 ^ (𝔭.asIdeal.inertiaDeg' w.asIdeal) := by
  have heq : HeckeCharacter.placeUnder' k E w = 𝔭 :=
    IsDedekindDomain.HeightOneSpectrum.ext (by rw [HeckeCharacter.placeUnder'_asIdeal, h𝔭w])
  show raySymbolUnitsHom E _ (primeUnit E w) = _
  rw [show raySymbolUnitsHom E _ (primeUnit E w)
        = raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E) from rfl,
    raySymbol_primeUnit, heq]

private theorem relNormCTM_primeUnit' (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    {𝔠 : Ideal (𝓞 k)} {w : HeightOneSpectrum (𝓞 E)} (hw : ¬ w.asIdeal ∣ HeckeCharacter.modulusExt k E 𝔠) :
    ((HeckeCharacter.relNormCTM k E 𝔠 (primeCarrier E (HeckeCharacter.modulusExt k E 𝔠) w hw) :
        ↥(coprimeToModulus k 𝔠)) : (FractionalIdeal ((𝓞 k)⁰) k)ˣ)
      = primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal) :=
  fracRelNormUnit_primeUnit' k E w (w.under (𝓞 k)) rfl

section Glue

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem inertiaDeg_eq_one_of_isArithFrobAt_one [IsGalois K L]
    (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    (H : IsArithFrobAt (𝓞 K) (1 : L ≃ₐ[K] L) Q) :
    (Q.under (𝓞 K)).inertiaDeg' Q = 1 := by
  classical
  letI : Field (𝓞 L ⧸ Q) := Ideal.Quotient.field Q
  haveI hp : (Q.under (𝓞 K)).IsMaximal := Ideal.IsMaximal.under (𝓞 K) Q
  letI : Field (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.Quotient.field _
  haveI : Q.LiesOver (Q.under (𝓞 K)) := ⟨rfl⟩
  have hQne : Q ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField L)
  have hpne : Q.under (𝓞 K) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hp (RingOfIntegers.not_isField K)
  haveI : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot _ hQne
  haveI : Finite (𝓞 K ⧸ Q.under (𝓞 K)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpne
  set q := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hqdef
  have hq1 : 1 < q := Finite.one_lt_card

  have hge : q ≤ Nat.card (𝓞 L ⧸ Q) :=
    Nat.card_le_card_of_injective _ (algebraMap (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 L ⧸ Q)).injective

  have hroot : ∀ y : 𝓞 L ⧸ Q, y ^ q = y := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    have h := H a
    rw [MulSemiringAction.toAlgHom_apply, one_smul] at h
    rw [← map_pow, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h
  have hle : Nat.card (𝓞 L ⧸ Q) ≤ q := by
    letI := Fintype.ofFinite (𝓞 L ⧸ Q)
    have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 L ⧸ Q)) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero _ hq1
    have hsub : (Finset.univ : Finset (𝓞 L ⧸ Q)).val ⊆
        (Polynomial.X ^ q - Polynomial.X : Polynomial (𝓞 L ⧸ Q)).roots := by
      intro y _
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X, hroot y, sub_self]
    have h := Polynomial.card_le_degree_of_subset_roots hsub
    rwa [Finset.card_univ, FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1,
      ← Nat.card_eq_fintype_card] at h
  have hcard : Nat.card (𝓞 L ⧸ Q) = q := le_antisymm hle hge
  have hpow := Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ Q.under (𝓞 K)) (V := 𝓞 L ⧸ Q)
  rw [hcard] at hpow
  rw [Ideal.inertiaDeg_algebraMap]
  have h1 : q ^ Module.finrank (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 L ⧸ Q) = q ^ 1 := by
    rw [pow_one]; exact hpow.symm
  exact Nat.pow_right_injective hq1 h1

private theorem inertiaDeg_primeAbove_eq_one_of_artinFrob_eq_one [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (h : artinFrob K L v = 1) :
    v.asIdeal.inertiaDeg' (primeAbove K L v) = 1 := by
  have H := isArithFrobAt_artinFrob K L v
  rw [h] at H
  have h1 := inertiaDeg_eq_one_of_isArithFrobAt_one (K := K) (primeAbove K L v) H
  rwa [under_primeAbove] at h1

private theorem artinSymbol_primeCarrier [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    {𝔣 : Ideal (𝓞 K)} {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) :
    artinSymbol K L 𝔣 (primeCarrier K 𝔣 v hv) = artinFrob K L v :=
  artinSymbol_prime K L hv

private theorem eq_of_ne_one_of_ne_one {G : Type*} [Group G] (hG : Nat.card G = 2)
    {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact two_ne_zero)
  have ha2 : a ^ 2 = 1 := by rw [← hG]; exact pow_card_eq_one'
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha
  have htop : Subgroup.zpowers a = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hG]
  have hb' : b ∈ Subgroup.zpowers a := htop ▸ Subgroup.mem_top b
  rw [mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image] at hb'
  obtain ⟨n, hn, hbn⟩ := hb'
  rw [Finset.mem_range] at hn
  interval_cases n
  · rw [pow_zero] at hbn
    exact absurd hbn.symm hb
  · rw [pow_one] at hbn
    exact hbn

private theorem normRaySubgroup_le_ker (𝔣 : Ideal (𝓞 K)) (ω : NarrowRayClassGroup K 𝔣 →* ℂˣ)
    (hω : ∀ (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ ((w.under (𝓞 K)).asIdeal ∣ 𝔣)),
      ω (primeClass K 𝔣 (w.under (𝓞 K)) hw ^
        ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)) = 1) :
    normRaySubgroup K L 𝔣 ≤ (ω.comp (NarrowRayClassGroup.mk K 𝔣)).ker := by
  unfold normRaySubgroup
  refine sup_le ?_ ?_
  · intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      NarrowRayClassGroup.mk_eq_one_of_mem K (Subgroup.mem_subgroupOf.mp hy), map_one]
  · rw [MonoidHom.range_le_ker_iff]

    have hgen : Subgroup.closure (primeCarriers L (HeckeCharacter.modulusExt K L 𝔣)) ≤
        ((ω.comp (NarrowRayClassGroup.mk K 𝔣)).comp (HeckeCharacter.relNormCTM K L 𝔣)).ker := by
      rw [Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]
      have hwv : ¬ ((w.under (𝓞 K)).asIdeal ∣ 𝔣) := fun h =>
        hw ((HeckeCharacter.placeUnder'_dvd_iff K L 𝔣 w).mp h)
      have hrel : HeckeCharacter.relNormCTM K L 𝔣 (primeCarrier L (HeckeCharacter.modulusExt K L 𝔣) w hw)
          = primeCarrier K 𝔣 (w.under (𝓞 K)) hwv ^ ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal) := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow]
        exact relNormCTM_primeUnit' K L hw
      rw [hrel, map_pow]
      exact hω w hwv
    rw [closure_primeCarriers_eq_top, top_le_iff] at hgen
    exact MonoidHom.ker_eq_top_iff.mp hgen

end Glue

end QuadraticNormIndexProof

end

open QuadraticNormIndexProof in
theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsMulCommutative (L ≃ₐ[K] L)]
    (h2 : Module.finrank K L = 2) (𝔣 : Ideal (𝓞 K)) (hadm : IsAdmissibleModulus K L 𝔣)
    (σ : L ≃ₐ[K] L) {Ip : Type*} [CommGroup Ip]
    (N : ↥(coprimeToModulus K 𝔣) → (Ip →* ↥(coprimeToModulus K 𝔣)))
    (ωp : ↥(coprimeToModulus K 𝔣) → (Ip →* (L ≃ₐ[K] L)))
    (P : ↥(coprimeToModulus K 𝔣) → Ip) (d : ↥(coprimeToModulus K 𝔣) → ℤ)
    (hcompat : ∀ p ∈ primeCarriers K 𝔣, ∀ x, artinSymbol K L 𝔣 (N p x) = ωp p x)
    (hker : ∀ p ∈ primeCarriers K 𝔣, ∀ x, ωp p x = 1 → N p x ∈ normRaySubgroup K L 𝔣)
    (hNP : ∀ p ∈ primeCarriers K 𝔣, N p (P p) = p)
    (hd : ∀ p ∈ primeCarriers K 𝔣, ωp p (P p) = σ ^ d p)
    (hcross : ∀ p ∈ primeCarriers K 𝔣, ∀ q ∈ primeCarriers K 𝔣,
      ∃ bp bq : Ip, N p bp = N q bq ∧ ωp p bp = σ)
    (ω : NarrowRayClassGroup K 𝔣 →* ℂˣ)
    (hω : ∀ (w : HeightOneSpectrum (𝓞 L)) (hw : ¬ ((w.under (𝓞 K)).asIdeal ∣ 𝔣)),
      ω (primeClass K 𝔣 (w.under (𝓞 K)) hw ^
        ((w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal)) = 1) :
    ω = 1 ∨
    (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ (v.asIdeal ∣ 𝔣)),
      ω (primeClass K 𝔣 v hv) ^ 2 = 1 ∧
      (ω (primeClass K 𝔣 v hv) = 1 ↔
        ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) = v ∧
          v.asIdeal.inertiaDeg' w.asIdeal = 1)) := by
  have _hadm := hadm

  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  have hG : Nat.card (L ≃ₐ[K] L) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  haveI : Finite (L ≃ₐ[K] L) := Nat.finite_of_card_ne_zero (by rw [hG]; exact two_ne_zero)

  have hkerLe : (artinSymbol K L 𝔣).ker ≤ normRaySubgroup K L 𝔣 := by
    have h := ker_inf_closure_le_of_transfer (normRaySubgroup K L 𝔣) (artinSymbol K L 𝔣) σ
      (primeCarriers K 𝔣) N ωp P d hcompat hker hNP hd hcross
    rwa [closure_primeCarriers_eq_top, inf_top_eq] at h

  set ω' : ↥(coprimeToModulus K 𝔣) →* ℂˣ := ω.comp (NarrowRayClassGroup.mk K 𝔣) with hω'def
  have hNle : normRaySubgroup K L 𝔣 ≤ ω'.ker := normRaySubgroup_le_ker 𝔣 ω hω
  have hω'_of_symbol : ∀ x : ↥(coprimeToModulus K 𝔣), artinSymbol K L 𝔣 x = 1 → ω' x = 1 :=
    fun x hx => MonoidHom.mem_ker.mp (hNle (hkerLe (MonoidHom.mem_ker.mpr hx)))
  have hsq : ∀ x : ↥(coprimeToModulus K 𝔣), ω' x ^ 2 = 1 := fun x => by
    rw [← map_pow]
    exact hω'_of_symbol _ (by rw [map_pow, ← hG]; exact pow_card_eq_one')
  have hprime : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ (v.asIdeal ∣ 𝔣)),
      ω (primeClass K 𝔣 v hv) = ω' (primeCarrier K 𝔣 v hv) := fun v hv => rfl
  by_cases hω1 : ω = 1
  · exact Or.inl hω1
  right

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ↥(coprimeToModulus K 𝔣), ω' x₀ ≠ 1 := by
    by_contra hcon
    apply hω1
    refine MonoidHom.ext fun y => ?_
    obtain ⟨c, rfl⟩ :=
      QuotientGroup.mk'_surjective ((narrowRaySubgroup K 𝔣).subgroupOf (coprimeToModulus K 𝔣)) y
    show ω' c = 1
    by_contra hc
    exact hcon ⟨c, hc⟩
  have hx₀s : artinSymbol K L 𝔣 x₀ ≠ 1 := fun h => hx₀ (hω'_of_symbol x₀ h)

  have hone_iff : ∀ x : ↥(coprimeToModulus K 𝔣), ω' x = 1 ↔ artinSymbol K L 𝔣 x = 1 := by
    intro x
    refine ⟨fun hx => ?_, hω'_of_symbol x⟩
    by_contra hxs
    have heq : artinSymbol K L 𝔣 (x * x₀⁻¹) = 1 := by
      rw [map_mul, map_inv, eq_of_ne_one_of_ne_one hG hxs hx₀s, mul_inv_cancel]
    have h := hω'_of_symbol _ heq
    rw [map_mul, map_inv, hx, one_mul, inv_eq_one] at h
    exact hx₀ h
  intro v hv
  refine ⟨by rw [hprime]; exact hsq _, ?_⟩
  rw [hprime, hone_iff, artinSymbol_primeCarrier (L := L) hv]
  constructor
  · intro hfrob
    exact ⟨⟨primeAbove K L v, inferInstance, primeAbove_ne_bot K L v⟩,
      HeightOneSpectrum.ext (under_primeAbove K L v),
      inertiaDeg_primeAbove_eq_one_of_artinFrob_eq_one v hfrob⟩
  · rintro ⟨w, hwv, hf⟩

    have h1 : ω (primeClass K 𝔣 v hv) = 1 := by
      subst hwv
      have h := hω w hv
      rwa [hf, pow_one] at h
    rwa [hprime, hone_iff, artinSymbol_primeCarrier (L := L) hv] at h1

end S_NumberField_QuadraticNormIndex_normClassChar_eq_one_or_inertiaDeg_iff
end P2MW
export P2MW.S_NumberField_QuadraticNormIndex_normClassChar_eq_one_or_inertiaDeg_iff (solution)

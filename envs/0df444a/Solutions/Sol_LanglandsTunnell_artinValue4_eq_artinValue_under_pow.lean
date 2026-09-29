-- Prove2me | solution 1 for LanglandsTunnell.artinValue4_eq_artinValue_under_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/01c9c806-3643-5ef2-951a-411eff951594

import Definitions.Def_LanglandsTunnell_C4Character
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2 LanglandsTunnell.P2.Artin FrobeniusDensity
open scoped Pointwise

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "fixFld"
namespace P1Filing
p2m_open "LanglandsTunnell"

private def ratPrime (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

section RelDeg

variable {G : Type*} [Group G] [Finite G] (H : Subgroup G) (σ : G)

private def IsRelDegree {G : Type*} [Group G] (H : Subgroup G) (σ : G) (n : ℕ) : Prop :=
  0 < n ∧ σ ^ n ∈ H ∧ ∀ m : ℕ, 0 < m → m < n → σ ^ m ∉ H

omit [Finite G] in
private theorem IsRelDegree.unique {n m : ℕ} (hn : IsRelDegree H σ n) (hm : IsRelDegree H σ m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact (hm.2.2 n hn.1 h hn.2.1).elim
  · exact h
  · exact (hn.2.2 m hm.1 h hm.2.1).elim

omit [Finite G] in
private theorem IsRelDegree.conj_iff {τ : G} (hτ : τ ∈ H) (n : ℕ) :
    IsRelDegree H (τ * σ * τ⁻¹) n ↔ IsRelDegree H σ n := by
  have key : ∀ k : ℕ, (τ * σ * τ⁻¹) ^ k ∈ H ↔ σ ^ k ∈ H := fun k => by
    rw [conj_pow]
    constructor
    · intro h
      have := H.mul_mem (H.mul_mem (H.inv_mem hτ) h) hτ
      simpa [mul_assoc] using this
    · intro h
      exact H.mul_mem (H.mul_mem hτ h) (H.inv_mem hτ)
  simp only [IsRelDegree, key]

open Classical in
private theorem isRelDegree_relDeg : IsRelDegree H σ (relDeg H σ) := by
  refine ⟨(Nat.find_spec (exists_pos_pow_mem H σ)).1, (Nat.find_spec (exists_pos_pow_mem H σ)).2,
    fun m hm hlt h => ?_⟩
  exact Nat.find_min (exists_pos_pow_mem H σ) hlt ⟨hm, h⟩

private theorem relDeg_pos : 0 < relDeg H σ := (isRelDegree_relDeg H σ).1

private theorem relDeg_dvd_of_pow_mem {m : ℕ} (hm : σ ^ m ∈ H) : relDeg H σ ∣ m := by
  have hn := isRelDegree_relDeg H σ
  by_contra hndvd
  have hpos : 0 < m % relDeg H σ :=
    Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
  have hlt : m % relDeg H σ < relDeg H σ := Nat.mod_lt _ hn.1
  refine hn.2.2 _ hpos hlt ?_
  have h := Nat.div_add_mod m (relDeg H σ)
  have hrew : σ ^ (m % relDeg H σ) = ((σ ^ relDeg H σ) ^ (m / relDeg H σ))⁻¹ * σ ^ m := by
    rw [← pow_mul, eq_inv_mul_iff_mul_eq, ← pow_add, h]
  rw [hrew]
  exact H.mul_mem (H.inv_mem (H.pow_mem hn.2.1 _)) hm

end RelDeg

section Transport

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

omit [IsGalois ℚ L] in
private theorem inertia_smul_eq_bot (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    (τ • Q).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : 𝓞 L, g • x - x ∈ τ • Q := fun x => AddSubgroup.mem_inertia.1 hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    refine AddSubgroup.mem_inertia.2 fun x => ?_
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

private theorem arithFrobAt_smul (τ : L ≃ₐ[ℚ] L) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)]
    [Finite (𝓞 L ⧸ (τ • Q))] (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q) = τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹ := by
  have h1 : IsArithFrobAt ℤ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)) (τ • Q) :=
    IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) (τ • Q)
  have h2 : IsArithFrobAt ℤ (τ * arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q * τ⁻¹) (τ • Q) :=
    (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end Transport

section GalInt

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (H : Subgroup (L ≃ₐ[ℚ] L))

private scoped instance isGaloisGroup_ringOfIntegers :
    IsGaloisGroup H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L) :=
  IsGaloisGroup.of_isFractionRing H (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L)) (𝓞 L)
    (FixedPoints.intermediateField H : IntermediateField ℚ L) L

end GalInt

section Qindep

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

private theorem artinValue_eq_chiGal_of_frob
    (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Finite (𝓞 L ⧸ Q)]
    (hQ : Q.under (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)) = v.asIdeal)
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) {n : ℕ}
    (hn : IsRelDegree (c8H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) n) :
    artinValue e hζ v = chiGal e hζ ⟨arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ^ n, hn.2.1⟩ := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI : (primeOver (c8H e) v).LiesOver v.asIdeal := ⟨(under_primeOver (c8H e) v).symm⟩
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeOver (c8H e) v) Q (c8H e)
  have hτ' : ((τ : L ≃ₐ[ℚ] L)) • primeOver (c8H e) v = Q := hτ
  subst hτ'
  have hI₀ : (primeOver (c8H e) v).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
    have h := inertia_smul_eq_bot ((τ : L ≃ₐ[ℚ] L))⁻¹ (((τ : L ≃ₐ[ℚ] L)) • primeOver (c8H e) v) hI
    rwa [inv_smul_smul] at h
  have hF := arithFrobAt_smul (τ : L ≃ₐ[ℚ] L) (primeOver (c8H e) v) hI₀
  have hn₀ : n = relDeg (c8H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c8H e) v)) := by
    rw [hF, IsRelDegree.conj_iff (c8H e) _ τ.2] at hn
    exact IsRelDegree.unique (c8H e) _ hn (isRelDegree_relDeg (c8H e) _)
  have hpow : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (((τ : L ≃ₐ[ℚ] L)) • primeOver (c8H e) v) ^ n
      = (τ : L ≃ₐ[ℚ] L) * seedFrob (c8H e) v * (τ : L ≃ₐ[ℚ] L)⁻¹ := by
    rw [hF, conj_pow, seedFrob, ← hn₀]
  have hmem : arithFrobAt ℤ (L ≃ₐ[ℚ] L) (((τ : L ≃ₐ[ℚ] L)) • primeOver (c8H e) v) ^ n ∈ c8H e := hn.2.1
  have key : (⟨_, hmem⟩ : ↥(c8H e)) = τ * ⟨seedFrob (c8H e) v, seedFrob_mem (c8H e) v⟩ * τ⁻¹ :=
    Subtype.ext hpow
  rw [artinValue_def, key, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

end Qindep

section ResidueHelpers

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

private theorem mk_pow_smul_of_isArithFrobAt {σ : G} {Q : Ideal B} (hF : IsArithFrobAt A σ Q)
    (n : ℕ) (x : B) :
    Ideal.Quotient.mk Q (σ ^ n • x)
      = Ideal.Quotient.mk Q x ^ (Nat.card (A ⧸ Q.under A) ^ n) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hx : Ideal.Quotient.mk Q (σ • x)
        = Ideal.Quotient.mk Q x ^ Nat.card (A ⧸ Q.under A) := by
      rw [← map_pow, Ideal.Quotient.eq]
      exact hF x
    rw [pow_succ, mul_smul, ih (σ • x), hx, ← pow_mul, pow_succ']

variable [Finite G] [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_card_pow_eq_self_of_pow_mem {H : Subgroup G} [SMulCommClass (↥H) C B]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {n : ℕ}
    (hmem : arithFrobAt A G Q ^ n ∈ H) (y : C ⧸ Q.under C) :
    y ^ (Nat.card (A ⧸ Q.under A) ^ n) = y := by
  have hF : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hfix : (arithFrobAt A G Q ^ n) • algebraMap C B c = algebraMap C B c := by
    have h : (⟨arithFrobAt A G Q ^ n, hmem⟩ : ↥H) • algebraMap C B c = algebraMap C B c := by
      rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    exact h
  have hq := mk_pow_smul_of_isArithFrobAt hF n (algebraMap C B c)
  rw [hfix] at hq
  rw [← map_pow, Ideal.Quotient.eq, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow,
    ← Ideal.Quotient.eq, map_pow]
  exact hq.symm

end ResidueHelpers

open Polynomial in
private theorem card_le_of_forall_pow_eq {R : Type*} [CommRing R] [IsDomain R] [Finite R] {q : ℕ} (hq : 1 < q)
    (h : ∀ y : R, y ^ q = y) : Nat.card R ≤ q := by
  classical
  haveI := Fintype.ofFinite R
  have hdeg : (X ^ q - X : R[X]).natDegree = q := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
    rw [natDegree_X]
    exact hq
  have hf0 : (X ^ q - X : R[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hroots : ∀ y : R, y ∈ (X ^ q - X : R[X]).roots := fun y =>
    (mem_roots hf0).2 (by simp [h y])
  calc Nat.card R = Fintype.card R := Nat.card_eq_fintype_card
    _ ≤ (X ^ q - X : R[X]).roots.toFinset.card :=
        Finset.card_le_card fun y _ => Multiset.mem_toFinset.2 (hroots y)
    _ ≤ Multiset.card (X ^ q - X : R[X]).roots := Multiset.toFinset_card_le _
    _ ≤ (X ^ q - X : R[X]).natDegree := card_roots' _
    _ = q := hdeg

private theorem card_int_quot_ratPrimeIdeal {ℓ : ℕ} : Nat.card (ℤ ⧸ ratPrimeIdeal ℓ) = ℓ := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv, Nat.card_zmod]

private theorem finite_int_quot_ratPrimeIdeal {ℓ : ℕ} [hℓ : Fact ℓ.Prime] : Finite (ℤ ⧸ ratPrimeIdeal ℓ) :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  Finite.of_equiv _ (Int.quotientSpanNatEquivZMod ℓ).toEquiv.symm

section RatPrimeHelpers

variable {L : Type} [Field L] [NumberField L]

private theorem natCast_mem_ratPrime_asIdeal (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ((ℓ : ℕ) : 𝓞 ℚ) ∈ (ratPrime ⟨ℓ, hℓ⟩).asIdeal := by
  have hid : (ratPrime ⟨ℓ, hℓ⟩).asIdeal
      = (Ideal.span {((ℓ : ℕ) : ℤ)}).comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    simp [ratPrime, Rat.HeightOneSpectrum.primesEquiv,
      IsDedekindDomain.HeightOneSpectrum.ofPrime_asIdeal]
  rw [hid, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

open Rat.HeightOneSpectrum in
private theorem under_eq_ratPrime_of_natCast_mem {E : IntermediateField ℚ L}
    (𝔓 : HeightOneSpectrum (𝓞 ↥E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hmem : ((ℓ : ℕ) : 𝓞 ↥E) ∈ 𝔓.asIdeal) :
    𝔓.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ := by
  set v : HeightOneSpectrum (𝓞 ℚ) := 𝔓.under (𝓞 ℚ) with hv_def
  have hmem_v : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have : algebraMap (𝓞 ℚ) (𝓞 ↥E) ((ℓ : ℕ) : 𝓞 ℚ) ∈ 𝔓.asIdeal := by
      rwa [map_natCast]
    exact this
  have hdvd : natGenerator v ∣ ℓ := by
    rw [natGenerator_dvd_iff]
    have h := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hmem_v
    rwa [map_natCast] at h
  have heq : natGenerator v = ℓ := (Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) hℓ).mp hdvd
  have happ : primesEquiv (R := 𝓞 ℚ) v = ⟨ℓ, hℓ⟩ := Subtype.ext heq
  rw [hv_def, ratPrime, ← happ, Equiv.symm_apply_apply]

private theorem card_quot_ratPrime (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card (𝓞 ℚ ⧸ (ratPrime ⟨ℓ, hℓ⟩).asIdeal) = ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hid : (ratPrime ⟨ℓ, hℓ⟩).asIdeal
      = (Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := by
    simp [ratPrime, Rat.HeightOneSpectrum.primesEquiv,
      IsDedekindDomain.HeightOneSpectrum.ofPrime_asIdeal]
  rw [hid]
  have hequiv := Ideal.quotientEquiv (Ideal.span {((ℓ : ℕ) : ℤ)})
    ((Ideal.span {((ℓ : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm)
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm rfl
  rw [← Nat.card_congr hequiv.toEquiv]
  exact card_int_quot_ratPrimeIdeal

end RatPrimeHelpers

section PowMem

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [Finite G]
  [Algebra.IsInvariant A B G] {C : Type*} [CommRing C] [Algebra C B]

private theorem pow_arithFrobAt_mem_of_card_under_eq_pow {H : Subgroup G}
    [SMulCommClass (↥H) C B] [Algebra.IsInvariant C B (↥H)]
    (Q : Ideal B) [Q.IsPrime] [Finite (B ⧸ Q)] {f : ℕ}
    (hcard : Nat.card (C ⧸ Q.under C) = Nat.card (A ⧸ Q.under A) ^ f)
    (hin : Q.inertia G = ⊥) : arithFrobAt A G Q ^ f ∈ H := by
  obtain ⟨s, hs⟩ := IsArithFrobAt.exists_of_isInvariant C (↥H) Q
  have hτ : IsArithFrobAt A (arithFrobAt A G Q) Q := IsArithFrobAt.arithFrobAt A G Q

  have key : ∀ x : B, (arithFrobAt A G Q ^ f) • x - (s : G) • x ∈ Q := by
    intro x
    have h1 := mk_pow_smul_of_isArithFrobAt hτ f x
    have h2 : (s : G) • x - x ^ (Nat.card (A ⧸ Q.under A) ^ f) ∈ Q := by
      have h := hs x
      rwa [hcard] at h
    rw [← Ideal.Quotient.eq, map_pow] at h2
    rw [← Ideal.Quotient.eq, h1, h2]

  have hmem : arithFrobAt A G Q ^ f * (s : G)⁻¹ ∈ Q.inertia G := by
    intro x
    have h := key ((s : G)⁻¹ • x)
    rwa [smul_inv_smul, ← mul_smul] at h
  rw [hin, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  rw [hmem]
  exact s.2

end PowMem

section ResidueDegree

variable {L : Type} [Field L] [NumberField L]

private theorem natCast_mem_under' (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ}
    (Q : Ideal (𝓞 L)) [hQl : Q.LiesOver (ratPrimeIdeal ℓ)] :
    ((ℓ : ℕ) : 𝓞 (↥(fixFld H))) ∈ Q.under (𝓞 (↥(fixFld H))) := by
  have h1 : ((ℓ : ℕ) : ℤ) ∈ ratPrimeIdeal ℓ := Ideal.mem_span_singleton_self _
  rw [hQl.over] at h1
  have h2 : algebraMap ℤ (𝓞 L) ((ℓ : ℕ) : ℤ) ∈ Q := Ideal.mem_comap.mp h1
  rw [Ideal.mem_comap, map_natCast]
  simpa using h2

variable [IsGalois ℚ L]

private theorem inertiaDeg_eq_relDeg (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (ratPrimeIdeal ℓ)] [Finite (𝓞 L ⧸ Q)]
    (hI : Q.inertia (L ≃ₐ[ℚ] L) = ⊥)
    (w : HeightOneSpectrum (𝓞 (↥(fixFld H)))) (hw : w.asIdeal = Q.under (𝓞 (↥(fixFld H)))) :
    (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal ‹_› (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  haveI hZmax : (Q.under ℤ).IsMaximal := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; infer_instance
  haveI hZfin : Finite (ℤ ⧸ Q.under ℤ) := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact finite_int_quot_ratPrimeIdeal
  haveI : Fintype (ℤ ⧸ Q.under ℤ) := Fintype.ofFinite _
  haveI hGG : IsGaloisGroup (↥H) (𝓞 (↥(fixFld H))) (𝓞 L) := isGaloisGroup_ringOfIntegers H
  haveI := hGG.commutes
  haveI := hGG.isInvariant
  have hcardZ : Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
    rw [← ‹Q.LiesOver (ratPrimeIdeal ℓ)›.over]; exact card_int_quot_ratPrimeIdeal

  haveI hkfin : Finite ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal) := by
    rw [hw]
    exact Finite.of_injective _
      (Ideal.quotientMap_injective (I := Q) (f := algebraMap (𝓞 (↥(fixFld H))) (𝓞 L)))
  haveI : Fintype ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal) := Fintype.ofFinite _
  haveI hkmax : w.asIdeal.IsMaximal := w.isMaximal

  have hunder : w.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ :=
    under_eq_ratPrime_of_natCast_mem w hℓ (by rw [hw]; exact natCast_mem_under' H Q)
  have hcb : Nat.card (𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal) = ℓ := by
    rw [hunder]; exact card_quot_ratPrime ℓ hℓ
  haveI : (w.under (𝓞 ℚ)).asIdeal.IsMaximal := (w.under (𝓞 ℚ)).isMaximal
  haveI hoverP : w.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩

  have hcardf : Nat.card ((𝓞 (↥(fixFld H))) ⧸ w.asIdeal)
      = ℓ ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
    letI := Ideal.Quotient.field (w.under (𝓞 ℚ)).asIdeal
    rw [Ideal.inertiaDeg_algebraMap, Module.natCard_eq_pow_finrank (K := 𝓞 ℚ ⧸ (w.under (𝓞 ℚ)).asIdeal), hcb]
  have hℓ1 : 1 < ℓ := hℓ.one_lt

  have hle : (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal ≤ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
    letI := Ideal.Quotient.field w.asIdeal
    have hpow : ∀ y : (𝓞 (↥(fixFld H))) ⧸ w.asIdeal,
        y ^ (ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)) = y := by
      rw [hw]
      intro y
      have h := pow_card_pow_eq_self_of_pow_mem (A := ℤ) (C := 𝓞 (↥(fixFld H))) (H := H) Q
        (isRelDegree_relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)).2.1 y
      rwa [hcardZ] at h
    have h1lt : 1 < ℓ ^ relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := Nat.one_lt_pow (relDeg_pos H _).ne' hℓ1
    have hcle := card_le_of_forall_pow_eq h1lt hpow
    rw [hcardf] at hcle
    exact (Nat.pow_le_pow_iff_right hℓ1).mp hcle

  have hge : relDeg H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) ≤ (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal := by
    have hcard' : Nat.card ((𝓞 (↥(fixFld H))) ⧸ Q.under (𝓞 (↥(fixFld H))))
        = Nat.card (ℤ ⧸ Q.under ℤ) ^ ((w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal) := by
      rw [hcardZ, ← hw, hcardf]
    have hmem := pow_arithFrobAt_mem_of_card_under_eq_pow (A := ℤ) (C := 𝓞 (↥(fixFld H))) (H := H) Q hcard' hI
    have hdvd := relDeg_dvd_of_pow_mem H _ hmem
    exact Nat.le_of_dvd (Ideal.inertiaDeg'_pos (w.under (𝓞 ℚ)).asIdeal w.asIdeal) hdvd
  exact le_antisymm hle hge

end ResidueDegree

section PrimeOverLiesOver

variable {L : Type} [Field L] [NumberField L]

private theorem asIdeal_under_int_eq_of_under_eq (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (w : HeightOneSpectrum (𝓞 ↥(fixFld H)))
    (hw : w.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩) :
    w.asIdeal.under ℤ = ratPrimeIdeal ℓ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine ((Int.ideal_span_isMaximal_of_prime ℓ).eq_of_le
    (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_).symm
  show Ideal.span {((ℓ : ℕ) : ℤ)} ≤ w.asIdeal.under ℤ
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
  have hmem := natCast_mem_ratPrime_asIdeal ℓ hℓ
  have hmem' : ((ℓ : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by rw [hw]; exact hmem
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem'
  exact hmem'

private theorem primeOver_liesOver_ratPrimeIdeal (H : Subgroup (L ≃ₐ[ℚ] L)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (w : HeightOneSpectrum (𝓞 ↥(fixFld H)))
    (hw : w.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩) :
    (primeOver H w).LiesOver (ratPrimeIdeal ℓ) := by
  constructor
  rw [← Ideal.under_under (A := ℤ) (B := 𝓞 ↥(fixFld H)) (C := 𝓞 L),
    under_primeOver, asIdeal_under_int_eq_of_under_eq H hℓ w hw]

end PrimeOverLiesOver

section Main

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

private abbrev K4 := (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)
private abbrev K8 := (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L)

private theorem inertia_primeOver_eq_bot
    (w : HeightOneSpectrum (𝓞 (K4 e)))
    (hw : (primeAbove (K4 e) L w).inertia (L ≃ₐ[ℚ] L) = ⊥) :
    (primeOver (c4H e) w).inertia (L ≃ₐ[ℚ] L) = ⊥ := by
  haveI : (primeOver (c4H e) w).LiesOver w.asIdeal := ⟨(under_primeOver (c4H e) w).symm⟩
  obtain ⟨τ, hτ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup w.asIdeal (primeAbove (K4 e) L w) (primeOver (c4H e) w) (c4H e)
  have hτ' : ((τ : L ≃ₐ[ℚ] L)) • primeAbove (K4 e) L w = primeOver (c4H e) w := hτ
  rw [← hτ']
  exact inertia_smul_eq_bot (τ : L ≃ₐ[ℚ] L) _ hw

omit [IsGalois ℚ L] in
private theorem under_primeOver_c4H_eq
    (w : HeightOneSpectrum (𝓞 (K4 e))) :
    (primeOver (c4H e) w).under (𝓞 (K8 e)) = (w.under (𝓞 (K8 e))).asIdeal := by
  rw [show (w.under (𝓞 (K8 e))).asIdeal = w.asIdeal.under (𝓞 (K8 e)) from rfl,
    ← under_primeOver (c4H e) w, Ideal.under_under]

private theorem seedFrob_c4H_eq_pow
    (w : HeightOneSpectrum (𝓞 (K4 e)))
    (hI : (primeOver (c4H e) w).inertia (L ≃ₐ[ℚ] L) = ⊥) :
    seedFrob (c4H e) w
      = (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) w)
          ^ relDeg (c8H e) (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver (c4H e) w)))
        ^ ((w.under (𝓞 (K8 e))).asIdeal.inertiaDeg' w.asIdeal) := by
  set Q₄ := primeOver (c4H e) w with hQ₄def
  set σ₄ := arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₄ with hσ₄def
  set v := w.under (𝓞 (K8 e)) with hvdef
  set f := v.asIdeal.inertiaDeg' w.asIdeal with hfdef
  show σ₄ ^ relDeg (c4H e) σ₄ = (σ₄ ^ relDeg (c8H e) σ₄) ^ f
  rw [← pow_mul]
  obtain ⟨⟨ℓ, hℓ⟩, hwℚ⟩ : ∃ p : Nat.Primes, w.under (𝓞 ℚ) = ratPrime p :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) (w.under (𝓞 ℚ)),
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply (w.under (𝓞 ℚ))).symm⟩
  haveI : Q₄.LiesOver (ratPrimeIdeal ℓ) :=
    hQ₄def ▸ primeOver_liesOver_ratPrimeIdeal (c4H e) hℓ w hwℚ
  have hvℚ : v.under (𝓞 ℚ) = ratPrime ⟨ℓ, hℓ⟩ := by
    rw [hvdef, ← hwℚ]
    exact HeightOneSpectrum.ext (Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 (K8 e)) w.asIdeal)
  have h4 : (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' w.asIdeal = relDeg (c4H e) σ₄ :=
    inertiaDeg_eq_relDeg (L := L) (c4H e) hℓ Q₄ hI w (under_primeOver (c4H e) w).symm
  have hQv : Q₄.under (𝓞 (K8 e)) = v.asIdeal := hQ₄def ▸ under_primeOver_c4H_eq e w
  have h8 : (v.under (𝓞 ℚ)).asIdeal.inertiaDeg' v.asIdeal = relDeg (c8H e) σ₄ :=
    inertiaDeg_eq_relDeg (L := L) (c8H e) hℓ Q₄ hI v hQv.symm
  have hunder_eq : v.under (𝓞 ℚ) = w.under (𝓞 ℚ) := by rw [hvℚ, hwℚ]
  haveI : (w.under (𝓞 ℚ)).asIdeal.IsMaximal := (w.under (𝓞 ℚ)).isMaximal
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : v.asIdeal.LiesOver (w.under (𝓞 ℚ)).asIdeal := ⟨by rw [← hunder_eq]; rfl⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have htow := Ideal.inertiaDeg_algebra_tower (w.under (𝓞 ℚ)).asIdeal v.asIdeal w.asIdeal
  have h8' : (w.under (𝓞 ℚ)).asIdeal.inertiaDeg' v.asIdeal = relDeg (c8H e) σ₄ := hunder_eq ▸ h8
  have heq : relDeg (c4H e) σ₄ = relDeg (c8H e) σ₄ * f := by rw [← h4, htow, h8']
  exact congrArg (σ₄ ^ ·) heq

end Main

end LanglandsTunnell.P1Filing
p2m_reactivate "P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow.LanglandsTunnell P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow.LanglandsTunnell.P1Filing"
p2m_reactivate "P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow.LanglandsTunnell"

open LanglandsTunnell.P1Filing in

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)
    (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L)))
    (hw : (primeAbove (FixedPoints.intermediateField (c4H e) : IntermediateField ℚ L) L w).inertia
      (L ≃ₐ[ℚ] L) = ⊥) :
    artinValue4 e hζ w
      = artinValue e hζ (w.under
          (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) ^
        ((w.under (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))).asIdeal.inertiaDeg'
          w.asIdeal) := by
  set Q₄ := primeOver (c4H e) w with hQ₄def
  set σ₄ := arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₄ with hσ₄def
  set v := w.under (𝓞 (K8 e)) with hvdef
  set f := v.asIdeal.inertiaDeg' w.asIdeal with hfdef
  have hI₄ : Q₄.inertia (L ≃ₐ[ℚ] L) = ⊥ := inertia_primeOver_eq_bot e w hw
  have hQv : Q₄.under (𝓞 (K8 e)) = v.asIdeal := under_primeOver_c4H_eq e w
  have hn₈ : IsRelDegree (c8H e) σ₄ (relDeg (c8H e) σ₄) := isRelDegree_relDeg (c8H e) σ₄
  have hav : artinValue e hζ v = chiGal e hζ ⟨σ₄ ^ relDeg (c8H e) σ₄, hn₈.2.1⟩ :=
    artinValue_eq_chiGal_of_frob e hζ v Q₄ hQv hI₄ hn₈
  have hpow : seedFrob (c4H e) w = (σ₄ ^ relDeg (c8H e) σ₄) ^ f := seedFrob_c4H_eq_pow e w hI₄
  have hLHS : artinValue4 e hζ w
      = chiGal e hζ ⟨seedFrob (c4H e) w, c4H_le_c8H e (seedFrob_mem (c4H e) w)⟩ := by
    rw [artinValue4_def, chiGal4_apply]
    rfl
  rw [hLHS, hav, ← map_pow]
  congr 1
  exact Subtype.ext hpow

end
p2m_reactivate "P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow.LanglandsTunnell P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow.LanglandsTunnell.P1Filing"

end S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow
end P2MW
export P2MW.S_LanglandsTunnell_artinValue4_eq_artinValue_under_pow (solution)

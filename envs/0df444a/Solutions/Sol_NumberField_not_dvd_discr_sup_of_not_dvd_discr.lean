-- Prove2me | solution 1 for NumberField.not_dvd_discr_sup_of_not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T10:46:49.81373+00:00
-- url     : https://prove2.me/submissions/25db8dbb-7b35-47fb-b875-d40bad583161

import Definitions.Def_MTT_Arithmetic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open NumberField

namespace AgentLDisc

theorem dvr_of_fu (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] :
    IsDedekindDomainDvr B where
  __ := IsNoetherianRing.of_finite A B
  is_dvr_at_nonzero_prime := by
    intro q hq hqp
    let q' := IsLocalRing.maximalIdeal (Localization.AtPrime q)
    suffices q'.IsPrincipal from ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
      (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp this
    let p := q.under A
    let := Localization.AtPrime.algebraOfLiesOver p q
    have : p.IsMaximal := (hqp.under A).isMaximal (q.under_ne_bot A hq)
    let : Field (A ⧸ p) := Ideal.Quotient.field p
    have := IsArtinianRing.of_finite (A ⧸ p) (B ⧸ p.map (algebraMap A B))
    suffices q' = (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) by
      rw [this, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q),
        ← Ideal.map_map]
      infer_instance
    rw [← (Algebra.FormallyUnramified.isRadical_map_isMaximal A B p).radical,
      IsLocalization.map_radical q.primeCompl,
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q,
      Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap A B))),
      IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk Ideal.map_comap_le⟩

lemma fu_away (K : Type*) [Field K] [NumberField K] (N : ℤ) (hN : discr K ∣ N) :
    Algebra.FormallyUnramified ℤ
      (Localization (Algebra.algebraMapSubmonoid (𝓞 K) (Submonoid.powers N))) := by
  have h : Algebra.algebraMapSubmonoid (𝓞 K) (Submonoid.powers N) =
      Submonoid.powers (algebraMap ℤ (𝓞 K) N) := Submonoid.map_powers _ _
  rw [h, ← Algebra.basicOpen_subset_unramifiedLocus_iff]
  intro Q hQ
  have hQ' : algebraMap ℤ (𝓞 K) N ∉ Q.asIdeal := hQ
  show Algebra.IsUnramifiedAt ℤ Q.asIdeal
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  apply hQ'
  obtain ⟨c, rfl⟩ := hN
  have := Ideal.le_of_dvd hdvd (NumberField.discr_mem_differentIdeal K (𝓞 K))
  rw [map_mul]
  exact Q.asIdeal.mul_mem_right _ (by simpa using this)

lemma mem_of_isIntegral {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (A : Subalgebra R S) [IsIntegrallyClosed A]
    (y : S) (hy : IsIntegral A y) (m : A) (hm : m ≠ 0) (hmy : (m : S) * y ∈ A) : y ∈ A := by
  obtain ⟨p, hmon, hp⟩ := hy
  let c : A := ⟨_, hmy⟩
  let K := FractionRing A
  have hfm : algebraMap A K m ≠ 0 := by
    intro h
    exact hm (IsFractionRing.injective A K (by rw [h, map_zero]))
  have hc0 : (Polynomial.scaleRoots p m).eval c = 0 := by
    apply Subtype.val_injective
    have h2 := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap A S) y m
    rw [hp, mul_zero] at h2
    have : algebraMap A S m * y = algebraMap A S c := rfl
    rw [this, Polynomial.eval₂_at_apply] at h2
    simpa using h2
  have hint : IsIntegral A (algebraMap A K c / algebraMap A K m) := by
    refine ⟨p, hmon, ?_⟩
    have h1 := Polynomial.scaleRoots_eval₂_mul (p := p) (algebraMap A K)
      (algebraMap A K c / algebraMap A K m) m
    rw [mul_div_cancel₀ _ hfm, Polynomial.eval₂_at_apply, hc0, map_zero] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hfm)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [eq_div_iff hfm, ← map_mul] at ha
  have hca : a * m = c := IsFractionRing.injective A K ha
  have hm' : (m : S) ≠ 0 := fun h => hm (Subtype.val_injective (by simpa using h))
  have key : (m : S) * y = (m : S) * a := by
    have := congrArg Subtype.val hca
    simp only [Subalgebra.coe_mul] at this
    change (m : S) * y = _
    rw [mul_comm (m : S) (a : S)]
    exact this.symm
  rw [mul_left_cancel₀ hm' key]
  exact a.2

lemma fu_L (K1 K2 L : Type*) [Field K1] [Field K2] [Field L] [NumberField K1] [NumberField K2]
    [NumberField L] (g1 : 𝓞 K1 →+* 𝓞 L) (g2 : 𝓞 K2 →+* 𝓞 L)
    (hgen : ∀ x : 𝓞 L, ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 L) * x ∈ g1.range ⊔ g2.range)
    (N : ℤ) (hN0 : N ≠ 0) (hN1 : discr K1 ∣ N) (hN2 : discr K2 ∣ N) :
    Algebra.FormallyUnramified ℤ
      (Localization (Algebra.algebraMapSubmonoid (𝓞 L) (Submonoid.powers N))) := by
  let M := Submonoid.powers N
  let Z := Localization M
  let B1 := Localization (Algebra.algebraMapSubmonoid (𝓞 K1) M)
  let B2 := Localization (Algebra.algebraMapSubmonoid (𝓞 K2) M)
  let O := Localization (Algebra.algebraMapSubmonoid (𝓞 L) M)
  have hM : M ≤ nonZeroDivisors ℤ := powers_le_nonZeroDivisors_of_noZeroDivisors hN0
  haveI : IsDomain Z := IsLocalization.isDomain_localization hM
  haveI : IsDedekindDomain Z := IsLocalization.isDedekindDomain ℤ hM Z
  have hMO : Algebra.algebraMapSubmonoid (𝓞 L) M ≤ nonZeroDivisors (𝓞 L) :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ hM
  haveI : IsDomain O := IsLocalization.isDomain_localization hMO
  haveI : Module.Finite Z B1 := Module.Finite.of_isLocalization ℤ (𝓞 K1) M
  haveI : Module.Finite Z B2 := Module.Finite.of_isLocalization ℤ (𝓞 K2) M
  haveI : Module.Finite Z O := Module.Finite.of_isLocalization ℤ (𝓞 L) M
  haveI : Algebra.FormallyUnramified ℤ B1 := fu_away K1 N hN1
  haveI : Algebra.FormallyUnramified ℤ B2 := fu_away K2 N hN2
  haveI : Algebra.FormallyUnramified Z B1 := .of_restrictScalars ℤ Z B1
  haveI : Algebra.FormallyUnramified Z B2 := .of_restrictScalars ℤ Z B2
  haveI : Algebra.FormallyUnramified Z (TensorProduct Z B1 B2) :=
    Algebra.FormallyUnramified.comp Z B1 (TensorProduct Z B1 B2)
  let φ1 : B1 →ₐ[Z] O := IsLocalization.mapₐ M Z B1 O g1.toIntAlgHom
  let φ2 : B2 →ₐ[Z] O := IsLocalization.mapₐ M Z B2 O g2.toIntAlgHom
  let Φ := Algebra.TensorProduct.productMap φ1 φ2
  let C : Subalgebra Z O := Φ.range
  haveI : Algebra.FormallyUnramified Z C :=
    .of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  haveI : Module.Finite Z C :=
    Module.Finite.of_surjective Φ.rangeRestrict.toLinearMap Φ.rangeRestrict_surjective
  haveI : IsDedekindDomainDvr C := dvr_of_fu Z C
  -- images of the rings of integers lie in C
  have hC1 : ∀ a : 𝓞 K1, algebraMap (𝓞 L) O (g1 a) ∈ C := by
    intro a
    have : φ1 (algebraMap (𝓞 K1) B1 a) = algebraMap (𝓞 L) O (g1 a) := by
      simp [φ1, IsLocalization.map_eq]
    rw [← this]
    have hle : φ1.range ≤ C := by
      simp only [C, Φ, Algebra.TensorProduct.productMap_range]; exact le_sup_left
    exact hle ⟨_, rfl⟩
  have hC2 : ∀ a : 𝓞 K2, algebraMap (𝓞 L) O (g2 a) ∈ C := by
    intro a
    have : φ2 (algebraMap (𝓞 K2) B2 a) = algebraMap (𝓞 L) O (g2 a) := by
      simp [φ2, IsLocalization.map_eq]
    rw [← this]
    have hle : φ2.range ≤ C := by
      simp only [C, Φ, Algebra.TensorProduct.productMap_range]; exact le_sup_right
    exact hle ⟨_, rfl⟩
  have hC0 : ∀ c ∈ g1.range ⊔ g2.range, algebraMap (𝓞 L) O c ∈ C := by
    intro c hc
    have : g1.range ⊔ g2.range ≤ (C.toSubring.comap (algebraMap (𝓞 L) O)) := by
      apply sup_le
      · rintro _ ⟨a, rfl⟩; exact hC1 a
      · rintro _ ⟨a, rfl⟩; exact hC2 a
    exact this hc
  have hinjO : Function.Injective (algebraMap (𝓞 L) O) := IsLocalization.injective O hMO
  have htop : C = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (𝓞 L) M) y
    obtain ⟨m, hm0, hmx⟩ := hgen x
    obtain ⟨n, hn, hns⟩ := s.2
    have hn0 : n ≠ 0 := nonZeroDivisors.ne_zero (hM hn)
    have hy : IsIntegral C (IsLocalization.mk' O x s) :=
      (Algebra.IsIntegral.isIntegral (R := Z) (IsLocalization.mk' O x s)).tower_top
    have hcast : ∀ k : ℤ, k ≠ 0 → ((k : ℤ) : O) ≠ 0 := by
      intro k hk h
      have : algebraMap (𝓞 L) O ((k : ℤ) : 𝓞 L) = 0 := by rw [map_intCast]; exact h
      rw [← map_zero (algebraMap (𝓞 L) O)] at this
      exact hk (by exact_mod_cast hinjO this)
    refine mem_of_isIntegral C _ hy ⟨(m : O) * (n : O), mul_mem (intCast_mem C m) (intCast_mem C n)⟩
      ?_ ?_
    · intro h
      have h' : (m : O) * (n : O) = 0 := congrArg Subtype.val h
      exact mul_ne_zero (hcast m hm0) (hcast n hn0) h'
    · have hspec := IsLocalization.mk'_spec O x s
      have hs : (s : 𝓞 L) = (n : 𝓞 L) := by rw [← hns]; simp
      have : (m : O) * (n : O) * IsLocalization.mk' O x s =
          algebraMap (𝓞 L) O ((m : 𝓞 L) * x) := by
        rw [map_mul, ← hspec, hs, map_intCast, map_intCast]
        ring
      simp only at this ⊢
      rw [this]
      exact hC0 _ hmx
  haveI : Algebra.FormallyUnramified Z O :=
    .of_surjective Φ (fun y => by
      have : y ∈ C := by rw [htop]; exact Algebra.mem_top
      exact this)
  exact Algebra.FormallyUnramified.comp ℤ Z O

theorem main_abs (K1 K2 L : Type*) [Field K1] [Field K2] [Field L] [NumberField K1]
    [NumberField K2] [NumberField L] (g1 : 𝓞 K1 →+* 𝓞 L) (g2 : 𝓞 K2 →+* 𝓞 L)
    (hgen : ∀ x : 𝓞 L, ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 L) * x ∈ g1.range ⊔ g2.range)
    {l : ℤ} (hl : Prime l) (h₁ : ¬ l ∣ discr K1) (h₂ : ¬ l ∣ discr K2) : ¬ l ∣ discr L := by
  set N := discr K1 * discr K2 with hNdef
  have hN0 : N ≠ 0 := mul_ne_zero (discr_ne_zero K1) (discr_ne_zero K2)
  have hFU := fu_L K1 K2 L g1 g2 hgen N hN0 (dvd_mul_right _ _) (dvd_mul_left _ _)
  have h : Algebra.algebraMapSubmonoid (𝓞 L) (Submonoid.powers N) =
      Submonoid.powers (algebraMap ℤ (𝓞 L) N) := Submonoid.map_powers _ _
  rw [h, ← Algebra.basicOpen_subset_unramifiedLocus_iff] at hFU
  rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) hl]
  intro P hP hlP
  have hNP : algebraMap ℤ (𝓞 L) N ∉ P := by
    intro hNP
    have hcomap : (P.comap (algebraMap ℤ (𝓞 L))).IsPrime := Ideal.comap_isPrime _ _
    have hle : Ideal.span {l} ≤ P.comap (algebraMap ℤ (𝓞 L)) := by
      rw [Ideal.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simpa using hlP
    have hmax : (Ideal.span {l} : Ideal ℤ).IsMaximal :=
      ((Ideal.span_singleton_prime hl.ne_zero).mpr hl).isMaximal
        (by simpa using hl.ne_zero)
    have heq := hmax.eq_of_le hcomap.ne_top hle
    have hNmem : N ∈ Ideal.span {l} := by rw [heq]; exact hNP
    rw [Ideal.mem_span_singleton] at hNmem
    rcases hl.dvd_or_dvd hNmem with h | h
    · exact h₁ h
    · exact h₂ h
  exact hFU (show (⟨P, hP⟩ : PrimeSpectrum (𝓞 L)) ∈ PrimeSpectrum.basicOpen _ from hNP)

end AgentLDisc

theorem _root_.solution
    (K₁ K₂ : IntermediateField ℚ MTT.Qbar)
    [NumberField K₁] [NumberField K₂]
    {l : ℤ} (hl : Prime l)
    (h₁ : ¬ l ∣ NumberField.discr K₁)
    (h₂ : ¬ l ∣ NumberField.discr K₂) :
    letI : NumberField ↥(K₁ ⊔ K₂) :=
      { to_charZero := inferInstance
        to_finiteDimensional := IntermediateField.finiteDimensional_sup K₁ K₂ }
    ¬ l ∣ NumberField.discr ↥(K₁ ⊔ K₂) := by
  letI : NumberField ↥(K₁ ⊔ K₂) :=
    { to_charZero := inferInstance
      to_finiteDimensional := IntermediateField.finiteDimensional_sup K₁ K₂ }
  let L := ↥(K₁ ⊔ K₂)
  let g1 : 𝓞 K₁ →+* 𝓞 L :=
    RingOfIntegers.mapRingHom (IntermediateField.inclusion le_sup_left : K₁ →ₐ[ℚ] L).toRingHom
  let g2 : 𝓞 K₂ →+* 𝓞 L :=
    RingOfIntegers.mapRingHom (IntermediateField.inclusion le_sup_right : K₂ →ₐ[ℚ] L).toRingHom
  refine AgentLDisc.main_abs K₁ K₂ L g1 g2 ?_ hl h₁ h₂
  intro x
  let ι : 𝓞 L →+* MTT.Qbar := (K₁ ⊔ K₂).val.toRingHom.comp (algebraMap (𝓞 L) L)
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp RingOfIntegers.coe_injective
  let T : Subring (𝓞 L) := g1.range ⊔ g2.range
  let S : Subalgebra ℚ MTT.Qbar :=
    { carrier := {w | ∃ m : ℤ, m ≠ 0 ∧ ∃ c ∈ T, ι c = m * w}
      mul_mem' := by
        rintro w1 w2 ⟨m1, hm1, c1, hc1, e1⟩ ⟨m2, hm2, c2, hc2, e2⟩
        refine ⟨m1 * m2, mul_ne_zero hm1 hm2, c1 * c2, T.mul_mem hc1 hc2, ?_⟩
        rw [map_mul, e1, e2]; push_cast; ring
      add_mem' := by
        rintro w1 w2 ⟨m1, hm1, c1, hc1, e1⟩ ⟨m2, hm2, c2, hc2, e2⟩
        refine ⟨m1 * m2, mul_ne_zero hm1 hm2, (m2 : 𝓞 L) * c1 + (m1 : 𝓞 L) * c2,
          T.add_mem (T.mul_mem (intCast_mem T _) hc1) (T.mul_mem (intCast_mem T _) hc2), ?_⟩
        rw [map_add, map_mul, map_mul, e1, e2, map_intCast, map_intCast]; push_cast; ring
      algebraMap_mem' := by
        intro r
        refine ⟨r.den, by exact_mod_cast r.den_nz, (r.num : 𝓞 L), intCast_mem T _, ?_⟩
        rw [map_intCast, eq_ratCast]
        have : (r.num : ℚ) = r.den * r := by
          rw [mul_comm]; exact (Rat.mul_den_eq_num r).symm
        exact_mod_cast congrArg (fun q : ℚ => (q : MTT.Qbar)) this }
  have := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have := Algebra.IsAlgebraic.trans ℤ ℚ K₁
  have := Algebra.IsAlgebraic.trans ℤ ℚ K₂
  have hK1 : K₁.toSubalgebra ≤ S := by
    intro w hw
    let k : K₁ := ⟨w, hw⟩
    obtain ⟨y, hy0, hyint⟩ :=
      IsAlgebraic.exists_integral_multiple (R := ℤ) (Algebra.IsAlgebraic.isAlgebraic k)
    refine ⟨y, hy0, g1 ⟨y • k, hyint⟩, le_sup_left (a := g1.range) ⟨_, rfl⟩, ?_⟩
    change ((y • k : K₁) : MTT.Qbar) = y * w
    simp [k, zsmul_eq_mul]
  have hK2 : K₂.toSubalgebra ≤ S := by
    intro w hw
    let k : K₂ := ⟨w, hw⟩
    obtain ⟨y, hy0, hyint⟩ :=
      IsAlgebraic.exists_integral_multiple (R := ℤ) (Algebra.IsAlgebraic.isAlgebraic k)
    refine ⟨y, hy0, g2 ⟨y • k, hyint⟩, le_sup_right (a := g1.range) ⟨_, rfl⟩, ?_⟩
    change ((y • k : K₂) : MTT.Qbar) = y * w
    simp [k, zsmul_eq_mul]
  have hsup : (K₁ ⊔ K₂).toSubalgebra ≤ S := by
    rw [IntermediateField.sup_toSubalgebra_of_left]
    exact sup_le hK1 hK2
  have hx : ((x : L) : MTT.Qbar) ∈ S := hsup (x : L).2
  obtain ⟨m, hm0, c, hc, e⟩ := hx
  refine ⟨m, hm0, ?_⟩
  have : c = (m : 𝓞 L) * x := hι (by rw [e, map_mul, map_intCast]; rfl)
  rw [← this]; exact hc

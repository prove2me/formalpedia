-- Prove2me | solution 1 for NumberField.sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/38cef656-1e60-5827-8c54-c4011dbdba04

import Mathlib
import Definitions.Def_FrobeniusDensity_PrimeSums
import Definitions.Def_NumberField_PrimeNormSums
import Theorems.Thm_FrobeniusDensity_tailSum_le
import Theorems.Thm_NumberField_exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension
p2m_attr_erase "instance" "Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"

set_option autoImplicit false

noncomputable section

namespace P2mCycloDensity

open NumberField IsDedekindDomain NumberField.PrimeNormSum Filter Topology
open scoped Classical

set_option linter.unusedSectionVars false

section OverPrime

variable (F : Type*) [Field F]

theorem under_eq_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)} (hQ : Q ≠ ⊤)
    (hqQ : (q : 𝓞 F) ∈ Q) : Q.under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hq)).irreducible
  have h1 : Ideal.span {(q : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap,
      map_natCast]
    exact hqQ
  exact (hmax.eq_of_le (Ideal.comap_ne_top _ hQ) h1).symm

theorem card_quotient_under_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)}
    (hQ : Q ≠ ⊤) (hqQ : (q : 𝓞 F) ∈ Q) : Nat.card (ℤ ⧸ Q.under ℤ) = q := by
  rw [under_eq_of_natCast_mem F hq hQ hqQ,
    Nat.card_congr (Int.quotientSpanNatEquivZMod q).toEquiv, Nat.card_zmod]

variable [NumberField F]

theorem finite_setOf_isPrime_le {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    {Q : Ideal (𝓞 F) | Q.IsPrime ∧ I ≤ Q}.Finite := by
  haveI : Finite ((𝓞 F) ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Finite (Ideal ((𝓞 F) ⧸ I)) :=
    Finite.of_injective (fun J : Ideal ((𝓞 F) ⧸ I) => (J : Set ((𝓞 F) ⧸ I)))
      fun _ _ h => SetLike.coe_injective h
  refine Set.Finite.of_finite_image (f := fun Q => Q.map (Ideal.Quotient.mk I))
    (Set.toFinite _) ?_
  rintro Q₁ ⟨-, hIQ₁⟩ Q₂ ⟨-, hIQ₂⟩ heq
  have key : ∀ Q : Ideal (𝓞 F), I ≤ Q →
      (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = Q := by
    intro Q hIQ
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIQ]
  rw [← key Q₁ hIQ₁, ← key Q₂ hIQ₂]
  exact congrArg _ heq

theorem finite_setOf_isMaximal_natCast_mem {p : ℕ} (hp : p.Prime) :
    {P : Ideal (𝓞 F) | P.IsMaximal ∧ (p : 𝓞 F) ∈ P}.Finite := by
  refine (finite_setOf_isPrime_le F (I := Ideal.span {(p : 𝓞 F)}) ?_).subset ?_
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr hp.ne_zero
  · rintro P ⟨hP, hpP⟩
    exact ⟨hP.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr hpP⟩

theorem ncard_setOf_isMaximal_natCast_mem_le {p : ℕ} (hp : p.Prime) :
    {P : Ideal (𝓞 F) | P.IsMaximal ∧ (p : 𝓞 F) ∈ P}.ncard ≤ Module.finrank ℚ F := by
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hsub : {P : Ideal (𝓞 F) | P.IsMaximal ∧ (p : 𝓞 F) ∈ P} ⊆
      ↑(IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 F)) := by
    rintro P ⟨hP, hpP⟩
    rw [IsDedekindDomain.coe_primesOverFinset hne]
    exact ⟨hP.isPrime, ⟨(under_eq_of_natCast_mem F hp hP.ne_top hpP).symm⟩⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (S := 𝓞 F) ℚ F hne

end OverPrime

section Pack

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]
  (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} E L]

theorem algEquiv_eq_of_apply_eq {ζ : L} (hζ : IsPrimitiveRoot ζ m) {σ τ : L ≃ₐ[E] L}
    (h : σ ζ = τ ζ) : σ = τ := by
  apply hζ.autToPow_injective E
  have hσ := hζ.autToPow_spec E σ
  have hτ := hζ.autToPow_spec E τ
  have hpow : ζ ^ ((hζ.autToPow E σ : ZMod m)).val = ζ ^ ((hζ.autToPow E τ : ZMod m)).val := by
    rw [hσ, hτ, h]
  have hval := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow
  exact Units.ext (ZMod.val_injective m hval)

theorem apply_eq_pow_of_cast_eq {ζ : L} (hζ : IsPrimitiveRoot ζ m) (τ : L ≃ₐ[E] L) {p : ℕ}
    (h : (p : ZMod m) = ((hζ.autToPow E τ : (ZMod m)ˣ) : ZMod m)) : τ ζ = ζ ^ p := by
  have hspec := hζ.autToPow_spec E τ
  rw [← h, ZMod.val_natCast] at hspec
  rw [← hspec]
  conv_rhs => rw [← Nat.mod_add_div p m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem exists_isArithFrobAt_int [IsGalois E L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
    (τ : L ≃ₐ[E] L) {p : ℕ} (hp : p.Prime) (v : Ideal (𝓞 E)) [hv : v.IsMaximal]
    (hvp : Ideal.absNorm v = p) (hτ : τ ζ = ζ ^ p) :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ (p : 𝓞 L) ∈ Q ∧ Q.under (𝓞 E) = v ∧ IsArithFrobAt ℤ τ Q := by

  have hcop : p.Coprime m := by
    have hprim : IsPrimitiveRoot (ζ ^ p) m := by
      rw [← hτ]
      exact hζ.map_of_injective τ.injective
    exact (hζ.pow_iff_coprime (NeZero.pos m) p).mp hprim

  have hker : RingHom.ker (algebraMap (𝓞 E) (𝓞 L)) ≤ v := by
    have hinj : Function.Injective (algebraMap (𝓞 E) (𝓞 L)) := by
      intro x y hxy
      have h' : algebraMap (𝓞 E) L x = algebraMap (𝓞 E) L y := by
        rw [IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L) L,
          IsScalarTower.algebraMap_apply (𝓞 E) (𝓞 L) L, hxy]
      rw [IsScalarTower.algebraMap_apply (𝓞 E) E L, IsScalarTower.algebraMap_apply (𝓞 E) E L] at h'
      exact RingOfIntegers.coe_injective ((algebraMap E L).injective h')
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨Q, hQmax, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v hker
  haveI : Q.IsMaximal := hQmax
  have hunder : Q.under (𝓞 E) = v := hQv

  have hpv : (p : 𝓞 E) ∈ v := by rw [← hvp]; exact Ideal.absNorm_mem v
  have hpQ : (p : 𝓞 L) ∈ Q := by
    have : algebraMap (𝓞 E) (𝓞 L) (p : 𝓞 E) ∈ Q := by
      rw [← Ideal.mem_comap]
      show (p : 𝓞 E) ∈ Q.under (𝓞 E)
      rw [hunder]
      exact hpv
    rwa [map_natCast] at this

  have hcardE : Nat.card (𝓞 E ⧸ Q.under (𝓞 E)) = p := by
    rw [hunder, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hvp]
  have hQtop : Q ≠ ⊤ := hQmax.ne_top
  have hcardZ : Nat.card (ℤ ⧸ Q.under ℤ) = p := card_quotient_under_of_natCast_mem L hp hQtop hpQ

  have hmQ : (m : 𝓞 L) ∉ Q := by
    intro hm
    have hmZ : (m : ℤ) ∈ Q.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hm
    rw [under_eq_of_natCast_mem L hp hQtop hpQ, Ideal.mem_span_singleton] at hmZ
    have hpm : p ∣ m := by exact_mod_cast hmZ
    have hp1 : p = 1 := Nat.Coprime.eq_one_of_dvd hcop hpm
    exact hp.one_lt.ne' hp1

  haveI : Finite (𝓞 L ⧸ Q) := Q.finiteQuotientOfFreeOfNeBot (by
    rintro rfl
    have : (p : 𝓞 L) = 0 := (Ideal.mem_bot).mp hpQ
    exact hp.ne_zero (by exact_mod_cast this))
  set φ : L ≃ₐ[E] L := arithFrobAt (𝓞 E) (L ≃ₐ[E] L) Q with hφdef
  have hφ : IsArithFrobAt (𝓞 E) φ Q := IsArithFrobAt.arithFrobAt (𝓞 E) (L ≃ₐ[E] L) Q

  set ζ' : 𝓞 L := hζ.toInteger with hζ'def
  have hζ'pow : ζ' ^ m = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hφζ' : φ • ζ' = ζ' ^ p := by
    have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hφ hζ'pow hmQ
    rw [hcardE] at h
    exact h
  have hφζ : φ ζ = ζ ^ p := by
    have h := congrArg (fun x : 𝓞 L => (x : L)) hφζ'
    simp only [map_pow] at h
    simp [hζ'def, hζ.coe_toInteger] at h
    exact h

  have hφτ : φ = τ := algEquiv_eq_of_apply_eq m hζ (hφζ.trans hτ.symm)
  refine ⟨Q, hQmax, hpQ, hunder, ?_⟩
  intro x
  have hx := hφ x
  rw [hcardE, hφτ] at hx
  rw [hcardZ]
  exact hx

end Pack

section Count

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]
  [IsGalois E L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} E L]

def frobSet (τ : L ≃ₐ[E] L) (p : ℕ) : Set (Ideal (𝓞 L)) :=
  {P | P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧ IsArithFrobAt ℤ τ P}

omit [IsGalois E L] [NeZero m] [IsCyclotomicExtension {m} E L] in
theorem frobSet_finite (τ : L ≃ₐ[E] L) {p : ℕ} (hp : p.Prime) : (frobSet τ p).Finite :=
  (finite_setOf_isMaximal_natCast_mem L hp).subset fun _ h => ⟨h.1, h.2.1⟩

omit [IsGalois E L] [NeZero m] [IsCyclotomicExtension {m} E L] in

theorem ncard_frobSet_le (τ : L ≃ₐ[E] L) {p : ℕ} (hp : p.Prime) :
    (frobSet τ p).ncard ≤ Module.finrank ℚ L :=
  (Set.ncard_le_ncard (show frobSet τ p ⊆ {P : Ideal (𝓞 L) | P.IsMaximal ∧ (p : 𝓞 L) ∈ P} from
      fun _ h => ⟨h.1, h.2.1⟩) (finite_setOf_isMaximal_natCast_mem L hp)).trans
    (ncard_setOf_isMaximal_natCast_mem_le L hp)

theorem card_le_ncard_frobSet {ζ : L} (hζ : IsPrimitiveRoot ζ m) (τ : L ≃ₐ[E] L) {p : ℕ}
    (hp : p.Prime) (hpa : (p : ZMod m) = ((hζ.autToPow E τ : (ZMod m)ˣ) : ZMod m))
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ v ∈ S, Ideal.absNorm v.asIdeal = p) :
    S.card ≤ (frobSet τ p).ncard := by
  have hτ : τ ζ = ζ ^ p := apply_eq_pow_of_cast_eq m hζ τ hpa
  have hex : ∀ v ∈ S, ∃ Q : Ideal (𝓞 L), Q ∈ frobSet τ p ∧ Q.under (𝓞 E) = v.asIdeal := by
    intro v hv
    haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    obtain ⟨Q, hQ, hpQ, hQv, hfr⟩ := exists_isArithFrobAt_int m hζ τ hp v.asIdeal (hS v hv) hτ
    exact ⟨Q, ⟨hQ, hpQ, hfr⟩, hQv⟩
  choose! f hf hf' using hex
  rw [Set.ncard_eq_toFinset_card _ (frobSet_finite τ hp)]
  refine Finset.card_le_card_of_injOn f (fun v hv => ?_) (fun v hv w hw h => ?_)
  · rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact hf v hv
  · apply HeightOneSpectrum.ext
    rw [← hf' v hv, ← hf' w hw, h]

end Count

section Analytic

theorem tsum_primes_eq_tsum_indicator (G : ℕ → ℝ) :
    ∑' p : Nat.Primes, G p = ∑' n : ℕ, {n : ℕ | n.Prime}.indicator G n :=
  tsum_subtype {n : ℕ | n.Prime} G

theorem rpow_neg_nonneg (s : ℝ) (n : ℕ) : 0 ≤ (n : ℝ) ^ (-s) :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem summable_rpow_neg {s : ℝ} (hs : 1 < s) : Summable fun n : ℕ => (n : ℝ) ^ (-s) :=
  Real.summable_nat_rpow.mpr (by linarith)

theorem summable_indicator_mul_rpow {s : ℝ} (hs : 1 < s) {a : ℕ → ℝ} {B : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (haB : ∀ n : ℕ, n.Prime → a n ≤ B) :
    Summable fun n : ℕ => {n : ℕ | n.Prime}.indicator (fun n => a n * (n : ℝ) ^ (-s)) n := by
  have hB : 0 ≤ B := (ha0 2).trans (haB 2 Nat.prime_two)
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) ((summable_rpow_neg hs).mul_left B)
  · exact Set.indicator_nonneg (fun m _ => mul_nonneg (ha0 m) (rpow_neg_nonneg s m)) _
  · by_cases hn : n ∈ {n : ℕ | n.Prime}
    · rw [Set.indicator_of_mem hn]
      exact mul_le_mul_of_nonneg_right (haB n hn) (rpow_neg_nonneg s n)
    · rw [Set.indicator_of_notMem hn]
      exact mul_nonneg hB (rpow_neg_nonneg s n)

theorem le_mul_log_of_lt {K δ s : ℝ} (_hK : 0 ≤ K) (hδ : 0 < δ) (hs : 1 < s)
    (hs' : s < 1 + Real.exp (-(K / δ))) : K ≤ δ * Real.log (1 / (s - 1)) := by
  have hpos : 0 < s - 1 := by linarith
  have h1 : s - 1 < Real.exp (-(K / δ)) := by linarith
  have h2 : Real.log (s - 1) < -(K / δ) := by
    have := Real.log_lt_log hpos h1
    rwa [Real.log_exp] at this
  have h3 : K / δ < Real.log (1 / (s - 1)) := by
    rw [one_div, Real.log_inv]
    linarith
  have h4 : K < δ * Real.log (1 / (s - 1)) := by
    have := (div_lt_iff₀ hδ).mp h3
    linarith [this]
  exact h4.le

theorem tail_le {F : Type} [Field F] [NumberField F] {s : ℝ} (hs : 1 ≤ s) :
    (∑' v : HeightOneSpectrum (𝓞 F), if (Ideal.absNorm v.asIdeal).Prime then 0 else pw F s v) ≤
      Ctail F := by
  rw [← tailSum_toReal, Ctail]
  refine ENNReal.toReal_mono ?_ (FrobeniusDensity.tailSum_le F hs)
  exact (ENNReal.mul_lt_top (ENNReal.natCast_ne_top _).lt_top tailConst_lt_top).ne

theorem density_over_base (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L]
    [Algebra E L] [IsGalois E L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} E L]
    (τ : L ≃ₐ[E] L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (1 / (Module.finrank E L : ℝ) - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : Nat.Primes, (((frobSet τ (p : ℕ)).ncard : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot E L (Set.mem_singleton m)
    (NeZero.ne m)
  set a : (ZMod m)ˣ := hζ.autToPow E τ with hadef
  set n : ℕ := Module.finrank E L with hndef
  obtain ⟨C, δH, hδH, hH⟩ :=
    NumberField.exists_forall_abs_tsum_absNorm_rpow_neg_sub_inv_finrank_mul_log_le_of_isCyclotomicExtension
      E L m hζ τ

  set Kc : ℝ := max 0 (C + Ctail E) with hKc
  have hKc0 : 0 ≤ Kc := le_max_left _ _
  refine ⟨min (1 + δH) (1 + Real.exp (-(Kc / δ))), lt_min (by linarith) (by
    linarith [Real.exp_pos (-(Kc / δ))]), fun s hs hs₀ => ?_⟩
  have hsH : s < 1 + δH := lt_of_lt_of_le hs₀ (min_le_left _ _)
  have hsK : s < 1 + Real.exp (-(Kc / δ)) := lt_of_lt_of_le hs₀ (min_le_right _ _)

  have hT : (n : ℝ)⁻¹ * Real.log (1 / (s - 1)) - C ≤ T E m (a : ZMod m) s := by
    have h := hH s hs hsH
    have h' : |T E m (a : ZMod m) s - (n : ℝ)⁻¹ * Real.log (1 / (s - 1))| ≤ C := h
    have := neg_abs_le (T E m (a : ZMod m) s - (n : ℝ)⁻¹ * Real.log (1 / (s - 1)))
    linarith

  set g : HeightOneSpectrum (𝓞 E) → ℝ := fun v =>
    if (Ideal.absNorm v.asIdeal).Prime ∧ (Ideal.absNorm v.asIdeal : ZMod m) = (a : ZMod m)
      then pw E s v else 0 with hgdef
  have hg0 : ∀ v, 0 ≤ g v := fun v => by
    simp only [hgdef]; split_ifs; exacts [pw_nonneg s v, le_rfl]
  have hgle : ∀ v, g v ≤ pw E s v := fun v => by
    simp only [hgdef]; split_ifs; exacts [le_rfl, pw_nonneg s v]
  have hgsum : Summable g := (summable_pw hs).of_nonneg_of_le hg0 hgle
  set tl : HeightOneSpectrum (𝓞 E) → ℝ := fun v =>
    if (Ideal.absNorm v.asIdeal).Prime then 0 else pw E s v with htldef
  have htlsum : Summable tl := summable_tail hs
  have hT_le : T E m (a : ZMod m) s ≤ (∑' v, g v) + Ctail E := by
    have hterm : ∀ v : HeightOneSpectrum (𝓞 E),
        (if (Ideal.absNorm v.asIdeal : ZMod m) = (a : ZMod m) then pw E s v else 0) ≤ g v + tl v := by
      intro v
      simp only [hgdef, htldef]
      by_cases hp : (Ideal.absNorm v.asIdeal).Prime <;>
        by_cases ha : (Ideal.absNorm v.asIdeal : ZMod m) = (a : ZMod m) <;>
        simp [hp, ha, pw_nonneg s v]
    have h1 : T E m (a : ZMod m) s ≤ ∑' v, (g v + tl v) :=
      (summable_T (a : ZMod m) hs).tsum_le_tsum hterm (hgsum.add htlsum)
    rw [hgsum.tsum_add htlsum] at h1
    linarith [tail_le (F := E) hs.le]

  set G : ℕ → ℝ := fun p => (((frobSet τ p).ncard : ℕ) : ℝ) * (p : ℝ) ^ (-s) with hGdef
  have hG0 : ∀ p, 0 ≤ G p := fun p => mul_nonneg (Nat.cast_nonneg _) (rpow_neg_nonneg s p)
  have hGsum : Summable fun p : ℕ => {p : ℕ | p.Prime}.indicator G p :=
    summable_indicator_mul_rpow hs (a := fun p => (((frobSet τ p).ncard : ℕ) : ℝ))
      (B := Module.finrank ℚ L) (fun p => Nat.cast_nonneg _)
      (fun p hp => by
        show (((frobSet τ p).ncard : ℕ) : ℝ) ≤ ((Module.finrank ℚ L : ℕ) : ℝ)
        exact_mod_cast ncard_frobSet_le τ hp)
  have hGtsum : ∑' p : Nat.Primes, G p = ∑' p : ℕ, {p : ℕ | p.Prime}.indicator G p :=
    tsum_primes_eq_tsum_indicator G

  have hg_le : (∑' v, g v) ≤ ∑' p : Nat.Primes, G p := by
    rw [hGtsum]
    refine Real.tsum_le_of_sum_le hg0 fun U => ?_
    set U' := U.filter fun v =>
      (Ideal.absNorm v.asIdeal).Prime ∧ (Ideal.absNorm v.asIdeal : ZMod m) = (a : ZMod m) with hU'
    have hsumU : ∑ v ∈ U, g v = ∑ v ∈ U', pw E s v := by
      rw [hU', Finset.sum_filter]
    rw [hsumU]
    set u : HeightOneSpectrum (𝓞 E) → ℕ := fun v => Ideal.absNorm v.asIdeal with hu
    have hmaps : ∀ v ∈ U', u v ∈ U'.image u := fun v hv => Finset.mem_image_of_mem _ hv
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hstep : ∀ q ∈ U'.image u, ∑ v ∈ U' with u v = q, pw E s v ≤ {p : ℕ | p.Prime}.indicator G q := by
      intro q hq
      obtain ⟨w, hwU', hwq⟩ := Finset.mem_image.mp hq
      have hw := (Finset.mem_filter.mp hwU').2
      have hqprime : q.Prime := by rw [← hwq]; exact hw.1
      have hqa : (q : ZMod m) = (a : ZMod m) := by rw [← hwq]; exact hw.2
      rw [Set.indicator_of_mem (show q ∈ {p : ℕ | p.Prime} from hqprime), hGdef]
      have hterm : ∀ v ∈ U'.filter (fun v => u v = q), pw E s v = (q : ℝ) ^ (-s) := by
        intro v hv
        rw [pw, ← (Finset.mem_filter.mp hv).2]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (rpow_neg_nonneg s q)
      exact_mod_cast card_le_ncard_frobSet m hζ τ hqprime hqa _
        (fun v hv => (Finset.mem_filter.mp hv).2)
    calc ∑ q ∈ U'.image u, ∑ v ∈ U' with u v = q, pw E s v
        ≤ ∑ q ∈ U'.image u, {p : ℕ | p.Prime}.indicator G q := Finset.sum_le_sum hstep
      _ ≤ ∑' q : ℕ, {p : ℕ | p.Prime}.indicator G q :=
          hGsum.sum_le_tsum _ (fun q _ => Set.indicator_nonneg (fun p _ => hG0 p) _)

  have hKle : Kc ≤ δ * Real.log (1 / (s - 1)) := le_mul_log_of_lt hKc0 hδ hs hsK
  have hCK : C + Ctail E ≤ Kc := le_max_right _ _
  have h1 : (n : ℝ)⁻¹ * Real.log (1 / (s - 1)) - C - Ctail E ≤ ∑' p : Nat.Primes, G p := by
    linarith
  rw [one_div (n : ℝ)]
  linarith

end Analytic

section Fixed

theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (σ : L ≃ₐ[K] L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (1 / (orderOf σ : ℝ) - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : Nat.Primes, (({P : Ideal (𝓞 L) | P.IsMaximal ∧ ((p : ℕ) : 𝓞 L) ∈ P ∧
            IsArithFrobAt ℤ σ P}.ncard : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s) := by
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m)
    (NeZero.ne m)
  set H : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers σ with hHdef
  set E : IntermediateField K L := IntermediateField.fixedField H with hEdef
  let eE : H ≃* (L ≃ₐ[E] L) := IntermediateField.subgroupEquivAlgEquiv H
  set τ : L ≃ₐ[E] L := eE ⟨σ, Subgroup.mem_zpowers σ⟩ with hτdef

  haveI : IsCyclotomicExtension {m} E L := by
    have hT : ∀ x : L, x ∈ Algebra.adjoin E {b : L | ∃ n : ℕ, n ∈ ({m} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} := by
      intro x
      have hx := IsCyclotomicExtension.adjoin_roots (S := ({m} : Set ℕ)) (A := K) (B := L) x
      have hle : Algebra.adjoin K {b : L | ∃ n : ℕ, n ∈ ({m} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1} ≤
          (Algebra.adjoin E {b : L | ∃ n : ℕ, n ∈ ({m} : Set ℕ) ∧ n ≠ 0 ∧ b ^ n = 1}).restrictScalars K := by
        apply Algebra.adjoin_le
        intro b hb
        rw [Subalgebra.coe_restrictScalars]
        exact Algebra.subset_adjoin hb
      exact (Subalgebra.mem_restrictScalars K).mp (hle hx)
    exact ⟨fun {k} hk _ => by
      rw [Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨ζ, hζ⟩, hT⟩

  have hfin : Module.finrank E L = orderOf σ := by
    rw [hEdef, IntermediateField.finrank_fixedField_eq_card, hHdef, Nat.card_zpowers]
  obtain ⟨s₀, hs₀, h⟩ := density_over_base E L m τ δ hδ
  refine ⟨s₀, hs₀, fun s hs hs' => ?_⟩
  have := h s hs hs'
  rw [hfin] at this
  exact this

end Fixed

end P2mCycloDensity

end

open NumberField in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (σ : L ≃ₐ[K] L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      (1 / (orderOf σ : ℝ) - δ) * Real.log (1 / (s - 1)) ≤
        ∑' p : Nat.Primes, (({P : Ideal (𝓞 L) | P.IsMaximal ∧ ((p : ℕ) : 𝓞 L) ∈ P ∧
            IsArithFrobAt ℤ σ P}.ncard : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-s) :=
  P2mCycloDensity.main K L m σ δ hδ

end S_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension
end P2MW
export P2MW.S_NumberField_sub_mul_log_le_tsum_ncard_isArithFrobAt_of_isCyclotomicExtension (solution)

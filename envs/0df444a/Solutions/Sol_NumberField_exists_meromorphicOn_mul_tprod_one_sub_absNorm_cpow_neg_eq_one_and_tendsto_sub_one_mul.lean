-- Prove2me | solution 1 for NumberField.exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/22e33f69-e0f9-5f60-87cb-570b70d4dab3

import Mathlib
import Definitions.Def_NumberField_PrimeNormSums
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain Filter Topology Complex UniqueFactorizationMonoid

namespace SF86a45a1dZ

variable {F : Type} [Field F] [NumberField F]

noncomputable def nrm (w : ℂ) (I : Ideal (𝓞 F)) : ℂ := ((Ideal.absNorm I : ℕ) : ℂ) ^ (-w)

theorem nrm_top (w : ℂ) : nrm w (⊤ : Ideal (𝓞 F)) = 1 := by
  simp [nrm]

theorem nrm_mul (w : ℂ) (I J : Ideal (𝓞 F)) : nrm w (I * J) = nrm w I * nrm w J := by
  unfold nrm
  rw [map_mul, Nat.cast_mul, natCast_mul_natCast_cpow]

theorem nrm_pow (w : ℂ) (I : Ideal (𝓞 F)) (e : ℕ) : nrm w (I ^ e) = nrm w I ^ e := by
  induction e with
  | zero => simp [nrm_top]
  | succ n ih => rw [pow_succ, pow_succ, nrm_mul, ih]

theorem one_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : 1 ≤ Ideal.absNorm I :=
  Nat.one_le_iff_ne_zero.mpr fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)

theorem norm_nrm (w : ℂ) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ‖nrm w I‖ = (Ideal.absNorm I : ℝ) ^ (-w.re) := by
  unfold nrm
  rw [norm_natCast_cpow_of_pos (one_le_absNorm hI)]
  simp

theorem norm_nrm_prime (w : ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖nrm w v.asIdeal‖ = NumberField.PrimeNormSum.pw F w.re v := by
  rw [norm_nrm w v.ne_bot]; rfl

theorem norm_nrm_prime_lt_one {w : ℂ} (hw : 0 < w.re) (v : HeightOneSpectrum (𝓞 F)) :
    ‖nrm w v.asIdeal‖ < 1 := by
  rw [norm_nrm w v.ne_bot]
  exact Real.rpow_lt_one_of_one_lt_of_neg (NumberField.PrimeNormSum.one_lt_absNorm_real v)
    (by linarith)

theorem one_sub_nrm_prime_ne_zero {w : ℂ} (hw : 0 < w.re) (v : HeightOneSpectrum (𝓞 F)) :
    1 - nrm w v.asIdeal ≠ 0 := by
  intro h
  have h1 : nrm w v.asIdeal = 1 := (sub_eq_zero.mp h).symm
  have := norm_nrm_prime_lt_one hw v
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem summable_norm_nrm_prime {w : ℂ} (hw : 1 < w.re) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ‖nrm w v.asIdeal‖ := by
  refine (NumberField.PrimeNormSum.summable_pw (F := F) hw).congr fun v => ?_
  exact (norm_nrm_prime w v).symm

noncomputable def idealCount (F : Type) [Field F] [NumberField F] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}

theorem summable_norm_nrm {w : ℂ} (hw : 1 < w.re) :
    Summable fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => ‖nrm w I.1‖ := by
  classical
  set σ : ℝ := w.re
  set e : ℕ → ℝ := fun n => (Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-σ)
    with he
  have h5 : Summable e := NumberField.PrimeNormSum.summable_dedekind_terms (F := F) hw
  have he0 : ∀ n, 0 ≤ e n := fun n =>
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine summable_of_sum_le (fun I => norm_nonneg _) (c := ∑' n, e n) fun T => ?_
  have hmaps : ∀ I ∈ T, Ideal.absNorm I.1 ∈ T.image fun I => Ideal.absNorm I.1 :=
    fun I hI => Finset.mem_image_of_mem _ hI
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hstep : ∀ n : ℕ, ∀ S : Finset {I : Ideal (𝓞 F) // I ≠ ⊥},
      (∀ I ∈ S, Ideal.absNorm I.1 = n) → ∑ I ∈ S, ‖nrm w I.1‖ ≤ e n := by
    intro n S hS
    have hterm : ∀ I ∈ S, ‖nrm w I.1‖ = (n : ℝ) ^ (-σ) := by
      intro I hI
      rw [norm_nrm w I.2, hS I hI]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, he]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    haveI : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
    have hle := Nat.card_le_card_of_injective
      (fun I : S => (⟨I.1.1, hS I.1 I.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n}))
      (fun a b h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h))
    rw [Nat.card_eq_finsetCard] at hle
    exact_mod_cast hle
  calc ∑ n ∈ T.image (fun I => Ideal.absNorm I.1),
        ∑ I ∈ T with Ideal.absNorm I.1 = n, ‖nrm w I.1‖
      ≤ ∑ n ∈ T.image (fun I => Ideal.absNorm I.1), e n :=
        Finset.sum_le_sum fun n _ => hstep n _ (fun I hI => (Finset.mem_filter.mp hI).2)
    _ ≤ ∑' n, e n := h5.sum_le_tsum _ (fun n _ => he0 n)

def NormFiber (F : Type) [Field F] [NumberField F] (n : ℕ) : Type :=
  {I : {I : Ideal (𝓞 F) // I ≠ ⊥} // Ideal.absNorm I.1 = n}

noncomputable def normFiberEquiv (F : Type) [Field F] [NumberField F] :
    (Σ n : ℕ, NormFiber F n) ≃ {I : Ideal (𝓞 F) // I ≠ ⊥} where
  toFun p := p.2.1
  invFun I := ⟨Ideal.absNorm I.1, I, rfl⟩
  left_inv p := by rcases p with ⟨n, I, rfl⟩; rfl
  right_inv I := rfl

scoped instance finite_normFiber (n : ℕ) : Finite (NormFiber F n) := by
  haveI : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 F) n).to_subtype
  refine Finite.of_injective (fun I : NormFiber F n =>
    (⟨I.1.1, I.2⟩ : {I : Ideal (𝓞 F) // Ideal.absNorm I = n})) ?_
  intro a b h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (Subtype.ext h)

theorem natCard_normFiber {n : ℕ} (hn : n ≠ 0) : Nat.card (NormFiber F n) = idealCount F n := by
  unfold idealCount
  refine Nat.card_congr
    { toFun := fun I => ⟨I.1.1, I.2⟩
      invFun := fun I => ⟨⟨I.1, fun h => hn (by rw [← I.2, h, Ideal.absNorm_bot])⟩, I.2⟩
      left_inv := fun I => rfl
      right_inv := fun I => rfl }

theorem isEmpty_normFiber_zero : IsEmpty (NormFiber F 0) :=
  ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩

theorem hasSum_nrm_dedekindZeta {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => nrm w I.1) (dedekindZeta F w) := by
  classical
  have hsum : Summable fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} => nrm w I.1 :=
    (summable_norm_nrm hw).of_norm

  have hsum' : Summable fun p : Σ n : ℕ, NormFiber F n => nrm w ((normFiberEquiv F p)).1 :=
    (normFiberEquiv F).summable_iff.mpr hsum
  have hfib : ∀ n : ℕ, HasSum (fun I : NormFiber F n => nrm w I.1.1)
      (LSeries.term (fun n => (idealCount F n : ℂ)) w n) := by
    intro n
    haveI : Fintype (NormFiber F n) := Fintype.ofFinite _
    have hconst : ∀ I : NormFiber F n, nrm w I.1.1 = ((n : ℕ) : ℂ) ^ (-w) := fun I => by
      unfold nrm; rw [I.2]
    have h := hasSum_fintype (fun I : NormFiber F n => nrm w I.1.1)
    rw [Finset.sum_congr rfl (fun I _ => hconst I), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h
    rcases eq_or_ne n 0 with rfl | hn
    · haveI := isEmpty_normFiber_zero (F := F)
      rw [LSeries.term_zero]
      simpa using h
    · rw [Fintype.card_eq_nat_card, natCard_normFiber hn] at h
      rw [LSeries.term_of_ne_zero hn]
      convert h using 1
      rw [cpow_neg, div_eq_mul_inv]
  have hsig : HasSum (fun p : Σ n : ℕ, NormFiber F n => nrm w p.2.1.1) (dedekindZeta F w) := by
    have hs2 : Summable fun p : Σ n : ℕ, NormFiber F n => nrm w p.2.1.1 := hsum'
    have := hs2.hasSum
    have hn : HasSum (fun n : ℕ => ∑' I : NormFiber F n, nrm w I.1.1)
        (∑' p : Σ n : ℕ, NormFiber F n, nrm w p.2.1.1) := hs2.hasSum.sigma (fun n => (hfib n).summable.hasSum)
    have heq : (fun n : ℕ => ∑' I : NormFiber F n, nrm w I.1.1)
        = fun n => LSeries.term (fun n => (idealCount F n : ℂ)) w n := by
      funext n; exact (hfib n).tsum_eq
    rw [heq] at hn
    have hL : HasSum (fun n => LSeries.term (fun n => (idealCount F n : ℂ)) w n) (dedekindZeta F w) :=
      (NumberField.PrimeNormSum.summable_card_absNorm (F := F) hw).hasSum
    rw [hn.unique hL] at this
    exact this
  exact (normFiberEquiv F).hasSum_iff.mp hsig

def IsFactoredBy (T : Finset (HeightOneSpectrum (𝓞 F))) (I : Ideal (𝓞 F)) : Prop :=
  I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ I → v ∈ T

theorem isFactoredBy_top (T : Finset (HeightOneSpectrum (𝓞 F))) :
    IsFactoredBy T (⊤ : Ideal (𝓞 F)) := by
  refine ⟨by simp, fun v hv => absurd ?_ v.isPrime.ne_top⟩
  exact top_le_iff.mp (Ideal.le_of_dvd hv)

theorem IsFactoredBy.mono {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hTT' : T ⊆ T')
    {I : Ideal (𝓞 F)} (hI : IsFactoredBy T I) : IsFactoredBy T' I :=
  ⟨hI.1, fun v hv => hTT' (hI.2 v hv)⟩

theorem eq_top_of_isFactoredBy_empty {I : Ideal (𝓞 F)}
    (hI : IsFactoredBy (∅ : Finset (HeightOneSpectrum (𝓞 F))) I) : I = ⊤ := by
  by_contra hne
  obtain ⟨P, hP⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hI.1
    fun h => hne (Ideal.isUnit_iff.mp h)
  obtain ⟨hP1, hP2⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mp hP
  exact absurd (hI.2 ⟨P, Ideal.isPrime_of_prime hP1, hP1.ne_zero⟩ hP2) (Finset.notMem_empty _)

theorem finite_setOf_dvd {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ I}.Finite := by
  classical
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      {v | v.asIdeal ∣ I} := fun v _ w _ h => HeightOneSpectrum.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine (normalizedFactors I).toFinset.finite_toSet.subset ?_
  rintro J ⟨v, hv, rfl⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨v.prime, hv⟩

theorem exists_isFactoredBy {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), IsFactoredBy T I :=
  ⟨(finite_setOf_dvd hI).toFinset, hI, fun v hv => (finite_setOf_dvd hI).mem_toFinset.mpr hv⟩

noncomputable def consFactored (v : HeightOneSpectrum (𝓞 F))
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hv : v ∉ T)
    (p : ℕ × {I : Ideal (𝓞 F) // IsFactoredBy T I}) :
    {I : Ideal (𝓞 F) // IsFactoredBy (T.cons v hv) I} := by
  refine ⟨v.asIdeal ^ p.1 * p.2.1, mul_ne_zero (pow_ne_zero _ v.ne_bot) p.2.2.1, fun w hw => ?_⟩
  rcases (Prime.dvd_mul w.prime).mp hw with hw | hw
  · have h1 : w.asIdeal ∣ v.asIdeal := w.prime.dvd_of_dvd_pow hw
    have h2 : w = v := HeightOneSpectrum.ext <|
      associated_iff_eq.mp ((Prime.dvd_prime_iff_associated w.prime v.prime).mp h1)
    simp [h2]
  · exact Finset.mem_cons_of_mem (p.2.2.2 w hw)

theorem consFactored_val (v : HeightOneSpectrum (𝓞 F))
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hv : v ∉ T)
    (p : ℕ × {I : Ideal (𝓞 F) // IsFactoredBy T I}) :
    (consFactored v hv p).1 = v.asIdeal ^ p.1 * p.2.1 := rfl

theorem consFactored_injective (v : HeightOneSpectrum (𝓞 F))
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hv : v ∉ T) :
    Function.Injective (consFactored v hv) := by
  classical
  have hcount : ∀ (e : ℕ) (J : {I : Ideal (𝓞 F) // IsFactoredBy T I}),
      Multiset.count v.asIdeal (normalizedFactors (v.asIdeal ^ e * J.1)) = e := by
    intro e J
    rw [normalizedFactors_mul (pow_ne_zero _ v.ne_bot) J.2.1, normalizedFactors_pow,
      normalizedFactors_irreducible v.prime.irreducible, Multiset.count_add,
      Multiset.count_nsmul, normalize_eq, Multiset.count_singleton_self, mul_one,
      Multiset.count_eq_zero_of_notMem, add_zero]
    intro hmem
    exact hv (J.2.2 v ((UniqueFactorizationMonoid.mem_normalizedFactors_iff J.2.1).mp hmem).2)
  rintro ⟨e, J⟩ ⟨e', J'⟩ h
  have h' : v.asIdeal ^ e * J.1 = v.asIdeal ^ e' * J'.1 := congrArg Subtype.val h
  have he : e = e' := by rw [← hcount e J, ← hcount e' J', h']
  subst he
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (pow_ne_zero _ v.ne_bot) h'))

theorem consFactored_surjective (v : HeightOneSpectrum (𝓞 F))
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hv : v ∉ T) :
    Function.Surjective (consFactored v hv) := by
  rintro ⟨I, hI0, hIfac⟩
  have hfin : FiniteMultiplicity v.asIdeal I := .of_prime_left v.prime hI0
  obtain ⟨J, hJ, hvJ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hI0 (by simpa using hJ)
  refine ⟨⟨multiplicity v.asIdeal I, J, hJ0, fun w hw => ?_⟩, Subtype.ext hJ.symm⟩
  have hwI : w.asIdeal ∣ I := hw.trans ((dvd_mul_left J _).trans (dvd_of_eq hJ.symm))
  rcases Finset.mem_cons.mp (hIfac w hwI) with rfl | hmem
  · exact absurd hw hvJ
  · exact hmem

noncomputable def consFactoredEquiv (v : HeightOneSpectrum (𝓞 F))
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hv : v ∉ T) :
    ℕ × {I : Ideal (𝓞 F) // IsFactoredBy T I} ≃
      {I : Ideal (𝓞 F) // IsFactoredBy (T.cons v hv) I} :=
  Equiv.ofBijective _ ⟨consFactored_injective v hv, consFactored_surjective v hv⟩

theorem summable_norm_nrm_factored {w : ℂ} (hw : 1 < w.re) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Summable fun I : {I : Ideal (𝓞 F) // IsFactoredBy T I} => ‖nrm w I.1‖ := by
  have hinj : Function.Injective
      (fun I : {I : Ideal (𝓞 F) // IsFactoredBy T I} => (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 F) // I ≠ ⊥})) := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  have h := (summable_norm_nrm (F := F) hw).comp_injective hinj
  exact h

theorem hasSum_nrm_factored {w : ℂ} (hw : 1 < w.re) (T : Finset (HeightOneSpectrum (𝓞 F))) :
    HasSum (fun I : {I : Ideal (𝓞 F) // IsFactoredBy T I} => nrm w I.1)
      (∏ v ∈ T, (1 - nrm w v.asIdeal)⁻¹) := by
  classical
  have hw0 : 0 < w.re := by linarith
  induction T using Finset.cons_induction_on with
  | empty =>
    rw [Finset.prod_empty]
    have huniq : ∀ I : {I : Ideal (𝓞 F) // IsFactoredBy ∅ I},
        I = ⟨⊤, isFactoredBy_top ∅⟩ := fun I => Subtype.ext (eq_top_of_isFactoredBy_empty I.2)
    have h := hasSum_single (f := fun I : {I : Ideal (𝓞 F) // IsFactoredBy ∅ I} => nrm w I.1)
      (⟨⊤, isFactoredBy_top ∅⟩ : {I : Ideal (𝓞 F) // IsFactoredBy ∅ I})
      (fun b hb => absurd (huniq b) hb)
    simpa [nrm_top] using h
  | cons v T hv ih =>
    rw [Finset.prod_cons]
    set x : ℂ := nrm w v.asIdeal with hx
    have hxn : ‖x‖ < 1 := norm_nrm_prime_lt_one hw0 v
    have hgeo : HasSum (fun n : ℕ => x ^ n) (1 - x)⁻¹ := hasSum_geometric_of_norm_lt_one hxn
    have hgeo_norm : Summable fun n : ℕ => ‖x ^ n‖ := by
      simp only [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) hxn
    have hfacT := summable_norm_nrm_factored (F := F) hw T
    have hprodsum := summable_mul_of_summable_norm hgeo_norm hfacT
    have hmul := hgeo.mul ih hprodsum
    have hmul' : HasSum ((fun I : {I : Ideal (𝓞 F) // IsFactoredBy (T.cons v hv) I} => nrm w I.1) ∘
        (consFactoredEquiv v hv)) ((1 - x)⁻¹ * ∏ v ∈ T, (1 - nrm w v.asIdeal)⁻¹) := by
      refine hmul.congr_fun fun p => ?_
      show nrm w (consFactored v hv p).1 = _
      rw [consFactored_val, nrm_mul, nrm_pow]
    exact (consFactoredEquiv v hv).hasSum_iff.mp hmul'

theorem tendsto_prod_inv_one_sub_nrm {w : ℂ} (hw : 1 < w.re) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ T, (1 - nrm w v.asIdeal)⁻¹)
      atTop (𝓝 (dedekindZeta F w)) := by
  classical

  set f : Finset (HeightOneSpectrum (𝓞 F)) → Ideal (𝓞 F) → ℂ :=
    fun T I => if IsFactoredBy T I then nrm w I else 0 with hf
  set g : Ideal (𝓞 F) → ℂ := fun I => if I ≠ ⊥ then nrm w I else 0 with hg
  set bound : Ideal (𝓞 F) → ℝ := fun I => ‖g I‖ with hbound

  have hgsum : Summable g := by
    have h := (summable_norm_nrm (F := F) hw).of_norm
    have h2 : Summable (Set.indicator {I : Ideal (𝓞 F) | I ≠ ⊥} (nrm w)) :=
      summable_subtype_iff_indicator.mp h
    refine h2.congr fun I => ?_
    simp only [hg, Set.indicator_apply, Set.mem_setOf_eq]
  have hbound_sum : Summable bound := hgsum.norm

  have hab : ∀ I : Ideal (𝓞 F), Tendsto (fun T => f T I) atTop (𝓝 (g I)) := by
    intro I
    by_cases hI : I = ⊥
    · have h1 : ∀ T, f T I = 0 := fun T => by
        simp only [hf]
        rw [if_neg]
        exact fun h => h.1 hI
      have h2 : g I = 0 := by simp [hg, hI]
      simp only [h1, h2]
      exact tendsto_const_nhds
    · obtain ⟨T₀, hT₀⟩ := exists_isFactoredBy hI
      have h2 : g I = nrm w I := by simp [hg, hI]
      rw [h2]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop T₀] with T hT
      simp only [hf]
      rw [if_pos (hT₀.mono hT)]
  have h_bound : ∀ᶠ T in atTop, ∀ I : Ideal (𝓞 F), ‖f T I‖ ≤ bound I := by
    refine Eventually.of_forall fun T I => ?_
    simp only [hf, hbound, hg]
    by_cases h : IsFactoredBy T I
    · rw [if_pos h, if_pos h.1]
    · rw [if_neg h, norm_zero]; exact norm_nonneg _
  have hlim := tendsto_tsum_of_dominated_convergence hbound_sum hab h_bound

  have hgt : ∑' I, g I = dedekindZeta F w := by
    rw [← (hasSum_nrm_dedekindZeta (F := F) hw).tsum_eq]
    have := tsum_subtype ({I : Ideal (𝓞 F) | I ≠ ⊥}) (nrm w)
    rw [show (fun I => g I) = Set.indicator {I : Ideal (𝓞 F) | I ≠ ⊥} (nrm w) from ?_]
    · exact this.symm
    funext I
    simp only [hg, Set.indicator_apply, Set.mem_setOf_eq]
  have hft : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∑' I, f T I = ∏ v ∈ T, (1 - nrm w v.asIdeal)⁻¹ := by
    intro T
    rw [← (hasSum_nrm_factored (F := F) hw T).tsum_eq]
    have := tsum_subtype ({I : Ideal (𝓞 F) | IsFactoredBy T I}) (nrm w)
    rw [show (fun I => f T I) = Set.indicator {I : Ideal (𝓞 F) | IsFactoredBy T I} (nrm w) from ?_]
    · exact this.symm
    funext I
    simp only [hf, Set.indicator_apply, Set.mem_setOf_eq]
  rw [hgt] at hlim
  refine hlim.congr fun T => ?_
  exact hft T

theorem dedekindZeta_mul_tprod_eq_one {w : ℂ} (hw : 1 < w.re) :
    Multipliable (fun v : HeightOneSpectrum (𝓞 F) => 1 - nrm w v.asIdeal) ∧
      dedekindZeta F w * ∏' v : HeightOneSpectrum (𝓞 F), (1 - nrm w v.asIdeal) = 1 := by
  have hw0 : 0 < w.re := by linarith
  have hneg : Summable fun v : HeightOneSpectrum (𝓞 F) => -nrm w v.asIdeal :=
    (summable_norm_nrm_prime hw).of_norm.neg
  have hmult : Multipliable (fun v : HeightOneSpectrum (𝓞 F) => 1 - nrm w v.asIdeal) := by
    have := Complex.multipliable_one_add_of_summable hneg
    simpa [sub_eq_add_neg] using this
  refine ⟨hmult, ?_⟩
  set P := ∏' v : HeightOneSpectrum (𝓞 F), (1 - nrm w v.asIdeal) with hP
  have hP0 : P ≠ 0 := by
    have h := tprod_one_add_ne_zero_of_summable (f := fun v : HeightOneSpectrum (𝓞 F) => -nrm w v.asIdeal)
      (fun v => by simpa [sub_eq_add_neg] using one_sub_nrm_prime_ne_zero hw0 v)
      (by simpa using summable_norm_nrm_prime (F := F) hw)
    first | exact h | simpa [sub_eq_add_neg] using h

  have hprod : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ T, (1 - nrm w v.asIdeal))
      atTop (𝓝 P) := by
    have h := hmult.hasProd
    simpa [HasProd] using h

  have hinv : Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ T, (1 - nrm w v.asIdeal)⁻¹)
      atTop (𝓝 P⁻¹) := by
    refine (hprod.inv₀ hP0).congr fun T => ?_
    rw [Finset.prod_inv_distrib]

  have hζ := tendsto_prod_inv_one_sub_nrm (F := F) hw
  have heq : dedekindZeta F w = P⁻¹ := tendsto_nhds_unique hζ hinv
  rw [heq, inv_mul_cancel₀ hP0]

noncomputable def archInv (r₁ r₂ : ℕ) (w : ℂ) : ℂ :=
  ((Gammaℝ w)⁻¹) ^ r₁ * ((Gammaℝ w)⁻¹ * (Gammaℝ (w + 1))⁻¹) ^ r₂

theorem differentiable_archInv (r₁ r₂ : ℕ) : Differentiable ℂ (archInv r₁ r₂) := by
  unfold archInv
  have h1 : Differentiable ℂ (fun w : ℂ => (Gammaℝ (w + 1))⁻¹) :=
    differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
  exact (differentiable_Gammaℝ_inv.pow r₁).mul ((differentiable_Gammaℝ_inv.mul h1).pow r₂)

theorem Gammaℝ_zero : Gammaℝ 0 = 0 := Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩

theorem archInv_zero {r₁ r₂ : ℕ} (h : r₁ + r₂ ≠ 0) : archInv r₁ r₂ 0 = 0 := by
  unfold archInv
  rw [Gammaℝ_zero, inv_zero, zero_mul]
  rcases Nat.eq_zero_or_pos r₁ with h1 | h1
  · subst h1
    have h2 : r₂ ≠ 0 := by simpa using h
    rw [zero_pow h2, mul_zero]
  · rw [zero_pow h1.ne', zero_mul]

theorem archInv_mul_eq_one {r₁ r₂ : ℕ} {w : ℂ} (hw : 0 < w.re) :
    archInv r₁ r₂ w * (Gammaℝ w ^ r₁ * Gammaℂ w ^ r₂) = 1 := by
  unfold archInv
  have h0 : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos hw
  have h1 : Gammaℝ (w + 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [← Gammaℝ_mul_Gammaℝ_add_one w]
  have : ((Gammaℝ w)⁻¹ * (Gammaℝ (w + 1))⁻¹) = (Gammaℝ w * Gammaℝ (w + 1))⁻¹ := by
    rw [mul_inv]
  rw [this, inv_pow, inv_pow, mul_mul_mul_comm, inv_mul_cancel₀ (pow_ne_zero _ h0),
    inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero h0 h1)), one_mul]

theorem archInv_one_ne_zero (r₁ r₂ : ℕ) : archInv r₁ r₂ 1 ≠ 0 := by
  have h := archInv_mul_eq_one (r₁ := r₁) (r₂ := r₂) (w := 1) (by simp)
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem differentiable_discPow (d : ℤ) (hd : d ≠ 0) :
    Differentiable ℂ (fun w : ℂ => (((|d| : ℤ) : ℂ)) ^ (w / 2)) := by
  refine Differentiable.const_cpow (differentiable_id.div_const 2) (Or.inl ?_)
  exact_mod_cast (abs_ne_zero.mpr hd)

theorem discPow_ne_zero (d : ℤ) (hd : d ≠ 0) (w : ℂ) : (((|d| : ℤ) : ℂ)) ^ (w / 2) ≠ 0 := by
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast (abs_ne_zero.mpr hd)

theorem exists_dedekindZeta_continuation (F : Type) [Field F] [NumberField F] :
    ∃ (ζc : ℂ → ℂ) (κ₀ : ℂ), κ₀ ≠ 0 ∧ MeromorphicOn ζc Set.univ ∧
      AnalyticOnNhd ℂ ζc {w : ℂ | w ≠ 1} ∧
      (∀ w : ℂ, 1 < w.re → ζc w = dedekindZeta F w) ∧
      Tendsto (fun w : ℂ => (w - 1) * ζc w) (𝓝[≠] (1 : ℂ)) (𝓝 κ₀) := by
  obtain ⟨Λ, hΛdiff, hΛfe, hΛeq, ⟨ξ, hξdiff, hξeq, -⟩, hξne, -⟩ :=
    NumberField.exists_completedDedekindZeta_package F
  obtain ⟨-, hξ1⟩ := hξne ξ hξdiff hξeq
  set r₁ := NumberField.InfinitePlace.nrRealPlaces F
  set r₂ := NumberField.InfinitePlace.nrComplexPlaces F
  set d : ℤ := NumberField.discr F
  have hd : d ≠ 0 := NumberField.discr_ne_zero F
  set D : ℂ → ℂ := fun w => (((|d| : ℤ) : ℂ)) ^ (w / 2) with hD_def
  set H : ℂ → ℂ := archInv r₁ r₂ with hH_def
  have hr : r₁ + r₂ ≠ 0 := by
    intro h
    have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    have h1 : r₁ = 0 := by omega
    have h2 : r₂ = 0 := by omega
    rw [show NumberField.InfinitePlace.nrRealPlaces F = r₁ from rfl,
      show NumberField.InfinitePlace.nrComplexPlaces F = r₂ from rfl, h1, h2] at hrank
    omega
  have hH0 : H 0 = 0 := archInv_zero hr
  have hHdiff : Differentiable ℂ H := differentiable_archInv r₁ r₂
  have hDdiff : Differentiable ℂ D := differentiable_discPow d hd
  have hDne : ∀ w, D w ≠ 0 := discPow_ne_zero d hd

  have hslope_an0 : AnalyticAt ℂ (dslope H 0) 0 := by
    obtain ⟨p, hp⟩ := (hHdiff.analyticAt 0)
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  have hslope_diff : Differentiable ℂ (dslope H 0) := by
    intro b
    by_cases hb : b = 0
    · subst hb; exact hslope_an0.differentiableAt
    · exact (differentiableAt_dslope_of_ne hb).mpr (hHdiff b)
  have hslope_ne : ∀ w : ℂ, w ≠ 0 → dslope H 0 w = H w / w := by
    intro w hw
    rw [dslope_of_ne _ hw, slope_def_field, hH0, sub_zero, sub_zero]

  set G : ℂ → ℂ := fun w => ξ w * (D w)⁻¹ * dslope H 0 w with hG_def
  have hGdiff : Differentiable ℂ G :=
    (hξdiff.mul (hDdiff.inv hDne)).mul hslope_diff
  set ζc : ℂ → ℂ := fun w => G w * (w - 1)⁻¹ with hζc_def
  refine ⟨ζc, G 1, ?_, ?_, ?_, ?_, ?_⟩
  ·
    simp only [hG_def]
    refine mul_ne_zero (mul_ne_zero hξ1 (inv_ne_zero (hDne 1))) ?_
    rw [hslope_ne 1 one_ne_zero, div_one]
    exact archInv_one_ne_zero r₁ r₂
  ·
    intro w _
    refine ((hGdiff.analyticAt w).meromorphicAt).mul ?_
    exact ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
  ·
    intro w hw
    have hw' : w ≠ 1 := hw
    refine (hGdiff.analyticAt w).mul ?_
    exact (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hw')
  ·
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw; linarith
    have hw1 : w ≠ 1 := by
      intro h; rw [h] at hw; simp at hw
    have hwre : 0 < w.re := by linarith
    have hΛw : Λ w = D w * Gammaℝ w ^ r₁ * Gammaℂ w ^ r₂ * dedekindZeta F w := hΛeq w hw
    have hξw := hξeq w hw0 hw1
    have harch : H w * (Gammaℝ w ^ r₁ * Gammaℂ w ^ r₂) = 1 :=
      archInv_mul_eq_one (r₁ := r₁) (r₂ := r₂) hwre
    have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    show ξ w * (D w)⁻¹ * dslope H 0 w * (w - 1)⁻¹ = dedekindZeta F w
    rw [hslope_ne w hw0, hξw, hΛw]
    calc w * (w - 1) * (D w * Gammaℝ w ^ r₁ * Gammaℂ w ^ r₂ * dedekindZeta F w) * (D w)⁻¹
          * (H w / w) * (w - 1)⁻¹
        = dedekindZeta F w * (H w * (Gammaℝ w ^ r₁ * Gammaℂ w ^ r₂)) * (w * w⁻¹)
            * ((w - 1) * (w - 1)⁻¹) * (D w * (D w)⁻¹) := by ring
      _ = dedekindZeta F w := by
        rw [harch, mul_inv_cancel₀ hw0, mul_inv_cancel₀ hsub, mul_inv_cancel₀ (hDne w)]; ring
  ·
    have hcont : ContinuousAt G 1 := (hGdiff 1).continuousAt
    refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
    simp only [hζc_def]
    field_simp

theorem differentiable_finsetProd_one_sub_nrm {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Differentiable ℂ (fun w : ℂ => ∏ v ∈ S, (1 - nrm w v.asIdeal)) := by
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const (1 : ℂ)).sub ?_
  have hne : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp (one_le_absNorm v.ne_bot))
  have h : Differentiable ℂ (fun w : ℂ => ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)) :=
    Differentiable.const_cpow differentiable_id.neg (Or.inl hne)
  exact h

theorem finsetProd_one_sub_nrm_ne_zero {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {w : ℂ} (hw : 0 < w.re) :
    ∏ v ∈ S, (1 - nrm w v.asIdeal) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_nrm_prime_ne_zero hw v

theorem multipliable_one_sub_nrm_compl {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {w : ℂ} (hw : 1 < w.re) :
    Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => 1 - nrm w v.1.asIdeal) := by
  have hneg : Summable fun v : HeightOneSpectrum (𝓞 F) => -nrm w v.asIdeal :=
    (summable_norm_nrm_prime hw).of_norm.neg
  have hnegS : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => -nrm w v.1.asIdeal := by
    have h := hneg.comp_injective
      (Subtype.val_injective (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ S))
    exact h
  have h := Complex.multipliable_one_add_of_summable hnegS
  exact h.congr fun v => (sub_eq_add_neg _ _).symm

theorem main_nrm (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (Z : ℂ → ℂ) (κ : ℂ), κ ≠ 0 ∧
      MeromorphicOn Z Set.univ ∧
      AnalyticOnNhd ℂ Z {w : ℂ | w ≠ 1} ∧
      (∀ w : ℂ, 1 < w.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => (1 - nrm w v.1.asIdeal)) ∧
        Z w * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - nrm w v.1.asIdeal) = 1) ∧
      Tendsto (fun w : ℂ => (w - 1) * Z w) (𝓝[≠] (1 : ℂ)) (𝓝 κ) := by
  obtain ⟨ζc, κ₀, hκ₀, hmero, han, heq, hlim⟩ := exists_dedekindZeta_continuation F
  have hESdiff : Differentiable ℂ (fun w : ℂ => ∏ v ∈ S, (1 - nrm w v.asIdeal)) :=
    differentiable_finsetProd_one_sub_nrm S
  refine ⟨fun w => ζc w * ∏ v ∈ S, (1 - nrm w v.asIdeal), κ₀ * ∏ v ∈ S, (1 - nrm 1 v.asIdeal),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero hκ₀ (finsetProd_one_sub_nrm_ne_zero S (by simp))
  · intro w hw
    exact (hmero w hw).mul (hESdiff.analyticAt w).meromorphicAt
  · intro w hw
    exact (han w hw).mul (hESdiff.analyticAt w)
  · intro w hw
    obtain ⟨hmult, hprod⟩ := dedekindZeta_mul_tprod_eq_one (F := F) hw
    have hcS := multipliable_one_sub_nrm_compl S hw

    have hS : Multipliable ((fun v : HeightOneSpectrum (𝓞 F) => 1 - nrm w v.asIdeal) ∘ (↑) :
        (↑S : Set (HeightOneSpectrum (𝓞 F))) → ℂ) :=
      (hasProd_fintype _).multipliable
    have hSc : Multipliable ((fun v : HeightOneSpectrum (𝓞 F) => 1 - nrm w v.asIdeal) ∘ (↑) :
        ↑((↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) → ℂ) := by
      exact hcS
    have hsplit0 := hS.tprod_mul_tprod_compl hSc
    have h2 : ∏' x : (↑S : Set (HeightOneSpectrum (𝓞 F))), (1 - nrm w (↑x : HeightOneSpectrum (𝓞 F)).asIdeal)
        = ∏ x ∈ S, (1 - nrm w x.asIdeal) :=
      Finset.tprod_subtype' S (fun v : HeightOneSpectrum (𝓞 F) => 1 - nrm w v.asIdeal)
    rw [h2] at hsplit0
    have hsplit : (∏ v ∈ S, (1 - nrm w v.asIdeal)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - nrm w v.1.asIdeal)
        = ∏' v : HeightOneSpectrum (𝓞 F), (1 - nrm w v.asIdeal) := by
      exact hsplit0
    refine ⟨hcS, ?_⟩
    show ζc w * (∏ v ∈ S, (1 - nrm w v.asIdeal)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - nrm w v.1.asIdeal) = 1
    rw [heq w hw, mul_assoc, hsplit]
    exact hprod
  · have hc : ContinuousAt (fun w : ℂ => ∏ v ∈ S, (1 - nrm w v.asIdeal)) 1 :=
      (hESdiff 1).continuousAt
    have h := hlim.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
    refine h.congr' ?_
    filter_upwards with w
    ring

end SF86a45a1dZ
p2m_reactivate "P2MW.S_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul.SF86a45a1dZ"

theorem solution
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ (Z : ℂ → ℂ) (κ : ℂ), κ ≠ 0 ∧
      MeromorphicOn Z Set.univ ∧
      AnalyticOnNhd ℂ Z {w : ℂ | w ≠ 1} ∧
      (∀ w : ℂ, 1 < w.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w))) ∧
        Z w * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)) = 1) ∧
      Tendsto (fun w : ℂ => (w - 1) * Z w) (𝓝[≠] (1 : ℂ)) (𝓝 κ) := by
  have h := SF86a45a1dZ.main_nrm F S
  unfold SF86a45a1dZ.nrm at h
  exact h

end S_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul
end P2MW
export P2MW.S_NumberField_exists_meromorphicOn_mul_tprod_one_sub_absNorm_cpow_neg_eq_one_and_tendsto_sub_one_mul (solution)

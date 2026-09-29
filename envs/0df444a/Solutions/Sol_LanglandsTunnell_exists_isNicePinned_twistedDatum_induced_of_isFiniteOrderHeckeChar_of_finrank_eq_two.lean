-- Prove2me | solution 1 for LanglandsTunnell.exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b7f3b2e2-aa73-5c18-afa6-8b6197f534e9

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum
import Theorems.Thm_LanglandsTunnell_Converse_isNicePinned_of_entire_pair
import Theorems.Thm_LanglandsTunnell_Converse_isArchCompAt_comp_idelicNorm_genuineBaseChange
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_zero_of_isOfFinOrder
import Theorems.Thm_LanglandsTunnell_exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one_of_finrank_eq_two
import Theorems.Thm_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
import Theorems.Thm_LanglandsTunnell_exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate
open scoped Pointwise

namespace InducedNiceSol

section Chars

variable {K : Type} [Field K] [NumberField K]

theorem norm_apply_eq_one {G : Type*} [Group G] {χ : G →* ℂˣ} (hχ : IsOfFinOrder χ) (x : G) :
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hχn⟩ := hχ.exists_pow_eq_one
  have h1 : ((χ x : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχn, MonoidHom.one_apply, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h1 hn.ne'

theorem localChar_mul (χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : localChar (χ * ψ) v t = localChar χ v t * localChar ψ v t := rfl

theorem localChar_inv (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) : localChar χ⁻¹ v t = (localChar χ v t)⁻¹ := rfl

theorem isUnramifiedCharAt_mul {χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : IsUnramifiedCharAt χ v) (hψ : IsUnramifiedCharAt ψ v) : IsUnramifiedCharAt (χ * ψ) v :=
  fun t h1 h2 => by rw [localChar_mul, hχ t h1 h2, hψ t h1 h2, one_mul]

theorem isUnramifiedCharAt_inv {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : IsUnramifiedCharAt χ v) : IsUnramifiedCharAt χ⁻¹ v :=
  fun t h1 h2 => by rw [localChar_inv, hχ t h1 h2, inv_one]

theorem mem_and_inv_mem_of_valuation_eq_one {v : HeightOneSpectrum (𝓞 K)} (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = 1) :
    (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
      ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  refine ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ht.le,
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]

theorem valuation_eq_one_of_mem {v : HeightOneSpectrum (𝓞 K)} (t : (v.adicCompletion K)ˣ)
    (h1 : (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (h2 : ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    Valued.v (t : v.adicCompletion K) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  have h0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)

theorem isUnramifiedCharAt_of_forall {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (h : ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 → localChar χ v t = 1) :
    IsUnramifiedCharAt χ v :=
  fun t h1 h2 => h t (valuation_eq_one_of_mem t h1 h2)

theorem apply_localUnit_eq_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hχ : IsUnramifiedCharAt χ v) (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = 1) :
    χ (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1 := by
  have h := mem_and_inv_mem_of_valuation_eq_one t ht
  exact hχ t h.1 h.2

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  omega

end Chars

section Fibre

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] Ideal.Quotient.field in
theorem absNorm_eq_pow_inertiaDeg {v : HeightOneSpectrum (𝓞 F)} {𝔓 : HeightOneSpectrum (𝓞 E)}
    (h : 𝔓.under (𝓞 F) = v) :
    Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm v.asIdeal ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
  haveI := v.isPrime.isMaximal v.ne_bot
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  haveI : Finite (𝓞 E ⧸ 𝔓.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔓.ne_bot
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ 𝔓.asIdeal) := Module.Finite.of_finite
  rw [Ideal.inertiaDeg_algebraMap, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact Module.natCard_eq_pow_finrank

theorem sum_le_finrank {v : HeightOneSpectrum (𝓞 F)} (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : ∀ 𝔓 ∈ T, 𝔓.under (𝓞 F) = v) :
    ∑ 𝔓 ∈ T, v.asIdeal.ramificationIdx' 𝔓.asIdeal * v.asIdeal.inertiaDeg' 𝔓.asIdeal ≤ Module.finrank F E ∧
      ∀ 𝔓 ∈ T, 1 ≤ v.asIdeal.ramificationIdx' 𝔓.asIdeal * v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  classical
  haveI := v.isPrime.isMaximal v.ne_bot
  have hsum := Ideal.sum_ramification_inertia (K := F) (L := E) (S := 𝓞 E) (p := v.asIdeal) v.ne_bot
  have hmem : ∀ 𝔓 ∈ T, 𝔓.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) := by
    intro 𝔓 h𝔓
    haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hT 𝔓 h𝔓, HeightOneSpectrum.under_asIdeal]⟩
    exact (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).mpr ⟨𝔓.isPrime, inferInstance⟩
  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E),
      1 ≤ v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).mp hP
    have he : v.asIdeal.ramificationIdx' P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P v.ne_bot
    have hf : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he hf.ne')
  have hinj : Set.InjOn (fun 𝔓 : HeightOneSpectrum (𝓞 E) => 𝔓.asIdeal) T :=
    fun a _ b _ h => HeightOneSpectrum.ext h
  have hsub : T.image (fun 𝔓 : HeightOneSpectrum (𝓞 E) => 𝔓.asIdeal) ⊆
      IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) := by
    intro P hP
    obtain ⟨𝔓, h𝔓, rfl⟩ := Finset.mem_image.mp hP
    exact hmem 𝔓 h𝔓
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun P =>
      v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P) (fun P _ _ => Nat.zero_le _)
  rw [hsum, Finset.sum_image hinj] at hle
  exact ⟨hle, fun 𝔓 h𝔓 => hpos _ (hmem 𝔓 h𝔓)⟩

theorem fibre_of_ne (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {w' w'' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w'') (h' : w'.under (𝓞 F) = v)
    (h'' : w''.under (𝓞 F) = v) :
    v.asIdeal.inertiaDeg' w'.asIdeal = 1 ∧ v.asIdeal.inertiaDeg' w''.asIdeal = 1 ∧
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = w' ∨ w = w'' := by
  classical
  have key : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ≠ w' → w ≠ w'' → False := by
    intro w hw h1 h2'
    obtain ⟨hle, hpos⟩ := sum_le_finrank (F := F) ({w, w', w''} : Finset (HeightOneSpectrum (𝓞 E)))
      (by
        intro 𝔓 h𝔓
        simp only [Finset.mem_insert, Finset.mem_singleton] at h𝔓
        rcases h𝔓 with rfl | rfl | rfl
        · exact hw
        · exact h'
        · exact h'')
    rw [h2, Finset.sum_insert (by simp [h1, h2']), Finset.sum_pair hne] at hle
    have a1 := hpos w (by simp)
    have a2 := hpos w' (by simp)
    have a3 := hpos w'' (by simp)
    omega
  obtain ⟨hle, hpos⟩ := sum_le_finrank (F := F) ({w', w''} : Finset (HeightOneSpectrum (𝓞 E)))
    (by
      intro 𝔓 h𝔓
      simp only [Finset.mem_insert, Finset.mem_singleton] at h𝔓
      rcases h𝔓 with rfl | rfl
      · exact h'
      · exact h'')
  rw [h2, Finset.sum_pair hne] at hle
  have a2 := hpos w' (by simp)
  have a3 := hpos w'' (by simp)
  have e1 : v.asIdeal.ramificationIdx' w'.asIdeal * v.asIdeal.inertiaDeg' w'.asIdeal = 1 := by omega
  have e2 : v.asIdeal.ramificationIdx' w''.asIdeal * v.asIdeal.inertiaDeg' w''.asIdeal = 1 := by omega
  refine ⟨Nat.eq_one_of_mul_eq_one_left e1, Nat.eq_one_of_mul_eq_one_left e2, fun w hw => ?_⟩
  by_contra hcon
  push Not at hcon
  exact key w hw hcon.1 hcon.2

theorem fibre_of_inertiaDeg_eq_two (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {w' : HeightOneSpectrum (𝓞 E)} (h' : w'.under (𝓞 F) = v) (hf : v.asIdeal.inertiaDeg' w'.asIdeal = 2) :
    ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = w' := by
  classical
  intro w hw
  by_contra hne
  obtain ⟨hle, hpos⟩ := sum_le_finrank (F := F) ({w, w'} : Finset (HeightOneSpectrum (𝓞 E)))
    (by
      intro 𝔓 h𝔓
      simp only [Finset.mem_insert, Finset.mem_singleton] at h𝔓
      rcases h𝔓 with rfl | rfl
      · exact hw
      · exact h')
  rw [h2, Finset.sum_pair hne, hf] at hle
  have a1 := hpos w (by simp)
  have a2 := hpos w' (by simp)
  have he : 1 ≤ v.asIdeal.ramificationIdx' w'.asIdeal := by
    have := hpos w' (by simp)
    rw [hf] at this
    omega
  nlinarith

theorem finite_setOf_under_mem (T : Finset (HeightOneSpectrum (𝓞 F))) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ T}.Finite := by
  have h : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ T} =
      ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 F))),
        Set.range (Subtype.val : v.Extension (𝓞 E) → HeightOneSpectrum (𝓞 E)) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_range, Finset.mem_coe]
    constructor
    · intro hw
      exact ⟨w.under (𝓞 F), hw, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨v, hv, ⟨w', rfl⟩⟩
      rw [w'.2]
      exact hv
  rw [h]
  refine Set.Finite.biUnion T.finite_toSet fun v _ => ?_
  haveI : Finite {w : HeightOneSpectrum (𝓞 E) // w.under (𝓞 F) = v} :=
    HeightOneSpectrum.Extension.finite (𝓞 F) F E (𝓞 E) v
  exact Set.finite_range _

theorem exists_finset_ramified :
    ∃ R : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ R, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
      v.asIdeal.ramificationIdx' w.asIdeal = 1 := by
  classical

  let B : Finset ℕ := (NumberField.discr E).natAbs.primeFactors
  have hfinE : {w : HeightOneSpectrum (𝓞 E) | ∃ p ∈ B, p.Prime ∧ (p : 𝓞 E) ∈ w.asIdeal}.Finite := by
    have hsub : {w : HeightOneSpectrum (𝓞 E) | ∃ p ∈ B, p.Prime ∧ (p : 𝓞 E) ∈ w.asIdeal} ⊆
        ⋃ p ∈ (B.filter Nat.Prime), {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {(p : 𝓞 E)}} := by
      rintro w ⟨p, hpB, hp, hpv⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter, exists_prop]
      exact ⟨p, ⟨hpB, hp⟩, by rw [Ideal.dvd_span_singleton]; exact hpv⟩
    refine Set.Finite.subset ?_ hsub
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => ?_
    have hp' : (p : ℕ).Prime := (Finset.mem_filter.mp hp).2
    apply Ideal.finite_factors
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp'.ne_zero
  refine ⟨hfinE.toFinset.image (fun w => w.under (𝓞 F)), fun v hv w hw => ?_⟩

  haveI := w.isPrime
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (w.asIdeal.under ℤ)).principal
  have hp' : w.asIdeal.under ℤ = Ideal.span {p} := hp
  have hne : w.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    have hn : ((Ideal.absNorm w.asIdeal : ℤ) : 𝓞 E) ∈ w.asIdeal := by
      rw [Int.cast_natCast]; exact Ideal.absNorm_mem _
    have : (Ideal.absNorm w.asIdeal : ℤ) ∈ w.asIdeal.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, eq_intCast]; exact hn
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at this
    exact w.ne_bot this
  have hp0 : p ≠ 0 := by
    intro h0; apply hne; rw [hp', h0]; simp
  have hprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    exact Ideal.IsPrime.under ℤ w.asIdeal
  set q : ℕ := p.natAbs with hq
  have hqprime : q.Prime := Int.prime_iff_natAbs_prime.mp hprime
  have hpmem : (p : 𝓞 E) ∈ w.asIdeal := by
    have : p ∈ w.asIdeal.under ℤ := by rw [hp']; exact Ideal.mem_span_singleton_self p
    rw [Ideal.under_def, Ideal.mem_comap, eq_intCast] at this
    exact this
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := by
    have hz : ((q : ℤ) : 𝓞 E) ∈ w.asIdeal ∨ ((-(q : ℤ) : ℤ) : 𝓞 E) ∈ w.asIdeal := by
      rcases Int.natAbs_eq p with h | h
      · left; rw [← h]; exact hpmem
      · right; rw [← h]; exact hpmem
    rcases hz with hz | hz
    · exact_mod_cast hz
    · rw [Int.cast_neg] at hz
      have := w.asIdeal.neg_mem hz
      rw [neg_neg] at this
      exact_mod_cast this

  have hqB : q ∉ B := by
    intro hB
    apply hv
    rw [Finset.mem_image]
    refine ⟨w, ?_, hw⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨q, hB, hqprime, hqmem⟩
  have hnd : ¬ ((q : ℤ) ∣ NumberField.discr E) := by
    intro h
    apply hqB
    rw [Nat.mem_primeFactors]
    exact ⟨hqprime, Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h),
      Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)⟩
  have hpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqprime
  haveI : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpr).mp hnd w.asIdeal inferInstance
      (by exact_mod_cast hqmem)
  haveI : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 F) (p := w.asIdeal)
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (w.asIdeal.under (𝓞 F)) w.asIdeal
    (Ideal.under_ne_bot (A := 𝓞 F) w.ne_bot)] at this
  rw [← HeightOneSpectrum.under_asIdeal, hw] at this
  exact this

end Fibre

section NormChar

open M4aHerbrand M4aHerbrand.GenuineDescent M4aHerbrand.Bridge

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

noncomputable def normChar (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ :=
  χ.comp (genuineBaseChange E M).idelicNorm

variable {E M}

theorem normChar_apply (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (x : (AdeleRing (𝓞 M) M)ˣ) :
    normChar E M χ x = χ ((genuineBaseChange E M).idelicNorm x) := rfl

theorem continuous_normChar {χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ} (hcχ : Continuous χ) :
    Continuous (normChar E M χ) :=
  hcχ.comp (Continuous.units_map _ (continuous_adelicNorm_genuineBaseChange E M))

theorem isUnitaryChar_normChar {χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ} (huχ : IsUnitaryChar (𝓞 E) E χ) :
    IsUnitaryChar (𝓞 M) M (normChar E M χ) := fun _ => huχ _

theorem idelicNorm_algebraMap (u : Mˣ) :
    (genuineBaseChange E M).idelicNorm (Units.map (algebraMap M (AdeleRing (𝓞 M) M) : M →* _) u) =
      Units.map (algebraMap E (AdeleRing (𝓞 E) E) : E →* _) (Units.map (Algebra.norm E : M →* E) u) :=
  Units.ext (adelicNorm_genuineBaseChange_algebraMap E M (u : M))

theorem isIdeleClassChar_normChar {χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 E) E χ) :
    IsIdeleClassChar (𝓞 M) M (normChar E M χ) := fun u => by
  rw [normChar_apply]
  erw [idelicNorm_algebraMap]
  exact hχ _

theorem idelicNorm_localUnit (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (t : (w.1.adicCompletion M)ˣ) :
    (genuineBaseChange E M).idelicNorm (Units.map (finIncl (𝓞 M) M) (localUnit (𝓞 M) M w.1 t)) =
      Units.map (finIncl (𝓞 E) E) (localUnit (𝓞 E) E v
        (Units.map (Algebra.norm (v.adicCompletion E) : w.1.adicCompletion M →* v.adicCompletion E) t)) := by
  classical
  set y : AdeleRing (𝓞 M) M := finIncl (𝓞 M) M (localUnit (𝓞 M) M w.1 t : (FiniteAdeleRing (𝓞 M) M)ˣ)
    with hy
  have hcw := M4aHerbrand.genuineAdelicNorm_componentwise E M y
  have hy2 : ∀ w' : HeightOneSpectrum (𝓞 M), (y.2 : FiniteAdeleRing (𝓞 M) M) w' =
      Function.update (1 : ∀ w' : HeightOneSpectrum (𝓞 M), w'.adicCompletion M) w.1
        (t : w.1.adicCompletion M) w' :=
    fun w' => rfl
  refine Units.ext (Prod.ext ?_ ?_)
  · show ((genuineBaseChange E M).adelicNorm y).1 = (1 : InfiniteAdeleRing E)
    have h1 : y.1 = 1 := rfl
    have := hcw.1
    rw [h1, map_one] at this
    exact this
  · show ((genuineBaseChange E M).adelicNorm y).2 =
      ((localUnit (𝓞 E) E v (Units.map (Algebra.norm (v.adicCompletion E) :
          w.1.adicCompletion M →* v.adicCompletion E) t) : (FiniteAdeleRing (𝓞 E) E)ˣ) :
        FiniteAdeleRing (𝓞 E) E)
    apply RestrictedProduct.ext
    intro v'
    refine (hcw.2 v').trans ?_
    show _ = Function.update (1 : ∀ v' : HeightOneSpectrum (𝓞 E), v'.adicCompletion E) v
      (Algebra.norm (v.adicCompletion E) (t : w.1.adicCompletion M)) v'
    letI := HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v'
    by_cases hvP : v' = v
    · subst hvP
      rw [Function.update_self, Fintype.prod_eq_single w]
      · rw [hy2, Function.update_self]
      · intro w' hw
        have hw1 : w'.1 ≠ w.1 := fun h => hw (Subtype.ext h)
        rw [hy2, Function.update_of_ne hw1, Pi.one_apply, map_one]
    · rw [Function.update_of_ne hvP, Pi.one_apply]
      apply Finset.prod_eq_one
      intro w' _
      have hw1 : w'.1 ≠ w.1 := by
        intro h
        apply hvP
        rw [← w'.2, h, w.2]
      rw [hy2, Function.update_of_ne hw1, Pi.one_apply, map_one]

theorem valuation_norm_eq_one (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M))
    (t : (w.1.adicCompletion M)ˣ) (ht : Valued.v (t : w.1.adicCompletion M) = 1) :
    Valued.v (Algebra.norm (v.adicCompletion E) (t : w.1.adicCompletion M)) = 1 := by
  rw [M4aHerbrand.valuation_norm_adicCompletion_eq_pow_inertiaDeg E M v w, ht, one_pow]

theorem isUnramifiedCharAt_normChar {χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ} (v : HeightOneSpectrum (𝓞 E))
    (w : v.Extension (𝓞 M)) (hχ : IsUnramifiedCharAt χ v) :
    IsUnramifiedCharAt (normChar E M χ) w.1 := by
  intro t h1 h2
  have ht := valuation_eq_one_of_mem t h1 h2
  rw [localChar_apply, normChar_apply, idelicNorm_localUnit v w t]
  exact apply_localUnit_eq_one hχ _ (valuation_norm_eq_one v w t ht)

theorem normChar_uniformizerIdele {χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ} (𝔓 : HeightOneSpectrum (𝓞 M))
    (hχ : IsUnramifiedCharAt χ (𝔓.under (𝓞 E))) :
    normChar E M χ (uniformizerIdele M 𝔓) =
      χ (uniformizerIdele E (𝔓.under (𝓞 E))) ^ (𝔓.under (𝓞 E)).asIdeal.inertiaDeg' 𝔓.asIdeal := by
  obtain ⟨t, ht, hN⟩ :=
    M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit E M 𝔓
  rw [normChar_apply, hN, map_mul, map_pow, apply_localUnit_eq_one hχ t ht, mul_one]

end NormChar

section Arch

variable {K : Type} [Field K] [NumberField K]

theorem archLocalChar_mul (χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (x : (w.Completion)ˣ) : archLocalChar (χ * ψ) w x = archLocalChar χ w x * archLocalChar ψ w x := rfl

omit [NumberField K] in
open NumberField.InfinitePlace.Completion in

theorem sign_sq_eq_one {w : InfinitePlace K} (hw : w.IsReal) (x : (w.Completion)ˣ) :
    (extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ)) ^ 2 = 1 := by
  have hreal : ((extensionEmbeddingOfIsReal hw (x : w.Completion) : ℝ) : ℂ) =
      extensionEmbedding w (x : w.Completion) := extensionEmbeddingOfIsReal_apply hw _
  have hnorm : ‖extensionEmbedding w (x : w.Completion)‖ = ‖(x : w.Completion)‖ := by
    have := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) (x : w.Completion)
    exact this
  have hx0 : ‖(x : w.Completion)‖ ≠ 0 := norm_ne_zero_iff.mpr x.ne_zero
  set r : ℝ := extensionEmbeddingOfIsReal hw (x : w.Completion) with hr
  rw [← hreal] at hnorm ⊢
  rw [Complex.norm_real] at hnorm

  have hr0 : r ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact hx0 hnorm.symm
  rw [← hnorm, Real.norm_eq_abs, div_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← sq_abs r,
    div_self]
  exact_mod_cast pow_ne_zero 2 (abs_ne_zero.mpr hr0)

omit [NumberField K] in
open NumberField.InfinitePlace.Completion in

theorem sign_zpow_eq_of_even_sub {w : InfinitePlace K} (hw : w.IsReal) (x : (w.Completion)ˣ)
    {a b : ℤ} (h : Even (a - b)) :
    (extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ)) ^ a =
      (extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ)) ^ b := by
  obtain ⟨m, hm⟩ := h
  set z := extensionEmbedding w (x : w.Completion) / (‖(x : w.Completion)‖ : ℂ) with hz
  have hz2 : z ^ (2 : ℤ) = 1 := by exact_mod_cast sign_sq_eq_one hw x
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_zpow 2 (by norm_num)] at hz2
    exact zero_ne_one hz2
  have ha : a = b + m * 2 := by omega
  rw [ha, zpow_add₀ hz0, zpow_mul', hz2, one_zpow, mul_one]

open NumberField.InfinitePlace.Completion in

theorem archLocalChar_neg_one_of_isArchCompAt {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {w : InfinitePlace K}
    {u : ℂ} {a : ℤ} (h : IsArchCompAt K χ w u a) :
    ((archLocalChar χ w (-1) : ℂˣ) : ℂ) = (-1) ^ a := by
  have := h (-1)
  rw [this]
  simp only [Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, Complex.one_cpow,
    one_mul, map_neg, map_one, div_one]

end Arch

section SPart

variable {K : Type} [Field K]

open scoped Classical in

noncomputable def expVec {β : Type} (S : Finset (HeightOneSpectrum (𝓞 K))) (vOf : β → ↥S) (f : β → ℕ)
    (T : Finset β) : ↥S → ℤ :=
  fun v => -∑ b ∈ T with vOf b = v, (f b : ℤ)

open scoped Classical in

noncomputable def coeffFamily {β : Type} (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Finset β)
    (vOf : β → ↥S) (f : β → ℕ) (α : β → ℂ) : (↥S → ℤ) → ℂ :=
  fun n => ∑ T ∈ W.powerset with expVec S vOf f T = n, ∏ b ∈ T, (-α b)

theorem prod_zpow_expVec {β : Type} [DecidableEq β] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (vOf : β → ↥S) (f : β → ℕ) (T : Finset β) (x : ↥S → ℂ) (hx : ∀ v, x v ≠ 0) :
    ∏ v : ↥S, x v ^ (expVec S vOf f T v) = ∏ b ∈ T, (x (vOf b)) ^ (-(f b : ℤ)) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp [expVec]
  | insert b T hb ih =>
    rw [Finset.prod_insert hb, ← ih]
    have hsplit : ∀ v : ↥S, x v ^ expVec S vOf f (insert b T) v =
        (if vOf b = v then x v ^ (-(f b : ℤ)) else 1) * x v ^ expVec S vOf f T v := by
      intro v
      unfold expVec
      rw [Finset.filter_insert]
      by_cases hv : vOf b = v
      · rw [if_pos hv, if_pos hv, Finset.sum_insert (by simp [hb]), neg_add, zpow_add₀ (hx v)]
      · rw [if_neg hv, if_neg hv, one_mul]
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq]
    simp

theorem hasSum_coeffFamily {β : Type} [DecidableEq β] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (W : Finset β) (vOf : β → ↥S) (f : β → ℕ) (α : β → ℂ) (x : ↥S → ℂ) (hx : ∀ v, x v ≠ 0) :
    HasSum (fun n : ↥S → ℤ => coeffFamily S W vOf f α n * ∏ v : ↥S, x v ^ (n v))
      (∏ b ∈ W, (1 - α b * (x (vOf b)) ^ (-(f b : ℤ)))) := by
  classical
  have hexp : ∏ b ∈ W, (1 - α b * (x (vOf b)) ^ (-(f b : ℤ))) =
      ∑ T ∈ W.powerset, ∏ b ∈ T, (-α b * (x (vOf b)) ^ (-(f b : ℤ))) := by
    have : ∀ b ∈ W, (1 - α b * (x (vOf b)) ^ (-(f b : ℤ))) =
        (-α b * (x (vOf b)) ^ (-(f b : ℤ))) + 1 := fun b _ => by ring
    rw [Finset.prod_congr rfl this, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_const_one, mul_one]
  have hterm : ∀ T ∈ W.powerset, ∏ b ∈ T, (-α b * (x (vOf b)) ^ (-(f b : ℤ))) =
      (∏ b ∈ T, (-α b)) * ∏ v : ↥S, x v ^ (expVec S vOf f T v) := by
    intro T _
    rw [prod_zpow_expVec S vOf f T x hx, ← Finset.prod_mul_distrib]
  rw [hexp, Finset.sum_congr rfl hterm]
  let g : Finset β → ℂ := fun T => (∏ b ∈ T, (-α b)) * ∏ v : ↥S, x v ^ (expVec S vOf f T v)
  have hfib : ∀ n : ↥S → ℤ, coeffFamily S W vOf f α n * ∏ v : ↥S, x v ^ (n v) =
      ∑ T ∈ W.powerset with expVec S vOf f T = n, g T := by
    intro n
    unfold coeffFamily
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_filter] at hT
    simp only [g, hT.2]
  simp_rw [hfib]
  have hzero : ∀ n ∉ (W.powerset).image (expVec S vOf f),
      ∑ T ∈ W.powerset with expVec S vOf f T = n, g T = 0 := by
    intro n hn
    apply Finset.sum_eq_zero
    intro T hT
    rw [Finset.mem_filter] at hT
    exact absurd (Finset.mem_image.mpr ⟨T, hT.1, hT.2⟩) hn
  rw [← Finset.sum_fiberwise_of_maps_to (g := expVec S vOf f)
    (fun T hT => Finset.mem_image_of_mem (expVec S vOf f) hT)]
  exact hasSum_sum_of_ne_finset_zero hzero

theorem tsum_coeffFamily {β : Type} [DecidableEq β] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (W : Finset β) (vOf : β → ↥S) (f : β → ℕ) (α : β → ℂ) (x : ↥S → ℂ) (hx : ∀ v, x v ≠ 0) :
    ∑' n : ↥S → ℤ, coeffFamily S W vOf f α n * ∏ v : ↥S, x v ^ (n v) =
      ∏ b ∈ W, (1 - α b * (x (vOf b)) ^ (-(f b : ℤ))) :=
  (hasSum_coeffFamily S W vOf f α x hx).tsum_eq

theorem norm_coeffFamily_le {β : Type} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (W : Finset β) (vOf : β → ↥S) (f : β → ℕ) (α : β → ℂ) (n : ↥S → ℤ) :
    ‖coeffFamily S W vOf f α n‖ ≤ ∑ T ∈ W.powerset, ∏ b ∈ T, ‖α b‖ := by
  classical
  unfold coeffFamily
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun T _ _ => norm_nonneg _)).trans ?_
  refine Finset.sum_le_sum fun T _ => ?_
  simp only [norm_prod, norm_neg, le_refl]

theorem coeffFamily_eq_zero_of_lt {β : Type} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (W : Finset β) (vOf : β → ↥S) (f : β → ℕ) (α : β → ℂ) (n : ↥S → ℤ)
    (hn : ∃ v, n v < expVec S vOf f W v) : coeffFamily S W vOf f α n = 0 := by
  classical
  obtain ⟨v, hv⟩ := hn
  unfold coeffFamily
  apply Finset.sum_eq_zero
  intro T hT
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  exfalso
  have hle : expVec S vOf f W v ≤ expVec S vOf f T v := by
    unfold expVec
    rw [neg_le_neg_iff]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset_filter _ hT.1)
      (fun b _ _ => by positivity)
  rw [hT.2] at hle
  omega

theorem coeffFamily_zero {β : Type} (S : Finset (HeightOneSpectrum (𝓞 K)))
    (W : Finset β) (vOf : β → ↥S) (f : β → ℕ) (hf : ∀ b, 1 ≤ f b) (α : β → ℂ) :
    coeffFamily S W vOf f α 0 = 1 := by
  classical
  unfold coeffFamily
  have hfilter : (W.powerset.filter fun T => expVec S vOf f T = 0) = {∅} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hT⟩
      by_contra hne
      obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h0 := congrFun hT (vOf b)
      unfold expVec at h0
      simp only [Pi.zero_apply, neg_eq_zero] at h0
      have hmem : b ∈ T.filter (fun b' => vOf b' = vOf b) := Finset.mem_filter.mpr ⟨hb, rfl⟩
      have hle : (f b : ℤ) ≤ ∑ b' ∈ T with vOf b' = vOf b, (f b' : ℤ) :=
        Finset.single_le_sum (f := fun b' => (f b' : ℤ)) (fun _ _ => by positivity) hmem
      have := hf b
      omega
    · rintro rfl
      refine ⟨Finset.empty_subset _, ?_⟩
      funext v
      simp [expVec]
  rw [hfilter, Finset.sum_singleton, Finset.prod_empty]

end SPart

section Analysis

theorem differentiable_cpow_neg (q : ℂ) (hq : q ≠ 0) : Differentiable ℂ fun s : ℂ => q ^ (-s) :=
  (differentiable_id.neg).const_cpow (Or.inl hq)

theorem boundedOnStrips_finset_prod {β : Type} (W : Finset β) (g : β → ℂ → ℂ)
    (hg : ∀ b ∈ W, LDatum.BoundedOnStrips (g b)) : LDatum.BoundedOnStrips fun s => ∏ b ∈ W, g b s := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    intro a b
    exact ⟨1, fun s _ _ => by simp⟩
  | insert b W hb ih =>
    intro a c
    obtain ⟨C₁, hC₁⟩ := hg b (Finset.mem_insert_self _ _) a c
    obtain ⟨C₂, hC₂⟩ := ih (fun b' hb' => hg b' (Finset.mem_insert_of_mem hb')) a c
    refine ⟨C₁ * C₂, fun s h1 h2 => ?_⟩
    dsimp only
    rw [Finset.prod_insert hb, norm_mul]
    have h0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ s h1 h2)
    exact mul_le_mul (hC₁ s h1 h2) (hC₂ s h1 h2) (norm_nonneg _) h0

theorem boundedOnStrips_mul {f g : ℂ → ℂ} (hf : LDatum.BoundedOnStrips f) (hg : LDatum.BoundedOnStrips g) :
    LDatum.BoundedOnStrips fun s => f s * g s := by
  intro a b
  obtain ⟨C₁, hC₁⟩ := hf a b
  obtain ⟨C₂, hC₂⟩ := hg a b
  refine ⟨C₁ * C₂, fun s h1 h2 => ?_⟩
  rw [norm_mul]
  have h0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ s h1 h2)
  exact mul_le_mul (hC₁ s h1 h2) (hC₂ s h1 h2) (norm_nonneg _) h0

theorem boundedOnStrips_one_sub (c : ℂ) (q : ℕ) (hq : 0 < q) (α β : ℝ) :
    LDatum.BoundedOnStrips fun s : ℂ => 1 - c * (q : ℂ) ^ ((α : ℂ) * s + β) := by
  intro a b

  refine ⟨1 + ‖c‖ * ((q : ℝ) ^ (α * a + β) + (q : ℝ) ^ (α * b + β)), fun s h1 h2 => ?_⟩
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_natCast_cpow_of_pos hq]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have hre : ((α : ℂ) * s + β).re = α * s.re + β := by simp
  rw [hre]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hx : α * s.re + β ≤ α * a + β ∨ α * s.re + β ≤ α * b + β := by
    rcases le_total 0 α with hα | hα
    · exact Or.inr (by nlinarith [mul_le_mul_of_nonneg_left h2 hα])
    · exact Or.inl (by nlinarith [mul_le_mul_of_nonpos_left h1 hα])
  rcases hx with h | h
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 h).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le hq1 h).trans (le_add_of_nonneg_left (by positivity))

theorem ofReal_mul_prod_zpow_cpow {ι : Type} (T : Finset ι) (N : ℝ) (hN : 0 < N) (q : ι → ℕ)
    (hq : ∀ i, 0 < q i) (k : ι → ℤ) (r : ℂ) :
    (((N * ∏ i ∈ T, (q i : ℝ) ^ (k i) : ℝ)) : ℂ) ^ r =
      (N : ℂ) ^ r * ∏ i ∈ T, ((q i : ℂ) ^ r) ^ (k i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_left_comm, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), ih]
    have hqpos : (0 : ℝ) < q i := by exact_mod_cast hq i
    have h1 : (((q i : ℝ) ^ (k i) : ℝ) : ℂ) ^ r = ((q i : ℂ) ^ r) ^ (k i) := by
      have hqk : (0 : ℝ) < (q i : ℝ) ^ (k i) := zpow_pos hqpos _
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hqk.ne'),
        Complex.cpow_def_of_ne_zero (by exact_mod_cast hqpos.ne'), ← Complex.exp_int_mul,
        ← Complex.ofReal_log hqk.le, Real.log_zpow,
        show ((q i : ℕ) : ℂ) = ((q i : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_log hqpos.le]
      push_cast
      ring_nf
    rw [h1]
    ring

theorem differentiable_finset_prod {β : Type} (W : Finset β) (g : β → ℂ → ℂ)
    (hg : ∀ b ∈ W, Differentiable ℂ (g b)) : Differentiable ℂ fun s => ∏ b ∈ W, g b s := by
  classical
  induction W using Finset.induction_on with
  | empty => simp
  | insert b W hb ih =>
    have h := (hg b (Finset.mem_insert_self _ _)).mul
      (ih fun b' hb' => hg b' (Finset.mem_insert_of_mem hb'))
    convert h using 1 <;> try rfl
    funext s
    rw [Finset.prod_insert hb]
    rfl

theorem natCast_pow_cpow (a n : ℕ) (s : ℂ) : (((a ^ n : ℕ)) : ℂ) ^ s = (((a : ℕ) : ℂ) ^ s) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

theorem natCast_cpow_ne_zero {a : ℕ} (ha : a ≠ 0) (s : ℂ) : ((a : ℂ)) ^ s ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (by exact_mod_cast ha)

end Analysis

section Table

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

open scoped Classical in

noncomputable def inducedTable (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) : HeckeEigensystem E ℂ :=
  letI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype (v.Extension (𝓞 M)) :=
    fun v => HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
  { level := ⊤
    level_ne_bot := by simp
    a := fun v => ∑ w : v.Extension (𝓞 M),
      if v.asIdeal.inertiaDeg' w.1.asIdeal = 1 then ((ξ (uniformizerIdele M w.1) : ℂˣ) : ℂ) else 0
    b := fun v => ∏ w : v.Extension (𝓞 M),
      if v.asIdeal.inertiaDeg' w.1.asIdeal = 1 then ((ξ (uniformizerIdele M w.1) : ℂˣ) : ℂ)
      else -((ξ (uniformizerIdele M w.1) : ℂˣ) : ℂ) }

variable {E M}

theorem inducedTable_split (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    {v : HeightOneSpectrum (𝓞 E)} {w' w'' : HeightOneSpectrum (𝓞 M)} (hne : w' ≠ w'')
    (h' : w'.under (𝓞 E) = v) (h'' : w''.under (𝓞 E) = v) :
    (inducedTable E M ξ).a v = ((ξ (uniformizerIdele M w') : ℂˣ) : ℂ) + ξ (uniformizerIdele M w'') ∧
      (inducedTable E M ξ).b v = ((ξ (uniformizerIdele M w') : ℂˣ) : ℂ) * ξ (uniformizerIdele M w'') := by
  classical
  letI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype (v.Extension (𝓞 M)) :=
    fun v => HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
  obtain ⟨hf', hf'', hall⟩ := fibre_of_ne h2 hne h' h''
  let w₁ : v.Extension (𝓞 M) := ⟨w', h'⟩
  let w₂ : v.Extension (𝓞 M) := ⟨w'', h''⟩
  have hne' : w₁ ≠ w₂ := fun h => hne (congrArg Subtype.val h)
  have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁, w₂} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hall w.1 w.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  constructor
  · show (∑ w : v.Extension (𝓞 M), _) = _
    rw [huniv, Finset.sum_pair hne']
    simp [w₁, w₂, hf', hf'']
  · show (∏ w : v.Extension (𝓞 M), _) = _
    rw [huniv, Finset.prod_pair hne']
    simp [w₁, w₂, hf', hf'']

theorem inducedTable_inert (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    {v : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 M)} (h' : w'.under (𝓞 E) = v)
    (hf : v.asIdeal.inertiaDeg' w'.asIdeal = 2) :
    (inducedTable E M ξ).a v = 0 ∧ (inducedTable E M ξ).b v = -((ξ (uniformizerIdele M w') : ℂˣ) : ℂ) := by
  classical
  letI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype (v.Extension (𝓞 M)) :=
    fun v => HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
  have hall := fibre_of_inertiaDeg_eq_two h2 h' hf
  let w₁ : v.Extension (𝓞 M) := ⟨w', h'⟩
  have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁} := by
    ext w
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hall w.1 w.2)
  constructor
  · show (∑ w : v.Extension (𝓞 M), _) = _
    rw [huniv, Finset.sum_singleton]
    simp [w₁, hf]
  · show (∏ w : v.Extension (𝓞 M), _) = _
    rw [huniv, Finset.prod_singleton]
    simp [w₁, hf]

theorem inducedTable_clause (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        (inducedTable E M ξ).a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        (inducedTable E M ξ).b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        (inducedTable E M ξ).a w = 0 ∧ (inducedTable E M ξ).b w = -(ξ (uniformizerIdele M w') : ℂ)) :=
  fun _ _ => ⟨fun _ _ hne h' h'' => inducedTable_split h2 ξ hne h' h'',
    fun _ h' hf => inducedTable_inert h2 ξ h' hf⟩

end Table

section Families

variable (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]

noncomputable def WS (S : Finset (HeightOneSpectrum (𝓞 E))) : Finset (HeightOneSpectrum (𝓞 M)) :=
  (finite_setOf_under_mem (F := E) (E := M) S).toFinset

variable {E M} in
theorem mem_WS {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 M)} :
    w ∈ WS E M S ↔ w.under (𝓞 E) ∈ S := by
  simp [WS]

open scoped Classical in

noncomputable def Wxi (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    Finset (HeightOneSpectrum (𝓞 M)) :=
  (WS E M S).filter (fun w => IsUnramifiedCharAt ξ w)

variable {E M} in
theorem mem_Wxi {ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {w : HeightOneSpectrum (𝓞 M)} : w ∈ Wxi E M ξ S ↔ w.under (𝓞 E) ∈ S ∧ IsUnramifiedCharAt ξ w := by
  classical
  simp [Wxi, mem_WS]

noncomputable def vOfW (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ↥(Wxi E M ξ S) → ↥S :=
  fun w => ⟨w.1.under (𝓞 E), (mem_Wxi.mp w.2).1⟩

noncomputable def fdeg (w : HeightOneSpectrum (𝓞 M)) : ℕ := (w.under (𝓞 E)).asIdeal.inertiaDeg' w.asIdeal

noncomputable def alphaCoef (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 M)) : ℂ :=
  (((ξ (uniformizerIdele M w))⁻¹ : ℂˣ) : ℂ) *
    (((Ideal.absNorm (w.under (𝓞 E)).asIdeal : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))) ^ (fdeg E M w)

noncomputable def betaCoef (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (w : HeightOneSpectrum (𝓞 M)) : ℂ :=
  ((ξ (uniformizerIdele M w) : ℂˣ) : ℂ) *
    (((Ideal.absNorm (w.under (𝓞 E)).asIdeal : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))) ^ (fdeg E M w)

noncomputable def Afam (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (↥S → ℤ) → ℂ :=
  coeffFamily S (Finset.univ : Finset ↥(Wxi E M ξ S)) (vOfW E M ξ S) (fun w => fdeg E M w.1)
    (fun w => alphaCoef E M ξ w.1)

noncomputable def Adfam (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℂ) (k : ↥S → ℤ) : (↥S → ℤ) → ℂ :=
  fun n => c * coeffFamily S (Finset.univ : Finset ↥(Wxi E M ξ S)) (vOfW E M ξ S)
    (fun w => fdeg E M w.1) (fun w => betaCoef E M ξ w.1) (n + k)

variable {E M}

theorem one_le_fdeg (w : HeightOneSpectrum (𝓞 M)) : 1 ≤ fdeg E M w := by
  unfold fdeg
  haveI : w.asIdeal.LiesOver (w.under (𝓞 E)).asIdeal := ⟨by rw [HeightOneSpectrum.under_asIdeal]⟩
  haveI := (w.under (𝓞 E)).isPrime.isMaximal (w.under (𝓞 E)).ne_bot
  exact Ideal.inertiaDeg'_pos _ _

theorem Afam_bounded (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℂ) (k : ↥S → ℤ) :
    ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖Afam E M ξ S n‖ ≤ C ∧ ‖Adfam E M ξ S c k n‖ ≤ C := by
  refine ⟨max (∑ T ∈ (Finset.univ : Finset ↥(Wxi E M ξ S)).powerset, ∏ b ∈ T, ‖alphaCoef E M ξ b.1‖)
    (‖c‖ * ∑ T ∈ (Finset.univ : Finset ↥(Wxi E M ξ S)).powerset, ∏ b ∈ T, ‖betaCoef E M ξ b.1‖),
    fun n => ⟨?_, ?_⟩⟩
  · exact (norm_coeffFamily_le _ _ _ _ _ n).trans (le_max_left _ _)
  · unfold Adfam
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (norm_coeffFamily_le _ _ _ _ _ _) (norm_nonneg _)).trans
      (le_max_right _ _)

theorem Afam_support (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (c : ℂ) (k : ↥S → ℤ) :
    ∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → Afam E M ξ S n = 0 ∧ Adfam E M ξ S c k n = 0 := by
  let e : ↥S → ℤ := expVec S (vOfW E M ξ S) (fun w => fdeg E M w.1) Finset.univ
  refine ⟨fun v => min (e v) (e v - k v), fun n hn => ⟨?_, ?_⟩⟩
  · obtain ⟨v, hv⟩ := hn
    exact coeffFamily_eq_zero_of_lt _ _ _ _ _ n ⟨v, lt_of_lt_of_le hv (min_le_left _ _)⟩
  · obtain ⟨v, hv⟩ := hn
    have hv' : (n + k) v < e v := by
      have := lt_of_lt_of_le hv (min_le_right _ _)
      simp only [Pi.add_apply]
      omega
    unfold Adfam
    rw [coeffFamily_eq_zero_of_lt _ _ _ _ _ (n + k) ⟨v, hv'⟩, mul_zero]

theorem Afam_ne_zero (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    Afam E M ξ S ≠ 0 := by
  intro h
  have h0 : Afam E M ξ S 0 = 0 := by rw [h]; rfl
  unfold Afam at h0
  rw [coeffFamily_zero S Finset.univ (vOfW E M ξ S) (fun w => fdeg E M w.1)
    (fun w => one_le_fdeg w.1)] at h0
  exact one_ne_zero h0

end Families

end InducedNiceSol

namespace InducedNiceSol

section Twist

variable {E : Type} [Field E] [NumberField E] {M : Type} [Field M] [NumberField M] [Algebra E M]

open M4aHerbrand.GenuineDescent NumberField.InfinitePlace NumberField.InfinitePlace.Completion Polynomial

open scoped Classical in

theorem isNicePinned_twist
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS₀S : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hramS : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (c : ℂ) (k : ↥S → ℤ)
    (hck : ∀ (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ), IsAdmissibleTwist E μ →
      (∀ v ∈ S, IsUnramifiedCharAt μ v) →
      heckeConductor M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) =
        finiteConductor E μ S * ∏ v : ↥S, (Ideal.absNorm v.1.asIdeal : ℝ) ^ (k v) ∧
      ∀ (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
        (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
        (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ),
        (∀ w', ∀ hw' : w'.IsReal,
          ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
            (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val) →
        (∀ w', ∀ hw' : w'.IsComplex,
          (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
            else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ),
          heckeRootNumber M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) aR' kC' =
            c * (∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (k v)) *
              pinnedRootNumber E (inducedTable E M ξ) μ S (fun _ _ => RealArchParam.oddArtin)
                (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC)
    (a₀ : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (ha₀ : ∀ w', ∀ hw' : w'.IsReal, IsArchCompAt M ξ w' 0 ((a₀ w' hw').val : ℤ))
    (hξC : ∀ w' : InfinitePlace M, w'.IsComplex → IsArchCompAt M ξ w' 0 0)
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ)
    (hμS : ∀ v ∈ S, IsUnramifiedCharAt μ v)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt E μ w (uR w hw) ((aR w hw).val : ℤ))
    (hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt E μ w (uC w hw) (kC w hw)) :
    IsNicePinned
      (twistedDatum E (inducedTable E M ξ) S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC)
      (sPart E S (Afam E M ξ S) μ) (sPartDual E S (Adfam E M ξ S c k) μ)
      (pinnedRootNumber E (inducedTable E M ξ) μ S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC)
      (finiteConductor E μ S) := by
  classical
  obtain ⟨hμcl, hμc, hμu⟩ := hμ

  set lam : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ := ξ * μ.comp (genuineBaseChange E M).idelicNorm with hlam_def
  have hlam' : lam = ξ * normChar E M μ := rfl
  have hlam_class : IsIdeleClassChar (𝓞 M) M lam := fun u => by
    rw [hlam', MonoidHom.mul_apply, hξ.isIdeleClassChar u, isIdeleClassChar_normChar hμcl u, one_mul]
  have hlam_cont : Continuous lam := by
    show Continuous fun x => ξ x * normChar E M μ x
    exact hξ.continuous.mul (continuous_normChar hμc)
  have hlam_unit : IsUnitaryChar (𝓞 M) M lam := fun x => by
    show ‖((ξ x * normChar E M μ x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, norm_apply_eq_one hξ.isOfFinOrder, isUnitaryChar_normChar hμu x,
      one_mul]
  have hlam_adm : IsAdmissibleTwist M lam := ⟨hlam_class, hlam_cont, hlam_unit⟩
  have hlam_ne : ∃ x ∈ normOneIdeles M, lam x ≠ 1 :=
    LanglandsTunnell.exists_mem_normOneIdeles_mul_comp_idelicNorm_ne_one_of_finrank_eq_two E M h2 ξ hξ
      S₀ hunr hcusp μ hμc hμu

  let uR' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ :=
    fun w' hw' => uR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))
  let aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2 :=
    fun w' hw' => aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)) + a₀ w' hw'
  let uC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ := fun w' _ =>
    if h : (w'.comap (algebraMap E M)).IsReal then uR _ h else uC _ (not_isReal_iff_isComplex.mp h)
  let kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ := fun w' _ =>
    if h : (w'.comap (algebraMap E M)).IsReal then 0 else
      (if IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w'
          (uC _ (not_isReal_iff_isComplex.mp h)) (kC _ (not_isReal_iff_isComplex.mp h))
        then kC _ (not_isReal_iff_isComplex.mp h) else -kC _ (not_isReal_iff_isComplex.mp h))
  have hz0 : ∀ (w' : InfinitePlace M) (x : (w'.Completion)ˣ),
      extensionEmbedding w' (x : w'.Completion) / (‖(x : w'.Completion)‖ : ℂ) ≠ 0 := by
    intro w' x
    refine div_ne_zero ((map_ne_zero (extensionEmbedding w')).mpr x.ne_zero) ?_
    exact_mod_cast norm_ne_zero_iff.mpr x.ne_zero
  have hRM : ∀ w', ∀ hw' : w'.IsReal, IsArchCompAt M lam w' (uR' w' hw') ((aR' w' hw').val : ℤ) := by
    intro w' hw' x
    have hN := (LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange E M μ w'
      (uR' w' hw')).1 hw' _ (hR _ (hw'.comap (algebraMap E M))) x
    have hX := ha₀ w' hw' x
    rw [hlam_def, archLocalChar_mul, Units.val_mul, hX, hN, mul_zero, Complex.cpow_zero, one_mul,
      mul_comm, mul_assoc, ← zpow_add₀ (hz0 w' x)]
    congr 1
    apply sign_zpow_eq_of_even_sub hw'
    have hv : (((aR' w' hw').val : ℕ) : ℤ) =
        ((((aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val +
          (a₀ w' hw').val : ℕ) : ℤ)) % 2 := by
      simp only [aR']
      rw [ZMod.val_add]
      push_cast
      rfl
    refine ⟨((((aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val +
      (a₀ w' hw').val : ℕ) : ℤ)) / 2, ?_⟩
    rw [hv]
    push_cast
    omega
  have hCM : ∀ w', ∀ hw' : w'.IsComplex, IsArchCompAt M lam w' (uC' w' hw') (kC' w' hw') := by
    intro w' hw' x
    have hX := hξC w' hw' x
    by_cases h : (w'.comap (algebraMap E M)).IsReal
    · have hN := (LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange E M μ w'
        (uR _ h)).2.1 hw' h _ (hR _ h) x
      simp only [uC', kC', dif_pos h]
      rw [hlam_def, archLocalChar_mul, Units.val_mul, hX, hN, mul_zero, Complex.cpow_zero, one_mul,
        zpow_zero, one_mul, mul_one]
    · have hc : (w'.comap (algebraMap E M)).IsComplex := not_isReal_iff_isComplex.mp h
      have hN := (LanglandsTunnell.Converse.isArchCompAt_comp_idelicNorm_genuineBaseChange E M μ w'
        (uC _ hc)).2.2 hw' hc _ (hC _ hc)
      simp only [uC', kC', dif_neg h]
      rw [hlam_def, archLocalChar_mul, Units.val_mul, hX, mul_zero, Complex.cpow_zero, one_mul,
        zpow_zero, one_mul]
      by_cases hk : IsArchCompAt M (μ.comp (genuineBaseChange E M).idelicNorm) w' (uC _ hc) (kC _ hc)
      · rw [if_pos hk]
        exact hk x
      · rw [if_neg hk]
        exact (hN.resolve_left hk) x
  have huR' : ∀ w', ∀ hw' : w'.IsReal,
      uR' w' hw' = uR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)) := fun _ _ => rfl
  have haR' : ∀ w', ∀ hw' : w'.IsReal,
      ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
        (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val := by
    intro w' hw'
    have hsub : aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)) = a₀ w' hw' :=
      add_sub_cancel_left _ _
    rw [archLocalChar_neg_one_of_isArchCompAt (ha₀ w' hw'), zpow_natCast, hsub]
  have huC' : ∀ w', ∀ hw' : w'.IsComplex,
      uC' w' hw' = if h : (w'.comap (algebraMap E M)).IsReal then uR _ h
        else uC _ (InfinitePlace.not_isReal_iff_isComplex.mp h) := fun _ _ => rfl
  have hkC' : ∀ w', ∀ hw' : w'.IsComplex,
      (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs := by
    intro w' hw'
    by_cases h : (w'.comap (algebraMap E M)).IsReal
    · simp only [kC', dif_pos h, Int.natAbs_zero]
    · simp only [kC', dif_neg h]
      split_ifs <;> simp [Int.natAbs_neg]

  have hnice := LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum M lam hlam_adm hlam_ne uR' aR' uC' kC'
    hRM hCM
  obtain ⟨-, -, -, ΛM, ΛMd, hdM, -, hbM, -, hmM, hmMd, hfeM⟩ := hnice
  obtain ⟨hwf, hconv, harch, hL⟩ :=
    LanglandsTunnell.wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
      E M h2 ξ hξ S₀ hunr hsign (inducedTable E M ξ) S hS₀S hramS (inducedTable_clause h2 ξ S) μ
      ⟨hμcl, hμc, hμu⟩ uR aR uC kC hR hC uR' aR' uC' kC' huR' haR' huC' hkC'
  obtain ⟨hcond, hroot⟩ := hck μ ⟨hμcl, hμc, hμu⟩ hμS
  have hW := hroot aR kC aR' kC' haR' hkC' uR uC

  set D := twistedDatum E (inducedTable E M ξ) S (fun _ _ => RealArchParam.oddArtin)
    (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC with hD
  set H := heckeDatum M lam uR' aR' uC' kC' with hH
  have hDc : (D.center : ℂ) = 1 / 2 := by
    rw [hD]
    show (((1 : ℝ) / 2 : ℝ) : ℂ) = 1 / 2
    push_cast
    rfl
  have hDa : D.abscissa = 1 := by rw [hD]; rfl
  have hHc : (H.center : ℂ) = 1 / 2 := by
    rw [hH]
    show (((1 : ℝ) / 2 : ℝ) : ℂ) = 1 / 2
    push_cast
    rfl
  have hHa : H.abscissa = 1 := by rw [hH]; rfl

  have hNv0 : ∀ v : HeightOneSpectrum (𝓞 E), (Ideal.absNorm v.asIdeal) ≠ 0 :=
    fun v => by have := two_le_absNorm v; omega
  have hNw0 : ∀ w : HeightOneSpectrum (𝓞 M), (Ideal.absNorm w.asIdeal) ≠ 0 :=
    fun w => by have := two_le_absNorm w; omega
  let eul : HeightOneSpectrum (𝓞 M) → ℂ → ℂ := fun w s =>
    if IsUnramifiedCharAt lam w then
      1 - ((lam (uniformizerIdele M w) : ℂˣ) : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)
    else 1
  let eulD : HeightOneSpectrum (𝓞 M) → ℂ → ℂ := fun w s =>
    if IsUnramifiedCharAt lam w then
      1 - (((lam (uniformizerIdele M w))⁻¹ : ℂˣ) : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)
    else 1
  have heul : ∀ w s, (H.euler w).eval (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)) = eul w s := by
    intro w s
    simp only [hH, heckeDatum, eul]
    split_ifs <;> simp
  have heulD : ∀ w s, (H.dual w).eval (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)) = eulD w s := by
    intro w s
    simp only [hH, heckeDatum, eulD]
    split_ifs <;> simp
  let polyS : ℂ → ℂ := fun s => ∏ w ∈ WS E M S, eul w s
  let polySd : ℂ → ℂ := fun s => ∏ w ∈ WS E M S, eulD w s
  have hfin : ∀ g : HeightOneSpectrum (𝓞 M) → ℂ,
      (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then g w' else 1) =
        ∏ w ∈ WS E M S, g w := by
    intro g
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := WS E M S) ?_]
    · exact Finset.prod_congr rfl fun w hw => if_pos (mem_WS.mp hw)
    · intro w hw
      rw [Function.mem_mulSupport] at hw
      rw [Finset.mem_coe, mem_WS]
      by_contra h
      exact hw (if_neg h)
  have hFS : ∀ s : ℂ, (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
      ((H.euler w').eval (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) =
        ∏ w ∈ WS E M S, (eul w s)⁻¹ := fun s => by
    rw [hfin fun w' => ((H.euler w').eval (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹]
    exact Finset.prod_congr rfl fun w _ => by rw [heul]
  have hFSd : ∀ s : ℂ, (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
      ((H.dual w').eval (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) =
        ∏ w ∈ WS E M S, (eulD w s)⁻¹ := fun s => by
    rw [hfin fun w' => ((H.dual w').eval (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹]
    exact Finset.prod_congr rfl fun w _ => by rw [heulD]
  have hlamval : ∀ x, ‖((lam x : ℂˣ) : ℂ)‖ = 1 := fun x => hlam_unit x
  have hone_sub_ne : ∀ (z : ℂ) (q : ℕ) (s : ℂ), ‖z‖ = 1 → 2 ≤ q → s.re ≠ 0 →
      1 - z * ((q : ℂ)) ^ (-s) ≠ 0 := by
    intro z q s hz hq hs h0
    have h1 : z * (q : ℂ) ^ (-s) = 1 := by
      have := sub_eq_zero.mp h0
      exact this.symm
    have hn : ‖z * (q : ℂ) ^ (-s)‖ = (q : ℝ) ^ (-s.re) := by
      rw [norm_mul, hz, one_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    rw [h1, norm_one] at hn
    have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · have := Real.one_lt_rpow hq1 (by linarith : 0 < -s.re)
      linarith
    · have := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith : -s.re < 0)
      linarith
  have heul_ne : ∀ w s, s.re ≠ 0 → eul w s ≠ 0 := by
    intro w s hs
    simp only [eul]
    split_ifs
    · exact hone_sub_ne _ _ _ (hlamval _) (two_le_absNorm w) hs
    · exact one_ne_zero
  have heulD_ne : ∀ w s, s.re ≠ 0 → eulD w s ≠ 0 := by
    intro w s hs
    simp only [eulD]
    split_ifs
    · refine hone_sub_ne _ _ _ ?_ (two_le_absNorm w) hs
      rw [Units.val_inv_eq_inv_val, norm_inv, hlamval, inv_one]
    · exact one_ne_zero

  have hbdd_const : LDatum.BoundedOnStrips fun _ : ℂ => (1 : ℂ) := fun _ _ => ⟨1, fun _ _ _ => by simp⟩
  have hpoly_diff : Differentiable ℂ polyS := by
    refine differentiable_finset_prod _ _ fun w _ => ?_
    simp only [eul]
    split_ifs
    · exact (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_cpow_neg _ (by exact_mod_cast hNw0 w)))
    · exact differentiable_const _
  have hpolyd_diff : Differentiable ℂ polySd := by
    refine differentiable_finset_prod _ _ fun w _ => ?_
    simp only [eulD]
    split_ifs
    · exact (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_cpow_neg _ (by exact_mod_cast hNw0 w)))
    · exact differentiable_const _
  have hpolyd_diff' : Differentiable ℂ fun s => polySd (1 - s) :=
    hpolyd_diff.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hpoly_bdd : LDatum.BoundedOnStrips polyS := by
    refine boundedOnStrips_finset_prod _ _ fun w _ => ?_
    by_cases hu : IsUnramifiedCharAt lam w
    · have h := boundedOnStrips_one_sub ((lam (uniformizerIdele M w) : ℂˣ) : ℂ)
        (Ideal.absNorm w.asIdeal) (Nat.pos_of_ne_zero (hNw0 w)) (-1) 0
      convert h using 2 with s
      simp only [eul, if_pos hu]
      congr 2
      push_cast
      ring_nf
    · convert hbdd_const using 2 with s
      simp only [eul, if_neg hu]
  have hpolyd_bdd' : LDatum.BoundedOnStrips fun s => polySd (1 - s) := by
    show LDatum.BoundedOnStrips fun s => ∏ w ∈ WS E M S, eulD w (1 - s)
    refine boundedOnStrips_finset_prod _ _ fun w _ => ?_
    by_cases hu : IsUnramifiedCharAt lam w
    · have h := boundedOnStrips_one_sub (((lam (uniformizerIdele M w))⁻¹ : ℂˣ) : ℂ)
        (Ideal.absNorm w.asIdeal) (Nat.pos_of_ne_zero (hNw0 w)) 1 (-1)
      convert h using 2 with s
      simp only [eulD, if_pos hu]
      congr 2
      push_cast
      ring_nf
    · convert hbdd_const using 2 with s
      simp only [eulD, if_neg hu]

  have hlamS : ∀ w ∈ WS E M S, (IsUnramifiedCharAt lam w ↔ IsUnramifiedCharAt ξ w) ∧
      lam (uniformizerIdele M w) =
        ξ (uniformizerIdele M w) * μ (uniformizerIdele E (w.under (𝓞 E))) ^ fdeg E M w := by
    intro w hw
    have hv := mem_WS.mp hw
    have hμv : IsUnramifiedCharAt μ (w.under (𝓞 E)) := hμS _ hv
    have hNu : IsUnramifiedCharAt (normChar E M μ) w :=
      isUnramifiedCharAt_normChar (w.under (𝓞 E)) ⟨w, rfl⟩ hμv
    refine ⟨⟨fun h => ?_, fun h => isUnramifiedCharAt_mul h hNu⟩, ?_⟩
    · have : ξ = lam * (normChar E M μ)⁻¹ := (mul_inv_cancel_right ξ (normChar E M μ)).symm
      rw [this]
      exact isUnramifiedCharAt_mul h (isUnramifiedCharAt_inv hNu)
    · rw [hlam', MonoidHom.mul_apply, normChar_uniformizerIdele w hμv]
      rfl
  have hNw : ∀ w : HeightOneSpectrum (𝓞 M),
      Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 E)).asIdeal ^ fdeg E M w :=
    fun w => absNorm_eq_pow_inertiaDeg rfl
  have hqne : ∀ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
    fun v => by exact_mod_cast hNv0 v

  have hsPart : ∀ s : ℂ, sPart E S (Afam E M ξ S) μ s = polySd (1 - s) := by
    intro s
    have hx : ∀ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) ≠ 0 :=
      fun v => mul_ne_zero (Units.ne_zero _) (natCast_cpow_ne_zero (hNv0 v.1) _)
    unfold sPart Afam
    rw [tsum_coeffFamily S _ _ _ _ _ hx]
    have hRHS : polySd (1 - s) = ∏ w ∈ Wxi E M ξ S,
        (1 - (((lam (uniformizerIdele M w))⁻¹ : ℂˣ) : ℂ) *
          ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(1 - s))) := by
      show (∏ w ∈ WS E M S, eulD w (1 - s)) = _
      rw [Wxi, Finset.prod_filter]
      refine Finset.prod_congr rfl fun w hw => ?_
      simp only [eulD, (hlamS w hw).1]
    rw [hRHS, ← Finset.prod_coe_sort (Wxi E M ξ S)]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hwS : w.1 ∈ WS E M S := (Finset.mem_filter.mp w.2).1
    obtain ⟨-, hval⟩ := hlamS w.1 hwS
    simp only [vOfW, alphaCoef]
    rw [hval, hNw w.1, natCast_pow_cpow]
    set q : ℂ := ((Ideal.absNorm (w.1.under (𝓞 E)).asIdeal : ℕ) : ℂ) with hq
    set X : ℂ := ((μ (uniformizerIdele E (w.1.under (𝓞 E))) : ℂˣ) : ℂ) with hX
    set z : ℂ := ((ξ (uniformizerIdele M w.1) : ℂˣ) : ℂ) with hz
    have hq0 : q ≠ 0 := hqne _
    have hkey : q ^ (-(1 / 2 : ℂ)) * (q ^ ((1 : ℂ) / 2 - s))⁻¹ = q ^ (-(1 - s)) := by
      rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hq0]
      congr 1
      ring
    rw [zpow_neg, zpow_natCast]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, mul_pow, mul_inv]
    rw [← hkey, mul_pow, inv_pow]
    ring

  have hsPartDual : ∀ t : ℂ, sPartDual E S (Adfam E M ξ S c k) μ t =
      c * (∏ v : ↥S, (((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2)) ^ (k v)) * polyS (1 - t) := by
    intro t
    let y : ↥S → ℂ := fun v => (((μ (uniformizerIdele E v.1))⁻¹ : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - t)
    have hy : ∀ v, y v ≠ 0 :=
      fun v => mul_ne_zero (Units.ne_zero _) (natCast_cpow_ne_zero (hNv0 v.1) _)
    have hy_inv : ∀ v, (y v)⁻¹ = ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2) := by
      intro v
      simp only [y]
      rw [mul_inv, Units.val_inv_eq_inv_val, inv_inv, ← Complex.cpow_neg, neg_sub]

    let CF : (↥S → ℤ) → ℂ := coeffFamily S (Finset.univ : Finset ↥(Wxi E M ξ S)) (vOfW E M ξ S)
      (fun w => fdeg E M w.1) (fun w => betaCoef E M ξ w.1)
    have hLHS : sPartDual E S (Adfam E M ξ S c k) μ t =
        ∑' n : ↥S → ℤ, c * CF (n + k) * ∏ v : ↥S, y v ^ (n v) := rfl
    have hreindex : (∑' n : ↥S → ℤ, c * CF (n + k) * ∏ v : ↥S, y v ^ (n v)) =
        ∑' m : ↥S → ℤ, c * CF m * ∏ v : ↥S, y v ^ ((m - k) v) := by
      have := Equiv.tsum_eq (Equiv.addRight k)
        (fun m : ↥S → ℤ => c * CF m * ∏ v : ↥S, y v ^ ((m - k) v))
      rw [← this]
      refine tsum_congr fun n => ?_
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    have hsplit : ∀ m : ↥S → ℤ, c * CF m * ∏ v : ↥S, y v ^ ((m - k) v) =
        (c * ∏ v : ↥S, y v ^ (-(k v))) * (CF m * ∏ v : ↥S, y v ^ (m v)) := by
      intro m
      have : ∏ v : ↥S, y v ^ ((m - k) v) = (∏ v : ↥S, y v ^ (m v)) * ∏ v : ↥S, y v ^ (-(k v)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun v _ => ?_
        rw [Pi.sub_apply, sub_eq_add_neg, zpow_add₀ (hy v)]
      rw [this]
      ring
    rw [hLHS, hreindex, tsum_congr hsplit, tsum_mul_left]
    have hser : (∑' m : ↥S → ℤ, CF m * ∏ v : ↥S, y v ^ (m v)) =
        ∏ b : ↥(Wxi E M ξ S), (1 - betaCoef E M ξ b.1 * (y (vOfW E M ξ S b)) ^ (-(fdeg E M b.1 : ℤ))) :=
      tsum_coeffFamily S _ _ _ _ _ hy
    rw [hser]
    have hmono : (∏ v : ↥S, y v ^ (-(k v))) = ∏ v : ↥S, (((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2)) ^ (k v) := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [zpow_neg, ← inv_zpow, hy_inv]
    rw [hmono]
    have hRHS : polyS (1 - t) = ∏ w ∈ Wxi E M ξ S,
        (1 - ((lam (uniformizerIdele M w) : ℂˣ) : ℂ) *
          ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(1 - t))) := by
      show (∏ w ∈ WS E M S, eul w (1 - t)) = _
      rw [Wxi, Finset.prod_filter]
      refine Finset.prod_congr rfl fun w hw => ?_
      simp only [eul, (hlamS w hw).1]
    rw [hRHS, ← Finset.prod_coe_sort (Wxi E M ξ S)]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    have hwS : w.1 ∈ WS E M S := (Finset.mem_filter.mp w.2).1
    obtain ⟨-, hval⟩ := hlamS w.1 hwS
    simp only [vOfW, betaCoef]
    rw [hval, hNw w.1, natCast_pow_cpow, zpow_neg, ← inv_zpow, hy_inv, zpow_natCast]
    set q : ℂ := ((Ideal.absNorm (w.1.under (𝓞 E)).asIdeal : ℕ) : ℂ) with hq
    have hq0 : q ≠ 0 := hqne _
    have hkey : q ^ (-(1 / 2 : ℂ)) * q ^ (t - 1 / 2) = q ^ (-(1 - t)) := by
      rw [← Complex.cpow_add _ _ hq0]
      congr 1
      ring
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
    rw [← hkey, mul_pow]
    ring

  let Λ₀ : ℂ → ℂ := fun s => ΛM s * polyS s * polySd (1 - s)
  let Λ₀d : ℂ → ℂ := fun t => Λ₀ (1 - t)
  have hΛ₀ : Differentiable ℂ Λ₀ := (hdM.mul hpoly_diff).mul hpolyd_diff'
  have hbv : LDatum.BoundedOnStrips Λ₀ := boundedOnStrips_mul (boundedOnStrips_mul hbM hpoly_bdd) hpolyd_bdd'
  have hN : 0 < finiteConductor E μ S := by
    unfold finiteConductor
    refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => ?_
    split_ifs
    · exact one_pos
    · exact zpow_pos (by exact_mod_cast Nat.pos_of_ne_zero (hNv0 v)) _
  have hfe : ∀ s : ℂ, Λ₀ s = Λ₀d (2 * (D.center : ℂ) - s) := by
    intro s
    simp only [Λ₀d]
    rw [hDc]
    congr 1
    ring
  refine LanglandsTunnell.Converse.isNicePinned_of_entire_pair D _ _ _ _ hwf hconv hN ⟨2, ?_, ?_⟩
    Λ₀ Λ₀d hΛ₀ hbv hfe ?_ ?_
  · rw [hDa]
    norm_num
  · rw [hsPart]
    show (∏ w ∈ WS E M S, eulD w (1 - 2)) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun w _ => heulD_ne w _ (by norm_num)
  ·
    intro s hs
    rw [hDa] at hs
    have hs' : (1 : ℝ) < s.re := hs
    have hs0 : s.re ≠ 0 := by linarith
    have hs1 : (1 - s).re ≠ 0 := by simp; linarith
    show ΛM s * polyS s * polySd (1 - s) = sPart E S (Afam E M ξ S) μ s * D.archFactor s * D.LFun s
    rw [hmM s (by rw [hHa]; exact hs'), (harch s).1, (hL s hs').1, hFS s, hsPart s]
    have hcancel : (∏ w ∈ WS E M S, (eul w s)⁻¹) * polyS s = 1 := by
      show (∏ w ∈ WS E M S, (eul w s)⁻¹) * ∏ w ∈ WS E M S, eul w s = 1
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun w _ => inv_mul_cancel₀ (heul_ne w s hs0)
    calc (1 : ℂ) * D.archFactor s * ((∏ w ∈ WS E M S, (eul w s)⁻¹) * D.LFun s) * polyS s * polySd (1 - s)
        = D.archFactor s * D.LFun s * polySd (1 - s) * ((∏ w ∈ WS E M S, (eul w s)⁻¹) * polyS s) := by
          ring
      _ = polySd (1 - s) * D.archFactor s * D.LFun s := by rw [hcancel]; ring
  ·
    intro t ht
    rw [hDa] at ht
    have ht' : (1 : ℝ) < t.re := ht
    have ht0 : t.re ≠ 0 := by linarith
    show ΛM (1 - t) * polyS (1 - t) * polySd (1 - (1 - t)) =
      pinnedRootNumber E (inducedTable E M ξ) μ S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC *
        ((finiteConductor E μ S : ℝ) : ℂ) ^ (t - (D.center : ℂ)) *
        sPartDual E S (Adfam E M ξ S c k) μ t * D.archFactorDual t * D.LFunDual t
    rw [sub_sub_cancel, hfeM (1 - t)]
    have e1 : (H.center : ℂ) - (1 - t) = t - 1 / 2 := by rw [hHc]; ring
    have e2 : 2 * (H.center : ℂ) - (1 - t) = t := by rw [hHc]; ring
    rw [e1, e2, hmMd t (by rw [hHa]; exact ht'), (harch t).2, (hL t ht').2, hFSd t, hDc, hsPartDual t, hW]
    have hA : ((heckeConductor M lam : ℝ) : ℂ) ^ (t - 1 / 2) =
        ((finiteConductor E μ S : ℝ) : ℂ) ^ (t - 1 / 2) *
          ∏ v : ↥S, (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2)) ^ (k v) := by
      rw [hcond]
      have := ofReal_mul_prod_zpow_cpow (Finset.univ : Finset ↥S) (finiteConductor E μ S) hN
        (fun v => Ideal.absNorm v.1.asIdeal) (fun v => Nat.pos_of_ne_zero (hNv0 v.1)) k (t - 1 / 2)
      exact this
    rw [hA]
    have hcancel : (∏ w ∈ WS E M S, (eulD w t)⁻¹) * polySd t = 1 := by
      show (∏ w ∈ WS E M S, (eulD w t)⁻¹) * ∏ w ∈ WS E M S, eulD w t = 1
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun w _ => inv_mul_cancel₀ (heulD_ne w t ht0)
    have hP : (∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (k v)) *
        (∏ v : ↥S, (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2)) ^ (k v)) =
        ∏ v : ↥S, (((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2)) ^ (k v) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ => (mul_zpow _ _ _).symm
    set P1 := ∏ v : ↥S, ((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) ^ (k v)
    set P2 := ∏ v : ↥S, (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2)) ^ (k v)
    set P12 := ∏ v : ↥S, (((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) *
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (t - 1 / 2)) ^ (k v)
    set εE := pinnedRootNumber E (inducedTable E M ξ) μ S (fun _ _ => RealArchParam.oddArtin)
      (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC
    set NE := ((finiteConductor E μ S : ℝ) : ℂ) ^ (t - 1 / 2)
    set F := ∏ w ∈ WS E M S, (eulD w t)⁻¹
    calc c * P1 * εE * (NE * P2) * ((1 : ℂ) * D.archFactorDual t * (F * D.LFunDual t)) *
          polyS (1 - t) * polySd t
        = εE * NE * (c * (P1 * P2) * polyS (1 - t)) * D.archFactorDual t * D.LFunDual t *
            (F * polySd t) := by ring
      _ = εE * NE * (c * P12 * polyS (1 - t)) * D.archFactorDual t * D.LFunDual t := by
          rw [hP, hcancel, mul_one]

end Twist

end InducedNiceSol

open InducedNiceSol Polynomial M4aHerbrand.GenuineDescent NumberField.InfinitePlace NumberField.InfinitePlace.Completion in

open scoped Classical in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (T₀ : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E))) (A Ad : (↥S → ℤ) → ℂ),
      T₀ ⊆ S ∧
      (∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
        (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
          Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
          Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
        (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
          Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ))) ∧
      (∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C) ∧
      (∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0) ∧
      A ≠ 0 ∧
      (∀ μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ, IsAdmissibleTwist E μ →
        (∀ v ∈ S, ∀ t : (v.adicCompletion E)ˣ, Valued.v (t : v.adicCompletion E) = 1 →
          localChar μ v t = 1) →
        ∀ (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ)
          (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
          (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ)
          (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ),
          (∀ w, ∀ hw : w.IsReal, IsArchCompAt E μ w (uR w hw) ((aR w hw).val : ℤ)) →
          (∀ w, ∀ hw : w.IsComplex, IsArchCompAt E μ w (uC w hw) (kC w hw)) →
          IsNicePinned
            (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
              (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC)
            (sPart E S A μ) (sPartDual E S Ad μ)
            (pinnedRootNumber E Pi μ S (fun _ _ => RealArchParam.oddArtin)
              (fun _ _ => ComplexArchParam.trivialArtin) uR aR uC kC)
            (finiteConductor E μ S)) := by
  classical
  obtain ⟨R, hR⟩ := exists_finset_ramified (F := E) (E := M)
  set S : Finset (HeightOneSpectrum (𝓞 E)) := T₀ ∪ S₀.image (fun w => w.under (𝓞 E)) ∪ R with hS
  have hT₀S : T₀ ⊆ S := fun v hv => by simp [hS, hv]
  have hS₀S : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S := fun w' hw' =>
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw'))
  have hramS : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1 :=
    fun v hv w' hw' => hR v (fun h => hv (by simp [hS, h])) w' hw'
  obtain ⟨c, k, hck⟩ :=
    LanglandsTunnell.exists_heckeRootNumber_eq_mul_pinnedRootNumber_and_heckeConductor_eq_induced_of_finrank_eq_two
      E M h2 ξ hξ S₀ hunr hsign (inducedTable E M ξ) S hS₀S hramS (inducedTable_clause h2 ξ S)
  have hP0b := fun w' : InfinitePlace M =>
    LanglandsTunnell.Converse.exists_isArchCompAt_zero_of_isOfFinOrder M ξ hξ.continuous hξ.isOfFinOrder w'
  choose a₀ ha₀ using fun (w' : InfinitePlace M) (hw' : w'.IsReal) => (hP0b w').1 hw'
  have hξC : ∀ w' : InfinitePlace M, w'.IsComplex → IsArchCompAt M ξ w' 0 0 := fun w' hw' => (hP0b w').2 hw'
  refine ⟨inducedTable E M ξ, S, Afam E M ξ S, Adfam E M ξ S c k, hT₀S, inducedTable_clause h2 ξ S,
    Afam_bounded ξ S c k, Afam_support ξ S c k, Afam_ne_zero ξ S, ?_⟩
  intro μ hμ hμS uR aR uC kC hR hC
  exact isNicePinned_twist h2 ξ hξ S₀ hunr hsign hcusp S hS₀S hramS c k hck a₀ ha₀ hξC μ hμ
    (fun v hv => isUnramifiedCharAt_of_forall (hμS v hv)) uR aR uC kC hR hC

end S_LanglandsTunnell_exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two (solution)

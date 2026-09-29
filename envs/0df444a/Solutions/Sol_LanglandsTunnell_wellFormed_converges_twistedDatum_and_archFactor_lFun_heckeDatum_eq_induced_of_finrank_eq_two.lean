-- Prove2me | solution 1 for LanglandsTunnell.wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/be2bc617-69a1-56ab-9b7c-7e9a0746d53d

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
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_LanglandsTunnell_prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate
open scoped Pointwise

namespace ArtinFactorSol

section Quad

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finiteDimensional (h2 : Module.finrank F E = 2) : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ h2

theorem isGalois (h2 : Module.finrank F E = 2) : IsGalois F E := by
  haveI := finiteDimensional h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  infer_instance

theorem card_gal (h2 : Module.finrank F E = 2) :
    haveI := finiteDimensional h2
    Fintype.card (E ≃ₐ[F] E) = 2 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]

theorem exists_ne_one (h2 : Module.finrank F E = 2) : ∃ τ : E ≃ₐ[F] E, τ ≠ 1 := by
  haveI := finiteDimensional h2
  have h : 1 < Fintype.card (E ≃ₐ[F] E) := by rw [card_gal h2]; norm_num
  haveI := Fintype.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

theorem eq_one_or_eq (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    (σ : E ≃ₐ[F] E) : σ = 1 ∨ σ = τ := by
  classical
  haveI := finiteDimensional h2
  have hcard : (Finset.univ : Finset (E ≃ₐ[F] E)).card = 2 := by
    rw [Finset.card_univ, card_gal h2]
  obtain ⟨x, y, -, hxy⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ g : E ≃ₐ[F] E, g = x ∨ g = y := fun g => by
    have := Finset.mem_univ g
    rw [hxy, Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  rcases hmem 1 with h1 | h1 <;> rcases hmem τ with hτ' | hτ' <;> rcases hmem σ with hσ | hσ
  all_goals first
    | exact absurd (hτ'.trans h1.symm) hτ
    | exact Or.inl (hσ.trans h1.symm)
    | exact Or.inr (hσ.trans hτ'.symm)

theorem mul_self_eq_one (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1) :
    τ * τ = 1 := by
  rcases eq_one_or_eq h2 hτ (τ * τ) with h | h
  · exact h
  · exact absurd (mul_left_cancel (h.trans (mul_one τ).symm)) hτ

end Quad

section Fibre

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

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

theorem split_of_ne (h2 : Module.finrank F E = 2) {w' w'' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w'')
    (h : w'.under (𝓞 F) = w''.under (𝓞 F)) :
    (w'.under (𝓞 F)).asIdeal.ramificationIdx' w'.asIdeal = 1 ∧
      (w'.under (𝓞 F)).asIdeal.inertiaDeg' w'.asIdeal = 1 ∧
      (w'.under (𝓞 F)).asIdeal.inertiaDeg' w''.asIdeal = 1 := by
  classical
  obtain ⟨hle, hpos⟩ := sum_le_finrank (F := F) (v := w'.under (𝓞 F))
    ({w', w''} : Finset (HeightOneSpectrum (𝓞 E)))
    (by
      intro 𝔓 h𝔓
      simp only [Finset.mem_insert, Finset.mem_singleton] at h𝔓
      rcases h𝔓 with rfl | rfl
      · rfl
      · exact h.symm)
  rw [h2, Finset.sum_pair hne] at hle
  have a2 := hpos w' (by simp)
  have a3 := hpos w'' (by simp)
  have e1 : (w'.under (𝓞 F)).asIdeal.ramificationIdx' w'.asIdeal *
      (w'.under (𝓞 F)).asIdeal.inertiaDeg' w'.asIdeal = 1 := by omega
  have e2 : (w'.under (𝓞 F)).asIdeal.ramificationIdx' w''.asIdeal *
      (w'.under (𝓞 F)).asIdeal.inertiaDeg' w''.asIdeal = 1 := by omega
  exact ⟨Nat.eq_one_of_mul_eq_one_right e1, Nat.eq_one_of_mul_eq_one_left e1,
    Nat.eq_one_of_mul_eq_one_left e2⟩

attribute [local instance] Ideal.Quotient.field in

theorem inertia_eq_bot (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    {𝔓 : HeightOneSpectrum (𝓞 E)} (h : 𝔓.under (𝓞 F) = v) (he : v.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    haveI := finiteDimensional h2
    𝔓.asIdeal.inertia (E ≃ₐ[F] E) = ⊥ := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) F E
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
  haveI := 𝔓.isPrime.isMaximal 𝔓.ne_bot
  haveI := v.isPrime.isMaximal v.ne_bot
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal 𝔓.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal 𝔓.asIdeal (E ≃ₐ[F] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, he] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

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

end Fibre

section FibreMore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

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

omit [NumberField E] in

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 F) = v := by
  haveI := v.isPrime.isMaximal v.ne_bot
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    apply v.ne_bot
    rw [hQ.over, hQ0, Ideal.under_def, Ideal.comap_bot_of_injective]
    exact RingOfIntegers.algebraMap.injective F E
  refine ⟨⟨Q, hQmax.isPrime, hQne⟩, HeightOneSpectrum.ext ?_⟩
  rw [HeightOneSpectrum.under_asIdeal]
  exact hQ.over.symm

theorem dichotomy (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F))
    (hram : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → v.asIdeal.ramificationIdx' w.asIdeal = 1) :
    (∃ w' w'' : HeightOneSpectrum (𝓞 E), w' ≠ w'' ∧ w'.under (𝓞 F) = v ∧ w''.under (𝓞 F) = v) ∨
    (∃ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = v ∧ v.asIdeal.inertiaDeg' w'.asIdeal = 2 ∧
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = w') := by
  classical
  obtain ⟨w', hw'⟩ := exists_under_eq (E := E) v
  by_cases hsplit : ∃ w'' : HeightOneSpectrum (𝓞 E), w'' ≠ w' ∧ w''.under (𝓞 F) = v
  · obtain ⟨w'', hne, hw''⟩ := hsplit
    exact Or.inl ⟨w', w'', hne.symm, hw', hw''⟩
  · push Not at hsplit
    have hall : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = w' := fun w hw => by
      by_contra hne
      exact hsplit w hne hw
    right
    refine ⟨w', hw', ?_, hall⟩

    haveI := v.isPrime.isMaximal v.ne_bot
    have hsum := Ideal.sum_ramification_inertia (K := F) (L := E) (S := 𝓞 E) (p := v.asIdeal) v.ne_bot
    have hset : IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) = {w'.asIdeal} := by
      ext P
      rw [Finset.mem_singleton]
      constructor
      · intro hP
        obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).mp hP
        have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
        have hw : (⟨P, hPp, hPne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
          HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal]; exact hPl.over.symm)
        exact congrArg HeightOneSpectrum.asIdeal (hall _ hw)
      · rintro rfl
        haveI : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw', HeightOneSpectrum.under_asIdeal]⟩
        exact (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).mpr ⟨w'.isPrime, inferInstance⟩
    rw [hset, Finset.sum_singleton, h2, hram w' hw', one_mul] at hsum
    exact hsum

end FibreMore

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
  refine ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ht.le, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_⟩
  rw [Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]

theorem valuation_eq_one_of_mem {v : HeightOneSpectrum (𝓞 K)} (t : (v.adicCompletion K)ˣ)
    (h1 : (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (h2 : ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    Valued.v (t : v.adicCompletion K) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  have h0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)

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
  ·
    show ((genuineBaseChange E M).adelicNorm y).1 = (1 : InfiniteAdeleRing E)
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

theorem isUnramifiedCharAt_of_normChar [IsGalois E M] {χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ}
    (v : HeightOneSpectrum (𝓞 E)) (w : v.Extension (𝓞 M)) (hI : w.1.asIdeal.inertia (M ≃ₐ[E] M) = ⊥)
    (hψ : IsUnramifiedCharAt (normChar E M χ) w.1) : IsUnramifiedCharAt χ v := by
  intro u h1 h2
  have hu := valuation_eq_one_of_mem u h1 h2
  obtain ⟨y, hy1, hyN⟩ := IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_eq_of_inertia_eq_bot
    E M v w hI (u : v.adicCompletion E) hu
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hy1
    exact zero_ne_one hy1
  have hmem := mem_and_inv_mem_of_valuation_eq_one (Units.mk0 y hy0) hy1
  have h := hψ (Units.mk0 y hy0) hmem.1 hmem.2
  rw [localChar_apply, normChar_apply, idelicNorm_localUnit v w] at h
  have hunits : (Units.map (Algebra.norm (v.adicCompletion E) :
      w.1.adicCompletion M →* v.adicCompletion E) (Units.mk0 y hy0)) = u := Units.ext hyN
  rw [hunits] at h
  exact h

end NormChar

section EulerM

variable {M : Type} [Field M] [NumberField M]

open scoped Classical in

noncomputable def fac (p : HeightOneSpectrum (𝓞 M) → Prop) (C : HeightOneSpectrum (𝓞 M) → ℂ) (s : ℂ)
    (w : HeightOneSpectrum (𝓞 M)) : ℂ :=
  (if p w then 1 - C w * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) else 1)⁻¹

theorem norm_cpow_le_half (w : HeightOneSpectrum (𝓞 M)) {s : ℂ} (hs : 1 < s.re) :
    ‖((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 ∧
      ‖((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  have hq : 2 ≤ Ideal.absNorm w.asIdeal := two_le_absNorm w
  have hnorm : ‖((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  refine ⟨?_, hnorm⟩
  rw [hnorm]
  have hq2 : (2 : ℝ) ≤ Ideal.absNorm w.asIdeal := by exact_mod_cast hq
  calc ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-s.re) ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), Real.rpow_one, Real.rpow_one]
        exact inv_anti₀ (by norm_num) hq2
    _ = 1 / 2 := by rw [Real.rpow_neg (by norm_num), Real.rpow_one, one_div]

theorem fac_ne_zero_and_norm_sub_one_le (p : HeightOneSpectrum (𝓞 M) → Prop)
    (C : HeightOneSpectrum (𝓞 M) → ℂ) (hC : ∀ w, ‖C w‖ = 1) {s : ℂ} (hs : 1 < s.re)
    (w : HeightOneSpectrum (𝓞 M)) :
    fac p C s w ≠ 0 ∧ ‖fac p C s w - 1‖ ≤ 2 * ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  classical
  obtain ⟨hhalf, hnorm⟩ := norm_cpow_le_half w hs
  unfold fac
  by_cases hp : p w
  · rw [if_pos hp]
    set g : ℂ := C w * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) with hg
    have hgn : ‖g‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-s.re) := by rw [hg, norm_mul, hC, one_mul, hnorm]
    have hgle : ‖g‖ ≤ 1 / 2 := by rw [hg, norm_mul, hC, one_mul]; exact hhalf
    have h1g : 1 / 2 ≤ ‖1 - g‖ := by
      have := norm_sub_norm_le (1 : ℂ) g
      rw [norm_one] at this
      linarith
    have hne : 1 - g ≠ 0 := fun h => by rw [h, norm_zero] at h1g; linarith
    refine ⟨inv_ne_zero hne, ?_⟩
    have hrew : (1 - g)⁻¹ - 1 = g / (1 - g) := by field_simp; ring
    rw [hrew, norm_div, div_le_iff₀ (by linarith), ← hgn]
    nlinarith [norm_nonneg g]
  · rw [if_neg hp, inv_one, sub_self, norm_zero]
    exact ⟨one_ne_zero, by positivity⟩

theorem summable_norm_fac_sub_one (p : HeightOneSpectrum (𝓞 M) → Prop)
    (C : HeightOneSpectrum (𝓞 M) → ℂ) (hC : ∀ w, ‖C w‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun w => ‖fac p C s w - 1‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun w => (fac_ne_zero_and_norm_sub_one_le p C hC hs w).2)
    ((NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt M hs).mul_left 2)

theorem multipliable_fac_and_tprod_ne_zero (p : HeightOneSpectrum (𝓞 M) → Prop)
    (C : HeightOneSpectrum (𝓞 M) → ℂ) (hC : ∀ w, ‖C w‖ = 1) {s : ℂ} (hs : 1 < s.re)
    (T : Set (HeightOneSpectrum (𝓞 M))) :
    Multipliable (fun w : T => fac p C s w) ∧ ∏' w : T, fac p C s w ≠ 0 := by
  have hsum : Summable fun w : T => ‖fac p C s w.1 - 1‖ :=
    (summable_norm_fac_sub_one p C hC hs).subtype T
  have heq : (fun w : T => fac p C s w) = fun w : T => 1 + (fac p C s w.1 - 1) := by
    funext w; ring
  rw [heq]
  exact ⟨multipliable_one_add_of_summable hsum, tprod_one_add_ne_zero_of_summable
    (fun w => by rw [add_sub_cancel]; exact (fac_ne_zero_and_norm_sub_one_le p C hC hs w.1).1) hsum⟩

end EulerM

section Regroup

variable {E : Type} [Field E] [NumberField E] {M : Type} [Field M] [NumberField M] [Algebra E M]

theorem hasProd_fibre (S : Finset (HeightOneSpectrum (𝓞 E))) (f : HeightOneSpectrum (𝓞 M) → ℂ)
    (T : Set (HeightOneSpectrum (𝓞 M))) (hT : ∀ w, w ∈ T ↔ w.under (𝓞 E) ∈ S)
    [∀ v : HeightOneSpectrum (𝓞 E), Fintype (v.Extension (𝓞 M))]
    (hmul : Multipliable (fun w : (Tᶜ : Set (HeightOneSpectrum (𝓞 M))) => f w)) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S} => ∏ w : v.1.Extension (𝓞 M), f w.1)
      (∏' w : (Tᶜ : Set (HeightOneSpectrum (𝓞 M))), f w) := by
  let e : (Σ v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S}, v.1.Extension (𝓞 M)) ≃
      (Tᶜ : Set (HeightOneSpectrum (𝓞 M))) :=
    { toFun := fun p => ⟨p.2.1, fun h => p.1.2 (p.2.2 ▸ (hT _).mp h)⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 E), fun h => w.2 ((hT _).mpr h)⟩, ⟨w.1, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
        have hw' : w.under (𝓞 E) = v := hw
        subst hw'
        rfl
      right_inv := fun w => rfl }
  have hSig : HasProd ((fun w : (Tᶜ : Set (HeightOneSpectrum (𝓞 M))) => f w) ∘ e) (∏' w : (Tᶜ : Set _), f w) :=
    (e.hasProd_iff).mpr hmul.hasProd
  exact hSig.sigma (fun v => hasProd_fintype _)

omit [NumberField M] in

theorem tprod_coe_finset (W : Finset (HeightOneSpectrum (𝓞 M))) (f : HeightOneSpectrum (𝓞 M) → ℂ) :
    ∏' w : ((W : Set (HeightOneSpectrum (𝓞 M)))), f w = ∏ w ∈ W, f w :=
  Finset.tprod_subtype W f

end Regroup

section FibreEuler

variable {E : Type} [Field E] [NumberField E] {M : Type} [Field M] [NumberField M] [Algebra E M]

open Polynomial

theorem lam_above (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    {v : HeightOneSpectrum (𝓞 E)} (hvS₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v → w ∉ S₀)
    (hμv : IsUnramifiedCharAt μ v) (w : HeightOneSpectrum (𝓞 M)) (hw : w.under (𝓞 E) = v) :
    IsUnramifiedCharAt (ξ * normChar E M μ) w ∧
      (((ξ * normChar E M μ) (uniformizerIdele M w) : ℂˣ) : ℂ) =
        ((ξ (uniformizerIdele M w) : ℂˣ) : ℂ) *
          ((μ (uniformizerIdele E v) : ℂˣ) : ℂ) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
  have hμw : IsUnramifiedCharAt μ (w.under (𝓞 E)) := hw.symm ▸ hμv
  refine ⟨isUnramifiedCharAt_mul (hunr w (hvS₀ w hw)) ?_, ?_⟩
  · exact isUnramifiedCharAt_normChar (w.under (𝓞 E)) ⟨w, rfl⟩ hμw
  · rw [MonoidHom.mul_apply, normChar_uniformizerIdele w hμw, Units.val_mul, Units.val_pow_eq_pow_val]
    subst hw
    rfl

theorem lam_ramified_above (h2 : Module.finrank E M = 2) (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    {v : HeightOneSpectrum (𝓞 E)} (hvS₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v → w ∉ S₀)
    (hram : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v → v.asIdeal.ramificationIdx' w.asIdeal = 1)
    (hμv : ¬ IsUnramifiedCharAt μ v) (w : HeightOneSpectrum (𝓞 M)) (hw : w.under (𝓞 E) = v) :
    ¬ IsUnramifiedCharAt (ξ * normChar E M μ) w := by
  intro hlam
  haveI := finiteDimensional h2
  haveI := isGalois h2
  apply hμv
  have hN : IsUnramifiedCharAt (normChar E M μ) w := by
    have : normChar E M μ = ξ⁻¹ * (ξ * normChar E M μ) := (inv_mul_cancel_left ξ _).symm
    rw [this]
    exact isUnramifiedCharAt_mul (isUnramifiedCharAt_inv (hunr w (hvS₀ w hw))) hlam
  subst hw
  exact isUnramifiedCharAt_of_normChar (w.under (𝓞 E)) ⟨w, rfl⟩
    (inertia_eq_bot h2 rfl (hram w rfl)) hN

variable (h2 : Module.finrank E M = 2)
  (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
  (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
  (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
  (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
  (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
    v.asIdeal.ramificationIdx' w'.asIdeal = 1)
  (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
    (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
      Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
      Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
    (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
      Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
  (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ)

include h2 hram hPi in

theorem table_bounds (hfin : IsOfFinOrder ξ) (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ S) :
    ‖Pi.a v‖ ≤ 2 ∧ ‖Pi.b v‖ = 1 := by
  rcases dichotomy h2 v (hram v hv) with ⟨w', w'', hne, h', h''⟩ | ⟨w', h', hf2, -⟩
  · obtain ⟨ha, hb⟩ := (hPi v hv).1 w' w'' hne h' h''
    rw [ha, hb, norm_mul, norm_apply_eq_one hfin, norm_apply_eq_one hfin, mul_one]
    refine ⟨(norm_add_le _ _).trans ?_, rfl⟩
    rw [norm_apply_eq_one hfin, norm_apply_eq_one hfin]
    norm_num
  · obtain ⟨ha, hb⟩ := (hPi v hv).2 w' h' hf2
    rw [ha, hb, norm_zero, norm_neg, norm_apply_eq_one hfin]
    exact ⟨by norm_num, rfl⟩

include h2 hunr hS₀ hram hPi in
open scoped Classical in

theorem fibre_euler (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ S) (s : ℂ) [Fintype (v.Extension (𝓞 M))] :
    ∏ w : v.Extension (𝓞 M), fac (IsUnramifiedCharAt (ξ * normChar E M μ))
        (fun w => (((ξ * normChar E M μ) (uniformizerIdele M w) : ℂˣ) : ℂ)) s w.1 =
      ((if IsUnramifiedCharAt μ v
        then C 1 - C (((μ (uniformizerIdele E v) : ℂˣ) : ℂ) * Pi.a v) * X
          + C ((((μ (uniformizerIdele E v))^2 : ℂˣ) : ℂ) * Pi.b v) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  classical
  have hvS₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v → w ∉ S₀ :=
    fun w hw hwS => hv (hw ▸ hS₀ w hwS)
  by_cases hμv : IsUnramifiedCharAt μ v
  · rw [if_pos hμv]
    have hfac : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v →
        fac (IsUnramifiedCharAt (ξ * normChar E M μ))
          (fun w => (((ξ * normChar E M μ) (uniformizerIdele M w) : ℂˣ) : ℂ)) s w =
        (1 - ((ξ (uniformizerIdele M w) : ℂˣ) : ℂ) *
          ((μ (uniformizerIdele E v) : ℂˣ) : ℂ) ^ v.asIdeal.inertiaDeg' w.asIdeal *
          ((((Ideal.absNorm v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
      intro w hw
      obtain ⟨hu, hval⟩ := lam_above ξ μ S₀ hunr hvS₀ hμv w hw
      unfold fac
      rw [if_pos hu]
      dsimp only
      rw [hval, absNorm_eq_pow_inertiaDeg hw]
    rcases dichotomy h2 v (hram v hv) with ⟨w', w'', hne, h', h''⟩ | ⟨w', h', hf2, hall⟩
    · obtain ⟨hf', hf'', hallw⟩ := fibre_of_ne h2 hne h' h''
      let w₁ : v.Extension (𝓞 M) := ⟨w', h'⟩
      let w₂ : v.Extension (𝓞 M) := ⟨w'', h''⟩
      have hne' : w₁ ≠ w₂ := fun h => hne (congrArg Subtype.val h)
      have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁, w₂} := by
        ext w
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        rcases hallw w.1 w.2 with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      obtain ⟨ha, hb⟩ := (hPi v hv).1 w' w'' hne h' h''
      rw [show (∏ w : v.Extension (𝓞 M), _) = ∏ w ∈ ({w₁, w₂} : Finset _), _ from by rw [← huniv],
        Finset.prod_pair hne', hfac w' h', hfac w'' h'', hf', hf'', ha, hb, ← mul_inv]
      congr 1
      simp only [pow_one, Units.val_pow_eq_pow_val, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      ring
    · let w₁ : v.Extension (𝓞 M) := ⟨w', h'⟩
      have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁} := by
        ext w
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subtype.ext (hall w.1 w.2)
      obtain ⟨ha, hb⟩ := (hPi v hv).2 w' h' hf2
      have hx2 : ((((Ideal.absNorm v.asIdeal) ^ 2 : ℕ) : ℂ) ^ (-s)) =
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ 2 := by
        rw [sq, sq, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      rw [show (∏ w : v.Extension (𝓞 M), _) = ∏ w ∈ ({w₁} : Finset _), _ from by rw [← huniv],
        Finset.prod_singleton, hfac w' h', hf2, ha, hb, hx2]
      congr 1
      simp only [Units.val_pow_eq_pow_val, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      ring
  · rw [if_neg hμv, Polynomial.eval_C, inv_one]
    refine Finset.prod_eq_one fun w _ => ?_
    unfold fac
    rw [if_neg (lam_ramified_above h2 ξ μ S₀ hunr hvS₀ (hram v hv) hμv w.1 w.2), inv_one]

include h2 hunr hS₀ hram hPi in
open scoped Classical in

theorem fibre_euler_dual (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ S) (s : ℂ) [Fintype (v.Extension (𝓞 M))] :
    ∏ w : v.Extension (𝓞 M), fac (IsUnramifiedCharAt (ξ * normChar E M μ))
        (fun w => ((((ξ * normChar E M μ) (uniformizerIdele M w))⁻¹ : ℂˣ) : ℂ)) s w.1 =
      ((if IsUnramifiedCharAt μ v
        then C 1 - C ((((μ (uniformizerIdele E v))⁻¹ : ℂˣ) : ℂ) * (Pi.a v / Pi.b v)) * X
          + C ((((μ (uniformizerIdele E v))^(-2 : ℤ) : ℂˣ) : ℂ) * (Pi.b v)⁻¹) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  classical
  have hvS₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v → w ∉ S₀ :=
    fun w hw hwS => hv (hw ▸ hS₀ w hwS)
  by_cases hμv : IsUnramifiedCharAt μ v
  · rw [if_pos hμv]
    have hfac : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v →
        fac (IsUnramifiedCharAt (ξ * normChar E M μ))
          (fun w => ((((ξ * normChar E M μ) (uniformizerIdele M w))⁻¹ : ℂˣ) : ℂ)) s w =
        (1 - (((ξ (uniformizerIdele M w) : ℂˣ) : ℂ) *
          ((μ (uniformizerIdele E v) : ℂˣ) : ℂ) ^ v.asIdeal.inertiaDeg' w.asIdeal)⁻¹ *
          ((((Ideal.absNorm v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
      intro w hw
      obtain ⟨hu, hval⟩ := lam_above ξ μ S₀ hunr hvS₀ hμv w hw
      unfold fac
      rw [if_pos hu]
      dsimp only
      rw [Units.val_inv_eq_inv_val, hval, absNorm_eq_pow_inertiaDeg hw]
    have hξ0 : ∀ w : HeightOneSpectrum (𝓞 M), ((ξ (uniformizerIdele M w) : ℂˣ) : ℂ) ≠ 0 :=
      fun w => Units.ne_zero _
    have hμ0 : ((μ (uniformizerIdele E v) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hzpow : ((((μ (uniformizerIdele E v)) ^ (-2 : ℤ) : ℂˣ)) : ℂ) =
        ((((μ (uniformizerIdele E v)) : ℂˣ) : ℂ) ^ 2)⁻¹ := by
      rw [Units.val_zpow_eq_zpow_val, zpow_neg, zpow_ofNat]
    rcases dichotomy h2 v (hram v hv) with ⟨w', w'', hne, h', h''⟩ | ⟨w', h', hf2, hall⟩
    · obtain ⟨hf', hf'', hallw⟩ := fibre_of_ne h2 hne h' h''
      let w₁ : v.Extension (𝓞 M) := ⟨w', h'⟩
      let w₂ : v.Extension (𝓞 M) := ⟨w'', h''⟩
      have hne' : w₁ ≠ w₂ := fun h => hne (congrArg Subtype.val h)
      have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁, w₂} := by
        ext w
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        rcases hallw w.1 w.2 with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      obtain ⟨ha, hb⟩ := (hPi v hv).1 w' w'' hne h' h''
      rw [show (∏ w : v.Extension (𝓞 M), _) = ∏ w ∈ ({w₁, w₂} : Finset _), _ from by rw [← huniv],
        Finset.prod_pair hne', hfac w' h', hfac w'' h'', hf', hf'', ha, hb, ← mul_inv, hzpow,
        Units.val_inv_eq_inv_val]
      congr 1
      simp only [pow_one, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      have h1 := hξ0 w'
      have h2' := hξ0 w''
      field_simp
      ring
    · let w₁ : v.Extension (𝓞 M) := ⟨w', h'⟩
      have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁} := by
        ext w
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        exact Subtype.ext (hall w.1 w.2)
      obtain ⟨ha, hb⟩ := (hPi v hv).2 w' h' hf2
      have hx2 : ((((Ideal.absNorm v.asIdeal) ^ 2 : ℕ) : ℂ) ^ (-s)) =
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ 2 := by
        rw [sq, sq, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
      rw [show (∏ w : v.Extension (𝓞 M), _) = ∏ w ∈ ({w₁} : Finset _), _ from by rw [← huniv],
        Finset.prod_singleton, hfac w' h', hf2, ha, hb, hx2, hzpow, Units.val_inv_eq_inv_val]
      congr 1
      simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      have h1 := hξ0 w'
      field_simp
      ring
  · rw [if_neg hμv, Polynomial.eval_C, inv_one]
    refine Finset.prod_eq_one fun w _ => ?_
    unfold fac
    rw [if_neg (lam_ramified_above h2 ξ μ S₀ hunr hvS₀ (hram v hv) hμv w.1 w.2), inv_one]

include h2 hram hPi in
open scoped Classical in

theorem norm_eval_sub_one_le (hfin : IsOfFinOrder ξ) (huμ : IsUnitaryChar (𝓞 E) E μ)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v ∉ S) {s : ℂ} (hs : 1 < s.re) :
    ‖(if IsUnramifiedCharAt μ v
        then C 1 - C (((μ (uniformizerIdele E v) : ℂˣ) : ℂ) * Pi.a v) * X
          + C ((((μ (uniformizerIdele E v))^2 : ℂˣ) : ℂ) * Pi.b v) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) - 1‖ ≤
      3 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) ∧
    ‖(if IsUnramifiedCharAt μ v
        then C 1 - C ((((μ (uniformizerIdele E v))⁻¹ : ℂˣ) : ℂ) * (Pi.a v / Pi.b v)) * X
          + C ((((μ (uniformizerIdele E v))^(-2 : ℤ) : ℂˣ) : ℂ) * (Pi.b v)⁻¹) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) - 1‖ ≤
      3 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  obtain ⟨hhalf, hnorm⟩ := norm_cpow_le_half v hs
  set x : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) with hx
  have hx1 : ‖x‖ ≤ 1 := hhalf.trans (by norm_num)
  obtain ⟨ha, hb⟩ := table_bounds h2 ξ Pi S hram hPi hfin v hv
  have hμ1 : ‖((μ (uniformizerIdele E v) : ℂˣ) : ℂ)‖ = 1 := huμ _
  have hbound : ∀ (c₁ c₂ : ℂ), ‖c₁‖ ≤ 2 → ‖c₂‖ ≤ 1 → ‖-(c₁ * x) + c₂ * x ^ 2‖ ≤ 3 * ‖x‖ := by
    intro c₁ c₂ h1 h2'
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_mul, norm_pow]
    have hxn := norm_nonneg x
    nlinarith [mul_le_mul h1 le_rfl hxn (by norm_num : (0:ℝ) ≤ 2),
      mul_le_mul h2' (show ‖x‖ ^ 2 ≤ ‖x‖ by nlinarith) (by positivity) (by norm_num : (0:ℝ) ≤ 1)]
  constructor
  · split_ifs
    · simp only [Units.val_pow_eq_pow_val, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      rw [show (1 : ℂ) - _ * x + _ * x ^ 2 - 1 = -((((μ (uniformizerIdele E v) : ℂˣ) : ℂ) * Pi.a v) * x)
        + (((μ (uniformizerIdele E v) : ℂˣ) : ℂ) ^ 2 * Pi.b v) * x ^ 2 by ring, ← hnorm]
      refine hbound _ _ ?_ ?_
      · rw [norm_mul, hμ1, one_mul]; exact ha
      · rw [norm_mul, norm_pow, hμ1, one_pow, one_mul, hb]
    · simp only [Polynomial.eval_C, sub_self, norm_zero]
      positivity
  · split_ifs
    · simp only [Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
      rw [show (1 : ℂ) - _ * x + _ * x ^ 2 - 1 =
        -(((((μ (uniformizerIdele E v))⁻¹ : ℂˣ) : ℂ) * (Pi.a v / Pi.b v)) * x)
        + ((((μ (uniformizerIdele E v)) ^ (-2 : ℤ) : ℂˣ) : ℂ) * (Pi.b v)⁻¹) * x ^ 2 by ring, ← hnorm]
      refine hbound _ _ ?_ ?_
      · rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, hμ1, inv_one, one_mul, norm_div, hb, div_one]
        exact ha
      · rw [norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, hμ1, one_zpow, one_mul, norm_inv, hb, inv_one]
    · simp only [Polynomial.eval_C, sub_self, norm_zero]
      positivity

end FibreEuler

section ArchBook

variable {K : Type} [Field K] [NumberField K]

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Complex

theorem archLocalChar_mul (χ ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : InfinitePlace K)
    (x : (w.Completion)ˣ) : archLocalChar (χ * ψ) w x = archLocalChar χ w x * archLocalChar ψ w x := rfl

omit [NumberField K] in

theorem exists_unit_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (t : ℝ) :
    ∃ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = Real.exp t ∧
      extensionEmbedding w (x : w.Completion) = (Real.exp t : ℂ) := by
  set y : w.Completion := (ringEquivRealOfIsReal hw).symm (Real.exp t) with hy
  have hey : extensionEmbeddingOfIsReal hw y = Real.exp t := by
    rw [← ringEquivRealOfIsReal_apply, hy, RingEquiv.apply_symm_apply]
  have hey' : extensionEmbedding w y = (Real.exp t : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hw, hey]
  have hnorm : ‖y‖ = Real.exp t := by
    have := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y
    rw [← this, hey', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact (Real.exp_pos t).ne' hnorm.symm
  exact ⟨Units.mk0 y hy0, hnorm, hey'⟩

omit [NumberField K] in

theorem exists_unit_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (t : ℝ) :
    ∃ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = Real.exp t ∧
      extensionEmbedding w (x : w.Completion) = (Real.exp t : ℂ) := by
  set y : w.Completion := (ringEquivComplexOfIsComplex hw).symm (Real.exp t) with hy
  have hey : extensionEmbedding w y = (Real.exp t : ℂ) := by
    rw [← ringEquivComplexOfIsComplex_apply hw, hy, RingEquiv.apply_symm_apply]
  have hnorm : ‖y‖ = Real.exp t := by
    have := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y
    rw [← this, hey, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact (Real.exp_pos t).ne' hnorm.symm
  exact ⟨Units.mk0 y hy0, hnorm, hey⟩

theorem re_eq_zero_of_isArchCompAt {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (huμ : IsUnitaryChar (𝓞 K) K μ)
    {w : InfinitePlace K} {u : ℂ} {a : ℤ} (h : IsArchCompAt K μ w u a) : u.re = 0 := by
  obtain ⟨x, hxn, hxe⟩ : ∃ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = Real.exp 1 ∧
      extensionEmbedding w (x : w.Completion) = (Real.exp 1 : ℂ) := by
    rcases isReal_or_isComplex w with hw | hw
    · exact exists_unit_of_isReal hw 1
    · exact exists_unit_of_isComplex hw 1
  have h1 : ‖((archLocalChar μ w x : ℂˣ) : ℂ)‖ = 1 := huμ _
  rw [h x, hxn, hxe, div_self (by exact_mod_cast (Real.exp_pos 1).ne'), one_zpow, mul_one,
    Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le), Complex.norm_exp,
    Real.exp_eq_one_iff] at h1
  have hm : (w.mult : ℝ) ≠ 0 := mult_coe_ne_zero
  simp only [Complex.ofReal_one, one_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at h1
  rcases mul_eq_zero.mp h1 with h' | h'
  · exact absurd h' hm
  · exact h'

theorem signShift_re_nonneg (b : ZMod 2) : 0 ≤ (signShift b).re ∧ (signShift b).re ≤ 1 := by
  unfold signShift
  split_ifs <;> simp

theorem prod_map_sum_singleton {ι : Type} (T : Finset ι) (x : ι → ℂ) (g : ℂ → ℂ) :
    ((∑ i ∈ T, ({x i} : Multiset ℂ)).map g).prod = ∏ i ∈ T, g (x i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add,
      Multiset.prod_add, ih, Multiset.map_singleton, Multiset.prod_singleton]

theorem prod_map_sum_pair {ι : Type} (T : Finset ι) (x y : ι → ℂ) (g : ℂ → ℂ) :
    ((∑ i ∈ T, ({x i, y i} : Multiset ℂ)).map g).prod = ∏ i ∈ T, g (x i) * g (y i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add,
      Multiset.prod_add, ih, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.map_singleton, Multiset.prod_singleton]

theorem mem_sum_iff {ι : Type} (T : Finset ι) (F : ι → Multiset ℂ) (z : ℂ) :
    z ∈ ∑ i ∈ T, F i ↔ ∃ i ∈ T, z ∈ F i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    rw [Finset.sum_insert hi, Multiset.mem_add, ih]
    simp [Finset.mem_insert, or_and_right, exists_or]

end ArchBook

end ArtinFactorSol

namespace ArtinFactorSol

open Polynomial M4aHerbrand.GenuineDescent NumberField.InfinitePlace NumberField.InfinitePlace.Completion Complex

open scoped Classical in

theorem wf_part
    (E : Type) [Field E] [NumberField E]
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμu : IsUnitaryChar (𝓞 E) E μ)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt E μ w (uR w hw) ((aR w hw).val : ℤ))
    (hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt E μ w (uC w hw) (kC w hw)) :
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).WellFormed := by
  classical
  set D := twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
    (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC with hD
  have hDa : D.abscissa = 1 := by rw [hD]; rfl
  have hshiftR : ∀ (u : ℂ) (b : ZMod 2), u.re = 0 →
      -(u + signShift b).re ≤ 1 ∧ -(-u + signShift b).re ≤ 1 := by
    intro u b hu
    obtain ⟨h0, -⟩ := signShift_re_nonneg b
    simp only [Complex.add_re, Complex.neg_re, hu, neg_zero, zero_add]
    constructor <;> linarith
  have hshiftC : ∀ (u : ℂ) (n : ℕ), u.re = 0 →
      -(u + (n : ℂ) / 2).re ≤ 1 ∧ -(-u + (n : ℂ) / 2).re ≤ 1 := by
    intro u n hu
    have hn : ((n : ℂ) / 2).re = (n : ℝ) / 2 := by simp
    simp only [Complex.add_re, Complex.neg_re, hu, neg_zero, zero_add, hn]
    constructor <;> linarith [(by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)]
  have hReU : ∀ w (hw : w.IsReal), (uR w hw).re = 0 := fun w hw => re_eq_zero_of_isArchCompAt hμu (hR w hw)
  have hReC : ∀ w (hw : w.IsComplex), (uC w hw).re = 0 := fun w hw => re_eq_zero_of_isArchCompAt hμu (hC w hw)
  have hdeg : ∀ (x y : ℂ), (C 1 - C x * X + C y * X ^ 2 : ℂ[X]).coeff 0 = 1 ∧
      (C 1 - C x * X + C y * X ^ 2 : ℂ[X]).natDegree ≤ 2 := by
    intro x y
    refine ⟨by simp, ?_⟩
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans (by norm_num))
    · exact Polynomial.natDegree_C_mul_X_pow_le _ _
  refine ⟨fun i => two_le_absNorm i.1, fun i => ?_, ?_, ?_, ?_, ?_⟩
  · show ((if _ then _ else _ : ℂ[X]).coeff 0 = 1 ∧ (if _ then _ else _ : ℂ[X]).natDegree ≤ 2 ∧
      (if _ then _ else _ : ℂ[X]).coeff 0 = 1 ∧ (if _ then _ else _ : ℂ[X]).natDegree ≤ 2)
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals split_ifs
    all_goals first | exact (hdeg _ _).1 | exact (hdeg _ _).2 | simp
  · intro z hz
    rw [hDa]
    simp only [hD, twistedDatum, twistedGammaR, RealArchParam.oddArtin, RealArchParam.twist,
      RealArchParam.gammaR, zero_add] at hz
    obtain ⟨w, -, hz⟩ := (mem_sum_iff _ _ _).mp hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> exact (hshiftR _ _ (hReU w.1 w.2)).1
  · intro z hz
    rw [hDa]
    simp only [hD, twistedDatum, twistedGammaC, RealArchParam.oddArtin, RealArchParam.twist,
      RealArchParam.gammaC, ComplexArchParam.trivialArtin, ComplexArchParam.twist,
      ComplexArchParam.gammaC, zero_add, Finset.sum_const_zero] at hz
    obtain ⟨w, -, hz⟩ := (mem_sum_iff _ _ _).mp hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> exact (hshiftC _ _ (hReC w.1 w.2)).1
  · intro z hz
    rw [hDa]
    simp only [hD, twistedDatum, twistedGammaR, RealArchParam.oddArtin, RealArchParam.twist,
      RealArchParam.gammaR, RealArchParam.dual, zero_add, neg_zero] at hz
    obtain ⟨w, -, hz⟩ := (mem_sum_iff _ _ _).mp hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> exact (hshiftR _ _ (hReU w.1 w.2)).2
  · intro z hz
    rw [hDa]
    simp only [hD, twistedDatum, twistedGammaC, RealArchParam.oddArtin, RealArchParam.twist,
      RealArchParam.gammaC, RealArchParam.dual, ComplexArchParam.trivialArtin, ComplexArchParam.twist,
      ComplexArchParam.gammaC, ComplexArchParam.dual, zero_add, neg_zero, Finset.sum_const_zero,
      Int.natAbs_neg] at hz
    obtain ⟨w, -, hz⟩ := (mem_sum_iff _ _ _).mp hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> exact (hshiftC _ _ (hReC w.1 w.2)).2

open scoped Classical in

theorem arch_part
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (uR' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ) (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (uC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ) (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ)
    (huR' : ∀ w', ∀ hw' : w'.IsReal,
      uR' w' hw' = uR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    (haR' : ∀ w', ∀ hw' : w'.IsReal,
      ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
        (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val)
    (huC' : ∀ w', ∀ hw' : w'.IsComplex,
      uC' w' hw' = if h : (w'.comap (algebraMap E M)).IsReal then uR _ h
        else uC _ (InfinitePlace.not_isReal_iff_isComplex.mp h))
    (hkC' : ∀ w', ∀ hw' : w'.IsComplex,
      (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) :
    ∀ s : ℂ,
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactor s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactor s ∧
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactorDual s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactorDual s := by
  classical
  intro s
  have hparity : ∀ (w₁ w₂ : InfinitePlace M) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal), w₁ ≠ w₂ →
      w₁.comap (algebraMap E M) = w₂.comap (algebraMap E M) →
      (aR' w₁ h₁ - aR (w₁.comap (algebraMap E M)) (h₁.comap (algebraMap E M))) +
        (aR' w₂ h₂ - aR (w₂.comap (algebraMap E M)) (h₂.comap (algebraMap E M))) = 1 := by
    intro w₁ w₂ h₁ h₂ hne hcomap
    have hprod := hsign w₁ w₂ hne h₁ h₂ hcomap
    rw [haR' w₁ h₁, haR' w₂ h₂] at hprod
    have keyZ : ∀ d₁ d₂ : ZMod 2, ((-1 : ℂ) ^ d₁.val) * (-1) ^ d₂.val = -1 → d₁ + d₂ = 1 := by
      intro d₁ d₂ h
      have hv : ∀ d : ZMod 2, d.val = 0 ∨ d.val = 1 := fun d => by have := ZMod.val_lt d; omega
      have hd : ∀ d : ZMod 2, d = (d.val : ZMod 2) := fun d => (ZMod.natCast_zmod_val d).symm
      rcases hv d₁ with e₁ | e₁ <;> rcases hv d₂ with e₂ | e₂ <;> rw [e₁, e₂] at h <;>
        norm_num at h <;> (rw [hd d₁, hd d₂, e₁, e₂]; decide)
    exact keyZ _ _ hprod
  have hP := LanglandsTunnell.prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two E M h2
    uR aR uC kC uR' aR' uC' kC'
    (fun w' hw' => aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    hparity huR' (fun w' hw' => by simp) huC' hkC' s
  have hPd := LanglandsTunnell.prod_gammaR_mul_prod_gammaC_infinitePlace_induced_eq_of_finrank_eq_two E M h2
    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) kC
    (fun w' hw' => -uR' w' hw') aR' (fun w' hw' => -uC' w' hw') kC'
    (fun w' hw' => aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    hparity (fun w' hw' => by simp only [huR']) (fun w' hw' => by simp)
    (fun w' hw' => by simp only [huC']; split_ifs <;> rfl) hkC' s
  simp only [LDatum.archFactor, LDatum.archFactorDual, heckeDatum, twistedDatum, twistedGammaR,
    twistedGammaC, RealArchParam.oddArtin, RealArchParam.twist, RealArchParam.gammaR,
    RealArchParam.gammaC, RealArchParam.dual, ComplexArchParam.trivialArtin, ComplexArchParam.twist,
    ComplexArchParam.gammaC, ComplexArchParam.dual, zero_add, neg_zero, Finset.sum_const_zero,
    Int.natAbs_neg]
  rw [prod_map_sum_singleton, prod_map_sum_singleton, prod_map_sum_pair, prod_map_sum_pair,
    prod_map_sum_singleton, prod_map_sum_singleton, prod_map_sum_pair, prod_map_sum_pair]
  refine ⟨hP.trans ?_, hPd.trans ?_⟩ <;>
  · congr 1
    exact Finset.prod_congr rfl fun w _ => sq _

open scoped Classical in

theorem finite_part
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμu : IsUnitaryChar (𝓞 E) E μ)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (uR' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ) (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (uC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ) (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ) :
    (∀ s : ℂ, 1 < s.re →
      ((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFun s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').euler w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFun s ∧
       (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFun s ≠ 0) ∧
      ((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFunDual s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').dual w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFunDual s ∧
       (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFunDual s ≠ 0)) ∧
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).Converges := by
  classical
  haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype (v.Extension (𝓞 M)) :=
    fun v => HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
  set lam : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ := ξ * μ.comp (genuineBaseChange E M).idelicNorm with hlam_def
  have hlam' : lam = ξ * normChar E M μ := rfl
  have hlam_unit : ∀ x, ‖((lam x : ℂˣ) : ℂ)‖ = 1 := fun x => by
    show ‖((ξ x * normChar E M μ x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, norm_apply_eq_one hξ.isOfFinOrder, isUnitaryChar_normChar hμu x, one_mul]
  set D := twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
    (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC with hD
  set H := heckeDatum M lam uR' aR' uC' kC' with hH
  have hDa : D.abscissa = 1 := by rw [hD]; rfl

  let p : HeightOneSpectrum (𝓞 M) → Prop := fun w => IsUnramifiedCharAt lam w
  let CP : HeightOneSpectrum (𝓞 M) → ℂ := fun w => ((lam (uniformizerIdele M w) : ℂˣ) : ℂ)
  let CD : HeightOneSpectrum (𝓞 M) → ℂ := fun w => (((lam (uniformizerIdele M w))⁻¹ : ℂˣ) : ℂ)
  have hCP : ∀ w, ‖CP w‖ = 1 := fun w => hlam_unit _
  have hCD : ∀ w, ‖CD w‖ = 1 := fun w => by
    simp only [CD]; rw [Units.val_inv_eq_inv_val, norm_inv, hlam_unit, inv_one]
  let WS : Finset (HeightOneSpectrum (𝓞 M)) := (finite_setOf_under_mem (F := E) (E := M) S).toFinset
  let T : Set (HeightOneSpectrum (𝓞 M)) := (WS : Set (HeightOneSpectrum (𝓞 M)))
  have hWS : ∀ w, w ∈ WS ↔ w.under (𝓞 E) ∈ S := fun w => by simp [WS]
  have hT : ∀ w, w ∈ T ↔ w.under (𝓞 E) ∈ S := fun w => by rw [← hWS]; simp [T]

  have hHeul : ∀ (s : ℂ) w, ((H.euler w).eval (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ = fac p CP s w := by
    intro s w
    simp only [hH, heckeDatum, fac, p, CP]
    split_ifs <;> simp
  have hHdual : ∀ (s : ℂ) w, ((H.dual w).eval (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ = fac p CD s w := by
    intro s w
    simp only [hH, heckeDatum, fac, p, CD]
    split_ifs <;> simp
  have hfinprod : ∀ (g : HeightOneSpectrum (𝓞 M) → ℂ) (s : ℂ) (C : HeightOneSpectrum (𝓞 M) → ℂ),
      (∀ w, (g w)⁻¹ = fac p C s w) →
      (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then (g w')⁻¹ else 1) =
        ∏ w ∈ WS, fac p C s w := by
    intro g s C hg
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := WS) ?_]
    · exact Finset.prod_congr rfl fun w hw => by rw [if_pos ((hWS w).mp hw), hg]
    · intro w hw
      rw [Function.mem_mulSupport] at hw
      rw [Finset.mem_coe, hWS]
      by_contra h
      exact hw (if_neg h)

  have key : ∀ (s : ℂ), 1 < s.re → ∀ (C : HeightOneSpectrum (𝓞 M) → ℂ), (∀ w, ‖C w‖ = 1) →
      ∀ (fE : {v : HeightOneSpectrum (𝓞 E) // v ∉ S} → ℂ),
      (∀ v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S}, ∏ w : v.1.Extension (𝓞 M), fac p C s w.1 = fE v) →
      (∏' w, fac p C s w) = (∏ w ∈ WS, fac p C s w) * ∏' v, fE v ∧ ∏' v, fE v ≠ 0 := by
    intro s hs C hC fE hfE
    obtain ⟨hmulT, -⟩ := multipliable_fac_and_tprod_ne_zero p C hC hs T
    obtain ⟨hmulTc, hneTc⟩ := multipliable_fac_and_tprod_ne_zero p C hC hs Tᶜ
    have hsplit := Multipliable.tprod_mul_tprod_compl (f := fac p C s) hmulT hmulTc
    have hfin : ∏' w : T, fac p C s w = ∏ w ∈ WS, fac p C s w := tprod_coe_finset WS _
    have hfib : HasProd (fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S} =>
        ∏ w : v.1.Extension (𝓞 M), fac p C s w.1) (∏' w : (Tᶜ : Set _), fac p C s w) :=
      hasProd_fibre S _ T hT hmulTc
    have hfib' : HasProd fE (∏' w : (Tᶜ : Set _), fac p C s w) := by
      convert hfib using 1
      funext v
      exact (hfE v).symm
    rw [← hsplit, hfin, hfib'.tprod_eq]
    exact ⟨rfl, hneTc⟩
  have hL : ∀ s : ℂ, 1 < s.re →
      (H.LFun s = (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
        ((H.euler w').eval (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) * D.LFun s ∧ D.LFun s ≠ 0) ∧
      (H.LFunDual s = (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
        ((H.dual w').eval (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) * D.LFunDual s ∧
        D.LFunDual s ≠ 0) := by
    intro s hs
    have hHL : H.LFun s = ∏' w, fac p CP s w := tprod_congr fun w => hHeul s w
    have hHLd : H.LFunDual s = ∏' w, fac p CD s w := tprod_congr fun w => hHdual s w
    have hDL : D.LFun s = ∏' v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S},
        ((if IsUnramifiedCharAt μ v.1
          then C 1 - C (((μ (uniformizerIdele E v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
            + C ((((μ (uniformizerIdele E v.1))^2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
      rw [hD]; rfl
    have hDLd : D.LFunDual s = ∏' v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S},
        ((if IsUnramifiedCharAt μ v.1
          then C 1 - C ((((μ (uniformizerIdele E v.1))⁻¹ : ℂˣ) : ℂ) * (Pi.a v.1 / Pi.b v.1)) * X
            + C ((((μ (uniformizerIdele E v.1))^(-2 : ℤ) : ℂˣ) : ℂ) * (Pi.b v.1)⁻¹) * X ^ 2
          else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
      rw [hD]; rfl
    obtain ⟨hk, hkne⟩ := key s hs CP hCP _ (fun v => fibre_euler h2 ξ S₀ hunr Pi S hS₀ hram hPi μ v.1 v.2 s)
    obtain ⟨hkd, hkdne⟩ := key s hs CD hCD _ (fun v => fibre_euler_dual h2 ξ S₀ hunr Pi S hS₀ hram hPi μ v.1 v.2 s)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hHL, hfinprod _ s CP (hHeul s), hDL, hk]
    · rw [hDL]; exact hkne
    · rw [hHLd, hfinprod _ s CD (hHdual s), hDLd, hkd]
    · rw [hDLd]; exact hkdne
  have hconv : D.Converges := by
    intro s hs
    rw [hDa] at hs
    have hsumE : Summable fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S} =>
        3 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
      ((NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt E hs).subtype _).mul_left 3
    refine ⟨?_, ?_, ((hL s hs).1).2, ((hL s hs).2).2⟩
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) hsumE
      exact (norm_eval_sub_one_le h2 ξ Pi S hram hPi μ hξ.isOfFinOrder hμu v.1 v.2 hs).1
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => ?_) hsumE
      exact (norm_eval_sub_one_le h2 ξ Pi S hram hPi μ hξ.isOfFinOrder hμu v.1 v.2 hs).2
  exact ⟨hL, hconv⟩

end ArtinFactorSol

open ArtinFactorSol Polynomial M4aHerbrand.GenuineDescent NumberField.InfinitePlace NumberField.InfinitePlace.Completion Complex in

open scoped Classical in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS₀ : ∀ w' ∈ S₀, w'.under (𝓞 E) ∈ S)
    (hram : ∀ v ∉ S, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v →
      v.asIdeal.ramificationIdx' w'.asIdeal = 1)
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (μ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist E μ)
    (uR : ∀ w : InfinitePlace E, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace E, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace E, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace E, w.IsComplex → ℤ)
    (hR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt E μ w (uR w hw) ((aR w hw).val : ℤ))
    (hC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt E μ w (uC w hw) (kC w hw))
    (uR' : ∀ w' : InfinitePlace M, w'.IsReal → ℂ) (aR' : ∀ w' : InfinitePlace M, w'.IsReal → ZMod 2)
    (uC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℂ) (kC' : ∀ w' : InfinitePlace M, w'.IsComplex → ℤ)
    (huR' : ∀ w', ∀ hw' : w'.IsReal,
      uR' w' hw' = uR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M)))
    (haR' : ∀ w', ∀ hw' : w'.IsReal,
      ((archLocalChar ξ w' (-1) : ℂˣ) : ℂ) =
        (-1) ^ (aR' w' hw' - aR (w'.comap (algebraMap E M)) (hw'.comap (algebraMap E M))).val)
    (huC' : ∀ w', ∀ hw' : w'.IsComplex,
      uC' w' hw' = if h : (w'.comap (algebraMap E M)).IsReal then uR _ h
        else uC _ (InfinitePlace.not_isReal_iff_isComplex.mp h))
    (hkC' : ∀ w', ∀ hw' : w'.IsComplex,
      (kC' w' hw').natAbs = if h : (w'.comap (algebraMap E M)).IsReal then 0
        else (kC _ (InfinitePlace.not_isReal_iff_isComplex.mp h)).natAbs) :
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).WellFormed ∧
    (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
        (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).Converges ∧
    (∀ s : ℂ,
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactor s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactor s ∧
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').archFactorDual s =
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).archFactorDual s) ∧
    (∀ s : ℂ, 1 < s.re →
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFun s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').euler w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFun s ∧
      (heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').LFunDual s =
        (∏ᶠ w' : HeightOneSpectrum (𝓞 M), if w'.under (𝓞 E) ∈ S then
          (((heckeDatum M (ξ * μ.comp (genuineBaseChange E M).idelicNorm) uR' aR' uC' kC').dual w').eval
            (((Ideal.absNorm w'.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ else 1) *
        (twistedDatum E Pi S (fun _ _ => RealArchParam.oddArtin)
          (fun _ _ => ComplexArchParam.trivialArtin) μ uR aR uC kC).LFunDual s) := by
  obtain ⟨-, -, hμu⟩ := hμ
  obtain ⟨hL, hconv⟩ := ArtinFactorSol.finite_part E M h2 ξ hξ S₀ hunr Pi S hS₀ hram hPi μ hμu uR aR uC kC
    uR' aR' uC' kC'
  exact ⟨ArtinFactorSol.wf_part E Pi S μ hμu uR aR uC kC hR hC, hconv,
    ArtinFactorSol.arch_part E M h2 ξ hξ S₀ hunr hsign Pi S hS₀ hram hPi μ uR aR uC kC uR' aR' uC' kC'
      huR' haR' huC' hkC',
    fun s hs => ⟨((hL s hs).1).1, ((hL s hs).2).1⟩⟩

end S_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_wellFormed_converges_twistedDatum_and_archFactor_lFun_heckeDatum_eq_induced_of_finrank_eq_two (solution)

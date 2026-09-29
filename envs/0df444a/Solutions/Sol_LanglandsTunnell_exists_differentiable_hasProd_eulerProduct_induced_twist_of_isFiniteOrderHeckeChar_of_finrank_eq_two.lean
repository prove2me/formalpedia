-- Prove2me | solution 1 for LanglandsTunnell.exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/12876e68-db31-5f37-98e5-b9b9de827309

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_M4aHerbrand_GenuineDescent_continuous_adelicNorm_genuineBaseChange
import Theorems.Thm_M4aHerbrand_GenuineDescent_adelicNorm_genuineBaseChange_algebraMap
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_eq_of_inertia_eq_bot
import Theorems.Thm_M4aHerbrand_genuineAdelicNorm_componentwise
import Theorems.Thm_M4aHerbrand_valuation_norm_adicCompletion_eq_pow_inertiaDeg
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Theorems.Thm_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
open scoped Pointwise

namespace InducedTwistEntireSol

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

section Action

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem algebraMap_smul (τ : E ≃ₐ[F] E) (x : 𝓞 E) :
    algebraMap (𝓞 E) E (τ • x) = τ (algebraMap (𝓞 E) E x) := rfl

omit [NumberField F] in
theorem smul_algebraMap (τ : E ≃ₐ[F] E) (a : 𝓞 F) :
    τ • (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply IsFractionRing.injective (𝓞 E) E
  rw [algebraMap_smul]
  change τ (algebraMap F E (algebraMap (𝓞 F) F a)) = algebraMap F E (algebraMap (𝓞 F) F a)
  exact τ.commutes _

omit [NumberField F] in
theorem smulCommClass : SMulCommClass (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) :=
  ⟨fun τ a x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap]⟩

attribute [local instance] smulCommClass

omit [NumberField F] [NumberField E] in
theorem smul_ideal_ne_bot (τ : E ≃ₐ[F] E) {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : τ • I ≠ ⊥ := by
  intro h
  apply hI
  have := congrArg (fun J : Ideal (𝓞 E) => τ⁻¹ • J) h
  simp only [inv_smul_smul] at this
  rw [this, ← Submodule.zero_eq_bot, smul_zero]

def smulHOS (τ : E ≃ₐ[F] E) (𝔓 : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  ⟨τ • 𝔓.asIdeal, inferInstance, smul_ideal_ne_bot τ 𝔓.ne_bot⟩

omit [NumberField F] [NumberField E] in
@[scoped simp] theorem smulHOS_asIdeal (τ : E ≃ₐ[F] E) (𝔓 : HeightOneSpectrum (𝓞 E)) :
    (smulHOS τ 𝔓).asIdeal = τ • 𝔓.asIdeal := rfl

omit [NumberField F] in
theorem under_smulHOS (τ : E ≃ₐ[F] E) (𝔓 : HeightOneSpectrum (𝓞 E)) :
    (smulHOS τ 𝔓).under (𝓞 F) = 𝔓.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, smulHOS_asIdeal,
    Ideal.under_smul]

omit [NumberField F] [NumberField E] in
theorem smulHOS_eq_iff {τ : E ≃ₐ[F] E} (𝔓 : HeightOneSpectrum (𝓞 E)) :
    smulHOS τ 𝔓 = 𝔓 ↔ τ • 𝔓.asIdeal = 𝔓.asIdeal :=
  ⟨fun h => by rw [← smulHOS_asIdeal, h], fun h => HeightOneSpectrum.ext h⟩

theorem smulHOS_smulHOS (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    (𝔓 : HeightOneSpectrum (𝓞 E)) : smulHOS τ (smulHOS τ 𝔓) = 𝔓 :=
  HeightOneSpectrum.ext (by rw [smulHOS_asIdeal, smulHOS_asIdeal, smul_smul, mul_self_eq_one h2 hτ,
    one_smul])

theorem eq_or_eq_smulHOS (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    {𝔓 𝔔 : HeightOneSpectrum (𝓞 E)} (h : 𝔔.under (𝓞 F) = 𝔓.under (𝓞 F)) :
    𝔔 = 𝔓 ∨ 𝔔 = smulHOS τ 𝔓 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) F E
  have hunder : 𝔓.asIdeal.under (𝓞 F) = 𝔔.asIdeal.under (𝓞 F) := by
    rw [← HeightOneSpectrum.under_asIdeal, ← HeightOneSpectrum.under_asIdeal, h]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 F) (𝓞 E) (E ≃ₐ[F] E)
    𝔓.asIdeal 𝔔.asIdeal hunder
  rcases eq_one_or_eq h2 hτ g with rfl | rfl
  · exact Or.inl (HeightOneSpectrum.ext (by rw [hg, one_smul]))
  · exact Or.inr (HeightOneSpectrum.ext (by rw [hg, smulHOS_asIdeal]))

end Action

section Ramification

variable (K : Type*) [Field K] [NumberField K]

theorem exists_prime_mem (𝔓 : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ 𝔓.asIdeal := by
  haveI := 𝔓.isPrime
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (𝔓.asIdeal.under ℤ)).principal
  have hp' : 𝔓.asIdeal.under ℤ = Ideal.span {p} := hp
  have hne : 𝔓.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    have hn : ((Ideal.absNorm 𝔓.asIdeal : ℤ) : 𝓞 K) ∈ 𝔓.asIdeal := by
      rw [Int.cast_natCast]; exact Ideal.absNorm_mem _
    have : (Ideal.absNorm 𝔓.asIdeal : ℤ) ∈ 𝔓.asIdeal.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, eq_intCast]; exact hn
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at this
    exact 𝔓.ne_bot this
  have hp0 : p ≠ 0 := by
    intro h0; apply hne; rw [hp', h0]; simp
  have hprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    exact Ideal.IsPrime.under ℤ 𝔓.asIdeal
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  have hmem : (p : 𝓞 K) ∈ 𝔓.asIdeal := by
    have : p ∈ 𝔓.asIdeal.under ℤ := by rw [hp']; exact Ideal.mem_span_singleton_self p
    rw [Ideal.under_def, Ideal.mem_comap, eq_intCast] at this
    exact this
  rcases Int.natAbs_eq p with h | h
  · rw [← Int.cast_natCast, ← h]; exact hmem
  · rw [← Int.cast_natCast, show ((p.natAbs : ℕ) : ℤ) = -p by omega, Int.cast_neg]
    exact 𝔓.asIdeal.neg_mem hmem

noncomputable def badPrimes : Finset ℕ := (NumberField.discr K).natAbs.primeFactors

theorem isUnramifiedAt_of_not_mem_badPrimes {p : ℕ} (hp : p.Prime) (hpB : p ∉ badPrimes K)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hpP : (p : 𝓞 K) ∈ P) : Algebra.IsUnramifiedAt ℤ P := by
  have hnd : ¬ ((p : ℤ) ∣ NumberField.discr K) := by
    intro h
    apply hpB
    rw [badPrimes, Nat.mem_primeFactors]
    exact ⟨hp, Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h),
      Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)⟩
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  exact (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpr).mp hnd P inferInstance
    (by exact_mod_cast hpP)

theorem finite_setOf_exists_mem (B : Finset ℕ) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ p ∈ B, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hsub : {v : HeightOneSpectrum (𝓞 K) | ∃ p ∈ B, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal} ⊆
      ⋃ p ∈ (B.filter Nat.Prime), {v : HeightOneSpectrum (𝓞 K) |
        v.asIdeal ∣ Ideal.span {(p : 𝓞 K)}} := by
    rintro v ⟨p, hpB, hp, hpv⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter, exists_prop]
    refine ⟨p, ⟨hpB, hp⟩, ?_⟩
    rw [Ideal.dvd_span_singleton]
    exact hpv
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => ?_
  have hp' : (p : ℕ).Prime := (Finset.mem_filter.mp hp).2
  apply Ideal.finite_factors
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp'.ne_zero

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def ramSet : Finset (HeightOneSpectrum (𝓞 F)) :=
  (finite_setOf_exists_mem F (badPrimes E)).toFinset

variable {F E}

omit [NumberField F] [NumberField E] in
theorem mem_under_iff {v : HeightOneSpectrum (𝓞 F)} {𝔓 : HeightOneSpectrum (𝓞 E)}
    (h : 𝔓.under (𝓞 F) = v) (x : 𝓞 F) :
    x ∈ v.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ 𝔓.asIdeal := by
  rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]

theorem ramificationIdx_eq_one {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ ramSet F E)
    {𝔓 : HeightOneSpectrum (𝓞 E)} (h : 𝔓.under (𝓞 F) = v) :
    v.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 := by
  obtain ⟨p, hp, hp𝔓⟩ := exists_prime_mem E 𝔓
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    rw [mem_under_iff h, map_natCast]; exact hp𝔓
  have hpB : p ∉ badPrimes E := by
    intro hB
    apply hv
    rw [ramSet, Set.Finite.mem_toFinset]
    exact ⟨p, hB, hp, hpv⟩
  haveI := 𝔓.isPrime
  haveI : Algebra.IsUnramifiedAt ℤ 𝔓.asIdeal := isUnramifiedAt_of_not_mem_badPrimes E hp hpB _ hp𝔓
  haveI : Algebra.IsUnramifiedAt (𝓞 F) 𝔓.asIdeal := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 F) (p := 𝔓.asIdeal)

attribute [local instance] Ideal.Quotient.field in

theorem card_stabilizer_eq_inertiaDeg (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ ramSet F E) {𝔓 : HeightOneSpectrum (𝓞 E)} (h : 𝔓.under (𝓞 F) = v) :
    haveI := finiteDimensional h2
    Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) 𝔓.asIdeal) = v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) F E
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
  haveI := 𝔓.isPrime.isMaximal 𝔓.ne_bot
  haveI := v.isPrime.isMaximal v.ne_bot
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[F] E) v.asIdeal 𝔓.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal 𝔓.asIdeal (E ≃ₐ[F] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot,
    ramificationIdx_eq_one hv h, one_mul,
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal 𝔓.asIdeal (E ≃ₐ[F] E), Ideal.inertiaDeg'_eq_inertiaDeg]

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

theorem dichotomy (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ ramSet F E) {𝔓 : HeightOneSpectrum (𝓞 E)}
    (h : 𝔓.under (𝓞 F) = v) :
    (smulHOS τ 𝔓 ≠ 𝔓 ∧ v.asIdeal.inertiaDeg' 𝔓.asIdeal = 1) ∨
      (smulHOS τ 𝔓 = 𝔓 ∧ v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2) := by
  haveI := finiteDimensional h2
  have hcard := card_stabilizer_eq_inertiaDeg h2 hv h
  by_cases hfix : τ • 𝔓.asIdeal = 𝔓.asIdeal
  · right
    refine ⟨(smulHOS_eq_iff 𝔓).mpr hfix, ?_⟩
    have htop : MulAction.stabilizer (E ≃ₐ[F] E) 𝔓.asIdeal = ⊤ := by
      rw [eq_top_iff]
      intro σ _
      rcases eq_one_or_eq h2 hτ σ with hσ | hσ
      · rw [hσ]; exact Subgroup.one_mem _
      · rw [hσ, MulAction.mem_stabilizer_iff]; exact hfix
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, card_gal h2] at hcard
    exact hcard.symm
  · left
    refine ⟨fun h' => hfix ((smulHOS_eq_iff 𝔓).mp h'), ?_⟩
    have hbot : MulAction.stabilizer (E ≃ₐ[F] E) 𝔓.asIdeal = ⊥ := by
      rw [eq_bot_iff]
      intro σ hσ
      rw [MulAction.mem_stabilizer_iff] at hσ
      rcases eq_one_or_eq h2 hτ σ with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1] at hσ; exact absurd hσ hfix
    rw [hbot, Subgroup.card_bot] at hcard
    exact hcard.symm

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

theorem split_of_ne (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    {w' w'' : HeightOneSpectrum (𝓞 E)} (hne : w' ≠ w'') (h : w'.under (𝓞 F) = w''.under (𝓞 F)) :
    w'' = smulHOS τ w' ∧ (w'.under (𝓞 F)).asIdeal.ramificationIdx' w'.asIdeal = 1 ∧
      (w'.under (𝓞 F)).asIdeal.inertiaDeg' w'.asIdeal = 1 ∧
      (w'.under (𝓞 F)).asIdeal.inertiaDeg' w''.asIdeal = 1 := by
  haveI := finiteDimensional h2
  have hw'' : w'' = smulHOS τ w' := by
    rcases eq_or_eq_smulHOS h2 hτ h.symm with h1 | h1
    · exact absurd h1.symm hne
    · exact h1

  obtain ⟨v, hv⟩ : ∃ v, w'.under (𝓞 F) = v := ⟨_, rfl⟩
  rw [hv] at h ⊢
  haveI := v.isPrime.isMaximal v.ne_bot
  haveI hlo' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hv, HeightOneSpectrum.under_asIdeal]⟩
  haveI hlo'' : w''.asIdeal.LiesOver v.asIdeal := ⟨by rw [h, HeightOneSpectrum.under_asIdeal]⟩
  haveI := w'.isPrime.isMaximal w'.ne_bot
  haveI := w''.isPrime.isMaximal w''.ne_bot
  have hsum := Ideal.sum_ramification_inertia (K := F) (L := E) (S := 𝓞 E) (p := v.asIdeal) v.ne_bot
  rw [h2] at hsum
  have hmem' : w'.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).mpr ⟨w'.isPrime, hlo'⟩
  have hmem'' : w''.asIdeal ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) :=
    (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).mpr ⟨w''.isPrime, hlo''⟩
  have hne' : w'.asIdeal ≠ w''.asIdeal := fun h' => hne (HeightOneSpectrum.ext h')
  have hpos : ∀ P ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E),
      1 ≤ v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P := by
    intro P hP
    obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 E)).mp hP
    have he : v.asIdeal.ramificationIdx' P ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P v.ne_bot
    have hf : 0 < v.asIdeal.inertiaDeg' P := Ideal.inertiaDeg'_pos v.asIdeal P
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he hf.ne')
  have hsub : ({w'.asIdeal, w''.asIdeal} : Finset (Ideal (𝓞 E))) ⊆
      IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 E) := by
    intro P hP
    rw [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hmem'
    · exact hmem''
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun P =>
      v.asIdeal.ramificationIdx' P * v.asIdeal.inertiaDeg' P) (fun P _ _ => Nat.zero_le _)
  rw [hsum, Finset.sum_pair hne'] at hle
  have h1' := hpos _ hmem'
  have h1'' := hpos _ hmem''
  have heq' : v.asIdeal.ramificationIdx' w'.asIdeal * v.asIdeal.inertiaDeg' w'.asIdeal = 1 := by omega
  have heq'' : v.asIdeal.ramificationIdx' w''.asIdeal * v.asIdeal.inertiaDeg' w''.asIdeal = 1 := by omega
  exact ⟨hw'', Nat.eq_one_of_mul_eq_one_right heq', Nat.eq_one_of_mul_eq_one_left heq',
    Nat.eq_one_of_mul_eq_one_left heq''⟩

end Ramification

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

section NonTrivial

variable {E : Type} [Field E] [NumberField E] {M : Type} [Field M] [NumberField M] [Algebra E M]

theorem normPowChar_unramified_and_apply (t : ℝ) (w : HeightOneSpectrum (𝓞 M)) :
    IsUnramifiedCharAt (normPowChar M t) w ∧
      ((normPowChar M t (uniformizerIdele M w) : ℂˣ) : ℂ) =
        ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) := by
  classical
  have h := NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
    M t w
  have hne : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * t)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot
  by_cases hu : IsUnramifiedCharAt (normPowChar M t) w
  · rw [if_pos hu] at h
    exact ⟨hu, h⟩
  · rw [if_neg hu] at h
    exact absurd h.symm hne

theorem exists_mem_normOneIdeles_ne_one (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hcχ : Continuous χ) (huχ : IsUnitaryChar (𝓞 E) E χ) :
    ∃ x ∈ normOneIdeles M, (ξ * normChar E M χ) x ≠ 1 := by
  classical
  haveI := finiteDimensional h2
  haveI := isGalois h2
  by_contra hcon
  have hcon' : ∀ x ∈ normOneIdeles M, (ξ * normChar E M χ) x = 1 := fun x hx => by
    by_contra h
    exact hcon ⟨x, hx, h⟩

  have hcont : Continuous (ξ * normChar E M χ) := by
    show Continuous fun x => ξ x * normChar E M χ x
    exact hξ.continuous.mul (continuous_normChar hcχ)
  have hunit : IsUnitaryChar (𝓞 M) M (ξ * normChar E M χ) := fun x => by
    show ‖((ξ x * normChar E M χ x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, norm_apply_eq_one hξ.isOfFinOrder, isUnitaryChar_normChar huχ x,
      one_mul]
  obtain ⟨t, ht⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles M
    (ξ * normChar E M χ) hcont hunit hcon'
  obtain ⟨w', w'', hne, hunder, hw', hw'', hval⟩ := hcusp
  obtain ⟨τ, hτ⟩ := exists_ne_one (F := E) (E := M) h2
  obtain ⟨-, he', hf', hf''⟩ := split_of_ne h2 hτ hne hunder
  obtain ⟨hnu', hnv'⟩ := normPowChar_unramified_and_apply (M := M) t w'
  obtain ⟨hnu'', hnv''⟩ := normPowChar_unramified_and_apply (M := M) t w''

  have hN' : Ideal.absNorm w'.asIdeal = Ideal.absNorm (w'.under (𝓞 E)).asIdeal := by
    rw [absNorm_eq_pow_inertiaDeg (F := E) rfl, hf', pow_one]
  have hN'' : Ideal.absNorm w''.asIdeal = Ideal.absNorm (w'.under (𝓞 E)).asIdeal := by
    rw [absNorm_eq_pow_inertiaDeg (F := E) hunder.symm, hf'', pow_one]
  have hnpeq : normPowChar M t (uniformizerIdele M w') = normPowChar M t (uniformizerIdele M w'') := by
    apply Units.ext
    rw [hnv', hnv'', hN', hN'']
  by_cases hχv : IsUnramifiedCharAt χ (w'.under (𝓞 E))
  ·
    have h1 : normChar E M χ (uniformizerIdele M w') = χ (uniformizerIdele E (w'.under (𝓞 E))) := by
      rw [normChar_uniformizerIdele w' hχv, hf', pow_one]
    have h2' : normChar E M χ (uniformizerIdele M w'') = χ (uniformizerIdele E (w'.under (𝓞 E))) := by
      have hχv'' : IsUnramifiedCharAt χ (w''.under (𝓞 E)) := hunder ▸ hχv
      rw [normChar_uniformizerIdele w'' hχv'']
      rw [← hunder, hf'', pow_one]
    have e1 : ξ (uniformizerIdele M w') * χ (uniformizerIdele E (w'.under (𝓞 E))) =
        normPowChar M t (uniformizerIdele M w') := by
      rw [← h1, ← MonoidHom.mul_apply, ht]
    have e2 : ξ (uniformizerIdele M w'') * χ (uniformizerIdele E (w'.under (𝓞 E))) =
        normPowChar M t (uniformizerIdele M w'') := by
      rw [← h2', ← MonoidHom.mul_apply, ht]
    apply hval
    apply mul_right_cancel (b := χ (uniformizerIdele E (w'.under (𝓞 E))))
    rw [e1, e2, hnpeq]
  ·
    apply hχv
    have hψ : normChar E M χ = ξ⁻¹ * (ξ * normChar E M χ) := (inv_mul_cancel_left ξ _).symm
    have hψunr : IsUnramifiedCharAt (normChar E M χ) w' := by
      rw [hψ, ht]
      exact isUnramifiedCharAt_mul (isUnramifiedCharAt_inv (hunr w' hw')) hnu'
    exact isUnramifiedCharAt_of_normChar (w'.under (𝓞 E)) ⟨w', rfl⟩
      (inertia_eq_bot h2 rfl he') hψunr

end NonTrivial

section Euler

variable {E : Type} [Field E] [NumberField E] {M : Type} [Field M] [NumberField M] [Algebra E M]

open scoped Classical in

noncomputable def gM (lam : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (s : ℂ) (w : HeightOneSpectrum (𝓞 M)) : ℂ :=
  (1 - (if IsUnramifiedCharAt lam w then ((lam (uniformizerIdele M w) : ℂˣ) : ℂ) else 0) *
    (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

open scoped Classical in

noncomputable def gE (Pi : HeckeEigensystem E ℂ) (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 E)) : ℂ :=
  ((if IsUnramifiedCharAt χ v
    then Polynomial.C 1 - Polynomial.C (((χ (uniformizerIdele E v) : ℂˣ) : ℂ) * Pi.a v) * Polynomial.X
      + Polynomial.C ((((χ (uniformizerIdele E v)) ^ 2 : ℂˣ) : ℂ) * Pi.b v) * Polynomial.X ^ 2
    else Polynomial.C 1 : Polynomial ℂ).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

theorem gM_of_unramified {lam : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ} {s : ℂ} {w : HeightOneSpectrum (𝓞 M)}
    (h : IsUnramifiedCharAt lam w) :
    gM lam s w = (1 - ((lam (uniformizerIdele M w) : ℂˣ) : ℂ) *
      (((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  classical
  simp only [gM, if_pos h]

theorem prod_gM_eq_gE (h2 : Module.finrank E M = 2) {τ : M ≃ₐ[E] M} (hτ : τ ≠ 1)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (Pi : HeckeEigensystem E ℂ) (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (s : ℂ)
    (v : HeightOneSpectrum (𝓞 E)) [Fintype (v.Extension (𝓞 M))]
    (hPi : (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = v → w''.under (𝓞 E) = v →
        Pi.a v = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b v = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = v → v.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a v = 0 ∧ Pi.b v = -(ξ (uniformizerIdele M w') : ℂ)))
    (hvram : v ∉ ramSet E M) (hvS₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v → w ∉ S₀)
    (hχv : IsUnramifiedCharAt χ v) :
    ∏ w : v.Extension (𝓞 M), gM (ξ * normChar E M χ) s w.1 = gE Pi χ s v := by
  classical
  haveI := finiteDimensional h2
  obtain ⟨𝔓, h𝔓⟩ := exists_under_eq (E := M) v

  have hlam : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v →
      IsUnramifiedCharAt (ξ * normChar E M χ) w ∧
        (((ξ * normChar E M χ) (uniformizerIdele M w) : ℂˣ) : ℂ) =
          ((ξ (uniformizerIdele M w) : ℂˣ) : ℂ) *
            ((χ (uniformizerIdele E v) : ℂˣ) : ℂ) ^ v.asIdeal.inertiaDeg' w.asIdeal := by
    intro w hw
    have hχw : IsUnramifiedCharAt χ (w.under (𝓞 E)) := hw.symm ▸ hχv
    refine ⟨isUnramifiedCharAt_mul (hunr w (hvS₀ w hw)) ?_, ?_⟩
    · exact isUnramifiedCharAt_normChar (w.under (𝓞 E)) ⟨w, rfl⟩ hχw
    · rw [MonoidHom.mul_apply, normChar_uniformizerIdele w hχw, Units.val_mul, Units.val_pow_eq_pow_val]
      subst hw
      rfl
  have hE : gE Pi χ s v = ((Polynomial.C 1 - Polynomial.C (((χ (uniformizerIdele E v) : ℂˣ) : ℂ) * Pi.a v)
      * Polynomial.X + Polynomial.C (((χ (uniformizerIdele E v) : ℂˣ) : ℂ) ^ 2 * Pi.b v) * Polynomial.X ^ 2 :
        Polynomial ℂ).eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    simp only [gE, if_pos hχv, Units.val_pow_eq_pow_val]
  have hfac : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v →
      gM (ξ * normChar E M χ) s w = (1 - ((ξ (uniformizerIdele M w) : ℂˣ) : ℂ) *
        ((χ (uniformizerIdele E v) : ℂˣ) : ℂ) ^ v.asIdeal.inertiaDeg' w.asIdeal *
          ((((Ideal.absNorm v.asIdeal) ^ v.asIdeal.inertiaDeg' w.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro w hw
    rw [gM_of_unramified (hlam w hw).1, (hlam w hw).2, absNorm_eq_pow_inertiaDeg hw]
  rcases dichotomy h2 hτ hvram h𝔓 with ⟨hsplit, hf1⟩ | ⟨hinert, hf2⟩
  ·
    have hτ𝔓 : (smulHOS τ 𝔓).under (𝓞 E) = v := (under_smulHOS τ 𝔓).trans h𝔓
    have hf1' : v.asIdeal.inertiaDeg' (smulHOS τ 𝔓).asIdeal = 1 := by
      rcases dichotomy h2 hτ hvram hτ𝔓 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd ((smulHOS_smulHOS h2 hτ 𝔓).symm.trans h) hsplit.symm
    let w₁ : v.Extension (𝓞 M) := ⟨𝔓, h𝔓⟩
    let w₂ : v.Extension (𝓞 M) := ⟨smulHOS τ 𝔓, hτ𝔓⟩
    have hne : w₁ ≠ w₂ := fun h => hsplit (congrArg Subtype.val h).symm
    have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁, w₂} := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases eq_or_eq_smulHOS h2 hτ (𝔓 := 𝔓) (𝔔 := w.1) (w.2.trans h𝔓.symm) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    have hprod : ∏ w : v.Extension (𝓞 M), gM (ξ * normChar E M χ) s w.1 =
        gM (ξ * normChar E M χ) s 𝔓 * gM (ξ * normChar E M χ) s (smulHOS τ 𝔓) := by
      rw [show (∏ w : v.Extension (𝓞 M), gM (ξ * normChar E M χ) s w.1) =
          ∏ w ∈ ({w₁, w₂} : Finset (v.Extension (𝓞 M))), gM (ξ * normChar E M χ) s w.1 from by
        rw [← huniv], Finset.prod_pair hne]
    obtain ⟨ha, hb⟩ := hPi.1 𝔓 (smulHOS τ 𝔓) hsplit.symm h𝔓 hτ𝔓
    rw [hprod, hfac 𝔓 h𝔓, hfac (smulHOS τ 𝔓) hτ𝔓, hf1, hf1', hE, ha, hb, ← mul_inv]
    congr 1
    simp only [pow_one, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    ring
  ·
    let w₁ : v.Extension (𝓞 M) := ⟨𝔓, h𝔓⟩
    have huniv : (Finset.univ : Finset (v.Extension (𝓞 M))) = {w₁} := by
      ext w
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      rcases eq_or_eq_smulHOS h2 hτ (𝔓 := 𝔓) (𝔔 := w.1) (w.2.trans h𝔓.symm) with h | h
      · exact Subtype.ext h
      · exact Subtype.ext (h.trans hinert)
    have hprod : ∏ w : v.Extension (𝓞 M), gM (ξ * normChar E M χ) s w.1 =
        gM (ξ * normChar E M χ) s 𝔓 := by
      rw [show (∏ w : v.Extension (𝓞 M), gM (ξ * normChar E M χ) s w.1) =
          ∏ w ∈ ({w₁} : Finset (v.Extension (𝓞 M))), gM (ξ * normChar E M χ) s w.1 from by
        rw [← huniv], Finset.prod_singleton]
    obtain ⟨ha, hb⟩ := hPi.2 𝔓 h𝔓 hf2
    have hx2 : ((((Ideal.absNorm v.asIdeal) ^ 2 : ℕ) : ℂ) ^ (-s)) =
        (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ 2 := by
      rw [sq, sq, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    rw [hprod, hfac 𝔓 h𝔓, hf2, hE, ha, hb, hx2]
    congr 1
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    ring

theorem finite_setOf_under_mem (T : Finset (HeightOneSpectrum (𝓞 E))) :
    {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 E) ∈ T}.Finite := by
  have h : {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 E) ∈ T} =
      ⋃ v ∈ (T : Set (HeightOneSpectrum (𝓞 E))),
        Set.range (Subtype.val : v.Extension (𝓞 M) → HeightOneSpectrum (𝓞 M)) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_range, Finset.mem_coe]
    constructor
    · intro hw
      exact ⟨w.under (𝓞 E), hw, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨v, hv, ⟨w', rfl⟩⟩
      rw [w'.2]
      exact hv
  rw [h]
  refine Set.Finite.biUnion T.finite_toSet fun v _ => ?_
  haveI : Finite {w : HeightOneSpectrum (𝓞 M) // w.under (𝓞 E) = v} :=
    HeightOneSpectrum.Extension.finite (𝓞 E) E M (𝓞 M) v
  exact Set.finite_range _

end Euler

end InducedTwistEntireSol
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two.InducedTwistEntireSol"

open InducedTwistEntireSol Polynomial in
open scoped Classical in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (Pi : HeckeEigensystem E ℂ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hPi : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
      (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
        Pi.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
        Pi.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
      (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
        Pi.a w = 0 ∧ Pi.b w = -(ξ (uniformizerIdele M w') : ℂ)))
    (χ : (AdeleRing (𝓞 E) E)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 E) E χ) (hcχ : Continuous χ)
    (huχ : IsUnitaryChar (𝓞 E) E χ) :
    ∃ S' : Finset (HeightOneSpectrum (𝓞 E)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      Differentiable ℂ Λ ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S'} =>
          ((if IsUnramifiedCharAt χ v.1
            then C 1 - C (((χ (uniformizerIdele E v.1) : ℂˣ) : ℂ) * Pi.a v.1) * X
              + C ((((χ (uniformizerIdele E v.1)) ^ 2 : ℂˣ) : ℂ) * Pi.b v.1) * X ^ 2
            else C 1 : ℂ[X]).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by
  classical
  haveI := finiteDimensional h2
  haveI := isGalois h2
  obtain ⟨τ, hτ⟩ := exists_ne_one (F := E) (E := M) h2

  set lam : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ := ξ * normChar E M χ with hlam
  have hlam_class : IsIdeleClassChar (𝓞 M) M lam := fun u => by
    rw [hlam, MonoidHom.mul_apply, hξ.isIdeleClassChar u, isIdeleClassChar_normChar hχ u, one_mul]
  have hlam_cont : Continuous lam := by
    show Continuous fun x => ξ x * normChar E M χ x
    exact hξ.continuous.mul (continuous_normChar hcχ)
  have hlam_unit : IsUnitaryChar (𝓞 M) M lam := fun x => by
    show ‖((ξ x * normChar E M χ x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, norm_apply_eq_one hξ.isOfFinOrder, isUnitaryChar_normChar huχ x,
      one_mul]
  have hlam_ne : ∃ x ∈ normOneIdeles M, lam x ≠ 1 :=
    exists_mem_normOneIdeles_ne_one h2 ξ hξ S₀ hunr hcusp χ hcχ huχ

  obtain ⟨Tχ, hTχ⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous E χ hcχ
  let S' : Finset (HeightOneSpectrum (𝓞 E)) :=
    S ∪ ramSet E M ∪ S₀.image (fun w => w.under (𝓞 E)) ∪ Tχ
  let TM : Finset (HeightOneSpectrum (𝓞 M)) := (finite_setOf_under_mem (M := M) S').toFinset
  have hTM : ∀ w : HeightOneSpectrum (𝓞 M), w ∈ TM ↔ w.under (𝓞 E) ∈ S' := fun w => by
    simp only [TM, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  obtain ⟨L, hLd, hL⟩ :=
    NumberField.TateGlobal.exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
      M lam hlam_class hlam_cont hlam_unit hlam_ne TM
  refine ⟨S', 4, L, hLd, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith

  have hEP := (NumberField.TateGlobal.differentiableOn_tprod_eulerFactor_of_norm_le_rpow M TM lam
    (fun _ => 1) (fun _ => 0) 0
    (fun w _ => by rw [Real.rpow_zero]; exact (hlam_unit _).le) 0 le_rfl
    (fun w _ => by
      rw [Real.rpow_zero]
      exact ⟨by simp, by simp⟩) 4 (by norm_num)).1 s hs
  have hfun : (fun w : {w : HeightOneSpectrum (𝓞 M) // w ∉ TM} =>
      ((if IsUnramifiedCharAt lam w.1
        then C 1 - C (((lam (uniformizerIdele M w.1) : ℂˣ) : ℂ) * (fun _ => (1 : ℂ)) w.1) * X
          + C ((((lam (uniformizerIdele M w.1)) ^ 2 : ℂˣ) : ℂ) * (fun _ => (0 : ℂ)) w.1) * X ^ 2
        else C 1 : ℂ[X]).eval (((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) =
      fun w => gM lam s w.1 := by
    funext w
    by_cases hw : IsUnramifiedCharAt lam w.1
    · rw [if_pos hw, gM_of_unramified hw]
      simp only [mul_one, mul_zero, map_zero, zero_mul, add_zero, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    · simp only [if_neg hw, gM, Polynomial.eval_C, zero_mul, sub_zero]
  rw [hfun] at hEP
  have hM : HasProd (fun w : {w : HeightOneSpectrum (𝓞 M) // w ∉ TM} => gM lam s w.1) (L s) := by
    rw [hL s hs1]
    convert hEP using 3 <;> first | rfl | with_reducible_and_instances rfl | simp

  haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype (v.Extension (𝓞 M)) :=
    fun v => HeightOneSpectrum.Extension.fintype (𝓞 E) E M (𝓞 M) v
  let e : (Σ v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S'}, v.1.Extension (𝓞 M)) ≃
      {w : HeightOneSpectrum (𝓞 M) // w ∉ TM} :=
    { toFun := fun p => ⟨p.2.1, fun h => p.1.2 (p.2.2 ▸ (hTM _).mp h)⟩
      invFun := fun w => ⟨⟨w.1.under (𝓞 E), fun h => w.2 ((hTM _).mpr h)⟩, ⟨w.1, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
        have hw' : w.under (𝓞 E) = v := hw
        subst hw'
        rfl
      right_inv := fun w => rfl }
  have hSig : HasProd ((fun w : {w : HeightOneSpectrum (𝓞 M) // w ∉ TM} => gM lam s w.1) ∘ e) (L s) :=
    (e.hasProd_iff).mpr hM
  have hfib := hSig.sigma (fun v => hasProd_fintype _)

  have hgood : ∀ v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S'},
      (∏ w : v.1.Extension (𝓞 M), gM lam s w.1) = gE Pi χ s v.1 := by
    rintro ⟨v, hv⟩
    have hvS : v ∉ S := fun h => hv (by simp [S', h])
    have hvram : v ∉ ramSet E M := fun h => hv (by simp [S', h])
    have hvS₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 E) = v → w ∉ S₀ := by
      intro w hw hwS
      exact hv (by simp [S', ← hw, Finset.mem_image_of_mem _ hwS])
    have hvT : v ∉ Tχ := fun h => hv (by simp [S', h])
    exact prod_gM_eq_gE h2 hτ ξ S₀ hunr Pi χ s v (hPi v hvS) hvram hvS₀ (hTχ v hvT)
  have hfib' : HasProd (fun v : {v : HeightOneSpectrum (𝓞 E) // v ∉ S'} => gE Pi χ s v.1) (L s) := by
    convert hfib using 1
    funext v
    exact (hgood v).symm
  exact hfib'

end S_LanglandsTunnell_exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two (solution)

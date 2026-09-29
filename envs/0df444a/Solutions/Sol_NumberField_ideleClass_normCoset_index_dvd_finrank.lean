-- Prove2me | solution 1 for NumberField.ideleClass_normCoset_index_dvd_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/29ec9aa0-448b-5c2e-ac60-1377fb6f2760

import Mathlib
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_M4aHerbrand_unitIdele_mem_idelicNorm_range
import Theorems.Thm_M4aHerbrand_exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit
import Theorems.Thm_LanglandsTunnell_Artin_artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
import Theorems.Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ideleClass_normCoset_index_dvd_finrank
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"

set_option autoImplicit false

namespace R3HC2

open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.Bridge M4aHerbrand.GenuineDescent
open Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin NumberField.NormIndex WithZero
open NumberField.AdelicLevel AutomorphicForm
open scoped nonZeroDivisors

section Ramified
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

attribute [local instance] FractionRing.liftAlgebra Ideal.Quotient.field

noncomputable def diffNorm : ℕ := Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L))

omit [IsGalois K L] in
theorem diffNorm_ne_zero : diffNorm K L ≠ 0 := by
  rw [diffNorm, Ne, Ideal.absNorm_eq_zero_iff]
  exact differentIdeal_ne_bot

theorem diffNorm_mem_of_inertia_ne_bot (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (hI : Q.inertia (L ≃ₐ[K] L) ≠ ⊥) : ((diffNorm K L : ℕ) : 𝓞 L) ∈ Q := by
  haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
  set p : Ideal (𝓞 K) := Q.under (𝓞 K) with hp
  haveI : Q.LiesOver p := ⟨rfl⟩
  have hp0 : p ≠ ⊥ := by
    intro h
    apply hQ
    exact Ideal.eq_bot_of_comap_eq_bot (by simpa [hp, Ideal.under_def] using h)
  haveI : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp0
  haveI : Finite (𝓞 K ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp0
  haveI : PerfectField (𝓞 K ⧸ p) := PerfectField.ofFinite
  haveI : Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) Q := by
    intro hunr
    apply hI
    have h1 : p.ramificationIdx' Q = 1 := by
      haveI := hunr
      have := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (p := Q)
      first | (rw [Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0]; exact this) | simpa [hp] using this
    have hcard : Nat.card (Q.inertia (L ≃ₐ[K] L)) = 1 := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) p Q,
        Ideal.ramificationIdxIn_eq_ramificationIdx p Q (L ≃ₐ[K] L),
        ← Ideal.ramificationIdx'_eq_ramificationIdx p Q hp0, h1]
    exact Subgroup.eq_bot_of_card_eq _ hcard
  have hdvd : Q ∣ differentIdeal (𝓞 K) (𝓞 L) := dvd_differentIdeal_iff.mpr hram
  have hle : differentIdeal (𝓞 K) (𝓞 L) ≤ Q := Ideal.le_of_dvd hdvd
  exact hle (Ideal.absNorm_mem _)

omit [NumberField K] [NumberField L] [IsGalois K L] in
theorem natCast_mem_under_iff {Q : Ideal (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (hQv : Q.under (𝓞 K) = v.asIdeal) (m : ℕ) :
    ((m : ℕ) : 𝓞 L) ∈ Q ↔ ((m : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  rw [← hQv, Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem exists_modulus (N : HeightOneSpectrum (𝓞 K) → ℕ) :
    ∃ 𝔣 : Ideal (𝓞 K), 𝔣 ≠ ⊥ ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ → v.asIdeal ^ N v ∣ 𝔣) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ 𝔣 →
        ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.under (𝓞 K) = v.asIdeal →
          Q.inertia (L ≃ₐ[K] L) = ⊥) := by
  classical
  set d : ℕ := diffNorm K L with hd
  have hd0 : d ≠ 0 := diffNorm_ne_zero K L
  set D : Ideal (𝓞 K) := Ideal.span {((d : ℕ) : 𝓞 K)} with hDdef
  have hD : D ≠ ⊥ := by
    rw [hDdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hd0
  have hT : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ D}.Finite := Ideal.finite_factors hD
  refine ⟨∏ v ∈ hT.toFinset, v.asIdeal ^ (N v + 1), ?_, ?_, ?_⟩
  · rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    rintro ⟨v, -, hv⟩
    exact v.ne_bot (by rw [← Ideal.zero_eq_bot]; exact eq_zero_of_pow_eq_zero hv)
  · intro v hI
    have hQ0 : primeAbove K L v ≠ ⊥ := primeAbove_ne_bot K L v
    have hmem := diffNorm_mem_of_inertia_ne_bot K L (primeAbove K L v) hQ0 hI
    rw [natCast_mem_under_iff K L (under_primeAbove K L v)] at hmem
    have hvT : v ∈ hT.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.mpr hmem
    exact (pow_dvd_pow _ (Nat.le_succ _)).trans (Finset.dvd_prod_of_mem _ hvT)
  · intro v hv Q hQp hQv
    by_contra hI
    have hQ0 : Q ≠ ⊥ := ne_bot_of_under_eq K L v hQv
    have hmem := diffNorm_mem_of_inertia_ne_bot K L Q hQ0 hI
    rw [natCast_mem_under_iff K L hQv] at hmem
    have hvT : v ∈ hT.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.mpr hmem
    exact hv ((dvd_pow_self _ (Nat.succ_ne_zero _)).trans (Finset.dvd_prod_of_mem _ hvT))

end Ramified

section Local

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝕀K" => (AdeleRing (𝓞 K) K)ˣ

noncomputable def mult (𝔣 : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors

theorem le_mult_of_pow_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)} {k : ℕ}
    (h : v.asIdeal ^ k ∣ 𝔣) : k ≤ mult K 𝔣 v := by
  rw [mult, ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔣) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
  exact h

theorem pow_mult_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal ^ mult K 𝔣 v ∣ 𝔣 := by
  rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
    Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr h𝔣) v.associates_irreducible, mult]

theorem mult_ne_zero_iff {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    mult K 𝔣 v ≠ 0 ↔ v.asIdeal ∣ 𝔣 := by
  rw [mult]
  exact Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible

theorem valued_coe (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k

theorem valued_coe_int (v : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r)) = v.intValuation r := by
  rw [valued_coe, HeightOneSpectrum.valuation_of_algebraMap]

theorem valued_sub_one_le_of_mem {v : HeightOneSpectrum (𝓞 K)} {r : 𝓞 K} {m : ℕ}
    (h : r - 1 ∈ v.asIdeal ^ m) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) - 1) ≤ exp (-(m : ℤ)) := by
  rw [← map_one (algebraMap K (v.adicCompletion K)), ← map_sub, ← map_one (algebraMap (𝓞 K) K),
    ← map_sub, valued_coe_int, HeightOneSpectrum.intValuation_le_pow_iff_dvd]
  exact Ideal.dvd_span_singleton.mpr h

theorem principal_snd (k : K) (v : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (𝔸K) k).2 v = algebraMap K (v.adicCompletion K) k := rfl

theorem principal_fst (k : K) (w : InfinitePlace K) (hw : w.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((algebraMap K (𝔸K) k).1 w) =
      InfinitePlace.embedding_of_isReal hw k :=
  InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw _

end Local

section Components

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝕀K" => (AdeleRing (𝓞 K) K)ˣ

theorem snd_mul_apply (x y : 𝔸K) (v : HeightOneSpectrum (𝓞 K)) : (x * y).2 v = x.2 v * y.2 v := rfl

theorem fst_mul_apply (x y : 𝔸K) (w : InfinitePlace K) : (x * y).1 w = x.1 w * y.1 w := rfl

theorem snd_units_inv (u : 𝕀K) (v : HeightOneSpectrum (𝓞 K)) :
    (((u⁻¹ : 𝕀K) : 𝕀K) : 𝔸K).2 v = ((((u : 𝕀K) : 𝔸K).2 v))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← snd_mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl

theorem fst_units_inv (u : 𝕀K) (w : InfinitePlace K) :
    (((u⁻¹ : 𝕀K) : 𝕀K) : 𝔸K).1 w = ((((u : 𝕀K) : 𝔸K).1 w))⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← fst_mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl

noncomputable def locIdele (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) : 𝕀K :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

theorem locIdele_fst (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((locIdele K v t : 𝕀K) : 𝔸K).1 = 1 := rfl

theorem locIdele_snd_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    ((locIdele K v t : 𝕀K) : 𝔸K).2 v = t := by
  change ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v = t
  exact localUnit_apply_self (𝓞 K) K v t

theorem locIdele_snd_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    ((locIdele K v t : 𝕀K) : 𝔸K).2 w = 1 := by
  change ((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = 1
  exact localUnit_apply_of_ne (𝓞 K) K v t hw

theorem finPart_locIdele_self (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    finPart v (locIdele K v t) = t :=
  Units.ext (locIdele_snd_self K v t)

theorem finPart_locIdele_of_ne (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) : finPart w (locIdele K v t) = 1 :=
  Units.ext (locIdele_snd_of_ne K v t hw)

theorem infPart_locIdele (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    infPart (locIdele K v t) = 1 :=
  Units.ext (locIdele_fst K v t)

theorem uniformizerIdele_eq (v : HeightOneSpectrum (𝓞 K)) :
    uniformizerIdele K v = locIdele K v (uniformizerUnit K v) := rfl

noncomputable def contentIdele (I : FractionalIdeal ((𝓞 K)⁰) K) : 𝕀K :=
  raySymbol K (uniformizerIdele K) I

theorem contentIdele_def (I : FractionalIdeal ((𝓞 K)⁰) K) :
    contentIdele K I = ∏ᶠ v : HeightOneSpectrum (𝓞 K), uniformizerIdele K v ^ FractionalIdeal.count K v I :=
  rfl

theorem finPart_contentIdele (I : FractionalIdeal ((𝓞 K)⁰) K) (w : HeightOneSpectrum (𝓞 K)) :
    finPart w (contentIdele K I) = uniformizerUnit K w ^ FractionalIdeal.count K w I := by
  rw [contentIdele_def, MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors K _ I)]
  rw [finprod_eq_single _ w]
  · rw [map_zpow, uniformizerIdele_eq, finPart_locIdele_self]
  · intro v hv
    rw [map_zpow, uniformizerIdele_eq, finPart_locIdele_of_ne K v _ hv.symm, one_zpow]

theorem infPart_contentIdele (I : FractionalIdeal ((𝓞 K)⁰) K) : infPart (contentIdele K I) = 1 := by
  rw [contentIdele_def, MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors K _ I)]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [map_zpow, uniformizerIdele_eq, infPart_locIdele, one_zpow]

theorem contentIdele_snd (I : FractionalIdeal ((𝓞 K)⁰) K) (w : HeightOneSpectrum (𝓞 K)) :
    ((contentIdele K I : 𝕀K) : 𝔸K).2 w =
      ((uniformizerUnit K w ^ FractionalIdeal.count K w I : (w.adicCompletion K)ˣ) : w.adicCompletion K) := by
  rw [← finPart_contentIdele]; rfl

theorem contentIdele_fst (I : FractionalIdeal ((𝓞 K)⁰) K) : ((contentIdele K I : 𝕀K) : 𝔸K).1 = 1 := by
  have := congrArg (fun u : (InfiniteAdeleRing K)ˣ => (u : InfiniteAdeleRing K)) (infPart_contentIdele K I)
  simpa using this

theorem valued_contentIdele (I : FractionalIdeal ((𝓞 K)⁰) K) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((contentIdele K I : 𝕀K) : 𝔸K).2 w) = exp (-FractionalIdeal.count K w I) := by
  rw [contentIdele_snd, Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← exp_zsmul,
    smul_eq_mul, mul_neg, mul_one]

theorem map_raySymbol {M M' : Type*} [CommGroup M] [CommGroup M'] (φ : M →* M')
    (f : HeightOneSpectrum (𝓞 K) → M) (I : FractionalIdeal ((𝓞 K)⁰) K) :
    φ (raySymbol K f I) = raySymbol K (φ ∘ f) I := by
  unfold raySymbol
  rw [MonoidHom.map_finprod _ (hasFiniteMulSupport_raySymbol_factors K f I)]
  simp only [map_zpow, Function.comp_apply]

end Components

section NormCriterion

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝕀K" => (AdeleRing (𝓞 K) K)ˣ

noncomputable def normSubgroup : Subgroup 𝕀K :=
  principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range

theorem mem_range_idelicNorm {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hdepth : ∀ v : HeightOneSpectrum (𝓞 K), (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ →
      v.asIdeal ^ admissibleExpOfDegree K (Module.finrank K L) v ∣ 𝔣)
    (u : 𝕀K)
    (hunit : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((u : 𝕀K) : 𝔸K).2 v) = 1)
    (hcong : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((u : 𝕀K) : 𝔸K).2 v - 1) ≤ exp (-(mult K 𝔣 v : ℤ)))
    (harch : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (((u : 𝕀K) : 𝔸K).1 w)) :
    u ∈ (genuineBaseChange K L).idelicNorm.range := by
  refine M4aHerbrand.unitIdele_mem_idelicNorm_range K L (genuineBaseChange K L) u hunit ?_
    (fun w hw _ => harch w hw)
  intro v hv
  have hd := hdepth v hv
  have hle : admissibleExpOfDegree K (Module.finrank K L) v ≤ mult K 𝔣 v := le_mult_of_pow_dvd K h𝔣 hd
  have hpos : 0 < admissibleExpOfDegree K (Module.finrank K L) v := by
    unfold admissibleExpOfDegree; omega
  have hvd : v.asIdeal ∣ 𝔣 := (dvd_pow_self _ hpos.ne').trans hd
  refine (hcong v hvd).trans ?_
  rw [← admissibleExpOfDegree_finrank, exp_le_exp, neg_le_neg_iff]
  exact_mod_cast hle

theorem locIdele_mem_range {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    (hdepth : ∀ v : HeightOneSpectrum (𝓞 K), (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ →
      v.asIdeal ^ admissibleExpOfDegree K (Module.finrank K L) v ∣ 𝔣)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = 1) :
    locIdele K v t ∈ (genuineBaseChange K L).idelicNorm.range := by
  refine mem_range_idelicNorm K L h𝔣 hdepth _ ?_ ?_ ?_
  · intro w
    by_cases hw : w = v
    · subst hw; rw [locIdele_snd_self]; exact ht
    · rw [locIdele_snd_of_ne K v t hw, map_one]
  · intro w hwd
    have hw : w ≠ v := fun h => hv (h ▸ hwd)
    rw [locIdele_snd_of_ne K v t hw, sub_self, map_zero]; exact zero_le'
  · intro w hw
    rw [locIdele_fst]
    change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw 1
    rw [map_one]; exact one_pos

end NormCriterion

section Psi

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝕀K" => (AdeleRing (𝓞 K) K)ˣ

abbrev NormQuot : Type := 𝕀K ⧸ normSubgroup K L

noncomputable def gfun (v : HeightOneSpectrum (𝓞 K)) : NormQuot K L :=
  QuotientGroup.mk (uniformizerIdele K v)

noncomputable def psi' : (FractionalIdeal ((𝓞 K)⁰) K)ˣ →* NormQuot K L :=
  raySymbolUnitsHom K (gfun K L)

omit [IsGalois K L] in
theorem psi'_apply (I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ) :
    psi' K L I = QuotientGroup.mk (contentIdele K (I : FractionalIdeal ((𝓞 K)⁰) K)) := by
  change raySymbol K (gfun K L) (I : FractionalIdeal ((𝓞 K)⁰) K) = _
  rw [contentIdele, show gfun K L = (QuotientGroup.mk' (normSubgroup K L)) ∘ uniformizerIdele K from rfl,
    ← map_raySymbol]
  rfl

omit [IsGalois K L] in
theorem principal_mem_normSubgroup (k : Kˣ) :
    Units.map (algebraMap K (𝔸K) : K →* 𝔸K) k ∈ normSubgroup K L :=
  Subgroup.mem_sup_left ⟨k, rfl⟩

omit [IsGalois K L] in
theorem norm_mem_normSubgroup {u : 𝕀K} (hu : u ∈ (genuineBaseChange K L).idelicNorm.range) :
    u ∈ normSubgroup K L :=
  Subgroup.mem_sup_right hu

variable {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
  (hdepth : ∀ v : HeightOneSpectrum (𝓞 K), (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ →
    v.asIdeal ^ admissibleExpOfDegree K (Module.finrank K L) v ∣ 𝔣)

include h𝔣 hdepth

theorem psi'_eq_one_of_narrowRaySet {I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ} (hI : I ∈ narrowRaySet K 𝔣) :
    psi' K L I = 1 := by
  obtain ⟨α, hα0, hα1, hpos, hIα⟩ := hI
  rw [psi'_apply, QuotientGroup.eq_one_iff, hIα]
  set C : 𝕀K := contentIdele K ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) with hC
  have hαK : (algebraMap (𝓞 K) K α : K) ≠ 0 := by
    simpa using hα0
  set a : Kˣ := Units.mk0 _ hαK with ha
  set P : 𝕀K := Units.map (algebraMap K (𝔸K) : K →* 𝔸K) a with hP

  have hJ0 : (Ideal.span {α} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hα0
  have hcount : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {α} : Ideal (𝓞 K))).factors : ℤ) :=
    fun v => FractionalIdeal.count_coe K v hJ0
  have hPv : ∀ v : HeightOneSpectrum (𝓞 K), ((P : 𝕀K) : 𝔸K).2 v =
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K α) := fun v => rfl
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((P : 𝕀K) : 𝔸K).2 v) =
      exp (-FractionalIdeal.count K v ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K)) := by
    intro v
    rw [hPv, valued_coe_int, HeightOneSpectrum.intValuation_if_neg _ hα0, hcount]
  have hu : P * C⁻¹ ∈ (genuineBaseChange K L).idelicNorm.range := by
    refine mem_range_idelicNorm K L h𝔣 hdepth _ ?_ ?_ ?_
    · intro v
      rw [Units.val_mul, snd_mul_apply, map_mul, hval, snd_units_inv, map_inv₀, hC, valued_contentIdele,
        ← exp_neg, neg_neg, ← exp_add, neg_add_cancel, exp_zero]
    · intro v hv
      have hc0 : FractionalIdeal.count K v ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 0 :=
        count_span_singleton_eq_zero_of_sub_one_mem K hα0 hα1 hv
      have hCv : ((C : 𝕀K) : 𝔸K).2 v = 1 := by
        rw [hC, contentIdele_snd, hc0, zpow_zero, Units.val_one]
      rw [Units.val_mul, snd_mul_apply, snd_units_inv, hCv, inv_one, mul_one, hPv]
      refine valued_sub_one_le_of_mem K ?_
      exact Ideal.le_of_dvd (pow_mult_dvd K h𝔣 v) hα1
    · intro w hw
      rw [Units.val_mul, fst_mul_apply, fst_units_inv, hC, contentIdele_fst,
        show (1 : InfiniteAdeleRing K) w = 1 from rfl, inv_one, mul_one, hP, Units.coe_map, MonoidHom.coe_coe,
        Units.val_mk0, principal_fst]
      exact hpos _
  have : C = (P * C⁻¹)⁻¹ * P := by group
  rw [this]
  exact (normSubgroup K L).mul_mem ((normSubgroup K L).inv_mem (norm_mem_normSubgroup K L hu))
    (principal_mem_normSubgroup K L a)

theorem gfun_pow_inertiaDeg_eq_one (𝔓 : HeightOneSpectrum (𝓞 L))
    (h𝔓 : ¬ (𝔓.under (𝓞 K)).asIdeal ∣ 𝔣) :
    gfun K L (𝔓.under (𝓞 K)) ^ ((𝔓.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓.asIdeal) = 1 := by
  obtain ⟨t, ht, hN⟩ :=
    M4aHerbrand.exists_idelicNorm_uniformizerIdele_eq_pow_inertiaDeg_mul_localUnit K L 𝔓
  rw [gfun, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  have hT : locIdele K (𝔓.under (𝓞 K)) t ∈ (genuineBaseChange K L).idelicNorm.range :=
    locIdele_mem_range K L h𝔣 hdepth h𝔓 t ht
  have heq : uniformizerIdele K (𝔓.under (𝓞 K)) ^ ((𝔓.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓.asIdeal) =
      (genuineBaseChange K L).idelicNorm (uniformizerIdele L 𝔓) * (locIdele K (𝔓.under (𝓞 K)) t)⁻¹ := by
    rw [hN]; exact (mul_inv_cancel_right _ _).symm
  rw [heq]
  exact (normSubgroup K L).mul_mem (norm_mem_normSubgroup K L ⟨_, rfl⟩)
    ((normSubgroup K L).inv_mem (norm_mem_normSubgroup K L hT))

theorem psi'_fracRelNormUnit_eq_one {Y : (FractionalIdeal ((𝓞 L)⁰) L)ˣ}
    (hY : Y ∈ coprimeToModulus L (modulusExt K L 𝔣)) :
    psi' K L (fracRelNormUnit K L Y) = 1 := by
  change psi' K L (raySymbol L _ (Y : FractionalIdeal ((𝓞 L)⁰) L)) = 1
  have hmap := map_raySymbol L (M := (FractionalIdeal ((𝓞 K)⁰) K)ˣ) (M' := NormQuot K L) (psi' K L)
    (fun w => primeUnit K (placeUnder' K L w) ^ (placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal)
    (Y : FractionalIdeal ((𝓞 L)⁰) L)
  rw [hmap]
  refine finprod_eq_one_of_forall_eq_one fun w => ?_
  by_cases hw : FractionalIdeal.count L w (Y : FractionalIdeal ((𝓞 L)⁰) L) = 0
  · rw [hw, zpow_zero]
  · have hwd : ¬ w.asIdeal ∣ modulusExt K L 𝔣 := fun h => hw ((mem_coprimeToModulus_iff L).mp hY w h)
    have hvd : ¬ (placeUnder' K L w).asIdeal ∣ 𝔣 := fun h => hwd ((placeUnder'_dvd_iff K L 𝔣 w).mp h)
    rw [Function.comp_apply, map_pow]
    have hprime : psi' K L (primeUnit K (placeUnder' K L w)) = gfun K L (placeUnder' K L w) :=
      raySymbol_primeUnit K (gfun K L) _
    rw [hprime]
    have h1 := gfun_pow_inertiaDeg_eq_one K L h𝔣 hdepth w hvd
    change gfun K L (placeUnder' K L w) ^ ((placeUnder' K L w).asIdeal.inertiaDeg' w.asIdeal) = 1 at h1
    rw [h1, one_zpow]

theorem normRaySubgroup_le_ker :
    normRaySubgroup K L 𝔣 ≤ ((psi' K L).comp (coprimeToModulus K 𝔣).subtype).ker := by
  refine sup_le ?_ ?_
  · intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    have hle : narrowRaySubgroup K 𝔣 ≤ (psi' K L).ker :=
      (Subgroup.closure_le _).mpr fun I hI => psi'_eq_one_of_narrowRaySet K L h𝔣 hdepth hI
    exact hle hy
  · rintro _ ⟨Y, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact psi'_fracRelNormUnit_eq_one K L h𝔣 hdepth Y.2

end Psi

section Adjuster

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝕀K" => (AdeleRing (𝓞 K) K)ˣ

noncomputable abbrev prin (α : Kˣ) : 𝕀K := Units.map (algebraMap K (𝔸K) : K →* 𝔸K) α

theorem prin_mul (a b : Kˣ) : prin K (a * b) = prin K a * prin K b := map_mul _ a b

theorem prin_snd (α : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((prin K α : 𝕀K) : 𝔸K).2 v = algebraMap K (v.adicCompletion K) (α : K) := rfl

theorem prin_fst (α : Kˣ) (w : InfinitePlace K) (hw : w.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (((prin K α : 𝕀K) : 𝔸K).1 w) =
      InfinitePlace.embedding_of_isReal hw (α : K) :=
  principal_fst K _ w hw

theorem exists_approx (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (hx : x ≠ 0) (e : ℕ) :
    ∃ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) = Valued.v x ∧
      Valued.v (algebraMap K (v.adicCompletion K) k * x⁻¹ - 1) ≤ exp (-(e : ℤ)) := by
  have hvx : Valued.v x ≠ 0 := by rwa [Ne, map_eq_zero]

  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K v
  set z : v.adicCompletion K := x * (algebraMap K (v.adicCompletion K) ϖ) ^ e with hz
  have hvz : Valued.v z = Valued.v x * exp (-(e : ℤ)) := by
    rw [hz, map_mul, map_pow, valued_coe, hϖ, ← exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  have hz0 : Valued.v z ≠ 0 := by rw [hvz]; exact mul_ne_zero hvx exp_ne_zero
  have hz0' : z ≠ 0 := fun h => by rw [h, map_zero] at hz0; exact hz0 rfl
  have hnhds : {y : v.adicCompletion K | Valued.v.restrict (y - x) < Valued.v.restrict z} ∈ nhds x := by
    rw [Valued.mem_nhds]
    have h' : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict z ≠ 0 := by simp [hz0']
    exact ⟨Units.mk0 _ h', fun y hy => hy⟩
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := K) v).mem_nhds hnhds
  have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - x) < Valued.v z :=
    (Valuation.restrict_lt_iff _).mp hk
  have hlt : Valued.v (algebraMap K (v.adicCompletion K) k - x) < Valued.v x := by
    refine hk'.trans_le ?_
    rw [hvz]
    conv_rhs => rw [← mul_one (Valued.v x)]
    gcongr
    rw [← exp_zero, exp_le_exp]; omega
  have hval : Valued.v (algebraMap K (v.adicCompletion K) k) = Valued.v x := Valuation.map_eq_of_sub_lt _ hlt
  refine ⟨k, hval, ?_⟩
  have : algebraMap K (v.adicCompletion K) k * x⁻¹ - 1 = (algebraMap K (v.adicCompletion K) k - x) * x⁻¹ := by
    field_simp
  rw [this, map_mul, map_inv₀]
  calc Valued.v (algebraMap K (v.adicCompletion K) k - x) * (Valued.v x)⁻¹
      ≤ Valued.v z * (Valued.v x)⁻¹ := by gcongr
    _ = exp (-(e : ℤ)) := by rw [hvz, mul_comm, ← mul_assoc, inv_mul_cancel₀ hvx, one_mul]

theorem exists_finite_adjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (x : 𝕀K) :
    ∃ α₀ : Kˣ, ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((x * (prin K α₀)⁻¹ : 𝕀K) : 𝔸K).2 v) = 1 ∧
      Valued.v (((x * (prin K α₀)⁻¹ : 𝕀K) : 𝔸K).2 v - 1) ≤ exp (-(mult K 𝔣 v : ℤ)) := by
  classical
  set S : Finset (HeightOneSpectrum (𝓞 K)) := (Ideal.finite_factors h𝔣).toFinset with hS
  have hmemS : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S ↔ v.asIdeal ∣ 𝔣 := fun v => by
    rw [hS, Set.Finite.mem_toFinset]; rfl

  have hx0 : ∀ v : HeightOneSpectrum (𝓞 K), ((x : 𝕀K) : 𝔸K).2 v ≠ 0 := fun v h => by
    have := congrArg (fun u : 𝕀K => ((u : 𝕀K) : 𝔸K).2 v) (mul_inv_cancel x)
    simp only [Units.val_mul, snd_mul_apply, h, zero_mul, Units.val_one] at this
    exact zero_ne_one this

  choose k hk using fun v : HeightOneSpectrum (𝓞 K) => exists_approx K v (((x : 𝕀K) : 𝔸K).2 v) (hx0 v) (mult K 𝔣 v)
  have hk0 : ∀ v, k v ≠ 0 := fun v h => by
    have := (hk v).1
    rw [h, map_zero, map_zero] at this
    exact hx0 v ((map_eq_zero _).mp this.symm)

  obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples_of_finset ((𝓞 K)⁰) (S.image k)
  have hdd0 : ((dd : 𝓞 K) : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero dd
  have hc : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ S → ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K dd * k v := by
    intro v hv
    obtain ⟨c, hc⟩ := (RingHom.mem_rangeS.mp (hdd (k v) (Finset.mem_image_of_mem k hv)))
    exact ⟨c, hc.trans (Algebra.smul_def _ _)⟩
  choose! c hcdef using hc
  have hc0 : ∀ v ∈ S, c v ≠ 0 := fun v hv h => by
    have := hcdef v hv
    rw [h, map_zero] at this
    exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hdd0) (hk0 v) this.symm

  set nn : HeightOneSpectrum (𝓞 K) → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {c v})).factors with hnn
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => nn v + mult K 𝔣 v) (fun v _ => v.prime)
    (fun v _ v' _ hne => fun h => hne (HeightOneSpectrum.ext h)) (fun v => c v)

  have hval : ∀ v ∈ S,
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a)) =
        Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v))) ∧
      Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) *
        (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v)))⁻¹ - 1) ≤ exp (-(mult K 𝔣 v : ℤ)) := by
    intro v hv
    have hcv : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v))) = exp (-(nn v : ℤ)) := by
      rw [valued_coe_int, HeightOneSpectrum.intValuation_if_neg _ (hc0 v hv)]
    have hsub : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) -
        algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v))) ≤ exp (-((nn v + mult K 𝔣 v : ℕ) : ℤ)) := by
      rw [← map_sub, ← map_sub, valued_coe_int, HeightOneSpectrum.intValuation_le_pow_iff_dvd]
      exact Ideal.dvd_span_singleton.mpr (ha v hv)
    have hmpos : 0 < mult K 𝔣 v := Nat.pos_of_ne_zero ((mult_ne_zero_iff K h𝔣 v).mpr ((hmemS v).mp hv))
    have hlt : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) -
        algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v))) <
        Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v))) := by
      refine hsub.trans_lt ?_
      rw [hcv, exp_lt_exp]; push_cast; omega
    have heq := Valuation.map_eq_of_sub_lt _ hlt
    refine ⟨heq, ?_⟩
    have hcne : algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v)) ≠ 0 := by
      intro h; rw [h, map_zero] at hcv; exact exp_ne_zero hcv.symm
    have : algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) *
        (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v)))⁻¹ - 1 =
        (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) -
          algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v))) *
        (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v)))⁻¹ := by
      field_simp
    rw [this, map_mul, map_inv₀, hcv]
    calc _ ≤ exp (-((nn v + mult K 𝔣 v : ℕ) : ℤ)) * (exp (-(nn v : ℤ)))⁻¹ := by gcongr
      _ = exp (-(mult K 𝔣 v : ℤ)) := by
          rw [← exp_neg, ← exp_add, exp_inj]; push_cast; ring

  by_cases hSe : S = ∅
  · refine ⟨1, fun v hv => ?_⟩
    have : v ∈ S := (hmemS v).mpr hv
    rw [hSe] at this; exact absurd this (Finset.notMem_empty v)
  obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  have ha0 : a ≠ 0 := by
    intro h
    have h1 := (hval v₀ hv₀).1
    rw [h, map_zero, map_zero, map_zero, eq_comm, map_eq_zero, map_eq_zero,
      map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)] at h1
    exact hc0 v₀ hv₀ h1

  have haK : algebraMap (𝓞 K) K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  have hdK : algebraMap (𝓞 K) K dd ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hdd0
  refine ⟨Units.mk0 (algebraMap (𝓞 K) K a) haK / Units.mk0 (algebraMap (𝓞 K) K dd) hdK, fun v hvd => ?_⟩
  have hv : v ∈ S := (hmemS v).mpr hvd

  set xv := ((x : 𝕀K) : 𝔸K).2 v with hxv
  set av := algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K a) with hav
  set cv := algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (c v)) with hcvd
  set dv := algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K dd) with hdv
  set kv := algebraMap K (v.adicCompletion K) (k v) with hkv
  have hcv_eq : cv = dv * kv := by rw [hcvd, hcdef v hv, map_mul]
  have hdv0 : dv ≠ 0 := by rw [hdv, map_ne_zero]; exact hdK
  have hkv0 : kv ≠ 0 := by rw [hkv, map_ne_zero]; exact hk0 v
  have hxv0 : xv ≠ 0 := hx0 v

  have hcomp : ((x * (prin K (Units.mk0 (algebraMap (𝓞 K) K a) haK / Units.mk0 (algebraMap (𝓞 K) K dd) hdK))⁻¹
      : 𝕀K) : 𝔸K).2 v = xv * (av * dv⁻¹)⁻¹ := by
    rw [Units.val_mul, snd_mul_apply, snd_units_inv, prin_snd]
    congr 2
    rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, map_div₀, div_eq_mul_inv]

  have h1 : Valued.v (kv * xv⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hkv, (hk v).1, mul_inv_cancel₀]; rwa [Ne, map_eq_zero]
  have h2 : Valued.v (av * cv⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hav, hcvd, (hval v hv).1, mul_inv_cancel₀]
    rw [Ne, map_eq_zero, ← hcvd, hcv_eq]; exact mul_ne_zero hdv0 hkv0
  have h12 := unit_cong_mul K h2 (hval v hv).2 h1 (hk v).2
  have hprod : av * cv⁻¹ * (kv * xv⁻¹) = (av * dv⁻¹) * xv⁻¹ := by
    rw [hcv_eq]; field_simp
  rw [hprod] at h12
  refine ⟨?_, ?_⟩
  · rw [hcomp, map_mul, map_inv₀]
    have := h12.1
    rw [map_mul, map_inv₀] at this
    have h' := congrArg Inv.inv this
    rwa [mul_inv_rev, inv_inv, inv_one] at h'
  · rw [hcomp]
    have := unit_cong_div K (a := (1 : v.adicCompletion K)) (by rw [sub_self, map_zero]; exact zero_le') h12.1 h12.2
    rwa [one_mul, mul_inv_rev, inv_inv] at this

end Adjuster

section Surj

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

local notation "𝔸K" => AdeleRing (𝓞 K) K
local notation "𝕀K" => (AdeleRing (𝓞 K) K)ˣ

omit [NumberField K] in

theorem infinitePlace_eq_of_embedding_of_isReal_eq {w w' : InfinitePlace K} (hw : w.IsReal) (hw' : w'.IsReal)
    (h : InfinitePlace.embedding_of_isReal hw = InfinitePlace.embedding_of_isReal hw') : w = w' := by
  have : w.embedding = w'.embedding := by
    ext x
    rw [← InfinitePlace.embedding_of_isReal_apply hw, ← InfinitePlace.embedding_of_isReal_apply hw', h]
  rw [← InfinitePlace.mk_embedding w, this, InfinitePlace.mk_embedding]

theorem ext_fst_ne_zero (y : 𝕀K) (w : InfinitePlace K) (hw : w.IsReal) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (((y : 𝕀K) : 𝔸K).1 w) ≠ 0 := by
  rw [map_ne_zero]
  intro h
  have := congrArg (fun u : 𝕀K => ((u : 𝕀K) : 𝔸K).1 w) (mul_inv_cancel y)
  simp only [Units.val_mul, fst_mul_apply, h, zero_mul, Units.val_one] at this
  exact zero_ne_one this

theorem exists_adjuster {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥) (x : 𝕀K) :
    ∃ α : Kˣ, (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔣 →
      Valued.v (((x * (prin K α)⁻¹ : 𝕀K) : 𝔸K).2 v) = 1 ∧
      Valued.v (((x * (prin K α)⁻¹ : 𝕀K) : 𝔸K).2 v - 1) ≤ exp (-(mult K 𝔣 v : ℤ))) ∧
      ∀ (w : InfinitePlace K) (hw : w.IsReal),
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (((x * (prin K α)⁻¹ : 𝕀K) : 𝔸K).1 w) := by
  obtain ⟨α₀, hα₀⟩ := exists_finite_adjuster K h𝔣 x
  set y : 𝕀K := x * (prin K α₀)⁻¹ with hy
  set r : ∀ w : InfinitePlace K, w.IsReal → ℝ := fun w hw =>
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (((y : 𝕀K) : 𝔸K).1 w) with hr
  have hr0 : ∀ (w : InfinitePlace K) (hw : w.IsReal), r w hw ≠ 0 := fun w hw => ext_fst_ne_zero K y w hw
  set Nset : Set (K →+* ℝ) := {φ | ∃ (w : InfinitePlace K) (hw : w.IsReal),
    φ = InfinitePlace.embedding_of_isReal hw ∧ r w hw < 0} with hN
  obtain ⟨δ, hδ0, hδ1, hδsign⟩ := NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff K 𝔣 h𝔣 Nset
  have hδK : algebraMap (𝓞 K) K δ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hδ0
  set δu : Kˣ := Units.mk0 _ hδK with hδu
  refine ⟨α₀ * δu, ?_, ?_⟩
  · intro v hv
    have hcomp : ((x * (prin K (α₀ * δu))⁻¹ : 𝕀K) : 𝔸K).2 v =
        ((y : 𝕀K) : 𝔸K).2 v * (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K δ))⁻¹ := by
      rw [hy, prin_mul, mul_inv_rev, ← mul_assoc, mul_right_comm, Units.val_mul, snd_mul_apply, snd_units_inv,
        prin_snd, hδu, Units.val_mk0]
    have hδv1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K δ) - 1) ≤ exp (-(mult K 𝔣 v : ℤ)) :=
      valued_sub_one_le_of_mem K (Ideal.le_of_dvd (pow_mult_dvd K h𝔣 v) hδ1)
    have hδv : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K δ)) = 1 := by
      have hlt : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K δ) - 1) < 1 := by
        refine hδv1.trans_lt ?_
        rw [← exp_zero, exp_lt_exp, neg_lt_zero, Int.natCast_pos]
        exact Nat.pos_of_ne_zero ((mult_ne_zero_iff K h𝔣 v).mpr hv)
      have := Valuation.map_one_add_of_lt _ hlt
      rwa [add_sub_cancel] at this
    refine ⟨?_, ?_⟩
    · rw [hcomp, map_mul, map_inv₀, (hα₀ v hv).1, hδv, inv_one, mul_one]
    · rw [hcomp]
      exact unit_cong_div K (hα₀ v hv).2 hδv hδv1
  · intro w hw
    have hcomp : ((x * (prin K (α₀ * δu))⁻¹ : 𝕀K) : 𝔸K).1 w =
        ((y : 𝕀K) : 𝔸K).1 w * (((prin K δu : 𝕀K) : 𝔸K).1 w)⁻¹ := by
      rw [hy, prin_mul, mul_inv_rev, ← mul_assoc, mul_right_comm, Units.val_mul, fst_mul_apply, fst_units_inv]
    rw [hcomp, map_mul, map_inv₀, prin_fst, hδu, Units.val_mk0]
    set φ := InfinitePlace.embedding_of_isReal hw with hφ
    have hφδ0 : φ (algebraMap (𝓞 K) K δ) ≠ 0 := by rw [map_ne_zero]; exact hδK
    change 0 < r w hw * (φ (algebraMap (𝓞 K) K δ))⁻¹
    by_cases hneg : r w hw < 0
    · have hmem : φ ∈ Nset := ⟨w, hw, rfl, hneg⟩
      have hδneg : φ (algebraMap (𝓞 K) K δ) < 0 := (hδsign φ).mpr hmem
      exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.mpr hδneg)
    · have hpos : 0 < r w hw := lt_of_le_of_ne (not_lt.mp hneg) (hr0 w hw).symm
      have hnmem : φ ∉ Nset := by
        rintro ⟨w', hw', hφ', hneg'⟩
        have hww : w = w' := infinitePlace_eq_of_embedding_of_isReal_eq K hw hw' hφ'
        subst hww
        exact hneg hneg'
      have hδpos : 0 < φ (algebraMap (𝓞 K) K δ) :=
        lt_of_le_of_ne (not_lt.mp fun h => hnmem ((hδsign φ).mp h)) hφδ0.symm
      exact mul_pos hpos (inv_pos.mpr hδpos)

variable {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
  (hdepth : ∀ v : HeightOneSpectrum (𝓞 K), (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ →
    v.asIdeal ^ admissibleExpOfDegree K (Module.finrank K L) v ∣ 𝔣)

include h𝔣 hdepth

theorem exists_psi'_eq (x : 𝕀K) :
    ∃ I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ, I ∈ coprimeToModulus K 𝔣 ∧ psi' K L I = QuotientGroup.mk x := by
  obtain ⟨α, hfin, harch⟩ := exists_adjuster K h𝔣 x
  set y : 𝕀K := x * (prin K α)⁻¹ with hy
  set I : (FractionalIdeal ((𝓞 K)⁰) K)ˣ := fadContentHom K (projFin K y) with hI
  have hord : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((y : 𝕀K) : 𝔸K).2 v) = exp (-placeOrd K (projFin K y) v) := by
    intro v
    rw [placeOrd, neg_neg, exp_log (valued_ne_zero_of_unit K _ v)]
    rfl
  have hfinsupp : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, placeOrd K (projFin K y) v = 0 := by
    rw [Filter.eventually_cofinite]
    exact finite_support_placeOrd K (projFin K y)
  have hIval : (I : FractionalIdeal ((𝓞 K)⁰) K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) ^ placeOrd K (projFin K y) v := by
    rw [hI]
    change ((∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ placeOrd K (projFin K y) v :
      (FractionalIdeal ((𝓞 K)⁰) K)ˣ) : FractionalIdeal ((𝓞 K)⁰) K) = _
    rw [← Units.coeHom_apply, MonoidHom.map_finprod]
    · refine finprod_congr fun v => ?_
      rw [map_zpow, Units.coeHom_apply, primeUnit_val]
    · refine (finite_support_placeOrd K (projFin K y)).subset fun v hv => ?_
      simp only [Function.mem_mulSupport, ne_eq] at hv
      rw [Function.mem_support]
      intro h; exact hv (by rw [h, zpow_zero])
  have hcount : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v (I : FractionalIdeal ((𝓞 K)⁰) K) = placeOrd K (projFin K y) v := by
    intro v; rw [hIval, FractionalIdeal.count_finprod K v _ hfinsupp]
  refine ⟨I, ?_, ?_⟩
  · rw [mem_coprimeToModulus_iff]
    intro v hv
    rw [hcount, placeOrd_eq_zero_iff]
    exact (hfin v hv).1
  · rw [psi'_apply]
    set C : 𝕀K := contentIdele K (I : FractionalIdeal ((𝓞 K)⁰) K) with hC

    have hu : y * C⁻¹ ∈ (genuineBaseChange K L).idelicNorm.range := by
      refine mem_range_idelicNorm K L h𝔣 hdepth _ ?_ ?_ ?_
      · intro v
        rw [Units.val_mul, snd_mul_apply, snd_units_inv, map_mul, map_inv₀, hord, hC, valued_contentIdele, hcount,
          ← exp_neg, ← exp_add, neg_neg, neg_add_cancel, exp_zero]
      · intro v hv
        have h0 : placeOrd K (projFin K y) v = 0 := (placeOrd_eq_zero_iff K _ v).mpr (hfin v hv).1
        have hCv : ((C : 𝕀K) : 𝔸K).2 v = 1 := by
          rw [hC, contentIdele_snd, hcount, h0, zpow_zero, Units.val_one]
        rw [Units.val_mul, snd_mul_apply, snd_units_inv, hCv, inv_one, mul_one]
        exact (hfin v hv).2
      · intro w hw
        rw [Units.val_mul, fst_mul_apply, fst_units_inv, hC, contentIdele_fst,
          show (1 : InfiniteAdeleRing K) w = 1 from rfl, inv_one, mul_one]
        exact harch w hw
    have h1 : (QuotientGroup.mk x : NormQuot K L) = QuotientGroup.mk y := by
      rw [hy, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        (QuotientGroup.eq_one_iff _).mpr (principal_mem_normSubgroup K L α), inv_one]
      exact (mul_one (QuotientGroup.mk x : NormQuot K L)).symm
    rw [h1, eq_comm, QuotientGroup.eq]
    have h2 := (normSubgroup K L).inv_mem (norm_mem_normSubgroup K L hu)
    rw [mul_inv_rev, inv_inv, mul_comm] at h2
    exact h2

end Surj

section Main

theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    (principalIdeles (𝓞 K) K ⊔ (genuineBaseChange K L).idelicNorm.range).index ∣ Module.finrank K L := by
  classical
  set n := Module.finrank K L with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'

  obtain ⟨𝔣, h𝔣, hdepth, -⟩ := exists_modulus K L (admissibleExpOfDegree K n)
  have hadm : IsAdmissibleModulusOfDegree K L n 𝔣 := ⟨h𝔣, hdepth⟩

  have hexp : ∀ x : L ≃ₐ[K] L, x ^ n = 1 := fun x => by
    rw [hn, ← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  obtain ⟨hsurj, hker⟩ :=
    LanglandsTunnell.Artin.artinSymbol_surjective_and_ker_eq_normRaySubgroup_of_pow_eq_one_of_isAdmissibleModulusOfDegree
      K L n hn0 hexp 𝔣 hadm
  have hidx : (normRaySubgroup K L 𝔣).index = n := by
    rw [← hker, Subgroup.index, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hn,
      ← IsGalois.card_aut_eq_finrank]

  set ψ : ↥(coprimeToModulus K 𝔣) →* NormQuot K L := (psi' K L).comp (coprimeToModulus K 𝔣).subtype with hψ
  have hψsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨I, hI, hIx⟩ := exists_psi'_eq K L h𝔣 hdepth x
    exact ⟨⟨I, hI⟩, hIx⟩
  have hle : normRaySubgroup K L 𝔣 ≤ ψ.ker := normRaySubgroup_le_ker K L h𝔣 hdepth
  have hcard : (normSubgroup K L).index = ψ.ker.index := by
    rw [Subgroup.index, Subgroup.index]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv).symm
  change (normSubgroup K L).index ∣ n
  rw [hcard, ← hidx]
  exact Subgroup.index_dvd_of_le hle

end Main

end R3HC2

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] :
    (M4aHerbrand.principalIdeles (NumberField.RingOfIntegers K) K ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range).index ∣ Module.finrank K L :=
  R3HC2.main K L

end S_NumberField_ideleClass_normCoset_index_dvd_finrank
end P2MW
export P2MW.S_NumberField_ideleClass_normCoset_index_dvd_finrank (solution)

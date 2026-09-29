-- Prove2me | solution 1 for ModularCurve.correspondence_heckeAlphaC_heckeBetaC_correspondence_heckeAlphaC_heckeBetaC_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/da2e5904-5d16-55da-9172-c5814d0422dc

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_correspondence
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_Divisor_correspondence_congr
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_separableAlong_heckeAlphaC_heckeBetaC
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Theorems.Thm_ModularCurve_finiteAlong_heckeBetaC
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaC
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_correspondence_heckeAlphaC_heckeBetaC_correspondence_heckeAlphaC_heckeBetaC_comm
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option Elab.async false
set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace CommAux

section Generic

variable {k : Type*} [Field k]

private theorem isIntegral_of_finiteAlong {F F' : Type*} [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hfin : FiniteAlong k φ) : φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := hfin
  exact (Algebra.IsIntegral.of_finite F F').isIntegral

private noncomputable def substLeg (s : ℕ) [NeZero s] (S T : IntermediateField k (LaurentSeries k))
    (hST : S.map (qExpandAlgC k s) ≤ T) : S →ₐ[k] T :=
  (IntermediateField.inclusion hST).comp (IntermediateField.equivMap S (qExpandAlgC k s)).toAlgHom

private theorem coe_substLeg (s : ℕ) [NeZero s] (S T : IntermediateField k (LaurentSeries k))
    (hST : S.map (qExpandAlgC k s) ≤ T) (x : S) :
    (substLeg s S T hST x : LaurentSeries k) = qExpand k s (x : LaurentSeries k) := rfl

private theorem modularFunctionFieldC_congr {n n' : ℕ} [NeZero n] [NeZero n'] (e : n = n') :
    modularFunctionFieldC k n = modularFunctionFieldC k n' := by
  subst e
  rfl

end Generic

section Concrete

variable {k : Type*} [Field k] (q' : ℕ) [Fact q'.Prime] [CharP k q'] (N ℓ ℓ' : ℕ) [NeZero N] [NeZero ℓ] [NeZero ℓ']

omit [Fact q'.Prime] in

private theorem roof_eq_modularFunctionFieldC_mul (M p : ℕ) [NeZero M] [NeZero p] (h : ¬ q' ∣ M * p) :
    charLDegeneracyRoof k M p = modularFunctionFieldC k (M * p) :=
  (charLDegeneracyRoof_eq_modularFunctionFieldFullC_mul k q' M p h).trans
    (modularFunctionFieldC_eq_modularFunctionFieldFullC k q' (M * p) h).symm

omit [Fact q'.Prime] in

private theorem roof_le_bigRoof (h₁ : ¬ q' ∣ N * ℓ') :
    charLDegeneracyRoof k N ℓ' ≤ charLDegeneracyRoof k (N * ℓ') ℓ := by
  rw [roof_eq_modularFunctionFieldC_mul q' N ℓ' h₁]
  exact modularFunctionFieldC_le_charLDegeneracyRoof k (N * ℓ') ℓ

omit [Fact q'.Prime] in

private theorem roof_le_bigRoof' (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    charLDegeneracyRoof k N ℓ ≤ charLDegeneracyRoof k (N * ℓ') ℓ := by
  rw [roof_eq_modularFunctionFieldC_mul q' N ℓ h₂, roof_eq_modularFunctionFieldC_mul q' (N * ℓ') ℓ h₃]
  have h := modularFunctionFieldC_le_charLDegeneracyRoof k (N * ℓ) ℓ'
  rw [roof_eq_modularFunctionFieldC_mul q' (N * ℓ) ℓ' h₄] at h
  exact h.trans_eq (modularFunctionFieldC_congr (Nat.mul_right_comm N ℓ ℓ'))

omit [Fact q'.Prime] in

private theorem map_qExpand_le_bigRoof (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    (charLDegeneracyRoof k N ℓ).map (qExpandAlgC k ℓ') ≤ charLDegeneracyRoof k (N * ℓ') ℓ := by
  rw [roof_eq_modularFunctionFieldC_mul q' N ℓ h₂, roof_eq_modularFunctionFieldC_mul q' (N * ℓ') ℓ h₃]
  have h := qExpand_image_le_charLDegeneracyRoof k (N * ℓ) ℓ'
  rw [roof_eq_modularFunctionFieldC_mul q' (N * ℓ) ℓ' h₄] at h
  exact h.trans_eq (modularFunctionFieldC_congr (Nat.mul_right_comm N ℓ ℓ'))

omit [Fact q'.Prime] in

private theorem map_qExpand_le_bigRoof' (h₁ : ¬ q' ∣ N * ℓ') :
    (charLDegeneracyRoof k N ℓ').map (qExpandAlgC k ℓ) ≤ charLDegeneracyRoof k (N * ℓ') ℓ := by
  rw [roof_eq_modularFunctionFieldC_mul q' N ℓ' h₁]
  exact qExpand_image_le_charLDegeneracyRoof k (N * ℓ') ℓ

private noncomputable def inclLeg₁ (h₁ : ¬ q' ∣ N * ℓ') :
    charLDegeneracyRoof k N ℓ' →ₐ[k] charLDegeneracyRoof k (N * ℓ') ℓ :=
  IntermediateField.inclusion (roof_le_bigRoof q' N ℓ ℓ' h₁)

private noncomputable def inclLeg₂ (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    charLDegeneracyRoof k N ℓ →ₐ[k] charLDegeneracyRoof k (N * ℓ') ℓ :=
  IntermediateField.inclusion (roof_le_bigRoof' q' N ℓ ℓ' h₂ h₃ h₄)

private noncomputable def substLeg₁ (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    charLDegeneracyRoof k N ℓ →ₐ[k] charLDegeneracyRoof k (N * ℓ') ℓ :=
  substLeg ℓ' _ _ (map_qExpand_le_bigRoof q' N ℓ ℓ' h₂ h₃ h₄)

private noncomputable def substLeg₂ (h₁ : ¬ q' ∣ N * ℓ') :
    charLDegeneracyRoof k N ℓ' →ₐ[k] charLDegeneracyRoof k (N * ℓ') ℓ :=
  substLeg ℓ _ _ (map_qExpand_le_bigRoof' q' N ℓ ℓ' h₁)

variable {q' N ℓ ℓ'}

private theorem not_dvd_left_of_not_dvd_mul {a b c : ℕ} (h : ¬ a ∣ b * c) : ¬ a ∣ b :=
  fun hb => h (hb.mul_right c)

private theorem filter_squarefree_divisors_mul_of_dvd (m ℓ : ℕ) (hm : m ≠ 0) (hℓ : ℓ.Prime) (h : ℓ ∣ m) :
    (m * ℓ).divisors.filter Squarefree = m.divisors.filter Squarefree := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.mul_ne_zero_iff, ne_eq, hm, hℓ.ne_zero,
    not_false_eq_true, and_true, and_self]
  constructor
  · rintro ⟨hd, hsq⟩
    refine ⟨?_, hsq⟩
    have hd0 : d ≠ 0 := fun h0 => by simp [h0] at hsq
    rw [← Nat.factorization_le_iff_dvd hd0 hm]
    intro p
    rcases eq_or_ne p ℓ with rfl | hp
    · calc d.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hd0).1 hsq p
        _ ≤ m.factorization p := hℓ.factorization_pos_of_dvd hm h
    · have := (Nat.factorization_le_iff_dvd hd0 (Nat.mul_ne_zero hm hℓ.ne_zero)).2 hd p
      rwa [Nat.factorization_mul hm hℓ.ne_zero, Finsupp.add_apply, hℓ.factorization, Finsupp.single_apply,
        if_neg (Ne.symm hp), add_zero] at this
  · rintro ⟨hd, hsq⟩
    exact ⟨hd.mul_right ℓ, hsq⟩

private theorem filter_squarefree_divisors_mul_of_not_dvd (m ℓ : ℕ) (hm : m ≠ 0) (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ m) :
    (m * ℓ).divisors.filter Squarefree
      = m.divisors.filter Squarefree ∪ (m.divisors.filter Squarefree).image (· * ℓ) := by
  have hcop : Nat.Coprime ℓ m := (Nat.Prime.coprime_iff_not_dvd hℓ).2 h
  ext d
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Nat.mem_divisors, Nat.mul_ne_zero_iff, ne_eq,
    hm, hℓ.ne_zero, not_false_eq_true, and_true, and_self]
  constructor
  · rintro ⟨hd, hsq⟩
    by_cases hℓd : ℓ ∣ d
    · right
      obtain ⟨a, rfl⟩ := hℓd
      refine ⟨a, ⟨Nat.dvd_of_mul_dvd_mul_left hℓ.pos (by rwa [Nat.mul_comm m ℓ] at hd),
        hsq.squarefree_of_dvd (dvd_mul_left a ℓ)⟩, Nat.mul_comm a ℓ⟩
    · left
      exact ⟨((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓd).symm.dvd_of_dvd_mul_right hd, hsq⟩
  · rintro (⟨hd, hsq⟩ | ⟨a, ⟨ha, hsqa⟩, rfl⟩)
    · exact ⟨hd.mul_right ℓ, hsq⟩
    · refine ⟨mul_dvd_mul_right ha ℓ, ?_⟩
      exact (Nat.squarefree_mul (Nat.Coprime.coprime_dvd_left ha hcop.symm)).2 ⟨hsqa, hℓ.squarefree⟩

private theorem dedekindPsi_mul_prime (m ℓ : ℕ) (hm : m ≠ 0) (hℓ : ℓ.Prime) :
    dedekindPsi (m * ℓ) = dedekindPsi m * (if ℓ ∣ m then ℓ else ℓ + 1) := by
  have hterm : ∀ d ∈ m.divisors.filter Squarefree, m * ℓ / d = m / d * ℓ := by
    intro d hd
    have hdm : d ∣ m := (Nat.mem_divisors.1 (Finset.mem_filter.1 hd).1).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_filter.1 hd).1
    obtain ⟨e, rfl⟩ := hdm
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ hdpos, Nat.mul_div_cancel_left _ hdpos]
  unfold dedekindPsi
  split_ifs with hdvd
  · rw [filter_squarefree_divisors_mul_of_dvd m ℓ hm hℓ hdvd, Finset.sum_mul]
    exact Finset.sum_congr rfl hterm
  · have hdisj : Disjoint (m.divisors.filter Squarefree) ((m.divisors.filter Squarefree).image (· * ℓ)) := by
      rw [Finset.disjoint_left]
      intro d hdS hdI
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hdI
      exact hdvd ((dvd_mul_left ℓ a).trans (Nat.mem_divisors.1 (Finset.mem_filter.1 hdS).1).1)
    rw [filter_squarefree_divisors_mul_of_not_dvd m ℓ hm hℓ hdvd, Finset.sum_union hdisj,
      Finset.sum_image fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hℓ.pos hab, Nat.mul_add, Nat.mul_one,
      Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl hterm
    · exact Finset.sum_congr rfl fun d _ => Nat.mul_div_mul_right m d hℓ.pos

private theorem dedekindPsi_ne_zero (m : ℕ) (hm : m ≠ 0) : dedekindPsi m ≠ 0 := by
  have h1 : (1 : ℕ) ∈ m.divisors.filter Squarefree :=
    Finset.mem_filter.2 ⟨Nat.one_mem_divisors.2 hm, squarefree_one⟩
  have hle : m / 1 ≤ dedekindPsi m := by
    unfold dedekindPsi
    exact Finset.single_le_sum (f := fun d => m / d) (fun _ _ => Nat.zero_le _) h1
  rw [Nat.div_one] at hle
  exact Nat.pos_iff_ne_zero.1 ((Nat.pos_of_ne_zero hm).trans_le hle)

private theorem dvd_mul_iff_of_ne {M ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') :
    ℓ ∣ M * ℓ' ↔ ℓ ∣ M := by
  constructor
  · intro hd
    rcases (Nat.Prime.dvd_mul hℓ).1 hd with h | h
    · exact h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hℓ').1 h) hne
  · exact fun hd => hd.mul_right ℓ'

section DegreeGeneric

variable {k : Type*} [Field k]

private theorem finrankAlong_inclusion {E : Type*} [Field E] [Algebra k E] {A B : IntermediateField k E}
    (h : A ≤ B) : finrankAlong k (IntermediateField.inclusion h) = A.relfinrank B := by
  rw [finrankAlong_eq_relfinrank_fieldRange]
  have hval : B.val.comp (IntermediateField.inclusion h) = A.val := by
    ext x
    rfl
  rw [hval, IntermediateField.fieldRange_val]

private theorem finiteAlong_inclusion_congr {E : Type*} [Field E] [Algebra k E]
    {A A' B B' : IntermediateField k E} (eA : A = A') (eB : B = B') (h : A ≤ B) (h' : A' ≤ B')
    (hf : FiniteAlong k (IntermediateField.inclusion h)) : FiniteAlong k (IntermediateField.inclusion h') := by
  subst eA
  subst eB
  exact hf

private theorem separableAlong_inclusion_congr {E : Type*} [Field E] [Algebra k E]
    {A A' B B' : IntermediateField k E} (eA : A = A') (eB : B = B') (h : A ≤ B) (h' : A' ≤ B')
    (hs : SeparableAlong k (IntermediateField.inclusion h)) :
    SeparableAlong k (IntermediateField.inclusion h') := by
  subst eA
  subst eB
  exact hs

private theorem separableAlong_comp {F F' F'' : Type*} [Field F] [Field F'] [Field F''] [Algebra k F]
    [Algebra k F'] [Algebra k F''] (φ : F →ₐ[k] F') (χ : F' →ₐ[k] F'') (hφ : SeparableAlong k φ)
    (hχ : SeparableAlong k χ) : SeparableAlong k (χ.comp φ) := by
  letI := algebraAlong φ
  letI := algebraAlong χ
  letI := algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsSeparable F F' := hφ
  haveI : Algebra.IsSeparable F' F'' := hχ
  exact Algebra.IsSeparable.trans F F' F''

end DegreeGeneric

section DegreeFormula

variable {k : Type*} [Field k] (q' : ℕ) [Fact q'.Prime] [CharP k q']

private theorem relfinrank_modularFunctionFieldC_mul (M p : ℕ) [NeZero M] [NeZero p] (hp : p.Prime)
    (hq'M : ¬ q' ∣ M) (hq'Mp : ¬ q' ∣ M * p) :
    (modularFunctionFieldC k M).relfinrank (modularFunctionFieldC k (M * p)) = if p ∣ M then p else p + 1 := by
  have hJ : IntermediateField.adjoin k {(jqModC k : LaurentSeries k)} ≤ modularFunctionFieldC k M := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact jqModC_mem k M
  have hMp : modularFunctionFieldC k M ≤ modularFunctionFieldC k (M * p) := by
    have h := modularFunctionFieldC_le_charLDegeneracyRoof k M p
    rwa [roof_eq_modularFunctionFieldC_mul q' M p hq'Mp] at h
  have htower := IntermediateField.relfinrank_mul_relfinrank hJ hMp
  rw [relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k M q' hq'M,
    relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k (M * p) q' hq'Mp,
    dedekindPsi_mul_prime M p (NeZero.ne M) hp] at htower
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (dedekindPsi_ne_zero M (NeZero.ne M))) htower

private theorem finrankAlong_heckeAlphaC_eq (M p : ℕ) [NeZero M] [NeZero p] (hp : p.Prime) (hq'M : ¬ q' ∣ M)
    (hq'Mp : ¬ q' ∣ M * p) : finrankAlong k (heckeAlphaC k M p) = if p ∣ M then p else p + 1 := by
  show finrankAlong k (IntermediateField.inclusion (modularFunctionFieldC_le_charLDegeneracyRoof k M p)) = _
  rw [finrankAlong_inclusion, roof_eq_modularFunctionFieldC_mul q' M p hq'Mp,
    relfinrank_modularFunctionFieldC_mul q' M p hp hq'M hq'Mp]

end DegreeFormula

omit [Fact q'.Prime] in

private theorem bigRoof_eq (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    charLDegeneracyRoof k (N * ℓ) ℓ' = charLDegeneracyRoof k (N * ℓ') ℓ := by
  rw [roof_eq_modularFunctionFieldC_mul q' (N * ℓ) ℓ' h₄, roof_eq_modularFunctionFieldC_mul q' (N * ℓ') ℓ h₃]
  exact modularFunctionFieldC_congr (Nat.mul_right_comm N ℓ ℓ')

omit [Fact q'.Prime] in

private theorem finiteAlong_comp₁ (hℓ' : ℓ'.Prime) (h₁ : ¬ q' ∣ N * ℓ') :
    FiniteAlong k ((inclLeg₁ q' N ℓ ℓ' h₁).comp (heckeBetaC k N ℓ')) := by
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  refine finiteAlong_comp _ _ (finiteAlong_heckeBetaC k N ℓ') ?_
  exact finiteAlong_inclusion_congr (roof_eq_modularFunctionFieldC_mul q' N ℓ' h₁).symm rfl
    (modularFunctionFieldC_le_charLDegeneracyRoof k (N * ℓ') ℓ) (roof_le_bigRoof q' N ℓ ℓ' h₁)
    (finiteAlong_heckeAlphaC k (N * ℓ') ℓ)

omit [Fact q'.Prime] in

private theorem finiteAlong_comp₂ (hℓ : ℓ.Prime) (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ)
    (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    FiniteAlong k ((inclLeg₂ q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeBetaC k N ℓ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  refine finiteAlong_comp _ _ (finiteAlong_heckeBetaC k N ℓ) ?_
  exact finiteAlong_inclusion_congr (roof_eq_modularFunctionFieldC_mul q' N ℓ h₂).symm (bigRoof_eq h₃ h₄)
    (modularFunctionFieldC_le_charLDegeneracyRoof k (N * ℓ) ℓ') (roof_le_bigRoof' q' N ℓ ℓ' h₂ h₃ h₄)
    (finiteAlong_heckeAlphaC k (N * ℓ) ℓ')

private theorem separableAlong_comp₁ (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (h₁ : ¬ q' ∣ N * ℓ') (h₃ : ¬ q' ∣ N * ℓ' * ℓ)
    [IsAlgClosed k] : SeparableAlong k ((inclLeg₁ q' N ℓ ℓ' h₁).comp (heckeBetaC k N ℓ')) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  refine separableAlong_comp _ _ (separableAlong_heckeAlphaC_heckeBetaC k N ℓ' h₁).2 ?_
  exact separableAlong_inclusion_congr (roof_eq_modularFunctionFieldC_mul q' N ℓ' h₁).symm rfl
    (modularFunctionFieldC_le_charLDegeneracyRoof k (N * ℓ') ℓ) (roof_le_bigRoof q' N ℓ ℓ' h₁)
    (separableAlong_heckeAlphaC_heckeBetaC k (N * ℓ') ℓ h₃).1

private theorem separableAlong_comp₂ (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ)
    (h₄ : ¬ q' ∣ N * ℓ * ℓ') [IsAlgClosed k] :
    SeparableAlong k ((inclLeg₂ q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeBetaC k N ℓ)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fact ℓ'.Prime := ⟨hℓ'⟩
  refine separableAlong_comp _ _ (separableAlong_heckeAlphaC_heckeBetaC k N ℓ h₂).2 ?_
  exact separableAlong_inclusion_congr (roof_eq_modularFunctionFieldC_mul q' N ℓ h₂).symm (bigRoof_eq h₃ h₄)
    (modularFunctionFieldC_le_charLDegeneracyRoof k (N * ℓ) ℓ') (roof_le_bigRoof' q' N ℓ ℓ' h₂ h₃ h₄)
    (separableAlong_heckeAlphaC_heckeBetaC k (N * ℓ) ℓ' h₄).1

private theorem finrankAlong_comp₁ (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (h₁ : ¬ q' ∣ N * ℓ')
    (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) :
    finrankAlong k ((inclLeg₁ q' N ℓ ℓ' h₁).comp (heckeBetaC k N ℓ'))
      = finrankAlong k (heckeBetaC k N ℓ') * finrankAlong k (heckeAlphaC k N ℓ) := by
  rw [finrankAlong_comp]
  congr 1
  show finrankAlong k (IntermediateField.inclusion (roof_le_bigRoof q' N ℓ ℓ' h₁)) = _
  rw [finrankAlong_inclusion, roof_eq_modularFunctionFieldC_mul q' N ℓ' h₁,
    roof_eq_modularFunctionFieldC_mul q' (N * ℓ') ℓ h₃,
    relfinrank_modularFunctionFieldC_mul q' (N * ℓ') ℓ hℓ (not_dvd_left_of_not_dvd_mul h₃) h₃,
    finrankAlong_heckeAlphaC_eq q' N ℓ hℓ (not_dvd_left_of_not_dvd_mul h₁) h₂]
  simp only [dvd_mul_iff_of_ne hℓ hℓ' hne]

private theorem finrankAlong_comp₂ (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (h₁ : ¬ q' ∣ N * ℓ')
    (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    finrankAlong k ((inclLeg₂ q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeBetaC k N ℓ))
      = finrankAlong k (heckeBetaC k N ℓ) * finrankAlong k (heckeAlphaC k N ℓ') := by
  rw [finrankAlong_comp]
  congr 1
  show finrankAlong k (IntermediateField.inclusion (roof_le_bigRoof' q' N ℓ ℓ' h₂ h₃ h₄)) = _
  rw [finrankAlong_inclusion, ← bigRoof_eq h₃ h₄, roof_eq_modularFunctionFieldC_mul q' N ℓ h₂,
    roof_eq_modularFunctionFieldC_mul q' (N * ℓ) ℓ' h₄,
    relfinrank_modularFunctionFieldC_mul q' (N * ℓ) ℓ' hℓ' (not_dvd_left_of_not_dvd_mul h₄) h₄,
    finrankAlong_heckeAlphaC_eq q' N ℓ' hℓ' (not_dvd_left_of_not_dvd_mul h₂) h₁]
  simp only [dvd_mul_iff_of_ne hℓ' hℓ hne.symm]

omit [Fact q'.Prime] in
private theorem coe_inclLeg₁ (h₁ : ¬ q' ∣ N * ℓ') (x : charLDegeneracyRoof k N ℓ') :
    (inclLeg₁ (k := k) q' N ℓ ℓ' h₁ x : LaurentSeries k) = (x : LaurentSeries k) :=
  IntermediateField.coe_inclusion (roof_le_bigRoof (k := k) q' N ℓ ℓ' h₁) x

omit [Fact q'.Prime] in
private theorem coe_inclLeg₂ (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ')
    (x : charLDegeneracyRoof k N ℓ) :
    (inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄ x : LaurentSeries k) = (x : LaurentSeries k) :=
  IntermediateField.coe_inclusion (roof_le_bigRoof' (k := k) q' N ℓ ℓ' h₂ h₃ h₄) x

omit [Fact q'.Prime] in
private theorem coe_substLeg₁ (h₂ : ¬ q' ∣ N * ℓ) (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ')
    (x : charLDegeneracyRoof k N ℓ) :
    (substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄ x : LaurentSeries k) = qExpand k ℓ' (x : LaurentSeries k) :=
  coe_substLeg ℓ' _ _ (map_qExpand_le_bigRoof (k := k) q' N ℓ ℓ' h₂ h₃ h₄) x

omit [Fact q'.Prime] in
private theorem coe_substLeg₂ (h₁ : ¬ q' ∣ N * ℓ') (x : charLDegeneracyRoof k N ℓ') :
    (substLeg₂ (k := k) q' N ℓ ℓ' h₁ x : LaurentSeries k) = qExpand k ℓ (x : LaurentSeries k) :=
  coe_substLeg ℓ _ _ (map_qExpand_le_bigRoof' (k := k) q' N ℓ ℓ' h₁) x

omit [Fact q'.Prime] in

private theorem sq₁_comm (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    (substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeAlphaC k N ℓ)
      = (inclLeg₁ (k := k) q' N ℓ ℓ' h₁).comp (heckeBetaC k N ℓ') :=
  AlgHom.ext fun x => Subtype.ext <| by
    simp only [AlgHom.comp_apply, coe_substLeg₁, coe_inclLeg₁, coe_heckeAlphaC, coe_heckeBetaC]

omit [Fact q'.Prime] in

private theorem sq₂_comm (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    (substLeg₂ (k := k) q' N ℓ ℓ' h₁).comp (heckeAlphaC k N ℓ')
      = (inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeBetaC k N ℓ) :=
  AlgHom.ext fun x => Subtype.ext <| by
    simp only [AlgHom.comp_apply, coe_substLeg₂, coe_inclLeg₂, coe_heckeAlphaC, coe_heckeBetaC]

omit [Fact q'.Prime] in

private theorem alphaLeg_eq (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    (inclLeg₁ (k := k) q' N ℓ ℓ' h₁).comp (heckeAlphaC k N ℓ')
      = (inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeAlphaC k N ℓ) :=
  AlgHom.ext fun x => Subtype.ext <| by
    simp only [AlgHom.comp_apply, coe_inclLeg₁, coe_inclLeg₂, coe_heckeAlphaC]

omit [Fact q'.Prime] in

private theorem betaLeg_eq (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    (substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeBetaC k N ℓ)
      = (substLeg₂ (k := k) q' N ℓ ℓ' h₁).comp (heckeBetaC k N ℓ') :=
  AlgHom.ext fun x => Subtype.ext <| by
    simp only [AlgHom.comp_apply, coe_substLeg₁, coe_substLeg₂, coe_heckeBetaC]
    rw [qExpand_qExpand, qExpand_qExpand]
    simp only [Nat.mul_comm ℓ' ℓ]

private theorem inv_mem_of_finiteAlong {F T : Type*} [Field F] [Field T] [Algebra k F] [Algebra k T]
    (c : F →ₐ[k] T) (hfin : FiniteAlong k c) (A : Subalgebra k T) (hc : ∀ x, c x ∈ A) :
    ∀ a ∈ A, a⁻¹ ∈ A := by
  letI := algebraAlong c
  haveI : Module.Finite F T := hfin
  intro a ha
  let A' : Subalgebra F T := { A with algebraMap_mem' := fun x => hc x }
  have halg : IsAlgebraic F a := (Algebra.IsAlgebraic.of_finite F T).isAlgebraic a
  exact A'.inv_mem_of_algebraic (x := ⟨a, ha⟩) halg

private theorem eq_top_of_inv_mem_of_generators (Z : IntermediateField k (LaurentSeries k)) (A : Subalgebra k Z)
    (hinv : ∀ a ∈ A, a⁻¹ ∈ A) (S₀ : Set (LaurentSeries k)) (hZ : Z ≤ IntermediateField.adjoin k S₀)
    (hS₀ : ∀ s ∈ S₀, ∃ a ∈ A, (a : LaurentSeries k) = s) : A = ⊤ := by
  let E : IntermediateField k Z := A.toIntermediateField hinv
  have hmap : IntermediateField.adjoin k S₀ ≤ E.map Z.val := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro s hs
    obtain ⟨a, ha, rfl⟩ := hS₀ s hs
    exact ⟨a, ha, rfl⟩
  have hE : E = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨e, he, hez⟩ := hmap (hZ z.2)
    exact (Subtype.ext hez : e = z) ▸ he
  have := congrArg IntermediateField.toSubalgebra hE
  simpa [E] using this

omit [Fact q'.Prime] in

private theorem adjoin_ranges₁ (hℓ' : ℓ'.Prime) (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    Algebra.adjoin k
      (Set.range ⇑(inclLeg₁ (k := k) q' N ℓ ℓ' h₁) ∪ Set.range ⇑(substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄)) = ⊤ := by
  refine eq_top_of_inv_mem_of_generators _ _
    (inv_mem_of_finiteAlong ((inclLeg₁ (k := k) q' N ℓ ℓ' h₁).comp (heckeBetaC k N ℓ'))
      (finiteAlong_comp₁ (k := k) (ℓ := ℓ) hℓ' h₁) _
      fun x => Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩))
    {jqModC k, jqNModC k (N * ℓ' * ℓ)} (roof_eq_modularFunctionFieldC_mul q' (N * ℓ') ℓ h₃).le ?_
  intro s hs
  rcases hs with rfl | rfl
  · refine ⟨inclLeg₁ (k := k) q' N ℓ ℓ' h₁ ⟨jqModC k, IntermediateField.subset_adjoin k _ (by simp)⟩,
      Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩), ?_⟩
    simp only [coe_inclLeg₁]
  · refine ⟨substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄ ⟨jqNModC k (N * ℓ), IntermediateField.subset_adjoin k _ (by simp)⟩,
      Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩), ?_⟩
    simp only [coe_substLeg₁]
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm, Nat.mul_left_comm]

omit [Fact q'.Prime] in

private theorem adjoin_ranges₂ (hℓ : ℓ.Prime) (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') :
    Algebra.adjoin k
      (Set.range ⇑(inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄) ∪ Set.range ⇑(substLeg₂ (k := k) q' N ℓ ℓ' h₁)) = ⊤ := by
  refine eq_top_of_inv_mem_of_generators _ _
    (inv_mem_of_finiteAlong ((inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).comp (heckeBetaC k N ℓ))
      (finiteAlong_comp₂ (k := k) hℓ h₂ h₃ h₄) _
      fun x => Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩))
    {jqModC k, jqNModC k (N * ℓ' * ℓ)} (roof_eq_modularFunctionFieldC_mul q' (N * ℓ') ℓ h₃).le ?_
  intro s hs
  rcases hs with rfl | rfl
  · refine ⟨inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄ ⟨jqModC k, IntermediateField.subset_adjoin k _ (by simp)⟩,
      Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩), ?_⟩
    simp only [coe_inclLeg₂]
  · refine ⟨substLeg₂ (k := k) q' N ℓ ℓ' h₁ ⟨jqNModC k (N * ℓ'), IntermediateField.subset_adjoin k _ (by simp)⟩,
      Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩), ?_⟩
    simp only [coe_substLeg₂]
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm, Nat.mul_left_comm]

private theorem hex₁ (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') [IsAlgClosed k]
    [HasPrincipalDivisors k (charLDegeneracyRoof k N ℓ)] [HasPrincipalDivisors k (charLDegeneracyRoof k (N * ℓ') ℓ)]
    (hα : HeckeAlphaCIntegral k N ℓ) (hβ' : HeckeBetaCIntegral k N ℓ')
    (hu : (substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom.IsIntegral)
    (hu' : (inclLeg₁ (k := k) q' N ℓ ℓ' h₁).toRingHom.IsIntegral)
    (D : Divisor k (charLDegeneracyRoof k N ℓ')) :
    Divisor.pullbackAlong (heckeAlphaC k N ℓ) hα (Divisor.pushforwardAlong (heckeBetaC k N ℓ') hβ' D)
      = Divisor.pushforwardAlong (substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄) hu
          (Divisor.pullbackAlong (inclLeg₁ (k := k) q' N ℓ ℓ' h₁) hu' D) :=
  Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong (heckeBetaC k N ℓ') (heckeAlphaC k N ℓ)
    (inclLeg₁ (k := k) q' N ℓ ℓ' h₁) (substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄) hβ' hα hu' hu (sq₁_comm h₁ h₂ h₃ h₄)
    (finiteAlong_comp₁ (k := k) (ℓ := ℓ) hℓ' h₁) (separableAlong_comp₁ hℓ hℓ' h₁ h₃) (adjoin_ranges₁ hℓ' h₁ h₂ h₃ h₄)
    (finrankAlong_comp₁ hℓ hℓ' hne h₁ h₂ h₃) D

private theorem hex₂ (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) (hne : ℓ ≠ ℓ') (h₁ : ¬ q' ∣ N * ℓ') (h₂ : ¬ q' ∣ N * ℓ)
    (h₃ : ¬ q' ∣ N * ℓ' * ℓ) (h₄ : ¬ q' ∣ N * ℓ * ℓ') [IsAlgClosed k]
    [HasPrincipalDivisors k (charLDegeneracyRoof k N ℓ')] [HasPrincipalDivisors k (charLDegeneracyRoof k (N * ℓ') ℓ)]
    (hα' : HeckeAlphaCIntegral k N ℓ') (hβ : HeckeBetaCIntegral k N ℓ)
    (hv : (substLeg₂ (k := k) q' N ℓ ℓ' h₁).toRingHom.IsIntegral)
    (hv' : (inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom.IsIntegral)
    (D : Divisor k (charLDegeneracyRoof k N ℓ)) :
    Divisor.pullbackAlong (heckeAlphaC k N ℓ') hα' (Divisor.pushforwardAlong (heckeBetaC k N ℓ) hβ D)
      = Divisor.pushforwardAlong (substLeg₂ (k := k) q' N ℓ ℓ' h₁) hv
          (Divisor.pullbackAlong (inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄) hv' D) :=
  Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong (heckeBetaC k N ℓ) (heckeAlphaC k N ℓ')
    (inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄) (substLeg₂ (k := k) q' N ℓ ℓ' h₁) hβ hα' hv' hv (sq₂_comm h₁ h₂ h₃ h₄)
    (finiteAlong_comp₂ (k := k) hℓ h₂ h₃ h₄) (separableAlong_comp₂ hℓ hℓ' h₂ h₃ h₄) (adjoin_ranges₂ hℓ h₁ h₂ h₃ h₄)
    (finrankAlong_comp₂ hℓ hℓ' hne h₁ h₂ h₃ h₄) D

private theorem not_dvd_mul_of_ne {q' M s : ℕ} (hq' : q'.Prime) (hs : s.Prime) (hM : ¬ q' ∣ M) (hsq' : s ≠ q') :
    ¬ q' ∣ M * s := fun h =>
  ((Nat.Prime.dvd_mul hq').mp h).elim hM fun h' => hsq' ((Nat.prime_dvd_prime_iff_eq hq' hs).mp h').symm

end Concrete

end CommAux

theorem solution
    (N ℓ ℓ' q' : ℕ) [NeZero N] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime) [Fact q'.Prime]
    (hℓq' : ℓ ≠ q') (hℓ'q' : ℓ' ≠ q') (hq'N : ¬ q' ∣ N)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
    ∀ [HasPrincipalDivisors k ↥(charLDegeneracyRoof k N ℓ)]
      [HasPrincipalDivisors k ↥(charLDegeneracyRoof k N ℓ')]
      (hα : HeckeAlphaCIntegral k N ℓ) (hβ : HeckeBetaCIntegral k N ℓ)
      (hα' : HeckeAlphaCIntegral k N ℓ') (hβ' : HeckeBetaCIntegral k N ℓ')
      (D : Divisor k ↥(modularFunctionFieldC k N)),
      Divisor.correspondence (heckeAlphaC k N ℓ) (heckeBetaC k N ℓ) hα hβ
          (Divisor.correspondence (heckeAlphaC k N ℓ') (heckeBetaC k N ℓ') hα' hβ' D)
        = Divisor.correspondence (heckeAlphaC k N ℓ') (heckeBetaC k N ℓ') hα' hβ'
            (Divisor.correspondence (heckeAlphaC k N ℓ) (heckeBetaC k N ℓ) hα hβ D) := by
  intro _hpd _hpd' hα hβ hα' hβ' D
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
  rcases eq_or_ne ℓ ℓ' with rfl | hne
  · rfl
  have hq' : q'.Prime := Fact.out
  have h₁ : ¬ q' ∣ N * ℓ' := CommAux.not_dvd_mul_of_ne hq' hℓ' hq'N hℓ'q'
  have h₂ : ¬ q' ∣ N * ℓ := CommAux.not_dvd_mul_of_ne hq' hℓ hq'N hℓq'
  have h₃ : ¬ q' ∣ N * ℓ' * ℓ := CommAux.not_dvd_mul_of_ne hq' hℓ h₁ hℓq'
  have h₄ : ¬ q' ∣ N * ℓ * ℓ' := CommAux.not_dvd_mul_of_ne hq' hℓ' h₂ hℓ'q'
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : HasPrincipalDivisors k (charLDegeneracyRoof k (N * ℓ') ℓ) :=
    hasPrincipalDivisors_charLDegeneracyRoof k (N * ℓ') ℓ
      (fun h0 => h₁ ((CharP.cast_eq_zero_iff k q' (N * ℓ')).mp h0))
      (fun h0 => h₂ (((CharP.cast_eq_zero_iff k q' ℓ).mp h0).trans (Nat.dvd_mul_left ℓ N)))
  have hc₁ := CommAux.isIntegral_of_finiteAlong _ (CommAux.finiteAlong_comp₁ (k := k) (ℓ := ℓ) hℓ' h₁)
  have hc₂ := CommAux.isIntegral_of_finiteAlong _ (CommAux.finiteAlong_comp₂ (k := k) hℓ h₂ h₃ h₄)
  have hu' : (CommAux.inclLeg₁ (k := k) q' N ℓ ℓ' h₁).toRingHom.IsIntegral :=
    RingHom.IsIntegral.tower_top (heckeBetaC k N ℓ').toRingHom (CommAux.inclLeg₁ (k := k) q' N ℓ ℓ' h₁).toRingHom hc₁
  have hv' : (CommAux.inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom.IsIntegral :=
    RingHom.IsIntegral.tower_top (heckeBetaC k N ℓ).toRingHom
      (CommAux.inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom hc₂
  have hu : (CommAux.substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom.IsIntegral := by
    have h := hc₁
    rw [← CommAux.sq₁_comm (k := k) h₁ h₂ h₃ h₄] at h
    exact RingHom.IsIntegral.tower_top (heckeAlphaC k N ℓ).toRingHom
      (CommAux.substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom h
  have hv : (CommAux.substLeg₂ (k := k) q' N ℓ ℓ' h₁).toRingHom.IsIntegral := by
    have h := hc₂
    rw [← CommAux.sq₂_comm (k := k) h₁ h₂ h₃ h₄] at h
    exact RingHom.IsIntegral.tower_top (heckeAlphaC k N ℓ').toRingHom
      (CommAux.substLeg₂ (k := k) q' N ℓ ℓ' h₁).toRingHom h
  have hA₁ := RingHom.IsIntegral.trans (heckeAlphaC k N ℓ').toRingHom
    (CommAux.inclLeg₁ (k := k) q' N ℓ ℓ' h₁).toRingHom hα' hu'
  have hB₁ := RingHom.IsIntegral.trans (heckeBetaC k N ℓ).toRingHom
    (CommAux.substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom hβ hu
  have hA₂ := RingHom.IsIntegral.trans (heckeAlphaC k N ℓ).toRingHom
    (CommAux.inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄).toRingHom hα hv'
  have hB₂ := RingHom.IsIntegral.trans (heckeBetaC k N ℓ').toRingHom
    (CommAux.substLeg₂ (k := k) q' N ℓ ℓ' h₁).toRingHom hβ' hv
  have orderA := Divisor.correspondence_correspondence (heckeAlphaC k N ℓ) (heckeBetaC k N ℓ) (heckeAlphaC k N ℓ')
    (heckeBetaC k N ℓ') (CommAux.substLeg₁ (k := k) q' N ℓ ℓ' h₂ h₃ h₄) (CommAux.inclLeg₁ (k := k) q' N ℓ ℓ' h₁)
    hα hβ hα' hβ' hu hu'
    hA₁ hB₁
    (CommAux.hex₁ hℓ hℓ' hne h₁ h₂ h₃ h₄ hα hβ' hu hu') D
  have orderB := Divisor.correspondence_correspondence (heckeAlphaC k N ℓ') (heckeBetaC k N ℓ') (heckeAlphaC k N ℓ)
    (heckeBetaC k N ℓ) (CommAux.substLeg₂ (k := k) q' N ℓ ℓ' h₁) (CommAux.inclLeg₂ (k := k) q' N ℓ ℓ' h₂ h₃ h₄)
    hα' hβ' hα hβ hv hv'
    hA₂ hB₂
    (CommAux.hex₂ hℓ hℓ' hne h₁ h₂ h₃ h₄ hα' hβ hv hv') D
  have hcongr := Divisor.correspondence_congr (CommAux.alphaLeg_eq (k := k) h₁ h₂ h₃ h₄)
    (CommAux.betaLeg_eq (k := k) h₁ h₂ h₃ h₄)
    hA₁ hB₁ hA₂ hB₂ D
  exact orderA.trans (hcongr.trans orderB.symm)

end S_ModularCurve_correspondence_heckeAlphaC_heckeBetaC_correspondence_heckeAlphaC_heckeBetaC_comm
end P2MW
export P2MW.S_ModularCurve_correspondence_heckeAlphaC_heckeBetaC_correspondence_heckeAlphaC_heckeBetaC_comm (solution)

-- Prove2me | solution 1 for ModularCurve.degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7680915e-0fd4-53e6-90ee-ea77e2935bb5

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_qExpand_jq_mem_adjoin_of_gcd_eq_one
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

p2m_open "ModularCurve~laurentBaseChange_mono~coeffEmb_qExpand"
open AlgebraicCurve

noncomputable section

namespace W6

section Generic

variable {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
  [Algebra K F] [Algebra K F'] [Algebra K F'']

theorem restrictAlong_restrictAlong (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') :
    (W.restrictAlong χ hχ).restrictAlong φ hφ = W.restrictAlong (χ.comp φ) hχφ :=
  Place.ext (SetLike.ext fun _ => Iff.rfl)

theorem pushforwardAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) :
    Divisor.pushforwardAlong φ hφ = Divisor.pushforwardAlong φ' hφ' := by
  subst h; rfl

theorem inertiaDegAlong_eq_one (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hF : ∀ v : Place K F, v.deg = 1) (hF' : ∀ w : Place K F', w.deg = 1) (w : Place K F') :
    w.inertiaDegAlong φ hφ = 1 := by
  have h := Place.deg_restrictAlong_mul_inertiaDegAlong φ hφ w
  rwa [hF, hF', one_mul] at h

theorem pushforwardAlong_single_one (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hF : ∀ v : Place K F, v.deg = 1) (hF' : ∀ w : Place K F', w.deg = 1)
    (w : Place K F') (n : ℤ) :
    Divisor.pushforwardAlong φ hφ (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong φ hφ) n := by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one φ hφ hF hF' w, Nat.cast_one,
    mul_one]

theorem pushforwardAlong_pushforwardAlong (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral)
    (hF : ∀ v : Place K F, v.deg = 1) (hF' : ∀ w : Place K F', w.deg = 1)
    (hF'' : ∀ W : Place K F'', W.deg = 1) (D : Divisor K F'') :
    Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D)
      = Divisor.pushforwardAlong (χ.comp φ) hχφ D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add W n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, pushforwardAlong_single_one χ hχ hF' hF'',
      pushforwardAlong_single_one φ hφ hF hF',
      pushforwardAlong_single_one (χ.comp φ) hχφ hF hF'',
      restrictAlong_restrictAlong φ χ hφ hχ hχφ]

theorem finiteAlong_comp (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) := by
  letI := algebraAlong φ
  letI := algebraAlong χ
  letI := algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite F F' := hφ
  haveI : Module.Finite F' F'' := hχ
  exact Module.Finite.trans F' F''

theorem finiteAlong_of_comp (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (h : FiniteAlong K (χ.comp φ)) : FiniteAlong K χ := by
  letI := algebraAlong φ
  letI := algebraAlong χ
  letI := algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite F F'' := h
  exact Module.Finite.of_restrictScalars_finite F F' F''

theorem finiteAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ') (hφ : FiniteAlong K φ) :
    FiniteAlong K φ' := by
  subst h; exact hφ

theorem isIntegral_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ') (hφ : φ.toRingHom.IsIntegral) :
    φ'.toRingHom.IsIntegral := by
  subst h; exact hφ

theorem finiteAlong_of_finrankAlong_pos (φ : F →ₐ[K] F') (h : 0 < finrankAlong K φ) :
    FiniteAlong K φ := by
  letI := algebraAlong φ
  exact Module.finite_of_finrank_pos h

theorem finrankAlong_comp (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') :
    finrankAlong K (χ.comp φ) = finrankAlong K φ * finrankAlong K χ := by
  letI := algebraAlong φ
  letI := algebraAlong χ
  letI := algebraAlong (χ.comp φ)
  haveI : IsScalarTower F F' F'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank F F' F'').symm

theorem separableAlong_of_charZero [CharZero F] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ := by
  letI := algebraAlong φ
  haveI : Algebra.IsIntegral F F' := ⟨fun x => hφ x⟩
  show Algebra.IsSeparable F F'
  infer_instance

theorem algebra_adjoin_eq_top_of_intermediateField_adjoin_eq_top (χ : F' →ₐ[K] F'')
    (hχ : χ.toRingHom.IsIntegral) (T : Set F'')
    (h : IntermediateField.adjoin K (Set.range χ ∪ T) = ⊤) :
    Algebra.adjoin K (Set.range χ ∪ T) = ⊤ := by
  have hinv : ∀ x ∈ Algebra.adjoin K (Set.range χ ∪ T), x⁻¹ ∈ Algebra.adjoin K (Set.range χ ∪ T) := by
    letI := algebraAlong χ
    intro x hx

    have h₁ : x ∈ Algebra.adjoin F' T := by
      change x ∈ Subsemiring.closure (Set.range (algebraMap F' F'') ∪ T)
      change x ∈ Subsemiring.closure (Set.range (algebraMap K F'') ∪ (Set.range χ ∪ T)) at hx
      refine Subsemiring.closure_mono ?_ hx
      rintro y (⟨k, rfl⟩ | ⟨z, rfl⟩ | hy)
      · exact Or.inl ⟨algebraMap K F' k, (χ.commutes k)⟩
      · exact Or.inl ⟨z, rfl⟩
      · exact Or.inr hy
    have h₂ : x⁻¹ ∈ Algebra.adjoin F' T := IsIntegral.inv_mem (hχ x) h₁
    change x⁻¹ ∈ Subsemiring.closure (Set.range (algebraMap F' F'') ∪ T) at h₂
    change x⁻¹ ∈ Subsemiring.closure (Set.range (algebraMap K F'') ∪ (Set.range χ ∪ T))
    refine Subsemiring.closure_mono ?_ h₂
    rintro y (⟨z, rfl⟩ | hy)
    · exact Or.inr (Or.inl ⟨z, rfl⟩)
    · exact Or.inr (Or.inr hy)
  have := IntermediateField.adjoin_eq_algebra_adjoin K (Set.range χ ∪ T) hinv
  rw [h, IntermediateField.top_toSubalgebra] at this
  exact this.symm

end Generic

section Modular

p2m_open "ModularCurve~laurentBaseChange_mono~coeffEmb_qExpand"

local notation "Qb" => AlgebraicClosure ℚ

theorem deg_eq_one (M : ℕ) [NeZero M] (v : Place Qb (modularFunctionFieldBar M)) : v.deg = 1 :=
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar M
  IsCurveOver.deg_eq_one_of_isAlgClosed v

theorem laurentBaseChange_mono (L : Type*) [Field L] [Algebra ℚ L]
    {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
      = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
    coeffMap_single]

variable (N₀ p : ℕ) [NeZero N₀] [NeZero p] (ℓ : ℕ) [NeZero ℓ]

theorem bar_le_incl : modularFunctionFieldBar (N₀ * ℓ) ≤ modularFunctionFieldBar (N₀ * p * ℓ) :=
  laurentBaseChange_mono Qb (full_degeneracy_le ⟨p, by ring⟩)

theorem bar_le_subst : modularFunctionFieldBar (N₀ * ℓ * p) ≤ modularFunctionFieldBar (N₀ * p * ℓ) :=
  laurentBaseChange_mono Qb (full_degeneracy_le ⟨1, by ring⟩)

def liftIncl : modularFunctionFieldBar (N₀ * ℓ) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ) :=
  IntermediateField.inclusion (bar_le_incl N₀ p ℓ)

def liftSubst : modularFunctionFieldBar (N₀ * ℓ) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ) :=
  (IntermediateField.inclusion (bar_le_subst N₀ p ℓ)).comp (heckeBetaBar Qb (N₀ * ℓ) p)

@[scoped simp] theorem coe_liftIncl (x : modularFunctionFieldBar (N₀ * ℓ)) :
    (liftIncl N₀ p ℓ x : LaurentSeries Qb) = x :=
  IntermediateField.coe_inclusion _ x

@[scoped simp] theorem coe_liftSubst (x : modularFunctionFieldBar (N₀ * ℓ)) :
    (liftSubst N₀ p ℓ x : LaurentSeries Qb) = qExpand Qb p (x : LaurentSeries Qb) := by
  show ((IntermediateField.inclusion (bar_le_subst N₀ p ℓ) (heckeBetaBar Qb (N₀ * ℓ) p x) :
      modularFunctionFieldBar (N₀ * p * ℓ)) : LaurentSeries Qb) = _
  rw [IntermediateField.coe_inclusion, coe_heckeBetaBar]

theorem liftIncl_comp_beta :
    (liftIncl N₀ p ℓ).comp (heckeBetaBar Qb N₀ ℓ)
      = (heckeBetaBar Qb (N₀ * p) ℓ).comp (heckeAlphaBar Qb N₀ p) :=
  AlgHom.ext fun x => Subtype.ext (by simp)

theorem alpha_comp_alpha_eq_liftIncl_comp_alpha :
    (heckeAlphaBar Qb (N₀ * p) ℓ).comp (heckeAlphaBar Qb N₀ p)
      = (liftIncl N₀ p ℓ).comp (heckeAlphaBar Qb N₀ ℓ) :=
  AlgHom.ext fun x => Subtype.ext (by simp)

theorem liftSubst_comp_beta :
    (liftSubst N₀ p ℓ).comp (heckeBetaBar Qb N₀ ℓ)
      = (heckeBetaBar Qb (N₀ * p) ℓ).comp (heckeBetaBar Qb N₀ p) :=
  AlgHom.ext fun x => Subtype.ext (by
    simp only [AlgHom.comp_apply, coe_liftSubst, coe_heckeBetaBar, qExpand_qExpand]
    exact qExpand_congr (Nat.mul_comm p ℓ) _)

theorem alpha_comp_beta_eq_liftSubst_comp_alpha :
    (heckeAlphaBar Qb (N₀ * p) ℓ).comp (heckeBetaBar Qb N₀ p)
      = (liftSubst N₀ p ℓ).comp (heckeAlphaBar Qb N₀ ℓ) :=
  AlgHom.ext fun x => Subtype.ext (by simp)

theorem adjoin_range_eq_top
    (u : modularFunctionFieldBar (N₀ * ℓ) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ))
    (u' : modularFunctionFieldBar (N₀ * p) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ))
    (S : Finset ℕ) (hSM : ∀ s ∈ S, s ∣ N₀ * p * ℓ) (hM : N₀ * p * ℓ ∈ S) (hgcd : S.gcd id = 1)
    (hgenS : ∀ (s : ℕ) [NeZero s], s ∈ S →
      coeffEmb Qb (qExpand ℚ s jq) ∈ ((IntermediateField.adjoin Qb
        (Set.range u ∪ Set.range u')).map (modularFunctionFieldBar (N₀ * p * ℓ)).val)) :
    IntermediateField.adjoin Qb (Set.range u ∪ Set.range u') = ⊤ := by
  set E := IntermediateField.adjoin Qb (Set.range u ∪ Set.range u') with hE
  set E' := E.map (modularFunctionFieldBar (N₀ * p * ℓ)).val with hE'

  have hle : modularFunctionFieldBar (N₀ * p * ℓ) ≤ E' := by
    change laurentBaseChange Qb (modularFunctionFieldFull (N₀ * p * ℓ)) ≤ E'
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hyT : y ∈ IntermediateField.adjoin ℚ {x : LaurentSeries ℚ |
        ∃ (s : ℕ) (_ : NeZero s), s ∈ S ∧ x = qExpand ℚ s jq} := by
      refine (show modularFunctionFieldFull (N₀ * p * ℓ) ≤ _ from ?_) hy
      rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
      rintro x ⟨d, hne, hdvd, rfl⟩
      exact ModularCurve.qExpand_jq_mem_adjoin_of_gcd_eq_one (N₀ * p * ℓ) S hSM hM hgcd d hdvd
    change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ _) at hyT
    have hy' : coeffEmb Qb y ∈ (Subfield.closure
        (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ {x : LaurentSeries ℚ |
          ∃ (s : ℕ) (_ : NeZero s), s ∈ S ∧ x = qExpand ℚ s jq})).map (coeffEmb Qb) :=
      ⟨y, hyT, rfl⟩
    rw [RingHom.map_field_closure] at hy'
    refine (Subfield.closure_le (t := E'.toSubfield)).mpr ?_ hy'
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨c, rfl⟩ | ⟨s, hne, hs, rfl⟩
    · rw [coeffEmb_algebraMap]
      exact E'.algebraMap_mem _
    · exact hgenS s hs

  rw [eq_top_iff]
  intro z _
  obtain ⟨e, he, hez⟩ := (IntermediateField.mem_map _).mp (hle z.2)
  have hez' : e = z := Subtype.ext hez
  exact hez' ▸ he

theorem gen_mem_of_liftIncl (u' : modularFunctionFieldBar (N₀ * p) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ))
    (s : ℕ) [NeZero s] (hs : s ∣ N₀ * ℓ) :
    coeffEmb Qb (qExpand ℚ s jq) ∈ ((IntermediateField.adjoin Qb
        (Set.range (liftIncl N₀ p ℓ) ∪ Set.range u')).map (modularFunctionFieldBar (N₀ * p * ℓ)).val) := by
  refine (IntermediateField.mem_map _).mpr ⟨liftIncl N₀ p ℓ ⟨coeffEmb Qb (qExpand ℚ s jq),
    coeffEmb_mem_laurentBaseChange Qb (jqd_mem_full (N₀ * ℓ) hs)⟩,
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨_, rfl⟩), ?_⟩
  rw [IntermediateField.val_mk]
  exact coe_liftIncl N₀ p ℓ _

theorem gen_mem_of_liftSubst (u' : modularFunctionFieldBar (N₀ * p) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ))
    (s : ℕ) [NeZero s] [NeZero (s * p)] (hs : s ∣ N₀ * ℓ) :
    coeffEmb Qb (qExpand ℚ (s * p) jq) ∈ ((IntermediateField.adjoin Qb
        (Set.range (liftSubst N₀ p ℓ) ∪ Set.range u')).map (modularFunctionFieldBar (N₀ * p * ℓ)).val) := by
  refine (IntermediateField.mem_map _).mpr ⟨liftSubst N₀ p ℓ ⟨coeffEmb Qb (qExpand ℚ s jq),
    coeffEmb_mem_laurentBaseChange Qb (jqd_mem_full (N₀ * ℓ) hs)⟩,
    IntermediateField.subset_adjoin _ _ (Or.inl ⟨_, rfl⟩), ?_⟩
  have hr : coeffEmb Qb (qExpand ℚ (s * p) jq) = qExpand Qb p (coeffEmb Qb (qExpand ℚ s jq)) := by
    rw [qExpand_congr (Nat.mul_comm s p), ← qExpand_qExpand, coeffEmb_qExpand]
  rw [hr]
  rw [IntermediateField.coe_val]
  exact coe_liftSubst N₀ p ℓ _

omit [NeZero N₀] [NeZero p] in

theorem gen_mem_of_beta (u : modularFunctionFieldBar (N₀ * ℓ) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ))
    (s : ℕ) [NeZero s] [NeZero (s * ℓ)] (hs : s ∣ N₀ * p) :
    coeffEmb Qb (qExpand ℚ (s * ℓ) jq) ∈ ((IntermediateField.adjoin Qb
        (Set.range u ∪ Set.range (heckeBetaBar Qb (N₀ * p) ℓ))).map
          (modularFunctionFieldBar (N₀ * p * ℓ)).val) := by
  refine (IntermediateField.mem_map _).mpr ⟨heckeBetaBar Qb (N₀ * p) ℓ ⟨coeffEmb Qb (qExpand ℚ s jq),
    coeffEmb_mem_laurentBaseChange Qb (jqd_mem_full (N₀ * p) hs)⟩,
    IntermediateField.subset_adjoin _ _ (Or.inr ⟨_, rfl⟩), ?_⟩
  have hr : coeffEmb Qb (qExpand ℚ (s * ℓ) jq) = qExpand Qb ℓ (coeffEmb Qb (qExpand ℚ s jq)) := by
    rw [qExpand_congr (Nat.mul_comm s ℓ), ← qExpand_qExpand, coeffEmb_qExpand]
  rw [hr]
  rw [IntermediateField.coe_val]
  exact coe_heckeBetaBar (N₀ * p) ℓ _

theorem adjoin_liftIncl_beta_eq_top :
    IntermediateField.adjoin Qb (Set.range (liftIncl N₀ p ℓ) ∪
      Set.range (heckeBetaBar Qb (N₀ * p) ℓ)) = ⊤ := by
  classical
  refine adjoin_range_eq_top N₀ p ℓ (liftIncl N₀ p ℓ) (heckeBetaBar Qb (N₀ * p) ℓ)
    ((N₀ * ℓ).divisors ∪ (N₀ * p).divisors.image (· * ℓ)) ?_ ?_ ?_ ?_
  · intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · exact (Nat.dvd_of_mem_divisors h).trans ⟨p, by ring⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      exact Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors he) ℓ
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨N₀ * p, Nat.mem_divisors_self _ (NeZero.ne (N₀ * p)), rfl⟩)
  · exact Nat.dvd_one.mp (Finset.gcd_dvd (f := id)
      (Finset.mem_union_left _ (Nat.one_mem_divisors.mpr (NeZero.ne (N₀ * ℓ)))))
  · intro s _ hs
    rcases Finset.mem_union.mp hs with h | h
    · exact gen_mem_of_liftIncl N₀ p ℓ _ s (Nat.dvd_of_mem_divisors h)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      haveI : NeZero e := ⟨Nat.pos_of_mem_divisors he |>.ne'⟩
      exact gen_mem_of_beta N₀ p ℓ _ e (Nat.dvd_of_mem_divisors he)

theorem adjoin_liftSubst_beta_eq_top (hprime : ℓ.Prime) (hℓp : ¬ ℓ ∣ p) :
    IntermediateField.adjoin Qb (Set.range (liftSubst N₀ p ℓ) ∪
      Set.range (heckeBetaBar Qb (N₀ * p) ℓ)) = ⊤ := by
  classical
  refine adjoin_range_eq_top N₀ p ℓ (liftSubst N₀ p ℓ) (heckeBetaBar Qb (N₀ * p) ℓ)
    ((N₀ * ℓ).divisors.image (· * p) ∪ (N₀ * p).divisors.image (· * ℓ)) ?_ ?_ ?_ ?_
  · intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      exact (Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors he) p).trans ⟨1, by ring⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      exact Nat.mul_dvd_mul_right (Nat.dvd_of_mem_divisors he) ℓ
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨N₀ * p, Nat.mem_divisors_self _ (NeZero.ne (N₀ * p)), rfl⟩)
  · have hp : (Finset.image (· * p) (N₀ * ℓ).divisors ∪ Finset.image (· * ℓ) (N₀ * p).divisors).gcd id ∣ p := by
      refine (Finset.gcd_dvd (f := id) (b := 1 * p) ?_).trans (by simp)
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne (N₀ * ℓ)), rfl⟩)
    have hl : (Finset.image (· * p) (N₀ * ℓ).divisors ∪ Finset.image (· * ℓ) (N₀ * p).divisors).gcd id ∣ ℓ := by
      refine (Finset.gcd_dvd (f := id) (b := 1 * ℓ) ?_).trans (by simp)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨1, Nat.one_mem_divisors.mpr (NeZero.ne (N₀ * p)), rfl⟩)
    have hcop : Nat.Coprime p ℓ := (hprime.coprime_iff_not_dvd.mpr hℓp).symm
    exact Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hp hl)
  · intro s _ hs
    rcases Finset.mem_union.mp hs with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      haveI : NeZero e := ⟨Nat.pos_of_mem_divisors he |>.ne'⟩
      exact gen_mem_of_liftSubst N₀ p ℓ _ e (Nat.dvd_of_mem_divisors he)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      haveI : NeZero e := ⟨Nat.pos_of_mem_divisors he |>.ne'⟩
      exact gen_mem_of_beta N₀ p ℓ _ e (Nat.dvd_of_mem_divisors he)

theorem pushforward_correspondence_of_leg [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (ψ' : modularFunctionFieldBar N₀ →ₐ[Qb] modularFunctionFieldBar (N₀ * p))
    (u : modularFunctionFieldBar (N₀ * ℓ) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ))
    (hψ' : ψ'.toRingHom.IsIntegral) (hψ'fin : FiniteAlong Qb ψ')
    (hsq : u.comp (heckeBetaBar Qb N₀ ℓ) = (heckeBetaBar Qb (N₀ * p) ℓ).comp ψ')
    (hpush : (heckeAlphaBar Qb (N₀ * p) ℓ).comp ψ' = u.comp (heckeAlphaBar Qb N₀ ℓ))
    (hgen : IntermediateField.adjoin Qb (Set.range u ∪ Set.range (heckeBetaBar Qb (N₀ * p) ℓ)) = ⊤)
    (hαU : HeckeAlphaBarIntegral Qb (N₀ * p) ℓ) (hβU : HeckeBetaBarIntegral Qb (N₀ * p) ℓ)
    [HasPrincipalDivisors Qb (modularFunctionFieldBar (N₀ * p * ℓ))]
    (hαL : HeckeAlphaBarIntegral Qb N₀ ℓ) (hβL : HeckeBetaBarIntegral Qb N₀ ℓ)
    [HasPrincipalDivisors Qb (modularFunctionFieldBar (N₀ * ℓ))]
    (D : Divisor Qb (modularFunctionFieldBar (N₀ * p))) :
    Divisor.pushforwardAlong ψ' hψ'
        (Divisor.correspondence (heckeBetaBar Qb (N₀ * p) ℓ) (heckeAlphaBar Qb (N₀ * p) ℓ) hβU hαU D)
      = Divisor.correspondence (heckeBetaBar Qb N₀ ℓ) (heckeAlphaBar Qb N₀ ℓ) hβL hαL
          (Divisor.pushforwardAlong ψ' hψ' D) := by
  have hprime : ℓ.Prime := Fact.out

  have hdvd : ℓ ∣ N₀ * p ↔ ℓ ∣ N₀ := by
    rw [hprime.dvd_mul]; exact or_iff_left hℓp
  have hdeg : finrankAlong Qb (heckeBetaBar Qb (N₀ * p) ℓ) = finrankAlong Qb (heckeBetaBar Qb N₀ ℓ) := by
    rw [ModularCurve.finrankAlong_heckeBetaBar Qb (N₀ * p) ℓ, ModularCurve.finrankAlong_heckeBetaBar Qb N₀ ℓ]
    by_cases h : ℓ ∣ N₀
    · rw [if_pos (hdvd.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hdvd.mp h')), if_neg h]
  have hposL : 0 < finrankAlong Qb (heckeBetaBar Qb N₀ ℓ) := by
    rw [ModularCurve.finrankAlong_heckeBetaBar Qb N₀ ℓ]; split_ifs <;> exact Nat.pos_of_ne_zero (by
      first | exact hprime.ne_zero | exact Nat.succ_ne_zero _)
  have hu'fin : FiniteAlong Qb (heckeBetaBar Qb (N₀ * p) ℓ) :=
    finiteAlong_of_finrankAlong_pos _ (hdeg ▸ hposL)

  have hcompint : ((heckeBetaBar Qb (N₀ * p) ℓ).comp ψ').toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hψ' hβU
  have hcomp : (u.comp (heckeBetaBar Qb N₀ ℓ)).toRingHom.IsIntegral :=
    isIntegral_congr hsq.symm hcompint
  have hu : u.toRingHom.IsIntegral := RingHom.IsIntegral.tower_top _ _ hcomp

  have hfin : FiniteAlong Qb ((heckeBetaBar Qb (N₀ * p) ℓ).comp ψ') :=
    finiteAlong_comp ψ' _ hψ'fin hu'fin
  have hsep : SeparableAlong Qb ((heckeBetaBar Qb (N₀ * p) ℓ).comp ψ') :=
    separableAlong_of_charZero _ hcompint
  have hgen' : Algebra.adjoin Qb
      (Set.range (heckeBetaBar Qb (N₀ * p) ℓ) ∪ Set.range u) = ⊤ :=
    algebra_adjoin_eq_top_of_intermediateField_adjoin_eq_top _ hβU _ (Set.union_comm _ _ ▸ hgen)
  have hLD : finrankAlong Qb ((heckeBetaBar Qb (N₀ * p) ℓ).comp ψ')
      = finrankAlong Qb ψ' * finrankAlong Qb (heckeBetaBar Qb N₀ ℓ) := by
    rw [finrankAlong_comp, hdeg]

  have h1 := deg_eq_one N₀
  have h2 := deg_eq_one (N₀ * p)
  have h3 := deg_eq_one (N₀ * ℓ)
  have h4 := deg_eq_one (N₀ * p * ℓ)
  have hc1 : ((heckeAlphaBar Qb (N₀ * p) ℓ).comp ψ').toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hψ' hαU
  have hc2 : (u.comp (heckeAlphaBar Qb N₀ ℓ)).toRingHom.IsIntegral :=
    RingHom.IsIntegral.trans _ _ hαL hu
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    pushforwardAlong_pushforwardAlong _ _ hψ' hαU hc1 h1 h2 h4,
    pushforwardAlong_congr hpush hc1 hc2,
    ← pushforwardAlong_pushforwardAlong _ _ hαL hu hc2 h1 h3 h4,
    ← AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
      ψ' (heckeBetaBar Qb N₀ ℓ) (heckeBetaBar Qb (N₀ * p) ℓ) u hψ' hβL hβU hu
      hsq hfin hsep hgen' hLD D]

theorem eq_of_leg (ℓ : Nat.Primes) (hℓp : ¬ (ℓ : ℕ) ∣ p)
    (hinUp : HeckeInputsAll (N₀ * p)) (hinLow : HeckeInputsAll N₀)
    (ψ' : modularFunctionFieldBar N₀ →ₐ[Qb] modularFunctionFieldBar (N₀ * p))
    (hψ' : ψ'.toRingHom.IsIntegral) (hψ'fin : FiniteAlong Qb ψ') (hψ'N : NormFormulaAlong Qb ψ' hψ'fin)
    (u : haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      modularFunctionFieldBar (N₀ * ℓ) →ₐ[Qb] modularFunctionFieldBar (N₀ * p * ℓ))
    (hsq : haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      u.comp (heckeBetaBar Qb N₀ ℓ) = (heckeBetaBar Qb (N₀ * p) ℓ).comp ψ')
    (hpush : haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      (heckeAlphaBar Qb (N₀ * p) ℓ).comp ψ' = u.comp (heckeAlphaBar Qb N₀ ℓ))
    (hgen : haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
      IntermediateField.adjoin Qb (Set.range u ∪ Set.range (heckeBetaBar Qb (N₀ * p) ℓ)) = ⊤)
    (y : JZero (N₀ * p)) :
    Pic0.pushforwardAlongHom ψ' hψ' hψ'fin hψ'N (heckeOperatorBar (N₀ * p) ℓ y)
      = heckeOperatorBar N₀ ℓ (Pic0.pushforwardAlongHom ψ' hψ' hψ'fin hψ'N y) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  obtain ⟨hαU, hβU, hPU, hfinU, hFIU, hNU⟩ := hinUp ℓ
  obtain ⟨hαL, hβL, hPL, hfinL, hFIL, hNL⟩ := hinLow ℓ
  rw [heckeOperatorBar_apply, heckeOperatorBar_apply]
  rw [heckeOperatorAlong_eq hαU hβU hFIU hfinU hNU, heckeOperatorAlong_eq hαL hβL hFIL hfinL hNL]
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  simp only [heckePic0Bar, Pic0.correspondence_mk, Pic0.pushforwardAlongHom_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  simp only [Pic0.coe_pushforwardAlongDegZero, Pic0.coe_degZeroCorrespondence]
  exact pushforward_correspondence_of_leg N₀ p ℓ hℓp ψ' u hψ' hψ'fin hsq hpush hgen hαU hβU hαL hβL _

theorem eq_main (ℓ : Nat.Primes) (hℓp : ¬ (ℓ : ℕ) ∣ p)
    (hinUp : HeckeInputsAll (N₀ * p)) (hinLow : HeckeInputsAll N₀)
    (i : Fin 2) (y : JZero (N₀ * p)) :
    degeneracyPushforwardPair N₀ p i (heckeOperatorBar (N₀ * p) ℓ y) =
      heckeOperatorBar N₀ ℓ (degeneracyPushforwardPair N₀ p i y) := by
  by_cases hdeg : DegeneracyPushforwardInputs N₀ p
  swap
  · simp [degeneracyPushforwardPair_of_not hdeg]
  obtain ⟨hα₁, hβ₁, hfinα₁, hfinβ₁, hNα₁, hNβ₁⟩ := hdeg
  rw [degeneracyPushforwardPair_eq hα₁ hβ₁ hfinα₁ hNα₁ hfinβ₁ hNβ₁]
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact eq_of_leg N₀ p ℓ hℓp hinUp hinLow (heckeAlphaBar Qb N₀ p) hα₁ hfinα₁ hNα₁
      (liftIncl N₀ p ℓ) (liftIncl_comp_beta N₀ p ℓ)
      (alpha_comp_alpha_eq_liftIncl_comp_alpha N₀ p ℓ) (adjoin_liftIncl_beta_eq_top N₀ p ℓ) y
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact eq_of_leg N₀ p ℓ hℓp hinUp hinLow (heckeBetaBar Qb N₀ p) hβ₁ hfinβ₁ hNβ₁
      (liftSubst N₀ p ℓ) (liftSubst_comp_beta N₀ p ℓ)
      (alpha_comp_beta_eq_liftSubst_comp_alpha N₀ p ℓ)
      (adjoin_liftSubst_beta_eq_top N₀ p ℓ ℓ.2 hℓp) y

end Modular

end W6
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd.W6"

theorem solution (N₀ p : ℕ) [NeZero N₀] [NeZero p]
    (hinUp : ModularCurve.HeckeInputsAll (N₀ * p)) (hinLow : ModularCurve.HeckeInputsAll N₀)
    (ℓ : Nat.Primes) (hℓp : ¬ (ℓ : ℕ) ∣ p) (i : Fin 2) (y : ModularCurve.JZero (N₀ * p)) :
    ModularCurve.degeneracyPushforwardPair N₀ p i (ModularCurve.heckeOperatorBar (N₀ * p) ℓ y) =
      ModularCurve.heckeOperatorBar N₀ ℓ (ModularCurve.degeneracyPushforwardPair N₀ p i y) :=
  W6.eq_main N₀ p ℓ hℓp hinUp hinLow i y

end
p2m_reactivate "P2MW.S_ModularCurve_degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd.W6"

end S_ModularCurve_degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_degeneracyPushforwardPair_heckeOperatorBar_of_not_dvd (solution)

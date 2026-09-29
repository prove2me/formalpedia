-- Prove2me | solution 1 for ModularCurve.kroneckerCongruence_norm_heckeBetaBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/683c03d8-9d2f-588e-b2e1-7e88c9c5f25c

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaBar
import Theorems.Thm_ModularCurve_exists_algEquiv_modularFunctionFieldBar_atkinLehner
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_kroneckerCongruence_norm_heckeBetaBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve HahnSeries AlgebraicCurve

namespace W6FK2

section Twist

variable {R S : Type*} [CommRing R] [CommRing S]

def twistFun (c : Rˣ) (x : LaurentSeries R) : LaurentSeries R where
  coeff n := ((c ^ n : Rˣ) : R) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h
    exact hn (by rw [h, mul_zero])

@[scoped simp] theorem twistFun_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twistFun c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem support_twistFun (c : Rˣ) (x : LaurentSeries R) : (twistFun c x).support = x.support := by
  ext n
  simp only [HahnSeries.mem_support, twistFun_coeff, ne_eq, Units.mul_right_eq_zero]

theorem twistFun_single (c : Rˣ) (k : ℤ) (r : R) :
    twistFun c (single k r) = single k (((c ^ k : Rˣ) : R) * r) := by
  ext n
  by_cases h : n = k
  · subst h; simp
  · simp [coeff_single_of_ne h]

def twist (c : Rˣ) : LaurentSeries R →+* LaurentSeries R where
  toFun := twistFun c
  map_one' := by
    rw [← single_zero_one, twistFun_single]; simp
  map_mul' x y := by
    ext a
    rw [twistFun_coeff,
      coeff_mul_right' (x := x) (y := y) (twistFun c y).isPWO_support
        (support_twistFun c y).symm.subset,
      coeff_mul_left' (x := twistFun c x) (y := twistFun c y) x.isPWO_support
        (support_twistFun c x).subset,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [twistFun_coeff, twistFun_coeff, ← hij.2.2, zpow_add, Units.val_mul]
    ring
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]

@[scoped simp] theorem twist_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twist c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem twist_one (x : LaurentSeries R) : twist (1 : Rˣ) x = x := by
  ext n; simp

theorem twist_qExpand_of_pow_eq_one (c : Rˣ) (m : ℕ) [NeZero m] (hc : c ^ m = 1)
    (z : LaurentSeries R) : twist c (qExpand R m z) = qExpand R m z := by
  ext n
  rw [twist_coeff]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [zpow_mul, zpow_natCast, hc, one_zpow, Units.val_one, one_mul]
  · rw [qExpand_coeff_of_not_dvd m _ h, mul_zero]

theorem coeffMap_twist (f : R →+* S) (c : Rˣ) (x : LaurentSeries R) :
    coeffMap f (twist c x) = twist (Units.map (f : R →* S) c) (coeffMap f x) := by
  ext n
  rw [coeffMap_coeff, twist_coeff, twist_coeff, coeffMap_coeff, map_mul, ← map_zpow,
    Units.coe_map]
  rfl

theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

def unexpand (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R) : LaurentSeries R where
  coeff k := P.coeff ((ℓ : ℤ) * k)
  isPWO_support' := by
    have hℓ : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    refine (P.isPWO_support.image_of_monotone (f := fun n : ℤ => n / (ℓ : ℤ))
      (fun a b h => Int.ediv_le_ediv hℓ h)).mono ?_
    intro k hk
    refine ⟨(ℓ : ℤ) * k, hk, ?_⟩
    show (ℓ : ℤ) * k / (ℓ : ℤ) = k
    exact Int.mul_ediv_cancel_left k hℓ.ne'

theorem unexpand_coeff (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R) (k : ℤ) :
    (unexpand ℓ P).coeff k = P.coeff ((ℓ : ℤ) * k) := rfl

theorem qExpand_unexpand (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R)
    (hP : ∀ n : ℤ, ¬ (ℓ : ℤ) ∣ n → P.coeff n = 0) : qExpand R ℓ (unexpand ℓ P) = P := by
  ext n
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, unexpand_coeff]
  · rw [qExpand_coeff_of_not_dvd ℓ _ h, hP n h]

end Twist

section Bar

local notation "Qb" => AlgebraicClosure ℚ

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c)
      = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb,
    coeffMap_single]

theorem modularFunctionFieldBar_eq_adjoin (M : ℕ) :
    modularFunctionFieldBar M
      = IntermediateField.adjoin Qb (coeffEmb Qb '' divisorExpansions M) := by
  apply le_antisymm
  · change laurentBaseChange Qb (modularFunctionFieldFull M) ≤ _
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    change y ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ _) at hy
    have hy' : coeffEmb Qb y ∈ (Subfield.closure
        (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ divisorExpansions M)).map (coeffEmb Qb) :=
      ⟨y, hy, rfl⟩
    rw [RingHom.map_field_closure] at hy'
    refine (Subfield.closure_le (t := (IntermediateField.adjoin Qb
      (coeffEmb Qb '' divisorExpansions M)).toSubfield)).mpr ?_ hy'
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨c, rfl⟩ | hx
    · rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact coeffEmb_mem_laurentBaseChange Qb (IntermediateField.subset_adjoin ℚ _ hx)

theorem algHom_ext_bar (M : ℕ) {E : Type*} [Semiring E] [Algebra Qb E]
    {f g : modularFunctionFieldBar M →ₐ[Qb] E}
    (h : ∀ (d : ℕ) [NeZero d], d ∣ M → ∀ x : modularFunctionFieldBar M,
      (x : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ d jq) → f x = g x) : f = g := by
  refine IntermediateField.algHom_ext_of_eq_adjoin Qb (modularFunctionFieldBar_eq_adjoin M) ?_
  rintro _ ⟨x, ⟨d, hne, hd, rfl⟩, rfl⟩
  exact h d hd _ rfl

def jBar (M : ℕ) : modularFunctionFieldBar M :=
  ⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (by
    simpa [qExpand_one_apply] using jqd_mem_full M (one_dvd _) (d := 1))⟩

@[scoped simp] theorem coe_jBar (M : ℕ) : ((jBar M : modularFunctionFieldBar M) : LaurentSeries Qb)
    = coeffEmb Qb jq := rfl

theorem coeffEmb_jq_coeff_neg_one : (coeffEmb Qb jq).coeff (-1) = 1 := by
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

def ALSpec (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) : Prop :=
  ∀ (d : ℕ) [NeZero d], d ∣ N → ∀ x : modularFunctionFieldBar (N * ℓ),
    ((x : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ d jq) →
      ((w x : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)
        = qExpand Qb ℓ (coeffEmb Qb (qExpand ℚ d jq))) ∧
    ((x : LaurentSeries Qb) = qExpand Qb ℓ (coeffEmb Qb (qExpand ℚ d jq)) →
      ((w x : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)
        = coeffEmb Qb (qExpand ℚ d jq))

theorem exists_AL (hℓN : ¬ ℓ ∣ N) :
    ∃ w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ), ALSpec N ℓ w :=
  ModularCurve.exists_algEquiv_modularFunctionFieldBar_atkinLehner N ℓ Fact.out hℓN

variable {N ℓ}

theorem AL_beta {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (hw : ALSpec N ℓ w) (x : modularFunctionFieldBar N) :
    w (heckeBetaBar Qb N ℓ x) = heckeAlphaBar Qb N ℓ x := by
  have h : w.toAlgHom.comp (heckeBetaBar Qb N ℓ) = heckeAlphaBar Qb N ℓ := by
    refine algHom_ext_bar N fun d _ hd x hx => Subtype.ext ?_
    have h2 := (hw d hd (heckeBetaBar Qb N ℓ x)).2 (by rw [coe_heckeBetaBar, hx])
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, coe_heckeAlphaBar]
    rw [hx]; exact h2
  exact DFunLike.congr_fun h x

theorem AL_alpha {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (hw : ALSpec N ℓ w) (x : modularFunctionFieldBar N) :
    w (heckeAlphaBar Qb N ℓ x) = heckeBetaBar Qb N ℓ x := by
  have h : w.toAlgHom.comp (heckeAlphaBar Qb N ℓ) = heckeBetaBar Qb N ℓ := by
    refine algHom_ext_bar N fun d _ hd x hx => Subtype.ext ?_
    have h1 := (hw d hd (heckeAlphaBar Qb N ℓ x)).1 (by rw [coe_heckeAlphaBar, hx])
    rw [AlgHom.comp_apply, AlgEquiv.coe_algHom, coe_heckeBetaBar]
    rw [hx]; exact h1
  exact DFunLike.congr_fun h x

end Bar

section Norm

local notation "Qb" => AlgebraicClosure ℚ

def EE (_ℓ : ℕ) : Type := AlgebraicClosure (LaurentSeries Qb)

variable (ℓ : ℕ) in
scoped instance : Field (EE ℓ) := inferInstanceAs (Field (AlgebraicClosure (LaurentSeries Qb)))

variable (ℓ : ℕ) in
scoped instance : IsAlgClosed (EE ℓ) := inferInstanceAs (IsAlgClosed (AlgebraicClosure (LaurentSeries Qb)))

def ιE (ℓ : ℕ) : LaurentSeries Qb →+* EE ℓ :=
  algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))

theorem ιE_injective (ℓ : ℕ) : Function.Injective (ιE ℓ) :=
  (algebraMap (LaurentSeries Qb) (AlgebraicClosure (LaurentSeries Qb))).injective

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

@[reducible] def algAlongAlpha :
    Algebra (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) :=
  algebraAlong (heckeAlphaBar Qb N ℓ)

@[reducible] def algAlphaE : Algebra (modularFunctionFieldBar N) (EE ℓ) :=
  (((ιE ℓ).comp (algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb))).comp
    (heckeBetaBar Qb N ℓ).toRingHom).toAlgebra

attribute [local instance] algAlongAlpha algAlphaE

theorem finrank_alpha (hℓN : ¬ ℓ ∣ N)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)} (hw : ALSpec N ℓ w) :
    Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) = ℓ + 1 := by
  have hβ := ModularCurve.finrankAlong_heckeBetaBar Qb N ℓ
  rw [if_neg hℓN] at hβ
  have hβ' : (letI := algebraAlong (heckeBetaBar Qb N ℓ)
      Module.finrank (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ))) = ℓ + 1 := hβ
  rw [← hβ']
  exact @Algebra.finrank_eq_of_equiv_equiv (modularFunctionFieldBar N)
    (modularFunctionFieldBar (N * ℓ)) _ _ (algAlongAlpha N ℓ) (modularFunctionFieldBar N)
    (modularFunctionFieldBar (N * ℓ)) _ _ (algebraAlong (heckeBetaBar Qb N ℓ))
    (RingEquiv.refl _) w.toRingEquiv (RingHom.ext fun x => (AL_alpha hw x).symm)

theorem finiteDimensional_alpha (hℓN : ¬ ℓ ∣ N)
    {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)} (hw : ALSpec N ℓ w) :
    FiniteDimensional (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) :=
  Module.finite_of_finrank_pos (by rw [finrank_alpha N ℓ hℓN hw]; exact Nat.succ_pos ℓ)

theorem algebraMap_FE_apply (f : modularFunctionFieldBar N) :
    algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) f
      = heckeAlphaBar Qb N ℓ f := rfl

omit [NeZero N] [Fact ℓ.Prime] in
theorem algebraMap_ELS_apply (x : modularFunctionFieldBar (N * ℓ)) :
    algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb) x = ↑x := rfl

theorem algebraMap_FEE_apply (f : modularFunctionFieldBar N) :
    algebraMap (modularFunctionFieldBar N) (EE ℓ) f
      = ιE ℓ ((heckeBetaBar Qb N ℓ f : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb) := rfl

theorem sigmaLast_comm (f : modularFunctionFieldBar N) :
    ((ιE ℓ).comp ((qExpand Qb ℓ).comp
      (algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb))))
      (algebraMap (modularFunctionFieldBar N) (modularFunctionFieldBar (N * ℓ)) f)
      = algebraMap (modularFunctionFieldBar N) (EE ℓ) f := by
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_FE_apply, algebraMap_ELS_apply,
    algebraMap_FEE_apply, coe_heckeAlphaBar, coe_heckeBetaBar]

variable {N ℓ}

def sigmaTwist (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ))
    (hw : ALSpec N ℓ w) (c : Qbˣ) (hc : c ^ ℓ = 1) :
    modularFunctionFieldBar (N * ℓ) →ₐ[modularFunctionFieldBar N] EE ℓ where
  toRingHom := (ιE ℓ).comp ((twist c).comp
    ((algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb)).comp w.toAlgHom.toRingHom))
  commutes' f := by
    show ιE ℓ (twist c ((w (heckeAlphaBar Qb N ℓ f) : modularFunctionFieldBar (N * ℓ)) :
        LaurentSeries Qb)) = ιE ℓ ((heckeBetaBar Qb N ℓ f : modularFunctionFieldBar (N * ℓ)) :
        LaurentSeries Qb)
    rw [AL_alpha hw, coe_heckeBetaBar, twist_qExpand_of_pow_eq_one c ℓ hc]

theorem sigmaTwist_apply (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ))
    (hw : ALSpec N ℓ w) (c : Qbˣ) (hc : c ^ ℓ = 1) (v : modularFunctionFieldBar (N * ℓ)) :
    sigmaTwist w hw c hc v
      = ιE ℓ (twist c ((w v : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)) := rfl

def sigmaLast : modularFunctionFieldBar (N * ℓ) →ₐ[modularFunctionFieldBar N] EE ℓ where
  toRingHom := (ιE ℓ).comp ((qExpand Qb ℓ).comp
    (algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb)))
  commutes' := sigmaLast_comm N ℓ

theorem sigmaLast_apply (v : modularFunctionFieldBar (N * ℓ)) :
    sigmaLast (N := N) v = ιE ℓ (qExpand Qb ℓ (v : LaurentSeries Qb)) := by
  show ((ιE ℓ).comp ((qExpand Qb ℓ).comp
      (algebraMap (modularFunctionFieldBar (N * ℓ)) (LaurentSeries Qb)))) v = _
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_ELS_apply]

def zu {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Qbˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem zu_pow {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (zu hζ ^ j) ^ ℓ = 1 := by
  ext
  rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu,
    Units.val_mk0, hζ.pow_eq_one, one_pow, Units.val_one]

def emb {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w) :
    Option (Fin ℓ) → (modularFunctionFieldBar (N * ℓ) →ₐ[modularFunctionFieldBar N] EE ℓ)
  | none => sigmaLast
  | some j => sigmaTwist w hw (zu hζ ^ (j : ℕ)) (zu_pow hζ j)

theorem emb_none_apply {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w)
    (v : modularFunctionFieldBar (N * ℓ)) :
    emb hζ w hw none v = ιE ℓ (qExpand Qb ℓ (v : LaurentSeries Qb)) :=
  sigmaLast_apply v

theorem emb_some_apply {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w)
    (j : Fin ℓ) (v : modularFunctionFieldBar (N * ℓ)) :
    emb hζ w hw (some j) v
      = ιE ℓ (twist (zu hζ ^ (j : ℕ)) ((w v : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)) :=
  rfl

def jBeta (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] : modularFunctionFieldBar (N * ℓ) :=
  heckeBetaBar Qb N ℓ (jBar N)

theorem w_jBeta {w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)}
    (hw : ALSpec N ℓ w) :
    ((w (jBeta N ℓ) : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb) = coeffEmb Qb jq := by
  rw [jBeta, AL_beta hw, coe_heckeAlphaBar, coe_jBar]

theorem coe_jBeta :
    ((jBeta N ℓ : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb)
      = qExpand Qb ℓ (coeffEmb Qb jq) := by
  rw [jBeta, coe_heckeBetaBar, coe_jBar]

theorem emb_injective {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w) :
    Function.Injective (emb hζ w hw) := by
  have hprime : ℓ.Prime := Fact.out
  have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne ℓ)

  let cf : Option (Fin ℓ) → Qb := fun o => Option.elim o (0 : Qb) (fun j => (ζ ^ (j : ℕ))⁻¹)
  have key : ∀ o : Option (Fin ℓ), ∃ s : LaurentSeries Qb,
      emb hζ w hw o (jBeta N ℓ) = ιE ℓ s ∧ s.coeff (-1) = cf o := by
    rintro (_ | j)
    · refine ⟨qExpand Qb ℓ (qExpand Qb ℓ (coeffEmb Qb jq)), ?_, ?_⟩
      · rw [emb_none_apply, coe_jBeta]
      · show (qExpand Qb ℓ (qExpand Qb ℓ (coeffEmb Qb jq))).coeff (-1) = 0
        refine qExpand_coeff_of_not_dvd ℓ _ fun h => ?_
        have h1 : (ℓ : ℤ) ∣ 1 := (dvd_neg).mp h
        have h2 : (ℓ : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
        exact hprime.one_lt.ne' (by exact_mod_cast h2)
    · refine ⟨twist (zu hζ ^ (j : ℕ)) (coeffEmb Qb jq), ?_, ?_⟩
      · rw [emb_some_apply, w_jBeta hw]
      · show (twist (zu hζ ^ (j : ℕ)) (coeffEmb Qb jq)).coeff (-1) = (ζ ^ (j : ℕ))⁻¹
        rw [twist_coeff, coeffEmb_jq_coeff_neg_one, mul_one, zpow_neg_one, Units.val_inv_eq_inv_val,
          Units.val_pow_eq_pow_val, zu, Units.val_mk0]
  intro o₁ o₂ h
  obtain ⟨s₁, hs₁, hc₁⟩ := key o₁
  obtain ⟨s₂, hs₂, hc₂⟩ := key o₂
  have hs : s₁ = s₂ := ιE_injective ℓ (by rw [← hs₁, ← hs₂, h])
  rw [hs] at hc₁
  have hc : cf o₁ = cf o₂ := hc₁.symm.trans hc₂
  rcases o₁ with _ | j₁ <;> rcases o₂ with _ | j₂
  · rfl
  · exact absurd hc.symm (inv_ne_zero (pow_ne_zero _ hz))
  · exact absurd hc (inv_ne_zero (pow_ne_zero _ hz))
  · have hv : ζ ^ (j₁ : ℕ) = ζ ^ (j₂ : ℕ) := inv_inj.mp hc
    exact congrArg some (Fin.ext (hζ.pow_inj j₁.2 j₂.2 hv))

theorem emb_bijective (hℓN : ¬ ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w) :
    Function.Bijective (emb hζ w hw) := by
  haveI := finiteDimensional_alpha N ℓ hℓN hw
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective hζ w hw, ?_⟩
  rw [Fintype.card_option, Fintype.card_fin, AlgHom.card, finrank_alpha N ℓ hℓN hw]

theorem qExpand_norm (hℓN : ¬ ℓ ∣ N) {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ)
    (w : modularFunctionFieldBar (N * ℓ) ≃ₐ[Qb] modularFunctionFieldBar (N * ℓ)) (hw : ALSpec N ℓ w)
    (v : modularFunctionFieldBar (N * ℓ)) :
    qExpand Qb ℓ ((Algebra.norm (modularFunctionFieldBar N) v :
        modularFunctionFieldBar N) : LaurentSeries Qb)
      = (∏ j ∈ Finset.range ℓ,
          twist (zu hζ ^ j) ((w v : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb))
        * qExpand Qb ℓ (v : LaurentSeries Qb) := by
  haveI := finiteDimensional_alpha N ℓ hℓN hw
  apply ιE_injective ℓ
  have h1 := Algebra.norm_eq_prod_embeddings (K := modularFunctionFieldBar N)
    (L := modularFunctionFieldBar (N * ℓ)) (E := EE ℓ) v
  have h2 : algebraMap (modularFunctionFieldBar N) (EE ℓ)
      (Algebra.norm (modularFunctionFieldBar N) v)
      = ιE ℓ (qExpand Qb ℓ ((Algebra.norm (modularFunctionFieldBar N) v :
          modularFunctionFieldBar N) : LaurentSeries Qb)) := by
    show ιE ℓ ((heckeBetaBar Qb N ℓ _ : modularFunctionFieldBar (N * ℓ)) : LaurentSeries Qb) = _
    rw [coe_heckeBetaBar]
  rw [← h2, h1, ← (emb_bijective hℓN hζ w hw).prod_comp (fun σ => σ v), Fintype.prod_option,
    map_mul, map_prod, Finset.prod_range]
  simp only [emb_none_apply, emb_some_apply]
  exact mul_comm _ _

end Norm

section Valuation

local notation "Qb" => AlgebraicClosure ℚ

variable {ℓ : ℕ} [Fact ℓ.Prime] (A : ValuationSubring Qb)

theorem zeta_mem {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : ζ ∈ A := by
  have hprime : ℓ.Prime := Fact.out
  rcases A.mem_or_inv_mem ζ with h | h
  · exact h
  · have h2 : (ζ⁻¹) ^ (ℓ - 1) = ζ := by
      rw [inv_pow]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ, Nat.sub_add_cancel hprime.one_le, hζ.pow_eq_one]
    rw [← h2]
    exact pow_mem h _

def zetaUnit {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) : Aˣ :=
  Units.ofPowEqOne (⟨ζ, zeta_mem A hζ⟩ : A) ℓ
    (Subtype.ext (by
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hζ.pow_eq_one)) (NeZero.ne ℓ)

theorem coe_zetaUnit {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    ((zetaUnit A hζ : A) : Qb) = ζ := rfl

theorem map_subtype_zetaUnit {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Units.map (A.subtype : A →* Qb) (zetaUnit A hζ) = zu hζ :=
  Units.ext rfl

theorem map_residue_zetaUnit [CharP (IsLocalRing.ResidueField A) ℓ]
    {ζ : Qb} (hζ : IsPrimitiveRoot ζ ℓ) :
    Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (zetaUnit A hζ) = 1 := by
  have hzℓ : (Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A)
      (zetaUnit A hζ)) ^ ℓ = 1 := by
    rw [← map_pow, zetaUnit, Units.pow_ofPowEqOne, map_one]
  apply Units.ext
  have h0 : ((Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A)
      (zetaUnit A hζ) : IsLocalRing.ResidueField A) - 1) ^ ℓ = 0 := by
    rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hzℓ, Units.val_one, one_pow, sub_self]
  rw [Units.val_one]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (NeZero.ne ℓ)).mp h0)

end Valuation

end W6FK2
p2m_reactivate "P2MW.S_ModularCurve_kroneckerCongruence_norm_heckeBetaBar.W6FK2"

open W6FK2 in
theorem solution (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (y : LaurentSeries A)
    (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar N) :
    ∃ y' : LaurentSeries A,
      ModularCurve.coeffMap A.subtype y' =
        ((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)
          Algebra.norm (ModularCurve.modularFunctionFieldBar N)
            (ModularCurve.heckeBetaBar (AlgebraicClosure ℚ) N ℓ ⟨ModularCurve.coeffMap A.subtype y, hy⟩) :
            ModularCurve.modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) ∧
      ModularCurve.coeffMap (IsLocalRing.residue A) y' =
        ModularCurve.coeffMap (frobenius (IsLocalRing.ResidueField A) ℓ)
            (ModularCurve.coeffMap (IsLocalRing.residue A) y) *
          ModularCurve.qExpand (IsLocalRing.ResidueField A) ℓ (ModularCurve.coeffMap (IsLocalRing.residue A) y) := by
  haveI : NeZero ((ℓ : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) ℓ
  obtain ⟨w, hw⟩ := exists_AL N ℓ hℓN

  set P : LaurentSeries A :=
    (∏ j ∈ Finset.range ℓ, twist (zetaUnit A hζ ^ j) y) * qExpand A ℓ (qExpand A ℓ y) with hP

  have hnorm := qExpand_norm hℓN hζ w hw
    (heckeBetaBar (AlgebraicClosure ℚ) N ℓ ⟨coeffMap A.subtype y, hy⟩)
  rw [AL_beta hw, coe_heckeAlphaBar, coe_heckeBetaBar] at hnorm
  have hPQ : coeffMap A.subtype P
      = (∏ j ∈ Finset.range ℓ, twist (zu hζ ^ j) (coeffMap A.subtype y))
        * qExpand (AlgebraicClosure ℚ) ℓ (qExpand (AlgebraicClosure ℚ) ℓ (coeffMap A.subtype y)) := by
    rw [hP, map_mul, map_prod, coeffMap_qExpand', coeffMap_qExpand']
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [coeffMap_twist, map_pow, map_subtype_zetaUnit]
  have hPQ' := hPQ.trans hnorm.symm

  have hPsupp : ∀ n : ℤ, ¬ (ℓ : ℤ) ∣ n → P.coeff n = 0 := by
    intro n hn
    have h := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff n) hPQ'
    simp only [coeffMap_coeff, qExpand_coeff_of_not_dvd ℓ _ hn] at h
    exact (map_eq_zero_iff A.subtype (fun a b hab => Subtype.ext hab)).mp h
  refine ⟨unexpand ℓ P, ?_, ?_⟩
  ·
    apply qExpand_injective ℓ
    rw [← coeffMap_qExpand' A.subtype ℓ (unexpand ℓ P), qExpand_unexpand ℓ P hPsupp]
    exact hPQ'
  ·
    apply qExpand_injective ℓ
    rw [← coeffMap_qExpand' (IsLocalRing.residue A) ℓ (unexpand ℓ P), qExpand_unexpand ℓ P hPsupp,
      hP, map_mul, map_prod, coeffMap_qExpand', coeffMap_qExpand',
      Finset.prod_eq_pow_card (b := coeffMap (IsLocalRing.residue A) y), Finset.card_range,
      map_mul, ← coeffMap_qExpand' (frobenius (IsLocalRing.ResidueField A) ℓ) ℓ,
      ← pow_char_eq_coeffMap_frobenius_qExpand ℓ]
    intro j _
    rw [coeffMap_twist, map_pow, map_residue_zetaUnit, one_pow, twist_one]

end
end S_ModularCurve_kroneckerCongruence_norm_heckeBetaBar
end P2MW
export P2MW.S_ModularCurve_kroneckerCongruence_norm_heckeBetaBar (solution)

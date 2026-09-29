-- Prove2me | solution 1 for ModularCurve.JOne.degeneracyPullbackPair_comm_heckeOperatorOneBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/13e2b391-30fe-584a-ba41-33b7503619ee

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1DegeneracyPullback
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaOneBar
import Theorems.Thm_ModularCurve_laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC
import Theorems.Thm_ModularCurve_laurentBaseChange_x1FunctionField_sup_adjoin_qExpand_x1x0FunctionFieldC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace X1DegHecke

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField CongruenceSubgroup HahnSeries"

open scoped MatrixGroups

local notation "𝕂" => AlgebraicClosure ℚ

section Groups

variable (N ℓ q : ℕ)

theorem T_mem_Gamma1_inf_Gamma0 : ModularGroup.T ∈ Gamma1 N ⊓ Gamma0 (N * q) := by
  refine ⟨by simp [Gamma1_mem, ModularGroup.T], ?_⟩
  simp [Gamma0_mem, ModularGroup.T]

scoped instance finiteIndex_Gamma1_inf_Gamma0 [NeZero N] [NeZero q] :
    (Gamma1 N ⊓ Gamma0 (N * q)).FiniteIndex := by
  haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne q)⟩
  infer_instance

variable {N ℓ q}

theorem Gamma0_le_of_dvd' {A B : ℕ} (h : A ∣ B) : Gamma0 B ≤ Gamma0 A := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have := congrArg (ZMod.castHom h (ZMod A)) hγ
  rwa [map_intCast, map_zero] at this

theorem roof_le {N' : ℕ} (h : N ∣ N') : Gamma1 N' ⊓ Gamma0 (N' * q) ≤ Gamma1 N ⊓ Gamma0 (N * q) :=
  inf_le_inf (Gamma1_le_of_dvd h) (Gamma0_le_of_dvd' (mul_dvd_mul_right h q))

theorem cocycle_roof {N' : ℕ} [NeZero ℓ] (h : N * ℓ ∣ N') :
    ∀ γ ∈ Gamma1 N' ⊓ Gamma0 (N' * q), ∃ γ₁ ∈ Gamma1 N ⊓ Gamma0 (N * q),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hγ1' := (Gamma1_mem N' γ).mp hγ1
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  obtain ⟨r, hr⟩ := h
  have hc : (((N' * q : ℕ)) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hc
  rw [hr] at hc'
  push_cast at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (N : ℤ) * q * (r * c'), γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  have hNN' : N ∣ N' := ⟨ℓ * r, by rw [hr]; ring⟩
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Gamma1_mem]
      obtain ⟨h00, h11, -⟩ := hγ1'
      refine ⟨?_, ?_, ?_⟩
      · have := congrArg (ZMod.castHom hNN' (ZMod N)) h00
        rw [map_intCast, map_one] at this; exact this
      · have := congrArg (ZMod.castHom hNN' (ZMod N)) h11
        rw [map_intCast, map_one] at this; exact this
      · show (((N : ℤ) * q * (r * c') : ℤ) : ZMod N) = 0
        push_cast; rw [ZMod.natCast_self]; ring
    · rw [Gamma0_mem]
      show (((N : ℤ) * q * (r * c') : ℤ) : ZMod (N * q)) = 0
      have : (((N * q : ℕ) : ℤ) : ZMod (N * q)) = 0 := by rw [Int.cast_natCast, ZMod.natCast_self]
      push_cast at this ⊢
      rw [this]; ring
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((N : ℤ) * q * (r * c')) = γ 1 0
    linear_combination -hc'
  · rfl

end Groups

section Roofs

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ q : ℕ) {N' : ℕ}

theorem laurentBaseChange_mono' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem coeffEmb_qExpand' (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem qExpand_mem_laurentBaseChange' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpand']
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

abbrev R (M : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (x1x0FunctionFieldC ℚ M (M * q))

variable {L N q}

def roofIncl (h : N ∣ N') : R L q N →ₐ[L] R L q N' :=
  IntermediateField.inclusion (laurentBaseChange_mono' L (qExpFunctionFieldC_mono ℚ (roof_le h)))

@[scoped simp] theorem coe_roofIncl (h : N ∣ N') (x : R L q N) :
    (roofIncl (L := L) (q := q) h x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem qExpand_mem_roof [NeZero N] [NeZero q] [NeZero ℓ] (h : N * ℓ ∣ N') :
    ∀ y ∈ x1x0FunctionFieldC ℚ N (N * q), qExpand ℚ ℓ y ∈ x1x0FunctionFieldC ℚ N' (N' * q) := by
  intro y hy
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ
    (Γ := Gamma1 N ⊓ Gamma0 (N * q)) (T_mem_Gamma1_inf_Gamma0 N q) ℓ (cocycle_roof h)
  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N ⊓ Gamma0 (N * q))) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N ⊓ Gamma0 (N * q)))).map
      (qExpandₐ ℓ) ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N' ⊓ Gamma0 (N' * q))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

def roofSubst [NeZero N] [NeZero q] [NeZero ℓ] (h : N * ℓ ∣ N') : R L q N →ₐ[L] R L q N' where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChange' L ℓ (qExpand_mem_roof ℓ h) x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

@[scoped simp] theorem coe_roofSubst [NeZero N] [NeZero q] [NeZero ℓ] (h : N * ℓ ∣ N') (x : R L q N) :
    (roofSubst (L := L) (q := q) ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

variable [NeZero N] [NeZero q] [NeZero ℓ]

theorem alpha_incl_sq (h : N ∣ N') :
    (heckeAlphaOneBar L N' q).comp (x1LevelInclBar L h)
      = (roofIncl (q := q) h).comp (heckeAlphaOneBar L N q) := by
  apply AlgHom.ext; intro x; apply Subtype.ext
  simp [coe_heckeAlphaOneBar, coe_x1LevelInclBar]

theorem beta_incl_sq (h : N ∣ N') (hβ : HeckeBetaOneDefined N q) (hβ' : HeckeBetaOneDefined N' q) :
    (heckeBetaOneBar L N' q).comp (x1LevelInclBar L h)
      = (roofIncl (q := q) h).comp (heckeBetaOneBar L N q) := by
  apply AlgHom.ext; intro x; apply Subtype.ext
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeBetaOneBar N' q hβ', coe_x1LevelInclBar,
    coe_roofIncl, coe_heckeBetaOneBar N q hβ]

theorem alpha_subst_sq (h : N * ℓ ∣ N') (hβℓ : HeckeBetaOneDefined N ℓ) :
    (heckeAlphaOneBar L N' q).comp (x1LevelSubstBar L ℓ h)
      = (roofSubst (q := q) ℓ h).comp (heckeAlphaOneBar L N q) := by
  apply AlgHom.ext; intro x; apply Subtype.ext
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeAlphaOneBar, coe_x1LevelSubstBar_of L ℓ h hβℓ,
    coe_roofSubst, coe_heckeAlphaOneBar]

theorem beta_subst_sq (h : N * ℓ ∣ N') (hβℓ : HeckeBetaOneDefined N ℓ) (hβ : HeckeBetaOneDefined N q)
    (hβ' : HeckeBetaOneDefined N' q) :
    (heckeBetaOneBar L N' q).comp (x1LevelSubstBar L ℓ h)
      = (roofSubst (q := q) ℓ h).comp (heckeBetaOneBar L N q) := by
  apply AlgHom.ext; intro x; apply Subtype.ext
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeBetaOneBar N' q hβ', coe_x1LevelSubstBar_of L ℓ h hβℓ,
    coe_roofSubst, coe_heckeBetaOneBar N q hβ, qExpand_qExpand, qExpand_qExpand]
  exact qExpand_congr (Nat.mul_comm q ℓ) _

end Roofs

section Exchange

variable {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
  [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
  [HasPrincipalDivisors K A] [HasPrincipalDivisors K B] [HasPrincipalDivisors K E]

theorem pullbackAlong_congr {φ ψ : F →ₐ[K] E} (h : φ = ψ)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h; rfl

theorem pullbackAlong_correspondence
    (α β : F →ₐ[K] A) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (α' β' : B →ₐ[K] E) (hα' : α'.toRingHom.IsIntegral) (hβ' : β'.toRingHom.IsIntegral)
    (ι : F →ₐ[K] B) (hι : ι.toRingHom.IsIntegral) (j : A →ₐ[K] E) (hj : j.toRingHom.IsIntegral)
    (hsqβ : β'.comp ι = j.comp β)
    (hex : ∀ E₀ : Divisor K A, Divisor.pullbackAlong ι hι (Divisor.pushforwardAlong α hα E₀)
      = Divisor.pushforwardAlong α' hα' (Divisor.pullbackAlong j hj E₀))
    (D : Divisor K F) :
    Divisor.pullbackAlong ι hι (Divisor.correspondence β α hβ hα D)
      = Divisor.correspondence β' α' hβ' hα' (Divisor.pullbackAlong ι hι D) := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, hex,
    Divisor.pullbackAlong_pullbackAlong ι β' hι hβ' (RingHom.IsIntegral.trans _ _ hι hβ') D,
    pullbackAlong_congr hsqβ (RingHom.IsIntegral.trans _ _ hι hβ') (RingHom.IsIntegral.trans _ _ hβ hj) D,
    ← Divisor.pullbackAlong_pullbackAlong β j hβ hj (RingHom.IsIntegral.trans _ _ hβ hj) D]

theorem pullbackAlongHom_correspondence
    (α β : F →ₐ[K] A) (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
    (hFIβ : FundamentalIdentityAlong K β hβ) (hfinα : FiniteAlong K α) (hNα : NormFormulaAlong K α hfinα)
    (α' β' : B →ₐ[K] E) (hα' : α'.toRingHom.IsIntegral) (hβ' : β'.toRingHom.IsIntegral)
    (hFIβ' : FundamentalIdentityAlong K β' hβ') (hfinα' : FiniteAlong K α')
    (hNα' : NormFormulaAlong K α' hfinα')
    (ι : F →ₐ[K] B) (hι : ι.toRingHom.IsIntegral) (hFIι : FundamentalIdentityAlong K ι hι)
    (j : A →ₐ[K] E) (hj : j.toRingHom.IsIntegral)
    (hsqβ : β'.comp ι = j.comp β)
    (hex : ∀ E₀ : Divisor K A, Divisor.pullbackAlong ι hι (Divisor.pushforwardAlong α hα E₀)
      = Divisor.pushforwardAlong α' hα' (Divisor.pullbackAlong j hj E₀))
    (x : Pic0 K F) :
    Pic0.pullbackAlongHom ι hι hFIι (Pic0.correspondence β α hβ hα hFIβ hfinα hNα x)
      = Pic0.correspondence β' α' hβ' hα' hFIβ' hfinα' hNα' (Pic0.pullbackAlongHom ι hι hFIι x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk, Pic0.correspondence_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  show Divisor.pullbackAlong ι hι (Divisor.correspondence β α hβ hα (D : Divisor K F))
    = Divisor.correspondence β' α' hβ' hα' (Divisor.pullbackAlong ι hι (D : Divisor K F))
  exact pullbackAlong_correspondence α β hα hβ α' β' hα' hβ' ι hι j hj hsqβ hex D

end Exchange

section Assembly

scoped instance neZero_coe_primes (q : Nat.Primes) : NeZero (q : ℕ) := ⟨q.2.ne_zero⟩

variable (N ℓ N' : ℕ) [NeZero N] [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hN' : N' = N * ℓ)
  (hin : HeckeDiamondInputsAll N) (hin' : HeckeDiamondInputsAll N') (q : Nat.Primes) (hqℓ : (q : ℕ) ≠ ℓ)

def ExchangeIncl (hNN' : N ∣ N') : Prop :=
  ∀ (hα : (heckeAlphaOneBar 𝕂 N q).toRingHom.IsIntegral)
    (hα' : (heckeAlphaOneBar 𝕂 N' q).toRingHom.IsIntegral)
    (hι : (x1LevelInclBar 𝕂 hNN').toRingHom.IsIntegral)
    (hj : (roofIncl (L := 𝕂) (q := q) hNN').toRingHom.IsIntegral)
    [HasPrincipalDivisors 𝕂 (R 𝕂 q N)] [HasPrincipalDivisors 𝕂 (R 𝕂 q N')]
    [HasPrincipalDivisors 𝕂 (x1FunctionFieldBar N')]
    (E₀ : Divisor 𝕂 (R 𝕂 q N)),
    Divisor.pullbackAlong (x1LevelInclBar 𝕂 hNN') hι
        (Divisor.pushforwardAlong (heckeAlphaOneBar 𝕂 N q) hα E₀)
      = Divisor.pushforwardAlong (heckeAlphaOneBar 𝕂 N' q) hα'
          (Divisor.pullbackAlong (roofIncl (L := 𝕂) (q := q) hNN') hj E₀)

def ExchangeSubst (h : N * ℓ ∣ N') : Prop :=
  ∀ (hα : (heckeAlphaOneBar 𝕂 N q).toRingHom.IsIntegral)
    (hα' : (heckeAlphaOneBar 𝕂 N' q).toRingHom.IsIntegral)
    (hι : (x1LevelSubstBar 𝕂 ℓ h).toRingHom.IsIntegral)
    (hj : (roofSubst (L := 𝕂) (q := q) ℓ h).toRingHom.IsIntegral)
    [HasPrincipalDivisors 𝕂 (R 𝕂 q N)] [HasPrincipalDivisors 𝕂 (R 𝕂 q N')]
    [HasPrincipalDivisors 𝕂 (x1FunctionFieldBar N')]
    (E₀ : Divisor 𝕂 (R 𝕂 q N)),
    Divisor.pullbackAlong (x1LevelSubstBar 𝕂 ℓ h) hι
        (Divisor.pushforwardAlong (heckeAlphaOneBar 𝕂 N q) hα E₀)
      = Divisor.pushforwardAlong (heckeAlphaOneBar 𝕂 N' q) hα'
          (Divisor.pullbackAlong (roofSubst (L := 𝕂) (q := q) ℓ h) hj E₀)

include hℓ hN' hin hin' hqℓ in

theorem pair_heckeOperatorOneBar_comm
    (hjI : ∀ hNN' : N ∣ N', (roofIncl (L := 𝕂) (q := q) hNN').toRingHom.IsIntegral)
    (hjS : ∀ h : N * ℓ ∣ N', (roofSubst (L := 𝕂) (q := q) ℓ h).toRingHom.IsIntegral)
    (hexI : ∀ hNN' : N ∣ N', ExchangeIncl N N' q hNN')
    (hexS : ∀ h : N * ℓ ∣ N', ExchangeSubst N ℓ N' q h)
    (i : Fin 2) (x : JOne N) :
    JOne.degeneracyPullbackPair N N' ℓ i (heckeOperatorOneBar N q x) =
      heckeOperatorOneBar N' q (JOne.degeneracyPullbackPair N N' ℓ i x) := by
  haveI : NeZero N' := ⟨by rw [hN']; exact mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩

  obtain ⟨hβd, hα, hβ, hP, hfin, hFI, hNf⟩ := hin.1 q
  obtain ⟨hβd', hα', hβ', hP', hfin', hFI', hNf'⟩ := hin'.1 q
  haveI := hP; haveI := hP'
  have eN : ∀ y : JOne N, heckeOperatorOneBar N q y = heckePic0OneBar hα hβ hFI hfin hNf y := fun y => by
    rw [heckeOperatorOneBar_apply]
    exact DFunLike.congr_fun (heckeOperatorOneAlong_eq hβd hα hβ hFI hfin hNf) y
  have eN' : ∀ y : JOne N', heckeOperatorOneBar N' q y = heckePic0OneBar hα' hβ' hFI' hfin' hNf' y := fun y => by
    rw [heckeOperatorOneBar_apply]
    exact DFunLike.congr_fun (heckeOperatorOneAlong_eq hβd' hα' hβ' hFI' hfin' hNf') y
  by_cases hinp : JOne.DegeneracyPullbackInputs N N' ℓ
  · obtain ⟨hdvd, hβℓ, h₁, h₂, hPt, hFI₁, hFI₂⟩ := hinp
    haveI := hPt
    rw [eN, eN', JOne.degeneracyPullbackPair_eq hdvd hβℓ h₁ h₂ hFI₁ hFI₂]
    revert i
    refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
    · simp only [Matrix.cons_val_zero]
      exact pullbackAlongHom_correspondence (heckeAlphaOneBar 𝕂 N q) (heckeBetaOneBar 𝕂 N q) hα hβ
        hFI hfin hNf (heckeAlphaOneBar 𝕂 N' q) (heckeBetaOneBar 𝕂 N' q) hα' hβ' hFI' hfin' hNf'
        (x1LevelInclBar 𝕂 _) h₁ hFI₁ (roofIncl (L := 𝕂) (q := q) _) (hjI _)
        (beta_incl_sq (L := 𝕂) _ hβd hβd') (fun E₀ => hexI _ hα hα' h₁ (hjI _) E₀) x
    · simp only [Matrix.cons_val_one]
      exact pullbackAlongHom_correspondence (heckeAlphaOneBar 𝕂 N q) (heckeBetaOneBar 𝕂 N q) hα hβ
        hFI hfin hNf (heckeAlphaOneBar 𝕂 N' q) (heckeBetaOneBar 𝕂 N' q) hα' hβ' hFI' hfin' hNf'
        (x1LevelSubstBar 𝕂 ℓ hdvd) h₂ hFI₂ (roofSubst (L := 𝕂) (q := q) ℓ hdvd) (hjS hdvd)
        (beta_subst_sq (L := 𝕂) ℓ hdvd hβℓ hβd hβd') (fun E₀ => hexS hdvd hα hα' h₂ (hjS hdvd) E₀) x
  · rw [JOne.degeneracyPullbackPair_apply_of_not hinp, JOne.degeneracyPullbackPair_apply_of_not hinp]
    exact (map_zero (heckeOperatorOneBar N' q)).symm

end Assembly

section RoofIntegral

namespace RoofGeneric

open Cardinal IntermediateField

section Exchange

variable {L E : Type*} [Field L] [Field E] [Algebra L E]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem isAlgebraic_algebraAdjoin {x : E} [Algebra.IsAlgebraic L⟮x⟯ E] :
    Algebra.IsAlgebraic (Algebra.adjoin L ({x} : Set E)) E :=
  Algebra.IsAlgebraic.trans (Algebra.adjoin L ({x} : Set E)) L⟮x⟯ E

theorem isAlgebraic_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [Algebra.IsAlgebraic L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    Algebra.IsAlgebraic L⟮y⟯ E := by
  have indx : AlgebraicIndependent L (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have indy : AlgebraicIndependent L (fun _ : Unit => y) :=
    algebraicIndependent_unique_type_iff.mpr hy
  have hrx : Set.range (fun _ : Unit => x) = {x} := Set.range_const
  have hry : Set.range (fun _ : Unit => y) = {y} := Set.range_const
  have algx : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun _ : Unit => x)) E := by
    rw [hrx]
    exact isAlgebraic_algebraAdjoin
  have basx : IsTranscendenceBasis L (fun _ : Unit => x) :=
    indx.isTranscendenceBasis_iff_isAlgebraic.mpr algx
  have basy : IsTranscendenceBasis L (fun _ : Unit => y) :=
    indy.isTranscendenceBasis_of_lift_trdeg_le_of_finite (le_of_eq basx.lift_cardinalMk_eq_trdeg.symm)
  have h := basy.isAlgebraic_field
  rwa [hry] at h

theorem finiteDimensional_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [FiniteDimensional L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    FiniteDimensional L⟮y⟯ E := by
  haveI : Algebra.IsAlgebraic L⟮y⟯ E := isAlgebraic_adjoin_of_transcendental hx hy
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite L⟮x⟯ E)
  set S : Set E := insert x (↑s : Set E) with hS
  haveI : Finite S := (s.finite_toSet.insert x).to_subtype
  set K' : IntermediateField L⟮y⟯ E := IntermediateField.adjoin L⟮y⟯ S with hK'def
  haveI hK'fin : FiniteDimensional L⟮y⟯ K' :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

  have hxK' : x ∈ K' := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hLx_le : ∀ c : L⟮x⟯, (c : E) ∈ K' := by
    intro c
    have hle : L⟮x⟯ ≤ K'.restrictScalars L := IntermediateField.adjoin_simple_le_iff.mpr hxK'
    exact hle c.2

  have hK' : K' = ⊤ := by
    suffices h : ∀ e : E, e ∈ K' from eq_top_iff.mpr fun e _ => h e
    intro e
    have he : e ∈ Submodule.span L⟮x⟯ (↑s : Set E) := by rw [hs]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul c z _ hz =>
        rw [IntermediateField.smul_def, smul_eq_mul] at *
        show (c : E) * z ∈ K'
        exact mul_mem (hLx_le c) hz
  have htop : FiniteDimensional L⟮y⟯ (⊤ : IntermediateField L⟮y⟯ E) := by
    rw [← hK']; exact hK'fin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := L⟮y⟯) (E := E)).toLinearEquiv

end Exchange

section Along

variable {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']

private theorem _root_.X1DegHecke.RoofGeneric.finiteAlong_of_transcendental (φ : F →ₐ[L] F') {x₀ : F} (hx₀ : Transcendental L x₀)
    {x₁ : F'} (hx₁ : Transcendental L x₁) [FiniteDimensional L⟮x₁⟯ F'] :
    AlgebraicCurve.FiniteAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ

  have hy₀ : Transcendental L (φ x₀) := by
    have h := (transcendental_algebraMap_iff (R := L) (S := F) (A := F')
      (φ.toRingHom.injective)).mpr hx₀
    exact h
  haveI hfin : FiniteDimensional L⟮φ x₀⟯ F' := finiteDimensional_adjoin_of_transcendental hx₁ hy₀

  set E₀ : IntermediateField L F := L⟮x₀⟯ with hE₀
  have hmap : E₀.map φ = L⟮φ x₀⟯ := by
    rw [hE₀, IntermediateField.adjoin_map, Set.image_singleton]
  let e : E₀ ≃ₐ[L] L⟮φ x₀⟯ := (E₀.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : E₀, ((e w : L⟮φ x₀⟯) : F') = φ (w : F) := by
    intro w
    rfl
  letI : Algebra E₀ F' := ((algebraMap F F').comp (algebraMap E₀ F)).toAlgebra
  haveI : IsScalarTower E₀ F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E₀ F' := by
    refine Module.Finite.of_equiv_equiv (A₁ := L⟮φ x₀⟯) (B₁ := F') (A₂ := E₀) (B₂ := F')
      e.symm.toRingEquiv (RingEquiv.refl F') ?_
    refine RingHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.refl_apply]
    rw [show e.symm.toRingEquiv (e w) = w from e.symm_apply_apply w]
    show φ (w : F) = ((e w : L⟮φ x₀⟯) : F')
    rw [he]
  show Module.Finite F F'
  exact Module.Finite.of_restrictScalars_finite E₀ F F'

p2m_export "X1DegHecke.RoofGeneric" "finiteAlong_of_transcendental"

theorem isIntegral_of_finiteAlong (φ : F →ₐ[L] F') (h : AlgebraicCurve.FiniteAlong L φ) :
    φ.toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := h
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  exact fun x => Algebra.IsIntegral.isIntegral x

end Along

end RoofGeneric

open scoped IntermediateField in

theorem exists_transcendental_finiteDimensional_roof' (L : Type*) [Field L] [Algebra ℚ L]
    (M q : ℕ) [NeZero M] [NeZero q] :
    ∃ x : R L q M, Transcendental L x ∧ FiniteDimensional L⟮x⟯ (R L q M) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (Gamma1 M ⊓ Gamma0 (M * q)) (T_mem_Gamma1_inf_Gamma0 M q)

theorem isIntegral_roofMap (L : Type*) [Field L] [Algebra ℚ L] {M M' q : ℕ} [NeZero M] [NeZero M']
    [NeZero q] (φ : R L q M →ₐ[L] R L q M') : φ.toRingHom.IsIntegral := by
  obtain ⟨x₀, hx₀, -⟩ := exists_transcendental_finiteDimensional_roof' L M q
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_roof' L M' q
  haveI := hfin
  exact RoofGeneric.isIntegral_of_finiteAlong φ (RoofGeneric.finiteAlong_of_transcendental φ hx₀ hx₁)

end RoofIntegral

end X1DegHecke
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

end
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

noncomputable section

namespace X1DegHecke

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField CongruenceSubgroup"

open scoped MatrixGroups IntermediateField

local notation "𝕂" => AlgebraicClosure ℚ

section GlueGeneric

variable {K L₀ : Type*} [Field K] [Field L₀] [Algebra K L₀]
variable {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B]

theorem adjoin_range_union_range_eq_top (E EA EB : IntermediateField K L₀)
    (u : A →ₐ[K] E) (v : B →ₐ[K] E) (hu : u.toRingHom.IsIntegral)
    (hA : EA ≤ IntermediateField.adjoin K (Set.range fun z : A => ((u z : E) : L₀)))
    (hB : EB ≤ IntermediateField.adjoin K (Set.range fun z : B => ((v z : E) : L₀)))
    (hGEN : E ≤ EA ⊔ EB) :
    Algebra.adjoin K (Set.range u ∪ Set.range v) = ⊤ := by
  set S : Subalgebra K E := Algebra.adjoin K (Set.range u ∪ Set.range v) with hSdef

  have hinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    letI := AlgebraicCurve.algebraAlong u
    let S₁ : Subalgebra A E :=
      { S.toSubsemiring with
        algebraMap_mem' := fun k => Algebra.subset_adjoin (Or.inl (Set.mem_range_self k)) }
    intro x hx
    have hint : IsIntegral A x := hu x
    have halg : IsAlgebraic A x := hint.isAlgebraic
    exact Subalgebra.inv_mem_of_algebraic S₁ (x := ⟨x, hx⟩) halg
  let T : IntermediateField K E := S.toIntermediateField hinv
  have hle : E ≤ IntermediateField.lift T := by
    refine hGEN.trans (sup_le (hA.trans ?_) (hB.trans ?_))
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact (IntermediateField.mem_lift (u z)).mpr (Algebra.subset_adjoin (Or.inl (Set.mem_range_self z)))
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact (IntermediateField.mem_lift (v z)).mpr (Algebra.subset_adjoin (Or.inr (Set.mem_range_self z)))
  have hTtop : T = ⊤ := by
    apply IntermediateField.lift_injective E
    rw [IntermediateField.lift_top]
    exact le_antisymm (IntermediateField.lift_le T) hle
  have h := congrArg IntermediateField.toSubalgebra hTtop
  rwa [toSubalgebra_toIntermediateField, IntermediateField.top_toSubalgebra] at h

end GlueGeneric
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

namespace FiniteGeneric

open Cardinal

section Exchange

variable {L E : Type*} [Field L] [Field E] [Algebra L E]

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isAlgebraic_algebraAdjoin {x : E} [Algebra.IsAlgebraic L⟮x⟯ E] :
    Algebra.IsAlgebraic (Algebra.adjoin L ({x} : Set E)) E :=
  Algebra.IsAlgebraic.trans (Algebra.adjoin L ({x} : Set E)) L⟮x⟯ E

theorem isAlgebraic_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [Algebra.IsAlgebraic L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    Algebra.IsAlgebraic L⟮y⟯ E := by
  have indx : AlgebraicIndependent L (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have indy : AlgebraicIndependent L (fun _ : Unit => y) :=
    algebraicIndependent_unique_type_iff.mpr hy
  have hrx : Set.range (fun _ : Unit => x) = {x} := Set.range_const
  have hry : Set.range (fun _ : Unit => y) = {y} := Set.range_const
  have algx : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range fun _ : Unit => x)) E := by
    rw [hrx]
    exact isAlgebraic_algebraAdjoin
  have basx : IsTranscendenceBasis L (fun _ : Unit => x) :=
    indx.isTranscendenceBasis_iff_isAlgebraic.mpr algx
  have basy : IsTranscendenceBasis L (fun _ : Unit => y) :=
    indy.isTranscendenceBasis_of_lift_trdeg_le_of_finite (le_of_eq basx.lift_cardinalMk_eq_trdeg.symm)
  have h := basy.isAlgebraic_field
  rwa [hry] at h

theorem finiteDimensional_adjoin_of_transcendental {x : E} (hx : Transcendental L x)
    [FiniteDimensional L⟮x⟯ E] {y : E} (hy : Transcendental L y) :
    FiniteDimensional L⟮y⟯ E := by
  haveI : Algebra.IsAlgebraic L⟮y⟯ E := isAlgebraic_adjoin_of_transcendental hx hy
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite L⟮x⟯ E)
  set S : Set E := insert x (↑s : Set E) with hS
  haveI : Finite S := (s.finite_toSet.insert x).to_subtype
  set K' : IntermediateField L⟮y⟯ E := IntermediateField.adjoin L⟮y⟯ S with hK'def
  haveI hK'fin : FiniteDimensional L⟮y⟯ K' :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  have hxK' : x ∈ K' := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hLx_le : ∀ c : L⟮x⟯, (c : E) ∈ K' := by
    intro c
    have hle : L⟮x⟯ ≤ K'.restrictScalars L := IntermediateField.adjoin_simple_le_iff.mpr hxK'
    exact hle c.2
  have hK' : K' = ⊤ := by
    suffices h : ∀ e : E, e ∈ K' from eq_top_iff.mpr fun e _ => h e
    intro e
    have he : e ∈ Submodule.span L⟮x⟯ (↑s : Set E) := by rw [hs]; exact Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul c z _ hz =>
        rw [IntermediateField.smul_def, smul_eq_mul] at *
        show (c : E) * z ∈ K'
        exact mul_mem (hLx_le c) hz
  have htop : FiniteDimensional L⟮y⟯ (⊤ : IntermediateField L⟮y⟯ E) := by
    rw [← hK']; exact hK'fin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := L⟮y⟯) (E := E)).toLinearEquiv

end Exchange
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

section Along

variable {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']

private theorem _root_.X1DegHecke.FiniteGeneric.finiteAlong_of_transcendental (φ : F →ₐ[L] F') {x₀ : F} (hx₀ : Transcendental L x₀)
    {x₁ : F'} (hx₁ : Transcendental L x₁) [FiniteDimensional L⟮x₁⟯ F'] :
    AlgebraicCurve.FiniteAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ

  have hy₀ : Transcendental L (φ x₀) := by
    have h := (transcendental_algebraMap_iff (R := L) (S := F) (A := F')
      (φ.toRingHom.injective)).mpr hx₀
    exact h
  haveI hfin : FiniteDimensional L⟮φ x₀⟯ F' := finiteDimensional_adjoin_of_transcendental hx₁ hy₀

  set E₀ : IntermediateField L F := L⟮x₀⟯ with hE₀
  have hmap : E₀.map φ = L⟮φ x₀⟯ := by
    rw [hE₀, IntermediateField.adjoin_map, Set.image_singleton]
  let e : E₀ ≃ₐ[L] L⟮φ x₀⟯ := (E₀.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : E₀, ((e w : L⟮φ x₀⟯) : F') = φ (w : F) := by
    intro w
    rfl
  letI : Algebra E₀ F' := ((algebraMap F F').comp (algebraMap E₀ F)).toAlgebra
  haveI : IsScalarTower E₀ F F' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite E₀ F' := by
    refine Module.Finite.of_equiv_equiv (A₁ := L⟮φ x₀⟯) (B₁ := F') (A₂ := E₀) (B₂ := F')
      e.symm.toRingEquiv (RingEquiv.refl F') ?_
    refine RingHom.ext fun z => ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, RingEquiv.refl_apply]
    rw [show e.symm.toRingEquiv (e w) = w from e.symm_apply_apply w]
    show φ (w : F) = ((e w : L⟮φ x₀⟯) : F')
    rw [he]
  show Module.Finite F F'
  exact Module.Finite.of_restrictScalars_finite E₀ F F'

p2m_export "X1DegHecke.FiniteGeneric" "finiteAlong_of_transcendental"

private theorem _root_.X1DegHecke.FiniteGeneric.isIntegral_of_finiteAlong (φ : F →ₐ[L] F') (h : AlgebraicCurve.FiniteAlong L φ) :
    φ.toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := h
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  exact fun x => Algebra.IsIntegral.isIntegral x

p2m_export "X1DegHecke.FiniteGeneric" "isIntegral_of_finiteAlong"
end Along
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

end FiniteGeneric
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

section Witnesses

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem exists_transcendental_finiteDimensional_x1 (M : ℕ) [NeZero M] :
    ∃ x : laurentBaseChange L (x1FunctionField M), Transcendental L x ∧
      FiniteDimensional L⟮x⟯ (laurentBaseChange L (x1FunctionField M)) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (Gamma1 M)
    (Subgroup.mem_inf.mp (T_mem_Gamma1_inf_Gamma0 M 1)).1

theorem exists_transcendental_finiteDimensional_roof (M : ℕ) [NeZero M] (t : ℕ) [NeZero t] :
    ∃ x : R L t M, Transcendental L x ∧ FiniteDimensional L⟮x⟯ (R L t M) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (Gamma1 M ⊓ Gamma0 (M * t)) (T_mem_Gamma1_inf_Gamma0 M t)

theorem finiteAlong_x1_roof {N : ℕ} [NeZero N] (M : ℕ) [NeZero M] (t : ℕ) [NeZero t]
    (φ : laurentBaseChange L (x1FunctionField N) →ₐ[L] R L t M) : FiniteAlong L φ := by
  obtain ⟨x₀, hx₀, -⟩ := exists_transcendental_finiteDimensional_x1 L N
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_roof L M t
  haveI := hfin
  exact FiniteGeneric.finiteAlong_of_transcendental _ hx₀ hx₁

theorem charZero_of_algebraRat' : CharZero L :=
  charZero_of_injective_algebraMap (algebraMap ℚ L).injective

scoped instance charZero_x1Bar (N : ℕ) : CharZero (laurentBaseChange L (x1FunctionField N)) := by
  haveI : CharZero L := charZero_of_algebraRat' L
  exact charZero_of_injective_algebraMap (algebraMap L _).injective

theorem T_mem_Gamma1' (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem cocycle₁ (M ℓ : ℕ) [NeZero ℓ] : ∀ γ ∈ Gamma1 M ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ Gamma1 M,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓc : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := hMℓc
  rw [Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (M : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma1_mem] at hγ1 ⊢
    obtain ⟨h00, h11, -⟩ := hγ1
    refine ⟨h00, h11, ?_⟩
    show (((M : ℤ) * c' : ℤ) : ZMod M) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((M : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

theorem heckeBetaOneDefined' (N t : ℕ) [NeZero N] [NeZero t] : HeckeBetaOneDefined N t := by
  intro y hy
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_Gamma1' N) t (cocycle₁ N t)
  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N)) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N))).map (qExpandₐ t)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 N ⊓ Gamma0 (N * t))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

end Witnesses
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

section Exchange5

theorem dvd_mul_iff_of_prime_ne {N ℓ : ℕ} (hℓ : ℓ.Prime) (q : Nat.Primes) (hqℓ : (q : ℕ) ≠ ℓ) :
    (q : ℕ) ∣ N * ℓ ↔ (q : ℕ) ∣ N := by
  refine ⟨fun h => ?_, fun h => h.mul_right ℓ⟩
  rcases (Nat.Prime.dvd_mul q.2).mp h with h | h
  · exact h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq q.2 hℓ).mp h) hqℓ

theorem finrank_LD (N : ℕ) [NeZero N] (ℓ : ℕ) (hℓ : ℓ.Prime) (N' : ℕ) (hN' : N' = N * ℓ)
    (q : Nat.Primes) (hqℓ : (q : ℕ) ≠ ℓ)
    {ι : laurentBaseChange 𝕂 (x1FunctionField N) →ₐ[𝕂] laurentBaseChange 𝕂 (x1FunctionField N')}
    {j : R 𝕂 q N →ₐ[𝕂] R 𝕂 q N'}
    (hsq : (heckeAlphaOneBar 𝕂 N' q).comp ι = j.comp (heckeAlphaOneBar 𝕂 N q)) :
    finrankAlong 𝕂 (j.comp (heckeAlphaOneBar 𝕂 N q))
      = finrankAlong 𝕂 (heckeAlphaOneBar 𝕂 N q) * finrankAlong 𝕂 ι := by
  haveI : NeZero N' := ⟨by rw [hN']; exact mul_ne_zero (NeZero.ne N) hℓ.ne_zero⟩
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hiff : (q : ℕ) ∣ N' ↔ (q : ℕ) ∣ N := by rw [hN']; exact dvd_mul_iff_of_prime_ne hℓ q hqℓ
  rw [← hsq, AlgebraicCurve.finrankAlong_comp, ModularCurve.finrankAlong_heckeAlphaOneBar,
    ModularCurve.finrankAlong_heckeAlphaOneBar]
  simp only [hiff]
  exact mul_comm _ _

theorem exchangeIncl (N : ℕ) [NeZero N] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (N' : ℕ)
    (hN' : N' = N * ℓ) (q : Nat.Primes) (hqℓ : (q : ℕ) ≠ ℓ) (hNN' : N ∣ N') :
    ExchangeIncl N N' q hNN' := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero N' := ⟨by rw [hN']; exact mul_ne_zero (NeZero.ne N) hℓ.ne_zero⟩
  intro hα hα' hι hj hP₁ hP₂ hP₃ E₀
  have hsq := alpha_incl_sq (L := 𝕂) (q := q) hNN'
  refine AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (heckeAlphaOneBar 𝕂 N q) (x1LevelInclBar 𝕂 hNN') (roofIncl (L := 𝕂) (q := q) hNN')
    (heckeAlphaOneBar 𝕂 N' q) hα hι hj hα' hsq ?_ ?_ ?_ ?_ E₀
  · exact finiteAlong_x1_roof 𝕂 N' q _
  · exact AlgebraicCurve.separableAlong_of_charZero _ (RingHom.IsIntegral.trans _ _ hα hj)
  · rw [Set.union_comm]
    refine adjoin_range_union_range_eq_top (R 𝕂 q N') (laurentBaseChange 𝕂 (x1FunctionField N'))
      (R 𝕂 q N) (heckeAlphaOneBar 𝕂 N' q) (roofIncl (L := 𝕂) (q := q) hNN') hα' ?_ ?_ ?_
    · intro y hy
      exact IntermediateField.subset_adjoin _ _ ⟨⟨y, hy⟩, coe_heckeAlphaOneBar N' q _⟩
    · intro y hy
      exact IntermediateField.subset_adjoin _ _ ⟨⟨y, hy⟩, coe_roofIncl hNN' _⟩
    · exact (ModularCurve.laurentBaseChange_x1FunctionField_sup_x1x0FunctionFieldC 𝕂 N ℓ q
        ((Nat.coprime_primes hℓ q.2).mpr (Ne.symm hqℓ)) N' hN').ge
  · exact finrank_LD N ℓ hℓ N' hN' q hqℓ hsq

theorem exchangeSubst (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (N' : ℕ)
    (hN' : N' = N * ℓ) (q : Nat.Primes) (hqℓ : (q : ℕ) ≠ ℓ) (h : N * ℓ ∣ N') :
    ExchangeSubst N ℓ N' q h := by
  haveI : NeZero N' := ⟨by rw [hN']; exact mul_ne_zero (NeZero.ne N) hℓ.ne_zero⟩
  intro hα hα' hι hj hP₁ hP₂ hP₃ E₀
  have hsq := alpha_subst_sq (L := 𝕂) (q := q) ℓ h (heckeBetaOneDefined' N ℓ)
  refine AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (heckeAlphaOneBar 𝕂 N q) (x1LevelSubstBar 𝕂 ℓ h) (roofSubst (L := 𝕂) (q := q) ℓ h)
    (heckeAlphaOneBar 𝕂 N' q) hα hι hj hα' hsq ?_ ?_ ?_ ?_ E₀
  · exact finiteAlong_x1_roof 𝕂 N' q _
  · exact AlgebraicCurve.separableAlong_of_charZero _ (RingHom.IsIntegral.trans _ _ hα hj)
  · rw [Set.union_comm]
    refine adjoin_range_union_range_eq_top (R 𝕂 q N') (laurentBaseChange 𝕂 (x1FunctionField N'))
      (IntermediateField.adjoin 𝕂 (qExpand 𝕂 ℓ '' (R 𝕂 q N : Set (LaurentSeries 𝕂))))
      (heckeAlphaOneBar 𝕂 N' q) (roofSubst (L := 𝕂) (q := q) ℓ h) hα' ?_ ?_ ?_
    · intro y hy
      exact IntermediateField.subset_adjoin _ _ ⟨⟨y, hy⟩, coe_heckeAlphaOneBar N' q _⟩
    · refine IntermediateField.adjoin.mono _ _ _ ?_
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, coe_roofSubst ℓ h _⟩
    · exact (ModularCurve.laurentBaseChange_x1FunctionField_sup_adjoin_qExpand_x1x0FunctionFieldC 𝕂 N ℓ q
        N' hN').ge
  · exact finrank_LD N ℓ hℓ N' hN' q hqℓ hsq

end Exchange5
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

end X1DegHecke
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

end
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

noncomputable section

namespace X1DegHecke

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental"

local notation "𝕂" => AlgebraicClosure ℚ

theorem c2a (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (N' : ℕ) (hN' : N' = N * ℓ)
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hin' : ModularCurve.HeckeDiamondInputsAll N')
    (i : Fin 2) (x : ModularCurve.JOne N) :
    ∀ q : Nat.Primes, (q : ℕ) ≠ ℓ →
      ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i (ModularCurve.heckeOperatorOneBar N q x) =
        ModularCurve.heckeOperatorOneBar N' q (ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i x) := by
  intro q hqℓ
  haveI : NeZero N' := ⟨by rw [hN']; exact mul_ne_zero (NeZero.ne N) (NeZero.ne ℓ)⟩
  exact pair_heckeOperatorOneBar_comm N ℓ N' hℓ hN' hin hin' q hqℓ
    (fun _ => isIntegral_roofMap 𝕂 _) (fun _ => isIntegral_roofMap 𝕂 _)
    (fun hNN' => exchangeIncl N ℓ hℓ hℓN N' hN' q hqℓ hNN') (fun h => exchangeSubst N ℓ hℓ hℓN N' hN' q hqℓ h) i x

end X1DegHecke
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

end
p2m_reactivate "P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar.X1DegHecke"

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (N' : ℕ) (hN' : N' = N * ℓ)
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hin' : ModularCurve.HeckeDiamondInputsAll N')
    (i : Fin 2) (x : ModularCurve.JOne N) :
    ∀ q : Nat.Primes, (q : ℕ) ≠ ℓ →
      ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i (ModularCurve.heckeOperatorOneBar N q x) =
        ModularCurve.heckeOperatorOneBar N' q (ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i x) :=
  X1DegHecke.c2a N ℓ hℓ hℓN N' hN' hin hin' i x

end S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar
end P2MW
export P2MW.S_ModularCurve_JOne_degeneracyPullbackPair_comm_heckeOperatorOneBar (solution)

-- Prove2me | solution 1 for ModularCurve.JH.heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cca3a33f-d707-5ff8-8665-cc3415994498

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pullbackAlong
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top
import Theorems.Thm_AlgebraicCurve_finiteAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_comp
import Theorems.Thm_AlgebraicCurve_finrankAlong_id
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_xHTopFunctionFieldC
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd
import Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaHBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.ProjectiveLine.map_mk ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace XHDegHecke

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField CongruenceSubgroup HahnSeries"

open scoped MatrixGroups

local notation "𝕂" => AlgebraicClosure ℚ

section Groups

variable (N ℓ q : ℕ)

theorem T_mem_GammaH_inf_Gamma0 (HN : Subgroup (ZMod N)ˣ) :
    ModularGroup.T ∈ CohCarrier.GammaH N HN ⊓ Gamma0 (N * q) := by
  refine ⟨translation_mem_GammaH N HN, ?_⟩
  simp [Gamma0_mem, ModularGroup.T]

scoped instance finiteIndex_GammaH [NeZero N] (HN : Subgroup (ZMod N)ˣ) : (CohCarrier.GammaH N HN).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH N HN)

scoped instance finiteIndex_GammaH_inf_Gamma0 [NeZero N] [NeZero q] (HN : Subgroup (ZMod N)ˣ) :
    (CohCarrier.GammaH N HN ⊓ Gamma0 (N * q)).FiniteIndex := by
  haveI : NeZero (N * q) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne q)⟩
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (N * q)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right N q)).trans (Gamma1_le_GammaH N HN)

variable {N ℓ q}

theorem Gamma0_le_of_dvd' {A B : ℕ} (h : A ∣ B) : Gamma0 B ≤ Gamma0 A := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have := congrArg (ZMod.castHom h (ZMod A)) hγ
  rwa [map_intCast, map_zero] at this

theorem roof_le {N' : ℕ} {HN : Subgroup (ZMod N)ˣ} {HN' : Subgroup (ZMod N')ˣ} (h : N ∣ N')
    (hle : CohCarrier.GammaH N' HN' ≤ CohCarrier.GammaH N HN) :
    CohCarrier.GammaH N' HN' ⊓ Gamma0 (N' * q) ≤ CohCarrier.GammaH N HN ⊓ Gamma0 (N * q) :=
  inf_le_inf hle (Gamma0_le_of_dvd' (mul_dvd_mul_right h q))

theorem cocycle_roof {N' : ℕ} [NeZero ℓ] {HN : Subgroup (ZMod N)ˣ} {HN' : Subgroup (ZMod N')ˣ}
    (h : N * ℓ ∣ N') (hle : CohCarrier.GammaH N' HN' ≤ CohCarrier.GammaH N HN) :
    ∀ γ ∈ CohCarrier.GammaH N' HN' ⊓ Gamma0 (N' * q), ∃ γ₁ ∈ CohCarrier.GammaH N HN ⊓ Gamma0 (N * q),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγH', hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hγH : γ ∈ CohCarrier.GammaH N HN := hle hγH'
  obtain ⟨hγ0N, hγu⟩ := CohCarrier.mem_GammaH_iff.mp hγH
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
  set γ₁ : SL(2, ℤ) := ⟨_, hdet'⟩ with hγ₁
  have hγ₁0 : γ₁ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show (((N : ℤ) * q * (r * c') : ℤ) : ZMod N) = 0
    push_cast; rw [ZMod.natCast_self]; ring
  refine ⟨γ₁, ?_, rfl, rfl, ?_, rfl⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [CohCarrier.mem_GammaH_iff]
      refine ⟨hγ₁0, ?_⟩

      have hu : CohCarrier.gamma0Units N ⟨γ₁, hγ₁0⟩ = CohCarrier.gamma0Units N ⟨γ, hγ0N⟩ := by
        ext
        simp [CohCarrier.gamma0Units, Gamma0Map, hγ₁]
      rw [hu]; exact hγu
    · rw [Gamma0_mem]
      show (((N : ℤ) * q * (r * c') : ℤ) : ZMod (N * q)) = 0
      have : (((N * q : ℕ) : ℤ) : ZMod (N * q)) = 0 := by rw [Int.cast_natCast, ZMod.natCast_self]
      push_cast at this ⊢
      rw [this]; ring
  · show (ℓ : ℤ) * ((N : ℤ) * q * (r * c')) = γ 1 0
    linear_combination -hc'

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

abbrev R (M : ℕ) (HM : Subgroup (ZMod M)ˣ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (xHTopFunctionFieldC ℚ M HM (M * q))

variable {L N q}
variable {HN : Subgroup (ZMod N)ˣ} {HN' : Subgroup (ZMod N')ˣ}

def roofIncl (h : N ∣ N') (hle : CohCarrier.GammaH N' HN' ≤ CohCarrier.GammaH N HN) :
    R L q N HN →ₐ[L] R L q N' HN' :=
  IntermediateField.inclusion (laurentBaseChange_mono' L (qExpFunctionFieldC_mono ℚ (roof_le h hle)))

@[scoped simp] theorem coe_roofIncl (h : N ∣ N') (hle : CohCarrier.GammaH N' HN' ≤ CohCarrier.GammaH N HN) (x : R L q N HN) :
    (roofIncl (L := L) (q := q) h hle x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

theorem qExpand_mem_roof [NeZero N] [NeZero q] [NeZero ℓ] (h : N * ℓ ∣ N')
    (hle : CohCarrier.GammaH N' HN' ≤ CohCarrier.GammaH N HN) :
    ∀ y ∈ xHTopFunctionFieldC ℚ N HN (N * q), qExpand ℚ ℓ y ∈ xHTopFunctionFieldC ℚ N' HN' (N' * q) := by
  intro y hy
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ
    (Γ := CohCarrier.GammaH N HN ⊓ Gamma0 (N * q)) (T_mem_GammaH_inf_Gamma0 N q HN) ℓ (cocycle_roof h hle)
  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH N HN ⊓ Gamma0 (N * q))) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH N HN ⊓ Gamma0 (N * q)))).map
      (qExpandₐ ℓ) ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH N' HN' ⊓ Gamma0 (N' * q))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

def roofSubst [NeZero N] [NeZero q] [NeZero ℓ] (h : N * ℓ ∣ N')
    (hle : CohCarrier.GammaH N' HN' ≤ CohCarrier.GammaH N HN) : R L q N HN →ₐ[L] R L q N' HN' where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChange' L ℓ (qExpand_mem_roof ℓ h hle) x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

@[scoped simp] theorem coe_roofSubst [NeZero N] [NeZero q] [NeZero ℓ] (h : N * ℓ ∣ N')
    (hle : CohCarrier.GammaH N' HN' ≤ CohCarrier.GammaH N HN) (x : R L q N HN) :
    (roofSubst (L := L) (q := q) ℓ h hle x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

end Roofs

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

theorem finiteAlong_of_transcendental (φ : F →ₐ[L] F') {x₀ : F} (hx₀ : Transcendental L x₀)
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

theorem isIntegral_of_finiteAlong (φ : F →ₐ[L] F') (h : AlgebraicCurve.FiniteAlong L φ) :
    φ.toRingHom.IsIntegral := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI : Module.Finite F F' := h
  haveI : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  exact fun x => Algebra.IsIntegral.isIntegral x

end Along

end RoofGeneric

open scoped IntermediateField in

theorem exists_transcendental_finiteDimensional_roof (L : Type*) [Field L] [Algebra ℚ L]
    (M q : ℕ) [NeZero M] [NeZero q] (HM : Subgroup (ZMod M)ˣ) :
    ∃ x : R L q M HM, Transcendental L x ∧ FiniteDimensional L⟮x⟯ (R L q M HM) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (CohCarrier.GammaH M HM ⊓ Gamma0 (M * q)) (T_mem_GammaH_inf_Gamma0 M q HM)

theorem isIntegral_roofMap (L : Type*) [Field L] [Algebra ℚ L] {M M' q : ℕ} [NeZero M] [NeZero M']
    [NeZero q] {HM : Subgroup (ZMod M)ˣ} {HM' : Subgroup (ZMod M')ˣ}
    (φ : R L q M HM →ₐ[L] R L q M' HM') : φ.toRingHom.IsIntegral := by
  obtain ⟨x₀, hx₀, -⟩ := exists_transcendental_finiteDimensional_roof L M q HM
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_roof L M' q HM'
  haveI := hfin
  exact RoofGeneric.isIntegral_of_finiteAlong φ (RoofGeneric.finiteAlong_of_transcendental φ hx₀ hx₁)

end RoofIntegral

end XHDegHecke
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

end
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

set_option maxHeartbeats 1600000

noncomputable section

namespace XHDegHecke

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField CongruenceSubgroup"

open scoped MatrixGroups IntermediateField

local notation "𝕂" => AlgebraicClosure ℚ

section GenGlue

variable {K L₀ : Type*} [Field K] [Field L₀] [Algebra K L₀]
variable {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B]

theorem intermediateField_adjoin_range_union_eq_top (E EA EB : IntermediateField K L₀)
    (u : A →ₐ[K] E) (v : B →ₐ[K] E)
    (hA : EA ≤ IntermediateField.adjoin K (Set.range fun z : A => ((u z : E) : L₀)))
    (hB : EB ≤ IntermediateField.adjoin K (Set.range fun z : B => ((v z : E) : L₀)))
    (hGEN : E ≤ EA ⊔ EB) :
    IntermediateField.adjoin K (Set.range u ∪ Set.range v) = ⊤ := by
  set T : IntermediateField K E := IntermediateField.adjoin K (Set.range u ∪ Set.range v) with hT
  have hle : E ≤ IntermediateField.lift T := by
    refine hGEN.trans (sup_le (hA.trans ?_) (hB.trans ?_))
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact (IntermediateField.mem_lift (u z)).mpr
        (IntermediateField.subset_adjoin _ _ (Or.inl (Set.mem_range_self z)))
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, rfl⟩
      exact (IntermediateField.mem_lift (v z)).mpr
        (IntermediateField.subset_adjoin _ _ (Or.inr (Set.mem_range_self z)))
  apply IntermediateField.lift_injective E
  rw [IntermediateField.lift_top]
  exact le_antisymm (IntermediateField.lift_le T) hle

theorem intermediateField_adjoin_range_id_union_eq_top {E : Type*} [Field E] [Algebra K E]
    (v : B →ₐ[K] E) :
    IntermediateField.adjoin K (Set.range (AlgHom.id K E) ∪ Set.range v) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨x, rfl⟩)

end GenGlue
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

section Finite3b

open scoped IntermediateField

theorem exists_transcendental_finiteDimensional_x1 (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (HM : Subgroup (ZMod M)ˣ) :
    ∃ x : laurentBaseChange L (xHFunctionField M HM), Transcendental L x ∧
      FiniteDimensional L⟮x⟯ (laurentBaseChange L (xHFunctionField M HM)) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
    (CohCarrier.GammaH M HM) (translation_mem_GammaH M HM)

theorem finiteAlong_x1_x1 (L : Type*) [Field L] [Algebra ℚ L] {M M' : ℕ} [NeZero M] [NeZero M']
    {HM : Subgroup (ZMod M)ˣ} {HM' : Subgroup (ZMod M')ˣ}
    (φ : laurentBaseChange L (xHFunctionField M HM) →ₐ[L] laurentBaseChange L (xHFunctionField M' HM')) :
    FiniteAlong L φ := by
  obtain ⟨x₀, hx₀, -⟩ := exists_transcendental_finiteDimensional_x1 L M HM
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_x1 L M' HM'
  haveI := hfin
  exact RoofGeneric.finiteAlong_of_transcendental φ hx₀ hx₁

theorem finiteAlong_x1_roof (L : Type*) [Field L] [Algebra ℚ L] {M M' q : ℕ} [NeZero M] [NeZero M']
    [NeZero q] {HM : Subgroup (ZMod M)ˣ} {HM' : Subgroup (ZMod M')ˣ} (φ : laurentBaseChange L (xHFunctionField M HM) →ₐ[L] R L q M' HM') : FiniteAlong L φ := by
  obtain ⟨x₀, hx₀, -⟩ := exists_transcendental_finiteDimensional_x1 L M HM
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_roof L M' q HM'
  haveI := hfin
  exact RoofGeneric.finiteAlong_of_transcendental φ hx₀ hx₁

theorem finiteAlong_roof_x1 (L : Type*) [Field L] [Algebra ℚ L] {M M' q : ℕ} [NeZero M] [NeZero M']
    [NeZero q] {HM : Subgroup (ZMod M)ˣ} {HM' : Subgroup (ZMod M')ˣ} (φ : R L q M HM →ₐ[L] laurentBaseChange L (xHFunctionField M' HM')) : FiniteAlong L φ := by
  obtain ⟨x₀, hx₀, -⟩ := exists_transcendental_finiteDimensional_roof L M q HM
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_x1 L M' HM'
  haveI := hfin
  exact RoofGeneric.finiteAlong_of_transcendental φ hx₀ hx₁

theorem finiteAlong_roof_roof (L : Type*) [Field L] [Algebra ℚ L] {M M' q : ℕ} [NeZero M] [NeZero M']
    [NeZero q] {HM : Subgroup (ZMod M)ˣ} {HM' : Subgroup (ZMod M')ˣ} (φ : R L q M HM →ₐ[L] R L q M' HM') : FiniteAlong L φ := by
  obtain ⟨x₀, hx₀, -⟩ := exists_transcendental_finiteDimensional_roof L M q HM
  obtain ⟨x₁, hx₁, hfin⟩ := exists_transcendental_finiteDimensional_roof L M' q HM'
  haveI := hfin
  exact RoofGeneric.finiteAlong_of_transcendental φ hx₀ hx₁

end Finite3b
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

section TwoComponent

variable (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
  (HN : Subgroup (ZMod N)ˣ) (HM : Subgroup (ZMod (N * p))ˣ)
  (hle : CohCarrier.GammaH (N * p) HM ≤ CohCarrier.GammaH N HN)
  (hdvd : N * p ∣ N * p)
  (hβN : HeckeBetaHDefined N HN p)
  (ι : R 𝕂 p N HN →ₐ[𝕂] laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))
  (hιcoe : ∀ u : R 𝕂 p N HN,
    ((ι u : laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)) : LaurentSeries 𝕂) = (u : LaurentSeries 𝕂))
  (W : R 𝕂 p N HN ≃ₐ[𝕂] R 𝕂 p N HN)
  (hWβ : ∀ x, W (heckeBetaHBar 𝕂 N HN p x) = heckeAlphaHBar 𝕂 N HN p x)

scoped instance neZero_mul_self : NeZero (N * p) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne p)⟩

abbrev iota2 : xHFunctionFieldBar N HN →ₐ[𝕂] laurentBaseChange 𝕂 (xHFunctionField (N * p) HM) :=
  ι.comp (heckeBetaHBar 𝕂 N HN p)

theorem isIntegral_j₂ : (roofSubst (L := 𝕂) (q := p) p hdvd hle).toRingHom.IsIntegral :=
  RoofGeneric.isIntegral_of_finiteAlong _ (finiteAlong_roof_roof 𝕂 _)

theorem isIntegral_id :
    (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))).toRingHom.IsIntegral :=
  RoofGeneric.isIntegral_of_finiteAlong _ (finiteAlong_x1_x1 𝕂 _)

theorem isIntegral_s' : (ι.comp W.symm.toAlgHom).toRingHom.IsIntegral :=
  RoofGeneric.isIntegral_of_finiteAlong _ (finiteAlong_roof_x1 𝕂 _)

include hβN hιcoe in

theorem sq_u : (heckeAlphaHBar 𝕂 (N * p) HM p).comp (iota2 N p HN HM ι)
    = (roofSubst (L := 𝕂) (q := p) p hdvd hle).comp (heckeAlphaHBar 𝕂 N HN p) := by
  apply AlgHom.ext; intro x; apply Subtype.ext
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_heckeAlphaHBar, AlgHom.comp_apply, hιcoe,
    coe_heckeBetaHBar N HN p hβN, coe_roofSubst, coe_heckeAlphaHBar]

include hWβ in

theorem sq_s : (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))).comp (iota2 N p HN HM ι)
    = (ι.comp W.symm.toAlgHom).comp (heckeAlphaHBar 𝕂 N HN p) := by
  apply AlgHom.ext
  intro x
  have hx : W.symm.toAlgHom (heckeAlphaHBar 𝕂 N HN p x) = heckeBetaHBar 𝕂 N HN p x := by
    show W.symm (heckeAlphaHBar 𝕂 N HN p x) = heckeBetaHBar 𝕂 N HN p x
    rw [← hWβ x, AlgEquiv.symm_apply_apply]
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [hx]

include hle in

theorem hgen_u :
    IntermediateField.adjoin 𝕂 (Set.range (heckeAlphaHBar 𝕂 (N * p) HM p) ∪
        Set.range (roofSubst (L := 𝕂) (q := p) p hdvd hle)) = ⊤ := by
  refine intermediateField_adjoin_range_union_eq_top (K := 𝕂) (R 𝕂 p (N * p) HM)
    (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))
    (IntermediateField.adjoin 𝕂 (qExpand 𝕂 p '' (R 𝕂 p N HN : Set (LaurentSeries 𝕂))))
    (heckeAlphaHBar 𝕂 (N * p) HM p) (roofSubst (L := 𝕂) (q := p) p hdvd hle) ?_ ?_ ?_
  · intro y hy
    exact IntermediateField.subset_adjoin _ _ ⟨⟨y, hy⟩, coe_heckeAlphaHBar (N * p) HM p _⟩
  · refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, coe_roofSubst p hdvd hle _⟩
  · exact (ModularCurve.laurentBaseChange_xHFunctionField_sup_adjoin_qExpand_xHTopFunctionFieldC 𝕂 N p
      (N * p) rfl HN HM hle).ge

include hle hβN hιcoe hWβ in
set_option maxHeartbeats 1600000 in

theorem exchange_two_component
    [HasPrincipalDivisors 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))]
    [HasPrincipalDivisors 𝕂 (R 𝕂 p (N * p) HM)] [HasPrincipalDivisors 𝕂 (R 𝕂 p N HN)]
    (h₂ : (iota2 N p HN HM ι).toRingHom.IsIntegral)
    (hα : (heckeAlphaHBar 𝕂 N HN p).toRingHom.IsIntegral)
    (hα' : (heckeAlphaHBar 𝕂 (N * p) HM p).toRingHom.IsIntegral)
    (hj₂ : (roofSubst (L := 𝕂) (q := p) p hdvd hle).toRingHom.IsIntegral)
    (hid : (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))).toRingHom.IsIntegral)
    (hs' : (ι.comp W.symm.toAlgHom).toRingHom.IsIntegral)
    (hdeg : finrankAlong 𝕂 (roofSubst (L := 𝕂) (q := p) p hdvd hle)
      + finrankAlong 𝕂 (ι.comp W.symm.toAlgHom)
      = finrankAlong 𝕂 (iota2 N p HN HM ι))
    (hne : ∃ (a : laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)) (b : R 𝕂 p N HN),
      (AlgHom.id 𝕂 _) a = (ι.comp W.symm.toAlgHom) b ∧
        heckeAlphaHBar 𝕂 (N * p) HM p a ≠ roofSubst (L := 𝕂) (q := p) p hdvd hle b)
    (E : Divisor 𝕂 (R 𝕂 p N HN)) :
    Divisor.pullbackAlong (iota2 N p HN HM ι) h₂
        (Divisor.pushforwardAlong (heckeAlphaHBar 𝕂 N HN p) hα E)
      = Divisor.pushforwardAlong (heckeAlphaHBar 𝕂 (N * p) HM p) hα'
          (Divisor.pullbackAlong (roofSubst (L := 𝕂) (q := p) p hdvd hle) hj₂ E)
        + Divisor.pushforwardAlong (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))) hid
          (Divisor.pullbackAlong (ι.comp W.symm.toAlgHom) hs' E) := by
  haveI : CharZero 𝕂 := inferInstance
  have hφfin : FiniteAlong 𝕂 (iota2 N p HN HM ι) := finiteAlong_x1_x1 𝕂 _
  have hψ'fin : FiniteAlong 𝕂 (heckeAlphaHBar 𝕂 N HN p) := finiteAlong_x1_roof 𝕂 _
  have hufin : FiniteAlong 𝕂 (heckeAlphaHBar 𝕂 (N * p) HM p) := finiteAlong_x1_roof 𝕂 _
  have hu'fin : FiniteAlong 𝕂 (roofSubst (L := 𝕂) (q := p) p hdvd hle) := finiteAlong_roof_roof 𝕂 _
  have hsfin : FiniteAlong 𝕂 (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))) :=
    finiteAlong_x1_x1 𝕂 _
  have hs'fin : FiniteAlong 𝕂 (ι.comp W.symm.toAlgHom) := finiteAlong_roof_x1 𝕂 _
  have hgen' : IntermediateField.adjoin 𝕂
      (Set.range (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))) ∪
        Set.range (ι.comp W.symm.toAlgHom)) = ⊤ :=
    intermediateField_adjoin_range_id_union_eq_top _
  exact AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_add_of_adjoin_eq_top
    (iota2 N p HN HM ι) (heckeAlphaHBar 𝕂 N HN p)
    (heckeAlphaHBar 𝕂 (N * p) HM p) (roofSubst (L := 𝕂) (q := p) p hdvd hle)
    (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)))
    (ι.comp W.symm.toAlgHom)
    (sq_u N p HN HM hle hdvd hβN ι hιcoe) (sq_s N p HN HM ι W hWβ)
    h₂ hα hα' hj₂ hid hs' hφfin hψ'fin hufin hu'fin hsfin hs'fin
    (hgen_u N p HN HM hle hdvd) hgen' hdeg hne E

end TwoComponent
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

end XHDegHecke
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

end
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

noncomputable section

namespace XHDegHecke
namespace C3b

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField"
open scoped MatrixGroups

section GenericDesc

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem restrictAlong_toValuationSubring (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') :
    (w.restrictAlong φ hφ).toValuationSubring = w.toValuationSubring.comap φ.toRingHom := rfl

theorem ramificationIndexAlong_eq (φ : F →ₐ[K] F') (w : Place K F') :
    Place.ramificationIndexAlong φ w = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ w.ord (φ f) = n} := rfl

theorem restrictAlong_comp_algEquiv (φ : F →ₐ[K] F') (σ : F ≃ₐ[K] F)
    (hφ : φ.toRingHom.IsIntegral) (h : (φ.comp σ.toAlgHom).toRingHom.IsIntegral) (w : Place K F') :
    w.restrictAlong (φ.comp σ.toAlgHom) h = (SemilinearAut.ofAlgAut σ)⁻¹ • w.restrictAlong φ hφ := by
  apply Place.ext
  rw [restrictAlong_toValuationSubring, SemilinearAut.smul_toValuationSubring,
    restrictAlong_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_inv_pointwise_smul_iff,
    ValuationSubring.mem_comap, SemilinearAut.ofAlgAut_smul]
  exact Iff.rfl

theorem ramificationIndexAlong_comp_algEquiv (φ : F →ₐ[K] F') (σ : F ≃ₐ[K] F) (w : Place K F') :
    Place.ramificationIndexAlong (φ.comp σ.toAlgHom) w = Place.ramificationIndexAlong φ w := by
  rw [ramificationIndexAlong_eq, ramificationIndexAlong_eq]
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hfn⟩
    exact ⟨σ f, (map_ne_zero_iff σ σ.injective).mpr hf, hfn⟩
  · rintro ⟨f, hf, hfn⟩
    refine ⟨σ.symm f, (map_ne_zero_iff σ.symm σ.symm.injective).mpr hf, ?_⟩
    show w.ord (φ (σ (σ.symm f))) = n
    rw [AlgEquiv.apply_symm_apply]
    exact hfn

theorem pullbackAlong_comp_algEquiv [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (σ : F ≃ₐ[K] F)
    (hφ : φ.toRingHom.IsIntegral) (h : (φ.comp σ.toAlgHom).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong (φ.comp σ.toAlgHom) h D
      = Divisor.pullbackAlong φ hφ (SemilinearAut.ofAlgAut σ • D) := by
  ext w
  rw [Divisor.pullbackAlong_apply, Divisor.pullbackAlong_apply, SemilinearAut.divisor_smul_apply,
    ramificationIndexAlong_comp_algEquiv, restrictAlong_comp_algEquiv φ σ hφ h]

theorem restrictAlong_id (h : (AlgHom.id K F).toRingHom.IsIntegral) (w : Place K F) :
    w.restrictAlong (AlgHom.id K F) h = w := by
  apply Place.ext
  rw [restrictAlong_toValuationSubring]
  ext x
  exact Iff.rfl

theorem inertiaDegAlong_id (h : (AlgHom.id K F).toRingHom.IsIntegral) (w : Place K F) :
    Place.inertiaDegAlong (AlgHom.id K F) h w = 1 := by
  letI := AlgebraicCurve.algebraAlong (AlgHom.id K F)
  haveI := AlgebraicCurve.isScalarTower_along (AlgHom.id K F)
  haveI : Algebra.IsIntegral F F := AlgebraicCurve.isIntegral_along _ h
  show Module.finrank (w.restrict F).ResidueField w.ResidueField = 1
  have hsurj : Function.Surjective (algebraMap (w.restrict F).ResidueField w.ResidueField) := by
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    refine ⟨IsLocalRing.residue _ ⟨(a : F), a.2⟩, ?_⟩
    rw [Place.algebraMap_residueField_eq, Place.restrictResidueMap_residue]
    rfl
  have e := LinearEquiv.ofBijective (Algebra.linearMap (w.restrict F).ResidueField w.ResidueField)
    ⟨(algebraMap (w.restrict F).ResidueField w.ResidueField).injective, hsurj⟩
  rw [← e.finrank_eq, Module.finrank_self]

theorem pushforwardAlong_id [HasPrincipalDivisors K F] (h : (AlgHom.id K F).toRingHom.IsIntegral)
    (D : Divisor K F) :
    Divisor.pushforwardAlong (AlgHom.id K F) h D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
    rw [map_add, ih, Divisor.pushforwardAlong_single, restrictAlong_id, inertiaDegAlong_id,
      Nat.cast_one, mul_one]

end GenericDesc
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

section HNE

local notation "𝕂" => AlgebraicClosure ℚ

variable (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (HN : Subgroup (ZMod N)ˣ) (HM : Subgroup (ZMod (N * p))ˣ)
  (hle : CohCarrier.GammaH (N * p) HM ≤ CohCarrier.GammaH N HN) (hdvd : N * p ∣ N * p)
  (ι : XHDegHecke.R 𝕂 p N HN →ₐ[𝕂] laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))
  (hιcoe : ∀ u : XHDegHecke.R 𝕂 p N HN,
    ((ι u : laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)) : LaurentSeries 𝕂) = (u : LaurentSeries 𝕂))

omit [NeZero N] [NeZero p] [Fact p.Prime] in

theorem coeffEmb_jq_mem_R : coeffEmb 𝕂 jq ∈ XHDegHecke.R 𝕂 p N HN :=
  coeffEmb_mem_laurentBaseChange 𝕂
    (intFormRatiosC_subset ℚ _ (by
      simpa only [jqModC_rat] using
        ModularCurve.jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH N HN ⊓ CongruenceSubgroup.Gamma0 (N * p))))

theorem coeffEmb_jq_not_mem_range_qExpand :
    coeffEmb 𝕂 jq ∉ Set.range (qExpand 𝕂 p) := by
  rintro ⟨z, hz⟩
  have hndvd : ¬ ((p : ℤ) ∣ (-1 : ℤ)) := by
    intro hd
    have h1 : (p : ℤ) ∣ 1 := (dvd_neg).mp hd
    have h2 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h1
    have h3 : p = 1 := by exact_mod_cast h2
    exact (Fact.out : p.Prime).one_lt.ne' h3
  have h := congrArg (fun s : LaurentSeries 𝕂 => s.coeff (-1)) hz
  simp only [coeffEmb_coeff, coeff_jq_neg_one, map_one] at h
  rw [qExpand_coeff_of_not_dvd p z hndvd] at h
  exact zero_ne_one h

include hιcoe in

theorem hne (W : XHDegHecke.R 𝕂 p N HN ≃ₐ[𝕂] XHDegHecke.R 𝕂 p N HN) :
    ∃ (a : laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)) (b : XHDegHecke.R 𝕂 p N HN),
      (AlgHom.id 𝕂 _) a = (ι.comp W.symm.toAlgHom) b ∧
      heckeAlphaHBar 𝕂 (N * p) HM p a ≠ XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle b := by
  let r : XHDegHecke.R 𝕂 p N HN := ⟨coeffEmb 𝕂 jq, coeffEmb_jq_mem_R N p HN⟩
  refine ⟨ι r, W r, ?_, ?_⟩
  · show ι r = ι (W.symm (W r))
    rw [AlgEquiv.symm_apply_apply]
  · intro h
    have h' := congrArg (fun y : XHDegHecke.R 𝕂 p (N * p) HM => (y : LaurentSeries 𝕂)) h
    simp only [coe_heckeAlphaHBar, hιcoe, XHDegHecke.coe_roofSubst] at h'
    exact coeffEmb_jq_not_mem_range_qExpand p ⟨_, h'.symm⟩

end HNE
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

end XHDegHecke.C3b
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

end
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

noncomputable section

namespace XHDegHecke
namespace C3b

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField"
open scoped MatrixGroups

local notation "𝕂" => AlgebraicClosure ℚ

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_congr [HasPrincipalDivisors K F'] {φ ψ : F →ₐ[K] F'} (h : φ = ψ)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong φ hφ D = Divisor.pullbackAlong ψ hψ D := by
  subst h; rfl

private theorem _root_.XHDegHecke.C3b.mk_zsmul [HasPrincipalDivisors K F] (n : ℤ) (D : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk (n • D) = n • Pic0.mk D :=
  QuotientAddGroup.mk_zsmul _ D n

p2m_export "XHDegHecke.C3b" "mk_zsmul"

theorem finrankAlong_algEquiv {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) :
    finrankAlong K e.toAlgHom = 1 := by
  have h := finrankAlong_comp e.toAlgHom e.symm.toAlgHom
  rw [AlgEquiv.symm_comp, finrankAlong_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

end Generic
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

section Maps

variable (N p : ℕ) [NeZero N] [NeZero p] (HN : Subgroup (ZMod N)ˣ) (HM : Subgroup (ZMod (N * p))ˣ)
  (hle : CohCarrier.GammaH (N * p) HM ≤ CohCarrier.GammaH N HN) (hdvd : N * p ∣ N * p)
  (ι : XHDegHecke.R 𝕂 p N HN →ₐ[𝕂] laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))
  (hιcoe : ∀ u : XHDegHecke.R 𝕂 p N HN,
    ((ι u : laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)) : LaurentSeries 𝕂) = (u : LaurentSeries 𝕂))

include hιcoe in

theorem j2_eq (h0' : HeckeBetaHDefined (N * p) HM p) :
    (heckeBetaHBar 𝕂 (N * p) HM p).comp ι = XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle := by
  apply AlgHom.ext; intro y; apply Subtype.ext
  rw [AlgHom.comp_apply, coe_heckeBetaHBar (N * p) HM p h0', hιcoe, XHDegHecke.coe_roofSubst]

end Maps
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

section Core

variable (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : ¬ p ∣ N)
  (HN : Subgroup (ZMod N)ˣ) (HM : Subgroup (ZMod (N * p))ˣ)
  (hle : CohCarrier.GammaH (N * p) HM ≤ CohCarrier.GammaH N HN) (hdvd : N * p ∣ N * p)
  (hβN : HeckeBetaHDefined N HN p)
  (ι : XHDegHecke.R 𝕂 p N HN →ₐ[𝕂] laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))
  (hιcoe : ∀ u : XHDegHecke.R 𝕂 p N HN,
    ((ι u : laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)) : LaurentSeries 𝕂) = (u : LaurentSeries 𝕂))

include hpN hβN hιcoe in
theorem hdeg
    (W : XHDegHecke.R 𝕂 p N HN ≃ₐ[𝕂] XHDegHecke.R 𝕂 p N HN)
    (hWβ : ∀ x, W (heckeBetaHBar 𝕂 N HN p x) = heckeAlphaHBar 𝕂 N HN p x) :
    finrankAlong 𝕂 (XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle) +
        finrankAlong 𝕂 (ι.comp W.symm.toAlgHom) =
      finrankAlong 𝕂 (XHDegHecke.iota2 N p HN HM ι) := by
  have hα : finrankAlong 𝕂 (heckeAlphaHBar 𝕂 N HN p) = p + 1 :=
    ModularCurve.finrankAlong_heckeAlphaHBar 𝕂 N HN hpN
  have hα' : finrankAlong 𝕂 (heckeAlphaHBar 𝕂 (N * p) HM p) = p :=
    ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd 𝕂 (N * p) HM p (dvd_mul_left p N)

  have hWβ' : W.toAlgHom.comp (heckeBetaHBar 𝕂 N HN p) = heckeAlphaHBar 𝕂 N HN p := AlgHom.ext hWβ
  have hβ : finrankAlong 𝕂 (heckeBetaHBar 𝕂 N HN p) = p + 1 := by
    have := congrArg (finrankAlong 𝕂) hWβ'
    rw [finrankAlong_comp, finrankAlong_algEquiv, mul_one, hα] at this
    exact this

  have hsq := XHDegHecke.sq_u N p HN HM hle hdvd hβN ι hιcoe
  have h1 := congrArg (finrankAlong 𝕂) hsq

  have h2 : finrankAlong 𝕂 (XHDegHecke.iota2 N p HN HM ι) =
      finrankAlong 𝕂 (heckeBetaHBar 𝕂 N HN p) * finrankAlong 𝕂 ι :=
    finrankAlong_comp _ _
  rw [finrankAlong_comp, finrankAlong_comp, finrankAlong_comp, hα', hα, hβ] at h1

  have h3 : finrankAlong 𝕂 (ι.comp W.symm.toAlgHom) = finrankAlong 𝕂 ι := by
    rw [finrankAlong_comp, finrankAlong_algEquiv, one_mul]
  rw [h3, h2, hβ]
  set k := finrankAlong 𝕂 ι
  set j := finrankAlong 𝕂 (XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle)
  have hj : j = p * k := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos p)
    have h1' := h1
    ring_nf at h1' ⊢
    linarith
  rw [hj]; ring

variable
  (h₂ : (XHDegHecke.iota2 N p HN HM ι).toRingHom.IsIntegral)
  (hκ : ι.toRingHom.IsIntegral)
  (hα : HeckeAlphaHBarIntegral 𝕂 N HN p)
  (hα' : HeckeAlphaHBarIntegral 𝕂 (N * p) HM p) (hβ' : HeckeBetaHBarIntegral 𝕂 (N * p) HM p)
  [HasPrincipalDivisors 𝕂 (xHFunctionFieldBar (N * p) HM)]
  [HasPrincipalDivisors 𝕂 (XHDegHecke.R 𝕂 p (N * p) HM)]
  [HasPrincipalDivisors 𝕂 (XHDegHecke.R 𝕂 p N HN)]

include hle hβN hιcoe in

theorem exchange_two_component'
    (W : XHDegHecke.R 𝕂 p N HN ≃ₐ[𝕂] XHDegHecke.R 𝕂 p N HN)
    (hWβ : ∀ x, W (heckeBetaHBar 𝕂 N HN p x) = heckeAlphaHBar 𝕂 N HN p x)
    (hj₂ : (XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle).toRingHom.IsIntegral)
    (hid : (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))).toRingHom.IsIntegral)
    (hs' : (ι.comp W.symm.toAlgHom).toRingHom.IsIntegral)
    (hdeg : finrankAlong 𝕂 (XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle)
      + finrankAlong 𝕂 (ι.comp W.symm.toAlgHom)
      = finrankAlong 𝕂 (XHDegHecke.iota2 N p HN HM ι))
    (hne : ∃ (a : laurentBaseChange 𝕂 (xHFunctionField (N * p) HM)) (b : XHDegHecke.R 𝕂 p N HN),
      (AlgHom.id 𝕂 _) a = (ι.comp W.symm.toAlgHom) b ∧
        heckeAlphaHBar 𝕂 (N * p) HM p a ≠ XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle b)
    (E : Divisor 𝕂 (XHDegHecke.R 𝕂 p N HN)) :
    Divisor.pullbackAlong (XHDegHecke.iota2 N p HN HM ι) h₂
        (Divisor.pushforwardAlong (heckeAlphaHBar 𝕂 N HN p) hα E)
      = Divisor.pushforwardAlong (heckeAlphaHBar 𝕂 (N * p) HM p) hα'
          (Divisor.pullbackAlong (XHDegHecke.roofSubst (L := 𝕂) (q := p) p hdvd hle) hj₂ E)
        + Divisor.pushforwardAlong (AlgHom.id 𝕂 (laurentBaseChange 𝕂 (xHFunctionField (N * p) HM))) hid
          (Divisor.pullbackAlong (ι.comp W.symm.toAlgHom) hs' E) :=
  XHDegHecke.exchange_two_component N p HN HM hle hdvd hβN ι hιcoe W hWβ h₂ hα hα' hj₂ hid hs' hdeg hne E

include hpN hle hdvd hβN hιcoe in

theorem divisor_identity_general (h0' : HeckeBetaHDefined (N * p) HM p)
    (W : XHDegHecke.R 𝕂 p N HN ≃ₐ[𝕂] XHDegHecke.R 𝕂 p N HN)
    (hWβ : ∀ x, W (heckeBetaHBar 𝕂 N HN p x) = heckeAlphaHBar 𝕂 N HN p x)
    (E : Divisor 𝕂 (XHDegHecke.R 𝕂 p N HN)) :
    Divisor.pullbackAlong (XHDegHecke.iota2 N p HN HM ι) h₂
        (Divisor.pushforwardAlong (heckeAlphaHBar 𝕂 N HN p) hα E) =
      Divisor.correspondence (heckeBetaHBar 𝕂 (N * p) HM p) (heckeAlphaHBar 𝕂 (N * p) HM p) hβ' hα'
          (Divisor.pullbackAlong ι hκ E) +
        Divisor.pullbackAlong ι hκ (SemilinearAut.ofAlgAut W.symm • E) := by
  have hj₂ := XHDegHecke.isIntegral_j₂ N p HN HM hle hdvd
  have hid := XHDegHecke.isIntegral_id N p HM
  have hs' := XHDegHecke.isIntegral_s' N p HN HM ι W
  rw [exchange_two_component' N p HN HM hle hdvd hβN ι hιcoe h₂ hα hα' W hWβ hj₂ hid hs'
      (hdeg N p hpN HN HM hle hdvd hβN ι hιcoe W hWβ) (hne N p HN HM hle hdvd ι hιcoe W) E,
    Divisor.correspondence_apply]
  congr 1
  ·
    congr 1
    rw [Divisor.pullbackAlong_pullbackAlong ι _ hκ hβ' (RingHom.IsIntegral.trans _ _ hκ hβ') E]
    exact pullbackAlong_congr (j2_eq N p HN HM hle hdvd ι hιcoe h0').symm hj₂ (RingHom.IsIntegral.trans _ _ hκ hβ') E
  ·
    rw [pushforwardAlong_id, pullbackAlong_comp_algEquiv _ W.symm hκ hs' E]

end Core
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

end XHDegHecke.C3b
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

namespace XHDegHecke
namespace C3b

p2m_open "ModularCurve AlgebraicCurve~finiteDimensional_adjoin_of_transcendental IntermediateField"
open scoped MatrixGroups

local notation "𝕂" => AlgebraicClosure ℚ

theorem head
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) [NeZero (N * p)]
    (HN : Subgroup (ZMod N)ˣ) (HM : Subgroup (ZMod (N * p))ˣ)
    (hle : CohCarrier.GammaH (N * p) HM ≤ CohCarrier.GammaH N HN)
    (hin : ModularCurve.HeckeInputsHAlong 𝕂 (N * p) HM p)
    (hβN : ModularCurve.HeckeBetaHDefined N HN p)
    (ι : XHDegHecke.R 𝕂 p N HN →ₐ[𝕂] xHFunctionFieldBar (N * p) HM)
    (hιcoe : ∀ u : XHDegHecke.R 𝕂 p N HN,
      ((ι u : xHFunctionFieldBar (N * p) HM) : LaurentSeries 𝕂) = (u : LaurentSeries 𝕂))
    (hα : ModularCurve.HeckeAlphaHBarIntegral 𝕂 N HN p)
    (hfinα : AlgebraicCurve.FiniteAlong 𝕂 (ModularCurve.heckeAlphaHBar 𝕂 N HN p))
    (hNα : AlgebraicCurve.NormFormulaAlong 𝕂 (ModularCurve.heckeAlphaHBar 𝕂 N HN p) hfinα)
    [AlgebraicCurve.HasPrincipalDivisors 𝕂 (XHDegHecke.R 𝕂 p N HN)]
    [AlgebraicCurve.HasPrincipalDivisors 𝕂 (xHFunctionFieldBar (N * p) HM)]
    (hι : ι.toRingHom.IsIntegral)
    (hFIι : AlgebraicCurve.FundamentalIdentityAlong 𝕂 ι hι)
    (hιβ : (ι.comp (ModularCurve.heckeBetaHBar 𝕂 N HN p)).toRingHom.IsIntegral)
    (hFIιβ : AlgebraicCurve.FundamentalIdentityAlong 𝕂 (ι.comp (ModularCurve.heckeBetaHBar 𝕂 N HN p)) hιβ)
    (W : XHDegHecke.R 𝕂 p N HN ≃ₐ[𝕂] XHDegHecke.R 𝕂 p N HN)
    (hWβ : ∀ x, W (heckeBetaHBar 𝕂 N HN p x) = heckeAlphaHBar 𝕂 N HN p x)
    (x : AlgebraicCurve.Pic0 𝕂 (XHDegHecke.R 𝕂 p N HN)) :
    ModularCurve.heckeOperatorHAlong 𝕂 (N * p) HM p (AlgebraicCurve.Pic0.pullbackAlongHom ι hι hFIι x) +
      AlgebraicCurve.Pic0.pullbackAlongHom ι hι hFIι (AlgebraicCurve.SemilinearAut.ofAlgAut W.symm • x) =
      AlgebraicCurve.Pic0.pullbackAlongHom (ι.comp (ModularCurve.heckeBetaHBar 𝕂 N HN p)) hιβ hFIιβ
        (AlgebraicCurve.Pic0.pushforwardAlongHom (ModularCurve.heckeAlphaHBar 𝕂 N HN p) hα hfinα hNα x) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hdvd : N * p ∣ N * p := dvd_refl _
  obtain ⟨h0', hα', hβ', hP', hfinα', hFI', hNα'⟩ := hin
  haveI := hP'
  rw [heckeOperatorHAlong_eq h0' hα' hβ' hFI' hfinα' hNα']
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective x
  rw [heckePic0HBar, Pic0.pushforwardAlongHom_mk, Pic0.pullbackAlongHom_mk, Pic0.pullbackAlongHom_mk,
    Pic0.correspondence_mk, SemilinearAut.pic0_smul_mk, Pic0.pullbackAlongHom_mk, ← Pic0.mk_add]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  exact (divisor_identity_general N p hpN HN HM hle hdvd hβN ι hιcoe hιβ hι hα hα' hβ' h0' W hWβ
    (E : Divisor 𝕂 (XHDegHecke.R 𝕂 p N HN))).symm

end XHDegHecke.C3b
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

end
p2m_reactivate "P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom.XHDegHecke"

open XHDegHecke.C3b in
theorem solution
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) (M : ℕ) [NeZero M] (hM : M = N * p)
    (H' : Subgroup (ZMod N)ˣ) (H : Subgroup (ZMod M)ˣ)
    (hle : CohCarrier.GammaH M H ≤ CohCarrier.GammaH N H')
    (pbar : (ZMod N)ˣ) (hpbar : (pbar : ZMod N) = p)
    (hin : ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H p)
    (hβN : ModularCurve.HeckeBetaHDefined N H' p)
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
    (hιcoe : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))),
      ((ι u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : ModularCurve.HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) N H' p)
    (hfinα : AlgebraicCurve.FiniteAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p))
    (hNα : AlgebraicCurve.NormFormulaAlong (AlgebraicClosure ℚ)
      (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p) hfinα)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p)))]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (hι : ι.toRingHom.IsIntegral)
    (hFIι : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hι)
    (hιβ : (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p)).toRingHom.IsIntegral)
    (hFIιβ : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p)) hιβ)
    (W : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p))))
    (hWβ : ∀ x : ↥(ModularCurve.xHFunctionFieldBar N H'),
        W (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p x) =
          ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p x)
    (hWα : ∀ x : ↥(ModularCurve.xHFunctionFieldBar N H'),
        W (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p x) =
          ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p
            ((ModularCurve.diamondAutHBar N H' pbar).symm x))
    (x : AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * p)))) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H p
        (AlgebraicCurve.Pic0.pullbackAlongHom ι hι hFIι x) +
      AlgebraicCurve.Pic0.pullbackAlongHom ι hι hFIι
        (AlgebraicCurve.SemilinearAut.ofAlgAut W.symm • x) =
      AlgebraicCurve.Pic0.pullbackAlongHom
          (ι.comp (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) N H' p)) hιβ hFIιβ
        (AlgebraicCurve.Pic0.pushforwardAlongHom
          (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) N H' p) hα hfinα hNα x) := by
  subst hM
  exact XHDegHecke.C3b.head N p hpN H' H hle hin hβN ι hιcoe hα hfinα hNα hι hFIι hιβ hFIιβ W hWβ x

end S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom
end P2MW
export P2MW.S_ModularCurve_JH_heckeOperatorHAlong_pullbackAlongHom_add_pullbackAlongHom_atkinLehner_smul_eq_pullbackAlongHom_comp_heckeBetaHBar_pushforwardAlongHom (solution)

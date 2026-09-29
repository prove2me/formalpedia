-- Prove2me | solution 1 for ModularCurve.finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/92af0557-a61e-5ece-88a7-0cb4f8004822

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import Theorems.Thm_AlgebraicCurve_finrankAlong_eq_relfinrank_fieldRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeAlphaOneBar intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset qExpFunctionFieldC_mono qExpand qExpand_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange GammaH_bot coeffMap_jqModC jqModC qSeriesBar uniformizerBar coe_uniformizerBar irreducible_uniformizerBar qInftyPlaceBar finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField qExpand_image_intFormRatiosC_subset jqModC_mem_intFormRatiosC order_jqModC"
namespace X1Degen
p2m_open "ModularCurve"

section ResidueAlgClosed

open IsLocalRing Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem isAlgClosed_residueField [IsAlgClosed L] : IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)
  have hf_lifts : f ∈ lifts (residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0
    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]
      exact hg_nat
    have hf1 : f = 1 := (hf_monic.natDegree_eq_zero).mp hf_deg
    exact hf_irr.not_isUnit (by rw [hf1]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg
  have hα_int : IsIntegral A α := by
    refine ⟨g, hg_monic, ?_⟩
    rwa [IsRoot.def, eval_map] at hα
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int
  refine ⟨residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      have hcomm : algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α := by
        rw [← ha, eval_map, eval₂_hom]
      rw [hcomm]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  have : f.eval (residue A a) = residue A (g.eval a) := by
    rw [← hg_map, eval_map, eval₂_hom]
  rw [this, hga, map_zero]

end ResidueAlgClosed

section Exchange

open scoped IntermediateField

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

open scoped IntermediateField

variable {L F F' : Type*} [Field L] [Field F] [Field F'] [Algebra L F] [Algebra L F']

theorem finiteAlong_of_transcendental (φ : F →ₐ[L] F') {x₀ : F} (hx₀ : Transcendental L x₀)
    {x₁ : F'} (hx₁ : Transcendental L x₁) [FiniteDimensional L⟮x₁⟯ F'] :
    AlgebraicCurve.FiniteAlong L φ := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isScalarTower_along φ
  have hy₀ : Transcendental L (φ x₀) :=
    (transcendental_algebraMap_iff (R := L) (S := F) (A := F') (φ.toRingHom.injective)).mpr hx₀
  haveI hfin : FiniteDimensional L⟮φ x₀⟯ F' := finiteDimensional_adjoin_of_transcendental hx₁ hy₀
  set E₀ : IntermediateField L F := L⟮x₀⟯ with hE₀
  have hmap : E₀.map φ = L⟮φ x₀⟯ := by
    rw [hE₀, IntermediateField.adjoin_map, Set.image_singleton]
  let e : E₀ ≃ₐ[L] L⟮φ x₀⟯ := (E₀.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : E₀, ((e w : L⟮φ x₀⟯) : F') = φ (w : F) := fun w => rfl
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

end Along

section Bridge

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem relfinrank_adjoin_simple_eq_finrank (F' : IntermediateField F E) (x : F') :
    relfinrank (adjoin F {(x : E)}) F' = Module.finrank (adjoin F ({x} : Set F')) F' := by
  have h1 := relfinrank_comap (adjoin F {(x : E)}) F'.val (⊤ : IntermediateField F F')
  have hmap : IntermediateField.map F'.val ⊤ = F' := by
    rw [← AlgHom.fieldRange_eq_map, fieldRange_val]
  have hcomap : IntermediateField.comap F'.val (adjoin F {(x : E)}) = adjoin F {x} := by
    have : adjoin F {(x : E)} = IntermediateField.map F'.val (adjoin F {x}) := by
      rw [adjoin_map, Set.image_singleton]; rfl
    rw [this, comap_map]
  rw [hmap, hcomap, relfinrank_top_right] at h1
  exact h1.symm

theorem finrankAlong_inclusion {A B : IntermediateField F E} (h : A ≤ B) :
    AlgebraicCurve.finrankAlong F (IntermediateField.inclusion h) = relfinrank A B := by
  rw [AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange A B (IntermediateField.inclusion h)]
  congr 1
  ext x
  rw [AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨f, hf⟩
    rw [AlgHom.comp_apply, IntermediateField.coe_val, IntermediateField.coe_inclusion] at hf
    rw [← hf]
    exact f.2
  · intro hx
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [AlgHom.comp_apply, IntermediateField.coe_val, IntermediateField.coe_inclusion]

end Bridge

section Groups

open CongruenceSubgroup
open scoped MatrixGroups

variable (M ℓ : ℕ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem T_mem_inf : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (M * ℓ) := by
  refine ⟨T_mem_Gamma1 M, ?_⟩
  simp [Gamma0_mem, ModularGroup.T]

scoped instance finiteIndex_inf [NeZero M] [NeZero ℓ] : (Gamma1 M ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  infer_instance

theorem cocycle [NeZero ℓ] : ∀ γ ∈ Gamma1 M ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ Gamma1 M,
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

def kerH : Subgroup (ZMod (M * ℓ))ˣ := (ZMod.unitsMap (dvd_mul_right M ℓ)).ker

theorem gammaH_kerH_eq [NeZero M] [NeZero ℓ] :
    CohCarrier.GammaH (M * ℓ) (kerH M ℓ) = Gamma1 M ⊓ Gamma0 (M * ℓ) := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  ext A
  rw [CohCarrier.mem_GammaH_iff, Subgroup.mem_inf]
  have hd : ∀ hA : A ∈ Gamma0 (M * ℓ),
      ((ZMod.unitsMap (dvd_mul_right M ℓ) (CohCarrier.gamma0Units (M * ℓ) ⟨A, hA⟩) : (ZMod M)ˣ) :
        ZMod M) = ((A 1 1 : ℤ) : ZMod M) := by
    intro hA
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, CohCarrier.val_gamma0Units]
    simp only [Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [ZMod.castHom_apply, ZMod.cast_intCast (dvd_mul_right M ℓ)]
  have hc : ∀ hA : A ∈ Gamma0 (M * ℓ), ((A 1 0 : ℤ) : ZMod M) = 0 := by
    intro hA
    have h := Gamma0_mem.mp hA
    have := congrArg (ZMod.castHom (dvd_mul_right M ℓ) (ZMod M)) h
    rwa [map_intCast, map_zero] at this
  constructor
  · rintro ⟨hA0, hAH⟩
    have h11 : ((A 1 1 : ℤ) : ZMod M) = 1 := by
      have h1 : ZMod.unitsMap (dvd_mul_right M ℓ) (CohCarrier.gamma0Units (M * ℓ) ⟨A, hA0⟩) = 1 := by
        have hAH' : CohCarrier.gamma0Units (M * ℓ) ⟨A, hA0⟩ ∈ (ZMod.unitsMap (dvd_mul_right M ℓ)).ker := hAH
        exact (MonoidHom.mem_ker).mp hAH'
      have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h1
      simp only [Units.val_one] at this
      rwa [hd hA0] at this
    have h10 : ((A 1 0 : ℤ) : ZMod M) = 0 := hc hA0
    refine ⟨?_, hA0⟩
    rw [Gamma1_mem]
    refine ⟨?_, h11, h10⟩
    have hda := CohCarrier.Gamma0_d_mul_a M ⟨A, Gamma0_mem.mpr h10⟩
    simp only at hda
    rw [h11, one_mul] at hda
    exact hda
  · rintro ⟨hA1, hA0⟩
    refine ⟨hA0, ?_⟩
    show CohCarrier.gamma0Units (M * ℓ) ⟨A, hA0⟩ ∈ (ZMod.unitsMap (dvd_mul_right M ℓ)).ker
    rw [MonoidHom.mem_ker]
    ext
    rw [hd hA0, Units.val_one]
    exact ((Gamma1_mem M A).mp hA1).2.1

end Groups

section Modular

p2m_open "AlgebraicCurve~isAlgebraic_adjoin_of_transcendental IntermediateField CongruenceSubgroup"
open scoped IntermediateField

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

variable (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
variable (P : ValuationSubring (AlgebraicClosure ℚ))

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "kP" => IsLocalRing.ResidueField P
local notation "Γ₁" => CongruenceSubgroup.Gamma1 M
local notation "Γ'" => CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)
local notation "Fq" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M))
local notation "Eq" => laurentBaseChange (AlgebraicClosure ℚ)
  (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)
local notation "Eb" => qExpFunctionFieldC (IsLocalRing.ResidueField P)
  (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))

theorem inf_le : (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) ≤ Γ₁ := inf_le_left

theorem Fb_le_Eb : (Fb : IntermediateField kP (LaurentSeries kP)) ≤ Eb := qExpFunctionFieldC_mono kP (inf_le M ℓ)

def αb : Fb →ₐ[kP] Eb := IntermediateField.inclusion (Fb_le_Eb M ℓ P)

theorem coe_αb (x : Fb) : (αb M ℓ P x : LaurentSeries kP) = (x : LaurentSeries kP) :=
  IntermediateField.coe_inclusion _ x

def qExpAlg (K : Type*) [Field K] (n : ℕ) [NeZero n] : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qExpand K n
  commutes' c := by
    show qExpand K n (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem qExpAlg_apply (K : Type*) [Field K] (n : ℕ) [NeZero n] (f : LaurentSeries K) :
    qExpAlg K n f = qExpand K n f := rfl

theorem map_qExpand_le : (Fb : IntermediateField kP (LaurentSeries kP)).map (qExpAlg kP ℓ) ≤ Eb := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := inferInstance
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset kP (T_mem_Gamma1 M) ℓ (cocycle M ℓ)
  show (IntermediateField.adjoin kP (intFormRatiosC kP Γ₁)).map (qExpAlg kP ℓ) ≤
    IntermediateField.adjoin kP (intFormRatiosC kP Γ')
  rw [IntermediateField.adjoin_map]
  exact IntermediateField.adjoin.mono kP _ _ hsub

def βb : Fb →ₐ[kP] Eb :=
  (IntermediateField.inclusion (map_qExpand_le M ℓ P)).comp
    ((Fb : IntermediateField kP (LaurentSeries kP)).equivMap (qExpAlg kP ℓ)).toAlgHom

theorem coe_βb (x : Fb) : (βb M ℓ P x : LaurentSeries kP) = qExpand kP ℓ (x : LaurentSeries kP) := rfl

theorem exists_jbar_bot :
    ∃ x : Fb, (x : LaurentSeries kP) = jqModC kP ∧ Transcendental kP x ∧
      FiniteDimensional kP⟮x⟯ Fb ∧
      ∀ y : Fq, (y : LaurentSeries ℚ̄) = jqModC ℚ̄ →
        Module.finrank kP⟮x⟯ Fb ≤ Module.finrank ℚ̄⟮y⟯ Fq :=
  ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
    (AlgebraicClosure ℚ) P Γ₁ (T_mem_Gamma1 M)

theorem exists_jbar_top :
    ∃ x : Eb, (x : LaurentSeries kP) = jqModC kP ∧ Transcendental kP x ∧
      FiniteDimensional kP⟮x⟯ Eb ∧
      ∀ y : Eq, (y : LaurentSeries ℚ̄) = jqModC ℚ̄ →
        Module.finrank kP⟮x⟯ Eb ≤ Module.finrank ℚ̄⟮y⟯ Eq :=
  ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
    (AlgebraicClosure ℚ) P Γ' (T_mem_inf M ℓ)

theorem finiteAlong_αb : FiniteAlong kP (αb M ℓ P) := by
  obtain ⟨x₀, -, hx₀, -, -⟩ := exists_jbar_bot M P
  obtain ⟨x₁, -, hx₁, hfin, -⟩ := exists_jbar_top M ℓ P
  haveI := hfin
  exact finiteAlong_of_transcendental _ hx₀ hx₁

theorem finiteAlong_βb : FiniteAlong kP (βb M ℓ P) := by
  obtain ⟨x₀, -, hx₀, -, -⟩ := exists_jbar_bot M P
  obtain ⟨x₁, -, hx₁, hfin, -⟩ := exists_jbar_top M ℓ P
  haveI := hfin
  exact finiteAlong_of_transcendental _ hx₀ hx₁

theorem separableAlong_αb : SeparableAlong kP (αb M ℓ P) := by
  haveI : IsAlgClosed kP := isAlgClosed_residueField P
  obtain ⟨xF, hxF, htrF, -, -⟩ := exists_jbar_bot M P
  obtain ⟨xE, hxE, htrE, hfinE, -⟩ := exists_jbar_top M ℓ P
  haveI := hfinE

  have hordE : (qSeriesBar kP Eb xE).order = -1 := by
    show ((xE : LaurentSeries kP)).order = -1
    rw [hxE]; exact order_jqModC kP
  let v : Place kP Eb := qInftyPlaceBar kP Eb ⟨xE, hordE⟩
  have ht : v.ord (xE⁻¹ : Eb) = 1 := by
    have h := v.ord_coe_irreducible (π := uniformizerBar hordE) (irreducible_uniformizerBar hordE)
    rwa [coe_uniformizerBar] at h
  haveI : Algebra.IsAlgebraic kP⟮xE⟯ Eb := Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable kP⟮(xE⁻¹ : Eb)⟯ Eb :=
    Place.isSeparable_adjoin_of_ord_eq_one xE v ht

  have hαx : αb M ℓ P xF = xE := Subtype.ext (by rw [coe_αb, hxF, hxE])
  have hαt : αb M ℓ P (xF⁻¹) = xE⁻¹ := by rw [map_inv₀, hαx]
  set S₀ : IntermediateField kP Fb := kP⟮(xF⁻¹ : Fb)⟯ with hS₀
  have hmap : S₀.map (αb M ℓ P) = kP⟮(xE⁻¹ : Eb)⟯ := by
    rw [hS₀, IntermediateField.adjoin_map, Set.image_singleton, hαt]
  let e : S₀ ≃ₐ[kP] kP⟮(xE⁻¹ : Eb)⟯ := (S₀.equivMap (αb M ℓ P)).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ w : S₀, ((e w : kP⟮(xE⁻¹ : Eb)⟯) : Eb) = αb M ℓ P (w : Fb) := fun w => rfl
  letI := algebraAlong (αb M ℓ P)
  haveI := isScalarTower_along (αb M ℓ P)
  letI : Algebra kP⟮(xE⁻¹ : Eb)⟯ Fb := (S₀.val.comp (e.symm : kP⟮(xE⁻¹ : Eb)⟯ →ₐ[kP] S₀)).toRingHom.toAlgebra
  haveI : IsScalarTower kP⟮(xE⁻¹ : Eb)⟯ Fb Eb := by
    refine IsScalarTower.of_algebraMap_eq fun w => ?_
    show (w : Eb) = αb M ℓ P ((e.symm w : S₀) : Fb)
    rw [← he, AlgEquiv.apply_symm_apply]
  show Algebra.IsSeparable Fb Eb
  exact Algebra.isSeparable_tower_top_of_isSeparable kP⟮(xE⁻¹ : Eb)⟯ Fb Eb

theorem laurentBaseChange_mono' {L : Type*} [Field L] [Algebra ℚ L]
    {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) :
    laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem Fq_le_Eq : (Fq : IntermediateField ℚ̄ (LaurentSeries ℚ̄)) ≤ Eq :=
  laurentBaseChange_mono' (qExpFunctionFieldC_mono ℚ (inf_le M ℓ))

theorem jq_mem_Fq : jqModC ℚ̄ ∈ (Fq : IntermediateField ℚ̄ (LaurentSeries ℚ̄)) := by
  have hjq : jqModC ℚ ∈ qExpFunctionFieldC ℚ Γ₁ :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  have : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC ℚ̄ := coeffMap_jqModC _
  rw [← this]
  exact coeffEmb_mem_laurentBaseChange _ hjq

theorem finrankAlong_alpha :
    finrankAlong ℚ̄ (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) = relfinrank Fq Eq := by
  have h := finrankAlong_inclusion (F := AlgebraicClosure ℚ) (E := LaurentSeries ℚ̄) (Fq_le_Eq M ℓ)
  exact h

theorem finrankAlong_αb : finrankAlong kP (αb M ℓ P) = relfinrank Fb Eb :=
  finrankAlong_inclusion (F := kP) (E := LaurentSeries kP) (Fb_le_Eb M ℓ P)

theorem relfinrank_eq {p : ℕ} [Fact p.Prime] (hpMℓ : ¬ p ∣ M * ℓ) (hP : P.LiesOverPrime p) :
    relfinrank Fb Eb = relfinrank Fq Eq := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  have hpM : ¬ p ∣ M := fun h => hpMℓ (dvd_mul_of_dvd_left h ℓ)
  obtain ⟨xb, hxb, htrb, hfdb, hDb⟩ := exists_jbar_bot M P
  obtain ⟨xe, hxe, htre, hfde, hDe⟩ := exists_jbar_top M ℓ P

  set yF : Fq := ⟨jqModC ℚ̄, jq_mem_Fq M⟩ with hyF
  set yE : Eq := ⟨jqModC ℚ̄, Fq_le_Eq M ℓ (jq_mem_Fq M)⟩ with hyE

  have hIb : Module.finrank ℚ̄⟮yF⟯ Fq ≤ Module.finrank kP⟮xb⟯ Fb := by
    have h := ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M ⊥ hpM P hP
    rw [GammaH_bot] at h
    exact h xb yF hxb rfl
  have hIe : Module.finrank ℚ̄⟮yE⟯ Eq ≤ Module.finrank kP⟮xe⟯ Eb := by
    have h := ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd (M * ℓ) (kerH M ℓ)
      hpMℓ P hP
    rw [gammaH_kerH_eq] at h
    exact h xe yE hxe rfl

  have hb : Module.finrank kP⟮xb⟯ Fb = Module.finrank ℚ̄⟮yF⟯ Fq := le_antisymm (hDb yF rfl) hIb
  have he : Module.finrank kP⟮xe⟯ Eb = Module.finrank ℚ̄⟮yE⟯ Eq := le_antisymm (hDe yE rfl) hIe
  have hpos : 0 < Module.finrank kP⟮xb⟯ Fb := by haveI := hfdb; exact Module.finrank_pos

  have hAb_le : (kP⟮jqModC kP⟯ : IntermediateField kP (LaurentSeries kP)) ≤ Fb :=
    IntermediateField.adjoin_simple_le_iff.mpr (hxb ▸ xb.2)
  have hAq_le : (ℚ̄⟮jqModC ℚ̄⟯ : IntermediateField ℚ̄ (LaurentSeries ℚ̄)) ≤ Fq :=
    IntermediateField.adjoin_simple_le_iff.mpr (jq_mem_Fq M)
  have e1 : relfinrank (kP⟮jqModC kP⟯ : IntermediateField kP (LaurentSeries kP)) Fb =
      Module.finrank kP⟮xb⟯ Fb := by
    have h := relfinrank_adjoin_simple_eq_finrank Fb xb
    rwa [hxb] at h
  have e2 : relfinrank (kP⟮jqModC kP⟯ : IntermediateField kP (LaurentSeries kP)) Eb =
      Module.finrank kP⟮xe⟯ Eb := by
    have h := relfinrank_adjoin_simple_eq_finrank Eb xe
    rwa [hxe] at h
  have e3 : relfinrank (ℚ̄⟮jqModC ℚ̄⟯ : IntermediateField ℚ̄ (LaurentSeries ℚ̄)) Fq =
      Module.finrank ℚ̄⟮yF⟯ Fq :=
    relfinrank_adjoin_simple_eq_finrank Fq yF
  have e4 : relfinrank (ℚ̄⟮jqModC ℚ̄⟯ : IntermediateField ℚ̄ (LaurentSeries ℚ̄)) Eq =
      Module.finrank ℚ̄⟮yE⟯ Eq :=
    relfinrank_adjoin_simple_eq_finrank Eq yE

  have tb := IntermediateField.relfinrank_mul_relfinrank hAb_le (Fb_le_Eb M ℓ P)
  have tq := IntermediateField.relfinrank_mul_relfinrank hAq_le (Fq_le_Eq M ℓ)
  rw [e1, e2, hb, he] at tb
  rw [e3, e4] at tq
  rw [hb] at hpos
  exact Nat.eq_of_mul_eq_mul_left hpos (tb.trans tq.symm)

end Modular

end ModularCurve.X1Degen
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd.ModularCurve P2MW.S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd.ModularCurve.X1Degen"
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd.ModularCurve P2MW.S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd.ModularCurve.X1Degen"

open ModularCurve.X1Degen in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (M p ℓ : ℕ) [NeZero M] [NeZero ℓ] [Fact p.Prime] (hpMℓ : ¬ p ∣ M * ℓ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    AlgebraicCurve.FiniteAlong (IsLocalRing.ResidueField P)
        (IntermediateField.inclusion
          (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField P)
            (inf_le_left : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
              CongruenceSubgroup.Gamma1 M))) ∧
      AlgebraicCurve.SeparableAlong (IsLocalRing.ResidueField P)
        (IntermediateField.inclusion
          (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField P)
            (inf_le_left : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
              CongruenceSubgroup.Gamma1 M))) ∧
      AlgebraicCurve.finrankAlong (IsLocalRing.ResidueField P)
          (IntermediateField.inclusion
            (ModularCurve.qExpFunctionFieldC_mono (IsLocalRing.ResidueField P)
              (inf_le_left : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) ≤
                CongruenceSubgroup.Gamma1 M))) =
        AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ)
          (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) ∧
      ∃ β : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M)
          →ₐ[IsLocalRing.ResidueField P]
          ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P)
            (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)),
        (∀ x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField P) (CongruenceSubgroup.Gamma1 M),
            (β x : LaurentSeries (IsLocalRing.ResidueField P)) =
              ModularCurve.qExpand (IsLocalRing.ResidueField P) ℓ
                (x : LaurentSeries (IsLocalRing.ResidueField P))) ∧
          AlgebraicCurve.FiniteAlong (IsLocalRing.ResidueField P) β := by
  refine ⟨finiteAlong_αb M ℓ P, separableAlong_αb M ℓ P, ?_, βb M ℓ P, coe_βb M ℓ P, finiteAlong_βb M ℓ P⟩
  exact ((finrankAlong_αb M ℓ P).trans (relfinrank_eq M ℓ P hpMℓ hP)).trans (finrankAlong_alpha M ℓ).symm

end S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_finrankAlong_inclusion_qExpFunctionFieldC_residueField_eq_of_not_dvd (solution)

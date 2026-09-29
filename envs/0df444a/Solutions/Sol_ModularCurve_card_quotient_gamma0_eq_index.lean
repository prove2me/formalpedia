-- Prove2me | solution 1 for ModularCurve.card_quotient_gamma0_eq_index
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/17689b13-6d6c-56da-a4db-7b4d4b3e1fe7

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Relrank
import Theorems.Thm_ModularForm_exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic
import Theorems.Thm_ModularCurve_Gamma0_index
import Theorems.Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant
import Theorems.Thm_ModularForm_exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant
import Theorems.Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionField
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_relfinrank_full_eq_dedekindPsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_card_quotient_gamma0_eq_index
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve p2m_export "ModularCurve" "dedekindPsi modularFunctionFieldFull laurentBaseChange jqNModC modularFunctionFieldC Gamma0_index jqModC_eq_qExpansion_E4_cube_div_discriminant exists_gamma0_qExpansion_div_eq_jqNModC coeffEmb_jq modularFunctionField_eq_full laurentBaseChange_modularFunctionField relfinrank_laurentBaseChange_modularFunctionFieldFull relfinrank_full_eq_dedekindPsi" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.card_quotient_gamma0_eq_index (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) = (CongruenceSubgroup.Gamma0 N).index := by
  rw [← Subgroup.index_eq_card]
  show Subgroup.relIndex _ _ = _
  rw [MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ Matrix.SpecialLinearGroup.mapGL_injective,
    Subgroup.relIndex_top_right]

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.card_quotient_gamma0_le_dedekindPsi (N : ℕ) [NeZero N] :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) ≤ ModularCurve.dedekindPsi N :=
  ((ModularCurve.card_quotient_gamma0_eq_index N).trans (ModularCurve.Gamma0_index N)).le

namespace AHBridge

noncomputable section

local notation "L" => LaurentSeries ℂ

def qe {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k) : L :=
  ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : L)

def JQ : L :=
  ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : L) ^ 3 /
    ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : L)

abbrev G0 (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := ↑(CongruenceSubgroup.Gamma0 N)

variable (N : ℕ)

lemma one_mem_strictPeriods : (1 : ℝ) ∈ (G0 N).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

lemma qe_mul {a b : ℤ} (f : ModularForm (G0 N) a) (g : ModularForm (G0 N) b) : qe (f.mul g) = qe f * qe g := by
  simp only [qe, ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods N), map_mul]

lemma qe_add {a : ℤ} (f g : ModularForm (G0 N) a) : qe (f + g) = qe f + qe g := by
  simp only [qe]
  rw [ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N), map_add]

lemma qe_neg {a : ℤ} (f : ModularForm (G0 N) a) : qe (-f) = -qe f := by
  simp only [qe]
  rw [ModularForm.coe_neg, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods N), map_neg]

lemma qe_smul {a : ℤ} (c : ℂ) (f : ModularForm (G0 N) a) : qe (c • f) = algebraMap ℂ L c * qe f := by
  simp only [qe]
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N), Algebra.smul_def,
    map_mul]
  congr 1

lemma qe_zero {a : ℤ} : qe (0 : ModularForm (G0 N) a) = 0 := by
  simp only [qe]
  rw [ModularForm.coe_zero, qExpansion_zero, map_zero]

lemma qe_eq_zero_iff {a : ℤ} (f : ModularForm (G0 N) a) : qe f = 0 ↔ f = 0 := by
  simp only [qe]
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods N)]
  exact (map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective)

lemma qe_mcast {a b : ℤ} (h : a = b) (f : ModularForm (G0 N) a) : qe (ModularForm.mcast h f) = qe f := by
  subst h; rfl

def IsRatio (x : L) : Prop :=
  ∃ (k : ℤ) (g h : ModularForm (G0 N) k), h ≠ 0 ∧ x = qe g / qe h

variable {N}

lemma IsRatio.mul {x y : L} (hx : IsRatio N x) (hy : IsRatio N y) : IsRatio N (x * y) := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  obtain ⟨k', g', h', hh', rfl⟩ := hy
  refine ⟨k + k', g.mul g', h.mul h', ?_, ?_⟩
  · intro h0
    have := (qe_eq_zero_iff N _).2 h0
    rw [qe_mul] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hh ((qe_eq_zero_iff N _).1 h1)
    · exact hh' ((qe_eq_zero_iff N _).1 h1)
  · rw [qe_mul, qe_mul]; ring

lemma IsRatio.add {x y : L} (hx : IsRatio N x) (hy : IsRatio N y) : IsRatio N (x + y) := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  obtain ⟨k', g', h', hh', rfl⟩ := hy
  have hqh : qe h ≠ 0 := fun h0 => hh ((qe_eq_zero_iff N _).1 h0)
  have hqh' : qe h' ≠ 0 := fun h0 => hh' ((qe_eq_zero_iff N _).1 h0)
  refine ⟨k + k', g.mul h' + ModularForm.mcast (add_comm k' k) (g'.mul h), h.mul h', ?_, ?_⟩
  · intro h0
    have := (qe_eq_zero_iff N _).2 h0
    rw [qe_mul] at this
    exact mul_ne_zero hqh hqh' this
  · rw [qe_add, qe_mcast, qe_mul, qe_mul, qe_mul]
    field_simp

lemma IsRatio.neg {x : L} (hx : IsRatio N x) : IsRatio N (-x) := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  exact ⟨k, -g, h, hh, by rw [qe_neg]; ring⟩

lemma IsRatio.inv {x : L} (hx : IsRatio N x) : IsRatio N x⁻¹ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  by_cases hg : g = 0
  · subst hg
    exact ⟨k, 0, h, hh, by simp [qe_zero]⟩
  · exact ⟨k, h, g, hg, by rw [inv_div]⟩

variable [NeZero N]

lemma exists_ne_zero : ∃ H : ModularForm (G0 N) 12, H ≠ 0 := by
  obtain ⟨_, H, hH, -⟩ := ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant N
  exact ⟨H, hH⟩

lemma IsRatio.const (c : ℂ) : IsRatio N (algebraMap ℂ L c) := by
  obtain ⟨H, hH⟩ := exists_ne_zero (N := N)
  have hqH : qe H ≠ 0 := fun h0 => hH ((qe_eq_zero_iff N _).1 h0)
  refine ⟨12, c • H, H, hH, ?_⟩
  rw [qe_smul, mul_div_assoc, div_self hqH, mul_one]

lemma IsRatio.zero : IsRatio N (0 : L) := by simpa using IsRatio.const (N := N) 0

lemma IsRatio.one : IsRatio N (1 : L) := by simpa using IsRatio.const (N := N) 1

variable (N)

def Kan : Subfield L where
  carrier := {x | IsRatio N x}
  mul_mem' := IsRatio.mul
  one_mem' := IsRatio.one
  add_mem' := IsRatio.add
  zero_mem' := IsRatio.zero
  neg_mem' := IsRatio.neg
  inv_mem' := fun _ => IsRatio.inv

lemma mem_Kan {x : L} : x ∈ Kan N ↔ IsRatio N x := Iff.rfl

lemma JQ_mem_Kan : JQ ∈ Kan N := by
  obtain ⟨G, H, hH, hGH⟩ := ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant N
  exact ⟨12, G, H, hH, hGH.symm⟩

lemma jqNModC_mem_Kan : ModularCurve.jqNModC ℂ N ∈ Kan N := by
  obtain ⟨G, H, hH, hGH⟩ := ModularCurve.exists_gamma0_qExpansion_div_eq_jqNModC N
  exact ⟨12, G, H, hH, hGH.symm⟩

abbrev K0 : IntermediateField ℂ L := IntermediateField.adjoin ℂ ({JQ} : Set L)

lemma K0_le_Kan : ∀ x ∈ K0, x ∈ Kan N := by
  intro x hx
  have hsub : (K0 : IntermediateField ℂ L) ≤
      (Kan N).toIntermediateField (fun c => IsRatio.const c) := by
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact JQ_mem_Kan N
  exact hsub hx

def KanK0 : IntermediateField K0 L :=
  (Kan N).toIntermediateField (fun c => K0_le_Kan N c c.2)

lemma mem_KanK0 {x : L} : x ∈ KanK0 N ↔ IsRatio N x := Iff.rfl

lemma exists_poly_of_isRatio {x : L} (hx : IsRatio N x) :
    ∃ B : Polynomial K0, B ≠ 0 ∧ B.natDegree ≤ ModularCurve.dedekindPsi N ∧ Polynomial.aeval x B = 0 := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  obtain ⟨B, hB0, hBdeg, hBx⟩ :=
    ModularForm.exists_polynomial_aeval_qExpansion_div_eq_zero_of_isArithmetic (one_mem_strictPeriods N) g h hh
  exact ⟨B, hB0, hBdeg.trans (ModularCurve.card_quotient_gamma0_le_dedekindPsi N), hBx⟩

lemma isIntegral_of_isRatio {x : L} (hx : IsRatio N x) : IsIntegral K0 x := by
  obtain ⟨B, hB0, -, hBx⟩ := exists_poly_of_isRatio N hx
  exact (isAlgebraic_iff_isIntegral).1 ⟨B, hB0, hBx⟩

lemma laurentBaseChange_eq :
    ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) =
      IntermediateField.adjoin ℂ ({JQ, ModularCurve.jqNModC ℂ N} : Set L) := by
  rw [← ModularCurve.modularFunctionField_eq_full, ModularCurve.laurentBaseChange_modularFunctionField,
    ModularCurve.modularFunctionFieldC, ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant]
  rfl

lemma K0_le_baseChange :
    (K0 : IntermediateField ℂ L) ≤ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) := by
  rw [laurentBaseChange_eq]
  exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 (Set.mem_insert _ _))

lemma finrank_baseChange :
    Module.finrank K0 (IntermediateField.extendScalars (K0_le_baseChange N)) = ModularCurve.dedekindPsi N := by
  have h1 := ModularCurve.relfinrank_laurentBaseChange_modularFunctionFieldFull ℂ N
  rw [ModularCurve.relfinrank_full_eq_dedekindPsi, ModularCurve.coeffEmb_jq,
    ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant] at h1
  have h2 : (IntermediateField.adjoin ℂ ({JQ} : Set L)).relfinrank
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) = ModularCurve.dedekindPsi N := h1
  rwa [IntermediateField.relfinrank_eq_finrank_of_le (K0_le_baseChange N)] at h2

theorem main {k : ℤ} (g h : ModularForm (G0 N) k) (hh : h ≠ 0) :
    qe g / qe h ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) := by
  set F : L := qe g / qe h with hF
  have hFr : IsRatio N F := ⟨k, g, h, hh, rfl⟩
  have hjr : IsRatio N (ModularCurve.jqNModC ℂ N) := jqNModC_mem_Kan N

  set E : IntermediateField K0 L :=
    IntermediateField.adjoin K0 ({ModularCurve.jqNModC ℂ N, F} : Set L) with hE
  haveI hEfin : FiniteDimensional K0 E := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    intro x hx
    rcases hx with rfl | hx
    · exact isIntegral_of_isRatio N hjr
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact isIntegral_of_isRatio N hFr

  have hEKan : E ≤ KanK0 N := by
    rw [hE, IntermediateField.adjoin_le_iff]
    intro x hx
    rcases hx with rfl | hx
    · exact hjr
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact hFr

  have hEdeg : Module.finrank K0 E ≤ ModularCurve.dedekindPsi N := by
    obtain ⟨α, hα⟩ := Field.exists_primitive_element K0 E
    have hαKan : IsRatio N (α : L) := hEKan α.2
    obtain ⟨B, hB0, hBdeg, hBα⟩ := exists_poly_of_isRatio N hαKan
    have hint : IsIntegral K0 α := .of_finite K0 α
    rw [← IntermediateField.finrank_top', ← hα, IntermediateField.adjoin.finrank hint]

    have hmin : minpoly K0 α = minpoly K0 (α : L) := by
      rw [← minpoly.algebraMap_eq (B := E) (B' := L) (algebraMap E L).injective α]
      rfl
    rw [hmin]
    have hle := minpoly.degree_le_of_ne_zero K0 (α : L) hB0 hBα
    exact (Polynomial.natDegree_le_natDegree hle).trans hBdeg

  set FL : IntermediateField K0 L := IntermediateField.extendScalars (K0_le_baseChange N) with hFL
  have hFLE : FL ≤ E := by
    intro x hx
    rw [hFL, IntermediateField.mem_extendScalars, laurentBaseChange_eq] at hx

    have hsub : IntermediateField.adjoin ℂ ({JQ, ModularCurve.jqNModC ℂ N} : Set L) ≤ E.restrictScalars ℂ := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      rcases hy with rfl | hy
      ·
        show JQ ∈ E
        have hJ : JQ ∈ (K0 : IntermediateField ℂ L) := IntermediateField.subset_adjoin ℂ _ (Set.mem_singleton _)
        exact E.algebraMap_mem ⟨JQ, hJ⟩
      · rw [Set.mem_singleton_iff] at hy; subst hy
        show ModularCurve.jqNModC ℂ N ∈ E
        exact IntermediateField.subset_adjoin K0 _ (Set.mem_insert _ _)
    exact hsub hx
  have hEq : FL = E :=
    IntermediateField.eq_of_le_of_finrank_le hFLE (by rw [hFL, finrank_baseChange]; exact hEdeg)
  have hFE : F ∈ E := IntermediateField.subset_adjoin K0 _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [← hEq, hFL, IntermediateField.mem_extendScalars] at hFE
  exact hFE

end

end AHBridge

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.qExpansion_div_mem_laurentBaseChange (N : ℕ) [NeZero N] {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0) :
    ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) /
        ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N) :=
  AHBridge.main N g h hh

example : ModularCurve.dedekindPsi 4 = 6 := by decide +kernel

example : ModularCurve.dedekindPsi 1 = 1 := by decide +kernel
example : Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
    (CongruenceSubgroup.Gamma0 1)).subgroupOf 𝒮ℒ) = 1 := by
  rw [ModularCurve.card_quotient_gamma0_eq_index, Subgroup.index_eq_one]
  ext γ
  simp only [CongruenceSubgroup.Gamma0_mem, Subgroup.mem_top, iff_true]
  exact Subsingleton.elim _ _

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_card_quotient_gamma0_eq_index.ModularCurve in
open UpperHalfPlane
open scoped MatrixGroups in

theorem solution (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) = (CongruenceSubgroup.Gamma0 N).index :=
  ModularCurve.card_quotient_gamma0_eq_index N

#print axioms solution

end S_ModularCurve_card_quotient_gamma0_eq_index
end P2MW
export P2MW.S_ModularCurve_card_quotient_gamma0_eq_index (solution)

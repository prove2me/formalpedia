-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/4b7cb847-287e-5bf9-a166-4eaf41f951e8

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_AdditiveJacquet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Hom.Basic
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum.LanglandsTunnell.CubicInduction"

noncomputable section

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum.LanglandsTunnell.CubicInduction Filter Topology"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 upperUnipotent3_inv_eq unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellCutoff_subset_bigCell3 cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul jacquetWhittaker3 diagonal3 diagonal3_coe principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 gl3Det_antidiagonal3 antidiagonal3_mem_cellCutoff cellSection_antidiagonal3_ne_zero eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det gl3Det_eq_bottom_expansion exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3 properSpace_adicCompletion_rat isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace T0bAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem eventually_lt_norm_div {n d : LocalGL3 v → v.adicCompletion ℚ} {g : LocalGL3 v}
    (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0) (hdg : d g = 0) (M : ℝ) :
    ∀ᶠ h in 𝓝 g, d h ≠ 0 → M < ‖n h / d h‖ := by
  have h1 : ∀ᶠ h in 𝓝 g, ‖n h‖ = ‖n g‖ := (hn.tendsto g).eventually (eventually_norm_eq v hng)
  have hpos : 0 < ‖n g‖ := norm_pos_iff.mpr hng
  have hεpos : 0 < ‖n g‖ / (max M 0 + 1) := div_pos hpos (by positivity)
  have h2 : ∀ᶠ h in 𝓝 g, ‖d h‖ < ‖n g‖ / (max M 0 + 1) := by
    have ht : Tendsto d (𝓝 g) (𝓝 0) := by simpa [hdg] using hd.tendsto g
    exact NormedAddGroup.tendsto_nhds_zero.mp ht _ hεpos
  filter_upwards [h1, h2] with h hn' hd' hd0
  have hdpos : 0 < ‖d h‖ := norm_pos_iff.mpr hd0
  rw [norm_div, hn']
  calc M ≤ max M 0 := le_max_left _ _
    _ < max M 0 + 1 := by linarith
    _ = ‖n g‖ / (‖n g‖ / (max M 0 + 1)) := by field_simp
    _ < ‖n g‖ / ‖d h‖ := div_lt_div_of_pos_left hpos hdpos hd'

private theorem eventually_cellSectionOf_eq_of_den (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : HasCompactSupport Φ) {g : LocalGL3 v}
    {n d : LocalGL3 v → v.adicCompletion ℚ} (i : Fin 3) (hn : Continuous n) (hd : Continuous d) (hng : n g ≠ 0)
    (hdg : d g = 0) (hratio : ∀ h, cellRatio v h i = n h / d h) (hden : ∀ h, h ∈ bigCell3 v → d h ≠ 0) :
    ∀ᶠ h in 𝓝 g, cellSectionOf v χ Φ h = cellSectionOf v χ Φ g := by
  obtain ⟨M, hM⟩ := (hΦ : IsCompact (tsupport Φ)).isBounded.exists_norm_le
  have hg : g ∉ bigCell3 v := fun hmem => hden g hmem hdg
  rw [cellSectionOf_apply_of_notMem v χ Φ hg]
  filter_upwards [eventually_lt_norm_div v hn hd hng hdg M] with h hh
  by_cases hmem : h ∈ bigCell3 v
  · rw [cellSectionOf_apply_of_mem v χ Φ hmem]
    have hi : M < ‖cellRatio v h i‖ := by rw [hratio]; exact hh (hden h hmem)
    have hbig : M < ‖cellRatio v h‖ := lt_of_lt_of_le hi (norm_le_pi_norm (cellRatio v h) i)
    have hΦ0 : Φ (cellRatio v h) = 0 :=
      image_eq_zero_of_notMem_tsupport fun hr => (not_lt.mpr (hM _ hr)) hbig
    rw [hΦ0, mul_zero]
  · exact cellSectionOf_apply_of_notMem v χ Φ hmem

private theorem cellSectionOf_mem_principalSeries3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ)
    (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    cellSectionOf v χ Φ ∈ principalSeries3 v χ := by
  refine ⟨?_, cellSectionOf_upperUnipotent3_mul v χ Φ, cellSectionOf_diagonal3_mul v χ Φ⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  by_cases hc : cornerEntry v g = 0
  · rcases exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero v hc with h21 | h22
    · exact eventually_cellSectionOf_eq_of_den v χ Φ hΦ.2 0 (continuous_gl3Entry v 2 1) (continuous_cornerEntry v)
        h21 hc (fun h => rfl) (fun h hh => hh.1)
    · exact eventually_cellSectionOf_eq_of_den v χ Φ hΦ.2 1 (continuous_gl3Entry v 2 2) (continuous_cornerEntry v)
        h22 hc (fun h => rfl) (fun h hh => hh.1)
  by_cases hl : lowerMinor v g = 0
  · exact eventually_cellSectionOf_eq_of_den v χ Φ hΦ.2 2 (continuous_outerMinor v) (continuous_lowerMinor v)
      (outerMinor_ne_zero_of_lowerMinor_eq_zero v hc hl) hl (fun h => rfl) (fun h hh => hh.2)
  have hcA : ContinuousAt (cornerEntry v) g := (continuous_cornerEntry v).continuousAt
  have hlA : ContinuousAt (lowerMinor v) g := (continuous_lowerMinor v).continuousAt
  have hdA : ContinuousAt (gl3Det v) g := (continuous_gl3Det v).continuousAt
  have hr : ContinuousAt (cellRatio v) g := by
    refine continuousAt_pi.mpr fun i => ?_
    fin_cases i
    · exact ((continuous_gl3Entry v 2 1).continuousAt).div hcA hc
    · exact ((continuous_gl3Entry v 2 2).continuousAt).div hcA hc
    · exact ((continuous_outerMinor v).continuousAt).div hlA hl
  have hbig : ∀ᶠ h in 𝓝 g, h ∈ bigCell3 v := by
    filter_upwards [hcA.eventually_ne hc, hlA.eventually_ne hl] with h hch hlh
    exact ⟨hch, hlh⟩
  have hΦr : ∀ᶠ h in 𝓝 g, Φ (cellRatio v h) = Φ (cellRatio v g) := hr.eventually (hΦ.1.eventually_eq _)
  have hval : ∀ᶠ h in 𝓝 g, cellValue v χ h = cellValue v χ g := by
    have hq0 : gl3Det v g / lowerMinor v g ≠ 0 := div_ne_zero (gl3Det_ne_zero v g) hl
    have hq1 : lowerMinor v g / cornerEntry v g ≠ 0 := div_ne_zero hl hc
    have e0 : ∀ᶠ h in nhds g,
        charExt (χ 0) (gl3Det v h / lowerMinor v h) = charExt (χ 0) (gl3Det v g / lowerMinor v g) :=
      (hdA.div hlA hl).eventually (eventually_charExt_eq v (χ 0) (hχ 0) hq0)
    have e1 : ∀ᶠ h in nhds g,
        charExt (χ 1) (lowerMinor v h / cornerEntry v h) = charExt (χ 1) (lowerMinor v g / cornerEntry v g) :=
      (hlA.div hcA hc).eventually (eventually_charExt_eq v (χ 1) (hχ 1) hq1)
    have e2 : ∀ᶠ h in nhds g, charExt (χ 2) (cornerEntry v h) = charExt (χ 2) (cornerEntry v g) :=
      hcA.eventually (eventually_charExt_eq v (χ 2) (hχ 2) hc)
    have e3 : ∀ᶠ h in nhds g, ‖gl3Det v h / lowerMinor v h‖ = ‖gl3Det v g / lowerMinor v g‖ :=
      (hdA.div hlA hl).eventually (eventually_norm_eq v hq0)
    have e4 : ∀ᶠ h in nhds g, ‖cornerEntry v h‖ = ‖cornerEntry v g‖ := hcA.eventually (eventually_norm_eq v hc)
    filter_upwards [e0, e1, e2, e3, e4] with h h0 h1 h2 h3 h4
    simp only [cellValue, h0, h1, h2, h3, h4]
  filter_upwards [hbig, hΦr, hval] with h h1 h2 h3
  rw [cellSectionOf_apply_of_mem v χ Φ h1, cellSectionOf_apply_of_mem v χ Φ ⟨hc, hl⟩, h2, h3]

end LanglandsTunnell.CubicInduction.T0bAux

section

namespace T0Cover

open Matrix

variable {F : Type*} [Field F]

private def lowerMinorCols (M : Matrix (Fin 3) (Fin 3) F) (a b : Fin 3) : F :=
  M 1 a * M 2 b - M 1 b * M 2 a

private theorem exists_bottom_ne_zero (M : Matrix (Fin 3) (Fin 3) F) (hM : M.det ≠ 0) : ∃ a, M 2 a ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  rw [Matrix.det_fin_three]
  simp [h 0, h 1, h 2]

private theorem exists_lowerMinorCols_ne_zero (M : Matrix (Fin 3) (Fin 3) F) (hM : M.det ≠ 0) {a : Fin 3}
    (ha : M 2 a ≠ 0) : ∃ b, b ≠ a ∧ lowerMinorCols M a b ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  have key : M.det * M 2 a = 0 := by
    fin_cases a <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] at h ⊢
    · have h1 : M 1 0 * M 2 1 - M 1 1 * M 2 0 = 0 := h 1 (by decide)
      have h2 : M 1 0 * M 2 2 - M 1 2 * M 2 0 = 0 := h 2 (by decide)
      rw [Matrix.det_fin_three]
      linear_combination (M 0 2 * M 2 0 - M 0 0 * M 2 2) * h1 + (M 0 0 * M 2 1 - M 0 1 * M 2 0) * h2
    · have h0 : M 1 1 * M 2 0 - M 1 0 * M 2 1 = 0 := h 0 (by decide)
      have h2 : M 1 1 * M 2 2 - M 1 2 * M 2 1 = 0 := h 2 (by decide)
      rw [Matrix.det_fin_three]
      linear_combination (M 0 1 * M 2 2 - M 0 2 * M 2 1) * h0 + (M 0 0 * M 2 1 - M 0 1 * M 2 0) * h2
    · have h0 : M 1 2 * M 2 0 - M 1 0 * M 2 2 = 0 := h 0 (by decide)
      have h1 : M 1 2 * M 2 1 - M 1 1 * M 2 2 = 0 := h 1 (by decide)
      rw [Matrix.det_fin_three]
      linear_combination (M 0 1 * M 2 2 - M 0 2 * M 2 1) * h0 + (M 0 2 * M 2 0 - M 0 0 * M 2 2) * h1
  exact (mul_eq_zero.mp key).resolve_right ha

private theorem exists_argmax_bottom_and_lowerMinorCols (N : F → ℝ) (hN0 : ∀ x, 0 ≤ N x) (hN : ∀ x, N x = 0 ↔ x = 0)
    (M : Matrix (Fin 3) (Fin 3) F) (hM : M.det ≠ 0) :
    ∃ a b : Fin 3, b ≠ a ∧ M 2 a ≠ 0 ∧ (∀ j, N (M 2 j) ≤ N (M 2 a)) ∧ lowerMinorCols M a b ≠ 0 ∧
      ∀ j, j ≠ a → N (lowerMinorCols M a j) ≤ N (lowerMinorCols M a b) := by
  classical
  obtain ⟨a, -, hamax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 3)) (fun j => N (M 2 j))
    ⟨0, Finset.mem_univ 0⟩
  have ha : M 2 a ≠ 0 := by
    obtain ⟨a', ha'⟩ := exists_bottom_ne_zero M hM
    intro hz
    have h1 : N (M 2 a') ≤ N (M 2 a) := hamax a' (Finset.mem_univ a')
    rw [hz, (hN 0).mpr rfl] at h1
    exact ha' ((hN _).mp (le_antisymm h1 (hN0 _)))
  obtain ⟨b, hbmem, hbmax⟩ := Finset.exists_max_image (Finset.univ.filter fun j => j ≠ a)
    (fun j => N (lowerMinorCols M a j)) (by
      obtain ⟨b₀, hb₀, -⟩ := exists_lowerMinorCols_ne_zero M hM ha
      exact ⟨b₀, Finset.mem_filter.mpr ⟨Finset.mem_univ b₀, hb₀⟩⟩)
  have hba : b ≠ a := (Finset.mem_filter.mp hbmem).2
  have hb : lowerMinorCols M a b ≠ 0 := by
    obtain ⟨b', hb'a, hb'⟩ := exists_lowerMinorCols_ne_zero M hM ha
    intro hz
    have h1 : N (lowerMinorCols M a b') ≤ N (lowerMinorCols M a b) :=
      hbmax b' (Finset.mem_filter.mpr ⟨Finset.mem_univ b', hb'a⟩)
    rw [hz, (hN 0).mpr rfl] at h1
    exact hb' ((hN _).mp (le_antisymm h1 (hN0 _)))
  refine ⟨a, b, hba, ha, fun j => hamax j (Finset.mem_univ j), hb, fun j hj => ?_⟩
  exact hbmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

end T0Cover

namespace T0Cover

open Filter Topology

variable {X : Type*} [TopologicalSpace X] {ι : Type*} {β : Type*} [LinearOrder β]

private noncomputable def argmaxIn [DecidableEq ι] (S : Finset ι) (w : ι → β) : Finset ι :=
  S.filter fun a => ∀ j ∈ S, w j ≤ w a

private theorem mem_argmaxIn_iff [DecidableEq ι] (S : Finset ι) (w : ι → β) (a : ι) :
    a ∈ argmaxIn S w ↔ a ∈ S ∧ ∀ j ∈ S, w j ≤ w a := by
  simp [argmaxIn]

private theorem argmaxIn_nonempty [DecidableEq ι] {S : Finset ι} (hS : S.Nonempty) (w : ι → β) :
    (argmaxIn S w).Nonempty := by
  obtain ⟨a, haS, ha⟩ := Finset.exists_max_image S w hS
  exact ⟨a, (mem_argmaxIn_iff S w a).mpr ⟨haS, ha⟩⟩

private theorem
    argmaxIn_comp_strictMono
    [DecidableEq ι] (S : Finset ι) (w : ι → β) {γ : Type*} [LinearOrder γ] {φ : β → γ}
    (hφ : StrictMono φ) : argmaxIn S (fun j => φ (w j)) = argmaxIn S w := by
  ext a
  simp only [mem_argmaxIn_iff, hφ.le_iff_le]

private theorem eventually_argmaxIn_eq [DecidableEq ι] (S : Finset ι) (N : ι → X → β) (x : X) {a₀ : ι} (ha₀ : a₀ ∈ S)
    (hmax : ∀ j ∈ S, N j x ≤ N a₀ x)
    (hN : ∀ j ∈ S, (∀ᶠ y in 𝓝 x, N j y = N j x) ∨ (N j x < N a₀ x ∧ ∀ᶠ y in 𝓝 x, N j y < N a₀ x)) :
    ∀ᶠ y in 𝓝 x, argmaxIn S (fun j => N j y) = argmaxIn S (fun j => N j x) := by
  have hQ : ∀ j ∈ S, ∀ᶠ y in 𝓝 x, N j y = N j x ∨ (N j x < N a₀ x ∧ N j y < N a₀ x) := by
    intro j hj
    rcases hN j hj with h | ⟨hlt, h⟩
    · exact h.mono fun _ hy => Or.inl hy
    · exact h.mono fun _ hy => Or.inr ⟨hlt, hy⟩
  have hall : ∀ᶠ y in 𝓝 x, ∀ j ∈ S, N j y = N j x ∨ (N j x < N a₀ x ∧ N j y < N a₀ x) :=
    (S.eventually_all).mpr hQ
  refine hall.mono fun y hy => ?_
  have ha₀y : N a₀ y = N a₀ x := by
    rcases hy a₀ ha₀ with h | ⟨hlt, -⟩
    · exact h
    · exact absurd hlt (lt_irrefl _)
  ext a
  rw [mem_argmaxIn_iff, mem_argmaxIn_iff]
  constructor
  · rintro ⟨haS, hay⟩
    refine ⟨haS, ?_⟩
    have hge : N a₀ x ≤ N a y := by rw [← ha₀y]; exact hay a₀ ha₀
    rcases hy a haS with h | ⟨-, hlt⟩
    · intro j hj
      exact (hmax j hj).trans (hge.trans_eq h)
    · exact absurd hge (not_le.mpr hlt)
  · rintro ⟨haS, hax⟩
    refine ⟨haS, ?_⟩
    have hax' : N a x = N a₀ x := le_antisymm (hmax a haS) (hax a₀ ha₀)
    have hay : N a y = N a₀ x := by
      rcases hy a haS with h | ⟨hlt, -⟩
      · rw [h, hax']
      · exact absurd hax' (ne_of_lt hlt)
    intro j hj
    rcases hy j hj with h | ⟨-, hlt⟩
    · rw [h, hay]; exact hmax j hj
    · rw [hay]; exact hlt.le

private noncomputable def
    firstArgmaxIn
    [DecidableEq ι] [LinearOrder ι] (S : Finset ι) (hS : S.Nonempty) (w : ι → β) : ι :=
  (argmaxIn S w).min' (argmaxIn_nonempty hS w)

private theorem firstArgmaxIn_mem [DecidableEq ι] [LinearOrder ι] (S : Finset ι) (hS : S.Nonempty) (w : ι → β) :
    firstArgmaxIn S hS w ∈ S ∧ ∀ j ∈ S, w j ≤ w (firstArgmaxIn S hS w) :=
  (mem_argmaxIn_iff S w _).mp (Finset.min'_mem _ _)

private theorem
    firstArgmaxIn_comp_strictMono
    [DecidableEq ι] [LinearOrder ι] (S : Finset ι) (hS : S.Nonempty) (w : ι → β)
    {γ : Type*} [LinearOrder γ] {φ : β → γ} (hφ : StrictMono φ) :
    firstArgmaxIn S hS (fun j => φ (w j)) = firstArgmaxIn S hS w := by
  simp only [firstArgmaxIn, argmaxIn_comp_strictMono S w hφ]

private theorem firstArgmaxIn_congr [DecidableEq ι] [LinearOrder ι] (S : Finset ι) (hS : S.Nonempty) {w w' : ι → β}
    (h : argmaxIn S w = argmaxIn S w') : firstArgmaxIn S hS w = firstArgmaxIn S hS w' := by
  simp only [firstArgmaxIn, h]

private theorem eventually_firstArgmaxIn_eq [DecidableEq ι] [LinearOrder ι] (S : Finset ι) (hS : S.Nonempty)
    (N : ι → X → β) (x : X) {a₀ : ι} (ha₀ : a₀ ∈ S) (hmax : ∀ j ∈ S, N j x ≤ N a₀ x)
    (hN : ∀ j ∈ S, (∀ᶠ y in 𝓝 x, N j y = N j x) ∨ (N j x < N a₀ x ∧ ∀ᶠ y in 𝓝 x, N j y < N a₀ x)) :
    ∀ᶠ y in 𝓝 x, firstArgmaxIn S hS (fun j => N j y) = firstArgmaxIn S hS (fun j => N j x) :=
  (eventually_argmaxIn_eq S N x ha₀ hmax hN).mono fun _ hy => firstArgmaxIn_congr S hS hy

end T0Cover

open Matrix IsDedekindDomain NumberField

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 upperUnipotent3_inv_eq unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellCutoff_subset_bigCell3 cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul jacquetWhittaker3 diagonal3 diagonal3_coe principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 gl3Det_antidiagonal3 antidiagonal3_mem_cellCutoff cellSection_antidiagonal3_ne_zero eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det gl3Det_eq_bottom_expansion exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3 properSpace_adicCompletion_rat isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace T0Aux

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_mul_upperUnipotent3_zero (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 0 = gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_upperUnipotent3_one (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 1 = gl3Entry v g i 1 + x * gl3Entry v g i 0 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem gl3Entry_mul_upperUnipotent3_two (g : LocalGL3 v) (x y z : v.adicCompletion ℚ) (i : Fin 3) :
    gl3Entry v (g * upperUnipotent3 x y z) i 2 = gl3Entry v g i 2 + z * gl3Entry v g i 0 + y * gl3Entry v g i 1 := by
  simp [gl3Entry, Matrix.mul_apply, Fin.sum_univ_three]
  ring

private theorem gl3Entry_mul_antidiagonal3_zero (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * antidiagonal3 v) i 0 = gl3Entry v g i 2 := by
  simp [gl3Entry, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_antidiagonal3_one (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * antidiagonal3 v) i 1 = gl3Entry v g i 1 := by
  simp [gl3Entry, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem gl3Entry_mul_antidiagonal3_two (g : LocalGL3 v) (i : Fin 3) :
    gl3Entry v (g * antidiagonal3 v) i 2 = gl3Entry v g i 0 := by
  simp [gl3Entry, antidiagonal3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem
    cornerEntry_mul_antidiagonal3
    (h : LocalGL3 v) : cornerEntry v (h * antidiagonal3 v) = gl3Entry v h 2 2 := by
  rw [cornerEntry, gl3Entry_mul_antidiagonal3_zero]

private theorem lowerMinor_mul_antidiagonal3 (h : LocalGL3 v) :
    lowerMinor v (h * antidiagonal3 v) =
      -(gl3Entry v h 1 1 * gl3Entry v h 2 2 - gl3Entry v h 1 2 * gl3Entry v h 2 1) := by
  simp only [lowerMinor, gl3Entry_mul_antidiagonal3_zero, gl3Entry_mul_antidiagonal3_one]
  ring

private theorem outerMinor_mul_antidiagonal3 (h : LocalGL3 v) :
    outerMinor v (h * antidiagonal3 v) =
      -(gl3Entry v h 1 0 * gl3Entry v h 2 2 - gl3Entry v h 1 2 * gl3Entry v h 2 0) := by
  simp only [outerMinor, gl3Entry_mul_antidiagonal3_zero, gl3Entry_mul_antidiagonal3_two]
  ring

private theorem mul_antidiagonal3_mem_cellCutoff (h : LocalGL3 v) (h22 : gl3Entry v h 2 2 ≠ 0)
    (hrow : ∀ j, Valued.v (gl3Entry v h 2 j) ≤ Valued.v (gl3Entry v h 2 2))
    (hμ : gl3Entry v h 1 1 * gl3Entry v h 2 2 - gl3Entry v h 1 2 * gl3Entry v h 2 1 ≠ 0)
    (hμle : Valued.v (gl3Entry v h 1 0 * gl3Entry v h 2 2 - gl3Entry v h 1 2 * gl3Entry v h 2 0) ≤
      Valued.v (gl3Entry v h 1 1 * gl3Entry v h 2 2 - gl3Entry v h 1 2 * gl3Entry v h 2 1)) :
    h * antidiagonal3 v ∈ cellCutoff v := by
  have hpos : 0 < Valued.v (gl3Entry v h 2 2) :=
    lt_of_le_of_ne zero_le' ((Valuation.ne_zero_iff _).mpr h22).symm
  have hμpos : 0 < Valued.v (gl3Entry v h 1 1 * gl3Entry v h 2 2 - gl3Entry v h 1 2 * gl3Entry v h 2 1) :=
    lt_of_le_of_ne zero_le' ((Valuation.ne_zero_iff _).mpr hμ).symm
  rw [cellCutoff, Set.mem_setOf_eq]
  refine ⟨?_, ?_, fun i => ?_⟩
  · rw [cornerEntry_mul_antidiagonal3]
    exact h22
  · rw [lowerMinor_mul_antidiagonal3]
    exact neg_ne_zero.mpr hμ
  fin_cases i
  · show Valued.v (cellRatio v (h * antidiagonal3 v) 0) ≤ 1
    simp only [cellRatio, Matrix.cons_val_zero, cornerEntry_mul_antidiagonal3, gl3Entry_mul_antidiagonal3_one,
      map_div₀]
    exact (div_le_one₀ hpos).mpr (hrow 1)
  · show Valued.v (cellRatio v (h * antidiagonal3 v) 1) ≤ 1
    simp only [cellRatio, Matrix.cons_val_one, Matrix.cons_val_zero, cornerEntry_mul_antidiagonal3,
      gl3Entry_mul_antidiagonal3_two, map_div₀]
    exact (div_le_one₀ hpos).mpr (hrow 0)
  · show Valued.v (cellRatio v (h * antidiagonal3 v) 2) ≤ 1
    simp only [cellRatio, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, outerMinor_mul_antidiagonal3,
      lowerMinor_mul_antidiagonal3, neg_div_neg_eq, map_div₀]
    exact (div_le_one₀ hμpos).mpr hμle

end T0Aux

end LanglandsTunnell.CubicInduction

open Matrix IsDedekindDomain NumberField Filter Topology

noncomputable section

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 upperUnipotent3_inv_eq unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellCutoff_subset_bigCell3 cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul jacquetWhittaker3 diagonal3 diagonal3_coe principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 gl3Det_antidiagonal3 antidiagonal3_mem_cellCutoff cellSection_antidiagonal3_ne_zero eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det gl3Det_eq_bottom_expansion exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3 properSpace_adicCompletion_rat isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

namespace T0Aux

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def rowVal (g : LocalGL3 v) (j : Fin 3) := Valued.v (gl3Entry v g 2 j)

private def rowArgmax (g : LocalGL3 v) : Finset (Fin 3) := T0Cover.argmaxIn Finset.univ (rowVal v g)

private def stage1Col (A : Finset (Fin 3)) : Fin 3 := if (2 : Fin 3) ∈ A then 2 else if (0 : Fin 3) ∈ A then 0 else 1

private def yzOf (c : Fin 3) : v.adicCompletion ℚ × v.adicCompletion ℚ :=
  if c = 2 then (0, 0) else if c = 1 then (1, 0) else (0, 1)

private def n1Of (g : LocalGL3 v) : LocalGL3 v :=
  upperUnipotent3 0 (yzOf v (stage1Col (rowArgmax v g))).1 (yzOf v (stage1Col (rowArgmax v g))).2

private theorem
    mem_rowArgmax_iff
    (g : LocalGL3 v) (a : Fin 3) : a ∈ rowArgmax v g ↔ ∀ j, rowVal v g j ≤ rowVal v g a := by
  simp [rowArgmax, T0Cover.mem_argmaxIn_iff]

private theorem rowArgmax_nonempty (g : LocalGL3 v) : (rowArgmax v g).Nonempty :=
  T0Cover.argmaxIn_nonempty Finset.univ_nonempty _

private theorem exists_rowVal_pos (g : LocalGL3 v) : ∃ a, 0 < rowVal v g a := by
  have hdet : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := gl3Det_ne_zero v g
  obtain ⟨a, ha⟩ := T0Cover.exists_bottom_ne_zero _ hdet
  exact ⟨a, lt_of_le_of_ne zero_le' ((Valuation.ne_zero_iff _).mpr ha).symm⟩

private theorem
    rowVal_pos_of_mem_rowArgmax
    (g : LocalGL3 v) {a : Fin 3} (ha : a ∈ rowArgmax v g) : 0 < rowVal v g a := by
  obtain ⟨a', ha'⟩ := exists_rowVal_pos v g
  exact ha'.trans_le (((mem_rowArgmax_iff v g a).mp ha) a')

private theorem stage1Col_mem (A : Finset (Fin 3)) (hA : A.Nonempty) : stage1Col A ∈ A := by
  unfold stage1Col
  split_ifs with h2 h0
  · exact h2
  · exact h0
  · obtain ⟨a, ha⟩ := hA
    fin_cases a
    · exact absurd ha h0
    · exact ha
    · exact absurd ha h2

private theorem stage1_spec (g : LocalGL3 v) :
    gl3Entry v (g * n1Of v g) 2 2 ≠ 0 ∧
      ∀ j, Valued.v (gl3Entry v (g * n1Of v g) 2 j) ≤ Valued.v (gl3Entry v (g * n1Of v g) 2 2) := by
  set A := rowArgmax v g with hA
  have hc : stage1Col A ∈ A := stage1Col_mem A (rowArgmax_nonempty v g)
  have hcmax : ∀ j, rowVal v g j ≤ rowVal v g (stage1Col A) := (mem_rowArgmax_iff v g _).mp hc
  have hcpos : 0 < rowVal v g (stage1Col A) := rowVal_pos_of_mem_rowArgmax v g hc

  have e0 : gl3Entry v (g * n1Of v g) 2 0 = gl3Entry v g 2 0 := gl3Entry_mul_upperUnipotent3_zero v g _ _ _ 2
  have e1 : gl3Entry v (g * n1Of v g) 2 1 = gl3Entry v g 2 1 := by
    rw [n1Of, gl3Entry_mul_upperUnipotent3_one, zero_mul, add_zero]
  have e2 : gl3Entry v (g * n1Of v g) 2 2 =
      gl3Entry v g 2 2 + (yzOf v (stage1Col A)).2 * gl3Entry v g 2 0 +
        (yzOf v (stage1Col A)).1 * gl3Entry v g 2 1 := by
    rw [n1Of, gl3Entry_mul_upperUnipotent3_two]

  have key : Valued.v (gl3Entry v (g * n1Of v g) 2 2) = rowVal v g (stage1Col A) := by
    rw [e2]
    unfold stage1Col yzOf
    by_cases h2 : (2 : Fin 3) ∈ A
    · simp [h2, rowVal]
    · have hlt : rowVal v g 2 < rowVal v g (stage1Col A) := by
        have : ¬ ∀ j, rowVal v g j ≤ rowVal v g 2 := fun h => h2 ((mem_rowArgmax_iff v g 2).mpr h)
        push Not at this
        obtain ⟨j, hj⟩ := this
        exact hj.trans_le (hcmax j)
      unfold stage1Col at hlt
      by_cases h0 : (0 : Fin 3) ∈ A
      · simp only [h2, h0, if_false, if_true] at hlt ⊢
        simp only [show ((0 : Fin 3) = 2) = False by decide, show ((0 : Fin 3) = 1) = False by decide, if_false,
          one_mul, zero_mul, add_zero]
        rw [rowVal] at hlt ⊢
        exact Valuation.map_add_eq_of_lt_right _ hlt
      · simp only [h2, h0, if_false] at hlt ⊢
        simp only [show ((1 : Fin 3) = 2) = False by decide, if_false, if_true, one_mul, zero_mul, add_zero]
        rw [rowVal] at hlt ⊢
        exact Valuation.map_add_eq_of_lt_right _ hlt
  refine ⟨fun hz => ?_, fun j => ?_⟩
  · rw [hz, map_zero] at key
    exact hcpos.ne key
  · rw [key]
    fin_cases j
    · show Valued.v (gl3Entry v (g * n1Of v g) 2 0) ≤ _
      rw [e0]; exact hcmax 0
    · show Valued.v (gl3Entry v (g * n1Of v g) 2 1) ≤ _
      rw [e1]; exact hcmax 1
    · show Valued.v (gl3Entry v (g * n1Of v g) 2 2) ≤ _
      rw [key]

private def colMinor (h : LocalGL3 v) (j : Fin 3) : v.adicCompletion ℚ :=
  gl3Entry v h 1 j * gl3Entry v h 2 2 - gl3Entry v h 1 2 * gl3Entry v h 2 j

private def epsOf (g : LocalGL3 v) : v.adicCompletion ℚ :=
  if Valued.v (colMinor v (g * n1Of v g) 0) ≤ Valued.v (colMinor v (g * n1Of v g) 1) then 0 else 1

private def nOf (g : LocalGL3 v) : LocalGL3 v :=
  upperUnipotent3 (epsOf v g) (yzOf v (stage1Col (rowArgmax v g))).1 (yzOf v (stage1Col (rowArgmax v g))).2

private theorem mul_nOf_eq (g : LocalGL3 v) : g * nOf v g = g * n1Of v g * upperUnipotent3 (epsOf v g) 0 0 := by
  rw [mul_assoc, n1Of, nOf, upperUnipotent3_mul_upperUnipotent3]
  congr 2 <;> simp

private theorem colMinor_mul_upperUnipotent3_x (h : LocalGL3 v) (x : v.adicCompletion ℚ) :
    colMinor v (h * upperUnipotent3 x 0 0) 0 = colMinor v h 0 ∧
      colMinor v (h * upperUnipotent3 x 0 0) 1 = colMinor v h 1 + x * colMinor v h 0 ∧
      (∀ i, gl3Entry v (h * upperUnipotent3 x 0 0) i 2 = gl3Entry v h i 2) ∧
      (∀ i, gl3Entry v (h * upperUnipotent3 x 0 0) i 0 = gl3Entry v h i 0) ∧
      ∀ i, gl3Entry v (h * upperUnipotent3 x 0 0) i 1 = gl3Entry v h i 1 + x * gl3Entry v h i 0 := by
  refine ⟨?_, ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · simp only [colMinor, gl3Entry_mul_upperUnipotent3_zero, gl3Entry_mul_upperUnipotent3_two, zero_mul, add_zero]
  · simp only [colMinor, gl3Entry_mul_upperUnipotent3_one, gl3Entry_mul_upperUnipotent3_two, zero_mul, add_zero]
    ring
  · rw [gl3Entry_mul_upperUnipotent3_two, zero_mul, zero_mul, add_zero, add_zero]
  · exact gl3Entry_mul_upperUnipotent3_zero v h _ _ _ i
  · exact gl3Entry_mul_upperUnipotent3_one v h _ _ _ i

private theorem exists_colMinor_ne_zero (h : LocalGL3 v) (h22 : gl3Entry v h 2 2 ≠ 0) :
    colMinor v h 0 ≠ 0 ∨ colMinor v h 1 ≠ 0 := by
  have hdet : (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)).det ≠ 0 := gl3Det_ne_zero v h
  obtain ⟨b, hb2, hb⟩ := T0Cover.exists_lowerMinorCols_ne_zero _ hdet (a := 2) h22
  have hneg : ∀ j, T0Cover.lowerMinorCols (h : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 j = -colMinor v h j := by
    intro j
    simp only [T0Cover.lowerMinorCols, colMinor, gl3Entry]
    ring
  rw [hneg, neg_ne_zero] at hb
  fin_cases b
  · exact Or.inl hb
  · exact Or.inr hb
  · exact absurd rfl hb2

private theorem nOf_spec (g : LocalGL3 v) :
    gl3Entry v (g * nOf v g) 2 2 ≠ 0 ∧
      (∀ j, Valued.v (gl3Entry v (g * nOf v g) 2 j) ≤ Valued.v (gl3Entry v (g * nOf v g) 2 2)) ∧
      colMinor v (g * nOf v g) 1 ≠ 0 ∧
      Valued.v (colMinor v (g * nOf v g) 0) ≤ Valued.v (colMinor v (g * nOf v g) 1) := by
  obtain ⟨h22, hrow⟩ := stage1_spec v g
  set h := g * n1Of v g with hh
  obtain ⟨m0, m1, c2, c0, c1⟩ := colMinor_mul_upperUnipotent3_x v h (epsOf v g)
  rw [mul_nOf_eq, ← hh]
  refine ⟨by rw [c2]; exact h22, fun j => ?_, ?_, ?_⟩
  · rw [c2]
    fin_cases j
    · show Valued.v (gl3Entry v (h * upperUnipotent3 (epsOf v g) 0 0) 2 0) ≤ _
      rw [c0]; exact hrow 0
    · show Valued.v (gl3Entry v (h * upperUnipotent3 (epsOf v g) 0 0) 2 1) ≤ _
      rw [c1]
      refine (Valuation.map_add _ _ _).trans (max_le (hrow 1) ?_)
      rw [Valuation.map_mul]
      refine mul_le_of_le_one_of_le ?_ (hrow 0)
      unfold epsOf; split_ifs <;> simp
    · show Valued.v (gl3Entry v (h * upperUnipotent3 (epsOf v g) 0 0) 2 2) ≤ _
      rw [c2]
  · rw [m1]
    unfold epsOf
    split_ifs with hle
    · rw [zero_mul, add_zero]
      intro hz
      rcases exists_colMinor_ne_zero v h h22 with h0 | h1
      · rw [hz, map_zero] at hle
        exact h0 ((Valuation.zero_iff _).mp (le_antisymm hle zero_le'))
      · exact h1 hz
    · rw [one_mul]
      push Not at hle
      intro hz
      have := Valuation.map_add_eq_of_lt_right _ hle
      rw [hz, map_zero] at this
      exact (lt_of_le_of_lt zero_le' hle).ne this
  · rw [m0, m1]
    unfold epsOf
    split_ifs with hle
    · rwa [zero_mul, add_zero]
    · push Not at hle
      rw [one_mul, Valuation.map_add_eq_of_lt_right _ hle]

private theorem
    mul_nOf_mul_antidiagonal3_mem_cellCutoff
    (g : LocalGL3 v) : g * nOf v g * antidiagonal3 v ∈ cellCutoff v := by
  obtain ⟨h22, hrow, hμ, hμle⟩ := nOf_spec v g
  exact mul_antidiagonal3_mem_cellCutoff v _ h22 hrow hμ hμle

private theorem rowVal_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    rowVal v (upperUnipotent3 x y z * g) = rowVal v g := by
  funext j
  simp only [rowVal, gl3Entry_upperUnipotent3_mul_two]

private theorem rowArgmax_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    rowArgmax v (upperUnipotent3 x y z * g) = rowArgmax v g := by
  simp only [rowArgmax, rowVal_upperUnipotent3_mul]

private theorem rowArgmax_diagonal3_mul (t : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    rowArgmax v (diagonal3 v t * g) = rowArgmax v g := by
  have ht : 0 < Valued.v (t 2 : v.adicCompletion ℚ) :=
    lt_of_le_of_ne zero_le' ((Valuation.ne_zero_iff _).mpr (t 2).ne_zero).symm
  have h : rowVal v (diagonal3 v t * g) = fun j => OrderIso.mulLeft₀ _ ht (rowVal v g j) := by
    funext j
    simp only [rowVal, gl3Entry_diagonal3_mul, Valuation.map_mul]
    rfl
  rw [rowArgmax, rowArgmax, h]
  exact T0Cover.argmaxIn_comp_strictMono _ _ (OrderIso.strictMono _)

private theorem n1Of_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    n1Of v (upperUnipotent3 x y z * g) = n1Of v g := by
  simp only [n1Of, rowArgmax_upperUnipotent3_mul]

private theorem n1Of_diagonal3_mul (t : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    n1Of v (diagonal3 v t * g) = n1Of v g := by
  simp only [n1Of, rowArgmax_diagonal3_mul]

private theorem colMinor_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (h : LocalGL3 v) (j : Fin 3) :
    colMinor v (upperUnipotent3 x y z * h) j = colMinor v h j := by
  simp only [colMinor, gl3Entry_upperUnipotent3_mul_one, gl3Entry_upperUnipotent3_mul_two]
  ring

private theorem colMinor_diagonal3_mul (t : Fin 3 → (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v) (j : Fin 3) :
    colMinor v (diagonal3 v t * h) j = (t 1 : v.adicCompletion ℚ) * (t 2 : v.adicCompletion ℚ) * colMinor v h j := by
  simp only [colMinor, gl3Entry_diagonal3_mul]
  ring

private theorem epsOf_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    epsOf v (upperUnipotent3 x y z * g) = epsOf v g := by
  simp only [epsOf, n1Of_upperUnipotent3_mul, mul_assoc, colMinor_upperUnipotent3_mul]

private theorem epsOf_diagonal3_mul (t : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    epsOf v (diagonal3 v t * g) = epsOf v g := by
  have ht : 0 < Valued.v (t 1 : v.adicCompletion ℚ) * Valued.v (t 2 : v.adicCompletion ℚ) := by
    rw [← Valuation.map_mul]
    exact lt_of_le_of_ne zero_le' ((Valuation.ne_zero_iff _).mpr (mul_ne_zero (t 1).ne_zero (t 2).ne_zero)).symm
  simp only [epsOf, n1Of_diagonal3_mul, mul_assoc, colMinor_diagonal3_mul, Valuation.map_mul]
  simp only [← mul_assoc, mul_le_mul_iff_right₀ ht]

private theorem nOf_upperUnipotent3_mul (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    nOf v (upperUnipotent3 x y z * g) = nOf v g := by
  simp only [nOf, epsOf_upperUnipotent3_mul, rowArgmax_upperUnipotent3_mul]

private theorem nOf_diagonal3_mul (t : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    nOf v (diagonal3 v t * g) = nOf v g := by
  simp only [nOf, epsOf_diagonal3_mul, rowArgmax_diagonal3_mul]

private theorem eventually_rowArgmax_eq (g₀ : LocalGL3 v) : ∀ᶠ g in 𝓝 g₀, rowArgmax v g = rowArgmax v g₀ := by
  obtain ⟨a₀, ha₀⟩ := rowArgmax_nonempty v g₀
  have hmax : ∀ j, rowVal v g₀ j ≤ rowVal v g₀ a₀ := (mem_rowArgmax_iff v g₀ a₀).mp ha₀
  have hpos : 0 < rowVal v g₀ a₀ := rowVal_pos_of_mem_rowArgmax v g₀ ha₀
  have hne : gl3Entry v g₀ 2 a₀ ≠ 0 := (Valuation.ne_zero_iff _).mp hpos.ne'
  refine T0Cover.eventually_argmaxIn_eq Finset.univ (fun j g => rowVal v g j) g₀ (Finset.mem_univ a₀)
    (fun j _ => hmax j) (fun j _ => ?_)
  by_cases hj : gl3Entry v g₀ 2 j = 0
  · right
    refine ⟨?_, ?_⟩
    · show Valued.v (gl3Entry v g₀ 2 j) < rowVal v g₀ a₀
      rw [hj, map_zero]; exact hpos
    · have ht : Tendsto (fun g => gl3Entry v g 2 j) (𝓝 g₀) (𝓝 0) := by
        simpa [hj] using (continuous_gl3Entry v 2 j).tendsto g₀
      exact ht.eventually (eventually_valued_lt v hne)
  · left
    exact ((continuous_gl3Entry v 2 j).tendsto g₀).eventually (eventually_valued_eq v hj)

private theorem eventually_n1Of_eq (g₀ : LocalGL3 v) : ∀ᶠ g in 𝓝 g₀, n1Of v g = n1Of v g₀ :=
  (eventually_rowArgmax_eq v g₀).mono fun _ h => by simp only [n1Of, h]

private theorem eventually_epsOf_eq (g₀ : LocalGL3 v) : ∀ᶠ g in 𝓝 g₀, epsOf v g = epsOf v g₀ := by

  set n₁ := n1Of v g₀ with hn₁
  have hcont : ∀ j, Continuous fun g : LocalGL3 v => colMinor v (g * n₁) j := fun j =>
    (((continuous_gl3Entry v 1 j).comp (continuous_mul_const n₁)).mul
      ((continuous_gl3Entry v 2 2).comp (continuous_mul_const n₁))).sub
      (((continuous_gl3Entry v 1 2).comp (continuous_mul_const n₁)).mul
        ((continuous_gl3Entry v 2 j).comp (continuous_mul_const n₁)))
  obtain ⟨h22, -⟩ := stage1_spec v g₀
  have hsome := exists_colMinor_ne_zero v (g₀ * n₁) h22

  have hcmp : ∀ᶠ g in 𝓝 g₀, (Valued.v (colMinor v (g * n₁) 0) ≤ Valued.v (colMinor v (g * n₁) 1) ↔
      Valued.v (colMinor v (g₀ * n₁) 0) ≤ Valued.v (colMinor v (g₀ * n₁) 1)) := by
    by_cases h0 : colMinor v (g₀ * n₁) 0 = 0
    · have h1 : colMinor v (g₀ * n₁) 1 ≠ 0 := hsome.resolve_left (fun h => h h0)
      have ev1 := ((hcont 1).tendsto g₀).eventually (eventually_valued_eq v h1)
      have ht : Tendsto (fun g => colMinor v (g * n₁) 0) (𝓝 g₀) (𝓝 0) := by
        simpa [h0] using (hcont 0).tendsto g₀
      have ev0 := ht.eventually (eventually_valued_lt v h1)
      filter_upwards [ev0, ev1] with g hg0 hg1
      rw [hg1, h0, map_zero]
      exact iff_of_true hg0.le zero_le'
    · by_cases h1 : colMinor v (g₀ * n₁) 1 = 0
      · have ev0 := ((hcont 0).tendsto g₀).eventually (eventually_valued_eq v h0)
        have ht : Tendsto (fun g => colMinor v (g * n₁) 1) (𝓝 g₀) (𝓝 0) := by
          simpa [h1] using (hcont 1).tendsto g₀
        have ev1 := ht.eventually (eventually_valued_lt v h0)
        filter_upwards [ev0, ev1] with g hg0 hg1
        rw [hg0, h1, map_zero]
        have hp : 0 < Valued.v (colMinor v (g₀ * n₁) 0) :=
          lt_of_le_of_ne zero_le' ((Valuation.ne_zero_iff _).mpr h0).symm
        exact iff_of_false (not_le.mpr hg1) (not_le.mpr hp)
      · have ev0 := ((hcont 0).tendsto g₀).eventually (eventually_valued_eq v h0)
        have ev1 := ((hcont 1).tendsto g₀).eventually (eventually_valued_eq v h1)
        filter_upwards [ev0, ev1] with g hg0 hg1
        rw [hg0, hg1]
  filter_upwards [hcmp, eventually_n1Of_eq v g₀] with g hg hn
  unfold epsOf
  rw [hn, ← hn₁]
  by_cases hle : Valued.v (colMinor v (g₀ * n₁) 0) ≤ Valued.v (colMinor v (g₀ * n₁) 1)
  · rw [if_pos hle, if_pos (hg.mpr hle)]
  · rw [if_neg hle, if_neg (fun h => hle (hg.mp h))]

private theorem eventually_nOf_eq (g₀ : LocalGL3 v) : ∀ᶠ g in 𝓝 g₀, nOf v g = nOf v g₀ := by
  filter_upwards [eventually_epsOf_eq v g₀, eventually_rowArgmax_eq v g₀] with g he hA
  simp only [nOf, he, hA]

private theorem isLocallyConstant_nOf : IsLocallyConstant (nOf v) :=
  (IsLocallyConstant.iff_eventually_eq _).mpr (eventually_nOf_eq v)

private theorem isClopen_fiber_nOf (n : LocalGL3 v) : IsClopen (nOf v ⁻¹' {n}) :=
  (isLocallyConstant_nOf v).isClopen_fiber n

private theorem upperUnipotent3_mul_mem_fiber_nOf_iff (n : LocalGL3 v) (x y z : v.adicCompletion ℚ) (g : LocalGL3 v) :
    upperUnipotent3 x y z * g ∈ nOf v ⁻¹' {n} ↔ g ∈ nOf v ⁻¹' {n} := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff, nOf_upperUnipotent3_mul]

private theorem diagonal3_mul_mem_fiber_nOf_iff (n : LocalGL3 v) (t : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v) :
    diagonal3 v t * g ∈ nOf v ⁻¹' {n} ↔ g ∈ nOf v ⁻¹' {n} := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff, nOf_diagonal3_mul]

private theorem nOf_mem_range (g : LocalGL3 v) :
    ∃ ε y z : v.adicCompletion ℚ, (ε = 0 ∨ ε = 1) ∧ ((y = 0 ∧ z = 0) ∨ (y = 1 ∧ z = 0) ∨ (y = 0 ∧ z = 1)) ∧
      nOf v g = upperUnipotent3 ε y z := by
  refine ⟨epsOf v g, (yzOf v (stage1Col (rowArgmax v g))).1, (yzOf v (stage1Col (rowArgmax v g))).2, ?_, ?_, rfl⟩
  · unfold epsOf; split_ifs <;> simp
  · unfold yzOf; split_ifs <;> simp

end T0Aux

end LanglandsTunnell.CubicInduction

end

end

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum.LanglandsTunnell.CubicInduction"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 upperUnipotent3_inv_eq unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellCutoff_subset_bigCell3 cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul jacquetWhittaker3 diagonal3 diagonal3_coe principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 gl3Det_antidiagonal3 antidiagonal3_mem_cellCutoff cellSection_antidiagonal3_ne_zero eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det gl3Det_eq_bottom_expansion exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3 properSpace_adicCompletion_rat isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace T0bAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Entries

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 0 = 1 ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 1 = x ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 2 2 = z ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 1 0 = 0 ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 1 1 = 1 ∧
      gl3Entry v (antidiagonal3 v * upperUnipotent3 x y z) 1 2 = y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gl3Entry, Units.val_mul, antidiagonal3_coe, upperUnipotent3_coe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem cornerEntry_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    cornerEntry v (antidiagonal3 v * upperUnipotent3 x y z) = 1 :=
  (gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z).1

private theorem lowerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    lowerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -1 := by
  obtain ⟨h20, h21, -, h10, h11, -⟩ := gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z
  simp [lowerMinor, h20, h21, h10, h11]

private theorem outerMinor_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    outerMinor v (antidiagonal3 v * upperUnipotent3 x y z) = -y := by
  obtain ⟨h20, -, h22, h10, -, h12⟩ := gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z
  simp [outerMinor, h20, h22, h10, h12]

private theorem gl3Det_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    gl3Det v (antidiagonal3 v * upperUnipotent3 x y z) = -1 := by
  simp [gl3Det, Units.val_mul, Matrix.det_mul, antidiagonal3_coe, upperUnipotent3_coe, Matrix.det_fin_three]

private theorem cellRatio_antidiagonal3_mul_upperUnipotent3 (x y z : v.adicCompletion ℚ) :
    cellRatio v (antidiagonal3 v * upperUnipotent3 x y z) = ![x, z, y] := by
  obtain ⟨h20, h21, h22, -, -, -⟩ := gl3Entry_antidiagonal3_mul_upperUnipotent3 v x y z
  have hc := cornerEntry_antidiagonal3_mul_upperUnipotent3 v x y z
  have hl := lowerMinor_antidiagonal3_mul_upperUnipotent3 v x y z
  have ho := outerMinor_antidiagonal3_mul_upperUnipotent3 v x y z
  ext i
  fin_cases i <;> simp [cellRatio, hc, hl, ho, h21, h22, neg_div_neg_eq]

private theorem cellValue_antidiagonal3_mul_upperUnipotent3 (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (x y z : v.adicCompletion ℚ) :
    cellValue v χ (antidiagonal3 v * upperUnipotent3 x y z) = cellValue v χ (antidiagonal3 v) := by
  simp only [cellValue, gl3Det_antidiagonal3_mul_upperUnipotent3, lowerMinor_antidiagonal3_mul_upperUnipotent3,
    cornerEntry_antidiagonal3_mul_upperUnipotent3, gl3Det_antidiagonal3, lowerMinor_antidiagonal3,
    cornerEntry_antidiagonal3]

end Entries

end LanglandsTunnell.CubicInduction.T0bAux

p2m_open "MeasureTheory IsDedekindDomain NumberField NumberField.StandardAddChar LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum.LanglandsTunnell.CubicInduction Filter Topology"

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 upperUnipotent3_inv_eq unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellCutoff_subset_bigCell3 cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul jacquetWhittaker3 diagonal3 diagonal3_coe principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 gl3Det_antidiagonal3 antidiagonal3_mem_cellCutoff cellSection_antidiagonal3_ne_zero eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det gl3Det_eq_bottom_expansion exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3 properSpace_adicCompletion_rat isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace T0bAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

section Pieces

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem gl3Entry_upperUnipotent3 (x y z : v.adicCompletion ℚ) (i j : Fin 3) :
    gl3Entry v (upperUnipotent3 x y z) i j = !![(1 : v.adicCompletion ℚ), x, z; 0, 1, y; 0, 0, 1] i j :=
  rfl

private theorem continuous_upperUnipotent3 :
    Continuous (fun q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      (upperUnipotent3 q.1 q.2.1 q.2.2 : LocalGL3 v)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [upperUnipotent3] <;> fun_prop

private theorem exists_eq_upperUnipotent3_mul_diagonal3 (g : LocalGL3 v)
    (h₁₀ : gl3Entry v g 1 0 = 0) (h₂₀ : gl3Entry v g 2 0 = 0) (h₂₁ : gl3Entry v g 2 1 = 0) :
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 x y z * diagonal3 v a := by
  have hdet : gl3Det v g = gl3Entry v g 0 0 * gl3Entry v g 1 1 * gl3Entry v g 2 2 := by
    rw [gl3Det_eq_bottom_expansion, h₁₀, h₂₀, h₂₁]
    ring
  have h₀ : gl3Entry v g 0 0 ≠ 0 := fun h => gl3Det_ne_zero v g (by rw [hdet, h, zero_mul, zero_mul])
  have h₁ : gl3Entry v g 1 1 ≠ 0 := fun h => gl3Det_ne_zero v g (by rw [hdet, h, mul_zero, zero_mul])
  have h₂ : gl3Entry v g 2 2 ≠ 0 := fun h => gl3Det_ne_zero v g (by rw [hdet, h, mul_zero])
  have e₁₀ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 0 = 0 := h₁₀
  have e₂₀ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 0 = 0 := h₂₀
  have e₂₁ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 1 = 0 := h₂₁
  have e₁ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 1 1 ≠ 0 := h₁
  have e₂ : (g : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) 2 2 ≠ 0 := h₂
  refine ⟨gl3Entry v g 0 1 / gl3Entry v g 1 1, gl3Entry v g 1 2 / gl3Entry v g 2 2,
    gl3Entry v g 0 2 / gl3Entry v g 2 2, ![Units.mk0 _ h₀, Units.mk0 _ h₁, Units.mk0 _ h₂], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gl3Entry, Matrix.mul_diagonal, e₁₀, e₂₀, e₂₁, e₁, e₂]

private theorem antidiagonal3_mul_antidiagonal3 : antidiagonal3 v * antidiagonal3 v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiagonal3_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

private theorem antidiagonal3_inv : (antidiagonal3 v)⁻¹ = antidiagonal3 v :=
  inv_eq_of_mul_eq_one_right (antidiagonal3_mul_antidiagonal3 v)

private def cellPoint (r : Fin 3 → v.adicCompletion ℚ) : LocalGL3 v :=
  antidiagonal3 v * upperUnipotent3 (r 0) (r 2) (r 1)

private theorem cellRatio_cellPoint (r : Fin 3 → v.adicCompletion ℚ) : cellRatio v (cellPoint v r) = r := by
  rw [cellPoint, cellRatio_antidiagonal3_mul_upperUnipotent3]
  ext i
  fin_cases i <;> rfl

private theorem cellValue_cellPoint (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (r : Fin 3 → v.adicCompletion ℚ) : cellValue v χ (cellPoint v r) = cellValue v χ (antidiagonal3 v) := by
  rw [cellPoint, cellValue_antidiagonal3_mul_upperUnipotent3]

private theorem cellPoint_mem_bigCell3 (r : Fin 3 → v.adicCompletion ℚ) : cellPoint v r ∈ bigCell3 v := by
  refine (mem_bigCell3_iff v _).mpr ⟨?_, ?_⟩
  · rw [cellPoint, cornerEntry_antidiagonal3_mul_upperUnipotent3]
    exact one_ne_zero
  · rw [cellPoint, lowerMinor_antidiagonal3_mul_upperUnipotent3]
    exact neg_ne_zero.mpr one_ne_zero

private theorem continuous_cellPoint : Continuous (cellPoint v) := by
  have h1 : Continuous fun r : Fin 3 → v.adicCompletion ℚ => (r 0, r 2, r 1) :=
    (continuous_apply 0).prodMk ((continuous_apply 2).prodMk (continuous_apply 1))
  show Continuous fun r : Fin 3 → v.adicCompletion ℚ => antidiagonal3 v * upperUnipotent3 (r 0) (r 2) (r 1)
  exact continuous_const.mul ((continuous_upperUnipotent3 v).comp h1)

private theorem exists_eq_upperUnipotent3_mul_diagonal3_mul_cellPoint (g : LocalGL3 v) (hg : g ∈ bigCell3 v) :
    ∃ (x y z : v.adicCompletion ℚ) (a : Fin 3 → (v.adicCompletion ℚ)ˣ),
      g = upperUnipotent3 x y z * (diagonal3 v a * cellPoint v (cellRatio v g)) := by
  obtain ⟨hc, hl⟩ := (mem_bigCell3_iff v g).mp hg
  have hc' : gl3Entry v g 2 0 ≠ 0 := hc
  have hl' : gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0 ≠ 0 := hl
  have hr0 : cellRatio v g 0 = gl3Entry v g 2 1 / gl3Entry v g 2 0 := rfl
  have hr1 : cellRatio v g 1 = gl3Entry v g 2 2 / gl3Entry v g 2 0 := rfl
  have hr2 : cellRatio v g 2 = (gl3Entry v g 1 0 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 0) /
      (gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0) := rfl
  have hinv : (cellPoint v (cellRatio v g))⁻¹ =
      upperUnipotent3 (-cellRatio v g 0) (-cellRatio v g 2) (cellRatio v g 0 * cellRatio v g 2 - cellRatio v g 1) *
        antidiagonal3 v := by
    rw [cellPoint, mul_inv_rev, upperUnipotent3_inv_eq, antidiagonal3_inv]
  have e0 : cellRatio v g 0 * gl3Entry v g 2 0 = gl3Entry v g 2 1 := by
    rw [hr0]
    exact div_mul_cancel₀ _ hc'
  have e1 : cellRatio v g 1 * gl3Entry v g 2 0 = gl3Entry v g 2 2 := by
    rw [hr1]
    exact div_mul_cancel₀ _ hc'
  have e2 : cellRatio v g 2 * (gl3Entry v g 1 0 * gl3Entry v g 2 1 - gl3Entry v g 1 1 * gl3Entry v g 2 0) =
      gl3Entry v g 1 0 * gl3Entry v g 2 2 - gl3Entry v g 1 2 * gl3Entry v g 2 0 := by
    rw [hr2]
    exact div_mul_cancel₀ _ hl'
  set h : LocalGL3 v := g * (cellPoint v (cellRatio v g))⁻¹ with hh
  have h10 : gl3Entry v h 1 0 = 0 := by
    rw [hh, hinv, ← mul_assoc, T0Aux.gl3Entry_mul_antidiagonal3_zero, T0Aux.gl3Entry_mul_upperUnipotent3_two]
    refine (mul_eq_zero.mp ?_).resolve_left hc'
    linear_combination (gl3Entry v g 1 0 * cellRatio v g 2) * e0 - gl3Entry v g 1 0 * e1 + e2
  have h20 : gl3Entry v h 2 0 = 0 := by
    rw [hh, hinv, ← mul_assoc, T0Aux.gl3Entry_mul_antidiagonal3_zero, T0Aux.gl3Entry_mul_upperUnipotent3_two]
    linear_combination cellRatio v g 2 * e0 - e1
  have h21 : gl3Entry v h 2 1 = 0 := by
    rw [hh, hinv, ← mul_assoc, T0Aux.gl3Entry_mul_antidiagonal3_one, T0Aux.gl3Entry_mul_upperUnipotent3_one]
    linear_combination (-1 : v.adicCompletion ℚ) * e0
  obtain ⟨x, y, z, a, hxyza⟩ := exists_eq_upperUnipotent3_mul_diagonal3 v h h10 h20 h21
  refine ⟨x, y, z, a, ?_⟩
  rw [← mul_assoc, ← hxyza, hh, inv_mul_cancel_right]

private theorem isCompact_setOf_valued_le_one : IsCompact {x : v.adicCompletion ℚ | Valued.v x ≤ 1} := by
  have h := isCompact_setOf_valued_sub_le v 0 0
  simpa [WithZero.exp_zero] using h

private theorem indicator_mem_principalSeries3_of_isClopen (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (S : Set (LocalGL3 v)) (hS : IsClopen S)
    (hSN : ∀ (x y z : v.adicCompletion ℚ) (g : LocalGL3 v), upperUnipotent3 x y z * g ∈ S ↔ g ∈ S)
    (hSD : ∀ (a : Fin 3 → (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v), diagonal3 v a * g ∈ S ↔ g ∈ S)
    (F : LocalGL3 v → ℂ) (hF : F ∈ principalSeries3 v χ) : S.indicator F ∈ principalSeries3 v χ := by
  obtain ⟨hlc, hN, hD⟩ := mem_principalSeries3_iff.mp hF
  refine mem_principalSeries3_iff.mpr ⟨?_, fun x y z g => ?_, fun a g => ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g => ?_
    by_cases hg : g ∈ S
    · filter_upwards [hS.isOpen.mem_nhds hg, (IsLocallyConstant.iff_eventually_eq _).mp hlc g] with h hh hfh
      rw [Set.indicator_of_mem hh, Set.indicator_of_mem hg, hfh]
    · filter_upwards [hS.compl.isOpen.mem_nhds hg] with h hh
      rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hg]
  · by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem ((hSN x y z g).mpr hg), Set.indicator_of_mem hg, hN]
    · rw [Set.indicator_of_notMem (fun h => hg ((hSN x y z g).mp h)), Set.indicator_of_notMem hg]
  · by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem ((hSD a g).mpr hg), Set.indicator_of_mem hg, hD]
    · rw [Set.indicator_of_notMem (fun h => hg ((hSD a g).mp h)), Set.indicator_of_notMem hg, mul_zero]

private theorem exists_eq_cellSectionOf_of_mem_principalSeries3_of_forall_mem_cellCutoff
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (t : LocalGL3 v → ℂ) (ht : t ∈ principalSeries3 v χ)
    (hsupp : ∀ g : LocalGL3 v, t g ≠ 0 → g ∈ cellCutoff v) :
    ∃ Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ, (IsLocallyConstant Φ ∧ HasCompactSupport Φ) ∧
      t = cellSectionOf v χ Φ := by
  obtain ⟨hlc, hN, hD⟩ := mem_principalSeries3_iff.mp ht
  have hC : cellValue v χ (antidiagonal3 v) ≠ 0 := by
    have h := cellSection_antidiagonal3_ne_zero v χ
    rwa [cellSection, Set.indicator_of_mem (antidiagonal3_mem_cellCutoff v)] at h
  refine ⟨fun r => (cellValue v χ (antidiagonal3 v))⁻¹ * t (cellPoint v r), ⟨?_, ?_⟩, ?_⟩
  · refine (IsLocallyConstant.iff_eventually_eq _).mpr fun r => ?_
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (hlc.comp_continuous (continuous_cellPoint v)) r]
      with r' hr'
    simp only [Function.comp_apply] at hr'
    rw [hr']
  · refine HasCompactSupport.intro (isCompact_univ_pi fun _ => isCompact_setOf_valued_le_one v) fun r hr => ?_
    rw [mul_eq_zero]
    right
    by_contra hne
    have hmem := hsupp _ hne
    simp only [cellCutoff, Set.mem_setOf_eq] at hmem
    obtain ⟨-, -, hrat⟩ := hmem
    rw [cellRatio_cellPoint] at hrat
    exact hr (Set.mem_univ_pi.mpr hrat)
  · funext g
    by_cases hg : g ∈ bigCell3 v
    · obtain ⟨x, y, z, a, hfac⟩ := exists_eq_upperUnipotent3_mul_diagonal3_mul_cellPoint v g hg
      rw [hfac, hN, hD, cellSectionOf_upperUnipotent3_mul, cellSectionOf_diagonal3_mul,
        cellSectionOf_apply_of_mem v χ _ (cellPoint_mem_bigCell3 v _), cellValue_cellPoint, cellRatio_cellPoint,
        mul_inv_cancel_left₀ hC]
    · rw [cellSectionOf_apply_of_notMem v χ _ hg]
      by_contra hne
      exact hg (cellCutoff_subset_bigCell3 v (hsupp g hne))

end Pieces

section Decomposition

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def xs (j : Fin 6) : v.adicCompletion ℚ := if (j : ℕ) < 3 then 0 else 1
private def ys (j : Fin 6) : v.adicCompletion ℚ := if (j : ℕ) % 3 = 1 then 1 else 0
private def zs (j : Fin 6) : v.adicCompletion ℚ := if (j : ℕ) % 3 = 2 then 1 else 0

private def nList (j : Fin 6) : LocalGL3 v := upperUnipotent3 (xs v j) (ys v j) (zs v j)

private theorem upperUnipotent3_injective {x y z x' y' z' : v.adicCompletion ℚ}
    (h : (upperUnipotent3 x y z : LocalGL3 v) = upperUnipotent3 x' y' z') : x = x' ∧ y = y' ∧ z = z' := by
  have h01 := congrArg (fun g : LocalGL3 v => gl3Entry v g 0 1) h
  have h12 := congrArg (fun g : LocalGL3 v => gl3Entry v g 1 2) h
  have h02 := congrArg (fun g : LocalGL3 v => gl3Entry v g 0 2) h
  simp only [gl3Entry_upperUnipotent3] at h01 h12 h02
  simp at h01 h12 h02
  exact ⟨h01, h12, h02⟩

private theorem nList_injective : Function.Injective (nList v) := by
  intro j k hjk
  obtain ⟨h1, h2, h3⟩ := upperUnipotent3_injective v hjk
  fin_cases j <;> fin_cases k <;> simp_all [xs, ys, zs]

private theorem exists_nOf_eq_nList (g : LocalGL3 v) : ∃ j : Fin 6, T0Aux.nOf v g = nList v j := by
  obtain ⟨ε, y, z, hε, hyz, hg⟩ := T0Aux.nOf_mem_range v g
  rw [hg]
  rcases hε with rfl | rfl <;> rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨0, by simp [nList, xs, ys, zs]⟩
  · exact ⟨1, by simp [nList, xs, ys, zs]⟩
  · exact ⟨2, by simp [nList, xs, ys, zs]⟩
  · exact ⟨3, by simp [nList, xs, ys, zs]⟩
  · exact ⟨4, by simp [nList, xs, ys, zs]⟩
  · exact ⟨5, by simp [nList, xs, ys, zs]⟩

private theorem exists_decomposition (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : LocalGL3 v → ℂ) (hf : f ∈ principalSeries3 v χ) :
    ∃ (n : ℕ) (κ : Fin n → ℂ) (x y z : Fin n → v.adicCompletion ℚ)
      (Φ : Fin n → (Fin 3 → v.adicCompletion ℚ) → ℂ),
      (∀ j, IsLocallyConstant (Φ j) ∧ HasCompactSupport (Φ j)) ∧
      f = ∑ j, κ j • gl3AmbientRightTranslate (R := ℂ)
        (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v) (cellSectionOf v χ (Φ j)) := by
  have hpiece : ∀ j : Fin 6, (T0Aux.nOf v ⁻¹' {nList v j}).indicator f ∈ principalSeries3 v χ := fun j =>
    indicator_mem_principalSeries3_of_isClopen v χ _ (T0Aux.isClopen_fiber_nOf v _)
      (T0Aux.upperUnipotent3_mul_mem_fiber_nOf_iff v _) (T0Aux.diagonal3_mul_mem_fiber_nOf_iff v _) f hf
  have htr : ∀ j : Fin 6, gl3AmbientRightTranslate (R := ℂ) (nList v j * antidiagonal3 v)⁻¹
      ((T0Aux.nOf v ⁻¹' {nList v j}).indicator f) ∈ principalSeries3 v χ :=
    fun j => rightTranslate_mem_principalSeries3 (hpiece j) _
  have hsupp : ∀ j : Fin 6, ∀ g : LocalGL3 v, gl3AmbientRightTranslate (R := ℂ) (nList v j * antidiagonal3 v)⁻¹
      ((T0Aux.nOf v ⁻¹' {nList v j}).indicator f) g ≠ 0 → g ∈ cellCutoff v := by
    intro j g hg
    rw [gl3AmbientRightTranslate_apply] at hg
    have hmem : g * (nList v j * antidiagonal3 v)⁻¹ ∈ T0Aux.nOf v ⁻¹' {nList v j} := by
      by_contra h
      exact hg (Set.indicator_of_notMem h f)
    have h1 : T0Aux.nOf v (g * (nList v j * antidiagonal3 v)⁻¹) = nList v j := hmem
    have h2 := T0Aux.mul_nOf_mul_antidiagonal3_mem_cellCutoff v (g * (nList v j * antidiagonal3 v)⁻¹)
    rw [h1, mul_assoc (g * (nList v j * antidiagonal3 v)⁻¹) (nList v j) (antidiagonal3 v),
      inv_mul_cancel_right] at h2
    exact h2
  choose Φ hΦ hΦeq using fun j : Fin 6 =>
    exists_eq_cellSectionOf_of_mem_principalSeries3_of_forall_mem_cellCutoff v χ _ (htr j) (hsupp j)
  refine ⟨6, fun _ => 1, xs v, ys v, zs v, Φ, hΦ, ?_⟩
  funext g
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, one_smul, gl3AmbientRightTranslate_apply]
  have hterm : ∀ j : Fin 6, cellSectionOf v χ (Φ j)
      (g * (upperUnipotent3 (xs v j) (ys v j) (zs v j) * antidiagonal3 v)) =
        (T0Aux.nOf v ⁻¹' {nList v j}).indicator f g := by
    intro j
    have h := congrFun (hΦeq j) (g * (nList v j * antidiagonal3 v))
    rw [gl3AmbientRightTranslate_apply, mul_inv_cancel_right] at h
    exact h.symm
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  obtain ⟨j₀, hj₀⟩ := exists_nOf_eq_nList v g
  rw [Finset.sum_eq_single j₀]
  · exact (Set.indicator_of_mem (show g ∈ T0Aux.nOf v ⁻¹' {nList v j₀} from hj₀) f).symm
  · intro j _ hj
    exact Set.indicator_of_notMem
      (show g ∉ T0Aux.nOf v ⁻¹' {nList v j} from fun h => hj (nList_injective v (hj₀.symm.trans h)).symm) f
  · intro h
    exact absurd (Finset.mem_univ j₀) h

end Decomposition

section Substitution

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def shiftMap (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ →
      v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  fun p => (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + p.1 * q.2.1)

private def shiftMapInv (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ →
      v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ :=
  fun p => (p.1 - q.1, p.2.1 - q.2.1, p.2.2 - q.2.2 - (p.1 - q.1) * q.2.1)

private theorem shiftMapInv_shiftMap (q p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    shiftMapInv v q (shiftMap v q p) = p := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [shiftMap, shiftMapInv] <;> ring

private theorem shiftMap_shiftMapInv (q p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    shiftMap v q (shiftMapInv v q p) = p := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [shiftMap, shiftMapInv] <;> ring

private theorem continuous_shiftMap (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    Continuous (shiftMap v q) := by
  unfold shiftMap
  fun_prop

private theorem continuous_shiftMapInv (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    Continuous (shiftMapInv v q) := by
  unfold shiftMapInv
  fun_prop

private def shiftHomeomorph (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) ≃ₜ
      (v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) where
  toFun := shiftMap v q
  invFun := shiftMapInv v q
  left_inv := shiftMapInv_shiftMap v q
  right_inv := shiftMap_shiftMapInv v q
  continuous_toFun := continuous_shiftMap v q
  continuous_invFun := continuous_shiftMapInv v q

private theorem isAddHaarMeasure_selfDualHaarAt :
    letI := localBorel ℚ v
    (selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  unfold selfDualHaarAt
  refine Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos ?_).ne'
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot))

private theorem measurePreserving_shiftMap (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    letI := localBorel ℚ v
    MeasurePreserving (shiftMap v q) (jacquetHaar3 v) (jacquetHaar3 v) := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion_rat v
  haveI : (selfDualHaarAt ℚ v).IsAddHaarMeasure := isAddHaarMeasure_selfDualHaarAt v
  haveI : SigmaFinite (selfDualHaarAt ℚ v) := inferInstance
  have hB : MeasurePreserving
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ => (p.1, (p.2.1, p.2.2 + p.1 * q.2.1)))
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) := by
    refine (MeasurePreserving.id (selfDualHaarAt ℚ v)).skew_product
      (g := fun (a : v.adicCompletion ℚ) (bc : v.adicCompletion ℚ × v.adicCompletion ℚ) =>
        (bc.1, bc.2 + a * q.2.1))
      ?_ ?_
    · exact measurable_snd.fst.prodMk (measurable_snd.snd.add (measurable_fst.mul_const _))
    · refine Filter.Eventually.of_forall fun a => ?_
      exact ((MeasurePreserving.id (selfDualHaarAt ℚ v)).prod
        (measurePreserving_add_right (selfDualHaarAt ℚ v) (a * q.2.1))).map_eq
  have hA : MeasurePreserving
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (p.1 + q.1, (p.2.1 + q.2.1, p.2.2 + q.2.2)))
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v)))
      ((selfDualHaarAt ℚ v).prod ((selfDualHaarAt ℚ v).prod (selfDualHaarAt ℚ v))) :=
    (measurePreserving_add_right (selfDualHaarAt ℚ v) q.1).prod
      ((measurePreserving_add_right (selfDualHaarAt ℚ v) q.2.1).prod
        (measurePreserving_add_right (selfDualHaarAt ℚ v) q.2.2))
  have hT : shiftMap v q =
      (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
        (p.1 + q.1, (p.2.1 + q.2.1, p.2.2 + q.2.2))) ∘
        (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
          (p.1, (p.2.1, p.2.2 + p.1 * q.2.1))) := by
    funext p
    refine Prod.ext rfl (Prod.ext rfl ?_)
    show p.2.2 + q.2.2 + p.1 * q.2.1 = p.2.2 + p.1 * q.2.1 + q.2.2
    ring
  rw [hT]
  exact hA.comp hB

private theorem jacquetTruncated3_rightTranslate_upperUnipotent3 (c : ℤ)
    (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) (hq : q ∈ unipotentBall3 v c)
    (u : LocalGL3 v → ℂ) :
    jacquetTruncated3 v c (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 q.1 q.2.1 q.2.2) u) =
      psiLocal ℚ v (q.1 + q.2.1) * jacquetTruncated3 v c u := by
  letI := localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := borelSpace_localBorel ℚ v
  haveI : ProperSpace (v.adicCompletion ℚ) := properSpace_adicCompletion_rat v
  have hmp := measurePreserving_shiftMap v q
  have hemb : MeasurableEmbedding (shiftMap v q) :=
    (shiftHomeomorph v q).toMeasurableEquiv.measurableEmbedding
  have himage : shiftMap v q '' unipotentBall3 v c = unipotentBall3 v c := by
    ext p
    constructor
    · rintro ⟨p', hp', rfl⟩
      exact unipotentBall3_mul_mem v hp' hq
    · intro hp
      refine ⟨shiftMapInv v q p, ?_, shiftMap_shiftMapInv v q p⟩
      have h1 := unipotentBall3_mul_mem v hp (unipotentBall3_inv_mem v hq)
      convert h1 using 1
      simp only [shiftMapInv]
      exact Prod.ext (by ring) (Prod.ext (by ring) (by ring))
  obtain ⟨G, hG⟩ : ∃ G : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ,
      G = fun p => psiLocal ℚ v (q.1 + q.2.1) *
        (psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) := ⟨_, rfl⟩
  have hfun : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 q.1 q.2.1 q.2.2) u
        (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) = fun p => G (shiftMap v q p) := by
    funext p
    rw [hG]
    simp only [gl3AmbientRightTranslate_apply, shiftMap, mul_assoc, upperUnipotent3_mul_upperUnipotent3]
    have hψ : psiLocal ℚ v (q.1 + q.2.1) * psiLocal ℚ v (-((p.1 + q.1) + (p.2.1 + q.2.1))) =
        psiLocal ℚ v (-(p.1 + p.2.1)) := by
      rw [show -((p.1 + q.1) + (p.2.1 + q.2.1)) = -(p.1 + p.2.1) + -(q.1 + q.2.1) by ring,
        AddChar.map_add_eq_mul (psiLocal ℚ v) (-(p.1 + p.2.1)) (-(q.1 + q.2.1)), mul_left_comm,
        ← AddChar.map_add_eq_mul (psiLocal ℚ v) (q.1 + q.2.1) (-(q.1 + q.2.1)), add_neg_cancel,
        AddChar.map_zero_eq_one, mul_one]
    rw [← mul_assoc, hψ]
  have key : ∫ p in unipotentBall3 v c, G (shiftMap v q p) ∂(jacquetHaar3 v) =
      ∫ p in unipotentBall3 v c, G p ∂(jacquetHaar3 v) := by
    rw [← hmp.setIntegral_image_emb hemb G (unipotentBall3 v c), himage]
  simp only [jacquetTruncated3]
  rw [hfun, key, hG]
  beta_reduce
  exact integral_const_mul _ _

end Substitution

section JacquetFunctional

variable (v : HeightOneSpectrum (𝓞 ℚ))

private def jIntegrand (u : LocalGL3 v → ℂ) :
    v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ → ℂ :=
  fun p => psiLocal ℚ v (-(p.1 + p.2.1)) * u (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)

private theorem jacquetTruncated3_finset_sum (c : ℤ) {n : ℕ} (κ : Fin n → ℂ) (u : Fin n → LocalGL3 v → ℂ)
    (hu : letI := localBorel ℚ v
      ∀ j, IntegrableOn (jIntegrand v (u j)) (unipotentBall3 v c) (jacquetHaar3 v)) :
    jacquetTruncated3 v c (∑ j, κ j • u j) = ∑ j, κ j * jacquetTruncated3 v c (u j) := by
  letI := localBorel ℚ v
  simp only [jacquetTruncated3]
  have hfun : (fun p : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ =>
      psiLocal ℚ v (-(p.1 + p.2.1)) * (∑ j, κ j • u j) (antidiagonal3 v * upperUnipotent3 p.1 p.2.1 p.2.2)) =
      fun p => ∑ j, κ j * jIntegrand v (u j) p := by
    funext p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, jIntegrand]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, integral_finsetSum _ fun j _ => (hu j).const_mul (κ j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

private theorem exists_stab_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) (f : LocalGL3 v → ℂ) (hf : f ∈ principalSeries3 v χ) :
    letI := localBorel ℚ v
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      IntegrableOn (jIntegrand v f) (unipotentBall3 v c) (jacquetHaar3 v) ∧
      jacquetTruncated3 v c f = jacquetTruncated3 v c₀ f := by
  letI := localBorel ℚ v
  obtain ⟨n, κ, x, y, z, Φ, hΦ, hdec⟩ := exists_decomposition v χ f hf
  choose cj hcj using fun j : Fin n =>
    exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf v χ hχ (Φ j) (hΦ j)
      (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v)
  refine ⟨Finset.univ.sup cj, fun c hc => ?_⟩
  have hle : ∀ j, (cj j : ℤ) ≤ c := fun j =>
    (Nat.cast_le.mpr (Finset.le_sup (f := cj) (Finset.mem_univ j))).trans hc
  have hle₀ : ∀ j, (cj j : ℤ) ≤ ((Finset.univ.sup cj : ℕ) : ℤ) := fun j =>
    Nat.cast_le.mpr (Finset.le_sup (f := cj) (Finset.mem_univ j))
  subst hdec
  constructor
  · have hfun : jIntegrand v (∑ j, κ j • gl3AmbientRightTranslate (R := ℂ)
        (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v) (cellSectionOf v χ (Φ j))) =
        fun p => ∑ j, κ j * jIntegrand v (gl3AmbientRightTranslate (R := ℂ)
          (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v) (cellSectionOf v χ (Φ j))) p := by
      funext p
      simp only [jIntegrand, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfun]
    exact integrable_finsetSum _ fun j _ => ((hcj j c (hle j)).1).const_mul (κ j)
  · rw [jacquetTruncated3_finset_sum v c κ _ (fun j => (hcj j c (hle j)).1),
      jacquetTruncated3_finset_sum v _ κ _ (fun j => (hcj j _ (hle₀ j)).1)]
    exact Finset.sum_congr rfl fun j _ => by rw [(hcj j c (hle j)).2, (hcj j _ (hle₀ j)).2]

private theorem jacquetValue_eq_jacquetTruncated3_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) (f : LocalGL3 v → ℂ) (hf : f ∈ principalSeries3 v χ) :
    letI := localBorel ℚ v
    ∃ c₀ : ℕ, ∀ c : ℤ, (c₀ : ℤ) ≤ c →
      IntegrableOn (jIntegrand v f) (unipotentBall3 v c) (jacquetHaar3 v) ∧
      jacquetValue v f = jacquetTruncated3 v c f := by
  letI := localBorel ℚ v
  obtain ⟨c₁, hc₁⟩ := exists_stab_of_mem v χ hχ f hf
  refine ⟨max c₁ (jacquetLevel v f), fun c hc => ⟨(hc₁ c ((Nat.cast_le.mpr (le_max_left _ _)).trans hc)).1, ?_⟩⟩
  exact (jacquetTruncated3_eq_jacquetValue v f ⟨c₁, fun c hc => (hc₁ c hc).2⟩
    ((Nat.cast_le.mpr (le_max_right _ _)).trans hc)).symm

private theorem jacquetValue_add_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) {f g : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (hg : g ∈ principalSeries3 v χ) : jacquetValue v (f + g) = jacquetValue v f + jacquetValue v g := by
  letI := localBorel ℚ v
  obtain ⟨cf, hcf⟩ := jacquetValue_eq_jacquetTruncated3_of_mem v χ hχ f hf
  obtain ⟨cg, hcg⟩ := jacquetValue_eq_jacquetTruncated3_of_mem v χ hχ g hg
  obtain ⟨cs, hcs⟩ := jacquetValue_eq_jacquetTruncated3_of_mem v χ hχ (f + g) (add_mem hf hg)
  set c : ℤ := max (max (cf : ℤ) (cg : ℤ)) (cs : ℤ) with hc
  have h1 : (cf : ℤ) ≤ c := (le_max_left _ _).trans (le_max_left _ _)
  have h2 : (cg : ℤ) ≤ c := (le_max_right _ _).trans (le_max_left _ _)
  have h3 : (cs : ℤ) ≤ c := le_max_right _ _
  rw [(hcs c h3).2, (hcf c h1).2, (hcg c h2).2]
  exact jacquetTruncated3_add v c f g (hcf c h1).1 (hcg c h2).1

private theorem jacquetValue_smul_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) (a : ℂ) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ) :
    jacquetValue v (a • f) = a * jacquetValue v f := by
  obtain ⟨cf, hcf⟩ := jacquetValue_eq_jacquetTruncated3_of_mem v χ hχ f hf
  obtain ⟨cs, hcs⟩ := jacquetValue_eq_jacquetTruncated3_of_mem v χ hχ (a • f) ((principalSeries3 v χ).smul_mem a hf)
  set c : ℤ := max (cf : ℤ) (cs : ℤ) with hc
  rw [(hcs c (le_max_right _ _)).2, (hcf c (le_max_left _ _)).2]
  exact jacquetTruncated3_smul v c a f

private theorem exists_mem_unipotentBall3 (q : v.adicCompletion ℚ × v.adicCompletion ℚ × v.adicCompletion ℚ) :
    ∃ c : ℕ, q ∈ unipotentBall3 v c := by
  have key : ∀ x : v.adicCompletion ℚ, ∃ n : ℕ, Valued.v x ≤ WithZero.exp (n : ℤ) := by
    intro x
    by_cases hx : Valued.v x = 0
    · exact ⟨0, by rw [hx]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      calc Valued.v x = WithZero.exp (WithZero.log (Valued.v x)) := (WithZero.exp_log hx).symm
        _ ≤ WithZero.exp (((WithZero.log (Valued.v x)).toNat : ℕ) : ℤ) :=
          WithZero.exp_le_exp.mpr (Int.self_le_toNat _)
  obtain ⟨n₁, h₁⟩ := key q.1
  obtain ⟨n₂, h₂⟩ := key q.2.1
  obtain ⟨n₃, h₃⟩ := key q.2.2
  refine ⟨max (max n₁ n₂) n₃, ?_⟩
  rw [mem_unipotentBall3_iff]
  have hm : (n₃ : ℤ) ≤ ((max (max n₁ n₂) n₃ : ℕ) : ℤ) := by exact_mod_cast le_max_right _ _
  have hnn : (0 : ℤ) ≤ ((max (max n₁ n₂) n₃ : ℕ) : ℤ) := Nat.cast_nonneg _
  refine ⟨h₁.trans (WithZero.exp_le_exp.mpr ?_), h₂.trans (WithZero.exp_le_exp.mpr ?_),
    h₃.trans (WithZero.exp_le_exp.mpr ?_)⟩
  · exact_mod_cast (le_max_left n₁ n₂).trans (le_max_left _ _)
  · exact_mod_cast (le_max_right n₁ n₂).trans (le_max_left _ _)
  · linarith

private theorem jacquetValue_rightTranslate_upperUnipotent3_of_mem (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) {f : LocalGL3 v → ℂ} (hf : f ∈ principalSeries3 v χ)
    (x y z : v.adicCompletion ℚ) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f) =
      psiLocal ℚ v (x + y) * jacquetValue v f := by
  obtain ⟨cf, hcf⟩ := jacquetValue_eq_jacquetTruncated3_of_mem v χ hχ f hf
  obtain ⟨ct, hct⟩ := jacquetValue_eq_jacquetTruncated3_of_mem v χ hχ _
    (rightTranslate_mem_principalSeries3 hf (upperUnipotent3 x y z))
  obtain ⟨cq, hcq⟩ := exists_mem_unipotentBall3 v (x, y, z)
  set c : ℤ := max (max (cf : ℤ) (ct : ℤ)) (cq : ℤ) with hc
  have hq : (x, y, z) ∈ unipotentBall3 v c := unipotentBall3_mono v (le_max_right _ _) hcq
  rw [(hct c ((le_max_right _ _).trans (le_max_left _ _))).2, (hcf c ((le_max_left _ _).trans (le_max_left _ _))).2]
  exact jacquetTruncated3_rightTranslate_upperUnipotent3 v c (x, y, z) hq f

private def jacquetFunctional (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i)) :
    ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ where
  toFun F := jacquetValue v (F : LocalGL3 v → ℂ)
  map_add' F G := jacquetValue_add_of_mem v χ hχ F.2 G.2
  map_smul' a F := by simpa using jacquetValue_smul_of_mem v χ hχ a F.2

private def jacquetFunctionalInv (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (hχ : ∀ i, IsLocallyConstant (χ i)) : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ where
  toFun F := jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1]) (F : LocalGL3 v → ℂ))
  map_add' F G := by
    show jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1])
      ((F : LocalGL3 v → ℂ) + (G : LocalGL3 v → ℂ))) = _
    rw [map_add]
    exact jacquetValue_add_of_mem v χ hχ (rightTranslate_mem_principalSeries3 F.2 _)
      (rightTranslate_mem_principalSeries3 G.2 _)
  map_smul' a F := by
    show jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1])
      (a • (F : LocalGL3 v → ℂ))) = _
    rw [map_smul, RingHom.id_apply, smul_eq_mul]
    exact jacquetValue_smul_of_mem v χ hχ a (rightTranslate_mem_principalSeries3 F.2 _)

private theorem gl3AmbientRightTranslate_gl3AmbientRightTranslate (g h : LocalGL3 v) (W : LocalGL3 v → ℂ) :
    gl3AmbientRightTranslate (R := ℂ) h (gl3AmbientRightTranslate (R := ℂ) g W) =
      gl3AmbientRightTranslate (R := ℂ) (h * g) W := by
  funext x
  simp [gl3AmbientRightTranslate_apply, mul_assoc]

private theorem diagonal3_mul_upperUnipotent3_neg (x y z : v.adicCompletion ℚ) :
    diagonal3 v ![1, -1, 1] * upperUnipotent3 x y z = upperUnipotent3 (-x) (-y) z * diagonal3 v ![1, -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal3_coe, upperUnipotent3_coe, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]

end JacquetFunctional

end LanglandsTunnell.CubicInduction.T0bAux

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "unipotentBall3 mem_unipotentBall3_iff unipotentBall3_mono upperUnipotent3_mul_upperUnipotent3 upperUnipotent3_inv_eq unipotentBall3_mul_mem unipotentBall3_inv_mem jacquetHaar3 jacquetTruncated3 jacquetTruncated3_add jacquetTruncated3_smul jacquetLevel jacquetValue jacquetTruncated3_eq_jacquetValue bigCell3 mem_bigCell3_iff cellCutoff_subset_bigCell3 cellSectionOf cellSectionOf_apply_of_mem cellSectionOf_apply_of_notMem cellSectionOf_upperUnipotent3_mul cellSectionOf_diagonal3_mul jacquetWhittaker3 diagonal3 diagonal3_coe principalSeries3 mem_principalSeries3_iff rightTranslate_mem_principalSeries3 coefficientFn IsWhittakerFunctional3 gl3Entry cornerEntry lowerMinor outerMinor gl3Det gl3Det_ne_zero gl3Entry_upperUnipotent3_mul_two gl3Entry_upperUnipotent3_mul_one gl3Entry_diagonal3_mul cellRatio cellCutoff cellValue cellSection antidiagonal3 antidiagonal3_coe cornerEntry_antidiagonal3 lowerMinor_antidiagonal3 gl3Det_antidiagonal3 antidiagonal3_mem_cellCutoff cellSection_antidiagonal3_ne_zero eventually_valued_eq eventually_valued_lt eventually_norm_eq eventually_charExt_eq continuous_gl3Entry continuous_cornerEntry continuous_lowerMinor continuous_outerMinor continuous_gl3Det gl3Det_eq_bottom_expansion exists_bottom_entry_ne_zero_of_cornerEntry_eq_zero outerMinor_ne_zero_of_lowerMinor_eq_zero gl3AmbientRightTranslate gl3AmbientRightTranslate_apply upperUnipotent3 upperUnipotent3_coe LocalGL3 properSpace_adicCompletion_rat isCompact_setOf_valued_le_one isCompact_setOf_valued_sub_le exists_forall_le_integrableOn_and_jacquetTruncated3_eq_of_cellSectionOf"
namespace T0bAux
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem jacquetValue_diagonal_rightTranslate_upperUnipotent3_of_mem
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i)) {f : LocalGL3 v → ℂ}
    (hf : f ∈ principalSeries3 v χ) (x y z : v.adicCompletion ℚ) :
    jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1])
        (gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f)) =
      (psiLocal ℚ v)⁻¹ (x + y) *
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1]) f) := by
  rw [gl3AmbientRightTranslate_gl3AmbientRightTranslate, diagonal3_mul_upperUnipotent3_neg,
    ← gl3AmbientRightTranslate_gl3AmbientRightTranslate,
    jacquetValue_rightTranslate_upperUnipotent3_of_mem v χ hχ
      (rightTranslate_mem_principalSeries3 hf (diagonal3 v ![1, -1, 1])) (-x) (-y) z,
    AddChar.inv_apply, neg_add]

end LanglandsTunnell.CubicInduction.T0bAux

end

open LanglandsTunnell.CubicInduction.T0bAux

theorem solution

    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i)) :
    ∃ Λ₀ Λ₁ : ↥(principalSeries3 v χ) →ₗ[ℂ] ℂ,
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ v) Λ₀ ∧
      (∀ F : ↥(principalSeries3 v χ), Λ₀ F = jacquetValue v (F : LocalGL3 v → ℂ)) ∧
      (∀ Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ →
        ∃ h : cellSectionOf v χ Φ ∈ principalSeries3 v χ,
          jacquetWhittaker3 v χ Φ = coefficientFn Λ₀ ⟨cellSectionOf v χ Φ, h⟩) ∧
      (∀ f : ↥(principalSeries3 v χ), ∃ (n : ℕ) (κ : Fin n → ℂ) (x y z : Fin n → v.adicCompletion ℚ)
        (Φ : Fin n → (Fin 3 → v.adicCompletion ℚ) → ℂ),
        (∀ j, IsLocallyConstant (Φ j) ∧ HasCompactSupport (Φ j)) ∧
        (f : LocalGL3 v → ℂ) = ∑ j, κ j • gl3AmbientRightTranslate (R := ℂ)
          (upperUnipotent3 (x j) (y j) (z j) * antidiagonal3 v) (cellSectionOf v χ (Φ j))) ∧
      IsWhittakerFunctional3 (NumberField.StandardAddChar.psiLocal ℚ v)⁻¹ Λ₁ ∧
      (∀ F : ↥(principalSeries3 v χ), Λ₁ F =
        jacquetValue v (gl3AmbientRightTranslate (R := ℂ) (diagonal3 v ![1, -1, 1]) (F : LocalGL3 v → ℂ))) ∧
      ∀ Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ →
        ∃ h : cellSectionOf v χ Φ ∈ principalSeries3 v χ,
          (fun k => jacquetWhittaker3 v χ Φ (diagonal3 v ![1, -1, 1] * k)) =
            coefficientFn Λ₁ ⟨cellSectionOf v χ Φ, h⟩ := by
  refine ⟨jacquetFunctional v χ hχ, jacquetFunctionalInv v χ hχ, ?_, fun _ => rfl, ?_, fun f => ?_, ?_, fun _ => rfl,
    ?_⟩
  · intro x y z F
    exact jacquetValue_rightTranslate_upperUnipotent3_of_mem v χ hχ F.2 x y z
  · intro Φ hΦ
    exact ⟨cellSectionOf_mem_principalSeries3 v χ hχ Φ hΦ, rfl⟩
  · exact exists_decomposition v χ f f.2
  · intro x y z F
    exact jacquetValue_diagonal_rightTranslate_upperUnipotent3_of_mem v χ hχ F.2 x y z
  · intro Φ hΦ
    refine ⟨cellSectionOf_mem_principalSeries3 v χ hχ Φ hΦ, ?_⟩
    funext k
    exact congrArg (jacquetValue v)
      (gl3AmbientRightTranslate_gl3AmbientRightTranslate v k (diagonal3 v ![1, -1, 1]) (cellSectionOf v χ Φ)).symm

end S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_isWhittakerFunctional3_psiLocal_and_inv_eq_jacquetValue_and_eq_sum (solution)

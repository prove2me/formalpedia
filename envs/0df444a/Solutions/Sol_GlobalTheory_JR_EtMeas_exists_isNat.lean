-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.exists_isNat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:22:36.66681+00:00
-- url     : https://prove2.me/submissions/1867b668-eb71-49b6-b73a-fb0a04bb4a9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsHaarQuotientIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_borel_units
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit
import Theorems.Thm_GlobalTheory_JR_EtMeas_normU_val
import Theorems.Thm_GlobalTheory_JR_EtMeas_isOpen_range
import Theorems.Thm_GlobalTheory_JR_EtMeas_isSES
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
import Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_eq_norm
import Theorems.Thm_GlobalTheory_JR_exists_haar_quotient_integral_formula
import Theorems.Thm_GlobalTheory_exists_isHaarMeasure_units_div_module
import Theorems.Thm_GlobalTheory_isOpenUnits_and_eventually_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtMeas
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.EtMeas
theorem _root_.solution [U : Unram F E] (A : Et F E) (μK : Measure A.K) (μL : Measure A.L)
    (hμK : μK.IsAddHaarMeasure) (hμL : μL.IsAddHaarMeasure) : ∃ ν, A.IsNat μK μL ν := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, -, _, hSK⟩ := top_facts F A.K
  obtain ⟨_, _, _, _, hSL⟩ := top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (starF A)⟩
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.K
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.L
  have hK := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.K)
  have hL := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.L)
  have : LocallyCompactSpace A.Lˣ := hL.locallyCompactSpace
  have : SecondCountableTopology A.Lˣ := hL.isEmbedding.secondCountableTopology
  have := borel_units A.K
  have := borel_units A.L
  have : SecondCountableTopology A.Kˣ := hK.isEmbedding.secondCountableTopology
  have hδ : ∀ y : A.Lˣ, ((A.absK (A.NL y) : ℝ) : ℂ) = ((distribHaarChar A.L y : ℝ) : ℂ) := by
    intro y
    rw [← normU_val, absK_unit]
    have := GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) y (normU A y) (hN y)
    rw [this]
  obtain ⟨mK, hmK, hfK⟩ := GlobalTheory.exists_isHaarMeasure_units_div_module A.K μK hμK hSK
  obtain ⟨mL, hmL, hfL⟩ := GlobalTheory.exists_isHaarMeasure_units_div_module A.L μL hμL hSL
  have hop := isOpen_range A
  have hC : (mK.comap (normU A).range.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) mK hop.isOpenEmbedding_subtypeVal
  obtain ⟨ν, hν, hf⟩ := GlobalTheory.JR.exists_haar_quotient_integral_formula _ _ _ _ _ (isSES A) mL _ hmL hC
  refine ⟨ν, hν, fun s hs h hh hsupp => ?_⟩
  have hs' : ∀ c : (normU A).range, A.NL (s (c : A.Kˣ)) = (c : A.Kˣ) := by
    rintro ⟨_, y, rfl⟩
    exact hs y y.isUnit
  have hu : ∀ c : (normU A).range, IsUnit (s (c : A.Kˣ)) := fun c => by
    have h1 := (c : A.Kˣ).isUnit.map (algebraMap A.K A.L)
    rw [← hs' c, hN] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hcs : HasCompactSupport fun u : A.Lˣ => h u := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Units.val ⁻¹' tsupport h) ?_
      fun u hu => subset_tsupport h hu
    refine hL.isInducing.isCompact_preimage' hh.2 fun y hy => ?_
    exact hsupp hy
  have e1 := hf (fun u => h u) (hh.1.continuous.comp Units.continuous_val) hcs (fun c => (hu c).unit)
    (fun c => Subtype.ext (Units.ext (hs' c)))
  have e2 := hfL h (fun y => ((A.absK (A.NL y) : ℝ) : ℂ)) hδ Set.univ MeasurableSet.univ
  have e3 := hfK (fun a => A.orbL ν h (s a)) (fun a => ((A.absK a : ℝ) : ℂ)) (fun u => by rw [absK_unit])
    _ hop.measurableSet
  have hset : {a : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a} = Units.val '' ((normU A).range : Set A.Kˣ) := by
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨_, ⟨hy.unit, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, y.isUnit, rfl⟩
  rw [hset, ← e3, ← integral_subtype_comap hop.measurableSet,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Units.val '' (Set.univ : Set A.Lˣ)), ← e2,
    Measure.restrict_univ, e1]
  · refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    simp only [Et.orbL]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    exact congrArg h (mul_comm _ _)
  · intro y hy
    have : h y = 0 := image_eq_zero_of_notMem_tsupport fun h1 => by
      obtain ⟨u, hu⟩ := hsupp h1
      exact hy ⟨u, trivial, hu⟩
    simp [this]
end GlobalTheory.JR.EtMeas

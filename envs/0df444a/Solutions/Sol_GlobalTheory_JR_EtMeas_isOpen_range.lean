-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.isOpen_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:51.629158+00:00
-- url     : https://prove2.me/submissions/3117a5b8-4065-4a39-a07f-1fdc4d188890

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
import Theorems.Thm_GlobalTheory_JR_EtMeas_normU_val
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure
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
theorem _root_.solution [U : Unram F E] (A : Et F E) : IsOpen ((normU A).range : Set A.Kˣ) := by
  have := U.charZero; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨-, hsq⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.K
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  have h1 : ∀ᶠ v : A.Kˣ in 𝓝 1, ∃ s : A.K, s ^ 2 = v := (Units.continuous_val.tendsto 1).eventually hsq
  filter_upwards [h1] with v ⟨s, hs⟩
  have hu : IsUnit s := (isUnit_pow_iff two_ne_zero).1 (hs ▸ v.isUnit)
  refine ⟨(hu.map (algebraMap A.K A.L)).unit, Units.ext (hinj ?_)⟩
  rw [normU_val, hN, IsUnit.unit_spec, A.star_K, ← map_mul, ← hs, sq]
end GlobalTheory.JR.EtMeas

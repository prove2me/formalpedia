-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.isSES
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:08.648182+00:00
-- url     : https://prove2.me/submissions/353f22c7-fadf-4248-82e1-863823d883fd

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
import Theorems.Thm_GlobalTheory_JR_EtMeas_continuous_NL
import Theorems.Thm_GlobalTheory_JR_EtMeas_normU_val
import Theorems.Thm_GlobalTheory_JR_EtMeas_isOpen_range
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
theorem _root_.solution [U : Unram F E] (A : Et F E) :
    TopologicalGroup.IsSES (Unitary.toUnits : unitary A.L →* A.Lˣ) (normU A).rangeRestrict := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := finite_L A
  obtain ⟨-, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, -, _, -⟩ := top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.K
  obtain ⟨_, -⟩ := GlobalTheory.isOpenUnits_and_eventually_sq F A.L
  have hK := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.K)
  have hL := IsOpenUnits.isOpenEmbedding_unitsVal (M := A.L)
  have hc : Continuous (normU A) := Units.continuous_map (continuous_NL A)
  have hker : ∀ y : A.Lˣ, normU A y = 1 ↔ y ∈ Set.range (Unitary.toUnits : unitary A.L →* A.Lˣ) := by
    intro y
    constructor
    · intro h
      have h1 : (y : A.L) * star (y : A.L) = 1 := by rw [← hN, ← normU_val, h]; simp
      exact ⟨⟨y, by rw [mul_comm]; exact h1, h1⟩, Units.ext rfl⟩
    · rintro ⟨t, rfl⟩
      refine Units.ext (hinj ?_)
      rw [normU_val, hN]
      simp
  have : LocallyCompactSpace A.Lˣ := hL.locallyCompactSpace
  have : LocallyCompactSpace A.Kˣ := hK.locallyCompactSpace
  have : SecondCountableTopology A.Lˣ := hL.isEmbedding.secondCountableTopology
  have : LocallyCompactSpace (normU A).range := (isOpen_range A).locallyCompactSpace
  have hc' : Continuous (normU A).rangeRestrict := hc.subtype_mk _
  refine ⟨⟨?_, ?_⟩, ⟨(normU A).rangeRestrict_surjective, hc',
    MonoidHom.isOpenMap_of_sigmaCompact _ (normU A).rangeRestrict_surjective hc'⟩, fun y => ?_⟩
  · exact hL.isEmbedding.of_comp_iff.1 IsEmbedding.subtypeVal
  · rw [show Set.range (Unitary.toUnits : unitary A.L →* A.Lˣ) = normU A ⁻¹' {1} from
      Set.ext fun y => (hker y).symm]
    exact isClosed_singleton.preimage hc
  · rw [← hker y, Subtype.ext_iff]; rfl
end GlobalTheory.JR.EtMeas

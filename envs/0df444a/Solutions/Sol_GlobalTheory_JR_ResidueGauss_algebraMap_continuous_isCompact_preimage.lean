-- Prove2me | solution 1 for GlobalTheory.JR.ResidueGauss.algebraMap_continuous_isCompact_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:09:42.781236+00:00
-- url     : https://prove2.me/submissions/5c368051-ab40-4c25-89ee-1cced4804647

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_JR_Et_quadratic_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ResidueGauss
namespace GlobalTheory.JR.ResidueGauss
theorem _root_.solution {F E : Type} [NontriviallyNormedField F]
    [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [U : Unram F E] (A : Et F E) :
    Continuous (algebraMap A.K A.L) ∧
      ∀ O : Set A.L, IsCompact O → IsCompact (algebraMap A.K A.L ⁻¹' O) := by
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨-, hinj, -, -, -⟩ := Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  let ιF : A.K →ₗ[F] A.L := (IsScalarTower.toAlgHom F A.K A.L).toLinearMap
  have hιF : ∀ s, ιF s = algebraMap A.K A.L s := fun s => rfl
  have hc : Continuous (algebraMap A.K A.L) := by
    have := IsModuleTopology.continuous_of_linearMap ιF
    exact this
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ιF (LinearMap.ker_eq_bot.2 hinj)
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  refine ⟨hc, fun O hO => ?_⟩
  refine (hO.image hrc).of_isClosed_subset (hO.isClosed.preimage hc) ?_
  intro s hs
  exact ⟨algebraMap A.K A.L s, hs, LinearMap.congr_fun hr s⟩
end GlobalTheory.JR.ResidueGauss

-- Prove2me | solution 1 for GlobalTheory.HCXi.KGroup.kset_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:29.706466+00:00
-- url     : https://prove2.me/submissions/316bdd56-4d09-4e40-b648-412d88584274

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Theorems.Thm_GlobalTheory_HCXi_KGroup_closedSubgroup
import Theorems.Thm_GlobalTheory_HCXi_KGroup_compact
import Theorems.Thm_GlobalTheory_HCXi_KGroup_hpk_mem
import Theorems.Thm_GlobalTheory_HCXi_KGroup_star_mem
import Theorems.Thm_GlobalTheory_HCXi_KGroup_comm_hpk
import Theorems.Thm_GlobalTheory_HCXi_KGroup_gN_biinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.HCXi GlobalTheory.HCXi.KGroup
namespace GlobalTheory.HCXi.KGroup
theorem _root_.solution : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g :=
  fun k r => ⟨closedSubgroup k r, compact k r, hpk_mem k r, fun _ h => ⟨star_mem h, comm_hpk h⟩,
    fun _ h _ h' g => gN_biinv h h' g⟩
end GlobalTheory.HCXi.KGroup

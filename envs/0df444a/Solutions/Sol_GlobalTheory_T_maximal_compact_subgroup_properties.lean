-- Prove2me | solution 1 for GlobalTheory.T.maximal_compact_subgroup_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:27.252975+00:00
-- url     : https://prove2.me/submissions/20c3445d-d758-4cca-a170-89c09c657e1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupProperties
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MaximalCompactSubgroupPropertiesStatement
import Theorems.Thm_GlobalTheory_HCXi_KGroup_kset_facts


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ k r : ℕ, IsClosedSubgroup (Kset k r) ∧ IsCompact (Kset k r) ∧ Hpk k r ∈ Kset k r ∧ (∀ κ ∈ Kset k r, κᴴ ∈ Kset k r ∧ κ * Hpk k r = Hpk k r * κ) ∧ ∀ κ ∈ Kset k r, ∀ κ' ∈ Kset k r, ∀ g : Mat k r, gN (κ * g * κ') = gN g := by
  first | exact @GlobalTheory.HCXi.KGroup.kset_facts | exact GlobalTheory.HCXi.KGroup.kset_facts | (intros; apply GlobalTheory.HCXi.KGroup.kset_facts <;> assumption)
end _root_.GlobalTheory.T

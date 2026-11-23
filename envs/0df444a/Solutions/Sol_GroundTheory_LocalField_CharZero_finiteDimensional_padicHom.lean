-- Prove2me | solution 1 for GroundTheory.LocalField.CharZero.finiteDimensional_padicHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:54.578805+00:00
-- url     : https://prove2.me/submissions/62defdbe-6297-439e-898d-313b08e00942

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Theorems.Thm_GroundTheory_LocalField_CharZero_continuous_padicHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel WithZero Topology
open GroundTheory.LocalField.CharZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [CharP 𝓀[K] p]
variable [Fact p.Prime]
variable [CharZero K]
namespace GroundTheory.LocalField.CharZero
theorem _root_.solution :
    letI := (padicHom K p).toAlgebra
    FiniteDimensional ℚ_[p] K := by
  let := (padicHom K p).toAlgebra
  have : T2Space K := by
    let := IsTopologicalAddGroup.rightUniformSpace K
    have := isUniformAddGroup_of_addCommGroup (G := K)
    infer_instance
  have : ContinuousSMul ℚ_[p] K :=
    ⟨((continuous_padicHom K p).comp continuous_fst).mul continuous_snd⟩
  exact FiniteDimensional.of_locallyCompactSpace ℚ_[p]
end GroundTheory.LocalField.CharZero

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.exists_near_of_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:36.474818+00:00
-- url     : https://prove2.me/submissions/b91b463d-1c8a-4140-9c00-c157179618e0

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution {c : Fin m → Fin m → L} {A : Set (Fin m → Fin m → L)} (hA : A ∈ 𝓝 c) :
    ∃ ε > 0, ∀ B : Fin m → Fin m → L, (∀ i j, ‖B i j - c i j‖ ≤ ε) → B ∈ A := by
  obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨ε / 2, half_pos hε, fun B hB => h (Metric.mem_ball.2 ?_)⟩
  refine (dist_pi_lt_iff hε).2 fun i => (dist_pi_lt_iff hε).2 fun j => ?_
  rw [dist_eq_norm]; exact (hB i j).trans_lt (half_lt_self hε)
end GlobalTheory.CompanionTheory.BLevel

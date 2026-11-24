-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BLevel.isOpen_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:20:29.362409+00:00
-- url     : https://prove2.me/submissions/24bd39bc-827e-4845-9148-43e58c619ea7

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerLast
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_LatticeCongruenceSubgroupsOpenCompact
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl Topology Filter
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BLevel
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
namespace GlobalTheory.CompanionTheory.BLevel
theorem _root_.solution {r : ℝ} (hr : 0 < r) : IsOpen {g : GL (Fin m) L | IsNear r g.1} := by
  have e : {A : Matrix (Fin m) (Fin m) L | IsNear r A} = ⋂ i, ⋂ j, (fun A : Matrix (Fin m) (Fin m) L => A i j) ⁻¹'
      Metric.closedBall ((1 : Matrix (Fin m) (Fin m) L) i j) r := by
    ext A; simp [IsNear, dist_eq_norm]
  have h2 : IsOpen {A : Matrix (Fin m) (Fin m) L | IsNear r A} := by
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (continuous_id.matrix_elem i j)
  exact h2.preimage Units.continuous_val
end GlobalTheory.CompanionTheory.BLevel

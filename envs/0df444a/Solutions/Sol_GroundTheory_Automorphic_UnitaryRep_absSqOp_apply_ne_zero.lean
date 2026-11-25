-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.absSqOp_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:21.847012+00:00
-- url     : https://prove2.me/submissions/f7d30ec5-9039-42c7-b803-e5ef544e8b79

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_inner_absSqOp_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution {f : G →₁[μ] ℂ} {v : H} (h : π.integrated μ f v ≠ 0) :
    π.absSqOp μ f v ≠ 0 := by
  intro h0
  have := π.inner_absSqOp_self μ f v
  rw [h0, inner_zero_right, eq_comm, inner_self_eq_zero] at this
  exact h this
end GroundTheory.Automorphic.UnitaryRep

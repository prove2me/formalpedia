-- Prove2me | solution 1 for GlobalTheory.Proof.TwistSupportPeriodicLevels.stabLat_le_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:47:57.428745+00:00
-- url     : https://prove2.me/submissions/6dd783ea-776a-43cb-8a50-b65f9218dfe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
import Theorems.Thm_GlobalTheory_StepData_mem_stabLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory GlobalTheory.Proof GlobalTheory.Proof.TwistSupportPeriodicLevels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
theorem _root_.solution {g : GL Y k} (hg : g ∈ KO k Y) : stabLat g ≤ KO k Y := by
  intro a ha
  have hc := mem_stabLat.mp ha
  have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hg hc) (inv_mem hg)
end GlobalTheory.Proof.TwistSupportPeriodicLevels

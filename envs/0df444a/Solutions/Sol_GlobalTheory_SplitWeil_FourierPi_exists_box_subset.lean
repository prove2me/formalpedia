-- Prove2me | solution 1 for GlobalTheory.SplitWeil.FourierPi.exists_box_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:48.561474+00:00
-- url     : https://prove2.me/submissions/a6eaba4a-956e-4cb7-bc7d-671affc4c0fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_exists_cball_subset


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]
namespace GlobalTheory.SplitWeil.FourierPi
theorem _root_.solution {U : Set (n → k)} (hU : U ∈ 𝓝 (0 : n → k)) : ∃ s : kˣ, box n s ⊆ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  have h1 : (⋂ i, t i) ∈ 𝓝 (0 : k) := Filter.iInter_mem.mpr ht
  obtain ⟨s, hs⟩ := exists_cball_subset h1
  exact ⟨s, fun x hx => hsub fun i _ => Set.mem_iInter.mp (hs (hx i trivial)) i⟩
end GlobalTheory.SplitWeil.FourierPi

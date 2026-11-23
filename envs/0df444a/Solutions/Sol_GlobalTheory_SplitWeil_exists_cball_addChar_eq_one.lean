-- Prove2me | solution 1 for GlobalTheory.SplitWeil.exists_cball_addChar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:31.611213+00:00
-- url     : https://prove2.me/submissions/23a7953d-c380-45b6-8768-2bd1be22bea3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
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
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ s : kˣ, ∀ y ∈ cball s, ψ y = 1 := by
  have hU : ψ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (0 : k) := by
    refine ((Circle.isOpen_centeredArc _).preimage hψ).mem_nhds ?_
    rw [Set.mem_preimage, AddChar.map_zero_eq_one]
    exact ⟨0, by simpa using Real.pi_pos, by simp⟩
  obtain ⟨s, hs⟩ := exists_cball_subset hU
  refine ⟨s, fun y hy => Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_⟩
  rw [← AddChar.map_nsmul_eq_pow]
  refine hs ?_
  clear * - hy
  induction n with
  | zero => simp [cball]
  | succ n ih => rw [succ_nsmul]; exact add_mem_cball ih hy
end GlobalTheory.SplitWeil

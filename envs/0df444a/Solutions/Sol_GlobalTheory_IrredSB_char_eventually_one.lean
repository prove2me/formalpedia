-- Prove2me | solution 1 for GlobalTheory.IrredSB.char_eventually_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:53:59.86304+00:00
-- url     : https://prove2.me/submissions/3df31f4c-5c47-4f12-b6f3-015cfeb9c3c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Theorems.Thm_GlobalTheory_IrredSB_eq_one_of_forall_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IrredSB
theorem _root_.solution (ψk : AddChar k Circle) (hψ : Continuous ψk) :
    ∀ᶠ x in 𝓝 (0 : k), ψk x = 1 := by
  have hc : Continuous (fun x : k => ‖(ψk x : ℂ) - 1‖) := by fun_prop
  have h1 : {x : k | ‖(ψk x : ℂ) - 1‖ < 1} ∈ 𝓝 (0 : k) :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 h1
  have hnb : {x : k | valuation k x < γ} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, subset_rfl⟩
  filter_upwards [hnb] with x hx
  have hx' : x ∈ (valuation k).ltAddSubgroup γ := hx
  refine Circle.ext (eq_one_of_forall_pow (Circle.norm_coe _) fun m => ?_)
  have hm : valuation k (m • x) < γ := (nsmul_mem hx' m : m • x ∈ (valuation k).ltAddSubgroup γ)
  have := hγ hm
  simpa [AddChar.map_nsmul_eq_pow, -nsmul_eq_mul] using this
end GlobalTheory.IrredSB

-- Prove2me | solution 1 for GlobalTheory.PartRedEval.exists_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:05.501682+00:00
-- url     : https://prove2.me/submissions/977691c7-b1ff-4f63-9624-8b3949cdb1ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEvaluateEntryOfMulLaw
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_exists_ne_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.PartRedEval
open GlobalTheory.PartRed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {R Q : Type} [Fintype R] [Fintype Q] [DecidableEq R] [DecidableEq Q]
namespace GlobalTheory.PartRedEval
theorem _root_.solution {ψ : AddChar k Circle} {c : kˣ} (h : HasConductor ψ c) (s : kˣ) {d : k} (hd : d ∉ cball s) :
    ∃ b : k, ψ (b * d) ≠ 1 ∧ ∀ u ∈ cball s, ψ (b * u) = 1 := by
  obtain ⟨t, ht, hne⟩ := h.exists_ne_one (c * s⁻¹) (x := d) (by
    rwa [show c * (c * s⁻¹)⁻¹ = s by rw [_root_.mul_inv_rev, inv_inv, mul_comm s, mul_inv_cancel_left]])
  refine ⟨t, hne, fun u hu => h.eq_one ?_⟩
  have h1 : valuation k t ≤ valuation k ((c * s⁻¹ : kˣ) : k) := ht
  have h2 : valuation k u ≤ valuation k (s : k) := hu
  show valuation k (t * u) ≤ valuation k (c : k)
  have h3 : (c : k) = ((c * s⁻¹ : kˣ) : k) * s := by simp
  rw [h3, map_mul, map_mul]
  exact mul_le_mul' h1 h2
end GlobalTheory.PartRedEval

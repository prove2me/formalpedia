-- Prove2me | solution 1 for GlobalTheory.SplitWeil.isLocallyConstant_nabs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:08.065439+00:00
-- url     : https://prove2.me/submissions/ad018b1b-6333-460c-aafa-e58103b1c407

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_iff
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball


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
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (k)
namespace GlobalTheory.SplitWeil
theorem _root_.solution : IsLocallyConstant (nabs k) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 : (fun z : kˣ => (z : k) - x) ⁻¹' cball (Units.mk0 r hr0 * x) ∈ 𝓝 x :=
    ((isOpen_cball _).preimage (Units.continuous_val.sub continuous_const)).mem_nhds (by simp [cball])
  filter_upwards [h1] with z hz
  rw [nabs_eq_iff]
  have h2 : valuation k ((z : k) - x) ≤ valuation k (r * x) := hz
  refine Valuation.map_eq_of_sub_lt _ (h2.trans_lt ?_)
  rw [map_mul]
  exact mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1
end GlobalTheory.SplitWeil

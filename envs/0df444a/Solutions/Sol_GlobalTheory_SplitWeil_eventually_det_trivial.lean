-- Prove2me | solution 1 for GlobalTheory.SplitWeil.eventually_det_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:41.078803+00:00
-- url     : https://prove2.me/submissions/bb0ec203-2121-498d-99d0-33b32a880a43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_valuation_eq_one
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_eq_one_of_valuation_eq_one


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
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (n : Type*) [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsOpen (μ.ker : Set kˣ)) :
    ∀ᶠ g : GL n k in 𝓝 1, μ (Matrix.GeneralLinearGroup.det g) = 1 ∧
      nabs k (Matrix.GeneralLinearGroup.det g) = 1 := by
  have hU := (hμ.inter isOpen_valuation_eq_one).preimage
    (Matrix.GeneralLinearGroup.continuous_det (n := n) (R := k))
  filter_upwards [hU.mem_nhds (x := 1) (by simp)] with g hg
  exact ⟨hg.1, nabs_eq_one_of_valuation_eq_one hg.2⟩
end GlobalTheory.SplitWeil

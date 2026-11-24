-- Prove2me | solution 1 for GlobalTheory.SplitWeil.om_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:27:23.32953+00:00
-- url     : https://prove2.me/submissions/4ba87434-8d8e-4689-8c92-5718c07728be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq

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
theorem _root_.solution (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (z : ℂ) (Φ Ψ : Matrix b a k → ℂ) :
    om μ g h (z • Φ + Ψ) = z • om μ g h Φ + om μ g h Ψ := by
  funext x
  simp only [om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.SplitWeil

-- Prove2me | solution 1 for GlobalTheory.FunObj.flatIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:15.688661+00:00
-- url     : https://prove2.me/submissions/afb482de-ac0d-4c92-8718-721174705167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Theorems.Thm_GlobalTheory_FunObj_flatIntegrable_of_isTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k}
namespace GlobalTheory.FunObj
theorem _root_.solution [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ G.s) (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} :
    IsUnif ϖ → Continuous ψ → G.IsTensor ϖ e (oppositePath G.m) T → FlatIntegrable hs ψ ν T :=
  fun _ hψ hT => flatIntegrable_of_isTensor hs ψ ν hψ hT
end GlobalTheory.FunObj

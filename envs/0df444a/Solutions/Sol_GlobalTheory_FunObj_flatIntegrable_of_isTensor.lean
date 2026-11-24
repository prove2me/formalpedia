-- Prove2me | solution 1 for GlobalTheory.FunObj.flatIntegrable_of_isTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:21.566696+00:00
-- url     : https://prove2.me/submissions/72bab499-5ada-4cb6-8379-320a669d82f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Theorems.Thm_GlobalTheory_FunObj_continuous_flatIntegrand
import Theorems.Thm_GlobalTheory_FunObj_hasCompactSupport_flatIntegrand
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


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
    (ν : Measure k) [ν.IsAddHaarMeasure] {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ} (hψ : Continuous ψ)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) : FlatIntegrable hs ψ ν T := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  intro g x y
  unfold varsVol
  exact (continuous_flatIntegrand hs hψ hT true g x y).integrable_of_hasCompactSupport
    (hasCompactSupport_flatIntegrand hs ψ hT true g x y)
end GlobalTheory.FunObj

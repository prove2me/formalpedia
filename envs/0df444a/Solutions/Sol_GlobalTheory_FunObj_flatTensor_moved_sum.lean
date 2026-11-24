-- Prove2me | solution 1 for GlobalTheory.FunObj.flatTensor_moved_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:23.177968+00:00
-- url     : https://prove2.me/submissions/dbcf07c5-93de-470c-98be-a33bb5b0489c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorMovedTensorFinsetSumLinear
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
open MeasureTheory GlobalTheory.FunObj
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
namespace GlobalTheory.FunObj
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s)
    (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : Continuous ψ) (ϖ : kˣ) (e : ℕ) (keep : Bool)
    (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ)
    (hT : ∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) (X : ColArgs G) (Y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y =
      ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hint : ∀ i ∈ S, Integrable (flatIntegrand hs ψ (moved G keep g (T i)) X Y) (varsVol G ν) := by
    intro i hi
    unfold varsVol
    exact (continuous_flatIntegrand hs hψ (hT i hi) keep g X Y).integrable_of_hasCompactSupport
      (hasCompactSupport_flatIntegrand hs ψ (hT i hi) keep g X Y)
  have h : ∀ v, flatIntegrand hs ψ (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y v =
      ∑ i ∈ S, x i * flatIntegrand hs ψ (moved G keep g (T i)) X Y v := by
    intro v
    simp only [flatIntegrand, moved, GlobalTheory.SplitFlip.Grid.pathAct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [flatTensor, h]
  rw [integral_finset_sum _ fun i hi => (hint i hi).const_mul _]
  simp only [integral_const_mul]
end GlobalTheory.FunObj

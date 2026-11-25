-- Prove2me | solution 1 for GlobalTheory.RootEx.LatOpen.eventually_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:46.013703+00:00
-- url     : https://prove2.me/submissions/e2863f07-a780-4560-b972-0d88bd6071db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenAndRelIndexNeZero
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.LatOpen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}
namespace GlobalTheory.RootEx.LatOpen
theorem _root_.solution (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) (x : ι → k) :
    ∀ᶠ t in nhds (0 : k), t • x ∈ L := by
  have hx : x ∈ Submodule.span k (L : Set (ι → k)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have h : (𝒪[k] : Set k) ∈ nhds (0 : k) := (isOpen_int k).mem_nhds (zero_mem 𝒪[k])
    filter_upwards [h] with t ht
    exact L.smul_mem (⟨t, ht⟩ : 𝒪[k]) hy
  | zero => exact Filter.Eventually.of_forall fun t => by simp
  | add y z _ _ hy hz =>
    filter_upwards [hy, hz] with t h1 h2
    rw [smul_add]
    exact L.add_mem h1 h2
  | smul a y _ hy =>
    have ht : Filter.Tendsto (fun t : k => t * a) (nhds 0) (nhds 0) := by
      have h : Continuous (fun t : k => t * a) := continuous_id.mul continuous_const
      simpa using h.tendsto 0
    filter_upwards [ht.eventually hy] with t h
    rwa [smul_smul]
end GlobalTheory.RootEx.LatOpen

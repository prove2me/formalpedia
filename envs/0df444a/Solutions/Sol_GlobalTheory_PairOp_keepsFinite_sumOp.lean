-- Prove2me | solution 1 for GlobalTheory.PairOp.keepsFinite_sumOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:48.082807+00:00
-- url     : https://prove2.me/submissions/38c968a0-f2a9-4d88-895f-0397ea8433e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_LatPair_sumOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
variable {χ}
variable {A B A' B' : Module.End ℂ (Form k n ℂ)}
namespace GlobalTheory.PairOp
theorem _root_.solution (S S' : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ)
    (hS : ∀ P Q, Q ∈ S P → P ∈ S' Q) : KeepsFinite (sumOp S w) := by
  intro φ hφ
  refine (hφ.biUnion fun Q _ => (S' Q).finite_toSet).subset ?_
  intro P hP
  rw [Function.mem_support, sumOp_apply] at hP
  obtain ⟨Q, hQ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
  exact Set.mem_biUnion (x := Q) (Function.mem_support.mpr fun h0 => hne (by rw [h0, smul_zero]))
    (Finset.mem_coe.mpr (hS P Q hQ))
end GlobalTheory.PairOp

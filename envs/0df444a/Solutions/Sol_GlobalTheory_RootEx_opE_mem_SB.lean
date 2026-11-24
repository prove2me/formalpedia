-- Prove2me | solution 1 for GlobalTheory.RootEx.opE_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:50:26.731813+00:00
-- url     : https://prove2.me/submissions/647514cd-5f38-46f1-ae55-c2f2ca009e33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Theorems.Thm_GlobalTheory_RootEx_integral_mul_mem_SB
import Theorems.Thm_GlobalTheory_RootEx_comp_affPt_mem_SB
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c : ℕ}
omit [BorelSpace k] [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.RootEx
theorem _root_.solution (p : ℕ) (ψ : AddChar k Circle) (ν : Measure k)
    {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) : opE ψ ν p Φ ∈ SB (Matrix n n' k) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  exact integral_mul_mem_SB _ _ (comp_affPt_mem_SB p hΦ)
    (fun e => (ψ (-ch (affPt p (0 : Matrix n n' k) e)) : ℂ))
end GlobalTheory.RootEx

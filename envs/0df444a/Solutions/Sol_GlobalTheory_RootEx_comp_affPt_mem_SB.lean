-- Prove2me | solution 1 for GlobalTheory.RootEx.comp_affPt_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:44.990072+00:00
-- url     : https://prove2.me/submissions/1da0f9da-2f48-4f7f-97cf-dc969bda5dfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Theorems.Thm_GlobalTheory_RootEx_continuous_affPt_uncurry
import Theorems.Thm_GlobalTheory_RootEx_isClosedEmbedding_affPt_uncurry

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
variable {k : Type*} [Field k] {n n' : Type*} {c : ℕ}
variable [TopologicalSpace k] [IsTopologicalRing k]
namespace GlobalTheory.RootEx
theorem _root_.solution [T2Space k] (p : ℕ) {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (hΦ : Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    (fun z : Matrix n n' k × ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) =>
        Φ (affPt p z.1 z.2)) ∈ SB _ :=
  ⟨hΦ.1.comp_continuous (continuous_affPt_uncurry p),
    hΦ.2.comp_isClosedEmbedding (isClosedEmbedding_affPt_uncurry p)⟩
end GlobalTheory.RootEx

-- Prove2me | solution 1 for GlobalTheory.LocFlat.add_right_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:36:56.583595+00:00
-- url     : https://prove2.me/submissions/64827f65-4d7b-4039-94b9-779e93318366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapFourierJacobiRowAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution {m m' k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
    {Φ : Matrix m m' k → ℂ} (hΦ : Φ ∈ SB (Matrix m m' k)) (a : Matrix m m' k) :
    (fun z => Φ (z + a)) ∈ SB (Matrix m m' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_right a), hΦ.2.comp_homeomorph (Homeomorph.addRight a)⟩
end GlobalTheory.LocFlat

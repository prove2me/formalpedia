-- Prove2me | solution 1 for GlobalTheory.LogResInt.isClosed_of_isAnalyticSubset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:42.844283+00:00
-- url     : https://prove2.me/submissions/db99d00b-1b8f-48da-8bcd-f211259b00d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Theorems.Thm_GlobalTheory_LogResInt_holoOn_continuousAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
noncomputable section
variable {d : ℕ} {X : Type} [TopologicalSpace X]
namespace GlobalTheory.LogResInt
theorem _root_.solution {A : FinHolAtlas d X} {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx => ?_)
  obtain ⟨W, hW, hxW, r, f, hf, hSW⟩ := hS x
  have : ¬ ∀ i, f i x = 0 := fun h => hx (hSW.ge ⟨hxW, h⟩).1
  push_neg at this
  obtain ⟨i, hi⟩ := this
  have hev : ∀ᶠ y in nhds x, f i y ≠ 0 := (holoOn_continuousAt (hf i) hxW).eventually_ne hi
  filter_upwards [hev, hW.mem_nhds hxW] with y hy hyW hyS
  exact hy ((hSW.le ⟨hyS, hyW⟩).2 i)
end GlobalTheory.LogResInt

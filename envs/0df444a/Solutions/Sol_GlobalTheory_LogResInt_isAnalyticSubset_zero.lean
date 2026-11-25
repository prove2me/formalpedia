-- Prove2me | solution 1 for GlobalTheory.LogResInt.isAnalyticSubset_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:00:39.031012+00:00
-- url     : https://prove2.me/submissions/c2711c65-ccdd-4623-8c2d-187f076c6266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Theorems.Thm_GlobalTheory_LogResInt_isSection_zero_iff

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
theorem _root_.solution {A : FinHolAtlas d X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) : A.IsAnalyticSubset {y | s y y = 0} := by
  intro x
  refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hs.1 x, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy, hyU⟩
    exact ⟨hyU, fun _ => (isSection_zero_iff hs hyU).2 hy⟩
  · rintro ⟨hyU, h⟩
    exact ⟨(isSection_zero_iff hs hyU).1 (h 0), hyU⟩
end GlobalTheory.LogResInt

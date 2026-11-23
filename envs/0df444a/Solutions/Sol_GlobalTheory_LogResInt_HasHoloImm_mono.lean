-- Prove2me | solution 1 for GlobalTheory.LogResInt.HasHoloImm.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:02.016434+00:00
-- url     : https://prove2.me/submissions/a06ef7f0-4c53-4718-be52-71fd47337ff5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset

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
namespace HasHoloImm
theorem _root_.solution {A : FinHolAtlas d X} {T T' : Set X} {k : ℕ} (h : HasHoloImm A T k)
    (hT : T ⊆ T') : HasHoloImm A T' k := by
  obtain ⟨U, g, j, hU, hne, hmaps, han, hinj⟩ := h
  exact ⟨U, g, j, hU, hne, fun z hz => ⟨hT (hmaps hz).1, (hmaps hz).2⟩, han, hinj⟩
end HasHoloImm
end GlobalTheory.LogResInt

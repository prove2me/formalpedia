-- Prove2me | solution 1 for GlobalTheory.LogResInt.holoOn_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:51:59.522722+00:00
-- url     : https://prove2.me/submissions/84dc0bc6-3baa-474b-8004-3f57e876ef05

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
theorem _root_.solution {A : FinHolAtlas d X} {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f)
    {x : X} (hx : x ∈ W) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
      simpa [Set.mem_preimage, (A.chart j).left_inv hj] using hx⟩).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]
end GlobalTheory.LogResInt

-- Prove2me | solution 1 for GlobalTheory.SmGL.isSmooth_extTensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:39.617133+00:00
-- url     : https://prove2.me/submissions/6ea093f4-5552-45b9-9172-2a67402da753

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G]
variable [IsTopologicalGroup G]
namespace GlobalTheory.SmGL
theorem _root_.solution [TopologicalSpace H] [IsTopologicalGroup H] {ρ : Representation F G V}
    {σ : Representation F H W} (hρ : IsSmooth ρ) (hσ : IsSmooth σ) : IsSmooth (extTensor ρ σ) := by
  intro x
  show x ∈ smoothPart (extTensor ρ σ)
  induction x with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul v w =>
    refine mem_smoothPart_of_nhds (Filter.mem_of_superset
      (((hρ v).prod (hσ w)).mem_nhds (by simp)) fun g hg => ?_)
    have h1 : ρ g.1 v = v := hg.1
    have h2 : σ g.2 w = w := hg.2
    simp [h1, h2]
end GlobalTheory.SmGL

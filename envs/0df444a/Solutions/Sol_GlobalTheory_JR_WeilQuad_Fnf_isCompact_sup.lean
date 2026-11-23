-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.Fnf.isCompact_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:57:58.928428+00:00
-- url     : https://prove2.me/submissions/e46eec66-93aa-4b6f-ba8c-7ef2546fa877

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFOpNOpFOpGauss

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.Fnf
namespace GlobalTheory.JR.WeilQuad.Fnf
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    (H K : AddSubgroup V) (hH : IsCompact (H : Set V)) (hK : IsCompact (K : Set V)) :
    IsCompact ((H ⊔ K : AddSubgroup V) : Set V) := by
  have : ((H ⊔ K : AddSubgroup V) : Set V) =
      (fun p : V × V => p.1 + p.2) '' ((H : Set V) ×ˢ (K : Set V)) := by
    ext v
    simp only [SetLike.mem_coe, AddSubgroup.mem_sup, Set.mem_image, Set.mem_prod, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  rw [this]
  exact (hH.prod hK).image continuous_add
end GlobalTheory.JR.WeilQuad.Fnf

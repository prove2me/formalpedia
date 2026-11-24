-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.coi_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:51:49.811063+00:00
-- url     : https://prove2.me/submissions/2fdd9635-7232-455a-b446-a6a54525137e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution {R₁ R₂ : Type} [Ring R₁] [Ring R₂] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {e₁ : ι₁ → R₁} {e₂ : ι₂ → R₂} (h₁ : CompleteOrthogonalIdempotents e₁)
    (h₂ : CompleteOrthogonalIdempotents e₂) :
    CompleteOrthogonalIdempotents (Sum.elim (fun i => ((e₁ i, 0) : R₁ × R₂)) (fun j => ((0, e₂ j) : R₁ × R₂))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact Prod.ext (h₁.idem i).eq (mul_zero 0)
    · exact Prod.ext (mul_zero 0) (h₂.idem j).eq
  · rintro (i | j) (i' | j') hne
    · have hii : i ≠ i' := fun h => hne (congrArg Sum.inl h)
      exact Prod.ext (h₁.ortho hii) (mul_zero 0)
    · exact Prod.ext (mul_zero _) (zero_mul _)
    · exact Prod.ext (zero_mul _) (mul_zero _)
    · have hjj : j ≠ j' := fun h => hne (congrArg Sum.inr h)
      exact Prod.ext (mul_zero 0) (h₂.ortho hjj)
  · rw [Fintype.sum_sum_type]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, h₁.complete]
    · simp [Prod.snd_sum, h₂.complete]
end GlobalTheory.UnitLemma.Desc

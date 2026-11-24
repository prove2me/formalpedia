-- Prove2me | solution 1 for GlobalTheory.PiSimple.pp_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.774954+00:00
-- url     : https://prove2.me/submissions/98325267-4549-4cb4-b20a-a985dfd20c69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmoduleTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OperatorStablePiTensorPureKernelSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOverStableSubmodulePiTensor
import Theorems.Thm_GlobalTheory_PiSimple_simpleOver_of_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.PiSimple
open GlobalTheory.TensHead
namespace GlobalTheory.PiSimple
theorem _root_.solution {σ ι : Type} (f : σ ≃ ι) (hσ : PP σ) : PP ι := by
  intro _ M _ _ Op K hr hs hso
  classical
  have H := hσ (fun s => M (f s)) (fun s => Op (f s)) (fun s => K (f s)) (fun s => hr _)
    (fun s => hs _) (fun s => hso _)
  refine simpleOver_of_equiv (PiTensorProduct.reindex ℂ M f.symm) _ _ _ _ ?_ ?_ H
  · apply le_antisymm
    · rw [piKer, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, ⟨i, hi⟩, rfl⟩, rfl⟩
      obtain ⟨s, rfl⟩ := f.surjective i
      exact Submodule.subset_span ⟨fun s => y (f s), ⟨s, hi⟩, by simp⟩
    · rw [piKer, Submodule.span_le]
      rintro _ ⟨z, ⟨s, hz⟩, rfl⟩
      refine ⟨PiTensorProduct.tprod ℂ (Equiv.piCongrLeft M f z),
        Submodule.subset_span ⟨_, ⟨f s, by simpa using hz⟩, rfl⟩, ?_⟩
      simp
  · rintro _ ⟨s, g, hg, rfl⟩
    refine ⟨piOp (f s) g, ⟨f s, g, hg, rfl⟩, fun x => ?_⟩
    have hu : (Function.update (fun j => (LinearMap.id : M (f j) →ₗ[ℂ] M (f j))) s g) =
        fun j => Function.update (fun i => (LinearMap.id : M i →ₗ[ℂ] M i)) (f s) g (f.symm.symm j) := by
      funext j
      by_cases h : j = s
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact (Function.update_of_ne (β := fun i => M i →ₗ[ℂ] M i) (a := f j) (a' := f s)
          (fun h' => h (f.injective h')) g (fun i => LinearMap.id)).symm
    simp only [piOp, LinearEquiv.coe_coe]
    rw [hu, PiTensorProduct.map_reindex]
end GlobalTheory.PiSimple

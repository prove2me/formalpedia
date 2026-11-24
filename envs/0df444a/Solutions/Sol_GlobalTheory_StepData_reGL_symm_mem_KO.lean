-- Prove2me | solution 1 for GlobalTheory.StepData.reGL_symm_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:13.191697+00:00
-- url     : https://prove2.me/submissions/2c983a08-0242-4bd2-9bad-6205dda49547

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterPrincipalSpec
import Theorems.Thm_GlobalTheory_StepData_mem_KO


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.StepData ValuativeRel Matrix
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
theorem _root_.solution {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  have hinv : ((reGL e).symm g)⁻¹ = (reGL e).symm g⁻¹ := (map_inv _ _).symm
  rw [mem_KO, mem_KO, hinv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 (e i) (e j), fun i j => h2 (e i) (e j)⟩
end GlobalTheory.StepData

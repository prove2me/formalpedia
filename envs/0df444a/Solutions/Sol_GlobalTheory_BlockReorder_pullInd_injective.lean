-- Prove2me | solution 1 for GlobalTheory.BlockReorder.pullInd_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:02:48.611752+00:00
-- url     : https://prove2.me/submissions/5df53803-7009-4297-a483-d40df144d556

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open GlobalTheory GlobalTheory.BlockReorder
variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {W : Type} [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.BlockReorder
theorem _root_.solution (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W) :
    Function.Injective (pullInd e ρ) := by
  intro f f' h
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  obtain ⟨y, rfl⟩ := (glIso k e).surjective x
  exact congrFun (congrArg (fun F : IndSp _ _ => F.1.1) h) y
end GlobalTheory.BlockReorder

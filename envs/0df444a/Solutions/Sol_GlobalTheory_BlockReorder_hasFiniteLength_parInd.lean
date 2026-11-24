-- Prove2me | solution 1 for GlobalTheory.BlockReorder.hasFiniteLength_parInd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:27.722456+00:00
-- url     : https://prove2.me/submissions/db8274ff-ac26-4839-b2d5-9abe3e5b4b6b

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
import Theorems.Thm_GlobalTheory_BlockReorder_pullInd_injective
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_of_injective
import Theorems.Thm_GlobalTheory_SmGL_hasFiniteLength_comp_iff


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
theorem _root_.solution (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) W)
    (h : HasFiniteLength (parInd (finSigmaFinEquiv : (Σ i, Fin (blockSize m i)) ≃ _) (ρ.comp (leviMap k e)))) :
    HasFiniteLength (parInd e ρ) := by
  have h1 : HasFiniteLength ((parInd e ρ).comp (glIso k e).toMonoidHom) :=
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (pullMap e ρ))
      (fun x y hxy => pullInd_injective e ρ hxy)
  exact (hasFiniteLength_comp_iff _ _ (glIso k e).surjective).1 h1
end GlobalTheory.BlockReorder

-- Prove2me | solution 1 for GlobalTheory.BlockReorder.continuous_leviMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:01.653652+00:00
-- url     : https://prove2.me/submissions/8833d330-ad83-4bbf-8f1f-6f009db39296

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IrreducibleAdmissibleGL_69e19a0de021488a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__StandardFunctorsFiniteLength_93eb2991d501e04b
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeviBlocksParabolicInductionFiniteLength
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_continuous_leviEmb


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
variable (R : Type) [CommRing R]
variable {R}
variable (R)
variable {R}
namespace GlobalTheory.BlockReorder
theorem _root_.solution [TopologicalSpace R] [IsTopologicalRing R] (e : (Σ a, m a) ≃ n) :
    Continuous (leviMap R e) := by
  refine continuous_pi fun a => Units.continuous_iff.2 ⟨continuous_matrix fun x y => ?_,
    continuous_matrix fun x y => ?_⟩
  · exact (Units.continuous_val.comp (continuous_leviEmb R _)).matrix_elem _ _
  · have : ∀ g : Levi R (fun i => Fin (blockSize m i)), (((leviMap R e g a)⁻¹ : GL (m a) R) : Matrix _ _ R) x y =
        (((leviEmb R finSigmaFinEquiv g)⁻¹ : GL _ R) : Matrix _ _ R) ((stdIdx e).symm (e ⟨a, x⟩))
          ((stdIdx e).symm (e ⟨a, y⟩)) := fun g => by
      rw [← Pi.inv_apply, ← map_inv, leviMap_apply, map_inv]
    simp only [this]
    exact (Units.continuous_coe_inv.comp (continuous_leviEmb R _)).matrix_elem _ _
end GlobalTheory.BlockReorder

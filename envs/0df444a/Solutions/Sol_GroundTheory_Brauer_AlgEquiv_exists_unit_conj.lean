-- Prove2me | solution 1 for GroundTheory.Brauer.AlgEquiv.exists_unit_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:58.40541+00:00
-- url     : https://prove2.me/submissions/a2525b92-52d9-47f4-ab3e-1414f4005ddf

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
import Theorems.Thm_GroundTheory_Brauer_exists_unit_conj
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier


attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.val_of
attribute [local simp] GroundTheory.Brauer.SkolemNoether.Twist.of_val

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
open SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
  [IsSimpleRing B] [FiniteDimensional K B]
namespace GroundTheory.Brauer
namespace AlgEquiv
theorem _root_.solution (σ : A ≃ₐ[K] A) :
    ∃ a : Aˣ, ∀ x, σ x = a * x * ↑a⁻¹ := by
  obtain ⟨a, ha⟩ := GroundTheory.Brauer.exists_unit_conj (AlgHom.id K A) σ.toAlgHom
  exact ⟨a, fun x ↦ by simpa using ha x⟩
end AlgEquiv
end GroundTheory.Brauer

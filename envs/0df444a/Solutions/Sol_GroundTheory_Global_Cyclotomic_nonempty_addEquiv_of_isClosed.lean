-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.nonempty_addEquiv_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:30:51.105116+00:00
-- url     : https://prove2.me/submissions/438c8bfc-4c2d-4f41-ad47-9a65366f883f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_eq_mul_of_isClosed
import Theorems.Thm_GroundTheory_Global_Cyclotomic_ext_toPadicInt
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply



set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂))
    (hne : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h ≠ 0) : Nonempty (H ≃+ ℤ̂) := by
  obtain ⟨g, hg0, hgH⟩ := exists_eq_mul_of_isClosed H hH hne
  let f : ℤ̂ →+ H :=
    { toFun := fun a => ⟨g * a, (hgH _).2 ⟨a, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [mul_add] }
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ext_toPadicInt fun q => ?_, fun y => ?_⟩
    · have := congrArg (fun z : H => toPadicInt q (z : ℤ̂)) hab
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul] at this
      exact mul_left_cancel₀ (hg0 q) this
    · obtain ⟨a, ha⟩ := (hgH y).1 y.2
      exact ⟨a, Subtype.ext ha.symm⟩
  exact ⟨(AddEquiv.ofBijective f hf).symm⟩
end GroundTheory.Global.Cyclotomic

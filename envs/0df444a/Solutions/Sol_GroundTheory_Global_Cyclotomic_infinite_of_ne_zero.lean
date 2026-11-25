-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.infinite_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:13.610525+00:00
-- url     : https://prove2.me/submissions/a14042d5-b6ab-4255-945f-fa73d791ab7c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
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
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (H : AddSubgroup ℤ_[ℓ]) {x : ℤ_[ℓ]} (hx : x ∈ H) (hx0 : x ≠ 0) :
    (H : Set ℤ_[ℓ]).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => k • x)
    (fun a b hab => by
      simp only [nsmul_eq_mul] at hab
      exact Nat.cast_injective (mul_right_cancel₀ hx0 hab))
    fun k => H.nsmul_mem hx k
end GroundTheory.Global.Cyclotomic

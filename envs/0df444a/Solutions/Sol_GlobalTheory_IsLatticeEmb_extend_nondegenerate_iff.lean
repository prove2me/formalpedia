-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.extend_nondegenerate_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:16:27.425792+00:00
-- url     : https://prove2.me/submissions/398f32ac-0f95-4112-827e-23ce0092af2a

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Theorems.Thm_GlobalTheory_IsLatticeEmb_extend_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IsLatticeEmb.extend_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {r : ℕ}
variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']
open GlobalTheory.IsLatticeEmb
variable {φ : M →ₗ[𝓞 K] (Fin r → K)}
namespace GlobalTheory.IsLatticeEmb
theorem _root_.solution (h : IsLatticeEmb φ) (β : LinearMap.BilinForm ℤ M) :
    (h.extend β).Nondegenerate ↔ Function.Injective β := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro hn x hx
    apply h.1
    rw [map_zero]
    refine hn.1 _ fun w => ?_
    obtain ⟨n, hn0, y, hy⟩ := h.exists_zsmul w
    have := h.extend_apply β x y
    rw [hy, hx, map_zsmul, LinearMap.zero_apply, Int.cast_zero] at this
    exact (smul_eq_zero.mp this).resolve_left hn0
  · intro hβ
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun v hv => ?_
    obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
    have : x = 0 := hβ x (LinearMap.ext fun y => by
      have := h.extend_apply β x y
      rw [hx, map_zsmul, LinearMap.smul_apply, hv, smul_zero] at this
      exact_mod_cast this.symm)
    rw [this, map_zero] at hx
    exact (smul_eq_zero.mp hx.symm).resolve_left hn
end GlobalTheory.IsLatticeEmb

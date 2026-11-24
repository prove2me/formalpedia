-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.bilin_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:40.021223+00:00
-- url     : https://prove2.me/submissions/8a5df29e-5474-4905-b44d-7f0c6f58e283

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (h : IsLatticeEmb φ) {B B' : LinearMap.BilinForm ℚ (Fin r → K)}
    (hB : ∀ x y, B (φ x) (φ y) = B' (φ x) (φ y)) : B = B' := by
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨m, hm, x, hx⟩ := h.exists_zsmul v
  obtain ⟨n, hn, y, hy⟩ := h.exists_zsmul w
  have := hB x y
  simp only [hx, hy, map_zsmul, LinearMap.smul_apply] at this
  exact smul_right_injective ℚ hm (smul_right_injective ℚ hn this)
end GlobalTheory.IsLatticeEmb

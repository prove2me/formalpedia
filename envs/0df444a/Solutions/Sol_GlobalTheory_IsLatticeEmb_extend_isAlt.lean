-- Prove2me | solution 1 for GlobalTheory.IsLatticeEmb.extend_isAlt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:16:25.449902+00:00
-- url     : https://prove2.me/submissions/646454c1-aea8-45a9-bd51-9b745943d2fb

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
theorem _root_.solution (h : IsLatticeEmb φ) {β : LinearMap.BilinForm ℤ M} (hβ : ∀ x, β x x = 0) :
    (h.extend β).IsAlt := by
  intro v
  obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
  have := h.extend_apply β x x
  simp only [hx, hβ, map_zsmul, LinearMap.smul_apply, Int.cast_zero, smul_eq_zero, hn,
    false_or] at this
  exact this
end GlobalTheory.IsLatticeEmb

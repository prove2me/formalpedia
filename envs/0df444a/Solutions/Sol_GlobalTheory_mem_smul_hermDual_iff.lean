-- Prove2me | solution 1 for GlobalTheory.mem_smul_hermDual_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:42.722896+00:00
-- url     : https://prove2.me/submissions/58c3694e-f3d7-4e4c-bda7-100b177f95d4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_GlobalTheory_mem_one_fractionalIdeal_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory
theorem _root_.solution {b : FractionalIdeal (𝓞 E)⁰ E} (hb : b ≠ 0) {x : Fin r → E} :
    x ∈ (b : Submodule (𝓞 E) E) • hermDual G Λ ↔ ∀ y ∈ Λ, herm G x y ∈ b := by
  constructor
  · intro hx y hy
    refine Submodule.smul_induction_on (p := fun x => herm G x y ∈ b) hx ?_ ?_
    · intro β hβ w hw
      rw [herm_smul_left, ← mul_one b]
      exact FractionalIdeal.mul_mem_mul hβ (mem_one_fractionalIdeal_iff.2 (hw y hy))
    · intro u v hu hv
      rw [herm_add_left]
      exact (b : Submodule (𝓞 E) E).add_mem hu hv
  · intro h
    have h1 : (1 : E) ∈ b * b⁻¹ := by
      rw [mul_inv_cancel₀ hb]; exact FractionalIdeal.one_mem_one _
    rw [← one_smul E x]
    refine FractionalIdeal.mul_induction_on (C := fun t : E =>
      t • x ∈ (b : Submodule (𝓞 E) E) • hermDual G Λ) h1 ?_ ?_
    · intro β hβ γ hγ
      rw [mul_smul]
      refine Submodule.smul_mem_smul hβ fun y hy => ?_
      rw [herm_smul_left, ← mem_one_fractionalIdeal_iff, ← inv_mul_cancel₀ hb]
      exact FractionalIdeal.mul_mem_mul hγ (h y hy)
    · intro u v hu hv
      rw [add_smul]
      exact add_mem hu hv
end GlobalTheory

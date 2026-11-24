-- Prove2me | solution 1 for GlobalTheory.hermDual_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:08.736747+00:00
-- url     : https://prove2.me/submissions/fb45f14a-cf4c-4248-b11b-7922a45fc3bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Theorems.Thm_GlobalTheory_conjFrac_ne_zero
import Theorems.Thm_GlobalTheory_mem_one_fractionalIdeal_iff
import Theorems.Thm_GlobalTheory_mem_hermDual
import Theorems.Thm_GlobalTheory_mem_smul_hermDual_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc



set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open scoped nonZeroDivisors
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {G : Matrix (Fin r) (Fin r) E} {Λ Λ₁ Λ₂ : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory
theorem _root_.solution {a : FractionalIdeal (𝓞 E)⁰ E} (ha : a ≠ 0) :
    hermDual G ((a : Submodule (𝓞 E) E) • Λ) =
      (((conjFrac a)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) • hermDual G Λ := by
  ext x
  rw [mem_smul_hermDual_iff (inv_ne_zero (conjFrac_ne_zero ha)), mem_hermDual]
  constructor
  · intro h y hy
    rw [FractionalIdeal.mem_inv_iff (conjFrac_ne_zero ha)]
    intro α hα
    rw [mem_one_fractionalIdeal_iff, mul_comm, ← cc_cc α, ← herm_smul_right]
    exact h _ (Submodule.smul_mem_smul (mem_conjFrac.1 hα) hy)
  · intro h y hy
    refine Submodule.smul_induction_on (p := fun y => IsIntegral ℤ (herm G x y)) hy ?_ ?_
    · intro α hα w hw
      rw [herm_smul_right, mul_comm, ← mem_one_fractionalIdeal_iff]
      exact (FractionalIdeal.mem_inv_iff (conjFrac_ne_zero ha)).1 (h w hw) _
        (cc_mem_conjFrac.2 hα)
    · intro u v hu hv
      rw [herm_add_right]
      exact hu.add hv
end GlobalTheory

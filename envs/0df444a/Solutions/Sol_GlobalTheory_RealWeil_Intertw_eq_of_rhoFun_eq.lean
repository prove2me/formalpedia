-- Prove2me | solution 1 for GlobalTheory.RealWeil.Intertw.eq_of_rhoFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:19:42.47509+00:00
-- url     : https://prove2.me/submissions/8c6a9cff-1f41-44f2-b952-274174992252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntertwiningSymplecticAndGroupLaw
import Theorems.Thm_GlobalTheory_RealWeil_Intertw_sympl_smul_right
import Theorems.Thm_GlobalTheory_RealWeil_Intertw_sympl_antisymm
import Theorems.Thm_GlobalTheory_RealWeil_Intertw_sympl_sub_left
import Theorems.Thm_GlobalTheory_RealWeil_Intertw_eq_zero_of_exp_eq_one
import Theorems.Thm_GlobalTheory_RealWeil_Intertw_rhoFun_gaussian_ne_zero
import Theorems.Thm_GlobalTheory_RealWeil_Intertw_eq_of_smul_eq_smul
import Theorems.Thm_GlobalTheory_RealWeil_exists_schwartz_rhoFun
import Theorems.Thm_GlobalTheory_RealWeil_sympl_single
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.Intertw
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.Intertw
theorem _root_.solution {u u' : l ⊕ l → ℝ} (h : ∀ g : Sch l, rhoFun u ⇑g = rhoFun u' ⇑g) : u = u' := by
  classical
  set g0 := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l) with hg0
  have key : ∀ z : l ⊕ l → ℝ, exp (((π * (2 * sympl (u - u') z) : ℝ) : ℂ) * I) = 1 := by
    intro z
    obtain ⟨g1, hg1⟩ := exists_schwartz_rhoFun l z g0
    have h1 := h g1
    rw [hg1, rhoFun_rhoFun, rhoFun_rhoFun] at h1
    have h2 := congrArg (rhoFun z) (h g0)
    rw [rhoFun_rhoFun, rhoFun_rhoFun, add_comm z u, add_comm z u', sympl_antisymm z u, sympl_antisymm z u'] at h2
    set a := sympl u z
    set b := sympl u' z
    set F := rhoFun (u + z) ⇑g0
    set G := rhoFun (u' + z) ⇑g0
    have h3 : (exp (((π * -b : ℝ) : ℂ) * I) * exp (((π * a : ℝ) : ℂ) * I)) • F =
        (exp (((π * b : ℝ) : ℂ) * I) * exp (((π * -a : ℝ) : ℂ) * I)) • F := by
      rw [mul_smul, h1, smul_smul, mul_comm, ← smul_smul, ← h2, smul_smul, mul_smul]
    have h4 := eq_of_smul_eq_smul (rhoFun_gaussian_ne_zero (u + z)) h3
    rw [← Complex.exp_add, ← Complex.exp_add] at h4
    rw [sympl_sub_left]
    have e : ((π * (2 * (a - b)) : ℝ) : ℂ) * I =
        (((π * -b : ℝ) : ℂ) * I + ((π * a : ℝ) : ℂ) * I) - (((π * b : ℝ) : ℂ) * I + ((π * -a : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [e, Complex.exp_sub, h4, div_self (exp_ne_zero _)]
  have hz : ∀ z, sympl (u - u') z = 0 := by
    intro z
    have := eq_zero_of_exp_eq_one (2 * sympl (u - u') z) fun r => by
      have := key (r • z)
      rwa [sympl_smul_right, show 2 * (r * sympl (u - u') z) = r * (2 * sympl (u - u') z) by ring] at this
    linarith
  have hJ : Matrix.J l ℝ *ᵥ (u - u') = 0 := by
    ext b
    have := hz (Pi.single b 1)
    rw [sympl_antisymm, sympl_single] at this
    simpa using this
  have hd : u - u' = 0 := by
    have : u - u' = -((Matrix.J l ℝ * Matrix.J l ℝ) *ᵥ (u - u')) := by
      rw [Matrix.J_squared, Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
    rw [this, ← Matrix.mulVec_mulVec, hJ, Matrix.mulVec_zero, neg_zero]
  exact sub_eq_zero.mp hd
end GlobalTheory.RealWeil.Intertw

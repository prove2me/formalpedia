-- Prove2me | solution 1 for GlobalTheory.CuspRep.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:48.895805+00:00
-- url     : https://prove2.me/submissions/7e7f8ca9-af8c-43a7-b072-d089add3cafd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele
import Theorems.Thm_GlobalTheory_CuspRep_unit_ne_zero
import Theorems.Thm_GlobalTheory_CuspRep_expU_log
import Theorems.Thm_GlobalTheory_CuspRep_exists_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CuspRep
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.CuspRep
theorem _root_.solution (ψ : (ι → ℂ)ˣ →* ℂˣ) (hψ : Continuous ψ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (u : (ι → ℂ)ˣ) (B : ℝ), 1 ≤ B → ‖(u : ι → ℂ)‖ ≤ B → ‖((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ)‖ ≤ B →
      ‖((ψ u : ℂˣ) : ℂ)‖ ≤ C * B ^ N := by
  obtain ⟨L, hL⟩ := exists_lin ψ hψ
  obtain ⟨N, hN⟩ := exists_nat_ge ‖L‖
  refine ⟨Real.exp (N * Real.pi), N, (Real.exp_pos _).le, fun u B hB h1 h2 => ?_⟩
  have hl : 0 ≤ Real.log B := Real.log_nonneg hB
  have hz : ‖fun i => Complex.log ((u : ι → ℂ) i)‖ ≤ Real.pi + Real.log B := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.log_re, Complex.log_im, add_comm]
    refine add_le_add (Complex.abs_arg_le_pi _) (abs_le.2 ⟨?_, ?_⟩)
    · have e : ((u⁻¹ : (ι → ℂ)ˣ) : ι → ℂ) i = ((u : ι → ℂ) i)⁻¹ :=
        eq_inv_of_mul_eq_one_right (congrFun u.mul_inv i)
      have := Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u⁻¹ i)) ((norm_le_pi_norm _ i).trans h2)
      rw [e, norm_inv, Real.log_inv] at this
      linarith
    · exact Real.log_le_log (norm_pos_iff.2 (unit_ne_zero u i)) ((norm_le_pi_norm _ i).trans h1)
  rw [← expU_log u, hL, Complex.norm_exp]
  have h3 : (L fun i => Complex.log ((u : ι → ℂ) i)).re ≤ N * (Real.pi + Real.log B) :=
    (Complex.re_le_norm _).trans ((L.le_opNorm _).trans (mul_le_mul hN hz (norm_nonneg _) (Nat.cast_nonneg _)))
  refine (Real.exp_le_exp.2 h3).trans_eq ?_
  rw [mul_add, Real.exp_add, ← Real.log_pow, Real.exp_log (by positivity)]
end GlobalTheory.CuspRep

-- Prove2me | solution 1 for GlobalTheory.AnArc.shift_mem_Theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:15.343806+00:00
-- url     : https://prove2.me/submissions/7b350faf-c267-4a76-b705-51c9a126ffa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_H_sub_H
import Theorems.Thm_P2M_GlobalTheory_AnArc_shift_apply__29043617d48c
import Theorems.Thm_GlobalTheory_AnArc_H_smul_left
import Theorems.Thm_GlobalTheory_AnArc_ah_add


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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable (k : ℕ) [NeZero k]
variable {k}
namespace GlobalTheory.AnArc
theorem _root_.solution {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta k α) (la : A.La) :
    A.shift k la α th ∈ A.Theta k (α + la.y) := by
  have hk : (k : ℂ) ≠ 0 := NeZero.ne _
  refine ⟨?_, fun m z => ?_⟩
  · have h1 : Differentiable ℂ fun z : Fin A.gB → ℂ => A.H z la.l := by
      unfold H hermForm dotProduct; fun_prop
    have h2 := h.1
    change Differentiable ℂ fun z => eTwoPi ((A.P0 la).1 α / k) * Complex.exp (-(Real.pi * A.H z la.l)) *
      th (z + (k : ℂ)⁻¹ • (A.P0 la).2)
    fun_prop
  · have h2 := A.H_sub_H la.l m
    have h3 : Complex.exp (-(Real.pi * (A.H z la.l + A.H m la.l))) *
        Complex.exp (k * (Real.pi * ((k : ℂ)⁻¹ * (A.H (A.ct la.y) m + A.H la.l m)))) *
        Complex.exp (Real.pi * A.H (A.ct α) m) =
        Complex.exp (Real.pi * (A.H (A.ct α) m + A.H (A.ct la.y) m)) * Complex.exp (-(Real.pi * A.H z la.l)) := by
      simp only [← Complex.exp_add]
      rw [Complex.exp_eq_exp_iff_exists_int, mul_left_comm (k : ℂ), mul_inv_cancel_left₀ hk]
      exact ⟨A.Ef la.l m, by linear_combination (Real.pi : ℂ) * h2⟩
    rw [shift_apply', shift_apply', add_right_comm, h.2, ah_add, mul_pow, ← Complex.exp_nat_mul, degeneratingTori_basePeriodMap_snd,
      H_smul_left, map_add, H_add_left, H_add_left, H_add_left]
    linear_combination (eTwoPi ((A.P0 la).1 α / k) * A.ah m z ^ k * th (z + (k : ℂ)⁻¹ • (A.ct la.y + la.l))) * h3
end GlobalTheory.AnArc

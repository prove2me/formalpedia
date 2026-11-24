-- Prove2me | solution 1 for GlobalTheory.AnArc.ah_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:57:42.550499+00:00
-- url     : https://prove2.me/submissions/41f36cbf-cc6b-45ea-b829-9d92861be8d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FormalThetaSumShiftPeriodDiv
import Theorems.Thm_GlobalTheory_AnArc_H_sub_H

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
namespace GlobalTheory.AnArc
theorem _root_.solution (l m : A.abelian₂) (z : Fin A.gB → ℂ) : A.ah (l + m) z = A.ah l (z + m) * A.ah m z := by
  have h : ((hermForm A.Hm l m).im : ℂ) = ((A.Ef l m : ℤ) : ℂ) := by rw [← A.Ef_eq]; simp
  have h2 := A.H_sub_H l m
  have h3 : Complex.exp (Real.pi * Complex.I * (A.Ef l m : ℤ)) *
      Complex.exp (Real.pi * A.H z (l + m : A.abelian₂) + Real.pi / 2 * A.H (l + m : A.abelian₂) (l + m : A.abelian₂)) =
      Complex.exp (Real.pi * A.H (z + m) l + Real.pi / 2 * A.H l l) *
        Complex.exp (Real.pi * A.H z m + Real.pi / 2 * A.H m m) := by
    rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨A.Ef l m, ?_⟩
    simp only [Submodule.coe_add, H_add_left, H_add_right]
    linear_combination (Real.pi / 2 : ℂ) * h2
  rw [ah, ah, ah, A.chi_add, h, mul_assoc, h3]
  ring
end GlobalTheory.AnArc

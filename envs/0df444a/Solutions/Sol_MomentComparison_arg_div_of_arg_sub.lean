-- Prove2me | solution 1 for MomentComparison.arg_div_of_arg_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:17:37.51809+00:00
-- url     : https://prove2.me/submissions/8f6a2382-fd2c-4188-b603-8a5559ea0fc9

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Definitions.Def_MomentComparison_ComplexPower

set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0)
    (hlo : -Real.pi < x.arg - y.arg) (hhi : x.arg - y.arg ≤ Real.pi) :
    (x / y).arg = x.arg - y.arg := by
  calc
    (x / y).arg = ((↑((x / y).arg)) : Real.Angle).toReal :=
      (Complex.arg_coe_angle_toReal_eq_arg _).symm
    _ = (((x.arg - y.arg : ℝ) : Real.Angle)).toReal := by
      rw [Complex.arg_div_coe_angle hx hy, Real.Angle.coe_sub]
    _ = x.arg - y.arg := Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr ⟨hlo, hhi⟩
end MomentComparison

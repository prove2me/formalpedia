-- Prove2me | solution 1 for OAI.CubeInversion.cube_index_filter_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:30.206747+00:00
-- url     : https://prove2.me/submissions/a921f937-2848-448f-af85-8ba8bb72df65

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.CubeInversion
namespace OAI.CubeInversion
theorem _root_.solution (m : ℕ) :
    (∑ h ∈ m.divisors, (ArithmeticFunction.moebius h : ℂ)) =
      if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact_mod_cast h
end OAI.CubeInversion

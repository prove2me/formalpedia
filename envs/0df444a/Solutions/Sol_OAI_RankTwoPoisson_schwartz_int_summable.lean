-- Prove2me | solution 1 for OAI.RankTwoPoisson.schwartz_int_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:45.088506+00:00
-- url     : https://prove2.me/submissions/dd5f14f6-1e33-4256-9a04-b073c13adb19

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization

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
open OAI.RankTwoPoisson
open Real
namespace OAI.RankTwoPoisson
theorem _root_.solution (f : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
end OAI.RankTwoPoisson

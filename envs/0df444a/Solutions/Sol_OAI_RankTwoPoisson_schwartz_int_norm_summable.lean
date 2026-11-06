-- Prove2me | solution 1 for OAI.RankTwoPoisson.schwartz_int_norm_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:34.168219+00:00
-- url     : https://prove2.me/submissions/87b09af9-07fa-4f76-9672-a0f3d8229d6e

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_RankTwoPoisson_schwartz_int_summable

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
    Summable (fun n : ℤ => ‖f (n : ℝ)‖) :=
  (schwartz_int_summable f).norm
end OAI.RankTwoPoisson

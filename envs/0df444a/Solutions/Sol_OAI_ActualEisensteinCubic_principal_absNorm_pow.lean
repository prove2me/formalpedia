-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.principal_absNorm_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:45:55.081193+00:00
-- url     : https://prove2.me/submissions/77168317-e41c-4539-9e7f-a434f09f610f

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit

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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (p : O) (k : ℕ) :
    Ideal.absNorm (Ideal.span {p ^ k}) =
      (Ideal.absNorm (Ideal.span {p})) ^ k := by
  rw [← Ideal.span_singleton_pow]
  exact map_pow Ideal.absNorm (Ideal.span {p}) k
end OAI.ActualEisensteinCubic

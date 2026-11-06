-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveGamma2_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:17.94334+00:00
-- url     : https://prove2.me/submissions/6dbfa7f1-976a-4229-9c8e-9a4fd9f4224b

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicGauss_normalized_cube_breveE
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_pow_two

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
open EisensteinEmbedding ConcreteTraceCRT
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (breveGamma2 P hgood p hP hp) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  unfold breveGamma2
  rw [canonicalSextic_pow_two]
  exact cubicGauss_normalized_cube_breveE P hgood p hP hp hprimary
end OAI.ActualEisensteinCubic

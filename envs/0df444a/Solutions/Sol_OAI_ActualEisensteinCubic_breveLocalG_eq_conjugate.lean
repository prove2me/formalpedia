-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveLocalG_eq_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:34.106853+00:00
-- url     : https://prove2.me/submissions/f9b27bdb-2c6a-4ae3-aa95-f96cc66a22f4

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_inverse_eq_conj_on_units

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
open ConcreteTraceCRT
open scoped ComplexConjugate
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    breveLocalG P hgood p hP hp =
      star (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O))) *
        breveGamma3 P hgood p hP hp := by
  have htwo : (2 : O ⧸ P) ≠ 0 := Ring.two_ne_zero hchar
  have hfour : (4 : O ⧸ P) ≠ 0 := by
    convert pow_ne_zero 2 htwo using 1 ; norm_num
  have hunit : IsUnit (4 : O ⧸ P) := isUnit_iff_ne_zero.mpr hfour
  let u : (O ⧸ P)ˣ := hunit.unit
  have hu : (u : O ⧸ P) = Ideal.Quotient.mk P (4 : O) := hunit.unit_spec
  unfold breveLocalG
  rw [← hu, canonicalSextic_inverse_eq_conj_on_units P hgood u]
end OAI.ActualEisensteinCubic

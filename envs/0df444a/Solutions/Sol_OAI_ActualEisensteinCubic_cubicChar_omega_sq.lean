-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicChar_omega_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:24:26.949209+00:00
-- url     : https://prove2.me/submissions/302c4ec2-349c-43fb-868f-0219eb318004

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_omega

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
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (omega ^ 2)) =
      omega ^ (2 * ((Nat.card (O ⧸ P) - 1) / 3)) := by
  rw [map_pow, map_pow, cubicChar_omega P hgood]
  ring
end OAI.ActualEisensteinCubic

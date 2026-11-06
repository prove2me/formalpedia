-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.algebraNorm_eq_coordinate_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:10.079503+00:00
-- url     : https://prove2.me/submissions/cf4c6196-a91a-49df-86d6-ab55699856bb

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_coordinate_norm_eq_mul_conjO
import Theorems.Thm_OAI_ActualEisensteinCubic_norm_int_eq_mul_conjO


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
open ActualEisensteinCoordinates ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (p : O) :
    Algebra.norm ℤ p = q (coords p) := by
  have h := (norm_int_eq_mul_conjO p).trans
    (coordinate_norm_eq_mul_conjO p).symm
  exact_mod_cast h
end OAI.ActualEisensteinCubic

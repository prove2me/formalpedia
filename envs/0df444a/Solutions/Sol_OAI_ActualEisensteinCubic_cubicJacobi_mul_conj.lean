-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.cubicJacobi_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:03.773191+00:00
-- url     : https://prove2.me/submissions/b48b063e-9983-4b98-ac70-7c685ff0c764

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_product
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicJacobi_conj

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
open OAI.ActualEisensteinCubic
open NumberField
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
        (Nat.card (O ⧸ P) : O) := by
  rw [cubicJacobi_conj P hgood]
  exact cubicJacobi_product P hgood
end OAI.ActualEisensteinCubic

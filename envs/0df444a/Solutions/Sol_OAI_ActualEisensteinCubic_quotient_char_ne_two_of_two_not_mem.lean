-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quotient_char_ne_two_of_two_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:03.952436+00:00
-- url     : https://prove2.me/submissions/a4f07261-6bfc-4ece-ae21-428dabb1b22f

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

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
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa only [map_ofNat, Nat.cast_ofNat] using hz)
end OAI.ActualEisensteinCubic

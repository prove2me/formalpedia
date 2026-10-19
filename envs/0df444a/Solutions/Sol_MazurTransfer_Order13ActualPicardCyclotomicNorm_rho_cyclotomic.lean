-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardCyclotomicNorm.rho_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T17:38:34.327999+00:00
-- url     : https://prove2.me/submissions/520d363d-ab0b-41fd-b3ca-d426e84bcbf2

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original literal arithmetic Picard cyclotomic contract and proof retained,
using the accepted public diamond-square and diamond-cube trace interfaces.
Design boundary: the actual arithmetic Picard diamond satisfies rho^2-rho+1=0.
Named downstream consumer: literal nineteen norm and original rational descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondTraceArithmeticData

noncomputable section
open MazurTransfer
open Order13ActualDiamondPicardEndomorphisms
namespace MazurTransfer.ActualPicardCyclotomicPublicHelpers20261017
theorem rho_cube_apply (c : ActualPicard) : (rho ^ 3) c = -c :=
  eq_neg_of_add_eq_zero_right (MazurTransfer.Order13ActualPicardDiamondTrace.hyperelliptic_trace_zero c)

theorem rho_pow_three : rho ^ 3 = -1 := by
  apply AddMonoidHom.ext
  intro c
  exact rho_cube_apply c

theorem rho_fourth_apply (c : ActualPicard) : (rho ^ 4) c = -rho c := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ]
  exact rho_cube_apply (rho c)

theorem rho_square_apply (c : ActualPicard) : (rho ^ 2) c = rho c - c := by
  have h := MazurTransfer.Order13ActualPicardDiamondTrace.order_three_trace_zero c
  rw [rho_fourth_apply] at h
  apply eq_of_sub_eq_zero
  calc
    (rho ^ 2) c - (rho c - c) = c + (rho ^ 2) c + -rho c := by abel
    _ = 0 := h

end MazurTransfer.ActualPicardCyclotomicPublicHelpers20261017

theorem solution : rho ^ 2 - rho + 1 = 0 := by
  apply AddMonoidHom.ext
  intro c
  change (rho ^ 2) c - rho c + c = 0
  rw [MazurTransfer.ActualPicardCyclotomicPublicHelpers20261017.rho_square_apply]
  abel


#print axioms solution

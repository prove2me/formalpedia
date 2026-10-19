-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardCyclotomicNorm.pi_comp_piConjugate_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T17:44:21.667058+00:00
-- url     : https://prove2.me/submissions/ed7a5ae3-b825-4036-8196-6549fa1bf1ec

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original full pi*piConjugate=nineteen contract and main calculation retained.
The square relation is derived explicitly from the public cyclotomic identity.
Design boundary: the two original arithmetic Picard endomorphisms compose to
scalar nineteen. Named downstream consumer: original norm-kernel and descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardCyclotomicNorm_rho_cyclotomic

noncomputable section
open MazurTransfer
open Order13ActualDiamondPicardEndomorphisms
namespace MazurTransfer.ActualPicardNormProductPublicHelpers20261017
theorem rho_square_apply (c : ActualPicard) : (rho ^ 2) c = rho c - c := by
  have h := congrArg (fun f : AddMonoid.End ActualPicard => f c) MazurTransfer.Order13ActualPicardCyclotomicNorm.rho_cyclotomic
  change (rho ^ 2) c - rho c + c = 0 at h
  apply sub_eq_zero.mp
  calc
    (rho ^ 2) c - (rho c - c) = (rho ^ 2) c - rho c + c := by abel
    _ = 0 := h
end MazurTransfer.ActualPicardNormProductPublicHelpers20261017

theorem solution : pi * piConjugate = 19 := by
  rw [pi_comp_piConjugate]
  apply AddMonoidHom.ext
  intro c
  change (15 : ℕ) • c + (4 : ℕ) • rho c - (4 : ℕ) • (rho ^ 2) c = (19 : ℕ) • c
  rw [MazurTransfer.ActualPicardNormProductPublicHelpers20261017.rho_square_apply]
  abel


#print axioms solution

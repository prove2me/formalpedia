-- Prove2me | solution 1 for MazurTransfer.order13_actual_rational_rho_square_apply
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T19:18:43.640269+00:00
-- url     : https://prove2.me/submissions/2058ba0e-57cf-47e4-8ebc-ec0cb07ab7aa

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardCyclotomicNorm_pi_comp_piConjugate_nineteen
import Theorems.Thm_MazurTransfer_order13_actual_rational_picard_torsion_cardinality_nineteen
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT arithmetic Picard interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the exact original rational diamond quadratic relation follows from the accepted norm identity and full rational torsion count. Named downstream consumer: the infinity-class eigenvalue and actual norm-kernel ordering. No rational rank hypothesis is used.
-/
noncomputable section
open MazurTransfer.Order13ActualDiamondPicardEndomorphisms

theorem solution (c : ActualPicard) : (rho ^ 2) c = rho c - c := by
  obtain ⟨hf, hcard⟩ := MazurTransfer.order13_actual_rational_picard_torsion_cardinality_nineteen
  let T := CommGroup.torsion (Multiplicative ActualPicard)
  change Finite T at hf
  change Nat.card T = 19 at hcard
  let : Finite T := hf
  have no_four_torsion (d : ActualPicard) (hd4 : (4 : ℕ) • d = 0) : d = 0 := by
    have hmem : Multiplicative.ofAdd d ∈ CommGroup.torsion (Multiplicative ActualPicard) := by
      rw [CommGroup.mem_torsion]
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨4, by decide, ?_⟩
      change Multiplicative.ofAdd ((4 : ℕ) • d) = Multiplicative.ofAdd 0
      exact congrArg Multiplicative.ofAdd hd4
    let t : T := ⟨Multiplicative.ofAdd d, hmem⟩
    have ht19 : t ^ 19 = 1 := by
      simpa only [hcard] using (pow_card_eq_one' (x := t))
    have h19 := congrArg Subtype.val ht19
    change Multiplicative.ofAdd ((19 : ℕ) • d) = Multiplicative.ofAdd 0 at h19
    have hd19 : (19 : ℕ) • d = 0 := congrArg Multiplicative.toAdd h19
    have hd20 : (20 : ℕ) • d = 0 := by
      rw [show (20 : ℕ) = 4 * 5 by decide, mul_nsmul, hd4, nsmul_zero]
    have h : (19 + 1 : ℕ) • d = 0 := hd20
    rwa [add_nsmul, hd19, one_nsmul, zero_add] at h
  have heq := congrArg (fun f : AddMonoid.End ActualPicard => f c)
    (pi_comp_piConjugate.symm.trans
      MazurTransfer.Order13ActualPicardCyclotomicNorm.pi_comp_piConjugate_nineteen)
  change (15 : ℕ) • c + (4 : ℕ) • rho c - (4 : ℕ) • (rho ^ 2) c = (19 : ℕ) • c at heq
  let y := (rho ^ 2) c - (rho c - c)
  have hy : (4 : ℕ) • y = (19 : ℕ) • c -
      ((15 : ℕ) • c + (4 : ℕ) • rho c - (4 : ℕ) • (rho ^ 2) c) := by
    dsimp [y]
    simp only [nsmul_sub]
    abel
  rw [heq, sub_self] at hy
  have hy0 := no_four_torsion y hy
  exact sub_eq_zero.mp hy0
#print axioms solution

-- Prove2me | solution 1 for MazurTransfer.Order13ArithmeticNormKernelCardinality.actual_arithmetic_norm_kernel_card_product
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T18:03:30.44498+00:00
-- url     : https://prove2.me/submissions/7ed802ab-1542-4e11-bc4a-4a1cfb6f312d

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualDiamondPicardEndomorphismsExplicitPublicOrderCertificate20261017
import Theorems.Thm_MazurTransfer_nineteen_norm_rational_kernel_card_product
import Theorems.Thm_MazurTransfer_Order13ActualPicardCyclotomicNorm_pi_comp_piConjugate_nineteen
import Theorems.Thm_MazurTransfer_order13_actual_rational_picard_torsion_cardinality_nineteen
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: compute the two arithmetic norm-kernel cardinalities from the full rational Picard torsion cardinality and the original norm identities. Named downstream consumer: rational Picard norm-kernel ordering and the actual Galois fixed-part computation. Original MazurTheorem source and official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
noncomputable section
open MazurTransfer.Order13ActualDiamondPicardEndomorphisms

theorem solution :
    Finite pi.ker ∧ Finite piConjugate.ker ∧ Nat.card pi.ker * Nat.card piConjugate.ker = 19 := by
  have hsum (x : ActualPicard) : pi x + piConjugate x = (8 : ℕ) • x := by
    change ((3 : ℕ) • x + (2 : ℕ) • rho x) +
      ((5 : ℕ) • x - (2 : ℕ) • rho x) = (8 : ℕ) • x
    abel
  obtain ⟨hf, hc⟩ :=
    MazurTransfer.order13_actual_rational_picard_torsion_cardinality_nineteen
  have hgf : piConjugate * pi = 19 :=
    piConjugate_comp_pi.trans (pi_comp_piConjugate.symm.trans
      MazurTransfer.Order13ActualPicardCyclotomicNorm.pi_comp_piConjugate_nineteen)
  obtain ⟨hfπ, hfπc, hprod, _⟩ := MazurTransfer.nineteen_norm_rational_kernel_card_product ActualPicard hf hc pi piConjugate
    (fun x => congrArg (fun h : AddMonoid.End ActualPicard => h x)
      MazurTransfer.Order13ActualPicardCyclotomicNorm.pi_comp_piConjugate_nineteen)
    (fun x => congrArg (fun h : AddMonoid.End ActualPicard => h x) hgf) hsum
  exact ⟨hfπ, hfπc, hprod⟩
#print axioms solution

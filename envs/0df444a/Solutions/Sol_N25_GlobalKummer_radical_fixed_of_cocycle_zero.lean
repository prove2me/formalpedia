-- Prove2me | solution 1 for N25.GlobalKummer.radical_fixed_of_cocycle_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:46.968367+00:00
-- url     : https://prove2.me/submissions/2a8f8322-a8f5-4e46-b00d-99bdd961a612

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

/-- Vanishing of a cyclotomic cocycle value fixes its actual Kummer radical. -/
theorem _root_.solution
    (c : groupCohomology.cocycles₁ cyclotomicRep)
    (e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)))
    (α : (AlgebraicClosure ℚ)ˣ)
    (hc : ∀ σ : Gal, (Additive.toMul (e (c σ))).val =
      groupCohomology.Kummer.kummerCocycle α σ)
    (σ : Gal) (hσ : c σ = 0) : σ (α : AlgebraicClosure ℚ) = α := by
  have h := hc σ
  rw [hσ, map_zero] at h
  have hu := congrArg (fun z : (AlgebraicClosure ℚ)ˣ => z * α) h.symm
  have heq : σ • α = α := by
    simpa [groupCohomology.Kummer.kummerCocycle, div_eq_mul_inv, mul_assoc] using hu
  exact congrArg (fun z : (AlgebraicClosure ℚ)ˣ => (z : AlgebraicClosure ℚ)) heq

end N25.GlobalKummer

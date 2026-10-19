-- Prove2me | solution 1 for MazurTransfer.Order13LocalRingInValuationSubring.local_coefficients_mem
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T03:43:24.066798+00:00
-- url     : https://prove2.me/submissions/b87d8f30-b7f1-4860-b0be-9510d30fe08c

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the canonical local integer coefficient ring is contained
in every valuation subring lying over the specified rational prime.
Named downstream consumer: inertia fixed lifts for integral order-13 norms.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps
import Theorems.Thm_MazurTransfer_Order13LocalRingInValuationSubring_integer_maximalIdeal_comap
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.RingTheory.Ideal.Int

noncomputable section
open MazurTransfer
open Order13LocalIntegralCoefficientMaps
theorem solution (q : ℕ) [Fact q.Prime] {Ω : Type} [Field Ω]
    [Algebra (LocalRing q) Ω] (A : ValuationSubring Ω) (hA : A.LiesOverPrime q)
    (r : LocalRing q) : algebraMap (LocalRing q) Ω r ∈ A := by
  have hu : ∀ s : (primeIdeal q).primeCompl, IsUnit ((Int.castRingHom A) s) := by
    intro s
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hs
    have hm : (Int.castRingHom A) s ∈ IsLocalRing.maximalIdeal A := hs
    have hi : (s : ℤ) ∈ (IsLocalRing.maximalIdeal A).comap (Int.castRingHom A) := hm
    rw [MazurTransfer.Order13LocalRingInValuationSubring.integer_maximalIdeal_comap q A hA] at hi
    exact s.property hi
  let ρ : LocalRing q →+* A := IsLocalization.lift hu
  have he : (algebraMap A Ω).comp ρ = algebraMap (LocalRing q) Ω := by
    apply IsLocalization.ringHom_ext (primeIdeal q).primeCompl
    exact Subsingleton.elim _ _
  have hr : ((ρ r : A) : Ω) = algebraMap (LocalRing q) Ω r := RingHom.congr_fun he r
  rw [← hr]
  exact (ρ r).property

#print axioms solution

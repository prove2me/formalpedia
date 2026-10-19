-- Prove2me | solution 1 for MazurTransfer.FiniteDivisorialPairingPerfectOfInjective.perfect_of_toHom_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T08:20:51.829257+00:00
-- url     : https://prove2.me/submissions/5c460603-cdd0-4416-b900-810e248560f8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the checked finite-character bound from Anthropic FLT,
pin 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: on finite divisor-class torsion, injectivity of a
divisorial pairing's character map implies perfection.
Named downstream consumer: perfection of the actual order-13 curve's
nineteen-pairing from the divisibility-based injectivity theorem.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
noncomputable section
namespace MazurTransfer.FiniteDivisorialPairingPerfectProofHelpers20261018
open scoped Classical
scoped instance finite_monoidHom_units (G : Type*) [CommGroup G] [Finite G] (K : Type*) [Field K] : Finite (G →* Kˣ) := by
  classical
  haveI := Fintype.ofFinite G
  have hexp : 0 < Monoid.exponent G := Monoid.exponent_pos.mpr Monoid.ExponentExists.of_finite
  let n : ℕ+ := ⟨Monoid.exponent G, hexp⟩
  let F : (G →* Kˣ) → (G → rootsOfUnity n K) := fun χ g =>
    ⟨χ g, by
      rw [mem_rootsOfUnity]
      show (χ g) ^ Monoid.exponent G = 1
      rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]⟩
  refine Finite.of_injective F fun χ χ' h => ?_
  ext g
  have := congrArg (fun f => ((f g : rootsOfUnity n K) : Kˣ)) h
  exact congrArg Units.val this

theorem natCard_monoidHom_units_le (G : Type*) [CommGroup G] [Finite G] (K : Type*) [Field K] :
    Nat.card (G →* Kˣ) ≤ Nat.card G := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite (G →* Kˣ)

  let ι : (G →* Kˣ) → (G →* K) := fun χ => (Units.coeHom K).comp χ
  have hι : Function.Injective ι := by
    intro χ χ' h; ext g
    have := DFunLike.congr_fun h g
    exact this
  have hli : LinearIndependent K (fun χ : G →* Kˣ => ((ι χ : G →* K) : G → K)) :=
    (linearIndependent_monoidHom G K).comp ι hι
  have h1 := hli.fintype_card_le_finrank
  rw [Module.finrank_pi K, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h1
  exact h1


end MazurTransfer.FiniteDivisorialPairingPerfectProofHelpers20261018
open AlgebraicCurve
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F] {n : ℕ} [NeZero n]
variable [Finite (Pic0.torsion K F n)]

theorem solution (e : DivisorialWeilPairingData K F n)
    (hi : Function.Injective e.toHom) : e.Perfect := by
  let E : Additive (HomPic0Gm K F n) ≃
      (Multiplicative (Pic0.torsion K F n) →* Kˣ) :=
    (Additive.toMul : Additive (HomPic0Gm K F n) ≃ HomPic0Gm K F n).trans
      (AddChar.toMonoidHomEquiv.trans MonoidHom.toHomUnitsMulEquiv.toEquiv)
  letI : Finite (Multiplicative (Pic0.torsion K F n) →* Kˣ) :=
    MazurTransfer.FiniteDivisorialPairingPerfectProofHelpers20261018.finite_monoidHom_units _ K
  letI : Finite (Additive (HomPic0Gm K F n)) := Finite.of_equiv _ E.symm
  have hc : Nat.card (Additive (HomPic0Gm K F n)) ≤ Nat.card (Pic0.torsion K F n) := by
    rw [Nat.card_congr E]
    have hc := MazurTransfer.FiniteDivisorialPairingPerfectProofHelpers20261018.natCard_monoidHom_units_le
      (Multiplicative (Pic0.torsion K F n)) K
    rw [Nat.card_congr
      (Multiplicative.toAdd : Multiplicative (Pic0.torsion K F n) ≃ Pic0.torsion K F n)] at hc
    exact hc
  exact hi.bijective_of_nat_card_le hc

#print axioms solution

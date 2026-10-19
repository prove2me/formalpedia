-- Prove2me | solution 1 for MazurTransfer.FiniteNondegeneratePairingAdjointKernels.natCard_adjoint_kernels_eq_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T12:17:01.722055+00:00
-- url     : https://prove2.me/submissions/bff2bc43-d345-4223-84b3-f5eea6c46079

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses complete checked finite-character and adjoint-kernel proofs from
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a finite nondegenerate bilinear unit-valued pairing
supplies every character, so its adjoint endomorphisms have equally
sized kernels without a supplied character-surjectivity premise.
Named downstream consumer: equality of the two actual order-13 Picard
norm-kernel cardinalities under the constructed perfect pairing.
-/
import Mathlib
import Theorems.Thm_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint
noncomputable section
namespace MazurTransfer.FiniteNondegenerateAdjointKernelProofHelpers20261018
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



variable {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]

theorem character_surjective_of_nondegenerate
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
    (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hright : ∀ y, (∀ x, e x y = 1) → y = 0) :
    ∀ χ : Multiplicative P →* Kˣ, ∃ y, ∀ x, e x y = χ (Multiplicative.ofAdd x) := by
  letI : Finite (Multiplicative P →* Kˣ) := finite_monoidHom_units _ K
  let cr : P → (Multiplicative P →* Kˣ) := fun y =>
    { toFun := fun x => e x.toAdd y
      map_one' := by
        change e 0 y = 1
        have h := hadd₁ 0 0 y
        rw [zero_add] at h
        exact mul_eq_left.mp h.symm
      map_mul' := fun x x' => hadd₁ x.toAdd x'.toAdd y }
  have hi : Function.Injective cr := by
    intro y y' h
    have hz : ∀ x, e x (y - y') = 1 := by
      intro x
      have hh : e x y = e x y' := DFunLike.congr_fun h (Multiplicative.ofAdd x)
      have ha := hadd₂ x (y - y') y'
      rw [sub_add_cancel, hh] at ha
      exact mul_eq_right.mp ha.symm
    exact sub_eq_zero.mp (hright _ hz)
  have hc : Nat.card (Multiplicative P →* Kˣ) ≤ Nat.card P := by
    have hc := natCard_monoidHom_units_le (Multiplicative P) K
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative P ≃ P)] at hc
    exact hc
  have hs := (hi.bijective_of_nat_card_le hc).2
  intro χ
  obtain ⟨y, hy⟩ := hs χ
  exact ⟨y, fun x => DFunLike.congr_fun hy (Multiplicative.ofAdd x)⟩

end MazurTransfer.FiniteNondegenerateAdjointKernelProofHelpers20261018

theorem solution {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
    (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0)
    (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (T T' : P →+ P) (hadj : ∀ x y, e (T x) y = e x (T' y)) :
    Nat.card T.ker = Nat.card T'.ker :=
  AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint e hadd₁ hadd₂ hleft hright
    (MazurTransfer.FiniteNondegenerateAdjointKernelProofHelpers20261018.character_surjective_of_nondegenerate e hadd₁ hadd₂ hright) T T' hadj

#print axioms solution

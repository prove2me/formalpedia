-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrExt.invol_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:07.079798+00:00
-- url     : https://prove2.me/submissions/84712a50-9f30-440f-a583-b8becc4f0014

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrExt
namespace GlobalTheory.UnitLemma.UnrExt
theorem _root_.solution {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p] {q : ℕ}
    (hq : Nat.card k = q ^ 2) (s : k ≃+* k) (hss : ∀ x, s (s x) = x) (hne : ∃ x, s x ≠ x) :
    (∃ f, q = p ^ f) ∧ ∀ x, s x = x ^ q := by
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let σ : k ≃ₐ[ZMod p] k := AlgEquiv.ofRingEquiv (f := s) (fun x => by
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective x
    simp)
  obtain ⟨⟨j, hj⟩, e⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) k).2 σ
  have ho := FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) k
  simp only at e
  have h2 : FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ (2 * j) = 1 := by
    rw [mul_comm, pow_mul, e]
    ext x
    exact hss x
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [ho] at hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hne
    apply hx
    have : σ x = x := by rw [← e]; simp
    exact this
  have hn : Module.finrank (ZMod p) k = 2 * j := by
    obtain ⟨m, hm⟩ := hdvd
    have : m = 1 := by
      rcases m with _ | _ | m
      · omega
      · rfl
      · nlinarith
    rw [hm, this, mul_one]
  have hc : Nat.card k = p ^ (2 * j) := by
    rw [← hn, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hqp : q = p ^ j := by
    rw [hc, mul_comm, pow_mul] at hq
    exact (Nat.pow_left_injective two_ne_zero hq).symm
  refine ⟨⟨j, hqp⟩, fun x => ?_⟩
  have h3 : σ x = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) k ^ j) x := by rw [e]
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card] at h3
  rw [hqp]
  exact h3
end GlobalTheory.UnitLemma.UnrExt

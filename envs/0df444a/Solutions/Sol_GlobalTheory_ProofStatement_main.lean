-- Prove2me | solution 1 for GlobalTheory.ProofStatement.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:39.431723+00:00
-- url     : https://prove2.me/submissions/826d6c1b-0f20-4468-b6c1-32ee81969c38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsBisAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProofStatement
namespace GlobalTheory.ProofStatement
theorem _root_.solution : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by
  intro l hl a ha
  set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK
  haveI : FiniteDimensional (ZMod l) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l
  obtain ⟨n, _, hcard⟩ := FiniteField.card K l
  have ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0 := by
    intro h; apply ha; exact congrArg Subtype.val h
  have hpow := FiniteField.pow_card_sub_one_eq_one _ ha'
  have hl1 : 2 ≤ l := hl.out.two_le
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hq : l ≤ l ^ (n : ℕ) := Nat.le_self_pow (by omega) l
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · rw [hcard]
    intro hd
    have h2 : l ∣ l ^ (n : ℕ) := dvd_pow_self l (by omega)
    have h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h2 hd
    rw [Nat.sub_sub_self (by omega)] at h3
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h3)
  · have := congrArg Subtype.val hpow
    simpa using this
end GlobalTheory.ProofStatement

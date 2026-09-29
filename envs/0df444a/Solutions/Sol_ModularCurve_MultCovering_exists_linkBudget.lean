-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_linkBudget
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7ac569df-4280-5830-9c11-08110cee7d06

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringLink
import Theorems.Thm_ValuationSubring_exists_uniform_pow_mul_mem_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_linkBudget
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ i j, (p : AlgebraicClosure ℚ) ^ B * linkMatrix Φ s hs i j ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ B * linkMatrixInv Φ s hs i j ∈ A :=
  by
  classical
  have hW : ∀ x : AlgebraicClosure ℚ, ∃ b : ℕ, ∀ n, b ≤ n → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime p → (p : AlgebraicClosure ℚ) ^ n * x ∈ A := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, fun n _ A _ => by rw [hx, mul_zero]; exact zero_mem _⟩
    · obtain ⟨b, hb⟩ := ValuationSubring.exists_uniform_pow_mul_mem_of_liesOverPrime (Fact.out : p.Prime) hx
      refine ⟨b, fun n hn A hA => ?_⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, mul_comm ((p : AlgebraicClosure ℚ) ^ b), mul_assoc]
      exact mul_mem (pow_mem (natCast_mem A p) m) (hb A hA).1
  choose b hb using hW
  let f₁ : Fin r × Fin r → ℕ := fun ij => b (linkMatrix Φ s hs ij.1 ij.2)
  let f₂ : Fin r × Fin r → ℕ := fun ij => b (linkMatrixInv Φ s hs ij.1 ij.2)
  refine ⟨Finset.univ.sup f₁ ⊔ Finset.univ.sup f₂, fun A hA i j => ⟨?_, ?_⟩⟩
  · have h1 : f₁ (i, j) ≤ Finset.univ.sup f₁ := Finset.le_sup (Finset.mem_univ (i, j))
    exact hb _ _ (h1.trans le_sup_left) A hA
  · have h2 : f₂ (i, j) ≤ Finset.univ.sup f₂ := Finset.le_sup (Finset.mem_univ (i, j))
    exact hb _ _ (h2.trans le_sup_right) A hA

end S_ModularCurve_MultCovering_exists_linkBudget
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_linkBudget (solution)

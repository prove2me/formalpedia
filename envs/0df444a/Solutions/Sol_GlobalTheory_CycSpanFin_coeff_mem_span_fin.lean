-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.coeff_mem_span_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:00.098268+00:00
-- url     : https://prove2.me/submissions/758dc2dc-47c9-4cfd-ad3b-e3970e010eca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CycSpanFin
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} {a : ℕ → M} {p : ℂ → M}
    (hp : ∀ u, p u = ∑ i ∈ Finset.range (n + 1), u ^ i • a i) {i : ℕ} (hi : i < n + 1) :
    a i ∈ Submodule.span ℂ (Set.range fun j : Fin (n + 1) => p ((j : ℕ) : ℂ)) := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  set Q : ℂ[X] := ∑ j ∈ Finset.range (n + 1), monomial j (φ (a j)) with hQdef
  have hev : ∀ u, Q.eval u = φ (p u) := by
    intro u
    rw [hp, map_sum]
    simp only [Q, eval_finset_sum, eval_monomial]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hdeg : Q.natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  have h0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Nat.cast_injective.comp Fin.val_injective) ?_ ?_
    · intro j
      rw [hev]
      exact (Submodule.mem_dualAnnihilator φ).1 hφ _ (Submodule.subset_span ⟨j, rfl⟩)
    · simpa using Nat.lt_succ_of_le hdeg
  have := congrArg (fun P : Polynomial ℂ => P.coeff i) h0
  simpa [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, hi, Nat.lt_succ_iff.1 hi] using this
end GlobalTheory.CycSpanFin

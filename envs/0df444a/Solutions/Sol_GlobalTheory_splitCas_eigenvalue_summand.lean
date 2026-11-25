-- Prove2me | solution 1 for GlobalTheory.splitCas_eigenvalue_summand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:23:51.246352+00:00
-- url     : https://prove2.me/submissions/00ef0984-41da-485d-becb-ce0e9f8930dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SplitCasEigenvalueSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
namespace GlobalTheory
private lemma dualTens_casimir_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (x : Fin n → M) :
    ∑ a, ∑ b, dualTens E a b (dualTens E b a x)
      = (fun i => Cas E (x i)) + (n : ℂ) • x + (2 : ℂ) • splitCas E x := by
  funext i
  have h1 : ∀ a b, dualTens E a b (dualTens E b a x) i
      = E a b (E b a (x i)) - (if i = a then E a b (x b) else 0)
        - (if i = b then E b a (x a) else 0) + (if i = b then x b else 0) := by
    intro a b
    simp only [dualTens, map_sub, if_true]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  simp only [Finset.sum_apply, h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Pi.smul_apply, splitCas, Cas,
    LinearMap.sum_apply, Module.End.mul_apply]
  rw [Finset.sum_comm (f := fun a b => if i = a then E a b (x b) else 0)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_smul_eq_nsmul, two_smul]
  abel
private lemma casG_sub_single {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) :
    casG (μ - Pi.single s 1) = casG μ - 2 * μ s + 1 := by
  unfold casG
  have : ∀ a, (μ - Pi.single s 1 : Fin n → ℝ) a ^ 2 = μ a ^ 2 + (if s = a then (-2 * μ s + 1) else 0) := by
    intro a
    by_cases h : s = a
    · subst h; simp; ring
    · simp [h, Ne.symm h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring
end GlobalTheory
end

set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → ∀ s (y : N s), splitCas E (io s y) = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io s y := by
  intro M _ _ n ε E N _ _ F io pr μ hE hF hT s y
  have h1 : io s (Cas (F s) y) = ∑ a, ∑ b, dualTens E a b (dualTens E b a (io s y)) := by
    simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hT.io_comm]
  rw [dualTens_casimir_sum, (hF s).2.2, map_smul, casG_sub_single] at h1
  have h2 : (fun i => Cas E (io s y i)) = (casG μ : ℂ) • io s y := by
    funext i; rw [hE.2.2]; rfl
  rw [h2] at h1
  have h3 : splitCas E (io s y) = (1 / 2 : ℂ) • (((casG μ - 2 * μ s + 1 : ℝ) : ℂ) • io s y
      - (casG μ : ℂ) • io s y - (n : ℂ) • io s y) := by
    rw [h1]; module
  rw [h3]; push_cast; module
end GlobalTheory

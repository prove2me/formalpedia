-- Prove2me | solution 1 for OAI.KaplanskyCounterexample.MultipleHNN.of_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:38:21.679474+00:00
-- url     : https://prove2.me/submissions/762102ad-f605-4901-8713-b12ff6096f57

import Mathlib
import Definitions.Def_OAIQWKAPHNN

section
-- module Solutions.OAIQW_Kaplansky.MultiHNN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open Monoid Function
namespace KaplanskyCounterexample.MultipleHNN

universe u v
variable {H : Type u} [Group H] {I : Type v}
variable (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i)

/-- Extend any finite sublist of the required conjugacies one at a time.
Mathlib's complete Britton-lemma proof supplies the embedding at each step. -/
theorem finite_partial_realization (S : Finset I) :
    ∃ (G : Type (max u v)) (_ : Group G) (f : H →* G),
      Function.Injective f ∧ ∃ t : I → G,
        ∀ i ∈ S, ∀ a : A i, t i * f a = f (φ i a) * t i := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨ULift.{v} H, inferInstance, (MulEquiv.ulift : ULift.{v} H ≃* H).symm.toMonoidHom,
      (MulEquiv.ulift : ULift.{v} H ≃* H).symm.injective, fun _ => 1, ?_⟩
    simp
  | @insert i S hi ih =>
    obtain ⟨G, hG, f, hf, t, ht⟩ := ih
    let fA := (A i).equivMapOfInjective f hf
    let fB := (B i).equivMapOfInjective f hf
    let ψ : (A i).map f ≃* (B i).map f := fA.symm.trans ((φ i).trans fB)
    let E := HNNExtension G ((A i).map f) ((B i).map f) ψ
    let emb : G →* E := HNNExtension.of
    let t' : I → E := fun j => if j = i then HNNExtension.t else emb (t j)
    refine ⟨E, inferInstance, emb.comp f,
      (HNNExtension.of_injective ψ).comp hf, t', ?_⟩
    intro j hj a
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
      simpa [t', fA, fB, ψ, emb] using h
    · by_cases hji : j = i
      · subst j
        have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
        simpa [t', fA, fB, ψ, emb] using h
      · simpa [t', hji, ← map_mul] using congrArg emb (ht j hj a)

theorem of_injective_oai [Fintype I] : Function.Injective (of A B φ) := by
  obtain ⟨G, hG, f, hf, t, ht⟩ := finite_partial_realization A B φ Finset.univ
  intro x y h
  apply hf
  have h' := congrArg (lift A B φ f t (fun i a => ht i (Finset.mem_univ i) a)) h
  simpa using h'

end KaplanskyCounterexample.MultipleHNN
end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.KaplanskyCounterexample.MultipleHNN.of_injective_oai.{u, v} := @OAI.KaplanskyCounterexample.MultipleHNN.of_injective_oai.{u, v}

-- Prove2me | solution 1 for HardyFLocal.symmetry_determines_causaloid
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:58:59.999624+00:00
-- url     : https://prove2.me/submissions/b521ea94-79e3-4cf3-903d-b77a1ad57e22

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
import Theorems.Thm_HardyFLocal_eq21_pair_expansion
import Theorems.Thm_HardyFLocal_clumping_respects_f_locality
open HardyFLocal HardyCausaloid

theorem solution {m n : ℕ} (S : FiducialFamily)
    (L : ∀ x : X m n, Ω × Ω → Label (Setting m n) (Outcome m n) x)
    (T : X m n → X m n → PairTable)
    (E : ∀ x : X m n, Label (Setting m n) (Outcome m n) x → Ω × Ω → ℝ)
    (hE : ∀ x α, labelOp α = ∑ p : Ω × Ω, E x α p • prodOp (S.map p.1) (S.map p.2))
    (hT : ∀ x x', IsSequentialPair x x' → ∀ l' l,
      S.map l' ∘ₗ S.map l = ∑ k, T x x' l' l k • S.map k) :
    (∀ x α, E x α = elemCoeff S (labelOp α)) ∧
    (∀ x x', IsSequentialPair x x' → T x x' = pairTable S) ∧
    (∀ (x x' : X m n) (α : Label (Setting m n) (Outcome m n) x)
        (α' : Label (Setting m n) (Outcome m n) x'),
      labelOp α = labelOp α' → E x α = E x' α') ∧
    ∀ O : Finset (X m n),
      (∀ (l : ∀ x : O, omegaOne L x.1) (k : omegaC L O),
        (clumpCausaloid L T E).Λ O l k = (actualCausaloid S L).Λ O l k) ∧
      ∀ α : Lab (Setting m n) (Outcome m n) O,
        (clumpCausaloid L T E).r O α = (actualCausaloid S L).r O α := by
  have he (x : X m n) (α : Label (Setting m n) (Outcome m n) x) : E x α = elemCoeff S (labelOp α) :=
    ((eq20_two_qubit_expansion S).2 _ ((eq20_two_qubit_expansion S).1 _ (α.1.cp α.2))).2 _ (hE x α)
  have ht (x x' : X m n) (h : IsSequentialPair x x') : T x x' = pairTable S := by
    funext a b
    exact (eq21_pair_expansion S a b).2.1 _ (hT x x' h a b)
  refine ⟨he,ht,fun x x' α α' h => by rw [he, he, h],?_⟩
  intro O
  exact (clumping_respects_f_locality L T (fun _ _ => pairTable S) E
    (fun _ α => elemCoeff S (labelOp α)) O (fun x _ x' _ h => ht x x' h)
    (fun x _ => funext (he x))).2

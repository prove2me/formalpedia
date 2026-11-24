-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:57.599371+00:00
-- url     : https://prove2.me/submissions/937fd622-d388-4fc1-8d6e-05f4beb5af57

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultisetConjugateNegOfProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.REAL
namespace GlobalTheory.CompanionTheory.Clozel
private theorem neg_one_pow_card_mul_prod_neg_add_conj (u : ℂ) (s : Multiset ℂ) :
    (-1 : ℂ) ^ Multiset.card s * (s.map fun w => -u + (starRingEnd ℂ) w).prod =
      (s.map fun w => u - (starRingEnd ℂ) w).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.prod_cons, ← ih, pow_succ]
    ring
end GlobalTheory.CompanionTheory.Clozel
end

set_option autoImplicit false
open Formalism.REAL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Clozel
namespace GlobalTheory.CompanionTheory.Clozel
theorem _root_.solution :
    ∀ (n : ℕ) (m m' : Multiset ℂ), Multiset.card m = n → Multiset.card m' = n →
      (∀ u : ℂ, (m.map (u + ·)).prod =
        (starRingEnd ℂ) (((-1 : ℂ) ^ n) * (m'.map (-(starRingEnd ℂ) u + ·)).prod)) →
      m' = m.map fun z => -(starRingEnd ℂ) z := by
  intro n m m' _ hm' h
  have key : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map fun w => u - (starRingEnd ℂ) w).prod := by
    intro u
    have hc : ((starRingEnd ℂ) ∘ fun w => -(starRingEnd ℂ) u + w) =
        fun w => -u + (starRingEnd ℂ) w := by
      funext w
      simp
    rw [h u, map_mul, map_pow, map_neg, map_one, map_multiset_prod, Multiset.map_map, hc, ← hm',
      neg_one_pow_card_mul_prod_neg_add_conj]
  have hpoly : ((m.map fun z => -z).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((m'.map (starRingEnd ℂ)).map fun a => Polynomial.X - Polynomial.C a).prod := by
    apply Polynomial.funext
    intro u
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def] using key u
  have hroots := congrArg Polynomial.roots hpoly
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hroots
  have hinv : (m'.map (starRingEnd ℂ)).map (starRingEnd ℂ) = m' := by
    simp [Multiset.map_map, Function.comp_def]
  rw [← hinv, ← hroots, Multiset.map_map]
  exact Multiset.map_congr rfl fun z _ => by simp
end GlobalTheory.CompanionTheory.Clozel

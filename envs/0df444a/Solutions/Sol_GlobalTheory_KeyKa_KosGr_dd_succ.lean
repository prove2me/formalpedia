-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.dd_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:30:55.080678+00:00
-- url     : https://prove2.me/submissions/f564f2ac-89c5-4760-9905-5edef6cf4361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j) (t : Fin g) (c : Finset (Fin g) → ∀ j, V j)
    (I : Finset (Fin g)) (hI : ∀ k ∈ I, k.val < t.val) (j : ℕ) :
    dd x (t.val + 1) c I j
      = dd x t.val c I j + (-1 : K) ^ I.card • x t j (c (insert t I) (j + 1)) := by
  have htI : t ∉ I := fun h => lt_irrefl _ (hI t h)
  have hfil : I.filter (· < t) = I := Finset.filter_true_of_mem fun k hk => hI k hk
  unfold dd
  rw [show (-1 : K) ^ I.card • x t j (c (insert t I) (j + 1)) = ∑ i : Fin g,
      if i = t then (-1 : K) ^ (I.filter (· < i)).card • x i j (c (insert i I) (j + 1)) else 0 by
    rw [Finset.sum_ite_eq' Finset.univ t, if_pos (Finset.mem_univ t), hfil]]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : i = t
  · subst h1
    simp [htI]
  · have h2 : i.val < t.val + 1 ↔ i.val < t.val :=
      ⟨fun h => lt_of_le_of_ne (Nat.lt_succ_iff.mp h) (fun e => h1 (Fin.ext e)), Nat.lt_succ_of_lt⟩
    simp only [h2, h1, if_false, add_zero]
end GlobalTheory.KeyKa.KosGr

-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.comm_word
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:19.387215+00:00
-- url     : https://prove2.me/submissions/d47d2c87-29b8-4850-b293-b0b21059b3c1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_cons
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_word_append
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_comm_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
variable [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
  (S Ω : Module.End ℂ V) (K : Finset ι) (c : ι → ι → ι → ℂ) (d o : Fin m → Fin m → ℂ)
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (l : List ι) : ∀ (p : List ι) (e : Fin m),
    ‖j (word Z p ((S * word Z l - word Z l * S) (y e)))‖ ≤
      l.length * c0 K c * bnd j Z y (p.length + l.length + 1) := by
  induction l with
  | nil =>
    intro p e
    simp [GlobalTheory.CompanionTheory.AnalyticWord.word_nil]
  | cons i l ih =>
    intro p e
    have hsplit : S * GlobalTheory.CompanionTheory.AnalyticWord.word Z (i :: l) - GlobalTheory.CompanionTheory.AnalyticWord.word Z (i :: l) * S =
        (S * Z i - Z i * S) * GlobalTheory.CompanionTheory.AnalyticWord.word Z l +
          Z i * (S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) := by
      rw [GlobalTheory.CompanionTheory.AnalyticWord.word_cons]
      simp only [mul_sub, sub_mul, mul_assoc]
      abel
    have h1 := GlobalTheory.CompanionTheory.AnalyticWord.comm_term j Z y S K c hS p l i e
    have h2 := ih (p ++ [i]) e
    have e2 : GlobalTheory.CompanionTheory.AnalyticWord.word Z (p ++ [i]) ((S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) (y e)) =
        GlobalTheory.CompanionTheory.AnalyticWord.word Z p (Z i ((S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) (y e))) := by
      rw [GlobalTheory.CompanionTheory.AnalyticWord.word_append, GlobalTheory.CompanionTheory.AnalyticWord.word_cons, GlobalTheory.CompanionTheory.AnalyticWord.word_nil, mul_one, Module.End.mul_apply]
    have hlen1 : p.length + l.length + 2 = p.length + (i :: l).length + 1 := by
      simp only [List.length_cons]; omega
    have hlen2 : (p ++ [i]).length + l.length + 1 = p.length + (i :: l).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [e2, hlen2] at h2
    rw [hlen1] at h1
    rw [hsplit, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, map_add, map_add]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    rw [List.length_cons, Nat.cast_succ]
    ring
end GlobalTheory.CompanionTheory.AnalyticWord

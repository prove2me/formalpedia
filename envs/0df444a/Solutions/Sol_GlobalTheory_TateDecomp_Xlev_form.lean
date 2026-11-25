-- Prove2me | solution 1 for GlobalTheory.TateDecomp.Xlev_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:03:19.155984+00:00
-- url     : https://prove2.me/submissions/1bf0fd81-cc75-4383-8f91-c5e4c92e7192

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_root_mem_Ks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution (K : FinExt l) {i : ℕ} (hi : 1 ≤ i) {ζ : Om l} (hζ : IsPrimitiveRoot ζ (l ^ i))
    {x : PadicComplex l} (hx : x ∈ Xlev K i) :
    ∃ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1)) ∧ y ⟨0, (Fact.out : l.Prime).pos⟩ = 0 ∧
      x = io l (∑ a : Fin l, ζ ^ (a : ℕ) * y a) := by
  have hp : l.Prime := Fact.out
  haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨ξ, w, hξ, ⟨⟨v, hv, rfl⟩, -⟩, rfl⟩ := hz
    have hζ' := hζ.map_of_injective (io l).injective
    obtain ⟨k, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hξ.pow_eq_one
    have hk : k.Coprime (l ^ i) := (hζ'.pow_iff_coprime (pow_pos hp.pos _) k).1 hξ
    have hk2 : k % l ≠ 0 := by
      intro h
      have h1 : l ∣ k := Nat.dvd_of_mod_eq_zero h
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hk h1 (dvd_pow_self l (by omega)))
    have hl : ζ ^ l ∈ Ks K (i - 1) := by
      refine root_mem_Ks K ?_
      rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hi, hζ.pow_eq_one]
    refine ⟨Pi.single ⟨k % l, Nat.mod_lt _ hp.pos⟩ ((ζ ^ l) ^ (k / l) * v), fun a => ?_, ?_, ?_⟩
    · rw [Pi.single_apply]
      split_ifs
      · exact mul_mem (pow_mem hl _) hv
      · exact zero_mem _
    · rw [Pi.single_eq_of_ne]
      intro h
      exact hk2 (congrArg Fin.val h).symm
    · rw [Finset.sum_eq_single ⟨k % l, Nat.mod_lt _ hp.pos⟩]
      · rw [Pi.single_eq_same, ← mul_assoc, ← pow_mul, ← pow_add, Nat.mod_add_div, map_mul, map_pow]
        rfl
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · simp
  | zero => exact ⟨0, fun _ => zero_mem _, rfl, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨y, h1, h2, rfl⟩ := ha
    obtain ⟨y', h1', h2', rfl⟩ := hb
    refine ⟨y + y', fun a => add_mem (h1 a) (h1' a), by rw [Pi.add_apply, h2, h2', add_zero], ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]
  | neg a _ ha =>
    obtain ⟨y, h1, h2, rfl⟩ := ha
    refine ⟨-y, fun a => neg_mem (h1 a), by rw [Pi.neg_apply, h2, neg_zero], ?_⟩
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, map_neg]
end GlobalTheory.TateDecomp

-- Prove2me | solution 1 for InterdepSOS.RSVCG.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:37:29.962774+00:00
-- url     : https://prove2.me/submissions/19c9344e-6228-4637-9016-d7baf821048c

import Mathlib
import Definitions.Def_InterdepSOS_RSVCG_Setting
import Definitions.Def_InterdepSOS_RSVCG_Mechanism
import Theorems.Thm_InterdepSOS_RSVCG_expost_ic
import Theorems.Thm_InterdepSOS_RSVCG_expost_ir
import Theorems.Thm_InterdepSOS_RSVCG_display_5

namespace InterdepSOS.RSVCG.RSRed
open InterdepSOS.RSVCG

theorem keepOn_le {n : ℕ} (S : Finset (Fin n)) (z : Signal n) : keepOn S z ≤ z := by
  intro j; unfold keepOn; split_ifs <;> simp

theorem weight_le_val {n m : ℕ} (v : Valuation n m) (hv : IsCombValuation v)
    (B : Finset (Fin n)) (s : Profile n m) (j : Fin n) (T : Bundle m) :
    vcgWeight v B s j T ≤ v j T (sigT s T) := by
  by_cases hT : T.Nonempty
  · exact hv.2.2.1 j T hT (keepOn_le _ _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    subst hT; simp [vcgWeight, hv.2.1]

theorem approx {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc)
    (s : Profile n m) (Tstar : Alloc n m) (hT : IsAllocOn Finset.univ Tstar) :
    welfare v s Tstar ≤ 4 * avgB (fun B => welfare v s (alloc B s)) := by
  classical
  have hmono : ∀ f f' : Finset (Fin n) → ℝ, (∀ B, f B ≤ f' B) → avgB f ≤ avgB f' := by
    intro f f' hff; unfold avgB
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun B _ => hff B) (by positivity)
  have step1 : welfare v s Tstar ≤
      ∑ i, 4 * avgB (fun B => if i ∈ B then vcgWeight v B s i (Tstar i) else 0) := by
    unfold welfare
    apply Finset.sum_le_sum; intro i _
    have := InterdepSOS.RSVCG.display_5 v g h hv hsep s i (Tstar i); linarith
  have step2 : ∑ i, 4 * avgB (fun B => if i ∈ B then vcgWeight v B s i (Tstar i) else 0) =
      4 * avgB (fun B => ∑ i ∈ B, vcgWeight v B s i (Tstar i)) := by
    rw [← Finset.mul_sum]; congr 1
    unfold avgB; rw [← Finset.mul_sum]; congr 1
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro B _
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have step3 : ∀ B, ∑ i ∈ B, vcgWeight v B s i (Tstar i) ≤ welfare v s (alloc B s) := by
    intro B
    let TB : Alloc n m := fun i => if i ∈ B then Tstar i else ∅
    have hTB : IsAllocOn B TB := by
      refine ⟨?_, ?_⟩
      · intro a b hab
        simp only [TB]
        split_ifs
        · exact hT.1 hab
        all_goals simp
      · intro a ha; simp [TB, ha]
    have h1 : ∑ i ∈ B, vcgWeight v B s i (Tstar i) = ∑ i ∈ B, vcgWeight v B s i (TB i) := by
      apply Finset.sum_congr rfl; intro i hi; simp [TB, hi]
    rw [h1]
    refine le_trans ((halloc B s).2 TB hTB) ?_
    unfold welfare
    refine le_trans (Finset.sum_le_sum fun i _ => weight_le_val v hv B s i _) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hv.1 _ _ _)
  rw [step2] at step1
  have := hmono _ _ step3
  linarith


end InterdepSOS.RSVCG.RSRed

open InterdepSOS.RSVCG

theorem solution {n m : ℕ} (v g : Valuation n m) (h : Fin n → Bundle m → NNReal → ℝ)
    (hv : IsCombValuation v) (hsep : IsSeparableSOS v g h)
    (alloc : Finset (Fin n) → Profile n m → Alloc n m) (halloc : IsVCGSelector v alloc) :
    (∀ B : Finset (Fin n),
      IsExPostIC v (alloc B) (vcgPay v g alloc B) ∧
        IsExPostIR v (alloc B) (vcgPay v g alloc B)) ∧
    ∀ (s : Profile n m) (Tstar : Alloc n m), IsAllocOn Finset.univ Tstar →
      welfare v s Tstar ≤ 4 * avgB (fun B => welfare v s (alloc B s)) :=
  ⟨fun B => ⟨expost_ic v g h hv hsep alloc halloc B, expost_ir v g h hv hsep alloc halloc B⟩,
   fun s Tstar hT => RSRed.approx v g h hv hsep alloc halloc s Tstar hT⟩

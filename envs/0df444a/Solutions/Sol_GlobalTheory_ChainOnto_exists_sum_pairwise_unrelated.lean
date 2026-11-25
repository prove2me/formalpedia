-- Prove2me | solution 1 for GlobalTheory.ChainOnto.exists_sum_pairwise_unrelated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:19.840071+00:00
-- url     : https://prove2.me/submissions/733046e9-2f5f-4531-9634-814453ae0bf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SurjectiveOfAdjointSeparatesLabelledParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ChainOnto
namespace GlobalTheory.ChainOnto
theorem _root_.solution {A I : Type} [AddCommGroup A] [Module ℂ A]
    (pA : A → I → Prop) (RA : I → I → Prop) (hRA : Equivalence RA)
    (hmerge : ∀ u u' B B' (a : ℂ), pA u B → pA u' B' → RA B B' → u + a • u' ≠ 0 → pA (u + a • u') B)
    (hsmul : ∀ u B (a : ℂ), pA u B → a ≠ 0 → pA (a • u) B) (u : A)
    (hu : u ∈ Submodule.span ℂ {u | ∃ B, pA u B}) :
    ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i := by
  classical
  let Q : A → Prop := fun u => ∃ (s : Finset I) (v : I → A), (∀ i ∈ s, pA (v i) i) ∧
      (∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → ¬ RA i i') ∧ u = ∑ i ∈ s, v i
  have hQ0 : Q 0 := ⟨∅, fun _ => 0, by simp, by simp, by simp⟩
  have hadd1 : ∀ u w B, Q u → pA w B → Q (u + w) := by
    rintro u w B ⟨s, v, hv, hp, rfl⟩ hw
    by_cases hex : ∃ i ∈ s, RA i B
    · obtain ⟨i, hi, hiB⟩ := hex
      by_cases hz : v i + w = 0
      · refine ⟨s.erase i, v, fun j hj => hv j (Finset.mem_of_mem_erase hj),
          fun j hj j' hj' => hp j (Finset.mem_of_mem_erase hj) j' (Finset.mem_of_mem_erase hj'), ?_⟩
        rw [← Finset.add_sum_erase s v hi]
        calc v i + ∑ x ∈ s.erase i, v x + w = (v i + w) + ∑ x ∈ s.erase i, v x := by abel
          _ = _ := by rw [hz, zero_add]
      · refine ⟨s, Function.update v i (v i + w), ?_, hp, ?_⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            simp only [Function.update_self]
            have := hmerge (v j) w j B 1 (hv j hj) hw hiB (by simpa using hz)
            simpa using this
          · rw [Function.update_of_ne hji]; exact hv j hj
        · rw [← Finset.add_sum_erase s (Function.update v i (v i + w)) hi, ← Finset.add_sum_erase s v hi]
          simp only [Function.update_self]
          rw [Finset.sum_congr rfl (fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _)]
          abel
    · push_neg at hex
      have hBs : B ∉ s := fun hB => hex B hB (hRA.refl B)
      refine ⟨insert B s, Function.update v B w, ?_, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with hj | hj
        · subst hj; simpa using hw
        · have hjB : j ≠ B := fun h => hBs (by rw [← h]; exact hj)
          rw [Function.update_of_ne hjB]; exact hv j hj
      · intro j hj j' hj' hne
        rw [Finset.mem_insert] at hj hj'
        rcases hj with hj | hj <;> rcases hj' with hj' | hj'
        · exact absurd (hj.trans hj'.symm) hne
        · subst hj; exact fun h => hex j' hj' (hRA.symm h)
        · subst hj'; exact hex j hj
        · exact hp j hj j' hj' hne
      · rw [Finset.sum_insert hBs, Function.update_self,
          Finset.sum_congr rfl (fun j hj => Function.update_of_ne (show j ≠ B from fun h => hBs (by rw [← h]; exact hj)) w v)]
        abel
  have haddS : ∀ (s' : Finset I) (v' : I → A) u, Q u → (∀ i ∈ s', pA (v' i) i) →
      Q (u + ∑ i ∈ s', v' i) := by
    intro s' v'
    induction s' using Finset.induction_on with
    | empty => intro u hu _; simpa using hu
    | insert a s ha ih =>
      intro u hu hv'
      rw [Finset.sum_insert ha, ← add_assoc]
      exact ih _ (hadd1 u (v' a) a hu (hv' a (Finset.mem_insert_self a s)))
        (fun i hi => hv' i (Finset.mem_insert_of_mem hi))
  have hadd : ∀ u u', Q u → Q u' → Q (u + u') := by
    rintro u u' hu ⟨s', v', hv', -, rfl⟩
    exact haddS s' v' u hu hv'
  have hsm : ∀ (a : ℂ) u, Q u → Q (a • u) := by
    rintro a u ⟨s, v, hv, hp, rfl⟩
    by_cases ha : a = 0
    · subst ha; simpa using hQ0
    · exact ⟨s, fun i => a • v i, fun i hi => hsmul _ _ a (hv i hi) ha, hp, by rw [Finset.smul_sum]⟩
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨B, hB⟩ := hx
    simpa using hadd1 0 x B hQ0 hB
  | zero => exact hQ0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul a x _ hx => exact hsm a x hx
end GlobalTheory.ChainOnto

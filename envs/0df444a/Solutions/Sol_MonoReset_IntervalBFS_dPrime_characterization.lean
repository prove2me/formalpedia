-- Prove2me | solution 1 for MonoReset.IntervalBFS.dPrime_characterization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T04:48:53.651854+00:00
-- url     : https://prove2.me/submissions/9a6196ad-352c-4218-b5d5-5390a63acfd8

import Definitions.Def_MonoReset_IntervalBFS_Model
import Theorems.Thm_MonoReset_IntervalBFS_lemma_2

open MonoReset.IntervalBFS

private lemma snd_mem_ivSet {n : ℕ} (I : Fin n × Fin n) : I.2 ∈ ivSet I := by
  simp [ivSet]

private lemma mem_ivSet_self {n : ℕ} {s x : Fin n} (hx : x ∈ ivSet (s, s)) : x = s := by
  simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  fin_omega

private lemma run_append_singleton {n k : ℕ} (δ : Fin k → Fin n → Fin n)
    (τ : List (Fin k)) (a : Fin k) (s : Fin n) :
    run δ (τ ++ [a]) s = δ a (run δ τ s) := by
  simp [run]

private lemma dPrime_append_singleton {n k : ℕ} (δ : Fin k → Fin n → Fin n)
    (τ : List (Fin k)) (a : Fin k) (x : Option (Fin n × Fin n)) :
    dPrime δ (τ ++ [a]) x = dPrime1 δ a (dPrime δ τ x) := by
  simp [dPrime]

theorem solution {n k : ℕ} (δ : Fin k → Fin n → Fin n)
    (hδ : ∀ a, IsMonotonic (δ a)) (τ : List (Fin k)) (I : Fin n × Fin n) :
    (run δ τ I.1 ≠ run δ τ I.2 →
        dPrime δ τ (some I) = some (run δ τ I.1, run δ τ I.2)) ∧
    ((∀ s ∈ ivSet I, run δ τ s = run δ τ I.1) →
        dPrime δ τ (some I) = some (run δ τ I.1, run δ τ I.1) ∨ dPrime δ τ (some I) = none) ∧
    (run δ τ I.1 = run δ τ I.2 → ¬ (∀ s ∈ ivSet I, run δ τ s = run δ τ I.1) →
        dPrime δ τ (some I) = none) ∧
    dPrime δ τ none = none := by
  induction τ using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_, rfl⟩
    · intro _
      rfl
    · intro h
      left
      have h2 : I.2 = I.1 := h I.2 (snd_mem_ivSet I)
      cases I
      simp_all [run, dPrime]
    · intro h12 hnot
      exfalso
      apply hnot
      intro s hs
      have hI : I = (I.1, I.1) := Prod.ext rfl h12.symm
      rw [hI] at hs
      exact mem_ivSet_self hs
  | append_singleton τ a ih =>
    rcases ih with ⟨ih1, ih2, ih3, ih4⟩
    have hnone : dPrime δ (τ ++ [a]) none = none := by
      rw [dPrime_append_singleton, ih4]
      rfl
    by_cases hneq : run δ τ I.1 ≠ run δ τ I.2
    · have hd : dPrime δ τ (some I) = some (run δ τ I.1, run δ τ I.2) := ih1 hneq
      have hsub : ∀ s ∈ ivSet I, run δ τ s ∈ ivSet (run δ τ I.1, run δ τ I.2) := by
        intro s hs
        exact lemma_2 δ hδ τ I (run δ τ I.1, run δ τ I.2) hd (Finset.mem_image_of_mem _ hs)
      by_cases ha : δ a (run δ τ I.1) ≠ δ a (run δ τ I.2)
      · have hd' : dPrime δ (τ ++ [a]) (some I) =
            some (run δ (τ ++ [a]) I.1, run δ (τ ++ [a]) I.2) := by
          rw [dPrime_append_singleton, hd, run_append_singleton, run_append_singleton]
          dsimp only [dPrime1]
          rw [if_pos ha]
        refine ⟨fun _ => hd', ?_, ?_, hnone⟩
        · intro hall
          exfalso
          apply ha
          have h2 := hall I.2 (snd_mem_ivSet I)
          simpa [run_append_singleton] using h2.symm
        · intro h12 _
          exfalso
          apply ha
          simpa [run_append_singleton] using h12
      · have ha_eq : δ a (run δ τ I.1) = δ a (run δ τ I.2) := not_ne_iff.mp ha
        by_cases hallJ : ∀ x ∈ ivSet (run δ τ I.1, run δ τ I.2), δ a x = δ a (run δ τ I.1)
        · have hd' : dPrime δ (τ ++ [a]) (some I) =
              some (run δ (τ ++ [a]) I.1, run δ (τ ++ [a]) I.1) := by
            rw [dPrime_append_singleton, hd, run_append_singleton]
            dsimp only [dPrime1]
            rw [if_neg ha, if_pos hallJ]
          refine ⟨?_, fun _ => Or.inl hd', ?_, hnone⟩
          · intro hneq'
            exfalso
            apply hneq'
            simpa [run_append_singleton] using ha_eq
          · intro _ hnot
            exfalso
            apply hnot
            intro s hs
            simpa [run_append_singleton] using hallJ (run δ τ s) (hsub s hs)
        · have hd' : dPrime δ (τ ++ [a]) (some I) = none := by
            rw [dPrime_append_singleton, hd]
            dsimp only [dPrime1]
            rw [if_neg ha, if_neg hallJ]
          refine ⟨?_, fun _ => Or.inr hd', fun _ _ => hd', hnone⟩
          · intro hneq'
            exfalso
            apply hneq'
            simpa [run_append_singleton] using ha_eq
    · have hneq_eq : run δ τ I.1 = run δ τ I.2 := not_ne_iff.mp hneq
      have ha_eq : run δ (τ ++ [a]) I.1 = run δ (τ ++ [a]) I.2 := by
        simpa [run_append_singleton] using congrArg (δ a) hneq_eq
      by_cases hallI : ∀ s ∈ ivSet I, run δ τ s = run δ τ I.1
      · have hallI' : ∀ s ∈ ivSet I, run δ (τ ++ [a]) s = run δ (τ ++ [a]) I.1 := by
          intro s hs
          simpa [run_append_singleton] using congrArg (δ a) (hallI s hs)
        refine ⟨fun hneq' => absurd ha_eq hneq', ?_, fun _ hnot => absurd hallI' hnot, hnone⟩
        intro _
        rcases ih2 hallI with hd | hd
        · left
          rw [dPrime_append_singleton, hd, run_append_singleton]
          have hall_self : ∀ s ∈ ivSet (run δ τ I.1, run δ τ I.1), δ a s = δ a (run δ τ I.1) := by
            intro s hs
            rw [mem_ivSet_self hs]
          have hne_self : ¬ (δ a (run δ τ I.1) ≠ δ a (run δ τ I.1)) := not_not.mpr rfl
          dsimp only [dPrime1]
          rw [if_neg hne_self, if_pos hall_self]
        · right
          rw [dPrime_append_singleton, hd]
          rfl
      · have hd : dPrime δ τ (some I) = none := ih3 hneq_eq hallI
        have hd' : dPrime δ (τ ++ [a]) (some I) = none := by
          rw [dPrime_append_singleton, hd]
          rfl
        exact ⟨fun hneq' => absurd ha_eq hneq', fun _ => Or.inr hd', fun _ _ => hd', hnone⟩

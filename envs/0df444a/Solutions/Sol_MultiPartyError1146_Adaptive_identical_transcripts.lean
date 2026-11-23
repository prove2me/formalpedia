-- Prove2me | solution 1 for MultiPartyError1146.Adaptive.identical_transcripts
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:29:51.232808+00:00
-- url     : https://prove2.me/submissions/dcfe964a-0404-4de0-a980-3cba73448ecb

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Attack
import Theorems.Thm_MultiPartyError1146_Adaptive_greedy_properties

set_option autoImplicit false

open MultiPartyError1146.Adaptive

theorem solution (n T k : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T)
    (hk : 1 ≤ k ∧ 2 * k < n) (P : Protocol n 1 T) (i : Fin n)
    (hi : target P k = some i) (x : Input n 1)
    (hx : ∀ j ∈ (greedy P k).chosen, x j 0 = (greedy P k).input j) :
    isolationAttack P k (Function.update x i (fun _ => false)) =
      isolationAttack P k (Function.update x i (fun _ => true)) := by
  classical
  obtain ⟨i', hi', hi'chosen, _hcard, _hbound, hcollision⟩ :=
    greedy_properties n T k hn hT hk P
  have hii : i' = i := Option.some.inj (hi'.symm.trans hi)
  subst i'
  let x₀ : Input n 1 := Function.update x i (fun _ => false)
  let x₁ : Input n 1 := Function.update x i (fun _ => true)
  have hiParty : i ∈ erasedParties P k := by
    simp [erasedParties, hi]
  have chosenParty {q : Fin n} (hq : q ∈ (greedy P k).chosen) :
      q ∈ erasedParties P k := by
    simp [erasedParties, hq]
  have chosen_ne {q : Fin n} (hq : q ∈ (greedy P k).chosen) : q ≠ i := by
    intro h
    subst q
    exact hi'chosen hq
  have hlen (y : Input n 1) (j : ℕ) :
      (maskedHistory P y (erasedParties P k) (erasedRounds P k) j).length = j := by
    induction j with
    | zero => simp [maskedHistory]
    | succ j ih => simp [maskedHistory, ih]
  have herased (y : Input n 1) :
      ∀ (j : ℕ) (q : Fin n), q ∈ erasedParties P k → ∀ s : Fin j,
        (((maskedHistory P y (erasedParties P k) (erasedRounds P k) j)[s.val]?.getD
          (fun _ => none)) q) = none := by
    intro j
    induction j with
    | zero => intro q hq s; exact Fin.elim0 s
    | succ j ih =>
        intro q hq s
        rw [maskedHistory]
        simp only [List.getElem?_append]
        by_cases hs : s.val < j
        · rw [if_pos (by simpa [hlen] using hs)]
          simpa using ih q hq ⟨s.val, hs⟩
        · have hsj : s.val = j := by omega
          rw [if_neg (by simpa [hlen] using hs)]
          simp [hlen, hsj, hq]
  have hx₀chosen (q : Fin n) (hq : q ∈ (greedy P k).chosen) :
      x₀ q = fun _ => (greedy P k).input q := by
    funext z
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    simp [x₀, chosen_ne hq, hx q hq]
  have hx₁chosen (q : Fin n) (hq : q ∈ (greedy P k).chosen) :
      x₁ q = fun _ => (greedy P k).input q := by
    funext z
    have hz : z = 0 := Subsingleton.elim _ _
    subst z
    simp [x₁, chosen_ne hq, hx q hq]
  have cas_none_of_two {a : Fin n → Symbol} {j₁ j₂ : Fin n}
      (hne : j₁ ≠ j₂) (h₁ : (a j₁).isSome) (h₂ : (a j₂).isSome) : cas a = none := by
    have hmem₁ : j₁ ∈ Finset.univ.filter (fun q => (a q).isSome) := by simp [h₁]
    have hmem₂ : j₂ ∈ Finset.univ.filter (fun q => (a q).isSome) := by simp [h₂]
    have hcard : 1 < (Finset.univ.filter (fun q => (a q).isSome)).card :=
      Finset.one_lt_card.mpr ⟨j₁, hmem₁, j₂, hmem₂, hne⟩
    simp [cas, show (Finset.univ.filter (fun q => (a q).isSome)).card ≠ 1 by omega]
  have hhist : ∀ j : ℕ,
      maskedHistory P x₀ (erasedParties P k) (erasedRounds P k) j =
        maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) j := by
    intro j
    induction j with
    | zero => simp [maskedHistory]
    | succ j ih =>
        rw [maskedHistory, maskedHistory, ih]
        congr 2
        funext r
        by_cases ht : j < T
        · let t : Fin T := ⟨j, ht⟩
          simp only [dif_pos ht]
          change (if r ∈ erasedParties P k ∨ t ∈ erasedRounds P k then none else
            cas (fun q => P.send t q (x₀ q)
              (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) j)[s.val]?.getD
                (fun _ => none)) q))) =
            (if r ∈ erasedParties P k ∨ t ∈ erasedRounds P k then none else
            cas (fun q => P.send t q (x₁ q)
              (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) j)[s.val]?.getD
                (fun _ => none)) q)))
          by_cases hp : r ∈ erasedParties P k
          · simp [hp]
          by_cases hr : t ∈ erasedRounds P k
          · simp [hp, hr]
          simp [hp, hr]
          by_cases htrem : t ∈ remainingRounds P k
          · have hnot : t ∉ silentSpeaking P i false ∪ silentSpeaking P i true := by
              intro hu
              apply hr
              simp [erasedRounds, hi, htrem, hu]
            have hnot₀ : t ∉ silentSpeaking P i false := by
              intro h; exact hnot (Finset.mem_union_left _ h)
            have hnot₁ : t ∉ silentSpeaking P i true := by
              intro h; exact hnot (Finset.mem_union_right _ h)
            have hpref :
                (fun s : Fin t.val => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                  (fun _ => none)) i) = (fun _ => none) := by
              funext s
              exact herased x₁ t.val i hiParty s
            have hsend :
                (fun q => P.send t q (x₀ q)
                  (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                    (fun _ => none)) q)) =
                (fun q => P.send t q (x₁ q)
                  (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                    (fun _ => none)) q)) := by
              funext q
              by_cases hqi : q = i
              · subst q
                have hsend₀ : P.send t i (x₀ i) (fun _ => none) = none := by
                  have hnone : ¬ (P.send t i (fun _ => false) (fun _ => none)).isSome := by
                    simpa [silentSpeaking] using hnot₀
                  simpa [x₀] using (Option.not_isSome_iff_eq_none.mp hnone)
                have hsend₁ : P.send t i (x₁ i) (fun _ => none) = none := by
                  have hnone : ¬ (P.send t i (fun _ => true) (fun _ => none)).isSome := by
                    simpa [silentSpeaking] using hnot₁
                  simpa [x₁] using (Option.not_isSome_iff_eq_none.mp hnone)
                rw [hpref, hsend₀, hsend₁]
              · simp [x₀, x₁, hqi]
            exact congrArg cas hsend
          · obtain ⟨j₁, hj₁, j₂, hj₂, hne, hs₁, hs₂⟩ := hcollision t htrem
            have ha₁₀ : (P.send t j₁ (x₀ j₁)
                (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                  (fun _ => none)) j₁)).isSome := by
              rw [show (fun s : Fin t.val => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                (fun _ => none)) j₁) = (fun _ => none) by
                  funext s; exact herased x₁ t.val j₁ (chosenParty hj₁) s]
              rw [hx₀chosen j₁ hj₁]
              simpa [silentSpeaking] using hs₁
            have ha₂₀ : (P.send t j₂ (x₀ j₂)
                (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                  (fun _ => none)) j₂)).isSome := by
              rw [show (fun s : Fin t.val => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                (fun _ => none)) j₂) = (fun _ => none) by
                  funext s; exact herased x₁ t.val j₂ (chosenParty hj₂) s]
              rw [hx₀chosen j₂ hj₂]
              simpa [silentSpeaking] using hs₂
            have ha₁₁ : (P.send t j₁ (x₁ j₁)
                (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                  (fun _ => none)) j₁)).isSome := by
              rw [show (fun s : Fin t.val => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                (fun _ => none)) j₁) = (fun _ => none) by
                  funext s; exact herased x₁ t.val j₁ (chosenParty hj₁) s]
              rw [hx₁chosen j₁ hj₁]
              simpa [silentSpeaking] using hs₁
            have ha₂₁ : (P.send t j₂ (x₁ j₂)
                (fun s => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                  (fun _ => none)) j₂)).isSome := by
              rw [show (fun s : Fin t.val => ((maskedHistory P x₁ (erasedParties P k) (erasedRounds P k) t.val)[s.val]?.getD
                (fun _ => none)) j₂) = (fun _ => none) by
                  funext s; exact herased x₁ t.val j₂ (chosenParty hj₂) s]
              rw [hx₁chosen j₂ hj₂]
              simpa [silentSpeaking] using hs₂
            exact (cas_none_of_two hne ha₁₀ ha₂₀).trans (cas_none_of_two hne ha₁₁ ha₂₁).symm
        · rw [dif_neg ht, dif_neg ht]
  have hfinal : isolationAttack P k x₀ = isolationAttack P k x₁ := by
    funext t q
    simp only [isolationAttack, maskedAdversary]
    rw [hhist T]
  simpa [x₀, x₁] using hfinal

-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:40.808971+00:00
-- url     : https://prove2.me/submissions/fba85f77-2e91-4aa6-85a0-11c0392943a1

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_cacheLearning

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

open scoped ENNReal

/-- Theorem 8, p.558: the specified previous-run policy, with the printed l ≤ p
tie. A pathwise bound applies also to adaptively generated inputs. Costs are
summed over every block of an arbitrary fixed finite unlimited-cache instance. -/
theorem solution (p : ℕ) (hp : 1 ≤ p) (B : Type) [Fintype B] (n : ℕ) (hn : 1 ≤ n)
    (s₀ : B → NonuniformCompetitive.Snoopy.State n) :
    ∃ a : ℝ, ∀ σ : B → List (NonuniformCompetitive.Snoopy.Req n),
      (∀ b, NonuniformCompetitive.Snoopy.Admissible (σ b)) →
      cacheFamilyCost (previousRunPolicy p) s₀ σ ≤
        ENNReal.ofReal (3 * (cacheFamilyOpt p s₀ σ).toReal + a) := by
          have hpne' : p ≠ 0 := by omega
          have sumSnoc : ∀ (τ : List (Req n)) (r : Req n) (F : ℕ → Req n → ℝ≥0∞),
              ∑ j : Fin (τ ++ [r]).length, F j (τ ++ [r])[j] = ∑ j : Fin τ.length, F j τ[j] + F τ.length r := by
            intro τ r F
            have hl : (τ ++ [r]).length = τ.length + 1 := by simp
            let g : Fin (τ.length + 1) → ℝ≥0∞ := fun i => F i ((τ ++ [r])[i.val]'(by rw [hl]; exact i.2))
            refine (Fin.sum_congr' g hl).trans ?_
            rw [Fin.sum_univ_castSucc]
            simp [g, List.getElem_append_left]
          have costSnoc : ∀ (A : OnlineAlgorithm n) (τ : List (Req n)) (r : Req n),
              A.cost p (τ ++ [r]) = A.cost p τ + stepCost p r (A.after τ) (A.moment (τ ++ [r])) (A.after (τ ++ [r])) := by
            intro A τ r
            unfold OnlineAlgorithm.cost
            rw [sumSnoc τ r (fun j x => stepCost p x (A.after ((τ ++ [r]).take j)) (A.moment ((τ ++ [r]).take (j+1))) (A.after ((τ ++ [r]).take (j+1))))]
            congr 1
            · apply Finset.sum_congr rfl
              intro j _
              have h1 : j.val ≤ τ.length := j.2.le
              have h2 : j.val + 1 ≤ τ.length := j.2
              rw [List.take_append_of_le_length h1, List.take_append_of_le_length h2]
            · rw [List.take_of_length_le (l := τ ++ [r]) (i := τ.length + 1) (by simp)]; simp
          have schedSnoc : ∀ (τ : List (Req n)) (r : Req n) (m s : ℕ → State n),
              scheduleCost p (τ ++ [r]) m s = scheduleCost p τ m s + stepCost p r (s τ.length) (m (τ.length + 1)) (s (τ.length + 1)) := by
            intro τ r m s
            unfold scheduleCost
            exact sumSnoc τ r (fun j x => stepCost p x (s j) (m (j+1)) (s (j+1)))
          have traceSnoc : ∀ (f : CachePolicy p) (s0 : State n) (τ : List (Req n)) (r : Req n),
              cacheTrace f s0 (τ ++ [r]) = cacheNext f (cacheTrace f s0 τ) r := by
            intro f s0 τ r
            have h : ∀ l, cacheTrace f s0 l = l.foldl (cacheNext f) {active := none, writes := 0, completed := [], threshold := (f []).val, state := s0} := by
              intro l; cases l <;> rfl
            rw [h, h, List.foldl_append]; rfl
          have momR : ∀ (f : CachePolicy p) (s0 : State n) (τ : List (Req n)) (i : Fin n),
              (cacheAlgorithm f s0).moment (τ ++ [Req.read i]) = cacheReadMoment (cacheTrace f s0 τ).state i := by
            intro f s0 τ i
            simp [cacheAlgorithm]
          have momW : ∀ (f : CachePolicy p) (s0 : State n) (τ : List (Req n)) (i : Fin n),
              (cacheAlgorithm f s0).moment (τ ++ [Req.write i]) = (cacheTrace f s0 τ).state := by
            intro f s0 τ i
            exact (cacheAlgorithm f s0).lookaheadZero τ i
          have admPre : ∀ (τ : List (Req n)) (r : Req n), Admissible (τ ++ [r]) → Admissible τ := by
            intro τ r h j i hj
            have hlt : j < τ.length := by
              by_contra hc; push Not at hc; rw [List.getElem?_eq_none hc] at hj; cases hj
            have := h j i (by rw [List.getElem?_append_left hlt]; exact hj)
            refine ⟨this.1, ?_⟩
            rw [List.getElem?_append_left (by omega)] at this
            exact this.2
          have admW : ∀ (τ : List (Req n)) (i : Fin n), Admissible (τ ++ [Req.write i]) →
              τ.getLast? = some (Req.read i) ∨ τ.getLast? = some (Req.write i) := by
            intro τ i h
            have := h τ.length i (by simp)
            rw [List.getElem?_append_left (by omega)] at this
            rw [List.getLast?_eq_getElem?]
            exact this.2
          have rwPre : ∀ (τ : List (Req n)) (r : Req n) (m s : ℕ → State n), RespectsWrites (τ ++ [r]) m s → RespectsWrites τ m s := by
            intro τ r m s h j hj
            have := h ⟨j.val, by simp⟩ (by simpa [List.getElem_append_left j.2] using hj)
            simpa using this
          have rwLast : ∀ (τ : List (Req n)) (i : Fin n) (m s : ℕ → State n), RespectsWrites (τ ++ [Req.write i]) m s → m (τ.length + 1) = s τ.length := by
            intro τ i m s h
            exact h ⟨τ.length, by simp⟩ (by simp [Req.isWrite])
          have polVal : ∀ h : List ℕ, (previousRunPolicy p h).val = if h.getLast?.getD 0 ≤ p then p else 0 := by
            intro h; unfold previousRunPolicy; split_ifs <;> rfl
          have readCost : ∀ (st : State n) (i : Fin n) (k : ℕ), stepCost p (Req.read i) st (cacheReadMoment st i) (if k = 0 then some i else cacheReadMoment st i) = (((if st = none ∨ st = some i then 0 else p : ℕ)) : ℝ≥0∞) := by
            intro st i k
            rcases st with _ | j
            · by_cases hk : k = 0 <;> simp [stepCost, transCost, taskCost, cacheReadMoment, hk]
            · by_cases hji : j = i
              · subst hji; by_cases hk : k = 0 <;> simp [stepCost, transCost, taskCost, cacheReadMoment, hk]
              · by_cases hk : k = 0 <;> simp [stepCost, transCost, taskCost, cacheReadMoment, hk, hji]
          have writeCost : ∀ (st : State n) (i : Fin n) (c : Prop) [Decidable c], (st = none ∨ st = some i) →
              stepCost p (Req.write i) st st (if st = none ∧ c then some i else st) = (((if st = none then 1 else 0 : ℕ)) : ℝ≥0∞) := by
            intro st i c _ hst
            rcases hst with rfl | rfl
            · by_cases hc : c <;> simp [stepCost, transCost, taskCost, hc]
            · simp [stepCost, transCost, taskCost]
          have T1 : ∀ (x y : State n) (i : Fin n), (((if x = some i then p else 0 : ℕ)) : ℝ≥0∞) ≤ transCost p x y + ((if y = some i then p else 0 : ℕ) : ℝ≥0∞) := by
            intro x y i
            rcases x with _ | a <;> rcases y with _ | b <;> simp [transCost] <;> split_ifs <;> simp_all
          have L1 : ∀ (r : Req n) (o mo o' : State n) (i : Fin n), (((if o = some i then p else 0 : ℕ)) : ℝ≥0∞) ≤ stepCost p r o mo o' + ((if o' = some i then p else 0 : ℕ) : ℝ≥0∞) := by
            intro r o mo o' i
            calc (((if o = some i then p else 0 : ℕ)) : ℝ≥0∞) ≤ transCost p o mo + ((if mo = some i then p else 0 : ℕ) : ℝ≥0∞) := T1 _ _ _
              _ ≤ transCost p o mo + (transCost p mo o' + ((if o' = some i then p else 0 : ℕ) : ℝ≥0∞)) := add_le_add_right (T1 _ _ _) _
              _ ≤ stepCost p r o mo o' + ((if o' = some i then p else 0 : ℕ) : ℝ≥0∞) := by
                unfold stepCost
                rw [← add_assoc]
                gcongr
                exact le_add_right le_rfl
          have L2 : ∀ (i j : Fin n) (o mo o' : State n), j ≠ i → (((if o = some j then p else 0 : ℕ)) : ℝ≥0∞) ≤ stepCost p (Req.read i) o mo o' := by
            intro i j o mo o' hji
            by_cases ho : o = some j
            · subst ho
              by_cases hmo : mo = some j
              · subst hmo; simp [stepCost, taskCost, hji]
              · have : transCost p (some j) mo = (p : ℝ≥0∞) := by simp [transCost, hmo]
                simp only [stepCost, this]
                push_cast
                exact le_add_right (le_add_right le_rfl)
            · simp [ho]
          have L3 : ∀ (i : Fin n) (o' : State n), (1 : ℝ≥0∞) ≤ stepCost p (Req.write i) none none o' := by
            intro i o'
            simp only [stepCost, taskCost]
            simp only [reduceCtorEq, if_false, if_true]
            exact le_add_right (le_add_left le_rfl)
          have L4 : ∀ (i j : Fin n) (o' : State n), j ≠ i → stepCost p (Req.write i) (some j) (some j) o' = ⊤ := by
            intro i j o' hji
            simp [stepCost, taskCost, hji]
          let Good : CacheMemory n → Option (Req n) → ℕ → ℝ≥0∞ → State n → Prop := fun q last A OPT o =>
            A + (if q.state = none then q.writes else p) ≤ 3 * (q.completed.map (fun l => min l p)).sum + 2 * min q.writes p + p ∧
            (q.state = none → q.writes < q.threshold) ∧
            (∀ i, q.active = some i → q.state = none ∨ q.state = some i) ∧
            (∀ i, (last = some (Req.read i) ∨ last = some (Req.write i)) → q.active = some i) ∧
            (q.threshold = 0 ∨ q.threshold = p) ∧
            (q.active = none → q.writes = 0 ∧ q.completed = []) ∧
            (((q.completed.map (fun l => min l p)).sum : ℕ) : ℝ≥0∞) ≤ OPT ∧
            (((q.completed.map (fun l => min l p)).sum + min q.writes p : ℕ) : ℝ≥0∞) ≤ OPT + ((if o = q.active then p else 0 : ℕ) : ℝ≥0∞)
          have key : ∀ (s0 : State n) (m s : ℕ → State n), s 0 = s0 → ∀ τ : List (Req n), Admissible τ → RespectsWrites τ m s →
              ∃ A : ℕ, (cacheAlgorithm (previousRunPolicy p) s0).cost p τ = (A : ℝ≥0∞) ∧
                Good (cacheTrace (previousRunPolicy p) s0 τ) τ.getLast? A (scheduleCost p τ m s) (s τ.length) := by
            intro s0 m s hs0 τ
            induction τ using List.reverseRecOn with
            | nil =>
              intro _ _
              refine ⟨0, by simp [OnlineAlgorithm.cost], ?_⟩
              have hp0 : (previousRunPolicy p []).val = p := by rw [polVal]; simp
              simp only [Good, cacheTrace, hp0]
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · split_ifs <;> simp
              · intro _; omega
              · intro i h; cases h
              · intro i h; simp at h
              · simp
              · simp
              · simp
              · simp
            | append_singleton τ r ih =>
              intro hadm hrw
              obtain ⟨A, hA, hG⟩ := ih (admPre τ r hadm) (rwPre τ r m s hrw)
              have hAft : ∀ l, (cacheAlgorithm (previousRunPolicy p) s0).after l = (cacheTrace (previousRunPolicy p) s0 l).state := fun _ => rfl
              rw [costSnoc, hA, hAft, hAft, traceSnoc, schedSnoc]
              have hlast : (τ ++ [r]).getLast? = some r := by simp
              rw [hlast, List.length_append, List.length_singleton]
              cases r with
              | read i =>
                rw [momR]
                generalize cacheTrace (previousRunPolicy p) s0 τ = q at hG ⊢
                generalize scheduleCost p τ m s = OPT at hG ⊢
                generalize s τ.length = o at hG ⊢
                generalize m (τ.length + 1) = mo
                generalize s (τ.length + 1) = o'
                obtain ⟨act, w, comp, k, st⟩ := q
                obtain ⟨hP, h1, h2, h4, h5, h6, hS1, hS2⟩ := hG
                simp only at hP h1 h2 h4 h5 h6 hS1 hS2
                by_cases hact : act = some i
                · subst hact
                  have e : cacheNext (previousRunPolicy p) ⟨some i, w, comp, k, st⟩ (Req.read i) = ⟨some i, w, comp, k, st⟩ := by
                    rcases h2 i rfl with hst | hst
                    · have := h1 hst; subst hst; simp [cacheNext, cacheReadMoment]; omega
                    · subst hst; simp [cacheNext, cacheReadMoment]
                  rw [e]
                  have ec : stepCost p (Req.read i) st (cacheReadMoment st i) st = 0 := by
                    rcases h2 i rfl with hst | hst <;> subst hst <;> simp [stepCost, transCost, taskCost, cacheReadMoment]
                  refine ⟨A, by rw [ec, add_zero], hP, h1, h2, ?_, h5, h6, ?_, ?_⟩
                  · intro i' hi'; simp at hi'; simp [hi']
                  · exact hS1.trans le_self_add
                  · refine hS2.trans ?_
                    rw [add_assoc]
                    exact add_le_add_right (L1 (Req.read i) o mo o' i) OPT
                · by_cases hnone : act = none
                  · subst hnone
                    obtain ⟨hw, hc⟩ := h6 rfl
                    subst hw; subst hc
                    have e : cacheNext (previousRunPolicy p) ⟨none, 0, [], k, st⟩ (Req.read i) = ⟨some i, 0, [], (previousRunPolicy p []).val, if (previousRunPolicy p []).val = 0 then some i else cacheReadMoment st i⟩ := by
                      simp [cacheNext]
                    rw [e, readCost]
                    have hp0 : (previousRunPolicy p []).val = p := by rw [polVal]; simp
                    rw [hp0]
                    have hpne : p ≠ 0 := by omega
                    simp only [hpne, if_false]
                    refine ⟨A + (if st = none ∨ st = some i then 0 else p), by push_cast; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · simp at hP
                      rcases st with _ | j
                      · simp [cacheReadMoment] at hP ⊢; omega
                      · by_cases hji : j = i
                        · subst hji; simp [cacheReadMoment] at hP ⊢; omega
                        · simp [cacheReadMoment, hji] at hP ⊢; omega
                    · intro _; simp; omega
                    · intro i' hi'
                      simp at hi'; subst hi'
                      rcases st with _ | j
                      · simp [cacheReadMoment]
                      · by_cases hji : j = i
                        · subst hji; simp [cacheReadMoment]
                        · simp [cacheReadMoment, hji]
                    · intro i' hi'; simp at hi'; simp [hi']
                    · right; rfl
                    · intro h; cases h
                    · simp
                    · simp
                  · obtain ⟨j, rfl⟩ := Option.ne_none_iff_exists'.mp hnone
                    have hji : j ≠ i := fun h => hact (h ▸ rfl)
                    have hst : cacheReadMoment st i = none := by
                      rcases h2 j rfl with h | h <;> subst h <;> simp [cacheReadMoment, hji]
                    have e : cacheNext (previousRunPolicy p) ⟨some j, w, comp, k, st⟩ (Req.read i) = ⟨some i, 0, comp ++ [w], (previousRunPolicy p (comp ++ [w])).val, if (previousRunPolicy p (comp ++ [w])).val = 0 then some i else cacheReadMoment st i⟩ := by
                      simp [cacheNext, hji]
                    rw [e, readCost, polVal, hst]
                    have hsum : ((comp ++ [w]).map (fun l => min l p)).sum = (comp.map (fun l => min l p)).sum + min w p := by simp
                    simp only [Good]
                    rw [hsum, Nat.zero_min, add_zero]
                    simp only [List.getLast?_concat, Option.getD_some]
                    refine ⟨A + (if st = none ∨ st = some i then 0 else p), by push_cast; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                    · rcases h2 j rfl with hs | hs <;> subst hs
                      · have := h1 rfl
                        by_cases hw : w ≤ p
                        · simp [hw, hpne'] at hP ⊢; omega
                        · exfalso; rcases h5 with h5 | h5 <;> omega
                      · by_cases hw : w ≤ p
                        · simp [hw, hji, hpne'] at hP ⊢; omega
                        · simp [hw, hji, hpne'] at hP ⊢; omega
                    · intro h0; by_cases hw : w ≤ p <;> simp [hw, hpne'] at h0 ⊢ <;> omega
                    · intro i' hi'; simp at hi'; subst hi'; by_cases hw : w ≤ p <;> simp [hw, hpne']
                    · intro i' hi'; simp at hi'; simp [hi']
                    · by_cases hw : w ≤ p <;> simp [hw, hpne']
                    · intro h; cases h
                    · exact hS2.trans (add_le_add_right (L2 i j o mo o' hji) OPT)
                    · exact (hS2.trans (add_le_add_right (L2 i j o mo o' hji) OPT)).trans le_self_add
              | write i =>
                rw [momW, rwLast τ i m s hrw]
                have hlastτ := admW τ i hadm
                generalize cacheTrace (previousRunPolicy p) s0 τ = q at hG ⊢
                generalize scheduleCost p τ m s = OPT at hG ⊢
                generalize s τ.length = o at hG ⊢
                generalize s (τ.length + 1) = o'
                obtain ⟨act, w, comp, k, st⟩ := q
                obtain ⟨hP, h1, h2, h4, h5, h6, hS1, hS2⟩ := hG
                simp only at hP h1 h2 h4 h5 h6 hS1 hS2
                have hact := h4 i hlastτ
                subst hact
                have e : cacheNext (previousRunPolicy p) ⟨some i, w, comp, k, st⟩ (Req.write i) = ⟨some i, w + 1, comp, k, if st = none ∧ k ≤ w + 1 then some i else st⟩ := rfl
                rw [e, writeCost _ _ _ (h2 i rfl)]
                refine ⟨A + (if st = none then 1 else 0), by push_cast; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · rcases h2 i rfl with hs | hs <;> subst hs
                  · have := h1 rfl
                    by_cases hk : k ≤ w + 1
                    · simp [hk] at hP ⊢; rcases h5 with h5 | h5 <;> subst h5 <;> omega
                    · simp [hk] at hP ⊢; omega
                  · simp at hP ⊢; omega
                · intro h0
                  rcases h2 i rfl with hs | hs <;> subst hs
                  · by_cases hk : k ≤ w + 1 <;> simp [hk] at h0 ⊢; omega
                  · simp at h0
                · intro i' hi'; simp at hi'; subst hi'
                  rcases h2 i rfl with hs | hs <;> subst hs
                  · by_cases hk : k ≤ w + 1 <;> simp [hk]
                  · simp
                · intro i' hi'; simp at hi'; simp [hi']
                · exact h5
                · intro h; cases h
                · exact hS1.trans le_self_add
                · rcases o with _ | j
                  · have hb := L3 i o'
                    have hS2' : ((((comp.map (fun l => min l p)).sum + min w p : ℕ)) : ℝ≥0∞) ≤ OPT := by simpa using hS2
                    calc (((comp.map (fun l => min l p)).sum + min (w+1) p : ℕ) : ℝ≥0∞)
                          ≤ (((comp.map (fun l => min l p)).sum + min w p : ℕ) : ℝ≥0∞) + 1 := by norm_cast; omega
                      _ ≤ OPT + stepCost p (Req.write i) none none o' := add_le_add hS2' hb
                      _ ≤ _ := le_self_add
                  · by_cases hji : j = i
                    · subst hji
                      have hb := L1 (Req.write j) (some j) (some j) o' j
                      simp only [if_true] at hb
                      calc (((comp.map (fun l => min l p)).sum + min (w+1) p : ℕ) : ℝ≥0∞)
                            ≤ (((comp.map (fun l => min l p)).sum : ℕ) : ℝ≥0∞) + (p : ℝ≥0∞) := by norm_cast; omega
                        _ ≤ OPT + (stepCost p (Req.write j) (some j) (some j) o' + ((if o' = some j then p else 0 : ℕ) : ℝ≥0∞)) := add_le_add hS1 hb
                        _ = _ := by rw [add_assoc]
                    · rw [L4 i j o' hji]; simp
          have block : ∀ (s0 : State n) (τ : List (Req n)), Admissible τ →
              (cacheAlgorithm (previousRunPolicy p) s0).cost p τ ≤ 3 * offlineCost p s0 τ + ((4 * p : ℕ) : ℝ≥0∞) := by
            intro s0 τ hadm
            have hsched : ∀ m s, s 0 = s0 → RespectsWrites τ m s → (cacheAlgorithm (previousRunPolicy p) s0).cost p τ ≤ scheduleCost p τ m s * 3 + ((4 * p : ℕ) : ℝ≥0∞) := by
              intro m s hs0 hrw
              obtain ⟨A, hA, hG⟩ := key s0 m s hs0 τ hadm hrw
              obtain ⟨hP, -, -, -, -, -, -, hS2⟩ := hG
              rw [hA]
              generalize ((cacheTrace (previousRunPolicy p) s0 τ).completed.map (fun l => min l p)).sum = S at hP hS2
              generalize (cacheTrace (previousRunPolicy p) s0 τ).writes = w at hP hS2
              have h1 : (A : ℝ≥0∞) ≤ 3 * (((S + min w p : ℕ)) : ℝ≥0∞) + (p : ℝ≥0∞) := by
                have : A ≤ 3 * (S + min w p) + p := by omega
                exact_mod_cast this
              have h2 : (((S + min w p : ℕ)) : ℝ≥0∞) ≤ scheduleCost p τ m s + (p : ℝ≥0∞) := by
                refine hS2.trans (add_le_add_right ?_ _)
                split_ifs <;> simp
              calc (A : ℝ≥0∞) ≤ 3 * (((S + min w p : ℕ)) : ℝ≥0∞) + (p : ℝ≥0∞) := h1
                _ ≤ 3 * (scheduleCost p τ m s + p) + p := by gcongr
                _ = _ := by push_cast; ring
            rw [← tsub_le_iff_right]
            have hdiv : ((cacheAlgorithm (previousRunPolicy p) s0).cost p τ - ((4 * p : ℕ) : ℝ≥0∞)) / 3 ≤ offlineCost p s0 τ := by
              unfold offlineCost
              simp only [le_iInf_iff]
              intro m s hs0 hrw
              rw [ENNReal.div_le_iff (by norm_num) (by norm_num), tsub_le_iff_right]
              exact hsched m s hs0 hrw
            rw [ENNReal.div_le_iff (by norm_num) (by norm_num)] at hdiv
            rw [mul_comm (3 : ℝ≥0∞)]; exact hdiv
          have transFin : ∀ x y : State n, transCost p x y ≠ ⊤ := by
            intro x y; unfold transCost; split_ifs
            · simp
            · cases x <;> simp
          have finOpt : ∀ (s0 : State n) (τ : List (Req n)), Admissible τ → offlineCost p s0 τ ≠ ⊤ := by
            intro s0 τ hadm
            apply ne_top_of_le_ne_top (b := scheduleCost p τ (fun _ => none) (fun j => if j = 0 then s0 else none))
            · unfold scheduleCost
              apply ENNReal.sum_ne_top.mpr
              intro j _
              simp only [stepCost]
              refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨transFin _ _, ?_⟩, transFin _ _⟩
              cases τ[j] <;> simp [taskCost]
            · unfold offlineCost
              refine iInf_le_of_le (fun _ => none) (iInf_le_of_le (fun j => if j = 0 then s0 else none) (iInf_le_of_le (by simp) (iInf_le_of_le ?_ le_rfl)))
              intro j hj
              have hj0 : j.val ≠ 0 := by
                intro h0
                rcases hr : τ[j] with i | i
                · rw [hr] at hj; simp [Req.isWrite] at hj
                · have := hadm j.val i (by rw [List.getElem?_eq_getElem j.2]; simp; exact hr)
                  omega
              simp [hj0]
          refine ⟨((Fintype.card B * (4 * p) : ℕ) : ℝ), ?_⟩
          intro σ hσ
          have hT : cacheFamilyOpt p s₀ σ ≠ ⊤ := by
            unfold cacheFamilyOpt; exact ENNReal.sum_ne_top.mpr (fun b _ => finOpt _ _ (hσ b))
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hT, ENNReal.ofReal_natCast]
          calc cacheFamilyCost (previousRunPolicy p) s₀ σ ≤ ∑ b, (3 * offlineCost p (s₀ b) (σ b) + ((4*p : ℕ) : ℝ≥0∞)) :=
                Finset.sum_le_sum (fun b _ => block _ _ (hσ b))
            _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
              simp [cacheFamilyOpt]

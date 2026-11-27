-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_15
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:12.545467+00:00
-- url     : https://prove2.me/submissions/6fe90e69-115f-4b95-bf62-e33447cf347e

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_knownCover

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory

/-- Theorem 15, Appendix pp.569–570. No finiteness, boundedness or minimum
separation is assumed of M. Permutations are minimized in the work function.
The original mixed-strategy algorithm need not be lazy or phase-based. -/
theorem solution {M : Type} [MetricSpace M] (k : ℕ) (hk : 0 < k)
    (s₀ : KServer.Config k M) (A : KServer.RandomizedAlgorithm k M) (α : ℝ)
    (hA : A.IsCompetitiveFrom s₀ α) :
    ∃ B : KServer.RandomizedAlgorithm k M,
      B.IsCompetitiveFrom s₀ α ∧
      ∀ (σ : List M) (V : Set M), KnownCover s₀ σ V →
        ∀ᵐ i ∂B.μ, V ⊆ Set.range ((B.alg i).conf σ) := by
          classical
          letI : MeasurableSpace A.ι := A.ms
          have move_nonneg : ∀ (s t : KServer.Config k M), 0 ≤ KServer.moveCost s t := by
            intro s t
            exact Finset.sum_nonneg (fun i _ => dist_nonneg)
          have move_triangle : ∀ (s t u : KServer.Config k M),
              KServer.moveCost s u ≤ KServer.moveCost s t + KServer.moveCost t u := by
            intro s t u
            unfold KServer.moveCost
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_le_sum (fun i _ => dist_triangle _ _ _)
          have move_self : ∀ s : KServer.Config k M, KServer.moveCost s s = 0 := by
            intro s
            simp [KServer.moveCost]
          have move_update : ∀ (s : KServer.Config k M) (i : Fin k) (r : M),
              KServer.moveCost s (Function.update s i r) = dist (s i) r := by
            intro s i r
            unfold KServer.moveCost
            have heq : (fun j => dist (s j) (Function.update s i r j)) =
                (fun j => if j = i then dist (s i) r else 0) := by
              funext j
              by_cases h : j = i
              · subst j; simp
              · simp [Function.update_of_ne h, h]
            rw [heq]
            simp
          have move_update_target : ∀ (s u : KServer.Config k M) (i : Fin k) (r : M),
              u i = r → dist (s i) r + KServer.moveCost (Function.update s i r) u =
                KServer.moveCost s u := by
            intro s u i r hi
            unfold KServer.moveCost
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
            simp only [Function.update_self, ← hi, dist_self, zero_add]
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          have lazy_step : ∀ (s t u : KServer.Config k M) (i : Fin k) (r : M),
              u i = r →
              dist (s i) r + KServer.moveCost (Function.update s i r) u ≤
                KServer.moveCost s t + KServer.moveCost t u := by
            intro s t u i r hi
            calc
              dist (s i) r + KServer.moveCost (Function.update s i r) u =
                  KServer.moveCost s u := by
                unfold KServer.moveCost
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
                simp only [Function.update_self, ← hi, dist_self, zero_add]
                congr 1
                apply Finset.sum_congr rfl
                intro j hj
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
              _ ≤ _ := move_triangle s t u
          let F : List M → Finset (ℝ × KServer.Config k M) :=
            fun σ => σ.foldl (fun T r => T.biUnion fun p =>
              Finset.univ.image fun i : Fin k =>
                (p.1 + dist (p.2 i) r, Function.update p.2 i r)) {(0, s₀)}
          have F_nil : F [] = {(0, s₀)} := rfl
          have F_append : ∀ (σ : List M) (r : M),
              F (σ ++ [r]) = (F σ).biUnion (fun p =>
                Finset.univ.image fun i : Fin k =>
                  (p.1 + dist (p.2 i) r, Function.update p.2 i r)) := by
            intro σ r
            simp [F, List.foldl_append]
          have F_nonempty : ∀ σ : List M, (F σ).Nonempty := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil => simp [F_nil]
            | append_singleton σ r ih =>
              obtain ⟨p, hp⟩ := ih
              rw [F_append]
              exact ⟨_, Finset.mem_biUnion.mpr ⟨p, hp,
                Finset.mem_image.mpr ⟨⟨0, hk⟩, Finset.mem_univ _, rfl⟩⟩⟩
          have F_nonneg : ∀ (σ : List M) (p : ℝ × KServer.Config k M),
              p ∈ F σ → 0 ≤ p.1 := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil =>
              intro p hp
              have hp' : p = (0, s₀) := by simpa [F_nil] using hp
              subst p
              exact le_refl _
            | append_singleton σ r ih =>
              intro p hp
              rw [F_append] at hp
              obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.mp hp
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
              exact add_nonneg (ih q hq) dist_nonneg
          have F_dominates : ∀ (σ : List M) (S : ℕ → KServer.Config k M),
              KServer.ServesFrom s₀ σ S → ∃ p ∈ F σ,
                p.1 + KServer.moveCost p.2 (S σ.length) ≤
                  ∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j + 1)) := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil =>
              intro S hS
              refine ⟨(0, s₀), by simp [F_nil], ?_⟩
              simp [hS.1, move_self]
            | append_singleton σ r ih =>
              intro S hS
              have hpre : KServer.ServesFrom s₀ σ S := by
                refine ⟨hS.1, ?_⟩
                intro j
                have h := hS.2 ⟨j, by simpa using j.isLt⟩
                simpa only [List.get_eq_getElem, List.getElem_append_left j.isLt] using h
              obtain ⟨p, hp, hpcost⟩ := ih S hpre
              obtain ⟨i, hi⟩ := hS.2 ⟨σ.length, by simp⟩
              have hir : S (σ.length + 1) i = r := by simpa using hi
              refine ⟨(p.1 + dist (p.2 i) r, Function.update p.2 i r), ?_, ?_⟩
              · rw [F_append]
                exact Finset.mem_biUnion.mpr ⟨p, hp,
                  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
              · simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
                have hs := lazy_step p.2 (S σ.length) (S (σ.length + 1)) i r hir
                linarith
          have F_realized : ∀ (σ : List M) (p : ℝ × KServer.Config k M), p ∈ F σ →
              ∃ S : ℕ → KServer.Config k M, KServer.ServesFrom s₀ σ S ∧
                S σ.length = p.2 ∧
                (∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j + 1))) = p.1 := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil =>
              intro p hp
              have hp' : p = (0, s₀) := by simpa [F_nil] using hp
              subst p
              refine ⟨fun _ => s₀, ⟨rfl, ?_⟩, rfl, ?_⟩
              · intro j; exact Fin.elim0 j
              · simp
            | append_singleton σ r ih =>
              intro p hp
              rw [F_append] at hp
              obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.mp hp
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
              obtain ⟨S, hS, hlast, hcost⟩ := ih q hq
              let T : ℕ → KServer.Config k M :=
                fun j => if j ≤ σ.length then S j else Function.update q.2 i r
              have hT : ∀ j, j ≤ σ.length → T j = S j := by
                intro j hj; simp [T, hj]
              have hTlast : T (σ.length + 1) = Function.update q.2 i r := by
                simp [T]
              refine ⟨T, ⟨?_, ?_⟩, ?_, ?_⟩
              · rw [hT 0 (Nat.zero_le _)]; exact hS.1
              · intro j
                by_cases hj : j.val < σ.length
                · obtain ⟨m, hm⟩ := hS.2 ⟨j, hj⟩
                  refine ⟨m, ?_⟩
                  rw [hT (j.val + 1) (by omega)]
                  simpa only [List.get_eq_getElem, List.getElem_append_left hj] using hm
                · have hj' : j.val = σ.length := by
                    have hle : j.val < σ.length + 1 := by simpa using j.isLt
                    omega
                  refine ⟨i, ?_⟩
                  simp [hj', hTlast]
              · simpa using hTlast
              · simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
                have hsum : (∑ j ∈ Finset.range σ.length, KServer.moveCost (T j) (T (j + 1))) =
                    ∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j + 1)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [hT j (by have := Finset.mem_range.mp hj; omega),
                    hT (j + 1) (by have := Finset.mem_range.mp hj; omega)]
                rw [hsum, hcost, hT σ.length (le_refl _), hlast, hTlast, move_update]
          have matching_nonneg : ∀ (s t : KServer.Config k M), 0 ≤ matchingCost s t := by
            intro s t
            unfold matchingCost
            exact Finset.le_inf' Finset.univ_nonempty _ (fun e _ => Finset.sum_nonneg (fun i _ => dist_nonneg))
          have matching_zero : ∀ (s t : KServer.Config k M), matchingCost s t = 0 →
              Set.range s = Set.range t := by
            intro s t h
            obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
              (fun e : Equiv.Perm (Fin k) => ∑ i, dist (s i) (t (e i)))
            have hall : ∀ i, s i = t (e i) := by
              intro i
              have hs : ∑ i, dist (s i) (t (e i)) = 0 := heq.symm.trans h
              exact dist_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => dist_nonneg)).mp hs i (Finset.mem_univ i))
            apply Set.Subset.antisymm
            · rintro x ⟨i, rfl⟩
              exact ⟨e i, (hall i).symm⟩
            · rintro x ⟨i, rfl⟩
              obtain ⟨j, rfl⟩ := e.surjective i
              exact ⟨j, hall j⟩
          have work_nonneg : ∀ (σ : List M) (s : KServer.Config k M),
              0 ≤ KServer.workFn s₀ σ s := by
            intro σ s
            unfold KServer.workFn
            apply Real.sInf_nonneg
            rintro c ⟨S, hS, rfl⟩
            exact add_nonneg (Finset.sum_nonneg (fun j _ => move_nonneg _ _)) (move_nonneg _ _)
          have workU_nonneg : ∀ (σ : List M) (s : KServer.Config k M),
              0 ≤ KServer.workFnU s₀ σ s := by
            intro σ s
            unfold KServer.workFnU
            exact le_ciInf (fun e => work_nonneg σ (s ∘ e))
          have work_finite : ∀ (σ : List M) (s : KServer.Config k M),
              KServer.workFn s₀ σ s = (F σ).inf' (F_nonempty σ)
                (fun p => p.1 + KServer.moveCost p.2 s) := by
            intro σ s
            obtain ⟨p, hp, hmin⟩ := Finset.exists_mem_eq_inf' (F_nonempty σ)
              (fun p => p.1 + KServer.moveCost p.2 s)
            have hbd : BddBelow {c : ℝ | ∃ S : ℕ → KServer.Config k M,
                KServer.ServesFrom s₀ σ S ∧ c =
                  (∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j + 1))) +
                    KServer.moveCost (S σ.length) s} := by
              refine ⟨0, ?_⟩
              rintro c ⟨S, hS, rfl⟩
              exact add_nonneg (Finset.sum_nonneg (fun j _ => move_nonneg _ _)) (move_nonneg _ _)
            obtain ⟨S, hS, hlast, hcost⟩ := F_realized σ p hp
            have hmem : p.1 + KServer.moveCost p.2 s ∈
                {c : ℝ | ∃ S : ℕ → KServer.Config k M,
                  KServer.ServesFrom s₀ σ S ∧ c =
                    (∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j + 1))) +
                      KServer.moveCost (S σ.length) s} := by
              exact ⟨S, hS, by rw [hlast, hcost]⟩
            apply le_antisymm
            · rw [hmin]
              exact csInf_le hbd hmem
            · apply le_csInf ⟨_, hmem⟩
              rintro c ⟨T, hT, rfl⟩
              obtain ⟨q, hq, hqcost⟩ := F_dominates σ T hT
              calc
                (F σ).inf' (F_nonempty σ) (fun p => p.1 + KServer.moveCost p.2 s) ≤
                    q.1 + KServer.moveCost q.2 s := Finset.inf'_le _ hq
                _ ≤ _ := by have := move_triangle q.2 (T σ.length) s; linarith
          have work_le_lazy : ∀ (σ : List M) (p : ℝ × KServer.Config k M), p ∈ F σ →
              ∀ s : KServer.Config k M, KServer.workFn s₀ σ s ≤ p.1 + KServer.moveCost p.2 s := by
            intro σ p hp s
            rw [work_finite]
            exact Finset.inf'_le _ hp
          have workU_le_lazy : ∀ (σ : List M) (p : ℝ × KServer.Config k M), p ∈ F σ →
              KServer.workFnU s₀ σ p.2 ≤ p.1 := by
            intro σ p hp
            unfold KServer.workFnU
            have h := ciInf_le (Finite.bddBelow_range (fun e : Equiv.Perm (Fin k) =>
              KServer.workFn s₀ σ (p.2 ∘ e))) (Equiv.refl _)
            have h' := work_le_lazy σ p hp p.2
            simpa [move_self, Function.comp_def] using h.trans h'
          have optimal_endpoint : ∀ σ : List M, ∃ p ∈ F σ,
              KServer.workFnU s₀ σ p.2 = p.1 ∧
              (∀ s : KServer.Config k M, p.1 ≤ KServer.workFnU s₀ σ s) ∧
              (∀ V : Set M, KnownCover s₀ σ V → V ⊆ Set.range p.2) := by
            intro σ
            obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (F σ) Prod.fst (F_nonempty σ)
            have hlow : ∀ s : KServer.Config k M, p.1 ≤ KServer.workFnU s₀ σ s := by
              intro s
              unfold KServer.workFnU
              apply le_ciInf
              intro e
              rw [work_finite]
              apply Finset.le_inf' _ _
              intro q hq
              exact (hmin q hq).trans (le_add_of_nonneg_right (move_nonneg _ _))
            have heq : KServer.workFnU s₀ σ p.2 = p.1 :=
              le_antisymm (workU_le_lazy σ p hp) (hlow p.2)
            refine ⟨p, hp, heq, hlow, ?_⟩
            intro V hV
            obtain ⟨t, ht, hcost⟩ := hV p.2
            rw [heq] at hcost
            have hmatch : matchingCost t p.2 = 0 := by
              have := hlow t
              have := matching_nonneg t p.2
              linarith
            exact (matching_zero t p.2 hmatch) ▸ ht
          let Q : List M → Finset M := fun σ => Finset.univ.image s₀ ∪ σ.toFinset
          have F_range : ∀ (σ : List M) (p : ℝ × KServer.Config k M),
              p ∈ F σ → ∀ i, p.2 i ∈ Q σ := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil =>
              intro p hp i
              have hp' : p = (0, s₀) := by simpa [F_nil] using hp
              subst p
              simp [Q]
            | append_singleton σ r ih =>
              intro p hp j
              rw [F_append] at hp
              obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.mp hp
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
              by_cases hji : j = i
              · subst j; simp [Q]
              · have := ih q hq j
                simpa [Q, Function.update_of_ne hji, or_assoc] using Or.inr this
          have cover_finite : ∀ (σ : List M) (V : Set M), KnownCover s₀ σ V →
              V ⊆ ↑(Q σ) ∧ V.Finite := by
            intro σ V hV
            obtain ⟨p, hp, heq, hlow, hcover⟩ := optimal_endpoint σ
            have hsub := hcover V hV
            have hfin : V.Finite := (Set.finite_range p.2).subset hsub
            refine ⟨?_, hfin⟩
            · rintro x hx
              obtain ⟨i, rfl⟩ := hsub hx
              exact F_range σ p hp i
          have matching_attain : ∀ s t : KServer.Config k M, ∃ e : Equiv.Perm (Fin k),
              matchingCost s t = KServer.moveCost s (t ∘ e) := by
            intro s t
            obtain ⟨e, he, heq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
              (fun e : Equiv.Perm (Fin k) => ∑ i, dist (s i) (t (e i)))
            exact ⟨e, heq⟩
          have matching_le : ∀ (s t : KServer.Config k M) (e : Equiv.Perm (Fin k)),
              matchingCost s t ≤ KServer.moveCost s (t ∘ e) := by
            intro s t e
            exact Finset.inf'_le _ (Finset.mem_univ e)
          have matching_triangle : ∀ s t u : KServer.Config k M,
              matchingCost s u ≤ matchingCost s t + matchingCost t u := by
            intro s t u
            obtain ⟨e, he⟩ := matching_attain s t
            obtain ⟨f, hf⟩ := matching_attain t u
            calc
              matchingCost s u ≤ KServer.moveCost s (u ∘ e.trans f) := matching_le s u _
              _ ≤ (∑ i, dist (s i) (t (e i))) + ∑ i, dist (t (e i)) (u (f (e i))) := by
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_le_sum (fun i _ => dist_triangle _ _ _)
              _ = matchingCost s t + matchingCost t u := by
                rw [Equiv.sum_comp e (fun i => dist (t i) (u (f i)))]
                rw [he, hf]
                rfl
          have workU_le_match : ∀ (σ : List M) (p : ℝ × KServer.Config k M), p ∈ F σ →
              ∀ s : KServer.Config k M,
                KServer.workFnU s₀ σ s ≤ p.1 + matchingCost p.2 s := by
            intro σ p hp s
            obtain ⟨e, he⟩ := matching_attain p.2 s
            rw [he]
            exact (ciInf_le (Finite.bddBelow_range _) e).trans (work_le_lazy σ p hp _)
          have workU_attain : ∀ (σ : List M) (s : KServer.Config k M), ∃ p ∈ F σ,
              KServer.workFnU s₀ σ s = p.1 + matchingCost p.2 s := by
            intro σ s
            obtain ⟨e, he, hmin⟩ := Finset.exists_min_image Finset.univ
              (fun e : Equiv.Perm (Fin k) => KServer.workFn s₀ σ (s ∘ e)) Finset.univ_nonempty
            have heq : KServer.workFnU s₀ σ s = KServer.workFn s₀ σ (s ∘ e) := by
              apply le_antisymm
              · exact ciInf_le (Finite.bddBelow_range _) e
              · exact le_ciInf (fun f => hmin f (Finset.mem_univ _))
            obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_inf' (F_nonempty σ)
              (fun p => p.1 + KServer.moveCost p.2 (s ∘ e))
            have hfull : KServer.workFnU s₀ σ s = p.1 + KServer.moveCost p.2 (s ∘ e) := by
              rw [heq, work_finite, hpeq]
            refine ⟨p, hp, le_antisymm (workU_le_match σ p hp s) ?_⟩
            rw [hfull]
            exact add_le_add (le_refl p.1) (matching_le p.2 s e)
          have covering_projection : ∀ (σ : List M) (s : KServer.Config k M), ∃ p ∈ F σ,
              KServer.workFnU s₀ σ s = p.1 + matchingCost p.2 s ∧
              (∀ V : Set M, KnownCover s₀ σ V → V ⊆ Set.range p.2) := by
            intro σ s
            let T := (F σ).filter (fun p => p.1 + matchingCost p.2 s = KServer.workFnU s₀ σ s)
            have hTne : T.Nonempty := by
              obtain ⟨p, hp, he⟩ := workU_attain σ s
              exact ⟨p, Finset.mem_filter.mpr ⟨hp, he.symm⟩⟩
            obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image T Prod.fst hTne
            have hpF : p ∈ F σ := (Finset.mem_filter.mp hp).1
            have hpeq : p.1 + matchingCost p.2 s = KServer.workFnU s₀ σ s :=
              (Finset.mem_filter.mp hp).2
            refine ⟨p, hpF, hpeq.symm, ?_⟩
            intro V hV
            obtain ⟨t, ht, hdom⟩ := hV p.2
            obtain ⟨q, hq, hqeq⟩ := workU_attain σ t
            have hlow : q.1 + matchingCost q.2 s ≤ KServer.workFnU s₀ σ s := by
              have htri := matching_triangle q.2 t s
              have htri' := matching_triangle t p.2 s
              have hwp := workU_le_lazy σ p hpF
              linarith
            have hqt : q ∈ T := Finset.mem_filter.mpr
              ⟨hq, le_antisymm hlow (workU_le_match σ q hq s)⟩
            have hqp := hmin q hqt
            have hz : matchingCost t p.2 = 0 := by
              have hqt0 := matching_nonneg q.2 t
              have htp0 := matching_nonneg t p.2
              have hwp := workU_le_lazy σ p hpF
              linarith
            exact (matching_zero t p.2 hz) ▸ ht
          let W : List M → Set M := fun σ => {x | KnownCover s₀ σ {x}}
          have covers_W : ∀ (σ : List M) (s : KServer.Config k M),
              (∀ V : Set M, KnownCover s₀ σ V → V ⊆ Set.range s) → W σ ⊆ Set.range s := by
            intro σ s hs x hx
            exact hs {x} hx (Set.mem_singleton x)
          have W_known : ∀ σ : List M, KnownCover s₀ σ (W σ) := by
            intro σ s
            obtain ⟨p, hp, heq, hcov⟩ := covering_projection σ s
            refine ⟨p.2, covers_W σ p.2 hcov, ?_⟩
            have := workU_le_lazy σ p hp
            linarith
          have W_contains : ∀ (σ : List M) (V : Set M), KnownCover s₀ σ V → V ⊆ W σ := by
            intro σ V hV x hx s
            obtain ⟨t, ht, hcost⟩ := hV s
            exact ⟨t, Set.singleton_subset_iff.mpr (ht hx), hcost⟩
          have W_finite : ∀ σ : List M, (W σ).Finite ∧ W σ ⊆ ↑(Q σ) := by
            intro σ
            have h := cover_finite σ (W σ) (W_known σ)
            exact ⟨h.2, h.1⟩
          have W_last : ∀ (σ : List M) (r : M), r ∈ W (σ ++ [r]) := by
            intro σ r s
            obtain ⟨p, hp, heq⟩ := workU_attain (σ ++ [r]) s
            have hr : r ∈ Set.range p.2 := by
              rw [F_append] at hp
              obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.mp hp
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
              exact ⟨i, Function.update_self _ _ _⟩
            refine ⟨p.2, Set.singleton_subset_iff.mpr hr, ?_⟩
            have := workU_le_lazy (σ ++ [r]) p hp
            linarith
          have workU_mono : ∀ (σ : List M) (r : M) (s : KServer.Config k M),
              KServer.workFnU s₀ σ s ≤ KServer.workFnU s₀ (σ ++ [r]) s := by
            intro σ r s
            unfold KServer.workFnU
            apply le_ciInf
            intro e
            have hle : KServer.workFnU s₀ σ s ≤ KServer.workFn s₀ σ (s ∘ e) :=
              ciInf_le (Finite.bddBelow_range _) e
            apply hle.trans
            rw [work_finite (σ ++ [r])]
            apply Finset.le_inf' _ _
            intro p hp
            rw [F_append] at hp
            obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.mp hp
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
            have hbase := work_le_lazy σ q hq (s ∘ e)
            have htri := move_triangle q.2 (Function.update q.2 i r) (s ∘ e)
            rw [move_update] at htri
            dsimp
            linarith
          have known_append : ∀ (σ : List M) (r : M), r ∈ W σ →
              ∀ s : KServer.Config k M,
                KServer.workFnU s₀ (σ ++ [r]) s = KServer.workFnU s₀ σ s := by
            intro σ r hr s
            apply le_antisymm _ (workU_mono σ r s)
            obtain ⟨p, hp, heq, hcov⟩ := covering_projection σ s
            obtain ⟨i, hi⟩ := hcov {r} hr (Set.mem_singleton r)
            have hstay : Function.update p.2 i r = p.2 := by
              rw [← hi]
              exact Function.update_eq_self _ _
            have hp' : p ∈ F (σ ++ [r]) := by
              rw [F_append]
              apply Finset.mem_biUnion.mpr
              refine ⟨p, hp, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩⟩
              simp [hi, hstay]
            rw [heq]
            exact workU_le_match (σ ++ [r]) p hp' s
          have known_padding : ∀ (σ τ : List M), (∀ r ∈ τ, r ∈ W σ) →
              ∀ s : KServer.Config k M,
                KServer.workFnU s₀ (σ ++ τ) s = KServer.workFnU s₀ σ s := by
            intro σ τ
            induction τ using List.reverseRecOn with
            | nil => intro h s; simp
            | append_singleton τ r ih =>
              intro h s
              have hτ : ∀ x ∈ τ, x ∈ W σ := by
                intro x hx; exact h x (List.mem_append_left _ hx)
              have he := ih hτ
              have hr : r ∈ W (σ ++ τ) := by
                have hr0 := h r (by simp)
                change KnownCover s₀ (σ ++ τ) {r}
                change KnownCover s₀ σ {r} at hr0
                intro t
                obtain ⟨u, hu, hcost⟩ := hr0 t
                exact ⟨u, hu, by simpa only [he] using hcost⟩
              rw [← List.append_assoc, known_append (σ ++ τ) r hr, he s]
          have workU_lipschitz : ∀ (σ : List M) (s t : KServer.Config k M),
              KServer.workFnU s₀ σ s ≤ KServer.workFnU s₀ σ t + matchingCost t s := by
            intro σ s t
            obtain ⟨p, hp, he⟩ := workU_attain σ t
            have hle := workU_le_match σ p hp s
            have htri := matching_triangle p.2 t s
            linarith
          have workU_hit : ∀ (σ : List M) (r : M) (s : KServer.Config k M),
              r ∈ Set.range s → KServer.workFnU s₀ (σ ++ [r]) s = KServer.workFnU s₀ σ s := by
            intro σ r s hr
            obtain ⟨j, hj⟩ := hr
            apply le_antisymm _ (workU_mono σ r s)
            obtain ⟨p, hp, he⟩ := workU_attain σ s
            obtain ⟨e, heq⟩ := matching_attain p.2 s
            let i := e.symm j
            have hi : (s ∘ e) i = r := by simp [i, hj]
            let q : ℝ × KServer.Config k M :=
              (p.1 + dist (p.2 i) r, Function.update p.2 i r)
            have hq : q ∈ F (σ ++ [r]) := by
              rw [F_append]
              exact Finset.mem_biUnion.mpr ⟨p, hp,
                Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
            calc
              KServer.workFnU s₀ (σ ++ [r]) s ≤ KServer.workFn s₀ (σ ++ [r]) (s ∘ e) :=
                ciInf_le (Finite.bddBelow_range _) e
              _ ≤ q.1 + KServer.moveCost q.2 (s ∘ e) := work_le_lazy _ q hq _
              _ = KServer.workFnU s₀ σ s := by
                dsimp [q]
                rw [add_assoc, move_update_target p.2 (s ∘ e) i r hi, ← heq, ← he]
          have workU_step_le : ∀ (σ : List M) (r : M) (s t : KServer.Config k M),
              r ∈ Set.range t → KServer.workFnU s₀ (σ ++ [r]) s ≤
                KServer.workFnU s₀ σ t + matchingCost t s := by
            intro σ r s t hr
            have h := workU_lipschitz (σ ++ [r]) s t
            rwa [workU_hit σ r t hr] at h
          have workU_step_attain : ∀ (σ : List M) (r : M) (s : KServer.Config k M),
              ∃ t : KServer.Config k M, r ∈ Set.range t ∧
                KServer.workFnU s₀ (σ ++ [r]) s = KServer.workFnU s₀ σ t + matchingCost t s := by
            intro σ r s
            obtain ⟨p, hp, heq⟩ := workU_attain (σ ++ [r]) s
            have hr : r ∈ Set.range p.2 := by
              rw [F_append] at hp
              obtain ⟨q, hq, hp⟩ := Finset.mem_biUnion.mp hp
              obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
              exact ⟨i, Function.update_self _ _ _⟩
            refine ⟨p.2, hr, le_antisymm (workU_step_le σ r s p.2 hr) ?_⟩
            have hmono := workU_mono σ r p.2
            have hle := workU_le_lazy (σ ++ [r]) p hp
            linarith
          have workU_extend : ∀ (σ τ : List M),
              (∀ s, KServer.workFnU s₀ σ s = KServer.workFnU s₀ τ s) →
              ∀ (ρ : List M) (s : KServer.Config k M),
                KServer.workFnU s₀ (σ ++ ρ) s = KServer.workFnU s₀ (τ ++ ρ) s := by
            intro σ τ heq ρ
            induction ρ using List.reverseRecOn with
            | nil => intro s; simpa using heq s
            | append_singleton ρ r ih =>
              intro s
              rw [← List.append_assoc, ← List.append_assoc]
              obtain ⟨u, hu, heu⟩ := workU_step_attain (σ ++ ρ) r s
              obtain ⟨v, hv, hev⟩ := workU_step_attain (τ ++ ρ) r s
              have h₁ := workU_step_le (τ ++ ρ) r s u hu
              have h₂ := workU_step_le (σ ++ ρ) r s v hv
              rw [ih u] at heu
              rw [ih v] at h₂
              linarith
          have work_le_schedule : ∀ (σ : List M) (S : ℕ → KServer.Config k M),
              KServer.ServesFrom s₀ σ S → ∀ s : KServer.Config k M,
                KServer.workFn s₀ σ s ≤
                  (∑ j ∈ Finset.range σ.length, KServer.moveCost (S j) (S (j + 1))) +
                    KServer.moveCost (S σ.length) s := by
            intro σ S hS s
            obtain ⟨p, hp, hcost⟩ := F_dominates σ S hS
            have hle := work_le_lazy σ p hp s
            have htri := move_triangle p.2 (S σ.length) s
            linarith
          have offline_endpoint : ∀ (σ : List M) (p : ℝ × KServer.Config k M), p ∈ F σ →
              (∀ s, p.1 ≤ KServer.workFnU s₀ σ s) → KServer.offlineCost s₀ σ = p.1 := by
            intro σ p hp hlow
            obtain ⟨S, hS, hlast, hcost⟩ := F_realized σ p hp
            have hmem : p.1 ∈ {c : ℝ | ∃ T : ℕ → KServer.Config k M,
                KServer.ServesFrom s₀ σ T ∧ c =
                  ∑ j ∈ Finset.range σ.length, KServer.moveCost (T j) (T (j + 1))} :=
              ⟨S, hS, hcost.symm⟩
            apply le_antisymm
            · apply csInf_le _ hmem
              refine ⟨0, ?_⟩
              rintro c ⟨T, hT, rfl⟩
              exact Finset.sum_nonneg (fun j _ => move_nonneg _ _)
            · apply le_csInf ⟨_, hmem⟩
              rintro c ⟨T, hT, rfl⟩
              have hle := work_le_schedule σ T hT (T σ.length)
              rw [move_self, add_zero] at hle
              exact (hlow _).trans ((ciInf_le (Finite.bddBelow_range _)
                (Equiv.refl (Fin k))).trans (by simpa [Function.comp_def] using hle))
          have offline_work_eq : ∀ (σ τ : List M),
              (∀ s, KServer.workFnU s₀ σ s = KServer.workFnU s₀ τ s) →
              KServer.offlineCost s₀ σ = KServer.offlineCost s₀ τ := by
            intro σ τ heq
            obtain ⟨p, hp, hep, hlp, hcp⟩ := optimal_endpoint σ
            obtain ⟨q, hq, heq', hlq, hcq⟩ := optimal_endpoint τ
            rw [offline_endpoint σ p hp hlp, offline_endpoint τ q hq hlq]
            have h₁ := hlp q.2
            have h₂ := hlq p.2
            rw [heq q.2, heq'] at h₁
            rw [← heq p.2, hep] at h₂
            exact le_antisymm h₁ h₂
          have cost_nonneg : ∀ (D : KServer.OnlineAlgorithm k M) (σ : List M), 0 ≤ D.cost σ := by
            intro D σ
            exact Finset.sum_nonneg (fun j _ => move_nonneg _ _)
          have cost_nil : ∀ D : KServer.OnlineAlgorithm k M, D.cost [] = 0 := by
            intro D; simp [KServer.OnlineAlgorithm.cost]
          have cost_append : ∀ (D : KServer.OnlineAlgorithm k M) (σ : List M) (r : M),
              D.cost (σ ++ [r]) = D.cost σ + KServer.moveCost (D.conf σ) (D.conf (σ ++ [r])) := by
            intro D σ r
            unfold KServer.OnlineAlgorithm.cost
            simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              have hj' := Finset.mem_range.mp hj
              rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
            · have hn : σ.length + 1 = (σ ++ [r]).length := by simp
              rw [hn, List.take_length, List.take_append_of_le_length (le_refl _), List.take_length]
          let ls : KServer.OnlineAlgorithm k M → List M → List M × KServer.Config k M :=
            fun D σ => σ.foldl (fun p r => (p.1 ++ [r], if r ∈ Set.range p.2 then p.2
              else Function.update p.2 (Classical.choose (D.serves p.1 r)) r)) ([], D.conf [])
          have ls_first : ∀ (D : KServer.OnlineAlgorithm k M) (σ : List M), (ls D σ).1 = σ := by
            intro D σ
            induction σ using List.reverseRecOn with
            | nil => rfl
            | append_singleton σ r ih =>
              simp only [ls, List.foldl_append, List.foldl_cons, List.foldl_nil]
              change (ls D σ).1 ++ [r] = σ ++ [r]
              rw [ih]
          have ls_append : ∀ (D : KServer.OnlineAlgorithm k M) (σ : List M) (r : M),
              (ls D (σ ++ [r])).2 = if r ∈ Set.range (ls D σ).2 then (ls D σ).2
                else Function.update (ls D σ).2 (Classical.choose (D.serves σ r)) r := by
            intro D σ r
            simp only [ls, List.foldl_append, List.foldl_cons, List.foldl_nil]
            change (if r ∈ Set.range (ls D σ).2 then (ls D σ).2 else
              Function.update (ls D σ).2 (Classical.choose (D.serves (ls D σ).1 r)) r) = _
            rw [ls_first]
          let lazyAlg : KServer.OnlineAlgorithm k M → KServer.OnlineAlgorithm k M := fun D => {
            conf := fun σ => (ls D σ).2
            serves := by
              intro σ r
              rw [ls_append]
              split_ifs with h
              · exact h
              · exact ⟨_, Function.update_self _ _ _⟩ }
          have lazy_nil : ∀ D : KServer.OnlineAlgorithm k M, (lazyAlg D).conf [] = D.conf [] := by
            intro D; rfl
          have lazy_hit : ∀ (D : KServer.OnlineAlgorithm k M) (σ : List M) (r : M),
              r ∈ Set.range ((lazyAlg D).conf σ) → (lazyAlg D).conf (σ ++ [r]) = (lazyAlg D).conf σ := by
            intro D σ r hr
            exact (ls_append D σ r).trans (if_pos hr)
          have lazy_bound : ∀ (D : KServer.OnlineAlgorithm k M) (σ : List M),
              (lazyAlg D).cost σ + KServer.moveCost ((lazyAlg D).conf σ) (D.conf σ) ≤ D.cost σ := by
            intro D σ
            induction σ using List.reverseRecOn with
            | nil => simp [cost_nil, lazy_nil, move_self]
            | append_singleton σ r ih =>
              rw [cost_append, cost_append]
              have hls := ls_append D σ r
              change (lazyAlg D).conf (σ ++ [r]) = _ at hls
              split_ifs at hls with hr
              · rw [hls, move_self, add_zero]
                have htri := move_triangle ((lazyAlg D).conf σ) (D.conf σ) (D.conf (σ ++ [r]))
                linarith
              · rw [hls, move_update]
                have hi := Classical.choose_spec (D.serves σ r)
                have hstep := lazy_step ((lazyAlg D).conf σ) (D.conf σ) (D.conf (σ ++ [r]))
                  (Classical.choose (D.serves σ r)) r hi
                linarith
          have lazy_range : ∀ (D : KServer.OnlineAlgorithm k M), D.conf [] = s₀ →
              ∀ (σ : List M) (i : Fin k), (lazyAlg D).conf σ i ∈ Q σ := by
            intro D hD σ
            induction σ using List.reverseRecOn with
            | nil => intro i; simp [lazy_nil, hD, Q]
            | append_singleton σ r ih =>
              intro i
              have hls := ls_append D σ r
              change (lazyAlg D).conf (σ ++ [r]) = _ at hls
              rw [hls]
              split_ifs with hr
              · have := ih i
                simpa [Q, or_assoc, or_left_comm, or_comm] using Or.inr (a := (lazyAlg D).conf σ i = r) this
              · by_cases hi : i = Classical.choose (D.serves σ r)
                · subst i; simp [Q]
                · have := ih i
                  simpa [Q, Function.update_of_ne hi, or_assoc, or_left_comm, or_comm] using
                    Or.inr (a := (lazyAlg D).conf σ i = r) this
          have metric_bounds : ∀ S : Finset M, ∃ δ E : ℝ, 0 < δ ∧ 0 < E ∧
              (∀ x ∈ S, ∀ y ∈ S, dist x y ≤ E) ∧
              (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) := by
            intro S
            let D : Finset ℝ := insert 1 (((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).image
              (fun p => dist p.1 p.2))
            obtain ⟨δ, hδ, hmin⟩ := Finset.exists_min_image D id (Finset.insert_nonempty _ _)
            have hδpos : 0 < δ := by
              rcases Finset.mem_insert.mp hδ with hδ | hδ
              · simpa [hδ] using (zero_lt_one : (0 : ℝ) < 1)
              · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hδ
                exact dist_pos.mpr (Finset.mem_filter.mp hp).2
            let E : ℝ := (∑ x ∈ S, ∑ y ∈ S, dist x y) + 1
            refine ⟨δ, E, hδpos, ?_, ?_, ?_⟩
            · have hsum : 0 ≤ ∑ x ∈ S, ∑ y ∈ S, dist x y :=
                Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => dist_nonneg))
              dsimp [E]; linarith
            · intro x hx y hy
              have h₁ : dist x y ≤ ∑ y ∈ S, dist x y :=
                Finset.single_le_sum (fun z _ => (dist_nonneg : 0 ≤ dist x z)) hy
              have h₂ : (∑ y ∈ S, dist x y) ≤ ∑ x ∈ S, ∑ y ∈ S, dist x y :=
                Finset.single_le_sum (fun z _ => Finset.sum_nonneg
                  (fun y _ => (dist_nonneg : 0 ≤ dist z y))) hx
              dsimp [E]; linarith
            · intro x hx y hy hxy
              exact hmin _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
                ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩))
          have cost_suffix_nonneg : ∀ (D : KServer.OnlineAlgorithm k M) (σ τ : List M),
              D.cost σ ≤ D.cost (σ ++ τ) := by
            intro D σ τ
            induction τ using List.reverseRecOn with
            | nil => simp
            | append_singleton τ r ih =>
              rw [← List.append_assoc, cost_append]
              exact ih.trans (le_add_of_nonneg_right (move_nonneg _ _))
          have move_path : ∀ (D : KServer.OnlineAlgorithm k M) (σ τ : List M),
              KServer.moveCost (D.conf σ) (D.conf (σ ++ τ)) ≤ D.cost (σ ++ τ) - D.cost σ := by
            intro D σ τ
            induction τ using List.reverseRecOn with
            | nil => simp [move_self]
            | append_singleton τ r ih =>
              rw [← List.append_assoc, cost_append]
              have htri := move_triangle (D.conf σ) (D.conf (σ ++ τ)) (D.conf ((σ ++ τ) ++ [r]))
              linarith
          have finite_move_eq : ∀ (S : Finset M) (δ : ℝ),
              (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) →
              ∀ (s t : KServer.Config k M), (∀ i, s i ∈ S) → (∀ i, t i ∈ S) →
                KServer.moveCost s t < δ → s = t := by
            intro S δ hδ s t hs ht hcost
            funext i
            by_contra hne
            have hlow := hδ (s i) (hs i) (t i) (ht i) hne
            have hsum : dist (s i) (t i) ≤ KServer.moveCost s t :=
              Finset.single_le_sum (fun _ _ => dist_nonneg) (Finset.mem_univ i)
            linarith
          have small_path : ∀ (D : KServer.OnlineAlgorithm k M) (S : Finset M) (δ : ℝ),
              0 < δ → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) →
              ∀ (σ τ : List M),
                (∀ ρ : List M, ρ <+: τ → ∀ i, D.conf (σ ++ ρ) i ∈ S) →
                D.cost (σ ++ τ) - D.cost σ < δ →
                D.conf (σ ++ τ) = D.conf σ ∧ ∀ r ∈ τ, r ∈ Set.range (D.conf σ) := by
            intro D S δ hδ hsep σ τ
            induction τ using List.reverseRecOn with
            | nil => intro hS hcost; simp
            | append_singleton τ r ih =>
              intro hS hcost
              have hSpre : ∀ ρ : List M, ρ <+: τ → ∀ i, D.conf (σ ++ ρ) i ∈ S := by
                intro ρ hρ
                exact hS ρ (hρ.trans (List.prefix_append τ [r]))
              have hpre : D.cost (σ ++ τ) - D.cost σ < δ := by
                have hmono := cost_suffix_nonneg D (σ ++ τ) [r]
                rw [List.append_assoc] at hmono
                linarith
              obtain ⟨heq, hcovered⟩ := ih hSpre hpre
              have hstep : KServer.moveCost (D.conf (σ ++ τ)) (D.conf (σ ++ (τ ++ [r]))) < δ := by
                have hmono := cost_suffix_nonneg D σ τ
                have hc := cost_append D (σ ++ τ) r
                rw [List.append_assoc] at hc
                linarith
              have heq' : D.conf (σ ++ (τ ++ [r])) = D.conf (σ ++ τ) := by
                symm
                exact finite_move_eq S δ hsep _ _
                  (hS τ (List.prefix_append τ [r])) (hS _ (List.prefix_refl _)) hstep
              refine ⟨heq'.trans heq, ?_⟩
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hcovered x hx
              · have hxr : x = r := by simpa using hx
                subst x
                have hr := D.serves (σ ++ τ) r
                rw [List.append_assoc, heq', heq] at hr
                exact hr
          have lazy_covered_suffix : ∀ (D : KServer.OnlineAlgorithm k M) (V : Set M) (σ τ : List M),
              V ⊆ Set.range ((lazyAlg D).conf σ) → (∀ r ∈ τ, r ∈ V) →
              (lazyAlg D).conf (σ ++ τ) = (lazyAlg D).conf σ := by
            intro D V σ τ hV hτ
            induction τ using List.reverseRecOn with
            | nil => simp
            | append_singleton τ r ih =>
              have hτ' : ∀ x ∈ τ, x ∈ V := fun x hx => hτ x (List.mem_append_left _ hx)
              have heq := ih hτ'
              rw [← List.append_assoc, lazy_hit D (σ ++ τ) r (by
                rw [heq]; exact hV (hτ r (by simp))), heq]
          have Q_padding : ∀ (σ p τ : List M), Q p ⊆ Q σ →
              (∀ r ∈ τ, r ∈ W σ) → Q (p ++ τ) ⊆ Q σ := by
            intro σ p τ hQ hτ x hx
            simp only [Q, Finset.mem_union, List.mem_toFinset, List.mem_append] at hx
            rcases hx with hx | hx | hx
            · exact hQ (Finset.mem_union_left _ hx)
            · exact hQ (Finset.mem_union_right _ (List.mem_toFinset.mpr hx))
            · exact (W_finite σ).2 (hτ x hx)
          have all_bounds : ∀ σ : List M, ∃ δ E : ℝ, 0 < δ ∧ 0 < E ∧
              (∀ x ∈ Q σ, ∀ y ∈ Q σ, dist x y ≤ E) ∧
              (∀ x ∈ Q σ, ∀ y ∈ Q σ, x ≠ y → δ ≤ dist x y) := fun σ => metric_bounds (Q σ)
          choose δ E hδ hE hdiam hsep using all_bounds
          have enough_cycles : ∀ σ : List M, ∃ n : ℕ, 2 * (k : ℝ) * E σ ≤ (n : ℝ) * δ σ := by
            intro σ
            obtain ⟨n, hn⟩ := exists_nat_gt (2 * (k : ℝ) * E σ / δ σ)
            exact ⟨n, ((div_lt_iff₀ (hδ σ)).mp hn).le⟩
          choose N hN using enough_cycles
          let v : List M → List M := fun σ => (W_finite σ).1.toFinset.toList
          have v_mem : ∀ (σ : List M) (r : M), r ∈ v σ ↔ r ∈ W σ := by
            intro σ r
            simp [v]
          let cyc : List M → ℕ → List M := fun σ => Nat.rec [] (fun _ τ => τ ++ v σ)
          have cyc_zero : ∀ σ, cyc σ 0 = [] := by intro σ; rfl
          have cyc_succ : ∀ σ n, cyc σ (n + 1) = cyc σ n ++ v σ := by intro σ n; rfl
          have cyc_mem : ∀ (σ : List M) (n : ℕ) (r : M), r ∈ cyc σ n → r ∈ W σ := by
            intro σ n
            induction n with
            | zero => simp [cyc_zero]
            | succ n ih =>
              intro r hr
              rw [cyc_succ] at hr
              exact (List.mem_append.mp hr).elim (ih r) ((v_mem σ r).mp)
          have force_cycles : ∀ (σ : List M) (n : ℕ) (D : KServer.OnlineAlgorithm k M),
              D.conf [] = s₀ → ∀ p : List M, Q p ⊆ Q σ →
              ¬ W σ ⊆ Set.range ((lazyAlg D).conf (p ++ cyc σ n)) →
              (n : ℝ) * δ σ ≤ (lazyAlg D).cost (p ++ cyc σ n) - (lazyAlg D).cost p := by
            intro σ n D hD p hQ
            induction n with
            | zero => simp [cyc_zero]
            | succ n ih =>
              intro hfail
              have hprev : ¬ W σ ⊆ Set.range ((lazyAlg D).conf (p ++ cyc σ n)) := by
                intro hcover
                have heq := lazy_covered_suffix D (W σ) (p ++ cyc σ n) (v σ) hcover
                  (fun r hr => (v_mem σ r).mp hr)
                apply hfail
                rw [cyc_succ, ← List.append_assoc, heq]
                exact hcover
              have hprevCost := ih hprev
              have hlast : δ σ ≤ (lazyAlg D).cost ((p ++ cyc σ n) ++ v σ) -
                  (lazyAlg D).cost (p ++ cyc σ n) := by
                by_contra hnot
                have hsmall := lt_of_not_ge hnot
                have hQprev := Q_padding σ p (cyc σ n) hQ (cyc_mem σ n)
                have hstates : ∀ ρ : List M, ρ <+: v σ → ∀ i,
                    (lazyAlg D).conf ((p ++ cyc σ n) ++ ρ) i ∈ Q σ := by
                  intro ρ hρ i
                  apply Q_padding σ (p ++ cyc σ n) ρ hQprev
                    (fun r hr => (v_mem σ r).mp (hρ.subset hr))
                  exact lazy_range D hD _ i
                obtain ⟨heq, hcovered⟩ := small_path (lazyAlg D) (Q σ) (δ σ) (hδ σ)
                  (hsep σ) (p ++ cyc σ n) (v σ) hstates hsmall
                apply hfail
                rw [cyc_succ, ← List.append_assoc, heq]
                intro r hr
                exact hcovered r ((v_mem σ r).mpr hr)
              rw [cyc_succ, ← List.append_assoc]
              push_cast
              nlinarith
          let ps : List M → List M × List M := fun σ => σ.foldl (fun p r =>
            (p.1 ++ [r], (p.2 ++ [r]) ++ cyc (p.1 ++ [r]) (N (p.1 ++ [r])))) ([], [])
          have ps_first : ∀ σ : List M, (ps σ).1 = σ := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil => rfl
            | append_singleton σ r ih =>
              simp only [ps, List.foldl_append, List.foldl_cons, List.foldl_nil]
              change (ps σ).1 ++ [r] = σ ++ [r]
              rw [ih]
          let φ : List M → List M := fun σ => (ps σ).2
          have φ_nil : φ [] = [] := rfl
          have φ_append : ∀ (σ : List M) (r : M),
              φ (σ ++ [r]) = (φ σ ++ [r]) ++ cyc (σ ++ [r]) (N (σ ++ [r])) := by
            intro σ r
            simp only [φ, ps, List.foldl_append, List.foldl_cons, List.foldl_nil]
            change ((ps σ).2 ++ [r]) ++ cyc ((ps σ).1 ++ [r]) (N ((ps σ).1 ++ [r])) = _
            rw [ps_first]
          have φ_work : ∀ (σ : List M) (s : KServer.Config k M),
              KServer.workFnU s₀ (φ σ) s = KServer.workFnU s₀ σ s := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil => intro s; rfl
            | append_singleton σ r ih =>
              intro s
              have he := workU_extend (φ σ) σ ih [r]
              have hpad : ∀ x ∈ cyc (σ ++ [r]) (N (σ ++ [r])), x ∈ W (φ σ ++ [r]) := by
                intro x hx
                have hx' := cyc_mem (σ ++ [r]) (N (σ ++ [r])) x hx
                change KnownCover s₀ (φ σ ++ [r]) {x}
                change KnownCover s₀ (σ ++ [r]) {x} at hx'
                intro t
                obtain ⟨u, hu, hcost⟩ := hx' t
                exact ⟨u, hu, by simpa only [he] using hcost⟩
              rw [φ_append, known_padding (φ σ ++ [r]) _ hpad, he s]
          have Q_append : ∀ σ τ : List M, Q (σ ++ τ) = Q σ ∪ τ.toFinset := by
            intro σ τ
            simp [Q, Finset.union_assoc]
          have φ_Q : ∀ σ : List M, Q (φ σ) = Q σ := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil => rfl
            | append_singleton σ r ih =>
              have hbase : Q (φ σ ++ [r]) = Q (σ ++ [r]) := by rw [Q_append, Q_append, ih]
              have hsub := Q_padding (σ ++ [r]) (φ σ ++ [r]) (cyc (σ ++ [r]) (N (σ ++ [r])))
                (by rw [hbase]) (cyc_mem _ _)
              apply Finset.Subset.antisymm
              · rwa [φ_append]
              · rw [φ_append]
                calc
                  Q (σ ++ [r]) = Q (φ σ ++ [r]) := hbase.symm
                  _ ⊆ Q ((φ σ ++ [r]) ++ cyc (σ ++ [r]) (N (σ ++ [r]))) := by
                    rw [Q_append (φ σ ++ [r]) (cyc (σ ++ [r]) (N (σ ++ [r])))]
                    exact Finset.subset_union_left
          have move_diam : ∀ (σ : List M) (s t : KServer.Config k M),
              (∀ i, s i ∈ Q σ) → (∀ i, t i ∈ Q σ) → KServer.moveCost s t ≤ (k : ℝ) * E σ := by
            intro σ s t hs ht
            calc
              KServer.moveCost s t ≤ ∑ _ : Fin k, E σ :=
                Finset.sum_le_sum (fun i _ => hdiam σ (s i) (hs i) (t i) (ht i))
              _ = _ := by simp
          have work_nil_zero : KServer.workFnU s₀ [] s₀ = 0 := by
            apply le_antisymm _ (workU_nonneg [] s₀)
            unfold KServer.workFnU
            refine (ciInf_le (Finite.bddBelow_range _) (Equiv.refl _)).trans ?_
            change KServer.workFn s₀ [] s₀ ≤ 0
            unfold KServer.workFn
            apply csInf_le
            · refine ⟨0, ?_⟩
              rintro c ⟨S, hS, rfl⟩
              exact add_nonneg (Finset.sum_nonneg (fun j _ => move_nonneg _ _)) (move_nonneg _ _)
            · refine ⟨fun _ => s₀, ⟨rfl, ?_⟩, ?_⟩
              · intro j
                exact Fin.elim0 j
              · simp [KServer.moveCost]
          have cover_nil : ∀ V : Set M, KnownCover s₀ [] V → V ⊆ Set.range s₀ := by
            intro V hV
            obtain ⟨t, ht, hcost⟩ := hV s₀
            rw [work_nil_zero] at hcost
            have hmatch : matchingCost t s₀ = 0 := by
              have := workU_nonneg [] t
              have := matching_nonneg t s₀
              linarith
            exact (matching_zero t s₀ hmatch) ▸ ht
          let C : List M → Type := fun σ =>
            {s : Fin k → {x : M // x ∈ Q σ} //
              W σ ⊆ Set.range (fun i => (s i).val) ∧
              (σ = [] → (fun i => (s i).val) = s₀)}
          have C_nonempty : ∀ σ : List M, Nonempty (C σ) := by
            intro σ
            obtain ⟨p, hp, heq, hlow, hcov⟩ := optimal_endpoint σ
            refine ⟨⟨fun i => ⟨p.2 i, F_range σ p hp i⟩, covers_W σ p.2 hcov, ?_⟩⟩
            intro hσ
            subst σ
            have hp' : p = (0, s₀) := by simpa [F_nil] using hp
            subst p
            rfl
          letI : ∀ σ : List M, Nonempty (C σ) := C_nonempty
          letI : ∀ σ : List M, Fintype (C σ) := fun σ => Fintype.ofFinite (C σ)
          letI : ∀ σ : List M, TopologicalSpace (C σ) := fun _ => ⊥
          letI : ∀ σ : List M, DiscreteTopology (C σ) := fun _ => ⟨rfl⟩
          letI : ∀ σ : List M, CompactSpace (C σ) := fun σ => inferInstance
          letI : ∀ σ : List M, T2Space (C σ) := fun σ => inferInstance
          let X := (σ : List M) → C σ
          letI : TopologicalSpace X := Pi.topologicalSpace
          letI : MeasurableSpace X := borel X
          letI : BorelSpace X := ⟨rfl⟩
          let d : X := fun σ => Classical.choice (C_nonempty σ)
          let alg : X → KServer.OnlineAlgorithm k M := fun x => {
            conf := fun σ i => ((x σ).val i).val
            serves := by
              intro σ r
              exact (x (σ ++ [r])).property.1 (W_last σ r) }
          have alg_initial : ∀ x : X, (alg x).conf [] = s₀ := by
            intro x
            exact (x []).property.2 rfl
          have alg_covers : ∀ (x : X) (σ : List M) (V : Set M), KnownCover s₀ σ V →
              V ⊆ Set.range ((alg x).conf σ) := by
            intro x σ V hV
            exact (W_contains σ V hV).trans (x σ).property.1
          have alg_cost_cont : ∀ σ : List M, Continuous (fun x : X => (alg x).cost σ) := by
            intro σ
            have hconf : ∀ (τ : List M) (i : Fin k), Continuous (fun x : X => (alg x).conf τ i) := by
              intro τ i
              exact (continuous_of_discreteTopology : Continuous
                (fun c : C τ => (c.val i).val)).comp (continuous_apply τ)
            unfold KServer.OnlineAlgorithm.cost KServer.moveCost
            apply continuous_finset_sum
            intro j hj
            apply continuous_finset_sum
            intro i hi
            exact (hconf _ i).dist (hconf _ i)
          have alg_cost_meas : ∀ σ : List M, Measurable (fun x : X => (alg x).cost σ) :=
            fun σ => (alg_cost_cont σ).measurable
          have transfer : (∃ φ : List M → List M,
              (∀ σ, KServer.offlineCost s₀ (φ σ) = KServer.offlineCost s₀ σ) ∧
              (∀ (D : KServer.OnlineAlgorithm k M), D.conf [] = s₀ →
                ∃ x : X, ∀ σ, (alg x).cost σ ≤ D.cost (φ σ))) →
              ∃ B : KServer.RandomizedAlgorithm k M,
                B.IsCompetitiveFrom s₀ α ∧ ∀ (σ : List M) (V : Set M), KnownCover s₀ σ V →
                  ∀ᵐ i ∂B.μ, V ⊆ Set.range ((B.alg i).conf σ) := by
            rintro ⟨φ, hφ, hsim⟩
            letI : IsProbabilityMeasure A.μ := A.prob
            obtain ⟨a, ha⟩ := hA.2
            let EC : List M → ProbabilityMeasure X → ENNReal :=
              fun σ P => ∫⁻ x, ENNReal.ofReal ((alg x).cost σ) ∂(P : Measure X)
            have hEC : ∀ σ, Continuous (EC σ) := by
              intro σ
              let f : C(X, NNReal) := ⟨fun x => Real.toNNReal ((alg x).cost σ),
                continuous_real_toNNReal.comp (alg_cost_cont σ)⟩
              exact ProbabilityMeasure.continuous_lintegral_continuousMap f
            let T : List M → Set (ProbabilityMeasure X) :=
              fun σ => {P | EC σ P ≤ ENNReal.ofReal (α * KServer.offlineCost s₀ σ + a)}
            have hT : ∀ σ, IsClosed (T σ) := by
              intro σ
              exact isClosed_le (hEC σ) continuous_const
            have finite_feasible : ∀ S : Finset (List M), (⋂ σ ∈ S, T σ).Nonempty := by
              intro S
              let J : Finset (List M) := S.biUnion fun σ =>
                (Finset.range (σ.length + 1)).image (fun j => σ.take j)
              let U : Finset X := Finset.univ.image (fun u : (τ : {τ // τ ∈ J}) → C τ.val =>
                fun τ => if hτ : τ ∈ J then u ⟨τ, hτ⟩ else d τ)
              let P : A.ι → X → Prop := fun i x => ∀ σ ∈ S, (alg x).cost σ ≤ (A.alg i).cost (φ σ)
              have P_meas : ∀ x : X, MeasurableSet {i | P i x} := by
                intro x
                convert Finset.measurableSet_biInter S (fun σ hσ =>
                  measurableSet_le (measurable_const : Measurable (fun _ : A.ι => (alg x).cost σ))
                    (A.meas (φ σ))) using 1
                ext i
                simp [P]
              have P_exists : ∀ i : A.ι, ∃ x ∈ U, P i x := by
                intro i
                obtain ⟨x, hx⟩ := hsim (A.alg i) (hA.1 i)
                let u : (τ : {τ // τ ∈ J}) → C τ.val := fun τ => x τ.val
                let y : X := fun τ => if hτ : τ ∈ J then u ⟨τ, hτ⟩ else d τ
                refine ⟨y, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, ?_⟩
                intro σ hσ
                have hxy : ∀ j, j ≤ σ.length → (alg y).conf (σ.take j) = (alg x).conf (σ.take j) := by
                  intro j hj
                  have hJ : σ.take j ∈ J := Finset.mem_biUnion.mpr ⟨σ, hσ,
                    Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩⟩
                  simp only [alg, y, dif_pos hJ, u]
                have hc : (alg y).cost σ = (alg x).cost σ := by
                  unfold KServer.OnlineAlgorithm.cost
                  apply Finset.sum_congr rfl
                  intro j hj
                  have hj' := Finset.mem_range.mp hj
                  rw [hxy j (by omega), hxy (j + 1) (by omega)]
                rw [hc]
                exact hx σ
              have select : ∀ K : Finset X, ∃ f : A.ι → X,
                  Measurable f ∧ ∀ i, (∃ x ∈ K, P i x) → P i (f i) := by
                intro K
                induction K using Finset.induction_on with
                | empty => exact ⟨fun _ => d, measurable_const, by simp⟩
                | @insert x K hx ih =>
                  obtain ⟨f, hf, hgood⟩ := ih
                  refine ⟨fun i => if P i x then x else f i,
                    Measurable.ite (P_meas x) measurable_const hf, ?_⟩
                  intro i hi
                  by_cases hix : P i x
                  · simpa [hix] using hix
                  · simp only [if_neg hix]
                    apply hgood i
                    obtain ⟨y, hy, hp⟩ := hi
                    rcases Finset.mem_insert.mp hy with heq | hy
                    · subst y; exact False.elim (hix hp)
                    · exact ⟨y, hy, hp⟩
              obtain ⟨f, hf, hgood⟩ := select U
              let Pμ : ProbabilityMeasure X := ProbabilityMeasure.map (⟨A.μ, A.prob⟩ : ProbabilityMeasure A.ι) hf.aemeasurable
              refine ⟨Pμ, ?_⟩
              apply Set.mem_iInter.mpr
              intro σ
              apply Set.mem_iInter.mpr
              intro hσ
              change EC σ Pμ ≤ _
              calc
                EC σ Pμ = ∫⁻ i, ENNReal.ofReal ((alg (f i)).cost σ) ∂A.μ := by
                  dsimp only [EC]
                  change (∫⁻ x, ENNReal.ofReal ((alg x).cost σ) ∂Measure.map f A.μ) = _
                  exact lintegral_map (ENNReal.measurable_ofReal.comp (alg_cost_meas σ)) hf
                _ ≤ A.expCost (φ σ) := by
                  apply lintegral_mono
                  intro i
                  exact ENNReal.ofReal_le_ofReal (hgood i (P_exists i) σ hσ)
                _ ≤ ENNReal.ofReal (α * KServer.offlineCost s₀ σ + a) := by
                  simpa only [hφ σ] using ha (φ σ)
            obtain ⟨Pμ, hPμ⟩ := CompactSpace.iInter_nonempty hT finite_feasible
            let B : KServer.RandomizedAlgorithm k M := {
              ι := X
              μ := (Pμ : Measure X)
              prob := inferInstance
              alg := alg
              meas := alg_cost_meas }
            refine ⟨B, ⟨alg_initial, a, ?_⟩, ?_⟩
            · intro σ
              exact Set.mem_iInter.mp hPμ σ
            · intro σ V hV
              exact Filter.Eventually.of_forall (fun x => alg_covers x σ V hV)
          apply transfer
          refine ⟨φ, (fun σ => offline_work_eq (φ σ) σ (φ_work σ)), ?_⟩
          intro D hD
          obtain ⟨opt, hopt⟩ := Classical.axiomOfChoice (fun σ => optimal_endpoint σ)
          have opt_mem : ∀ σ, opt σ ∈ F σ := fun σ => (hopt σ).1
          have opt_cover : ∀ σ, W σ ⊆ Set.range (opt σ).2 :=
            fun σ => covers_W σ (opt σ).2 (hopt σ).2.2.2
          have opt_nil : (opt []).2 = s₀ := by
            have hp : opt [] = (0, s₀) := by simpa [F_nil] using opt_mem []
            rw [hp]
          let b : List M → KServer.Config k M := fun σ =>
            if W σ ⊆ Set.range ((lazyAlg D).conf (φ σ)) then (lazyAlg D).conf (φ σ) else (opt σ).2
          have b_covers : ∀ σ, W σ ⊆ Set.range (b σ) := by
            intro σ
            dsimp only [b]
            split_ifs with h
            · exact h
            · exact opt_cover σ
          have b_nil : b [] = s₀ := by
            dsimp only [b]
            split_ifs
            · rw [φ_nil, lazy_nil, hD]
            · exact opt_nil
          have b_range : ∀ σ i, b σ i ∈ Q σ := by
            intro σ i
            dsimp only [b]
            split_ifs
            · rw [← φ_Q σ]
              exact lazy_range D hD (φ σ) i
            · exact F_range σ (opt σ) (opt_mem σ) i
          let BD : KServer.OnlineAlgorithm k M := {
            conf := b
            serves := fun σ r => b_covers (σ ++ [r]) (W_last σ r) }
          have simulation_bound : ∀ σ : List M,
              BD.cost σ + KServer.moveCost (b σ) ((lazyAlg D).conf (φ σ)) ≤ (lazyAlg D).cost (φ σ) := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil => simp [cost_nil, φ_nil, b_nil, lazy_nil, hD, move_self]
            | append_singleton σ r ih =>
              rw [cost_append]
              change BD.cost σ + KServer.moveCost (b σ) (b (σ ++ [r])) +
                KServer.moveCost (b (σ ++ [r])) ((lazyAlg D).conf (φ (σ ++ [r]))) ≤ _
              by_cases hcover : W (σ ++ [r]) ⊆ Set.range ((lazyAlg D).conf (φ (σ ++ [r])))
              · have hb : b (σ ++ [r]) = (lazyAlg D).conf (φ (σ ++ [r])) := if_pos hcover
                rw [hb, move_self, add_zero]
                have htri := move_triangle (b σ) ((lazyAlg D).conf (φ σ))
                  ((lazyAlg D).conf (φ (σ ++ [r])))
                have hpath := move_path (lazyAlg D) (φ σ)
                  ([r] ++ cyc (σ ++ [r]) (N (σ ++ [r])))
                have hpath' : KServer.moveCost ((lazyAlg D).conf (φ σ))
                    ((lazyAlg D).conf (φ (σ ++ [r]))) ≤
                    (lazyAlg D).cost (φ (σ ++ [r])) - (lazyAlg D).cost (φ σ) := by
                  simpa only [← List.append_assoc, ← φ_append] using hpath
                linarith
              · have hb : b (σ ++ [r]) = (opt (σ ++ [r])).2 := if_neg hcover
                rw [hb]
                have hbase : Q (φ σ ++ [r]) = Q (σ ++ [r]) := by rw [Q_append, Q_append, φ_Q]
                have hbaseRange : ∀ i, (lazyAlg D).conf (φ σ ++ [r]) i ∈ Q (σ ++ [r]) := by
                  intro i
                  rw [← hbase]
                  exact lazy_range D hD _ i
                have hfinalRange : ∀ i, (lazyAlg D).conf (φ (σ ++ [r])) i ∈ Q (σ ++ [r]) := by
                  intro i
                  rw [← φ_Q]
                  exact lazy_range D hD _ i
                have hoptRange : ∀ i, (opt (σ ++ [r])).2 i ∈ Q (σ ++ [r]) :=
                  F_range _ _ (opt_mem _)
                have hmove₁ := move_diam (σ ++ [r]) ((lazyAlg D).conf (φ σ ++ [r]))
                  (opt (σ ++ [r])).2 hbaseRange hoptRange
                have hmove₂ := move_diam (σ ++ [r]) (opt (σ ++ [r])).2
                  ((lazyAlg D).conf (φ (σ ++ [r]))) hoptRange hfinalRange
                have hforce := force_cycles (σ ++ [r]) (N (σ ++ [r])) D hD (φ σ ++ [r])
                  (by rw [hbase]) (by simpa only [← φ_append] using hcover)
                rw [← φ_append] at hforce
                have hcycle := hN (σ ++ [r])
                have hc := cost_append (lazyAlg D) (φ σ) r
                have htri₁ := move_triangle (b σ) ((lazyAlg D).conf (φ σ))
                  ((lazyAlg D).conf (φ σ ++ [r]))
                have htri₂ := move_triangle (b σ) ((lazyAlg D).conf (φ σ ++ [r]))
                  (opt (σ ++ [r])).2
                linarith
          let x : X := fun σ => ⟨fun i => ⟨b σ i, b_range σ i⟩, b_covers σ, fun hσ => hσ ▸ b_nil⟩
          refine ⟨x, ?_⟩
          intro σ
          change BD.cost σ ≤ D.cost (φ σ)
          have hsim := simulation_bound σ
          have hret := move_nonneg (b σ) ((lazyAlg D).conf (φ σ))
          have hlazy := lazy_bound D (φ σ)
          have hret' := move_nonneg ((lazyAlg D).conf (φ σ)) (D.conf (φ σ))
          linarith

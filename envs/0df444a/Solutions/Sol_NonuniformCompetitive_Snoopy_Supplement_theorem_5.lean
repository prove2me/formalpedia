-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:41.981818+00:00
-- url     : https://prove2.me/submissions/ef08418f-2aa8-4625-98d6-38c4bace08bc

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_adaptiveSnoopy

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 5, p.554: adaptive online lower bound, already witnessed by one
block. At least two processors and positive integral transfer cost are the
nondegenerate source setting. Randomized policies are arbitrary causal policies,
not only phase or threshold policies. The same a must cover arbitrarily many
bounded interactions. Observed actions must be measurable, as required for the
source's adaptive random experiment. -/
theorem solution (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p)
    (s₀ : NonuniformCompetitive.Snoopy.State n)
    (A : NonuniformCompetitive.Snoopy.RandomizedAlgorithm n p) (hreg : SnoopyRegular A)
    (c : ℝ) (hA : SnoopyAdaptiveCompetitive A s₀ c) : 2 ≤ c := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      classical
      obtain ⟨hinit, a, ha⟩ := hA
      have hcR : Countable (NonuniformCompetitive.Snoopy.Req (m+2)) := by
        refine Function.Injective.countable (f := fun r : NonuniformCompetitive.Snoopy.Req (m+2) =>
          match r with | .read i => (false, i) | .write i => (true, i)) ?_
        intro x y h; cases x <;> cases y <;> simp_all
      have hcost : ∀ (X : NonuniformCompetitive.Snoopy.OnlineAlgorithm (m+2))
          (l : List (NonuniformCompetitive.Snoopy.Req (m+2))) (r : NonuniformCompetitive.Snoopy.Req (m+2)),
          X.cost p (l ++ [r]) = X.cost p l + NonuniformCompetitive.Snoopy.stepCost p r (X.after l)
            (X.moment (l ++ [r])) (X.after (l ++ [r])) := by
        intro X l r
        have hlen : (l ++ [r]).length = l.length + 1 := by simp
        unfold NonuniformCompetitive.Snoopy.OnlineAlgorithm.cost
        rw [← (finCongr hlen.symm).sum_comp, Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro j _
          have hj := j.isLt
          simp only [finCongr_apply, Fin.val_cast, Fin.val_castSucc]
          rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
          congr 1
          simp [List.getElem_append_left hj]
        · simp only [finCongr_apply, Fin.val_cast, Fin.val_last]
          rw [List.take_of_length_le (l := l ++ [r]) (i := l.length + 1) (by simp)]
          rw [List.take_append_of_le_length (le_refl _), List.take_length]
          simp
      let nr : State (m+2) → Option (Req (m+2)) → Req (m+2) := fun s L =>
        if s = some 0 then .read 1 else if L = some (.read 0) ∨ L = some (.write 0) then .write 0 else .read 0
      let S : SnoopyStrategy (m+2) := ⟨fun h => some (nr ((h.getLast?.map (fun x => x.2.2)).getD s₀)
        (h.getLast?.map (fun x => x.1)))⟩
      have hplay : ∀ (X : OnlineAlgorithm (m+2)), X.after [] = s₀ → ∀ N,
          ((snoopyPlay X S N).getLast?.map (fun x => x.2.2)).getD s₀ = X.after (snoopyInput X S N) ∧
          snoopyInput X S (N+1) = snoopyInput X S N ++
            [nr (X.after (snoopyInput X S N)) (snoopyInput X S N).getLast?] := by
        intro X hX N
        have h1 : ∀ N, ((snoopyPlay X S N).getLast?.map (fun x => x.2.2)).getD s₀ = X.after (snoopyInput X S N) := by
          intro N
          induction N with
          | zero => simp [snoopyPlay, snoopyInput, hX]
          | succ k ih =>
            simp only [snoopyInput, snoopyPlay, S]
            simp
        refine ⟨h1 N, ?_⟩
        have := h1 N
        simp only [snoopyInput] at this ⊢
        simp only [snoopyPlay, S, this, List.getLast?_map]
        simp
      have hrec : ∀ i N, snoopyInput (A.alg i) S (N+1) = snoopyInput (A.alg i) S N ++
          [nr ((A.alg i).after (snoopyInput (A.alg i) S N)) (snoopyInput (A.alg i) S N).getLast?] :=
        fun i N => (hplay _ (hinit i) N).2
      have hzero : ∀ X, snoopyInput X S 0 = [] := by simp [snoopyInput, snoopyPlay]
      have hadm1 : ∀ (l : List (Req (m+2))) (s : State (m+2)), Admissible l →
          Admissible (l ++ [nr s l.getLast?]) := by
        intro l s hl j k hj
        rcases lt_trichotomy j l.length with h | h | h
        · rw [List.getElem?_append_left h] at hj
          obtain ⟨h0, h1⟩ := hl j k hj
          refine ⟨h0, ?_⟩
          rw [List.getElem?_append_left (by omega)]
          exact h1
        · subst h
          simp only [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero,
            Option.some.injEq] at hj
          simp only [nr] at hj
          split_ifs at hj with h1 h2
          · cases hj
            have hne : l ≠ [] := by
              rintro rfl; simp at h2
            have hpos : 0 < l.length := List.length_pos_iff.mpr hne
            refine ⟨hpos, ?_⟩
            rw [List.getElem?_append_left (by omega), ← List.getLast?_eq_getElem?]
            exact h2
        · rw [List.getElem?_eq_none (by simp; omega)] at hj
          cases hj
      have hadm : ∀ i N, Admissible (snoopyInput (A.alg i) S N) := by
        intro i N
        induction N with
        | zero => rw [hzero]; intro j k hj; simp at hj
        | succ k ih => rw [hrec]; exact hadm1 _ _ ih
      let B1 : OnlineAlgorithm (m+2) :=
        { after := fun l => if l = [] then s₀ else none
          moment := fun l => if l.getLast?.map Req.isWrite = some true then
              (if l.dropLast = [] then s₀ else none) else none
          lookaheadZero := by intro l i; simp [Req.isWrite] }
      let f2 : Req (m+2) → State (m+2) := fun r => if r = .read 0 ∨ r = .write 0 then some 0 else none
      let B2 : OnlineAlgorithm (m+2) :=
        { after := fun l => (l.getLast?.map f2).getD s₀
          moment := fun l => if l.getLast?.map Req.isWrite = some true then (l.dropLast.getLast?.map f2).getD s₀
              else if (l.dropLast.getLast?.map f2).getD s₀ = some 0 ∧ l.getLast? = some (.read 0) then some 0
              else none
          lookaheadZero := by intro l i; simp [Req.isWrite] }
      have hB1 : B1.after [] = s₀ := rfl
      have hB2 : B2.after [] = s₀ := rfl
      have hstep : ∀ (σ : List (Req (m+2))) (s mo af : State (m+2)),
          ((nr s σ.getLast?).isWrite = true → mo = s) →
          (σ = [] → stepCost p (nr s σ.getLast?) (B1.after σ) (B1.moment (σ++[nr s σ.getLast?]))
              (B1.after (σ++[nr s σ.getLast?])) + stepCost p (nr s σ.getLast?) (B2.after σ)
              (B2.moment (σ++[nr s σ.getLast?])) (B2.after (σ++[nr s σ.getLast?])) ≤ 2 * p) ∧
          (σ ≠ [] → stepCost p (nr s σ.getLast?) (B1.after σ) (B1.moment (σ++[nr s σ.getLast?]))
              (B1.after (σ++[nr s σ.getLast?])) + stepCost p (nr s σ.getLast?) (B2.after σ)
              (B2.moment (σ++[nr s σ.getLast?])) (B2.after (σ++[nr s σ.getLast?]))
              ≤ stepCost p (nr s σ.getLast?) s mo af) ∧
          (stepCost p (nr s σ.getLast?) (B1.after σ) (B1.moment (σ++[nr s σ.getLast?]))
              (B1.after (σ++[nr s σ.getLast?])) + stepCost p (nr s σ.getLast?) (B2.after σ)
              (B2.moment (σ++[nr s σ.getLast?])) (B2.after (σ++[nr s σ.getLast?])) ≤ 2 * p + 1) ∧
          (nr s σ.getLast? ≠ .read 0 → 1 ≤ stepCost p (nr s σ.getLast?) s mo af) ∧
          (nr s σ.getLast? = .read 0 → σ.getLast? ≠ some (.read 0)) := by
        intro σ s mo af hmo
        have hp' : (1:ENNReal) ≤ p := by exact_mod_cast hp
        rcases List.eq_nil_or_concat σ with rfl | ⟨L, b, rfl⟩
        · by_cases hs : s = some 0
          · subst hs
            simp [nr, B1, B2, f2, stepCost, transCost, taskCost, Req.isWrite]
            rcases hs0 : s₀ with _ | k <;> rcases mo with _ | j <;> simp [two_mul, hp'] <;>
              split_ifs <;> simp_all <;> exact le_trans (Nat.one_le_cast.mpr hp) le_self_add
          · simp [nr, hs, B1, B2, f2, stepCost, transCost, taskCost, Req.isWrite]
            rcases hs0 : s₀ with _ | k <;> simp [two_mul, hp'] <;> by_cases hk : k = 0 <;> simp [hk, add_assoc]
        · by_cases hs : s = some 0
          · subst hs
            simp [nr, B1, B2, f2, stepCost, transCost, taskCost, Req.isWrite]
            have h1p : (1:ENNReal) ≤ p := Nat.one_le_cast.mpr hp
            by_cases hb : b = .read 0 ∨ b = .write 0
            · have hb' : ¬(¬b = Req.read 0 ∧ ¬b = Req.write 0) := by tauto
              simp only [hb, hb', if_true, if_false]
              rcases mo with _ | j
              · simp [two_mul, add_assoc]; exact hp
              · by_cases hj : j = 0
                · subst hj; simp [two_mul, add_assoc]
                · simp [hj, two_mul, add_assoc]
                  split_ifs <;> simp [h1p] <;> exact le_trans h1p le_self_add
            · have hb' : (¬b = Req.read 0 ∧ ¬b = Req.write 0) := by tauto
              simp only [hb, hb', if_true, if_false]
              rcases mo with _ | j
              · simp [h1p]
              · by_cases hj : j = 0
                · subst hj; simp
                · simp [hj]
                  split_ifs <;> simp [h1p] <;> exact le_trans h1p le_self_add
          · by_cases hb : b = .read 0 ∨ b = .write 0
            · have hmo' : mo = s := hmo (by simp [nr, hs, hb, Req.isWrite])
              subst hmo'
              simp [nr, hs, hb, B1, B2, f2, stepCost, transCost, taskCost, Req.isWrite]
              split_ifs <;> simp
            · simp [nr, hs, hb, B1, B2, f2, stepCost, transCost, taskCost, Req.isWrite]
              tauto
      have hc0 : ∀ X : OnlineAlgorithm (m+2), X.cost p [] = 0 := fun X => by
        simp [OnlineAlgorithm.cost]
      have hinv : ∀ i N,
          B1.cost p (snoopyInput (A.alg i) S N) + B2.cost p (snoopyInput (A.alg i) S N) ≤
            (A.alg i).cost p (snoopyInput (A.alg i) S N) + 2 * p ∧
          B1.cost p (snoopyInput (A.alg i) S N) + B2.cost p (snoopyInput (A.alg i) S N) ≤
            (2 * p + 1) * N ∧
          (N : ENNReal) ≤ 2 * (A.alg i).cost p (snoopyInput (A.alg i) S N) +
            (if (snoopyInput (A.alg i) S N).getLast? = some (.read 0) then 1 else 0) := by
        intro i N
        induction N with
        | zero => simp only [hzero, hc0]; simp
        | succ N ih =>
          set X := A.alg i with hXdef
          rw [hrec]
          set σ := snoopyInput X S N with hσ
          have hmo : ∀ r : Req (m+2), r.isWrite = true → X.moment (σ ++ [r]) = X.after σ := by
            intro r hw
            cases r with
            | read k => simp [Req.isWrite] at hw
            | write k => exact X.lookaheadZero σ k
          obtain ⟨h1, h2, h3, h4, h5⟩ := hstep σ (X.after σ) (X.moment (σ ++ [nr (X.after σ) σ.getLast?]))
            (X.after (σ ++ [nr (X.after σ) σ.getLast?])) (hmo _)
          rw [hcost X, hcost B1, hcost B2]
          obtain ⟨ih1, ih2, ih3⟩ := ih
          set r := nr (X.after σ) σ.getLast? with hr
          set x := X.cost p σ
          set y1 := B1.cost p σ
          set y2 := B2.cost p σ
          set dA := stepCost p r (X.after σ) (X.moment (σ ++ [r])) (X.after (σ ++ [r]))
          set d1 := stepCost p r (B1.after σ) (B1.moment (σ ++ [r])) (B1.after (σ ++ [r]))
          set d2 := stepCost p r (B2.after σ) (B2.moment (σ ++ [r])) (B2.after (σ ++ [r]))
          refine ⟨?_, ?_, ?_⟩
          · by_cases hσe : σ = []
            · have hy1 : y1 = 0 := by show B1.cost p σ = 0; rw [hσe, hc0]
              have hy2 : y2 = 0 := by show B2.cost p σ = 0; rw [hσe, hc0]
              calc y1 + d1 + (y2 + d2) = d1 + d2 := by rw [hy1, hy2]; ring
                _ ≤ 2 * p := h1 hσe
                _ ≤ x + dA + 2 * p := le_add_self
            · calc y1 + d1 + (y2 + d2) = (y1 + y2) + (d1 + d2) := by ring
                _ ≤ (x + 2 * p) + dA := add_le_add ih1 (h2 hσe)
                _ = x + dA + 2 * p := by ring
          · calc y1 + d1 + (y2 + d2) = (y1 + y2) + (d1 + d2) := by ring
              _ ≤ (2 * p + 1) * N + (2 * p + 1) := add_le_add ih2 h3
              _ = (2 * p + 1) * ((N + 1 : ℕ) : ENNReal) := by push_cast; ring
          · rw [List.getLast?_concat]
            by_cases hr0 : r = .read 0
            · have hind : ¬ σ.getLast? = some (.read 0) := h5 hr0
              rw [if_neg hind, add_zero] at ih3
              rw [hr0, if_pos rfl]
              calc ((N + 1 : ℕ) : ENNReal) = N + 1 := by push_cast; ring
                _ ≤ 2 * x + 1 := by gcongr
                _ ≤ 2 * (x + dA) + 1 := by gcongr; exact le_self_add
            · have hdA : 1 ≤ dA := h4 hr0
              have hne : ¬ some r = some (Req.read (0 : Fin (m+2))) := by simpa using hr0
              rw [if_neg hne, add_zero]
              have hind : (if σ.getLast? = some (Req.read 0) then (1:ENNReal) else 0) ≤ 1 := by
                split_ifs <;> simp
              calc ((N + 1 : ℕ) : ENNReal) = N + 1 := by push_cast; ring
                _ ≤ 2 * x + 1 + 1 := by gcongr; exact ih3.trans (by gcongr)
                _ = 2 * x + 2 * 1 := by ring
                _ ≤ 2 * (x + dA) := by rw [mul_add]; gcongr
      letI := A.ms
      haveI := A.prob
      have hset2 : ∀ (l' l : List (Req (m+2))),
          MeasurableSet {i | l' ++ [nr ((A.alg i).after l') l'.getLast?] = l} := by
        intro l' l
        have : {i | l' ++ [nr ((A.alg i).after l') l'.getLast?] = l} =
            ⋃ s : State (m+2), {i | (A.alg i).after l' = s} ∩ {_i | l' ++ [nr s l'.getLast?] = l} := by
          ext i; simp
        rw [this]
        exact MeasurableSet.iUnion fun s => (hreg l' s).2.inter (MeasurableSet.const _)
      have hfib : ∀ N (l : List (Req (m+2))), MeasurableSet {i | snoopyInput (A.alg i) S N = l} := by
        intro N
        induction N with
        | zero => intro l; simp only [hzero]; exact MeasurableSet.const _
        | succ N ih =>
          intro l
          have : {i | snoopyInput (A.alg i) S (N+1) = l} = ⋃ l' : List (Req (m+2)),
              {i | snoopyInput (A.alg i) S N = l'} ∩
                {i | l' ++ [nr ((A.alg i).after l') l'.getLast?] = l} := by
            ext i; simp only [hrec, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
            constructor
            · intro h; exact ⟨_, rfl, h⟩
            · rintro ⟨l', h1, h2⟩; subst h1; exact h2
          rw [this]
          exact MeasurableSet.iUnion fun l' => (ih l').inter (hset2 l' l)
      have hmeasF : ∀ N (G : A.ι → List (Req (m+2)) → ENNReal), (∀ l, Measurable fun i => G i l) →
          Measurable fun i => G i (snoopyInput (A.alg i) S N) := by
        intro N G hG t ht
        have : (fun i => G i (snoopyInput (A.alg i) S N)) ⁻¹' t =
            ⋃ l, {i | snoopyInput (A.alg i) S N = l} ∩ (fun i => G i l) ⁻¹' t := by
          ext i; simp
        rw [this]
        exact MeasurableSet.iUnion fun l => (hfib N l).inter (hG l ht)
      by_contra hc
      push_neg at hc
      set c' := max c 0 with hc'
      have hc'2 : c' < 2 := max_lt hc (by norm_num)
      have hc'0 : 0 ≤ c' := le_max_right _ _
      obtain ⟨N, hN⟩ := exists_nat_gt (1 + 2 * (4 * (p:ℝ) + 2 * |a|) / (2 - c'))
      have hmA := hmeasF N (fun i l => (A.alg i).cost p l) (fun l => A.meas l)
      have hm1 := hmeasF N (fun _ l => B1.cost p l) (fun l => measurable_const)
      have hm2 := hmeasF N (fun _ l => B2.cost p l) (fun l => measurable_const)
      set EA := snoopyInteractingCost A S N with hEA
      set E1 := snoopyComparatorCost A S N B1 with hE1
      set E2 := snoopyComparatorCost A S N B2 with hE2
      have hF1 : E1 + E2 ≤ EA + 2 * p := by
        rw [hE1, hE2, hEA, snoopyComparatorCost, snoopyComparatorCost, snoopyInteractingCost,
          ← MeasureTheory.lintegral_add_left hm1]
        calc ∫⁻ i, (B1.cost p (snoopyInput (A.alg i) S N) + B2.cost p (snoopyInput (A.alg i) S N)) ∂A.μ
            ≤ ∫⁻ i, ((A.alg i).cost p (snoopyInput (A.alg i) S N) + 2 * p) ∂A.μ :=
              MeasureTheory.lintegral_mono fun i => (hinv i N).1
          _ = _ := by rw [MeasureTheory.lintegral_add_right _ measurable_const]; simp
      have hF2 : E1 + E2 ≤ (2 * p + 1) * N := by
        rw [hE1, hE2, snoopyComparatorCost, snoopyComparatorCost, ← MeasureTheory.lintegral_add_left hm1]
        calc ∫⁻ i, (B1.cost p (snoopyInput (A.alg i) S N) + B2.cost p (snoopyInput (A.alg i) S N)) ∂A.μ
            ≤ ∫⁻ _i, ((2 * p + 1) * N : ENNReal) ∂A.μ :=
              MeasureTheory.lintegral_mono fun i => (hinv i N).2.1
          _ = _ := by simp
      have hF3 : (N : ENNReal) ≤ 2 * EA + 1 := by
        rw [hEA, snoopyInteractingCost]
        calc (N : ENNReal) = ∫⁻ _i, (N : ENNReal) ∂A.μ := by simp
          _ ≤ ∫⁻ i, (2 * (A.alg i).cost p (snoopyInput (A.alg i) S N) + 1) ∂A.μ := by
              refine MeasureTheory.lintegral_mono fun i => (hinv i N).2.2.trans ?_
              gcongr
              split_ifs <;> simp
          _ = _ := by
              rw [MeasureTheory.lintegral_add_right _ measurable_const,
                MeasureTheory.lintegral_const_mul _ hmA]
              simp
      have h2p : 2 * (p : ENNReal) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
      have hfin : (2 * (p : ENNReal) + 1) * N ≠ ⊤ := by
        exact ENNReal.mul_ne_top (by simp [h2p]) (by simp)
      have hE1t : E1 ≠ ⊤ := ne_top_of_le_ne_top hfin (le_trans le_self_add hF2)
      have hE2t : E2 ≠ ⊤ := ne_top_of_le_ne_top hfin (le_trans le_add_self hF2)
      have hA1 := ha N S B1 hB1 (fun i => hadm i N) hmA hm1 hE1t
      have hA2 := ha N S B2 hB2 (fun i => hadm i N) hmA hm2 hE2t
      rw [← hEA, ← hE1] at hA1
      rw [← hEA, ← hE2] at hA2
      have hEAt : EA ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA1
      have h2EA : 2 * EA ≠ ⊤ := ENNReal.mul_ne_top (by simp) hEAt
      set X := EA.toReal
      set Y1 := E1.toReal
      set Y2 := E2.toReal
      have hY1 : 0 ≤ Y1 := ENNReal.toReal_nonneg
      have hY2 : 0 ≤ Y2 := ENNReal.toReal_nonneg
      have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
      have hX1 : X ≤ c' * Y1 + |a| := by
        refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hA1.trans (ENNReal.ofReal_le_ofReal ?_))
        have : c * Y1 ≤ c' * Y1 := mul_le_mul_of_nonneg_right (le_max_left _ _) hY1
        linarith [le_abs_self a]
      have hX2 : X ≤ c' * Y2 + |a| := by
        refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hA2.trans (ENNReal.ofReal_le_ofReal ?_))
        have : c * Y2 ≤ c' * Y2 := mul_le_mul_of_nonneg_right (le_max_left _ _) hY2
        linarith [le_abs_self a]
      have hR1 : Y1 + Y2 ≤ X + 2 * p := by
        have := (ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hE1t, hE2t⟩)
          (ENNReal.add_ne_top.2 ⟨hEAt, h2p⟩)).2 hF1
        rw [ENNReal.toReal_add hE1t hE2t, ENNReal.toReal_add hEAt h2p] at this
        simpa using this
      have hR3 : (N : ℝ) ≤ 2 * X + 1 := by
        have := (ENNReal.toReal_le_toReal (by simp) (by simp [h2EA])).2 hF3
        rw [ENNReal.toReal_add h2EA (by simp), ENNReal.toReal_mul] at this
        simpa using this
      have hkey : (2 - c') * X ≤ 4 * p + 2 * |a| := by
        have : 2 * X ≤ c' * (X + 2 * p) + 2 * |a| := by nlinarith
        nlinarith
      have hpos : 0 < 2 - c' := by linarith
      have hN' : 2 * (4 * (p:ℝ) + 2 * |a|) < (N - 1) * (2 - c') := by
        have := (div_lt_iff₀ hpos).1 (by linarith : 2 * (4 * (p:ℝ) + 2 * |a|) / (2 - c') < N - 1)
        linarith
      nlinarith

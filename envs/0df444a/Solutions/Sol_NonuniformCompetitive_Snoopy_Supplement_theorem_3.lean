-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:31:19.155207+00:00
-- url     : https://prove2.me/submissions/8ee01a51-349b-434b-8bbe-0a0b90f418f3

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_phaseSystem

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 3, pp.548–549, with the full bounded phase property of p.547.
The LP bounds range over every causal mixed policy on retained phase words,
with initialization at the phase start and almost-sure endpoint agreement.
There is no requirement that such a policy extend transparently across deleted
requests, and no restriction of the competitor to normalized or phase policies.
Reachable phase boundaries are known states of the actual work function, so the
source warm-up prefixes are real task inputs. The infimum is a real greatest
lower bound; an empty or unbounded set is not assigned a default value.
The additive constant is kept inside Competitive, before every input word. -/
theorem solution {S R : Type} [Fintype S] [Fintype R] [LinearOrder S]
    (T : TaskSystem S R) (s₀ : S) (F : PhaseSystem T s₀) (hF : F.Valid)
    (α : ℝ) (hα : IsGLB (phaseBounds F) α) :
    ∀ (A : TaskRandomized T) (c : ℝ), A.Competitive s₀ c → α ≤ c := by
      set_option maxHeartbeats 4000000 in
      focus
        intro A c hA
        classical
        let (B : TaskRandomized T) : MeasurableSpace B.ι := B.ms
        let (B : TaskRandomized T) : MeasureTheory.IsProbabilityMeasure B.μ := B.prob
        let : Nonempty S := ⟨s₀⟩
        have hsc (w : List R) (r : R) (b m s : ℕ → S) :
            taskScheduleCost T (w ++ [r]) b m s = taskScheduleCost T w b m s +
              ((T.distance (s w.length) (b w.length) : ENNReal) +
                (T.distance (b w.length) (m w.length) : ENNReal) +
                T.task r (m w.length) +
                (T.distance (m w.length) (s (w.length + 1)) : ENNReal)) := by
          let : Inhabited R := ⟨r⟩
          unfold taskScheduleCost
          simp only [Fin.getElem_fin, ← getElem!_pos]
          rw [List.length_append, List.length_singleton]
          rw [Fin.sum_univ_castSucc]
          congr 1
          · apply Finset.sum_congr rfl
            intro j _
            simp [List.getElem_append_left j.isLt, j.isLt]
          · simp
        have hw0 (s t : S) : taskWork T s [] t = (T.distance s t : ENNReal) := by
          apply le_antisymm
          · unfold taskWork
            apply iInf_le_of_le (fun _ => s)
            apply iInf_le_of_le (fun _ => s)
            apply iInf_le_of_le (fun _ => s)
            apply iInf_le_of_le (by simp [TaskScheduleOK])
            simp [taskScheduleCost]
          · unfold taskWork
            refine le_iInf fun b => le_iInf fun m => le_iInf fun u => le_iInf fun hu => ?_
            simpa [taskScheduleCost, hu.1]
        have hwrec (s t : S) (w : List R) (r : R) :
            taskWork T s (w ++ [r]) t =
              ⨅ x : S, taskWork T s w x + T.task r x + (T.distance x t : ENNReal) := by
          apply le_antisymm
          · refine le_iInf fun x => ?_
            simp only [taskWork, ENNReal.iInf_add]
            refine le_iInf fun b => le_iInf fun m => le_iInf fun u => le_iInf fun hu => ?_
            let b' : ℕ → S := fun j => if j < w.length then b j else x
            let m' : ℕ → S := fun j => if j < w.length then m j else x
            let u' : ℕ → S := fun j => if j ≤ w.length then u j else t
            have hu' : TaskScheduleOK T s (w ++ [r]) b' m' u' := by
              constructor
              · simpa [u'] using hu.1
              · intro j hj
                by_cases h : (j : ℕ) < w.length
                · simpa [b', m', h] using hu.2 ⟨j, h⟩ (by simpa [List.getElem_append_left h] using hj)
                · simp [b', m', h]
            refine iInf_le_of_le b' (iInf_le_of_le m' (iInf_le_of_le u' (iInf_le_of_le hu' ?_)))
            rw [hsc]
            have heq : taskScheduleCost T w b' m' u' = taskScheduleCost T w b m u := by
              unfold taskScheduleCost
              apply Finset.sum_congr rfl
              intro j _
              simp [b', m', u', j.isLt, Nat.le_of_lt j.isLt, show (j : ℕ) + 1 ≤ w.length from j.isLt]
            rw [heq]
            simp [b', m', u', T.diagonal, add_assoc]
          · unfold taskWork
            refine le_iInf fun b => le_iInf fun m => le_iInf fun u => le_iInf fun hu => ?_
            have hpre : TaskScheduleOK T s w b m u := by
              refine ⟨hu.1, fun j hj => ?_⟩
              exact hu.2 ⟨j, by simpa using Nat.lt_succ_of_lt j.isLt⟩ (by simpa [List.getElem_append_left j.isLt] using hj)
            refine le_trans (iInf_le_of_le (m w.length)
              (a := (taskScheduleCost T w b m u + (T.distance (u w.length) (m w.length) : ENNReal)) +
                T.task r (m w.length) + (T.distance (m w.length) t : ENNReal)) ?_) ?_
            · have hpw : taskWork T s w (m w.length) ≤ taskScheduleCost T w b m u +
                  (T.distance (u w.length) (m w.length) : ENNReal) := by
                unfold taskWork
                exact iInf_le_of_le b (iInf_le_of_le m (iInf_le_of_le u (iInf_le_of_le hpre le_rfl)))
              exact add_le_add_left (add_le_add_left hpw _) _
            · rw [hsc]
              have htri₁ : (T.distance (u w.length) (m w.length) : ENNReal) ≤
                  (T.distance (u w.length) (b w.length) : ENNReal) +
                  (T.distance (b w.length) (m w.length) : ENNReal) := by
                exact_mod_cast T.triangle (u w.length) (b w.length) (m w.length)
              have htri₂ : (T.distance (m w.length) t : ENNReal) ≤
                  (T.distance (m w.length) (u (w.length + 1)) : ENNReal) +
                  (T.distance (u (w.length + 1)) t : ENNReal) := by
                exact_mod_cast T.triangle (m w.length) (u (w.length + 1)) t
              simp only [List.length_append, List.length_singleton]
              calc
                _ ≤ taskScheduleCost T w b m u +
                    ((T.distance (u w.length) (b w.length) : ENNReal) +
                    (T.distance (b w.length) (m w.length) : ENNReal)) + T.task r (m w.length) +
                    ((T.distance (m w.length) (u (w.length + 1)) : ENNReal) +
                    (T.distance (u (w.length + 1)) t : ENNReal)) :=
                  add_le_add (add_le_add_left (add_le_add_right htri₁ _) _) htri₂
                _ = _ := by ac_rfl
        have hwtri (s : S) (w : List R) (x t : S) :
            taskWork T s w t ≤ taskWork T s w x + (T.distance x t : ENNReal) := by
          simp only [taskWork, ENNReal.iInf_add]
          refine le_iInf fun b => le_iInf fun m => le_iInf fun u => le_iInf fun hu => ?_
          refine le_trans (iInf_le_of_le b (iInf_le_of_le m (iInf_le_of_le u
            (iInf_le_of_le hu le_rfl)))) ?_
          have ht : (T.distance (u w.length) t : ENNReal) ≤
              (T.distance (u w.length) x : ENNReal) + (T.distance x t : ENNReal) := by
            exact_mod_cast T.triangle (u w.length) x t
          simpa only [add_assoc] using add_le_add_right ht (taskScheduleCost T w b m u)
        have hraw (s : S) (w : List R) (x : S) (hx : TaskRawKnown T s w x) :
            ∀ t, taskWork T s w t = taskOpt T s w + (T.distance x t : ENNReal) := by
          have ho : taskOpt T s w = taskWork T s w x := by
            apply le_antisymm (iInf_le _ x)
            exact le_iInf fun t => le_trans (le_add_right le_rfl) (hx.2 t)
          intro t
          rw [ho]
          exact le_antisymm (hwtri s w x t) (hx.2 t)
        have ho0 (s : S) : taskOpt T s [] = 0 := by
          apply le_antisymm _ (by positivity)
          exact le_trans (iInf_le _ s) (by simp [hw0, T.diagonal])
        have homono (s : S) (u v : List R) (huv : u.IsPrefix v) :
            taskOpt T s u ≤ taskOpt T s v := by
          obtain ⟨z, rfl⟩ := huv
          induction z using List.reverseRecOn with
          | nil => simp
          | @append_singleton z r ih =>
            apply le_trans ih
            unfold taskOpt
            refine le_iInf fun t => ?_
            rw [← List.append_assoc, hwrec]
            refine le_iInf fun x => ?_
            exact le_trans (iInf_le _ x) (le_add_right (le_add_right le_rfl))
        have hcappend (B : TaskOnline T) (w : List R) (r : R) :
            B.cost (w ++ [r]) = B.cost w + taskActionCost B w r := by
          let : Inhabited R := ⟨r⟩
          unfold TaskOnline.cost
          simp only [Fin.getElem_fin, ← getElem!_pos]
          rw [List.length_append, List.length_singleton]
          rw [Fin.sum_univ_castSucc]
          congr 1
          · apply Finset.sum_congr rfl
            intro j _
            simp [List.getElem_append_left j.isLt,
              List.take_append_of_le_length (Nat.le_of_lt j.isLt),
              List.take_append_of_le_length (show (j : ℕ) + 1 ≤ w.length from j.isLt)]
          · simp [taskActionCost, List.take_of_length_le (show (w ++ [r]).length ≤ w.length + 1 by simp)]
        have hopcost (B : TaskOnline T) (s : S) (hb : B.after [] = s) (w : List R) :
            taskOpt T s w ≤ B.cost w := by
          let b := fun j => B.before (w.take j)
          let m := fun j => B.moment (w.take (j + 1))
          let u := fun j => B.after (w.take j)
          have hu : TaskScheduleOK T s w b m u := by
            refine ⟨by simpa [u] using hb, ?_⟩
            intro j hj
            dsimp only [b, m]
            rw [List.take_succ_eq_append_getElem j.isLt]
            exact B.zero (w.take j) w[j] hj
          refine le_trans (iInf_le _ (B.after w)) ?_
          refine le_trans (iInf_le_of_le b (iInf_le_of_le m (iInf_le_of_le u
            (iInf_le_of_le hu le_rfl)))) ?_
          simp [taskScheduleCost, TaskOnline.cost, b, m, u, T.diagonal]
        have heappend (B : TaskRandomized T) (w : List R) (r : R) :
            B.expCost (w ++ [r]) = B.expCost w + ∫⁻ i, taskActionCost (B.alg i) w r ∂B.μ := by
          simp only [TaskRandomized.expCost, hcappend]
          exact MeasureTheory.lintegral_add_left (B.meas w) _
        have hoexp (B : TaskRandomized T) (s : S) (hb : ∀ i, (B.alg i).after [] = s)
            (w : List R) : taskOpt T s w ≤ B.expCost w := by
          calc
            _ = ∫⁻ _ : B.ι, taskOpt T s w ∂B.μ := by simp
            _ ≤ _ := MeasureTheory.lintegral_mono fun i => hopcost (B.alg i) s (hb i) w
        have hezero (B : TaskRandomized T) : B.expCost [] = 0 := by
          simp [TaskRandomized.expCost, TaskOnline.cost]
        have hFM : ∀ (n : ℕ) (Q : Type) [Finite Q] (M : Q → Fin n → ℝ) (o b : Q → ℝ),
            IsClosed {β : ℝ | ∃ y : Fin n → ℝ, ∀ q, b q ≤ β * o q + ∑ i, M q i * y i} := by
          intro n
          induction n with
          | zero =>
            intro Q _ M o b
            have : {β : ℝ | ∃ y : Fin 0 → ℝ, ∀ q, b q ≤ β * o q + ∑ i, M q i * y i} =
                ⋂ q, {β : ℝ | b q ≤ β * o q} := by
              ext β
              simp
            rw [this]
            exact isClosed_iInter fun q => isClosed_le continuous_const (by fun_prop)
          | succ n ih =>
            intro Q _ M o b
            let P := {q : Q // 0 < M q 0}
            let N := {q : Q // M q 0 < 0}
            let Z := {q : Q // M q 0 = 0}
            let M' : Z ⊕ (P × N) → Fin n → ℝ := fun x => match x with
              | .inl z => fun i => M z.1 i.succ
              | .inr (p, m) => fun i => M p.1 i.succ / M p.1 0 - M m.1 i.succ / M m.1 0
            let o' : Z ⊕ (P × N) → ℝ := fun x => match x with
              | .inl z => o z.1
              | .inr (p, m) => o p.1 / M p.1 0 - o m.1 / M m.1 0
            let b' : Z ⊕ (P × N) → ℝ := fun x => match x with
              | .inl z => b z.1
              | .inr (p, m) => b p.1 / M p.1 0 - b m.1 / M m.1 0
            have key := ih (Z ⊕ (P × N)) M' o' b'
            convert key using 1
            ext β
            simp only [Set.mem_ofPred_eq]
            -- L q y : bound for the eliminated variable
            let L : Q → (Fin n → ℝ) → ℝ := fun q y =>
              (b q - β * o q - ∑ i, M q i.succ * y i) / M q 0
            have hpair : ∀ (p : P) (m : N) (y : Fin n → ℝ),
                (b' (.inr (p, m)) ≤ β * o' (.inr (p, m)) + ∑ i, M' (.inr (p, m)) i * y i) ↔
                  L p.1 y ≤ L m.1 y := by
              intro p m y
              have e : ∑ i, M' (.inr (p, m)) i * y i =
                  (∑ i, M p.1 i.succ * y i) / M p.1 0 - (∑ i, M m.1 i.succ * y i) / M m.1 0 := by
                rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun i _ => ?_
                simp only [M']
                ring
              rw [e]
              simp only [L, b', o']
              constructor
              · intro h
                simp only [sub_div, mul_sub, mul_div_assoc] at h ⊢
                linarith
              · intro h
                simp only [sub_div, mul_sub, mul_div_assoc] at h ⊢
                linarith
            constructor
            · rintro ⟨y, hy⟩
              refine ⟨fun i => y i.succ, ?_⟩
              rintro (z | ⟨p, m⟩)
              · have := hy z.1
                rw [Fin.sum_univ_succ, z.2] at this
                simpa [M', o', b'] using this
              · rw [hpair]
                have h1 := hy p.1
                have h2 := hy m.1
                rw [Fin.sum_univ_succ] at h1 h2
                have g1 : L p.1 (fun i => y i.succ) ≤ y 0 := by
                  simp only [L]
                  rw [div_le_iff₀ p.2]
                  linarith
                have g2 : y 0 ≤ L m.1 (fun i => y i.succ) := by
                  simp only [L]
                  rw [le_div_iff_of_neg m.2]
                  linarith
                exact g1.trans g2
            · rintro ⟨y, hy⟩
              have hex : ∃ y0 : ℝ, (∀ p : P, L p.1 y ≤ y0) ∧ ∀ m : N, y0 ≤ L m.1 y := by
                by_cases hP : Nonempty P
                · refine ⟨⨆ p : P, L p.1 y, fun p => le_ciSup (f := fun p : P => L p.1 y) (Set.finite_range _).bddAbove p, fun m => ciSup_le fun p => ?_⟩
                  exact (hpair p m y).1 (hy (.inr (p, m)))
                · refine ⟨⨅ m : N, L m.1 y, fun p => (hP ⟨p⟩).elim, fun m => ciInf_le (f := fun m : N => L m.1 y) (Set.finite_range _).bddBelow m⟩
              obtain ⟨y0, h1, h2⟩ := hex
              refine ⟨Fin.cons y0 y, fun q => ?_⟩
              rw [Fin.sum_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              rcases lt_trichotomy (M q 0) 0 with h | h | h
              · have := h2 ⟨q, h⟩
                simp only [L] at this
                rw [le_div_iff_of_neg h] at this
                linarith
              · have := hy (.inl ⟨q, h⟩)
                simp only [M', o', b'] at this
                rw [h]
                linarith
              · have := h1 ⟨q, h⟩
                simp only [L] at this
                rw [div_le_iff₀ h] at this
                linarith
        have hoptraw (s : S) (x : List R) (t : S) (h : TaskRawKnown T s x t) :
            taskOpt T s x = taskWork T s x t := by
          apply le_antisymm (iInf_le _ t)
          exact le_iInf fun u => le_trans (le_add_right le_rfl) (h.2 u)
        have hadd (s : S) (x : List R) (t : S) (h : TaskRawKnown T s x t) (w : List R) :
            ∀ u, taskWork T s (x ++ w) u = taskWork T s x t + taskWork T t w u := by
          induction w using List.reverseRecOn with
          | nil =>
            intro u
            rw [List.append_nil, hw0, hraw s x t h u, hoptraw s x t h]
          | @append_singleton w r ih =>
            intro u
            rw [← List.append_assoc, hwrec, hwrec, ENNReal.add_iInf]
            refine iInf_congr fun y => ?_
            rw [ih y]
            ring
        have hfree0 (t : S) (p : List R) (hp : ∀ r ∈ p, T.task r t = 0) :
            ∀ u, taskWork T t p u = (T.distance t u : ENNReal) := by
          induction p using List.reverseRecOn with
          | nil => exact hw0 t
          | @append_singleton p r ih =>
            intro u
            have ih' := ih (fun r' hr' => hp r' (by simp [hr']))
            rw [hwrec]
            apply le_antisymm
            · refine iInf_le_of_le t ?_
              rw [ih' t, hp r (by simp), T.diagonal]
              simp
            · refine le_iInf fun y => ?_
              rw [ih' y]
              calc (T.distance t u : ENNReal) ≤ (T.distance t y : ENNReal) + (T.distance y u : ENNReal) := by
                    exact_mod_cast T.triangle t y u
                _ ≤ _ := add_le_add_left le_self_add _
        have hcat (s : S) (x : List R) (t : S) (h : TaskRawKnown T s x t) (w : List R) (f : S)
            (hw : TaskRawKnown T t w f) :
            TaskRawKnown T s (x ++ w) f ∧ taskOpt T s (x ++ w) = taskOpt T s x + taskOpt T t w := by
          have h1 : TaskRawKnown T s (x ++ w) f := by
            refine ⟨?_, fun u => ?_⟩
            · rw [hadd s x t h]
              exact ENNReal.add_ne_top.2 ⟨h.1, hw.1⟩
            · rw [hadd s x t h, hadd s x t h, add_assoc]
              exact add_le_add le_rfl (hw.2 u)
          refine ⟨h1, ?_⟩
          rw [hoptraw s _ f h1, hadd s x t h, hoptraw s x t h, hoptraw t w f hw]
        have hfreeknown (t : S) (p : List R) (hp : ∀ r ∈ p, T.task r t = 0) :
            TaskRawKnown T t p t ∧ taskOpt T t p = 0 := by
          have h0 := hfree0 t p hp
          have h1 : TaskRawKnown T t p t := by
            refine ⟨by simp [h0], fun u => ?_⟩
            simp [h0, T.diagonal]
          refine ⟨h1, ?_⟩
          rw [hoptraw t p t h1, h0, T.diagonal]
          simp
        -- minimal positive cost
        obtain ⟨ε, hε0, hεt, hεd, hεr⟩ : ∃ ε : ENNReal, 0 < ε ∧ ε ≠ ⊤ ∧
            (∀ u v : S, (T.distance u v : ENNReal) ≠ 0 → ε ≤ (T.distance u v : ENNReal)) ∧
            (∀ (r : R) (u : S), T.task r u ≠ 0 → ε ≤ T.task r u) := by
          let e1 : ENNReal := (Finset.univ.filter fun z : S × S => (T.distance z.1 z.2 : ENNReal) ≠ 0).inf
            fun z => (T.distance z.1 z.2 : ENNReal)
          let e2 : ENNReal := (Finset.univ.filter fun z : R × S => T.task z.1 z.2 ≠ 0).inf
            fun z => T.task z.1 z.2
          refine ⟨min 1 (min e1 e2), ?_, ?_, ?_, ?_⟩
          · refine lt_min one_pos (lt_min ?_ ?_)
            · refine (Finset.lt_inf_iff (by simp)).2 fun z hz => ?_
              exact pos_iff_ne_zero.2 (Finset.mem_filter.1 hz).2
            · refine (Finset.lt_inf_iff (by simp)).2 fun z hz => ?_
              exact pos_iff_ne_zero.2 (Finset.mem_filter.1 hz).2
          · exact ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)
          · intro u v h
            refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
            exact Finset.inf_le (f := fun z : S × S => (T.distance z.1 z.2 : ENNReal)) (b := (u, v)) (by simpa using h)
          · intro r u h
            refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
            exact Finset.inf_le (f := fun z : R × S => T.task z.1 z.2) (b := (r, u)) (by simpa using h)
        have htri (u v w : S) : (T.distance u w : ENNReal) ≤ (T.distance u v : ENNReal) + (T.distance v w : ENNReal) := by
          exact_mod_cast T.triangle u v w
        obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, ∀ u v : S, (T.distance u v : ENNReal) ≤ n * ε := by
          obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt (a := ε) (b := ∑ z : S × S, (T.distance z.1 z.2 : ENNReal))
            hε0.ne' (ENNReal.sum_ne_top.2 fun z _ => ENNReal.coe_ne_top)
          refine ⟨n, fun u v => ?_⟩
          refine le_trans ?_ hn.le
          exact Finset.single_le_sum (f := fun z : S × S => (T.distance z.1 z.2 : ENNReal))
            (fun _ _ => zero_le) (Finset.mem_univ (u, v))
        -- movement lower bound
        have hmove (B : TaskOnline T) (x z : List R) :
            B.cost x + (T.distance (B.after x) (B.after (x ++ z)) : ENNReal) ≤ B.cost (x ++ z) := by
          induction z using List.reverseRecOn with
          | nil => simp [T.diagonal]
          | @append_singleton z r ih =>
            rw [← List.append_assoc, hcappend]
            unfold taskActionCost
            set y := x ++ z
            have t1 := htri (B.after x) (B.after y) (B.after (y ++ [r]))
            have t2 := htri (B.after y) (B.before y) (B.after (y ++ [r]))
            have t3 := htri (B.before y) (B.moment (y ++ [r])) (B.after (y ++ [r]))
            calc B.cost x + (T.distance (B.after x) (B.after (y ++ [r])) : ENNReal)
                ≤ B.cost x + ((T.distance (B.after x) (B.after y) : ENNReal) +
                  ((T.distance (B.after y) (B.before y) : ENNReal) +
                  ((T.distance (B.before y) (B.moment (y ++ [r])) : ENNReal) +
                    (T.distance (B.moment (y ++ [r])) (B.after (y ++ [r])) : ENNReal)))) := by
                  refine add_le_add le_rfl (t1.trans (add_le_add le_rfl (t2.trans (add_le_add le_rfl t3))))
              _ = (B.cost x + (T.distance (B.after x) (B.after y) : ENNReal)) +
                  ((T.distance (B.after y) (B.before y) : ENNReal) +
                  (T.distance (B.before y) (B.moment (y ++ [r])) : ENNReal) + 0 +
                    (T.distance (B.moment (y ++ [r])) (B.after (y ++ [r])) : ENNReal)) := by ring
              _ ≤ _ := by gcongr; exact zero_le
        -- a visit to t
        have hvisit (B : TaskOnline T) (t : S) (x z : List R) :
            (B.cost x + (T.distance (B.after x) t : ENNReal) + (T.distance t (B.after (x ++ z)) : ENNReal) ≤ B.cost (x ++ z)) ∨
            (B.after x ≠ t ∧ ∀ (v : List R) (r : R), (v ++ [r]).IsPrefix z →
              B.after (x ++ v) ≠ t ∧ B.before (x ++ v) ≠ t ∧ B.moment (x ++ v ++ [r]) ≠ t ∧ B.after (x ++ v ++ [r]) ≠ t) := by
          induction z using List.reverseRecOn with
          | nil =>
            by_cases h : B.after x = t
            · left; simp [h, T.diagonal]
            · right
              refine ⟨h, fun v r hv => ?_⟩
              simp at hv
          | @append_singleton z r ih =>
            rw [← List.append_assoc]
            rcases ih with ih | ih
            · left
              have h1 := hmove B (x ++ z) [r]
              refine le_trans ?_ h1
              refine le_trans ?_ (add_le_add ih le_rfl)
              rw [add_assoc (_ + _)]
              exact add_le_add le_rfl (htri _ _ _)
            · have hm := hmove B x z
              have hc := hcappend B (x ++ z) r
              unfold taskActionCost at hc
              by_cases ha : B.after (x ++ z ++ [r]) = t
              · left
                have h1 := hmove B x (z ++ [r])
                rw [← List.append_assoc, ha] at h1
                rw [ha, T.diagonal]
                simpa using h1
              by_cases hb : B.before (x ++ z) = t
              · left
                rw [hc, hb]
                have t1 := htri (B.after x) (B.after (x ++ z)) t
                have t3 := htri t (B.moment (x ++ z ++ [r])) (B.after (x ++ z ++ [r]))
                calc _ ≤ B.cost x + ((T.distance (B.after x) (B.after (x ++ z)) : ENNReal) + (T.distance (B.after (x ++ z)) t : ENNReal)) +
                      ((T.distance t (B.moment (x ++ z ++ [r])) : ENNReal) + (T.distance (B.moment (x ++ z ++ [r])) (B.after (x ++ z ++ [r])) : ENNReal)) := by
                      gcongr
                  _ = (B.cost x + (T.distance (B.after x) (B.after (x ++ z)) : ENNReal)) + ((T.distance (B.after (x ++ z)) t : ENNReal) +
                      (T.distance t (B.moment (x ++ z ++ [r])) : ENNReal) + 0 + (T.distance (B.moment (x ++ z ++ [r])) (B.after (x ++ z ++ [r])) : ENNReal)) := by ring
                  _ ≤ _ := by gcongr; exact zero_le
              by_cases hq : B.moment (x ++ z ++ [r]) = t
              · left
                rw [hc, hq]
                have t1 := htri (B.after x) (B.after (x ++ z)) t
                have t3 := htri (B.after (x ++ z)) (B.before (x ++ z)) t
                calc _ ≤ B.cost x + ((T.distance (B.after x) (B.after (x ++ z)) : ENNReal) + ((T.distance (B.after (x ++ z)) (B.before (x ++ z)) : ENNReal) + (T.distance (B.before (x ++ z)) t : ENNReal))) +
                      (T.distance t (B.after (x ++ z ++ [r])) : ENNReal) := by
                      refine add_le_add (add_le_add le_rfl (t1.trans (add_le_add le_rfl t3))) le_rfl
                  _ = (B.cost x + (T.distance (B.after x) (B.after (x ++ z)) : ENNReal)) + ((T.distance (B.after (x ++ z)) (B.before (x ++ z)) : ENNReal) +
                      (T.distance (B.before (x ++ z)) t : ENNReal) + 0 + (T.distance t (B.after (x ++ z ++ [r])) : ENNReal)) := by ring
                  _ ≤ _ := by gcongr; exact zero_le
              right
              refine ⟨ih.1, fun v r' hv => ?_⟩
              rcases List.prefix_concat_iff.1 hv with he | hpre
              · obtain ⟨rfl, hr⟩ := List.append_inj' he rfl
                have hr' : r' = r := by simpa using hr
                subst hr'
                refine ⟨?_, hb, hq, ha⟩
                rcases List.eq_nil_or_concat v with rfl | ⟨v', r'', rfl⟩
                · simpa using ih.1
                · have := (ih.2 v' r'' (by simp)).2.2.2
                  simpa using this
              · exact ih.2 v r' hpre
        have hsched (B : TaskOnline T) (x z : List R) :
            B.cost (x ++ z) = B.cost x + taskScheduleCost T z (fun j => B.before (x ++ z.take j))
              (fun j => B.moment (x ++ z.take (j + 1))) (fun j => B.after (x ++ z.take j)) := by
          induction z using List.reverseRecOn with
          | nil => simp [taskScheduleCost]
          | @append_singleton z r ih =>
            rw [← List.append_assoc, hcappend, ih, hsc, add_assoc]
            congr 1
            congr 1
            · unfold taskScheduleCost
              apply Finset.sum_congr rfl
              intro j _
              simp [List.take_append_of_le_length (Nat.le_of_lt j.isLt),
                List.take_append_of_le_length (show (j : ℕ) + 1 ≤ z.length from j.isLt)]
            · simp [taskActionCost, List.take_of_length_le (show (z ++ [r]).length ≤ z.length + 1 by simp)]
        have hposε (z : List R) (b m s : ℕ → S) (h : 0 < taskScheduleCost T z b m s) :
            ε ≤ taskScheduleCost T z b m s := by
          unfold taskScheduleCost at h ⊢
          by_contra hlt
          have hall : ∀ j : Fin z.length, ((T.distance (s j) (b j) : ENNReal) + (T.distance (b j) (m j) : ENNReal) +
            T.task z[j] (m j) + (T.distance (m j) (s (j + 1)) : ENNReal)) = 0 := by
            intro j
            by_contra hne
            apply hlt
            refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j))
            by_cases h1 : (T.distance (s j) (b j) : ENNReal) = 0
            · by_cases h2 : (T.distance (b j) (m j) : ENNReal) = 0
              · by_cases h3 : T.task z[j] (m j) = 0
                · by_cases h4 : (T.distance (m j) (s (j + 1)) : ENNReal) = 0
                  · exact (hne (by rw [h1, h2, h3, h4]; simp)).elim
                  · exact (hεd _ _ h4).trans le_add_self
                · exact (hεr _ _ h3).trans (le_add_right le_add_self)
              · exact (hεd _ _ h2).trans (le_add_right (le_add_right le_add_self))
            · exact (hεd _ _ h1).trans (le_add_right (le_add_right le_self_add))
          rw [Finset.sum_eq_zero (fun j _ => hall j)] at h
          exact lt_irrefl _ h
        have hpass (t : S) (ρ : List R)
            (hρ : ∀ (b m s : ℕ → S),
            (∀ j : Fin ρ.length, T.lookahead ρ[j] = false → m j = b j) →
            (s 0 ≠ t ∧ ∀ j : Fin ρ.length, b j ≠ t ∧ m j ≠ t ∧ s j ≠ t ∧ s (j + 1) ≠ t) →
            0 < taskScheduleCost T ρ b m s) (B : TaskOnline T) (x : List R) :
            (B.cost x + (T.distance (B.after x) t : ENNReal) + (T.distance t (B.after (x ++ ρ)) : ENNReal) ≤ B.cost (x ++ ρ)) ∨
            B.cost x + ε ≤ B.cost (x ++ ρ) := by
          rcases hvisit B t x ρ with h | h
          · exact Or.inl h
          · right
            rw [hsched]
            refine add_le_add le_rfl (hposε _ _ _ _ (hρ _ _ _ ?_ ?_))
            · intro j hj
              have : ρ.take (j + 1) = ρ.take j ++ [ρ[j]] := by
                rw [List.take_succ_eq_append_getElem j.isLt]; rfl
              simp only [this, ← List.append_assoc]
              exact B.zero _ _ hj
            · refine ⟨by simpa using h.1, fun j => ?_⟩
              have e : ρ.take (j + 1) = ρ.take j ++ [ρ[j]] := by
                rw [List.take_succ_eq_append_getElem j.isLt]; rfl
              have := h.2 (ρ.take j) ρ[j] (by rw [← e]; exact List.take_prefix _ _)
              simp only [e, ← List.append_assoc]
              exact ⟨this.2.1, this.2.2.1, this.1, this.2.2.2⟩
        have hpad (t : S) (ht : HasForcingWord T t) : ∃ p : List R, (∀ r ∈ p, T.task r t = 0) ∧
            ∀ (B : TaskOnline T) (x : List R),
              B.cost x + (T.distance (B.after x) t : ENNReal) ≤ B.cost (x ++ p) ∧
              B.cost x + (T.distance t (B.after (x ++ p)) : ENNReal) ≤ B.cost (x ++ p) := by
          obtain ⟨ρ, hρ0, hρ⟩ := ht
          have hN : ∀ n : ℕ, ∃ p : List R, (∀ r ∈ p, T.task r t = 0) ∧ ∀ (B : TaskOnline T) (x : List R),
              (B.cost x + (T.distance (B.after x) t : ENNReal) + (T.distance t (B.after (x ++ p)) : ENNReal) ≤ B.cost (x ++ p)) ∨
              B.cost x + n * ε ≤ B.cost (x ++ p) := by
            intro n
            induction n with
            | zero => exact ⟨[], by simp, fun B x => Or.inr (by simp)⟩
            | succ n ih =>
              obtain ⟨p, hp0, hp⟩ := ih
              refine ⟨p ++ ρ, ?_, fun B x => ?_⟩
              · intro r hr
                rcases List.mem_append.1 hr with h | h
                · exact hp0 r h
                · exact hρ0 r h
              rw [← List.append_assoc]
              rcases hp B x with h | h
              · left
                have h1 := hmove B (x ++ p) ρ
                refine le_trans ?_ h1
                refine le_trans ?_ (add_le_add h le_rfl)
                rw [add_assoc (_ + _)]
                exact add_le_add le_rfl (htri _ _ _)
              · rcases hpass t ρ hρ B (x ++ p) with h2 | h2
                · left
                  refine le_trans ?_ h2
                  have h1 := hmove B x p
                  refine add_le_add ?_ le_rfl
                  refine le_trans ?_ (add_le_add h1 le_rfl)
                  rw [add_assoc]
                  exact add_le_add le_rfl (htri _ _ _)
                · right
                  refine le_trans ?_ h2
                  refine le_trans (le_of_eq ?_) (add_le_add h le_rfl)
                  push_cast
                  ring
          obtain ⟨p, hp0, hp⟩ := hN n₀
          refine ⟨p, hp0, fun B x => ?_⟩
          rcases hp B x with h | h
          · exact ⟨le_trans le_self_add h, le_trans (by gcongr; exact le_self_add) h⟩
          · exact ⟨le_trans (add_le_add le_rfl (hn₀ _ _)) h, le_trans (add_le_add le_rfl (hn₀ _ _)) h⟩
        obtain ⟨hA0, a, hAc⟩ := hA
        have hEC : ∀ x, taskOpt T s₀ x ≠ ⊤ → A.expCost x ≠ ⊤ ∧
            (A.expCost x).toReal ≤ c * (taskOpt T s₀ x).toReal + max a 0 := by
          intro x hx
          have h := hAc x hx
          have hle := hoexp A s₀ hA0 x
          refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, ?_⟩
          by_cases hz : taskOpt T s₀ x = 0
          · rw [hz] at h ⊢
            simp only [ENNReal.toReal_zero, mul_zero, zero_add] at h ⊢
            have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
            rwa [ENNReal.toReal_ofReal'] at this
          · have hp : 0 < ENNReal.ofReal (c * (taskOpt T s₀ x).toReal + a) :=
              lt_of_lt_of_le (pos_iff_ne_zero.2 hz) (hle.trans h)
            have hp' := ENNReal.ofReal_pos.1 hp
            have := ENNReal.toReal_le_of_le_ofReal hp'.le h
            have := le_max_left a 0
            linarith
        let g : List R → ℝ := fun x => c * (taskOpt T s₀ x).toReal - (A.expCost x).toReal
        let Φ : S → ℝ := fun s => sInf (g '' {x | TaskRawKnown T s₀ x s})
        have hrawfin : ∀ (s : S) x t, TaskRawKnown T s x t → taskOpt T s x ≠ ⊤ := by
          intro s x t h
          rw [hoptraw s x t h]
          exact h.1
        have hΦle : ∀ x s, TaskRawKnown T s₀ x s → Φ s ≤ g x := by
          intro x s h
          refine csInf_le ⟨-max a 0, ?_⟩ ⟨x, h, rfl⟩
          rintro _ ⟨z, hz, rfl⟩
          have := (hEC z (hrawfin _ _ _ hz)).2
          simp only [g]
          linarith
        have hXne : ∀ q ∈ F.alphabet, ∃ x, TaskRawKnown T s₀ x q.start := by
          intro q hq
          obtain ⟨_, _, _, h, hs, hp⟩ := hF.2.1 q hq
          exact ⟨h, hs ▸ (hF.2.2.2.2.1 h hp).1⟩
        have hcompl : ∀ (s : S) (u v : List R), (F.runFrom s u).complete <+: (F.runFrom s (u ++ v)).complete := by
          intro s u v
          induction v using List.reverseRecOn with
          | nil => simp
          | @append_singleton v r ih =>
            refine ih.trans ?_
            have : F.runFrom s (u ++ (v ++ [r])) = F.step (F.runFrom s (u ++ v)) r := by
              simp [PhaseSystem.runFrom, List.foldl_append]
            rw [this]
            unfold PhaseSystem.step
            split_ifs
            · exact List.prefix_rfl
            · dsimp only
              split
              · exact List.prefix_rfl
              · exact List.prefix_append _ _
        have hpf : ∀ q ∈ F.alphabet, ∀ q' ∈ F.alphabet, q'.start = q.start → q'.word <+: q.word → q' = q := by
          intro q hq q' hq' hs hw
          obtain ⟨z, hz⟩ := hw
          have h1 := (hF.2.1 q hq).2.1
          have h2 := (hF.2.1 q' hq').2.1
          have h3 := hcompl q'.start q'.word z
          rw [hz, h2, hs, h1] at h3
          simpa using h3
        have hfincost : ∀ x : List R, (Set.range fun i => (A.alg i).cost x).Finite := by
          intro x
          let K : (Fin x.length → S × S × S × S) → ENNReal := fun e => ∑ j : Fin x.length,
            ((T.distance (e j).1 (e j).2.1 : ENNReal) + (T.distance (e j).2.1 (e j).2.2.1 : ENNReal) +
              T.task x[j] (e j).2.2.1 + (T.distance (e j).2.2.1 (e j).2.2.2 : ENNReal))
          refine (Set.finite_range K).subset ?_
          rintro _ ⟨i, rfl⟩
          exact ⟨fun j => ((A.alg i).after (x.take j), (A.alg i).before (x.take j),
            (A.alg i).moment (x.take (j + 1)), (A.alg i).after (x.take (j + 1))), rfl⟩
        have hJ : Finite {q : TaskPhase S R // q ∈ F.alphabet} := F.alphabet.finite_toSet
        have hpol : ∀ δ : ℝ, 0 < δ → ∀ s : S, ∃ P : TaskRandomized T, (∀ i, (P.alg i).after [] = s) ∧
            ∀ q ∈ F.alphabet, q.start = s → (∀ i, (P.alg i).after q.word = q.finish) ∧
              P.expCost q.word ≤ ENNReal.ofReal (c * (taskOpt T q.start q.word).toReal + Φ q.start - Φ q.finish + δ) := by
          intro δ hδ s
          by_cases hs : ∃ q ∈ F.alphabet, q.start = s
          swap
          · let P0 : TaskRandomized T :=
              { ι := Unit
                ms := ⊤
                μ := @MeasureTheory.Measure.dirac Unit ⊤ ()
                prob := MeasureTheory.Measure.dirac.isProbabilityMeasure
                alg := fun _ => ⟨fun _ => s, fun _ => s, fun _ => s, fun _ _ _ => rfl⟩
                meas := fun _ => measurable_const }
            exact ⟨P0, fun _ => rfl, fun q hq hqs => (hs ⟨q, hq, hqs⟩).elim⟩
          obtain ⟨q0, hq0, hq0s⟩ := hs
          obtain ⟨ps, hps0, hpsB⟩ := hpad s (hq0s ▸ (hF.1 q0 hq0).1)
          choose! pf hpf0 hpfB using fun (q : TaskPhase S R) (hq : q ∈ F.alphabet) => hpad q.finish (hF.1 q hq).2
          obtain ⟨x, hx, hgx⟩ : ∃ x, TaskRawKnown T s₀ x s ∧ g x < Φ s + δ := by
            have hne : (g '' {x | TaskRawKnown T s₀ x s}).Nonempty := by
              obtain ⟨x, hx⟩ := hXne q0 hq0
              exact ⟨g x, x, hq0s ▸ hx, rfl⟩
            obtain ⟨_, ⟨x, hx, rfl⟩, h⟩ := Real.lt_sInf_add_pos hne hδ
            exact ⟨x, hx, h⟩
          let y := x ++ ps
          let D : Option {q : TaskPhase S R // q ∈ F.alphabet} → List R := fun j => match j with
            | none => x
            | some q => y ++ q.1.word ++ pf q.1
          let V : A.ι → (Option {q : TaskPhase S R // q ∈ F.alphabet} → ENNReal) := fun i j => (A.alg i).cost (D j)
          have hVm : Measurable V := measurable_pi_lambda _ fun j => A.meas (D j)
          have hVfin : (Set.range V).Finite := by
            refine (Set.Finite.pi' (fun j => hfincost (D j))).subset ?_
            rintro _ ⟨i, rfl⟩ j
            exact ⟨i, rfl⟩
          have hιfin : Finite (Set.range V) := hVfin
          let mι : MeasurableSpace (Set.range V) := ⊤
          let V' : A.ι → Set.range V := fun i => ⟨V i, i, rfl⟩
          have hV'm : Measurable V' := by
            refine measurable_to_countable' fun v => ?_
            have : V' ⁻¹' {v} = V ⁻¹' {v.1} := by
              ext i
              simp [V', Subtype.ext_iff]
            rw [this]
            exact hVm (measurableSet_singleton _)
          let rep : Set.range V → A.ι := fun v => Classical.choose v.2
          have hrep : ∀ v, V (rep v) = v.1 := fun v => Classical.choose_spec v.2
          let aft : TaskOnline T → List R → S := fun B u =>
            if u = [] then s else if h : ∃ q ∈ F.alphabet, q.start = s ∧ q.word = u then (Classical.choose h).finish
            else B.after (y ++ u)
          let mk : TaskOnline T → TaskOnline T := fun B =>
            { before := fun u => B.before (y ++ u)
              moment := fun u => B.moment (y ++ u)
              after := aft B
              zero := fun h r hl => by
                rw [← List.append_assoc]
                exact B.zero _ _ hl }
          have haft : ∀ B, ∀ q ∈ F.alphabet, q.start = s → aft B q.word = q.finish := by
            intro B q hq hqs
            have hne : q.word ≠ [] := (hF.2.1 q hq).1.1
            have hex : ∃ q' ∈ F.alphabet, q'.start = s ∧ q'.word = q.word := ⟨q, hq, hqs, rfl⟩
            have hc := Classical.choose_spec hex
            have := hpf q hq (Classical.choose hex) hc.1 (by rw [hc.2.1, hqs]) (by rw [hc.2.2])
            simp only [aft, if_neg hne, dif_pos hex]
            rw [this]
          have haft' : ∀ B, ∀ q ∈ F.alphabet, q.start = s → ∀ v, v <+: q.word → v ≠ q.word → v ≠ [] →
              aft B v = B.after (y ++ v) := by
            intro B q hq hqs v hv hvq hv0
            have hnex : ¬ ∃ q' ∈ F.alphabet, q'.start = s ∧ q'.word = v := by
              rintro ⟨q', hq', hqs', rfl⟩
              have := hpf q hq q' hq' (by rw [hqs, hqs']) hv
              exact hvq (by rw [this])
            simp only [aft, if_neg hv0, dif_neg hnex]
          have hQ : ∀ (B : TaskOnline T) (u : List R), (∀ v, v <+: u → v ≠ [] → aft B v = B.after (y ++ v)) →
              (mk B).cost u + B.cost y + (T.distance (aft B u) (B.after (y ++ u)) : ENNReal) ≤
                (T.distance s (B.after y) : ENNReal) + B.cost (y ++ u) := by
            intro B u
            induction u using List.reverseRecOn with
            | nil =>
              intro _
              have e0 : (mk B).cost [] = 0 := by simp [TaskOnline.cost]
              have e1 : aft B [] = s := by simp [aft]
              rw [e0, e1, List.append_nil, zero_add, add_comm]
            | @append_singleton u r ih =>
              intro hu
              have ih' := ih (fun v hv hv0 => hu v (hv.trans (List.prefix_append _ _)) hv0)
              have hl := hu (u ++ [r]) List.prefix_rfl (by simp)
              rw [hcappend, hl, T.diagonal, ← List.append_assoc, hcappend B]
              unfold taskActionCost
              have e1 : (mk B).after u = aft B u := rfl
              have e2 : (mk B).before u = B.before (y ++ u) := rfl
              have e3 : (mk B).moment (u ++ [r]) = B.moment (y ++ u ++ [r]) := by
                rw [List.append_assoc]
              have e4 : (mk B).after (u ++ [r]) = B.after (y ++ u ++ [r]) := by
                rw [List.append_assoc]; exact hl
              rw [e1, e2, e3, e4]
              have t1 := htri (aft B u) (B.after (y ++ u)) (B.before (y ++ u))
              calc _ ≤ (mk B).cost u + (((T.distance (aft B u) (B.after (y ++ u)) : ENNReal) + (T.distance (B.after (y ++ u)) (B.before (y ++ u)) : ENNReal)) +
                    (T.distance (B.before (y ++ u)) (B.moment (y ++ u ++ [r])) : ENNReal) + T.task r (B.moment (y ++ u ++ [r])) +
                    (T.distance (B.moment (y ++ u ++ [r])) (B.after (y ++ u ++ [r])) : ENNReal)) + B.cost y + ((0 : NNReal) : ENNReal) := by
                    gcongr
                _ = ((mk B).cost u + B.cost y + (T.distance (aft B u) (B.after (y ++ u)) : ENNReal)) +
                    ((T.distance (B.after (y ++ u)) (B.before (y ++ u)) : ENNReal) +
                    (T.distance (B.before (y ++ u)) (B.moment (y ++ u ++ [r])) : ENNReal) + T.task r (B.moment (y ++ u ++ [r])) +
                    (T.distance (B.moment (y ++ u ++ [r])) (B.after (y ++ u ++ [r])) : ENNReal)) := by
                    rw [ENNReal.coe_zero]; ring
                _ ≤ _ := by
                    refine (add_le_add ih' le_rfl).trans (le_of_eq ?_)
                    ring
          have hpath : ∀ (B : TaskOnline T), ∀ q ∈ F.alphabet, q.start = s →
              (mk B).cost q.word + B.cost x ≤ B.cost (y ++ q.word ++ pf q) := by
            intro B q hq hqs
            have hne : q.word ≠ [] := (hF.2.1 q hq).1.1
            obtain ⟨u, r, hur⟩ : ∃ u r, q.word = u ++ [r] := by
              rcases List.eq_nil_or_concat q.word with h | ⟨u, r, h⟩
              · exact (hne h).elim
              · exact ⟨u, r, by simpa using h⟩
            have h1 := hQ B u (fun v hv hv0 => haft' B q hq hqs v (hv.trans (by rw [hur]; exact List.prefix_append _ _))
              (by
                intro h
                have := hv.length_le
                rw [h, hur] at this
                simp at this) hv0)
            have h2 := (hpsB B x).2
            have h3 := (hpfB q hq B (y ++ q.word)).1
            have hl := haft B q hq hqs
            have hyfin : (T.distance s (B.after y) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
            refine le_trans ?_ h3
            rw [← hl, hur, hcappend, ← List.append_assoc, hcappend B]
            unfold taskActionCost
            have e1 : (mk B).after u = aft B u := rfl
            have e2 : (mk B).before u = B.before (y ++ u) := rfl
            have e3 : (mk B).moment (u ++ [r]) = B.moment (y ++ u ++ [r]) := by
              rw [List.append_assoc]
            have e4 : (mk B).after (u ++ [r]) = aft B (u ++ [r]) := rfl
            rw [e1, e2, e3, e4]
            have t1 := htri (aft B u) (B.after (y ++ u)) (B.before (y ++ u))
            have t2 := htri (B.moment (y ++ u ++ [r])) (B.after (y ++ u ++ [r])) (aft B (u ++ [r]))
            refine (ENNReal.add_le_add_iff_right hyfin).1 ?_
            calc _ ≤ (mk B).cost u + (((T.distance (aft B u) (B.after (y ++ u)) : ENNReal) + (T.distance (B.after (y ++ u)) (B.before (y ++ u)) : ENNReal)) +
                    (T.distance (B.before (y ++ u)) (B.moment (y ++ u ++ [r])) : ENNReal) + T.task r (B.moment (y ++ u ++ [r])) +
                    ((T.distance (B.moment (y ++ u ++ [r])) (B.after (y ++ u ++ [r])) : ENNReal) +
                    (T.distance (B.after (y ++ u ++ [r])) (aft B (u ++ [r])) : ENNReal))) + B.cost x + (T.distance s (B.after y) : ENNReal) := by
                    gcongr
              _ = (mk B).cost u + (B.cost x + (T.distance s (B.after y) : ENNReal)) + (T.distance (aft B u) (B.after (y ++ u)) : ENNReal) +
                    ((T.distance (B.after (y ++ u)) (B.before (y ++ u)) : ENNReal) +
                    (T.distance (B.before (y ++ u)) (B.moment (y ++ u ++ [r])) : ENNReal) + T.task r (B.moment (y ++ u ++ [r])) +
                    ((T.distance (B.moment (y ++ u ++ [r])) (B.after (y ++ u ++ [r])) : ENNReal) +
                    (T.distance (B.after (y ++ u ++ [r])) (aft B (u ++ [r])) : ENNReal))) := by ring
              _ ≤ (mk B).cost u + B.cost y + (T.distance (aft B u) (B.after (y ++ u)) : ENNReal) +
                    ((T.distance (B.after (y ++ u)) (B.before (y ++ u)) : ENNReal) +
                    (T.distance (B.before (y ++ u)) (B.moment (y ++ u ++ [r])) : ENNReal) + T.task r (B.moment (y ++ u ++ [r])) +
                    ((T.distance (B.moment (y ++ u ++ [r])) (B.after (y ++ u ++ [r])) : ENNReal) +
                    (T.distance (B.after (y ++ u ++ [r])) (aft B (u ++ [r])) : ENNReal))) := by gcongr
              _ ≤ _ := by
                    refine (add_le_add h1 le_rfl).trans (le_of_eq ?_)
                    ring
          have hprob : MeasureTheory.IsProbabilityMeasure (A.μ.map V') :=
            MeasureTheory.Measure.isProbabilityMeasure_map hV'm.aemeasurable
          let P : TaskRandomized T :=
            { ι := Set.range V
              ms := mι
              μ := A.μ.map V'
              prob := hprob
              alg := fun v => mk (A.alg (rep v))
              meas := fun _ => measurable_from_top }
          refine ⟨P, fun i => ?_, fun q hq hqs => ⟨fun i => haft (A.alg (rep i)) q hq hqs, ?_⟩⟩
          · change aft (A.alg (rep i)) [] = s
            simp [aft]
          have hE : P.expCost q.word + A.expCost x ≤ A.expCost (y ++ q.word ++ pf q) := by
            have h1 : P.expCost q.word = ∫⁻ i, (mk (A.alg (rep (V' i)))).cost q.word ∂A.μ := by
              change ∫⁻ v, (mk (A.alg (rep v))).cost q.word ∂(A.μ.map V') = _
              rw [MeasureTheory.lintegral_map measurable_from_top hV'm]
            rw [h1]
            unfold TaskRandomized.expCost
            rw [← MeasureTheory.lintegral_add_right _ (A.meas x)]
            refine MeasureTheory.lintegral_mono fun i => ?_
            have h2 := hpath (A.alg (rep (V' i))) q hq hqs
            have h3 : (A.alg (rep (V' i))).cost x = (A.alg i).cost x := congrFun (hrep (V' i)) none
            have h4 : (A.alg (rep (V' i))).cost (y ++ q.word ++ pf q) = (A.alg i).cost (y ++ q.word ++ pf q) :=
              congrFun (hrep (V' i)) (some ⟨q, hq⟩)
            rw [h3, h4] at h2
            exact h2
          have hqv := (hF.2.1 q hq).1
          have hk1 := hcat s₀ x s hx ps s (hfreeknown s ps hps0).1
          have hk2 := hcat s₀ y s hk1.1 q.word q.finish (hqs ▸ hqv.2.1)
          have hk3 := hcat s₀ _ _ hk2.1 (pf q) q.finish (hfreeknown _ _ (hpf0 q hq)).1
          have ho : taskOpt T s₀ (y ++ q.word ++ pf q) = taskOpt T s₀ x + taskOpt T q.start q.word := by
            rw [hk3.2, hk2.2, hk1.2, (hfreeknown _ _ (hpf0 q hq)).2, (hfreeknown s ps hps0).2, hqs]
            simp
          have hxfin := hrawfin _ _ _ hx
          have hEx := (hEC x hxfin).1
          have hED := (hEC _ (hrawfin _ _ _ hk3.1)).1
          have hPfin : P.expCost q.word ≠ ⊤ := ne_top_of_le_ne_top hED (le_self_add.trans hE)
          have hreal := ENNReal.toReal_mono hED hE
          rw [ENNReal.toReal_add hPfin hEx] at hreal
          have hΦ := hΦle _ _ hk3.1
          simp only [g] at hΦ hgx
          rw [ho, ENNReal.toReal_add hxfin hqv.2.2.2] at hΦ
          rw [← ENNReal.ofReal_toReal hPfin]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hqs] at hΦ ⊢
          linarith
        have core : ∀ e : ℝ, 0 < e → ∃ x ∈ phaseBounds F, x ≤ c + e := by
          intro e he
          let Q := {q : TaskPhase S R // q ∈ F.alphabet}
          have hov : ∀ q : Q, 0 < (taskOpt T q.1.start q.1.word).toReal := fun q =>
            ENNReal.toReal_pos (hF.2.1 q.1 q.2).1.2.2.1.ne' (hF.2.1 q.1 q.2).1.2.2.2
          -- uniform bound on 1/opt
          obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, ∀ q : Q, 1 / (taskOpt T q.1.start q.1.word).toReal ≤ K1 := by
            obtain ⟨K1, h⟩ := (Set.finite_range fun q : Q => 1 / (taskOpt T q.1.start q.1.word).toReal).bddAbove
            exact ⟨K1, fun q => h ⟨q, rfl⟩⟩
          let K := max K1 1
          have hKpos : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
          have hKo : ∀ q : Q, 1 ≤ K * (taskOpt T q.1.start q.1.word).toReal := by
            intro q
            have h1 := hK1 q
            rw [div_le_iff₀ (hov q)] at h1
            exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hov q).le)
          choose pol hpol0 hpolq using hpol (e / K) (by positivity)
          have hPP : IsPhasePolicy F pol :=
            ⟨hpol0, fun q hq => Filter.Eventually.of_forall (hpolq q.start q hq rfl).1⟩
          -- real reformulation of feasibility
          have hfeas : ∀ (policy : S → TaskRandomized T),
              (∀ (s : S) (i : (policy s).ι), ((policy s).alg i).after [] = s) →
              (∀ q : Q, (policy q.1.start).expCost q.1.word ≠ ⊤) → ∀ (β : ℝ) (Ψ : S → ℝ),
              (PhaseLPFeasible T (fun q : Q => q.val) policy β Ψ ↔
                ∀ q : Q, ((policy q.1.start).expCost q.1.word).toReal ≤
                  β * (taskOpt T q.1.start q.1.word).toReal + Ψ q.1.start - Ψ q.1.finish) := by
            intro policy h0 hfin β Ψ
            constructor
            · intro h q
              have h1 := h.2.2 q
              have h2 : 0 < (policy q.1.start).expCost q.1.word :=
                lt_of_lt_of_le (hF.2.1 q.1 q.2).1.2.2.1 (hoexp _ _ (h0 _) _)
              have h3 := ENNReal.ofReal_pos.1 (lt_of_lt_of_le h2 h1)
              exact ENNReal.toReal_le_of_le_ofReal h3.le h1
            · intro h
              refine ⟨fun q => (hF.2.1 q.1 q.2).1, h0, fun q => ?_⟩
              rw [← ENNReal.ofReal_toReal (hfin q)]
              exact ENNReal.ofReal_le_ofReal (h q)
          have hfin1 : ∀ q : Q, (pol q.1.start).expCost q.1.word ≠ ⊤ := fun q =>
            ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpolq q.1.start q.1 q.2 rfl).2
          have hge : ∀ (policy : S → TaskRandomized T),
              (∀ (s : S) (i : (policy s).ι), ((policy s).alg i).after [] = s) →
              (∀ q : Q, (policy q.1.start).expCost q.1.word ≠ ⊤) → ∀ q : Q, 
              0 ≤ ((policy q.1.start).expCost q.1.word).toReal := fun _ _ _ _ => ENNReal.toReal_nonneg
          let C : Q → ℝ := fun q => ((pol q.1.start).expCost q.1.word).toReal
          let O : Q → ℝ := fun q => (taskOpt T q.1.start q.1.word).toReal
          let 𝓑 : Set ℝ := {β | ∃ Ψ : S → ℝ, ∀ q : Q, C q ≤ β * O q + Ψ q.1.start - Ψ q.1.finish}
          have hmem : c + e ∈ 𝓑 := by
            refine ⟨Φ, fun q => ?_⟩
            have h1 := (hfeas pol hpol0 hfin1 (c + e) Φ).1
              ⟨fun q => (hF.2.1 q.1 q.2).1, hpol0, fun q => (hpolq q.1.start q.1 q.2 rfl).2.trans
                (ENNReal.ofReal_le_ofReal (by
                  have h2 := hKo q
                  have h3 : e / K ≤ e * (taskOpt T q.1.start q.1.word).toReal := by
                    rw [div_le_iff₀ hKpos]
                    nlinarith
                  linarith))⟩ q
            exact h1
          have hclosed : IsClosed 𝓑 := by
            let eq := Fintype.equivFin S
            have h := hFM (Fintype.card S) Q
              (fun q i => (if eq q.1.start = i then (1:ℝ) else 0) - (if eq q.1.finish = i then (1:ℝ) else 0)) O C
            convert h using 1
            ext β
            simp only [𝓑, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨Ψ, hΨ⟩
              refine ⟨fun i => Ψ (eq.symm i), fun q => ?_⟩
              have := hΨ q
              simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
                Finset.mem_univ, if_true, Equiv.symm_apply_apply]
              linarith
            · rintro ⟨y, hy⟩
              refine ⟨fun s => y (eq s), fun q => ?_⟩
              have := hy q
              simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq,
                Finset.mem_univ, if_true] at this
              linarith
          -- bounded below through one policy with an attained bound
          have hne : (phaseBounds F).Nonempty := by
            by_contra hne
            rw [Set.not_nonempty_iff_eq_empty] at hne
            rw [hne] at hα
            have : α + 1 ≤ α := hα.2 (by simp [lowerBounds])
            linarith
          obtain ⟨x0, pol0, hP0, ⟨Ψ0, hΨ0⟩, hmin0⟩ := hne
          have hfin0 : ∀ q : Q, (pol0 q.1.start).expCost q.1.word ≠ ⊤ := fun q =>
            ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hΨ0.2.2 q)
          obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, ∀ q : Q, ((pol0 q.1.start).expCost q.1.word).toReal / O q ≤ K2 := by
            obtain ⟨K2, h⟩ := (Set.finite_range fun q : Q => ((pol0 q.1.start).expCost q.1.word).toReal / O q).bddAbove
            exact ⟨K2, fun q => h ⟨q, rfl⟩⟩
          have hbdd : BddBelow 𝓑 := by
            refine ⟨x0 - K2, ?_⟩
            rintro β ⟨Ψ, hΨ⟩
            have h1 : x0 ≤ β + K2 := by
              refine hmin0 (β + K2) Ψ ((hfeas pol0 hP0.1 hfin0 _ _).2 fun q => ?_)
              have h2 := hK2 q
              rw [div_le_iff₀ (hov q)] at h2
              have h3 := hΨ q
              have h4 : 0 ≤ C q := ENNReal.toReal_nonneg
              simp only [O] at h2 h3
              linarith
            linarith
          have hinf : sInf 𝓑 ∈ 𝓑 := hclosed.csInf_mem ⟨_, hmem⟩ hbdd
          refine ⟨sInf 𝓑, ⟨pol, hPP, ?_, ?_⟩, csInf_le hbdd hmem⟩
          · obtain ⟨Ψ, hΨ⟩ := hinf
            exact ⟨Ψ, (hfeas pol hpol0 hfin1 _ _).2 hΨ⟩
          · intro β Ψ h
            exact csInf_le hbdd ⟨Ψ, (hfeas pol hpol0 hfin1 _ _).1 h⟩
        refine le_of_forall_pos_lt_add fun e he => ?_
        obtain ⟨x, hx, hxc⟩ := core (e / 2) (by positivity)
        have := hα.1 hx
        linarith

-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:59.15169+00:00
-- url     : https://prove2.me/submissions/943723d8-4812-4027-98a2-f3ff69471a42

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_phaseSystem

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 2, p.547 (proof continues p.548). The finite directed task model,
causal filtering, known-state boundaries and bounded incomplete phase are those
of §2. The LP bound is its attained finite minimum, with potential sign
Φ_start − Φ_finish. The conclusion is global competitiveness with one additive
constant; no competitiveness inequality is part of IsPhaseBased. -/
theorem solution {S R : Type} [Fintype S] [Fintype R] [LinearOrder S]
    (T : TaskSystem S R) (s₀ : S) (F : PhaseSystem T s₀) (hF : F.Valid)
    (localPolicy : S → TaskRandomized T) (A : TaskRandomized T)
    (hA : IsPhaseBased F localPolicy A) (α : ℝ)
    (hLP : IsPhaseLPBound T
      (fun q : {q : TaskPhase S R // q ∈ F.alphabet} => q.val) localPolicy α) :
    A.Competitive s₀ α := by
      classical
      letI (B : TaskRandomized T) : MeasurableSpace B.ι := B.ms
      letI (B : TaskRandomized T) : MeasureTheory.IsProbabilityMeasure B.μ := B.prob
      letI : Nonempty S := ⟨s₀⟩
      have hsc (w : List R) (r : R) (b m s : ℕ → S) :
          taskScheduleCost T (w ++ [r]) b m s = taskScheduleCost T w b m s +
            ((T.distance (s w.length) (b w.length) : ENNReal) +
              (T.distance (b w.length) (m w.length) : ENNReal) +
              T.task r (m w.length) +
              (T.distance (m w.length) (s (w.length + 1)) : ENNReal)) := by
        letI : Inhabited R := ⟨r⟩
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
        letI : Inhabited R := ⟨r⟩
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
      have hemono (B : TaskRandomized T) (u v : List R) (huv : u.IsPrefix v) :
          B.expCost u ≤ B.expCost v := by
        obtain ⟨z, rfl⟩ := huv
        induction z using List.reverseRecOn with
        | nil => simp
        | @append_singleton z r ih =>
          rw [← List.append_assoc, heappend]
          exact le_trans ih (le_add_right le_rfl)
      have hrun (h : List R) (r : R) : F.run (h ++ [r]) = F.step (F.run h) r := by
        simp [PhaseSystem.run, PhaseSystem.runFrom, List.foldl_append]
      have hrun0 : F.run [] = ⟨s₀, [], []⟩ := rfl
      have hfiniteIntegral {I : Type} [MeasurableSpace I] (μ : MeasureTheory.Measure I)
          (f : I → S × S × S × S) (c : S × S × S × S → ENNReal)
          (hf : ∀ v, MeasurableSet {i | f i = v}) :
          (∫⁻ i, c (f i) ∂μ) = ∑ v, c v * μ {i | f i = v} := by
        have hpoint (i : I) : c (f i) = ∑ v, (Set.indicator {i | f i = v} (fun _ => c v)) i := by
          simp [Set.indicator_apply]
        simp_rw [hpoint]
        rw [MeasureTheory.lintegral_finset_sum _ (fun v _ => measurable_const.indicator (hf v))]
        apply Finset.sum_congr rfl
        intro v _
        rw [MeasureTheory.lintegral_indicator (hf v)]
        simp
      have hkeep (h : List R) (r : R)
          (hi : F.ignore (F.run h).state (F.run h).pending r ≠ true) :
          (∫⁻ i, taskActionCost (A.alg i) h r ∂A.μ) =
          ∫⁻ i, taskActionCost ((localPolicy (F.run h).state).alg i) (F.run h).pending r
            ∂(localPolicy (F.run h).state).μ := by
        have ha := hA.2.2.2 h r
        dsimp only at ha
        rw [if_neg hi] at ha
        let c : S × S × S × S → ENNReal := fun v =>
          (T.distance v.1 v.2.1 : ENNReal) + (T.distance v.2.1 v.2.2.1 : ENNReal) +
          T.task r v.2.2.1 + (T.distance v.2.2.1 v.2.2.2 : ENNReal)
        change (∫⁻ i, c (taskActions (A.alg i) h r) ∂A.μ) =
          ∫⁻ i, c (taskActions ((localPolicy (F.run h).state).alg i) (F.run h).pending r)
            ∂(localPolicy (F.run h).state).μ
        rw [hfiniteIntegral _ _ _ (fun v => (ha v).1),
          hfiniteIntegral _ _ _ (fun v => (ha v).2.1)]
        apply Finset.sum_congr rfl
        intro v _
        rw [(ha v).2.2]
      rcases hF with ⟨hforce, hvalid, hmem, hprefix, hboundary, hignore⟩
      obtain ⟨Φ, hΦ⟩ := hLP.1
      let O : TaskPhase S R → ENNReal := fun q => taskOpt T q.start q.word
      let L : TaskPhase S R → ENNReal := fun q => (localPolicy q.start).expCost q.word
      let C : List R → ENNReal := fun h => ((F.run h).complete.map O).sum
      let E : List R → ENNReal := fun h => ((F.run h).complete.map L).sum
      let V : List R → ℝ := fun h => ((F.run h).complete.map (fun q => Φ q.start - Φ q.finish)).sum
      have hdecomp (h : List R) :
          (∀ t, taskWork T s₀ h t = C h + taskWork T (F.run h).state (F.run h).pending t) ∧
          A.expCost h = E h + (localPolicy (F.run h).state).expCost (F.run h).pending ∧
          V h = Φ s₀ - Φ (F.run h).state := by
        induction h using List.reverseRecOn with
        | nil => simp [C, E, V, hrun0, hezero]
        | @append_singleton h r ih =>
          by_cases hi : F.ignore (F.run h).state (F.run h).pending r = true
          · have hrs : F.run (h ++ [r]) = F.run h := by simp [hrun, PhaseSystem.step, hi]
            have hz : (∫⁻ i, taskActionCost (A.alg i) h r ∂A.μ) = 0 := by
              have hh := hA.2.2.2 h r
              dsimp only at hh
              rw [if_pos hi] at hh
              calc
                _ = ∫⁻ _ : A.ι, (0 : ENNReal) ∂A.μ := by
                  apply MeasureTheory.lintegral_congr_ae
                  filter_upwards [hh] with i hh
                  exact hh.1
                _ = 0 := by simp
            refine ⟨?_, ?_, ?_⟩
            · intro t
              simpa [C, hrs] using (hignore h r hi t).trans (ih.1 t)
            · simpa [E, hrs, heappend, hz] using ih.2.1
            · simpa [V, hrs] using ih.2.2
          · have hwstep (t : S) : taskWork T s₀ (h ++ [r]) t =
                C h + taskWork T (F.run h).state ((F.run h).pending ++ [r]) t := by
              rw [hwrec, hwrec]
              simp_rw [ih.1]
              simp only [ENNReal.add_iInf, add_assoc]
            have hestep : A.expCost (h ++ [r]) =
                E h + (localPolicy (F.run h).state).expCost ((F.run h).pending ++ [r]) := by
              rw [heappend, ih.2.1, heappend, hkeep h r hi]
              exact add_assoc _ _ _
            cases hf : F.finish (F.run h).state ((F.run h).pending ++ [r]) with
            | none =>
              have hrs : F.run (h ++ [r]) =
                  ⟨(F.run h).state, (F.run h).pending ++ [r], (F.run h).complete⟩ := by
                simp [hrun, PhaseSystem.step, hi, hf]
              refine ⟨?_, ?_, ?_⟩
              · simpa [C, hrs] using hwstep
              · simpa [E, hrs] using hestep
              · simpa [V, hrs] using ih.2.2
            | some s =>
              let q : TaskPhase S R := ⟨(F.run h).state, s, (F.run h).pending ++ [r]⟩
              have hrs : F.run (h ++ [r]) = ⟨s, [], (F.run h).complete ++ [q]⟩ := by
                simp [hrun, PhaseSystem.step, hi, hf, q]
              have hq : q ∈ F.alphabet := hmem (h ++ [r]) q (by simp [hrs])
              have hqraw := (hvalid q hq).1.2.1
              refine ⟨?_, ?_, ?_⟩
              · intro t
                rw [hwstep]
                have hqeq := hraw q.start q.word q.finish hqraw t
                simpa [C, hrs, hw0, O, q, add_assoc] using congrArg (C h + ·) hqeq
              · simpa [E, hrs, L, q, hezero, add_assoc] using hestep
              · simp only [V, hrs, List.map_append, List.map_cons, List.map_nil,
                  List.sum_append, List.sum_cons, List.sum_nil, add_zero]
                change V h + (Φ (F.run h).state - Φ s) = Φ s₀ - Φ s
                rw [ih.2.2]
                ring
      have hphase (q : TaskPhase S R) (hq : q ∈ F.alphabet) :
          O q ≠ ⊤ ∧ L q ≠ ⊤ ∧
            (L q).toReal ≤ α * (O q).toReal + (Φ q.start - Φ q.finish) := by
        have hb := hΦ.2.2 ⟨q, hq⟩
        change L q ≤ ENNReal.ofReal (α * (O q).toReal + Φ q.start - Φ q.finish) at hb
        have hp : 0 < L q := lt_of_lt_of_le (hvalid q hq).1.2.2.1
          (hoexp (localPolicy q.start) q.start (hA.2.1 q.start) q.word)
        have hn : 0 ≤ α * (O q).toReal + Φ q.start - Φ q.finish :=
          le_of_lt (ENNReal.ofReal_pos.mp (lt_of_lt_of_le hp hb))
        refine ⟨(hvalid q hq).1.2.2.2, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb, ?_⟩
        simpa only [sub_eq_add_neg, add_assoc] using ENNReal.toReal_le_of_le_ofReal hn hb
      have hsum (qs : List (TaskPhase S R)) (hq : ∀ q ∈ qs, q ∈ F.alphabet) :
          (qs.map O).sum ≠ ⊤ ∧ (qs.map L).sum ≠ ⊤ ∧
          (qs.map L).sum.toReal ≤ α * (qs.map O).sum.toReal +
            (qs.map (fun q => Φ q.start - Φ q.finish)).sum := by
        induction qs with
        | nil => simp
        | cons q qs ih =>
          have hp := hphase q (hq q (by simp))
          have ht := ih (fun q h => hq q (by simp [h]))
          simp only [List.map_cons, List.sum_cons]
          refine ⟨ENNReal.add_ne_top.mpr ⟨hp.1, ht.1⟩,
            ENNReal.add_ne_top.mpr ⟨hp.2.1, ht.2.1⟩, ?_⟩
          rw [ENNReal.toReal_add hp.2.1 ht.2.1, ENNReal.toReal_add hp.1 ht.1]
          nlinarith [hp.2.2, ht.2.2]
      let M : ℝ := (F.alphabet.map (fun q => (L q).toReal)).sum
      let N : ℝ := (F.alphabet.map (fun q => (O q).toReal)).sum
      have hM : 0 ≤ M := List.sum_nonneg (by intro x hx; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx; positivity)
      have hN : 0 ≤ N := List.sum_nonneg (by intro x hx; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx; positivity)
      have htail (h : List R) :
          (localPolicy (F.run h).state).expCost (F.run h).pending ≠ ⊤ ∧
          taskOpt T (F.run h).state (F.run h).pending ≠ ⊤ ∧
          ((localPolicy (F.run h).state).expCost (F.run h).pending).toReal ≤ M ∧
          (taskOpt T (F.run h).state (F.run h).pending).toReal ≤ N := by
        by_cases he : (F.run h).pending = []
        · simpa [he, hezero, ho0] using And.intro hM hN
        · obtain ⟨q, hq, hs, hp⟩ := hprefix h he
          have hph := hphase q hq
          have hec : (localPolicy (F.run h).state).expCost (F.run h).pending ≤ L q := by
            simpa only [L, ← hs] using hemono (localPolicy q.start) (F.run h).pending q.word hp
          have hoc : taskOpt T (F.run h).state (F.run h).pending ≤ O q := by
            simpa only [O, ← hs] using homono q.start (F.run h).pending q.word hp
          have hen : (localPolicy (F.run h).state).expCost (F.run h).pending ≠ ⊤ :=
            ne_top_of_le_ne_top hph.2.1 hec
          have hon : taskOpt T (F.run h).state (F.run h).pending ≠ ⊤ :=
            ne_top_of_le_ne_top hph.1 hoc
          refine ⟨hen, hon, ?_, ?_⟩
          · apply le_trans ((ENNReal.toReal_le_toReal hen hph.2.1).mpr hec)
            exact List.single_le_sum (by intro x hx; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx; positivity)
              _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
          · apply le_trans ((ENNReal.toReal_le_toReal hon hph.1).mpr hoc)
            exact List.single_le_sum (by intro x hx; obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx; positivity)
              _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
      let K : ℝ := ∑ s : S, |Φ s|
      have hK (s : S) : - Φ s ≤ K := by
        exact le_trans (neg_le_abs (Φ s)) (Finset.single_le_sum (fun t _ => abs_nonneg (Φ t)) (Finset.mem_univ s))
      refine ⟨hA.1, Φ s₀ + K + M + |α| * N, ?_⟩
      intro h hfin
      have hs := hsum (F.run h).complete (hmem h)
      change C h ≠ ⊤ ∧ E h ≠ ⊤ ∧ (E h).toReal ≤ α * (C h).toReal + V h at hs
      have ht := htail h
      have hd := hdecomp h
      have hopt : taskOpt T s₀ h = C h + taskOpt T (F.run h).state (F.run h).pending := by
        change (⨅ t, taskWork T s₀ h t) = C h + ⨅ t, taskWork T (F.run h).state (F.run h).pending t
        simp_rw [hd.1]
        exact ENNReal.add_iInf.symm
      have hefin : A.expCost h ≠ ⊤ := by
        rw [hd.2.1]
        exact ENNReal.add_ne_top.mpr ⟨hs.2.1, ht.1⟩
      have hoptreal : (taskOpt T s₀ h).toReal = (C h).toReal +
          (taskOpt T (F.run h).state (F.run h).pending).toReal := by
        rw [hopt, ENNReal.toReal_add hs.1 ht.2.1]
      have hcostreal : (A.expCost h).toReal ≤ α * (C h).toReal + Φ s₀ - Φ (F.run h).state + M := by
        rw [hd.2.1, ENNReal.toReal_add hs.2.1 ht.1]
        have hb := hs.2.2
        rw [hd.2.2] at hb
        linarith [ht.2.2.1]
      have herror : -α * (taskOpt T (F.run h).state (F.run h).pending).toReal ≤ |α| * N := by
        calc
          _ ≤ |α| * (taskOpt T (F.run h).state (F.run h).pending).toReal :=
            mul_le_mul_of_nonneg_right (neg_le_abs α) ENNReal.toReal_nonneg
          _ ≤ _ := mul_le_mul_of_nonneg_left ht.2.2.2 (abs_nonneg α)
      have hfinal : (A.expCost h).toReal ≤ α * (taskOpt T s₀ h).toReal +
          (Φ s₀ + K + M + |α| * N) := by
        rw [hoptreal]
        nlinarith [hK (F.run h).state]
      rw [← ENNReal.ofReal_toReal hefin]
      exact ENNReal.ofReal_le_ofReal hfinal

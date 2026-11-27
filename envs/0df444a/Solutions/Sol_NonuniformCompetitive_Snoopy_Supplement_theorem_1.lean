-- Prove2me | solution 1 for NonuniformCompetitive.Snoopy.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:30:21.424486+00:00
-- url     : https://prove2.me/submissions/4768878d-f8fa-423a-84a7-121f887f0aa1

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_taskSystem

open NonuniformCompetitive
open NonuniformCompetitive.Snoopy
open NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory

/-- Theorem 1, pp.545–546, for the source's directed zero-cost task systems,
with both look-ahead conventions. The canonical order resolves precisely the
known-state ties specified on p.545. Competitiveness concerns feasible finite
inputs; infinite processing costs remain representable in the definitions. -/
theorem solution {S R : Type} [Fintype S] [Fintype R] [LinearOrder S]
    (T : TaskSystem S R) (s₀ : S) (hw : HasForcingWords T)
    (A : TaskRandomized T) (α : ℝ) (hA : A.Competitive s₀ α) :
    ∃ B : TaskRandomized T, B.Competitive s₀ α ∧
      ∀ (σ : List R) (s : S), σ ≠ [] → TaskKnown T s₀ σ s →
        ∀ᵐ i ∂B.μ, (B.alg i).after σ = s := by
          classical
          let _ : MeasurableSpace A.ι := A.ms
          have hcost_append : ∀ (C : TaskOnline T) (σ : List R) (r : R),
              C.cost (σ ++ [r]) = C.cost σ +
                ((T.distance (C.after σ) (C.before σ) : ENNReal) +
                  (T.distance (C.before σ) (C.moment (σ ++ [r])) : ENNReal) +
                  T.task r (C.moment (σ ++ [r])) +
                  (T.distance (C.moment (σ ++ [r])) (C.after (σ ++ [r])) : ENNReal)) := by
            intro C σ r
            unfold TaskOnline.cost
            rw [← Fin.sum_congr' _ (show σ.length + 1 = (σ ++ [r]).length by simp)]
            rw [Fin.sum_univ_castSucc]
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              have hj₁ : (j : ℕ) ≤ σ.length := Nat.le_of_lt j.isLt
              have hj₂ : (j : ℕ) + 1 ≤ σ.length := j.isLt
              simp [List.take_append_of_le_length hj₁, List.take_append_of_le_length hj₂,
                List.getElem_append_left j.isLt]
            · simp [List.take_of_length_le (show (σ ++ [r]).length ≤ σ.length + 1 by simp)]
          have hdtri : ∀ x y z : S, (T.distance x z : ENNReal) ≤
              (T.distance x y : ENNReal) + (T.distance y z : ENNReal) := by
            intro x y z
            exact_mod_cast T.triangle x y z
          have hscost_append : ∀ (σ : List R) (r : R) (b m s : ℕ → S),
              taskScheduleCost T (σ ++ [r]) b m s = taskScheduleCost T σ b m s +
                ((T.distance (s σ.length) (b σ.length) : ENNReal) +
                  (T.distance (b σ.length) (m σ.length) : ENNReal) +
                  T.task r (m σ.length) +
                  (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal)) := by
            intro σ r b m s
            unfold taskScheduleCost
            rw [← Fin.sum_congr' _ (show σ.length + 1 = (σ ++ [r]).length by simp)]
            rw [Fin.sum_univ_castSucc]
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              simp [List.getElem_append_left j.isLt]
            · simp
          have hscost_cat : ∀ (σ τ : List R) (b m s : ℕ → S),
              taskScheduleCost T (σ ++ τ) b m s = taskScheduleCost T σ b m s +
                taskScheduleCost T τ (fun j => b (σ.length + j))
                  (fun j => m (σ.length + j)) (fun j => s (σ.length + j)) := by
            intro σ τ b m s
            induction τ using List.reverseRecOn with
            | nil =>
              rw [List.append_nil]
              simp [taskScheduleCost]
            | append_singleton τ r ih =>
              rw [← List.append_assoc, hscost_append, ih, hscost_append]
              simp only [List.length_append, Nat.add_assoc, add_assoc]
          have hins : ∀ a b c d : ENNReal, a + b + d ≤ a + b + c + d := by
            intro a b c d
            calc
              a + b + d ≤ a + b + d + c := le_self_add
              _ = a + b + c + d := by ac_rfl
          have hleg : ∀ (r : R) (x b m y : S),
              (T.distance x y : ENNReal) ≤ (T.distance x b : ENNReal) +
                (T.distance b m : ENNReal) + T.task r m + (T.distance m y : ENNReal) := by
            intro r x b m y
            calc
              (T.distance x y : ENNReal) ≤ (T.distance x m : ENNReal) +
                  (T.distance m y : ENNReal) := hdtri _ _ _
              _ ≤ ((T.distance x b : ENNReal) + (T.distance b m : ENNReal)) +
                  (T.distance m y : ENNReal) := by gcongr; exact hdtri _ _ _
              _ ≤ _ := hins _ _ _ _
          have hpath : ∀ (σ : List R) (b m s : ℕ → S),
              (T.distance (s 0) (s σ.length) : ENNReal) ≤ taskScheduleCost T σ b m s := by
            intro σ b m s
            induction σ using List.reverseRecOn with
            | nil => simp [taskScheduleCost, T.diagonal]
            | append_singleton σ r ih =>
              rw [hscost_append]
              simp only [List.length_append, List.length_singleton]
              exact (hdtri (s 0) (s σ.length) (s (σ.length + 1))).trans
                (add_le_add ih (hleg r _ _ _ _))
          have hdetour : ∀ (σ : List R) (b m s : ℕ → S) (v : S),
              (s 0 = v ∨ ∃ j : Fin σ.length,
                b j = v ∨ m j = v ∨ s j = v ∨ s (j + 1) = v) →
              (T.distance (s 0) v : ENNReal) + (T.distance v (s σ.length) : ENNReal) ≤
                taskScheduleCost T σ b m s := by
            intro σ b m s v hv
            induction σ using List.reverseRecOn with
            | nil =>
              rcases hv with hv | ⟨j, hj⟩
              · simp [List.length_nil, hv, T.diagonal, taskScheduleCost]
              · exact Fin.elim0 j
            | append_singleton σ r ih =>
              have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
              rw [hlen] at hv ⊢
              rw [hscost_append]
              have hext : (T.distance (s 0) v : ENNReal) + (T.distance v (s σ.length) : ENNReal) ≤
                  taskScheduleCost T σ b m s →
                  (T.distance (s 0) v : ENNReal) + (T.distance v (s (σ.length + 1)) : ENNReal) ≤
                  taskScheduleCost T σ b m s +
                    ((T.distance (s σ.length) (b σ.length) : ENNReal) +
                      (T.distance (b σ.length) (m σ.length) : ENNReal) + T.task r (m σ.length) +
                      (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal)) := by
                intro hp
                calc
                  _ ≤ (T.distance (s 0) v : ENNReal) + ((T.distance v (s σ.length) : ENNReal) +
                      (T.distance (s σ.length) (s (σ.length + 1)) : ENNReal)) := by
                    gcongr; exact hdtri _ _ _
                  _ = ((T.distance (s 0) v : ENNReal) + (T.distance v (s σ.length) : ENNReal)) +
                      (T.distance (s σ.length) (s (σ.length + 1)) : ENNReal) := (add_assoc _ _ _).symm
                  _ ≤ _ := add_le_add hp (hleg r _ _ _ _)
              rcases hv with hv | ⟨j, hj⟩
              · exact hext (ih (Or.inl hv))
              · by_cases hjlt : (j : ℕ) < σ.length
                · exact hext (ih (Or.inr ⟨⟨j, hjlt⟩, hj⟩))
                · have hjeq : (j : ℕ) = σ.length := by omega
                  simp only [hjeq] at hj
                  have hp := hpath σ b m s
                  have h₁ := hdtri (s 0) (s σ.length) (b σ.length)
                  have h₂ := hdtri (s 0) (b σ.length) (m σ.length)
                  have h₃ := hdtri (b σ.length) (m σ.length) (s (σ.length + 1))
                  have h₄ := hdtri (s σ.length) (b σ.length) (m σ.length)
                  rcases hj with hj | hj | hj | hj
                  · subst v
                    calc
                      _ ≤ ((T.distance (s 0) (s σ.length) : ENNReal) +
                          (T.distance (s σ.length) (b σ.length) : ENNReal)) +
                          ((T.distance (b σ.length) (m σ.length) : ENNReal) +
                            (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal)) := add_le_add h₁ h₃
                      _ ≤ _ := by
                        calc
                          _ ≤ taskScheduleCost T σ b m s + ((T.distance (s σ.length) (b σ.length) : ENNReal) +
                            (T.distance (b σ.length) (m σ.length) : ENNReal) +
                            (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal)) := by
                              simpa only [add_assoc] using add_le_add_left hp
                                ((T.distance (s σ.length) (b σ.length) : ENNReal) +
                                ((T.distance (b σ.length) (m σ.length) : ENNReal) +
                                (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal)))
                          _ ≤ _ := add_le_add_right (hins _ _ _ _) _
                  · subst v
                    calc
                      _ ≤ (((T.distance (s 0) (s σ.length) : ENNReal) +
                          (T.distance (s σ.length) (b σ.length) : ENNReal)) +
                          (T.distance (b σ.length) (m σ.length) : ENNReal)) +
                          (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal) := by
                            gcongr
                            exact h₂.trans (by gcongr)
                      _ ≤ _ := by
                        have hh := add_le_add_left hp
                          ((T.distance (s σ.length) (b σ.length) : ENNReal) +
                          (T.distance (b σ.length) (m σ.length) : ENNReal) +
                          (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal))
                        calc
                          _ ≤ taskScheduleCost T σ b m s + ((T.distance (s σ.length) (b σ.length) : ENNReal) +
                            (T.distance (b σ.length) (m σ.length) : ENNReal) +
                            (T.distance (m σ.length) (s (σ.length + 1)) : ENNReal)) := by
                              simpa only [add_assoc] using hh
                          _ ≤ _ := add_le_add_right (hins _ _ _ _) _
                  · subst v
                    exact add_le_add hp (hleg r _ _ _ _)
                  · subst v
                    simpa [T.diagonal, hscost_append] using (hpath (σ ++ [r]) b m s)
          let D : NNReal := ∑ x : S, ∑ y : S, T.distance x y
          have hD : ∀ x y, (T.distance x y : ENNReal) ≤ (D : ENNReal) := by
            intro x y
            apply ENNReal.coe_le_coe.mpr
            change T.distance x y ≤ ∑ a : S, ∑ b : S, T.distance a b
            exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ y)).trans
              (Finset.single_le_sum (f := fun a : S => ∑ b : S, T.distance a b)
                (fun _ _ => bot_le) (Finset.mem_univ x))
          have hgap : ∀ ρ : List R, ∃ c : ENNReal, 0 < c ∧ c ≠ ⊤ ∧
              ∀ b m s : ℕ → S, 0 < taskScheduleCost T ρ b m s → c ≤ taskScheduleCost T ρ b m s := by
            intro ρ
            let f : (Fin ρ.length → S × S × S × S) → ENNReal := fun p =>
              ∑ j : Fin ρ.length, ((T.distance (p j).1 (p j).2.1 : ENNReal) +
                (T.distance (p j).2.1 (p j).2.2.1 : ENNReal) + T.task ρ[j] (p j).2.2.1 +
                (T.distance (p j).2.2.1 (p j).2.2.2 : ENNReal))
            let F : Finset ENNReal := insert 1 ((Finset.univ.image f).filter fun c => 0 < c)
            have hF : F.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
            let c := F.inf' hF id
            have hc : 0 < c := by
              apply (Finset.lt_inf'_iff hF).mpr
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact zero_lt_one
              · exact (Finset.mem_filter.mp hx).2
            have hcone : c ≤ 1 := Finset.inf'_le id (Finset.mem_insert_self _ _)
            refine ⟨c, hc, ne_top_of_le_ne_top (by simp) hcone, ?_⟩
            intro b m s hs
            have hf : f (fun j => (s j, b j, m j, s (j + 1))) = taskScheduleCost T ρ b m s := rfl
            apply Finset.inf'_le id
            apply Finset.mem_insert_of_mem
            apply Finset.mem_filter.mpr
            refine ⟨?_, hs⟩
            exact Finset.mem_image.mpr ⟨(fun j => (s j, b j, m j, s (j + 1))), Finset.mem_univ _, hf⟩
          have hforce : ∀ v : S, ∃ q : List R,
              (∀ r ∈ q, T.task r v = 0) ∧
              ∀ b m s : ℕ → S,
                (∀ j : Fin q.length, T.lookahead q[j] = false → m j = b j) →
                (T.distance (s 0) v : ENNReal) + (T.distance v (s q.length) : ENNReal) ≤
                  taskScheduleCost T q b m s := by
            intro v
            obtain ⟨ρ, hρfree, hρforce⟩ := hw v
            obtain ⟨c, hc, hcfin, hcle⟩ := hgap ρ
            obtain ⟨n, hn⟩ := exists_lt_nsmul (ENNReal.toNNReal_pos hc.ne' hcfin) (D + D)
            have hn' : (D : ENNReal) + (D : ENNReal) ≤ n • c := by
              rw [← ENNReal.coe_toNNReal hcfin]
              exact_mod_cast hn.le
            let q : ℕ → List R := fun n => (List.replicate n ρ).flatten
            have hqstep : ∀ n, q (n + 1) = ρ ++ q n := by
              intro n
              simp only [q, List.replicate_succ, List.flatten_cons]
            have hlarge : ∀ k (b m s : ℕ → S),
                (∀ (j : ℕ) (hj : j < (q k).length), T.lookahead (q k)[j] = false → m j = b j) →
                (∀ j ≤ (q k).length, s j ≠ v) →
                (∀ j < (q k).length, b j ≠ v ∧ m j ≠ v) →
                k • c ≤ taskScheduleCost T (q k) b m s := by
              intro k
              induction k with
              | zero => intro b m s hz hs hb; simp [q, taskScheduleCost]
              | succ k ih =>
                intro b m s hz hs hb
                simp only [hqstep] at hz hs hb ⊢
                have hz₁ : ∀ j : Fin ρ.length, T.lookahead ρ[j] = false → m j = b j := by
                  intro j hj
                  have hj' : T.lookahead (ρ ++ q k)[(j : ℕ)] = false := by
                    simpa [List.getElem_append_left j.isLt] using hj
                  exact hz j (by simp; omega) hj'
                have hpos : 0 < taskScheduleCost T ρ b m s := by
                  apply hρforce b m s hz₁
                  refine ⟨hs 0 (by simp), ?_⟩
                  intro j
                  have hh := hb j (by simp; omega)
                  exact ⟨hh.1, hh.2, hs j (by simp; omega), hs (j + 1) (by simp; omega)⟩
                have htail := ih (fun j => b (ρ.length + j)) (fun j => m (ρ.length + j))
                  (fun j => s (ρ.length + j))
                have htail' : k • c ≤ taskScheduleCost T (q k)
                    (fun j => b (ρ.length + j)) (fun j => m (ρ.length + j))
                    (fun j => s (ρ.length + j)) := by
                  apply htail
                  · intro j hj hzero
                    have hidx : ρ.length + j < (ρ ++ q k).length := by simp; omega
                    have hj' : T.lookahead (ρ ++ q k)[ρ.length + j] = false := by
                      simpa [List.getElem_append_right (by omega : ρ.length ≤ ρ.length + (j : ℕ))] using hzero
                    exact hz (ρ.length + j) (by simp; omega) hj'
                  · intro j hj
                    exact hs (ρ.length + j) (by simp; omega)
                  · intro j hj
                    exact hb (ρ.length + j) (by simp; omega)
                rw [hscost_cat, succ_nsmul]
                simpa [add_comm] using add_le_add (hcle b m s hpos) htail'
            refine ⟨q n, ?_, ?_⟩
            · intro r hr
              obtain ⟨l, hl, hr⟩ := List.mem_flatten.mp hr
              have hl' : l = ρ := (List.mem_replicate.mp hl).2
              exact hρfree r (hl' ▸ hr)
            · intro b m s hz
              by_cases hv : s 0 = v ∨ ∃ j : Fin (q n).length,
                  b j = v ∨ m j = v ∨ s j = v ∨ s (j + 1) = v
              · exact hdetour (q n) b m s v hv
              · have hs : ∀ j ≤ (q n).length, s j ≠ v := by
                  intro j hj heq
                  by_cases hj0 : j = 0
                  · exact hv (Or.inl (hj0 ▸ heq))
                  · apply hv
                    refine Or.inr ⟨⟨j - 1, by omega⟩, Or.inr (Or.inr (Or.inr ?_))⟩
                    simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using heq
                have hb : ∀ j : Fin (q n).length, b j ≠ v ∧ m j ≠ v := by
                  intro j
                  exact ⟨fun h => hv (Or.inr ⟨j, Or.inl h⟩),
                    fun h => hv (Or.inr ⟨j, Or.inr (Or.inl h)⟩)⟩
                exact (add_le_add (hD _ _) (hD _ _)).trans (hn'.trans (hlarge n b m s (fun j hj => hz ⟨j, hj⟩) hs (fun j hj => hb ⟨j, hj⟩)))
          have hwork_step : ∀ (σ : List R) (r : R) (t : S),
              taskWork T s₀ (σ ++ [r]) t =
                ⨅ x : S, taskWork T s₀ σ x + T.task r x + (T.distance x t : ENNReal) := by
            intro σ r t
            apply le_antisymm
            · refine le_iInf fun x => ?_
              simp only [taskWork, ENNReal.iInf_add]
              refine le_iInf fun b => le_iInf fun m => le_iInf fun s => le_iInf fun hs => ?_
              let b' : ℕ → S := fun j => if j < σ.length then b j else x
              let m' : ℕ → S := fun j => if j < σ.length then m j else x
              let s' : ℕ → S := fun j => if j ≤ σ.length then s j else t
              have hsame : taskScheduleCost T σ b' m' s' = taskScheduleCost T σ b m s := by
                apply Finset.sum_congr rfl
                intro j hj
                simp only [b', m', s', if_pos j.isLt, if_pos (Nat.le_of_lt j.isLt),
                  if_pos (show (j : ℕ) + 1 ≤ σ.length from j.isLt)]
              have hok : TaskScheduleOK T s₀ (σ ++ [r]) b' m' s' := by
                refine ⟨?_, ?_⟩
                · simpa [s'] using hs.1
                · intro j hj
                  by_cases h : (j : ℕ) < σ.length
                  · have hzero := hs.2 ⟨j, h⟩
                    change T.lookahead (σ ++ [r])[(j : ℕ)] = false at hj
                    rw [List.getElem_append_left h] at hj
                    simpa [b', m', h] using hzero hj
                  · simp [b', m', h]
              refine iInf_le_of_le b' (iInf_le_of_le m' (iInf_le_of_le s' (iInf_le_of_le hok ?_)))
              rw [hscost_append, hsame]
              simp [b', m', s', T.diagonal, add_assoc]
            · unfold taskWork
              refine le_iInf fun b => le_iInf fun m => le_iInf fun s => le_iInf fun hs => ?_
              have hok : TaskScheduleOK T s₀ σ b m s := by
                refine ⟨hs.1, ?_⟩
                intro j hj
                apply hs.2 ⟨j, by simpa using Nat.lt_succ_of_lt j.isLt⟩
                simpa [List.getElem_append_left j.isLt] using hj
              have hwle : taskWork T s₀ σ (m σ.length) ≤
                  taskScheduleCost T σ b m s + (T.distance (s σ.length) (m σ.length) : ENNReal) := by
                exact iInf_le_of_le b (iInf_le_of_le m (iInf_le_of_le s (iInf_le_of_le hok le_rfl)))
              calc
                (⨅ x : S, taskWork T s₀ σ x + T.task r x + (T.distance x t : ENNReal)) ≤
                    taskWork T s₀ σ (m σ.length) + T.task r (m σ.length) +
                      (T.distance (m σ.length) t : ENNReal) := iInf_le _ _
                _ ≤ (taskScheduleCost T σ b m s +
                    ((T.distance (s σ.length) (b σ.length) : ENNReal) +
                      (T.distance (b σ.length) (m σ.length) : ENNReal))) +
                    T.task r (m σ.length) +
                    ((T.distance (m σ.length) (s (σ.length + 1)) : ENNReal) +
                      (T.distance (s (σ.length + 1)) t : ENNReal)) := by
                  gcongr
                  · exact hwle.trans (add_le_add_right (hdtri _ _ _) _)
                  · exact hdtri _ _ _
                _ = taskScheduleCost T (σ ++ [r]) b m s +
                      (T.distance (s (σ ++ [r]).length) t : ENNReal) := by
                  rw [hscost_append]
                  simp only [List.length_append, List.length_singleton]
                  ac_rfl
          have hwork_lip : ∀ (σ : List R) (s t : S),
              taskWork T s₀ σ t ≤ taskWork T s₀ σ s + (T.distance s t : ENNReal) := by
            intro σ s t
            simp only [taskWork, ENNReal.iInf_add]
            refine le_iInf fun b => le_iInf fun m => le_iInf fun a => le_iInf fun ha => ?_
            refine iInf_le_of_le b (iInf_le_of_le m (iInf_le_of_le a (iInf_le_of_le ha ?_)))
            simpa only [add_assoc] using add_le_add_right (hdtri (a σ.length) s t) (taskScheduleCost T σ b m a)
          have hwork_mono : ∀ (σ : List R) (r : R) (t : S),
              taskWork T s₀ σ t ≤ taskWork T s₀ (σ ++ [r]) t := by
            intro σ r t
            rw [hwork_step]
            refine le_iInf fun x => ?_
            exact (hwork_lip σ x t).trans (by gcongr; exact le_add_of_nonneg_right bot_le)
          have hwork_free : ∀ (σ : List R) (r : R) (s : S),
              TaskRawKnown T s₀ σ s → T.task r s = 0 →
              ∀ t, taskWork T s₀ (σ ++ [r]) t = taskWork T s₀ σ t := by
            intro σ r s hs hr t
            apply le_antisymm
            · rw [hwork_step]
              calc
                (⨅ x : S, taskWork T s₀ σ x + T.task r x + (T.distance x t : ENNReal)) ≤
                    taskWork T s₀ σ s + T.task r s + (T.distance s t : ENNReal) := iInf_le _ _
                _ = taskWork T s₀ σ s + (T.distance s t : ENNReal) := by rw [hr, add_zero]
                _ ≤ taskWork T s₀ σ t := hs.2 t
            · exact hwork_mono σ r t
          have hwork_free_word : ∀ (σ ρ : List R) (s : S),
              TaskRawKnown T s₀ σ s → (∀ r ∈ ρ, T.task r s = 0) →
              ∀ t, taskWork T s₀ (σ ++ ρ) t = taskWork T s₀ σ t := by
            intro σ ρ s hs hρ
            induction ρ using List.reverseRecOn with
            | nil => intro t; rw [List.append_nil]
            | append_singleton ρ r ih =>
              have hρ' : ∀ r' ∈ ρ, T.task r' s = 0 := fun r' hr' => hρ r' (List.mem_append_left _ hr')
              have heq := ih hρ'
              have hs' : TaskRawKnown T s₀ (σ ++ ρ) s := by
                constructor
                · simpa only [heq] using hs.1
                · intro t; simpa only [heq] using hs.2 t
              intro t
              rw [← List.append_assoc, hwork_free (σ ++ ρ) r s hs' (hρ r (by simp)), heq]
          have huniq : ∀ (σ : List R) (s t : S), TaskKnown T s₀ σ s → TaskKnown T s₀ σ t → s = t := by
            intro σ s t hs ht
            rcases lt_trichotomy s t with h | h | h
            · exact absurd hs.1 (ht.2 s h)
            · exact h
            · exact absurd ht.1 (hs.2 t h)
          let kn : List R → Option S := fun σ =>
            if h : σ ≠ [] ∧ ∃ s, TaskKnown T s₀ σ s then some (Classical.choose h.2) else none
          have hkn : ∀ σ s, σ ≠ [] → TaskKnown T s₀ σ s → kn σ = some s := by
            intro σ s hσ hs
            have h : σ ≠ [] ∧ ∃ s, TaskKnown T s₀ σ s := ⟨hσ, s, hs⟩
            simp only [kn, dif_pos h]
            exact congrArg some (huniq σ _ _ (Classical.choose_spec h.2) hs)
          choose q hqfree hqforce using hforce
          let pad : List R → List R := fun σ => (kn σ).elim [] q
          let g : List R → List R := List.reverseRec []
            (fun σ r prev => (prev ++ [r]) ++ pad (σ ++ [r]))
          have hg0 : g [] = [] := by simp [g, List.reverseRec]
          have hgstep : ∀ σ r, g (σ ++ [r]) = (g σ ++ [r]) ++ pad (σ ++ [r]) := by
            intro σ r
            exact List.reverseRec_concat _ _ _ _
          have hkn_some : ∀ σ s, kn σ = some s → σ ≠ [] ∧ TaskKnown T s₀ σ s := by
            intro σ s h
            dsimp [kn] at h
            split at h
            · rename_i hσ
              have heq : Classical.choose hσ.2 = s := Option.some.inj h
              exact ⟨hσ.1, heq ▸ Classical.choose_spec hσ.2⟩
            · contradiction
          have hkn0 : kn [] = none := by simp [kn]
          have hgwork : ∀ σ t, taskWork T s₀ (g σ) t = taskWork T s₀ σ t := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil => intro t; rw [hg0]
            | append_singleton σ r ih =>
              have hbase : ∀ t, taskWork T s₀ (g σ ++ [r]) t = taskWork T s₀ (σ ++ [r]) t := by
                intro t
                simp only [hwork_step, ih]
              rw [hgstep]
              cases hk : kn (σ ++ [r]) with
              | none => simpa [pad, hk] using hbase
              | some v =>
                have hv := (hkn_some _ _ hk).2.1
                have hv' : TaskRawKnown T s₀ (g σ ++ [r]) v := by
                  constructor
                  · simpa only [hbase] using hv.1
                  · intro t; simpa only [hbase] using hv.2 t
                simpa only [pad, hk, Option.elim_some, hbase] using
                  hwork_free_word (g σ ++ [r]) (q v) v hv' (hqfree v)
          have hgopt : ∀ σ, taskOpt T s₀ (g σ) = taskOpt T s₀ σ := by
            intro σ; simp only [taskOpt, hgwork]
          have honline_cat : ∀ (C : TaskOnline T) (τ ρ : List R),
              C.cost (τ ++ ρ) = C.cost τ + taskScheduleCost T ρ
                (fun j => C.before (τ ++ ρ.take j))
                (fun j => C.moment (τ ++ ρ.take (j + 1)))
                (fun j => C.after (τ ++ ρ.take j)) := by
            intro C τ ρ
            change taskScheduleCost T (τ ++ ρ)
              (fun j => C.before ((τ ++ ρ).take j))
              (fun j => C.moment ((τ ++ ρ).take (j + 1)))
              (fun j => C.after ((τ ++ ρ).take j)) = _
            rw [hscost_cat]
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              simp only [List.take_append_of_le_length (Nat.le_of_lt j.isLt),
                List.take_append_of_le_length (show (j : ℕ) + 1 ≤ τ.length from j.isLt)]
            · apply Finset.sum_congr rfl
              intro j hj
              simp only [List.take_append, List.take_of_length_le (by omega : τ.length ≤ τ.length + (j : ℕ)),
                List.take_of_length_le (by omega : τ.length ≤ τ.length + (j : ℕ) + 1),
                List.take_of_length_le (by omega : τ.length ≤ τ.length + ((j : ℕ) + 1)),
                Nat.add_sub_cancel_left, show τ.length + (j : ℕ) + 1 - τ.length = (j : ℕ) + 1 by omega]
          have hsegforce : ∀ (C : TaskOnline T) (τ : List R) (v : S),
              (T.distance (C.after τ) v : ENNReal) +
                  (T.distance v (C.after (τ ++ q v)) : ENNReal) ≤
                taskScheduleCost T (q v)
                  (fun j => C.before (τ ++ (q v).take j))
                  (fun j => C.moment (τ ++ (q v).take (j + 1)))
                  (fun j => C.after (τ ++ (q v).take j)) := by
            intro C τ v
            convert hqforce v
              (fun j => C.before (τ ++ (q v).take j))
              (fun j => C.moment (τ ++ (q v).take (j + 1)))
              (fun j => C.after (τ ++ (q v).take j)) ?_ using 1 <;> simp
            intro j hj
            have ht : (q v).take ((j : ℕ) + 1) = (q v).take j ++ [(q v)[j]] := by
              exact List.take_succ_eq_append_getElem j.isLt
            rw [ht, ← List.append_assoc]
            exact C.zero _ _ hj
          let base : List R → List R := fun σ =>
            if h : σ = [] then [] else g σ.dropLast ++ [σ.getLast h]
          have hbase_step : ∀ σ r, base (σ ++ [r]) = g σ ++ [r] := by
            intro σ r
            simp [base]
          let F : TaskOnline T → TaskOnline T := fun C =>
            { before := fun σ => C.before (g σ)
              moment := fun σ => C.moment (base σ)
              after := fun σ => (kn σ).getD (C.after (g σ))
              zero := by
                intro σ r hr
                simp only [hbase_step]
                exact C.zero (g σ) r hr }
          have hF0 : ∀ C, (F C).after [] = C.after [] := by
            intro C; simp [F, hkn0, hg0]
          have hFknown : ∀ C σ s, σ ≠ [] → TaskKnown T s₀ σ s → (F C).after σ = s := by
            intro C σ s hσ hs
            change (kn σ).getD _ = s
            rw [hkn σ s hσ hs]
            rfl
          have hFcost : ∀ (C : TaskOnline T) (σ : List R),
              (F C).cost σ + (T.distance ((F C).after σ) (C.after (g σ)) : ENNReal) ≤ C.cost (g σ) := by
            intro C σ
            induction σ using List.reverseRecOn with
            | nil => simp [TaskOnline.cost, hF0, hg0, T.diagonal]
            | append_singleton σ r ih =>
              let x := C.after (g σ)
              let b := C.before (g σ)
              let m := C.moment (g σ ++ [r])
              let y := C.after (g σ ++ [r])
              let z := C.after (g (σ ++ [r]))
              let v := (F C).after σ
              let w := (F C).after (σ ++ [r])
              have hfirst : (F C).cost σ + (T.distance v b : ENNReal) ≤
                  C.cost (g σ) + (T.distance x b : ENNReal) := by
                calc
                  _ ≤ (F C).cost σ + ((T.distance v x : ENNReal) + (T.distance x b : ENNReal)) := by
                    gcongr; exact hdtri _ _ _
                  _ = ((F C).cost σ + (T.distance v x : ENNReal)) + (T.distance x b : ENNReal) :=
                    (add_assoc _ _ _).symm
                  _ ≤ _ := add_le_add_left ih _
              have hlast : (T.distance m w : ENNReal) + (T.distance w z : ENNReal) ≤
                  (T.distance m y : ENNReal) + taskScheduleCost T (pad (σ ++ [r]))
                    (fun j => C.before ((g σ ++ [r]) ++ (pad (σ ++ [r])).take j))
                    (fun j => C.moment ((g σ ++ [r]) ++ (pad (σ ++ [r])).take (j + 1)))
                    (fun j => C.after ((g σ ++ [r]) ++ (pad (σ ++ [r])).take j)) := by
                cases hk : kn (σ ++ [r]) with
                | none =>
                  have hw : w = y := by simp [w, F, hk, hgstep, pad, y]
                  have hz : z = y := by simp [z, hgstep, pad, hk, y]
                  simp [hw, hz, pad, hk, taskScheduleCost, T.diagonal]
                | some u =>
                  have hw : w = u := by simp [w, F, hk]
                  have hz : z = C.after ((g σ ++ [r]) ++ q u) := by simp [z, hgstep, pad, hk]
                  rw [hw, hz]
                  simp only [pad, hk, Option.elim_some]
                  calc
                    _ ≤ ((T.distance m y : ENNReal) + (T.distance y u : ENNReal)) +
                        (T.distance u (C.after ((g σ ++ [r]) ++ q u)) : ENNReal) := by
                          gcongr; exact hdtri _ _ _
                    _ = (T.distance m y : ENNReal) + ((T.distance y u : ENNReal) +
                        (T.distance u (C.after ((g σ ++ [r]) ++ q u)) : ENNReal)) := add_assoc _ _ _
                    _ ≤ _ := add_le_add_right (hsegforce C (g σ ++ [r]) u) _
              rw [hcost_append, hgstep, honline_cat, hcost_append]
              rw [show (F C).before σ = b from rfl,
                show (F C).moment (σ ++ [r]) = m by simp [F, hbase_step, m], ← hgstep σ r]
              change ((F C).cost σ + ((T.distance v b : ENNReal) + (T.distance b m : ENNReal) +
                T.task r m + (T.distance m w : ENNReal))) + (T.distance w z : ENNReal) ≤ _
              calc
                _ = ((F C).cost σ + (T.distance v b : ENNReal)) +
                    (T.distance b m : ENNReal) + T.task r m +
                    ((T.distance m w : ENNReal) + (T.distance w z : ENNReal)) := by ac_rfl
                _ ≤ _ := by
                  have hh := add_le_add (add_le_add_left (add_le_add_left hfirst (T.distance b m : ENNReal))
                    (T.task r m)) hlast
                  simpa only [add_assoc] using hh
          letI : IsProbabilityMeasure A.μ := A.prob
          have hcostrange : ∀ σ : List R, (Set.range (fun C : TaskOnline T => C.cost σ)).Finite := by
            intro σ
            let f : (Fin σ.length → S × S × S × S) → ENNReal := fun p =>
              ∑ j : Fin σ.length, ((T.distance (p j).1 (p j).2.1 : ENNReal) +
                (T.distance (p j).2.1 (p j).2.2.1 : ENNReal) + T.task σ[j] (p j).2.2.1 +
                (T.distance (p j).2.2.1 (p j).2.2.2 : ENNReal))
            apply (Set.finite_range f).subset
            rintro c ⟨C, rfl⟩
            exact ⟨fun j => (C.after (σ.take j), C.before (σ.take j),
              C.moment (σ.take (j + 1)), C.after (σ.take (j + 1))), rfl⟩
          letI : TopologicalSpace S := ⊥
          letI : DiscreteTopology S := ⟨rfl⟩
          let X := Fin 3 → List R → S
          let P : X → Prop := fun x => x 2 [] = s₀ ∧
            (∀ σ r, T.lookahead r = false → x 1 (σ ++ [r]) = x 0 σ) ∧
            (∀ σ s, σ ≠ [] → TaskKnown T s₀ σ s → x 2 σ = s)
          have hP : IsClosed {x : X | P x} := by
            change IsClosed ({x : X | x 2 [] = s₀} ∩
              ({x : X | ∀ σ r, T.lookahead r = false → x 1 (σ ++ [r]) = x 0 σ} ∩
              {x : X | ∀ σ s, σ ≠ [] → TaskKnown T s₀ σ s → x 2 σ = s}))
            apply IsClosed.inter (isClosed_eq (by fun_prop) continuous_const)
            apply IsClosed.inter
            · simp only [Set.setOf_forall]
              exact isClosed_iInter fun σ => isClosed_iInter fun r => isClosed_iInter fun hr =>
                isClosed_eq (by fun_prop) (by fun_prop)
            · simp only [Set.setOf_forall]
              exact isClosed_iInter fun σ => isClosed_iInter fun s => isClosed_iInter fun hσ =>
                isClosed_iInter fun hs => isClosed_eq (by fun_prop) continuous_const
          let K := {x : X // P x}
          letI : CompactSpace K := isCompact_iff_compactSpace.mp hP.isCompact
          letI : MeasurableSpace K := borel K
          letI : BorelSpace K := ⟨rfl⟩
          let alg : K → TaskOnline T := fun k =>
            { before := k.1 0
              moment := k.1 1
              after := k.1 2
              zero := k.2.2.1 }
          let normal : A.ι → K := fun i =>
            ⟨![(F (A.alg i)).before, (F (A.alg i)).moment, (F (A.alg i)).after],
              ⟨by change (F (A.alg i)).after [] = s₀; rw [hF0]; exact hA.1 i,
                (F (A.alg i)).zero, hFknown (A.alg i)⟩⟩
          have hnormal : ∀ i, alg (normal i) = F (A.alg i) := by
            intro i
            rfl
          have hcoord : ∀ (a : Fin 3) (σ : List R), IsLocallyConstant (fun k : K => k.1 a σ) := by
            intro a σ
            apply (IsLocallyConstant.iff_continuous _).mpr
            change Continuous (fun k : {x : X // P x} => k.1 a σ)
            have h₁ : Continuous (fun x : X => x a) := continuous_apply a
            have h₂ : Continuous (fun x : List R → S => x σ) := continuous_apply σ
            exact h₂.comp (h₁.comp continuous_subtype_val)
          have hloc : ∀ σ, IsLocallyConstant (fun k : K => (alg k).cost σ) := by
            intro σ
            induction σ using List.reverseRecOn with
            | nil =>
              apply IsLocallyConstant.of_constant
              intro x y
              simp [TaskOnline.cost]
            | append_singleton σ r ih =>
              simp only [hcost_append]
              exact ih.add (((((hcoord 2 σ).comp₂ (hcoord 0 σ)
                (fun x y => (T.distance x y : ENNReal))).add
                ((hcoord 0 σ).comp₂ (hcoord 1 (σ ++ [r]))
                  (fun x y => (T.distance x y : ENNReal)))).add
                  ((hcoord 1 (σ ++ [r])).comp (T.task r))).add
                ((hcoord 1 (σ ++ [r])).comp₂ (hcoord 2 (σ ++ [r]))
                  (fun x y => (T.distance x y : ENNReal))))
          let trunc : List R → ℕ → C(K, NNReal) := fun σ n =>
            ⟨fun k => (min ((alg k).cost σ) (n : ENNReal)).toNNReal,
              ((hloc σ).comp (fun c => (min c (n : ENNReal)).toNNReal)).continuous⟩
          have htrunc : ∀ σ n k, (trunc σ n k : ENNReal) = min ((alg k).cost σ) (n : ENNReal) := by
            intro σ n k
            exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top (by simp) (min_le_right _ _))
          obtain ⟨a, ha⟩ := hA.2
          let bound : List R → ENNReal := fun σ =>
            if taskOpt T s₀ σ = ⊤ then ⊤ else ENNReal.ofReal (α * (taskOpt T s₀ σ).toReal + a)
          have hbound : ∀ σ, A.expCost (g σ) ≤ bound σ := by
            intro σ
            by_cases hσ : taskOpt T s₀ σ = ⊤
            · simp [bound, hσ]
            · simpa only [bound, if_neg hσ, hgopt] using ha (g σ) (by simpa only [hgopt] using hσ)
          let V : List R × ℕ → Set (ProbabilityMeasure K) := fun p =>
            {ν | (∫⁻ k, (trunc p.1 p.2 k : ENNReal) ∂(ν : Measure K)) ≤ bound p.1}
          have hVclosed : ∀ p, IsClosed (V p) := by
            intro p
            exact isClosed_le (ProbabilityMeasure.continuous_lintegral_continuousMap (trunc p.1 p.2))
              continuous_const
          have hfinite : ∀ u : Finset (List R × ℕ), (⋂ p ∈ u, V p).Nonempty := by
            intro u
            let Y := (p : u) → Set.range (fun C : TaskOnline T => C.cost (g p.1.1))
            letI : ∀ p : u, Fintype (Set.range (fun C : TaskOnline T => C.cost (g p.1.1))) :=
              fun p => (hcostrange (g p.1.1)).fintype
            letI : MeasurableSpace Y := inferInstance
            let profile : A.ι → Y := fun i p => ⟨(A.alg i).cost (g p.1.1), ⟨A.alg i, rfl⟩⟩
            have hmprofile : Measurable profile := by
              apply measurable_pi_lambda
              intro p
              exact (A.meas (g p.1.1)).subtype_mk
            let Z := Set.range profile
            letI : Fintype Z := Fintype.ofFinite Z
            letI : MeasurableSpace Z := inferInstance
            let pr : A.ι → Z := fun i => ⟨profile i, ⟨i, rfl⟩⟩
            have hmpr : Measurable pr := hmprofile.subtype_mk
            let rep : Z → A.ι := fun z => Classical.choose z.2
            have hrep : ∀ z, profile (rep z) = z.1 := fun z => Classical.choose_spec z.2
            let out : Z → K := fun z => normal (rep z)
            have hmout : Measurable out := measurable_of_countable _
            let ν : ProbabilityMeasure K :=
              ⟨Measure.map (out ∘ pr) A.μ, Measure.isProbabilityMeasure_map (hmout.comp hmpr).aemeasurable⟩
            refine ⟨ν, ?_⟩
            simp only [Set.mem_iInter]
            intro p hp
            change (∫⁻ k, (trunc p.1 p.2 k : ENNReal) ∂(ν : Measure K)) ≤ bound p.1
            rw [show (ν : Measure K) = Measure.map (out ∘ pr) A.μ from rfl,
              lintegral_map (trunc p.1 p.2).continuous.measurable.coe_nnreal_ennreal (hmout.comp hmpr)]
            apply le_trans (lintegral_mono fun i => ?_) (hbound p.1)
            rw [htrunc]
            apply (min_le_left _ _).trans
            have hh := congrArg (fun y : Y => (y ⟨p, hp⟩).1) (hrep (pr i))
            change (A.alg (rep (pr i))).cost (g p.1) = (A.alg i).cost (g p.1) at hh
            change (alg (normal (rep (pr i)))).cost p.1 ≤ _
            rw [hnormal, ← hh]
            exact le_self_add.trans (hFcost _ _)
          obtain ⟨ν, hν⟩ := CompactSpace.iInter_nonempty hVclosed hfinite
          have hνbound : ∀ σ n, (∫⁻ k, (trunc σ n k : ENNReal) ∂(ν : Measure K)) ≤ bound σ := by
            intro σ n
            exact Set.mem_iInter.mp hν (σ, n)
          have hνfull : ∀ σ, (∫⁻ k, (alg k).cost σ ∂(ν : Measure K)) ≤ bound σ := by
            intro σ
            have heq : ∀ k, (⨆ n : ℕ, (trunc σ n k : ENNReal)) = (alg k).cost σ := by
              intro k
              simp only [htrunc]
              exact (inf_iSup_eq ((alg k).cost σ) (fun n : ℕ => (n : ENNReal))).symm.trans
                (by rw [ENNReal.iSup_natCast]; exact inf_top_eq _)
            calc
              (∫⁻ k, (alg k).cost σ ∂(ν : Measure K)) =
                  ∫⁻ k, ⨆ n : ℕ, (trunc σ n k : ENNReal) ∂(ν : Measure K) := by
                    apply lintegral_congr
                    intro k
                    exact (heq k).symm
              _ = ⨆ n : ℕ, ∫⁻ k, (trunc σ n k : ENNReal) ∂(ν : Measure K) := by
                apply lintegral_iSup
                · intro n
                  exact (trunc σ n).continuous.measurable.coe_nnreal_ennreal
                · intro n m hnm k
                  simp only [htrunc]
                  exact min_le_min le_rfl (by exact_mod_cast hnm)
              _ ≤ bound σ := iSup_le (hνbound σ)
          let B : TaskRandomized T :=
            { ι := K
              μ := (ν : Measure K)
              prob := inferInstance
              alg := alg
              meas := fun σ => (hloc σ).continuous.measurable }
          refine ⟨B, ⟨?_, a, ?_⟩, ?_⟩
          · intro k
            exact k.2.1
          · intro σ hσ
            exact (hνfull σ).trans_eq (if_neg hσ)
          · intro σ s hσ hs
            exact Filter.Eventually.of_forall fun k => k.2.2.2 σ s hσ hs

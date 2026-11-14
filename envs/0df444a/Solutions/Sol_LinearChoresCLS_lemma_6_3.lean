-- Prove2me | solution 1 for LinearChoresCLS.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T19:44:37.151481+00:00
-- url     : https://prove2.me/submissions/d518e6b1-79f9-4524-9b4f-6a6d45f072f0

import Definitions.Def_LinearChoresCLS_Psi

open Finset LinearChoresCLS

section
variable {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
variable {F : ChoresMarket N M} {p : M → ℝ} {z : N → M → ℝ}

private theorem ratio_le_mu (a : N) (j : M) : p j / F.disutil a j ≤ F.mu a p :=
  Finset.le_sup' (fun k => p k / F.disutil a k) (Finset.mem_univ j)

/-- A one-chore optimal-ratio bundle witnesses the minimum disutility.
Equality in the resulting weighted sum forces every used chore to attain the ratio. -/
private theorem demand_conditions (hF : F.Valid) (hCE : F.IsCE p z) (a : N) :
    (∑ j, p j * z a j) = F.earn a ∧
    0 < F.mu a p ∧ ∀ j, 0 < z a j → p j / F.disutil a j = F.mu a p := by
  classical
  obtain ⟨hz, hbudget, hopt⟩ := hCE.2.2.1 a
  have hpospay : 0 < ∑ j, p j * z a j := lt_of_lt_of_le (hF.2.1 a) hbudget
  obtain ⟨i, hi⟩ : ∃ i, 0 < p i * z a i := by
    by_contra! hall
    exact hpospay.not_ge (Finset.sum_nonpos (fun i _ => hall i))
  have hpi : 0 < p i := by
    by_contra! h
    rw [le_antisymm h (hCE.1 i), zero_mul] at hi
    exact hi.false
  have hmu : 0 < F.mu a p :=
    lt_of_lt_of_le (div_pos hpi (hF.1 a i)) (ratio_le_mu a i)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_eq_sup' (univ_nonempty : (univ : Finset M).Nonempty)
    (fun j => p j / F.disutil a j)
  change F.mu a p = _ at hb
  have hbmul : F.mu a p * F.disutil a b = p b := (eq_div_iff (hF.1 a b).ne').mp hb
  have hpb : 0 < p b := by rw [← hbmul]; exact mul_pos hmu (hF.1 a b)
  let y : M → ℝ := fun j => if j = b then F.earn a / p b else 0
  have hy : ∀ j, 0 ≤ y j := by
    intro j
    dsimp [y]
    split_ifs
    · exact div_nonneg (hF.2.1 a).le hpb.le
    · exact le_rfl
  have hyval : ∑ j, p j * y j = F.earn a := by
    simp [y, mul_ite]
    field_simp
  have hycost : ∑ j, F.disutil a j * y j = F.disutil a b * (F.earn a / p b) := by
    simp [y, mul_ite]
  have hcost := hopt y hy hyval.ge
  rw [hycost] at hcost
  have hcap : F.mu a p * (∑ j, F.disutil a j * z a j) ≤ F.earn a := calc
    _ ≤ F.mu a p * (F.disutil a b * (F.earn a / p b)) := mul_le_mul_of_nonneg_left hcost hmu.le
    _ = _ := by rw [← mul_assoc, hbmul]; field_simp
  have hterm (j : M) : p j * z a j ≤ F.mu a p * (F.disutil a j * z a j) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((div_le_iff₀ (hF.1 a j)).mp (ratio_le_mu a j)) (hz j)
  have hsum := Finset.sum_le_sum (s := (univ : Finset M)) (fun j _ => hterm j)
  rw [← Finset.mul_sum] at hsum
  have hearn := le_antisymm (hsum.trans hcap) hbudget
  refine ⟨hearn, hmu, ?_⟩
  intro j hj
  have hgap : ∑ k, (F.mu a p * (F.disutil a k * z a k) - p k * z a k) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have hg := Finset.single_le_sum (s := (univ : Finset M))
    (f := fun k => F.mu a p * (F.disutil a k * z a k) - p k * z a k)
    (fun k _ => sub_nonneg.mpr (hterm k)) (Finset.mem_univ j)
  rw [hgap] at hg
  apply (div_eq_iff (hF.1 a j).ne').mpr
  apply mul_right_cancel₀ hj.ne'
  rw [mul_assoc]
  exact le_antisymm (hterm j) (sub_nonpos.mp hg)

open Classical in
/-- If outsiders cannot earn the whole value of the output, some gadget agent uses it. -/
private theorem inside_uses (hF : F.Valid) (hCE : F.IsCE p z) (a₀ a₁ a₂ : N) (o : M)
    (h : (∑ a ∈ univ.filter (fun a => a ≠ a₀ ∧ a ≠ a₁ ∧ a ≠ a₂ ∧ 0 < z a o), F.earn a)
      < F.supply o * p o) :
    0 < z a₀ o ∨ 0 < z a₁ o ∨ 0 < z a₂ o := by
  classical
  by_contra! hn
  rw [Finset.sum_filter] at h
  have bound (a : N) : z a o * p o ≤
      (if a ≠ a₀ ∧ a ≠ a₁ ∧ a ≠ a₂ ∧ 0 < z a o then F.earn a else 0) := by
    split_ifs with ha
    · rw [mul_comm, ← (demand_conditions hF hCE a).1]
      exact Finset.single_le_sum (fun j _ => mul_nonneg (hCE.1 j) (hCE.2.1 a j)) (mem_univ o)
    · have hzero : z a o = 0 := by
        apply le_antisymm _ (hCE.2.1 a o)
        by_contra! hpos
        exact ha ⟨fun e => (not_lt.mpr hn.1) (e ▸ hpos),
          fun e => (not_lt.mpr hn.2.1) (e ▸ hpos),
          fun e => (not_lt.mpr hn.2.2) (e ▸ hpos), hpos⟩
      simp [hzero]
  have hsum := Finset.sum_le_sum (s := (univ : Finset N)) (fun a _ => bound a)
  rw [← Finset.sum_mul, hCE.2.2.2 o] at hsum
  exact (not_lt_of_ge hsum) h

omit [Nonempty M] in
/-- If the whole output pays less than one agent's requirement, she must use another chore. -/
private theorem uses_other (hCE : F.IsCE p z) (a : N) (o : M)
    (h : F.supply o * p o < F.earn a) : ∃ j, j ≠ o ∧ 0 < z a j := by
  classical
  by_contra! hn
  have hone : (∑ j, p j * z a j) = p o * z a o := by
    apply Finset.sum_eq_single o
    · intro j _ hj
      rw [le_antisymm (hn j hj) (hCE.2.1 a j), mul_zero]
    · simp
  have hqty : z a o ≤ F.supply o := by
    rw [← hCE.2.2.2 o]
    exact Finset.single_le_sum (fun i _ => hCE.2.1 i o) (mem_univ a)
  have hbudget := (hCE.2.2.1 a).2.1
  rw [hone, mul_comm] at hbudget
  exact (not_lt_of_ge (hbudget.trans (mul_le_mul_of_nonneg_right hqty (hCE.1 o)))) h

end
open Classical in
theorem solution {N M : Type*} [Fintype N] [Fintype M] [Nonempty M]
    (F : ChoresMarket N M) (hF : F.Valid) (p : M → ℝ) (z : N → M → ℝ) (hCE : F.IsCE p z)
    (j j' pplus pminus : M) (hjj' : j ≠ j') (hpj : pplus ≠ j) (hpj' : pplus ≠ j')
    (hmj : pminus ≠ j) (hmj' : pminus ≠ j') (hpm : pplus ≠ pminus)
    (amax a1 a2 : N) (h01 : amax ≠ a1) (h02 : amax ≠ a2) (h12 : a1 ≠ a2) (B S q : ℝ)
    (hB : F.earn amax = B ∧ F.earn a1 = B ∧ F.earn a2 = B)
    (hS : F.supply pplus = S ∧ F.supply pminus = S)
    (hd : F.disutil amax j = q ∧ F.disutil amax j' = q ∧ F.disutil amax pplus = 1 ∧
      F.disutil a1 j = 1 / q ∧ F.disutil a1 pminus = 1 ∧
      F.disutil a2 j' = 1 / q ∧ F.disutil a2 pminus = 1)
    (hdes : (∀ ℓ, 0 < z amax ℓ → ℓ = j ∨ ℓ = j' ∨ ℓ = pplus) ∧
      (∀ ℓ, 0 < z a1 ℓ → ℓ = j ∨ ℓ = pminus) ∧ (∀ ℓ, 0 < z a2 ℓ → ℓ = j' ∨ ℓ = pminus))
    (hpc : (∑ a ∈ univ.filter (fun a => a ≠ amax ∧ a ≠ a1 ∧ a ≠ a2 ∧ 0 < z a pplus), F.earn a)
        < S * p pplus ∧ S * p pplus < B ∧
      (∑ a ∈ univ.filter (fun a => a ≠ amax ∧ a ≠ a1 ∧ a ≠ a2 ∧ 0 < z a pminus), F.earn a)
        < S * p pminus ∧ S * p pminus < B) :
    p pplus = max (p j) (p j') / q ∧ p pminus = q * min (p j) (p j') ∧
      Real.log (p pplus / p pminus) = |Real.log (p j / p j')| - 2 * Real.log q ∧
      F.mu amax p = max (p j) (p j') / q ∧ F.mu a1 p = q * p j ∧ F.mu a2 p = q * p j' := by
  classical
  obtain ⟨Bmax, B₁, B₂⟩ := hB
  obtain ⟨Splus, Sminus⟩ := hS
  obtain ⟨dj, dj', dplus, d₁, d₁minus, d₂, d₂minus⟩ := hd
  obtain ⟨desMax, des₁, des₂⟩ := hdes
  obtain ⟨loPlus, hiPlus, loMinus, hiMinus⟩ := hpc
  have qpos : 0 < q := by simpa [dj] using hF.1 amax j
  have used (a : N) (i : M) (h : 0 < z a i) :=
    (demand_conditions hF hCE a).2.2 i h
  -- The lower payment bounds force gadget participation in each output.
  have plusUse : 0 < z amax pplus := by
    rcases inside_uses hF hCE amax a1 a2 pplus (by simpa [Splus] using loPlus) with h | h | h
    · exact h
    · rcases des₁ _ h with e | e <;> contradiction
    · rcases des₂ _ h with e | e <;> contradiction
  have minusUse : 0 < z a1 pminus ∨ 0 < z a2 pminus := by
    rcases inside_uses hF hCE amax a1 a2 pminus (by simpa [Sminus] using loMinus) with h | h
    · rcases desMax _ h with e | e | e
      · exact (hmj e).elim
      · exact (hmj' e).elim
      · exact (hpm e.symm).elim
    · exact h
  -- Each agent also needs earnings from an input.
  obtain ⟨k, hk, hzk⟩ := uses_other hCE amax pplus (by simpa [Splus, Bmax] using hiPlus)
  have maxInput : k = j ∨ k = j' := (desMax _ hzk).elim Or.inl
    (fun h => Or.inr (h.resolve_right hk))
  have usedInput (a : N) (i : M) (hB : F.earn a = B)
      (hdes : ∀ ℓ, 0 < z a ℓ → ℓ = i ∨ ℓ = pminus) : 0 < z a i := by
    obtain ⟨c, hc, hzc⟩ := uses_other hCE a pminus (by simpa [Sminus, hB] using hiMinus)
    exact ((hdes c hzc).resolve_right hc) ▸ hzc
  have mu₁ : F.mu a1 p = q * p j := by
    simpa [d₁, div_div_eq_mul_div, mul_comm] using (used a1 j (usedInput a1 j B₁ des₁)).symm
  have mu₂ : F.mu a2 p = q * p j' := by
    simpa [d₂, div_div_eq_mul_div, mul_comm] using (used a2 j' (usedInput a2 j' B₂ des₂)).symm
  have plusMu : p pplus = F.mu amax p := by simpa [dplus] using used amax pplus plusUse
  have muMax : F.mu amax p = max (p j) (p j') / q := by
    apply le_antisymm
    · rcases maxInput with rfl | rfl
      · rw [← used _ _ hzk, dj]
        exact div_le_div_of_nonneg_right (le_max_left _ _) qpos.le
      · rw [← used _ _ hzk, dj']
        exact div_le_div_of_nonneg_right (le_max_right _ _) qpos.le
    · apply (div_le_iff₀ qpos).mpr
      apply max_le
      · exact (div_le_iff₀ qpos).mp (by simpa [dj] using ratio_le_mu (F := F) (p := p) amax j)
      · exact (div_le_iff₀ qpos).mp (by simpa [dj'] using ratio_le_mu (F := F) (p := p) amax j')
  have plusPrice := plusMu.trans muMax
  have minusPrice : p pminus = q * min (p j) (p j') := by
    rw [mul_min_of_nonneg _ _ qpos.le]
    have h₁ : p pminus ≤ q * p j := by
      simpa [d₁minus, mu₁] using ratio_le_mu (F := F) (p := p) a1 pminus
    have h₂ : p pminus ≤ q * p j' := by
      simpa [d₂minus, mu₂] using ratio_le_mu (F := F) (p := p) a2 pminus
    apply le_antisymm (le_min h₁ h₂)
    rcases minusUse with h | h
    · have he : p pminus = q * p j := by simpa [d₁minus, mu₁] using used a1 pminus h
      exact (min_le_left _ _).trans he.ge
    · have he : p pminus = q * p j' := by simpa [d₂minus, mu₂] using used a2 pminus h
      exact (min_le_right _ _).trans he.ge
  refine ⟨plusPrice, minusPrice, ?_, muMax, mu₁, mu₂⟩
  have posInput (a : N) (i : M) (hm : F.mu a p = q * p i) : 0 < p i := by
    have h := (demand_conditions hF hCE a).2.1
    rw [hm] at h
    exact (mul_pos_iff_of_pos_left qpos).mp h
  have pj := posInput a1 j mu₁
  have pj' := posInput a2 j' mu₂
  rw [plusPrice, minusPrice]
  rcases le_total (p j) (p j') with hh | hh
  · rw [max_eq_right hh, min_eq_left hh]
    rw [Real.log_div (div_ne_zero pj'.ne' qpos.ne') (mul_ne_zero qpos.ne' pj.ne'),
      Real.log_div pj'.ne' qpos.ne', Real.log_mul qpos.ne' pj.ne',
      Real.log_div pj.ne' pj'.ne', abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log pj hh))]
    ring
  · rw [max_eq_left hh, min_eq_right hh]
    rw [Real.log_div (div_ne_zero pj.ne' qpos.ne') (mul_ne_zero qpos.ne' pj'.ne'),
      Real.log_div pj.ne' qpos.ne', Real.log_mul qpos.ne' pj'.ne',
      Real.log_div pj.ne' pj'.ne', abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log pj' hh))]
    ring

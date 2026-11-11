-- Prove2me | solution 1 for MNLTrisection.Adaptive.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T10:17:18.677279+00:00
-- url     : https://prove2.me/submissions/fa34f209-3b62-40cb-b80b-121d2e2cae5a

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

set_option autoImplicit false

/-! Child A of a6a3dbbc (MNLTrisection.Adaptive.theorem_3): MNL level-set structure facts. -/

namespace A6a3

open MNLBandit.UCB ChoiceCDLP.MNL MNLTrisection.Adaptive

variable {N : ℕ}

lemma rev_eq (v r : Fin N → ℝ) (S : Finset (Fin N)) :
    rev v r S = (∑ j ∈ S, r j * v j) / (∑ j ∈ S, v j + 1) := rfl

lemma denom_pos (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    0 < ∑ j ∈ S, v j + 1 := by
  have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv j); linarith

lemma rev_le_optRev (v r : Fin N → ℝ) (S : Finset (Fin N)) : rev v r S ≤ optRev v r := by
  unfold optRev optRevenue
  exact Finset.le_sup' (fun S => mnlObjective v r 1 S) (Finset.mem_univ S)

lemma optRev_nonneg (v r : Fin N → ℝ) : 0 ≤ optRev v r := by
  have := rev_le_optRev v r ∅
  simpa [rev, mnlObjective] using this

lemma exists_opt (v r : Fin N → ℝ) : ∃ S, rev v r S = optRev v r := by
  unfold optRev optRevenue
  obtain ⟨S, -, hS⟩ := Finset.exists_mem_eq_sup'
    (⟨∅, Finset.mem_univ _⟩ : (Finset.univ : Finset (Finset (Fin N))).Nonempty)
    (fun S => mnlObjective v r 1 S)
  exact ⟨S, hS.symm⟩

lemma rev_nonneg (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i)
    (S : Finset (Fin N)) : 0 ≤ rev v r S := by
  rw [rev_eq]
  exact div_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hr j) (hv j)))
    (denom_pos v hv S).le

lemma rev_le_one (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, r i ≤ 1)
    (S : Finset (Fin N)) : rev v r S ≤ 1 := by
  rw [rev_eq, div_le_one (denom_pos v hv S)]
  have : ∑ j ∈ S, r j * v j ≤ ∑ j ∈ S, v j :=
    Finset.sum_le_sum (fun j _ => by nlinarith [hr j, hv j])
  linarith

lemma optRev_le_one (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, r i ≤ 1) :
    optRev v r ≤ 1 := by
  obtain ⟨S, hS⟩ := exists_opt v r
  rw [← hS]; exact rev_le_one v r hv hr S

lemma le_rev_iff (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) (θ : ℝ) :
    θ ≤ rev v r S ↔ θ * (∑ j ∈ S, v j + 1) ≤ ∑ j ∈ S, r j * v j := by
  rw [rev_eq, le_div_iff₀ (denom_pos v hv S)]

lemma sum_shift (v r : Fin N → ℝ) (S : Finset (Fin N)) (θ : ℝ) :
    ∑ j ∈ S, (r j - θ) * v j = ∑ j ∈ S, r j * v j - θ * ∑ j ∈ S, v j := by
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

lemma levelSet_max (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) (S : Finset (Fin N)) :
    ∑ j ∈ S, (r j - θ) * v j ≤ ∑ j ∈ levelSet r θ, (r j - θ) * v j := by
  have h1 : ∑ j ∈ S, (r j - θ) * v j ≤
      ∑ j ∈ S.filter (fun j => θ ≤ r j), (r j - θ) * v j := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun j => θ ≤ r j)]
    have : ∑ j ∈ S.filter (fun j => ¬ θ ≤ r j), (r j - θ) * v j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      rw [Finset.mem_filter] at hj
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp hj.2]) (hv j)
    linarith
  have h2 : ∑ j ∈ S.filter (fun j => θ ≤ r j), (r j - θ) * v j ≤
      ∑ j ∈ levelSet r θ, (r j - θ) * v j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_filter] at hj
      simp [levelSet, hj.2]
    · intro j hj _
      simp only [levelSet, Finset.mem_filter] at hj
      exact mul_nonneg (by linarith [hj.2]) (hv j)
  linarith

/-- Below the optimum the level set earns at least its threshold: `θ ≤ θ* → θ ≤ F θ`. -/
lemma le_F_of_le (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) (hθ : θ ≤ optRev v r) :
    θ ≤ F v r θ := by
  obtain ⟨S, hS⟩ := exists_opt v r
  have hopt := (le_rev_iff v r hv S (optRev v r)).1 (le_of_eq hS.symm)
  have hmax := levelSet_max v r hv θ S
  rw [sum_shift, sum_shift] at hmax
  have hVS : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  unfold F
  rw [le_rev_iff v r hv]
  nlinarith

lemma F_le_optRev (v r : Fin N → ℝ) (θ : ℝ) : F v r θ ≤ optRev v r :=
  rev_le_optRev v r _

lemma F_optRev (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : F v r (optRev v r) = optRev v r :=
  le_antisymm (F_le_optRev v r _) (le_F_of_le v r hv _ le_rfl)

lemma thetaStar_eq (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) : thetaStar v r = optRev v r := by
  unfold thetaStar Fstar
  apply IsGreatest.csSup_eq
  refine ⟨⟨optRev v r, Set.mem_Ici.2 (optRev_nonneg v r), F_optRev v r hv⟩, ?_⟩
  rintro z ⟨θ, -, rfl⟩
  exact F_le_optRev v r θ

/-- Exploit regret below the optimum: `θ ≤ θ* → θ* − F θ ≤ θ* − θ`. -/
lemma regret_le_of_le (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (θ : ℝ) (hθ : θ ≤ optRev v r) :
    optRev v r - F v r θ ≤ optRev v r - θ := by
  linarith [le_F_of_le v r hv θ hθ]

/-- Above the optimum `F` is antitone: `θ* ≤ a ≤ y → F y ≤ F a`. -/
lemma F_antitone_above (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (a y : ℝ)
    (ha : optRev v r ≤ a) (hay : a ≤ y) : F v r y ≤ F v r a := by
  have hsub : levelSet r y ⊆ levelSet r a := by
    intro j hj
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    linarith
  have hFy : F v r y ≤ a := le_trans (F_le_optRev v r y) ha
  unfold F at hFy ⊢
  rw [rev_eq] at hFy
  rw [rev_eq, rev_eq]
  set M := levelSet r a \ levelSet r y with hM
  have hN := Finset.sum_sdiff hsub (f := fun j => r j * v j)
  have hV := Finset.sum_sdiff hsub (f := fun j => v j)
  rw [← hN, ← hV]
  have hDy := denom_pos v hv (levelSet r y)
  have hVm : 0 ≤ ∑ j ∈ M, v j := Finset.sum_nonneg (fun j _ => hv j)
  have hNm : a * ∑ j ∈ M, v j ≤ ∑ j ∈ M, r j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    rw [hM, Finset.mem_sdiff] at hj
    simp only [levelSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact mul_le_mul_of_nonneg_right hj.1 (hv j)
  rw [div_le_iff₀ hDy] at hFy
  rw [div_le_div_iff₀ hDy (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right hFy hVm]

/-! Child B: the history measure sums to one; regret as an expectation; regret ≤ T. -/

lemma choiceProb_nonneg (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N))
    (c : Option (Fin N)) : 0 ≤ choiceProb v S c := by
  have hD := denom_pos v hv S
  cases c with
  | none => simp only [choiceProb]; exact div_nonneg zero_le_one (by linarith)
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv i) (by linarith)
    · exact le_rfl

lemma choiceProb_sum (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    ∑ c : Option (Fin N), choiceProb v S c = 1 := by
  have hD : (1 + ∑ j ∈ S, v j) ≠ 0 := by linarith [denom_pos v hv S]
  rw [Fintype.sum_option]
  simp only [choiceProb]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← add_div]
  exact div_self hD

lemma histPrefix_snoc_castSucc {T : ℕ} (h : History N T) (c : Option (Fin N)) (t : Fin T) :
    histPrefix (Fin.snoc h c : History N (T + 1)) t.castSucc = histPrefix h t := by
  funext u
  show (Fin.snoc h c : History N (T + 1)) (Fin.castLE _ u) = h (Fin.castLE _ u)
  have : (Fin.castLE (t.castSucc).isLt.le u : Fin (T + 1)) =
      Fin.castSucc (Fin.castLE t.isLt.le u) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma histPrefix_snoc_last {T : ℕ} (h : History N T) (c : Option (Fin N)) :
    histPrefix (Fin.snoc h c : History N (T + 1)) (Fin.last T) = h := by
  funext u
  show (Fin.snoc h c : History N (T + 1)) (Fin.castLE _ u) = h u
  have : (Fin.castLE (Fin.last T).isLt.le u : Fin (T + 1)) = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma offered_snoc_castSucc (π : Policy N) {T : ℕ} (h : History N T) (c : Option (Fin N))
    (t : Fin T) : offered π (Fin.snoc h c : History N (T + 1)) t.castSucc = offered π h t :=
  congrArg (π t.val) (histPrefix_snoc_castSucc h c t)

lemma offered_snoc_last (π : Policy N) {T : ℕ} (h : History N T) (c : Option (Fin N)) :
    offered π (Fin.snoc h c : History N (T + 1)) (Fin.last T) = π T h :=
  congrArg (π T) (histPrefix_snoc_last h c)

lemma histProb_snoc (v : Fin N → ℝ) (π : Policy N) {T : ℕ} (h : History N T)
    (c : Option (Fin N)) :
    histProb v π (Fin.snoc h c : History N (T + 1)) = histProb v π h * choiceProb v (π T h) c := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  simp only [offered_snoc_castSucc, offered_snoc_last, Fin.snoc_castSucc, Fin.snoc_last]

lemma sum_hist_succ {T : ℕ} (f : History N (T + 1) → ℝ) :
    ∑ h : History N (T + 1), f h =
      ∑ h : History N T, ∑ c : Option (Fin N), f (Fin.snoc h c) := by
  let e : History N T × Option (Fin N) ≃ History N (T + 1) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun h => (Fin.init h, h (Fin.last T))
      left_inv := fun p => by simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun h => by simp [Fin.snoc_init_self] }
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

lemma histProb_nonneg (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) {T : ℕ}
    (h : History N T) : 0 ≤ histProb v π h :=
  Finset.prod_nonneg (fun t _ => choiceProb_nonneg v hv _ _)

lemma histProb_sum_one (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ) :
    ∑ h : History N T, histProb v π h = 1 := by
  induction T with
  | zero => simp [histProb]
  | succ T ih =>
    rw [sum_hist_succ]
    simp_rw [histProb_snoc, ← Finset.mul_sum, choiceProb_sum v hv, mul_one]
    exact ih

lemma regret_eq (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ) :
    regret v r Finset.univ ⟨∅, Finset.mem_univ _⟩ π T =
      ∑ h : History N T, histProb v π h *
        ∑ t : Fin T, (optRev v r - rev v r (offered π h t)) := by
  unfold regret expectedRevenue
  have h1 := histProb_sum_one v hv π T
  have key : ∀ h : History N T, histProb v π h *
      ∑ t : Fin T, (optRev v r - rev v r (offered π h t)) =
      histProb v π h * ((T : ℝ) * optRev v r) -
        histProb v π h * ∑ t : Fin T, mnlObjective v r 1 (offered π h t) := by
    intro h
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub]
    rfl
  rw [Finset.sum_congr rfl (fun h _ => key h), Finset.sum_sub_distrib, ← Finset.sum_mul, h1,
    one_mul]
  rfl

lemma regret_le_T (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr0 : ∀ i, 0 ≤ r i)
    (hr1 : ∀ i, r i ≤ 1) (π : Policy N) (T : ℕ) :
    regret v r Finset.univ ⟨∅, Finset.mem_univ _⟩ π T ≤ T := by
  rw [regret_eq v r hv]
  calc _ ≤ ∑ h : History N T, histProb v π h * (T : ℝ) := by
        apply Finset.sum_le_sum
        intro h _
        apply mul_le_mul_of_nonneg_left _ (histProb_nonneg v hv π h)
        calc ∑ t : Fin T, (optRev v r - rev v r (offered π h t)) ≤ ∑ t : Fin T, (1 : ℝ) :=
              Finset.sum_le_sum (fun t _ => by
                linarith [optRev_le_one v r hv hr1, rev_nonneg v r hv hr0 (offered π h t)])
          _ = T := by simp
    _ = T := by rw [← Finset.sum_mul, histProb_sum_one v hv π T, one_mul]

lemma le_two_sqrt (T : ℕ) (hT : T ≤ 4) : (T : ℝ) ≤ 2 * Real.sqrt T := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) T)
  have h0 := Real.sqrt_nonneg (T : ℝ)
  have hT' : (T : ℝ) ≤ 4 := by exact_mod_cast hT
  have h4 : Real.sqrt T ≤ 2 := by nlinarith
  nlinarith

/-! Child D (start): the trisection invariant `b − a = (2/3)^τ`, `0 ≤ a`, `b ≤ 1` on every reachable state. -/

def Inv (s : AlgState) : Prop := s.b - s.a = (2 / 3 : ℝ) ^ s.tau ∧ 0 ≤ s.a ∧ s.b ≤ 1

lemma step_inv (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N)) (hs : Inv s) :
    Inv (step r T s c) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hP := pow_pos (by norm_num : (0 : ℝ) < 2 / 3) s.tau
  unfold step
  split_ifs
  · exact ⟨h1, h2, h3⟩
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [epochStart, AlgState.y, AlgState.x, pow_succ] <;> linarith
  · refine ⟨?_, ?_, ?_⟩ <;> simp only [epochStart, AlgState.y, AlgState.x, pow_succ] <;> linarith
  · exact ⟨h1, h2, h3⟩

lemma inv_foldl (r : Fin N → ℝ) (T : ℕ) (l : List (Option (Fin N))) (s : AlgState)
    (hs : Inv s) : Inv (l.foldl (step r T) s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons c l ih => exact ih _ (step_inv r T s c hs)

lemma inv_init : Inv initState := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [initState, epochStart]

lemma stateAt_inv (r : Fin N → ℝ) (T t : ℕ) (p : Fin t → Option (Fin N)) :
    Inv (stateAt r T t p) :=
  inv_foldl r T _ _ inv_init

lemma yx_eq (s : AlgState) (hs : Inv s) : s.y - s.x = eps s.tau := by
  unfold AlgState.y AlgState.x eps
  linarith [hs.1]

/-! Child D (cont.): a period potential (`Σ_{σ<τ} n_σ + k ≤ t`), started epochs have
`X_τ = 8Tε_τ² ≥ 9/4` once `T ≥ 3`, and the final confidence radius is at most `ε_τ/2`. -/

noncomputable def nSum (T τ : ℕ) : ℕ := ∑ σ ∈ Finset.range τ, nEpoch T σ

noncomputable def pot (T : ℕ) (s : AlgState) : ℕ := nSum T s.tau + s.k

lemma nSum_succ (T τ : ℕ) : nSum T (τ + 1) = nSum T τ + nEpoch T τ := by
  simp [nSum, Finset.sum_range_succ]

lemma step_pot (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N)) (hs : Inv s) :
    pot T (step r T s c) ≤ pot T s + 1 := by
  have hyx : innerLen T (s.y - s.x) = nEpoch T s.tau := by rw [yx_eq s hs]; rfl
  unfold step
  split_ifs with h1 h2 h3
  · simp [pot]
  · rw [hyx] at h2
    simp only [pot, epochStart, nSum_succ]
    omega
  · rw [hyx] at h2
    simp only [pot, epochStart, nSum_succ]
    omega
  · simp [pot]
    omega

lemma pot_foldl (r : Fin N → ℝ) (T : ℕ) (l : List (Option (Fin N))) (s : AlgState)
    (hs : Inv s) : pot T (l.foldl (step r T) s) ≤ pot T s + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons c l ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih _ (step_inv r T s c hs)
    have h2 := step_pot r T s c hs
    omega

lemma pot_stateAt (r : Fin N → ℝ) (T t : ℕ) (p : Fin t → Option (Fin N)) :
    pot T (stateAt r T t p) ≤ t := by
  have h := pot_foldl r T (List.ofFn p) initState inv_init
  have h0 : pot T initState = 0 := by simp [pot, initState, epochStart, nSum]
  rw [h0, zero_add, List.length_ofFn] at h
  exact h

noncomputable def Xe (T τ : ℕ) : ℝ := 8 * (T : ℝ) * eps τ ^ 2

lemma eps_pos (τ : ℕ) : 0 < eps τ := by unfold eps; positivity

lemma eps_succ (τ : ℕ) : eps (τ + 1) = 2 / 3 * eps τ := by unfold eps; rw [pow_succ]; ring

lemma Xe_succ (T τ : ℕ) : Xe T (τ + 1) = 4 / 9 * Xe T τ := by
  unfold Xe; rw [eps_succ]; ring

lemma Xe_zero (T : ℕ) : Xe T 0 = 8 * T / 9 := by unfold Xe eps; ring

lemma nEpoch_ge (T τ : ℕ) :
    8 * ((eps τ)⁻¹ ^ 2 * Real.log (Xe T τ)) ≤ (nEpoch T τ : ℝ) := by
  unfold nEpoch innerLen Xe
  set x := (eps τ)⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * eps τ ^ 2)
  have h1 := Nat.le_ceil x
  have h2 : 8 * ⌈x⌉₊ ≤ max 1 (8 * ⌈x⌉₊) := le_max_right _ _
  calc 8 * x ≤ 8 * (⌈x⌉₊ : ℝ) := by linarith
    _ = ((8 * ⌈x⌉₊ : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast h2

lemma log_ge (x : ℝ) (hx : 9 / 4 ≤ x) : 5 / 9 ≤ Real.log x := by
  have hx0 : 0 < x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hx0
  have hi : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
  have : x⁻¹ ≤ 4 / 9 := by nlinarith [inv_pos.2 hx0]
  linarith

lemma big_of_lt (T τ : ℕ) (hX : 9 / 4 ≤ Xe T τ) (hn : (nEpoch T τ : ℝ) < T) :
    81 / 16 ≤ Xe T τ := by
  by_contra hlt
  rw [not_le] at hlt
  have he := eps_pos τ
  have hL := log_ge _ hX
  have hng := nEpoch_ge T τ
  have hq : (eps τ)⁻¹ ^ 2 * eps τ ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ he.ne']; simp
  have hq0 : 0 < (eps τ)⁻¹ ^ 2 := by positivity
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hm := mul_lt_mul_of_pos_left hlt hq0
  have he8 : (eps τ)⁻¹ ^ 2 * Xe T τ = 8 * T := by
    unfold Xe
    rw [show (eps τ)⁻¹ ^ 2 * (8 * (T : ℝ) * eps τ ^ 2) = 8 * T * ((eps τ)⁻¹ ^ 2 * eps τ ^ 2)
      by ring, hq, mul_one]
  have hqL := mul_le_mul_of_nonneg_left hL hq0.le
  linarith

lemma started_X (T : ℕ) (hT : 3 ≤ T) (τ : ℕ) (h : ∀ σ < τ, (nEpoch T σ : ℝ) < T) :
    9 / 4 ≤ Xe T τ := by
  induction τ with
  | zero =>
    rw [Xe_zero]
    have : (3 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  | succ τ ih =>
    have hτ := ih (fun σ hσ => h σ (by omega))
    have := big_of_lt T τ hτ (h τ (by omega))
    rw [Xe_succ]; linarith

/-- Every epoch reached before the horizon has `8Tε_τ² ≥ 9/4` (for `T ≥ 3`). -/
lemma reach_X (r : Fin N → ℝ) (T : ℕ) (hT : 3 ≤ T) (t : ℕ) (ht : t < T)
    (p : Fin t → Option (Fin N)) : 9 / 4 ≤ Xe T (stateAt r T t p).tau := by
  apply started_X T hT
  intro σ hσ
  have h1 := pot_stateAt r T t p
  have h2 : nEpoch T σ ≤ nSum T (stateAt r T t p).tau := by
    unfold nSum
    exact Finset.single_le_sum (f := fun σ => nEpoch T σ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 hσ)
  have : nEpoch T σ < T := by unfold pot at h1; omega
  exact_mod_cast this

/-- At the last inner iteration the confidence radius is at most `ε_τ / 2`. -/
lemma radius_le (T τ : ℕ) (hX : 9 / 4 ≤ Xe T τ) : radius T (nEpoch T τ) ≤ eps τ / 2 := by
  have he := eps_pos τ
  have hL := log_ge _ hX
  have hng := nEpoch_ge T τ
  have hq : (eps τ)⁻¹ ^ 2 * eps τ ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ he.ne']; simp
  have hq0 : 0 < (eps τ)⁻¹ ^ 2 := by positivity
  have hqL : 0 < (eps τ)⁻¹ ^ 2 * Real.log (Xe T τ) := mul_pos hq0 (by linarith)
  have hnpos : 0 < (nEpoch T τ : ℝ) := by linarith
  have hq59 := mul_le_mul_of_nonneg_left hL hq0.le
  have hnq : (eps τ)⁻¹ ^ 2 ≤ (nEpoch T τ : ℝ) := by linarith
  have he8 : (eps τ)⁻¹ ^ 2 * Xe T τ = 8 * T := by
    unfold Xe
    rw [show (eps τ)⁻¹ ^ 2 * (8 * (T : ℝ) * eps τ ^ 2) = 8 * T * ((eps τ)⁻¹ ^ 2 * eps τ ^ 2)
      by ring, hq, mul_one]
  have hX0 : 0 ≤ Xe T τ := by linarith
  have hT : 0 < (T : ℝ) := by
    have := mul_pos hq0 (by linarith : (0 : ℝ) < Xe T τ)
    linarith
  have hratio : 8 * (T : ℝ) / nEpoch T τ ≤ Xe T τ := by
    rw [div_le_iff₀ hnpos]
    have := mul_le_mul_of_nonneg_left hnq hX0
    linarith
  have hlog : Real.log (8 * T / nEpoch T τ) ≤ Real.log (Xe T τ) :=
    Real.log_le_log (div_pos (by linarith) hnpos) hratio
  have hk : (eps τ / 2) ^ 2 * (8 * ((eps τ)⁻¹ ^ 2 * Real.log (Xe T τ))) =
      2 * Real.log (Xe T τ) := by
    rw [show (eps τ / 2) ^ 2 * (8 * ((eps τ)⁻¹ ^ 2 * Real.log (Xe T τ))) =
      2 * ((eps τ)⁻¹ ^ 2 * eps τ ^ 2) * Real.log (Xe T τ) by ring, hq, mul_one]
  unfold radius
  rw [show eps τ / 2 = Real.sqrt ((eps τ / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hnpos]
  have := mul_le_mul_of_nonneg_left hng (sq_nonneg (eps τ / 2))
  linarith

/-! Child C1: finite Hoeffding lemma and the exponential supermartingale on `histProb`
(arbitrary predictable weights `w t p ∈ [0,1]`; stopping = weights that vanish after a crossing). -/

open MeasureTheory ProbabilityTheory in
lemma hoeff01 {n : ℕ} (w : Fin n → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (ℓ : Fin n → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i ∧ ℓ i ≤ 1) (s : ℝ) :
    ∑ i, w i * Real.exp (s * (ℓ i - ∑ j, w j * ℓ j)) ≤ Real.exp (s ^ 2 / 8) := by
  classical
  let μ : Measure (Fin n) := ∑ i, ENNReal.ofReal (w i) • Measure.dirac i
  have hμs : ∀ j, μ {j} = ENNReal.ofReal (w j) := by
    intro j
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator]
  have hμr : ∀ j, μ.real {j} = w j := by
    intro j
    rw [measureReal_def, hμs, ENNReal.toReal_ofReal (hw0 j)]
  have : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1, ENNReal.ofReal_one]
  have hint : ∀ f : Fin n → ℝ, ∫ x, f x ∂μ = ∑ i, w i * f i := by
    intro f
    rw [integral_fintype (Integrable.of_finite)]
    simp [hμr]
  have hH := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := ℓ) (a := 0) (b := 1)
    (Measurable.of_discrete).aemeasurable
    (Filter.Eventually.of_forall fun i => ⟨(hℓ i).1, (hℓ i).2⟩)
  have h2 := hH.mgf_le s
  have hc : ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    have : ‖(1:ℝ) - 0‖₊ = 1 := by ext; simp
    rw [this]; norm_num
  rw [hc] at h2
  simp only [mgf, hint] at h2
  convert h2 using 2
  push_cast; ring

lemma hoeff_opt (w : Option (Fin N) → ℝ) (hw0 : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    (ℓ : Option (Fin N) → ℝ) (hℓ : ∀ c, 0 ≤ ℓ c ∧ ℓ c ≤ 1) (s : ℝ) :
    ∑ c, w c * Real.exp (s * (ℓ c - ∑ d, w d * ℓ d)) ≤ Real.exp (s ^ 2 / 8) := by
  have hs : ∀ g : Option (Fin N) → ℝ, ∑ c, g c = ∑ i : Fin (N + 1), g (finSuccEquiv N i) :=
    fun g => (Fintype.sum_equiv (finSuccEquiv N) _ _ (fun _ => rfl)).symm
  have hw1' : ∑ i : Fin (N + 1), w (finSuccEquiv N i) = 1 := by rw [← hs]; exact hw1
  simp only [hs]
  exact hoeff01 (fun i => w (finSuccEquiv N i)) (fun i => hw0 _) hw1' _ (fun i => hℓ _) s

lemma mean_choiceRev (v r : Fin N → ℝ) (S : Finset (Fin N)) :
    ∑ c, choiceProb v S c * choiceRev r c = rev v r S := by
  rw [Fintype.sum_option]
  simp only [choiceProb, choiceRev, mul_zero, zero_add, rev_eq, ite_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter]
  rw [show (∑ j ∈ S, v j + 1) = 1 + ∑ j ∈ S, v j by ring, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma choiceRev_mem (r : Fin N → ℝ) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) :
    ∀ c, 0 ≤ choiceRev r c ∧ choiceRev r c ≤ 1
  | none => by simp [choiceRev]
  | some i => hr i

lemma pref_castSucc {β : Type*} (w : (t : ℕ) → (Fin t → Option (Fin N)) → β) {T : ℕ}
    (h : History N T) (c : Option (Fin N)) (t : Fin T) :
    w (t.castSucc).val (histPrefix (Fin.snoc h c : History N (T + 1)) t.castSucc) =
      w t.val (histPrefix h t) :=
  congrArg (w t.val) (histPrefix_snoc_castSucc h c t)

lemma pref_last {β : Type*} (w : (t : ℕ) → (Fin t → Option (Fin N)) → β) {T : ℕ}
    (h : History N T) (c : Option (Fin N)) :
    w (Fin.last T).val (histPrefix (Fin.snoc h c : History N (T + 1)) (Fin.last T)) = w T h :=
  congrArg (w T) (histPrefix_snoc_last h c)

/-- The weighted centred revenue sum `Σ_t w_t (r_{c_t} − R(S_t))`. -/
noncomputable def Zs (v r : Fin N → ℝ) (π : Policy N)
    (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) {T : ℕ} (h : History N T) : ℝ :=
  ∑ t : Fin T, w t.val (histPrefix h t) * (choiceRev r (h t) - rev v r (offered π h t))

/-- The weight total `Σ_t w_t`. -/
noncomputable def Ks (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) {T : ℕ} (h : History N T) : ℝ :=
  ∑ t : Fin T, w t.val (histPrefix h t)

lemma Zs_snoc (v r : Fin N → ℝ) (π : Policy N) (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ)
    {T : ℕ} (h : History N T) (c : Option (Fin N)) :
    Zs v r π w (Fin.snoc h c : History N (T + 1)) =
      Zs v r π w h + w T h * (choiceRev r c - rev v r (π T h)) := by
  unfold Zs
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [pref_castSucc w h c t, offered_snoc_castSucc π h c t, Fin.snoc_castSucc]
  · rw [pref_last w h c, offered_snoc_last π h c, Fin.snoc_last]

lemma Ks_snoc (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) {T : ℕ} (h : History N T)
    (c : Option (Fin N)) : Ks w (Fin.snoc h c : History N (T + 1)) = Ks w h + w T h := by
  unfold Ks
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [pref_castSucc w h c t]
  · rw [pref_last w h c]

/-- The exponential supermartingale: `E[exp(s Z_T − s²/8 K_T)] ≤ 1`. -/
lemma supermart (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (π : Policy N) (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ)
    (hw : ∀ t p, 0 ≤ w t p ∧ w t p ≤ 1) (s : ℝ) (T : ℕ) :
    ∑ h : History N T, histProb v π h *
      Real.exp (s * Zs v r π w h - s ^ 2 / 8 * Ks w h) ≤ 1 := by
  induction T with
  | zero => simp [histProb, Zs, Ks]
  | succ T ih =>
    rw [sum_hist_succ]
    refine le_trans (Finset.sum_le_sum fun h _ => ?_) ih
    simp only [histProb_snoc, Zs_snoc, Ks_snoc]
    have key := hoeff_opt (choiceProb v (π T h)) (choiceProb_nonneg v hv _)
      (choiceProb_sum v hv _) (choiceRev r) (choiceRev_mem r hr) (s * w T h)
    rw [mean_choiceRev] at key
    have hw2 : (s * w T h) ^ 2 / 8 ≤ s ^ 2 / 8 * w T h := by
      have := hw T h
      have h3 : w T h ^ 2 ≤ w T h := by nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg s)
      nlinarith
    have key2 := key.trans (Real.exp_le_exp.2 hw2)
    set A := s * Zs v r π w h - s ^ 2 / 8 * Ks w h
    set B := s ^ 2 / 8 * w T h
    have hP : 0 ≤ histProb v π h * Real.exp A * Real.exp (-B) :=
      mul_nonneg (mul_nonneg (histProb_nonneg v hv π h) (Real.exp_pos _).le) (Real.exp_pos _).le
    calc ∑ c, histProb v π h * choiceProb v (π T h) c *
          Real.exp (s * (Zs v r π w h + w T h * (choiceRev r c - rev v r (π T h))) -
            s ^ 2 / 8 * (Ks w h + w T h))
        = histProb v π h * Real.exp A * Real.exp (-B) *
            ∑ c, choiceProb v (π T h) c *
              Real.exp (s * w T h * (choiceRev r c - rev v r (π T h))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          rw [show s * (Zs v r π w h + w T h * (choiceRev r c - rev v r (π T h))) -
              s ^ 2 / 8 * (Ks w h + w T h) =
              A + -B + s * w T h * (choiceRev r c - rev v r (π T h)) by ring,
            Real.exp_add, Real.exp_add]
          ring
      _ ≤ histProb v π h * Real.exp A * Real.exp (-B) * Real.exp B :=
          mul_le_mul_of_nonneg_left key2 hP
      _ = histProb v π h * Real.exp A := by
          rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-! Child C2: one exponential step, a generic supermartingale bound, and Ville's maximal
inequality on `histProb` (stopping via `Hs`: frozen at `K` after the first crossing). -/

lemma exp_step (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (π : Policy N) (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ)
    (hw : ∀ t p, 0 ≤ w t p ∧ w t p ≤ 1) (s : ℝ) {T : ℕ} (h : History N T) :
    ∑ c, choiceProb v (π T h) c *
      Real.exp (s * Zs v r π w (Fin.snoc h c : History N (T + 1)) -
        s ^ 2 / 8 * Ks w (Fin.snoc h c : History N (T + 1))) ≤
      Real.exp (s * Zs v r π w h - s ^ 2 / 8 * Ks w h) := by
  simp only [Zs_snoc, Ks_snoc]
  have key := hoeff_opt (choiceProb v (π T h)) (choiceProb_nonneg v hv _)
    (choiceProb_sum v hv _) (choiceRev r) (choiceRev_mem r hr) (s * w T h)
  rw [mean_choiceRev] at key
  have hw2 : (s * w T h) ^ 2 / 8 ≤ s ^ 2 / 8 * w T h := by
    have := hw T h
    have h3 : w T h ^ 2 ≤ w T h := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg s)
    nlinarith
  have key2 := key.trans (Real.exp_le_exp.2 hw2)
  set A := s * Zs v r π w h - s ^ 2 / 8 * Ks w h
  set B := s ^ 2 / 8 * w T h
  have hP : 0 ≤ Real.exp A * Real.exp (-B) :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  calc ∑ c, choiceProb v (π T h) c *
        Real.exp (s * (Zs v r π w h + w T h * (choiceRev r c - rev v r (π T h))) -
          s ^ 2 / 8 * (Ks w h + w T h))
      = Real.exp A * Real.exp (-B) *
          ∑ c, choiceProb v (π T h) c *
            Real.exp (s * w T h * (choiceRev r c - rev v r (π T h))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [show s * (Zs v r π w h + w T h * (choiceRev r c - rev v r (π T h))) -
            s ^ 2 / 8 * (Ks w h + w T h) =
            A + -B + s * w T h * (choiceRev r c - rev v r (π T h)) by ring,
          Real.exp_add, Real.exp_add]
        ring
    _ ≤ Real.exp A * Real.exp (-B) * Real.exp B := mul_le_mul_of_nonneg_left key2 hP
    _ = Real.exp A := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

lemma gen_supermart (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N)
    (G : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ)
    (hstep : ∀ t (p : Fin t → Option (Fin N)),
      ∑ c, choiceProb v (π t p) c * G (t + 1) (Fin.snoc p c) ≤ G t p) (T : ℕ) :
    ∑ h : History N T, histProb v π h * G T h ≤ G 0 Fin.elim0 := by
  induction T with
  | zero =>
    rw [Fintype.sum_eq_single Fin.elim0 (fun h hh => absurd (funext fun i => i.elim0) hh)]
    simp [histProb]
  | succ T ih =>
    rw [sum_hist_succ]
    refine le_trans (Finset.sum_le_sum fun h _ => ?_) ih
    simp only [histProb_snoc]
    calc ∑ c, histProb v π h * choiceProb v (π T h) c * G (T + 1) (Fin.snoc h c)
        = histProb v π h * ∑ c, choiceProb v (π T h) c * G (T + 1) (Fin.snoc h c) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
      _ ≤ histProb v π h * G T h :=
          mul_le_mul_of_nonneg_left (hstep T h) (histProb_nonneg v hv π h)

/-- The prefix of length `u ≤ t` of a choice sequence. -/
def pre {t : ℕ} (p : Fin t → Option (Fin N)) (u : ℕ) (hu : u ≤ t) : Fin u → Option (Fin N) :=
  fun i => p (Fin.castLE hu i)

lemma pre_snoc {t : ℕ} (p : Fin t → Option (Fin N)) (c : Option (Fin N)) (u : ℕ)
    (hu' : u ≤ t + 1) (hu : u ≤ t) :
    pre (Fin.snoc p c : Fin (t + 1) → Option (Fin N)) u hu' = pre p u hu := by
  funext i
  simp only [pre]
  have : (Fin.castLE hu' i : Fin (t + 1)) = Fin.castSucc (Fin.castLE hu i) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma pre_self {t : ℕ} (p : Fin t → Option (Fin N)) (hu : t ≤ t) : pre p t hu = p := by
  funext i; rfl

/-- `p` has reached level `K` of `G` at some prefix of length `≤ t`. -/
def Crossed (G : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) (K : ℝ) {t : ℕ}
    (p : Fin t → Option (Fin N)) : Prop :=
  ∃ u, ∃ hu : u ≤ t, K ≤ G u (pre p u hu)

lemma crossed_snoc (G : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) (K : ℝ) {t : ℕ}
    (p : Fin t → Option (Fin N)) (c : Option (Fin N)) :
    Crossed G K (Fin.snoc p c : Fin (t + 1) → Option (Fin N)) ↔
      Crossed G K p ∨ K ≤ G (t + 1) (Fin.snoc p c) := by
  constructor
  · rintro ⟨u, hu, hK⟩
    rcases Nat.lt_or_ge u (t + 1) with h | h
    · left
      refine ⟨u, Nat.lt_succ_iff.1 h, ?_⟩
      rw [← pre_snoc p c u hu (Nat.lt_succ_iff.1 h)]
      exact hK
    · right
      obtain rfl : u = t + 1 := le_antisymm hu h
      rwa [pre_self] at hK
  · rintro (⟨u, hu, hK⟩ | hK)
    · exact ⟨u, hu.trans (Nat.le_succ t), by rw [pre_snoc p c u _ hu]; exact hK⟩
    · exact ⟨t + 1, le_rfl, by rw [pre_self]; exact hK⟩

/-- The process stopped (frozen at `K`) once it has crossed `K`. -/
noncomputable def Hs (G : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) (K : ℝ) (t : ℕ)
    (p : Fin t → Option (Fin N)) : ℝ := by
  classical
  exact if Crossed G K p then K else G t p

/-- Ville's maximal inequality: `K · ℙ(∃ u ≤ T, G_u ≥ K) ≤ G_0`. -/
lemma ville (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N)
    (G : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) (hG0 : ∀ t p, 0 ≤ G t p)
    (hstep : ∀ t (p : Fin t → Option (Fin N)),
      ∑ c, choiceProb v (π t p) c * G (t + 1) (Fin.snoc p c) ≤ G t p)
    (K : ℝ) (hK : 0 < K) (T : ℕ) :
    K * probT v π T (fun h => Crossed G K h) ≤ G 0 Fin.elim0 := by
  classical
  have hH0 : ∀ t p, 0 ≤ Hs G K t p := by
    intro t p
    unfold Hs
    split_ifs
    · exact hK.le
    · exact hG0 t p
  have hHstep : ∀ t (p : Fin t → Option (Fin N)),
      ∑ c, choiceProb v (π t p) c * Hs G K (t + 1) (Fin.snoc p c) ≤ Hs G K t p := by
    intro t p
    by_cases hc : Crossed G K p
    · have hK' : ∀ c, Hs G K (t + 1) (Fin.snoc p c) = K := fun c => by
        unfold Hs
        rw [if_pos ((crossed_snoc G K p c).2 (Or.inl hc))]
      simp only [hK', ← Finset.sum_mul, choiceProb_sum v hv, one_mul]
      unfold Hs
      rw [if_pos hc]
    · have hle : ∀ c, Hs G K (t + 1) (Fin.snoc p c) ≤ G (t + 1) (Fin.snoc p c) := fun c => by
        unfold Hs
        split_ifs with h1
        · rcases (crossed_snoc G K p c).1 h1 with h2 | h2
          · exact absurd h2 hc
          · exact h2
        · exact le_rfl
      calc _ ≤ ∑ c, choiceProb v (π t p) c * G (t + 1) (Fin.snoc p c) :=
            Finset.sum_le_sum fun c _ =>
              mul_le_mul_of_nonneg_left (hle c) (choiceProb_nonneg v hv _ c)
        _ ≤ G t p := hstep t p
        _ = Hs G K t p := by unfold Hs; rw [if_neg hc]
  have hsm := gen_supermart v hv π (Hs G K) hHstep T
  have h0 : Hs G K 0 Fin.elim0 ≤ G 0 Fin.elim0 := by
    unfold Hs
    split_ifs with h1
    · obtain ⟨u, hu, hKu⟩ := h1
      obtain rfl : u = 0 := Nat.le_zero.1 hu
      have : pre (Fin.elim0 : Fin 0 → Option (Fin N)) 0 hu = Fin.elim0 :=
        funext fun i => i.elim0
      rwa [this] at hKu
    · exact le_rfl
  unfold probT
  rw [Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum fun h _ => ?_) (hsm.trans h0)
  split_ifs with hc
  · unfold Hs
    rw [if_pos hc, mul_comm]
  · rw [mul_zero]
    exact mul_nonneg (histProb_nonneg v hv π h) (hH0 T h)

/-- The exponential process `exp(s Z_t − s²/8 K_t)`. -/
noncomputable def expG (v r : Fin N → ℝ) (π : Policy N)
    (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ) (s : ℝ) (t : ℕ)
    (p : Fin t → Option (Fin N)) : ℝ :=
  Real.exp (s * Zs v r π w (p : History N t) - s ^ 2 / 8 * Ks w (p : History N t))

/-- Anytime exponential tail: `ℙ(∃ u ≤ T, s Z_u − s²/8 K_u ≥ a) ≤ e^{−a}`. -/
lemma ville_exp (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (π : Policy N) (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ)
    (hw : ∀ t p, 0 ≤ w t p ∧ w t p ≤ 1) (s a : ℝ) (T : ℕ) :
    probT v π T (fun h => Crossed (expG v r π w s) (Real.exp a) h) ≤ Real.exp (-a) := by
  have hV := ville v hv π (expG v r π w s) (fun t p => (Real.exp_pos _).le)
    (fun t p => by unfold expG; exact exp_step v r hv hr π w hw s p) (Real.exp a)
    (Real.exp_pos a) T
  have h1 : expG v r π w s 0 Fin.elim0 = 1 := by simp [expG, Zs, Ks]
  rw [h1] at hV
  calc probT v π T (fun h => Crossed (expG v r π w s) (Real.exp a) h)
      = Real.exp (-a) * (Real.exp a *
          probT v π T (fun h => Crossed (expG v r π w s) (Real.exp a) h)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-a) * 1 := mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le
    _ = Real.exp (-a) := mul_one _

/-! ### C3: union bounds and dyadic peeling -/

lemma probT_mono (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E E' : History N T → Prop) (hE : ∀ h, E h → E' h) :
    probT v π T E ≤ probT v π T E' := by
  classical
  unfold probT
  apply Finset.sum_le_sum
  intro h _
  by_cases h1 : E h
  · rw [if_pos h1, if_pos (hE h h1)]
  · rw [if_neg h1]
    split_ifs
    · exact histProb_nonneg v hv π h
    · exact le_rfl

lemma probT_or (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (A B : History N T → Prop) :
    probT v π T (fun h => A h ∨ B h) ≤ probT v π T A + probT v π T B := by
  classical
  unfold probT
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h _
  have := histProb_nonneg v hv π h
  split_ifs <;> simp_all

lemma probT_biUnion (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (s : Finset ℕ) (E : ℕ → History N T → Prop) :
    probT v π T (fun h => ∃ k ∈ s, E k h) ≤ ∑ k ∈ s, probT v π T (E k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [probT]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk]
    calc probT v π T (fun h => ∃ j ∈ insert k s, E j h)
        ≤ probT v π T (fun h => E k h ∨ ∃ j ∈ s, E j h) := by
          apply probT_mono v hv π T
          intro h hh
          obtain ⟨j, hj, hE⟩ := hh
          rcases Finset.mem_insert.1 hj with rfl | hj'
          · exact Or.inl hE
          · exact Or.inr ⟨j, hj', hE⟩
      _ ≤ probT v π T (E k) + probT v π T (fun h => ∃ j ∈ s, E j h) := probT_or v hv π T _ _
      _ ≤ _ := by linarith

/-- One block: `ℙ(∃ u, K_u ≤ k ∧ σ Z_u ≥ λ) ≤ exp(−2λ²/k)`. -/
lemma block (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (π : Policy N) (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ)
    (hw : ∀ t p, 0 ≤ w t p ∧ w t p ≤ 1) (T : ℕ) (σ : ℝ) (hσ : σ * σ = 1)
    (lam kk : ℝ) (hlam : 0 ≤ lam) (hk : 0 < kk) :
    probT v π T (fun h => ∃ u, ∃ hu : u ≤ T, Ks w (pre h u hu) ≤ kk ∧
        lam ≤ σ * Zs v r π w (pre h u hu)) ≤ Real.exp (-(2 * lam ^ 2 / kk)) := by
  refine le_trans (probT_mono v hv π T _ _ ?_)
    (ville_exp v r hv hr π w hw (4 * σ * lam / kk) (2 * lam ^ 2 / kk) T)
  rintro h ⟨u, hu, hK, hZ⟩
  refine ⟨u, hu, ?_⟩
  unfold expG
  apply Real.exp_le_exp.2
  generalize Zs v r π w (pre h u hu) = Z at hZ ⊢
  generalize Ks w (pre h u hu) = K at hK ⊢
  have hq : 0 < 1 / kk := by positivity
  have hqK : K * (1 / kk) ≤ 1 := by
    rw [mul_one_div]; exact (div_le_one hk).2 hK
  have e1 : 4 * σ * lam / kk * Z = 4 * lam * (1 / kk) * (σ * Z) := by ring
  have e2 : (4 * σ * lam / kk) ^ 2 / 8 * K = 2 * lam ^ 2 * (1 / kk) * (K * (1 / kk)) * (σ * σ) := by
    ring
  have e3 : 2 * lam ^ 2 / kk = 2 * lam ^ 2 * (1 / kk) := by ring
  rw [e1, e2, e3, hσ]
  have h1 := mul_le_mul_of_nonneg_left hZ (by positivity : (0:ℝ) ≤ 4 * lam * (1 / kk))
  have h2 := mul_le_mul_of_nonneg_left hqK (by positivity : (0:ℝ) ≤ 2 * lam ^ 2 * (1 / kk))
  nlinarith

lemma dyadic (x : ℝ) (h1 : 1 ≤ x) : ∃ k : ℕ, (2:ℝ) ^ k ≤ x ∧ x ≤ 2 ^ (k + 1) := by
  set m := ⌊x⌋₊ with hm
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast h1)
  refine ⟨Nat.log 2 m, ?_, ?_⟩
  · have h := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    calc (2:ℝ) ^ Nat.log 2 m = ((2 ^ Nat.log 2 m : ℕ) : ℝ) := by norm_cast
      _ ≤ m := by exact_mod_cast h
      _ ≤ x := Nat.floor_le (by linarith)
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    have h' : m + 1 ≤ 2 ^ (Nat.log 2 m + 1) := h
    have hx := Nat.lt_floor_add_one x
    calc x ≤ (m : ℝ) + 1 := hx.le
      _ = ((m + 1 : ℕ) : ℝ) := by norm_cast
      _ ≤ ((2 ^ (Nat.log 2 m + 1) : ℕ) : ℝ) := by exact_mod_cast h'
      _ = 2 ^ (Nat.log 2 m + 1) := by norm_cast

lemma thr_le (x g c : ℝ) (hg : 0 ≤ g) (hc : 0 < c) (k : ℕ) (hk1 : (2:ℝ) ^ k ≤ x)
    (hk2 : x ≤ 2 ^ (k + 1)) :
    2 ^ k * g + Real.sqrt (2 ^ k * max 0 (Real.log (c / 2 ^ (k + 1)))) ≤
      x * g + Real.sqrt (2 * x * Real.log (c / x)) := by
  have hx : 0 < x := lt_of_lt_of_le (by positivity) hk1
  apply add_le_add (mul_le_mul_of_nonneg_right hk1 hg)
  rcases le_total (Real.log (c / 2 ^ (k + 1))) 0 with hL | hL
  · rw [max_eq_left hL, mul_zero, Real.sqrt_zero]; exact Real.sqrt_nonneg _
  · rw [max_eq_right hL]
    apply Real.sqrt_le_sqrt
    have hdiv : c / 2 ^ (k + 1) ≤ c / x := div_le_div_of_nonneg_left hc.le hx hk2
    have hlog : Real.log (c / 2 ^ (k + 1)) ≤ Real.log (c / x) :=
      Real.log_le_log (by positivity) hdiv
    have h2x : (2:ℝ) ^ k ≤ 2 * x := by linarith
    calc 2 ^ k * Real.log (c / 2 ^ (k + 1)) ≤ (2 * x) * Real.log (c / 2 ^ (k + 1)) :=
          mul_le_mul_of_nonneg_right h2x hL
      _ ≤ (2 * x) * Real.log (c / x) := mul_le_mul_of_nonneg_left hlog (by positivity)

lemma block_bound (g c : ℝ) (hc : 0 < c) (hg : 0 ≤ g) (k : ℕ) :
    Real.exp (-(2 * (2 ^ k * g + Real.sqrt (2 ^ k * max 0 (Real.log (c / 2 ^ (k + 1))))) ^ 2 /
        2 ^ (k + 1))) ≤ 2 ^ (k + 1) / c * Real.exp (-(2 ^ k * g ^ 2)) := by
  set M := max 0 (Real.log (c / 2 ^ (k + 1))) with hM
  have hM0 : 0 ≤ M := le_max_left _ _
  have hML : Real.log (c / 2 ^ (k + 1)) ≤ M := le_max_right _ _
  have hp : (0:ℝ) < 2 ^ k := by positivity
  have hs : Real.sqrt (2 ^ k * M) ^ 2 = 2 ^ k * M := Real.sq_sqrt (by positivity)
  have hsq0 : 0 ≤ Real.sqrt (2 ^ k * M) := Real.sqrt_nonneg _
  have key : 2 ^ k * g ^ 2 + M ≤
      2 * (2 ^ k * g + Real.sqrt (2 ^ k * M)) ^ 2 / 2 ^ (k + 1) := by
    have h2 : (2:ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
    rw [le_div_iff₀ (by positivity), h2]
    nlinarith [mul_nonneg (mul_nonneg hp.le hg) hsq0]
  calc _ ≤ Real.exp (-(2 ^ k * g ^ 2 + M)) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-M) * Real.exp (-(2 ^ k * g ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-Real.log (c / 2 ^ (k + 1))) * Real.exp (-(2 ^ k * g ^ 2)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
    _ = 2 ^ (k + 1) / c * Real.exp (-(2 ^ k * g ^ 2)) := by
        rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]

/-- **C3 peeling**: `ℙ(∃ u: 1 ≤ K_u < 2^{K+1}, σ Z_u ≥ K_u g + √(2 K_u log(c/K_u)))`
`≤ Σ_{k≤K} 2^{k+1}/c · exp(−2^k g²)`. -/
lemma peel (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (π : Policy N) (w : (t : ℕ) → (Fin t → Option (Fin N)) → ℝ)
    (hw : ∀ t p, 0 ≤ w t p ∧ w t p ≤ 1) (T : ℕ) (σ : ℝ) (hσ : σ * σ = 1)
    (g c : ℝ) (hg : 0 ≤ g) (hc : 0 < c) (K : ℕ) :
    probT v π T (fun h => ∃ u, ∃ hu : u ≤ T, 1 ≤ Ks w (pre h u hu) ∧
        Ks w (pre h u hu) < 2 ^ (K + 1) ∧
        Ks w (pre h u hu) * g + Real.sqrt (2 * Ks w (pre h u hu) *
          Real.log (c / Ks w (pre h u hu))) ≤ σ * Zs v r π w (pre h u hu)) ≤
      ∑ k ∈ Finset.range (K + 1), 2 ^ (k + 1) / c * Real.exp (-(2 ^ k * g ^ 2)) := by
  classical
  have hE : ∀ h : History N T, (∃ u, ∃ hu : u ≤ T, 1 ≤ Ks w (pre h u hu) ∧
        Ks w (pre h u hu) < 2 ^ (K + 1) ∧
        Ks w (pre h u hu) * g + Real.sqrt (2 * Ks w (pre h u hu) *
          Real.log (c / Ks w (pre h u hu))) ≤ σ * Zs v r π w (pre h u hu)) →
      ∃ k ∈ Finset.range (K + 1), ∃ u, ∃ hu : u ≤ T, Ks w (pre h u hu) ≤ 2 ^ (k + 1) ∧
        2 ^ k * g + Real.sqrt (2 ^ k * max 0 (Real.log (c / 2 ^ (k + 1)))) ≤
          σ * Zs v r π w (pre h u hu) := by
    rintro h ⟨u, hu, h1, h2, h3⟩
    obtain ⟨k, hk1, hk2⟩ := dyadic _ h1
    refine ⟨k, Finset.mem_range.2 ?_, u, hu, hk2, (thr_le _ g c hg hc k hk1 hk2).trans h3⟩
    by_contra hcon
    have : (2:ℝ) ^ (K + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  refine (probT_mono v hv π T _ _ hE).trans ((probT_biUnion v hv π T _
    (fun k h => ∃ u, ∃ hu : u ≤ T, Ks w (pre h u hu) ≤ 2 ^ (k + 1) ∧
        2 ^ k * g + Real.sqrt (2 ^ k * max 0 (Real.log (c / 2 ^ (k + 1)))) ≤
          σ * Zs v r π w (pre h u hu))).trans ?_)
  apply Finset.sum_le_sum
  intro k _
  exact (block v r hv hr π w hw T σ hσ _ _
    (add_nonneg (mul_nonneg (by positivity) hg) (Real.sqrt_nonneg _)) (by positivity)).trans
    (block_bound g c hc hg k)

lemma geom_sum_le (c : ℝ) (hc : 0 < c) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), 2 ^ (k + 1) / c * Real.exp (-(2 ^ k * (0:ℝ) ^ 2)) ≤
      2 ^ (K + 2) / c := by
  have hs : ∀ K : ℕ, ∑ k ∈ Finset.range (K + 1), (2:ℝ) ^ (k + 1) = 2 ^ (K + 2) - 2 := by
    intro K
    induction K with
    | zero => norm_num
    | succ K ih => rw [Finset.sum_range_succ, ih]; ring
  have h0 : ∀ k : ℕ, (2:ℝ) ^ (k + 1) / c * Real.exp (-(2 ^ k * (0:ℝ) ^ 2)) = 2 ^ (k + 1) / c := by
    intro k; simp
  simp only [h0]
  rw [← Finset.sum_div, hs K]
  exact (div_le_div_iff_of_pos_right hc).2 (by linarith)

lemma gap_term (c g : ℝ) (hc : 0 < c) (hg : 0 < g) (k : ℕ) :
    2 ^ (k + 1) / c * Real.exp (-(2 ^ k * g ^ 2)) ≤
      4 / (c * g ^ 2) * (Real.exp (-(2 ^ k * g ^ 2) / 2) - Real.exp (-(2 ^ k * g ^ 2))) := by
  have hc0 := hc.ne'
  have hg0 := hg.ne'
  have hexp : Real.exp (-(2 ^ k * g ^ 2) / 2) =
      Real.exp (-(2 ^ k * g ^ 2)) * Real.exp ((2 ^ k * g ^ 2) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle : (2 ^ k * g ^ 2) / 2 + 1 ≤ Real.exp ((2 ^ k * g ^ 2) / 2) := Real.add_one_le_exp _
  have he : 0 < Real.exp (-(2 ^ k * g ^ 2)) := Real.exp_pos _
  have key : (2 ^ k * g ^ 2) * Real.exp (-(2 ^ k * g ^ 2)) ≤
      2 * (Real.exp (-(2 ^ k * g ^ 2)) * Real.exp ((2 ^ k * g ^ 2) / 2) -
        Real.exp (-(2 ^ k * g ^ 2))) := by
    nlinarith [mul_le_mul_of_nonneg_left hle he.le]
  calc 2 ^ (k + 1) / c * Real.exp (-(2 ^ k * g ^ 2))
      = 2 / (c * g ^ 2) * ((2 ^ k * g ^ 2) * Real.exp (-(2 ^ k * g ^ 2))) := by
        rw [pow_succ]; field_simp
    _ ≤ 2 / (c * g ^ 2) * (2 * (Real.exp (-(2 ^ k * g ^ 2)) * Real.exp ((2 ^ k * g ^ 2) / 2) -
        Real.exp (-(2 ^ k * g ^ 2)))) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := by rw [hexp]; ring

lemma tele (g : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (Real.exp (-(2 ^ k * g ^ 2) / 2) - Real.exp (-(2 ^ k * g ^ 2))) =
      Real.exp (-(g ^ 2) / 2) - Real.exp (-(2 ^ K * g ^ 2)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have : -(2 ^ (K + 1) * g ^ 2) / 2 = -(2 ^ K * g ^ 2) := by rw [pow_succ]; ring
    rw [this]; ring

lemma gap_sum (c g : ℝ) (hc : 0 < c) (hg : 0 < g) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), 2 ^ (k + 1) / c * Real.exp (-(2 ^ k * g ^ 2)) ≤
      4 / (c * g ^ 2) := by
  calc _ ≤ ∑ k ∈ Finset.range (K + 1), 4 / (c * g ^ 2) *
        (Real.exp (-(2 ^ k * g ^ 2) / 2) - Real.exp (-(2 ^ k * g ^ 2))) :=
        Finset.sum_le_sum (fun k _ => gap_term c g hc hg k)
    _ = 4 / (c * g ^ 2) * (Real.exp (-(g ^ 2) / 2) - Real.exp (-(2 ^ K * g ^ 2))) := by
        rw [← Finset.mul_sum, tele]
    _ ≤ 4 / (c * g ^ 2) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 : Real.exp (-(g ^ 2) / 2) ≤ 1 :=
          Real.exp_le_one_iff.2 (by have := sq_nonneg g; linarith)
        linarith [Real.exp_pos (-(2 ^ K * g ^ 2))]
    _ = _ := mul_one _

/-! ### P0: the epoch-σ exploration accounting invariant -/

lemma stateAt_snoc (r : Fin N → ℝ) (T t : ℕ) (p : Fin t → Option (Fin N)) (c : Option (Fin N)) :
    stateAt r T (t + 1) (Fin.snoc p c : Fin (t + 1) → Option (Fin N)) =
      step r T (stateAt r T t p) c := by
  unfold stateAt
  rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma step_cases (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N)) :
    (s.exploreNow ∧ step r T s c =
      { s with rho := s.rho + choiceRev r c,
               lo := (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - radius T (s.k + 1),
               up := (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) + radius T (s.k + 1),
               explored := true }) ∨
    (¬ s.exploreNow ∧ innerLen T (s.y - s.x) ≤ s.k + 1 ∧
      (step r T s c = epochStart (s.tau + 1) s.a s.y ∨
       step r T s c = epochStart (s.tau + 1) s.x s.b)) ∨
    (¬ s.exploreNow ∧ ¬ innerLen T (s.y - s.x) ≤ s.k + 1 ∧
      step r T s c = { s with k := s.k + 1, explored := false }) := by
  classical
  unfold step
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨h1, h2, Or.inr rfl⟩)
  · exact Or.inr (Or.inr ⟨h1, h2, rfl⟩)

lemma step_tau (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N)) :
    (step r T s c).tau = s.tau ∨ ∃ a b, step r T s c = epochStart (s.tau + 1) a b := by
  rcases step_cases r T s c with ⟨_, h⟩ | ⟨_, _, h | h⟩ | ⟨_, _, h⟩
  · left; rw [h]
  · right; exact ⟨_, _, h⟩
  · right; exact ⟨_, _, h⟩
  · left; rw [h]

lemma innerLen_pos (T : ℕ) (e : ℝ) : 0 < innerLen T e :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Weight of the explorations of epoch `σ`. -/
noncomputable def wS (σ : ℕ) (s : AlgState) : ℝ := by
  classical
  exact if s.tau = σ ∧ s.exploreNow then 1 else 0

noncomputable def wE (r : Fin N → ℝ) (T σ : ℕ) (t : ℕ) (p : Fin t → Option (Fin N)) : ℝ :=
  wS σ (stateAt r T t p)

lemma wE_mem (r : Fin N → ℝ) (T σ : ℕ) (t : ℕ) (p : Fin t → Option (Fin N)) :
    0 ≤ wE r T σ t p ∧ wE r T σ t p ≤ 1 := by
  unfold wE wS; split_ifs <;> norm_num

/-- The accounting invariant of epoch `σ` (`Z`, `K` = centred exploration sum and count). -/
abbrev J (v r : Fin N → ℝ) (T σ : ℕ) (s : AlgState) (Z K : ℝ) : Prop :=
  (s.tau < σ → Z = 0 ∧ K = 0) ∧
  (s.tau = σ → ∃ m : ℕ, K = m ∧ s.rho = Z + m * F v r s.y ∧
    (m = 0 → s.lo = 0 ∧ s.up = 1) ∧
    (0 < m → s.lo = s.rho / m - radius T m ∧ s.up = s.rho / m + radius T m) ∧
    (s.explored = true → s.k + 1 = m) ∧
    (s.explored = false → s.lo ≤ s.y → s.y ≤ s.up → s.k = m) ∧
    s.k < innerLen T (s.y - s.x) ∧ m ≤ s.k + 1)

lemma J_start (v r : Fin N → ℝ) (T σ τ : ℕ) (a b : ℝ) :
    J v r T σ (epochStart τ a b) 0 0 := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨0, by simp, by simp [epochStart], fun _ => ⟨rfl, rfl⟩,
    fun h => absurd h (lt_irrefl 0), fun h => ?_, fun _ _ _ => rfl, innerLen_pos _ _,
    Nat.zero_le _⟩⟩
  change false = true at h
  exact absurd h (by decide)

lemma J_step (v r : Fin N → ℝ) (T σ : ℕ) (s : AlgState) (c : Option (Fin N)) (Z K : ℝ)
    (hJ : J v r T σ s Z K) :
    J v r T σ (step r T s c)
      (Z + wS σ s * (choiceRev r c - rev v r (offerOf r s))) (K + wS σ s) := by
  classical
  obtain ⟨hlt, heq⟩ := hJ
  by_cases hτ : s.tau = σ
  · obtain ⟨m, hK, hrho, h0, hpos, hex, hnex, hk, hmk⟩ := heq hτ
    rcases step_cases r T s c with ⟨hE, hst⟩ | ⟨hE, hend, hst | hst⟩ | ⟨hE, hend, hst⟩
    · have hw : wS σ s = 1 := by unfold wS; rw [if_pos ⟨hτ, hE⟩]
      have hoff : offerOf r s = levelSet r s.y := by unfold offerOf; rw [if_pos hE]
      have hkm : s.k = m := hnex hE.1 hE.2.1 hE.2.2
      rw [hst, hw, hoff]
      refine ⟨fun h => ?_, fun _ => ⟨m + 1, ?_, ?_, fun h => absurd h (by omega), fun _ => ?_,
        fun _ => ?_, fun h => ?_, ?_, ?_⟩⟩
      · change s.tau < σ at h; omega
      · rw [hK]; push_cast; ring
      · show s.rho + choiceRev r c =
          Z + 1 * (choiceRev r c - rev v r (levelSet r s.y)) + ((m + 1 : ℕ) : ℝ) * F v r s.y
        rw [hrho]; unfold F; push_cast; ring
      · show (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) - radius T (s.k + 1) =
            (s.rho + choiceRev r c) / ((m + 1 : ℕ) : ℝ) - radius T (m + 1) ∧
          (s.rho + choiceRev r c) / ((s.k + 1 : ℕ) : ℝ) + radius T (s.k + 1) =
            (s.rho + choiceRev r c) / ((m + 1 : ℕ) : ℝ) + radius T (m + 1)
        rw [hkm]; exact ⟨rfl, rfl⟩
      · show s.k + 1 = m + 1
        omega
      · change true = false at h
        exact absurd h (by decide)
      · show s.k < innerLen T (s.y - s.x)
        exact hk
      · show m + 1 ≤ s.k + 1
        omega
    · rw [hst]
      exact ⟨fun h => absurd h (by change ¬ s.tau + 1 < σ; omega),
        fun h => absurd h (by change ¬ s.tau + 1 = σ; omega)⟩
    · rw [hst]
      exact ⟨fun h => absurd h (by change ¬ s.tau + 1 < σ; omega),
        fun h => absurd h (by change ¬ s.tau + 1 = σ; omega)⟩
    · have hw : wS σ s = 0 := by unfold wS; rw [if_neg (fun h => hE h.2)]
      rw [hst, hw]
      refine ⟨fun h => ?_, fun _ => ⟨m, ?_, ?_, fun h => h0 h, fun h => hpos h, fun h => ?_,
        fun _ hl hu => ?_, ?_, ?_⟩⟩
      · change s.tau < σ at h; omega
      · rw [hK]; ring
      · show s.rho = Z + 0 * (choiceRev r c - rev v r (offerOf r s)) + (m : ℝ) * F v r s.y
        rw [hrho]; ring
      · change false = true at h
        exact absurd h (by decide)
      · change s.lo ≤ s.y at hl
        change s.y ≤ s.up at hu
        show s.k + 1 = m
        cases hx : s.explored
        · exact absurd ⟨hx, hl, hu⟩ hE
        · exact hex hx
      · show s.k + 1 < innerLen T (s.y - s.x)
        omega
      · show m ≤ s.k + 1 + 1
        omega
  · have hw : wS σ s = 0 := by unfold wS; rw [if_neg (fun h => hτ h.1)]
    rw [hw, zero_mul, add_zero, add_zero]
    have hst := step_tau r T s c
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hst with h' | ⟨a, b, h'⟩
      · exact hlt (by omega)
      · rw [h'] at h; change s.tau + 1 < σ at h; exact hlt (by omega)
    · rcases hst with h' | ⟨a, b, h'⟩
      · exact absurd (h'.symm.trans h) hτ
      · have h2 : s.tau + 1 = σ := by rw [h'] at h; exact h
        obtain ⟨hZ, hK⟩ := hlt (by omega)
        rw [hZ, hK, h']
        rw [h'] at h
        exact (J_start v r T σ _ a b).2 h

lemma J_stateAt (v r : Fin N → ℝ) (T σ : ℕ) : ∀ (t : ℕ) (p : Fin t → Option (Fin N)),
    J v r T σ (stateAt r T t p) (Zs v r (adaptivePolicy r T) (wE r T σ) (p : History N t))
      (Ks (wE r T σ) (p : History N t)) := by
  intro t
  induction t with
  | zero =>
    intro p
    have h1 : stateAt r T 0 p = initState := by simp [stateAt]
    have h2 : Zs v r (adaptivePolicy r T) (wE r T σ) (p : History N 0) = 0 := by simp [Zs]
    have h3 : Ks (wE r T σ) (p : History N 0) = 0 := by simp [Ks]
    rw [h1, h2, h3]
    exact J_start v r T σ 0 0 1
  | succ t ih =>
    intro p
    obtain ⟨q, c, rfl⟩ : ∃ q c, p = Fin.snoc q c :=
      ⟨Fin.init p, p (Fin.last t), (Fin.snoc_init_self p).symm⟩
    rw [stateAt_snoc, Zs_snoc, Ks_snoc]
    exact J_step v r T σ _ c _ _ (ih q)

/-! ### P1: a wrong `b`-move is a lower-tail peeling event -/

lemma m_rad (T m : ℕ) (hm : 0 < m) :
    (m : ℝ) * radius T m = Real.sqrt (2 * (m : ℝ) * Real.log (8 * (T : ℝ) / (m : ℝ))) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  unfold radius
  rw [show ∀ A : ℝ, (m : ℝ) * Real.sqrt A = Real.sqrt ((m : ℝ) ^ 2 * A) from fun A => by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hm'.le]]
  congr 1
  first
  | (field_simp; ring)
  | field_simp

lemma WB_peel (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (T σ : ℕ) (u : ℕ)
    (p : Fin u → Option (Fin N))
    (hτ : (stateAt r T u p).tau = σ) (hup : (stateAt r T u p).up < (stateAt r T u p).y)
    (hy : (stateAt r T u p).y ≤ optRev v r) :
    1 ≤ Ks (wE r T σ) (p : History N u) ∧
    Ks (wE r T σ) (p : History N u) < 2 ^ (Nat.log 2 (nEpoch T σ) + 1) ∧
    Ks (wE r T σ) (p : History N u) * 0 + Real.sqrt (2 * Ks (wE r T σ) (p : History N u) *
      Real.log (8 * (T : ℝ) / Ks (wE r T σ) (p : History N u))) ≤
      (-1) * Zs v r (adaptivePolicy r T) (wE r T σ) (p : History N u) := by
  obtain ⟨-, hJ⟩ := J_stateAt v r T σ u p
  obtain ⟨m, hK, hrho, h0, hpos, -, -, hk, hmk⟩ := hJ hτ
  generalize hZ : Zs v r (adaptivePolicy r T) (wE r T σ) (p : History N u) = Z at hrho ⊢
  have hI := stateAt_inv r T u p
  generalize stateAt r T u p = s at hτ hup hy hrho h0 hpos hk hmk hI
  obtain ⟨hI1, hI2, hI3⟩ := hI
  have hpow : (0:ℝ) < (2/3) ^ s.tau := by positivity
  have hy1 : s.y ≤ 1 := by unfold AlgState.y; linarith
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · obtain ⟨-, hu1⟩ := h0 h; linarith
    · exact h
  have hFy : s.y ≤ F v r s.y := le_F_of_le v r hv _ hy
  obtain ⟨-, hupm⟩ := hpos hm
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn : m ≤ nEpoch T σ := by
    have := yx_eq s ⟨hI1, hI2, hI3⟩
    rw [this, hτ] at hk
    unfold nEpoch; omega
  rw [hK]
  refine ⟨by exact_mod_cast hm, ?_, ?_⟩
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (nEpoch T σ)
    have : m < 2 ^ (Nat.log 2 (nEpoch T σ) + 1) := lt_of_le_of_lt hn h1
    exact_mod_cast this
  · rw [mul_zero, zero_add, ← m_rad T m hm]
    rw [hupm, hrho] at hup
    have hq : (Z + m * F v r s.y) / m * m = Z + m * F v r s.y := div_mul_cancel₀ _ hm'.ne'
    have h3 := mul_lt_mul_of_pos_left hup hm'
    have h4 := mul_le_mul_of_nonneg_left hFy hm'.le
    nlinarith

/-- `ℙ(wrong b-move in epoch σ) ≤ n_σ / (2T)`. -/
lemma prob_WB (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (T σ : ℕ) (hT : 0 < T) :
    probT v (adaptivePolicy r T) T (fun h => ∃ u, ∃ hu : u ≤ T,
      (stateAt r T u (pre h u hu)).tau = σ ∧
      (stateAt r T u (pre h u hu)).up < (stateAt r T u (pre h u hu)).y ∧
      (stateAt r T u (pre h u hu)).y ≤ optRev v r) ≤ (nEpoch T σ : ℝ) / (2 * T) := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hc : (0:ℝ) < 8 * T := by positivity
  refine (probT_mono v hv _ T _ _ ?_).trans ((peel v r hv hr (adaptivePolicy r T) (wE r T σ)
    (wE_mem r T σ) T (-1) (by norm_num) 0 (8 * T) le_rfl hc (Nat.log 2 (nEpoch T σ))).trans
    ((geom_sum_le _ hc _).trans ?_))
  · rintro h ⟨u, hu, h1, h2, h3⟩
    exact ⟨u, hu, WB_peel v r hv T σ u _ h1 h2 h3⟩
  · have hn0 : nEpoch T σ ≠ 0 := (innerLen_pos _ _).ne'
    have h1 := Nat.pow_log_le_self 2 hn0
    have h2 : (2:ℝ) ^ Nat.log 2 (nEpoch T σ) ≤ nEpoch T σ := by exact_mod_cast h1
    rw [pow_add, div_le_div_iff₀ hc (by positivity)]
    nlinarith

/-! ### P2: a wrong `a`-move is an upper-tail peeling event with gap `γ` -/

lemma WA_peel (v r : Fin N → ℝ) (T σ : ℕ) (hX : 9 / 4 ≤ Xe T σ) (γ : ℝ) (u : ℕ)
    (p : Fin u → Option (Fin N))
    (hτ : (stateAt r T u p).tau = σ) (hE : ¬ (stateAt r T u p).exploreNow)
    (hend : innerLen T ((stateAt r T u p).y - (stateAt r T u p).x) ≤ (stateAt r T u p).k + 1)
    (hup : ¬ (stateAt r T u p).up < (stateAt r T u p).y)
    (hγ : γ + eps σ ≤ (stateAt r T u p).y - F v r (stateAt r T u p).y) (hγ0 : 0 ≤ γ) :
    1 ≤ Ks (wE r T σ) (p : History N u) ∧
    Ks (wE r T σ) (p : History N u) < 2 ^ (Nat.log 2 (nEpoch T σ) + 1) ∧
    Ks (wE r T σ) (p : History N u) * γ + Real.sqrt (2 * Ks (wE r T σ) (p : History N u) *
      Real.log (8 * (T : ℝ) / Ks (wE r T σ) (p : History N u))) ≤
      1 * Zs v r (adaptivePolicy r T) (wE r T σ) (p : History N u) := by
  obtain ⟨-, hJ⟩ := J_stateAt v r T σ u p
  obtain ⟨m, hK, hrho, h0, hpos, hex, hnex, hk, hmk⟩ := hJ hτ
  generalize hZ : Zs v r (adaptivePolicy r T) (wE r T σ) (p : History N u) = Z at hrho ⊢
  have hI := stateAt_inv r T u p
  generalize stateAt r T u p = s at hτ hE hend hup hγ hrho h0 hpos hex hnex hk hmk hI
  obtain ⟨hI1, hI2, hI3⟩ := hI
  have hpow : (0:ℝ) < (2/3) ^ s.tau := by positivity
  have hy0 : 0 ≤ s.y := by unfold AlgState.y; linarith
  have hyx := yx_eq s ⟨hI1, hI2, hI3⟩
  rw [hyx, hτ] at hk hend
  push_neg at hup
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · obtain ⟨hl0, -⟩ := h0 h
      exfalso
      cases hx : s.explored
      · exact hE ⟨hx, by rw [hl0]; exact hy0, hup⟩
      · have := hex hx; omega
    · exact h
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hn : m ≤ nEpoch T σ := by unfold nEpoch; omega
  obtain ⟨hlo, hupm⟩ := hpos hm
  rw [hK]
  refine ⟨by exact_mod_cast hm, ?_, ?_⟩
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (nEpoch T σ)
    have : m < 2 ^ (Nat.log 2 (nEpoch T σ) + 1) := lt_of_le_of_lt hn h1
    exact_mod_cast this
  rw [← m_rad T m hm, one_mul]
  have hq : (Z + m * F v r s.y) / m * m = Z + m * F v r s.y := div_mul_cancel₀ _ hm'.ne'
  have heps := (eps_pos σ).le
  cases hx : s.explored
  · have hlo' : s.y < s.lo := by
      by_contra hc
      push_neg at hc
      exact hE ⟨hx, hc, hup⟩
    rw [hlo, hrho] at hlo'
    have h3 := mul_lt_mul_of_pos_left hlo' hm'
    have h4 := mul_le_mul_of_nonneg_left hγ hm'.le
    nlinarith [mul_nonneg hm'.le heps]
  · have hmn : m = nEpoch T σ := by have := hex hx; unfold nEpoch; omega
    have hrad := radius_le T σ hX
    rw [← hmn] at hrad
    rw [hupm, hrho] at hup
    have h3 := mul_le_mul_of_nonneg_left hup hm'.le
    have h4 := mul_le_mul_of_nonneg_left hγ hm'.le
    have h5 := mul_le_mul_of_nonneg_left hrad hm'.le
    nlinarith

/-- `ℙ(epoch σ ends with an a-move although y_σ − F(y_σ) ≥ γ + ε_σ) ≤ 1/(2Tγ²)`. -/
lemma prob_WA (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (T σ : ℕ) (hT : 0 < T) (hX : 9 / 4 ≤ Xe T σ) (γ : ℝ) (hγ : 0 < γ) :
    probT v (adaptivePolicy r T) T (fun h => ∃ u, ∃ hu : u ≤ T,
      (stateAt r T u (pre h u hu)).tau = σ ∧ ¬ (stateAt r T u (pre h u hu)).exploreNow ∧
      innerLen T ((stateAt r T u (pre h u hu)).y - (stateAt r T u (pre h u hu)).x) ≤
        (stateAt r T u (pre h u hu)).k + 1 ∧
      ¬ (stateAt r T u (pre h u hu)).up < (stateAt r T u (pre h u hu)).y ∧
      γ + eps σ ≤ (stateAt r T u (pre h u hu)).y - F v r (stateAt r T u (pre h u hu)).y) ≤
      1 / (2 * T * γ ^ 2) := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hc : (0:ℝ) < 8 * T := by positivity
  refine (probT_mono v hv _ T _ _ ?_).trans ((peel v r hv hr (adaptivePolicy r T) (wE r T σ)
    (wE_mem r T σ) T 1 (by norm_num) γ (8 * T) hγ.le hc (Nat.log 2 (nEpoch T σ))).trans
    ((gap_sum _ _ hc hγ _).trans (le_of_eq ?_)))
  · rintro h ⟨u, hu, h1, h2, h3, h4, h5⟩
    exact ⟨u, hu, WA_peel v r T σ hX γ u _ h1 h2 h3 h4 h5 hγ.le⟩
  · rw [div_eq_div_iff (by positivity) (by positivity)]
    ring

/-- The same event with `γ = 0`: probability `≤ n_σ/(2T)`. -/
lemma prob_WA0 (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (T σ : ℕ) (hT : 0 < T) (hX : 9 / 4 ≤ Xe T σ) :
    probT v (adaptivePolicy r T) T (fun h => ∃ u, ∃ hu : u ≤ T,
      (stateAt r T u (pre h u hu)).tau = σ ∧ ¬ (stateAt r T u (pre h u hu)).exploreNow ∧
      innerLen T ((stateAt r T u (pre h u hu)).y - (stateAt r T u (pre h u hu)).x) ≤
        (stateAt r T u (pre h u hu)).k + 1 ∧
      ¬ (stateAt r T u (pre h u hu)).up < (stateAt r T u (pre h u hu)).y ∧
      0 + eps σ ≤ (stateAt r T u (pre h u hu)).y - F v r (stateAt r T u (pre h u hu)).y) ≤
      (nEpoch T σ : ℝ) / (2 * T) := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hc : (0:ℝ) < 8 * T := by positivity
  refine (probT_mono v hv _ T _ _ ?_).trans ((peel v r hv hr (adaptivePolicy r T) (wE r T σ)
    (wE_mem r T σ) T 1 (by norm_num) 0 (8 * T) le_rfl hc (Nat.log 2 (nEpoch T σ))).trans
    ((geom_sum_le _ hc _).trans ?_))
  · rintro h ⟨u, hu, h1, h2, h3, h4, h5⟩
    exact ⟨u, hu, WA_peel v r T σ hX 0 u _ h1 h2 h3 h4 h5 le_rfl⟩
  · have hn0 : nEpoch T σ ≠ 0 := (innerLen_pos _ _).ne'
    have h1 := Nat.pow_log_le_self 2 hn0
    have h2 : (2:ℝ) ^ Nat.log 2 (nEpoch T σ) ≤ nEpoch T σ := by exact_mod_cast h1
    rw [pow_add, div_le_div_iff₀ hc (by positivity)]
    nlinarith

/-! ### D2: an epoch has at most `2 n_σ` periods -/

lemma k_lt (r : Fin N → ℝ) (T t : ℕ) (p : Fin t → Option (Fin N)) :
    (stateAt r T t p).k < nEpoch T (stateAt r T t p).tau := by
  obtain ⟨m, -, -, -, -, -, -, hk, -⟩ := (J_stateAt r r T (stateAt r T t p).tau t p).2 rfl
  rw [yx_eq _ (stateAt_inv r T t p)] at hk
  exact hk

noncomputable def q2 (T : ℕ) (s : AlgState) : ℕ :=
  2 * nSum T s.tau + 2 * s.k + (if s.explored then 1 else 0)

lemma q2_le (T : ℕ) (s : AlgState) :
    2 * nSum T s.tau + 2 * s.k ≤ q2 T s ∧ q2 T s ≤ 2 * nSum T s.tau + 2 * s.k + 1 := by
  unfold q2; split_ifs <;> omega

lemma step_q2 (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N)) (hs : Inv s)
    (hk : s.k < nEpoch T s.tau) : q2 T s + 1 ≤ q2 T (step r T s c) := by
  have hyx := yx_eq s hs
  have hb := q2_le T s
  rcases step_cases r T s c with ⟨hE, hst⟩ | ⟨hE, hend, hst | hst⟩ | ⟨hE, hend, hst⟩
  · have h1 : q2 T s = 2 * nSum T s.tau + 2 * s.k := by simp [q2, hE.1]
    have h2 : q2 T (step r T s c) = 2 * nSum T s.tau + 2 * s.k + 1 := by rw [hst]; simp [q2]
    omega
  · rw [hyx] at hend
    change nEpoch T s.tau ≤ s.k + 1 at hend
    have h2 : q2 T (step r T s c) = 2 * nSum T (s.tau + 1) := by rw [hst]; simp [q2, epochStart]
    rw [h2, nSum_succ]
    omega
  · rw [hyx] at hend
    change nEpoch T s.tau ≤ s.k + 1 at hend
    have h2 : q2 T (step r T s c) = 2 * nSum T (s.tau + 1) := by rw [hst]; simp [q2, epochStart]
    rw [h2, nSum_succ]
    omega
  · have h2 : q2 T (step r T s c) = 2 * nSum T s.tau + 2 * (s.k + 1) := by rw [hst]; simp [q2]
    omega

lemma q2_stateAt (r : Fin N → ℝ) (T : ℕ) : ∀ (t : ℕ) (p : Fin t → Option (Fin N)) (u : ℕ)
    (hu : u ≤ t), q2 T (stateAt r T u (pre p u hu)) + (t - u) ≤ q2 T (stateAt r T t p) := by
  intro t
  induction t with
  | zero =>
    intro p u hu
    obtain rfl : u = 0 := by omega
    rw [pre_self]; omega
  | succ t ih =>
    intro p u hu
    obtain ⟨q, c, rfl⟩ : ∃ q c, p = Fin.snoc q c :=
      ⟨Fin.init p, p (Fin.last t), (Fin.snoc_init_self p).symm⟩
    rcases Nat.lt_or_ge u (t + 1) with h | h
    · have hu' : u ≤ t := Nat.lt_succ_iff.1 h
      rw [pre_snoc q c u hu hu', stateAt_snoc]
      have h1 := ih q u hu'
      have h2 := step_q2 r T (stateAt r T t q) c (stateAt_inv r T t q) (k_lt r T t q)
      omega
    · obtain rfl : u = t + 1 := le_antisymm hu h
      rw [pre_self]; omega

lemma epoch_card (r : Fin N → ℝ) (T σ : ℕ) (h : History N T) :
    (Finset.univ.filter (fun t : Fin T => (stateAt r T t.val (histPrefix h t)).tau = σ)).card ≤
      2 * nEpoch T σ := by
  classical
  have key : ∀ t1 t2 : Fin T, t1.val ≤ t2.val →
      q2 T (stateAt r T t1.val (histPrefix h t1)) + (t2.val - t1.val) ≤
        q2 T (stateAt r T t2.val (histPrefix h t2)) :=
    fun t1 t2 hle => q2_stateAt r T t2.val (histPrefix h t2) t1.val hle
  have hin : ∀ t : Fin T, (stateAt r T t.val (histPrefix h t)).tau = σ →
      2 * nSum T σ ≤ q2 T (stateAt r T t.val (histPrefix h t)) ∧
      q2 T (stateAt r T t.val (histPrefix h t)) < 2 * nSum T σ + 2 * nEpoch T σ := by
    intro t ht
    have hb := q2_le T (stateAt r T t.val (histPrefix h t))
    have hk := k_lt r T t.val (histPrefix h t)
    rw [ht] at hb hk
    omega
  calc _ ≤ (Finset.range (2 * nEpoch T σ)).card := by
        apply Finset.card_le_card_of_injOn
          (fun t : Fin T => q2 T (stateAt r T t.val (histPrefix h t)) - 2 * nSum T σ)
        · intro t ht
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht
          simp only [Finset.coe_range, Set.mem_Iio]
          have := hin t ht
          omega
        · intro t1 ht1 t2 ht2 heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht1 ht2
          simp only at heq
          have b1 := hin t1 ht1
          have b2 := hin t2 ht2
          rcases lt_trichotomy t1.val t2.val with hl | hl | hl
          · have := key t1 t2 hl.le; omega
          · exact Fin.ext hl
          · have := key t2 t1 hl.le; omega
    _ = 2 * nEpoch T σ := Finset.card_range _

/-! ### P3: pathwise accounting of wrong moves -/

noncomputable def ind (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

lemma ind_nonneg (P : Prop) : 0 ≤ ind P := by
  unfold ind; split_ifs <;> norm_num

lemma ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma ind_of (P : Prop) (hP : P) : ind P = 1 := by
  unfold ind; rw [if_pos hP]

lemma ind_of_not (P : Prop) (hP : ¬ P) : ind P = 0 := by
  unfold ind; rw [if_neg hP]

/-- Wrong `b`-move witness of epoch `σ` along the full history `h`. -/
def WBev (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) : Prop :=
  ∃ u, ∃ hu : u ≤ T, (stateAt r T u (pre h u hu)).tau = σ ∧
      (stateAt r T u (pre h u hu)).up < (stateAt r T u (pre h u hu)).y ∧
      (stateAt r T u (pre h u hu)).y ≤ optRev v r

/-- `a`-move of epoch `σ` with gap at least `γ + eps σ`. -/
def WAev (v r : Fin N → ℝ) (T σ : ℕ) (γ : ℝ) (h : History N T) : Prop :=
  ∃ u, ∃ hu : u ≤ T,
      (stateAt r T u (pre h u hu)).tau = σ ∧ ¬ (stateAt r T u (pre h u hu)).exploreNow ∧
      innerLen T ((stateAt r T u (pre h u hu)).y - (stateAt r T u (pre h u hu)).x) ≤
        (stateAt r T u (pre h u hu)).k + 1 ∧
      ¬ (stateAt r T u (pre h u hu)).up < (stateAt r T u (pre h u hu)).y ∧
      γ + eps σ ≤ (stateAt r T u (pre h u hu)).y - F v r (stateAt r T u (pre h u hu)).y

noncomputable def Gs (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) : ℝ :=
  ∑ j ∈ Finset.range (σ + 2), 2 ^ (j + 1) * eps σ * ind (WAev v r T σ ((2 ^ j - 1) * eps σ) h)

lemma Gs_nonneg (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) : 0 ≤ Gs v r T σ h :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg (by positivity) (eps_pos σ).le)
    (ind_nonneg _))

lemma F_nonneg (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr0 : ∀ i, 0 ≤ r i) (θ : ℝ) :
    0 ≤ F v r θ := rev_nonneg v r hv hr0 _

lemma inv_ba (s : AlgState) (hs : Inv s) : s.b - s.a = 3 * eps s.tau := by
  obtain ⟨hba, -, -⟩ := hs; unfold eps; linarith

lemma inv_by (s : AlgState) (hs : Inv s) : s.b - s.y = eps s.tau := by
  obtain ⟨hba, -, -⟩ := hs; unfold AlgState.y eps; linarith

lemma inv_y1 (s : AlgState) (hs : Inv s) : s.a ≤ s.y ∧ s.y ≤ 1 := by
  have h3 := inv_ba s hs
  have he := eps_pos s.tau
  obtain ⟨-, -, hb⟩ := hs; unfold AlgState.y; constructor <;> linarith

lemma g_le_Gs (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr0 : ∀ i, 0 ≤ r i) (T τ : ℕ)
    (h : History N T) (s : AlgState) (hs : Inv s) (hτ : s.tau = τ) (hx : optRev v r < s.x)
    (hWA : ∀ γ : ℝ, γ + eps τ ≤ s.y - F v r s.y → WAev v r T τ γ h) :
    optRev v r - F v r s.x ≤ Gs v r T τ h := by
  have hyx := yx_eq s hs
  rw [hτ] at hyx
  have he := eps_pos τ
  have hFy : F v r s.y ≤ F v r s.x := F_antitone_above v r hv s.x s.y hx.le (by linarith)
  have hFle : F v r s.y ≤ optRev v r := F_le_optRev v r s.y
  have hF0 : 0 ≤ F v r s.y := F_nonneg v r hv hr0 s.y
  have hy1 := (inv_y1 s hs).2
  have hg1 : eps τ ≤ s.y - F v r s.y := by linarith
  have hgle : s.y - F v r s.y ≤ 1 := by linarith
  obtain ⟨k, hk1, hk2⟩ := dyadic ((s.y - F v r s.y) / eps τ) (by rw [le_div_iff₀ he]; linarith)
  have hk1' : 2 ^ k * eps τ ≤ s.y - F v r s.y := by rwa [le_div_iff₀ he] at hk1
  have hk2' : s.y - F v r s.y ≤ 2 ^ (k + 1) * eps τ := by rwa [div_le_iff₀ he] at hk2
  have hkσ : k < τ + 2 := by
    by_contra hcon
    push Not at hcon
    have hmono : (2:ℝ) ^ (τ + 2) * eps τ ≤ 2 ^ k * eps τ := by
      gcongr
      · norm_num
    have h43 : (1:ℝ) < 2 ^ (τ + 2) * eps τ := by
      have hid : (2:ℝ) ^ (τ + 2) * eps τ = 4 / 3 * (2 * (2 / 3)) ^ τ := by
        unfold eps; rw [mul_pow]; ring
      rw [hid]
      have : (1:ℝ) ≤ (2 * (2 / 3)) ^ τ := one_le_pow₀ (by norm_num)
      linarith
    linarith
  have hev : WAev v r T τ ((2 ^ k - 1) * eps τ) h := hWA _ (by
    have : (2 ^ k - 1) * eps τ + eps τ = 2 ^ k * eps τ := by ring
    linarith)
  have hterm : 2 ^ (k + 1) * eps τ * ind (WAev v r T τ ((2 ^ k - 1) * eps τ) h) ≤
      Gs v r T τ h := by
    unfold Gs
    exact Finset.single_le_sum
      (f := fun j => 2 ^ (j + 1) * eps τ * ind (WAev v r T τ ((2 ^ j - 1) * eps τ) h))
      (fun j _ => mul_nonneg (mul_nonneg (by positivity) he.le) (ind_nonneg _))
      (Finset.mem_range.2 hkσ)
  rw [ind_of _ hev, mul_one] at hterm
  linarith

lemma step_bmove (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N))
    (hE : ¬ s.exploreNow) (hend : innerLen T (s.y - s.x) ≤ s.k + 1) (hu : s.up < s.y) :
    step r T s c = epochStart (s.tau + 1) s.a s.y := by
  unfold step; rw [if_neg hE, if_pos hend, if_pos hu]

lemma step_amove (r : Fin N → ℝ) (T : ℕ) (s : AlgState) (c : Option (Fin N))
    (hE : ¬ s.exploreNow) (hend : innerLen T (s.y - s.x) ≤ s.k + 1) (hu : ¬ s.up < s.y) :
    step r T s c = epochStart (s.tau + 1) s.x s.b := by
  unfold step; rw [if_neg hE, if_pos hend, if_neg hu]

lemma P3_step (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr0 : ∀ i, 0 ≤ r i) (T : ℕ)
    (h : History N T) (s : AlgState) (c : Option (Fin N)) (hs : Inv s)
    (hWB : s.up < s.y → s.y ≤ optRev v r → WBev v r T s.tau h)
    (hWA : ¬ s.exploreNow → innerLen T (s.y - s.x) ≤ s.k + 1 → ¬ s.up < s.y →
        ∀ γ : ℝ, γ + eps s.tau ≤ s.y - F v r s.y → WAev v r T s.tau γ h)
    (h1 : optRev v r - s.b ≤ ∑ σ ∈ Finset.range s.tau, eps σ * ind (WBev v r T σ h))
    (h2 : optRev v r < s.a →
        optRev v r - F v r s.a ≤ ∑ σ ∈ Finset.range s.tau, Gs v r T σ h) :
    (optRev v r - (step r T s c).b ≤
        ∑ σ ∈ Finset.range (step r T s c).tau, eps σ * ind (WBev v r T σ h)) ∧
    (optRev v r < (step r T s c).a → optRev v r - F v r (step r T s c).a ≤
        ∑ σ ∈ Finset.range (step r T s c).tau, Gs v r T σ h) := by
  have hB0 : ∀ σ, 0 ≤ eps σ * ind (WBev v r T σ h) :=
    fun σ => mul_nonneg (eps_pos σ).le (ind_nonneg _)
  have hS2 : 0 ≤ ∑ σ ∈ Finset.range s.tau, Gs v r T σ h :=
    Finset.sum_nonneg (fun σ _ => Gs_nonneg v r T σ h)
  by_cases hE : s.exploreNow
  · rcases step_cases r T s c with ⟨_, hst⟩ | ⟨hE', _⟩ | ⟨hE', _⟩
    · rw [hst]; exact ⟨h1, h2⟩
    · exact absurd hE hE'
    · exact absurd hE hE'
  by_cases hend : innerLen T (s.y - s.x) ≤ s.k + 1
  · by_cases hu : s.up < s.y
    · rw [step_bmove r T s c hE hend hu]
      refine ⟨?_, fun ha => ?_⟩
      · show optRev v r - s.y ≤
          ∑ σ ∈ Finset.range (s.tau + 1), eps σ * ind (WBev v r T σ h)
        rw [Finset.sum_range_succ]
        have hby := inv_by s hs
        by_cases hy : s.y ≤ optRev v r
        · rw [ind_of _ (hWB hu hy), mul_one]; linarith
        · have hS1 := Finset.sum_nonneg (fun σ (_ : σ ∈ Finset.range s.tau) => hB0 σ)
          linarith [hB0 s.tau, not_le.1 hy]
      · change optRev v r < s.a at ha
        show optRev v r - F v r s.a ≤ ∑ σ ∈ Finset.range (s.tau + 1), Gs v r T σ h
        rw [Finset.sum_range_succ]
        linarith [h2 ha, Gs_nonneg v r T s.tau h]
    · rw [step_amove r T s c hE hend hu]
      refine ⟨?_, fun hx => ?_⟩
      · show optRev v r - s.b ≤
          ∑ σ ∈ Finset.range (s.tau + 1), eps σ * ind (WBev v r T σ h)
        rw [Finset.sum_range_succ]
        linarith [hB0 s.tau]
      · change optRev v r < s.x at hx
        show optRev v r - F v r s.x ≤ ∑ σ ∈ Finset.range (s.tau + 1), Gs v r T σ h
        rw [Finset.sum_range_succ]
        have := g_le_Gs v r hv hr0 T s.tau h s hs rfl hx (hWA hE hend hu)
        linarith
  · rcases step_cases r T s c with ⟨hE', _⟩ | ⟨_, hend', _⟩ | ⟨_, _, hst⟩
    · exact absurd hE' hE
    · exact absurd hend' hend
    · rw [hst]; exact ⟨h1, h2⟩

lemma pre_succ {T : ℕ} (h : Fin T → Option (Fin N)) (t : ℕ) (ht : t + 1 ≤ T) :
    pre h (t + 1) ht = Fin.snoc (pre h t (by omega)) (h ⟨t, by omega⟩) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; rfl
  · rw [Fin.snoc_castSucc]; rfl

lemma P3 (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (T : ℕ) (h : History N T) : ∀ t (ht : t ≤ T),
      (optRev v r - (stateAt r T t (pre h t ht)).b ≤
        ∑ σ ∈ Finset.range (stateAt r T t (pre h t ht)).tau, eps σ * ind (WBev v r T σ h)) ∧
      (optRev v r < (stateAt r T t (pre h t ht)).a →
        optRev v r - F v r (stateAt r T t (pre h t ht)).a ≤
          ∑ σ ∈ Finset.range (stateAt r T t (pre h t ht)).tau, Gs v r T σ h) := by
  intro t
  induction t with
  | zero =>
    intro ht
    have h0 : stateAt r T 0 (pre h 0 ht) = initState := by simp [stateAt]
    rw [h0]
    refine ⟨?_, fun ha => ?_⟩
    · show optRev v r - 1 ≤ ∑ σ ∈ Finset.range 0, eps σ * ind (WBev v r T σ h)
      rw [Finset.sum_range_zero]; linarith [optRev_le_one v r hv hr1]
    · exact absurd ha (not_lt.2 (optRev_nonneg v r))
  | succ t ih =>
    intro ht
    have ht' : t ≤ T := by omega
    rw [pre_succ h t ht, stateAt_snoc]
    obtain ⟨h1, h2⟩ := ih ht'
    refine P3_step v r hv hr0 T h _ _ (stateAt_inv r T t _) ?_ ?_ h1 h2
    · intro hu hy; exact ⟨t, ht', rfl, hu, hy⟩
    · intro hE hend hu γ hγ; exact ⟨t, ht', rfl, hE, hend, hu, hγ⟩

/-- Per-period regret, pathwise. -/
lemma period_bound (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (s : AlgState) (hs : Inv s)
    (B G : ℝ) (h1 : optRev v r - s.b ≤ B) (hB : 0 ≤ B)
    (h2 : optRev v r < s.a → optRev v r - F v r s.a ≤ G) (hG : 0 ≤ G) :
    optRev v r - rev v r (offerOf r s) ≤ 3 * eps s.tau + B + G +
      ind (s.exploreNow ∧ optRev v r < s.y) * (s.y - F v r s.y) := by
  classical
  have h3 := inv_ba s hs
  have hay := (inv_y1 s hs).1
  have he := eps_pos s.tau
  unfold offerOf
  split_ifs with hE
  · show optRev v r - F v r s.y ≤ _
    by_cases hy : optRev v r < s.y
    · rw [ind_of _ ⟨hE, hy⟩, one_mul]; linarith
    · rw [ind_of_not _ (fun hh => hy hh.2), zero_mul]
      have := le_F_of_le v r hv s.y (not_lt.1 hy)
      linarith
  · show optRev v r - F v r s.a ≤ _
    rw [ind_of_not _ (fun hh => hE hh.1), zero_mul]
    by_cases ha : optRev v r < s.a
    · linarith [h2 ha]
    · have := le_F_of_le v r hv s.a (not_lt.1 ha)
      linarith

/-! ### E: explorations above `θ*` -/

lemma radius_anti (T m₁ m : ℕ) (h1 : 0 < m₁) (h : m₁ ≤ m) : radius T m ≤ radius T m₁ := by
  have hm1 : (0:ℝ) < m₁ := by exact_mod_cast h1
  have hm : (m₁:ℝ) ≤ m := by exact_mod_cast h
  have hm0 : (0:ℝ) < m := by linarith
  have hT : (0:ℝ) ≤ T := Nat.cast_nonneg T
  unfold radius
  by_cases hc : (m:ℝ) ≤ 8 * T
  · apply Real.sqrt_le_sqrt
    have hl0 : 0 ≤ Real.log (8 * T / m) :=
      Real.log_nonneg (by rw [le_div_iff₀ hm0]; linarith)
    have hl : Real.log (8 * T / m) ≤ Real.log (8 * T / m₁) :=
      Real.log_le_log (div_pos (by linarith) hm0) (by gcongr)
    calc 2 * Real.log (8 * T / m) / m ≤ 2 * Real.log (8 * T / m₁) / m := by gcongr
      _ ≤ 2 * Real.log (8 * T / m₁) / m₁ := by
          apply div_le_div_of_nonneg_left (by linarith) hm1 hm
  · push Not at hc
    have hl : Real.log (8 * T / m) ≤ 0 :=
      Real.log_nonpos (by positivity) (by rw [div_le_one hm0]; linarith)
    have h2 : 2 * Real.log (8 * T / m) / m ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hm0.le
    rw [Real.sqrt_eq_zero'.2 h2]
    exact Real.sqrt_nonneg _

lemma innerLen_ge (T : ℕ) (e : ℝ) :
    8 * (e⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * e ^ 2)) ≤ (innerLen T e : ℝ) := by
  unfold innerLen
  set x := e⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * e ^ 2)
  have h1 := Nat.le_ceil x
  have h2 : 8 * ⌈x⌉₊ ≤ max 1 (8 * ⌈x⌉₊) := le_max_right _ _
  calc 8 * x ≤ 8 * (⌈x⌉₊ : ℝ) := by linarith
    _ = ((8 * ⌈x⌉₊ : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := by exact_mod_cast h2

lemma radius_le_e (T : ℕ) (e : ℝ) (he : 0 < e) (hX : 9 / 4 ≤ 8 * (T : ℝ) * e ^ 2) :
    radius T (innerLen T e) ≤ e / 2 := by
  have hL := log_ge _ hX
  have hng := innerLen_ge T e
  have hq : e⁻¹ ^ 2 * e ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ he.ne']; simp
  have hq0 : 0 < e⁻¹ ^ 2 := by positivity
  have hnpos : 0 < (innerLen T e : ℝ) := by
    have := mul_pos hq0 (by linarith : (0:ℝ) < Real.log (8 * (T : ℝ) * e ^ 2))
    linarith
  have hq59 := mul_le_mul_of_nonneg_left hL hq0.le
  have hnq : e⁻¹ ^ 2 ≤ (innerLen T e : ℝ) := by linarith
  have he8 : e⁻¹ ^ 2 * (8 * (T : ℝ) * e ^ 2) = 8 * T := by
    rw [show e⁻¹ ^ 2 * (8 * (T : ℝ) * e ^ 2) = 8 * T * (e⁻¹ ^ 2 * e ^ 2) by ring, hq, mul_one]
  have hX0 : 0 ≤ 8 * (T : ℝ) * e ^ 2 := by linarith
  have hT : 0 < (T : ℝ) := by
    have := mul_pos hq0 (by linarith : (0 : ℝ) < 8 * (T : ℝ) * e ^ 2)
    linarith
  have hratio : 8 * (T : ℝ) / innerLen T e ≤ 8 * (T : ℝ) * e ^ 2 := by
    rw [div_le_iff₀ hnpos]
    have := mul_le_mul_of_nonneg_left hnq hX0
    linarith
  have hlog : Real.log (8 * T / innerLen T e) ≤ Real.log (8 * (T : ℝ) * e ^ 2) :=
    Real.log_le_log (div_pos (by linarith) hnpos) hratio
  have hk : (e / 2) ^ 2 * (8 * (e⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * e ^ 2))) =
      2 * Real.log (8 * (T : ℝ) * e ^ 2) := by
    rw [show (e / 2) ^ 2 * (8 * (e⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * e ^ 2))) =
      2 * (e⁻¹ ^ 2 * e ^ 2) * Real.log (8 * (T : ℝ) * e ^ 2) by ring, hq, mul_one]
  unfold radius
  rw [show e / 2 = Real.sqrt ((e / 2) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hnpos]
  have := mul_le_mul_of_nonneg_left hng (sq_nonneg (e / 2))
  linarith

/-- Large-gap exploration event of epoch `σ` at level `j` (peel shape, gap `2^(j+1) eps σ`). -/
def EVev (v r : Fin N → ℝ) (T σ j : ℕ) (h : History N T) : Prop :=
  ∃ u, ∃ hu : u ≤ T, 1 ≤ Ks (wE r T σ) (pre h u hu) ∧
    Ks (wE r T σ) (pre h u hu) < 2 ^ (Nat.log 2 (nEpoch T σ) + 1) ∧
    Ks (wE r T σ) (pre h u hu) * (2 ^ (j + 1) * eps σ) +
      Real.sqrt (2 * Ks (wE r T σ) (pre h u hu) *
        Real.log (8 * (T : ℝ) / Ks (wE r T σ) (pre h u hu))) ≤
      1 * Zs v r (adaptivePolicy r T) (wE r T σ) (pre h u hu)

noncomputable def Mj (T σ j : ℕ) : ℕ := by
  classical
  exact if 2 ^ (j + 2) * eps σ ≤ 1 then innerLen T (2 ^ (j + 1) * eps σ) else 0

noncomputable def Eb (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) (t : ℕ) (ht : t ≤ T) : ℝ :=
  4 * eps σ * wE r T σ t (pre h t ht) +
  ∑ j ∈ Finset.range (σ + 1), 2 ^ (j + 3) * eps σ *
    (ind (wE r T σ t (pre h t ht) = 1 ∧ Ks (wE r T σ) (pre h t ht) < Mj T σ j) +
      ind (EVev v r T σ j h))

lemma Eb_ge (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) (t : ℕ) (ht : t ≤ T) (j : ℕ)
    (hj : j < σ + 1) :
    4 * eps σ * wE r T σ t (pre h t ht) + 2 ^ (j + 3) * eps σ *
      (ind (wE r T σ t (pre h t ht) = 1 ∧ Ks (wE r T σ) (pre h t ht) < Mj T σ j) +
        ind (EVev v r T σ j h)) ≤ Eb v r T σ h t ht := by
  unfold Eb
  have := Finset.single_le_sum (s := Finset.range (σ + 1))
    (f := fun j => 2 ^ (j + 3) * eps σ *
      (ind (wE r T σ t (pre h t ht) = 1 ∧ Ks (wE r T σ) (pre h t ht) < Mj T σ j) +
        ind (EVev v r T σ j h)))
    (fun j _ => mul_nonneg (mul_nonneg (by positivity) (eps_pos σ).le)
      (add_nonneg (ind_nonneg _) (ind_nonneg _))) (Finset.mem_range.2 hj)
  linarith

lemma Eb_nonneg (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) (t : ℕ) (ht : t ≤ T) :
    0 ≤ Eb v r T σ h t ht := by
  have h0 := Eb_ge v r T σ h t ht 0 (by omega)
  have hw := (wE_mem r T σ t (pre h t ht)).1
  have := eps_pos σ
  have := ind_nonneg (wE r T σ t (pre h t ht) = 1 ∧ Ks (wE r T σ) (pre h t ht) < Mj T σ 0)
  have := ind_nonneg (EVev v r T σ 0 h)
  have : 0 ≤ 4 * eps σ * wE r T σ t (pre h t ht) := by positivity
  have : 0 ≤ 2 ^ (0 + 3) * eps σ * (ind (wE r T σ t (pre h t ht) = 1 ∧
      Ks (wE r T σ) (pre h t ht) < Mj T σ 0) + ind (EVev v r T σ 0 h)) := by positivity
  linarith

lemma big_eps (σ : ℕ) : (1:ℝ) < 2 ^ (σ + 2) * eps σ := by
  have hid : (2:ℝ) ^ (σ + 2) * eps σ = 4 / 3 * (2 * (2 / 3)) ^ σ := by
    unfold eps; rw [mul_pow]; ring
  rw [hid]
  have : (1:ℝ) ≤ (2 * (2 / 3)) ^ σ := one_le_pow₀ (by norm_num)
  linarith

set_option maxHeartbeats 1000000 in
lemma E_t_bound (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr0 : ∀ i, 0 ≤ r i) (T : ℕ)
    (h : History N T) (t : ℕ) (ht : t ≤ T)
    (hX : 9 / 4 ≤ Xe T (stateAt r T t (pre h t ht)).tau) :
    ind ((stateAt r T t (pre h t ht)).exploreNow ∧
        optRev v r < (stateAt r T t (pre h t ht)).y) *
      ((stateAt r T t (pre h t ht)).y - F v r (stateAt r T t (pre h t ht)).y) ≤
    Eb v r T (stateAt r T t (pre h t ht)).tau h t ht := by
  classical
  by_cases hc : (stateAt r T t (pre h t ht)).exploreNow ∧
      optRev v r < (stateAt r T t (pre h t ht)).y
  swap
  · rw [ind_of_not _ hc, zero_mul]; exact Eb_nonneg v r T _ h t ht
  rw [ind_of _ hc, one_mul]
  obtain ⟨hE, hy⟩ := hc
  set p := pre h t ht with hp
  set s := stateAt r T t p with hs_def
  set σ := s.tau with hσ
  have hw : wE r T σ t p = 1 := by
    show wS σ s = 1
    unfold wS; rw [if_pos ⟨rfl, hE⟩]
  have hinv := stateAt_inv r T t p
  have hyx := yx_eq s hinv
  have he := eps_pos σ
  have hFle := F_le_optRev v r s.y
  have hy1 := (inv_y1 s hinv).2
  have hF0 := F_nonneg v r hv hr0 s.y
  by_cases hg : s.y - F v r s.y ≤ 4 * eps σ
  · have h0 := Eb_ge v r T σ h t ht 0 (by omega)
    rw [hw] at h0
    have := ind_nonneg (EVev v r T σ 0 h)
    have := ind_nonneg ((1:ℝ) = 1 ∧ Ks (wE r T σ) p < Mj T σ 0)
    have : 0 ≤ 2 ^ (0 + 3) * eps σ * (ind ((1:ℝ) = 1 ∧ Ks (wE r T σ) p < Mj T σ 0) +
        ind (EVev v r T σ 0 h)) := by positivity
    linarith
  push Not at hg
  obtain ⟨j, hj1, hj2⟩ := dyadic ((s.y - F v r s.y) / (4 * eps σ))
    (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hj1' : 2 ^ (j + 2) * eps σ ≤ s.y - F v r s.y := by
    rw [le_div_iff₀ (by linarith)] at hj1
    have : (2:ℝ) ^ (j + 2) * eps σ = 2 ^ j * (4 * eps σ) := by ring
    linarith
  have hj2' : s.y - F v r s.y ≤ 2 ^ (j + 3) * eps σ := by
    rw [div_le_iff₀ (by linarith)] at hj2
    have : (2:ℝ) ^ (j + 3) * eps σ = 2 ^ (j + 1) * (4 * eps σ) := by ring
    linarith
  have hjσ : j < σ + 1 := by
    by_contra hcon
    push Not at hcon
    have hmono : (2:ℝ) ^ (σ + 2) * eps σ ≤ 2 ^ (j + 2) * eps σ := by
      gcongr
      · norm_num
      · omega
    linarith [big_eps σ]
  have hj1le : (2:ℝ) ^ (j + 2) * eps σ ≤ 1 := by linarith
  have hMj : Mj T σ j = innerLen T (2 ^ (j + 1) * eps σ) := by unfold Mj; rw [if_pos hj1le]
  have hge := Eb_ge v r T σ h t ht j hjσ
  have hw0 : 0 ≤ 4 * eps σ * wE r T σ t p := by rw [hw]; linarith
  suffices hsum : 1 ≤ ind (wE r T σ t p = 1 ∧ Ks (wE r T σ) p < Mj T σ j) +
      ind (EVev v r T σ j h) by
    have : 2 ^ (j + 3) * eps σ * 1 ≤ 2 ^ (j + 3) * eps σ *
        (ind (wE r T σ t p = 1 ∧ Ks (wE r T σ) p < Mj T σ j) + ind (EVev v r T σ j h)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    linarith
  obtain ⟨m, hK, hrho, h0, hpos, -, -, hk, hmk⟩ := (J_stateAt v r T σ t p).2 rfl
  have hA0 := ind_nonneg (wE r T σ t p = 1 ∧ Ks (wE r T σ) p < Mj T σ j)
  have hB0 := ind_nonneg (EVev v r T σ j h)
  by_cases hm : (m : ℝ) < Mj T σ j
  · rw [ind_of _ ⟨hw, by rw [hK]; exact hm⟩]; linarith
  push Not at hm
  have hMpos : (0:ℝ) < Mj T σ j := by rw [hMj]; exact_mod_cast innerLen_pos T _
  have hmpos : (0:ℝ) < m := by linarith
  have hmN : 0 < m := by exact_mod_cast hmpos
  have hMm : Mj T σ j ≤ m := by exact_mod_cast hm
  obtain ⟨-, hup⟩ := hpos hmN
  have hrad : radius T m ≤ 2 ^ j * eps σ := by
    have he2 : 0 < 2 ^ (j + 1) * eps σ := by positivity
    have hX2 : 9 / 4 ≤ 8 * (T : ℝ) * (2 ^ (j + 1) * eps σ) ^ 2 := by
      have h1 : (1:ℝ) ≤ (2 ^ (j + 1)) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
      have hT0 : (0:ℝ) ≤ 8 * T * eps σ ^ 2 := by positivity
      have : 8 * (T : ℝ) * (2 ^ (j + 1) * eps σ) ^ 2 = (2 ^ (j + 1)) ^ 2 * (8 * T * eps σ ^ 2) := by
        ring
      rw [this]
      have : Xe T σ = 8 * T * eps σ ^ 2 := rfl
      nlinarith
    have := radius_le_e T _ he2 hX2
    have h3 := radius_anti T (Mj T σ j) m (by rw [hMj]; exact innerLen_pos T _) hMm
    rw [hMj] at h3
    have : 2 ^ (j + 1) * eps σ / 2 = 2 ^ j * eps σ := by ring
    linarith
  have hyup : s.y ≤ s.up := hE.2.2
  rw [hup, hrho] at hyup
  set Z := Zs v r (adaptivePolicy r T) (wE r T σ) p with hZ
  have hdiv : (Z + (m:ℝ) * F v r s.y) / m = Z / m + F v r s.y := by
    field_simp
  rw [hdiv] at hyup
  have hZm : (m:ℝ) * (s.y - F v r s.y - radius T m) ≤ Z := by
    have : s.y - F v r s.y - radius T m ≤ Z / m := by linarith
    rwa [le_div_iff₀ hmpos, mul_comm] at this
  have hmr := m_rad T m hmN
  have hkey : (m:ℝ) * (2 ^ (j + 1) * eps σ) + (m:ℝ) * radius T m ≤
      (m:ℝ) * (s.y - F v r s.y - radius T m) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hmpos.le
    have : (2:ℝ) ^ (j + 2) * eps σ = 2 ^ (j + 1) * eps σ + 2 * (2 ^ j * eps σ) := by ring
    linarith
  have hnE : (m:ℝ) < 2 ^ (Nat.log 2 (nEpoch T σ) + 1) := by
    have h1 : m ≤ nEpoch T σ := by
      have hk' : s.k < innerLen T (s.y - s.x) := hk
      have hmk' : m ≤ s.k + 1 := hmk
      rw [hyx] at hk'
      have : innerLen T (eps s.tau) = nEpoch T σ := rfl
      omega
    have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (nEpoch T σ)
    have h3 : m < 2 ^ (Nat.log 2 (nEpoch T σ) + 1) := lt_of_le_of_lt h1 h2
    exact_mod_cast h3
  have hev : EVev v r T σ j h := by
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · rw [hK]; exact_mod_cast hmN
    · rw [hK]; exact hnE
    · rw [hK, ← hmr, one_mul]; linarith
  rw [ind_of _ hev]; linarith

/-! ### Per-history bound -/

lemma tau_le (r : Fin N → ℝ) (T : ℕ) : ∀ (t : ℕ) (p : Fin t → Option (Fin N)),
    (stateAt r T t p).tau ≤ t := by
  intro t
  induction t with
  | zero =>
    intro p
    have h1 : stateAt r T 0 p = initState := by simp [stateAt]
    rw [h1]; exact Nat.le_refl _
  | succ t ih =>
    intro p
    obtain ⟨q, c, rfl⟩ : ∃ q c, p = Fin.snoc q c :=
      ⟨Fin.init p, p (Fin.last t), (Fin.snoc_init_self p).symm⟩
    rw [stateAt_snoc]
    rcases step_tau r T (stateAt r T t q) c with h' | ⟨a, b, h'⟩
    · rw [h']; exact Nat.le_succ_of_le (ih q)
    · rw [h']; show (stateAt r T t q).tau + 1 ≤ t + 1; exact Nat.succ_le_succ (ih q)

lemma eps_anti {σ τ : ℕ} (h : σ ≤ τ) : eps τ ≤ eps σ := by
  unfold eps
  have := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 2 / 3) (by norm_num) h
  linarith

lemma Xe_anti (T : ℕ) {σ τ : ℕ} (h : σ ≤ τ) : Xe T τ ≤ Xe T σ := by
  unfold Xe
  have h1 := eps_anti h
  have h2 := eps_pos τ
  have h3 : eps τ ^ 2 ≤ eps σ ^ 2 := pow_le_pow_left₀ h2.le h1 2
  have : (0:ℝ) ≤ 8 * T := by positivity
  nlinarith

lemma count_le (L : ℕ) (a x : ℕ → ℝ) (M : ℕ) (h0 : a 0 = 0)
    (hstep : ∀ n < L, a (n + 1) = a n + x n) (hx : ∀ n < L, x n = 0 ∨ x n = 1) :
    ∀ n ≤ L, ∃ k : ℕ, a n = k ∧ ∑ t ∈ Finset.range n, ind (x t = 1 ∧ a t < M) ≤ k ∧
      ∑ t ∈ Finset.range n, ind (x t = 1 ∧ a t < M) ≤ M := by
  intro n
  induction n with
  | zero => intro _; exact ⟨0, by simp [h0], by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨k, hk, h1, h2⟩ := ih (by omega)
    rw [Finset.sum_range_succ, hstep n (by omega)]
    rcases hx n (by omega) with hx0 | hx1
    · have hn0 : ¬ (x n = 1 ∧ a n < M) := fun hh => by
        have := hh.1; rw [hx0] at this; norm_num at this
      rw [ind_of_not _ hn0]
      exact ⟨k, by rw [hk, hx0, add_zero], by linarith, by linarith⟩
    · by_cases hkM : k < M
      · rw [ind_of _ ⟨hx1, by rw [hk]; exact_mod_cast hkM⟩]
        have hk1 : ((k:ℝ) + 1) ≤ M := by exact_mod_cast Nat.succ_le_of_lt hkM
        exact ⟨k + 1, by rw [hk, hx1]; push_cast; ring, by push_cast; linarith, by linarith⟩
      · have hn0 : ¬ (x n = 1 ∧ a n < M) := fun hh => hkM (by
          have := hh.2; rw [hk] at this; exact_mod_cast this)
        rw [ind_of_not _ hn0]
        exact ⟨k + 1, by rw [hk, hx1]; push_cast; ring, by push_cast; linarith, by linarith⟩

set_option maxHeartbeats 1000000 in
lemma ES (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) :
    ∑ t : Fin T, (3 * eps σ * ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) +
        Eb v r T σ h t.val t.isLt.le) ≤
      14 * eps σ * nEpoch T σ + ∑ j ∈ Finset.range (σ + 1),
        2 ^ (j + 3) * eps σ * (Mj T σ j + T * ind (EVev v r T σ j h)) := by
  classical
  have he := eps_pos σ
  have hcard : ∑ t : Fin T, ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) ≤
      2 * nEpoch T σ := by
    have hc := epoch_card r T σ h
    have heq : ∑ t : Fin T, ind ((stateAt r T t.val (histPrefix h t)).tau = σ) =
        ((Finset.univ.filter (fun t : Fin T => (stateAt r T t.val (histPrefix h t)).tau = σ)).card
          : ℝ) := by
      rw [Finset.card_filter]; push_cast
      apply Finset.sum_congr rfl; intro t _
      by_cases hP : (stateAt r T t.val (histPrefix h t)).tau = σ
      · rw [ind_of _ hP]; simp [hP]
      · rw [ind_of_not _ hP]; simp [hP]
    have : ∑ t : Fin T, ind ((stateAt r T t.val (histPrefix h t)).tau = σ) ≤ 2 * nEpoch T σ := by
      rw [heq]; exact_mod_cast hc
    exact this
  have hw : ∀ t : Fin T, wE r T σ t.val (pre h t.val t.isLt.le) ≤
      ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) := by
    intro t
    by_cases hP : (stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ
    · rw [ind_of _ hP]; exact (wE_mem r T σ _ _).2
    · rw [ind_of_not _ hP]
      show wS σ _ ≤ 0
      unfold wS; rw [if_neg (fun hh => hP hh.1)]
  have hcount : ∀ j, ∑ t : Fin T, ind (wE r T σ t.val (pre h t.val t.isLt.le) = 1 ∧
      Ks (wE r T σ) (pre h t.val t.isLt.le) < Mj T σ j) ≤ Mj T σ j := by
    intro j
    have hA0 : (fun n => if hn : n ≤ T then Ks (wE r T σ) (pre h n hn) else 0) 0 = 0 := by
      show (if hn : 0 ≤ T then Ks (wE r T σ) (pre h 0 hn) else 0) = 0
      rw [dif_pos (Nat.zero_le T)] <;> simp [Ks]
    have hA1 : ∀ n < T, (fun n => if hn : n ≤ T then Ks (wE r T σ) (pre h n hn) else 0) (n + 1) =
        (fun n => if hn : n ≤ T then Ks (wE r T σ) (pre h n hn) else 0) n +
          (fun n => if hn : n ≤ T then wE r T σ n (pre h n hn) else 0) n := by
      intro n hn
      show (if hn : n + 1 ≤ T then Ks (wE r T σ) (pre h (n + 1) hn) else 0) =
        (if hn : n ≤ T then Ks (wE r T σ) (pre h n hn) else 0) +
          (if hn : n ≤ T then wE r T σ n (pre h n hn) else 0)
      rw [dif_pos (by omega : n + 1 ≤ T), dif_pos (by omega : n ≤ T), dif_pos (by omega : n ≤ T),
        pre_succ h n (by omega), Ks_snoc]
    have hA2 : ∀ n < T, (fun n => if hn : n ≤ T then wE r T σ n (pre h n hn) else 0) n = 0 ∨
        (fun n => if hn : n ≤ T then wE r T σ n (pre h n hn) else 0) n = 1 := by
      intro n hn
      show (if hn : n ≤ T then wE r T σ n (pre h n hn) else 0) = 0 ∨
        (if hn : n ≤ T then wE r T σ n (pre h n hn) else 0) = 1
      rw [dif_pos (by omega : n ≤ T)]
      unfold wE wS
      split_ifs
      · right; rfl
      · left; rfl
    obtain ⟨k, -, -, hM⟩ := count_le T
      (fun n => if hn : n ≤ T then Ks (wE r T σ) (pre h n hn) else 0)
      (fun n => if hn : n ≤ T then wE r T σ n (pre h n hn) else 0) (Mj T σ j) hA0 hA1 hA2 T le_rfl
    rw [Finset.sum_range] at hM
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun t _ => ?_))) hM
    simp only [dif_pos t.isLt.le]
  have hsplit : ∑ t : Fin T, (3 * eps σ * ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) +
        Eb v r T σ h t.val t.isLt.le) =
      3 * eps σ * ∑ t : Fin T, ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) +
      (4 * eps σ * ∑ t : Fin T, wE r T σ t.val (pre h t.val t.isLt.le) +
      ∑ j ∈ Finset.range (σ + 1), 2 ^ (j + 3) * eps σ *
        (∑ t : Fin T, ind (wE r T σ t.val (pre h t.val t.isLt.le) = 1 ∧
          Ks (wE r T σ) (pre h t.val t.isLt.le) < Mj T σ j) + T * ind (EVev v r T σ j h))) := by
    unfold Eb
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_comm]
    congr 2
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsplit]
  have hwsum : ∑ t : Fin T, wE r T σ t.val (pre h t.val t.isLt.le) ≤ 2 * nEpoch T σ :=
    le_trans (Finset.sum_le_sum (fun t _ => hw t)) hcard
  have hj : ∑ j ∈ Finset.range (σ + 1), 2 ^ (j + 3) * eps σ *
        (∑ t : Fin T, ind (wE r T σ t.val (pre h t.val t.isLt.le) = 1 ∧
          Ks (wE r T σ) (pre h t.val t.isLt.le) < Mj T σ j) + T * ind (EVev v r T σ j h)) ≤
      ∑ j ∈ Finset.range (σ + 1), 2 ^ (j + 3) * eps σ * (Mj T σ j + T * ind (EVev v r T σ j h)) := by
    apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [hcount j]
  have h1 : 3 * eps σ * ∑ t : Fin T, ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) ≤
      3 * eps σ * (2 * nEpoch T σ) := mul_le_mul_of_nonneg_left hcard (by linarith)
  have h2 : 4 * eps σ * ∑ t : Fin T, wE r T σ t.val (pre h t.val t.isLt.le) ≤
      4 * eps σ * (2 * nEpoch T σ) := mul_le_mul_of_nonneg_left hwsum (by linarith)
  linarith

noncomputable def Sset (T : ℕ) : Finset ℕ := (Finset.range T).filter (fun σ => 9 / 4 ≤ Xe T σ)

noncomputable def BBh (v r : Fin N → ℝ) (T : ℕ) (h : History N T) : ℝ :=
  ∑ σ ∈ Sset T, eps σ * ind (WBev v r T σ h)

noncomputable def GGh (v r : Fin N → ℝ) (T : ℕ) (h : History N T) : ℝ :=
  ∑ σ ∈ Sset T, Gs v r T σ h

noncomputable def EEh (v r : Fin N → ℝ) (T : ℕ) (h : History N T) : ℝ :=
  ∑ σ ∈ Sset T, (14 * eps σ * nEpoch T σ + ∑ j ∈ Finset.range (σ + 1),
        2 ^ (j + 3) * eps σ * (Mj T σ j + T * ind (EVev v r T σ j h)))

set_option maxHeartbeats 1000000 in
lemma PH (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i ≤ 1)
    (T : ℕ) (hT : 3 ≤ T) (h : History N T) :
    ∑ t : Fin T, (optRev v r - rev v r (offered (adaptivePolicy r T) h t)) ≤
      T * BBh v r T h + T * GGh v r T h + EEh v r T h := by
  classical
  have hmem : ∀ t : Fin T, (stateAt r T t.val (pre h t.val t.isLt.le)).tau ∈ Sset T := by
    intro t
    have h1 := tau_le r T t.val (pre h t.val t.isLt.le)
    have h2 := reach_X r T hT t.val t.isLt (pre h t.val t.isLt.le)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by have := t.isLt; omega), h2⟩
  have hsub : ∀ t : Fin T,
      Finset.range (stateAt r T t.val (pre h t.val t.isLt.le)).tau ⊆ Sset T := by
    intro t σ hσ
    have hσ' := Finset.mem_range.1 hσ
    have hm := Finset.mem_filter.1 (hmem t)
    have hm1 := Finset.mem_range.1 hm.1
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), le_trans hm.2 (Xe_anti T hσ'.le)⟩
  have hper : ∀ t : Fin T, optRev v r - rev v r (offered (adaptivePolicy r T) h t) ≤
      BBh v r T h + GGh v r T h + ∑ σ ∈ Sset T,
        (3 * eps σ * ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) +
          Eb v r T σ h t.val t.isLt.le) := by
    intro t
    obtain ⟨h1, h2⟩ := P3 v r hv hr0 hr1 T h t.val t.isLt.le
    set s := stateAt r T t.val (pre h t.val t.isLt.le) with hs
    have hB : ∑ σ ∈ Finset.range s.tau, eps σ * ind (WBev v r T σ h) ≤ BBh v r T h :=
      Finset.sum_le_sum_of_subset_of_nonneg (hsub t)
        (fun σ _ _ => mul_nonneg (eps_pos σ).le (ind_nonneg _))
    have hG : ∑ σ ∈ Finset.range s.tau, Gs v r T σ h ≤ GGh v r T h :=
      Finset.sum_le_sum_of_subset_of_nonneg (hsub t) (fun σ _ _ => Gs_nonneg v r T σ h)
    have hpb := period_bound v r hv s (stateAt_inv r T _ _) _ _ h1
      (Finset.sum_nonneg (fun σ _ => mul_nonneg (eps_pos σ).le (ind_nonneg _))) h2
      (Finset.sum_nonneg (fun σ _ => Gs_nonneg v r T σ h))
    have hE := E_t_bound v r hv hr0 T h t.val t.isLt.le (Finset.mem_filter.1 (hmem t)).2
    have hsingle : 3 * eps s.tau * ind (s.tau = s.tau) + Eb v r T s.tau h t.val t.isLt.le ≤
        ∑ σ ∈ Sset T, (3 * eps σ * ind (s.tau = σ) + Eb v r T σ h t.val t.isLt.le) :=
      Finset.single_le_sum
        (f := fun σ => 3 * eps σ * ind (s.tau = σ) + Eb v r T σ h t.val t.isLt.le)
        (fun σ _ => add_nonneg (mul_nonneg (by linarith [eps_pos σ]) (ind_nonneg _))
          (Eb_nonneg v r T σ h t.val t.isLt.le)) (hmem t)
    rw [ind_of _ rfl, mul_one] at hsingle
    change optRev v r - rev v r (offerOf r s) ≤ _
    linarith
  calc ∑ t : Fin T, (optRev v r - rev v r (offered (adaptivePolicy r T) h t))
      ≤ ∑ t : Fin T, (BBh v r T h + GGh v r T h + ∑ σ ∈ Sset T,
        (3 * eps σ * ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) +
          Eb v r T σ h t.val t.isLt.le)) := Finset.sum_le_sum (fun t _ => hper t)
    _ = T * BBh v r T h + T * GGh v r T h + ∑ σ ∈ Sset T, ∑ t : Fin T,
        (3 * eps σ * ind ((stateAt r T t.val (pre h t.val t.isLt.le)).tau = σ) +
          Eb v r T σ h t.val t.isLt.le) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, Finset.sum_comm]
    _ ≤ T * BBh v r T h + T * GGh v r T h + EEh v r T h := by
        unfold EEh
        have := Finset.sum_le_sum (s := Sset T) (fun σ _ => ES v r T σ h)
        linarith


/-! ## Session 5: expectation, per-epoch bounds, summation -/

lemma E_ind (v : Fin N → ℝ) (π : Policy N) (T : ℕ) (E : History N T → Prop) :
    ∑ h : History N T, histProb v π h * ind (E h) = probT v π T E := by
  classical
  unfold probT ind
  refine Finset.sum_congr rfl (fun h _ => ?_)
  split_ifs <;> simp

lemma E_const (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ) (d : ℝ) :
    ∑ h : History N T, histProb v π h * d = d := by
  rw [← Finset.sum_mul, histProb_sum_one v hv π T, one_mul]

lemma E_one (v : Fin N → ℝ) (π : Policy N) (T : ℕ) (K : ℝ) (E : History N T → Prop) :
    ∑ h : History N T, histProb v π h * (K * ind (E h)) = K * probT v π T E := by
  rw [← E_ind v π T E, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun h _ => by ring)

lemma E_lin (v : Fin N → ℝ) (π : Policy N) (T : ℕ) (J : Finset ℕ) (c : ℕ → ℝ)
    (E : ℕ → History N T → Prop) :
    ∑ h : History N T, histProb v π h * ∑ j ∈ J, c j * ind (E j h) =
      ∑ j ∈ J, c j * probT v π T (E j) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← E_ind v π T (E j), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun h _ => by ring)

lemma E_split (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ) (d : ℝ)
    (f g k : History N T → ℝ) :
    ∑ h : History N T, histProb v π h * (d + f h + g h + k h) =
      d + ∑ h : History N T, histProb v π h * f h + ∑ h : History N T, histProb v π h * g h +
        ∑ h : History N T, histProb v π h * k h := by
  simp only [mul_add, Finset.sum_add_distrib, E_const v hv π T]

lemma innerLen_le (T : ℕ) (e : ℝ) (hL : 0 ≤ Real.log (8 * (T : ℝ) * e ^ 2)) :
    (innerLen T e : ℝ) ≤ 8 * (e⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * e ^ 2)) + 8 := by
  unfold innerLen
  have hx : 0 ≤ e⁻¹ ^ 2 * Real.log (8 * (T : ℝ) * e ^ 2) := mul_nonneg (by positivity) hL
  have h1 := Nat.ceil_lt_add_one hx
  push_cast
  exact max_le (by linarith) (by linarith)

lemma eps_le_third (σ : ℕ) : eps σ ≤ 1 / 3 := by
  unfold eps
  have : (2 / 3 : ℝ) ^ σ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma logX_nonneg (T σ : ℕ) (hX : 9 / 4 ≤ Xe T σ) : 0 ≤ Real.log (Xe T σ) := by
  have := log_ge _ hX
  linarith

lemma epsn_le (T σ : ℕ) (hX : 9 / 4 ≤ Xe T σ) :
    eps σ * (nEpoch T σ : ℝ) ≤ (8 * Real.log (Xe T σ) + 8) / eps σ := by
  have he := eps_pos σ
  have he3 := eps_le_third σ
  have hL := logX_nonneg T σ hX
  have hn : (nEpoch T σ : ℝ) ≤ 8 * ((eps σ)⁻¹ ^ 2 * Real.log (Xe T σ)) + 8 := by
    unfold nEpoch
    exact innerLen_le T (eps σ) hL
  have hq : (eps σ)⁻¹ ^ 2 * eps σ ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ he.ne']; simp
  rw [le_div_iff₀ he]
  have h2 : eps σ ^ 2 ≤ 1 := by nlinarith
  calc eps σ * (nEpoch T σ : ℝ) * eps σ = eps σ ^ 2 * (nEpoch T σ : ℝ) := by ring
    _ ≤ eps σ ^ 2 * (8 * ((eps σ)⁻¹ ^ 2 * Real.log (Xe T σ)) + 8) :=
        mul_le_mul_of_nonneg_left hn (pow_nonneg he.le 2)
    _ = 8 * Real.log (Xe T σ) * ((eps σ)⁻¹ ^ 2 * eps σ ^ 2) + 8 * eps σ ^ 2 := by ring
    _ ≤ 8 * Real.log (Xe T σ) + 8 := by rw [hq]; nlinarith

lemma succ_le_inv_eps (σ : ℕ) : (σ : ℝ) + 1 ≤ 1 / eps σ := by
  have key : ∀ m : ℕ, (m : ℝ) + 1 ≤ 2 * (3 / 2 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      push_cast
      rw [pow_succ]
      nlinarith
  have h3 : 1 / eps σ = 3 * (3 / 2 : ℝ) ^ σ := by
    unfold eps
    rw [one_div, mul_inv, ← inv_pow]
    norm_num
  rw [h3]
  have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ σ := one_le_pow₀ (by norm_num)
  linarith [key σ]

set_option maxHeartbeats 1000000 in
lemma Mj_term (T σ j : ℕ) (hX : 9 / 4 ≤ Xe T σ) :
    (2:ℝ) ^ (j + 3) * eps σ * (Mj T σ j : ℝ) ≤
      16 * ((2 * ((j : ℝ) + 1) + Real.log (Xe T σ)) * (1 / (2:ℝ)) ^ j) / eps σ + 16 := by
  have he := eps_pos σ
  have he' : eps σ ≠ 0 := he.ne'
  have hL := logX_nonneg T σ hX
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have hB : 0 ≤ 2 * ((j : ℝ) + 1) + Real.log (Xe T σ) := by linarith
  have hh : (0:ℝ) ≤ (1 / (2:ℝ)) ^ j := by positivity
  have hR : 0 ≤ 16 * ((2 * ((j : ℝ) + 1) + Real.log (Xe T σ)) * (1 / (2:ℝ)) ^ j) / eps σ :=
    div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hB hh)) he.le
  have hp : (0:ℝ) < 2 ^ (j + 1) := pow_pos two_pos _
  unfold Mj
  split_ifs with hc
  · have hXp : 0 < Xe T σ := by linarith
    have hY : 8 * (T : ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2 = (2:ℝ) ^ (2 * (j + 1)) * Xe T σ := by
      unfold Xe; ring
    have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlog : Real.log (8 * (T : ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2) =
        ((2 * (j + 1) : ℕ) : ℝ) * Real.log 2 + Real.log (Xe T σ) := by
      rw [hY, Real.log_mul (pow_pos two_pos _).ne' hXp.ne', Real.log_pow]
    have hc0 : (0:ℝ) ≤ ((2 * (j + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hLj0 : 0 ≤ Real.log (8 * (T : ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2) := by
      rw [hlog]
      have := mul_nonneg hc0 hl2'.le
      linarith
    have hLj : Real.log (8 * (T : ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2) ≤
        2 * ((j : ℝ) + 1) + Real.log (Xe T σ) := by
      rw [hlog]
      have h3 := mul_le_mul_of_nonneg_left hl1 hc0
      push_cast at h3 ⊢
      linarith
    have hn := innerLen_le T ((2:ℝ) ^ (j + 1) * eps σ) hLj0
    have h4 : (2:ℝ) ^ (j + 2) * eps σ = 4 * (2 ^ j * eps σ) := by ring
    have hc' : (2:ℝ) ^ j * eps σ ≤ 1 / 4 := by rw [h4] at hc; linarith
    have hid : ∀ Lj : ℝ, (2:ℝ) ^ (j + 3) * eps σ *
        (8 * (((2:ℝ) ^ (j + 1) * eps σ)⁻¹ ^ 2 * Lj) + 8) =
        16 * (Lj * (1 / (2:ℝ)) ^ j) / eps σ + 64 * (2 ^ j * eps σ) := by
      intro Lj
      simp only [one_div, inv_pow]
      field_simp
      ring
    have hfin : 16 * (Real.log (8 * (T : ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2) *
          (1 / (2:ℝ)) ^ j) / eps σ ≤
        16 * ((2 * ((j : ℝ) + 1) + Real.log (Xe T σ)) * (1 / (2:ℝ)) ^ j) / eps σ := by
      apply div_le_div_of_nonneg_right _ he.le
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLj hh) (by norm_num)
    calc (2:ℝ) ^ (j + 3) * eps σ * ((innerLen T ((2:ℝ) ^ (j + 1) * eps σ) : ℕ) : ℝ)
        ≤ (2:ℝ) ^ (j + 3) * eps σ * (8 * (((2:ℝ) ^ (j + 1) * eps σ)⁻¹ ^ 2 *
            Real.log (8 * (T : ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2)) + 8) :=
          mul_le_mul_of_nonneg_left hn (mul_nonneg (pow_pos two_pos _).le he.le)
      _ = _ := hid _
      _ ≤ _ := by linarith
  · simp only [Nat.cast_zero, mul_zero]
    linarith

lemma sum_jhalf (L : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (2 * ((j : ℝ) + 1) + L) * (1 / (2:ℝ)) ^ j +
      (4 * (m : ℝ) + 8 + 2 * L) * (1 / (2:ℝ)) ^ m = 8 + 2 * L := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    ring

lemma sum_jhalf_le (L : ℝ) (hL : 0 ≤ L) (m : ℕ) :
    ∑ j ∈ Finset.range m, (2 * ((j : ℝ) + 1) + L) * (1 / (2:ℝ)) ^ j ≤ 8 + 2 * L := by
  have h := sum_jhalf L m
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have : 0 ≤ (4 * (m : ℝ) + 8 + 2 * L) * (1 / (2:ℝ)) ^ m :=
    mul_nonneg (by linarith) (by positivity)
  linarith

lemma sum_half_div (K e : ℝ) (hK : 0 ≤ K) (he : 0 < e) (m : ℕ) :
    ∑ j ∈ Finset.range m, K * (1 / (2:ℝ)) ^ j / e ≤ 2 * K / e := by
  rw [← Finset.sum_div, ← Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ he.le
  have := sum_geometric_two_le m
  nlinarith

lemma geom_set (S : Finset ℕ) (z : ℕ → ℝ) (q : ℝ) (hq : 6 / 5 ≤ q) (hz0 : ∀ σ, 0 ≤ z σ)
    (hrec : ∀ σ, z (σ + 1) = q * z σ) (hb : ∀ σ ∈ S, z σ ≤ 1) :
    ∑ σ ∈ S, z σ ≤ 6 := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  have hsub : S ⊆ Finset.range (S.max' hS + 1) := fun σ hσ =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_max' S σ hσ))
  have htel : ∀ m : ℕ, (q - 1) * ∑ σ ∈ Finset.range m, z σ = z m - z 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih, hrec]; ring
  have h1 := htel (S.max' hS + 1)
  have hM := hb _ (S.max'_mem hS)
  have hz00 := hz0 0
  have hsum : ∑ σ ∈ S, z σ ≤ ∑ σ ∈ Finset.range (S.max' hS + 1), z σ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun σ _ _ => hz0 σ)
  rw [hrec] at h1
  have hq0 : 0 ≤ q := by linarith
  have h2 : (q - 1) * ∑ σ ∈ Finset.range (S.max' hS + 1), z σ ≤ q := by
    rw [h1]; nlinarith [mul_le_mul_of_nonneg_left hM hq0]
  have h3 : ∑ σ ∈ Finset.range (S.max' hS + 1), z σ ≤ 6 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon (by linarith : (0:ℝ) < q - 1)]
  linarith

noncomputable def uu (T σ : ℕ) : ℝ := Real.sqrt (1 / (Real.sqrt (8 * (T : ℝ)) * eps σ))

lemma uu_rec (T σ : ℕ) : uu T (σ + 1) = Real.sqrt (3 / 2) * uu T σ := by
  unfold uu
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3 / 2)]
  congr 1
  rw [eps_succ, show Real.sqrt (8 * (T:ℝ)) * (2 / 3 * eps σ) =
    2 / 3 * (Real.sqrt (8 * (T:ℝ)) * eps σ) by ring, one_div, one_div, mul_inv]
  norm_num

lemma term_le_uu (T σ : ℕ) (hX : 9 / 4 ≤ Xe T σ) :
    (1 + Real.log (Xe T σ)) / eps σ ≤ 5 * Real.sqrt (8 * (T : ℝ)) * uu T σ ∧ uu T σ ≤ 1 := by
  have he := eps_pos σ
  have huu : uu T σ = 1 / Real.sqrt (Real.sqrt (8 * (T : ℝ)) * eps σ) := by
    unfold uu; rw [one_div, Real.sqrt_inv, one_div]
  have hs2 : Real.sqrt (8 * (T : ℝ)) ^ 2 = 8 * (T : ℝ) := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (8 * (T : ℝ)) := Real.sqrt_nonneg _
  set s := Real.sqrt (8 * (T : ℝ)) with hs
  have hXY : Xe T σ = (s * eps σ) ^ 2 := by
    unfold Xe; rw [mul_pow, hs2]
  have hY0 : 0 ≤ s * eps σ := mul_nonneg hs0 he.le
  have hY32 : 3 / 2 ≤ s * eps σ := by nlinarith
  have hw2 : Real.sqrt (s * eps σ) ^ 2 = s * eps σ := Real.sq_sqrt hY0
  have hw0 : 0 ≤ Real.sqrt (s * eps σ) := Real.sqrt_nonneg _
  set w := Real.sqrt (s * eps σ) with hw
  have hw1 : 1 ≤ w := by nlinarith
  have hwpos : 0 < w := by linarith
  have hlogX : Real.log (Xe T σ) ≤ 4 * w := by
    rw [hXY, ← hw2, ← pow_mul, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hwpos
    push_cast
    linarith
  have hkey : 5 * s * (1 / w) * eps σ = 5 * w := by
    have hw' : w ≠ 0 := hwpos.ne'
    calc 5 * s * (1 / w) * eps σ = 5 * (s * eps σ) / w := by ring
      _ = 5 * (w ^ 2) / w := by rw [hw2]
      _ = 5 * w := by first | (field_simp; ring) | field_simp
  constructor
  · rw [huu, div_le_iff₀ he, hkey]
    linarith
  · rw [huu, div_le_one hwpos]
    exact hw1

noncomputable def Qs (v r : Fin N → ℝ) (T σ : ℕ) (h : History N T) : ℝ :=
  (T : ℝ) * (eps σ * ind (WBev v r T σ h)) + (T : ℝ) * Gs v r T σ h +
    (14 * eps σ * nEpoch T σ + ∑ j ∈ Finset.range (σ + 1),
      2 ^ (j + 3) * eps σ * (Mj T σ j + T * ind (EVev v r T σ j h)))

lemma BGE_eq (v r : Fin N → ℝ) (T : ℕ) (h : History N T) :
    (T : ℝ) * BBh v r T h + (T : ℝ) * GGh v r T h + EEh v r T h =
      ∑ σ ∈ Sset T, Qs v r T σ h := by
  unfold BBh GGh EEh Qs
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

set_option maxHeartbeats 1000000 in
lemma sigma_exp (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (T σ : ℕ) (hT : 0 < T) (hX : 9 / 4 ≤ Xe T σ) :
    ∑ h : History N T, histProb v (adaptivePolicy r T) h * Qs v r T σ h ≤
      300 * (1 + Real.log (Xe T σ)) / eps σ := by
  have hTr : (0:ℝ) < T := by exact_mod_cast hT
  have hT' : (T:ℝ) ≠ 0 := hTr.ne'
  have he := eps_pos σ
  have he' : eps σ ≠ 0 := he.ne'
  have hL := logX_nonneg T σ hX
  have hdec : ∀ h : History N T, Qs v r T σ h =
      (14 * (eps σ * (nEpoch T σ : ℝ)) +
        ∑ j ∈ Finset.range (σ + 1), (2:ℝ) ^ (j + 3) * eps σ * (Mj T σ j : ℝ)) +
      ((T:ℝ) * eps σ) * ind (WBev v r T σ h) +
      ∑ j ∈ Finset.range (σ + 2), ((T:ℝ) * 2 ^ (j + 1) * eps σ) *
        ind (WAev v r T σ ((2 ^ j - 1) * eps σ) h) +
      ∑ j ∈ Finset.range (σ + 1), ((2:ℝ) ^ (j + 3) * eps σ * T) * ind (EVev v r T σ j h) := by
    intro h
    have hG : (T:ℝ) * Gs v r T σ h = ∑ j ∈ Finset.range (σ + 2), ((T:ℝ) * 2 ^ (j + 1) * eps σ) *
        ind (WAev v r T σ ((2 ^ j - 1) * eps σ) h) := by
      unfold Gs; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    have hE : ∑ j ∈ Finset.range (σ + 1), (2:ℝ) ^ (j + 3) * eps σ *
          ((Mj T σ j : ℝ) + (T:ℝ) * ind (EVev v r T σ j h)) =
        ∑ j ∈ Finset.range (σ + 1), (2:ℝ) ^ (j + 3) * eps σ * (Mj T σ j : ℝ) +
        ∑ j ∈ Finset.range (σ + 1), ((2:ℝ) ^ (j + 3) * eps σ * T) * ind (EVev v r T σ j h) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun j _ => by ring)
    unfold Qs
    rw [hG, hE]
    ring
  have eq1 : ∑ h : History N T, histProb v (adaptivePolicy r T) h * Qs v r T σ h =
      (14 * (eps σ * (nEpoch T σ : ℝ)) +
        ∑ j ∈ Finset.range (σ + 1), (2:ℝ) ^ (j + 3) * eps σ * (Mj T σ j : ℝ)) +
      ((T:ℝ) * eps σ) * probT v (adaptivePolicy r T) T (WBev v r T σ) +
      ∑ j ∈ Finset.range (σ + 2), ((T:ℝ) * 2 ^ (j + 1) * eps σ) *
        probT v (adaptivePolicy r T) T (WAev v r T σ ((2 ^ j - 1) * eps σ)) +
      ∑ j ∈ Finset.range (σ + 1), ((2:ℝ) ^ (j + 3) * eps σ * T) *
        probT v (adaptivePolicy r T) T (EVev v r T σ j) := by
    simp_rw [hdec]
    rw [E_split v hv (adaptivePolicy r T) T, E_one, E_lin, E_lin]
  rw [eq1]
  have hεn := epsn_le T σ hX
  have bA : ((T:ℝ) * eps σ) * probT v (adaptivePolicy r T) T (WBev v r T σ) ≤
      (eps σ * (nEpoch T σ : ℝ)) / 2 := by
    have pWB : probT v (adaptivePolicy r T) T (WBev v r T σ) ≤ (nEpoch T σ : ℝ) / (2 * T) :=
      prob_WB v r hv hr T σ hT
    calc _ ≤ ((T:ℝ) * eps σ) * ((nEpoch T σ : ℝ) / (2 * T)) :=
          mul_le_mul_of_nonneg_left pWB (mul_nonneg hTr.le he.le)
      _ = _ := by (try simp only [one_div, inv_pow]); first | (field_simp; ring) | field_simp
  have bB : ∑ j ∈ Finset.range (σ + 2), ((T:ℝ) * 2 ^ (j + 1) * eps σ) *
        probT v (adaptivePolicy r T) T (WAev v r T σ ((2 ^ j - 1) * eps σ)) ≤
      eps σ * (nEpoch T σ : ℝ) + 4 * (eps σ)⁻¹ := by
    rw [Finset.sum_range_succ']
    have p0 : probT v (adaptivePolicy r T) T (WAev v r T σ (((2:ℝ) ^ 0 - 1) * eps σ)) ≤
        (nEpoch T σ : ℝ) / (2 * T) := by
      have h0 : ((2:ℝ) ^ 0 - 1) * eps σ = 0 := by norm_num
      rw [h0]
      exact prob_WA0 v r hv hr T σ hT hX
    have t0 : (T:ℝ) * 2 ^ (0 + 1) * eps σ *
        probT v (adaptivePolicy r T) T (WAev v r T σ (((2:ℝ) ^ 0 - 1) * eps σ)) ≤
        eps σ * (nEpoch T σ : ℝ) := by
      calc _ ≤ (T:ℝ) * 2 ^ (0 + 1) * eps σ * ((nEpoch T σ : ℝ) / (2 * T)) :=
            mul_le_mul_of_nonneg_left p0 (mul_nonneg (mul_nonneg hTr.le (by norm_num)) he.le)
        _ = _ := by (try simp only [one_div, inv_pow]); first | (field_simp; ring) | field_simp
    have tj : ∀ j ∈ Finset.range (σ + 1), (T:ℝ) * 2 ^ (j + 1 + 1) * eps σ *
        probT v (adaptivePolicy r T) T (WAev v r T σ (((2:ℝ) ^ (j + 1) - 1) * eps σ)) ≤
        2 * (1 / (2:ℝ)) ^ j / eps σ := by
      intro j _
      have h1j : (1:ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have h2j : (2:ℝ) ^ j ≤ 2 ^ (j + 1) - 1 := by rw [pow_succ]; linarith
      have hpos : 0 < (2:ℝ) ^ j * eps σ := mul_pos (pow_pos two_pos j) he
      have hle : (2:ℝ) ^ j * eps σ ≤ ((2:ℝ) ^ (j + 1) - 1) * eps σ :=
        mul_le_mul_of_nonneg_right h2j he.le
      have hγ : 0 < ((2:ℝ) ^ (j + 1) - 1) * eps σ := lt_of_lt_of_le hpos hle
      have pj := prob_WA v r hv hr T σ hT hX _ hγ
      have hsq : ((2:ℝ) ^ j * eps σ) ^ 2 ≤ (((2:ℝ) ^ (j + 1) - 1) * eps σ) ^ 2 := by
        nlinarith
      have hb : 1 / (2 * (T:ℝ) * (((2:ℝ) ^ (j + 1) - 1) * eps σ) ^ 2) ≤
          1 / (2 * (T:ℝ) * ((2:ℝ) ^ j * eps σ) ^ 2) := by
        apply one_div_le_one_div_of_le (mul_pos (mul_pos two_pos hTr) (pow_pos hpos 2))
        exact mul_le_mul_of_nonneg_left hsq (by positivity)
      calc _ ≤ (T:ℝ) * 2 ^ (j + 1 + 1) * eps σ * (1 / (2 * (T:ℝ) * ((2:ℝ) ^ j * eps σ) ^ 2)) :=
            mul_le_mul_of_nonneg_left (pj.trans hb)
              (mul_nonneg (mul_nonneg hTr.le (by positivity)) he.le)
        _ = _ := by (try simp only [one_div, inv_pow]); first | (field_simp; ring) | field_simp
    have hS := Finset.sum_le_sum tj
    have hs := sum_half_div 2 (eps σ) (by norm_num) he (σ + 1)
    have hn4 : 2 * 2 / eps σ = 4 * (eps σ)⁻¹ := by ring
    calc _ ≤ 2 * 2 / eps σ + eps σ * (nEpoch T σ : ℝ) := add_le_add (hS.trans hs) t0
      _ = _ := by rw [hn4]; ring
  have bC : ∑ j ∈ Finset.range (σ + 1), ((2:ℝ) ^ (j + 3) * eps σ * T) *
        probT v (adaptivePolicy r T) T (EVev v r T σ j) ≤ 2 * (eps σ)⁻¹ := by
    have tE : ∀ j ∈ Finset.range (σ + 1), ((2:ℝ) ^ (j + 3) * eps σ * T) *
        probT v (adaptivePolicy r T) T (EVev v r T σ j) ≤ 1 * (1 / (2:ℝ)) ^ j / eps σ := by
      intro j _
      have hg : 0 < (2:ℝ) ^ (j + 1) * eps σ := mul_pos (pow_pos two_pos _) he
      have hc : 0 < 8 * (T:ℝ) := by positivity
      have pE : probT v (adaptivePolicy r T) T (EVev v r T σ j) ≤
          4 / (8 * (T:ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2) :=
        (peel v r hv hr (adaptivePolicy r T) (wE r T σ) (wE_mem r T σ) T 1 (by norm_num)
          _ _ hg.le hc (Nat.log 2 (nEpoch T σ))).trans (gap_sum _ _ hc hg _)
      calc _ ≤ ((2:ℝ) ^ (j + 3) * eps σ * T) * (4 / (8 * (T:ℝ) * ((2:ℝ) ^ (j + 1) * eps σ) ^ 2)) :=
            mul_le_mul_of_nonneg_left pE
              (mul_nonneg (mul_nonneg (by positivity) he.le) hTr.le)
        _ = _ := by (try simp only [one_div, inv_pow]); first | (field_simp; ring) | field_simp
    have hS := Finset.sum_le_sum tE
    have hs := sum_half_div 1 (eps σ) (by norm_num) he (σ + 1)
    have hn2 : 2 * 1 / eps σ = 2 * (eps σ)⁻¹ := by ring
    linarith
  have bM : ∑ j ∈ Finset.range (σ + 1), (2:ℝ) ^ (j + 3) * eps σ * (Mj T σ j : ℝ) ≤
      144 * (eps σ)⁻¹ + 32 * (Real.log (Xe T σ) * (eps σ)⁻¹) := by
    have h1 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (σ + 1)) => Mj_term T σ j hX)
    have h2 : ∑ j ∈ Finset.range (σ + 1), (16 * ((2 * ((j : ℝ) + 1) + Real.log (Xe T σ)) *
        (1 / (2:ℝ)) ^ j) / eps σ + 16) =
        16 * ((∑ j ∈ Finset.range (σ + 1), (2 * ((j : ℝ) + 1) + Real.log (Xe T σ)) *
          (1 / (2:ℝ)) ^ j) * (eps σ)⁻¹) + 16 * ((σ : ℝ) + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl (fun j _ => by ring)
      · push_cast; ring
    have h3 := sum_jhalf_le (Real.log (Xe T σ)) hL (σ + 1)
    have h4 := succ_le_inv_eps σ
    have h5 : 1 / eps σ = (eps σ)⁻¹ := one_div _
    have hi0 : 0 ≤ (eps σ)⁻¹ := inv_nonneg.2 he.le
    have h6 := mul_le_mul_of_nonneg_right h3 hi0
    have h7 : (8 + 2 * Real.log (Xe T σ)) * (eps σ)⁻¹ =
        8 * (eps σ)⁻¹ + 2 * (Real.log (Xe T σ) * (eps σ)⁻¹) := by ring
    rw [h2] at h1
    rw [h5] at h4
    linarith
  have hεn' : eps σ * (nEpoch T σ : ℝ) ≤
      8 * (Real.log (Xe T σ) * (eps σ)⁻¹) + 8 * (eps σ)⁻¹ := by
    calc _ ≤ _ := hεn
      _ = _ := by ring
  have n5 : 300 * (1 + Real.log (Xe T σ)) / eps σ =
      300 * (eps σ)⁻¹ + 300 * (Real.log (Xe T σ) * (eps σ)⁻¹) := by ring
  have hi0 : 0 ≤ (eps σ)⁻¹ := inv_nonneg.2 he.le
  have hLi : 0 ≤ Real.log (Xe T σ) * (eps σ)⁻¹ := mul_nonneg hL hi0
  rw [n5]
  linarith

lemma main_bound (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (T : ℕ) (hT : 3 ≤ T) :
    regret v r Finset.univ ⟨∅, Finset.mem_univ _⟩ (adaptivePolicy r T) T ≤
      27000 * Real.sqrt T := by
  have hT0 : 0 < T := by omega
  have hr0 : ∀ i, 0 ≤ r i := fun i => (hr i).1
  have hr1 : ∀ i, r i ≤ 1 := fun i => (hr i).2
  have hq : (6 / 5 : ℝ) ≤ Real.sqrt (3 / 2) := by
    rw [show (6 / 5 : ℝ) = Real.sqrt ((6 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h8 : Real.sqrt 8 ≤ 3 := by
    rw [show (3 : ℝ) = Real.sqrt (3 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs8 : Real.sqrt (8 * (T : ℝ)) = Real.sqrt 8 * Real.sqrt T :=
    Real.sqrt_mul (by norm_num) _
  have hsT := Real.sqrt_nonneg (T : ℝ)
  have hgeo : ∑ σ ∈ Sset T, uu T σ ≤ 6 :=
    geom_set (Sset T) (uu T) (Real.sqrt (3 / 2)) hq (fun σ => Real.sqrt_nonneg _)
      (fun σ => uu_rec T σ) (fun σ hσ => (term_le_uu T σ (Finset.mem_filter.1 hσ).2).2)
  rw [regret_eq v r hv]
  calc ∑ h : History N T, histProb v (adaptivePolicy r T) h *
        ∑ t : Fin T, (optRev v r - rev v r (offered (adaptivePolicy r T) h t))
      ≤ ∑ h : History N T, histProb v (adaptivePolicy r T) h * ∑ σ ∈ Sset T, Qs v r T σ h := by
        apply Finset.sum_le_sum
        intro h _
        apply mul_le_mul_of_nonneg_left _ (histProb_nonneg v hv _ h)
        rw [← BGE_eq]
        exact PH v r hv hr0 hr1 T hT h
    _ = ∑ σ ∈ Sset T, ∑ h : History N T, histProb v (adaptivePolicy r T) h * Qs v r T σ h := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ ∑ σ ∈ Sset T, 300 * (5 * Real.sqrt (8 * (T : ℝ)) * uu T σ) := by
        apply Finset.sum_le_sum
        intro σ hσ
        have hX := (Finset.mem_filter.1 hσ).2
        have h1 := sigma_exp v r hv hr T σ hT0 hX
        have h2 := (term_le_uu T σ hX).1
        have h3 : 300 * (1 + Real.log (Xe T σ)) / eps σ =
            300 * ((1 + Real.log (Xe T σ)) / eps σ) := by ring
        linarith
    _ = 1500 * Real.sqrt (8 * (T : ℝ)) * ∑ σ ∈ Sset T, uu T σ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun σ _ => by ring)
    _ ≤ 1500 * Real.sqrt (8 * (T : ℝ)) * 6 :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ ≤ 27000 * Real.sqrt T := by
        rw [hs8]
        nlinarith [mul_le_mul_of_nonneg_right h8 hsT]

end A6a3

open MNLBandit.UCB MNLTrisection.Adaptive in
theorem solution :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (N T : ℕ) (v r : Fin N → ℝ), (∀ i, 0 ≤ v i) →
      (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      regret v r (Finset.univ : Finset (Finset (Fin N))) ⟨∅, Finset.mem_univ _⟩
        (adaptivePolicy r T) T ≤ C₁ * Real.sqrt T := by
  refine ⟨27000, by norm_num, fun N T v r hv hr => ?_⟩
  have hr' : ∀ i, 0 ≤ r i ∧ r i ≤ 1 := fun i => hr i
  by_cases hT : 3 ≤ T
  · exact A6a3.main_bound v r hv hr' T hT
  · have h1 := A6a3.regret_le_T v r hv (fun i => (hr' i).1) (fun i => (hr' i).2)
      (adaptivePolicy r T) T
    have h2 := A6a3.le_two_sqrt T (by omega)
    have h3 := Real.sqrt_nonneg (T : ℝ)
    linarith

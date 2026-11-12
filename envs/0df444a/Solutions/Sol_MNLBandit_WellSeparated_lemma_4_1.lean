-- Prove2me | solution 1 for MNLBandit.WellSeparated.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T15:27:04.109194+00:00
-- url     : https://prove2.me/submissions/a2b8c5e1-9320-4e81-8611-166d23e36cd8

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting

set_option autoImplicit false

namespace B269

open MNLBandit.WellSeparated
open MNLBandit.UCB (AlgState EpochRecord TcountL vbarL vUCBL runAlg step initState optimisticSet
  choiceProb)

variable {N : ℕ}

/-! ### The history measure -/

lemma denom_pos (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    0 < 1 + ∑ j ∈ S, v j := by
  have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv j); linarith

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

lemma histPrefix_snoc_castSucc {T : ℕ} (h : Fin T → Option (Fin N)) (c : Option (Fin N))
    (t : Fin T) :
    histPrefix (Fin.snoc h c : Fin (T + 1) → Option (Fin N)) t.castSucc = histPrefix h t := by
  funext u
  show (Fin.snoc h c : Fin (T + 1) → Option (Fin N)) (Fin.castLE _ u) = h (Fin.castLE _ u)
  have : (Fin.castLE (t.castSucc).isLt.le u : Fin (T + 1)) =
      Fin.castSucc (Fin.castLE t.isLt.le u) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma histPrefix_snoc_last {T : ℕ} (h : Fin T → Option (Fin N)) (c : Option (Fin N)) :
    histPrefix (Fin.snoc h c : Fin (T + 1) → Option (Fin N)) (Fin.last T) = h := by
  funext u
  show (Fin.snoc h c : Fin (T + 1) → Option (Fin N)) (Fin.castLE _ u) = h u
  have : (Fin.castLE (Fin.last T).isLt.le u : Fin (T + 1)) = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma histProb_snoc (v : Fin N → ℝ) (π : MNLBandit.UCB.Policy N) {T : ℕ}
    (h : Fin T → Option (Fin N)) (c : Option (Fin N)) :
    histProb v π (T + 1) (Fin.snoc h c : Fin (T + 1) → Option (Fin N)) =
      histProb v π T h * choiceProb v (π T h) c := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  have e1 : ∀ t : Fin T, π (t.castSucc : Fin (T + 1)).val
      (histPrefix (Fin.snoc h c : Fin (T + 1) → Option (Fin N)) t.castSucc) =
        π t.val (histPrefix h t) :=
    fun t => congrArg (π t.val) (histPrefix_snoc_castSucc h c t)
  have e2 : π (Fin.last T).val
      (histPrefix (Fin.snoc h c : Fin (T + 1) → Option (Fin N)) (Fin.last T)) = π T h :=
    congrArg (π T) (histPrefix_snoc_last h c)
  simp only [e1, e2, Fin.snoc_castSucc, Fin.snoc_last]

lemma sum_hist_succ {T : ℕ} (f : (Fin (T + 1) → Option (Fin N)) → ℝ) :
    ∑ h : Fin (T + 1) → Option (Fin N), f h =
      ∑ h : Fin T → Option (Fin N), ∑ c : Option (Fin N), f (Fin.snoc h c) := by
  let e : (Fin T → Option (Fin N)) × Option (Fin N) ≃ (Fin (T + 1) → Option (Fin N)) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun h => (Fin.init h, h (Fin.last T))
      left_inv := fun p => by simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun h => by simp [Fin.snoc_init_self] }
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

lemma histProb_nonneg (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : MNLBandit.UCB.Policy N) {T : ℕ}
    (h : Fin T → Option (Fin N)) : 0 ≤ histProb v π T h :=
  Finset.prod_nonneg (fun t _ => choiceProb_nonneg v hv _ _)

lemma ofFn_snoc {α : Type} {T : ℕ} (h : Fin T → α) (c : α) :
    List.ofFn (Fin.snoc h c : Fin (T + 1) → α) = List.ofFn h ++ [c] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma runAlg_append (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (l : List (Option (Fin N))) (c : Option (Fin N)) :
    runAlg r sel (l ++ [c]) = step r sel (runAlg r sel l) c := by
  simp [runAlg, List.foldl_append]

/-! ### The exponential potential -/

lemma take_snoc {α : Type} (l : List α) (x : α) (ℓ : ℕ) :
    (l ++ [x]).take ℓ = if l.length < ℓ then l.take ℓ ++ [x] else l.take ℓ := by
  rw [List.take_append]
  split_ifs with h
  · obtain ⟨k, hk⟩ : ∃ k, ℓ - l.length = k + 1 := ⟨ℓ - l.length - 1, by omega⟩
    rw [hk]; simp
  · rw [show ℓ - l.length = 0 by omega]; simp

def Acnt (ℓ : ℕ) (i : Fin N) (past : List (EpochRecord N)) : ℕ :=
  (((past.take ℓ).filter (fun e => decide (i ∈ e.1))).map (fun e => e.2 i)).sum

def Aof (ℓ : ℕ) (i : Fin N) (s : AlgState N) : ℕ :=
  Acnt ℓ i s.past + (if s.past.length < ℓ ∧ i ∈ s.cur then s.counts i else 0)

def Bof (ℓ : ℕ) (i : Fin N) (s : AlgState N) : ℕ := TcountL (s.past.take ℓ) i

noncomputable def Kf (v : Fin N → ℝ) (i : Fin N) (θ : ℝ) : ℝ := 1 + v i - v i * Real.exp θ

noncomputable def Phi (v : Fin N → ℝ) (ℓ : ℕ) (i : Fin N) (θ : ℝ) (s : AlgState N) : ℝ :=
  Real.exp (θ * (Aof ℓ i s : ℝ)) * Kf v i θ ^ (Bof ℓ i s)

noncomputable def gval (v : Fin N → ℝ) (i : Fin N) (θ : ℝ) : Option (Fin N) → ℝ
  | none => Kf v i θ
  | some j => if j = i then Real.exp θ else 1

noncomputable def gfac (v : Fin N → ℝ) (ℓ : ℕ) (i : Fin N) (θ : ℝ) (s : AlgState N)
    (c : Option (Fin N)) : ℝ :=
  if s.past.length < ℓ ∧ i ∈ s.cur then gval v i θ c else 1

lemma Aof_none (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (ℓ : ℕ)
    (i : Fin N) (s : AlgState N) : Aof ℓ i (step r sel s none) = Aof ℓ i s := by
  simp only [step, Aof, Acnt, take_snoc]
  by_cases hl : s.past.length < ℓ
  · by_cases hi : i ∈ s.cur
    · simp [hl, hi, List.filter_append, List.filter_cons]
    · simp [hl, hi, List.filter_append, List.filter_cons]
  · simp [hl]

lemma Bof_none (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (ℓ : ℕ)
    (i : Fin N) (s : AlgState N) : Bof ℓ i (step r sel s none) =
      Bof ℓ i s + (if s.past.length < ℓ ∧ i ∈ s.cur then 1 else 0) := by
  simp only [step, Bof, TcountL, take_snoc]
  by_cases hl : s.past.length < ℓ
  · by_cases hi : i ∈ s.cur
    · simp [hl, hi, List.filter_append, List.filter_cons]
    · simp [hl, hi, List.filter_append, List.filter_cons]
  · simp [hl]

lemma Aof_some (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (ℓ : ℕ)
    (i : Fin N) (s : AlgState N) (j : Fin N) : Aof ℓ i (step r sel s (some j)) =
      Aof ℓ i s + (if (s.past.length < ℓ ∧ i ∈ s.cur) ∧ j = i then 1 else 0) := by
  show Acnt ℓ i s.past + (if s.past.length < ℓ ∧ i ∈ s.cur then
      Function.update s.counts j (s.counts j + 1) i else 0) = _
  unfold Aof
  by_cases hc : s.past.length < ℓ ∧ i ∈ s.cur
  · by_cases hj : j = i
    · subst hj; simp [hc]; omega
    · simp [hc, hj, Function.update_apply, Ne.symm hj]
  · simp [hc]

lemma Bof_some (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (ℓ : ℕ)
    (i : Fin N) (s : AlgState N) (j : Fin N) : Bof ℓ i (step r sel s (some j)) = Bof ℓ i s :=
  rfl

lemma Phi_step (v : Fin N → ℝ) (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (ℓ : ℕ) (i : Fin N) (θ : ℝ) (s : AlgState N) (c : Option (Fin N)) :
    Phi v ℓ i θ (step r sel s c) = Phi v ℓ i θ s * gfac v ℓ i θ s c := by
  unfold Phi gfac
  by_cases hc : s.past.length < ℓ ∧ i ∈ s.cur
  · cases c with
    | none =>
      rw [Aof_none, Bof_none, if_pos hc, if_pos hc, pow_succ]
      simp only [gval]; ring
    | some j =>
      rw [Aof_some, Bof_some, if_pos hc]
      by_cases hj : j = i
      · rw [if_pos ⟨hc, hj⟩]; simp only [gval, if_pos hj]; push_cast
        rw [mul_add, Real.exp_add, mul_one]; ring
      · rw [if_neg (fun h => hj h.2), add_zero]; simp only [gval, if_neg hj, mul_one]
  · rw [if_neg hc, mul_one]
    cases c with
    | none => rw [Aof_none, Bof_none, if_neg hc, add_zero]
    | some j => rw [Aof_some, Bof_some, if_neg (fun h => hc h.1), add_zero]

lemma gsum (v : Fin N → ℝ) (hv : ∀ j, 0 ≤ v j) (ℓ : ℕ) (i : Fin N) (θ : ℝ) (s : AlgState N) :
    ∑ c : Option (Fin N), choiceProb v s.cur c * gfac v ℓ i θ s c = 1 := by
  unfold gfac
  by_cases hc : s.past.length < ℓ ∧ i ∈ s.cur
  · simp only [if_pos hc]
    have hD : (1 + ∑ j ∈ s.cur, v j) ≠ 0 := (denom_pos v hv s.cur).ne'
    rw [Fintype.sum_option]
    simp only [choiceProb, gval]
    have key : ∀ j : Fin N,
        (if j ∈ s.cur then v j / (1 + ∑ j ∈ s.cur, v j) else 0) *
            (if j = i then Real.exp θ else 1)
          = (if j ∈ s.cur then v j / (1 + ∑ j ∈ s.cur, v j) else 0) +
            (if j = i then v i / (1 + ∑ j ∈ s.cur, v j) * (Real.exp θ - 1) else 0) := by
      intro j
      by_cases hj : j = i
      · subst hj; rw [if_pos hc.2, if_pos rfl, if_pos rfl]; ring
      · rw [if_neg hj, if_neg hj, mul_one, add_zero]
    rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, Finset.sum_ite_eq']
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
    simp only [Finset.mem_univ, if_true]
    unfold Kf
    field_simp
    ring
  · simp only [if_neg hc, mul_one]
    exact choiceProb_sum v hv s.cur

lemma EPhi (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (hv : ∀ j, 0 ≤ v j)
    (ℓ : ℕ) (i : Fin N) (θ : ℝ) (T : ℕ) :
    ∑ h : Fin T → Option (Fin N),
      histProb v (alg1 r sel) T h * Phi v ℓ i θ (runAlg r sel (List.ofFn h)) = 1 := by
  induction T with
  | zero =>
    simp [histProb, Phi, Aof, Bof, Acnt, TcountL, runAlg, initState]
  | succ T ih =>
    rw [sum_hist_succ, ← ih]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    simp only [histProb_snoc, ofFn_snoc, runAlg_append, Phi_step]
    have hc : alg1 r sel T h = (runAlg r sel (List.ofFn h)).cur := rfl
    rw [hc]
    calc ∑ c : Option (Fin N), histProb v (alg1 r sel) T h *
            choiceProb v (runAlg r sel (List.ofFn h)).cur c *
            (Phi v ℓ i θ (runAlg r sel (List.ofFn h)) *
              gfac v ℓ i θ (runAlg r sel (List.ofFn h)) c)
        = histProb v (alg1 r sel) T h * Phi v ℓ i θ (runAlg r sel (List.ofFn h)) *
            ∑ c : Option (Fin N), choiceProb v (runAlg r sel (List.ofFn h)).cur c *
              gfac v ℓ i θ (runAlg r sel (List.ofFn h)) c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun c _ => by ring)
      _ = _ := by rw [gsum v hv, mul_one]

lemma Phi_nonneg (v : Fin N → ℝ) (ℓ : ℕ) (i : Fin N) (θ : ℝ) (hK : 0 < Kf v i θ)
    (s : AlgState N) : 0 ≤ Phi v ℓ i θ s :=
  mul_nonneg (Real.exp_pos _).le (pow_nonneg hK.le _)

lemma probT_le_of_Phi {T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv : ∀ j, 0 ≤ v j) (ℓ : ℕ) (i : Fin N) (θ : ℝ) (hK : 0 < Kf v i θ)
    (E : (Fin T → Option (Fin N)) → Prop) (L : ℝ)
    (hE : ∀ h, E h → Real.exp (2 * L) ≤ Phi v ℓ i θ (runAlg r sel (List.ofFn h))) :
    probT v (alg1 r sel) T E ≤ Real.exp (-(2 * L)) := by
  classical
  have hsum := EPhi v r sel hv ℓ i θ T
  have hpos := Real.exp_pos (2 * L)
  rw [Real.exp_neg, ← one_div, le_div_iff₀ hpos]
  unfold probT
  rw [Finset.sum_mul]
  refine le_trans (Finset.sum_le_sum fun h _ => ?_) hsum.le
  have hp := histProb_nonneg v hv (alg1 r sel) h
  split_ifs with hh
  · exact mul_le_mul_of_nonneg_left (hE h hh) hp
  · rw [zero_mul]; exact mul_nonneg hp (Phi_nonneg v ℓ i θ hK _)

lemma probT_union {T : ℕ} (v : Fin N → ℝ) (hv : ∀ j, 0 ≤ v j) (π : MNLBandit.UCB.Policy N)
    (E : (Fin T → Option (Fin N)) → Prop) (F : ℕ → (Fin T → Option (Fin N)) → Prop)
    (S : Finset ℕ) (hcov : ∀ h, E h → ∃ m ∈ S, F m h) :
    probT v π T E ≤ ∑ m ∈ S, probT v π T (F m) := by
  classical
  unfold probT
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h _
  have hp := histProb_nonneg v hv π h
  split_ifs with hE
  · obtain ⟨m, hm, hF⟩ := hcov h hE
    have := Finset.single_le_sum
      (f := fun m' => if F m' h then histProb v π T h else 0)
      (fun m' _ => by split_ifs <;> linarith) hm
    simp only [if_pos hF] at this
    exact this
  · exact Finset.sum_nonneg (fun m' _ => by split_ifs <;> linarith)

/-! ### Final-state bookkeeping -/

lemma vbar_eq (l : List (EpochRecord N)) (ℓ : ℕ) (i : Fin N) :
    vbarL (l.take ℓ) i = (Acnt ℓ i l : ℝ) / (TcountL (l.take ℓ) i : ℝ) := by
  unfold vbarL Acnt
  rw [Nat.cast_list_sum, List.map_map]
  rfl

lemma Bof_le (ℓ : ℕ) (i : Fin N) (s : AlgState N) : Bof ℓ i s ≤ ℓ :=
  (List.length_filter_le _ _).trans (List.length_take_le _ _)

lemma Phi_final (v : Fin N → ℝ) (ℓ : ℕ) (i : Fin N) (θ : ℝ) (s : AlgState N)
    (hl : ℓ ≤ s.past.length) :
    Phi v ℓ i θ s = Real.exp (θ * (Acnt ℓ i s.past : ℝ)) * Kf v i θ ^ (Bof ℓ i s) := by
  unfold Phi Aof
  rw [if_neg (fun h => absurd h.1 (not_lt.mpr hl)), add_zero]

lemma vUCB_eq {T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : Fin T → Option (Fin N)) (i : Fin N) (ℓ : ℕ)
    (hl : ℓ ≤ (runAlg r sel (List.ofFn h)).past.length)
    (h0 : Bof ℓ i (runAlg r sel (List.ofFn h)) ≠ 0) :
    vUCB r sel h i ℓ =
      (Acnt ℓ i (runAlg r sel (List.ofFn h)).past : ℝ) / (Bof ℓ i (runAlg r sel (List.ofFn h)) : ℝ)
      + Real.sqrt ((Acnt ℓ i (runAlg r sel (List.ofFn h)).past : ℝ) /
          (Bof ℓ i (runAlg r sel (List.ofFn h)) : ℝ)
          * (48 * Real.log (Real.sqrt N * ℓ + 1)) / (Bof ℓ i (runAlg r sel (List.ofFn h)) : ℝ))
      + 48 * Real.log (Real.sqrt N * ℓ + 1) / (Bof ℓ i (runAlg r sel (List.ofFn h)) : ℝ) := by
  have hlen : ((runAlg r sel (List.ofFn h)).past.take ℓ).length = ℓ := by
    rw [List.length_take]; omega
  show vUCBL ((runAlg r sel (List.ofFn h)).past.take ℓ) i = _
  unfold vUCBL
  rw [if_neg (show ¬ TcountL ((runAlg r sel (List.ofFn h)).past.take ℓ) i = 0 from h0), hlen,
    vbar_eq]
  rfl

def Inv (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (s : AlgState N) : Prop :=
  (∀ k (hk : k < s.past.length), (s.past[k]).1 = optimisticSet r sel (s.past.take k)) ∧
    s.cur = optimisticSet r sel s.past

lemma Inv_step (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (s : AlgState N)
    (hs : Inv r sel s) (c : Option (Fin N)) : Inv r sel (step r sel s c) := by
  cases c with
  | none =>
    refine ⟨?_, rfl⟩
    intro k hk
    simp only [step] at hk ⊢
    rw [List.length_append, List.length_singleton] at hk
    by_cases hkl : k < s.past.length
    · rw [List.getElem_append_left hkl, List.take_append_of_le_length hkl.le]
      exact hs.1 k hkl
    · have hk' : k = s.past.length := by omega
      subst hk'
      simp [List.getElem_append, List.take_append, hs.2]
  | some j => exact hs

lemma Inv_foldl (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
    ∀ (l : List (Option (Fin N))) (s : AlgState N), Inv r sel s →
      Inv r sel (l.foldl (step r sel) s) := by
  intro l
  induction l with
  | nil => intro s hs; exact hs
  | cons c l ih => intro s hs; exact ih _ (Inv_step r sel s hs c)

lemma Inv_runAlg (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (l : List (Option (Fin N))) : Inv r sel (runAlg r sel l) :=
  Inv_foldl r sel l _ ⟨fun k hk => absurd hk (by simp [initState]), rfl⟩

lemma TcountL_snoc (l : List (EpochRecord N)) (x : EpochRecord N) (i : Fin N) :
    TcountL (l ++ [x]) i = TcountL l i + (if i ∈ x.1 then 1 else 0) := by
  unfold TcountL
  by_cases hx : i ∈ x.1 <;> simp [hx, List.filter_append, List.filter_cons]

lemma Tcount_eq {T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : Fin T → Option (Fin N)) (i : Fin N) :
    ∀ ℓ, ℓ ≤ (runAlg r sel (List.ofFn h)).past.length →
      Tcount r sel h i ℓ = Bof ℓ i (runAlg r sel (List.ofFn h)) := by
  have hinv := Inv_runAlg r sel (List.ofFn h)
  intro ℓ
  induction ℓ with
  | zero => intro _; simp [Tcount, Bof, TcountL]
  | succ k ih =>
    intro hk
    have hk' : k < (runAlg r sel (List.ofFn h)).past.length := by omega
    have ih' := ih hk'.le
    unfold Tcount Bof at ih' ⊢
    rw [Finset.card_filter] at ih' ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih', List.take_succ,
      List.getElem?_eq_getElem hk', Option.toList_some, TcountL_snoc]
    congr 1
    have : epochSet r sel h (k + 1) = ((runAlg r sel (List.ofFn h)).past[k]).1 := by
      rw [hinv.1 k hk']; simp [epochSet, completedEpochs]
    rw [this]

/-! ### Analytic inequalities -/

lemma LK1 (v μ : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    v * μ - 2 * v * μ ^ 2 ≤ Real.log (1 + v - v * Real.exp (-μ)) := by
  have habs := Real.abs_exp_sub_one_sub_id_le (x := -μ)
    (by rw [abs_neg, abs_of_nonneg hμ0]; exact hμ1)
  have hup : Real.exp (-μ) ≤ 1 - μ + μ ^ 2 := by
    have := (abs_le.mp habs).2; nlinarith
  have hlow : 1 - μ ≤ Real.exp (-μ) := by have := Real.add_one_le_exp (-μ); linarith
  have he1 : Real.exp (-μ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  set z := v * (1 - Real.exp (-μ)) with hz
  have hz0 : 0 ≤ z := mul_nonneg hv0 (by linarith)
  have hzlo : v * (μ - μ ^ 2) ≤ z := mul_le_mul_of_nonneg_left (by linarith) hv0
  have hzhi : z ≤ v * μ := mul_le_mul_of_nonneg_left (by linarith) hv0
  have hK : 1 + v - v * Real.exp (-μ) = 1 + z := by rw [hz]; ring
  rw [hK]
  have hz1 : 0 < 1 + z := by linarith
  have hlog : 1 - (1 + z)⁻¹ ≤ Real.log (1 + z) := Real.one_sub_inv_le_log_of_pos hz1
  have h1 : (1 + z)⁻¹ * (1 + z) = 1 := inv_mul_cancel₀ hz1.ne'
  have h2 : 0 < (1 + z)⁻¹ := inv_pos.mpr hz1
  have hinv : (1 + z)⁻¹ ≤ 1 - z + z ^ 2 := by
    nlinarith [pow_nonneg hz0 3, mul_pos h2 hz1]
  have hz2 : z ^ 2 ≤ v * μ ^ 2 := by
    have : z ^ 2 ≤ (v * μ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hv0 (sub_nonneg.2 hv1)) (sq_nonneg μ)]
  nlinarith

lemma LK2 (v θ : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1 / 9) :
    -(v * θ) - 3 * v * θ ^ 2 ≤ Real.log (1 + v - v * Real.exp θ) ∧
      0 < 1 + v - v * Real.exp θ := by
  have habs := Real.abs_exp_sub_one_sub_id_le (x := θ) (by rw [abs_of_nonneg hθ0]; linarith)
  have hup : Real.exp θ ≤ 1 + θ + θ ^ 2 := by have := (abs_le.mp habs).2; linarith
  have hlow : θ + 1 ≤ Real.exp θ := Real.add_one_le_exp θ
  set w := v * (Real.exp θ - 1) with hw
  have hw0 : 0 ≤ w := mul_nonneg hv0 (by linarith)
  have hθθ : θ + θ ^ 2 ≤ 10 / 9 * θ := by nlinarith
  have hwhi : w ≤ v * (θ + θ ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hv0
  have hwhi' : w ≤ 10 / 9 * (v * θ) := by nlinarith
  have hw13 : w ≤ 1 / 3 := by nlinarith
  have hK : 1 + v - v * Real.exp θ = 1 - w := by rw [hw]; ring
  rw [hK]
  have hKpos : 0 < 1 - w := by linarith
  refine ⟨?_, hKpos⟩
  have hlog : 1 - (1 - w)⁻¹ ≤ Real.log (1 - w) := Real.one_sub_inv_le_log_of_pos hKpos
  have h1 : (1 - w)⁻¹ * (1 - w) = 1 := inv_mul_cancel₀ hKpos.ne'
  have h2 : 0 < (1 - w)⁻¹ := inv_pos.mpr hKpos
  have hinv : (1 - w)⁻¹ ≤ 1 + w + 3 / 2 * w ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg w) (by linarith : (0:ℝ) ≤ 1 / 2 - 3 / 2 * w),
      mul_pos h2 hKpos]
  have hw2 : w ^ 2 ≤ 100 / 81 * v * θ ^ 2 := by
    have : w ^ 2 ≤ (10 / 9 * (v * θ)) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hv0 (sub_nonneg.2 hv1)) (sq_nonneg θ)]
  nlinarith [mul_nonneg hv0 (sq_nonneg θ)]

lemma part1_core (v A m L : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hm : 0 < m) (hL : 0 < L)
    (hA : 0 ≤ A) (hev : A / m + Real.sqrt (A / m * (48 * L) / m) + 48 * L / m < v) :
    2 * L ≤ -Real.sqrt (L / m / v) * A +
      m * Real.log (1 + v - v * Real.exp (-Real.sqrt (L / m / v))) := by
  have hA' : A = A / m * m := (div_mul_cancel₀ A hm.ne').symm
  have hL' : L = L / m * m := (div_mul_cancel₀ L hm.ne').symm
  have e2 : A / m * (48 * L) / m = 48 * (A / m) * (L / m) := by ring
  have e4 : 48 * L / m = 48 * (L / m) := by ring
  rw [e2, e4] at hev
  set y := L / m with hy
  set u := A / m with hu
  have hy0 : 0 < y := div_pos hL hm
  have hu0 : 0 ≤ u := div_nonneg hA hm.le
  set w := Real.sqrt (48 * u * y) with hwdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = 48 * u * y := Real.sq_sqrt (by positivity)
  have hvpos : 0 < v := by linarith
  have hdw : w ≤ v - u := by linarith
  have h48 : 48 * y ≤ v - u := by linarith
  have hd0 : 0 ≤ v - u := by linarith
  have hd2 : 24 * v * y ≤ (v - u) ^ 2 := by
    nlinarith [mul_le_mul hdw hdw hw0 hd0, mul_le_mul_of_nonneg_left h48 hd0]
  set μ := Real.sqrt (y / v) with hμ
  have hμ0 : 0 ≤ μ := Real.sqrt_nonneg _
  have hμ2 : μ ^ 2 = y / v := Real.sq_sqrt (by positivity)
  have hyv : y ≤ v := by linarith
  have hμ1 : μ ≤ 1 := by
    have : μ ^ 2 ≤ 1 := by rw [hμ2, div_le_one hvpos]; exact hyv
    nlinarith
  have hvμ2 : v * μ ^ 2 = y := by rw [hμ2]; field_simp
  have hX2 : v * (μ * (v - u)) ^ 2 = y * (v - u) ^ 2 := by rw [← hvμ2]; ring
  have hX : 24 * y ^ 2 ≤ (μ * (v - u)) ^ 2 := by
    have h1 : v * (24 * y ^ 2) ≤ v * (μ * (v - u)) ^ 2 := by
      rw [hX2]; nlinarith [mul_le_mul_of_nonneg_left hd2 hy0.le]
    exact le_of_mul_le_mul_left h1 hvpos
  have hμd : 4 * y ≤ μ * (v - u) := by
    nlinarith [mul_nonneg hμ0 hd0, mul_pos hy0 hy0]
  have hlog := LK1 v μ hv0 hv1 hμ0 hμ1
  have hper : 2 * y ≤ -μ * u + Real.log (1 + v - v * Real.exp (-μ)) := by nlinarith
  calc 2 * L = m * (2 * y) := by rw [hL']; ring
    _ ≤ m * (-μ * u + Real.log (1 + v - v * Real.exp (-μ))) :=
        mul_le_mul_of_nonneg_left hper hm.le
    _ = -μ * A + m * Real.log (1 + v - v * Real.exp (-μ)) := by rw [hA']; ring

noncomputable def lam2 (v y : ℝ) : ℝ :=
  (5 * Real.sqrt (v * y) + 36 * y) / (6 * v + 9 * (5 * Real.sqrt (v * y) + 36 * y))

lemma lam2_bd (v y : ℝ) (hv0 : 0 ≤ v) (hy : 0 < y) : 0 < lam2 v y ∧ lam2 v y ≤ 1 / 9 := by
  unfold lam2
  have hs := Real.sqrt_nonneg (v * y)
  have hd : 0 < 5 * Real.sqrt (v * y) + 36 * y := by linarith
  have hD : 0 < 6 * v + 9 * (5 * Real.sqrt (v * y) + 36 * y) := by linarith
  refine ⟨div_pos hd hD, ?_⟩
  rw [div_le_iff₀ hD]; linarith

lemma C1_ge : Real.sqrt 48 + 25 / 4 ≤ C₁ := by
  unfold C₁
  have a1 := Real.sq_sqrt (show (0:ℝ) ≤ 72 by norm_num)
  have a2 := Real.sq_sqrt (show (0:ℝ) ≤ 24 by norm_num)
  have a3 := Real.sq_sqrt (show (0:ℝ) ≤ 48 by norm_num)
  have b1 := Real.sqrt_nonneg (72:ℝ)
  have b2 := Real.sqrt_nonneg (24:ℝ)
  have b3 := Real.sqrt_nonneg (48:ℝ)
  have c1 : (8.48:ℝ) ≤ Real.sqrt 72 := by nlinarith
  have c2 : (4.89:ℝ) ≤ Real.sqrt 24 := by nlinarith
  have c3 : Real.sqrt 48 ≤ 6.93 := by nlinarith
  linarith

lemma sq_le_imp (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

set_option maxHeartbeats 1000000 in
lemma part2_core (v A m L : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hm : 0 < m) (hL : 0 < L)
    (hA : 0 ≤ A)
    (hev : C₁ * Real.sqrt (v * L / m) + C₂ * L / m <
      A / m + Real.sqrt (A / m * (48 * L) / m) + 48 * L / m - v) :
    2 * L ≤ lam2 v (L / m) * A + m * Real.log (1 + v - v * Real.exp (lam2 v (L / m))) := by
  have hA' : A = A / m * m := (div_mul_cancel₀ A hm.ne').symm
  have hL' : L = L / m * m := (div_mul_cancel₀ L hm.ne').symm
  have e1 : v * L / m = v * (L / m) := by ring
  have e2 : A / m * (48 * L) / m = 48 * (A / m) * (L / m) := by ring
  have e3 : C₂ * L / m = 144 * (L / m) := by unfold C₂; ring
  have e4 : 48 * L / m = 48 * (L / m) := by ring
  rw [e1, e2, e3, e4] at hev
  set y := L / m with hy
  set u := A / m with hu
  have hy0 : 0 < y := div_pos hL hm
  have hu0 : 0 ≤ u := div_nonneg hA hm.le
  have hla := lam2_bd v y hv0 hy0
  have hlaD : lam2 v y * (6 * v + 9 * (5 * Real.sqrt (v * y) + 36 * y)) =
      5 * Real.sqrt (v * y) + 36 * y := by
    unfold lam2
    have hs := Real.sqrt_nonneg (v * y)
    exact div_mul_cancel₀ _ (by linarith)
  set la := lam2 v y with hladef
  set s := Real.sqrt (v * y) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = v * y := Real.sq_sqrt (by positivity)
  set w := Real.sqrt (48 * u * y) with hwdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = 48 * u * y := Real.sq_sqrt (by positivity)
  have hq0 : 0 ≤ Real.sqrt 48 := Real.sqrt_nonneg _
  have hq2 : Real.sqrt 48 ^ 2 = 48 := Real.sq_sqrt (by norm_num)
  have hC := C1_ge
  set p := Real.sqrt 48 * s with hpdef
  have hp0 : 0 ≤ p := mul_nonneg hq0 hs0
  have hp2 : p ^ 2 = 48 * v * y := by rw [hpdef, mul_pow, hq2, hs2]; ring
  have hCs : p + 25 / 4 * s ≤ C₁ * s := by
    rw [hpdef]; nlinarith [mul_le_mul_of_nonneg_right hC hs0]
  have hd0 : 0 ≤ u - v := by
    by_contra hneg
    push_neg at hneg
    have hwp : w ≤ p := sq_le_imp w p hw0 hp0 (by nlinarith [mul_lt_mul_of_pos_right hneg hy0])
    nlinarith
  have hwle : w ≤ p + (u - v) / 4 + 48 * y := by
    apply sq_le_imp w _ hw0 (by linarith)
    nlinarith [sq_nonneg ((u - v) / 4 - 48 * y), mul_nonneg hp0 (by linarith :
      (0:ℝ) ≤ (u - v) / 4 + 48 * y)]
  have hd1 : 5 * s + 36 * y ≤ u - v := by linarith
  set d1 := 5 * s + 36 * y with hd1def
  have hd1pos : 0 < d1 := by linarith
  have hD : 0 < 6 * v + 9 * d1 := by linarith
  have hlog := (LK2 v la hv0 hv1 hla.1.le hla.2).1
  have h6 : 6 * v * la ≤ d1 := by nlinarith [mul_nonneg hd1pos.le hla.1.le]
  have hsq : 4 * y * (6 * v + 9 * d1) ≤ d1 ^ 2 := by
    nlinarith [mul_nonneg hv0 hy0.le, mul_nonneg hs0 hy0.le]
  have h4 : 4 * y ≤ la * d1 := by
    have e : la * d1 * (6 * v + 9 * d1) = d1 ^ 2 := by
      rw [show la * d1 * (6 * v + 9 * d1) = (la * (6 * v + 9 * d1)) * d1 by ring, hlaD]; ring
    have : 4 * y * (6 * v + 9 * d1) ≤ la * d1 * (6 * v + 9 * d1) := by linarith
    exact le_of_mul_le_mul_right this hD
  have hper : 2 * y ≤ la * u + Real.log (1 + v - v * Real.exp la) := by
    nlinarith [mul_le_mul_of_nonneg_left hd1 hla.1.le, mul_le_mul_of_nonneg_left h6 hla.1.le]
  calc 2 * L = m * (2 * y) := by rw [hL']; ring
    _ ≤ m * (la * u + Real.log (1 + v - v * Real.exp la)) :=
        mul_le_mul_of_nonneg_left hper hm.le
    _ = la * A + m * Real.log (1 + v - v * Real.exp la) := by rw [hA']; ring

lemma exp_le_Phi (θ A K : ℝ) (hK : 0 < K) (m : ℕ) (L : ℝ)
    (h : 2 * L ≤ θ * A + (m : ℝ) * Real.log K) :
    Real.exp (2 * L) ≤ Real.exp (θ * A) * K ^ m := by
  rw [← Real.exp_log hK, ← Real.exp_nat_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr h

lemma L_pos (N ℓ : ℕ) (hN : 0 < N) (hℓ : 1 ≤ ℓ) : 0 < Real.log (Real.sqrt N * ℓ + 1) := by
  apply Real.log_pos
  have h1 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h2 : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
  nlinarith

lemma expbound (N ℓ : ℕ) (hN : 0 < N) (hℓ : 1 ≤ ℓ) :
    Real.exp (-(2 * Real.log (Real.sqrt N * ℓ + 1))) ≤ 1 / ((N : ℝ) * ℓ ^ 2) := by
  have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs0 := Real.sqrt_nonneg (N : ℝ)
  have hl0 : (0:ℝ) ≤ ℓ := Nat.cast_nonneg _
  have hx : 0 < Real.sqrt N * ℓ + 1 := by positivity
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hℓ' : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  rw [show -(2 * Real.log (Real.sqrt N * ℓ + 1)) = Real.log (((Real.sqrt N * ℓ + 1) ^ 2)⁻¹) by
    rw [Real.log_inv, Real.log_pow]; push_cast; ring]
  rw [Real.exp_log (by positivity), ← one_div]
  apply one_div_le_one_div_of_le (mul_pos hN' (pow_pos hℓ' 2))
  nlinarith [mul_nonneg hs0 hl0]

lemma sum_bound (N ℓ : ℕ) (hN : 0 < N) (hℓ : 1 ≤ ℓ) (c : ℝ) (hc : 1 ≤ c) :
    ∑ _m ∈ Finset.Icc 1 ℓ, (1 / ((N : ℝ) * ℓ ^ 2)) ≤ c / ((N : ℝ) * ℓ) := by
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hℓ' : (0:ℝ) < ℓ := by exact_mod_cast hℓ
  have e : ((ℓ + 1 - 1 : ℕ) : ℝ) = ℓ := by simp
  rw [e]
  rw [show (ℓ : ℝ) * (1 / ((N : ℝ) * ℓ ^ 2)) = 1 / ((N : ℝ) * ℓ) by field_simp]
  exact div_le_div_of_nonneg_right hc (by positivity)

/-! ### The two parts -/

theorem part1 (N : ℕ) (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧ vUCB r sel h i ℓ < v i)
      ≤ 6 / ((N : ℝ) * ℓ) := by
  have hv0 : ∀ j, 0 ≤ v j := fun j => (hv j).1
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hL := L_pos N ℓ hN hℓ
  refine le_trans (probT_union v hv0 (alg1 r sel) _
    (fun m h => ℓ ≤ epochsDone r sel h ∧ Bof ℓ i (runAlg r sel (List.ofFn h)) = m ∧
      vUCB r sel h i ℓ < v i)
    (Finset.Icc 1 ℓ) ?_) ?_
  · rintro h ⟨hl, hlt⟩
    refine ⟨Bof ℓ i (runAlg r sel (List.ofFn h)), ?_, hl, rfl, hlt⟩
    rw [Finset.mem_Icc]
    refine ⟨?_, Bof_le _ _ _⟩
    by_contra h0
    have h0' : Bof ℓ i (runAlg r sel (List.ofFn h)) = 0 := by omega
    have : vUCB r sel h i ℓ = 1 := by
      show vUCBL _ i = 1
      unfold vUCBL
      exact if_pos (show TcountL ((completedEpochs r sel h).take ℓ) i = 0 from h0')
    linarith [(hv i).2]
  · refine le_trans (Finset.sum_le_sum (g := fun _ => 1 / ((N : ℝ) * ℓ ^ 2)) ?_)
      (sum_bound N ℓ hN hℓ 6 (by norm_num))
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm.1
    set L := Real.log (Real.sqrt N * ℓ + 1) with hLdef
    have hK : 0 < Kf v i (-Real.sqrt (L / m / v i)) := by
      unfold Kf
      have : Real.exp (-Real.sqrt (L / m / v i)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
      nlinarith [(hv i).1]
    refine le_trans (probT_le_of_Phi v r sel hv0 ℓ i _ hK _ L ?_) (expbound N ℓ hN hℓ)
    rintro h ⟨hl, hB, hlt⟩
    have hl' : ℓ ≤ (runAlg r sel (List.ofFn h)).past.length := hl
    rw [vUCB_eq r sel h i ℓ hl' (by omega), hB] at hlt
    rw [Phi_final v ℓ i _ _ hl', hB]
    apply exp_le_Phi _ _ _ hK
    exact part1_core (v i) _ _ L (hv i).1 (hv i).2 hmpos hL (Nat.cast_nonneg _) hlt

theorem part2 (N : ℕ) (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
          C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ
            < vUCB r sel h i ℓ - v i)
      ≤ 7 / ((N : ℝ) * ℓ) := by
  have hv0 : ∀ j, 0 ≤ v j := fun j => (hv j).1
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hL := L_pos N ℓ hN hℓ
  refine le_trans (probT_union v hv0 (alg1 r sel) _
    (fun m h => ℓ ≤ epochsDone r sel h ∧ Bof ℓ i (runAlg r sel (List.ofFn h)) = m ∧
      (1 ≤ Tcount r sel h i ℓ ∧
          C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ
            < vUCB r sel h i ℓ - v i))
    (Finset.Icc 1 ℓ) ?_) ?_
  · rintro h ⟨hl, h1, hb⟩
    refine ⟨Bof ℓ i (runAlg r sel (List.ofFn h)), ?_, hl, rfl, h1, hb⟩
    rw [Finset.mem_Icc]
    refine ⟨?_, Bof_le _ _ _⟩
    rw [← Tcount_eq r sel h i ℓ hl]; exact h1
  · refine le_trans (Finset.sum_le_sum (g := fun _ => 1 / ((N : ℝ) * ℓ ^ 2)) ?_)
      (sum_bound N ℓ hN hℓ 7 (by norm_num))
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm.1
    set L := Real.log (Real.sqrt N * ℓ + 1) with hLdef
    have hla := lam2_bd (v i) (L / m) (hv i).1 (div_pos hL hmpos)
    have hK : 0 < Kf v i (lam2 (v i) (L / m)) :=
      (LK2 (v i) _ (hv i).1 (hv i).2 hla.1.le hla.2).2
    refine le_trans (probT_le_of_Phi v r sel hv0 ℓ i _ hK _ L ?_) (expbound N ℓ hN hℓ)
    rintro h ⟨hl, hB, _, hb⟩
    have hl' : ℓ ≤ (runAlg r sel (List.ofFn h)).past.length := hl
    rw [vUCB_eq r sel h i ℓ hl' (by omega), Tcount_eq r sel h i ℓ hl', hB] at hb
    rw [Phi_final v ℓ i _ _ hl', hB]
    apply exp_le_Phi _ _ _ hK
    exact part2_core (v i) _ _ L (hv i).1 (hv i).2 hmpos hL (Nat.cast_nonneg _) hb

end B269

open ChoiceCDLP.MNL MNLBandit.WellSeparated in
theorem solution (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (i : Fin N) :
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧ vUCB r sel h i ℓ < v i)
      ≤ 6 / ((N : ℝ) * ℓ) ∧
    probT v (alg1 r sel) T
        (fun h => ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
          C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ
            < vUCB r sel h i ℓ - v i)
      ≤ 7 / ((N : ℝ) * ℓ) := by
  exact ⟨B269.part1 N v r sel hv T ℓ hℓ i, B269.part2 N v r sel hv T ℓ hℓ i⟩

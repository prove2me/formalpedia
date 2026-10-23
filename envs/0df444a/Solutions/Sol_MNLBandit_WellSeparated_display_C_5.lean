-- Prove2me | solution 1 for MNLBandit.WellSeparated.display_C_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:21:46.105365+00:00
-- url     : https://prove2.me/submissions/95242ac4-0e81-410e-b385-9090d749e964

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting



namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

theorem g58_sum_snoc {α : Type} [Fintype α] (T : ℕ) (f : (Fin (T+1) → α) → ℝ) :
    ∑ h, f h = ∑ h' : Fin T → α, ∑ o, f (Fin.snoc h' o) := by
  classical
  rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem g58_prefix_castSucc {N T : ℕ} (h' : Fin T → Option (Fin N)) (o : Option (Fin N)) (i : Fin T) :
    histPrefix (Fin.snoc h' o : Fin (T+1) → Option (Fin N)) (Fin.castSucc i) = histPrefix h' i := by
  funext u
  simp only [histPrefix]
  have : Fin.castLE (Fin.castSucc i).isLt.le u = Fin.castSucc (Fin.castLE i.isLt.le u) :=
    Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

theorem g58_prefix_last {N T : ℕ} (h' : Fin T → Option (Fin N)) (o : Option (Fin N)) :
    histPrefix (Fin.snoc h' o : Fin (T+1) → Option (Fin N)) (Fin.last T) = h' := by
  funext u
  simp only [histPrefix]
  have : Fin.castLE (Fin.last T).isLt.le u = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

theorem g58_ofFn_snoc {α : Type} {T : ℕ} (h' : Fin T → α) (o : α) :
    List.ofFn (Fin.snoc h' o : Fin (T+1) → α) = List.ofFn h' ++ [o] := by
  rw [List.ofFn_succ']
  simp

theorem g58_runAlg_append {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (l : List (Option (Fin N))) (o : Option (Fin N)) :
    MNLBandit.UCB.runAlg r sel (l ++ [o]) =
      MNLBandit.UCB.step r sel (MNLBandit.UCB.runAlg r sel l) o := by
  unfold MNLBandit.UCB.runAlg
  rw [List.foldl_append]
  rfl

theorem g58_cur_inv {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (l : List (Option (Fin N))) :
    (MNLBandit.UCB.runAlg r sel l).cur =
      MNLBandit.UCB.optimisticSet r sel (MNLBandit.UCB.runAlg r sel l).past := by
  unfold MNLBandit.UCB.runAlg
  suffices H : ∀ s : MNLBandit.UCB.AlgState N, s.cur = MNLBandit.UCB.optimisticSet r sel s.past →
      (l.foldl (MNLBandit.UCB.step r sel) s).cur =
        MNLBandit.UCB.optimisticSet r sel (l.foldl (MNLBandit.UCB.step r sel) s).past from
    H _ rfl
  induction l with
  | nil => intro s hs; exact hs
  | cons a l ih =>
    intro s hs
    rw [List.foldl_cons]
    apply ih
    cases a with
    | none => rfl
    | some i => exact hs

theorem g58_hp_snoc {N : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (T : ℕ) (h' : Fin T → Option (Fin N)) (o : Option (Fin N)) :
    histProb v (alg1 r sel) (T+1) (Fin.snoc h' o) =
      histProb v (alg1 r sel) T h' *
        MNLBandit.UCB.choiceProb v (MNLBandit.UCB.runAlg r sel (List.ofFn h')).cur o := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.snoc_castSucc]
    congr 2
    exact g58_prefix_castSucc h' o i
  · rw [Fin.snoc_last]
    congr 1
    show (MNLBandit.UCB.runAlg r sel (List.ofFn (histPrefix (Fin.snoc h' o : Fin (T+1) → _) (Fin.last T)))).cur = _
    rw [g58_prefix_last]

theorem g58_choice_sum {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (S : Finset (Fin N)) :
    ∑ o, MNLBandit.UCB.choiceProb v S o = 1 := by
  classical
  rw [Fintype.sum_option]
  simp only [MNLBandit.UCB.choiceProb]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← add_div]
  have : 0 < 1 + ∑ j ∈ S, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => (hv j).1); linarith
  exact div_self this.ne'

theorem g58_choice_nonneg {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (S : Finset (Fin N)) (o : Option (Fin N)) :
    0 ≤ MNLBandit.UCB.choiceProb v S o := by
  have : 0 < 1 + ∑ j ∈ S, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => (hv j).1); linarith
  cases o with
  | none => simp only [MNLBandit.UCB.choiceProb]; positivity
  | some i =>
    simp only [MNLBandit.UCB.choiceProb]
    split_ifs
    · exact div_nonneg (hv i).1 this.le
    · exact le_rfl

theorem g58_hp_nonneg {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ) (h : Fin T → Option (Fin N)) :
    0 ≤ histProb v (alg1 r sel) T h :=
  Finset.prod_nonneg (fun t _ => g58_choice_nonneg v hv _ _)

/-- the epoch potential: credits of completed epochs. -/
noncomputable def g58Pl {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (w : Finset (Fin N) → ℝ) (past : List (MNLBandit.UCB.EpochRecord N)) : ℝ :=
  ∑ k ∈ Finset.range past.length, w (MNLBandit.UCB.optimisticSet r sel (past.take k))

theorem g58_Pl_append {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (w : Finset (Fin N) → ℝ) (past : List (MNLBandit.UCB.EpochRecord N))
    (e : MNLBandit.UCB.EpochRecord N) :
    g58Pl r sel w (past ++ [e]) = g58Pl r sel w past + w (MNLBandit.UCB.optimisticSet r sel past) := by
  unfold g58Pl
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [List.take_append_of_le_length (by simp at hk; omega)]
  · rw [List.take_left']
    rfl

theorem g58_martingale {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (g : Finset (Fin N) → ℝ) (T : ℕ) :
    ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h = 1 ∧
    ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
      (g58Pl r sel (fun S => (1 + ∑ j ∈ S, v j) * g S)
          (MNLBandit.UCB.runAlg r sel (List.ofFn h)).past
        - ∑ t : Fin T, g (alg1 r sel t (histPrefix h t))) = 0 := by
  induction T with
  | zero =>
    constructor
    · simp [histProb]
    · simp [histProb, g58Pl, MNLBandit.UCB.runAlg, MNLBandit.UCB.initState]
  | succ T ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set w : Finset (Fin N) → ℝ := fun S => (1 + ∑ j ∈ S, v j) * g S with hw
    constructor
    · rw [g58_sum_snoc]
      rw [← ih1]
      apply Finset.sum_congr rfl
      intro h' _
      simp only [g58_hp_snoc]
      rw [← Finset.mul_sum, g58_choice_sum v hv, mul_one]
    · rw [g58_sum_snoc]
      rw [← ih2]
      apply Finset.sum_congr rfl
      intro h' _
      set s := MNLBandit.UCB.runAlg r sel (List.ofFn h') with hs
      set G := g58Pl r sel w s.past - ∑ t : Fin T, g (alg1 r sel t (histPrefix h' t)) with hG
      have hstep : ∀ o, g58Pl r sel w
            (MNLBandit.UCB.runAlg r sel (List.ofFn (Fin.snoc h' o : Fin (T+1) → _))).past
          - ∑ t : Fin (T+1), g (alg1 r sel t (histPrefix (Fin.snoc h' o : Fin (T+1) → _) t))
          = G + (if o = none then w s.cur else 0) - g s.cur := by
        intro o
        rw [Fin.sum_univ_castSucc]
        have e1 : ∀ i : Fin T, g (alg1 r sel (Fin.castSucc i)
            (histPrefix (Fin.snoc h' o : Fin (T+1) → _) (Fin.castSucc i))) =
            g (alg1 r sel i (histPrefix h' i)) := by
          intro i
          congr 2
          exact g58_prefix_castSucc h' o i
        have e2 : alg1 r sel (Fin.last T)
            (histPrefix (Fin.snoc h' o : Fin (T+1) → _) (Fin.last T)) = s.cur := by
          show (MNLBandit.UCB.runAlg r sel
            (List.ofFn (histPrefix (Fin.snoc h' o : Fin (T+1) → _) (Fin.last T)))).cur = _
          rw [g58_prefix_last]
        simp only [e1, e2]
        rw [g58_ofFn_snoc, g58_runAlg_append, ← hs]
        cases o with
        | none =>
          simp only [MNLBandit.UCB.step, if_true]
          rw [g58_Pl_append, hG, ← g58_cur_inv r sel (List.ofFn h'), ← hs]
          ring
        | some i =>
          simp only [MNLBandit.UCB.step, reduceCtorEq, if_false, hG]
          ring
      simp only [g58_hp_snoc, hstep, mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, g58_choice_sum v hv, one_mul]
      rw [Fintype.sum_option]
      simp only [if_true, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, add_zero]
      have hpos : 0 < 1 + ∑ j ∈ s.cur, v j := by
        have := Finset.sum_nonneg (fun j (_ : j ∈ s.cur) => (hv j).1); linarith
      simp only [MNLBandit.UCB.choiceProb, hw]
      rw [← hs]
      field_simp
      ring

theorem g58_Icc_shift (f : ℕ → ℝ) (M : ℕ) :
    ∑ ℓ ∈ Finset.Icc 1 M, f (ℓ - 1) = ∑ k ∈ Finset.range M, f k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
    simp

theorem display_C_5_core (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel) (T : ℕ) :
    MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤
      ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        ∑ ℓ ∈ Finset.Icc 1 (epochsStarted r sel h),
          (1 + ∑ j ∈ epochSet r sel h ℓ, v j) *
            (MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r (epochSet r sel h ℓ)) := by
  set R := MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 with hR
  set g : Finset (Fin N) → ℝ := fun S => R - revenue v r S with hg
  set w : Finset (Fin N) → ℝ := fun S => (1 + ∑ j ∈ S, v j) * g S with hw
  obtain ⟨h1, h2⟩ := g58_martingale v r hv sel g T
  have hreg : MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T =
      ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        ∑ t : Fin T, g (alg1 r sel t (histPrefix h t)) := by
    unfold MNLBandit.UCB.regret MNLBandit.UCB.expectedRevenue
    have e : ∀ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        ∑ t : Fin T, g (alg1 r sel t (histPrefix h t)) =
        histProb v (alg1 r sel) T h * (T * R) -
          histProb v (alg1 r sel) T h * ∑ t : Fin T, revenue v r (alg1 r sel t (histPrefix h t)) := by
      intro h
      simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun h _ => e h), Finset.sum_sub_distrib, ← Finset.sum_mul, h1,
      one_mul]
    rfl
  have hw0 : ∀ x, 0 ≤ w (MNLBandit.UCB.optimisticSet r sel x) := by
    intro x
    have hmem := (hsel (fun S => mnlObjective (fun i => MNLBandit.UCB.vUCBL x i) r 1 S)).1
    have hle : revenue v r (MNLBandit.UCB.optimisticSet r sel x) ≤ R := by
      rw [hR]; unfold MNLBandit.UCB.optRevenue
      exact Finset.le_sup' (fun S => mnlObjective v r 1 S) hmem
    have : 0 ≤ ∑ j ∈ MNLBandit.UCB.optimisticSet r sel x, v j :=
      Finset.sum_nonneg (fun j _ => (hv j).1)
    simp only [hw, hg]
    apply mul_nonneg (by linarith) (by linarith)
  rw [hreg]
  have h2' : ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        ∑ t : Fin T, g (alg1 r sel t (histPrefix h t)) =
      ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        g58Pl r sel w (MNLBandit.UCB.runAlg r sel (List.ofFn h)).past := by
    have := h2
    simp only [mul_sub, Finset.sum_sub_distrib] at this
    linarith
  rw [h2']
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ (g58_hp_nonneg v r hv sel T h)
  have hQ : ∑ ℓ ∈ Finset.Icc 1 (epochsStarted r sel h),
          (1 + ∑ j ∈ epochSet r sel h ℓ, v j) *
            (R - revenue v r (epochSet r sel h ℓ)) =
      ∑ k ∈ Finset.range (epochsStarted r sel h),
        w (MNLBandit.UCB.optimisticSet r sel ((completedEpochs r sel h).take k)) := by
    rw [← g58_Icc_shift]
    rfl
  rw [hQ]
  unfold g58Pl
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · apply Finset.range_subset_range.2
    unfold epochsStarted epochsDone completedEpochs
    omega
  · intro k _ _
    exact hw0 _

end MNLBandit.WellSeparated

open MNLBandit.WellSeparated
open ChoiceCDLP.MNL

theorem solution (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel) (T : ℕ) :
    MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤
      ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        ∑ ℓ ∈ Finset.Icc 1 (epochsStarted r sel h),
          (1 + ∑ j ∈ epochSet r sel h ℓ, v j) *
            (MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r (epochSet r sel h ℓ)) := by
  exact display_C_5_core N v r 𝒮 h𝒮 sel hv hsel T

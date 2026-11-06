-- Prove2me | solution 1 for MehtaOnlineAdAllocation.MSVV.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T11:04:27.430414+00:00
-- url     : https://prove2.me/submissions/3b185f11-a2ca-4320-aac1-4cf2519f523a

import Mathlib
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRun
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_SmallBids
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

set_option autoImplicit false

namespace AdWordsMSVV.LowerBound.KVVAux

open AdWordsMSVV.LowerBound Finset

theorem winner_spec {N M B : ℕ} {I : Instance N M} {a : DetAlg N M} {t : Fin M} {r : Fin N}
    (h : winner B I a t = some r) : r ∈ I t ∧ load B I a t.val r < B := by
  unfold winner at h
  cases hx : a t (reveal I t) with
  | none => rw [hx] at h; cases h
  | some r' =>
    rw [hx] at h
    simp only at h
    by_cases h1 : r' ∈ I t ∧ load B I a t.val r' < B
    · rw [if_pos h1] at h
      cases h
      exact h1
    · rw [if_neg h1] at h
      cases h

theorem load_succ {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (n : ℕ) (hn : n < M)
    (r : Fin N) :
    load B I a (n + 1) r = load B I a n r + (if winner B I a ⟨n, hn⟩ = some r then 1 else 0) := by
  rw [load]
  simp only [dif_pos hn]
  unfold winner
  cases hx : a ⟨n, hn⟩ (reveal I ⟨n, hn⟩) with
  | none => simp
  | some r' =>
    simp only
    by_cases h1 : r' ∈ I ⟨n, hn⟩ ∧ load B I a n r' < B
    · simp only [if_pos h1]
      by_cases hr : r = r'
      · subst hr; simp
      · simp [hr, Ne.symm hr]
    · simp only [if_neg h1]; simp

theorem load_stop {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (n : ℕ) (hn : ¬ n < M) :
    load B I a (n + 1) = load B I a n := by
  rw [load]
  simp only [dif_neg hn]

theorem load_le {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) :
    ∀ n r, load B I a n r ≤ B := by
  intro n
  induction n with
  | zero => intro r; rw [load]; exact Nat.zero_le _
  | succ n ih =>
    intro r
    by_cases hn : n < M
    · rw [load_succ B I a n hn r]
      split_ifs with hw
      · have := (winner_spec hw).2
        simp only at this
        omega
      · simpa using ih r
    · rw [load_stop B I a n hn]; exact ih r

theorem load_eq_sum {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (r : Fin N) :
    ∀ n, load B I a n r = ∑ t : Fin M, if t.val < n ∧ winner B I a t = some r then 1 else 0 := by
  intro n
  induction n with
  | zero => rw [load]; simp
  | succ n ih =>
    by_cases hn : n < M
    · rw [load_succ B I a n hn r, ih]
      have key : ∀ t : Fin M, (if t.val < n + 1 ∧ winner B I a t = some r then 1 else 0) =
          (if t.val < n ∧ winner B I a t = some r then 1 else 0) +
          (if t = ⟨n, hn⟩ then (if winner B I a ⟨n, hn⟩ = some r then 1 else 0) else 0) := by
        intro t
        by_cases ht : t = ⟨n, hn⟩
        · subst ht; simp
        · have hne : t.val ≠ n := fun h => ht (Fin.ext h)
          have e : t.val < n + 1 ↔ t.val < n := by omega
          simp [e, ht]
      rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_add_distrib]
      simp
    · rw [load_stop B I a n hn, ih]
      apply Finset.sum_congr rfl
      intro t _
      have := t.isLt
      have e : t.val < n + 1 ↔ t.val < n := by omega
      simp only [e]

theorem reveal_congr {N M : ℕ} {I I' : Instance N M} {u : Fin M}
    (h : ∀ s : Fin M, s ≤ u → I s = I' s) : reveal I u = reveal I' u := by
  funext j
  unfold reveal
  split_ifs with hj
  · rw [h j hj]
  · rfl

theorem load_congr {N M : ℕ} (B : ℕ) {I I' : Instance N M} (a : DetAlg N M) {u : Fin M}
    (h : ∀ s : Fin M, s ≤ u → I s = I' s) : ∀ n, n ≤ u.val → load B I a n = load B I' a n := by
  intro n
  induction n with
  | zero => intro _; rw [load, load]
  | succ n ih =>
    intro hn
    have hnM : n < M := by have := u.isLt; omega
    have hle : (⟨n, hnM⟩ : Fin M) ≤ u := by
      rw [Fin.le_def]; simp only; omega
    have h2 : ∀ s : Fin M, s ≤ ⟨n, hnM⟩ → I s = I' s := fun s hs => h s (le_trans hs hle)
    rw [load, load]
    simp only [dif_pos hnM]
    rw [ih (by omega), reveal_congr h2, h ⟨n, hnM⟩ hle]

theorem winner_congr {N M : ℕ} (B : ℕ) {I I' : Instance N M} (a : DetAlg N M) {t : Fin M}
    (h : ∀ s : Fin M, s ≤ t → I s = I' s) : winner B I a t = winner B I' a t := by
  unfold winner
  rw [reveal_congr h, h t le_rfl, load_congr B a h t.val le_rfl]

theorem mem_round {N B : ℕ} (π : Equiv.Perm (Fin N)) (t : Fin (N * B)) (r : Fin N) :
    r ∈ roundInstance N B π t ↔ t.val / B ≤ (π.symm r).val := by
  simp [roundInstance]

theorem round_swap {N B : ℕ} (π : Equiv.Perm (Fin N)) (j j' : Fin N) (s : Fin (N * B))
    (hj : s.val / B ≤ j.val) (hj' : s.val / B ≤ j'.val) :
    roundInstance N B (π * Equiv.swap j j') s = roundInstance N B π s := by
  ext r
  rw [mem_round, mem_round]
  have e : (π * Equiv.swap j j').symm r = Equiv.swap j j' (π.symm r) := by
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [e]
  generalize π.symm r = k
  by_cases h1 : k = j
  · subst h1; rw [Equiv.swap_apply_left]; constructor <;> intro <;> omega
  · by_cases h2 : k = j'
    · subst h2; rw [Equiv.swap_apply_right]; constructor <;> intro <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem swap_count {N B : ℕ} (a : DetAlg N (N * B)) (t : Fin (N * B)) (j j' : Fin N)
    (hj : t.val / B ≤ j.val) (hj' : t.val / B ≤ j'.val) :
    (∑ π : Equiv.Perm (Fin N),
        if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0) =
      ∑ π : Equiv.Perm (Fin N),
        if winner B (roundInstance N B π) a t = some (π j') then (1 : ℝ) else 0 := by
  rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j j'))
    (fun π => if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro π _
  have hw : winner B (roundInstance N B (π * Equiv.swap j j')) a t =
      winner B (roundInstance N B π) a t := by
    apply winner_congr
    intro s hs
    have : s.val / B ≤ t.val / B := Nat.div_le_div_right (Fin.le_def.mp hs)
    exact round_swap π j j' s (le_trans this hj) (le_trans this hj')
  simp only [Equiv.coe_mulRight]
  simp only [hw, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem sum_j_le_one {N : ℕ} (π : Equiv.Perm (Fin N)) (o : Option (Fin N)) :
    (∑ j : Fin N, if o = some (π j) then (1 : ℝ) else 0) ≤ 1 := by
  cases o with
  | none => simp
  | some r =>
    have e : ∀ j, (some r = some (π j)) ↔ (j = π.symm r) := by
      intro j
      rw [Option.some.injEq, Equiv.eq_symm_apply, eq_comm]
    simp_rw [e]
    simp

theorem cnt (n i J : ℕ) (c : ℝ) :
    ∑ k ∈ range n, (if i ≤ k ∧ k < J then c else 0) = ((min n J - i : ℕ) : ℝ) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have e : (min (n + 1) J - i) = (min n J - i) + (if i ≤ n ∧ n < J then 1 else 0) := by
      split_ifs <;> omega
    rw [e]
    push_cast
    split_ifs <;> ring

theorem block_sum {N B : ℕ} (g : ℕ → ℝ) :
    ∑ t : Fin (N * B), g (t.val / B) = B * ∑ i ∈ range N, g i := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB; simp
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have e : ∀ (i : Fin N) (s : Fin B), (finProdFinEquiv (i, s)).val / B = i.val := by
    intro i s
    rw [finProdFinEquiv_apply_val]
    simp only
    rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt s.isLt, zero_add]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => (B : ℝ) * g i) N, Finset.mul_sum]

theorem perm_sum_bound (N B J : ℕ) (hJ : J ≤ N) (a : DetAlg N (N * B)) :
    (∑ π : Equiv.Perm (Fin N), (revenue B (roundInstance N B π) a : ℝ)) ≤
      (N.factorial : ℝ) * B *
        (((N - J : ℕ) : ℝ) + ∑ i ∈ range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)) := by
  set K : ℝ := (N.factorial : ℝ) with hK
  have hcard : ∑ _π : Equiv.Perm (Fin N), (1 : ℝ) = K := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]; simp [hK]
  let c : Fin (N * B) → Fin N → ℝ := fun t j => ∑ π : Equiv.Perm (Fin N),
    if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0
  have hrev : ∀ π : Equiv.Perm (Fin N), (revenue B (roundInstance N B π) a : ℝ) =
      ∑ j : Fin N, (load B (roundInstance N B π) a (N * B) (π j) : ℝ) := by
    intro π
    unfold revenue
    push_cast
    exact (Equiv.sum_comp π (fun r => (load B (roundInstance N B π) a (N * B) r : ℝ))).symm
  have hload : ∀ (π : Equiv.Perm (Fin N)) (j : Fin N),
      (load B (roundInstance N B π) a (N * B) (π j) : ℝ) =
        ∑ t : Fin (N * B), if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0 := by
    intro π j
    rw [load_eq_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro t _
    simp [t.isLt]
  have hj : ∀ j : Fin N, ∑ π : Equiv.Perm (Fin N), (load B (roundInstance N B π) a (N * B) (π j) : ℝ)
      ≤ if j.val < J then ∑ t, c t j else K * B := by
    intro j
    split_ifs
    · rw [Finset.sum_congr rfl (fun π _ => hload π j), Finset.sum_comm]
    · calc _ ≤ ∑ _π : Equiv.Perm (Fin N), (B : ℝ) * 1 :=
            Finset.sum_le_sum (fun π _ => by
              rw [mul_one]; exact_mod_cast load_le B _ a _ _)
        _ = K * B := by rw [← Finset.mul_sum, hcard, mul_comm]
  have ht : ∀ t : Fin (N * B), ∑ j : Fin N, (if j.val < J then c t j else 0) ≤
      K * (((J - t.val / B : ℕ) : ℝ) / ((N - t.val / B : ℕ) : ℝ)) := by
    intro t
    have hiN : t.val / B < N :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t.isLt (Nat.mul_comm N B))
    set i := t.val / B with hi
    let j₀ : Fin N := ⟨i, hiN⟩
    have hc : ∀ j : Fin N, c t j = if i ≤ j.val then c t j₀ else 0 := by
      intro j
      split_ifs with h
      · exact swap_count a t j j₀ h le_rfl
      · apply Finset.sum_eq_zero
        intro π _
        rw [if_neg]
        intro hw
        have := (winner_spec hw).1
        rw [mem_round, Equiv.symm_apply_apply] at this
        omega
    have htot : ∑ j : Fin N, c t j ≤ K := by
      calc ∑ j : Fin N, c t j = ∑ π : Equiv.Perm (Fin N), ∑ j : Fin N,
            (if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0) :=
            Finset.sum_comm
        _ ≤ ∑ _π : Equiv.Perm (Fin N), (1 : ℝ) :=
            Finset.sum_le_sum (fun π _ => sum_j_le_one π _)
        _ = K := hcard
    have e1 : ∑ j : Fin N, c t j = ((N - i : ℕ) : ℝ) * c t j₀ := by
      rw [Finset.sum_congr rfl (fun j _ => hc j)]
      have := Fin.sum_univ_eq_sum_range (fun k => if i ≤ k ∧ k < N then c t j₀ else 0) N
      rw [cnt, min_self] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _
      simp [j.isLt]
    have e2 : ∑ j : Fin N, (if j.val < J then c t j else 0) = ((J - i : ℕ) : ℝ) * c t j₀ := by
      have := Fin.sum_univ_eq_sum_range (fun k => if i ≤ k ∧ k < J then c t j₀ else 0) N
      rw [cnt, min_eq_right hJ] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _
      rw [hc j]
      by_cases h1 : j.val < J <;> by_cases h2 : i ≤ j.val <;> simp [h1, h2]
    rw [e2]
    have hNi : (0 : ℝ) < ((N - i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hiN
    have hc0 : c t j₀ ≤ K / ((N - i : ℕ) : ℝ) := by
      rw [le_div_iff₀ hNi]; rw [e1] at htot; linarith
    calc ((J - i : ℕ) : ℝ) * c t j₀ ≤ ((J - i : ℕ) : ℝ) * (K / ((N - i : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hc0 (by positivity)
      _ = _ := by ring
  have hcount : ∑ j : Fin N, (if j.val < J then (0 : ℝ) else K * B) = ((N - J : ℕ) : ℝ) * (K * B) := by
    have := Fin.sum_univ_eq_sum_range (fun k => if J ≤ k ∧ k < N then K * B else 0) N
    rw [cnt, min_self] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : j.val < J
    · simp [h1]
    · have : J ≤ j.val := by omega
      simp [h1, this, j.isLt]
  have hb := block_sum (N := N) (B := B)
    (fun i => K * (((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)))
  calc (∑ π : Equiv.Perm (Fin N), (revenue B (roundInstance N B π) a : ℝ))
      = ∑ j : Fin N, ∑ π : Equiv.Perm (Fin N),
          (load B (roundInstance N B π) a (N * B) (π j) : ℝ) := by
        rw [Finset.sum_congr rfl (fun π _ => hrev π)]
        exact Finset.sum_comm
    _ ≤ ∑ j : Fin N, (if j.val < J then ∑ t, c t j else K * B) :=
        Finset.sum_le_sum (fun j _ => hj j)
    _ = ∑ j : Fin N, ((∑ t, (if j.val < J then c t j else 0)) +
          (if j.val < J then (0 : ℝ) else K * B)) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
    _ = ∑ t, ∑ j : Fin N, (if j.val < J then c t j else 0) +
          ∑ j : Fin N, (if j.val < J then (0 : ℝ) else K * B) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ t : Fin (N * B), K * (((J - t.val / B : ℕ) : ℝ) / ((N - t.val / B : ℕ) : ℝ)) +
          ((N - J : ℕ) : ℝ) * (K * B) :=
        add_le_add (Finset.sum_le_sum (fun t _ => ht t)) (le_of_eq hcount)
    _ = K * B * (((N - J : ℕ) : ℝ) + ∑ i ∈ range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)) := by
        rw [hb, ← Finset.mul_sum]; ring

theorem harm_log (m : ℕ) : ∀ J : ℕ, Real.log (((m + J + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
    ∑ i ∈ range J, (1 : ℝ) / ((m + J - i : ℕ) : ℝ) := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ i ∈ range J, (1 : ℝ) / ((m + (J + 1) - (i + 1) : ℕ) : ℝ) =
        1 / ((m + J - i : ℕ) : ℝ) := by
      intro i _
      rw [show m + (J + 1) - (i + 1) = m + J - i by omega]
    rw [Finset.sum_congr rfl h1]
    have hp1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hp2 : (0 : ℝ) < ((m + J + 1 : ℕ) : ℝ) := by positivity
    have hp3 : (0 : ℝ) < ((m + (J + 1) + 1 : ℕ) : ℝ) := by positivity
    have e : ((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) =
        (((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + J + 1 : ℕ) : ℝ)) *
          (((m + J + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
      field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have h2 : Real.log (((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + J + 1 : ℕ) : ℝ)) ≤
        1 / ((m + (J + 1) - 0 : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos
        (x := ((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + J + 1 : ℕ) : ℝ)) (by positivity)
      calc _ ≤ _ := this
        _ = _ := by
          rw [Nat.sub_zero]
          push_cast
          field_simp
          ring
    linarith

theorem core (m J : ℕ) (h : Real.exp 1 * ((m : ℝ) + 1) ≤ (m : ℝ) + J + 1) :
    (m : ℝ) + ∑ i ∈ range (m + J), ((J - i : ℕ) : ℝ) / ((m + J - i : ℕ) : ℝ) ≤ J := by
  have hsplit : ∑ i ∈ range (m + J), ((J - i : ℕ) : ℝ) / ((m + J - i : ℕ) : ℝ) =
      ∑ i ∈ range J, (1 - (m : ℝ) * (1 / ((m + J - i : ℕ) : ℝ))) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show J ≤ m + J by omega)]
    rw [Finset.sum_eq_zero (s := Ico J (m + J)) (fun i hi => by
        rw [Finset.mem_Ico] at hi
        rw [show J - i = 0 by omega]
        simp), add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ((J - i : ℕ) : ℝ) = (J : ℝ) - i := by rw [Nat.cast_sub hi.le]
    have h2 : ((m + J - i : ℕ) : ℝ) = (m : ℝ) + J - i := by
      rw [Nat.cast_sub (by omega : i ≤ m + J)]; push_cast; ring
    have h3 : (0 : ℝ) < (m : ℝ) + J - i := by
      have : (i : ℝ) < J := by exact_mod_cast hi
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [h1, h2]
    field_simp
    ring
  rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hS := harm_log m J
  have hlog : 1 ≤ Real.log (((m + J + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    rw [le_div_iff₀ (by positivity)]
    push_cast
    linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : (m : ℝ) * 1 ≤ (m : ℝ) * ∑ i ∈ range J, (1 : ℝ) / ((m + J - i : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (le_trans hlog hS) hm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this ⊢
  linarith

theorem analytic (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : ⌈2 / δ⌉₊ + 2 ≤ N) :
    ∃ J : ℕ, J ≤ N ∧ ((N - J : ℕ) : ℝ) + ∑ i ∈ range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ) ≤
      (1 - Real.exp (-1) + δ) * N := by
  set e := Real.exp 1 with he
  have he3 : e < 3 := by
    have := Real.exp_one_lt_d9
    rw [he]; linarith
  have he1 : 1 < e := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    rw [he]; linarith
  have hepos : 0 < e := by linarith
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hδN : 2 ≤ δ * N := by
    have h1 : 2 / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 / δ⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈2 / δ⌉₊ ≤ N)
    have h3 : 2 / δ ≤ N := le_trans h1 h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  obtain ⟨m, hmle, hmlow⟩ : ∃ m : ℕ, e * ((m : ℝ) + 1) ≤ (N : ℝ) + 1 ∧
      ((N : ℝ) + 1) / e - 2 < m := by
    set F := ⌊((N : ℝ) + 1) / e⌋₊ with hF
    have hF1 : 1 ≤ F := by
      apply Nat.le_floor
      rw [le_div_iff₀ hepos]
      push_cast
      linarith
    have hFle : (F : ℝ) ≤ ((N : ℝ) + 1) / e := Nat.floor_le (by positivity)
    have hFgt : ((N : ℝ) + 1) / e < F + 1 := Nat.lt_floor_add_one _
    refine ⟨F - 1, ?_, ?_⟩
    · have : ((F - 1 : ℕ) : ℝ) + 1 = F := by
        rw [Nat.cast_sub hF1]; push_cast; ring
      rw [this]
      rw [le_div_iff₀ hepos] at hFle
      linarith
    · rw [Nat.cast_sub hF1]; push_cast; linarith
  have hmN : m ≤ N := by
    have : (m : ℝ) + 1 ≤ (N : ℝ) + 1 := by nlinarith
    have : (m : ℝ) ≤ N := by linarith
    exact_mod_cast this
  obtain ⟨J, rfl⟩ : ∃ J, N = m + J := ⟨N - m, by omega⟩
  refine ⟨J, by omega, ?_⟩
  rw [show m + J - J = m by omega]
  have hc := core m J (by push_cast at hmle; linarith)
  have hinv : Real.exp (-1) = e⁻¹ := by rw [he, Real.exp_neg]
  rw [hinv]
  push_cast at hmlow hδN ⊢
  rw [div_eq_mul_inv] at hmlow
  nlinarith [inv_pos.mpr hepos]

theorem avg_le {α : Type} (A : PMF α) (s : Finset α) (hs : ∀ a, a ∈ s) {ι : Type} [Fintype ι]
    (f : α → ι → ℝ) (C : ℝ) (h : ∀ a, ∑ π, f a π ≤ C) :
    ∑ π, ∑ a ∈ s, (A a).toReal * f a π ≤ C := by
  have hA : ∑ a ∈ s, (A a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top A a)]
    have h1 : ∑' a, A a = ∑ a ∈ s, A a := tsum_eq_sum (fun b hb => absurd (hs b) hb)
    rw [← h1, PMF.tsum_coe, ENNReal.toReal_one]
  rw [Finset.sum_comm]
  calc ∑ a ∈ s, ∑ π, (A a).toReal * f a π = ∑ a ∈ s, (A a).toReal * ∑ π, f a π := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ s, (A a).toReal * C :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    _ = C := by rw [← Finset.sum_mul, hA, one_mul]

theorem offline_eq (N B : ℕ) (hB : 1 ≤ B) (π : Equiv.Perm (Fin N)) :
    offlineRevenue B (roundInstance N B π) (roundAllocation N B π) = N * B := by
  unfold offlineRevenue
  have hBpos : 0 < B := hB
  have key : ∀ r : Fin N, min B ((univ.filter (fun t => roundAllocation N B π t = some r ∧
      r ∈ roundInstance N B π t)).card) = B := by
    intro r
    apply min_eq_left
    have hv : ∀ s : Fin B, (finProdFinEquiv (π.symm r, s)).val / B = (π.symm r).val := by
      intro s
      rw [finProdFinEquiv_apply_val]
      simp only
      rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt s.isLt, zero_add]
    have hcard := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin B)))
      (t := univ.filter (fun t => roundAllocation N B π t = some r ∧ r ∈ roundInstance N B π t))
      (fun s => finProdFinEquiv (π.symm r, s)) ?_ ?_
    · simpa using hcard
    · intro s _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · unfold roundAllocation
        rw [dif_pos (by rw [hv s]; exact (π.symm r).isLt)]
        congr 1
        have : (⟨(finProdFinEquiv (π.symm r, s)).val / B, by rw [hv s]; exact (π.symm r).isLt⟩ :
            Fin N) = π.symm r := Fin.ext (hv s)
        rw [this, Equiv.apply_symm_apply]
      · rw [mem_round, hv s]
    · intro s₁ _ s₂ _ h
      have := finProdFinEquiv.injective h
      simpa using this
  rw [Finset.sum_congr rfl (fun r _ => key r)]
  simp

end AdWordsMSVV.LowerBound.KVVAux

open AdWordsMSVV.LowerBound in
theorem AdWordsMSVV.LowerBound.KVVAux.kvv_theorem_9 :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : ℕ, 1 ≤ B →
      ∀ A : RandAlg N (N * B), ∃ (I : Instance N (N * B)) (τ : Fin (N * B) → Option (Fin N)),
        offlineRevenue B I τ = N * B ∧
        expectedRevenue B I A ≤ (1 - Real.exp (-1) + δ) * ((N : ℝ) * B) := by
  intro δ hδ
  refine ⟨⌈2 / δ⌉₊ + 2, ?_⟩
  intro N hN B hB A
  obtain ⟨J, hJN, hX⟩ := KVVAux.analytic δ hδ N hN
  set X : ℝ := ((N - J : ℕ) : ℝ) + ∑ i ∈ Finset.range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)
    with hXdef
  have hsum : ∑ π : Equiv.Perm (Fin N), expectedRevenue B (roundInstance N B π) A ≤
      ∑ _π : Equiv.Perm (Fin N), ((B : ℝ) * X) := by
    have hconst : ∑ _π : Equiv.Perm (Fin N), ((B : ℝ) * X) = (N.factorial : ℝ) * B * X := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hconst]
    unfold expectedRevenue
    exact KVVAux.avg_le A _ (fun a => by simp) (fun a π => (revenue B (roundInstance N B π) a : ℝ))
      _ (fun a => KVVAux.perm_sum_bound N B J hJN a)
  obtain ⟨π, _, hπ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨roundInstance N B π, roundAllocation N B π, KVVAux.offline_eq N B hB π, ?_⟩
  calc expectedRevenue B (roundInstance N B π) A ≤ (B : ℝ) * X := hπ
    _ ≤ (B : ℝ) * ((1 - Real.exp (-1) + δ) * N) :=
        mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg B)
    _ = (1 - Real.exp (-1) + δ) * ((N : ℝ) * B) := by ring

namespace MehtaOnlineAdAllocation.MSVV.P1Aux

open MehtaOnlineAdAllocation.MSVV Finset

lemma sum_before_succ {M : ℕ} (P : Fin M → Prop) [DecidablePred P] (f : Fin M → ℝ) (t : ℕ)
    (ht : t < M) :
    ∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < t + 1 ∧ P j), f j
      = ∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < t ∧ P j), f j
        + (if P ⟨t, ht⟩ then f ⟨t, ht⟩ else 0) := by
  rw [sum_filter, sum_filter]
  have h0 : (if P ⟨t, ht⟩ then f ⟨t, ht⟩ else 0)
      = ∑ j : Fin M, if (j:ℕ) = t ∧ P j then f j else 0 := by
    rw [Finset.sum_eq_single (⟨t, ht⟩ : Fin M)]
    · simp
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hj (Fin.ext h1)
    · intro h; exact absurd (mem_univ _) h
  rw [h0, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h1 : (j:ℕ) < t
  · have h2 : (j:ℕ) ≠ t := by omega
    have h3 : (j:ℕ) < t + 1 := by omega
    simp [h1, h2, h3]
  · by_cases h2 : (j:ℕ) = t
    · simp [h1, h2]
    · have h3 : ¬ (j:ℕ) < t + 1 := by omega
      simp [h1, h2, h3]

variable {N M : ℕ}

lemma assigned_nonneg (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) :
    0 ≤ assignedBefore I σ u t :=
  sum_nonneg (fun v _ => I.bid_nonneg u v)

lemma spend_nonneg (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) :
    0 ≤ spend I σ u t :=
  le_min (I.budget_pos u).le (assigned_nonneg I σ u t)

lemma spend_le (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) :
    spend I σ u t ≤ I.budget u := min_le_left _ _

lemma assigned_mono (I : Instance N M) (σ : Allocation N M) (u : Fin N) {t t' : ℕ}
    (h : t ≤ t') : assignedBefore I σ u t ≤ assignedBefore I σ u t' := by
  unfold assignedBefore
  apply sum_le_sum_of_subset_of_nonneg
  · intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv ⊢
    exact ⟨lt_of_lt_of_le hv.1 h, hv.2⟩
  · intro v _ _
    exact I.bid_nonneg u v

lemma spend_mono (I : Instance N M) (σ : Allocation N M) (u : Fin N) {t t' : ℕ}
    (h : t ≤ t') : spend I σ u t ≤ spend I σ u t' :=
  min_le_min le_rfl (assigned_mono I σ u h)

lemma assigned_succ (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) (ht : t < M) :
    assignedBefore I σ u (t + 1) = assignedBefore I σ u t
      + (if σ ⟨t, ht⟩ = some u then I.bid u ⟨t, ht⟩ else 0) := by
  unfold assignedBefore
  exact sum_before_succ (fun v => σ v = some u) (fun v => I.bid u v) t ht

lemma spend_succ_ne (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) (ht : t < M)
    (h : σ ⟨t, ht⟩ ≠ some u) : spend I σ u (t + 1) = spend I σ u t := by
  unfold spend
  rw [assigned_succ I σ u t ht, if_neg h, add_zero]

lemma spend_succ_eq (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) (ht : t < M)
    (h : σ ⟨t, ht⟩ = some u) (hlt : spend I σ u t < I.budget u) :
    spend I σ u (t + 1) = spend I σ u t + cappedBid I σ u ⟨t, ht⟩ := by
  have hA : assignedBefore I σ u t < I.budget u := by
    unfold spend at hlt
    rcases min_lt_iff.mp hlt with h1 | h1
    · exact absurd h1 (lt_irrefl _)
    · exact h1
  have hs : spend I σ u t = assignedBefore I σ u t := min_eq_right hA.le
  have hc : cappedBid I σ u ⟨t, ht⟩ = min (I.bid u ⟨t, ht⟩) (I.budget u - spend I σ u t) := rfl
  rw [hc, hs]
  have h2 : spend I σ u (t + 1) = min (I.budget u) (assignedBefore I σ u (t + 1)) := rfl
  rw [h2, assigned_succ I σ u t ht, if_pos h]
  rcases le_total (I.bid u ⟨t, ht⟩) (I.budget u - assignedBefore I σ u t) with h3 | h3
  · rw [min_eq_left h3, min_eq_right (by linarith)]
  · rw [min_eq_right h3, min_eq_left (by linarith)]
    ring

lemma psi_nonneg_of_le {x : ℝ} (hx : x ≤ 1) : 0 ≤ psi x := by
  unfold psi
  have : Real.exp (x - 1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

lemma frac_le_one (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) :
    spend I σ u t / I.budget u ≤ 1 :=
  (div_le_one (I.budget_pos u)).mpr (spend_le I σ u t)

lemma capped_nonneg (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : Fin M) :
    0 ≤ cappedBid I σ u t :=
  le_min (I.bid_nonneg u t) (by linarith [spend_le I σ u t.val])

lemma score_nonneg (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : Fin M) :
    0 ≤ score I σ u t :=
  mul_nonneg (capped_nonneg I σ u t) (psi_nonneg_of_le (frac_le_one I σ u t.val))

/-- The score of the bidder that wins query `t` (zero if `t` is unallocated). -/
noncomputable def mx (I : Instance N M) (σ : Allocation N M) (t : Fin M) : ℝ :=
  ∑ u, if σ t = some u then score I σ u t else 0

lemma mx_nonneg (I : Instance N M) (σ : Allocation N M) (t : Fin M) : 0 ≤ mx I σ t := by
  unfold mx
  apply sum_nonneg
  intro u _
  split_ifs
  · exact score_nonneg I σ u t
  · exact le_rfl

lemma score_le_mx (I : Instance N M) (σ : Allocation N M) (hrun : IsRun I σ) (u : Fin N)
    (t : Fin M) : score I σ u t ≤ mx I σ t := by
  have hr := hrun t
  unfold mx
  cases hσ : σ t with
  | none =>
    simp only [hσ] at hr
    rw [hr u]
    simp
  | some w =>
    simp only [hσ] at hr
    rw [Finset.sum_eq_single w]
    · rw [if_pos rfl]
      exact hr.2 u
    · intro v _ hv
      rw [if_neg]
      intro h
      exact hv (Option.some_inj.mp h).symm
    · intro h
      exact absurd (mem_univ w) h

/-- Scores collected by bidder `u` before time `t`. -/
noncomputable def Sc (I : Instance N M) (σ : Allocation N M) (u : Fin N) (t : ℕ) : ℝ :=
  ∑ v ∈ univ.filter (fun v : Fin M => v.val < t ∧ σ v = some u), score I σ u v

lemma step_ineq {B s d η : ℝ} (hB : 0 < B) (hs0 : 0 ≤ s) (hsB : s ≤ B) (hd0 : 0 ≤ d)
    (hdB : d ≤ B) (hdη : d ≤ η * B) :
    B * (Real.exp ((s + d) / B) - 1) + Real.exp 1 * (d * psi (s / B))
      ≤ B * (Real.exp (s / B) - 1) + (1 + η) * Real.exp 1 * d := by
  set x := s / B with hxdef
  set δ := d / B with hδdef
  have hx1 : x ≤ 1 := (div_le_one hB).mpr hsB
  have hδ0 : 0 ≤ δ := div_nonneg hd0 hB.le
  have hδ1 : δ ≤ 1 := (div_le_one hB).mpr hdB
  have hδη : δ ≤ η := (div_le_iff₀ hB).mpr hdη
  have hdd : d = B * δ := by rw [hδdef]; field_simp
  have hsplit : (s + d) / B = x + δ := by rw [add_div]
  rw [hsplit, Real.exp_add]
  unfold psi
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hEx : Real.exp 1 * Real.exp (x - 1) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hq2 : |Real.exp δ - 1 - δ| ≤ δ ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le (by rw [abs_of_nonneg hδ0]; exact hδ1)
  have hq3 : Real.exp δ - 1 - δ ≤ η * δ := by
    have h1 := (abs_le.mp hq2).2
    have h2 : δ ^ 2 ≤ η * δ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hδη hδ0
    linarith
  have hq4 : 0 ≤ Real.exp δ - 1 - δ := by linarith [Real.add_one_le_exp δ]
  have hex : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
  have key : Real.exp x * (Real.exp δ - 1 - δ) ≤ Real.exp 1 * (η * δ) :=
    mul_le_mul hex hq3 hq4 hE.le
  have key2 := mul_le_mul_of_nonneg_left key hB.le
  rw [hdd]
  have e1 : Real.exp 1 * (B * δ * (1 - Real.exp (x - 1)))
      = Real.exp 1 * (B * δ) - B * δ * (Real.exp 1 * Real.exp (x - 1)) := by ring
  rw [e1, hEx]
  nlinarith [key2]

lemma inv_run (I : Instance N M) (σ : Allocation N M) (hrun : IsRun I σ) {η : ℝ}
    (hη : SmallBids I η) (u : Fin N) :
    ∀ t, t ≤ M → I.budget u * (Real.exp (spend I σ u t / I.budget u) - 1)
      + Real.exp 1 * Sc I σ u t ≤ (1 + η) * Real.exp 1 * spend I σ u t := by
  intro t
  induction t with
  | zero =>
    intro _
    have hf : (univ.filter (fun v : Fin M => v.val < 0 ∧ σ v = some u)) = ∅ := by
      ext v
      simp
    have h0 : spend I σ u 0 = 0 := by
      unfold spend assignedBefore
      rw [hf, sum_empty]
      exact min_eq_right (I.budget_pos u).le
    have h1 : Sc I σ u 0 = 0 := by
      unfold Sc
      rw [hf, sum_empty]
    rw [h0, h1]
    simp
  | succ t ih =>
    intro ht
    have htM : t < M := by omega
    have ih := ih (by omega)
    have hSc : Sc I σ u (t + 1) = Sc I σ u t
        + (if σ ⟨t, htM⟩ = some u then score I σ u ⟨t, htM⟩ else 0) := by
      unfold Sc
      exact sum_before_succ (fun v => σ v = some u) (fun v => score I σ u v) t htM
    by_cases hσ : σ ⟨t, htM⟩ = some u
    · have hr := hrun ⟨t, htM⟩
      simp only [hσ] at hr
      have hlt : spend I σ u t < I.budget u := hr.1
      rw [hSc, if_pos hσ, spend_succ_eq I σ u t htM hσ hlt]
      have hsc : score I σ u ⟨t, htM⟩
          = cappedBid I σ u ⟨t, htM⟩ * psi (spend I σ u t / I.budget u) := rfl
      rw [hsc]
      have hd0 := capped_nonneg I σ u ⟨t, htM⟩
      have hdB : cappedBid I σ u ⟨t, htM⟩ ≤ I.budget u := by
        have h1 : cappedBid I σ u ⟨t, htM⟩ ≤ I.budget u - spend I σ u t := min_le_right _ _
        linarith [spend_nonneg I σ u t]
      have hdη : cappedBid I σ u ⟨t, htM⟩ ≤ η * I.budget u :=
        le_trans (min_le_left _ _) (hη u ⟨t, htM⟩)
      have := step_ineq (I.budget_pos u) (spend_nonneg I σ u t) (spend_le I σ u t) hd0 hdB hdη
      linarith
    · rw [hSc, if_neg hσ, add_zero, spend_succ_ne I σ u t htM hσ]
      exact ih

/-- Scaled dual value of bidder `u`. -/
noncomputable def W (I : Instance N M) (σ : Allocation N M) (η : ℝ) (u : Fin N) : ℝ :=
  if spend I σ u M ≤ (1 - η) * I.budget u then
    I.budget u * (Real.exp (spend I σ u M / I.budget u) - 1)
  else (Real.exp 1 - 1) * I.budget u

lemma per_u (I : Instance N M) (σ : Allocation N M) (hrun : IsRun I σ) {η : ℝ} (hη0 : 0 ≤ η)
    (hη2 : η ≤ 1 / 2) (hη : SmallBids I η) (u : Fin N) :
    W I σ η u + Real.exp 1 * Sc I σ u M ≤ (1 + 3 * η) * Real.exp 1 * spend I σ u M := by
  have hinv := inv_run I σ hrun hη u M le_rfl
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hs0 := spend_nonneg I σ u M
  unfold W
  split_ifs with hc
  · nlinarith [mul_nonneg (mul_nonneg hη0 hE.le) hs0]
  · replace hc := not_le.mp hc
    set s := spend I σ u M with hsdef
    set B := I.budget u with hBdef
    have hB : 0 < B := I.budget_pos u
    set f := s / B with hfdef
    have hf : 1 - η < f := by
      rw [hfdef, lt_div_iff₀ hB]
      exact hc
    have hexpf : Real.exp f = Real.exp (f - 1) * Real.exp 1 := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hge : f ≤ Real.exp (f - 1) := by linarith [Real.add_one_le_exp (f - 1)]
    have hEf : Real.exp 1 - Real.exp f ≤ Real.exp 1 * η := by
      have : f * Real.exp 1 ≤ Real.exp (f - 1) * Real.exp 1 :=
        mul_le_mul_of_nonneg_right hge hE.le
      nlinarith
    have hB2 : B ≤ 2 * s := by nlinarith
    have h1 : B * (Real.exp 1 - Real.exp f) ≤ B * (Real.exp 1 * η) :=
      mul_le_mul_of_nonneg_left hEf hB.le
    have h2 : B * (Real.exp 1 * η) ≤ 2 * s * (Real.exp 1 * η) :=
      mul_le_mul_of_nonneg_right hB2 (mul_nonneg hE.le hη0)
    nlinarith

lemma dual_u (I : Instance N M) (σ : Allocation N M) (hrun : IsRun I σ) {η : ℝ}
    (hη0 : 0 ≤ η) (hη : SmallBids I η) (τ : Allocation N M) (u : Fin N) :
    (Real.exp 1 - 1) * spend I τ u M ≤ W I σ η u
      + Real.exp 1 * ∑ v ∈ univ.filter (fun v : Fin M => v.val < M ∧ τ v = some u), mx I σ v := by
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hE1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hB : 0 < I.budget u := I.budget_pos u
  have hmx0 : 0 ≤ ∑ v ∈ univ.filter (fun v : Fin M => v.val < M ∧ τ v = some u), mx I σ v :=
    sum_nonneg (fun v _ => mx_nonneg I σ v)
  unfold W
  split_ifs with hc
  · set s := spend I σ u M with hsdef
    set B := I.budget u with hBdef
    set f := s / B with hfdef
    have hf0 : 0 ≤ f := div_nonneg (spend_nonneg I σ u M) hB.le
    have hf1 : f ≤ 1 := frac_le_one I σ u M
    have hp1 : 0 ≤ Real.exp f - 1 := by linarith [Real.add_one_le_exp f]
    have hp2 : 0 ≤ Real.exp 1 - Real.exp f := by linarith [Real.exp_le_exp.mpr hf1]
    have hv : ∀ v : Fin M, (Real.exp 1 - Real.exp f) * I.bid u v ≤ Real.exp 1 * mx I σ v := by
      intro v
      have hsv : spend I σ u v.val ≤ s := spend_mono I σ u (le_of_lt v.isLt)
      have hbv : I.bid u v ≤ η * B := hη u v
      have hcap : cappedBid I σ u v = I.bid u v := by
        apply min_eq_left
        linarith
      have hfv : Real.exp (spend I σ u v.val / B) ≤ Real.exp f :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hsv hB.le)
      have hEx : Real.exp 1 * Real.exp (spend I σ u v.val / B - 1)
          = Real.exp (spend I σ u v.val / B) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hsc : Real.exp 1 * score I σ u v
          = I.bid u v * (Real.exp 1 - Real.exp (spend I σ u v.val / B)) := by
        have hs' : score I σ u v = cappedBid I σ u v * psi (spend I σ u v.val / B) := rfl
        rw [hs', hcap]
        unfold psi
        linear_combination (-I.bid u v) * hEx
      have hb0 := I.bid_nonneg u v
      calc (Real.exp 1 - Real.exp f) * I.bid u v
          ≤ I.bid u v * (Real.exp 1 - Real.exp (spend I σ u v.val / B)) := by nlinarith
        _ = Real.exp 1 * score I σ u v := hsc.symm
        _ ≤ Real.exp 1 * mx I σ v :=
            mul_le_mul_of_nonneg_left (score_le_mx I σ hrun u v) hE.le
    have hsum : (Real.exp 1 - Real.exp f) * assignedBefore I τ u M
        ≤ Real.exp 1 * ∑ v ∈ univ.filter (fun v : Fin M => v.val < M ∧ τ v = some u),
            mx I σ v := by
      unfold assignedBefore
      rw [mul_sum, mul_sum]
      exact sum_le_sum (fun v _ => hv v)
    have hm : spend I τ u M = min B (assignedBefore I τ u M) := rfl
    rw [hm]
    have a1 := mul_le_mul_of_nonneg_left (min_le_left B (assignedBefore I τ u M)) hp1
    have a2 := mul_le_mul_of_nonneg_left (min_le_right B (assignedBefore I τ u M)) hp2
    nlinarith
  · have h1 : spend I τ u M ≤ I.budget u := spend_le I τ u M
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ Real.exp 1 - 1)
    nlinarith

lemma route (I : Instance N M) (σ τ : Allocation N M) :
    ∑ u, ∑ v ∈ univ.filter (fun v : Fin M => v.val < M ∧ τ v = some u), mx I σ v
      ≤ ∑ v, mx I σ v := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro v _
  cases hτ : τ v with
  | none =>
    simp only [reduceCtorEq, and_false, if_false, sum_const_zero]
    exact mx_nonneg I σ v
  | some w =>
    rw [Finset.sum_eq_single w]
    · split_ifs
      · exact le_rfl
      · exact mx_nonneg I σ v
    · intro b _ hb
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hb (Option.some_inj.mp h).symm
    · intro h
      exact absurd (mem_univ w) h

lemma sum_Sc (I : Instance N M) (σ : Allocation N M) :
    ∑ u, Sc I σ u M = ∑ v, mx I σ v := by
  unfold Sc mx
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun v _ => sum_congr rfl (fun u _ => ?_))
  simp only [v.isLt, true_and]

lemma revenue_nonneg (I : Instance N M) (σ : Allocation N M) : 0 ≤ revenue I σ :=
  sum_nonneg (fun u _ => spend_nonneg I σ u M)

lemma main_bound (I : Instance N M) (σ : Allocation N M) (hrun : IsRun I σ) {η : ℝ}
    (hη0 : 0 ≤ η) (hη2 : η ≤ 1 / 2) (hη : SmallBids I η) (τ : Allocation N M) :
    (1 - Real.exp (-1)) * revenue I τ ≤ (1 + 3 * η) * revenue I σ := by
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have htot : (Real.exp 1 - 1) * revenue I τ
      ≤ (1 + 3 * η) * Real.exp 1 * revenue I σ := by
    unfold revenue
    rw [mul_sum, mul_sum]
    calc ∑ u, (Real.exp 1 - 1) * spend I τ u M
        ≤ ∑ u, (W I σ η u + Real.exp 1 *
            ∑ v ∈ univ.filter (fun v : Fin M => v.val < M ∧ τ v = some u), mx I σ v) :=
          sum_le_sum (fun u _ => dual_u I σ hrun hη0 hη τ u)
      _ = ∑ u, W I σ η u + Real.exp 1 * ∑ u,
            ∑ v ∈ univ.filter (fun v : Fin M => v.val < M ∧ τ v = some u), mx I σ v := by
          rw [sum_add_distrib, mul_sum]
      _ ≤ ∑ u, W I σ η u + Real.exp 1 * ∑ v, mx I σ v := by
          have := mul_le_mul_of_nonneg_left (route I σ τ) hE.le
          linarith
      _ = ∑ u, (W I σ η u + Real.exp 1 * Sc I σ u M) := by
          rw [sum_add_distrib, ← mul_sum, sum_Sc]
      _ ≤ ∑ u, (1 + 3 * η) * Real.exp 1 * spend I σ u M :=
          sum_le_sum (fun u _ => per_u I σ hrun hη0 hη2 hη u)
  have hc : Real.exp 1 * (1 - Real.exp (-1)) = Real.exp 1 - 1 := by
    have : Real.exp 1 * Real.exp (-1) = 1 := by
      rw [← Real.exp_add]
      simp
    linear_combination (-1 : ℝ) * this
  have h3 : Real.exp 1 * ((1 - Real.exp (-1)) * revenue I τ)
      ≤ Real.exp 1 * ((1 + 3 * η) * revenue I σ) := by
    have e1 : Real.exp 1 * ((1 - Real.exp (-1)) * revenue I τ)
        = (Real.exp 1 - 1) * revenue I τ := by rw [← hc]; ring
    have e2 : Real.exp 1 * ((1 + 3 * η) * revenue I σ)
        = (1 + 3 * η) * Real.exp 1 * revenue I σ := by ring
    rw [e1, e2]
    exact htot
  exact le_of_mul_le_mul_left h3 hE

lemma part1 : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (N M : ℕ) (I : Instance N M), SmallBids I η →
      ∀ σ : Allocation N M, IsRun I σ → ∀ τ : Allocation N M,
        (1 - Real.exp (-1) - ε) * revenue I τ ≤ revenue I σ := by
  intro ε hε
  refine ⟨min (1 / 4) (ε / 3), lt_min (by norm_num) (by linarith), ?_⟩
  intro N M I hsb σ hrun τ
  set η := min (1 / 4 : ℝ) (ε / 3) with hηdef
  have hη0 : 0 ≤ η := le_of_lt (lt_min (by norm_num) (by linarith))
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hηε : η ≤ ε / 3 := min_le_right _ _
  have hmain := main_bound I σ hrun hη0 (by linarith) hsb τ
  set c := 1 - Real.exp (-1) with hcdef
  have hc1 : c ≤ 1 := by
    have := Real.exp_pos (-1)
    linarith
  have hτ0 := revenue_nonneg I τ
  have hσ0 := revenue_nonneg I σ
  have h1 : (c - ε) * revenue I τ ≤ (c - 3 * η) * revenue I τ :=
    mul_le_mul_of_nonneg_right (by linarith) hτ0
  have h2 : (c - 3 * η) * revenue I τ ≤ (1 - 3 * η) * (c * revenue I τ) := by
    nlinarith [mul_nonneg (mul_nonneg hη0 (sub_nonneg.mpr hc1)) hτ0]
  have h3 : (1 - 3 * η) * (c * revenue I τ) ≤ (1 - 3 * η) * ((1 + 3 * η) * revenue I σ) :=
    mul_le_mul_of_nonneg_left hmain (by linarith)
  have h4 : (1 - 3 * η) * ((1 + 3 * η) * revenue I σ) ≤ revenue I σ := by
    nlinarith [mul_nonneg (mul_nonneg hη0 hη0) hσ0]
  linarith

end MehtaOnlineAdAllocation.MSVV.P1Aux

open MehtaOnlineAdAllocation.MSVV in
theorem MehtaOnlineAdAllocation.MSVV.P1Aux.part2 :
    (∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∀ A : (N B : ℕ) → AdWordsMSVV.LowerBound.RandAlg N (N * B),
      ∃ N B : ℕ, 0 < N ∧ 1 ≤ B ∧ 1 ≤ η * (B : ℝ) ∧
      ∃ (I : AdWordsMSVV.LowerBound.Instance N (N * B))
        (τ : Fin (N * B) → Option (Fin N)),
        AdWordsMSVV.LowerBound.offlineRevenue B I τ = N * B ∧
        AdWordsMSVV.LowerBound.expectedRevenue B I (A N B) ≤
          (1 - Real.exp (-1) + ε) * ((N : ℝ) * (B : ℝ))) := by
  intro ε hε η hη A
  obtain ⟨N₀, hN₀⟩ := AdWordsMSVV.LowerBound.KVVAux.kvv_theorem_9 ε hε
  set N := max N₀ 1 with hNdef
  set B := max 1 ⌈1 / η⌉₊ with hBdef
  have hN : 0 < N := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  have hB : 1 ≤ B := le_max_left _ _
  have hηB : 1 ≤ η * (B : ℝ) := by
    have h1 : (1 / η) ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / η⌉₊ : ℝ) ≤ (B : ℝ) := by exact_mod_cast le_max_right _ _
    have h3 : η * (1 / η) = 1 := by field_simp
    have h4 := mul_le_mul_of_nonneg_left (le_trans h1 h2) hη.le
    linarith
  obtain ⟨I, τ, h1, h2⟩ := hN₀ N (le_max_left _ _) B hB (A N B)
  exact ⟨N, B, hN, hB, hηB, I, τ, h1, h2⟩

open MehtaOnlineAdAllocation.MSVV in
theorem solution :
    (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (N M : ℕ) (I : Instance N M), SmallBids I η →
      ∀ σ : Allocation N M, IsRun I σ → ∀ τ : Allocation N M,
        (1 - Real.exp (-1) - ε) * revenue I τ ≤ revenue I σ) ∧
    (∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∀ A : (N B : ℕ) → AdWordsMSVV.LowerBound.RandAlg N (N * B),
      ∃ N B : ℕ, 0 < N ∧ 1 ≤ B ∧ 1 ≤ η * (B : ℝ) ∧
      ∃ (I : AdWordsMSVV.LowerBound.Instance N (N * B))
        (τ : Fin (N * B) → Option (Fin N)),
        AdWordsMSVV.LowerBound.offlineRevenue B I τ = N * B ∧
        AdWordsMSVV.LowerBound.expectedRevenue B I (A N B) ≤
          (1 - Real.exp (-1) + ε) * ((N : ℝ) * (B : ℝ))) := by
  exact ⟨MehtaOnlineAdAllocation.MSVV.P1Aux.part1, MehtaOnlineAdAllocation.MSVV.P1Aux.part2⟩

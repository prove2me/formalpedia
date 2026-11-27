-- Prove2me | solution 1 for LinearChoresCLS.epsQKKT_cls_reduction
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:38:51.010001+00:00
-- url     : https://prove2.me/submissions/34ab1e84-28ad-46af-a459-a02a46b17afc

import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_EpsKKT

set_option autoImplicit false


namespace ClsTotal
open NetworkEquilibriumCLS.LinearNash

def IsRatR (r : ℝ) : Prop := ∃ q : ℚ, r = q

theorem isRat_getD (l : List ℝ) (h : ∀ r ∈ l, IsRatR r) (i : ℕ) : IsRatR (l[i]?.getD 0) := by
  cases hl : l[i]? with
  | none => exact ⟨0, by simp⟩
  | some r => exact h r (List.mem_of_getElem? hl)

theorem isRat_gateEval (x prior : List ℝ) (hx : ∀ r ∈ x, IsRatR r) (hp : ∀ r ∈ prior, IsRatR r)
    (g : ArithmeticGate) : IsRatR (gateEval x prior g) := by
  cases g with
  | input i => exact isRat_getD x hx i
  | constant r => exact ⟨r, rfl⟩
  | add a b =>
    obtain ⟨u, hu⟩ := isRat_getD prior hp a; obtain ⟨v, hv⟩ := isRat_getD prior hp b
    exact ⟨u + v, by simp only [gateEval, hu, hv]; push_cast; rfl⟩
  | sub a b =>
    obtain ⟨u, hu⟩ := isRat_getD prior hp a; obtain ⟨v, hv⟩ := isRat_getD prior hp b
    exact ⟨u - v, by simp only [gateEval, hu, hv]; push_cast; rfl⟩
  | mul a b =>
    obtain ⟨u, hu⟩ := isRat_getD prior hp a; obtain ⟨v, hv⟩ := isRat_getD prior hp b
    exact ⟨u * v, by simp only [gateEval, hu, hv]; push_cast; rfl⟩
  | minimum a b =>
    obtain ⟨u, hu⟩ := isRat_getD prior hp a; obtain ⟨v, hv⟩ := isRat_getD prior hp b
    exact ⟨min u v, by simp only [gateEval, hu, hv]; push_cast; rfl⟩
  | maximum a b =>
    obtain ⟨u, hu⟩ := isRat_getD prior hp a; obtain ⟨v, hv⟩ := isRat_getD prior hp b
    exact ⟨max u v, by simp only [gateEval, hu, hv]; push_cast; rfl⟩
  | test a b =>
    obtain ⟨u, hu⟩ := isRat_getD prior hp a; obtain ⟨v, hv⟩ := isRat_getD prior hp b
    refine ⟨if v < u then 1 else 0, ?_⟩
    simp only [gateEval, hu, hv]
    split_ifs with h1 h2 h2 <;> first | (push_cast; rfl) | (exact absurd (by exact_mod_cast h1) h2) |
      (exact absurd (by exact_mod_cast h2) h1)

theorem isRat_fold (x : List ℝ) (hx : ∀ r ∈ x, IsRatR r) (gs : List ArithmeticGate) :
    ∀ prior : List ℝ, (∀ r ∈ prior, IsRatR r) →
      ∀ r ∈ gs.foldl (fun prior g => prior ++ [gateEval x prior g]) prior, IsRatR r := by
  induction gs with
  | nil => intro prior hp; simpa using hp
  | cons g gs ih =>
    intro prior hp
    simp only [List.foldl_cons]
    apply ih
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hp r hr
    · exact isRat_gateEval x prior hx hp g

theorem isRat_clip (r : ℝ) (h : IsRatR r) : IsRatR (clip r) := by
  obtain ⟨q, rfl⟩ := h
  exact ⟨max 0 (min 1 q), by simp [clip]⟩

theorem isRat_outputs (C : CLSInstance) (z : Fin 3 → ℚ) (j : Fin 4) :
    IsRatR (circuitOutputs C (fun i => (z i : ℝ)) j) := by
  unfold circuitOutputs
  apply isRat_clip
  apply isRat_getD
  apply isRat_fold
  · intro r hr
    simp only [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    exact ⟨z i, rfl⟩
  · simp

theorem clip_mem (r : ℝ) : 0 ≤ clip r ∧ clip r ≤ 1 := by
  unfold clip; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

end ClsTotal

namespace ClsTotal
open NetworkEquilibriumCLS.LinearNash

/-- rational move. -/
theorem move_rat (C : CLSInstance) (z : Fin 3 → ℚ) :
    ∃ w : Fin 3 → ℚ, (fun i => (w i : ℝ)) = clsMove C (fun i => (z i : ℝ)) ∧
      InCube (fun i => (w i : ℝ)) := by
  have h : ∀ i : Fin 3, IsRatR (clsMove C (fun i => (z i : ℝ)) i) := fun i =>
    isRat_outputs C z ⟨i.val + 1, by omega⟩
  choose w hw using h
  refine ⟨w, funext fun i => (hw i).symm, fun i => ?_⟩
  show 0 ≤ (w i : ℝ) ∧ (w i : ℝ) ≤ 1
  rw [← hw i]
  exact clip_mem _

theorem cls_total (C : CLSInstance) (hC : C.Valid) : ∃ t, clsSearch.answer (encCLS C) t := by
  by_contra hno
  push_neg at hno
  have hε : 0 < C.epsilon := hC.1
  have hL : 0 < C.lipschitz := hC.2.1
  set P := clsPotential C
  -- no local optimum answer
  have h1 : ∀ z : Fin 3 → ℚ, InCube (fun i => (z i : ℝ)) →
      P (clsMove C (fun i => (z i : ℝ))) < P (fun i => (z i : ℝ)) - C.epsilon := by
    intro z hz
    by_contra h
    push_neg at h
    exact hno (false :: encVector z) ⟨C, hC, rfl, Or.inl ⟨z, rfl, hz, h⟩⟩
  -- potential is Lipschitz on rational points
  have h2 : ∀ z w : Fin 3 → ℚ, InCube (fun i => (z i : ℝ)) → InCube (fun i => (w i : ℝ)) →
      |P (fun i => (z i : ℝ)) - P (fun i => (w i : ℝ))| ≤
        (C.lipschitz : ℝ) * distance3 (fun i => (z i : ℝ)) (fun i => (w i : ℝ)) := by
    intro z w hz hw
    by_contra h
    push_neg at h
    exact hno (true :: false :: (encVector z ++ encVector w))
      ⟨C, hC, rfl, Or.inr ⟨z, w, false, rfl, hz, hw, by simpa using h⟩⟩
  -- grid
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((C.lipschitz : ℝ) / C.epsilon)
  set N := N0 + 1
  have hNpos : (0 : ℝ) < N := by positivity
  let pt : (Fin 3 → Fin (N + 1)) → (Fin 3 → ℚ) := fun k i => ((k i : ℕ) : ℚ) / N
  have hpt : ∀ k, InCube (fun i => ((pt k i : ℚ) : ℝ)) := by
    intro k i
    simp only [pt]
    have hk : ((k i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (k i).isLt
    push_cast
    constructor
    · positivity
    · rw [div_le_one hNpos]; exact hk
  obtain ⟨kstar, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun k => P (fun i => ((pt k i : ℚ) : ℝ))) ⟨fun _ => 0, Finset.mem_univ _⟩
  obtain ⟨w, hw, hwc⟩ := move_rat C (pt kstar)
  -- round w to the grid
  have hfl : ∀ i, (⌊(N : ℚ) * w i⌋₊ : ℚ) ≤ N * w i ∧ (N : ℚ) * w i < ⌊(N : ℚ) * w i⌋₊ + 1 := by
    intro i
    have h0' : (0 : ℝ) ≤ (w i : ℝ) := (hwc i).1
    have h0 : (0 : ℚ) ≤ w i := by exact_mod_cast h0'
    exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have hwi : ∀ i, ⌊(N : ℚ) * w i⌋₊ < N + 1 := by
    intro i
    have h0' : (w i : ℝ) ≤ 1 := (hwc i).2
    have h0 : w i ≤ 1 := by exact_mod_cast h0'
    have h3 : (⌊(N : ℚ) * w i⌋₊ : ℚ) ≤ N := by
      have := (hfl i).1
      have : (N : ℚ) * w i ≤ N := by nlinarith [(Nat.cast_nonneg N : (0:ℚ) ≤ N)]
      linarith
    have : ⌊(N : ℚ) * w i⌋₊ ≤ N := by exact_mod_cast h3
    omega
  let k' : Fin 3 → Fin (N + 1) := fun i => ⟨⌊(N : ℚ) * w i⌋₊, hwi i⟩
  have hNq : (0 : ℚ) < N := by positivity
  have hd : ∀ i, |(w i : ℝ) - ((pt k' i : ℚ) : ℝ)| ≤ 1 / N := by
    intro i
    have e : ((pt k' i : ℚ) : ℝ) = ((⌊(N : ℚ) * w i⌋₊ : ℚ) / N : ℚ) := rfl
    rw [e]
    have : |w i - (⌊(N : ℚ) * w i⌋₊ : ℚ) / N| ≤ 1 / N := by
      obtain ⟨a, b⟩ := hfl i
      have e : w i - (⌊(N : ℚ) * w i⌋₊ : ℚ) / N = ((N : ℚ) * w i - ⌊(N : ℚ) * w i⌋₊) / N := by
        field_simp
      rw [e, abs_div, abs_of_pos hNq]
      apply div_le_div_of_nonneg_right _ hNq.le
      rw [abs_le]; constructor <;> linarith
    have := (Rat.cast_le (K := ℝ)).mpr this
    push_cast at this ⊢
    exact this
  have hdist : distance3 (fun i => (w i : ℝ)) (fun i => ((pt k' i : ℚ) : ℝ)) ≤ 1 / N := by
    unfold distance3
    exact max_le (hd 0) (max_le (hd 1) (hd 2))
  have hlip := h2 w (pt k') hwc (hpt k')
  have hstep := h1 (pt kstar) (hpt kstar)
  rw [← hw] at hstep
  have hm := hmin k' (Finset.mem_univ _)
  have hLN : (C.lipschitz : ℝ) * (1 / N) < C.epsilon := by
    have hεr : (0 : ℝ) < C.epsilon := by exact_mod_cast hε
    have hN0' : (C.lipschitz : ℝ) / C.epsilon < N := by
      have : ((N0 : ℕ) : ℝ) < N := by simp [N]
      linarith
    rw [div_lt_iff₀ hεr] at hN0'
    rw [mul_one_div, div_lt_iff₀ hNpos]
    linarith
  have hLd : (C.lipschitz : ℝ) * distance3 (fun i => (w i : ℝ)) (fun i => ((pt k' i : ℚ) : ℝ)) ≤
      (C.lipschitz : ℝ) * (1 / N) :=
    mul_le_mul_of_nonneg_left hdist (by exact_mod_cast hL.le)
  have := (abs_le.mp hlip).1
  linarith

end ClsTotal


open NetworkEquilibriumCLS.LinearNash LinearChoresCLS

theorem encNat_len_pos' (n : ℕ) : 1 ≤ (encNat n).length := by simp [encNat]; omega

theorem encVector_len {n : ℕ} (hn : 0 < n) (z : Fin n → ℚ) : 2 ≤ (encVector z).length := by
  have h1 := encNat_len_pos' n
  have h2 : 1 ≤ (encRat (z ⟨0, hn⟩)).length := by simp [encRat, encInt]
  have h3 : (encRat (z ⟨0, hn⟩)).length ≤ ((List.ofFn z).flatMap encRat).length := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [List.ofFn_succ]
  simp only [encVector, encList, List.length_append, List.length_ofFn] at *
  omega

def P0 : Quadratic 1 := ⟨fun _ _ => 0, fun _ => 0, fun _ _ => rfl⟩

theorem solution : ¬ (∀ k : ℕ, SearchReduces (bounded epsQKKTSearch k) clsSearch) := by
  intro h
  obtain ⟨f, g, -, -, hred⟩ := h 0
  obtain ⟨hv, hans⟩ := hred (encQuadratic P0 ++ encRat 1) ⟨1, one_pos, P0, 1, one_pos, rfl⟩
  obtain ⟨C, hC, hCe⟩ := hv
  obtain ⟨t, ht⟩ := ClsTotal.cls_total C hC
  rw [hCe] at ht
  obtain ⟨hA, hlen⟩ := hans t ht
  obtain ⟨n, hn, P, ε, -, -, z, hy, -⟩ := hA
  rw [← hy] at hlen
  have := encVector_len hn z
  simp at hlen
  omega

-- Prove2me | solution 1 for LimitedBFGS.SQN.sqn_eq_pcg
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:28:05.933205+00:00
-- url     : https://prove2.me/submissions/0341b01f-453e-4f70-8596-238ec5dc220d

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_sqnIter
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix


namespace LimitedBFGS.SQN

section Dev
variable {n : ℕ}

lemma dv_bfgsStep_mulVec_of_orth (H : Matrix (Fin n) (Fin n) ℝ) (s y g : Fin n → ℝ)
    (hs : s ⬝ᵥ g = 0) :
    bfgsStep H s y *ᵥ g = H *ᵥ g - (bfgsRho s y * (y ⬝ᵥ (H *ᵥ g))) • s := by
  have hv : bfgsV s y *ᵥ g = g := by
    simp [bfgsV, sub_mulVec, smul_mulVec, vecMulVec_mulVec, hs]
  have hvT : ∀ w, (bfgsV s y)ᵀ *ᵥ w = w - (bfgsRho s y * (y ⬝ᵥ w)) • s := by
    intro w
    simp [bfgsV, transpose_sub, transpose_smul, transpose_vecMulVec, sub_mulVec,
      smul_mulVec, vecMulVec_mulVec, smul_smul, mul_comm]
  rw [bfgsStep, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hv, hvT, smul_mulVec,
    vecMulVec_mulVec, hs]
  simp

lemma dv_foldl_fix (g w : Fin n → ℝ) (L : List ((Fin n → ℝ) × (Fin n → ℝ)))
    (hL : ∀ p ∈ L, p.1 ⬝ᵥ g = 0 ∧ p.2 ⬝ᵥ w = 0) :
    ∀ H : Matrix (Fin n) (Fin n) ℝ, H *ᵥ g = w →
      (L.foldl (fun H p => bfgsStep H p.1 p.2) H) *ᵥ g = w := by
  induction L with
  | nil => intro H hH; simpa using hH
  | cons p L ih =>
    intro H hH
    rw [List.foldl_cons]
    apply ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    rw [dv_bfgsStep_mulVec_of_orth _ _ _ _ (hL p (by simp)).1, hH, (hL p (by simp)).2]
    simp

lemma dv_symm (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsHermitian) (u v : Fin n → ℝ) :
    u ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (M *ᵥ u) := by
  have hT : Mᵀ = M := by
    have := hM.eq
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]

lemma dv_pos (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosDef) {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < x ⬝ᵥ (M *ᵥ x) := by
  simpa using hM.dotProduct_mulVec_pos hx

variable (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ)
  (x₀ : Fin n → ℝ)

noncomputable def gP (k : ℕ) : Fin n → ℝ := grad A b (pcgIter A b H₀ x₀ k).x
noncomputable def dP (k : ℕ) : Fin n → ℝ := (pcgIter A b H₀ x₀ k).d
noncomputable def aP (k : ℕ) : ℝ := exactStep A b (pcgIter A b H₀ x₀ k).x (dP A b H₀ x₀ k)

lemma x_succ (k : ℕ) : (pcgIter A b H₀ x₀ (k+1)).x
    = (pcgIter A b H₀ x₀ k).x + aP A b H₀ x₀ k • dP A b H₀ x₀ k := rfl

lemma g_succ (k : ℕ) : gP A b H₀ x₀ (k+1) = gP A b H₀ x₀ k + aP A b H₀ x₀ k • (A *ᵥ dP A b H₀ x₀ k) := by
  unfold gP grad
  rw [x_succ, mulVec_add, mulVec_smul]
  abel

lemma d_succ (k : ℕ) : dP A b H₀ x₀ (k+1) = -(H₀ *ᵥ gP A b H₀ x₀ (k+1)) +
    (((gP A b H₀ x₀ (k+1) - gP A b H₀ x₀ k) ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ (k+1))) /
      ((gP A b H₀ x₀ (k+1) - gP A b H₀ x₀ k) ⬝ᵥ dP A b H₀ x₀ k)) • dP A b H₀ x₀ k := rfl

lemma d_zero : dP A b H₀ x₀ 0 = -(H₀ *ᵥ gP A b H₀ x₀ 0) := rfl

lemma a_def (k : ℕ) : aP A b H₀ x₀ k = -(gP A b H₀ x₀ k ⬝ᵥ dP A b H₀ x₀ k) /
    (dP A b H₀ x₀ k ⬝ᵥ (A *ᵥ dP A b H₀ x₀ k)) := rfl

lemma gzero_dzero (k : ℕ) (h : gP A b H₀ x₀ k = 0) : dP A b H₀ x₀ k = 0 := by
  cases k with
  | zero => rw [d_zero, h]; simp
  | succ k => rw [d_succ, h]; simp

lemma gd_eq (k : ℕ) (hO : ∀ i < k, gP A b H₀ x₀ k ⬝ᵥ dP A b H₀ x₀ i = 0) :
    gP A b H₀ x₀ k ⬝ᵥ dP A b H₀ x₀ k = -(gP A b H₀ x₀ k ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ k)) := by
  cases k with
  | zero => rw [d_zero]; simp
  | succ k =>
    conv_lhs => rw [d_succ]
    rw [dotProduct_add, dotProduct_smul, hO k (Nat.lt_succ_self k)]
    simp

lemma a_ne (hA : A.PosDef) (hH₀ : H₀.PosDef) (k : ℕ)
    (hO : ∀ i < k, gP A b H₀ x₀ k ⬝ᵥ dP A b H₀ x₀ i = 0) (hd : dP A b H₀ x₀ k ≠ 0) :
    aP A b H₀ x₀ k ≠ 0 := by
  have hg : gP A b H₀ x₀ k ≠ 0 := fun h => hd (gzero_dzero A b H₀ x₀ k h)
  have h1 := dv_pos H₀ hH₀ hg
  have h2 := dv_pos A hA hd
  rw [a_def, gd_eq A b H₀ x₀ k hO]
  apply div_ne_zero _ h2.ne'
  simp [h1.ne']

lemma gd_succ (hA : A.PosDef) (k : ℕ) : gP A b H₀ x₀ (k+1) ⬝ᵥ dP A b H₀ x₀ k = 0 := by
  by_cases hd : dP A b H₀ x₀ k = 0
  · simp [hd]
  have h2 := dv_pos A hA hd
  rw [g_succ, add_dotProduct, smul_dotProduct, a_def, dotProduct_comm (A *ᵥ _)]
  simp only [smul_eq_mul]
  field_simp
  ring

lemma gH_zero (k : ℕ) (hO : ∀ i < k+1, gP A b H₀ x₀ (k+1) ⬝ᵥ dP A b H₀ x₀ i = 0) :
    ∀ l ≤ k, gP A b H₀ x₀ (k+1) ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ l) = 0 := by
  intro l hl
  cases l with
  | zero =>
    have : H₀ *ᵥ gP A b H₀ x₀ 0 = -dP A b H₀ x₀ 0 := by rw [d_zero, neg_neg]
    rw [this, dotProduct_neg, hO 0 (by omega), neg_zero]
  | succ l =>
    have : H₀ *ᵥ gP A b H₀ x₀ (l+1) = -dP A b H₀ x₀ (l+1) +
      (((gP A b H₀ x₀ (l+1) - gP A b H₀ x₀ l) ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ (l+1))) /
      ((gP A b H₀ x₀ (l+1) - gP A b H₀ x₀ l) ⬝ᵥ dP A b H₀ x₀ l)) • dP A b H₀ x₀ l := by
      rw [d_succ]; abel
    rw [this, dotProduct_add, dotProduct_neg, dotProduct_smul, hO (l+1) (by omega),
      hO l (by omega)]
    simp

def Inv (k : ℕ) : Prop := ∀ j ≤ k, (∀ i < j, gP A b H₀ x₀ j ⬝ᵥ dP A b H₀ x₀ i = 0) ∧
  (∀ i < j, dP A b H₀ x₀ j ⬝ᵥ (A *ᵥ dP A b H₀ x₀ i) = 0)

lemma inv_all (hA : A.PosDef) (hH₀ : H₀.PosDef) : ∀ k, Inv A b H₀ x₀ k := by
  intro k
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro j hj
    rcases Nat.lt_or_ge j (k+1) with hjk | hjk
    · exact ih j (by omega)
    obtain rfl : j = k + 1 := by omega
    have hO : ∀ i < k+1, gP A b H₀ x₀ (k+1) ⬝ᵥ dP A b H₀ x₀ i = 0 := by
      intro i hi
      rcases Nat.lt_or_ge i k with hik | hik
      · rw [g_succ, add_dotProduct, smul_dotProduct, (ih k le_rfl).1 i hik, dotProduct_comm,
          dv_symm A hA.1, (ih k le_rfl).2 i hik]
        simp
      · obtain rfl : i = k := by omega
        exact gd_succ A b H₀ x₀ hA i
    have hGH := gH_zero A b H₀ x₀ k hO
    refine ⟨hO, ?_⟩
    intro i hi
    by_cases hdi : dP A b H₀ x₀ i = 0
    · simp [hdi]
    have hai := a_ne A b H₀ x₀ hA hH₀ i (ih i (by omega)).1 hdi
    -- α_i • A d_i = g_{i+1} - g_i
    have hy : aP A b H₀ x₀ i • (A *ᵥ dP A b H₀ x₀ i) = gP A b H₀ x₀ (i+1) - gP A b H₀ x₀ i := by
      rw [g_succ]; abel
    rw [d_succ, add_dotProduct, neg_dotProduct, smul_dotProduct]
    rcases Nat.lt_or_ge i k with hik | hik
    · have h1 : (H₀ *ᵥ gP A b H₀ x₀ (k+1)) ⬝ᵥ (A *ᵥ dP A b H₀ x₀ i) = 0 := by
        have : aP A b H₀ x₀ i * ((H₀ *ᵥ gP A b H₀ x₀ (k+1)) ⬝ᵥ (A *ᵥ dP A b H₀ x₀ i)) = 0 := by
          rw [← smul_eq_mul, ← dotProduct_smul, hy, dotProduct_sub,
            dotProduct_comm (H₀ *ᵥ gP A b H₀ x₀ (k+1)), dotProduct_comm (H₀ *ᵥ gP A b H₀ x₀ (k+1)),
            dv_symm H₀ hH₀.1 (gP A b H₀ x₀ (i+1)), dv_symm H₀ hH₀.1 (gP A b H₀ x₀ i),
            hGH (i+1) (by omega), hGH i (by omega), sub_zero]
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hai
        · exact h
      rw [h1, (ih k le_rfl).2 i hik]
      simp
    · obtain rfl : i = k := by omega
      have h2 := dv_pos A hA hdi
      rw [← hy, smul_dotProduct, smul_dotProduct, dotProduct_comm (A *ᵥ dP A b H₀ x₀ i)
        (dP A b H₀ x₀ i), dotProduct_comm (H₀ *ᵥ _) (A *ᵥ dP A b H₀ x₀ i)]
      simp only [smul_eq_mul]
      field_simp
      ring

lemma gHg_orth (hA : A.PosDef) (hH₀ : H₀.PosDef) (i j : ℕ) (hij : i ≠ j) :
    gP A b H₀ x₀ i ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ j) = 0 := by
  have key : ∀ i j, j < i → gP A b H₀ x₀ i ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ j) = 0 := by
    intro i j hji
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact gH_zero A b H₀ x₀ k ((inv_all A b H₀ x₀ hA hH₀ (k+1)) (k+1) le_rfl).1 j (by omega)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · rw [dv_symm H₀ hH₀.1]; exact key j i h
  · exact key i j h

theorem sqn_eq_pcg_core (hA : A.PosDef) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m) (i : ℕ) :
    (sqnIter A b H₀ m x₀ i).x = (pcgIter A b H₀ x₀ i).x ∧
      sqnDir A b H₀ (sqnIter A b H₀ m x₀ i) = (pcgIter A b H₀ x₀ i).d ∧
      ∀ p ∈ (sqnIter A b H₀ m x₀ i).pairs, ∃ j < i,
        p = ((pcgIter A b H₀ x₀ (j+1)).x - (pcgIter A b H₀ x₀ j).x,
             gP A b H₀ x₀ (j+1) - gP A b H₀ x₀ j) := by
  induction i with
  | zero =>
    refine ⟨rfl, ?_, ?_⟩
    · simp [sqnDir, sqnIter, specialHList, pcgIter]
    · simp [sqnIter]
  | succ i ih =>
    obtain ⟨hx, hd, hpairs⟩ := ih
    have hx' : (sqnIter A b H₀ m x₀ (i+1)).x = (pcgIter A b H₀ x₀ (i+1)).x := by
      show (sqnIter A b H₀ m x₀ i).x + exactStep A b (sqnIter A b H₀ m x₀ i).x
        (sqnDir A b H₀ (sqnIter A b H₀ m x₀ i)) • sqnDir A b H₀ (sqnIter A b H₀ m x₀ i) = _
      rw [hx, hd]; rfl
    set L := (sqnIter A b H₀ m x₀ i).pairs with hL
    set q : (Fin n → ℝ) × (Fin n → ℝ) := ((pcgIter A b H₀ x₀ (i+1)).x - (pcgIter A b H₀ x₀ i).x,
             gP A b H₀ x₀ (i+1) - gP A b H₀ x₀ i) with hq
    have hp : (sqnIter A b H₀ m x₀ (i+1)).pairs = (L ++ [q]).drop ((L ++ [q]).length - m) := by
      show ((sqnIter A b H₀ m x₀ i).pairs ++ [((sqnIter A b H₀ m x₀ i).x + exactStep A b (sqnIter A b H₀ m x₀ i).x
        (sqnDir A b H₀ (sqnIter A b H₀ m x₀ i)) • sqnDir A b H₀ (sqnIter A b H₀ m x₀ i) - (sqnIter A b H₀ m x₀ i).x,
        grad A b ((sqnIter A b H₀ m x₀ i).x + exactStep A b (sqnIter A b H₀ m x₀ i).x
        (sqnDir A b H₀ (sqnIter A b H₀ m x₀ i)) • sqnDir A b H₀ (sqnIter A b H₀ m x₀ i)) - grad A b (sqnIter A b H₀ m x₀ i).x)]).drop _ = _
      rw [hx, hd]; rfl
    have hlen : (L ++ [q]).length - m ≤ L.length := by simp; omega
    have hp2 : (sqnIter A b H₀ m x₀ (i+1)).pairs = L.drop ((L ++ [q]).length - m) ++ [q] := by
      rw [hp, List.drop_append_of_le_length hlen]
    have hOall := ((inv_all A b H₀ x₀ hA hH₀ (i+1)) (i+1) le_rfl).1
    have hGH := gH_zero A b H₀ x₀ i hOall
    have hs_eq : ∀ j, (pcgIter A b H₀ x₀ (j+1)).x - (pcgIter A b H₀ x₀ j).x
        = aP A b H₀ x₀ j • dP A b H₀ x₀ j := by
      intro j; rw [x_succ]; abel
    refine ⟨hx', ?_, ?_⟩
    · have hq1 : q.1 ⬝ᵥ gP A b H₀ x₀ (i+1) = 0 := by
        rw [hq, hs_eq, smul_dotProduct, dotProduct_comm, gd_succ A b H₀ x₀ hA]; simp
      unfold sqnDir
      rw [hp2, hx', specialHList, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change -(bfgsStep _ q.1 q.2 *ᵥ gP A b H₀ x₀ (i+1)) = _
      rw [dv_bfgsStep_mulVec_of_orth _ _ _ _ hq1]
      rw [dv_foldl_fix (gP A b H₀ x₀ (i+1)) (H₀ *ᵥ gP A b H₀ x₀ (i+1)) _ ?_ H₀ rfl]
      · change _ = dP A b H₀ x₀ (i+1)
        rw [d_succ]
        have hy : gP A b H₀ x₀ (i+1) - gP A b H₀ x₀ i = aP A b H₀ x₀ i • (A *ᵥ dP A b H₀ x₀ i) := by
          rw [g_succ]; abel
        rw [hq]
        simp only [hs_eq, hy, bfgsRho, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_smul]
        have key : 1 / (aP A b H₀ x₀ i * (aP A b H₀ x₀ i * ((A *ᵥ dP A b H₀ x₀ i) ⬝ᵥ dP A b H₀ x₀ i))) *
            (aP A b H₀ x₀ i * ((A *ᵥ dP A b H₀ x₀ i) ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ (i + 1)))) * aP A b H₀ x₀ i
            = aP A b H₀ x₀ i * ((A *ᵥ dP A b H₀ x₀ i) ⬝ᵥ (H₀ *ᵥ gP A b H₀ x₀ (i + 1))) /
              (aP A b H₀ x₀ i * ((A *ᵥ dP A b H₀ x₀ i) ⬝ᵥ dP A b H₀ x₀ i)) := by
          by_cases ha : aP A b H₀ x₀ i = 0
          · simp [ha]
          by_cases he : (A *ᵥ dP A b H₀ x₀ i) ⬝ᵥ dP A b H₀ x₀ i = 0
          · simp [he]
          field_simp
        rw [key]
        abel
      · intro p hpm
        obtain ⟨j, hj, rfl⟩ := hpairs p (List.mem_of_mem_drop hpm)
        constructor
        · simp only
          rw [hs_eq, smul_dotProduct, dotProduct_comm, hOall j (by omega)]; simp
        · simp only
          rw [sub_dotProduct, dv_symm H₀ hH₀.1 (gP A b H₀ x₀ (j+1)),
            dv_symm H₀ hH₀.1 (gP A b H₀ x₀ j), hGH (j+1) (by omega), hGH j (by omega), sub_zero]
    · intro p hpm
      rw [hp2] at hpm
      rcases List.mem_append.1 hpm with h | h
      · obtain ⟨j, hj, hpj⟩ := hpairs p (List.mem_of_mem_drop h)
        exact ⟨j, by omega, hpj⟩
      · rw [List.mem_singleton] at h
        exact ⟨i, by omega, h⟩

theorem sqn_eq_pcg_main (hA : A.PosDef) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m) (i : ℕ) :
    (sqnIter A b H₀ m x₀ i).x = (pcgIter A b H₀ x₀ i).x ∧
      sqnDir A b H₀ (sqnIter A b H₀ m x₀ i) = (pcgIter A b H₀ x₀ i).d :=
  ⟨(sqn_eq_pcg_core A b H₀ x₀ hA hH₀ m hm i).1, (sqn_eq_pcg_core A b H₀ x₀ hA hH₀ m hm i).2.1⟩

theorem sqn_term_core (hA : A.PosDef) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m) :
    ∃ k ≤ n, grad A b (sqnIter A b H₀ m x₀ k).x = 0 := by
  by_contra hcon
  push_neg at hcon
  have hne : ∀ k ≤ n, gP A b H₀ x₀ k ≠ 0 := by
    intro k hk
    have := hcon k hk
    rwa [(sqn_eq_pcg_core A b H₀ x₀ hA hH₀ m hm k).1] at this
  let v : Fin (n+1) → (Fin n → ℝ) := fun i => gP A b H₀ x₀ i
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h0 : (∑ i, c i • v i) ⬝ᵥ (H₀ *ᵥ v j) = 0 := by rw [hc]; simp
    rw [sum_dotProduct, Finset.sum_eq_single j] at h0
    · rw [smul_dotProduct, smul_eq_mul] at h0
      have hp := dv_pos H₀ hH₀ (hne j (by omega))
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hp.ne'
    · intro i _ hij
      rw [smul_dotProduct, gHg_orth A b H₀ x₀ hA hH₀ i j (fun h => hij (Fin.ext h))]
      simp
    · simp
  have := hli.fintype_card_le_finrank
  simp at this

end Dev
end LimitedBFGS.SQN

open LimitedBFGS.SQN


theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (b : Fin n → ℝ)
    (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (m : ℕ) (hm : 1 ≤ m)
    (x₀ : Fin n → ℝ) (i : ℕ) :
    (sqnIter A b H₀ m x₀ i).x = (pcgIter A b H₀ x₀ i).x ∧
      sqnDir A b H₀ (sqnIter A b H₀ m x₀ i) = (pcgIter A b H₀ x₀ i).d := by
  exact sqn_eq_pcg_main A b H₀ x₀ hA hH₀ m hm i

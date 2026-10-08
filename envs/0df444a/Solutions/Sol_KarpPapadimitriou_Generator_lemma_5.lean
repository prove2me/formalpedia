-- Prove2me | solution 1 for KarpPapadimitriou.Generator.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:31:38.666984+00:00
-- url     : https://prove2.me/submissions/9321c571-ac80-43a4-992f-f7330f4a3e48

import Mathlib
import Definitions.Def_KarpPapadimitriou_Generator_Hyperplanes



namespace KarpPapadimitriou.Generator
open Matrix

lemma normalLength_le (n P : ℕ) (f : Fin n → ℤ) (g : ℤ) (h : SmallHyperplane P f g) :
    0 < normalLength f ∧ normalLength f ≤ 2 ^ (n + P) := by
  obtain ⟨hf, hb, _⟩ := h
  constructor
  · unfold normalLength
    apply Real.sqrt_pos.mpr
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc; push_neg at hc; exact hf (funext hc)
    calc (0:ℝ) < (f i : ℝ)^2 := by positivity
      _ ≤ _ := Finset.single_le_sum (f := fun i => ((f i : ℝ)^2)) (fun j _ => by positivity) (Finset.mem_univ i)
  · unfold normalLength
    rw [show ((2:ℝ) ^ (n + P)) = Real.sqrt (((2:ℝ)^(n+P))^2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    have : ∀ i, ((f i : ℝ))^2 ≤ ((2:ℝ)^P)^2 := by
      intro i
      have h1 : |(f i : ℝ)| ≤ 2^P := by
        have := hb i
        have : ((f i).natAbs : ℝ) ≤ 2^P := by exact_mod_cast this
        simpa [Nat.cast_natAbs] using this
      calc ((f i : ℝ))^2 = |(f i : ℝ)|^2 := (sq_abs _).symm
        _ ≤ ((2:ℝ)^P)^2 := by gcongr
    calc ∑ i : Fin n, ((f i : ℝ) ^ 2) ≤ ∑ i : Fin n, ((2:ℝ)^P)^2 := Finset.sum_le_sum (fun i _ => this i)
      _ = n * ((2:ℝ)^P)^2 := by simp
      _ ≤ (2:ℝ)^n * ((2:ℝ)^P)^2 := by
          gcongr
          exact_mod_cast (Nat.lt_two_pow_self).le
      _ ≤ ((2:ℝ)^(n+P))^2 := by
          rw [pow_add, mul_pow]
          have : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
          have h0 : (0:ℝ) ≤ ((2:ℝ)^P)^2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right (show (2:ℝ)^n ≤ (2^n)^2 by nlinarith) h0]

lemma tParam_ge (n P : ℕ) (c : Fin n → ℤ) (k : ℤ) : n + P ≤ tParam n P c k := by
  unfold tParam
  have h1 : n+1 ≤ (n+1)^2 := by nlinarith
  have h2 : (n+1)*(P+1) ≤ (n+1)^2*(P+1) := Nat.mul_le_mul_right _ h1
  have : n + P ≤ (n+1)^2*(P+1) := by nlinarith
  omega

theorem lemma4_core (n P : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (r : Fin n → ℚ) (f : Fin n → ℤ) (g : ℤ)
    (hsmall : SmallHyperplane P f g)
    (hden : ∀ i, (r i).den ≤ 2 ^ tParam n P c k)
    (hout : dotQ f r ≠ (g : ℚ)) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤
      hyperplaneDistance f g (realPoint r) := by
  set T := tParam n P c k with hT
  have hTge : n + P ≤ T := tParam_ge n P c k
  obtain ⟨hNpos, hNle⟩ := normalLength_le n P f g hsmall
  set D : ℕ := ∏ i, (r i).den with hD
  have hDle : D ≤ 2 ^ (T * n) := by
    calc D ≤ ∏ _i : Fin n, 2 ^ T := Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => hden i)
      _ = 2 ^ (T * n) := by simp [pow_mul]
  have hDpos : 0 < D := Finset.prod_pos (fun i _ => (r i).den_pos)
  have hint : ∀ i, ∃ z : ℤ, (D : ℚ) * r i = z := by
    intro i
    obtain ⟨e, he⟩ : (r i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    refine ⟨(e : ℤ) * (r i).num, ?_⟩
    have h1 : (r i) * (r i).den = (r i).num := Rat.mul_den_eq_num (r i)
    rw [he]; push_cast
    rw [← h1]; ring
  choose z hz using hint
  have hK : (D : ℚ) * (dotQ f r - g) = ((∑ i, f i * z i - D * g : ℤ) : ℚ) := by
    unfold dotQ
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← hz i]; ring
  have hKne : (∑ i, f i * z i - D * g : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at hK
    simp at hK
    rcases hK with h | h
    · exact absurd (by exact_mod_cast h : D = 0) hDpos.ne'
    · exact hout (by linarith)
  have hK1 : (1:ℝ) ≤ |(D:ℝ) * (((dotQ f r : ℚ) : ℝ) - g)| := by
    have : ((D : ℚ) * (dotQ f r - g) : ℚ) = ((∑ i, f i * z i - D * g : ℤ) : ℚ) := hK
    have h2 : (((D : ℚ) * (dotQ f r - g) : ℚ) : ℝ) = (((∑ i, f i * z i - D * g : ℤ) : ℚ) : ℝ) := by rw [this]
    push_cast at h2
    rw [h2]
    have : (1:ℤ) ≤ |(∑ i, f i * z i - D * g : ℤ)| := Int.one_le_abs hKne
    exact_mod_cast this
  have hdot : dotR f (realPoint r) = ((dotQ f r : ℚ) : ℝ) := by
    unfold dotR dotQ realPoint; push_cast; rfl
  unfold hyperplaneDistance
  rw [hdot]
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ D)] at hK1
  have hDle' : (D:ℝ) ≤ 2 ^ (T * n) := by exact_mod_cast hDle
  have hA : (1:ℝ) / 2^(T*n) ≤ |((dotQ f r : ℚ) : ℝ) - g| := by
    rw [div_le_iff₀ (by positivity)]
    calc (1:ℝ) ≤ D * |((dotQ f r : ℚ) : ℝ) - g| := hK1
      _ ≤ 2^(T*n) * |((dotQ f r : ℚ) : ℝ) - g| := by gcongr
      _ = _ := by ring
  have hNle' : normalLength f ≤ 2 ^ T := le_trans hNle (pow_le_pow_right₀ (by norm_num) hTge)
  rw [le_div_iff₀ hNpos]
  have h3 : (1:ℝ) / 2 ^ ((n + 1) * T) * normalLength f ≤ 1 / 2^(T*n) := by
    rw [show (n+1)*T = T*n + T by ring, pow_add]
    calc (1:ℝ) / (2^(T*n) * 2^T) * normalLength f ≤ 1 / (2^(T*n) * 2^T) * 2^T := by gcongr
      _ = 1 / 2^(T*n) := by field_simp
  linarith


lemma dotR_add_smul {n : ℕ} (f : Fin n → ℤ) (r q : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    dotR f (r + s • (q - r)) = dotR f r + s * (dotR f q - dotR f r) := by
  unfold dotR
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine congrArg₂ (· - ·) ?_ ?_ <;> (apply Finset.sum_congr rfl; intro i _; ring)

lemma u_const {n m : ℕ} (H : Fin m → (Fin n → ℤ) × ℤ) (f : Fin n → ℤ) (g : ℤ)
    (hdisjoint : hyperplane f g ∩ flat H = ∅)
    (r q : EuclideanSpace ℝ (Fin n)) (hr : r ∈ flat H) (hq : q ∈ flat H) :
    dotR f r - g = dotR f q - g := by
  by_contra hne
  have hne' : dotR f r - dotR f q ≠ 0 := fun h => hne (by linarith)
  set s : ℝ := (dotR f r - g) / (dotR f r - dotR f q) with hs
  have hz : r + s • (q - r) ∈ hyperplane f g ∩ flat H := by
    constructor
    · show dotR f _ = g
      rw [dotR_add_smul, hs]
      field_simp
      ring
    · intro i
      show dotR (H i).1 _ = _
      rw [dotR_add_smul]
      have h1 : dotR (H i).1 r = (H i).2 := hr i
      have h2 : dotR (H i).1 q = (H i).2 := hq i
      rw [h1, h2]; ring
  rw [hdisjoint] at hz
  exact hz

lemma sq_le_pow (n : ℕ) : n * n ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.lt_or_ge k 4 with hk | hk
    · interval_cases k <;> norm_num
    · have : 2 * k + 1 ≤ 2 ^ (k+2) := by
        have := Nat.lt_two_pow_self (n := k); nlinarith [pow_succ 2 k, pow_succ 2 (k+1)]
      calc (k+1)*(k+1) = k*k + (2*k+1) := by ring
        _ ≤ 2^(k+2) + 2^(k+2) := Nat.add_le_add ih this
        _ = 2^(k+1+2) := by ring


/-- Gram determinant facts. -/
lemma gram_facts (n P m : ℕ) (H : Fin m → (Fin n → ℤ) × ℤ)
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hind : IndependentNormals H) :
    m ≤ n ∧ (Matrix.of (fun i j => (H i).1 j) * (Matrix.of (fun i j => (H i).1 j))ᵀ).det ≠ 0 ∧
      (Matrix.of (fun i j => (H i).1 j) * (Matrix.of (fun i j => (H i).1 j))ᵀ).det.natAbs
        ≤ 2 ^ (n * (n + 2 + 2 * P)) := by
  classical
  have hmn : m ≤ n := by
    have := hind.fintype_card_le_finrank
    simpa using this
  let A : Matrix (Fin m) (Fin n) ℤ := Matrix.of fun i j => (H i).1 j
  let G : Matrix (Fin m) (Fin m) ℤ := A * A.transpose
  set d : ℤ := G.det with hd
  have hdne : d ≠ 0 := by
    intro h0
    have h0G : G.det = 0 := by rw [← hd]; exact h0
    have h0' : (G.map (Int.cast : ℤ → ℝ)).det = 0 := by
      have h := RingHom.map_det (Int.castRingHom ℝ) G
      rw [h0G] at h
      simpa using h.symm
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0'
    have hGR : G.map (Int.cast : ℤ → ℝ) = (A.map (Int.cast : ℤ → ℝ)) * (A.map (Int.cast : ℤ → ℝ)).transpose := by
      ext i j; simp [G, Matrix.mul_apply]
    set AR := A.map (Int.cast : ℤ → ℝ) with hAR
    have h1 : AR *ᵥ (v ᵥ* AR) = 0 := by
      rw [hGR, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose] at hv
      exact hv
    have hw : v ᵥ* AR = 0 := by
      have h2 : (v ᵥ* AR) ⬝ᵥ (v ᵥ* AR) = 0 := by
        calc (v ᵥ* AR) ⬝ᵥ (v ᵥ* AR) = (v ᵥ* AR) ⬝ᵥ (ARᵀ *ᵥ v) := by rw [Matrix.mulVec_transpose]
          _ = ((v ᵥ* AR) ᵥ* ARᵀ) ⬝ᵥ v := Matrix.dotProduct_mulVec (v ᵥ* AR) ARᵀ v
          _ = (AR *ᵥ (v ᵥ* AR)) ⬝ᵥ v := by rw [Matrix.vecMul_transpose]
          _ = 0 := by rw [h1]; simp
      exact dotProduct_self_eq_zero.mp h2
    apply hv0
    have := Fintype.linearIndependent_iff.mp hind v (by
      ext j
      have := congrFun hw j
      have e : ∀ x, AR x j = (((H x).1 j : ℤ) : ℝ) := fun x => rfl
      simp only [Matrix.vecMul, dotProduct, e] at this
      simpa [Finset.sum_apply, mul_comm] using this)
    funext i; exact this i
  refine ⟨hmn, hdne, ?_⟩
  have hdb : |d| ≤ (m.factorial : ℤ) * ((n : ℤ) * 4 ^ P) ^ m := by
    have := Matrix.det_le (A := G) (abv := AbsoluteValue.abs) (x := ((n : ℤ) * 4 ^ P)) (by
      intro i j
      show |G i j| ≤ _
      simp only [G, A, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
      calc |∑ l, (H i).1 l * (H j).1 l| ≤ ∑ l : Fin n, |(H i).1 l * (H j).1 l| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l : Fin n, (4:ℤ)^P := by
            apply Finset.sum_le_sum; intro l _
            rw [abs_mul]
            have hi := (hsmall i).2.1 l
            have hj := (hsmall j).2.1 l
            have hi' : |(H i).1 l| ≤ 2^P := by
              rw [Int.abs_eq_natAbs]; exact_mod_cast hi
            have hj' : |(H j).1 l| ≤ 2^P := by
              rw [Int.abs_eq_natAbs]; exact_mod_cast hj
            calc |(H i).1 l| * |(H j).1 l| ≤ 2^P * 2^P := mul_le_mul hi' hj' (abs_nonneg _) (by positivity)
              _ = 4^P := by rw [← mul_pow]; norm_num
        _ = n * 4^P := by simp)
    simpa [Fintype.card_fin, nsmul_eq_mul] using this
  have hdb' : d.natAbs ≤ m.factorial * (n * 4 ^ P) ^ m := by
    have : ((d.natAbs : ℕ) : ℤ) ≤ ((m.factorial * (n * 4 ^ P) ^ m : ℕ) : ℤ) := by
      rw [Nat.cast_natAbs]; push_cast; simpa using hdb
    exact_mod_cast this
  have hfac : m.factorial ≤ n ^ m := (Nat.factorial_le_pow m).trans (Nat.pow_le_pow_left hmn m)
  have hn2 : n * (n * 4 ^ P) ≤ 2 ^ (n + 2 + 2 * P) := by
    have h3 := sq_le_pow n
    calc n * (n * 4 ^ P) = (n * n) * 4 ^ P := by ring
      _ ≤ 2 ^ (n+2) * 2 ^ (2 * P) := by
          apply Nat.mul_le_mul h3; rw [pow_mul]; norm_num
      _ = _ := by rw [← pow_add]
  calc d.natAbs ≤ m.factorial * (n * 4 ^ P) ^ m := hdb'
    _ ≤ n ^ m * (n * 4 ^ P) ^ m := Nat.mul_le_mul_right _ hfac
    _ = (n * (n * 4 ^ P)) ^ m := (mul_pow _ _ _).symm
    _ ≤ (2 ^ (n + 2 + 2 * P)) ^ m := Nat.pow_le_pow_left hn2 m
    _ ≤ (2 ^ (n + 2 + 2 * P)) ^ n := Nat.pow_le_pow_right (by positivity) hmn
    _ = 2 ^ ((n + 2 + 2 * P) * n) := (pow_mul _ _ _).symm
    _ = 2 ^ (n * (n + 2 + 2 * P)) := by rw [mul_comm]


lemma dotR_sub_smul {n : ℕ} (f : Fin n → ℤ) (r q : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    dotR f (r - s • q) = dotR f r - s * dotR f q := by
  unfold dotR
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl; intro i _; ring

theorem lemma5_core (n P j : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin (j + 2) → (Fin n → ℤ) × ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hind : IndependentNormals H)
    (hr : ∀ i : Fin (j + 2), i.val ≤ j → r ∈ hyperplane (H i).1 (H i).2) :
    Metric.infDist r (flat H) ≤
      ((2 : ℝ) ^ tParam n P c k - 1) *
        hyperplaneDistance (H ⟨j + 1, by omega⟩).1 (H ⟨j + 1, by omega⟩).2 r := by
  classical
  set T := tParam n P c k with hT
  let H' : Fin (j+1) → (Fin n → ℤ) × ℤ := fun i => H (Fin.castSucc i)
  have hsmall' : ∀ i, SmallHyperplane P (H' i).1 (H' i).2 := fun i => hsmall _
  have hind' : IndependentNormals H' := by
    unfold IndependentNormals at hind ⊢
    exact hind.comp Fin.castSucc (Fin.castSucc_injective _)
  obtain ⟨hmn, hdne, hdb⟩ := gram_facts n P (j+1) H' hsmall' hind'
  set A : Matrix (Fin (j+1)) (Fin n) ℤ := Matrix.of (fun i l => (H' i).1 l) with hA
  set G : Matrix (Fin (j+1)) (Fin (j+1)) ℤ := A * Aᵀ with hG
  set d : ℤ := G.det with hd
  have hdne' : d ≠ 0 := hdne
  set fz : Fin n → ℤ := (H (Fin.last (j+1))).1 with hfz
  set gz : ℤ := (H (Fin.last (j+1))).2 with hgz
  have hfsmall : SmallHyperplane P fz gz := hsmall _
  let y : Fin (j+1) → ℤ := G.adjugate *ᵥ (A *ᵥ fz)
  let w : Fin n → ℤ := d • fz - Aᵀ *ᵥ y
  have e1 : A *ᵥ (Aᵀ *ᵥ y) = G *ᵥ y := by rw [Matrix.mulVec_mulVec]
  have e2 : G *ᵥ y = d • (A *ᵥ fz) := by
    simp only [y]; rw [Matrix.mulVec_mulVec, hd, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hAw : A *ᵥ w = 0 := by
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [e1, e2]; simp
  have hwne : w ≠ 0 := by
    intro hw0
    have h1 : d • fz = Aᵀ *ᵥ y := sub_eq_zero.mp hw0
    have key := Fintype.linearIndependent_iff.mp hind
      (Fin.snoc (fun i : Fin (j+1) => (y i : ℝ)) (-(d : ℝ)) : Fin (j+2) → ℝ) (by
        ext l
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, Pi.zero_apply]
        have := congrFun h1 l
        simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.transpose_apply, hA,
          Matrix.of_apply] at this
        have h2 : ((d * fz l : ℤ) : ℝ) = ((∑ x, (H' x).1 l * y x : ℤ) : ℝ) := by rw [this]
        push_cast at h2
        have h3 : (fz l : ℝ) = ((H (Fin.last (j+1))).1 l : ℝ) := rfl
        rw [← h3]
        have : ∑ x : Fin (j+1), (y x : ℝ) * ((H (Fin.castSucc x)).1 l : ℝ) = ∑ x, ((H' x).1 l : ℝ) * y x := by
          apply Finset.sum_congr rfl; intro x _; simp only [H']; ring
        rw [this, ← h2]; ring)
    have := key (Fin.last (j+1))
    simp at this
    exact hdne' this
  -- integer facts
  set W : ℤ := w ⬝ᵥ w with hW
  have hWpos : 1 ≤ W := by
    have h0 : 0 ≤ W := by
      rw [hW]; unfold dotProduct; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have : W ≠ 0 := fun h => hwne (dotProduct_self_eq_zero.mp h)
    omega
  have hfw : d * (fz ⬝ᵥ w) = W := by
    have h0 : (Aᵀ *ᵥ y) ⬝ᵥ w = 0 := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hAw]; simp
    have : W = (d • fz - Aᵀ *ᵥ y) ⬝ᵥ w := rfl
    rw [this, sub_dotProduct, h0, smul_dotProduct]; simp
  -- real vector
  let wR : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => (w i : ℝ))
  have hdotw : ∀ v : Fin n → ℤ, dotR v wR = ((v ⬝ᵥ w : ℤ) : ℝ) := by
    intro v; unfold dotR dotProduct; push_cast; rfl
  have hfwR : (d : ℝ) * dotR fz wR = (W : ℝ) := by
    rw [hdotw]; exact_mod_cast hfw
  have hWR : (1:ℝ) ≤ W := by exact_mod_cast hWpos
  have hfwne : dotR fz wR ≠ 0 := by
    intro h; rw [h] at hfwR; simp at hfwR; linarith
  have hnormw : ‖wR‖ ^ 2 = (W : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [hW]; unfold dotProduct; push_cast
    apply Finset.sum_congr rfl; intro i _; simp [wR]; ring
  set u : ℝ := dotR fz r - gz with hu
  set cc : ℝ := u / dotR fz wR with hcc
  set p : EuclideanSpace ℝ (Fin n) := r - cc • wR with hp
  have hpflat : p ∈ flat H := by
    intro i
    show dotR (H i).1 p = ((H i).2 : ℝ)
    rw [hp, dotR_sub_smul]
    by_cases hi : i.val ≤ j
    · have hri : dotR (H i).1 r = ((H i).2 : ℝ) := hr i hi
      have h0 : dotR (H i).1 wR = 0 := by
        rw [hdotw]
        have := congrFun hAw ⟨i.val, by omega⟩
        simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, Pi.zero_apply] at this
        have e : (⟨i.val, by omega⟩ : Fin (j+1)).castSucc = i := Fin.ext rfl
        simp only [H', e] at this
        exact_mod_cast this
      rw [hri, h0]; ring
    · have : i = Fin.last (j+1) := Fin.ext (by have := i.isLt; simp; omega)
      subst this
      show dotR fz r - cc * dotR fz wR = (gz : ℝ)
      rw [hcc, div_mul_cancel₀ _ hfwne]; rw [hu]; ring
  have hdist : Metric.infDist r (flat H) ≤ ‖r - p‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hpflat
  have hrp : r - p = cc • wR := by rw [hp]; abel
  have hnorm_le : ‖r - p‖ ≤ |u| * |(d:ℝ)| := by
    rw [hrp, norm_smul, Real.norm_eq_abs, hcc, abs_div]
    have hdpos : 0 < |(d:ℝ)| := abs_pos.mpr (by exact_mod_cast hdne')
    have hfwabs : |(d:ℝ)| * |dotR fz wR| = W := by
      rw [← abs_mul, hfwR, abs_of_nonneg (by linarith)]
    have hfwpos : 0 < |dotR fz wR| := abs_pos.mpr hfwne
    have hwn : ‖wR‖ ≤ W := by
      have h0 := norm_nonneg wR
      nlinarith
    calc |u| / |dotR fz wR| * ‖wR‖ ≤ |u| / |dotR fz wR| * W := by gcongr
      _ = |u| * |(d:ℝ)| := by
          rw [← hfwabs]; field_simp
  -- bound |d| * N
  obtain ⟨hNpos, hNle⟩ := normalLength_le n P fz gz hfsmall
  have hdR : |(d:ℝ)| ≤ 2 ^ (n * (n + 2 + 2 * P)) := by
    have : ((d.natAbs : ℕ) : ℝ) ≤ ((2 ^ (n * (n + 2 + 2 * P)) : ℕ) : ℝ) := by exact_mod_cast hdb
    rw [Nat.cast_natAbs] at this
    push_cast at this
    simpa using this
  have hTbig : n * (n + 2 + 2 * P) + (n + P) + 2 ≤ T := by
    rw [hT]; unfold tParam
    have h1 : n ≤ ∑ i : Fin n, (Nat.clog 2 (c i).natAbs + 1) := by
      calc n = ∑ _i : Fin n, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => by omega)
    have : n * (n + 2 + 2 * P) + (n + P) + 1 ≤ (n+1)^2*(P+1) + n := by
      nlinarith [Nat.zero_le (n*n*P), Nat.zero_le P]
    omega
  have hprod : |(d:ℝ)| * normalLength fz ≤ (2:ℝ) ^ T - 1 := by
    have h1 : |(d:ℝ)| * normalLength fz ≤ 2 ^ (n * (n + 2 + 2 * P)) * 2 ^ (n + P) :=
      mul_le_mul hdR hNle hNpos.le (by positivity)
    rw [← pow_add] at h1
    have h2 : (2:ℝ) ^ (n * (n + 2 + 2 * P) + (n + P)) * 4 ≤ 2 ^ T := by
      calc (2:ℝ) ^ (n * (n + 2 + 2 * P) + (n + P)) * 4 = 2 ^ (n * (n + 2 + 2 * P) + (n + P) + 2) := by ring
        _ ≤ 2 ^ T := pow_le_pow_right₀ (by norm_num) hTbig
    have h3 : (1:ℝ) ≤ 2 ^ (n * (n + 2 + 2 * P) + (n + P)) := one_le_pow₀ (by norm_num)
    linarith
  show Metric.infDist r (flat H) ≤ ((2 : ℝ) ^ T - 1) * hyperplaneDistance fz gz r
  unfold hyperplaneDistance
  have hu' : dotR fz r - (gz : ℝ) = u := rfl
  rw [hu']
  refine hdist.trans (hnorm_le.trans ?_)
  rw [← mul_div_assoc, le_div_iff₀ hNpos]
  calc |u| * |(d:ℝ)| * normalLength fz = |u| * (|(d:ℝ)| * normalLength fz) := by ring
    _ ≤ |u| * ((2:ℝ)^T - 1) := by gcongr
    _ = _ := by ring

end KarpPapadimitriou.Generator

open KarpPapadimitriou.Generator


theorem solution (n P j : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin (j + 2) → (Fin n → ℤ) × ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hind : IndependentNormals H)
    (hr : ∀ i : Fin (j + 2), i.val ≤ j → r ∈ hyperplane (H i).1 (H i).2) :
    Metric.infDist r (flat H) ≤
      ((2 : ℝ) ^ tParam n P c k - 1) *
        hyperplaneDistance (H ⟨j + 1, by omega⟩).1 (H ⟨j + 1, by omega⟩).2 r := by
  exact lemma5_core n P j c k H r hsmall hind hr

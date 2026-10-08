-- Prove2me | solution 1 for KarpPapadimitriou.Generator.corollary_lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T21:26:32.687289+00:00
-- url     : https://prove2.me/submissions/7d38e422-782a-488f-b754-cae60bd45294

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

/-- existence of a rational point in the flat with controlled denominator -/
lemma exists_rat_point (n P m : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin m → (Fin n → ℤ) × ℤ)
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hind : IndependentNormals H) :
    ∃ q : Fin n → ℚ, (∀ i, (q i).den ≤ 2 ^ tParam n P c k) ∧
      ∀ i, dotQ (H i).1 q = ((H i).2 : ℚ) := by
  classical
  set T := tParam n P c k with hT
  have hmn : m ≤ n := by
    have := hind.fintype_card_le_finrank
    simpa using this
  let A : Matrix (Fin m) (Fin n) ℤ := fun i j => (H i).1 j
  let b : Fin m → ℤ := fun i => (H i).2
  let G : Matrix (Fin m) (Fin m) ℤ := A * A.transpose
  set d : ℤ := G.det with hd
  -- d ≠ 0
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
  -- solution
  let y : Fin m → ℤ := G.adjugate *ᵥ b
  let x : Fin n → ℤ := A.transpose *ᵥ y
  have hAx : A *ᵥ x = d • b := by
    have : A *ᵥ x = G *ᵥ y := by
      simp only [x, Matrix.mulVec_mulVec]; rfl
    rw [this]
    simp only [y, Matrix.mulVec_mulVec, G, hd]
    rw [Matrix.mul_adjugate]; simp
  refine ⟨fun j => (x j : ℚ) / (d : ℚ), ?_, ?_⟩
  · intro j
    -- den bound
    have h1 : (((x j : ℚ) / (d : ℚ)).den : ℤ) ∣ d := by
      have : ((x j : ℚ) / (d : ℚ)) = Rat.divInt (x j) d := by
        rw [Rat.divInt_eq_div]
      rw [this]; exact Rat.den_dvd _ _
    have h2 : ((x j : ℚ) / (d : ℚ)).den ≤ d.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hdne) (Int.ofNat_dvd_left.mp h1)
    refine h2.trans ?_
    -- |d| ≤ 2^T
    have hdb : |d| ≤ (m.factorial : ℤ) * ((n : ℤ) * 4 ^ P) ^ m := by
      have := Matrix.det_le (A := G) (abv := AbsoluteValue.abs) (x := ((n : ℤ) * 4 ^ P)) (by
        intro i j
        show |G i j| ≤ _
        simp only [G, Matrix.mul_apply, Matrix.transpose_apply]
        calc |∑ l, A i l * A j l| ≤ ∑ l : Fin n, |A i l * A j l| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ l : Fin n, (4:ℤ)^P := by
              apply Finset.sum_le_sum; intro l _
              rw [abs_mul]
              have hi := (hsmall i).2.1 l
              have hj := (hsmall j).2.1 l
              have hi' : |A i l| ≤ 2^P := by
                show |(H i).1 l| ≤ _
                rw [Int.abs_eq_natAbs]; exact_mod_cast hi
              have hj' : |A j l| ≤ 2^P := by
                show |(H j).1 l| ≤ _
                rw [Int.abs_eq_natAbs]; exact_mod_cast hj
              calc |A i l| * |A j l| ≤ 2^P * 2^P := mul_le_mul hi' hj' (abs_nonneg _) (by positivity)
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
    have hTge2 : n * (n + 2 + 2 * P) ≤ T := by
      rw [hT]; unfold tParam
      have : n * (n + 2 + 2 * P) ≤ (n+1)^2*(P+1) := by nlinarith [Nat.zero_le (n*n*P), Nat.zero_le P]
      omega
    calc d.natAbs ≤ m.factorial * (n * 4 ^ P) ^ m := hdb'
      _ ≤ n ^ m * (n * 4 ^ P) ^ m := Nat.mul_le_mul_right _ hfac
      _ = (n * (n * 4 ^ P)) ^ m := (mul_pow _ _ _).symm
      _ ≤ (2 ^ (n + 2 + 2 * P)) ^ m := Nat.pow_le_pow_left hn2 m
      _ ≤ (2 ^ (n + 2 + 2 * P)) ^ n := Nat.pow_le_pow_right (by positivity) hmn
      _ = 2 ^ ((n + 2 + 2 * P) * n) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ T := Nat.pow_le_pow_right (by norm_num) (by rw [mul_comm]; exact hTge2)
  · intro i
    have := congrFun hAx i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, A, b] at this
    unfold dotQ
    have h3 : ((∑ j, (H i).1 j * x j : ℤ) : ℚ) = ((d * (H i).2 : ℤ) : ℚ) := by rw [this]
    push_cast at h3
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hdne
    calc ∑ j, (((H i).1 j : ℤ) : ℚ) * ((x j : ℚ) / d) = (∑ j, ((H i).1 j : ℚ) * x j) / d := by
          rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by rw [h3]; field_simp


theorem cor_core (n P m : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin m → (Fin n → ℤ) × ℤ) (f : Fin n → ℤ) (g : ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hsmall_new : SmallHyperplane P f g)
    (hind : IndependentNormals H)
    (hr : r ∈ flat H)
    (hdisjoint : hyperplane f g ∩ flat H = ∅) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤ hyperplaneDistance f g r := by
  obtain ⟨q, hden, hq⟩ := exists_rat_point n P m c k H hsmall hind
  have hqflat : realPoint q ∈ flat H := by
    intro i
    show dotR (H i).1 (realPoint q) = _
    have : dotR (H i).1 (realPoint q) = ((dotQ (H i).1 q : ℚ) : ℝ) := by
      unfold dotR dotQ realPoint; push_cast; rfl
    rw [this, hq i]; simp
  have hconst := u_const H f g hdisjoint r (realPoint q) hr hqflat
  have hout : dotQ f q ≠ (g : ℚ) := by
    intro h
    have hmem : realPoint q ∈ hyperplane f g ∩ flat H := by
      refine ⟨?_, hqflat⟩
      show dotR f (realPoint q) = g
      have : dotR f (realPoint q) = ((dotQ f q : ℚ) : ℝ) := by
        unfold dotR dotQ realPoint; push_cast; rfl
      rw [this, h]; simp
    rw [hdisjoint] at hmem; exact hmem
  have := lemma4_core n P c k q f g hsmall_new hden hout
  unfold hyperplaneDistance at this ⊢
  rw [hconst]; exact this

end KarpPapadimitriou.Generator

open KarpPapadimitriou.Generator


theorem solution (n P m : ℕ) (c : Fin n → ℤ) (k : ℤ)
    (H : Fin m → (Fin n → ℤ) × ℤ) (f : Fin n → ℤ) (g : ℤ)
    (r : EuclideanSpace ℝ (Fin n))
    (hsmall : ∀ i, SmallHyperplane P (H i).1 (H i).2)
    (hsmall_new : SmallHyperplane P f g)
    (hind : IndependentNormals H)
    (hr : r ∈ flat H)
    (hdisjoint : hyperplane f g ∩ flat H = ∅) :
    (1 : ℝ) / 2 ^ ((n + 1) * tParam n P c k) ≤ hyperplaneDistance f g r := by
  exact cor_core n P m c k H f g r hsmall hsmall_new hind hr hdisjoint

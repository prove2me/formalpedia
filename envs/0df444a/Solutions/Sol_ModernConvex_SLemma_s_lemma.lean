-- Prove2me | solution 1 for ModernConvex.SLemma.s_lemma
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T14:54:33.867145+00:00
-- url     : https://prove2.me/submissions/091b7a3a-71c5-4d37-be6d-c8bfb07dbda4

import Mathlib

open Matrix

lemma g70mc1_bil {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (x y : Fin n → ℝ) :
    y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
  have hAt : Aᵀ = A := by
    have := hA.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  rw [dotProduct_mulVec, ← mulVec_transpose, hAt, dotProduct_comm]

lemma g70mc1_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (x y : Fin n → ℝ) (s : ℝ) :
    (x + s • y) ⬝ᵥ (A *ᵥ (x + s • y)) =
      x ⬝ᵥ (A *ᵥ x) + 2 * s * (x ⬝ᵥ (A *ᵥ y)) + s ^ 2 * (y ⬝ᵥ (A *ᵥ y)) := by
  have h := g70mc1_bil A hA x y
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [h]; ring

/-- two-point lemma: if a(x) > 0 > a(y) then a(x) b(y) - a(y) b(x) ≥ 0 -/
lemma g70mc1_two {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    (himp : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) → 0 ≤ x ⬝ᵥ (B *ᵥ x))
    (x y : Fin n → ℝ) (hx : 0 < x ⬝ᵥ (A *ᵥ x)) (hy : y ⬝ᵥ (A *ᵥ y) < 0) :
    y ⬝ᵥ (A *ᵥ y) * (x ⬝ᵥ (B *ᵥ x)) ≤ x ⬝ᵥ (A *ᵥ x) * (y ⬝ᵥ (B *ᵥ y)) := by
  set ax := x ⬝ᵥ (A *ᵥ x)
  set ay := y ⬝ᵥ (A *ᵥ y)
  set axy := x ⬝ᵥ (A *ᵥ y)
  set bx := x ⬝ᵥ (B *ᵥ x)
  set bY := y ⬝ᵥ (B *ᵥ y)
  set bxy := x ⬝ᵥ (B *ᵥ y)
  have hdisc : 0 < axy ^ 2 - ax * ay := by nlinarith [sq_nonneg axy]
  set dd := Real.sqrt (axy ^ 2 - ax * ay)
  have hd2 : dd ^ 2 = axy ^ 2 - ax * ay := Real.sq_sqrt hdisc.le
  have hd0 : 0 ≤ dd := Real.sqrt_nonneg _
  have hdg : |axy| < dd := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hd1 : axy < dd := lt_of_le_of_lt (le_abs_self _) hdg
  have hd1' : -axy < dd := lt_of_le_of_lt (neg_le_abs _) hdg
  set s1 := (-axy + dd) / ay
  set s2 := (-axy - dd) / ay
  have hs1 : s1 < 0 := div_neg_of_pos_of_neg (by linarith) hy
  have hs2 : 0 < s2 := div_pos_of_neg_of_neg (by linarith) hy
  have hroot : ∀ s, ay * s ^ 2 + 2 * axy * s + ax = 0 → 0 ≤ bx + 2 * s * bxy + s ^ 2 * bY := by
    intro s hs
    have := himp (x + s • y) (by rw [g70mc1_expand A hA]; nlinarith)
    rwa [g70mc1_expand B hB] at this
  have hay : ay ≠ 0 := hy.ne
  have hr1 : ay * s1 ^ 2 + 2 * axy * s1 + ax = 0 := by
    have e : ay * s1 ^ 2 + 2 * axy * s1 + ax = (dd ^ 2 - axy ^ 2 + ax * ay) / ay := by
      simp only [s1]; field_simp; ring
    rw [e, hd2]; simp
  have hr2 : ay * s2 ^ 2 + 2 * axy * s2 + ax = 0 := by
    have e : ay * s2 ^ 2 + 2 * axy * s2 + ax = (dd ^ 2 - axy ^ 2 + ax * ay) / ay := by
      simp only [s2]; field_simp; ring
    rw [e, hd2]; simp
  have h1 := hroot s1 hr1
  have h2 := hroot s2 hr2
  -- s2 * h1 - s1 * h2 = (s2 - s1) (bx - s1 s2 bY)
  have hcomb : 0 ≤ (s2 - s1) * (bx - s1 * s2 * bY) := by
    have e : (s2 - s1) * (bx - s1 * s2 * bY) =
        s2 * (bx + 2 * s1 * bxy + s1 ^ 2 * bY) + (-s1) * (bx + 2 * s2 * bxy + s2 ^ 2 * bY) := by
      ring
    rw [e]
    exact add_nonneg (mul_nonneg hs2.le h1) (mul_nonneg (by linarith) h2)
  have hprod : s1 * s2 * ay = ax := by
    have e : s1 * s2 * ay = (axy ^ 2 - dd ^ 2) / ay := by
      simp only [s1, s2]; field_simp; ring
    rw [e, hd2]; field_simp; ring
  have hpos : 0 ≤ bx - s1 * s2 * bY := by
    rcases (mul_nonneg_iff.1 hcomb) with ⟨_, h'⟩ | ⟨h1', _⟩
    · exact h'
    · linarith
  have := mul_le_mul_of_nonpos_left hpos hy.le
  have e : ay * (bx - s1 * s2 * bY) = ay * bx - ax * bY := by rw [← hprod]; ring
  linarith

theorem g70mc1_slemma {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hfeas : ∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (A *ᵥ x)) :
    (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) → 0 ≤ x ⬝ᵥ (B *ᵥ x)) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ (B - lam • A).PosSemidef := by
  constructor
  · intro himp
    set S := {r : ℝ | ∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (A *ᵥ x) ∧ r = x ⬝ᵥ (B *ᵥ x) / x ⬝ᵥ (A *ᵥ x)}
    have hne : S.Nonempty := by
      obtain ⟨x, hx⟩ := hfeas; exact ⟨_, x, hx, rfl⟩
    have hbdd : BddBelow S := ⟨0, by
      rintro _ ⟨x, hx, rfl⟩; exact div_nonneg (himp x hx.le) hx.le⟩
    refine ⟨sInf S, le_csInf hne (by rintro _ ⟨x, hx, rfl⟩; exact div_nonneg (himp x hx.le) hx.le), ?_⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub (by unfold IsHermitian; rw [conjTranspose_smul, star_trivial, hA.eq])) fun y => ?_
    rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul,
      sub_nonneg]
    rcases lt_trichotomy (y ⬝ᵥ (A *ᵥ y)) 0 with hy | hy | hy
    · -- need b(y)/a(y) ≤ sInf S
      have hle : y ⬝ᵥ (B *ᵥ y) / y ⬝ᵥ (A *ᵥ y) ≤ sInf S := by
        apply le_csInf hne
        rintro _ ⟨x, hx, rfl⟩
        have key := g70mc1_two A B hA hB himp x y hx hy
        rw [div_le_iff_of_neg hy, div_mul_eq_mul_div, div_le_iff₀ hx]
        linarith
      rwa [div_le_iff_of_neg hy] at hle
    · rw [hy, mul_zero]; exact himp y hy.ge
    · have := csInf_le hbdd ⟨y, hy, rfl⟩
      rwa [le_div_iff₀ hy] at this
  · rintro ⟨lam, hlam, hpsd⟩ x hx
    have := hpsd.dotProduct_mulVec_nonneg x
    rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul] at this
    nlinarith [mul_nonneg hlam hx]

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hfeas : ∃ x : Fin n → ℝ, 0 < x ⬝ᵥ (A *ᵥ x)) :
    (∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (A *ᵥ x) → 0 ≤ x ⬝ᵥ (B *ᵥ x)) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ (B - lam • A).PosSemidef := by
  exact g70mc1_slemma A B hA hB hfeas


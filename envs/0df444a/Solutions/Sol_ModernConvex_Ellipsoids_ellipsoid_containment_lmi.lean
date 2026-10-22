-- Prove2me | solution 1 for ModernConvex.Ellipsoids.ellipsoid_containment_lmi
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T15:09:24.236236+00:00
-- url     : https://prove2.me/submissions/27eca56b-7aaf-4aac-b6b9-fe0e3c3ba1f7

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix ModernConvex.Ellipsoids

lemma g70mc1_b3form {n q : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) (s : ℝ) (Q : Matrix (Fin q) (Fin q) ℝ)
    (ξ : Fin n → ℝ) (t : ℝ) (u : Fin q → ℝ) :
    Sum.elim (Sum.elim ξ (fun _ => t)) u ⬝ᵥ
      (block3 P p R s Q *ᵥ Sum.elim (Sum.elim ξ (fun _ => t)) u) =
      ξ ⬝ᵥ (P *ᵥ ξ) + 2 * t * (p ⬝ᵥ ξ) + 2 * (ξ ⬝ᵥ (R *ᵥ u)) + s * t ^ 2 + u ⬝ᵥ (Q *ᵥ u) := by
  simp only [dotProduct, mulVec, Fintype.sum_sum_type, block3, of_apply, Sum.elim_inl,
    Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton, zero_mul, add_zero, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : ∑ x, ∑ i, u x * (R i x * ξ i) = ∑ i, ∑ x, ξ i * (R i x * u x) := by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  have h2 : ∑ i, t * (p i * ξ i) = ∑ i, ξ i * (p i * t) := by
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [h1, h2]
  have e3 : ∑ i, 2 * t * (p i * ξ i) = 2 * ∑ i, ξ i * (p i * t) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have e4 : ∑ x, ∑ i, 2 * (ξ x * (R x i * u i)) = 2 * ∑ i, ∑ x, ξ i * (R i x * u x) := by
    simp only [Finset.mul_sum]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  rw [e3, e4]; ring

lemma g70mc1_dotB {m k : ℕ} (B : Matrix (Fin m) (Fin k) ℝ) (w : Fin m → ℝ) (y : Fin k → ℝ) :
    w ⬝ᵥ (B *ᵥ y) = (Bᵀ *ᵥ w) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_transpose]

lemma g70mc1_b3herm {n q : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (p : Fin n → ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) (s : ℝ) (Q : Matrix (Fin q) (Fin q) ℝ) (hQ : Qᵀ = Q) :
    (block3 P p R s Q).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_eq_transpose_of_trivial]
  ext r c
  rcases r with (i | _) | k <;> rcases c with (j | _) | l <;>
    simp only [transpose_apply, block3, of_apply]
  · exact congrFun (congrFun hP i) j
  · exact congrFun (congrFun hQ k) l

lemma g70mc1_split {n q : ℕ} (v : (Fin n ⊕ Unit) ⊕ Fin q → ℝ) :
    v = Sum.elim (Sum.elim (fun i => v (Sum.inl (Sum.inl i))) (fun _ => v (Sum.inl (Sum.inr ()))))
      (fun k => v (Sum.inr k)) := by
  ext r; rcases r with (i | ⟨⟩) | k <;> rfl

/-- generic: PSD iff F ≥ 0 -/
lemma g70mc1_psd_iff {n q : ℕ} (Mx : Matrix ((Fin n ⊕ Unit) ⊕ Fin q) ((Fin n ⊕ Unit) ⊕ Fin q) ℝ)
    (hMx : Mx.IsHermitian) (φ : (Fin n → ℝ) → (Fin n → ℝ)) (hφ : ∀ η, ∃ ξ, φ ξ = η)
    (g : ℝ → (Fin q → ℝ) → (Fin n → ℝ)) (F : ℝ → (Fin q → ℝ) → ℝ)
    (hform : ∀ ξ t u, Sum.elim (Sum.elim ξ (fun _ => t)) u ⬝ᵥ
      (Mx *ᵥ Sum.elim (Sum.elim ξ (fun _ => t)) u) = (φ ξ + g t u) ⬝ᵥ (φ ξ + g t u) + F t u) :
    Mx.PosSemidef ↔ ∀ t u, 0 ≤ F t u := by
  constructor
  · intro h t u
    obtain ⟨ξ, hξ⟩ := hφ (-g t u)
    have := h.dotProduct_mulVec_nonneg (Sum.elim (Sum.elim ξ (fun _ => t)) u)
    rw [star_trivial, hform, hξ, neg_add_cancel, zero_dotProduct, zero_add] at this
    exact this
  · intro h
    refine PosSemidef.of_dotProduct_mulVec_nonneg hMx fun v => ?_
    rw [star_trivial, g70mc1_split v, hform]
    exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (h _ _)

lemma g70mc1_sqexp {n : ℕ} (a b : Fin n → ℝ) :
    (a + b) ⬝ᵥ (a + b) = a ⬝ᵥ a + 2 * (a ⬝ᵥ b) + b ⬝ᵥ b := by
  simp only [add_dotProduct, dotProduct_add]; rw [dotProduct_comm b a]; ring

section
variable {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ) (z : Fin n → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ)

noncomputable def g70mc1_F (lam t : ℝ) (u : Fin q → ℝ) : ℝ :=
  (1 - lam) * t ^ 2 + lam * (u ⬝ᵥ u) -
    (t • (Y *ᵥ (z - y)) + (Y * Z) *ᵥ u) ⬝ᵥ (t • (Y *ᵥ (z - y)) + (Y * Z) *ᵥ u)

lemma g70mc1_lmi1 (lam : ℝ) :
    (block3 1 (Y *ᵥ (z - y)) (Y * Z) (1 - lam) (lam • 1)).PosSemidef ↔
      ∀ t u, 0 ≤ g70mc1_F Z z Y y lam t u := by
  apply g70mc1_psd_iff _ (g70mc1_b3herm _ (transpose_one) _ _ _ _ (by
    rw [transpose_smul, transpose_one])) id (fun η => ⟨η, rfl⟩)
    (fun t u => t • (Y *ᵥ (z - y)) + (Y * Z) *ᵥ u)
  intro ξ t u
  rw [g70mc1_b3form, g70mc1_sqexp]
  simp only [g70mc1_F, id, one_mulVec, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_add]
  rw [dotProduct_comm ξ (Y *ᵥ (z - y))]
  ring

lemma g70mc1_lmi2 (hY : Y.det ≠ 0) (lam : ℝ) :
    (block3 (Y⁻¹ * (Y⁻¹)ᵀ) (z - y) Z (1 - lam) (lam • 1)).PosSemidef ↔
      ∀ t u, 0 ≤ g70mc1_F Z z Y y lam t u := by
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.2 hY
  have hYi : Y⁻¹ * Y = 1 := nonsing_inv_mul Y hu
  have hYi' : Y * Y⁻¹ = 1 := mul_nonsing_inv Y hu
  apply g70mc1_psd_iff _ (g70mc1_b3herm _ (by rw [transpose_mul, transpose_transpose]) _ _ _ _ (by
    rw [transpose_smul, transpose_one])) (fun ξ => (Y⁻¹)ᵀ *ᵥ ξ)
    (fun η => ⟨Yᵀ *ᵥ η, by rw [mulVec_mulVec, ← transpose_mul, hYi', transpose_one, one_mulVec]⟩)
    (fun t u => t • (Y *ᵥ (z - y)) + (Y * Z) *ᵥ u)
  intro ξ t u
  rw [g70mc1_b3form, g70mc1_sqexp]
  have e1 : ξ ⬝ᵥ ((Y⁻¹ * (Y⁻¹)ᵀ) *ᵥ ξ) = ((Y⁻¹)ᵀ *ᵥ ξ) ⬝ᵥ ((Y⁻¹)ᵀ *ᵥ ξ) := by
    rw [← mulVec_mulVec, g70mc1_dotB]
  have e2 : (z - y) ⬝ᵥ ξ = ((Y⁻¹)ᵀ *ᵥ ξ) ⬝ᵥ (Y *ᵥ (z - y)) := by
    rw [← g70mc1_dotB, mulVec_mulVec, hYi, one_mulVec, dotProduct_comm]
  have e3 : ξ ⬝ᵥ (Z *ᵥ u) = ((Y⁻¹)ᵀ *ᵥ ξ) ⬝ᵥ ((Y * Z) *ᵥ u) := by
    rw [← g70mc1_dotB, mulVec_mulVec, ← Matrix.mul_assoc, hYi, Matrix.one_mul]
  rw [e1, e2, e3]
  simp only [g70mc1_F, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_add]
  ring

end
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

lemma g70mc1_qdiag {q : ℕ} (c : ℝ) (e : Fin q → ℝ) (t : ℝ) (u : Fin q → ℝ) :
    (Fin.cons t u : Fin (q + 1) → ℝ) ⬝ᵥ (diagonal (Fin.cons c e : Fin (q + 1) → ℝ) *ᵥ
      (Fin.cons t u : Fin (q + 1) → ℝ)) = c * t ^ 2 + ∑ k, e k * u k ^ 2 := by
  simp only [dotProduct, mulVec_diagonal, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma g70mc1_diag_herm {q : ℕ} (d : Fin q → ℝ) : (diagonal d).IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial, diagonal_transpose]

theorem g70mc1_contain {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ) (z : Fin n → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (hq : 0 < q) :
    ellipsoid Z z ⊆ quadEllipsoid Y y ↔ ∃ lam : ℝ, ∀ t u, 0 ≤ g70mc1_F Z z Y y lam t u := by
  set w := Y *ᵥ (z - y)
  set M := Y * Z
  have hquad : ∀ u : Fin q → ℝ, Z *ᵥ u + z ∈ quadEllipsoid Y y ↔
      (w + M *ᵥ u) ⬝ᵥ (w + M *ᵥ u) ≤ 1 := by
    intro u
    have e : Z *ᵥ u + z - y = Z *ᵥ u + (z - y) := by abel
    simp only [quadEllipsoid, Set.mem_setOf_eq, e]
    rw [← mulVec_mulVec, g70mc1_dotB, transpose_transpose, mulVec_add, ← mulVec_mulVec, add_comm]
  constructor
  · intro hsub
    -- S-lemma packaging
    let N : Matrix (Fin n) (Fin (q + 1)) ℝ := Matrix.of fun i j => Fin.cases (w i) (fun k => M i k) j
    have hN : ∀ t u, N *ᵥ (Fin.cons t u : Fin (q + 1) → ℝ) = t • w + M *ᵥ u := by
      intro t u; ext i
      simp [N, mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    let As : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ := diagonal (Fin.cons 1 (fun _ => -1))
    let Bs : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ := diagonal (Fin.cons 1 (fun _ => 0)) - Nᵀ * N
    have hqa : ∀ t u, (Fin.cons t u : Fin (q + 1) → ℝ) ⬝ᵥ (As *ᵥ Fin.cons t u) = t ^ 2 - u ⬝ᵥ u := by
      intro t u; rw [g70mc1_qdiag]; simp [dotProduct, sq]; ring
    have hqb : ∀ t u, (Fin.cons t u : Fin (q + 1) → ℝ) ⬝ᵥ (Bs *ᵥ Fin.cons t u) =
        t ^ 2 - (t • w + M *ᵥ u) ⬝ᵥ (t • w + M *ᵥ u) := by
      intro t u
      simp only [Bs]
      rw [sub_mulVec, dotProduct_sub, g70mc1_qdiag, ← mulVec_mulVec, g70mc1_dotB Nᵀ,
        transpose_transpose, hN]
      simp
    have hAh : As.IsHermitian := g70mc1_diag_herm _
    have hBh : Bs.IsHermitian := (g70mc1_diag_herm _).sub (by unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial, transpose_mul, transpose_transpose])
    have himp : ∀ x : Fin (q + 1) → ℝ, 0 ≤ x ⬝ᵥ (As *ᵥ x) → 0 ≤ x ⬝ᵥ (Bs *ᵥ x) := by
      intro x hx
      rw [← Fin.cons_self_tail x] at hx ⊢
      rw [hqa] at hx; rw [hqb]
      set t := x 0
      set u := Fin.tail x
      rcases eq_or_ne t 0 with h0 | h0
      · have huu : u ⬝ᵥ u = 0 := le_antisymm (by rw [h0] at hx; linarith)
          (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
        have hu0 : u = 0 := dotProduct_self_eq_zero.1 huu
        rw [h0, hu0]; simp
      · have ht2 : 0 < t ^ 2 := by positivity
        have hu' : (t⁻¹ • u) ⬝ᵥ (t⁻¹ • u) ≤ 1 := by
          rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
            inv_pow]
          rw [inv_mul_le_iff₀ ht2]; linarith
        have hin := (hquad _).1 (hsub ⟨t⁻¹ • u, hu', rfl⟩)
        have e : t • w + M *ᵥ u = t • (w + M *ᵥ (t⁻¹ • u)) := by
          rw [mulVec_smul, smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul]
        rw [e, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq]
        nlinarith
    have hfeas : ∃ x : Fin (q + 1) → ℝ, 0 < x ⬝ᵥ (As *ᵥ x) :=
      ⟨Fin.cons 1 0, by rw [hqa]; simp⟩
    obtain ⟨lam, _, hpsd⟩ := (g70mc1_slemma As Bs hAh hBh hfeas).1 himp
    refine ⟨lam, fun t u => ?_⟩
    have := hpsd.dotProduct_mulVec_nonneg (Fin.cons t u)
    rw [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul,
      hqa, hqb] at this
    simp only [g70mc1_F]
    linarith
  · rintro ⟨lam, hF⟩ x ⟨u, hu, rfl⟩
    rw [hquad]
    -- lam ≥ 0
    let u0 : Fin q → ℝ := Pi.single ⟨0, hq⟩ 1
    have hu0 : u0 ⬝ᵥ u0 = 1 := by simp [u0]
    have h0 := hF 0 u0
    simp only [g70mc1_F, zero_smul, zero_add, hu0] at h0
    have hnn : 0 ≤ (M *ᵥ u0) ⬝ᵥ (M *ᵥ u0) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hlam : 0 ≤ lam := by nlinarith
    have h1 := hF 1 u
    simp only [g70mc1_F, one_smul] at h1
    nlinarith [mul_le_mul_of_nonneg_left hu hlam]

theorem solution {n q : ℕ} (Z : Matrix (Fin n) (Fin q) ℝ) (z : Fin n → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (hY : Y.det ≠ 0) (hq : 0 < q) :
    (ellipsoid Z z ⊆ quadEllipsoid Y y ↔
      ∃ lam : ℝ, (block3 1 (Y *ᵥ (z - y)) (Y * Z) (1 - lam) (lam • 1)).PosSemidef) ∧
    (ellipsoid Z z ⊆ quadEllipsoid Y y ↔
      ∃ lam : ℝ, (block3 (Y⁻¹ * (Y⁻¹)ᵀ) (z - y) Z (1 - lam) (lam • 1)).PosSemidef) := by

  rw [g70mc1_contain Z z Y y hq]
  refine ⟨exists_congr fun lam => (g70mc1_lmi1 Z z Y y lam).symm,
    exists_congr fun lam => (g70mc1_lmi2 Z z Y y hY lam).symm⟩

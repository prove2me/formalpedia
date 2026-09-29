-- Prove2me | solution 1 for GrandUnifiedTheories.phi_mem_specialUnitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:04:51.389389+00:00
-- url     : https://prove2.me/submissions/275fce9b-b1fb-45f3-b1a7-104eac4f151f

import Mathlib
import Definitions.Def_GUT_standard_model_group
import Definitions.Def_GUT_realification

open GrandUnifiedTheories

theorem W3a_GrandUnifiedTheories_star (a : Circle) : star (a : ℂ) = (a : ℂ)⁻¹ := by
  rw [← Circle.coe_inv, Circle.coe_inv_eq_conj]; rfl

theorem W3a_GrandUnifiedTheories_conj (a : Circle) : (starRingEnd ℂ) (a : ℂ) = (a : ℂ)⁻¹ := by
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]

theorem W3a_GrandUnifiedTheories_smul_mem {n : Type} [Fintype n] [DecidableEq n]
    (b : Circle) {P : Matrix n n ℂ} (hP : P ∈ Matrix.unitaryGroup n ℂ) :
    (b : ℂ) • P ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hP ⊢
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP, W3a_GrandUnifiedTheories_star,
    mul_inv_cancel₀ (Circle.coe_ne_zero b), one_smul]

theorem W3a_GrandUnifiedTheories_fromBlocks_mem {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {P : Matrix m m ℂ} {Q : Matrix n n ℂ}
    (hP : P ∈ Matrix.unitaryGroup m ℂ) (hQ : Q ∈ Matrix.unitaryGroup n ℂ) :
    Matrix.fromBlocks P 0 0 Q ∈ Matrix.unitaryGroup (m ⊕ n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hP hQ ⊢
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp [hP, hQ]

theorem W3a_GrandUnifiedTheories_scalar_mem {n : Type} [Fintype n] [DecidableEq n]
    (b : Circle) (hd : b ^ Fintype.card n = 1) :
    (b : ℂ) • (1 : Matrix n n ℂ) ∈ Matrix.specialUnitaryGroup n ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨W3a_GrandUnifiedTheories_smul_mem b (one_mem _), ?_⟩
  rw [Matrix.det_smul, Matrix.det_one, mul_one, ← Circle.coe_pow, hd, Circle.coe_one]

theorem W3a_GrandUnifiedTheories_card_roots (n : ℕ) [NeZero n] :
    Nat.card {a : Circle // a ^ n = 1} = n := by
  have e : {a : Circle // a ^ n = 1} ≃ rootsOfUnity n Circle :=
    { toFun := fun a => ⟨toUnits a.1, by rw [mem_rootsOfUnity, ← map_pow, a.2, map_one]⟩
      invFun := fun ζ => ⟨((ζ.1 : Circleˣ) : Circle), (mem_rootsOfUnity' n ζ.1).mp ζ.2⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun ζ => Subtype.ext (Units.ext rfl) }
  rw [Nat.card_congr e, Nat.card_congr (rootsOfUnityCircleEquiv n).toEquiv,
    Complex.card_rootsOfUnity]

theorem W3a_GrandUnifiedTheories_pullback
    {G₁ G₂ H₁ H₂ K₁ K₂ : Type} [Group G₁] [Group G₂] [Group H₁] [Group H₂]
    [Group K₁] [Group K₂]
    (phiTilde : G₁ →* G₂) (thetaTilde : G₁ →* H₁) (psi : G₂ →* H₂) (etaTilde : H₁ →* H₂)
    (q : H₁ →* K₁) (p : H₂ →* K₂) (i : K₁ →* K₂)
    (hUpper : ∀ x : G₁, etaTilde (thetaTilde x) = psi (phiTilde x))
    (hLower : ∀ g : H₁, i (q g) = p (etaTilde g))
    (hEta : Function.Injective etaTilde)
    (hOuter : ∀ (g' : G₂) (k : K₁), i k = p (psi g') →
      ∃ x : G₁, q (thetaTilde x) = k ∧ phiTilde x = g') :
    ∀ (g : H₁) (g' : G₂), etaTilde g = psi g' →
      ∃ x : G₁, thetaTilde x = g ∧ phiTilde x = g' := by
  intro g g' hgg
  obtain ⟨x, _, hx2⟩ := hOuter g' (q g) (by rw [hLower, hgg])
  refine ⟨x, hEta ?_, hx2⟩
  rw [hUpper, hx2, hgg]

theorem W3a_GrandUnifiedTheories_realify_injective : Function.Injective realify := by
  intro A B h
  have key : ∀ (i : Idx5) (s : Fin 2), ∃ x : Idx10, idx10ToC x = (i, s) := by
    rintro (i | i) s
    · exact ⟨Sum.inl (i, s), rfl⟩
    · exact ⟨Sum.inr (i, s), rfl⟩
  ext i j
  obtain ⟨x0, hx0⟩ := key i 0
  obtain ⟨x1, hx1⟩ := key i 1
  obtain ⟨y0, hy0⟩ := key j 0
  have h1 := congrFun (congrFun h x0) y0
  have h2 := congrFun (congrFun h x1) y0
  simp only [realify, Matrix.of_apply, hx0, hx1, hy0, realEntry] at h1 h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2

theorem W3a_GrandUnifiedTheories_realify_map_mul (A B : Matrix Idx5 Idx5 ℂ) :
    realify (A * B) = realify A * realify B := by
  have hsum : ∀ (s t : Fin 2) (f : Idx5 → ℂ),
      realEntry (∑ k, f k) s t = ∑ k, realEntry (f k) s t := by
    intro s t f
    fin_cases s <;> fin_cases t <;> simp [realEntry, Complex.re_sum, Complex.im_sum]
  have hmul : ∀ (s t : Fin 2) (z w : ℂ),
      realEntry (z * w) s t = ∑ u, realEntry z s u * realEntry w u t := by
    intro s t z w
    fin_cases s <;> fin_cases t <;> simp [realEntry, Fin.sum_univ_two] <;> ring
  ext x y
  simp only [realify, Matrix.of_apply, Matrix.mul_apply, hsum, hmul]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, idx10ToC]

theorem solution (x : GSM) :
    phiMatrix x ∈ Matrix.specialUnitaryGroup Idx5 ℂ := by
  obtain ⟨a, g, h⟩ := x
  have ha := Circle.coe_ne_zero a
  have hg := Matrix.mem_specialUnitaryGroup_iff.mp g.2
  have hh := Matrix.mem_specialUnitaryGroup_iff.mp h.2
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · have e1 : ((a : ℂ) ^ 3) = ((a ^ 3 : Circle) : ℂ) := by simp
    have e2 : (((a⁻¹ : Circle) : ℂ) ^ 2) = ((a⁻¹ ^ 2 : Circle) : ℂ) := by simp
    simp only [phiMatrix]
    rw [e1, e2]
    exact W3a_GrandUnifiedTheories_fromBlocks_mem (W3a_GrandUnifiedTheories_smul_mem _ hg.1)
      (W3a_GrandUnifiedTheories_smul_mem _ hh.1)
  · simp only [phiMatrix]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, hg.2, hh.2]
    simp only [Fintype.card_fin, Circle.coe_inv, mul_one]
    calc ((a : ℂ) ^ 3) ^ 2 * (((a : ℂ)⁻¹) ^ 2) ^ 3 = ((a : ℂ) * (a : ℂ)⁻¹) ^ 6 := by ring
      _ = 1 := by rw [mul_inv_cancel₀ ha, one_pow]

theorem W3a_GrandUnifiedTheories_phi_map_mul (x y : GSM) :
    phiMatrix (x * y) = phiMatrix x * phiMatrix y := by
  obtain ⟨a, g, h⟩ := x
  obtain ⟨b, g', h'⟩ := y
  have hg : (((g * g' : Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
      = g * g' := rfl
  have hh : (((h * h' : Matrix.specialUnitaryGroup (Fin 3) ℂ)) : Matrix (Fin 3) (Fin 3) ℂ)
      = h * h' := rfl
  simp only [phiMatrix, Prod.mk_mul_mk, hg, hh, Circle.coe_mul, Circle.coe_inv]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_pow, mul_inv, mul_comm]

theorem W3a_GrandUnifiedTheories_phi_eq_one_iff (x : GSM) :
    phiMatrix x = 1 ↔
      ((x.1 : ℂ) ^ 6 = 1 ∧
        (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = (((x.1)⁻¹ : Circle) : ℂ) ^ 3 • 1 ∧
        (x.2.2 : Matrix (Fin 3) (Fin 3) ℂ) = ((x.1 : ℂ) ^ 2) • 1) := by
  obtain ⟨a, g, h⟩ := x
  have ha := Circle.coe_ne_zero a
  have hgd := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  simp only [phiMatrix, Circle.coe_inv]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨h1, -, -, h2⟩
    have hg : (g : Matrix (Fin 2) (Fin 2) ℂ) = ((a : ℂ)⁻¹) ^ 3 • 1 := by
      rw [← h1, smul_smul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, one_smul]
    have hh : (h : Matrix (Fin 3) (Fin 3) ℂ) = (a : ℂ) ^ 2 • 1 := by
      rw [← h2, smul_smul, ← mul_pow, mul_inv_cancel₀ ha, one_pow, one_smul]
    refine ⟨?_, hg, hh⟩
    rw [hg, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hgd
    have h6 : ((a : ℂ) ^ 6)⁻¹ = 1 := by rw [← hgd]; ring
    exact inv_eq_one.mp h6
  · rintro ⟨-, hg, hh⟩
    refine ⟨?_, rfl, rfl, ?_⟩
    · rw [hg, smul_smul, ← mul_pow, mul_inv_cancel₀ ha, one_pow, one_smul]
    · rw [hh, smul_smul, ← mul_pow, inv_mul_cancel₀ ha, one_pow, one_smul]

theorem W3a_GrandUnifiedTheories_phi_ker_card : Nat.card {x : GSM // phiMatrix x = 1} = 6 := by
  refine (Nat.card_congr ?_).trans (W3a_GrandUnifiedTheories_card_roots 6)
  exact
    { toFun := fun x => ⟨x.1.1, Circle.coe_injective (by
        rw [Circle.coe_pow, Circle.coe_one]
        exact ((W3a_GrandUnifiedTheories_phi_eq_one_iff x.1).mp x.2).1)⟩
      invFun := fun a => ⟨(a.1,
          ⟨((a.1⁻¹ ^ 3 : Circle) : ℂ) • 1, W3a_GrandUnifiedTheories_scalar_mem _ (by
            rw [Fintype.card_fin, ← pow_mul, inv_pow]; exact inv_eq_one.mpr a.2)⟩,
          ⟨((a.1 ^ 2 : Circle) : ℂ) • 1, W3a_GrandUnifiedTheories_scalar_mem _ (by
            rw [Fintype.card_fin, ← pow_mul]; exact a.2)⟩),
        (W3a_GrandUnifiedTheories_phi_eq_one_iff _).mpr
          ⟨by rw [← Circle.coe_pow, a.2, Circle.coe_one], by simp, by simp⟩⟩
      left_inv := fun x => by
        obtain ⟨⟨a, g, h⟩, hx⟩ := x
        obtain ⟨-, hg, hh⟩ := (W3a_GrandUnifiedTheories_phi_eq_one_iff _).mp hx
        have hg' : (g : Matrix (Fin 2) (Fin 2) ℂ) = ((a⁻¹ ^ 3 : Circle) : ℂ) • 1 := by
          rw [Circle.coe_pow]; exact hg
        have hh' : (h : Matrix (Fin 3) (Fin 3) ℂ) = ((a ^ 2 : Circle) : ℂ) • 1 := by
          rw [Circle.coe_pow]; exact hh
        apply Subtype.ext
        exact Prod.ext rfl (Prod.ext (Subtype.ext hg'.symm) (Subtype.ext hh'.symm))
      right_inv := fun a => rfl }

theorem W3a_GrandUnifiedTheories_phi_range_eq (A : Matrix Idx5 Idx5 ℂ) :
    (∃ x : GSM, phiMatrix x = A) ↔
      (A ∈ Matrix.specialUnitaryGroup Idx5 ℂ ∧
        ∀ i j, A (Sum.inl i) (Sum.inr j) = 0 ∧ A (Sum.inr j) (Sum.inl i) = 0) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨solution x,
      fun i j => ⟨by simp [phiMatrix], by simp [phiMatrix]⟩⟩
  · rintro ⟨hA, hblk⟩
    obtain ⟨hU, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hA
    have hAeq : A = Matrix.fromBlocks A.toBlocks₁₁ 0 0 A.toBlocks₂₂ := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rfl
      · simp [(hblk i j).1]
      · simp [(hblk j i).2]
      · rfl
    generalize A.toBlocks₁₁ = P at hAeq
    generalize A.toBlocks₂₂ = Q at hAeq
    subst hAeq
    have hPU : P ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ Q ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hU
      simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero,
        zero_add] at hU
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hU
      simp only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      exact ⟨hU.1, hU.2.2.2⟩
    have hdet' : P.det * Q.det = 1 := by rwa [Matrix.det_fromBlocks_zero₂₁] at hdet
    have hnorm : ‖P.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hPU.1)
    set w : Circle := Circle.exp (Complex.arg P.det / 6) with hwdef
    have hw : (w : ℂ) ^ 6 = P.det := by
      rw [hwdef, Circle.coe_exp, ← Complex.exp_nat_mul]
      have h := Complex.norm_mul_exp_arg_mul_I P.det
      rw [hnorm, Complex.ofReal_one, one_mul] at h
      calc Complex.exp (((6 : ℕ) : ℂ) * (((Complex.arg P.det / 6 : ℝ)) * Complex.I))
          = Complex.exp (Complex.arg P.det * Complex.I) := by congr 1; push_cast; ring
        _ = P.det := h
    have hw0 := Circle.coe_ne_zero w
    have hgmem : ((w⁻¹ ^ 3 : Circle) : ℂ) • P ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
      refine Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨W3a_GrandUnifiedTheories_smul_mem _ hPU.1, ?_⟩
      rw [Matrix.det_smul, Fintype.card_fin, Circle.coe_pow, Circle.coe_inv, ← hw]
      calc (((w : ℂ)⁻¹) ^ 3) ^ 2 * (w : ℂ) ^ 6 = ((w : ℂ)⁻¹ * w) ^ 6 := by ring
        _ = 1 := by rw [inv_mul_cancel₀ hw0, one_pow]
    have hhmem : ((w ^ 2 : Circle) : ℂ) • Q ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
      refine Matrix.mem_specialUnitaryGroup_iff.mpr
        ⟨W3a_GrandUnifiedTheories_smul_mem _ hPU.2, ?_⟩
      rw [Matrix.det_smul, Fintype.card_fin, Circle.coe_pow]
      calc ((w : ℂ) ^ 2) ^ 3 * Q.det = (w : ℂ) ^ 6 * Q.det := by ring
        _ = 1 := by rw [hw, hdet']
    refine ⟨(w, ⟨_, hgmem⟩, ⟨_, hhmem⟩), ?_⟩
    simp only [phiMatrix]
    congr 1
    · rw [smul_smul, Circle.coe_pow, Circle.coe_inv, ← mul_pow, mul_inv_cancel₀ hw0, one_pow,
        one_smul]
    · rw [smul_smul, Circle.coe_pow, Circle.coe_inv, ← mul_pow, inv_mul_cancel₀ hw0, one_pow,
        one_smul]

theorem W3a_GrandUnifiedTheories_beta_map_mul (x y : GSM) :
    betaMatrix (x * y) =
      ((betaMatrix x).1 * (betaMatrix y).1,
        (betaMatrix x).2.1 * (betaMatrix y).2.1,
        (betaMatrix x).2.2 * (betaMatrix y).2.2) := by
  obtain ⟨a, g, h⟩ := x
  obtain ⟨b, g', h'⟩ := y
  have hh : (((h * h' : Matrix.specialUnitaryGroup (Fin 3) ℂ)) : Matrix (Fin 3) (Fin 3) ℂ)
      = h * h' := rfl
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [betaMatrix, Prod.mk_mul_mk, Circle.coe_mul, Circle.coe_inv]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_pow, mul_inv, mul_comm]
  · simp only [betaMatrix, Prod.mk_mul_mk, hh, Circle.coe_mul, Circle.coe_inv]
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.diagonal_mul_diagonal, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_pow,
      mul_inv, mul_comm]

theorem W3a_GrandUnifiedTheories_beta_mem_specialUnitaryGroup (x : GSM) :
    (betaMatrix x).1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      (betaMatrix x).2.1 ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ∧
      (betaMatrix x).2.2 ∈ Matrix.specialUnitaryGroup Idx4 ℂ := by
  obtain ⟨a, g, h⟩ := x
  have ha := Circle.coe_ne_zero a
  have hh := Matrix.mem_specialUnitaryGroup_iff.mp h.2
  refine ⟨g.2, ?_, ?_⟩
  · rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    simp only [betaMatrix, Circle.coe_inv]
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      ext i
      fin_cases i <;> simp [W3a_GrandUnifiedTheories_star, W3a_GrandUnifiedTheories_conj, ha]
    · rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp [ha]
  · have e : (betaMatrix (a, g, h)).2.2 = Matrix.fromBlocks ((a : ℂ) • (h : Matrix (Fin 3) (Fin 3) ℂ))
        0 0 (((a⁻¹ ^ 3 : Circle) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
      simp [betaMatrix, Matrix.smul_one_eq_diagonal]
    rw [e, Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨W3a_GrandUnifiedTheories_fromBlocks_mem (W3a_GrandUnifiedTheories_smul_mem a hh.1)
      (W3a_GrandUnifiedTheories_smul_mem _ (one_mem _)), ?_⟩
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_smul, hh.2, Matrix.det_one]
    simp [ha]

theorem W3a_GrandUnifiedTheories_beta_eq_one_iff (x : GSM) :
    betaMatrix x = (1, 1, 1) ↔
      ((x.1 : ℂ) ^ 3 = 1 ∧
        (x.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
        (x.2.2 : Matrix (Fin 3) (Fin 3) ℂ) = (((x.1)⁻¹ : Circle) : ℂ) • 1) := by
  obtain ⟨a, g, h⟩ := x
  have ha := Circle.coe_ne_zero a
  simp only [betaMatrix, Circle.coe_inv, Prod.mk.injEq]
  constructor
  · rintro ⟨hg, hd, hb⟩
    have h3 : (a : ℂ) ^ 3 = 1 := by
      have := congrFun (congrFun hd 0) 0
      simpa [Matrix.diagonal] using this
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hb
    obtain ⟨h1, -, -, -⟩ := hb
    refine ⟨h3, hg, ?_⟩
    rw [← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · rintro ⟨h3, hg, hh⟩
    refine ⟨hg, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply, h3]
    · rw [hh, smul_smul, mul_inv_cancel₀ ha, one_smul]
      have : (fun _ : Fin 1 => ((a : ℂ)⁻¹) ^ 3) = fun _ => 1 := by
        ext; simp [h3]
      rw [this, Matrix.diagonal_one, Matrix.fromBlocks_one]

theorem W3a_GrandUnifiedTheories_beta_ker_card :
    Nat.card {x : GSM // betaMatrix x = (1, 1, 1)} = 3 := by
  refine (Nat.card_congr ?_).trans (W3a_GrandUnifiedTheories_card_roots 3)
  exact
    { toFun := fun x => ⟨x.1.1, Circle.coe_injective (by
        rw [Circle.coe_pow, Circle.coe_one]
        exact ((W3a_GrandUnifiedTheories_beta_eq_one_iff x.1).mp x.2).1)⟩
      invFun := fun a => ⟨(a.1, 1,
          ⟨((a.1⁻¹ : Circle) : ℂ) • 1, W3a_GrandUnifiedTheories_scalar_mem _ (by
            rw [Fintype.card_fin, inv_pow, a.2, inv_one])⟩),
        (W3a_GrandUnifiedTheories_beta_eq_one_iff _).mpr
          ⟨by rw [← Circle.coe_pow, a.2, Circle.coe_one], rfl, rfl⟩⟩
      left_inv := fun x => by
        obtain ⟨⟨a, g, h⟩, hx⟩ := x
        obtain ⟨-, hg, hh⟩ := (W3a_GrandUnifiedTheories_beta_eq_one_iff _).mp hx
        apply Subtype.ext
        exact Prod.ext rfl (Prod.ext (Subtype.ext hg.symm) (Subtype.ext hh.symm))
      right_inv := fun a => rfl }

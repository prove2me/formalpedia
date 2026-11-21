-- Prove2me | solution 1 for HigherOrderId.Certify.eq_82_83
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:35:12.483417+00:00
-- url     : https://prove2.me/submissions/90ca5db7-0e24-4f93-8012-d507fa9459b3

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion

section
open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify.Dev.B2
open HigherOrderId.Certify

lemma tri_sum (n : ℕ) : ∑ i ∈ Finset.range n, (n - i) = (n + 1).choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, (n - i) + n := by
      rw [show ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, ((n - i) + 1) from
        Finset.sum_congr rfl (fun i hi => by have := Finset.mem_range.mp hi; omega)]
      simp [Finset.sum_add_distrib]
    rw [this, ih, Nat.choose_succ_succ (n + 1) 1]
    simp; ring

lemma card_symIdx (m : ℕ) : Fintype.card (SymIdx m) = (m + 1).choose 2 := by
  rw [← tri_sum, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type,
    ← Fin.sum_univ_eq_sum_range (fun i => m - i) m]
  apply Finset.sum_congr rfl
  intro i _
  show (∑ y : Fin m, if i ≤ y then 1 else 0) = m - i
  rw [← Finset.card_filter]
  have : (Finset.univ.filter fun j : Fin m => i ≤ j) = Finset.Ici i := by ext j; simp
  rw [this, Fin.card_Ici]

/-- symmetric matrix with prescribed upper triangle -/
noncomputable def Bc {m : ℕ} (c : SymIdx m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if h : i ≤ j then c ⟨(i, j), h⟩ else c ⟨(j, i), le_of_not_ge h⟩

lemma Bc_symm {m : ℕ} (c : SymIdx m → ℝ) : (Bc c).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, Bc]
  by_cases h1 : i ≤ j <;> by_cases h2 : j ≤ i
  · have : i = j := le_antisymm h1 h2
    subst this; simp
  · simp [h1, h2]
  · simp [h1, h2]
  · exact absurd (le_total i j) (by tauto)

lemma Bc_ne {m : ℕ} (c : SymIdx m → ℝ) (hc : c ≠ 0) : Bc c ≠ 0 := by
  intro h
  apply hc; funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa [Bc, p.2] using this

end HigherOrderId.Certify.Dev.B2

namespace HigherOrderId.Certify

end HigherOrderId.Certify
end

section
open Matrix

namespace HigherOrderId.Certify.Dev.Nuc

variable {d : ℕ} {T : Type*} [Fintype T] [DecidableEq T]

theorem nuclear_le (A : Matrix (Fin d) T ℝ) :
    ∑ j, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues j) ≤
      ∑ a, Real.sqrt (∑ p, A a p ^ 2) := by
  have hM := Matrix.isHermitian_conjTranspose_mul_self A
  set lam : T → ℝ := hM.eigenvalues with hlam
  have hlam0 : ∀ j, 0 ≤ lam j :=
    fun j => (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg j
  set V : Matrix T T ℝ := (hM.eigenvectorUnitary : Matrix T T ℝ) with hV
  have hVV : Vᵀ * V = 1 := by
    have := Unitary.coe_star_mul_self hM.eigenvectorUnitary
    simpa [hV, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hVV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hVV
  have hspec : Aᵀ * A = V * diagonal lam * Vᵀ := by
    have := hM.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at this
    simpa [hV, hlam, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using this
  have hΛ : (A * V)ᵀ * (A * V) = diagonal lam := by
    calc (A * V)ᵀ * (A * V) = Vᵀ * (Aᵀ * A) * V := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = diagonal lam := by
          rw [hspec]
          calc Vᵀ * (V * diagonal lam * Vᵀ) * V = (Vᵀ * V) * diagonal lam * (Vᵀ * V) := by
                simp only [Matrix.mul_assoc]
            _ = _ := by rw [hVV]; simp
  set s : T → ℝ := fun j => Real.sqrt (lam j) with hs
  set sinv : T → ℝ := fun j => (s j)⁻¹ with hsinv
  set Y : Matrix (Fin d) T ℝ := A * V with hY
  set Yh : Matrix (Fin d) T ℝ := Y * diagonal sinv with hYh
  have hss : ∀ j, s j * s j = lam j := fun j => Real.mul_self_sqrt (hlam0 j)
  -- F1
  have F1 : ∑ j, s j = ∑ a, ∑ j, Yh a j * Y a j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have hcol : ∑ a, Y a j * Y a j = lam j := by
      have := congrFun (congrFun hΛ j) j
      simpa [Matrix.mul_apply, Matrix.transpose_apply] using this
    have : ∑ a, Yh a j * Y a j = sinv j * lam j := by
      rw [← hcol, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      simp [hYh, Matrix.mul_apply, Matrix.diagonal]; ring
    rw [this]
    by_cases h0 : s j = 0
    · have : lam j = 0 := by rw [← hss j, h0]; simp
      simp [hsinv, h0, this]
    · simp only [hsinv]; rw [← hss j]; field_simp
  -- F2
  have F2 : ∀ a, ∑ j, Y a j ^ 2 = ∑ p, A a p ^ 2 := by
    intro a
    have : (Y * Yᵀ) a a = (A * Aᵀ) a a := by
      rw [hY, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV', Matrix.one_mul]
    simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using this
  -- F3
  have F3 : ∀ a, ∑ j, Yh a j ^ 2 ≤ 1 := by
    intro a
    set P : Matrix (Fin d) (Fin d) ℝ := Yh * Yhᵀ with hP
    have hPs : Pᵀ = P := by
      rw [hP, Matrix.transpose_mul, Matrix.transpose_transpose]
    have hPP : P * P = P := by
      have hdiag : (diagonal sinv * diagonal sinv : Matrix T T ℝ) * diagonal lam *
          (diagonal sinv * diagonal sinv) = diagonal sinv * diagonal sinv := by
        simp only [Matrix.diagonal_mul_diagonal]
        congr 1; funext j
        by_cases h0 : s j = 0
        · simp [hsinv, h0]
        · have h1 : lam j = s j * s j := (hss j).symm
          simp only [hsinv, h1]; field_simp
      have ht : Yhᵀ = diagonal sinv * Yᵀ := by rw [hYh, Matrix.transpose_mul, Matrix.diagonal_transpose]
      have hΛ2 : ∀ X : Matrix T (Fin d) ℝ, Yᵀ * (Y * X) = diagonal lam * X := by
        intro X; rw [← Matrix.mul_assoc, hΛ]
      have hd2 : ∀ X : Matrix T (Fin d) ℝ, diagonal sinv * (diagonal sinv * (diagonal lam *
          (diagonal sinv * (diagonal sinv * X)))) = diagonal sinv * (diagonal sinv * X) := by
        intro X
        have := congrArg (· * X) hdiag
        simp only [Matrix.mul_assoc] at this
        exact this
      calc P * P = Y * (diagonal sinv * (diagonal sinv * (Yᵀ * (Y * (diagonal sinv *
            (diagonal sinv * Yᵀ)))))) := by
            rw [hP, hYh, ht]; simp only [Matrix.mul_assoc]
        _ = Y * (diagonal sinv * (diagonal sinv * (diagonal lam *
            (diagonal sinv * (diagonal sinv * Yᵀ))))) := by rw [hΛ2]
        _ = Y * (diagonal sinv * (diagonal sinv * Yᵀ)) := by rw [hd2]
        _ = P := by rw [hP, hYh, ht]; simp only [Matrix.mul_assoc]
    have h1 : P a a = ∑ j, Yh a j ^ 2 := by
      simp [hP, Matrix.mul_apply, sq]
    have h2 : (P * P) a a = ∑ b, P a b ^ 2 := by
      simp only [Matrix.mul_apply, sq]
      apply Finset.sum_congr rfl; intro b _
      have := congrFun (congrFun hPs a) b
      simp only [Matrix.transpose_apply] at this
      rw [this]
    rw [hPP] at h2
    have h3 : P a a ^ 2 ≤ ∑ b, P a b ^ 2 :=
      Finset.single_le_sum (f := fun b => P a b ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
    rw [← h2] at h3
    have h0 : 0 ≤ P a a := by rw [h1]; positivity
    rw [← h1]
    nlinarith
  calc ∑ j, s j = ∑ a, ∑ j, Yh a j * Y a j := F1
    _ ≤ ∑ a, Real.sqrt (∑ p, A a p ^ 2) := by
      apply Finset.sum_le_sum; intro a _
      calc ∑ j, Yh a j * Y a j ≤ Real.sqrt (∑ j, Yh a j ^ 2) * Real.sqrt (∑ j, Y a j ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ ≤ 1 * Real.sqrt (∑ p, A a p ^ 2) := by
            rw [F2 a]
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            calc Real.sqrt (∑ j, Yh a j ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (F3 a)
              _ = 1 := Real.sqrt_one
        _ = _ := one_mul _

end HigherOrderId.Certify.Dev.Nuc
end

section
open Matrix

namespace HigherOrderId.Certify.Dev.E82
open HigherOrderId.Certify
open HigherOrderId.Certify.Dev.B2

lemma sum_sym {m : ℕ} (f : Fin m → Fin m → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ p : SymIdx m, (if p.1.1 = p.1.2 then 1 else 2) * f p.1.1 p.1.2 = ∑ i, ∑ j, f i j := by
  have h1 : ∑ p : SymIdx m, (if p.1.1 = p.1.2 then (1:ℝ) else 2) * f p.1.1 p.1.2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≤ p.2),
        (if p.1 = p.2 then (1:ℝ) else 2) * f p.1 p.2 :=
    (Finset.sum_subtype (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≤ p.2))
      (by intro x; simp) (fun p => (if p.1 = p.2 then (1:ℝ) else 2) * f p.1 p.2)).symm
  rw [h1, Finset.sum_filter, Fintype.sum_prod_type]
  have h2 : ∑ i, ∑ j, f i j = ∑ i, ∑ j, ((if i ≤ j then f i j else 0) + (if j < i then f i j else 0)) := by
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    by_cases h : i ≤ j
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mp h]
  have h3 : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    rw [hf]
  rw [h2]
  simp only [Finset.sum_add_distrib]
  rw [h3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rcases lt_trichotomy i j with h | h | h
  · simp [h, h.le, ne_of_lt h]; ring
  · subst h; simp
  · simp [not_le.mpr h, not_lt.mpr h.le]

lemma quad_single {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : Fin d) (i j : Fin m) :
    (U * Matrix.single i j (1:ℝ) * Uᵀ) a a = U a i * U a j := by
  have : (U * Matrix.single i j (1:ℝ) * Uᵀ) a a =
      ∑ k, ∑ l, U a k * (Matrix.single i j (1:ℝ)) k l * U a l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [this]
  simp [Matrix.single_apply, ite_and, mul_comm]

lemma DUmat_apply {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : Fin d) (p : SymIdx m) :
    DUmat U a p = (if p.1.1 = p.1.2 then U a p.1.1 * U a p.1.1
      else Real.sqrt 2 * (U a p.1.1 * U a p.1.2)) := by
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only [DUmat, DU, symBasis]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    exact quad_single U a i i
  · simp only [h, if_false]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_add, Matrix.add_mul,
      Matrix.add_apply, quad_single, quad_single]
    have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    have h3 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    simp only [smul_eq_mul]
    field_simp
    have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h4]; ring


lemma quad_gen {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (a : Fin d) :
    (U * B * Uᵀ) a a = ∑ k, ∑ l, U a k * B k l * U a l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma row_sq {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : Fin d) :
    ∑ p, DUmat U a p ^ 2 = (∑ i, U a i ^ 2) ^ 2 := by
  have h1 : ∀ p : SymIdx m, DUmat U a p ^ 2 =
      (if p.1.1 = p.1.2 then (1:ℝ) else 2) * (U a p.1.1 * U a p.1.2) ^ 2 := by
    intro p
    rw [DUmat_apply]
    by_cases h : p.1.1 = p.1.2
    · simp only [h, if_true]; ring
    · simp only [h, if_false]
      have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      rw [mul_pow, h4]
  simp_rw [h1]
  rw [sum_sym (fun i j => (U a i * U a j) ^ 2) (fun i j => by ring)]
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma frob_row {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : Fin d) :
    frobNorm (vecMulVec (U a) (U a)) = ∑ i, U a i ^ 2 := by
  have : frobInner (vecMulVec (U a) (U a)) (vecMulVec (U a) (U a)) = (∑ i, U a i ^ 2) ^ 2 := by
    simp only [frobInner, Matrix.vecMulVec_apply]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  unfold frobNorm
  rw [this]
  exact Real.sqrt_sq (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem part_a {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) :
    ∑ j, singVals U j ≤ ∑ a, frobNorm (vecMulVec (U a) (U a)) := by
  have := Nuc.nuclear_le (DUmat U)
  unfold singVals
  refine this.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl; intro a _
  rw [row_sq, frob_row]
  exact Real.sqrt_sq (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem part_b {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hU : Uᵀ * U = 1) :
    ∑ a, frobNorm (vecMulVec (U a) (U a)) = (m : ℝ) := by
  simp_rw [frob_row]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ a, U a i ^ 2 = 1 := by
    intro i
    have := congrFun (congrFun hU i) i
    simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using this
  simp [this]

lemma DU_Bc {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (c : SymIdx m → ℝ) :
    DU U (Bc (fun p => if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2)) = DUmat U *ᵥ c := by
  funext a
  simp only [DU]
  rw [quad_gen]
  have hs := Bc_symm (fun p : SymIdx m => if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2)
  rw [← sum_sym (fun k l => U a k * Bc (fun p : SymIdx m => if p.1.1 = p.1.2 then c p else
      c p / Real.sqrt 2) k l * U a l) (fun i j => by
        have := congrFun (congrFun hs i) j
        simp only [Matrix.transpose_apply] at this
        rw [← this]; ring)]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl; intro p _
  rw [DUmat_apply]
  have hp := p.2
  have : Bc (fun q : SymIdx m => if q.1.1 = q.1.2 then c q else c q / Real.sqrt 2) p.1.1 p.1.2
      = if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2 := by
    simp [Bc, hp]
  rw [this]
  by_cases h : p.1.1 = p.1.2
  · simp only [h, if_true]; ring
  · simp only [h, if_false]
    have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
    have h4 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [h5]; ring

lemma singVals_pos {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hF : FullColRank U) (j : SymIdx m) :
    0 < singVals U j := by
  have hinj : Function.Injective (DUmat U).mulVec := by
    have key : ∀ c : SymIdx m → ℝ, DUmat U *ᵥ c = 0 → c = 0 := by
      intro c hc'
      set c' : SymIdx m → ℝ := fun p => if p.1.1 = p.1.2 then c p else c p / Real.sqrt 2 with hc'def
      have hD : DU U (Bc c') = 0 := by rw [hc'def, DU_Bc, hc']
      have hB0 : Bc c' = 0 := hF _ (Bc_symm c') hD
      have : c' = 0 := by
        by_contra hne; exact Bc_ne c' hne hB0
      funext p
      have := congrFun this p
      simp only [hc'def, Pi.zero_apply] at this
      by_cases h : p.1.1 = p.1.2
      · simpa [h] using this
      · simp only [h, if_false] at this
        have h2 : Real.sqrt 2 ≠ 0 := by positivity
        simpa [h2] using this
    intro x y hxy
    have h0 : DUmat U *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (key _ h0)
  have hpd := Matrix.PosDef.conjTranspose_mul_self (DUmat U) hinj
  exact Real.sqrt_pos.mpr (hpd.eigenvalues_pos j)


lemma jensen_inv {T : Type*} [Fintype T] [Nonempty T] (a : T → ℝ) (hpos : ∀ j, 0 < a j) (s : ℕ) :
    ((1 / (Fintype.card T : ℝ)) * ∑ j, a j)⁻¹ ^ s ≤
      (1 / (Fintype.card T : ℝ)) * ∑ j, (a j)⁻¹ ^ s := by
  have hc : (0:ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hconv : ConvexOn ℝ (Set.Ioi (0:ℝ)) fun x : ℝ => x ^ (-(s:ℤ)) := convexOn_zpow (-(s:ℤ))
  have := hconv.map_sum_le (t := Finset.univ) (w := fun _ : T => 1 / (Fintype.card T : ℝ))
    (p := a) (fun _ _ => by positivity)
    (by simp [Finset.sum_const, Finset.card_univ]) (fun j _ => hpos j)
  simp only [smul_eq_mul, ← Finset.mul_sum, _root_.zpow_neg, zpow_natCast] at this
  simp only [inv_pow]
  exact this

end HigherOrderId.Certify.Dev.E82

namespace HigherOrderId.Certify
open Dev.E82

theorem chk_eq_82_83 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d m : ℕ) (U : Matrix (Fin d) (Fin m) ℝ), 10 ≤ d → Uᵀ * U = 1 →
        (∑ j, singVals U j ≤ ∑ a, frobNorm (vecMulVec (U a) (U a))) ∧
        (∑ a, frobNorm (vecMulVec (U a) (U a)) = (m : ℝ)) ∧
        (1 ≤ m → FullColRank U →
          (∀ s ∈ ({2, 4} : Finset ℕ),
            ((1 / (Fintype.card (SymIdx m) : ℝ)) * ∑ j, singVals U j)⁻¹ ^ s ≤
                (1 / (Fintype.card (SymIdx m) : ℝ)) * ∑ j, (singVals U j)⁻¹ ^ s ∧
            ((m : ℝ) / (Fintype.card (SymIdx m) : ℝ))⁻¹ ^ s ≤
                ((1 / (Fintype.card (SymIdx m) : ℝ)) * ∑ j, singVals U j)⁻¹ ^ s) ∧
          (Fintype.card (SymIdx m) : ℝ) ^ 3 / (m : ℝ) ^ 2 ≤ ∑ j, (singVals U j)⁻¹ ^ 2 ∧
          c * (m : ℝ) ^ 4 ≤ (Fintype.card (SymIdx m) : ℝ) ^ 3 / (m : ℝ) ^ 2 ∧
          (Fintype.card (SymIdx m) : ℝ) ^ 5 / (m : ℝ) ^ 4 ≤ ∑ j, (singVals U j)⁻¹ ^ 4 ∧
          c * (m : ℝ) ^ 6 ≤ (Fintype.card (SymIdx m) : ℝ) ^ 5 / (m : ℝ) ^ 4) := by
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro d m U _ hU
  have ha := part_a U
  have hb := part_b U hU
  refine ⟨ha, hb, ?_⟩
  intro hm hF
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by linarith
  have hcard : Fintype.card (SymIdx m) = (m + 1).choose 2 := Dev.B2.card_symIdx m
  have hne : Nonempty (SymIdx m) := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]; exact Nat.choose_pos (by omega)
  set t : ℝ := (Fintype.card (SymIdx m) : ℝ) with ht
  have htv : t = (m : ℝ) * (m + 1) / 2 := by
    rw [ht, hcard, Nat.cast_choose_two]; push_cast; ring
  have htpos : 0 < t := by rw [htv]; positivity
  have hapos := singVals_pos U hF
  have hSpos : 0 < ∑ j, singVals U j := Finset.sum_pos (fun j _ => hapos j) Finset.univ_nonempty
  have hS : ∑ j, singVals U j ≤ m := ha.trans hb.le
  have hmean_pos : 0 < (1 / t) * ∑ j, singVals U j := by positivity
  have hmean_le : (1 / t) * ∑ j, singVals U j ≤ (m : ℝ) / t := by
    rw [one_div, inv_mul_eq_div]; exact div_le_div_of_nonneg_right hS htpos.le
  have hB : ∀ s : ℕ, ((m : ℝ) / t)⁻¹ ^ s ≤ ((1 / t) * ∑ j, singVals U j)⁻¹ ^ s := by
    intro s
    apply pow_le_pow_left₀ (by positivity)
    exact inv_anti₀ hmean_pos hmean_le
  have hA : ∀ s : ℕ, ((1 / t) * ∑ j, singVals U j)⁻¹ ^ s ≤ (1 / t) * ∑ j, (singVals U j)⁻¹ ^ s :=
    fun s => jensen_inv (singVals U) hapos s
  have ht2 : (m : ℝ) ^ 2 / 2 ≤ t := by rw [htv]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s _; exact ⟨hA s, hB s⟩
  · have h2 := (hB 2).trans (hA 2)
    calc t ^ 3 / (m : ℝ) ^ 2 = t * (((m : ℝ) / t)⁻¹ ^ 2) := by field_simp
      _ ≤ t * ((1 / t) * ∑ j, (singVals U j)⁻¹ ^ 2) := mul_le_mul_of_nonneg_left h2 htpos.le
      _ = _ := by field_simp
  · rw [le_div_iff₀ (by positivity)]
    have : ((m : ℝ) ^ 2 / 2) ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ (by positivity) ht2 3
    have h6 : (0:ℝ) ≤ (m : ℝ) ^ 6 := by positivity
    nlinarith
  · have h2 := (hB 4).trans (hA 4)
    calc t ^ 5 / (m : ℝ) ^ 4 = t * (((m : ℝ) / t)⁻¹ ^ 4) := by field_simp
      _ ≤ t * ((1 / t) * ∑ j, (singVals U j)⁻¹ ^ 4) := mul_le_mul_of_nonneg_left h2 htpos.le
      _ = _ := by field_simp
  · rw [le_div_iff₀ (by positivity)]
    have : ((m : ℝ) ^ 2 / 2) ^ 5 ≤ t ^ 5 := pow_le_pow_left₀ (by positivity) ht2 5
    have h6 : (0:ℝ) ≤ (m : ℝ) ^ 10 := by positivity
    nlinarith

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_eq_82_83 := @HigherOrderId.Certify.chk_eq_82_83

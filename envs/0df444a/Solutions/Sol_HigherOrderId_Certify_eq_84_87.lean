-- Prove2me | solution 1 for HigherOrderId.Certify.eq_84_87
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T12:42:45.321531+00:00
-- url     : https://prove2.me/submissions/bcd993ed-f07a-4f16-ba06-45980f5feae3

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model
import Definitions.Def_HigherOrderId_Certify_Completion
import Definitions.Def_HigherOrderId_Certify_TallCompletion

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

lemma DU_smul {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (r : ℝ) (A : Matrix (Fin m) (Fin m) ℝ) :
    DU U (r • A) = r • DU U A := by
  funext a; simp [DU]

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

end HigherOrderId.Certify
end

section
open Matrix

namespace HigherOrderId.Certify.Dev.E84
open HigherOrderId.Certify

lemma frobInner_eq_trace {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X Y = (Xᵀ * Y).trace := by
  simp only [frobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

lemma frobInner_add_right {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X (Y + Z) = frobInner X Y + frobInner X Z := by
  simp only [frobInner, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma frobInner_add_left {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (X + Y) Z = frobInner X Z + frobInner Y Z := by
  simp only [frobInner, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

lemma frobInner_smul_right {n : ℕ} (c : ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X (c • Y) = c * frobInner X Y := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma frobInner_smul_left {n : ℕ} (c : ℝ) (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (c • X) Y = c * frobInner X Y := by
  simp only [frobInner, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma frobInner_comm {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) : frobInner X Y = frobInner Y X := by
  simp only [frobInner]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

lemma frobInner_self_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobInner X X :=
  Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_self_nonneg _))

lemma frobNorm_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : frobNorm X ^ 2 = frobInner X X := by
  unfold frobNorm; exact Real.sq_sqrt (frobInner_self_nonneg X)

lemma frobInner_le {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    frobInner X Y ≤ frobNorm X * frobNorm Y := by
  have hX : frobInner X X = ∑ i, ∑ j, X i j ^ 2 := by simp [frobInner, sq]
  have hY : frobInner Y Y = ∑ i, ∑ j, Y i j ^ 2 := by simp [frobInner, sq]
  unfold frobNorm
  rw [hX, hY]
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n × Fin n))
    (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
  simp only [Fintype.sum_prod_type] at this
  exact this

/-- unitary-conjugated inner products -/
lemma frobInner_conj {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (B B' : Matrix (Fin m) (Fin m) ℝ) :
    frobInner (U * B * Uᵀ) (U * B' * Uᵀ) = frobInner B B' := by
  rw [frobInner_eq_trace, frobInner_eq_trace]
  have : (U * B * Uᵀ)ᵀ * (U * B' * Uᵀ) = U * (Bᵀ * B') * Uᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]

lemma frobInner_conj_rest {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (X : Matrix (Fin d) (Fin d) ℝ) (hX : Uᵀ * X * U = 0) :
    frobInner (U * B * Uᵀ) X = 0 := by
  rw [frobInner_eq_trace]
  have : (U * B * Uᵀ)ᵀ * X = U * (Bᵀ * (Uᵀ * X)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm]
  have h2 : Bᵀ * (Uᵀ * X) * U = Bᵀ * (Uᵀ * X * U) := by simp only [Matrix.mul_assoc]
  rw [h2, hX]; simp

lemma frobInner_diag {n : ℕ} (y : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (Matrix.diagonal y) X = y ⬝ᵥ diagVec X := by
  simp [frobInner, diagVec, dotProduct, Matrix.diagonal_apply]


lemma frobInner_sub_left {n : ℕ} (X Y Z : Matrix (Fin n) (Fin n) ℝ) :
    frobInner (X - Y) Z = frobInner X Z - frobInner Y Z := by
  simp only [frobInner, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma diag_Drest {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : ℝ) (y : Fin d → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (hDU : DU U B = a • y) (hadj : DUadj U y = a • B) :
    diagVec (DrestAdj U y) = (1 - a ^ 2) • y := by
  funext i
  have h1 : DrestAdj U y = Matrix.diagonal y - U * (DUadj U y) * Uᵀ := by
    simp [DrestAdj, DUadj, Matrix.mul_assoc]
  have h2 : (U * (a • B) * Uᵀ) i i = a * (a * y i) := by
    have := congrFun (B2.DU_smul U a B) i
    have h3 : DU U B i = a * y i := by
      have := congrFun hDU i; simpa using this
    simp only [DU, Pi.smul_apply, smul_eq_mul] at this h3 ⊢
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, h3]
  simp only [diagVec, h1, hadj, Matrix.sub_apply, Matrix.diagonal_apply_eq, h2, Pi.smul_apply,
    smul_eq_mul]
  ring

lemma inRest_Drest {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hU : Uᵀ * U = 1) (y : Fin d → ℝ) :
    InRest U (DrestAdj U y) := by
  have h1 : DrestAdj U y = Matrix.diagonal y - U * (DUadj U y) * Uᵀ := by
    simp [DrestAdj, DUadj, Matrix.mul_assoc]
  have hS : (DUadj U y)ᵀ = DUadj U y := by
    simp [DUadj, Matrix.transpose_mul, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsSymm
    rw [h1, Matrix.transpose_sub, Matrix.diagonal_transpose, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hS, Matrix.mul_assoc]
  · rw [h1]
    have e1 : Uᵀ * Matrix.diagonal y * U = DUadj U y := rfl
    have e2 : Uᵀ * (U * DUadj U y * Uᵀ) * U = DUadj U y := by
      calc Uᵀ * (U * DUadj U y * Uᵀ) * U = (Uᵀ * U) * DUadj U y * (Uᵀ * U) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU]; simp
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2, sub_self]

lemma inner_Drest {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (y : Fin d → ℝ)
    (X : Matrix (Fin d) (Fin d) ℝ) (hX : Uᵀ * X * U = 0) :
    frobInner (DrestAdj U y) X = y ⬝ᵥ diagVec X := by
  have h1 : DrestAdj U y = Matrix.diagonal y - U * (DUadj U y) * Uᵀ := by
    simp [DrestAdj, DUadj, Matrix.mul_assoc]
  rw [h1, frobInner_sub_left, frobInner_conj_rest U _ X hX, sub_zero, frobInner_diag]

noncomputable def rr {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : ℝ) (y : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := (-(a / (1 - a ^ 2))) • DrestAdj U y

lemma rr_rest {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hU : Uᵀ * U = 1) (a : ℝ) (y : Fin d → ℝ) :
    InRest U (rr U a y) := by
  obtain ⟨h1, h2⟩ := inRest_Drest U hU y
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsSymm at h1 ⊢
    rw [rr, Matrix.transpose_smul, h1]
  · rw [rr, Matrix.mul_smul, Matrix.smul_mul, h2, smul_zero]

lemma rr_diag {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : ℝ) (y : Fin d → ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (hDU : DU U B = a • y) (hadj : DUadj U y = a • B)
    (ha : 1 - a ^ 2 ≠ 0) : diagVec (rr U a y) = (-a) • y := by
  funext i
  have := congrFun (diag_Drest U a y B hDU hadj) i
  simp only [diagVec, rr, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply] at this ⊢
  rw [this]; field_simp

lemma inner_rr {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (hU : Uᵀ * U = 1)
    (ai aj : ℝ) (yi yj : Fin d → ℝ) (Bj : Matrix (Fin m) (Fin m) ℝ)
    (hDU : DU U Bj = aj • yj) (hadj : DUadj U yj = aj • Bj) :
    frobInner (rr U ai yi) (rr U aj yj) =
      (-(ai / (1 - ai ^ 2))) * (-(aj / (1 - aj ^ 2))) * ((1 - aj ^ 2) * (yi ⬝ᵥ yj)) := by
  have hrest := (inRest_Drest U hU yj).2
  have := inner_Drest U yi (DrestAdj U yj) hrest
  rw [diag_Drest U aj yj Bj hDU hadj, dotProduct_smul, smul_eq_mul] at this
  rw [rr, rr, frobInner_smul_left, frobInner_smul_right, this]; ring

lemma rr_eq {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (a : ℝ) (y : Fin d → ℝ) :
    (-(a / (1 - a ^ 2))) • DrestAdj U y = rr U a y := rfl

end HigherOrderId.Certify.Dev.E84
end

section
open Matrix

namespace HigherOrderId.Certify
open Dev.E84 Dev.E82

theorem chk_eq_84_87 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (d m : ℕ) (U : Matrix (Fin d) (Fin m) ℝ), 10 ≤ d → Uᵀ * U = 1 → 6 ≤ m →
        FullColRank U →
        ((Finset.univ.filter (fun j => (1 / 2 : ℝ) < singVals U j)).card ≤ 2 * m) ∧
        (∃ I : Finset (SymIdx m),
          (Fintype.card (SymIdx m) : ℝ) - 2 * m ≤ (I.card : ℝ) ∧
          (m : ℝ) ^ 2 / 4 ≤ (Fintype.card (SymIdx m) : ℝ) - 2 * m ∧
          ∀ j ∈ I, singVals U j ≤ 1 / 2) ∧
        (∀ (I : Finset (SymIdx m)),
          (Fintype.card (SymIdx m) : ℝ) - 2 * m ≤ (I.card : ℝ) →
          (∀ j ∈ I, singVals U j ≤ 1 / 2) →
          ∀ (B : SymIdx m → Matrix (Fin m) (Fin m) ℝ) (y : SymIdx m → Fin d → ℝ),
            (∀ j ∈ I, (B j).IsSymm) →
            (∀ i ∈ I, ∀ j ∈ I, frobInner (B i) (B j) = if i = j then 1 else 0) →
            (∀ i ∈ I, ∀ j ∈ I, y i ⬝ᵥ y j = if i = j then 1 else 0) →
            (∀ j ∈ I, DU U (B j) = singVals U j • y j ∧ DUadj U (y j) = singVals U j • B j) →
            (∀ j ∈ I, diagVec (DrestAdj U (y j)) = (1 - singVals U j ^ 2) • y j) ∧
            (∀ j ∈ I,
              InRest U ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ∧
              diagVec ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) =
                (-(singVals U j)) • y j ∧
              (∀ r' : Matrix (Fin d) (Fin d) ℝ, InRest U r' →
                diagVec r' = (-(singVals U j)) • y j →
                frobNorm ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ≤
                  frobNorm r') ∧
              frobNorm ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ^ 2 =
                singVals U j ^ 2 / (1 - singVals U j ^ 2)) ∧
            (∀ j ∈ I,
              IsSymZeroDiag (U * B j * Uᵀ +
                (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ∧
              frobNorm (U * B j * Uᵀ +
                (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) ^ 2 =
                (1 - singVals U j ^ 2)⁻¹ ∧
              1 ≤ (1 - singVals U j ^ 2)⁻¹ ∧ (1 - singVals U j ^ 2)⁻¹ ≤ 4 / 3) ∧
            (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
              frobInner
                  (U * B i * Uᵀ + (-(singVals U i / (1 - singVals U i ^ 2))) • DrestAdj U (y i))
                  (U * B j * Uᵀ + (-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j))
                = 0 ∧
              frobInner ((-(singVals U i / (1 - singVals U i ^ 2))) • DrestAdj U (y i))
                  ((-(singVals U j / (1 - singVals U j ^ 2))) • DrestAdj U (y j)) = 0) ∧
            ((1 / (I.card : ℝ)) * ∑ j ∈ I, singVals U j)⁻¹ ^ 2 ≤
              (1 / (I.card : ℝ)) * ∑ j ∈ I, (singVals U j)⁻¹ ^ 2 ∧
            ∑ j ∈ I, singVals U j ≤ ∑ j, singVals U j ∧
            ∑ j, singVals U j ≤ (m : ℝ) ∧
            (I.card : ℝ) ^ 3 / (∑ j ∈ I, singVals U j) ^ 2 ≤ ∑ j ∈ I, (singVals U j)⁻¹ ^ 2 ∧
            (I.card : ℝ) ^ 3 / (m : ℝ) ^ 2 ≤ (I.card : ℝ) ^ 3 / (∑ j ∈ I, singVals U j) ^ 2 ∧
            c * (m : ℝ) ^ 4 ≤ (I.card : ℝ) ^ 3 / (m : ℝ) ^ 2) := by
  refine ⟨1 / 64, by norm_num, ?_⟩
  intro d m U _ hU hm hF
  have hcard : Fintype.card (SymIdx m) = (m + 1).choose 2 := Dev.B2.card_symIdx m
  set t : ℝ := (Fintype.card (SymIdx m) : ℝ) with ht
  have hmR : (6:ℝ) ≤ m := by exact_mod_cast hm
  have htv : t = (m : ℝ) * (m + 1) / 2 := by
    rw [ht, hcard, Nat.cast_choose_two]; push_cast; ring
  have hS : ∑ j, singVals U j ≤ m := (part_a U).trans (part_b U hU).le
  have hnn : ∀ j, 0 ≤ singVals U j := fun j => Real.sqrt_nonneg _
  have hpos := singVals_pos U hF
  have hgap : (m : ℝ) ^ 2 / 4 ≤ t - 2 * m := by rw [htv]; nlinarith
  have hJ : (Finset.univ.filter (fun j => (1 / 2 : ℝ) < singVals U j)).card ≤ 2 * m := by
    set J := Finset.univ.filter (fun j => (1 / 2 : ℝ) < singVals U j) with hJdef
    have h1 : J.card • (1 / 2 : ℝ) ≤ ∑ j ∈ J, singVals U j :=
      Finset.card_nsmul_le_sum J _ _ (fun j hj => (Finset.mem_filter.mp hj).2.le)
    have h2 : ∑ j ∈ J, singVals U j ≤ ∑ j, singVals U j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnn j)
    rw [nsmul_eq_mul] at h1
    have : (J.card : ℝ) ≤ 2 * m := by linarith
    exact_mod_cast this
  refine ⟨hJ, ?_, ?_⟩
  · refine ⟨Finset.univ.filter (fun j => singVals U j ≤ 1 / 2), ?_, ?_, ?_⟩
    · have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (SymIdx m)))
        (fun j => singVals U j ≤ 1 / 2)
      simp only [not_le, Finset.card_univ] at this
      have h3 : ((Finset.univ.filter (fun j => singVals U j ≤ 1 / 2)).card : ℝ) +
          (Finset.univ.filter (fun j => (1 / 2 : ℝ) < singVals U j)).card = t := by
        rw [ht]; exact_mod_cast this
      have h4 : ((Finset.univ.filter (fun j => (1 / 2 : ℝ) < singVals U j)).card : ℝ) ≤ 2 * m := by
        exact_mod_cast hJ
      linarith
    · exact hgap
    · intro j hj; exact (Finset.mem_filter.mp hj).2
  · intro I hIcard hIle B y hBs hBo hyo hrel
    have hn : (m : ℝ) ^ 2 / 4 ≤ I.card := by linarith
    have hnpos : (0:ℝ) < I.card := by nlinarith
    have hIne : I.Nonempty := by
      apply Finset.card_pos.mp; exact_mod_cast hnpos
    have hfact : ∀ j ∈ I, 1 - singVals U j ^ 2 ≠ 0 ∧ 0 < 1 - singVals U j ^ 2 ∧
        3 / 4 ≤ 1 - singVals U j ^ 2 := by
      intro j hj
      have h1 := hIle j hj
      have h2 := hnn j
      have : singVals U j ^ 2 ≤ 1 / 4 := by nlinarith
      refine ⟨by linarith, by linarith, by linarith⟩
    have hyy : ∀ j ∈ I, y j ⬝ᵥ y j = 1 := fun j hj => by have := hyo j hj j hj; rwa [if_pos rfl] at this
    have hBB : ∀ j ∈ I, frobInner (B j) (B j) = 1 := fun j hj => by have := hBo j hj j hj; rwa [if_pos rfl] at this
    have hNr : ∀ j ∈ I, frobInner (rr U (singVals U j) (y j)) (rr U (singVals U j) (y j)) =
        singVals U j ^ 2 / (1 - singVals U j ^ 2) := by
      intro j hj
      rw [inner_rr U hU _ _ _ _ _ (hrel j hj).1 (hrel j hj).2, hyy j hj]
      obtain ⟨h0, _, _⟩ := hfact j hj
      field_simp
    have hQQ : ∀ i ∈ I, ∀ j ∈ I, frobInner (U * B i * Uᵀ + rr U (singVals U i) (y i))
        (U * B j * Uᵀ + rr U (singVals U j) (y j)) =
        frobInner (B i) (B j) + frobInner (rr U (singVals U i) (y i)) (rr U (singVals U j) (y j)) := by
      intro i hi j hj
      rw [frobInner_add_left, frobInner_add_right, frobInner_add_right, frobInner_conj U hU,
        frobInner_conj_rest U _ _ (rr_rest U hU _ _).2, frobInner_comm (rr U _ (y i)) (U * B j * Uᵀ),
        frobInner_conj_rest U _ _ (rr_rest U hU _ _).2]
      ring
    simp only [rr_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      exact diag_Drest U _ _ _ (hrel j hj).1 (hrel j hj).2
    · intro j hj
      obtain ⟨h0, h1, h2⟩ := hfact j hj
      refine ⟨rr_rest U hU _ _, rr_diag U _ _ _ (hrel j hj).1 (hrel j hj).2 h0, ?_, ?_⟩
      · intro r' hr' hdr
        have hin : frobInner (rr U (singVals U j) (y j)) r' =
            singVals U j ^ 2 / (1 - singVals U j ^ 2) := by
          rw [rr, frobInner_smul_left, inner_Drest U _ r' hr'.2, hdr, dotProduct_smul, hyy j hj]
          field_simp
          try ring
        have hsq := frobNorm_sq (rr U (singVals U j) (y j))
        rw [hNr j hj] at hsq
        have hcs := frobInner_le (rr U (singVals U j) (y j)) r'
        rw [hin] at hcs
        by_contra hlt
        push_neg at hlt
        have hr0 : 0 ≤ frobNorm r' := Real.sqrt_nonneg _
        have hrr0 : 0 ≤ frobNorm (rr U (singVals U j) (y j)) := Real.sqrt_nonneg _
        nlinarith
      · rw [frobNorm_sq, hNr j hj]
    · intro j hj
      obtain ⟨h0, h1, h2⟩ := hfact j hj
      have hQN : frobInner (U * B j * Uᵀ + rr U (singVals U j) (y j))
          (U * B j * Uᵀ + rr U (singVals U j) (y j)) = (1 - singVals U j ^ 2)⁻¹ := by
        rw [hQQ j hj j hj, hBB j hj, hNr j hj]; field_simp; ring
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · unfold Matrix.IsSymm
        rw [Matrix.transpose_add, (rr_rest U hU _ _).1.eq]
        congr 1
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, (hBs j hj).eq,
          Matrix.mul_assoc]
      · intro i
        have h5 := congrFun (rr_diag U _ _ _ (hrel j hj).1 (hrel j hj).2 h0) i
        have h6 := congrFun (hrel j hj).1 i
        simp only [diagVec, Pi.smul_apply, smul_eq_mul] at h5 h6
        simp only [DU] at h6
        rw [Matrix.add_apply, h5, h6]; ring
      · rw [frobNorm_sq, hQN]
      · exact one_le_inv₀ h1 |>.mpr (by nlinarith [sq_nonneg (singVals U j)])
      · rw [inv_le_comm₀ h1 (by norm_num)]; linarith
    · intro i hi j hj hij
      have hBij : frobInner (B i) (B j) = 0 := by simpa [hij] using hBo i hi j hj
      have hr : frobInner (rr U (singVals U i) (y i)) (rr U (singVals U j) (y j)) = 0 := by
        rw [inner_rr U hU _ _ _ _ _ (hrel j hj).1 (hrel j hj).2]
        have : y i ⬝ᵥ y j = 0 := by simpa [hij] using hyo i hi j hj
        rw [this]; ring
      exact ⟨by rw [hQQ i hi j hj, hBij, hr]; ring, hr⟩
    · -- Jensen part
      have hSIpos : 0 < ∑ j ∈ I, singVals U j := Finset.sum_pos (fun j _ => hpos j) hIne
      have hSIle : ∑ j ∈ I, singVals U j ≤ ∑ j, singVals U j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnn j)
      haveI : Nonempty I := hIne.to_subtype
      have hjen : ∀ s : ℕ, ((1 / (I.card : ℝ)) * ∑ j ∈ I, singVals U j)⁻¹ ^ s ≤
          (1 / (I.card : ℝ)) * ∑ j ∈ I, (singVals U j)⁻¹ ^ s := by
        intro s
        have := Dev.E82.jensen_inv (fun j : I => singVals U j) (fun j => hpos j) s
        beta_reduce at this
        rw [Fintype.card_coe, Finset.sum_coe_sort I (fun j => singVals U j),
          Finset.sum_coe_sort I (fun j => (singVals U j)⁻¹ ^ s)] at this
        exact this
      have hm0 : (0:ℝ) < m := by linarith
      have h3 : (I.card : ℝ) ^ 3 / (∑ j ∈ I, singVals U j) ^ 2 ≤ ∑ j ∈ I, (singVals U j)⁻¹ ^ 2 := by
        have h2 := hjen 2
        calc (I.card : ℝ) ^ 3 / (∑ j ∈ I, singVals U j) ^ 2
            = I.card * (((1 / (I.card : ℝ)) * ∑ j ∈ I, singVals U j)⁻¹ ^ 2) := by
              field_simp
          _ ≤ I.card * ((1 / (I.card : ℝ)) * ∑ j ∈ I, (singVals U j)⁻¹ ^ 2) :=
              mul_le_mul_of_nonneg_left h2 hnpos.le
          _ = _ := by field_simp
      have h4 : (I.card : ℝ) ^ 3 / (m : ℝ) ^ 2 ≤ (I.card : ℝ) ^ 3 / (∑ j ∈ I, singVals U j) ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : ∑ j ∈ I, singVals U j ≤ m := hSIle.trans hS
        nlinarith
      refine ⟨hjen 2, hSIle, hS, h3, h4, ?_⟩
      rw [le_div_iff₀ (by positivity)]
      have : ((m : ℝ) ^ 2 / 4) ^ 3 ≤ (I.card : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hn 3
      have h6 : (0:ℝ) ≤ (m : ℝ) ^ 6 := by positivity
      nlinarith

end HigherOrderId.Certify
end

theorem solution : type_of% @HigherOrderId.Certify.chk_eq_84_87 := @HigherOrderId.Certify.chk_eq_84_87

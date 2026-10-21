-- Prove2me | solution 1 for NetPriceDisc.Random.theorem_5_1_dense
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:00:12.003103+00:00
-- url     : https://prove2.me/submissions/9a7611eb-7dc2-4fe7-b08d-14d4841f3309

import Mathlib
import Definitions.Def_NetPriceDisc_Random_Model
import Theorems.Thm_NetPriceDisc_Random_eq_3
import Theorems.Thm_NetPriceDisc_Random_eq_4
import Theorems.Thm_NetPriceDisc_Random_eq_12_rayleigh
import Theorems.Thm_NetPriceDisc_Random_eq_14
open Matrix
open scoped Matrix.Norms.L2Operator

namespace NetPriceDisc.Random.PDRAux
open NetPriceDisc.Random

lemma wt_nonneg {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset (Fin n × Fin n)) :
    0 ≤ q ^ S.card * (1 - q) ^ ((Finset.univ : Finset (Fin n)).offDiag.card - S.card) := by
  have : 0 ≤ 1 - q := by linarith
  positivity

lemma erExpect_mono {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {F H : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (h : ∀ S ∈ (Finset.univ : Finset (Fin n)).offDiag.powerset, F (adjOf S) ≤ H (adjOf S)) :
    erExpect n q F ≤ erExpect n q H := by
  unfold erExpect
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (h S hS) (wt_nonneg hq0 hq1 S)

lemma erExpect_nonneg {n : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {F : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (h : ∀ S ∈ (Finset.univ : Finset (Fin n)).offDiag.powerset, 0 ≤ F (adjOf S)) :
    0 ≤ erExpect n q F := by
  unfold erExpect
  apply Finset.sum_nonneg
  intro S hS
  exact mul_nonneg (wt_nonneg hq0 hq1 S) (h S hS)

lemma erExpect_add {n : ℕ} {q : ℝ} (F H : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    erExpect n q (fun G => F G + H G) = erExpect n q F + erExpect n q H := by
  unfold erExpect; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro S _; ring

lemma erExpect_const_mul {n : ℕ} {q : ℝ} (c : ℝ) (F : Matrix (Fin n) (Fin n) ℝ → ℝ) :
    erExpect n q (fun G => c * F G) = c * erExpect n q F := by
  unfold erExpect; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _; ring

lemma adjOf_nonneg {n : ℕ} (S : Finset (Fin n × Fin n)) : ∀ i j, 0 ≤ adjOf S i j := by
  intro i j; unfold adjOf; split_ifs <;> norm_num

lemma adjOf_bin {n : ℕ} (S : Finset (Fin n × Fin n)) : ∀ i j, adjOf S i j = 0 ∨ adjOf S i j = 1 := by
  intro i j; unfold adjOf; split_ifs <;> simp

lemma adjOf_diag {n : ℕ} (S : Finset (Fin n × Fin n))
    (hS : S ⊆ (Finset.univ : Finset (Fin n)).offDiag) : ∀ i, adjOf S i i = 0 := by
  intro i; unfold adjOf
  have : (i, i) ∉ S := by
    intro h; have := hS h; simp at this
  simp [this]

lemma adjOf_ne_zero {n : ℕ} (S : Finset (Fin n × Fin n)) (hS : S.Nonempty) : adjOf S ≠ 0 := by
  obtain ⟨⟨i, j⟩, h⟩ := hS
  intro h0
  have := congrFun (congrFun h0 i) j
  simp [adjOf, h] at this

lemma adjOf_empty {n : ℕ} : adjOf (∅ : Finset (Fin n × Fin n)) = 0 := by
  ext i j; simp [adjOf]

lemma pow_entries_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hA l j))

lemma walks_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    0 ≤ walks A k := by
  unfold walks
  apply Finset.sum_nonneg; intro i _
  simp only [ones, one_mul, mulVec, dotProduct, mul_one]
  apply Finset.sum_nonneg; intro j _
  exact pow_entries_nonneg A hA k i j

lemma walks_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    walks (c • A) k = c ^ k * walks A k := by
  unfold walks
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

lemma sym_nonneg {n : ℕ} (S : Finset (Fin n × Fin n)) :
    ∀ i j, 0 ≤ (adjOf S + (adjOf S)ᵀ) i j := by
  intro i j
  simp only [Matrix.add_apply, Matrix.transpose_apply]
  exact add_nonneg (adjOf_nonneg S i j) (adjOf_nonneg S j i)
noncomputable def vn {n : ℕ} (x : Fin n → ℝ) : ℝ := ‖WithLp.toLp 2 x‖

lemma vn_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ vn x := norm_nonneg _

lemma vn_sq {n : ℕ} (x : Fin n → ℝ) : vn x ^ 2 = x ⬝ᵥ x := by
  unfold vn; rw [EuclideanSpace.norm_sq_eq]; simp [dotProduct, sq]

lemma dot_le {n : ℕ} (x y : Fin n → ℝ) : x ⬝ᵥ y ≤ vn x * vn y := by
  have h1 : inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rw [← h1]; exact real_inner_le_norm _ _

lemma vn_add_le {n : ℕ} (x y : Fin n → ℝ) : vn (x + y) ≤ vn x + vn y := by
  unfold vn; rw [WithLp.toLp_add]; exact norm_add_le _ _

lemma vn_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : vn (c • x) = |c| * vn x := by
  unfold vn; rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma vn_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    vn (A *ᵥ x) ≤ ‖A‖ * vn x := by
  unfold vn; simpa using Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)

lemma vn_le_of_abs {n : ℕ} {x y : Fin n → ℝ} (h : ∀ i, |x i| ≤ y i) : vn x ≤ vn y := by
  have : vn x ^ 2 ≤ vn y ^ 2 := by
    rw [vn_sq, vn_sq]; unfold dotProduct; apply Finset.sum_le_sum; intro i _
    have h1 := h i
    have h2 := abs_nonneg (x i)
    have h3 : x i * x i = |x i| * |x i| := (abs_mul_abs_self (x i)).symm
    rw [h3]; exact mul_le_mul h1 h1 h2 (le_trans h2 h1)
  exact (pow_le_pow_iff_left₀ (vn_nonneg x) (vn_nonneg y) (by norm_num)).1 this

lemma vn_abs {n : ℕ} (x : Fin n → ℝ) : vn (fun i => |x i|) = vn x := by
  have : vn (fun i => |x i|) ^ 2 = vn x ^ 2 := by
    rw [vn_sq, vn_sq]; simp [dotProduct, abs_mul_abs_self]
  exact (pow_left_inj₀ (vn_nonneg _) (vn_nonneg x) (by norm_num)).1 this

lemma dot_self_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x := by
  rw [← vn_sq]; positivity

lemma coercive_inv {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c)
    (h : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x)) : M * M⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have h0 : M *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have h1 := h (x - y)
  rw [h0, dotProduct_zero] at h1
  have h2 := dot_self_nonneg (x - y)
  have h3 : (x - y) ⬝ᵥ (x - y) = 0 := by
    by_contra hne
    have : 0 < (x - y) ⬝ᵥ (x - y) := lt_of_le_of_ne h2 (Ne.symm hne)
    nlinarith
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 h3)

lemma quad_le_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ ‖A‖ * (x ⬝ᵥ x) := by
  have h1 := dot_le x (A *ᵥ x)
  have h2 := vn_mulVec A x
  have h3 : vn x * vn (A *ᵥ x) ≤ vn x * (‖A‖ * vn x) :=
    mul_le_mul_of_nonneg_left h2 (vn_nonneg x)
  rw [← vn_sq]; nlinarith

/-- The key deterministic inequality (regret as a quadratic form). -/
lemma det_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlam : 0 < specNorm (G + Gᵀ)) :
    ones n ⬝ᵥ ((1 - (ρ / specNorm (G + Gᵀ)) • (G + Gᵀ))⁻¹ *ᵥ ones n) -
      ones n ⬝ᵥ ((1 - (2 * ρ / specNorm (G + Gᵀ)) • G)⁻¹ *ᵥ ones n) ≤
    vn (((ρ / specNorm (G + Gᵀ)) • (G - Gᵀ)) *ᵥ
      ((1 - (ρ / specNorm (G + Gᵀ)) • (G + Gᵀ))⁻¹ *ᵥ ones n)) ^ 2 / (1 - ρ) := by
  set lam := specNorm (G + Gᵀ) with hlamdef
  set S : Matrix (Fin n) (Fin n) ℝ := 1 - (ρ / lam) • (G + Gᵀ) with hSdef
  set T : Matrix (Fin n) (Fin n) ℝ := 1 - (2 * ρ / lam) • G with hTdef
  set N : Matrix (Fin n) (Fin n) ℝ := (ρ / lam) • (G - Gᵀ) with hNdef
  have h1ρ : 0 < 1 - ρ := by linarith
  have hTSN : T = S - N := by
    rw [hTdef, hSdef, hNdef]; ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
      smul_eq_mul]
    ring
  have hScoer : ∀ x, (1 - ρ) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x) := by
    intro x
    rw [hSdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    have hq := quad_le_norm (G + Gᵀ) x
    have hx := dot_self_nonneg x
    have : ρ / lam * (x ⬝ᵥ ((G + Gᵀ) *ᵥ x)) ≤ ρ * (x ⬝ᵥ x) := by
      have h2 : ρ / lam * (x ⬝ᵥ ((G + Gᵀ) *ᵥ x)) ≤ ρ / lam * (lam * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      have h3 : ρ / lam * (lam * (x ⬝ᵥ x)) = ρ * (x ⬝ᵥ x) := by field_simp
      linarith
    linarith
  have hNanti : ∀ x, x ⬝ᵥ (N *ᵥ x) = 0 := by
    intro x
    rw [hNdef, Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub]
    have : x ⬝ᵥ (Gᵀ *ᵥ x) = x ⬝ᵥ (G *ᵥ x) := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
    rw [this, sub_self, smul_zero]
  have hNbil : ∀ y z, y ⬝ᵥ (N *ᵥ z) = -(z ⬝ᵥ (N *ᵥ y)) := by
    intro y z
    have h := hNanti (y + z)
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hNanti y,
      hNanti z] at h
    linarith
  have hTcoer : ∀ x, (1 - ρ) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (T *ᵥ x) := by
    intro x
    rw [hTSN, Matrix.sub_mulVec, dotProduct_sub, hNanti x, sub_zero]
    exact hScoer x
  have hSsymm : Sᵀ = S := by
    rw [hSdef]; ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]; ring
  have hSsym : ∀ y z, y ⬝ᵥ (S *ᵥ z) = z ⬝ᵥ (S *ᵥ y) := by
    intro y z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSsymm, dotProduct_comm]
  have hSinv := coercive_inv S (1 - ρ) h1ρ hScoer
  have hTinv := coercive_inv T (1 - ρ) h1ρ hTcoer
  set v := S⁻¹ *ᵥ ones n with hvdef
  set u := T⁻¹ *ᵥ ones n with hudef
  have hSv : S *ᵥ v = ones n := by rw [hvdef, Matrix.mulVec_mulVec, hSinv, Matrix.one_mulVec]
  have hTu : T *ᵥ u = ones n := by rw [hudef, Matrix.mulVec_mulVec, hTinv, Matrix.one_mulVec]
  set w := u - v with hwdef
  have hTw : T *ᵥ w = N *ᵥ v := by
    rw [hwdef, Matrix.mulVec_sub, hTu, hTSN, Matrix.sub_mulVec, hSv]; abel
  have e1 : ones n ⬝ᵥ w = v ⬝ᵥ (S *ᵥ w) := by
    rw [← hSv, dotProduct_comm, hSsym w v]
  have e2 : v ⬝ᵥ (T *ᵥ w) = 0 := by rw [hTw]; exact hNanti v
  have e3 : v ⬝ᵥ (T *ᵥ w) = v ⬝ᵥ (S *ᵥ w) - v ⬝ᵥ (N *ᵥ w) := by
    rw [hTSN, Matrix.sub_mulVec, dotProduct_sub]
  have e4 : w ⬝ᵥ (T *ᵥ w) = w ⬝ᵥ (N *ᵥ v) := by rw [hTw]
  have e5 : w ⬝ᵥ (T *ᵥ w) = w ⬝ᵥ (S *ᵥ w) := by
    rw [hTSN, Matrix.sub_mulVec, dotProduct_sub, hNanti w, sub_zero]
  have e7 := hNbil v w
  have hkey : ones n ⬝ᵥ v - ones n ⬝ᵥ u = w ⬝ᵥ (S *ᵥ w) := by
    have : ones n ⬝ᵥ u = ones n ⬝ᵥ v + ones n ⬝ᵥ w := by rw [hwdef, dotProduct_sub]; ring
    linarith
  rw [hkey]
  -- bound
  have hc := hScoer w
  have hww := vn_sq w
  have hd := dot_le w (N *ᵥ v)
  have hS_eq : w ⬝ᵥ (S *ᵥ w) = w ⬝ᵥ (N *ᵥ v) := by rw [← e5, e4]
  have hvw := vn_nonneg w
  have hvN := vn_nonneg (N *ᵥ v)
  have hwb : (1 - ρ) * vn w ≤ vn (N *ᵥ v) := by
    rcases eq_or_lt_of_le hvw with h0 | hpos
    · rw [← h0]; simp [hvN]
    · have : (1 - ρ) * vn w * vn w ≤ vn (N *ᵥ v) * vn w := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  rw [hS_eq, le_div_iff₀ h1ρ]
  have : w ⬝ᵥ (N *ᵥ v) * (1 - ρ) ≤ vn w * vn (N *ᵥ v) * (1 - ρ) :=
    mul_le_mul_of_nonneg_right hd h1ρ.le
  nlinarith

lemma Nv_bound {n : ℕ} (hn : 1 ≤ n) (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hlam : 0 < specNorm (G + Gᵀ))
    (hd : (ones n ⬝ᵥ ((G + Gᵀ) *ᵥ ones n)) / n ≤ specNorm (G + Gᵀ)) :
    vn (((ρ / specNorm (G + Gᵀ)) • (G - Gᵀ)) *ᵥ
      ((1 - (ρ / specNorm (G + Gᵀ)) • (G + Gᵀ))⁻¹ *ᵥ ones n)) ≤
    ρ / (specNorm (G + Gᵀ) * (1 - ρ) ^ 2) *
      (vn (G *ᵥ ones n - Gᵀ *ᵥ ones n) +
        vn ((G + Gᵀ) *ᵥ ones n - ((ones n ⬝ᵥ ((G + Gᵀ) *ᵥ ones n)) / n) • ones n)) := by
  set lam := specNorm (G + Gᵀ) with hlamdef
  set A := G + Gᵀ with hAdef
  set S : Matrix (Fin n) (Fin n) ℝ := 1 - (ρ / lam) • A with hSdef
  set N : Matrix (Fin n) (Fin n) ℝ := (ρ / lam) • (G - Gᵀ) with hNdef
  have h1ρ : 0 < 1 - ρ := by linarith
  have hAnn : ∀ i j, 0 ≤ A i j := by
    intro i j; rw [hAdef]; simp only [Matrix.add_apply, Matrix.transpose_apply]
    exact add_nonneg (hG i j) (hG j i)
  have hScoer : ∀ x, (1 - ρ) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x) := by
    intro x
    rw [hSdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul]
    have hq := quad_le_norm A x
    have : ρ / lam * (x ⬝ᵥ (A *ᵥ x)) ≤ ρ * (x ⬝ᵥ x) := by
      have h2 : ρ / lam * (x ⬝ᵥ (A *ᵥ x)) ≤ ρ / lam * (lam * (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      have h3 : ρ / lam * (lam * (x ⬝ᵥ x)) = ρ * (x ⬝ᵥ x) := by field_simp
      linarith
    linarith
  have hSinv := coercive_inv S (1 - ρ) h1ρ hScoer
  set v := S⁻¹ *ᵥ ones n with hvdef
  have hSv : S *ᵥ v = ones n := by rw [hvdef, Matrix.mulVec_mulVec, hSinv, Matrix.one_mulVec]
  set d := A *ᵥ ones n with hddef
  set db := (ones n ⬝ᵥ d) / n with hdbdef
  have hdb0 : 0 ≤ db := by
    rw [hdbdef]; apply div_nonneg _ (by positivity)
    unfold dotProduct; apply Finset.sum_nonneg; intro i _
    simp only [hddef, ones, one_mul, mulVec, dotProduct, mul_one]
    exact Finset.sum_nonneg (fun j _ => hAnn i j)
  set t := ρ * db / lam with htdef
  have ht0 : 0 ≤ t := by positivity
  have htρ : t ≤ ρ := by
    rw [htdef, div_le_iff₀ hlam]; nlinarith
  have h1t : 0 < 1 - t := by linarith
  set β := 1 / (1 - t) with hβdef
  have hβ0 : 0 < β := by positivity
  have hβle : β ≤ 1 / (1 - ρ) := by
    rw [hβdef]; exact one_div_le_one_div_of_le h1ρ (by linarith)
  set r := v - β • ones n with hrdef
  have hSr : S *ᵥ r = (β * ρ / lam) • (d - db • ones n) := by
    rw [hrdef, Matrix.mulVec_sub, hSv, Matrix.mulVec_smul, hSdef, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.smul_mulVec]
    have hb : β * (1 - t) = 1 := by rw [hβdef]; field_simp
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ones]
    rw [← hddef]
    have : β = 1 + β * t := by linarith
    rw [htdef] at this
    have hl : lam ≠ 0 := hlam.ne'
    field_simp
    rw [htdef] at hb
    field_simp at hb
    nlinarith [hb]
  have hvSr : vn (S *ᵥ r) = β * ρ / lam * vn (d - db • ones n) := by
    rw [hSr, vn_smul, abs_of_nonneg (by positivity)]
  have hrb : (1 - ρ) * vn r ≤ vn (S *ᵥ r) := by
    have hc := hScoer r
    have hd2 := dot_le r (S *ᵥ r)
    have hrr := vn_sq r
    have hvr := vn_nonneg r
    have hvS := vn_nonneg (S *ᵥ r)
    rcases eq_or_lt_of_le hvr with h0 | hpos
    · rw [← h0]; simp [hvS]
    · have : (1 - ρ) * vn r * vn r ≤ vn (S *ᵥ r) * vn r := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  have hvdec : v = r + β • ones n := by rw [hrdef]; abel
  have hNv : N *ᵥ v = β • (N *ᵥ ones n) + N *ᵥ r := by
    rw [hvdec, Matrix.mulVec_add, Matrix.mulVec_smul]; abel
  have hN1 : vn (N *ᵥ ones n) = ρ / lam * vn (G *ᵥ ones n - Gᵀ *ᵥ ones n) := by
    rw [hNdef, Matrix.smul_mulVec, vn_smul, abs_of_nonneg (by positivity), Matrix.sub_mulVec]
  have hNr : vn (N *ᵥ r) ≤ ρ * vn r := by
    rw [hNdef, Matrix.smul_mulVec, vn_smul, abs_of_nonneg (by positivity)]
    have hent : ∀ i, |((G - Gᵀ) *ᵥ r) i| ≤ (A *ᵥ (fun j => |r j|)) i := by
      intro i
      simp only [mulVec, dotProduct, Matrix.sub_apply, Matrix.transpose_apply, hAdef,
        Matrix.add_apply]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      apply Finset.sum_le_sum; intro j _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [abs_le]; constructor <;> linarith [hG i j, hG j i]
    have h1 := vn_le_of_abs hent
    have h2 := vn_mulVec A (fun j => |r j|)
    rw [vn_abs] at h2
    have h3 : vn ((G - Gᵀ) *ᵥ r) ≤ lam * vn r := le_trans h1 h2
    calc ρ / lam * vn ((G - Gᵀ) *ᵥ r) ≤ ρ / lam * (lam * vn r) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ρ * vn r := by field_simp
  -- combine
  set X := vn (G *ᵥ ones n - Gᵀ *ᵥ ones n)
  set Y := vn (d - db • ones n)
  have hX : 0 ≤ X := vn_nonneg _
  have hY : 0 ≤ Y := vn_nonneg _
  have hr2 : vn r ≤ β * ρ / lam * Y / (1 - ρ) := by
    rw [le_div_iff₀ h1ρ]; linarith [hvSr ▸ hrb]
  have step : vn (N *ᵥ v) ≤ β * (ρ / lam * X) + ρ * (β * ρ / lam * Y / (1 - ρ)) := by
    rw [hNv]
    refine le_trans (vn_add_le _ _) ?_
    rw [vn_smul, abs_of_pos hβ0, hN1]
    have := mul_le_mul_of_nonneg_left hr2 hρ0.le
    linarith
  refine le_trans step ?_
  -- β ≤ 1/(1-ρ), ρ ≤ 1
  have hlam' : 0 < ρ / lam := by positivity
  have hq1 : β * (ρ / lam * X) ≤ ρ / (lam * (1 - ρ) ^ 2) * X := by
    have e : ρ / (lam * (1 - ρ) ^ 2) = (1 / (1 - ρ) ^ 2) * (ρ / lam) := by field_simp
    rw [e]
    have hb2 : β ≤ 1 / (1 - ρ) ^ 2 := by
      refine le_trans hβle ?_
      rw [div_le_div_iff₀ h1ρ (by positivity)]; nlinarith
    have := mul_le_mul_of_nonneg_right hb2 (mul_nonneg hlam'.le hX)
    linarith
  have hq2 : ρ * (β * ρ / lam * Y / (1 - ρ)) ≤ ρ / (lam * (1 - ρ) ^ 2) * Y := by
    have e1 : ρ * (β * ρ / lam * Y / (1 - ρ)) = (ρ * β) * (ρ / lam * Y) / (1 - ρ) := by ring
    have e2 : ρ / (lam * (1 - ρ) ^ 2) * Y = (1 / (1 - ρ)) * (ρ / lam * Y) / (1 - ρ) := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ h1ρ.le
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg hlam'.le hY)
    have : ρ * β ≤ β := by nlinarith
    linarith
  linarith

lemma wsum_prod {α : Type*} [DecidableEq α] (T : Finset α) (q : ℝ) (a b : α → ℝ) :
    ∑ S ∈ T.powerset, q ^ S.card * (1 - q) ^ (T.card - S.card) *
      ((∏ e ∈ S, a e) * ∏ e ∈ T \ S, b e) = ∏ e ∈ T, (q * a e + (1 - q) * b e) := by
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S hS
  have hsub := Finset.mem_powerset.1 hS
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset hsub]
  ring

lemma erExpect_congr {n : ℕ} {q : ℝ} {F H : Matrix (Fin n) (Fin n) ℝ → ℝ}
    (h : ∀ S ∈ (Finset.univ : Finset (Fin n)).offDiag.powerset, F (adjOf S) = H (adjOf S)) :
    erExpect n q F = erExpect n q H := by
  unfold erExpect
  apply Finset.sum_congr rfl
  intro S hS; rw [h S hS]

lemma erExpect_sum {n : ℕ} {q : ℝ} {ι : Type*} (s : Finset ι)
    (F : ι → Matrix (Fin n) (Fin n) ℝ → ℝ) :
    erExpect n q (fun G => ∑ i ∈ s, F i G) = ∑ i ∈ s, erExpect n q (F i) := by
  unfold erExpect
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro S _
  rw [Finset.mul_sum]

lemma erExpect_one {n : ℕ} (q : ℝ) : erExpect n q (fun _ => 1) = 1 := by
  unfold erExpect
  simp only [mul_one]
  rw [Finset.sum_pow_mul_eq_add_pow]; simp

lemma erExpect_pair {n : ℕ} (q : ℝ) (e f : Fin n × Fin n)
    (he : e ∈ (Finset.univ : Finset (Fin n)).offDiag)
    (hf : f ∈ (Finset.univ : Finset (Fin n)).offDiag) :
    erExpect n q (fun G => G e.1 e.2 * G f.1 f.2) = if e = f then q else q ^ 2 := by
  classical
  set T := (Finset.univ : Finset (Fin n)).offDiag
  have hc : ∀ S ∈ T.powerset, (fun G : Matrix (Fin n) (Fin n) ℝ => G e.1 e.2 * G f.1 f.2)
      (adjOf S) = (∏ g ∈ S, (1:ℝ)) * ∏ g ∈ T \ S, (if g = e ∨ g = f then (0:ℝ) else 1) := by
    intro S hS
    have hsub := Finset.mem_powerset.1 hS
    simp only [adjOf, Prod.mk.eta, Finset.prod_const_one, one_mul]
    by_cases h1 : e ∈ S
    · by_cases h2 : f ∈ S
      · rw [if_pos h1, if_pos h2, one_mul]
        symm; apply Finset.prod_eq_one; intro g hg
        rw [Finset.mem_sdiff] at hg
        rw [if_neg]; rintro (rfl | rfl)
        · exact hg.2 h1
        · exact hg.2 h2
      · rw [if_pos h1, if_neg h2, mul_zero]
        symm; apply Finset.prod_eq_zero (i := f) (Finset.mem_sdiff.2 ⟨hf, h2⟩)
        simp
    · rw [if_neg h1, zero_mul]
      symm; apply Finset.prod_eq_zero (i := e) (Finset.mem_sdiff.2 ⟨he, h1⟩)
      simp
  have h1 : erExpect n q (fun G => G e.1 e.2 * G f.1 f.2) =
      ∏ g ∈ T, (q * 1 + (1 - q) * (if g = e ∨ g = f then (0:ℝ) else 1)) := by
    rw [← wsum_prod]
    unfold erExpect
    apply Finset.sum_congr rfl
    intro S hS; rw [hc S hS]
  rw [h1]
  by_cases hef : e = f
  · subst hef
    rw [if_pos rfl, ← Finset.mul_prod_erase T _ he]
    simp only [true_or, if_true, mul_zero, add_zero, mul_one]
    rw [Finset.prod_eq_one]; · ring
    intro g hg
    have : g ≠ e := Finset.ne_of_mem_erase hg
    simp [this]
  · rw [if_neg hef, ← Finset.mul_prod_erase T _ he,
      ← Finset.mul_prod_erase (T.erase e) _ (Finset.mem_erase.2 ⟨Ne.symm hef, hf⟩)]
    simp only [true_or, or_true, if_true, mul_zero, add_zero, mul_one]
    rw [Finset.prod_eq_one]; · ring
    intro g hg
    have h1 : g ≠ f := Finset.ne_of_mem_erase hg
    have h2 : g ≠ e := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hg)
    simp [h1, h2]

lemma erExpect_entry {n : ℕ} (q : ℝ) (e : Fin n × Fin n)
    (he : e ∈ (Finset.univ : Finset (Fin n)).offDiag) :
    erExpect n q (fun G => G e.1 e.2) = q := by
  have h := erExpect_pair q e e he he
  rw [if_pos rfl] at h
  have hc : erExpect n q (fun G => G e.1 e.2) = erExpect n q (fun G => G e.1 e.2 * G e.1 e.2) := by
    apply erExpect_congr
    intro S _
    simp only [adjOf]; split_ifs <;> norm_num
  rw [hc, h]

/-- second moment of a linear statistic of the arcs -/
lemma erExpect_lin_sq {n : ℕ} (q : ℝ) (c : Fin n × Fin n → ℝ) (μ : ℝ) :
    erExpect n q (fun G => (∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag,
        c e * G e.1 e.2 - μ) ^ 2) =
      q * (1 - q) * ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, c e ^ 2 +
        (q * ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, c e - μ) ^ 2 := by
  classical
  set T := (Finset.univ : Finset (Fin n)).offDiag
  have hexp : (fun G : Matrix (Fin n) (Fin n) ℝ => (∑ e ∈ T, c e * G e.1 e.2 - μ) ^ 2) =
      fun G => ∑ e ∈ T, ∑ f ∈ T, (c e * c f) * (G e.1 e.2 * G f.1 f.2) +
        (-(2 * μ) * ∑ e ∈ T, c e * G e.1 e.2 + μ ^ 2 * 1) := by
    funext G
    have : (∑ e ∈ T, c e * G e.1 e.2) ^ 2 =
        ∑ e ∈ T, ∑ f ∈ T, (c e * c f) * (G e.1 e.2 * G f.1 f.2) := by
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro e _; apply Finset.sum_congr rfl; intro f _; ring
    rw [sub_sq, this]; ring
  rw [hexp, erExpect_add, erExpect_add, erExpect_const_mul, erExpect_const_mul, erExpect_one,
    erExpect_sum]
  rw [erExpect_sum]
  simp_rw [erExpect_sum, erExpect_const_mul]
  have h2 : ∀ e ∈ T, ∑ f ∈ T, c e * c f * erExpect n q (fun G => G e.1 e.2 * G f.1 f.2) =
      c e * c e * (q - q ^ 2) + c e * (q ^ 2 * ∑ f ∈ T, c f) := by
    intro e he
    rw [Finset.sum_congr rfl (g := fun f => c e * c f * (if e = f then q else q ^ 2))
      (fun f hf => by rw [erExpect_pair q e f he hf])]
    have : ∀ f, c e * c f * (if e = f then q else q ^ 2) =
        (if e = f then c e * c f * (q - q ^ 2) else 0) + c e * c f * q ^ 2 := by
      intro f; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun f _ => this f), Finset.sum_add_distrib, Finset.sum_ite_eq T e,
      if_pos he, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  have h3 : ∑ x ∈ T, c x * erExpect n q (fun G => G x.1 x.2) = q * ∑ e ∈ T, c e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x hx; rw [erExpect_entry q x hx]; ring
  have h4 : ∑ e ∈ T, c e * c e * (q - q ^ 2) = (q - q ^ 2) * ∑ e ∈ T, c e ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  have h5 : ∑ e ∈ T, c e * (q ^ 2 * ∑ f ∈ T, c f) = q ^ 2 * (∑ e ∈ T, c e) ^ 2 := by
    rw [← Finset.sum_mul]; ring
  rw [h3, h4, h5]
  ring

lemma sum_offDiag_conv {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, G i i = 0)
    (h : Fin n × Fin n → ℝ) :
    ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, h e * G e.1 e.2 =
      ∑ i, ∑ j, h (i, j) * G i j := by
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_subset (Finset.subset_univ _)
  intro e _ he
  simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, not_not] at he
  have : G e.1 e.2 = 0 := by rw [he]; exact hdiag _
  rw [this, mul_zero]

lemma count_fst {n : ℕ} (i : Fin n) :
    ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, (if e.1 = i then (1:ℝ) else 0) = n - 1 := by
  rw [Finset.sum_boole]
  have : ((Finset.univ : Finset (Fin n)).offDiag.filter (fun e => e.1 = i)).card =
      (Finset.univ.erase i).card := by
    apply Finset.card_nbij' (fun e => e.2) (fun j => (i, j))
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at he
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and]
      rw [← he.2]; exact Ne.symm he.1
    · intro j hj
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and] at hj
      simp only [Finset.coe_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq]
      exact ⟨Ne.symm hj, trivial⟩
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at he
      ext <;> simp [he.2]
    · intro j _; rfl
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin]
  rcases n with _ | n
  · exact absurd i.2 (by simp)
  · push_cast; ring

lemma count_snd {n : ℕ} (i : Fin n) :
    ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, (if e.2 = i then (1:ℝ) else 0) = n - 1 := by
  rw [Finset.sum_boole]
  have : ((Finset.univ : Finset (Fin n)).offDiag.filter (fun e => e.2 = i)).card =
      (Finset.univ.erase i).card := by
    apply Finset.card_nbij' (fun e => e.1) (fun j => (j, i))
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at he
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and]
      rw [← he.2]; exact he.1
    · intro j hj
      simp only [Finset.coe_erase, Finset.coe_univ, Set.mem_sdiff, Set.mem_univ,
        Set.mem_singleton_iff, true_and] at hj
      simp only [Finset.coe_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq]
      exact ⟨hj, trivial⟩
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_offDiag, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at he
      ext <;> simp [he.2]
    · intro j _; rfl
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin]
  rcases n with _ | n
  · exact absurd i.2 (by simp)
  · push_cast; ring

lemma sum_sq_dev_le {n : ℕ} (hn : 1 ≤ n) (x : Fin n → ℝ) (μ : ℝ) :
    ∑ i, (x i - (∑ j, x j) / n) ^ 2 ≤ ∑ i, (x i - μ) ^ 2 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  set s := ∑ j, x j
  have e1 : ∑ i, (x i - μ) ^ 2 = ∑ i, x i ^ 2 - 2 * μ * s + n * μ ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  have e2 : ∑ i, (x i - s / n) ^ 2 = ∑ i, x i ^ 2 - 2 * (s / n) * s + n * (s / n) ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  rw [e1, e2]
  have : 0 ≤ (s - n * μ) ^ 2 / n := by positivity
  have h3 : (s - n * μ) ^ 2 / n = (-(2 * μ * s) + n * μ ^ 2) - (-(2 * (s / n) * s) + n * (s / n) ^ 2) := by
    field_simp; ring
  linarith

lemma coef_sq_eq {n : ℕ} (i : Fin n) (e : Fin n × Fin n)
    (he : e ∈ (Finset.univ : Finset (Fin n)).offDiag) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ((if e.1 = i then (1:ℝ) else 0) + s * (if e.2 = i then (1:ℝ) else 0)) ^ 2 =
      (if e.1 = i then (1:ℝ) else 0) + (if e.2 = i then (1:ℝ) else 0) := by
  simp only [Finset.mem_offDiag, Finset.mem_univ, true_and] at he
  by_cases h1 : e.1 = i
  · have h2 : e.2 ≠ i := by rw [← h1]; exact Ne.symm he
    simp [h1, h2]
  · by_cases h2 : e.2 = i
    · simp only [h1, h2, if_false, if_true]
      rcases hs with rfl | rfl <;> norm_num
    · simp [h1, h2]

lemma deg_conv {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, G i i = 0) (i : Fin n)
    (s : ℝ) :
    ∑ j, (G i j + s * G j i) = ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag,
      ((if e.1 = i then (1:ℝ) else 0) + s * (if e.2 = i then (1:ℝ) else 0)) * G e.1 e.2 := by
  rw [sum_offDiag_conv G hdiag]
  have h1 : ∑ x, ∑ y, (if x = i then (1:ℝ) else 0) * G x y = ∑ y, G i y := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have h2 : ∑ x, ∑ y, (s * if y = i then (1:ℝ) else 0) * G x y = ∑ x, s * G x i := by
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  simp only [add_mul, Finset.sum_add_distrib]
  rw [h1, h2]

lemma E_deg {n : ℕ} (q : ℝ) (i : Fin n) (s : ℝ) (hs : s = 1 ∨ s = -1) (μ : ℝ) :
    erExpect n q (fun G => (∑ j, (G i j + s * G j i) - μ) ^ 2) =
      q * (1 - q) * (2 * ((n:ℝ) - 1)) + (q * ((n - 1) + s * (n - 1)) - μ) ^ 2 := by
  set T := (Finset.univ : Finset (Fin n)).offDiag
  set c : Fin n × Fin n → ℝ := fun e =>
    (if e.1 = i then (1:ℝ) else 0) + s * (if e.2 = i then (1:ℝ) else 0) with hc
  have hcongr : erExpect n q (fun G => (∑ j, (G i j + s * G j i) - μ) ^ 2) =
      erExpect n q (fun G => (∑ e ∈ T, c e * G e.1 e.2 - μ) ^ 2) := by
    apply erExpect_congr
    intro S hS
    have hdiag := adjOf_diag S (Finset.mem_powerset.1 hS)
    rw [deg_conv (adjOf S) hdiag i s]
  rw [hcongr, erExpect_lin_sq]
  have h1 : ∑ e ∈ T, c e ^ 2 = 2 * ((n:ℝ) - 1) := by
    rw [Finset.sum_congr rfl (fun e he => coef_sq_eq i e he s hs), Finset.sum_add_distrib,
      count_fst, count_snd]; ring
  have h2 : ∑ e ∈ T, c e = (n - 1) + s * (n - 1) := by
    simp only [hc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, count_fst, count_snd]
  rw [h1, h2]

lemma E_cnt {n : ℕ} (q : ℝ) :
    erExpect n q (fun G => (∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, G e.1 e.2 -
        ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * q) ^ 2) =
      q * (1 - q) * ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) := by
  have h := erExpect_lin_sq (n := n) q (fun _ => 1)
    (((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * q)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]; ring

lemma ident_X {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    vn (G *ᵥ ones n - Gᵀ *ᵥ ones n) ^ 2 = ∑ i, (∑ j, (G i j + (-1) * G j i) - 0) ^ 2 := by
  rw [vn_sq]
  simp only [dotProduct, mulVec, ones, mul_one, Pi.sub_apply, Matrix.transpose_apply, sub_zero]
  apply Finset.sum_congr rfl; intro i _
  rw [← sq]; congr 1
  rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring

lemma ident_deg {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ((G + Gᵀ) *ᵥ ones n) i = ∑ j, (G i j + 1 * G j i) := by
  simp [mulVec, dotProduct, ones]

lemma ident_Y {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (db : ℝ) :
    vn ((G + Gᵀ) *ᵥ ones n - db • ones n) ^ 2 = ∑ i, (∑ j, (G i j + 1 * G j i) - db) ^ 2 := by
  rw [vn_sq]
  unfold dotProduct
  apply Finset.sum_congr rfl; intro i _
  rw [Pi.sub_apply, Pi.smul_apply, ident_deg, smul_eq_mul]
  simp only [ones, mul_one]; ring

lemma ident_tot {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hdiag : ∀ i, G i i = 0) :
    ones n ⬝ᵥ ((G + Gᵀ) *ᵥ ones n) = ∑ i, ∑ j, (G i j + 1 * G j i) ∧
    ones n ⬝ᵥ ((G + Gᵀ) *ᵥ ones n) =
      2 * ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, G e.1 e.2 := by
  have h1 : ones n ⬝ᵥ ((G + Gᵀ) *ᵥ ones n) = ∑ i, ∑ j, (G i j + 1 * G j i) := by
    unfold dotProduct
    apply Finset.sum_congr rfl; intro i _
    rw [ident_deg]; simp [ones]
  refine ⟨h1, ?_⟩
  rw [h1]
  have h2 := sum_offDiag_conv G hdiag (fun _ => 1)
  simp only [one_mul] at h2
  rw [h2]
  simp only [one_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => G j i)]
  ring

lemma profit0_nonneg (a c ρ : ℝ) (hca : c < a) (n : ℕ) :
    0 ≤ profit a c ρ (0 : Matrix (Fin n) (Fin n) ℝ) (uniformPrice n a c) := by
  simp only [profit, xStar, uniformPrice, Matrix.transpose_zero, add_zero, smul_zero,
    sub_zero, inv_one, Matrix.one_mulVec]
  unfold dotProduct
  apply Finset.sum_nonneg; intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ones, mul_one]
  have h1 : 0 ≤ (a + c) / 2 - c := by linarith
  have h2 : 0 ≤ a - (a + c) / 2 := by linarith
  have : 0 ≤ 1 / 2 * (a - (a + c) / 2) := by positivity
  exact mul_nonneg h1 this

lemma regret_le_Rmax (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {n : ℕ} (S : Finset (Fin n × Fin n)) :
    regret a c ρ (adjOf S) ≤ 1 / 2 * ((a - c) / 2) ^ 2 * n / (1 - ρ) := by
  have h14 := (eq_14 a c ρ ha hca hρ0 hρ1 (adjOf S) (adjOf_nonneg S)).2
  have hp : 0 ≤ profit a c ρ (adjOf S) (uniformPrice n a c) := by
    rcases S.eq_empty_or_nonempty with h0 | hne
    · subst h0; rw [adjOf_empty]; exact profit0_nonneg a c ρ hca n
    · have h4 := eq_4 a c ρ ha hca hρ0 hρ1 (adjOf S) (adjOf_nonneg S) (adjOf_ne_zero S hne)
      rw [h4.2.1]
      have hs : 0 ≤ ones n ⬝ᵥ ((1 - (2 * ρ / specNorm (adjOf S + (adjOf S)ᵀ)) • adjOf S)⁻¹ *ᵥ
          ones n) := by
        apply h4.2.2.nonneg
        intro k
        have : 0 ≤ specNorm (adjOf S + (adjOf S)ᵀ) := norm_nonneg _
        exact mul_nonneg (pow_nonneg (by positivity) _) (walks_nonneg _ (adjOf_nonneg S) k)
      positivity
  unfold regret
  have : 1 / 2 * ((a - c) / 2) ^ 2 * ((n:ℝ) / (1 - ρ)) = 1 / 2 * ((a - c) / 2) ^ 2 * n / (1 - ρ) := by
    ring
  linarith

lemma final_arith (C1 ρ lam L X Y X2 Y2 Z D : ℝ) (hC1 : 0 < C1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlam : 0 < lam) (hL : 0 < L) (hLl : L ≤ lam) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hD : D ≤ Z ^ 2 / (1 - ρ)) (hZb : Z ≤ ρ / (lam * (1 - ρ) ^ 2) * (X + Y))
    (hX2 : X ^ 2 = X2) (hY2 : Y ^ 2 ≤ Y2) :
    C1 * D ≤ (2 * C1 * ρ ^ 2 / (1 - ρ) ^ 5) / L ^ 2 * (X2 + Y2) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hX2n : 0 ≤ X2 := by rw [← hX2]; positivity
  have hY2n : 0 ≤ Y2 := le_trans (sq_nonneg Y) hY2
  have hZsq : Z ^ 2 ≤ (ρ / (lam * (1 - ρ) ^ 2)) ^ 2 * (2 * (X2 + Y2)) := by
    have h1 : Z ^ 2 ≤ (ρ / (lam * (1 - ρ) ^ 2) * (X + Y)) ^ 2 := pow_le_pow_left₀ hZ hZb 2
    have h2 : (X + Y) ^ 2 ≤ 2 * (X2 + Y2) := by
      have := sq_nonneg (X - Y)
      nlinarith
    rw [mul_pow] at h1
    have h3 : 0 ≤ (ρ / (lam * (1 - ρ) ^ 2)) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_left h2 h3
    linarith
  have h1 : C1 * D ≤ C1 * (Z ^ 2 / (1 - ρ)) := mul_le_mul_of_nonneg_left hD hC1.le
  have h2 : C1 * (Z ^ 2 / (1 - ρ)) ≤
      C1 * ((ρ / (lam * (1 - ρ) ^ 2)) ^ 2 * (2 * (X2 + Y2)) / (1 - ρ)) := by
    apply mul_le_mul_of_nonneg_left _ hC1.le
    exact div_le_div_of_nonneg_right hZsq h1ρ.le
  have h3 : C1 * ((ρ / (lam * (1 - ρ) ^ 2)) ^ 2 * (2 * (X2 + Y2)) / (1 - ρ)) =
      (2 * C1 * ρ ^ 2 / (1 - ρ) ^ 5) / lam ^ 2 * (X2 + Y2) := by
    field_simp
  have hmono : (2 * C1 * ρ ^ 2 / (1 - ρ) ^ 5) / lam ^ 2 * (X2 + Y2) ≤
      (2 * C1 * ρ ^ 2 / (1 - ρ) ^ 5) / L ^ 2 * (X2 + Y2) := by
    apply mul_le_mul_of_nonneg_right _ (add_nonneg hX2n hY2n)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hL.le hLl 2
  linarith

lemma pointwise_dense (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {n : ℕ} (hn : 2 ≤ n) (q : ℝ) (hq : 0 < q)
    (S : Finset (Fin n × Fin n)) (hS : S ⊆ (Finset.univ : Finset (Fin n)).offDiag) :
    regret a c ρ (adjOf S) ≤
      (2 * (1 / 2 * ((a - c) / 2) ^ 2) * ρ ^ 2 / (1 - ρ) ^ 5) / (((n:ℝ) - 1) * q) ^ 2 *
        ((∑ i, (∑ j, (adjOf S i j + (-1) * adjOf S j i) - 0) ^ 2) +
         (∑ i, (∑ j, (adjOf S i j + 1 * adjOf S j i) - 2 * ((n:ℝ) - 1) * q) ^ 2)) +
      (1 / 2 * ((a - c) / 2) ^ 2 * n / (1 - ρ)) /
          (((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * q / 2) ^ 2 *
        (∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, adjOf S e.1 e.2 -
          ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) * q) ^ 2 := by
  set G := adjOf S with hGdef
  set C1 : ℝ := 1 / 2 * ((a - c) / 2) ^ 2 with hC1
  have h1ρ : 0 < 1 - ρ := by linarith
  have hC1p : 0 < C1 := by
    have : 0 < a - c := by linarith
    positivity
  set m : ℝ := ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) with hm
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hmval : m = n * ((n:ℝ) - 1) := by
    rw [hm, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.cast_sub, Nat.cast_mul]
    · ring
    · exact Nat.le_mul_self n
  have hL : 0 < ((n:ℝ) - 1) * q := mul_pos (by linarith) hq
  have hmq : 0 < m * q := by rw [hmval]; exact mul_pos (mul_pos (by linarith) (by linarith)) hq
  set Cnt := ∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, G e.1 e.2 with hCnt
  set X2 := ∑ i, (∑ j, (G i j + (-1) * G j i) - 0) ^ 2 with hX2
  set Y2 := ∑ i, (∑ j, (G i j + 1 * G j i) - 2 * ((n:ℝ) - 1) * q) ^ 2 with hY2
  have hX2n : 0 ≤ X2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hY2n : 0 ≤ Y2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hK0 : 0 ≤ (2 * C1 * ρ ^ 2 / (1 - ρ) ^ 5) / (((n:ℝ) - 1) * q) ^ 2 * (X2 + Y2) := by
    positivity
  have hRm := regret_le_Rmax a c ρ ha hca hρ0 hρ1 S
  have hRmax0 : 0 ≤ C1 * n / (1 - ρ) := by positivity
  have hsec0 : 0 ≤ (C1 * n / (1 - ρ)) / (m * q / 2) ^ 2 * (Cnt - m * q) ^ 2 := by positivity
  by_cases hc : Cnt < m * q / 2
  · -- bad event
    have : C1 * n / (1 - ρ) ≤ (C1 * n / (1 - ρ)) / (m * q / 2) ^ 2 * (Cnt - m * q) ^ 2 := by
      have hpos : 0 < (m * q / 2) ^ 2 := by positivity
      have hsq : (m * q / 2) ^ 2 ≤ (Cnt - m * q) ^ 2 := by
        have h1 : m * q / 2 ≤ m * q - Cnt := by linarith
        have h2 : 0 ≤ m * q / 2 := by positivity
        nlinarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      exact mul_le_mul_of_nonneg_left hsq hRmax0
    linarith
  · push Not at hc
    have hdiag := adjOf_diag S hS
    have hCntpos : 0 < Cnt := by linarith [half_pos hmq]
    have hne : S.Nonempty := by
      rcases S.eq_empty_or_nonempty with h0 | h
      · exfalso
        have : Cnt = 0 := by
          rw [hCnt, hGdef, h0, adjOf_empty]; simp
        linarith
      · exact h
    have hG0 := adjOf_ne_zero S hne
    obtain ⟨htot1, htot2⟩ := ident_tot G hdiag
    set lam := specNorm (G + Gᵀ) with hlam
    have h12 := eq_12_rayleigh G (adjOf_nonneg S)
    have hw1 : walks (G + Gᵀ) 1 = ones n ⬝ᵥ ((G + Gᵀ) *ᵥ ones n) := by
      unfold walks; rw [pow_one]
    have h11 : ones n ⬝ᵥ ones n = n := by simp [ones, dotProduct]
    rw [hw1, h11] at h12
    have hlamL : ((n:ℝ) - 1) * q ≤ lam := by
      refine le_trans ?_ h12
      rw [htot2, le_div_iff₀ (by linarith)]
      have : m * q = n * (((n:ℝ) - 1) * q) := by rw [hmval]; ring
      nlinarith
    have hlampos : 0 < lam := lt_of_lt_of_le hL hlamL
    have hnb := Nv_bound (by omega : 1 ≤ n) G (adjOf_nonneg S) ρ hρ0 hρ1 hlampos h12
    have hdb := det_bound G ρ hρ0 hρ1 hlampos
    have h3 := eq_3 a c ρ ha hca hρ0 hρ1 G (adjOf_nonneg S) hG0
    have h4 := eq_4 a c ρ ha hca hρ0 hρ1 G (adjOf_nonneg S) hG0
    have hreg : regret a c ρ G = C1 * (ones n ⬝ᵥ ((1 - (ρ / lam) • (G + Gᵀ))⁻¹ *ᵥ ones n) -
        ones n ⬝ᵥ ((1 - (2 * ρ / lam) • G)⁻¹ *ᵥ ones n)) := by
      unfold regret optProfit
      rw [h3.1.csSup_eq, h4.2.1]; ring
    have hY : vn ((G + Gᵀ) *ᵥ ones n - ((ones n ⬝ᵥ ((G + Gᵀ) *ᵥ ones n)) / n) • ones n) ^ 2
        ≤ Y2 := by
      rw [ident_Y, htot1]
      exact sum_sq_dev_le (by omega) (fun i => ∑ j, (G i j + 1 * G j i)) _
    have hfin := final_arith C1 ρ lam (((n:ℝ) - 1) * q) _ _ X2 Y2 _ _ hC1p hρ0 hρ1 hlampos hL hlamL
      (vn_nonneg _) (vn_nonneg _) (vn_nonneg _) hdb hnb (ident_X G) hY
    rw [hreg]
    linarith

lemma dense_arith (K0 C1 ρ W ε n q L m E : ℝ) (hK0p : 0 < K0) (hC1p : 0 < C1) (h1ρ : 0 < 1 - ρ)
    (hε : 0 < ε) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hn1 : 1 ≤ n) (hLpos : 0 < L) (hmqpos : 0 < m * q)
    (hW : W = 8 * K0 + 8 * C1 / (1 - ρ)) (hLM : W / ε / 2 ≤ L) (hmq : m * q = n * L)
    (hpt : E ≤ K0 / L ^ 2 * (n * (2 * L * (1 - q)) + n * (2 * L * (1 - q))) +
      C1 * n / (1 - ρ) / (m * q / 2) ^ 2 * (q * (1 - q) * m)) :
    E ≤ ε * n := by
  have hnpos : 0 < n := by linarith
  have hWp : 0 < W := by rw [hW]; positivity
  have hMp : 0 < W / ε := by positivity
  have h1q : 1 - q ≤ 1 := by linarith
  have h1q0 : 0 ≤ 1 - q := by linarith
  have t1 : K0 / L ^ 2 * (n * (2 * L * (1 - q)) + n * (2 * L * (1 - q))) ≤ 4 * K0 * n / L := by
    have : K0 / L ^ 2 * (n * (2 * L * (1 - q)) + n * (2 * L * (1 - q))) =
        4 * K0 * n / L * (1 - q) := by field_simp; ring
    rw [this]
    have : 0 ≤ 4 * K0 * n / L := by positivity
    nlinarith
  have t2 : C1 * n / (1 - ρ) / (m * q / 2) ^ 2 * (q * (1 - q) * m) ≤ 4 * C1 / ((1 - ρ) * L) := by
    have e : C1 * n / (1 - ρ) / (m * q / 2) ^ 2 * (q * (1 - q) * m) =
        4 * C1 / ((1 - ρ) * L) * (1 - q) := by
      have hm0 : m ≠ 0 := by
        intro h; rw [h, zero_mul] at hmqpos; exact lt_irrefl _ hmqpos
      have : q * (1 - q) * m = (m * q) * (1 - q) := by ring
      rw [this, hmq]
      field_simp
      ring
    rw [e]
    have : 0 ≤ 4 * C1 / ((1 - ρ) * L) := by positivity
    nlinarith
  have t3 : 4 * K0 * n / L ≤ 8 * K0 * n / (W / ε) := by
    rw [div_le_div_iff₀ hLpos hMp]
    have h0 : 0 ≤ 4 * K0 * n := by positivity
    have := mul_le_mul_of_nonneg_left (by linarith : W / ε ≤ 2 * L) h0
    linarith
  have t4 : 4 * C1 / ((1 - ρ) * L) ≤ 8 * C1 / (1 - ρ) * n / (W / ε) := by
    rw [div_le_div_iff₀ (by positivity) hMp]
    have : 8 * C1 / (1 - ρ) * n * ((1 - ρ) * L) = 8 * C1 * n * L := by field_simp
    rw [this]
    have : 4 * C1 * (W / ε) ≤ 8 * C1 * n * L := by
      have h0 : 0 ≤ 4 * C1 := by positivity
      have h1 := mul_le_mul_of_nonneg_left (by linarith : W / ε ≤ 2 * L) h0
      have h2 : 8 * C1 * L ≤ 8 * C1 * n * L := by
        have : 8 * C1 * L * 1 ≤ 8 * C1 * L * n :=
          mul_le_mul_of_nonneg_left hn1 (by positivity)
        linarith
      linarith
    linarith
  have t5 : 8 * K0 * n / (W / ε) + 8 * C1 / (1 - ρ) * n / (W / ε) = ε * n := by
    rw [hW]; field_simp
  linarith


end NetPriceDisc.Random.PDRAux

open NetPriceDisc.Random NetPriceDisc.Random.PDRAux in
theorem solution (a c ρ : ℝ) (ha : 0 < a) (hca : c < a) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ, 0 ≤ q → q ≤ 1 → M ≤ (n : ℝ) * q →
      erExpect n q (regret a c ρ) ≤ ε * n := by
  set C1 : ℝ := 1 / 2 * ((a - c) / 2) ^ 2 with hC1
  have h1ρ : 0 < 1 - ρ := by linarith
  have hC1p : 0 < C1 := by
    have : 0 < a - c := by linarith
    positivity
  set K0 : ℝ := 2 * C1 * ρ ^ 2 / (1 - ρ) ^ 5 with hK0
  have hK0p : 0 < K0 := by positivity
  set W : ℝ := 8 * K0 + 8 * C1 / (1 - ρ) with hW
  have hWp : 0 < W := by positivity
  refine ⟨W / ε, 2, ?_⟩
  intro n hn q hq0 hq1 hMq
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hMp : 0 < W / ε := by positivity
  have hnq : 0 < (n:ℝ) * q := lt_of_lt_of_le hMp hMq
  have hq : 0 < q := by
    rcases lt_or_eq_of_le hq0 with h | h
    · exact h
    · rw [← h, mul_zero] at hnq; exact absurd hnq (lt_irrefl _)
  set L : ℝ := ((n:ℝ) - 1) * q with hLdef
  have hL2 : (n:ℝ) * q / 2 ≤ L := by
    rw [hLdef]; nlinarith
  have hLM : W / ε / 2 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  set m : ℝ := ((Finset.univ : Finset (Fin n)).offDiag.card : ℝ) with hm
  have hmval : m = n * ((n:ℝ) - 1) := by
    rw [hm, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, Nat.cast_sub, Nat.cast_mul]
    · ring
    · exact Nat.le_mul_self n
  have hmq : m * q = n * L := by rw [hmval, hLdef]; ring
  have hmqpos : 0 < m * q := by rw [hmq]; positivity
  -- pointwise bound and linearity
  have hpt := erExpect_mono hq0 hq1 (F := regret a c ρ)
    (H := fun G => K0 / L ^ 2 *
        ((∑ i, (∑ j, (G i j + (-1) * G j i) - 0) ^ 2) +
         (∑ i, (∑ j, (G i j + 1 * G j i) - 2 * ((n:ℝ) - 1) * q) ^ 2)) +
      (C1 * n / (1 - ρ)) / (m * q / 2) ^ 2 *
        (∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, G e.1 e.2 - m * q) ^ 2)
    (fun S hS => pointwise_dense a c ρ ha hca hρ0 hρ1 (n := n) hn q hq S
      (Finset.mem_powerset.1 hS))
  rw [erExpect_add, erExpect_const_mul, erExpect_const_mul, erExpect_add, erExpect_sum,
    erExpect_sum] at hpt
  have hEc : erExpect n q (fun G : Matrix (Fin n) (Fin n) ℝ =>
      (∑ e ∈ (Finset.univ : Finset (Fin n)).offDiag, G e.1 e.2 - m * q) ^ 2) = q * (1 - q) * m :=
    E_cnt q
  rw [hEc] at hpt
  simp only [E_deg q _ (-1) (Or.inr rfl) 0, E_deg q _ 1 (Or.inl rfl) _,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hpt
  -- now hpt is an explicit numeric bound
  have hv1 : q * (1 - q) * (2 * ((n:ℝ) - 1)) + (q * (((n:ℝ) - 1) + -1 * ((n:ℝ) - 1)) - 0) ^ 2
      = 2 * L * (1 - q) := by rw [hLdef]; ring
  have hv2 : q * (1 - q) * (2 * ((n:ℝ) - 1)) + (q * (((n:ℝ) - 1) + 1 * ((n:ℝ) - 1)) -
      2 * ((n:ℝ) - 1) * q) ^ 2 = 2 * L * (1 - q) := by rw [hLdef]; ring
  rw [hv1, hv2] at hpt
  exact dense_arith K0 C1 ρ W ε (n:ℝ) q L m _ hK0p hC1p h1ρ hε hq0 hq1 (by linarith) hLpos hmqpos
    hW hLM hmq hpt

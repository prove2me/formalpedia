-- Prove2me | solution 1 for ModernConvex.PathFollowing.closeness_estimate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:30:37.786354+00:00
-- url     : https://prove2.me/submissions/87c87c2b-8744-4c51-8bf3-3ab49d42b975

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP
import Theorems.Thm_ModernConvex_PathFollowing_scaled_direction_bounds
import Theorems.Thm_ModernConvex_PathFollowing_updated_pair_feasible

-- ===== PFA =====

open Matrix
open scoped MatrixOrder

namespace X4PF
open ModernConvex.PathFollowing

variable {k : ℕ}

lemma frob_nonneg (A : Matrix (Fin k) (Fin k) ℝ) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

lemma frob_sq (A : Matrix (Fin k) (Fin k) ℝ) : frobNorm A ^ 2 = (Aᴴ * A).trace := by
  unfold frobNorm
  rw [Real.sq_sqrt (by positivity)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_trivial]
  rw [Finset.sum_comm]
  simp [sq]

noncomputable def toE (A : Matrix (Fin k) (Fin k) ℝ) : EuclideanSpace ℝ (Fin k × Fin k) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

lemma frob_eq (A : Matrix (Fin k) (Fin k) ℝ) : frobNorm A = ‖toE A‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold frobNorm toE
  congr 1
  rw [Fintype.sum_prod_type]
  simp

lemma frob_sub_le (A B : Matrix (Fin k) (Fin k) ℝ) :
    frobNorm (A - B) ≤ frobNorm A + frobNorm B := by
  rw [frob_eq, frob_eq, frob_eq]
  have : toE (A - B) = toE A - toE B := by ext p; simp [toE]
  rw [this]; exact norm_sub_le _ _

lemma frob_smul (c : ℝ) (A : Matrix (Fin k) (Fin k) ℝ) :
    frobNorm (c • A) = |c| * frobNorm A := by
  rw [frob_eq, frob_eq]
  have : toE (c • A) = c • toE A := by ext p; simp [toE]
  rw [this, norm_smul, Real.norm_eq_abs]

lemma frob_le_of (A B : Matrix (Fin k) (Fin k) ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, |A i j| ≤ c * |B i j|) : frobNorm A ≤ c * frobNorm B := by
  unfold frobNorm
  calc √(∑ i, ∑ j, A i j ^ 2) ≤ √(∑ i, ∑ j, c ^ 2 * B i j ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
        have h1 := pow_le_pow_left₀ (abs_nonneg _) (h i j) 2
        rw [mul_pow, sq_abs, sq_abs] at h1
        exact h1
    _ = c * √(∑ i, ∑ j, B i j ^ 2) := by
        simp_rw [← Finset.mul_sum]
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Frobenius norm invariant under orthogonal conjugation (via squares). -/
lemma frob_conj (U D : Matrix (Fin k) (Fin k) ℝ) (hU : star U * U = 1) :
    frobNorm (U * D * star U) = frobNorm D := by
  have h2 : frobNorm (U * D * star U) ^ 2 = frobNorm D ^ 2 := by
    rw [frob_sq, frob_sq]
    have hs : star U = Uᴴ := rfl
    rw [hs] at hU ⊢
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc (U * (Dᴴ * Uᴴ) * (U * D * Uᴴ)).trace = (U * (Dᴴ * (Uᴴ * U) * D) * Uᴴ).trace := by
          simp only [Matrix.mul_assoc]
      _ = (Dᴴ * D).trace := by
          rw [hU, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have := frob_nonneg (U * D * star U)
  have := frob_nonneg D
  nlinarith [sq_nonneg (frobNorm (U * D * star U) - frobNorm D),
    sq_nonneg (frobNorm (U * D * star U) + frobNorm D)]

lemma frob_diag (v : Fin k → ℝ) : frobNorm (diagonal v) = √(∑ i, v i ^ 2) := by
  unfold frobNorm
  congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [diagonal_apply_ne _ (Ne.symm hj)]
  · simp

/-- spectral bound: `‖a - 1 + (1+a)⁻¹‖ ≤ ρ²/(1-ρ)` if `‖a‖ ≤ ρ < 1`. -/
lemma spec (a : Matrix (Fin k) (Fin k) ℝ) (ha : a.IsHermitian) (ρ : ℝ) (hρ : ρ < 1)
    (h : frobNorm a ≤ ρ) : frobNorm (a - 1 + (1 + a)⁻¹) ≤ ρ ^ 2 / (1 - ρ) := by
  set U : Matrix (Fin k) (Fin k) ℝ := (ha.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ)
  set lam := ha.eigenvalues
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hA : a = U * diagonal lam * star U := by
    have h1 := ha.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h1
    have h2 : (RCLike.ofReal ∘ ha.eigenvalues : Fin k → ℝ) = lam := by funext i; simp [lam]
    rw [h2] at h1; exact h1
  have hfa : frobNorm a = √(∑ i, lam i ^ 2) := by
    rw [hA, frob_conj _ _ hU, frob_diag]
  have hlam : ∀ i, |lam i| ≤ ρ := by
    intro i
    have : lam i ^ 2 ≤ ∑ j, lam j ^ 2 :=
      Finset.single_le_sum (f := fun j => lam j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : |lam i| ≤ √(∑ j, lam j ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt this
    linarith
  have hpos : ∀ i, 0 < 1 + lam i := by
    intro i; have := hlam i; have := neg_abs_le (lam i); linarith
  set f : Fin k → ℝ := fun i => lam i ^ 2 / (1 + lam i)
  have hinv : (1 + a)⁻¹ = U * diagonal (fun i => (1 + lam i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hA]
    have e1 : (1 : Matrix (Fin k) (Fin k) ℝ) = U * 1 * star U := by rw [Matrix.mul_one, hU']
    calc (1 + U * diagonal lam * star U) * (U * diagonal (fun i => (1 + lam i)⁻¹) * star U)
        = (U * 1 * star U + U * diagonal lam * star U) *
            (U * diagonal (fun i => (1 + lam i)⁻¹) * star U) := by rw [← e1]
      _ = U * ((1 + diagonal lam) * (star U * U) * diagonal (fun i => (1 + lam i)⁻¹)) * star U := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = U * 1 * star U := by
          rw [hU, Matrix.mul_one]
          congr 2
          rw [← diagonal_one, diagonal_add, diagonal_mul_diagonal]
          congr 1; funext i
          field_simp [(hpos i).ne']
      _ = 1 := by rw [Matrix.mul_one, hU']
  have hE : a - 1 + (1 + a)⁻¹ = U * diagonal f * star U := by
    rw [hinv]
    conv_lhs => rw [hA]
    have e1 : (1 : Matrix (Fin k) (Fin k) ℝ) = U * 1 * star U := by rw [Matrix.mul_one, hU']
    rw [e1, ← Matrix.sub_mul, ← Matrix.mul_sub, ← Matrix.add_mul, ← Matrix.mul_add]
    congr 2
    rw [← diagonal_one, diagonal_sub, diagonal_add]
    congr 1; ext i
    simp only [f]
    field_simp [(hpos i).ne']
    ring
  rw [hE, frob_conj _ _ hU]
  have hρ0 : 0 ≤ ρ := le_trans (frob_nonneg a) h
  have hc : 0 ≤ ρ / (1 - ρ) := div_nonneg hρ0 (by linarith)
  have key : frobNorm (diagonal f) ≤ ρ / (1 - ρ) * frobNorm (diagonal lam) := by
    apply frob_le_of _ _ _ hc
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [diagonal_apply_eq, f]
      rw [abs_div, abs_of_pos (hpos i), div_le_iff₀ (hpos i)]
      have hl := hlam i
      have hp := neg_abs_le (lam i)
      rw [sq, abs_mul]
      have h1ρ : 0 < 1 - ρ := by linarith
      -- |l|*|l| ≤ ρ/(1-ρ)*|l|*(1+l)
      have h3 : ρ / (1 - ρ) * (1 - ρ) ≤ ρ / (1 - ρ) * (1 + lam i) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
      rw [div_mul_cancel₀ _ h1ρ.ne'] at h3
      have h4 := mul_le_mul_of_nonneg_left (le_trans hl h3) (abs_nonneg (lam i))
      linarith
    · simp [diagonal_apply_ne _ hij]
  have hfl : frobNorm (diagonal lam) = frobNorm a := by rw [hfa, frob_diag]
  rw [hfl] at key
  calc frobNorm (diagonal f) ≤ ρ / (1 - ρ) * frobNorm a := key
    _ ≤ ρ / (1 - ρ) * ρ := mul_le_mul_of_nonneg_left h hc
    _ = ρ ^ 2 / (1 - ρ) := by ring

/-- real trace positivity: `0 ≤ tr(P Bᴴ B)` for `P ⪰ 0`. -/
lemma tr_psd_mul {P : Matrix (Fin k) (Fin k) ℝ} (hP : P.PosSemidef)
    (B : Matrix (Fin k) (Fin k) ℝ) : 0 ≤ (P * (Bᴴ * B)).trace := by
  have h : (P * (Bᴴ * B)).trace = (B * P * Bᴴ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [h]
  exact (hP.mul_mul_conjTranspose_same B).trace_nonneg

/-- `tr(CGCG) ≤ c² tr(GG)` for `C = BᴴB ⪯ c`, `G` Hermitian. -/
lemma tr_bound (B G : Matrix (Fin k) (Fin k) ℝ) (c : ℝ) (hc : 0 ≤ c) (hG : G.IsHermitian)
    (hle : (c • (1 : Matrix (Fin k) (Fin k) ℝ) - Bᴴ * B).PosSemidef) :
    (Bᴴ * B * G * (Bᴴ * B) * G).trace ≤ c ^ 2 * (G * G).trace := by
  set C := Bᴴ * B
  have t1 := tr_psd_mul hle (B * G)
  have t2 := tr_psd_mul hle G
  rw [conjTranspose_mul, hG.eq] at t1
  rw [hG.eq] at t2
  have e1 : (C * G * C * G).trace = c * (G * C * G).trace -
      ((c • 1 - C) * (G * Bᴴ * (B * G))).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul]
    have : (G * C * G).trace = (G * Bᴴ * (B * G)).trace := by
      simp only [C, Matrix.mul_assoc]
    rw [this]
    have : (C * G * C * G).trace = (C * (G * Bᴴ * (B * G))).trace := by
      simp only [C, Matrix.mul_assoc]
    rw [this]; ring
  have e2 : (G * C * G).trace = c * (G * G).trace - ((c • 1 - C) * (G * G)).trace := by
    rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      smul_eq_mul]
    have : (G * C * G).trace = (C * (G * G)).trace := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [this]; ring
  have hGG : 0 ≤ (G * G).trace := by
    have := tr_psd_mul (P := 1) Matrix.PosSemidef.one G
    rwa [Matrix.one_mul, hG.eq] at this
  rw [e1, e2]
  nlinarith

end X4PF

-- ===== PFB =====

open Matrix
open scoped MatrixOrder

namespace X4PF
open ModernConvex.PathFollowing

variable {k : ℕ}

lemma diag_nonneg (d : Fin k → ℝ) (hd : ∀ i, 0 ≤ d i) : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ diagonal d := by
  rw [Matrix.nonneg_iff_posSemidef, posSemidef_diagonal_iff]; exact hd

lemma sqrt_diag (x : Fin k → ℝ) (hx : ∀ i, 0 ≤ x i) :
    CFC.sqrt (diagonal x) = diagonal (fun i => √(x i)) := by
  rw [CFC.sqrt_eq_iff _ _ (diag_nonneg x hx) (diag_nonneg _ fun i => Real.sqrt_nonneg _)]
  rw [diagonal_mul_diagonal]; congr 1; funext i; exact Real.mul_self_sqrt (hx i)

lemma diag_inv (d : Fin k → ℝ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hd i)

lemma diag_herm (d : Fin k → ℝ) : (diagonal d).IsHermitian := by
  unfold IsHermitian; rw [diagonal_conjTranspose]; simp

/-- the entrywise form of the reduced Newton system (6.5.46). -/
lemma entry (x s : Fin k → ℝ) (hx : ∀ i, 0 < x i) (μ : ℝ) (dX dS : Matrix (Fin k) (Fin k) ℝ)
    (heq : dX * diagonal s + diagonal x * dS + dS * diagonal x + diagonal s * dX =
      (2 * μ) • (1 : Matrix (Fin k) (Fin k) ℝ) - (2 : ℝ) • (diagonal x * diagonal s)) (i j : Fin k) :
    √(x i) * (diagonal s + dS) i j * √(x j) = μ * (1 : Matrix (Fin k) (Fin k) ℝ) i j -
      (√(x i))⁻¹ * dX i j * (√(x j))⁻¹ * (x i * x j * (s i + s j) / (x i + x j)) := by
  have e := congrFun (congrFun heq i) j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, mul_diagonal, diagonal_mul,
    diagonal_mul_diagonal, smul_eq_mul] at e
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq, Matrix.one_apply_eq, Matrix.add_apply] at e ⊢
    have hu := Real.sq_sqrt (hx i).le
    have hu0 := Real.sqrt_pos.mpr (hx i)
    generalize √(x i) = u at hu hu0 ⊢
    rw [← hu] at e ⊢
    field_simp
    linear_combination (1 / 2 : ℝ) * e
  · simp only [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, Matrix.add_apply] at e ⊢
    have hu := Real.sq_sqrt (hx i).le
    have hu0 := Real.sqrt_pos.mpr (hx i)
    have hv := Real.sq_sqrt (hx j).le
    have hv0 := Real.sqrt_pos.mpr (hx j)
    generalize √(x i) = u at hu hu0 ⊢
    generalize √(x j) = v at hv hv0 ⊢
    rw [← hu, ← hv] at e ⊢
    have : 0 < u ^ 2 + v ^ 2 := by positivity
    field_simp
    linear_combination (u * v) * e

/-- `|μ - w_ij| ≤ t + κ`. -/
lemma w_bound (x s : Fin k → ℝ) (hx : ∀ i, 0 < x i) (κ t μ : ℝ) (hμ : μ = 1 - t) (ht : 0 ≤ t)
    (hz : ∀ i, |x i * s i - 1| ≤ κ) (i j : Fin k) :
    |μ - x i * x j * (s i + s j) / (x i + x j)| ≤ t + κ := by
  have hxi := hx i; have hxj := hx j
  have hpos : 0 < x i + x j := by linarith
  have e : 1 - x i * x j * (s i + s j) / (x i + x j) =
      -((x i * s i - 1) * x j + (x j * s j - 1) * x i) / (x i + x j) := by
    field_simp; ring
  have h1 : |1 - x i * x j * (s i + s j) / (x i + x j)| ≤ κ := by
    rw [e, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |(x i * s i - 1) * x j + (x j * s j - 1) * x i|
        ≤ |(x i * s i - 1) * x j| + |(x j * s j - 1) * x i| := abs_add_le _ _
      _ = |x i * s i - 1| * x j + |x j * s j - 1| * x i := by
          rw [abs_mul, abs_mul, abs_of_pos hxi, abs_of_pos hxj]
      _ ≤ κ * x j + κ * x i := by
          gcongr
          · exact hz i
          · exact hz j
      _ = κ * (x i + x j) := by ring
  have : μ - x i * x j * (s i + s j) / (x i + x j) =
      (1 - x i * x j * (s i + s j) / (x i + x j)) - t := by rw [hμ]; ring
  rw [this]
  calc |(1 - x i * x j * (s i + s j) / (x i + x j)) - t|
      ≤ |1 - x i * x j * (s i + s j) / (x i + x j)| + |t| := abs_sub _ _
    _ ≤ κ + t := by rw [abs_of_nonneg ht]; linarith
    _ = t + κ := by ring

end X4PF

-- ===== PFC =====

open Matrix
open scoped MatrixOrder

namespace X4PF
open ModernConvex.PathFollowing

lemma final_ineq (t κ ρ μ : ℝ) (hμ : μ = 1 - t) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ht0 : 0 ≤ t) :
    μ⁻¹ * ((1 + ρ) * ((t + κ) * ρ + μ * (ρ ^ 2 / (1 - ρ)))) ≤
      ρ * (1 + ρ) / (1 - t) * (t + ρ / (1 - ρ) + κ / (1 - κ)) := by
  rw [← hμ]
  have h1ρ : 0 < 1 - ρ := by linarith
  have hκ1' : 0 < 1 - κ := by linarith
  have hk1 : κ ≤ κ / (1 - κ) := by
    rw [le_div_iff₀ hκ1']; nlinarith
  have e1 : μ * (ρ ^ 2 / (1 - ρ)) ≤ ρ * (ρ / (1 - ρ)) := by
    rw [show ρ * (ρ / (1 - ρ)) = 1 * (ρ ^ 2 / (1 - ρ)) by ring]
    exact mul_le_mul_of_nonneg_right hμ1 (div_nonneg (sq_nonneg _) h1ρ.le)
  have e2 : κ * ρ ≤ κ / (1 - κ) * ρ := mul_le_mul_of_nonneg_right hk1 hρ0
  have hb : (t + κ) * ρ + μ * (ρ ^ 2 / (1 - ρ)) ≤ ρ * (t + ρ / (1 - ρ) + κ / (1 - κ)) := by
    nlinarith
  have hc : 0 ≤ μ⁻¹ * (1 + ρ) := mul_nonneg (inv_nonneg.mpr hμ0.le) (by linarith)
  calc μ⁻¹ * ((1 + ρ) * ((t + κ) * ρ + μ * (ρ ^ 2 / (1 - ρ))))
      = μ⁻¹ * (1 + ρ) * ((t + κ) * ρ + μ * (ρ ^ 2 / (1 - ρ))) := by ring
    _ ≤ μ⁻¹ * (1 + ρ) * (ρ * (t + ρ / (1 - ρ) + κ / (1 - κ))) :=
        mul_le_mul_of_nonneg_left hb hc
    _ = ρ * (1 + ρ) / μ * (t + ρ / (1 - ρ) + κ / (1 - κ)) := by
        rw [div_eq_mul_inv]; ring

theorem main {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) (dX dS : Matrix (Fin k) (Fin k) ℝ)
    (hd : P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) dX dS) :
    centralPathDist (muPlus k χ)⁻¹ (diagonal x + dX) (diagonal s + dS) ≤
      closenessBound k κ χ := by
  obtain ⟨hb1, -⟩ := scaled_direction_bounds hk P κ χ x s h dX dS hd
  obtain ⟨hXp, -, -, -, -, hle⟩ := updated_pair_feasible hk P κ χ x s h dX dS hd
  have hx := h.x_pos
  have hχ := h.chi_pos
  have hχκ := h.chi_le_kappa
  have hκ := h.kappa_le
  -- scalar parameters
  set t := χ / √(k : ℝ) with ht
  have hsk : 1 ≤ √(k : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hk
  have ht0 : 0 ≤ t := div_nonneg hχ.le (by linarith)
  have htχ : t ≤ χ := div_le_self hχ.le hsk
  set μ := muPlus k χ with hμdef
  have hμ : μ = 1 - t := rfl
  have hμ0 : 0 < μ := by rw [hμ]; linarith
  have hμ1 : μ ≤ 1 := by rw [hμ]; linarith
  set ρ := rho κ χ with hρdef
  have hκ1 : 0 < 1 - κ := by linarith
  have hsq : √(χ ^ 2 + κ ^ 2) < 1 - κ := by
    rw [Real.sqrt_lt' hκ1]; nlinarith
  have hρ0 : 0 ≤ ρ := div_nonneg (Real.sqrt_nonneg _) hκ1.le
  have hρ1 : ρ < 1 := by
    show √(χ ^ 2 + κ ^ 2) / (1 - κ) < 1
    rw [div_lt_one hκ1]; exact hsq
  -- diagonal scalings
  set Dm : Matrix (Fin k) (Fin k) ℝ := diagonal (fun i => √(x i)) with hDm
  set Di : Matrix (Fin k) (Fin k) ℝ := diagonal (fun i => (√(x i))⁻¹) with hDi
  have hsx : ∀ i, √(x i) ≠ 0 := fun i => (Real.sqrt_pos.mpr (hx i)).ne'
  have hsqX : CFC.sqrt (diagonal x) = Dm := sqrt_diag x (fun i => (hx i).le)
  have hinvD : Dm⁻¹ = Di := diag_inv _ hsx
  have hDmDi : Dm * Di = 1 := by
    rw [hDm, hDi, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
    exact mul_inv_cancel₀ (hsx i)
  have hDiDm : Di * Dm = 1 := by
    rw [hDm, hDi, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
    exact inv_mul_cancel₀ (hsx i)
  have hDiXDi : Di * diagonal x * Di = 1 := by
    rw [hDi, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
    have := Real.mul_self_sqrt (hx i).le
    field_simp [hsx i]; linarith
  have hDmH : Dm.IsHermitian := diag_herm _
  have hDiH : Di.IsHermitian := diag_herm _
  -- a = δX
  set a := Di * dX * Di with ha
  rw [hsqX, hinvD] at hb1
  have hdXH : dX.IsHermitian := P.L_sym dX hd.1
  have hdSH : dS.IsHermitian := hd.2.1.1
  have haH : a.IsHermitian := by
    unfold IsHermitian; rw [ha, conjTranspose_mul, conjTranspose_mul, hDiH.eq, hdXH.eq,
      Matrix.mul_assoc]
  -- the updated pair
  set Xp := diagonal x + dX with hXpdef
  set Sp := diagonal s + dS with hSpdef
  set R := CFC.sqrt Xp with hRdef
  have hXp0 : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ Xp := by
    rw [Matrix.nonneg_iff_posSemidef]; exact hXp.posSemidef
  have hRR : R * R = Xp := CFC.sqrt_mul_sqrt_self Xp hXp0
  have hRH : R.IsHermitian := by
    have : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ R := CFC.sqrt_nonneg Xp
    rw [Matrix.nonneg_iff_posSemidef] at this; exact this.isHermitian
  have hXpU : IsUnit Xp := hXp.isUnit
  have hRU : IsUnit R := by
    rw [← hRR] at hXpU; exact isUnit_of_mul_isUnit_left hXpU
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hRU
  have hXpinv : Xp⁻¹ = R⁻¹ * R⁻¹ := by rw [← hRR, Matrix.mul_inv_rev]
  have hRXR : R * Xp⁻¹ * R = 1 := by
    rw [hXpinv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRdet, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hRdet]
  have hXpH : Xp.IsHermitian := hXp.isHermitian
  have hSpH : Sp.IsHermitian := (diag_herm s).add hdSH
  have hXpiH : Xp⁻¹.IsHermitian := hXpH.inv
  set H := Sp - μ • Xp⁻¹ with hHdef
  have hHH : H.IsHermitian := by
    unfold IsHermitian
    rw [hHdef, conjTranspose_sub, conjTranspose_smul, hSpH.eq, hXpiH.eq, star_trivial]
  -- step 1: the distance is μ⁻¹ ‖R H R‖
  have hstep1 : centralPathDist μ⁻¹ Xp Sp = μ⁻¹ * frobNorm (R * H * R) := by
    unfold centralPathDist
    rw [← hRdef]
    have : μ⁻¹ • (R * Sp * R) - 1 = μ⁻¹ • (R * H * R) := by
      rw [hHdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hRXR,
        smul_sub, smul_smul, inv_mul_cancel₀ hμ0.ne', one_smul]
    rw [this, frob_smul, abs_of_pos (inv_pos.mpr hμ0)]
  -- step 2: ‖RHR‖² = tr(Xp H Xp H)
  have hstep2 : frobNorm (R * H * R) ^ 2 = (Xp * H * Xp * H).trace := by
    rw [frob_sq, conjTranspose_mul, conjTranspose_mul, hRH.eq, hHH.eq]
    calc (R * (H * R) * (R * H * R)).trace = (R * (H * (R * R) * H * R)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (H * (R * R) * H * (R * R)).trace := by
          rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
      _ = (Xp * H * Xp * H).trace := by
          rw [hRR, Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  -- step 3: scaling by Dm
  set C := Di * Xp * Di with hCdef
  have hC : C = 1 + a := by
    rw [hCdef, hXpdef, Matrix.mul_add, Matrix.add_mul, hDiXDi]
  have hXpC : Xp = Dm * C * Dm := by
    rw [hCdef]
    calc Xp = (Dm * Di) * Xp * (Di * Dm) := by rw [hDmDi, hDiDm, Matrix.one_mul, Matrix.mul_one]
      _ = Dm * (Di * Xp * Di) * Dm := by simp only [Matrix.mul_assoc]
  set B := R * Di with hBdef
  have hBC : Bᴴ * B = C := by
    rw [hBdef, conjTranspose_mul, hRH.eq, hDiH.eq, hCdef, ← hRR]
    simp only [Matrix.mul_assoc]
  set G := Dm * H * Dm with hGdef
  have hGH : G.IsHermitian := by
    unfold IsHermitian; rw [hGdef, conjTranspose_mul, conjTranspose_mul, hDmH.eq, hHH.eq,
      Matrix.mul_assoc]
  have hstep3 : (Xp * H * Xp * H).trace = (C * G * C * G).trace := by
    rw [hXpC]
    calc (Dm * C * Dm * H * (Dm * C * Dm) * H).trace
        = (Dm * (C * Dm * H * Dm * C * Dm * H)).trace := by simp only [Matrix.mul_assoc]
      _ = (C * Dm * H * Dm * C * Dm * H * Dm).trace := by rw [Matrix.trace_mul_comm]
      _ = (C * G * C * G).trace := by rw [hGdef]; simp only [Matrix.mul_assoc]
  have hleC : ((1 + ρ) • (1 : Matrix (Fin k) (Fin k) ℝ) - Bᴴ * B).PosSemidef := by
    have := hle.conjTranspose_mul_mul_same Di
    rw [hDiH.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hDiXDi] at this
    rw [hBC]; exact this
  have hstep4 : (C * G * C * G).trace ≤ (1 + ρ) ^ 2 * frobNorm G ^ 2 := by
    have := tr_bound B G (1 + ρ) (by linarith) hGH hleC
    rw [hBC] at this
    rw [frob_sq, hGH.eq]; exact this
  -- step 4: decomposition of G
  have hCinv : (1 + a)⁻¹ = Dm * Xp⁻¹ * Dm := by
    rw [← hC]
    apply Matrix.inv_eq_right_inv
    rw [hCdef]
    calc Di * Xp * Di * (Dm * Xp⁻¹ * Dm) = Di * (Xp * (Di * Dm) * Xp⁻¹) * Dm := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hDiDm, Matrix.mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hXpU),
            Matrix.mul_one, hDiDm]
  set w : Fin k → Fin k → ℝ := fun i j => x i * x j * (s i + s j) / (x i + x j) with hw
  set Hd : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => a i j * (μ - w i j) with hHd
  set E := a - 1 + (1 + a)⁻¹ with hE
  have hGdec : G = Hd - μ • E := by
    have hG2 : G = Dm * Sp * Dm - μ • (1 + a)⁻¹ := by
      rw [hCinv, hGdef, hHdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [hG2, hE]
    ext i j
    have hent := entry x s hx μ dX dS hd.2.2 i j
    have haij : a i j = (√(x i))⁻¹ * dX i j * (√(x j))⁻¹ := by
      rw [ha, hDi, mul_diagonal, diagonal_mul]
    have hS : (Dm * Sp * Dm) i j = √(x i) * Sp i j * √(x j) := by
      rw [hDm, mul_diagonal, diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, hHd,
      Matrix.of_apply, hS]
    rw [hSpdef, hent, ← haij]
    simp only [hw]
    ring
  -- step 5: the bounds
  have hz : ∀ i, |x i * s i - 1| ≤ κ := by
    intro i
    have h1 : (x i * s i - 1) ^ 2 ≤ ∑ j, (x j * s j - 1) ^ 2 :=
      Finset.single_le_sum (f := fun j => (x j * s j - 1) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    have h2 := le_trans h1 h.close
    have hκ0 : 0 ≤ κ := by linarith
    exact abs_le_of_sq_le_sq' h2 hκ0 |> fun ⟨h3, h4⟩ => abs_le.mpr ⟨h3, h4⟩
  have hHdb : frobNorm Hd ≤ (t + κ) * frobNorm a := by
    apply frob_le_of _ _ _ (by linarith)
    intro i j
    simp only [hHd, Matrix.of_apply, abs_mul]
    rw [mul_comm (t + κ)]
    exact mul_le_mul_of_nonneg_left (w_bound x s hx κ t μ hμ ht0 hz i j) (abs_nonneg _)
  have hEb : frobNorm E ≤ ρ ^ 2 / (1 - ρ) := spec a haH ρ hρ1 hb1
  have hGb : frobNorm G ≤ (t + κ) * ρ + μ * (ρ ^ 2 / (1 - ρ)) := by
    rw [hGdec]
    calc frobNorm (Hd - μ • E) ≤ frobNorm Hd + frobNorm (μ • E) := frob_sub_le _ _
      _ = frobNorm Hd + μ * frobNorm E := by rw [frob_smul, abs_of_pos hμ0]
      _ ≤ (t + κ) * ρ + μ * (ρ ^ 2 / (1 - ρ)) := by
          gcongr
          · exact le_trans hHdb (mul_le_mul_of_nonneg_left hb1 (by linarith))
  -- assemble
  set β := (t + κ) * ρ + μ * (ρ ^ 2 / (1 - ρ)) with hβ
  have hβ0 : 0 ≤ β := by
    have : 0 ≤ ρ ^ 2 / (1 - ρ) := div_nonneg (sq_nonneg _) (by linarith)
    exact add_nonneg (mul_nonneg (by linarith) hρ0) (mul_nonneg hμ0.le this)
  have hRHRsq : frobNorm (R * H * R) ^ 2 ≤ ((1 + ρ) * β) ^ 2 := by
    rw [hstep2, hstep3]
    calc (C * G * C * G).trace ≤ (1 + ρ) ^ 2 * frobNorm G ^ 2 := hstep4
      _ ≤ (1 + ρ) ^ 2 * β ^ 2 := by
          gcongr
          · exact frob_nonneg G
      _ = ((1 + ρ) * β) ^ 2 := by ring
  have hRHR : frobNorm (R * H * R) ≤ (1 + ρ) * β := by
    have h0 := frob_nonneg (R * H * R)
    have h1 : 0 ≤ (1 + ρ) * β := by positivity
    nlinarith
  show centralPathDist μ⁻¹ Xp Sp ≤ closenessBound k κ χ
  rw [hstep1]
  have hfin : μ⁻¹ * ((1 + ρ) * β) ≤ closenessBound k κ χ :=
    final_ineq t κ ρ μ hμ hμ0 hμ1 hρ0 hρ1 (by linarith) (by linarith) ht0
  calc μ⁻¹ * frobNorm (R * H * R) ≤ μ⁻¹ * ((1 + ρ) * β) :=
        mul_le_mul_of_nonneg_left hRHR (inv_nonneg.mpr hμ0.le)
    _ ≤ closenessBound k κ χ := hfin

end X4PF

-- ===== PFSol =====

open Matrix
open scoped MatrixOrder
open ModernConvex.PathFollowing

theorem solution {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ)
    (x s : Fin k → ℝ) (h : P.ReducedSituation κ χ x s) (dX dS : Matrix (Fin k) (Fin k) ℝ)
    (hd : P.IsReducedDirection (diagonal x) (diagonal s) (muPlus k χ) dX dS) :
    centralPathDist (muPlus k χ)⁻¹ (diagonal x + dX) (diagonal s + dS) ≤
      closenessBound k κ χ :=
  X4PF.main hk P κ χ x s h dX dS hd

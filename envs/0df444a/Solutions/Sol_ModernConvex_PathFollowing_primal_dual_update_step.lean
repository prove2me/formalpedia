-- Prove2me | solution 1 for ModernConvex.PathFollowing.primal_dual_update_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:49:02.935818+00:00
-- url     : https://prove2.me/submissions/1d763d21-9fe4-4d05-a8b5-d34b1ef20b3e

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP
import Theorems.Thm_ModernConvex_PathFollowing_reduced_system_unique
import Theorems.Thm_ModernConvex_PathFollowing_updated_pair_feasible
import Theorems.Thm_ModernConvex_PathFollowing_closeness_estimate
import Theorems.Thm_ModernConvex_PathFollowing_closeness_bound_le_kappa

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

-- ===== PFD =====

open Matrix

namespace X4PF

variable {k : ℕ}

set_option linter.deprecated false in
/-- Commuting real symmetric matrices are simultaneously orthogonally diagonalizable. -/
lemma simdiag (A B : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : Commute A B) :
    ∃ U : Matrix (Fin k) (Fin k) ℝ, star U * U = 1 ∧ U * star U = 1 ∧
      ∃ α β : Fin k → ℝ, star U * A * U = diagonal α ∧ star U * B * U = diagonal β := by
  set TA := Matrix.toEuclideanLin A
  set TB := Matrix.toEuclideanLin B
  have sA : TA.IsSymmetric := (isHermitian_iff_isSymmetric).mp hA
  have sB : TB.IsSymmetric := (isHermitian_iff_isSymmetric).mp hB
  have cAB : Commute TA TB := by
    show TA * TB = TB * TA
    ext v i
    simp only [TA, TB, Module.End.mul_apply, toEuclideanLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_mulVec, hAB.eq]
  classical
  have hint0 := LinearMap.IsSymmetric.directSum_isInternal_of_commute sA sB cAB
  have horth0 := LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace sA sB
  set V : ℝ × ℝ → Submodule ℝ (EuclideanSpace ℝ (Fin k)) :=
    fun i => Module.End.eigenspace TA i.2 ⊓ Module.End.eigenspace TB i.1 with hV
  have hfin : {i | V i ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hint0.submodule_iSupIndep
  let _ : Fintype {i // V i ≠ ⊥} := hfin.fintype
  have hint : DirectSum.IsInternal (fun i : {i // V i ≠ ⊥} => V i.1) :=
    DirectSum.isInternal_ne_bot_iff.mpr hint0
  have horth : OrthogonalFamily ℝ (fun i : {i // V i ≠ ⊥} => V i.1)
      fun i => (V i.1).subtypeₗᵢ := horth0.comp Subtype.val_injective
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = k := finrank_euclideanSpace_fin
  set b := hint.subordinateOrthonormalBasis hn horth
  set idx := fun j => hint.subordinateOrthonormalBasisIndex hn j horth
  have hmem : ∀ j, b j ∈ (Module.End.eigenspace TA (idx j).1.2 ⊓
      Module.End.eigenspace TB (idx j).1.1) :=
    fun j => hint.subordinateOrthonormalBasis_subordinate hn j horth
  set U : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => b j i with hU
  have hUU : star U * U = 1 := by
    ext l j
    have := orthonormal_iff_ite.mp b.orthonormal l j
    rw [PiLp.inner_apply] at this
    simp only [star_eq_conjTranspose, Matrix.mul_apply, conjTranspose_apply, star_trivial, hU,
      Matrix.of_apply, Matrix.one_apply]
    rw [← this]
    apply Finset.sum_congr rfl; intro i _
    simp [mul_comm]
  have hUU' : U * star U = 1 := mul_eq_one_comm.mp hUU
  have eig : ∀ (T : Matrix (Fin k) (Fin k) ℝ) (c : Fin k → ℝ),
      (∀ j, Matrix.toEuclideanLin T (b j) = c j • b j) → star U * T * U = diagonal c := by
    intro T c hc
    have hTU : T * U = U * diagonal c := by
      ext i j
      have := congrArg (fun v => (WithLp.ofLp v) i) (hc j)
      simp only [toEuclideanLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul, Pi.smul_apply,
        smul_eq_mul, Matrix.mulVec, dotProduct] at this
      rw [mul_diagonal, Matrix.mul_apply]
      simp only [hU, Matrix.of_apply]
      rw [this, mul_comm]
    rw [Matrix.mul_assoc, hTU, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  refine ⟨U, hUU, hUU', fun j => (idx j).1.2, fun j => (idx j).1.1, ?_, ?_⟩
  · apply eig; intro j
    exact Module.End.mem_eigenspace_iff.mp (hmem j).1
  · apply eig; intro j
    exact Module.End.mem_eigenspace_iff.mp (hmem j).2

end X4PF

-- ===== PFE =====

open Matrix
open scoped MatrixOrder

namespace X4PF
open ModernConvex.PathFollowing

variable {k : ℕ}

/-- `‖t X^{1/2} S X^{1/2} − I‖₂² = t² Tr(XSXS) − 2t Tr(XS) + k`. -/
lemma dist_sq (t : ℝ) (X S : Matrix (Fin k) (Fin k) ℝ) (hX : X.PosDef) (hS : S.IsHermitian) :
    centralPathDist t X S ^ 2 = t ^ 2 * (X * S * (X * S)).trace - 2 * t * (X * S).trace + k := by
  unfold centralPathDist
  set R := CFC.sqrt X with hRdef
  have hX0 : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ X := by
    rw [Matrix.nonneg_iff_posSemidef]; exact hX.posSemidef
  have hRR : R * R = X := CFC.sqrt_mul_sqrt_self X hX0
  have hRH : R.IsHermitian := by
    have : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ R := CFC.sqrt_nonneg X
    rw [Matrix.nonneg_iff_posSemidef] at this; exact this.isHermitian
  set A := R * S * R with hA
  have hAH : Aᴴ = A := by
    rw [hA, conjTranspose_mul, conjTranspose_mul, hRH.eq, hS.eq, Matrix.mul_assoc]
  rw [frob_sq]
  have hM : (t • A - 1)ᴴ = t • A - 1 := by
    rw [conjTranspose_sub, conjTranspose_smul, hAH, conjTranspose_one, star_trivial]
  rw [hM]
  have e : (t • A - 1) * (t • A - 1) = t ^ 2 • (A * A) - (2 * t) • A + 1 := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  have t1 : A.trace = (X * S).trace := by
    rw [hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hRR]
  have t2 : (A * A).trace = (X * S * (X * S)).trace := by
    have h1 : (A * A).trace = (S * (R * R) * S * (R * R)).trace := by
      rw [hA, show R * S * R * (R * S * R) = R * (S * (R * R) * S * R) by
        simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [h1, hRR, show S * X * S * X = S * (X * S * X) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, t1, t2,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul]

lemma dist_nonneg (t : ℝ) (X S : Matrix (Fin k) (Fin k) ℝ) : 0 ≤ centralPathDist t X S :=
  frob_nonneg _

section transport

variable (W Wi : Matrix (Fin k) (Fin k) ℝ) (T : ℝ)

/-- `Φ Y = T Wᴴ Y W`. -/
def Φ (Y : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ := T • (Wᴴ * Y * W)
/-- `Ψ Z = Wi Z Wiᴴ`. -/
def Ψ (Z : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ := Wi * Z * Wiᴴ

def Φlin : Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ where
  toFun := Φ W T
  map_add' Y Z := by simp only [Φ, Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' c Y := by
    simp only [Φ, Matrix.mul_smul, Matrix.smul_mul, smul_comm T c, RingHom.id_apply]

variable {W Wi T}
variable (hW : W * Wi = 1) (hW' : Wi * W = 1)
include hW hW'

lemma hWct : Wiᴴ * Wᴴ = 1 := by rw [← conjTranspose_mul, hW, conjTranspose_one]
lemma hWct' : Wᴴ * Wiᴴ = 1 := by rw [← conjTranspose_mul, hW', conjTranspose_one]

lemma ΦΨ (Y Z : Matrix (Fin k) (Fin k) ℝ) : Φ W T Y * Ψ Wi Z = T • (Wᴴ * (Y * Z) * Wiᴴ) := by
  simp only [Φ, Ψ, Matrix.smul_mul]
  congr 1
  calc Wᴴ * Y * W * (Wi * Z * Wiᴴ) = Wᴴ * Y * (W * Wi) * Z * Wiᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hW, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma ΨΦ (Y Z : Matrix (Fin k) (Fin k) ℝ) : Ψ Wi Z * Φ W T Y = T • (Wi * (Z * Y) * W) := by
  simp only [Φ, Ψ, Matrix.mul_smul]
  congr 1
  calc Wi * Z * Wiᴴ * (Wᴴ * Y * W) = Wi * Z * (Wiᴴ * Wᴴ) * Y * W := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hWct hW hW', Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma tr1 (Y Z : Matrix (Fin k) (Fin k) ℝ) : (Φ W T Y * Ψ Wi Z).trace = T * (Y * Z).trace := by
  rw [ΦΨ hW hW', Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    hWct hW hW', Matrix.one_mul]

lemma tr2 (Y Z : Matrix (Fin k) (Fin k) ℝ) :
    (Φ W T Y * Ψ Wi Z * (Φ W T Y * Ψ Wi Z)).trace = T ^ 2 * (Y * Z * (Y * Z)).trace := by
  rw [ΦΨ hW hW', Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  have : Wᴴ * (Y * Z) * Wiᴴ * (Wᴴ * (Y * Z) * Wiᴴ) = Wᴴ * (Y * Z * (Y * Z)) * Wiᴴ := by
    calc _ = Wᴴ * (Y * Z) * (Wiᴴ * Wᴴ) * (Y * Z) * Wiᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWct hW hW', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hWct hW hW', Matrix.one_mul]; ring

lemma Φ_inj (hT : T ≠ 0) {Y Z : Matrix (Fin k) (Fin k) ℝ} (h : Φ W T Y = Φ W T Z) : Y = Z := by
  have e : ∀ Y : Matrix (Fin k) (Fin k) ℝ, T⁻¹ • (Wiᴴ * Φ W T Y * Wi) = Y := by
    intro Y
    simp only [Φ, Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hT, one_smul]
    calc Wiᴴ * (Wᴴ * Y * W) * Wi = (Wiᴴ * Wᴴ) * Y * (W * Wi) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hWct hW hW', hW, Matrix.one_mul, Matrix.mul_one]
  rw [← e Y, ← e Z, h]

lemma Φ_surj (hT : T ≠ 0) (Y' : Matrix (Fin k) (Fin k) ℝ) :
    Φ W T (T⁻¹ • (Wiᴴ * Y' * Wi)) = Y' := by
  simp only [Φ, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hT, one_smul]
  calc Wᴴ * (Wiᴴ * Y' * Wi) * W = (Wᴴ * Wiᴴ) * Y' * (Wi * W) := by simp only [Matrix.mul_assoc]
    _ = Y' := by rw [hWct' hW hW', hW', Matrix.one_mul, Matrix.mul_one]

lemma Ψ_inj {Y Z : Matrix (Fin k) (Fin k) ℝ} (h : Ψ Wi Y = Ψ Wi Z) : Y = Z := by
  have e : ∀ Y : Matrix (Fin k) (Fin k) ℝ, W * Ψ Wi Y * Wᴴ = Y := by
    intro Y
    simp only [Ψ]
    calc W * (Wi * Y * Wiᴴ) * Wᴴ = (W * Wi) * Y * (Wiᴴ * Wᴴ) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hWct hW hW', hW, Matrix.one_mul, Matrix.mul_one]
  rw [← e Y, ← e Z, h]

lemma Ψ_surj (Z' : Matrix (Fin k) (Fin k) ℝ) : Ψ Wi (W * Z' * Wᴴ) = Z' := by
  simp only [Ψ]
  calc Wi * (W * Z' * Wᴴ) * Wiᴴ = (Wi * W) * Z' * (Wᴴ * Wiᴴ) := by simp only [Matrix.mul_assoc]
    _ = Z' := by rw [hWct' hW hW', hW', Matrix.one_mul, Matrix.mul_one]

omit hW hW' in
lemma Φ_herm {Y : Matrix (Fin k) (Fin k) ℝ} (hY : Y.IsHermitian) : (Φ W T Y).IsHermitian := by
  unfold IsHermitian Φ
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    hY.eq, star_trivial, Matrix.mul_assoc]

omit hW hW' in
lemma Ψ_herm {Y : Matrix (Fin k) (Fin k) ℝ} (hY : Y.IsHermitian) : (Ψ Wi Y).IsHermitian := by
  unfold IsHermitian Ψ
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hY.eq, Matrix.mul_assoc]

lemma Ψ_herm_iff {Y : Matrix (Fin k) (Fin k) ℝ} : (Ψ Wi Y).IsHermitian ↔ Y.IsHermitian := by
  refine ⟨fun h => ?_, Ψ_herm⟩
  have : (Ψ Wi Y)ᴴ = Ψ Wi Yᴴ := by
    unfold Ψ; rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  unfold IsHermitian
  apply Ψ_inj hW hW'
  rw [← this, h.eq]

/-- distance transport. -/
lemma dist_tr (c : ℝ) (X S : Matrix (Fin k) (Fin k) ℝ) (hX : X.PosDef) (hS : S.IsHermitian)
    (hX' : (Φ W T X).PosDef) :
    centralPathDist c (Φ W T X) (Ψ Wi S) = centralPathDist (c * T) X S := by
  have h1 := dist_sq c _ _ hX' (Ψ_herm (Wi := Wi) hS)
  have h2 := dist_sq (c * T) X S hX hS
  rw [tr1 hW hW', tr2 hW hW'] at h1
  have : centralPathDist c (Φ W T X) (Ψ Wi S) ^ 2 = centralPathDist (c * T) X S ^ 2 := by
    rw [h1, h2]; ring
  have a1 := dist_nonneg c (Φ W T X) (Ψ Wi S)
  have a2 := dist_nonneg (c * T) X S
  nlinarith [sq_nonneg (centralPathDist c (Φ W T X) (Ψ Wi S) - centralPathDist (c * T) X S)]

end transport

end X4PF

-- ===== PFF =====

open Matrix
open scoped MatrixOrder

namespace X4PF
open ModernConvex.PathFollowing

variable {k : ℕ}

/-- the transported SDP pair. -/
def P' (P : SDPPair k) (W Wi : Matrix (Fin k) (Fin k) ℝ) (T : ℝ) : SDPPair k where
  L := P.L.map (Φlin W T)
  B := Φ W T P.B
  C := Ψ Wi P.C
  L_sym := by
    rintro _ ⟨Y, hY, rfl⟩
    exact Φ_herm (P.L_sym Y hY)
  B_sym := Φ_herm P.B_sym
  C_sym := Ψ_herm P.C_sym

section
variable {P : SDPPair k} {W Wi : Matrix (Fin k) (Fin k) ℝ} {T : ℝ}
  (hW : W * Wi = 1) (hW' : Wi * W = 1) (hT : T ≠ 0)
include hW hW' hT

lemma mem_L' {Y : Matrix (Fin k) (Fin k) ℝ} : Φ W T Y ∈ (P' P W Wi T).L ↔ Y ∈ P.L := by
  constructor
  · rintro ⟨Z, hZ, e⟩
    have : Z = Y := Φ_inj hW hW' hT e
    rwa [← this]
  · intro h; exact Submodule.mem_map_of_mem h

lemma mem_orth {Z : Matrix (Fin k) (Fin k) ℝ} :
    Ψ Wi Z ∈ orthSym (P' P W Wi T).L ↔ Z ∈ orthSym P.L := by
  constructor
  · rintro ⟨hH, h⟩
    refine ⟨(Ψ_herm_iff hW hW').mp hH, fun Y hY => ?_⟩
    have := h (Φ W T Y) ((mem_L' hW hW' hT).mpr hY)
    rw [tr1 hW hW'] at this
    exact (mul_eq_zero.mp this).resolve_left hT
  · rintro ⟨hH, h⟩
    refine ⟨Ψ_herm hH, ?_⟩
    rintro _ ⟨Y, hY, rfl⟩
    show (Φ W T Y * Ψ Wi Z).trace = 0
    rw [tr1 hW hW', h Y hY, mul_zero]

end

lemma orth_add {L : Submodule ℝ (Matrix (Fin k) (Fin k) ℝ)} {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : A ∈ orthSym L) (hB : B ∈ orthSym L) : A + B ∈ orthSym L :=
  ⟨hA.1.add hB.1, fun Y hY => by rw [Matrix.mul_add, Matrix.trace_add, hA.2 Y hY, hB.2 Y hY,
    add_zero]⟩

lemma sum_sq_sub (a : Fin k → ℝ) :
    ∑ i, (a i - 1) ^ 2 = ∑ i, a i ^ 2 - 2 * ∑ i, a i + k := by
  have : ∀ i, (a i - 1) ^ 2 = a i ^ 2 - 2 * a i + 1 := fun i => by ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem goal {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ) (hχ : 0 < χ)
    (hχκ : χ ≤ κ) (hκ : κ ≤ 0.1) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : P.StrictlyPrimalFeasible X) (hS : P.StrictlyDualFeasible S)
    (hclose : centralPathDist (penaltyOf X S) X S ≤ κ)
    (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsCommutingScaling Q X S) :
    (∃! d : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ,
        P.IsSearchDirection Q X S (nextPenalty k χ (penaltyOf X S)) d.1 d.2) ∧
      ∀ dX dS : Matrix (Fin k) (Fin k) ℝ,
        P.IsSearchDirection Q X S (nextPenalty k χ (penaltyOf X S)) dX dS →
          P.StrictlyPrimalFeasible (X + dX) ∧ P.StrictlyDualFeasible (S + dS) ∧
          nextPenalty k χ (penaltyOf X S) = penaltyOf (X + dX) (S + dS) ∧
          P.InNbhd κ (nextPenalty k χ (penaltyOf X S)) (X + dX) (S + dS) := by
  obtain ⟨hXL, hXpd⟩ := hX
  obtain ⟨hSC, hSpd⟩ := hS
  obtain ⟨hQpd, hcomm⟩ := hQ
  have hQH := hQpd.isHermitian
  have hQU : IsUnit Q := hQpd.isUnit
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQU
  have hQiH : Q⁻¹.IsHermitian := hQH.inv
  have hXH := hXpd.isHermitian
  have hSH := hSpd.isHermitian
  have hXtH : (Q * X * Q).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, conjTranspose_mul, hQH.eq, hXH.eq, Matrix.mul_assoc]
  have hStH : (Q⁻¹ * S * Q⁻¹).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, conjTranspose_mul, hQiH.eq, hSH.eq, Matrix.mul_assoc]
  obtain ⟨U, hUU, hUU', α, β, hα, hβ⟩ := simdiag _ _ hXtH hStH hcomm
  rw [star_eq_conjTranspose] at hUU hUU' hα hβ
  set W := Q * U with hWdef
  set Wi := Uᴴ * Q⁻¹ with hWidef
  have hW : W * Wi = 1 := by
    calc W * Wi = Q * (U * Uᴴ) * Q⁻¹ := by simp only [W, Wi, Matrix.mul_assoc]
      _ = 1 := by rw [hUU', Matrix.mul_one, Matrix.mul_nonsing_inv _ hQdet]
  have hW' : Wi * W = 1 := by
    calc Wi * W = Uᴴ * (Q⁻¹ * Q) * U := by simp only [W, Wi, Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hQdet, Matrix.mul_one, hUU]
  have hWct : Wᴴ = Uᴴ * Q := by rw [hWdef, conjTranspose_mul, hQH.eq]
  have hWict : Wiᴴ = Q⁻¹ * U := by rw [hWidef, conjTranspose_mul, hQiH.eq, conjTranspose_conjTranspose]
  have hWX : Wᴴ * X * W = diagonal α := by
    rw [hWct, ← hα]; simp only [W, Matrix.mul_assoc]
  have hWS : Wi * S * Wiᴴ = diagonal β := by
    rw [hWict, ← hβ]; simp only [Wi, Matrix.mul_assoc]
  have hWU : IsUnit W := IsUnit.of_mul_eq_one Wi hW
  have hWiU : IsUnit Wi := IsUnit.of_mul_eq_one W hW'
  have hαpos : ∀ i, 0 < α i := by
    have : (diagonal α).PosDef := by
      rw [← hWX, ← star_eq_conjTranspose]
      exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hWU).mpr hXpd
    exact posDef_diagonal_iff.mp this
  have hβpos : ∀ i, 0 < β i := by
    have : (diagonal β).PosDef := by
      rw [← hWS, ← star_eq_conjTranspose]
      exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hWiU).mpr hSpd
    exact posDef_diagonal_iff.mp this
  -- the trace Tr(XS)
  have hτ : (X * S).trace = ∑ i, α i * β i := by
    have := tr1 (T := 1) hW hW' X S
    simp only [Φ, Ψ, one_smul, one_mul] at this
    rw [← this, hWX, hWS, diagonal_mul_diagonal, trace_diagonal]
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hτpos : 0 < (X * S).trace := by
    rw [hτ]; exact Finset.sum_pos (fun i _ => mul_pos (hαpos i) (hβpos i)) hne
  set T := penaltyOf X S with hTdef
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hT0 : 0 < T := div_pos hk0 hτpos
  have hTne : T ≠ 0 := hT0.ne'
  set x : Fin k → ℝ := fun i => T * α i with hx
  set s : Fin k → ℝ := β with hs
  have hΦX : Φ W T X = diagonal x := by
    simp only [Φ, hWX, hx, ← diagonal_smul]; rfl
  have hΨS : Ψ Wi S = diagonal s := hWS
  -- parameters
  set μ := muPlus k χ with hμdef
  have hsk : 1 ≤ √(k : ℝ) := by rw [Real.one_le_sqrt]; exact_mod_cast hk
  have hμ0 : 0 < μ := by
    show 0 < 1 - χ / √(k : ℝ)
    have : χ / √(k : ℝ) ≤ χ := div_le_self hχ.le hsk
    linarith
  have htp : nextPenalty k χ T = μ⁻¹ * T := rfl
  set P2 := P' P W Wi T with hP2
  have hxs : diagonal x * diagonal s = Φ W T X * Ψ Wi S := by rw [hΦX, hΨS]
  have hred : P2.ReducedSituation κ χ x s := by
    refine ⟨fun i => mul_pos hT0 (hαpos i), hβpos, ?_, ?_, ?_, ?_, hχ, hχκ, hκ⟩
    · rw [← hΦX]
      show Φ W T X + Φ W T P.B ∈ P2.L
      have : Φ W T X + Φ W T P.B = Φ W T (X + P.B) := ((Φlin W T).map_add X P.B).symm
      rw [this]; exact (mem_L' hW hW' hTne).mpr hXL
    · rw [← hΨS]
      show Ψ Wi S - Ψ Wi P.C ∈ orthSym P2.L
      have : Ψ Wi S - Ψ Wi P.C = Ψ Wi (S - P.C) := by
        simp only [Ψ, Matrix.mul_sub, Matrix.sub_mul]
      rw [this]; exact (mem_orth hW hW' hTne).mpr hSC
    · have := tr1 (T := T) hW hW' X S
      rw [← hxs, diagonal_mul_diagonal, trace_diagonal, hτ] at this
      rw [this, ← hτ, hTdef]; unfold penaltyOf; field_simp
    · have hdx : (diagonal x).PosDef := posDef_diagonal_iff.mpr fun i => mul_pos hT0 (hαpos i)
      have h1 := dist_sq 1 (diagonal x) (diagonal s) hdx (diag_herm s)
      have h2 : centralPathDist 1 (diagonal x) (diagonal s) = centralPathDist T X S := by
        rw [← hΦX, ← hΨS, dist_tr hW hW' 1 X S hXpd hSH (by rw [hΦX]; exact hdx), one_mul]
      simp only [diagonal_mul_diagonal, trace_diagonal, one_pow, one_mul, mul_one] at h1
      have h3 : centralPathDist T X S ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ (dist_nonneg _ _ _) hclose 2
      rw [h2] at h1
      have h4 := sum_sq_sub (fun i => x i * s i)
      rw [h4]
      have e : ∀ i, (x i * s i) ^ 2 = x i * s i * (x i * s i) := fun i => by ring
      simp only [e]; linarith
  have hF : ∀ N : Matrix (Fin k) (Fin k) ℝ, T • (Uᴴ * (Q * N * Q⁻¹) * U) = T • (Wᴴ * N * Wiᴴ) := by
    intro N; rw [hWct, hWict]; simp only [Matrix.mul_assoc]
  have hF' : ∀ N : Matrix (Fin k) (Fin k) ℝ, T • (Uᴴ * (Q⁻¹ * N * Q) * U) = T • (Wi * N * W) := by
    intro N; simp only [W, Wi, Matrix.mul_assoc]
  have Finj : ∀ M N : Matrix (Fin k) (Fin k) ℝ, T • (Uᴴ * M * U) = T • (Uᴴ * N * U) → M = N := by
    intro M N h
    have e : ∀ M : Matrix (Fin k) (Fin k) ℝ, U * (T⁻¹ • (T • (Uᴴ * M * U))) * Uᴴ = M := by
      intro M; rw [smul_smul, inv_mul_cancel₀ hTne, one_smul]
      calc U * (Uᴴ * M * U) * Uᴴ = (U * Uᴴ) * M * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [hUU', Matrix.one_mul, Matrix.mul_one]
    rw [← e M, ← e N, h]
  have hdiagc : diagonal s * diagonal x = diagonal x * diagonal s := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]; congr 1; funext i; ring
  have hcoef : T * (2 / nextPenalty k χ T) = 2 * μ := by
    rw [htp]; field_simp
  have key : ∀ dX dS, P.IsSearchDirection Q X S (nextPenalty k χ T) dX dS ↔
      P2.IsReducedDirection (diagonal x) (diagonal s) μ (Φ W T dX) (Ψ Wi dS) := by
    intro dX dS
    unfold SDPPair.IsSearchDirection SDPPair.IsReducedDirection
    rw [← mem_L' (P := P) (Y := dX) hW hW' hTne, ← mem_orth (P := P) (Z := dS) hW hW' hTne]
    apply and_congr Iff.rfl; apply and_congr Iff.rfl
    have eL : Φ W T dX * diagonal s + diagonal x * Ψ Wi dS + Ψ Wi dS * diagonal x +
        diagonal s * Φ W T dX =
        T • (Uᴴ * (Q * (dX * S + X * dS) * Q⁻¹ + Q⁻¹ * (dS * X + S * dX) * Q) * U) := by
      rw [← hΦX, ← hΨS, ΦΨ hW hW', ΦΨ hW hW', ΨΦ hW hW', ΨΦ hW hW']
      simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
      rw [hF, hF, hF', hF']
      abel
    have eR : (2 * μ) • (1 : Matrix (Fin k) (Fin k) ℝ) - (2 : ℝ) • (diagonal x * diagonal s) =
        T • (Uᴴ * ((2 / nextPenalty k χ T) • (1 : Matrix (Fin k) (Fin k) ℝ) -
          (Q * X * S * Q⁻¹ + Q⁻¹ * S * X * Q)) * U) := by
      have h1 : T • (Uᴴ * ((2 / nextPenalty k χ T) • (1 : Matrix (Fin k) (Fin k) ℝ)) * U) =
          (2 * μ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, smul_smul, hcoef]
      have h2 : T • (Uᴴ * (Q * X * S * Q⁻¹) * U) = diagonal x * diagonal s := by
        rw [show Q * X * S * Q⁻¹ = Q * (X * S) * Q⁻¹ by simp only [Matrix.mul_assoc], hF,
          ← ΦΨ hW hW', hΦX, hΨS]
      have h3 : T • (Uᴴ * (Q⁻¹ * S * X * Q) * U) = diagonal s * diagonal x := by
        rw [show Q⁻¹ * S * X * Q = Q⁻¹ * (S * X) * Q by simp only [Matrix.mul_assoc], hF',
          ← ΨΦ hW hW', hΦX, hΨS]
      rw [Matrix.mul_sub, Matrix.sub_mul, smul_sub, h1, Matrix.mul_add, Matrix.add_mul, smul_add,
        h2, h3, hdiagc, two_smul]
    rw [eL, eR]
    exact ⟨fun h => by rw [h], fun h => Finj _ _ h⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨d', hd', huniq⟩ := reduced_system_unique hk P2 κ χ x s hred
    refine ⟨(T⁻¹ • (Wiᴴ * d'.1 * Wi), W * d'.2 * Wᴴ), ?_, ?_⟩
    · show P.IsSearchDirection Q X S (nextPenalty k χ T) (T⁻¹ • (Wiᴴ * d'.1 * Wi)) (W * d'.2 * Wᴴ)
      rw [key, Φ_surj hW hW' hTne, Ψ_surj hW hW']; exact hd'
    · intro e he
      have he' := (key e.1 e.2).mp he
      have := huniq (Φ W T e.1, Ψ Wi e.2) he'
      ext1
      · apply Φ_inj hW hW' hTne; rw [Φ_surj hW hW' hTne]; exact congrArg Prod.fst this
      · apply Ψ_inj hW hW'; rw [Ψ_surj hW hW']; exact congrArg Prod.snd this
  · intro dX dS hsd
    have hr := (key dX dS).mp hsd
    obtain ⟨hXp, hSp, -, -, htr, -⟩ := updated_pair_feasible hk P2 κ χ x s hred _ _ hr
    have hce := closeness_estimate hk P2 κ χ x s hred _ _ hr
    have hcb := closeness_bound_le_kappa k hk κ χ hχ hχκ hκ
    have eX : diagonal x + Φ W T dX = Φ W T (X + dX) := by
      rw [← hΦX]; exact ((Φlin W T).map_add X dX).symm
    have eS : diagonal s + Ψ Wi dS = Ψ Wi (S + dS) := by
      rw [← hΨS]; simp only [Ψ, Matrix.mul_add, Matrix.add_mul]
    rw [eX] at hXp; rw [eS] at hSp; rw [eX, eS] at htr hce
    have hXp' : (X + dX).PosDef := by
      have : (Wᴴ * (X + dX) * W).PosDef := by
        have h := hXp.smul (inv_pos.mpr hT0)
        simp only [Φ, smul_smul, inv_mul_cancel₀ hTne, one_smul] at h; exact h
      rw [← star_eq_conjTranspose] at this
      exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hWU).mp this
    have hSp' : (S + dS).PosDef := by
      have : (Wi * (S + dS) * star Wi).PosDef := hSp
      exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hWiU).mp this
    have hXL' : X + dX + P.B ∈ P.L := by
      have := P.L.add_mem hXL hsd.1
      rwa [show X + P.B + dX = X + dX + P.B by abel] at this
    have hSC' : S + dS - P.C ∈ orthSym P.L := by
      have := orth_add hSC hsd.2.1
      rwa [show S - P.C + dS = S + dS - P.C by abel] at this
    have htr' : T * ((X + dX) * (S + dS)).trace = μ * k := by rw [← tr1 hW hW']; exact htr
    have hpen : nextPenalty k χ T = penaltyOf (X + dX) (S + dS) := by
      rw [htp]; unfold penaltyOf
      have hpos : ((X + dX) * (S + dS)).trace = μ * k / T := by
        rw [eq_div_iff hTne]; linarith [htr']
      rw [hpos]; field_simp
    have hdist : centralPathDist (nextPenalty k χ T) (X + dX) (S + dS) ≤ κ := by
      rw [htp, ← dist_tr hW hW' μ⁻¹ (X + dX) (S + dS) hXp' hSp'.isHermitian hXp]
      exact le_trans hce hcb
    refine ⟨⟨hXL', hXp'⟩, ⟨hSC', hSp'⟩, hpen, hXL', hSC', ?_, hXp', hSp', hdist⟩
    rw [htp]; exact mul_pos (inv_pos.mpr hμ0) hT0

end X4PF

-- ===== PFGSol =====

open Matrix
open scoped MatrixOrder
open ModernConvex.PathFollowing

theorem solution {k : ℕ} (hk : 0 < k) (P : SDPPair k) (κ χ : ℝ) (hχ : 0 < χ)
    (hχκ : χ ≤ κ) (hκ : κ ≤ 0.1) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : P.StrictlyPrimalFeasible X) (hS : P.StrictlyDualFeasible S)
    (hclose : centralPathDist (penaltyOf X S) X S ≤ κ)
    (Q : Matrix (Fin k) (Fin k) ℝ) (hQ : IsCommutingScaling Q X S) :
    (∃! d : Matrix (Fin k) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ,
        P.IsSearchDirection Q X S (nextPenalty k χ (penaltyOf X S)) d.1 d.2) ∧
      ∀ dX dS : Matrix (Fin k) (Fin k) ℝ,
        P.IsSearchDirection Q X S (nextPenalty k χ (penaltyOf X S)) dX dS →
          P.StrictlyPrimalFeasible (X + dX) ∧ P.StrictlyDualFeasible (S + dS) ∧
          nextPenalty k χ (penaltyOf X S) = penaltyOf (X + dX) (S + dS) ∧
          P.InNbhd κ (nextPenalty k χ (penaltyOf X S)) (X + dX) (S + dS) :=
  X4PF.goal hk P κ χ hχ hχκ hκ X S hX hS hclose Q hQ

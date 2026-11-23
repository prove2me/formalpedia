-- Prove2me | solution 1 for MomentPolytopes.QuantumFunctionals.lemma_6_29
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T03:59:43.343809+00:00
-- url     : https://prove2.me/submissions/74b3b09a-25c7-4238-b7eb-f261fe1abebf

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace Aux629

open MomentPolytopes.QuantumFunctionals

lemma star_mul_self_eq_norm_sq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> (simp [Complex.normSq_apply]; try ring)

lemma frobNorm_sq_eq_trace_conjTranspose_mul {m : Type} [Fintype m] (M : Matrix m m ℂ) :
    ∑ i, ∑ j, ‖M i j‖ ^ 2 = (Mᴴ * M).trace.re := by
  rw [Finset.sum_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul_self_eq_norm_sq, Complex.ofReal_re]

lemma cfc_inv_sqrt_one {n : ℕ} :
    cfc (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ).IsHermitian := Matrix.isHermitian_one
  rw [h1.cfc_eq, Matrix.IsHermitian.cfc]
  have heig : ∀ i : Fin n, h1.eigenvalues i = 1 := by
    intro i
    have hv := h1.mulVec_eigenvectorBasis i
    have hne0 := h1.eigenvectorBasis.orthonormal.ne_zero i
    have hne : (h1.eigenvectorBasis i).ofLp ≠ 0 := by
      intro h0
      exact hne0 (WithLp.ofLp_injective _ h0)
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    have hjeq := congrFun hv j
    simp only [Matrix.one_mulVec, Pi.smul_apply, RCLike.real_smul_eq_coe_mul] at hjeq
    have hmul : (((h1.eigenvalues i : ℝ) : ℂ) - 1) * (h1.eigenvectorBasis i).ofLp j = 0 := by
      linear_combination hjeq.symm
    rcases mul_eq_zero.mp hmul with hsub | hzero
    · have : ((h1.eigenvalues i : ℝ) : ℂ) = 1 := sub_eq_zero.mp hsub
      exact_mod_cast this
    · exact absurd hzero hj
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) ∘ h1.eigenvalues) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [heig i]
    · simp [hij]
  change (h1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) ∘ h1.eigenvalues) *
      star (h1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1
  rw [hdiag, mul_one]
  exact Unitary.coe_mul_star_self h1.eigenvectorUnitary

lemma frobNorm_cfc_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    frobNorm (cfc f A) = Real.sqrt (∑ i : Fin n, f (hA.eigenvalues i) ^ 2) := by
  unfold frobNorm
  congr 1
  rw [frobNorm_sq_eq_trace_conjTranspose_mul, hA.cfc_eq, Matrix.IsHermitian.cfc]
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
  have hD_herm : Dᴴ = D := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij, Ne.symm hij]
  have hUU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hprod : (U * D * Uᴴ)ᴴ * (U * D * Uᴴ) = U * (D * D) * Uᴴ := by
    calc
      (U * D * Uᴴ)ᴴ * (U * D * Uᴴ)
          = U * (D * ((Uᴴ * U) * (D * Uᴴ))) := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD_herm, Matrix.mul_assoc]
      _ = U * (D * (D * Uᴴ)) := by rw [hUU, one_mul]
      _ = U * (D * D) * Uᴴ := by simp only [Matrix.mul_assoc]
  change ((U * D * Uᴴ)ᴴ * (U * D * Uᴴ)).trace.re = _
  rw [hprod, Matrix.trace_mul_cycle, hUU, one_mul]
  simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum, sq]

lemma posDef_conjTranspose_mul_self {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (hdet : G.det ≠ 0) :
    (Gᴴ * G).PosDef := by
  have hHerm : (Gᴴ * G).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_mul]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro x hx
  have hGx : G *ᵥ x ≠ 0 := by
    intro h0
    have hunit : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).mpr (Ne.isUnit hdet)
    have hinj := Matrix.mulVec_injective_of_isUnit hunit
    exact hx (hinj (by simpa using h0))
  have hcalc : star x ⬝ᵥ (Gᴴ * G) *ᵥ x = star (G *ᵥ x) ⬝ᵥ (G *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  rw [hcalc]
  have hpos : 0 < ∑ i, ‖(G *ᵥ x) i‖ ^ 2 := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, (G *ᵥ x) i ≠ 0 := Function.ne_iff.mp hGx
    exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hi₀))
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖(G *ᵥ x) i‖) (Finset.mem_univ i₀))
  have hdot : star (G *ᵥ x) ⬝ᵥ (G *ᵥ x) = ((∑ i, ‖(G *ᵥ x) i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, star_mul_self_eq_norm_sq, Complex.ofReal_sum]
  rw [hdot]
  exact_mod_cast hpos

end Aux629

open MomentPolytopes.QuantumFunctionals

theorem solution (n : ℕ) (g : Matrix (Fin n) (Fin n) ℤ) (hg : g.det ≠ 0) (S : ℝ) (hS : 1 ≤ S)
    (hbound : ∀ i j, |((g i j : ℤ) : ℝ)| ≤ S) :
    pdDist 1 ((g.map (Int.cast : ℤ → ℂ))ᴴ * g.map (Int.cast : ℤ → ℂ)) ≤
      2 * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.log (n * S) := by
  set G : Matrix (Fin n) (Fin n) ℂ := g.map (Int.cast : ℤ → ℂ)
  set A : Matrix (Fin n) (Fin n) ℂ := Gᴴ * G
  have hpd : pdDist 1 A = frobNorm (cfc Real.log A) := by
    unfold pdDist
    rw [Aux629.cfc_inv_sqrt_one, one_mul, mul_one]
  rw [hpd]
  have hdetG : G.det ≠ 0 := by
    have hmap : G.det = ((g.det : ℤ) : ℂ) := by
      simpa [G] using (RingHom.map_det (Int.castRingHom ℂ) g).symm
    rw [hmap]
    exact_mod_cast hg
  have hPos : A.PosDef := Aux629.posDef_conjTranspose_mul_self G hdetG
  have hHerm : A.IsHermitian := hPos.isHermitian
  rw [Aux629.frobNorm_cfc_eq hHerm Real.log]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · simp [Real.zero_rpow (by norm_num : (3 : ℝ) / 2 ≠ 0)]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn_pos) with h1 | hn2
  · subst h1
    have hg00_ne : g 0 0 ≠ 0 := by
      simpa [Matrix.det_fin_one] using hg
    have hg00_ge1 : (1 : ℝ) ≤ |((g 0 0 : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |g 0 0| := Int.one_le_abs hg00_ne
      exact_mod_cast this
    have hg00_leS : |((g 0 0 : ℤ) : ℝ)| ≤ S := hbound 0 0
    have htr : hHerm.eigenvalues 0 = |((g 0 0 : ℤ) : ℝ)| ^ 2 := by
      have h1_tr : A.trace = ((hHerm.eigenvalues 0 : ℝ) : ℂ) := by
        simpa [Fin.sum_univ_one] using hHerm.trace_eq_sum_eigenvalues
      have h1_re : A.trace.re = hHerm.eigenvalues 0 := by
        simpa using congrArg Complex.re h1_tr
      have hA00 : A.trace.re = |((g 0 0 : ℤ) : ℝ)| ^ 2 := by
        rw [← Aux629.frobNorm_sq_eq_trace_conjTranspose_mul G]
        simp [G, Complex.norm_intCast]
      linarith
    simp only [Fin.sum_univ_one, htr, Nat.cast_one, one_mul, Real.one_rpow]
    have hlog_nonneg : 0 ≤ Real.log (|((g 0 0 : ℤ) : ℝ)| ^ 2) :=
      Real.log_nonneg (by nlinarith)
    rw [Real.sqrt_sq hlog_nonneg, Real.log_pow, Nat.cast_ofNat]
    have hlog_le : Real.log |((g 0 0 : ℤ) : ℝ)| ≤ Real.log S :=
      Real.log_le_log (by linarith) hg00_leS
    linarith
  · -- Case n ≥ 2
    have hS_pos : 0 < S := by linarith
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hnS_gt1 : 1 < (n : ℝ) * S := by nlinarith
    have hlog_nS_nonneg : 0 ≤ Real.log ((n : ℝ) * S) := Real.log_nonneg (by linarith)
    have htr_le : ∑ i : Fin n, hHerm.eigenvalues i ≤ ((n : ℝ) * S) ^ 2 := by
      have htr0 : A.trace = ((∑ i : Fin n, hHerm.eigenvalues i : ℝ) : ℂ) := by
        simpa using hHerm.trace_eq_sum_eigenvalues
      have htr1 : ∑ i : Fin n, hHerm.eigenvalues i = A.trace.re := by
        simpa using (congrArg Complex.re htr0).symm
      rw [htr1, ← Aux629.frobNorm_sq_eq_trace_conjTranspose_mul G]
      have hentry : ∀ i j : Fin n, ‖G i j‖ ^ 2 ≤ S ^ 2 := fun i j => by
        have hnorm : ‖G i j‖ = |((g i j : ℤ) : ℝ)| := by
          simp [G, Complex.norm_intCast]
        rw [hnorm]
        exact sq_le_sq.mpr (by rw [abs_abs, abs_of_pos hS_pos]; exact hbound i j)
      calc
        ∑ i : Fin n, ∑ j : Fin n, ‖G i j‖ ^ 2
            ≤ ∑ _i : Fin n, ∑ _j : Fin n, S ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
        _ = ((n : ℝ) * S) ^ 2 := by
          simp [Finset.sum_const]
          ring
    have hdet_ge1 : (1 : ℝ) ≤ ∏ i : Fin n, hHerm.eigenvalues i := by
      set d : ℤ := g.det
      have hdet1 : ((∏ i : Fin n, hHerm.eigenvalues i : ℝ) : ℂ) = A.det := by
        rw [hHerm.det_eq_prod_eigenvalues]
        simp
      have hdetA : A.det = (((d : ℝ) ^ 2 : ℝ) : ℂ) := by
        have hmap : G.det = (d : ℂ) := by
          simpa [G, d] using (RingHom.map_det (Int.castRingHom ℂ) g).symm
        have h1 : A.det = star G.det * G.det := by
          rw [show A = Gᴴ * G from rfl, Matrix.det_mul, Matrix.det_conjTranspose]
        have h2 : star G.det * G.det = star (d : ℂ) * (d : ℂ) :=
          congrArg₂ (fun a b : ℂ => star a * b) hmap hmap
        rw [h1, h2, star_intCast]
        push_cast
        ring
      have hprod_eq : ∏ i : Fin n, hHerm.eigenvalues i = (d : ℝ) ^ 2 :=
        Complex.ofReal_injective (hdet1.trans hdetA)
      rw [hprod_eq]
      have habs : (1 : ℤ) ≤ |d| := Int.one_le_abs hg
      have habsR : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast habs
      nlinarith [sq_abs (d : ℝ)]
    have heig_pos : ∀ i : Fin n, 0 < hHerm.eigenvalues i := fun i => hPos.eigenvalues_pos i
    have heig_upper : ∀ i : Fin n, hHerm.eigenvalues i ≤ ((n : ℝ) * S) ^ 2 := fun i =>
      le_trans (Finset.single_le_sum (fun j _ => le_of_lt (heig_pos j)) (Finset.mem_univ i)) htr_le
    have heig_log_abs : ∀ i : Fin n,
        |Real.log (hHerm.eigenvalues i)| ≤ 2 * ((n : ℝ) - 1) * Real.log ((n : ℝ) * S) := by
      intro i
      rw [abs_le]
      constructor
      · have hrest : ∏ j ∈ Finset.univ.erase i, hHerm.eigenvalues j ≤
            (((n : ℝ) * S) ^ 2) ^ (n - 1) := by
          calc
            ∏ j ∈ Finset.univ.erase i, hHerm.eigenvalues j
                ≤ ∏ _j ∈ Finset.univ.erase i, ((n : ℝ) * S) ^ 2 :=
              Finset.prod_le_prod (fun j _ => le_of_lt (heig_pos j)) fun j _ => heig_upper j
            _ = (((n : ℝ) * S) ^ 2) ^ (n - 1) := by
              rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
        have hmul_ge1 : 1 ≤ hHerm.eigenvalues i * (((n : ℝ) * S) ^ 2) ^ (n - 1) := by
          have hsplit : hHerm.eigenvalues i * ∏ j ∈ Finset.univ.erase i, hHerm.eigenvalues j =
              ∏ j : Fin n, hHerm.eigenvalues j :=
            Finset.mul_prod_erase Finset.univ hHerm.eigenvalues (Finset.mem_univ i)
          nlinarith [heig_pos i]
        have hpow_pos : 0 < (((n : ℝ) * S) ^ 2) ^ (n - 1) := by positivity
        have hlog_prod := Real.log_nonneg hmul_ge1
        rw [Real.log_mul (ne_of_gt (heig_pos i)) (ne_of_gt hpow_pos), Real.log_pow,
          Real.log_pow] at hlog_prod
        have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        rw [hn1_cast] at hlog_prod
        push_cast at hlog_prod
        linarith
      · have h1 : Real.log (hHerm.eigenvalues i) ≤ Real.log (((n : ℝ) * S) ^ 2) :=
          Real.log_le_log (heig_pos i) (heig_upper i)
        rw [Real.log_pow, Nat.cast_ofNat] at h1
        nlinarith
    have hsum_le : ∑ i : Fin n, Real.log (hHerm.eigenvalues i) ^ 2 ≤
        (2 * Real.sqrt (n : ℝ) * ((n : ℝ) - 1) * Real.log ((n : ℝ) * S)) ^ 2 := by
      calc
        ∑ i : Fin n, Real.log (hHerm.eigenvalues i) ^ 2
            ≤ ∑ _i : Fin n, (2 * ((n : ℝ) - 1) * Real.log ((n : ℝ) * S)) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sq_abs (Real.log (hHerm.eigenvalues i))]
          exact sq_le_sq' (by nlinarith [abs_nonneg (Real.log (hHerm.eigenvalues i))])
            (heig_log_abs i)
        _ = (n : ℝ) * (2 * ((n : ℝ) - 1) * Real.log ((n : ℝ) * S)) ^ 2 := by
          simp [Finset.sum_const]
        _ = (2 * Real.sqrt (n : ℝ) * ((n : ℝ) - 1) * Real.log ((n : ℝ) * S)) ^ 2 := by
          have hsqn : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
          ring_nf
          rw [hsqn]
          ring
    have hrhs_nonneg : 0 ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) - 1) * Real.log ((n : ℝ) * S) := by
      have : 0 ≤ (n : ℝ) - 1 := by linarith
      positivity
    calc
      Real.sqrt (∑ i : Fin n, Real.log (hHerm.eigenvalues i) ^ 2)
          ≤ 2 * Real.sqrt (n : ℝ) * ((n : ℝ) - 1) * Real.log ((n : ℝ) * S) := by
        rw [← Real.sqrt_sq hrhs_nonneg]
        exact Real.sqrt_le_sqrt hsum_le
      _ ≤ 2 * (Real.sqrt (n : ℝ) * (n : ℝ)) * Real.log ((n : ℝ) * S) := by
        have hsqrt_nn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        nlinarith
      _ = 2 * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.log ((n : ℝ) * S) := by
        congr 2
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one (by positivity : (n : ℝ) ≠ 0)]
        norm_num

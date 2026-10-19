-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Boundary.endpoint_le_two_of_physical_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:46:36.95062+00:00
-- url     : https://prove2.me/submissions/661de543-4d23-4306-86aa-5fc8b9574fc4

import Mathlib
import Definitions.Def_CrouzeixHilbert
import Definitions.Def_OAIQWCH000
import Theorems.Thm_OAI_CrouzeixHilbert_Boundary_densityLp_ordered

section
-- module Solutions.OAIQW_CrouzeixHilbert.Amplification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Amplification. -/

noncomputable section

open scoped TensorProduct Matrix.Norms.L2Operator InnerProductSpace

open Set

namespace CrouzeixHilbert

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {G : Type v} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

open scoped Kronecker

theorem norm_matrixAmplificationCoordinates (n m : ℕ)
    (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    ‖matrixAmplificationCoordinates n m v‖ = ‖v‖ := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq (matrixAmplificationCoordinates n m).continuous.norm continuous_norm) ?_
  intro a
  simp only [matrixAmplificationCoordinates, ContinuousLinearMap.fromCompletion_apply_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.norm_map,
    UniformSpace.Completion.norm_coe]

theorem matrixAmplificationCoordinates_tensorOperator {n m : ℕ}
    (M : Coeff n) (B : Coeff m) (v : Amplification (EuclideanSpace ℂ (Fin n)) m) :
    matrixAmplificationCoordinates n m (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B v) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B) (matrixAmplificationCoordinates n m v) := by
  refine UniformSpace.Completion.induction_on v
    (isClosed_eq ((matrixAmplificationCoordinates n m).continuous.comp
      (tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) M) B).continuous)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M ⊗ₖ B)).continuous.comp
        (matrixAmplificationCoordinates n m).continuous)) ?_
  intro a
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x y =>
    simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
    apply PiLp.ext
    rintro ⟨i, j⟩
    simp only [matrixAmplificationCoordinates_tmul, Matrix.ofLp_toEuclideanCLM,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  | add a b ha hb => simp only [UniformSpace.Completion.coe_add, map_add, ha, hb]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Forms. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

theorem trace_conjTranspose_mul_re {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    (Aᴴ * A).trace.re = ‖toHS A‖ ^ 2 := by
  rw [norm_toHS_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]

theorem trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  have h := (hA.mul_mul_conjTranspose_same C).trace_nonneg
  rw [Matrix.trace_mul_cycle] at h
  simpa only [Matrix.star_eq_conjTranspose, Matrix.trace_mul_comm A] using
    (Complex.nonneg_iff.mp h).1

theorem trace_fromBlocks {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℂ) (B : Matrix n m ℂ) (C : Matrix m n ℂ) (D : Matrix m m ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem block_posSemidef_norm_sq {k : ℕ}
    (p q r : Matrix (Fin k) (Fin k) ℂ)
    (h : (Matrix.fromBlocks p rᴴ r q).PosSemidef) :
    2 * ‖toHS r‖ ^ 2 ≤ ‖toHS p‖ ^ 2 + ‖toHS q‖ ^ 2 := by
  let J : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ :=
    Matrix.fromBlocks 1 0 0 (-1)
  have hp : pᴴ = p := (Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian).1.eq
  have hq : qᴴ = q := (Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian).2.2.2.eq
  have hh := trace_mul_nonneg h (h.conjTranspose_mul_mul_same J)
  have hJ : Jᴴ = J := by simp [J, Matrix.fromBlocks_conjTranspose]
  rw [hJ] at hh
  simp only [J, Matrix.fromBlocks_multiply, mul_one, one_mul, mul_zero, zero_mul,
    Matrix.mul_neg, Matrix.neg_mul, zero_add, add_zero, trace_fromBlocks,
    Matrix.trace_add, Matrix.trace_neg, Complex.add_re, Complex.neg_re] at hh
  have hr : (r * rᴴ).trace.re = ‖toHS r‖ ^ 2 := by
    rw [Matrix.trace_mul_comm, trace_conjTranspose_mul_re]
  have hpp := trace_conjTranspose_mul_re p
  have hqq := trace_conjTranspose_mul_re q
  rw [hp] at hpp
  rw [hq] at hqq
  rw [hpp, hqq] at hh
  rw [trace_conjTranspose_mul_re, hr] at hh
  linarith

theorem lp_block_posSemidef_norm_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {k : ℕ} (p q r : Lp (HS k) 2 μ)
    (h : ∀ᵐ t ∂μ, (Matrix.fromBlocks (ofHS (p t))
      (ofHS (r t))ᴴ (ofHS (r t)) (ofHS (q t))).PosSemidef) :
    2 * ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
  have hi := integral_mono_ae (((Lp.memLp r).norm.integrable_sq).const_mul 2)
    (((Lp.memLp p).norm.integrable_sq).add ((Lp.memLp q).norm.integrable_sq))
    (h.mono fun t ht => by simpa only [toHS_ofHS, Pi.add_apply] using
      block_posSemidef_norm_sq (ofHS (p t)) (ofHS (q t)) (ofHS (r t)) ht)
  simpa only [Pi.add_apply, integral_const_mul, integral_add (Lp.memLp p).norm.integrable_sq
    (Lp.memLp q).norm.integrable_sq, ← lp_norm_sq_eq_integral] using hi

section Splitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace ThreeWaySplitting

variable (s : ThreeWaySplitting E)

theorem proj_orthogonal {i j : Fin 3} (hij : i ≠ j) (x y : E) :
    ⟪s.proj i x, s.proj j y⟫_ℝ = 0 := by
  rw [← s.self_adjoint i, ContinuousLinearMap.adjoint_inner_left,
    s.proj_proj, ite_eq_right hij, inner_zero_right]

theorem norm_sq_decomposition (x : E) :
    ‖x‖ ^ 2 = ‖s.proj 0 x‖ ^ 2 + ‖s.proj 1 x‖ ^ 2 + ‖s.proj 2 x‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 = ‖s.proj 0 x + s.proj 1 x + s.proj 2 x‖ ^ 2 := by rw [s.total_apply]
    _ = _ := by
      simp only [norm_add_sq_real, inner_add_left,
        s.proj_orthogonal (by decide : (0 : Fin 3) ≠ 1),
        s.proj_orthogonal (by decide : (0 : Fin 3) ≠ 2),
        s.proj_orthogonal (by decide : (1 : Fin 3) ≠ 2),
        add_zero, mul_zero]

theorem norm_proj_le (i : Fin 3) : ‖s.proj i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  have h := s.norm_sq_decomposition u
  have h0 := sq_nonneg ‖s.proj 0 u‖
  have h1 := sq_nonneg ‖s.proj 1 u‖
  have h2 := sq_nonneg ‖s.proj 2 u‖
  have hs : ‖s.proj i u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    fin_cases i
    · change ‖s.proj 0 u‖ ^ 2 ≤ ‖u‖ ^ 2
      linarith only [h, h1, h2]
    · change ‖s.proj 1 u‖ ^ 2 ≤ ‖u‖ ^ 2
      linarith only [h, h0, h2]
    · change ‖s.proj 2 u‖ ^ 2 ≤ ‖u‖ ^ 2
      linarith only [h, h0, h1]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

variable {s} {T : E →L[ℝ] E}

theorem range_support (hT : (s.proj 1).comp T = T) (i : Fin 3) (x : E) :
    s.proj i (T x) = if i = 1 then T x else 0 := by
  have ht : s.proj 1 (T x) = T x := congrArg (fun f : E →L[ℝ] E => f x) hT
  calc
    s.proj i (T x) = s.proj i (s.proj 1 (T x)) := by rw [ht]
    _ = _ := by
      rw [s.proj_proj]
      split_ifs with hi
      · subst i
        exact ht
      · rfl

@[simp] theorem proj0_cauchyAdjoint (hT : (s.proj 1).comp T = T) (x : E) :
    s.proj 0 (s.cauchyAdjoint T x) = s.proj 0 x := by
  simp [range_support hT]

@[simp] theorem proj1_cauchyAdjoint (hT : (s.proj 1).comp T = T) (x : E) :
    s.proj 1 (s.cauchyAdjoint T x) = s.proj 1 x + T (s.proj 2 x) := by
  simp [range_support hT]

@[simp] theorem proj2_cauchyAdjoint (hT : (s.proj 1).comp T = T) (x : E) :
    s.proj 2 (s.cauchyAdjoint T x) = 0 := by
  simp [range_support hT]

theorem norm_cauchyAdjoint_sq (hT : (s.proj 1).comp T = T) (x : E) :
    ‖s.cauchyAdjoint T x‖ ^ 2 =
      ‖s.proj 0 x‖ ^ 2 + ‖s.proj 1 x + T (s.proj 2 x)‖ ^ 2 := by
  rw [s.norm_sq_decomposition (s.cauchyAdjoint T x)]
  simp only [proj0_cauchyAdjoint hT, proj1_cauchyAdjoint hT,
    proj2_cauchyAdjoint hT, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem weighted_norm_sq (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1) (x : E) :
    ‖s.cauchyAdjoint T x‖ ^ 2 + ‖s.proj 0 (s.cauchyAdjoint T x)‖ ^ 2 ≤
      2 * ‖x‖ ^ 2 := by
  have hn := norm_apply_le_of_norm_le_one hTnorm (s.proj 2 x)
  have hnsq : ‖T (s.proj 2 x)‖ ^ 2 ≤ ‖s.proj 2 x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hsum := norm_add_le (s.proj 1 x) (T (s.proj 2 x))
  have hsumsq := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  rw [norm_cauchyAdjoint_sq hT, proj0_cauchyAdjoint hT, s.norm_sq_decomposition x]
  nlinarith [sq_nonneg (‖s.proj 1 x‖ - ‖T (s.proj 2 x)‖)]

namespace CompatibleInvolution

variable (j : CompatibleInvolution s)

theorem norm_add_op_sq (u : E) (hneg : s.proj 2 u = 0)
    (h0 : j.op (s.proj 0 u) = s.proj 0 u) :
    ‖u + j.op u‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖s.proj 0 u‖ ^ 2) := by
  have hu : u = s.proj 0 u + s.proj 1 u := by
    simpa only [hneg, add_zero] using (s.total_apply u).symm
  have hju : j.op u = s.proj 0 u + s.proj 2 (j.op u) := by
    calc
      j.op u = j.op (s.proj 0 u + s.proj 1 u) := congrArg j.op hu
      _ = _ := by rw [map_add, h0, j.proj_pos]
  have hi : ⟪u, j.op u⟫_ℝ = ‖s.proj 0 u‖ ^ 2 := by
    calc
      ⟪u, j.op u⟫_ℝ = ⟪s.proj 0 u + s.proj 1 u,
          s.proj 0 u + s.proj 2 (j.op u)⟫_ℝ := congrArg₂ (inner ℝ) hu hju
      _ = _ := by
        simp only [inner_add_left, inner_add_right,
          s.proj_orthogonal (by decide : (0 : Fin 3) ≠ 2),
          s.proj_orthogonal (by decide : (1 : Fin 3) ≠ 0),
          s.proj_orthogonal (by decide : (1 : Fin 3) ≠ 2),
          real_inner_self_eq_norm_sq, add_zero]
  rw [norm_add_sq_real, hi, j.op.norm_map]
  ring

theorem cauchyAdjoint_add_op_sq (hT : (s.proj 1).comp T = T) (u : E)
    (hu : j.op u = u) :
    ‖s.cauchyAdjoint T u + j.op (s.cauchyAdjoint T u)‖ ^ 2 =
      2 * (‖s.cauchyAdjoint T u‖ ^ 2 + ‖s.proj 0 (s.cauchyAdjoint T u)‖ ^ 2) := by
  apply j.norm_add_op_sq _ (proj2_cauchyAdjoint hT u)
  rw [proj0_cauchyAdjoint hT, j.proj_zero, hu]

theorem adjoint_reflected_orthogonal (hT : (s.proj 1).comp T = T)
    (r : E) (hr : s.proj 0 r = 0) :
    ⟪s.cauchyAdjoint T r, j.op (s.cauchyAdjoint T (j.op r))⟫_ℝ = 0 := by
  let g := s.cauchyAdjoint T r
  let h := s.cauchyAdjoint T (j.op r)
  have hg : g = s.proj 1 g := by
    have ht := s.total_apply g
    simpa only [g, proj0_cauchyAdjoint hT, proj2_cauchyAdjoint hT, hr,
      zero_add, add_zero] using ht.symm
  have hm : s.proj 0 (j.op r) = 0 := by rw [← j.proj_zero, hr, map_zero]
  have hh : h = s.proj 1 h := by
    have ht := s.total_apply h
    simpa only [h, proj0_cauchyAdjoint hT, proj2_cauchyAdjoint hT, hm,
      zero_add, add_zero] using ht.symm
  calc
    ⟪g, j.op h⟫_ℝ = ⟪s.proj 1 g, s.proj 2 (j.op h)⟫_ℝ := by
      have hjh : j.op h = s.proj 2 (j.op h) := by
        calc
          j.op h = j.op (s.proj 1 h) := congrArg j.op hh
          _ = _ := j.proj_pos h
      exact congrArg₂ (inner ℝ) hg hjh
    _ = 0 := s.proj_orthogonal (by decide) _ _

theorem norm_cross_ge (hT : (s.proj 1).comp T = T)
    (r : E) (hr : s.proj 0 r = 0) (κ : ℝ) :
    κ ^ 2 * ‖s.cauchyAdjoint T r‖ ^ 2 ≤
      ‖κ • s.cauchyAdjoint T r + κ⁻¹ • j.op (s.cauchyAdjoint T (j.op r))‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_left, inner_smul_right,
    j.adjoint_reflected_orthogonal hT r hr, mul_zero, mul_zero, mul_zero, add_zero]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  exact le_add_of_nonneg_right (by positivity)

end CompatibleInvolution

theorem ordered_projection (L : E →L[ℝ] E)
    (hL : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) (r : E) :
    s.cauchyAdjoint T (ContinuousLinearMap.adjoint L r) =
      s.cauchyAdjoint T (ContinuousLinearMap.adjoint L (s.cauchyAdjoint T r)) := by
  have h := congrArg ContinuousLinearMap.adjoint hL
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] at h
  exact (congrArg (fun M : E →L[ℝ] E => M r) h).symm

theorem norm_adjoint_apply_le_of_norm_le_one {L : E →L[ℝ] E}
    (hL : ‖L‖ ≤ 1) (x : E) : ‖ContinuousLinearMap.adjoint L x‖ ≤ ‖x‖ :=
  norm_apply_le_of_norm_le_one ((ContinuousLinearMap.adjoint.norm_map L).trans_le hL) x

theorem diagonal_estimate (j : CompatibleInvolution s)
    (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1)
    (L : E →L[ℝ] E) (hLnorm : ‖L‖ ≤ 1)
    (hL : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (p r : E) (hp : p = ContinuousLinearMap.adjoint L r) (hpstar : j.op p = p) :
    ‖s.cauchyAdjoint T p + j.op (s.cauchyAdjoint T (j.op p))‖ ^ 2 ≤
      4 * ‖s.cauchyAdjoint T r‖ ^ 2 := by
  have hd : s.cauchyAdjoint T p =
      s.cauchyAdjoint T (ContinuousLinearMap.adjoint L (s.cauchyAdjoint T r)) := by
    rw [hp, ordered_projection L hL r]
  have hn := norm_adjoint_apply_le_of_norm_le_one hLnorm (s.cauchyAdjoint T r)
  have hnsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hw := weighted_norm_sq hT hTnorm
    (ContinuousLinearMap.adjoint L (s.cauchyAdjoint T r))
  rw [hpstar, j.cauchyAdjoint_add_op_sq hT p hpstar, hd]
  linarith

theorem ordered_comparison_of_block_norm (j : CompatibleInvolution s)
    (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1)
    (L R : E →L[ℝ] E) (hLnorm : ‖L‖ ≤ 1) (hRnorm : ‖R‖ ≤ 1)
    (hL : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      L.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (hR : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        (R.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      R.comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (p q r : E) (hp : p = ContinuousLinearMap.adjoint L r)
    (hq : q = ContinuousLinearMap.adjoint R r)
    (hpstar : j.op p = p) (hqstar : j.op q = q)
    (hrmean : s.proj 0 r = 0) (hpmean : s.proj 0 p ≠ 0)
    (κ : ℝ) (hκ : 0 < κ)
    (hblock : 2 * ‖κ • s.cauchyAdjoint T r +
          κ⁻¹ • j.op (s.cauchyAdjoint T (j.op r))‖ ^ 2 ≤
      ‖s.cauchyAdjoint T p + j.op (s.cauchyAdjoint T (j.op p))‖ ^ 2 +
      ‖s.cauchyAdjoint T q + j.op (s.cauchyAdjoint T (j.op q))‖ ^ 2) : κ ≤ 2 := by
  have hg : s.cauchyAdjoint T r ≠ 0 := by
    intro hg
    have hd : s.cauchyAdjoint T p = 0 := by
      rw [hp, ordered_projection L hL r, hg, map_zero, map_zero]
    apply hpmean
    rw [← proj0_cauchyAdjoint hT p, hd, map_zero]
  have hgp : 0 < ‖s.cauchyAdjoint T r‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hpbound := diagonal_estimate j hT hTnorm L hLnorm hL p r hp hpstar
  have hqbound := diagonal_estimate j hT hTnorm R hRnorm hR q r hq hqstar
  have hcross := j.norm_cross_ge hT r hrmean κ
  have hm : κ ^ 2 * ‖s.cauchyAdjoint T r‖ ^ 2 ≤
      4 * ‖s.cauchyAdjoint T r‖ ^ 2 := by linarith
  have hsq : κ ^ 2 ≤ 4 := (mul_le_mul_iff_of_pos_right hgp).mp hm
  nlinarith

end ThreeWaySplitting

end Splitting

section FieldAction

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem fieldAction_apply_ae (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) (u : Lp E 2 μ) :
    fieldAction L hL hLn u =ᵐ[μ] fun t => L t (u t) := by
  unfold fieldAction
  dsimp only [LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

omit [CompleteSpace E] in
theorem norm_fieldAction_le (L : α → E →L[ℝ] E) (hL : AEStronglyMeasurable L μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) : ‖fieldAction L hL hLn‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [fieldAction_apply_ae L hL hLn u, hLn] with t ht hn
  rw [ht]
  exact ThreeWaySplitting.norm_apply_le_of_norm_le_one hn _

theorem adjoint_fieldAction (L M : α → E →L[ℝ] E)
    (hL : AEStronglyMeasurable L μ) (hM : AEStronglyMeasurable M μ)
    (hLn : ∀ᵐ t ∂μ, ‖L t‖ ≤ 1) (hMn : ∀ᵐ t ∂μ, ‖M t‖ ≤ 1)
    (ha : ∀ᵐ t ∂μ, ContinuousLinearMap.adjoint (L t) = M t) :
    ContinuousLinearMap.adjoint (fieldAction L hL hLn) = fieldAction M hM hMn := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldAction_apply_ae M hM hMn u, fieldAction_apply_ae L hL hLn v, ha]
    with t hu hv ht
  rw [hu, hv, ← ht, ContinuousLinearMap.adjoint_inner_left]

end FieldAction

section MatrixMultipliers

theorem inner_toHS {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ⟪toHS A, toHS B⟫_ℂ = (Aᴴ * B).trace := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, toHS,
    Fintype.sum_prod_type, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, starRingEnd_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem real_inner_toHS {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ⟪toHS A, toHS B⟫_ℝ = (Aᴴ * B).trace.re := by
  rw [← inner_toHS]
  simp only [PiLp.inner_apply, toHS, real_inner_eq_re_inner ℂ,
    RCLike.re_to_complex, Complex.re_sum]

@[simp] theorem adjoint_hsLeft {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ContinuousLinearMap.adjoint (hsLeft A) = hsLeft Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  obtain ⟨U, rfl⟩ := (hsEquiv k).surjective u
  obtain ⟨V, rfl⟩ := (hsEquiv k).surjective v
  simp only [hsEquiv_apply, hsLeft_apply, ofHS_toHS, 
    real_inner_toHS, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

@[simp] theorem adjoint_hsRight {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ContinuousLinearMap.adjoint (hsRight A) = hsRight Aᴴ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  obtain ⟨U, rfl⟩ := (hsEquiv k).surjective u
  obtain ⟨V, rfl⟩ := (hsEquiv k).surjective v
  simp only [hsEquiv_apply, hsRight_apply, ofHS_toHS, 
    real_inner_toHS, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm (V * A)]

end MatrixMultipliers

section L2Multipliers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : ℕ}

theorem lpStar_apply_ae (u : Lp (HS k) 2 μ) :
    lpStar u =ᵐ[μ] fun t => toHS (ofHS (u t))ᴴ :=
  (hsStar k).toContinuousLinearMap.coeFn_compLpL u

@[simp] theorem lpStar_lpStar (u : Lp (HS k) 2 μ) : lpStar (lpStar u) = u := by
  apply Lp.ext
  filter_upwards [lpStar_apply_ae u, lpStar_apply_ae (lpStar u)] with t hu hsu
  simp only [hsu, hu, ofHS_toHS, Matrix.conjTranspose_conjTranspose, toHS_ofHS]

theorem lpLeft_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    lpLeft F hm hn u =ᵐ[μ] fun t => toHS (F t * ofHS (u t)) :=
  fieldAction_apply_ae _ _ _ _

theorem lpRight_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    lpRight F hm hn u =ᵐ[μ] fun t => toHS (ofHS (u t) * F t) :=
  fieldAction_apply_ae _ _ _ _

theorem norm_lpLeft_le (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) :
    ‖lpLeft F hm hn‖ ≤ 1 := norm_fieldAction_le _ _ _

theorem norm_lpRight_le (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1) :
    ‖lpRight F hm hn‖ ≤ 1 := norm_fieldAction_le _ _ _

theorem aestronglyMeasurable_conjTranspose (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) : AEStronglyMeasurable (fun t => (F t)ᴴ) μ :=
  (show Continuous (fun A : Matrix (Fin k) (Fin k) ℂ => Aᴴ) by fun_prop).comp_aestronglyMeasurable hm

theorem lpLeft_adjoint_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    ContinuousLinearMap.adjoint (lpLeft F hm hn) u =ᵐ[μ]
      fun t => toHS ((F t)ᴴ * ofHS (u t)) := by
  have hm' := aestronglyMeasurable_conjTranspose F hm
  have hn' : ∀ᵐ t ∂μ, ‖(F t)ᴴ‖ ≤ 1 := hn.mono fun t ht => by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have h : ContinuousLinearMap.adjoint (lpLeft F hm hn) = lpLeft (fun t => (F t)ᴴ) hm' hn' :=
    adjoint_fieldAction _ _ _ _ _ _ (Filter.Eventually.of_forall fun t => adjoint_hsLeft _)
  rw [h]
  exact lpLeft_apply_ae _ _ _ _

theorem lpRight_adjoint_apply_ae (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (u : Lp (HS k) 2 μ) :
    ContinuousLinearMap.adjoint (lpRight F hm hn) u =ᵐ[μ]
      fun t => toHS (ofHS (u t) * (F t)ᴴ) := by
  have hm' := aestronglyMeasurable_conjTranspose F hm
  have hn' : ∀ᵐ t ∂μ, ‖(F t)ᴴ‖ ≤ 1 := hn.mono fun t ht => by
    rwa [Matrix.l2_opNorm_conjTranspose]
  have h : ContinuousLinearMap.adjoint (lpRight F hm hn) = lpRight (fun t => (F t)ᴴ) hm' hn' :=
    adjoint_fieldAction _ _ _ _ _ _ (Filter.Eventually.of_forall fun t => adjoint_hsRight _)
  rw [h]
  exact lpRight_apply_ae _ _ _ _

theorem lpStar_eq_self_iff (u : Lp (HS k) 2 μ) :
    lpStar u = u ↔ ∀ᵐ t ∂μ, (ofHS (u t)).IsHermitian := by
  constructor
  · intro h
    filter_upwards [lpStar_apply_ae u] with t ht
    rw [h] at ht
    have he := congrArg ofHS ht
    exact (he.trans (ofHS_toHS _)).symm
  · intro h
    apply Lp.ext
    filter_upwards [lpStar_apply_ae u, h] with t ht he
    rw [ht, he.eq, toHS_ofHS]

theorem lp_ordered_comparison
    (s : ThreeWaySplitting (Lp (HS k) 2 μ))
    (hstar0 : ∀ u, lpStar (s.proj 0 u) = s.proj 0 (lpStar u))
    (hstar1 : ∀ u, lpStar (s.proj 1 u) = s.proj 2 (lpStar u))
    (T : Lp (HS k) 2 μ →L[ℝ] Lp (HS k) 2 μ)
    (hT : (s.proj 1).comp T = T) (hTnorm : ‖T‖ ≤ 1)
    (F : α → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F μ) (hn : ∀ᵐ t ∂μ, ‖F t‖ ≤ 1)
    (hleft : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        ((lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      (lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (hright : (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)).comp
        ((lpRight F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T))) =
      (lpRight F hm hn).comp (ContinuousLinearMap.adjoint (s.cauchyAdjoint T)))
    (p q r : Lp (HS k) 2 μ)
    (hpstar : ∀ᵐ t ∂μ, (ofHS (p t)).IsHermitian)
    (hqstar : ∀ᵐ t ∂μ, (ofHS (q t)).IsHermitian)
    (hp : ∀ᵐ t ∂μ, ofHS (p t) = (F t)ᴴ * ofHS (r t))
    (hq : ∀ᵐ t ∂μ, ofHS (q t) = ofHS (r t) * (F t)ᴴ)
    (hrmean : s.proj 0 r = 0) (hpmean : s.proj 0 p ≠ 0)
    (κ : ℝ) (hκ : 0 < κ)
    (hblock : let D := s.cauchyAdjoint T
      let pₑ := D p + lpStar (D (lpStar p))
      let qₑ := D q + lpStar (D (lpStar q))
      let rₑ := κ • D r + κ⁻¹ • lpStar (D (lpStar r))
      ∀ᵐ t ∂μ, (Matrix.fromBlocks (ofHS (pₑ t))
        (ofHS (rₑ t))ᴴ (ofHS (rₑ t)) (ofHS (qₑ t))).PosSemidef) : κ ≤ 2 := by
  let j : s.CompatibleInvolution := {
    op := lpStar
    involutive := lpStar_lpStar
    proj_zero := hstar0
    proj_pos := hstar1 }
  have hp' : p = ContinuousLinearMap.adjoint (lpLeft F hm hn) r := by
    apply Lp.ext
    filter_upwards [hp, lpLeft_adjoint_apply_ae F hm hn r] with t ht ha
    rw [ha, ← ht, toHS_ofHS]
  have hq' : q = ContinuousLinearMap.adjoint (lpRight F hm hn) r := by
    apply Lp.ext
    filter_upwards [hq, lpRight_adjoint_apply_ae F hm hn r] with t ht ha
    rw [ha, ← ht, toHS_ofHS]
  exact ThreeWaySplitting.ordered_comparison_of_block_norm j hT hTnorm
    (lpLeft F hm hn) (lpRight F hm hn) (norm_lpLeft_le F hm hn)
    (norm_lpRight_le F hm hn) hleft hright p q r hp' hq'
    ((lpStar_eq_self_iff p).mpr hpstar) ((lpStar_eq_self_iff q).mpr hqstar)
    hrmean hpmean κ hκ (lp_block_posSemidef_norm_sq _ _ _ hblock)

end L2Multipliers

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Fourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fourier. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace lp Classical Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

attribute [local instance] OAI.CrouzeixHilbert.Boundary.instFactLtRealOfNat_solutions
lemma matrixFourierBasis_repr {k : ℕ} (u : BoundaryL2 k) (a : ℤ × (Fin k × Fin k)) :
    (matrixFourierBasis k).repr u a = fourierCoeff (lpEntry a.2 u) a.1 := by
  rw [HilbertBasis.repr_apply_apply, matrixFourierBasis_apply, inner_matrixFourier,
    ← coe_fourierBasis, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]

lemma repr_lpStar {k : ℕ} (u : BoundaryL2 k) (n : ℤ) (i j : Fin k) :
    (matrixFourierBasis k).repr (lpStar u) (n,(i,j)) =
      star ((matrixFourierBasis k).repr u (-n,(j,i))) := by
  rw [matrixFourierBasis_repr, matrixFourierBasis_repr]
  simp only [fourierCoeff, neg_neg, smul_eq_mul, Complex.star_def]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [lpEntry_apply_ae (i,j) (lpStar u), lpStar_apply_ae u,
    lpEntry_apply_ae (j,i) u] with t he hs he'
  simp only [he, hs, he', toHS, ofHS,
    Matrix.conjTranspose_apply, Complex.star_def, map_mul, fourier_neg]

lemma lpStar_fourierProj_zero {k : ℕ} (u : BoundaryL2 k) :
    lpStar (fourierProjC k 0 u) = fourierProjC k 0 (lpStar u) := by
  apply (matrixFourierBasis k).repr.injective
  ext ⟨n,i,j⟩
  rw [repr_lpStar, repr_fourierProjC, repr_fourierProjC, repr_lpStar]
  simp only [frequencyPart_zero, neg_eq_zero, apply_ite (star : ℂ → ℂ), star_zero]

lemma lpStar_fourierProj_pos {k : ℕ} (u : BoundaryL2 k) :
    lpStar (fourierProjC k 1 u) = fourierProjC k 2 (lpStar u) := by
  apply (matrixFourierBasis k).repr.injective
  ext ⟨n,i,j⟩
  rw [repr_lpStar, repr_fourierProjC, repr_fourierProjC, repr_lpStar]
  simp only [frequencyPart_pos, frequencyPart_neg, neg_pos,
    apply_ite (star : ℂ → ℂ), star_zero]

lemma repr_zero_eq_mean {k : ℕ} (u : BoundaryL2 k) (i j : Fin k) :
    (matrixFourierBasis k).repr u (0,(i,j)) = matrixMean u i j := by
  rw [matrixFourierBasis_repr]
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul]
  exact integral_congr_ae (lpEntry_apply_ae (i,j) u)

lemma mean_eq_zero_iff {k : ℕ} (u : BoundaryL2 k) :
    matrixMean u = 0 ↔ (fourierSplitting k).proj 0 u = 0 := by
  constructor
  · intro h
    apply (matrixFourierBasis k).repr.injective
    ext ⟨n,i,j⟩
    change (matrixFourierBasis k).repr (fourierProjC k 0 u) (n,(i,j)) = _
    rw [repr_fourierProjC, map_zero]
    change (if frequencyPart 0 n then _ else 0) = 0
    by_cases hn : n = 0
    · subst n
      simp only [frequencyPart_zero, ite_true, repr_zero_eq_mean, h, Matrix.zero_apply]
    · simp only [frequencyPart_zero, ite_eq_right hn]
  · intro h
    ext i j
    have hz := congrArg (fun v : BoundaryL2 k => (matrixFourierBasis k).repr v (0,(i,j))) h
    change (matrixFourierBasis k).repr (fourierProjC k 0 u) (0,(i,j)) = _ at hz
    simpa only [repr_fourierProjC, frequencyPart_zero, ite_true, repr_zero_eq_mean,
      map_zero, lp.coeFn_zero, Pi.zero_apply, Matrix.zero_apply] using hz

lemma norm_fourier_proj_le (k : ℕ) (i : Fin 3) :
    ‖(fourierSplitting k).proj i‖ ≤ 1 := (fourierSplitting k).norm_proj_le i

lemma upperTransfer_range {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    ((fourierSplitting k).proj 1).comp (upperTransfer M) = upperTransfer M := by
  apply ContinuousLinearMap.ext
  intro u
  change (fourierSplitting k).proj 1 ((fourierSplitting k).proj 1 _) = _
  simp only [ThreeWaySplitting.proj_proj, ite_true]
  rfl

lemma norm_upperTransfer_le {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k)
    (hM : ‖M‖ ≤ 1) : ‖upperTransfer M‖ ≤ 1 := by
  calc
    _ ≤ ‖(fourierSplitting k).proj 1‖ * ‖ContinuousLinearMap.adjoint M‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_fourier_proj_le k 1)
      (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hM)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

lemma adjoint_boundaryCauchy {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    ContinuousLinearMap.adjoint (boundaryCauchy M) = boundaryCauchyAdjoint M := by
  simp only [boundaryCauchy, boundaryCauchyAdjoint, ThreeWaySplitting.cauchyAdjoint,
    upperTransfer, map_add, ContinuousLinearMap.adjoint_comp,
    ThreeWaySplitting.self_adjoint, ContinuousLinearMap.comp_assoc]

lemma adjoint_boundaryCauchyAdjoint {k : ℕ} (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) :
    ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M) = boundaryCauchy M := by
  rw [← adjoint_boundaryCauchy, ContinuousLinearMap.adjoint_adjoint]

theorem fourier_ordered_comparison {k : ℕ}
    (M : BoundaryL2 k →L[ℝ] BoundaryL2 k) (hM : ‖M‖ ≤ 1)
    (F : CircleSpace → Matrix (Fin k) (Fin k) ℂ)
    (hm : AEStronglyMeasurable F circleMeasure)
    (hn : ∀ᵐ t ∂circleMeasure, ‖F t‖ ≤ 1)
    (hleft : (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)).comp
        ((lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M))) =
      (lpLeft F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)))
    (hright : (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)).comp
        ((lpRight F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M))) =
      (lpRight F hm hn).comp (ContinuousLinearMap.adjoint (boundaryCauchyAdjoint M)))
    (p q r : BoundaryL2 k)
    (hpstar : ∀ᵐ t ∂circleMeasure, (ofHS (p t)).IsHermitian)
    (hqstar : ∀ᵐ t ∂circleMeasure, (ofHS (q t)).IsHermitian)
    (hp : ∀ᵐ t ∂circleMeasure, ofHS (p t) = (F t)ᴴ * ofHS (r t))
    (hq : ∀ᵐ t ∂circleMeasure, ofHS (q t) = ofHS (r t) * (F t)ᴴ)
    (hrmean : matrixMean r = 0) (hpmean : 0 < (matrixMean p).trace.re)
    (κ : ℝ) (hκ : 0 < κ)
    (hblock : let D := boundaryCauchyAdjoint M
      let pₑ := D p + lpStar (D (lpStar p))
      let qₑ := D q + lpStar (D (lpStar q))
      let rₑ := κ • D r + κ⁻¹ • lpStar (D (lpStar r))
      ∀ᵐ t ∂circleMeasure, (Matrix.fromBlocks (ofHS (pₑ t))
        (ofHS (rₑ t))ᴴ (ofHS (rₑ t)) (ofHS (qₑ t))).PosSemidef) : κ ≤ 2 := by
  apply lp_ordered_comparison (fourierSplitting k)
    lpStar_fourierProj_zero lpStar_fourierProj_pos (upperTransfer M)
    (upperTransfer_range M) (norm_upperTransfer_le M hM) F hm hn
    hleft hright p q r hpstar hqstar hp hq ((mean_eq_zero_iff r).mp hrmean) _ κ hκ hblock
  intro h
  have hz : matrixMean p = 0 := (mean_eq_zero_iff p).mpr h
  simp only [hz, Matrix.trace_zero, Complex.zero_re] at hpmean
  exact lt_irrefl 0 hpmean

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Density. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

section PartialTraces

variable {n m : Type*} [Fintype n]

variable [Fintype m]

theorem crossPartialTrace_block_posSemidef (X Y : Matrix n m ℂ) :
    (Matrix.fromBlocks (crossPartialTrace X X) (crossPartialTrace Y X)
      (crossPartialTrace X Y) (crossPartialTrace Y Y)).PosSemidef := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromCols X Y)).transpose
  have he : Matrix.fromBlocks (crossPartialTrace X X) (crossPartialTrace Y X)
      (crossPartialTrace X Y) (crossPartialTrace Y Y) =
      ((Matrix.fromCols X Y)ᴴ * Matrix.fromCols X Y)ᵀ := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [he]
  exact h

omit [Fintype m] in
theorem weightedPartialTrace_factor (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) :
    weightedPartialTrace (Lᴴ * L) X Y = crossPartialTrace (L * X) (L * Y) := by
  simp only [weightedPartialTrace, crossPartialTrace, Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable [DecidableEq n]

theorem weightedPartialTrace_block_posSemidef (E : Matrix n n ℂ)
    (hE : E.PosSemidef) (X Y : Matrix n m ℂ) :
    (Matrix.fromBlocks (weightedPartialTrace E X X) (weightedPartialTrace E Y X)
      (weightedPartialTrace E X Y) (weightedPartialTrace E Y Y)).PosSemidef := by
  obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  rw [hL]
  simpa only [Matrix.star_eq_conjTranspose, weightedPartialTrace_factor] using
    crossPartialTrace_block_posSemidef (L * X) (L * Y)

end PartialTraces

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.Vectorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vectorization. -/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.L2Operator Kronecker InnerProductSpace MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Realization

theorem kronecker_toHS {n : ℕ} (A B X : Coeff n) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (A ⊗ₖ B)) (Boundary.toHS X) =
      Boundary.toHS (A * X * Bᵀ) := by
  apply PiLp.ext
  rintro ⟨i,j⟩
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Boundary.toHS,
    WithLp.ofLp_toLp, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem tensorOperator_vectorization {n : ℕ} (A B X : Coeff n) :
    tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) A) B (vectorization X) =
      vectorization (A * X * Bᵀ) := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  apply e.injective
  change matrixAmplificationCoordinates n n _ = matrixAmplificationCoordinates n n _
  rw [matrixAmplificationCoordinates_tensorOperator, vectorization_coordinates,
    vectorization_coordinates, kronecker_toHS]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.TensorDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor Density. -/

noncomputable section

open MeasureTheory Set Filter

open scoped Topology InnerProductSpace TensorProduct Matrix.Norms.L2Operator

namespace CrouzeixHilbert

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorRealNormedSpace
attribute [local instance] OAI.CrouzeixHilbert.tensorDensityOperatorCompleteSpace
variable [CompleteSpace H]

theorem tensorOperator_star (A : Operator H) {m : ℕ} (B : Coeff m) :
    tensorOperator (star A) (star B) = star (tensorOperator A B) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq ((tensorOperator (star A) (star B)).continuous.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro a
  refine UniformSpace.Completion.induction_on y
    (isClosed_eq (continuous_const.inner continuous_id)
      (continuous_const.inner (tensorOperator A B).continuous)) ?_
  intro b
  simp only [tensorOperator, ContinuousLinearMap.completion_apply_coe,
    UniformSpace.Completion.inner_coe, map_star]
  induction a using TensorProduct.induction_on with
  | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
  | tmul x u =>
    induction b using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | simp
    | tmul y v => simp [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    | add b c hb hc => simp only [inner_add_right, map_add, hb, hc]
  | add a c ha hc => simp only [inner_add_left, map_add, ha, hc]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.DensityCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Density Compatibility. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Boundary

theorem integral_weightedPartialTrace {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} (E : α → Coeff n) (hE : Integrable E μ) (X Y : Coeff n) :
    (∫ t, weightedPartialTrace (E t) X Y ∂μ) =
      weightedPartialTrace (∫ t, E t ∂μ) X Y :=
  (weightedPartialTraceCLM X Y).integral_comp_comm hE

theorem densityLp_apply_ae {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) :
    densityLp E X Y =ᵐ[circleMeasure] fun t => toHS (weightedPartialTrace (E t) X Y) :=
  ContinuousMap.coeFn_toLp _ _

theorem matrixMean_densityLp {n : ℕ} (E : C(CircleSpace, Coeff n)) (X Y : Coeff n) :
    matrixMean (densityLp E X Y) = weightedPartialTrace (∫ t, E t ∂circleMeasure) X Y := by
  rw [← integral_weightedPartialTrace E
    (E.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  ext i j
  change (∫ t, densityLp E X Y t (i,j) ∂circleMeasure) = _
  have hi : Integrable (fun t => weightedPartialTrace (E t) X Y) circleMeasure :=
    (weightedPartialTraceCLM X Y).integrable_comp
      (E.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  let e : Coeff n →L[ℂ] ℂ :=
    (PiLp.proj 2 (fun _ : Fin n × Fin n => ℂ) (i,j)).comp (toHSCLM n)
  change (∫ t, densityLp E X Y t (i,j) ∂circleMeasure) =
    e (∫ t, weightedPartialTrace (E t) X Y ∂circleMeasure)
  rw [← e.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [densityLp_apply_ae E X Y] with t ht
  rw [ht]
  rfl

theorem matrixMean_densityLp_mass_one {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hmass : ∫ t, E t ∂circleMeasure = 1) (X Y : Coeff n) :
    matrixMean (densityLp E X Y) = (Xᴴ * Y)ᵀ := by
  rw [matrixMean_densityLp, hmass, weightedPartialTrace, mul_one]

theorem densityLp_block_posSemidef {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (X Y : Coeff n) :
    ∀ᵐ t ∂circleMeasure,
      (Matrix.fromBlocks (ofHS (densityLp E X X t))
        (ofHS (densityLp E X Y t))ᴴ (ofHS (densityLp E X Y t))
        (ofHS (densityLp E Y Y t))).PosSemidef := by
  filter_upwards [densityLp_apply_ae E X X, densityLp_apply_ae E Y Y,
    densityLp_apply_ae E X Y] with t hp hq hr
  simp only [hp, hq, hr, ofHS_toHS]
  have hs : (weightedPartialTrace (E t) X Y)ᴴ = weightedPartialTrace (E t) Y X := by
    simp only [weightedPartialTrace, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
      Matrix.conjTranspose_mul, (hE t).isHermitian.eq, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [hs]
  exact weightedPartialTrace_block_posSemidef (E t) (hE t) X Y

theorem densityLp_self_hermitian {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (X : Coeff n) :
    ∀ᵐ t ∂circleMeasure, (ofHS (densityLp E X X t)).IsHermitian := by
  filter_upwards [densityLp_apply_ae E X X] with t ht
  rw [ht, ofHS_toHS]
  exact ((hE t).conjTranspose_mul_mul_same X).transpose.isHermitian

end Boundary

open Boundary

theorem inner_vectorization {n : ℕ} (X Y : Coeff n) :
    ⟪vectorization X, vectorization Y⟫_ℂ = (Xᴴ * Y).trace := by
  let e : Amplification (EuclideanSpace ℂ (Fin n)) n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin n × Fin n) :=
    ⟨(matrixAmplificationCoordinates n n).toLinearMap, norm_matrixAmplificationCoordinates n n⟩
  rw [← e.inner_map_map]
  change ⟪matrixAmplificationCoordinates n n (vectorization X),
    matrixAmplificationCoordinates n n (vectorization Y)⟫_ℂ = _
  rw [vectorization_coordinates, vectorization_coordinates, inner_toHS]

theorem weightedPartialTrace_testing {n : ℕ} (E : Coeff n) (hE : E.IsHermitian)
    (X Y U : Coeff n) :
    ⟪toHS (weightedPartialTrace E X Y), toHS U⟫_ℂ =
      ⟪vectorization Y, tensorOperator (Matrix.toEuclideanCLM (𝕜 := ℂ) E) U
        (vectorization X)⟫_ℂ := by
  rw [tensorOperator_vectorization, inner_vectorization, inner_toHS]
  simp only [weightedPartialTrace, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hE.eq]
  rw [← Matrix.trace_transpose (_ * U), Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.trace_mul_comm Uᵀ]
  simp only [Matrix.mul_assoc]

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.BoundaryFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary Fibers. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

theorem matrixMean_cross_zero {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hmass : ∫ t, E t ∂circleMeasure = 1) (X Y : Coeff n) (hXY : Xᴴ * Y = 0) :
    matrixMean (densityLp E X Y) = 0 := by
  rw [matrixMean_densityLp_mass_one E hmass, hXY, Matrix.transpose_zero]

theorem trace_matrixMean_self_one {n : ℕ} (E : C(CircleSpace, Coeff n))
    (hmass : ∫ t, E t ∂circleMeasure = 1) (X : Coeff n)
    (hX : ‖vectorization X‖ = 1) :
    (matrixMean (densityLp E X X)).trace = 1 := by
  rw [matrixMean_densityLp_mass_one E hmass, Matrix.trace_transpose,
    ← inner_vectorization, inner_self_eq_norm_sq_to_K, hX]
  norm_num

end CrouzeixHilbert.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.CauchyProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cauchy Projection. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

section OperatorIntegral

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem inner_integral_operator_apply (T : α → E →L[ℂ] E)
    (hT : Integrable T μ) (x y : E) :
    ⟪y, (∫ t, T t ∂μ) x⟫_ℂ = ∫ t, ⟪y, T t x⟫_ℂ ∂μ := by
  rw [ContinuousLinearMap.integral_apply hT]
  have hf : Integrable (fun t => T t x) μ :=
    (ContinuousLinearMap.apply ℂ _ x).integrable_comp hT
  exact (integral_inner (𝕜 := ℂ) hf y).symm

end OperatorIntegral

namespace Boundary

theorem boundaryField_apply_ae {n : ℕ} (U : C(CircleSpace, Coeff n)) :
    boundaryField U =ᵐ[circleMeasure] fun t => toHS (U t) :=
  ContinuousMap.coeFn_toLp _ _

theorem integrable_tensor_field {n : ℕ} (E U : C(CircleSpace, Coeff n)) :
    Integrable (fun t => tensorOperator (matrixOperatorMap n (E t)) (U t)) circleMeasure := by
  have hc : Continuous (fun t => tensorOperator (matrixOperatorMap n (E t)) (U t)) :=
    ((tensorBilinearCLM n).continuous.comp
      ((matrixOperatorMap n).continuous.comp E.continuous)).clm_apply U.continuous
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem densityLp_inner_boundaryField {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (X Y : Coeff n) :
    ⟪densityLp E X Y, boundaryField U⟫_ℂ =
      ⟪vectorization Y, (∫ t, tensorOperator (matrixOperatorMap n (E t)) (U t)
         ∂circleMeasure) (vectorization X)⟫_ℂ := by
  rw [inner_integral_operator_apply _ (integrable_tensor_field E U), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [densityLp_apply_ae E X Y, boundaryField_apply_ae U] with t he hu
  rw [he, hu]
  exact weightedPartialTrace_testing (E t) (hE t) X Y (U t)

theorem toHS_single {n : ℕ} (i j : Fin n) :
    toHS (Matrix.single i j (1 : ℂ)) = EuclideanSpace.single (i,j) (1 : ℂ) := by
  ext ⟨a,b⟩
  change (Matrix.single i j (1 : ℂ)) a b = _
  simp only [Matrix.single_apply, PiLp.single_apply]
  by_cases hai : a = i <;> by_cases hbj : b = j <;> simp [hai, hbj, Prod.ext_iff, eq_comm]

@[simp] theorem boundaryField_matrixLaurentMonomial {n : ℕ}
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    boundaryField (matrixLaurentMonomial a c) = c • matrixFourier a := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (matrixLaurentMonomial a c),
    matrixFourier_apply_ae a, Lp.coeFn_smul c (matrixFourier a)] with t hu hf hs
  rw [hu, hs, Pi.smul_apply, hf]
  change toHS ((c * fourier a.1 t) • Matrix.single a.2.1 a.2.2 (1 : ℂ)) = _
  rw [← toHSCLM_apply, map_smul, toHSCLM_apply, toHS_single, mul_smul]

theorem boundary_real_inner_eq_re {n : ℕ} (u v : BoundaryL2 n) :
    ⟪u, v⟫_ℝ = (⟪u, v⟫_ℂ).re := boundary_real_inner u v

theorem eq_of_inner_matrixLaurentMonomial {n : ℕ} {u v : BoundaryL2 n}
    (h : ∀ (a : ℤ × (Fin n × Fin n)) (c : ℂ),
      ⟪u, boundaryField (matrixLaurentMonomial a c)⟫_ℝ =
      ⟪v, boundaryField (matrixLaurentMonomial a c)⟫_ℝ) : u = v := by
  apply (matrixFourierBasis n).repr.injective
  ext a
  simp only [HilbertBasis.repr_apply_apply, matrixFourierBasis_apply]
  rw [← inner_conj_symm (matrixFourier a) u, ← inner_conj_symm (matrixFourier a) v]
  congr 1
  apply Complex.ext
  · have hr := h a 1
    simpa only [boundaryField_matrixLaurentMonomial, one_smul,
      boundary_real_inner_eq_re] using hr
  · have hi := h a Complex.I
    simp only [boundaryField_matrixLaurentMonomial, boundary_real_inner_eq_re,
      inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub] at hi
    exact neg_injective hi

end Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.SimilarityRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Similarity Representation. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Endpoint

section Intertwining

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem intertwining_inner (S B D : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (hSB : S * B = D * S) (x y : E) (a b : ℝ) (hb : b ≠ 0)
    (hx : S x = (a : ℂ) • x) (hy : S y = (b : ℂ) • y) :
    ⟪y, B x⟫_ℂ = ((a / b : ℝ) : ℂ) * ⟪y, D x⟫_ℂ := by
  have he : (b : ℂ) * ⟪y, B x⟫_ℂ = (a : ℂ) * ⟪y, D x⟫_ℂ := by
    calc
      _ = ⟪S y, B x⟫_ℂ := by rw [hy, inner_smul_left]; simp
      _ = ⟪y, S (B x)⟫_ℂ := by
        simpa only [hS.adjoint_eq] using ContinuousLinearMap.adjoint_inner_left S (B x) y
      _ = ⟪y, D (S x)⟫_ℂ := by
        rw [← mul_apply_eq_comp, hSB, mul_apply_eq_comp]
      _ = _ := by rw [hx, map_smul, inner_smul_right]
  rw [Complex.ofReal_div, div_mul_eq_mul_div,
    eq_div_iff (by exact_mod_cast hb : (b : ℂ) ≠ 0), mul_comm]
  exact he

theorem intertwining_adjoint_inner (S B D : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (hSB : S * B = D * S) (x y : E) (a b : ℝ) (ha : a ≠ 0)
    (hx : S x = (a : ℂ) • x) (hy : S y = (b : ℂ) • y) :
    ⟪y, B.adjoint x⟫_ℂ = ((b / a : ℝ) : ℂ) * ⟪y, D.adjoint x⟫_ℂ := by
  have he := congrArg (starRingEnd ℂ) (intertwining_inner S B D hS hSB y x b a ha hy hx)
  simpa only [map_mul, inner_conj_symm, Complex.conj_ofReal,
    ContinuousLinearMap.adjoint_inner_right] using he

end Intertwining

end Endpoint

section OperatorIntegral

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem integral_operator_adjoint (T : α → V →L[ℂ] V) :
    (∫ t, T t ∂μ).adjoint = ∫ t, (T t).adjoint ∂μ := by
  simpa only [starL'_apply, ContinuousLinearMap.star_eq_adjoint] using
    ((starL' ℝ : (V →L[ℂ] V) ≃L[ℝ] (V →L[ℂ] V)).integral_comp_comm T).symm

end OperatorIntegral

namespace Boundary

@[simp] theorem boundaryField_star {n : ℕ} (U : C(CircleSpace, Coeff n)) :
    boundaryField (boundaryStar U) = lpStar (boundaryField U) := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (boundaryStar U),
    boundaryField_apply_ae U, lpStar_apply_ae (boundaryField U)] with t hs hu hl
  rw [hs, hl, hu, ofHS_toHS]
  rfl

@[simp] theorem tensorIntegral_star {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) :
    tensorIntegral E (boundaryStar U) = (tensorIntegral E U).adjoint := by
  rw [tensorIntegral, tensorIntegral, integral_operator_adjoint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change tensorOperator (matrixOperatorMap n (E t)) (U t)ᴴ =
      (tensorOperator (matrixOperatorMap n (E t)) (U t)).adjoint
    calc
      _ = tensorOperator (star (matrixOperatorMap n (E t))) (star (U t)) := by
        congr 1
        simp only [matrixOperatorMap_apply, ← map_star,
          Matrix.star_eq_conjTranspose, (hE t).eq]
      _ = star (tensorOperator (matrixOperatorMap n (E t)) (U t)) :=
        tensorOperator_star _ _
      _ = _ := ContinuousLinearMap.star_eq_adjoint _

theorem real_inner_densityLp_field {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (X Y : Coeff n) :
    ⟪densityLp E X Y, boundaryField U⟫_ℝ =
      (⟪vectorization Y, tensorIntegral E U (vectorization X)⟫_ℂ).re := by
  rw [boundary_real_inner, densityLp_inner_boundaryField E U hE]
  rfl

theorem real_inner_densityLp_star_field {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (X Y : Coeff n) :
    ⟪densityLp E X Y, lpStar (boundaryField U)⟫_ℝ =
      (⟪vectorization Y, (tensorIntegral E U).adjoint (vectorization X)⟫_ℂ).re := by
  rw [← boundaryField_star, real_inner_densityLp_field E (boundaryStar U) hE,
    tensorIntegral_star E U hE]

theorem lpStar_inner_right {n : ℕ} (u v : BoundaryL2 n) :
    ⟪u, lpStar v⟫_ℝ = ⟪lpStar u, v⟫_ℝ := by
  have h := (lpStar (k := n) (μ := circleMeasure)).inner_map_map (lpStar u) v
  simpa only [lpStar_lpStar] using h

theorem reflectedBoundaryCauchy_pairing {n : ℕ}
    (M : BoundaryL2 n →L[ℝ] BoundaryL2 n) (r u : BoundaryL2 n) :
    ⟪r, reflectedBoundaryCauchy M u⟫_ℝ =
      ⟪lpStar (boundaryCauchyAdjoint M (lpStar r)), u⟫_ℝ := by
  change ⟪r, lpStar (boundaryCauchy M (lpStar u))⟫_ℝ = _
  rw [lpStar_inner_right, ← ContinuousLinearMap.adjoint_inner_left,
    adjoint_boundaryCauchy, lpStar_inner_right]

theorem projected_density_of_laurent_testing {n : ℕ}
    (M : BoundaryL2 n →L[ℝ] BoundaryL2 n)
    (E Λ : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (hΛ : ∀ t, (Λ t).IsHermitian)
    (S : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)) (hS : IsSelfAdjoint S)
    (X Y : Coeff n) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : S (vectorization X) = (a : ℂ) • vectorization X)
    (hy : S (vectorization Y) = (b : ℂ) • vectorization Y)
    (htest : ∀ (j : ℤ × (Fin n × Fin n)) (c : ℂ),
      ∃ (V W : C(CircleSpace, Coeff n))
        (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
        boundaryCauchy M (boundaryField (matrixLaurentMonomial j c)) = boundaryField V ∧
        boundaryCauchy M (lpStar (boundaryField (matrixLaurentMonomial j c))) = boundaryField W ∧
        tensorIntegral E (matrixLaurentMonomial j c) = B + L.adjoint ∧
        S * B = tensorIntegral Λ V * S ∧ S * L = tensorIntegral Λ W * S) :
    densityLp E X Y = (a / b) • boundaryCauchyAdjoint M (densityLp Λ X Y) +
      (b / a) • lpStar (boundaryCauchyAdjoint M (lpStar (densityLp Λ X Y))) := by
  apply eq_of_inner_matrixLaurentMonomial
  intro j c
  obtain ⟨V, W, B, L, hV, hW, hR, hB, hL⟩ := htest j c
  have hB' := Endpoint.intertwining_inner S B (tensorIntegral Λ V) hS hB
    (vectorization X) (vectorization Y) a b hb hx hy
  have hL' := Endpoint.intertwining_adjoint_inner S L (tensorIntegral Λ W) hS hL
    (vectorization X) (vectorization Y) a b ha hx hy
  rw [real_inner_densityLp_field E _ hE, hR, add_apply, inner_add_right,
    hB', hL', Complex.add_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← real_inner_densityLp_field Λ V hΛ,
    ← real_inner_densityLp_star_field Λ W hΛ, ← hV, ← hW]
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_boundaryCauchy]
  have hr := reflectedBoundaryCauchy_pairing M (densityLp Λ X Y)
    (boundaryField (matrixLaurentMonomial j c))
  change ⟪densityLp Λ X Y, lpStar (boundaryCauchy M
    (lpStar (boundaryField (matrixLaurentMonomial j c))))⟫_ℝ = _ at hr
  rw [hr, inner_add_left, real_inner_smul_left, real_inner_smul_left]

end Boundary

end CrouzeixHilbert

end

end OAI
end

section
-- module Solutions.OAIQW_CrouzeixHilbert.PhysicalComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Physical Comparison. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert.Boundary

theorem endpoint_le_two_of_physical_tests_oai {n : ℕ}
    (M : BoundaryL2 n →L[ℝ] BoundaryL2 n) (hM : ‖M‖ ≤ 1)
    (E Λ F : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).PosSemidef) (hΛ : ∀ t, (Λ t).PosSemidef)
    (hmass : ∫ t, Λ t ∂circleMeasure = 1) (hF : ∀ t, ‖F t‖ ≤ 1)
    (hleft : (boundaryCauchy M).comp
        ((lpLeft F F.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M)) =
      (lpLeft F F.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M))
    (hright : (boundaryCauchy M).comp
        ((lpRight F F.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M)) =
      (lpRight F F.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hF)).comp (boundaryCauchy M))
    (S : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)) (hS : IsSelfAdjoint S)
    (X Y : Coeff n) (hX : ‖vectorization X‖ = 1) (hY : ‖vectorization Y‖ = 1)
    (hXY : Xᴴ * Y = 0) (κ : ℝ) (hκ : 0 < κ)
    (hx : S (vectorization X) = (κ : ℂ) • vectorization X)
    (hy : S (vectorization Y) = vectorization Y)
    (hI : tensorIntegral Λ F (vectorization X) = vectorization Y)
    (htest : ∀ (j : ℤ × (Fin n × Fin n)) (c : ℂ),
      ∃ (V W : C(CircleSpace, Coeff n))
        (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
        boundaryCauchy M (boundaryField (matrixLaurentMonomial j c)) = boundaryField V ∧
        boundaryCauchy M (lpStar (boundaryField (matrixLaurentMonomial j c))) =
          boundaryField W ∧
        tensorIntegral E (matrixLaurentMonomial j c) = B + L.adjoint ∧
        S * B = tensorIntegral Λ V * S ∧ S * L = tensorIntegral Λ W * S) :
    κ ≤ 2 := by
  have hy' : S (vectorization Y) = ((1 : ℝ) : ℂ) • vectorization Y := by
    simpa only [Complex.ofReal_one, one_smul] using hy
  have hP := projected_density_of_laurent_testing M E Λ
    (fun t => (hE t).isHermitian) (fun t => (hΛ t).isHermitian) S hS
    X X κ κ hκ.ne' hκ.ne' hx hx htest
  simp only [div_self hκ.ne', one_smul] at hP
  have hQ := projected_density_of_laurent_testing M E Λ
    (fun t => (hE t).isHermitian) (fun t => (hΛ t).isHermitian) S hS
    Y Y 1 1 one_ne_zero one_ne_zero hy' hy' htest
  simp only [div_one, one_smul] at hQ
  have hR := projected_density_of_laurent_testing M E Λ
    (fun t => (hE t).isHermitian) (fun t => (hΛ t).isHermitian) S hS
    X Y κ 1 hκ.ne' one_ne_zero hx hy' htest
  simp only [div_one, one_div] at hR
  have hord := densityLp_ordered Λ F hΛ hmass hF X Y (hX.trans hY.symm) hI
  refine fourier_ordered_comparison M hM F F.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hF) ?_ ?_
    (densityLp Λ X X) (densityLp Λ Y Y) (densityLp Λ X Y)
    (densityLp_self_hermitian Λ hΛ X) (densityLp_self_hermitian Λ hΛ Y)
    (hord.mono fun _ ht => ht.1) (hord.mono fun _ ht => ht.2.2)
    (matrixMean_cross_zero Λ hmass X Y hXY) ?_ κ hκ ?_
  · simpa only [adjoint_boundaryCauchyAdjoint] using hleft
  · simpa only [adjoint_boundaryCauchyAdjoint] using hright
  · rw [trace_matrixMean_self_one Λ hmass X hX, Complex.one_re]
    exact zero_lt_one
  · have hb := densityLp_block_posSemidef E hE X Y
    rw [hP, hQ, hR] at hb
    exact hb

end CrouzeixHilbert.Boundary

end

end OAI
end

theorem solution : type_of% @OAI.CrouzeixHilbert.Boundary.endpoint_le_two_of_physical_tests_oai := @OAI.CrouzeixHilbert.Boundary.endpoint_le_two_of_physical_tests_oai

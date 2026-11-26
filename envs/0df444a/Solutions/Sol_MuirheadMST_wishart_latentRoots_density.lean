-- Prove2me | solution 1 for MuirheadMST.wishart_latentRoots_density
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T20:52:39.142715+00:00
-- url     : https://prove2.me/submissions/9caca90f-2f14-46bb-89bc-7f4bad82232b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MuirheadMST_Wishart
import Theorems.Thm_MuirheadMST_latentRoots_density_of_invariant
import Theorems.Thm_MuirheadMST_wishart_density

open MeasureTheory ProbabilityTheory

open scoped Classical

noncomputable section

namespace WLRAux

open MuirheadMST

/-- The positive-definite cone is measurable (copied from the `wishart_density` solution). -/
lemma measurableSet_posDef (m : ℕ) :
    MeasurableSet {A : Fin m → Fin m → ℝ | (Matrix.of A).PosDef} := by
  have hdet : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).det :=
    continuous_id.matrix_det
  have key : {A : Fin m → Fin m → ℝ | (Matrix.of A).PosDef} =
      ({A | ∀ i j, A j i = A i j} ∩ ⋂ x : Fin m → ℝ, {A | 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of A) x)}) ∩
        {A | (Matrix.of A).det ≠ 0} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro h
      refine ⟨⟨fun i j => ?_, fun x => ?_⟩, h.det_pos.ne'⟩
      · simpa using (Matrix.IsHermitian.ext_iff.1 h.1) i j
      · simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.1 h.posSemidef).2 x
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hps : (Matrix.of A).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.2
          ⟨Matrix.IsHermitian.ext_iff.2 fun i j => by simpa using h1 i j, fun x => by simpa using h2 x⟩
      exact hps.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit h3))
  rw [key]
  refine MeasurableSet.inter (IsClosed.measurableSet ?_) (IsOpen.measurableSet ?_)
  · refine IsClosed.inter ?_ (isClosed_iInter fun x => isClosed_le continuous_const ?_)
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq (by fun_prop) (by fun_prop)
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
  · exact isOpen_ne_fun hdet continuous_const

/-- The `W_m(n, λI)` density in simplified form, with constant `K`. -/
def g (m n : ℕ) (K lam : ℝ) (A : Fin m → Fin m → ℝ) : ENNReal :=
  ENNReal.ofReal (if (Matrix.of A).PosDef then
    K * Real.exp (-(Matrix.of A).trace / (2 * lam)) * (Matrix.of A).det ^ (((n : ℝ) - m - 1) / 2)
  else 0)

lemma measurable_g (m n : ℕ) (K lam : ℝ) : Measurable (g m n K lam) := by
  have hdet : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).det :=
    continuous_id.matrix_det
  have htr : Continuous fun A : Fin m → Fin m → ℝ => (Matrix.of A).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]; fun_prop
  refine Measurable.ennreal_ofReal (Measurable.ite (measurableSet_posDef m) ?_ measurable_const)
  exact (measurable_const.mul (htr.measurable.neg.div_const _).exp).mul
    (hdet.measurable.pow_const _)

/-- Orthogonal conjugation preserves positive definiteness. -/
lemma posDef_conj {m : ℕ} {H : Matrix (Fin m) (Fin m) ℝ} (hH : H ∈ Matrix.orthogonalGroup (Fin m) ℝ)
    {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosDef) : (H * A * H.transpose).PosDef := by
  have hHt : H * H.transpose = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff _ _).1 hH
  have hinj : Function.Injective fun v => Matrix.vecMul v H := by
    intro v w hvw
    have := congrArg (fun u => Matrix.vecMul u H.transpose) hvw
    simpa [Matrix.vecMul_vecMul, hHt] using this
  simpa using hA.mul_mul_conjTranspose_same hinj

lemma g_conj (m n : ℕ) (K lam : ℝ) (H : Matrix (Fin m) (Fin m) ℝ)
    (hH : H ∈ Matrix.orthogonalGroup (Fin m) ℝ) (A : Fin m → Fin m → ℝ) :
    g m n K lam (Matrix.of.symm (H * Matrix.of A * H.transpose)) = g m n K lam A := by
  have hHt : H * H.transpose = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff _ _).1 hH
  have htH : H.transpose * H = 1 := by
    exact (Matrix.mem_orthogonalGroup_iff' _ _).1 hH
  have hHt' : H.transpose ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_transpose]; exact htH
  set B := Matrix.of A
  have hpd : (H * B * H.transpose).PosDef ↔ B.PosDef := by
    refine ⟨fun h => ?_, posDef_conj hH⟩
    have := posDef_conj hHt' h
    rwa [Matrix.transpose_transpose, ← Matrix.mul_assoc, ← Matrix.mul_assoc, htH, Matrix.one_mul,
      Matrix.mul_assoc, htH, Matrix.mul_one] at this
  have htr : (H * B * H.transpose).trace = B.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, htH, Matrix.one_mul]
  have hdet : (H * B * H.transpose).det = B.det := by
    have h1 := congrArg Matrix.det hHt
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    linear_combination B.det * h1
  simp only [g, Equiv.apply_symm_apply, hpd, htr, hdet, B]

lemma multivariateGamma_pos (m : ℕ) {a : ℝ} (ha : ((m : ℝ) - 1) / 2 < a) :
    0 < multivariateGamma m a := by
  unfold multivariateGamma
  refine mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Finset.prod_pos fun i _ => Real.Gamma_pos_of_pos ?_)
  have : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  linarith

end WLRAux

open WLRAux MuirheadMST in
theorem solution (m n : ℕ) (hmn : m ≤ n) (lam : ℝ) (hlam : 0 < lam) :
    (wishart m n (lam • (1 : Matrix (Fin m) (Fin m) ℝ))).map latentRoots =
      (volume : Measure (Fin m → ℝ)).withDensity fun l => ENNReal.ofReal
        (if StrictAnti l ∧ ∀ i, 0 < l i then
          Real.pi ^ ((m : ℝ) ^ 2 / 2) /
              ((2 * lam) ^ ((m : ℝ) * n / 2) * multivariateGamma m ((n : ℝ) / 2) *
                multivariateGamma m ((m : ℝ) / 2)) *
            Real.exp (-(∑ i, l i) / (2 * lam)) * (∏ i, l i ^ (((n : ℝ) - m - 1) / 2)) *
            vandermondeProd l
        else 0) := by
  set K : ℝ := (2 ^ ((m : ℝ) * n / 2) * multivariateGamma m ((n : ℝ) / 2) *
    lam ^ ((m : ℝ) * n / 2))⁻¹ with hK
  have hW : wishart m n (lam • (1 : Matrix (Fin m) (Fin m) ℝ)) = (symVolume m).withDensity (g m n K lam) := by
    rw [wishart_density m n hmn _ (Matrix.PosDef.one.smul hlam)]
    have hinv : (lam • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ = lam⁻¹ • 1 := by
      refine Matrix.inv_eq_left_inv ?_
      rw [smul_mul_smul_comm, inv_mul_cancel₀ hlam.ne', Matrix.one_mul, one_smul]
    have hdet : (lam • (1 : Matrix (Fin m) (Fin m) ℝ)).det ^ ((n : ℝ) / 2) =
        lam ^ ((m : ℝ) * n / 2) := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Real.rpow_natCast,
        ← Real.rpow_mul hlam.le]
      ring_nf
    congr 1
    funext A
    unfold g
    congr 1
    split_ifs
    · rw [hinv, hdet, hK, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
      ring_nf
    · rfl
  rw [hW, latentRoots_density_of_invariant m _ (measurable_g m n K lam)
    (fun A hA => by simp [g, hA]) (g_conj m n K lam)]
  congr 1
  funext l
  split_ifs with hl
  · have hd : Matrix.of (diagArray l) = Matrix.diagonal l := by
      ext i j; simp [diagArray, Matrix.diagonal_apply]
    have hpd : (Matrix.diagonal l).PosDef := Matrix.PosDef.diagonal hl.2
    have hV : 0 ≤ vandermondeProd l := by
      refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => ?_
      split_ifs with h
      · linarith [hl.1 h]
      · exact zero_le_one
    have hC : 0 ≤ Real.pi ^ ((m : ℝ) ^ 2 / 2) / multivariateGamma m ((m : ℝ) / 2) :=
      div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
        (multivariateGamma_pos m (by linarith)).le
    simp only [g, hd, if_pos hpd, Matrix.trace_diagonal, Matrix.det_diagonal]
    rw [← ENNReal.ofReal_mul (mul_nonneg hC hV), ← Real.finsetProd_rpow _ _ fun i _ => (hl.2 i).le,
      Real.mul_rpow (by norm_num) hlam.le, hK]
    ring
  · simp

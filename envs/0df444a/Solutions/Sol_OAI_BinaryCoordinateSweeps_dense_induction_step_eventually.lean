-- Prove2me | solution 1 for OAI.BinaryCoordinateSweeps.dense_induction_step_eventually
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T16:00:06.189118+00:00
-- url     : https://prove2.me/submissions/6f916ceb-2635-4c0c-895c-9f8e556e3269

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000
import Theorems.Thm_OAI_BinaryCoordinateSweeps_GridSplit_occurring_auxiliary_eventually

section
-- module Solutions.OAIB3_Bsw.Compat
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceInterpolation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma entry_norm_le (A : M ι) (i j : ι) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ ι := PiLp.single 2 j 1
  have he : ‖e‖ = 1 := by simp [e]
  have hi := PiLp.norm_apply_le ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A e) i
  have hval : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A e).ofLp i = A i j := by
    simp only [Matrix.ofLp_toEuclideanCLM, e, PiLp.ofLp_single, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply]
  rw [hval] at hi
  exact hi.trans (by simpa only [he, mul_one, ← Matrix.cstar_norm_def] using ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) A).le_opNorm e)

lemma trace_norm_le (A : M ι) : ‖Matrix.trace A‖ ≤ Fintype.card ι * ‖A‖ := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, ‖A‖ := Finset.sum_le_sum fun i _ => entry_norm_le A i i
    _ = _ := by simp

lemma prod_norm_le_one (l : List (M ι))
    (hl : ∀ a ∈ l, ‖a‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil =>
      change ‖(1 : M ι)‖ ≤ 1
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  | cons a l ih =>
      rw [List.prod_cons]
      exact (norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hl _ (by simp))).trans
          (ih (fun b hb => hl b (by simp [hb]))))

lemma diagPower_add (d : ι → ℝ) (z w : ℂ) :
    diagPower d (z+w) = diagPower d z * diagPower d w := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagPower, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
    split_ifs <;> simp [add_mul, Complex.exp_add]
  · simp [diagPower, Matrix.diagonal_apply_ne _ hij]

lemma diagPower_norm_le_one (d : ι → ℝ) (hd0 : ∀ i, 0 ≤ d i) (hd : ∀ i, d i ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖diagPower d z‖ ≤ 1 := by
  rw [diagPower, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs with hi
  · simp
  · rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hz (Real.log_nonpos (hd0 i) (hd i))

lemma diagPower_imag_norm_le_one (d : ι → ℝ) (t : ℝ) :
    ‖diagPower d ((t : ℂ) * Complex.I)‖ ≤ 1 := by
  rw [diagPower, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  split_ifs <;> simp [Complex.norm_exp, Complex.mul_re]

omit [Fintype ι] in
lemma diagPower_one (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    diagPower d 1 = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [diagPower, Matrix.diagonal_apply_eq, one_mul]
    by_cases hi : d i = 0
    · simp [hi]
    · rw [ite_eq_right hi, ← Complex.ofReal_exp, Real.exp_log (lt_of_le_of_ne (hd i) (Ne.symm hi))]
  · simp [diagPower, Matrix.diagonal_apply_ne _ hij]

lemma differentiable_diagPower (d : ι → ℝ) : Differentiable ℂ (diagPower d) := by
  let L := (Matrix.diagonalLinearMap ι ℂ ℂ).toContinuousLinearMap
  change Differentiable ℂ (fun z => L (fun i => if d i = 0 then 0 else
    Complex.exp (z * (Real.log (d i) : ℂ))))
  apply L.differentiable.comp
  apply differentiable_pi.mpr
  intro i
  by_cases hi : d i = 0
  · simp [hi]
  · simp only [hi, ite_false]
    exact Complex.differentiable_exp.comp (differentiable_id.mul_const _)

lemma word_norm_le_one {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ) (hA : ∀ j, ‖A j‖ ≤ 1) (hd0 : ∀ j i, 0 ≤ d j i) (hd : ∀ j i, d j i ≤ 1)
    (hx : ∀ j, 0 ≤ (x j).re) : ‖word A d x‖ ≤ 1 := by
  apply prod_norm_le_one
  intro B hB
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hB
  exact (norm_mul_le _ _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (hA j)).trans
      (diagPower_norm_le_one (d j) (hd0 j) (hd j) (hx j)))

lemma differentiable_word {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ → ℂ) (hx : ∀ j, Differentiable ℂ (x j)) :
    Differentiable ℂ (fun z => word A d (fun j => x j z)) := by
  induction m with
  | zero => simp [word]
  | succ m ih =>
      simp only [word, List.ofFn_succ, List.prod_cons]
      apply Differentiable.mul
      · have h₀ : Differentiable ℂ (fun z => diagPower (d 0) (x 0 z)) :=
          (differentiable_diagPower (d 0)).comp (hx 0)
        exact (differentiable_const (A 0)).mul h₀
      · exact ih (fun j => A j.succ) (fun j => d j.succ) (fun j => x j.succ)
          (fun j => hx j.succ)

lemma differentiable_traceWord {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ → ℂ) (hx : ∀ j, Differentiable ℂ (x j)) :
    Differentiable ℂ (fun z => traceWord A d (fun j => x j z)) := by
  exact (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.differentiable.comp
    (differentiable_word A d x hx)

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma star_diagReal (s : ι → ℝ) : star (diagReal s) = diagReal s := by
  simp [diagReal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]

lemma diagReal_mul (s t : ι → ℝ) : diagReal s * diagReal t = diagReal (fun i => s i*t i) := by
  simp [diagReal, Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

omit [DecidableEq ι] in
lemma gram_product (X Y : M ι) :
    star (X*Y) * (X*Y) = star Y * (star X * X) * Y := by
  simp only [star_mul, mul_assoc]

lemma gram_diagonal_factor (X : M ι) (s : ι → ℝ)
    (hX : star X * X = diagReal (fun i => s i ^ 2)) :
    ∃ U : M ι, ‖U‖ ≤ 1 ∧ X = U * diagReal s := by
  let t : ι → ℝ := fun i => (s i)⁻¹
  let U := X * diagReal t
  have hU : star U * U = diagReal (fun i => if s i = 0 then 0 else 1) := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    congr 1
    funext i
    dsimp [t]
    split_ifs with hi
    · simp [hi]
    · field_simp
  have hUnorm : ‖U‖ ≤ 1 := by
    have h : ‖star U * U‖ ≤ 1 := by
      rw [hU, diagReal, Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
      intro i
      split_ifs <;> norm_num
    rw [CStarRing.norm_star_mul_self] at h
    nlinarith [norm_nonneg U]
  let w : ι → ℝ := fun i => 1 - t i * s i
  have hz : star (X * diagReal w) * (X * diagReal w) = 0 := by
    rw [gram_product, hX, star_diagReal, diagReal_mul, diagReal_mul]
    have hw : (fun i => (w i * s i ^ 2) * w i) = 0 := by
      funext i
      dsimp [w, t]
      by_cases hi : s i = 0 <;> simp [hi]
    rw [hw]
    simp [diagReal]
  have hzero : X * diagReal w = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  have hw : diagReal w = 1 - diagReal t * diagReal s := by
    rw [diagReal_mul]
    dsimp [diagReal, w]
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    simp
  rw [hw, mul_sub, mul_one] at hzero
  refine ⟨U, hUnorm, ?_⟩
  exact (sub_eq_zero.mp hzero).trans (mul_assoc _ _ _).symm

theorem exists_partial_svd (A : M ι) :
    ∃ (U : M ι) (V : Matrix.unitaryGroup ι ℂ) (s : ι → ℝ),
      (∀ i, 0 ≤ s i) ∧ ‖U‖ ≤ 1 ∧
      A = U * diagReal s * star (V : M ι) ∧
      star A * A = (V : M ι) * diagReal (fun i => s i ^ 2) * star (V : M ι) := by
  let h := Matrix.isHermitian_conjTranspose_mul_self A
  let V := h.eigenvectorUnitary
  let s : ι → ℝ := fun i => Real.sqrt (h.eigenvalues i)
  have hs0 : ∀ i, 0 ≤ s i := fun i => Real.sqrt_nonneg _
  have hs : ∀ i, s i ^ 2 = h.eigenvalues i := fun i =>
    Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)
  have hdiag : star (V : M ι) * (star A * A) * (V : M ι) =
      diagReal (fun i => s i ^ 2) := by
    simpa only [V, s, hs, diagReal, Matrix.star_eq_conjTranspose, Function.comp_def,
      Unitary.conjStarAlgAut_star_apply] using! h.conjStarAlgAut_star_eigenvectorUnitary
  have hgram : star (A * (V : M ι)) * (A * (V : M ι)) =
      diagReal (fun i => s i ^ 2) := by rw [gram_product, hdiag]
  obtain ⟨U, hU, heq⟩ := gram_diagonal_factor (A * (V : M ι)) s hgram
  have hVV : (V : M ι) * star (V : M ι) = 1 := by
    simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self V
  refine ⟨U, V, s, hs0, hU, ?_, ?_⟩
  · have heq' := congrArg (fun X => X * star (V : M ι)) heq
    simpa only [mul_assoc, hVV, mul_one] using heq'
  · calc
      star A * A = ((V : M ι) * star (V : M ι)) * (star A * A) *
          ((V : M ι) * star (V : M ι)) := by rw [hVV, one_mul, mul_one]
      _ = (V : M ι) * (star (V : M ι) * (star A * A) * (V : M ι)) *
          star (V : M ι) := by simp only [mul_assoc]
      _ = _ := by rw [hdiag]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SpectralMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma diagReal_pow (s : ι → ℝ) (q : ℕ) :
    (diagReal s)^q = diagReal (fun i => s i ^ q) := by
  simp [diagReal, Matrix.diagonal_pow]

lemma trace_unitary_conj (V : Matrix.unitaryGroup ι ℂ) (B : M ι) :
    Matrix.trace ((V : M ι) * B * star (V : M ι)) = Matrix.trace B := by
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

lemma unitary_conj_pow (V : Matrix.unitaryGroup ι ℂ) (B : M ι) (q : ℕ) :
    ((V : M ι) * B * star (V : M ι))^q = (V : M ι) * B^q * star (V : M ι) := by
  have h := ((Unitary.conjStarAlgAut ℂ (M ι) V).toAlgEquiv.map_pow B q).symm
  change (Unitary.conjStarAlgAut ℂ (M ι) V B)^q =
    Unitary.conjStarAlgAut ℂ (M ι) V (B^q) at h
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star] using h

lemma matrixMoment_of_svd (A : M ι) (q : ℕ) (V : Matrix.unitaryGroup ι ℂ)
    (s : ι → ℝ) (hgram : star A * A = (V : M ι) * diagReal (fun i => s i^2) * star (V : M ι)) :
    matrixMoment q A = ∑ i, s i ^ (2*q) := by
  rw [matrixMoment, hgram, unitary_conj_pow, trace_unitary_conj, diagReal_pow]
  simp only [diagReal, Matrix.trace_diagonal,
    Complex.re_sum, Complex.ofReal_re, ← pow_mul]

lemma matrixMoment_nonneg (q : ℕ) (A : M ι) : 0 ≤ matrixMoment q A := by
  obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  rw [matrixMoment_of_svd A q V s hg]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (hs i) _)

lemma matrixMoment_eq_zero_iff {q : ℕ} (hq : 0 < q) (A : M ι) :
    matrixMoment q A = 0 ↔ A = 0 := by
  constructor
  · intro h
    obtain ⟨U, V, s, hs, hU, hA, hg⟩ := exists_partial_svd A
    rw [matrixMoment_of_svd A q V s hg] at h
    have hi : ∀ i, s i = 0 := by
      intro i
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => pow_nonneg (hs j) (2*q))).mp h
      exact (pow_eq_zero_iff (by omega : 2*q ≠ 0)).mp (hz i (Finset.mem_univ _))
    rw [hA]
    simp [diagReal, hi]
  · intro h
    simp [matrixMoment, h, zero_pow (by omega : q ≠ 0)]

lemma unitary_norm_le_one (V : Matrix.unitaryGroup ι ℂ) : ‖(V : M ι)‖ ≤ 1 := by
  have h1 : ‖(1 : M ι)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by simp)
  have h : ‖(V : M ι)‖ * ‖(V : M ι)‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, Unitary.coe_star_mul_self]
    exact h1
  nlinarith [norm_nonneg (V : M ι)]

omit [Fintype ι] in
lemma diagPower_real (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) {x : ℝ} (hx : 0 < x) :
    diagPower d (x : ℂ) = diagReal (fun i => (d i) ^ x) := by
  unfold diagPower diagReal
  congr 1
  funext i
  by_cases hi : d i = 0
  · simp [hi, Real.zero_rpow hx.ne']
  · rw [ite_eq_right hi]
    change Complex.exp ((x : ℂ) * (Real.log (d i) : ℂ)) = ((d i ^ x : ℝ) : ℂ)
    rw [Real.rpow_def_of_pos (lt_of_le_of_ne (hd i) (Ne.symm hi))]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
    congr 2
    ring

lemma density_normalization {m : ℕ} (hm : 0 < m) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    {t : ℝ} (ht : 0 < t) (hts : ∑ i, s i^m = t) :
    let d : ι → ℝ := fun i => s i ^ m / t
    (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
    diagReal s = (t ^ ((m : ℝ)⁻¹) : ℝ) • diagPower d (((m : ℝ)⁻¹ : ℝ) : ℂ) := by
  dsimp only
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : ∀ i, 0 ≤ s i^m/t := fun i => div_nonneg (pow_nonneg (hs i) _) ht.le
  refine ⟨hd, ?_, ?_⟩
  · rw [← Finset.sum_div, hts, div_self ht.ne']
  · rw [diagPower_real _ hd (inv_pos.mpr hm')]
    unfold diagReal
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    change (s i : ℂ) = ((t ^ (m : ℝ)⁻¹ : ℝ) : ℂ) *
      (((s i ^ m / t) ^ (m : ℝ)⁻¹ : ℝ) : ℂ)
    rw [Real.div_rpow (pow_nonneg (hs i) _) ht.le,
      Real.pow_rpow_inv_natCast (hs i) (Nat.ne_of_gt hm)]
    norm_cast
    exact (mul_div_cancel₀ (s i) (Real.rpow_pos_of_pos ht _).ne').symm

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceConvex
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Matrix.Norms.L2Operator
open Complex

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_diagonal_le (A : M ι) (d : ι → ℝ)
    (hA : ‖A‖ ≤ 1) (hd : ∀ i, 0 ≤ d i) :
    ‖Matrix.trace (A * Matrix.diagonal (fun i => (d i : ℂ)))‖ ≤ ∑ i, d i := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_diagonal]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hd i)]
  exact mul_le_of_le_one_left (hd i) ((entry_norm_le A i i).trans hA)

lemma trace_prod_density_le (L : List (M ι)) (A : M ι) (d : ι → ℝ)
    (hL : ∀ B ∈ L, ‖B‖ ≤ 1) (hA : ‖A‖ ≤ 1) (hd : ∀ i, 0 ≤ d i)
    (hmem : A * Matrix.diagonal (fun i => (d i : ℂ)) ∈ L) :
    ‖Matrix.trace L.prod‖ ≤ ∑ i, d i := by
  obtain ⟨l, r, rfl⟩ := List.mem_iff_append.mp hmem
  have hl : ‖l.prod‖ ≤ 1 := prod_norm_le_one l (fun B hB => hL B (by simp [hB]))
  have hr : ‖r.prod‖ ≤ 1 := prod_norm_le_one r (fun B hB => hL B (by simp [hB]))
  simp only [List.prod_append, List.prod_cons]
  rw [← mul_assoc, Matrix.trace_mul_cycle]
  rw [← mul_assoc]
  apply trace_mul_diagonal_le _ d _ hd
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
    ((norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hr).trans hl))).trans hA)

lemma word_absorb_phase {m : ℕ} (A : Fin m → M ι) (d : Fin m → ι → ℝ)
    (x : Fin m → ℂ) :
    word A d x = word (fun j => A j * diagPower (d j) ((x j).im * I)) d
      (fun j => ((x j).re : ℂ)) := by
  unfold word
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  have hx : x j = ((x j).im : ℂ) * I + ((x j).re : ℂ) := by
    rw [add_comm]; exact (Complex.re_add_im (x j)).symm
  calc
    A j * diagPower (d j) (x j) = A j *
        diagPower (d j) (((x j).im : ℂ) * I + ((x j).re : ℂ)) := by rw [← hx]
    _ = _ := by rw [diagPower_add, mul_assoc]

lemma admissible_complex {m : ℕ} (d : Fin m → ι → ℝ) (x : Fin m → ℝ)
    (hx : Admissible d x) (A : Fin m → M ι) (hA : ∀ j, ‖A j‖ ≤ 1)
    (z : Fin m → ℂ) (hz : ∀ j, (z j).re = x j) : ‖traceWord A d z‖ ≤ 1 := by
  unfold traceWord
  rw [word_absorb_phase]
  simp only [hz]
  apply hx
  intro j
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hA j)).trans
    (diagPower_imag_norm_le_one _ _))

lemma vertex_mem_exponentSet {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1) (j : Fin m) :
    Pi.single j 1 ∈ exponentSet d := by
  have hd1 : ∀ j i, d j i ≤ 1 := by
    intro j i
    rw [← hs j]
    exact Finset.single_le_sum (fun i _ => hd j i) (Finset.mem_univ i)
  constructor
  · intro i; simp only [Pi.single_apply]; split_ifs <;> norm_num
  · intro A hA
    have hv0 : ∀ i : Fin m, 0 ≤ (((Pi.single j 1 : Fin m → ℝ) i) : ℂ).re := by
      intro i; simp only [ofReal_re, Pi.single_apply]; split_ifs <;> norm_num
    have hmem : A j * Matrix.diagonal (fun i => (d j i : ℂ)) ∈
        List.ofFn (fun k => A k * diagPower (d k) (((Pi.single j 1 : Fin m → ℝ) k) : ℂ)) := by
      apply List.mem_ofFn.mpr
      refine ⟨j, ?_⟩
      simp [diagPower_one _ (hd j)]
    have hlist : ∀ B ∈ List.ofFn (fun k => A k *
        diagPower (d k) (((Pi.single j 1 : Fin m → ℝ) k) : ℂ)), ‖B‖ ≤ 1 := by
      intro B hB
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hB
      exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hA k)).trans
        (diagPower_norm_le_one _ (hd k) (hd1 k) (hv0 k)))
    unfold traceWord word
    exact (trace_prod_density_le _ _ (d j) hlist (hA j) (hd j) hmem).trans_eq (hs j)

lemma convex_exponentSet {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hd1 : ∀ j i, d j i ≤ 1) :
    Convex ℝ (exponentSet d) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hb (hy.1 j))
  · intro A hA
    let e (j : Fin m) (z : ℂ) := (1-z) * (x j : ℂ) + z * (y j : ℂ)
    let f (z : ℂ) := traceWord A d (fun j => e j z)
    have he : ∀ j, Differentiable ℂ (e j) := fun j =>
      (((differentiable_const (1 : ℂ)).sub differentiable_id).mul_const _).add
        (differentiable_id.mul_const _)
    have hf : Differentiable ℂ f := differentiable_traceWord A d e he
    have hre (j : Fin m) (z : ℂ) : (e j z).re = (1-z.re)*x j + z.re*y j := by
      simp [e, Complex.mul_re]
    have hbound : BddAbove ((norm ∘ f) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
      refine ⟨Fintype.card ι, ?_⟩
      rintro t ⟨z, hz, rfl⟩
      have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := hz
      have hw : ‖word A d (fun j => e j z)‖ ≤ 1 :=
        word_norm_le_one A d _ hA hd hd1 (fun j => by
          rw [hre]
          exact add_nonneg (mul_nonneg (sub_nonneg.mpr hz'.2) (hx.1 j))
            (mul_nonneg hz'.1 (hy.1 j)))
      exact (trace_norm_le _).trans (mul_le_of_le_one_right (Nat.cast_nonneg _) hw)
    have hleft : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖f z‖ ≤ 1 := by
      intro z hz
      have hz' : z.re = 0 := hz
      exact admissible_complex d x hx.2 A hA _ (fun j => by rw [hre, hz']; ring)
    have hright : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖f z‖ ≤ 1 := by
      intro z hz
      have hz' : z.re = 1 := hz
      exact admissible_complex d y hy.2 A hA _ (fun j => by rw [hre, hz']; ring)
    have hb1 : b ≤ 1 := by linarith
    have hbi : (b : ℂ) ∈ HadamardThreeLines.verticalClosedStrip 0 1 := ⟨hb, hb1⟩
    have hthree := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      f hbi hf.diffContOnCl hbound hleft hright
    have heval : f (b : ℂ) = traceWord A d (fun j => ((a • x + b • y) j : ℂ)) := by
      change traceWord A d (fun j => e j (b : ℂ)) = _
      apply congrArg (traceWord A d)
      funext j
      dsimp only [e]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add,
        Complex.ofReal_mul]
      have ha' : (a : ℂ) = 1 - (b : ℂ) := by exact_mod_cast (show a = 1-b by linarith)
      rw [ha']
    simpa [heval] using hthree

theorem trace_diagonal_simplex {m : ℕ} (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (A : Fin m → M ι) (hA : ∀ j, ‖A j‖ ≤ 1) :
    ‖traceWord A d (fun j => (x j : ℂ))‖ ≤ 1 := by
  have hd1 : ∀ j i, d j i ≤ 1 := by
    intro j i
    rw [← hs j]
    exact Finset.single_le_sum (fun i _ => hd j i) (Finset.mem_univ i)
  have hc := convex_exponentSet d hd hd1
  have hsum := hc.sum_mem (t := Finset.univ) (w := x) (z := fun j => Pi.single j (1 : ℝ))
    (fun j _ => hx j) hsx (fun j _ => vertex_mem_exponentSet d hd hs j)
  have heq : ∑ j, x j • Pi.single j (1 : ℝ) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [heq] at hsum
  exact hsum.2 A hA

end BinaryCoordinateSweeps.TraceHolder

end

open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma prod_sandwich_succ {α : Type*} [Monoid α] (n : ℕ)
    (U D V : Fin (n+1) → α) :
    (List.ofFn (fun j => U j * D j * V j)).prod =
      U 0 * D 0 * (List.ofFn (fun j : Fin n =>
        (V j.castSucc * U j.succ) * D j.succ)).prod * V (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      rw [ih (fun j => U j.succ) (fun j => D j.succ) (fun j => V j.succ)]
      simp only [List.ofFn_succ, List.prod_cons, Fin.castSucc_zero, Fin.succ_zero_eq_one,
        Fin.succ_last, Fin.castSucc_succ]
      simp only [mul_assoc]

lemma trace_prod_sandwich {n : ℕ} (U D V : Fin (n+1) → M ι) :
    Matrix.trace (List.ofFn (fun j => U j * D j * V j)).prod =
      Matrix.trace (List.ofFn (Fin.cons (V (Fin.last n) * U 0 * D 0)
        (fun j : Fin n => (V j.castSucc * U j.succ) * D j.succ))).prod := by
  rw [prod_sandwich_succ, List.ofFn_succ, List.prod_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.trace_mul_comm]
  congr 1
  simp only [mul_assoc]

theorem trace_diagonal_sandwich {n : ℕ} (d : Fin (n+1) → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin (n+1) → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (U V : Fin (n+1) → M ι) (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod‖ ≤ 1 := by
  let A : Fin (n+1) → M ι := Fin.cons (V (Fin.last n) * U 0)
    (fun j : Fin n => V j.castSucc * U j.succ)
  have hA : ∀ j, ‖A j‖ ≤ 1 := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hV _)).trans (hU _))
    · exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) (hV _)).trans (hU _))
  have heq : Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod =
      traceWord A d (fun j => (x j : ℂ)) := by
    rw [trace_prod_sandwich]
    unfold traceWord word
    congr 2
    apply List.ofFn_inj.mpr
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  rw [heq]
  exact trace_diagonal_simplex d hd hs x hx hsx A hA

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_TraceHolder
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma normalized_svd {q : ℕ} (hq : 0 < q) (A : M ι) (ht : 0 < matrixMoment q A) :
    ∃ (U V : M ι) (d : ι → ℝ), ‖U‖ ≤ 1 ∧ ‖V‖ ≤ 1 ∧
      (∀ i, 0 ≤ d i) ∧ (∑ i, d i = 1) ∧
      A = (matrixMoment q A ^ ((2*q : ℕ) : ℝ)⁻¹ : ℝ) •
        (U * diagPower d ((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * V) := by
  obtain ⟨U, W, s, hs, hU, hA, hg⟩ := exists_partial_svd A
  have hsum := matrixMoment_of_svd A q W s hg
  obtain ⟨hd, hsumd, heq⟩ := density_normalization (by omega : 0 < 2*q) s hs ht hsum.symm
  refine ⟨U, star (W : M ι), fun i => s i ^ (2*q) / matrixMoment q A,
    hU, ?_, hd, hsumd, ?_⟩
  · simpa only [norm_star] using unitary_norm_le_one W
  · conv_lhs => rw [hA, heq]
    simp only [mul_smul_comm, smul_mul_assoc]

lemma prod_ofFn_smul {m : ℕ} (r : Fin m → ℝ) (A : Fin m → M ι) :
    (List.ofFn (fun j => r j • A j)).prod = (∏ j, r j) • (List.ofFn A).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      rw [ih]
      rw [smul_mul_smul_comm]

lemma trace_diagonal_sandwich_pos {m : ℕ} (hm : 0 < m) (d : Fin m → ι → ℝ)
    (hd : ∀ j i, 0 ≤ d j i) (hs : ∀ j, ∑ i, d j i = 1)
    (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j) (hsx : ∑ j, x j = 1)
    (U V : Fin m → M ι) (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => U j * diagPower (d j) (x j : ℂ) * V j)).prod‖ ≤ 1 := by
  cases m with
  | zero => omega
  | succ n => exact trace_diagonal_sandwich d hd hs x hx hsx U V hU hV

theorem matrix_trace_holder {q : ℕ} (hq : 0 < q) (A : Fin (2*q) → M ι) :
    ‖Matrix.trace (List.ofFn A).prod‖ ≤
      ∏ j, matrixMoment q (A j) ^ (((2*q : ℕ) : ℝ)⁻¹) := by
  classical
  have hm : 0 < 2*q := by omega
  have hm' : 0 < ((2*q : ℕ) : ℝ) := by exact_mod_cast hm
  by_cases hzero : ∃ j, matrixMoment q (A j) = 0
  · obtain ⟨j, hj⟩ := hzero
    have hAj : A j = 0 := (matrixMoment_eq_zero_iff hq (A j)).mp hj
    have hp : (List.ofFn A).prod = 0 := List.prod_eq_zero (List.mem_ofFn.mpr ⟨j, hAj⟩)
    rw [hp, Matrix.trace_zero, norm_zero]
    exact Finset.prod_nonneg (fun k _ => Real.rpow_nonneg (matrixMoment_nonneg _ _) _)
  · have ht : ∀ j, 0 < matrixMoment q (A j) := by
      intro j
      exact lt_of_le_of_ne (matrixMoment_nonneg _ _) (Ne.symm (fun h => hzero ⟨j, h⟩))
    choose U V d hU hV hd hs heq using fun j => normalized_svd hq (A j) (ht j)
    let r : Fin (2*q) → ℝ := fun j => matrixMoment q (A j) ^ (((2*q : ℕ) : ℝ)⁻¹)
    let B : Fin (2*q) → M ι := fun j =>
      U j * diagPower (d j) (((((2*q : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) * V j
    have hb : ‖Matrix.trace (List.ofFn B).prod‖ ≤ 1 := by
      apply trace_diagonal_sandwich_pos hm d hd hs (fun _ => ((2*q : ℕ) : ℝ)⁻¹)
        (fun _ => (inv_pos.mpr hm').le) _ U V hU hV
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ hm'.ne'
    have hEq : A = fun j => r j • B j := funext heq
    conv_lhs => rw [hEq, prod_ofFn_smul, Matrix.trace_smul, norm_smul]
    have hr : 0 ≤ ∏ j, r j := Finset.prod_nonneg fun j _ => Real.rpow_nonneg (ht j).le _
    rw [Real.norm_eq_abs, abs_of_nonneg hr]
    exact mul_le_of_le_one_right hr hb

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_mul_pow_comm (A B : M ι) (q : ℕ) :
    Matrix.trace ((A * B)^q) = Matrix.trace ((B * A)^q) := by
  cases q with
  | zero => rfl
  | succ q =>
      rw [pow_succ, ← mul_assoc, mul_pow_mul, Matrix.trace_mul_comm,
        ← mul_assoc, ← pow_succ']

lemma matrixMoment_star (q : ℕ) (A : M ι) :
    matrixMoment q (star A) = matrixMoment q A := by
  simp only [matrixMoment, star_star]
  rw [trace_mul_pow_comm]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_SchattenBasic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma alternating_prod {R : Type*} [Monoid R] (q : ℕ) (x y : R) :
    (List.ofFn (fun i : Fin (2*q) => if i.val%2=0 then x else y)).prod=(x*y)^q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 2*(q+1)=2*q+1+1 by omega]
    simp only [List.ofFn_succ,List.prod_cons,Fin.val_zero,Fin.val_succ]
    norm_num only [Nat.zero_mod,Nat.reduceMod,ite_eq_left,ite_eq_right]
    have he (i : Fin (2*q)) : (i.val+1+1)%2=i.val%2 := by omega
    simp_rw [he]
    rw [ih,pow_succ']
    exact (mul_assoc _ _ _).symm

lemma matrixMoment_smul (q : ℕ) (r : ℝ) (A : M ι) :
    matrixMoment q (r • A)=r^(2*q)*matrixMoment q A := by
  unfold matrixMoment
  rw [star_smul,star_trivial,smul_mul_smul_comm,smul_pow,Matrix.trace_smul]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [← pow_two,← pow_mul]

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_PositiveTraceRestriction
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

lemma positive_pow {B : W →ₗ[ℂ] W} (hB : B.IsPositive) (q : ℕ) : (B^q).IsPositive :=
  match q with
  | 0 => LinearMap.isPositive_one
  | 1 => by simpa using hB
  | n+2 => by
    rw [pow_succ,pow_succ']
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hB.adjoint_eq] using (positive_pow hB n).conj_adjoint B

theorem positive_trace_restrict_le (S : Submodule ℂ W) (B : W →ₗ[ℂ] W)
    (hB : B.IsPositive) (hS : ∀ x ∈ S, B x ∈ S) :
    (LinearMap.trace ℂ S (B.restrict hS)).re ≤ (LinearMap.trace ℂ W B).re := by
  let P := S.starProjection.toLinearMap
  let Q : W →ₗ[ℂ] W := 1-P
  have hPsy : P.IsSymmetric := (Submodule.isSymmetricProjection_starProjection S).isSymmetric
  have hQsy : Q.IsSymmetric := LinearMap.IsSymmetric.id.sub hPsy
  have hPP : P*P = P := by
    ext x
    exact congrArg (fun t : W →L[ℂ] W => t x) S.isIdempotentElem_starProjection
  have hQQ : Q*Q = Q := by
    dsimp [Q]
    noncomm_ring [hPP]
  have hQBQ : (Q*B*Q).IsPositive := by
    simpa only [Module.End.mul_eq_comp,LinearMap.comp_assoc,hQsy.adjoint_eq] using hB.conj_adjoint Q
  have hpRange : ∀ x, ((P*B)*P) x ∈ S := by
    intro x
    exact S.starProjection_apply_mem _
  have hpRestr : ((P*B)*P).restrict (fun x _ => hpRange x) = B.restrict hS := by
    ext x
    change P (B (P x.val)) = B x.val
    rw [show P x.val = x.val from Submodule.starProjection_eq_self_iff.mpr x.property]
    exact Submodule.starProjection_eq_self_iff.mpr (hS x.val x.property)
  have hTrP : LinearMap.trace ℂ W (P*B*P) = LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (P.comp (B*P)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*P*P) = _
    rw [mul_assoc,hPP]
  have hTrQ : LinearMap.trace ℂ W (Q*B*Q) = LinearMap.trace ℂ W B -
      LinearMap.trace ℂ W (B*P) := by
    change LinearMap.trace ℂ W (Q.comp (B*Q)) = _
    rw [LinearMap.trace_comp_comm']
    change LinearMap.trace ℂ W (B*Q*Q) = _
    rw [mul_assoc,hQQ]
    dsimp [Q]
    rw [mul_sub,mul_one,map_sub]
  have hTrace := LinearMap.trace_restrict_eq_of_forall_mem S (P*B*P) hpRange
  rw [hpRestr,hTrP] at hTrace
  have hn := (Complex.nonneg_iff.mp hQBQ.trace_nonneg).1
  rw [hTrQ,Complex.sub_re,← hTrace] at hn
  linarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicTrace
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible]

theorem isotypic_trace (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (hAB : ∀ f : IntertwiningMap ρ σ, ∀ v : V, B (f v) = f (A v)) :
    LinearMap.trace ℂ (isotypicSpan ρ σ)
      (B.restrict (isotypic_invariant_of_compatible ρ σ A B hAB)) =
    (Module.finrank ℂ (IntertwiningMap ρ σ) : ℂ) * LinearMap.trace ℂ V A := by
  let e := evaluationEquiv ρ σ
  let C := B.restrict (isotypic_invariant_of_compatible ρ σ A B hAB)
  have he : e.symm.conj C = TensorProduct.map A (LinearMap.id :
      IntertwiningMap ρ σ →ₗ[ℂ] IntertwiningMap ρ σ) := by
    apply TensorProduct.ext'
    intro v f
    apply e.injective
    change e (e.symm (C (e (v ⊗ₜ[ℂ] f)))) = e (A v ⊗ₜ[ℂ] f)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hAB f v
  have ht := LinearMap.trace_conj' C e.symm
  rw [he,LinearMap.trace_tensorProduct',LinearMap.trace_id] at ht
  exact ht.symm.trans (mul_comm _ _)

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IsotypicMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma average_compatible (p : G → ℂ) (f : IntertwiningMap ρ σ) (v : V) :
    groupAverage σ p (f v) = f (groupAverage ρ p v) := by
  simp only [groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    IntertwiningMap.isIntertwining]

lemma adjoint_average_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (f : IntertwiningMap ρ σ) (v : V) :
    (groupAverage σ p).adjoint (f v) = f ((groupAverage ρ p).adjoint v) := by
  simp only [groupAverage,map_sum,map_smulₛₗ,unitary_rep_adjoint ρ hρ,
    unitary_rep_adjoint σ hσ,LinearMap.sum_apply,LinearMap.smul_apply,
    IntertwiningMap.isIntertwining, RingHom.id_apply]

lemma even_compatible (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (q : ℕ) (f : IntertwiningMap ρ σ) (v : V) :
    (((groupAverage σ p).adjoint * groupAverage σ p)^q) (f v) =
      f ((((groupAverage ρ p).adjoint * groupAverage ρ p)^q) v) := by
  induction q generalizing v with
  | zero => simp
  | succ q ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,ih]
    rw [Module.End.mul_apply,average_compatible,adjoint_average_compatible ρ σ p hρ hσ]
    rfl

theorem multiplicity_moment_le [ρ.IsIrreducible] (p : G → ℂ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖) (q : ℕ) :
    (Module.finrank ℂ (IntertwiningMap ρ σ) : ℝ) * evenMoment q (groupAverage ρ p) ≤
      evenMoment q (groupAverage σ p) := by
  let A := ((groupAverage ρ p).adjoint * groupAverage ρ p)^q
  let B := ((groupAverage σ p).adjoint * groupAverage σ p)^q
  have hAB := even_compatible ρ σ p hρ hσ q
  have hBp : B.IsPositive := positive_pow (LinearMap.isPositive_adjoint_comp_self _) q
  have hle := positive_trace_restrict_le (isotypicSpan ρ σ) B hBp
    (isotypic_invariant_of_compatible ρ σ A B hAB)
  rw [isotypic_trace ρ σ A B hAB] at hle
  simpa only [A, B, evenMoment, Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] using hle

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_LinearEvenMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [Fintype ι] [DecidableEq ι]

lemma trace_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (A : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V A = Matrix.trace (LinearMap.toMatrixOrthonormal v A) :=
  LinearMap.trace_eq_matrix_trace ℂ v.toBasis A

lemma evenMoment_orthonormalMatrix (v : OrthonormalBasis ι ℂ V) (q : ℕ) (A : V →ₗ[ℂ] V) :
    evenMoment q A=matrixMoment q (LinearMap.toMatrixOrthonormal v A) := by
  unfold evenMoment matrixMoment
  rw [trace_orthonormalMatrix v]
  simp only [map_pow,map_mul,← LinearMap.star_eq_adjoint,map_star]

lemma evenMoment_nonneg (q : ℕ) (A : V →ₗ[ℂ] V) : 0≤evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  exact matrixMoment_nonneg _ _

lemma evenMoment_adjoint (q : ℕ) (A : V →ₗ[ℂ] V) : evenMoment q A.adjoint=evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V),
    evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  rw [← LinearMap.star_eq_adjoint,map_star]
  exact matrixMoment_star q _

lemma evenMoment_smul (q : ℕ) (r : ℝ) (A : V →ₗ[ℂ] V) :
    evenMoment q (r • A)=r^(2*q)*evenMoment q A := by
  rw [evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V),
    evenMoment_orthonormalMatrix (stdOrthonormalBasis ℂ V)]
  rw [← algebraMap_smul ℂ r A,map_smul]
  rw [algebraMap_smul ℂ r]
  exact matrixMoment_smul q r _

lemma evenMoment_unitary_left (q : ℕ) (U A : V →ₗ[ℂ] V) (hu : U.adjoint*U=1) :
    evenMoment q (U*A)=evenMoment q A := by
  unfold evenMoment
  rw [show (U*A).adjoint*(U*A)=A.adjoint*A by
    rw [← LinearMap.star_eq_adjoint,star_mul]; calc
      _ = A.adjoint*(U.adjoint*U)*A := by noncomm_ring
      _ = _ := by rw [hu,mul_one]]

lemma linear_trace_holder {q : ℕ} (hq : 0<q) (A : Fin (2*q) → V →ₗ[ℂ] V) :
    ‖LinearMap.trace ℂ V (List.ofFn A).prod‖ ≤
      ∏j, evenMoment q (A j)^(((2*q:ℕ):ℝ)⁻¹) := by
  let v := stdOrthonormalBasis ℂ V
  rw [trace_orthonormalMatrix v,map_list_prod,List.map_ofFn]
  simpa only [Function.comp_def,evenMoment_orthonormalMatrix v] using
    matrix_trace_holder hq (fun j => LinearMap.toMatrixOrthonormal v (A j))

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_CyclicHolder
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Cyclic

variable {A : Type*} [Fintype A]

omit [Fintype A] in
lemma chainWeight_cons (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (a : A) (x : Fin (n+1) → A) :
    chainWeight (n+1) p (Fin.cons a x) =
      p 0 a (x 0) * chainWeight n (fun i => p i.succ) x := by
  unfold chainWeight
  rw [Fin.prod_univ_succ]
  simp

lemma sum_chainWeight (n : ℕ) (p : Fin n → A → A → ℝ)
    (hp : ∀ i y, ∑ x, p i x y = 1) :
    ∑ x : Fin (n+1) → A, chainWeight n p x = (Fintype.card A : ℝ) := by
  induction n with
  | zero => simp [chainWeight]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+2) => A)).sum_comp]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    change (∑ x : Fin (n+1) → A, ∑ a : A, chainWeight (n+1) p (Fin.cons a x)) = _
    simp_rw [chainWeight_cons]
    simp only [← Finset.sum_mul, hp, one_mul]
    exact ih (fun i => p i.succ) (fun i => hp i.succ)

omit [Fintype A] in
lemma deletedWeight_last (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (x : Fin (n+1) → A) :
    deletedWeight n p (Fin.last n) x = chainWeight n (fun i => p i.castSucc) x := by
  unfold deletedWeight chainWeight
  rw [Fin.prod_univ_castSucc]
  simp [finRotate_apply, Fin.coeSucc_eq_succ]

omit [Fintype A] in
lemma deletedWeight_reindex (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (r : Fin (n+1)) (x : Fin (n+1) → A) :
    let e := finCycle (r - Fin.last n)
    deletedWeight n p r x =
      deletedWeight n (fun i => p (e i)) (Fin.last n) (fun i => x (e i)) := by
  dsimp only
  let e := finCycle (r - Fin.last n)
  have helast : e (Fin.last n) = r := by simp [e, finCycle_apply]
  have heq (i : Fin (n+1)) : e i = r ↔ i = Fin.last n := by
    rw [← helast, e.injective.eq_iff]
  have hecomm (i : Fin (n+1)) : e (finRotate (n+1) i) = finRotate (n+1) (e i) := by
    simp only [e, finCycle_apply, finRotate_apply]
    abel
  unfold deletedWeight
  rw [← Equiv.prod_comp e (fun i => if i = r then (1 : ℝ) else p i (x i) (x (finRotate (n+1) i)))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [heq, ← hecomm]
  rfl

lemma sum_deletedWeight (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i y, ∑ x, p i x y = 1) (r : Fin (n+1)) :
    ∑ x : Fin (n+1) → A, deletedWeight n p r x = (Fintype.card A : ℝ) := by
  let e := finCycle (r - Fin.last n)
  have hdel (x : Fin (n+1) → A) : deletedWeight n p r x =
      chainWeight n (fun i => p (e i.castSucc)) (fun i => x (e i)) := by
    rw [deletedWeight_reindex n p r x, deletedWeight_last]
  simp_rw [hdel]
  have he : (∑ x : Fin (n+1) → A,
      chainWeight n (fun i => p (e i.castSucc)) (fun i => x (e i))) =
      ∑ x : Fin (n+1) → A, chainWeight n (fun i => p (e i.castSucc)) x := by
    exact (Equiv.arrowCongr e.symm (Equiv.refl A)).sum_comp _
  rw [he]
  exact sum_chainWeight n _ (fun i => hp (e i.castSucc))

omit [Fintype A] in
lemma deletedWeight_nonneg (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y) (r : Fin (n+1)) (x : Fin (n+1) → A) :
    0 ≤ deletedWeight n p r x := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact zero_le_one
  · exact hp _ _ _

omit [Fintype A] in
lemma prod_deletedWeight (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (x : Fin (n+1) → A) :
    ∏ r, deletedWeight n p r x =
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ n := by
  unfold deletedWeight
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have hset : Finset.univ.filter (fun r : Fin (n+1) => ¬ i = r) =
      Finset.univ.erase i := by ext r; simp [ne_comm]
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp

omit [Fintype A] in
lemma prod_deletedWeight_rpow (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y) (x : Fin (n+1) → A) :
    (∏ r, (deletedWeight n p r x) ^ (1 / (n+1 : ℝ))) =
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ)) := by
  rw [Real.finsetProd_rpow _ _ (fun r _ => deletedWeight_nonneg n p hp r x),
    prod_deletedWeight,
    ← Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hp _ _ _) _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_natCast, ← Real.rpow_mul (hp _ _ _)]
  congr 1
  ring

theorem sum_cycle_rpow_le_card (n : ℕ) (p : Fin (n+1) → A → A → ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y)
    (hsum : ∀ i y, ∑ x, p i x y = 1) :
    (∑ x : Fin (n+1) → A,
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ)))
        ≤ (Fintype.card A : ℝ) := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  calc
    _ = ∑ x : Fin (n+1) → A,
          ∏ r, (deletedWeight n p r x) ^ (1 / (n+1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (prod_deletedWeight_rpow n p hp x).symm
    _ ≤ ∑ x : Fin (n+1) → A,
          ∑ r, (1 / (n+1 : ℝ)) * deletedWeight n p r x := by
      apply Finset.sum_le_sum
      intro x _
      apply Real.geom_mean_le_arith_mean_weighted
      · intro r _; positivity
      · simp [hn]
      · intro r _; exact deletedWeight_nonneg n p hp r x
    _ = (Fintype.card A : ℝ) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, sum_deletedWeight n p hsum]
      simp [hn]

end BinaryCoordinateSweeps.Cyclic

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_Basic
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section FiniteProbability
variable {Ω G : Type*} [Fintype Ω] [Fintype G]

lemma finiteLaw_nonneg (f : Ω → G) (g : G) : 0 ≤ finiteLaw f g := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

lemma finiteLaw_sum [Nonempty Ω] (f : Ω → G) : ∑ g, finiteLaw f g = 1 := by
  classical
  simp only [finiteLaw]
  rw [Finset.sum_comm]
  simp [Fintype.card_ne_zero]

end FiniteProbability

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_GridSweepPath
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

theorem pathEvent_nonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    ∃ g : GridChoices bits, pathEvent H g := by
  classical
  let A (j : Fin b) (y : GridOutside bits j) :=
    {k : Fin h // (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i) = y}
  have hp (j : Fin b) (y : GridOutside bits j) :
      ∃ σ : Equiv.Perm (Slot (bits j)), ∀ k : A j y,
        σ (H.position j.castSucc k.val j) = H.position j.succ k.val j := by
    apply Equiv.Perm.exists_extending_pair
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.castSucc
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
    · intro k l he
      apply Subtype.ext
      apply H.disjoint j.succ
      funext i
      by_cases hi : i = j
      · subst i; exact he
      · rw [H.changes_only_stage j k.val i hi, H.changes_only_stage j l.val i hi]
        exact (congrFun k.property ⟨i, hi⟩).trans (congrFun l.property ⟨i, hi⟩).symm
  choose g hg using hp
  refine ⟨g, ?_⟩
  intro j k
  apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
  simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
  apply Prod.ext
  · exact hg j _ ⟨k, rfl⟩
  · funext i
    exact (H.changes_only_stage j k i.val i.property).symm

lemma lineLaw_pos (d : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : Equiv.Perm (Slot d)) : 0 < lineLaw d z g := by
  have hu : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    exact inv_pos.mpr hc
  exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hz1) hu)
    (mul_nonneg hz (finiteLaw_nonneg (binarySweep d) g))

lemma gridWeight_pos {b : ℕ} (bits : Fin b → ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1)
    (g : GridChoices bits) : 0 < gridWeight bits z g := by
  apply Finset.prod_pos
  intro j _
  exact Finset.prod_pos (fun y _ => lineLaw_pos (bits j) hz hz1 (g j y))

theorem conditionalNormalizer_pos {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) : 0 < conditionalNormalizer H z := by
  classical
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  apply Finset.sum_pos'
  · intro g' _
    split_ifs
    · exact (gridWeight_pos bits hz hz1 g').le
    · exact le_rfl
  · exact ⟨g, Finset.mem_univ _, by simpa [hg] using gridWeight_pos bits hz hz1 g⟩

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_IndependentHistory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps

section Assignments
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [Fintype I]

lemma card_assignment_completions (A B : I ↪ X) :
    Fintype.card {σ : Equiv.Perm X // Assigns A B σ} =
      (Fintype.card X - Fintype.card I).factorial := by
  classical
  let eA := Equiv.ofInjective A A.injective
  let eB := Equiv.ofInjective B B.injective
  let e₀ : Set.range A ≃ Set.range B := eA.symm.trans eB
  have ha : Fintype.card (Set.range A) = Fintype.card I := Fintype.card_congr eA.symm
  have hb : Fintype.card (Set.range B) = Fintype.card I := Fintype.card_congr eB.symm
  let e : {σ : Equiv.Perm X // Assigns A B σ} ≃
      {σ : X ≃ X // ∀ x : Set.range A, σ x = e₀ x} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro σ
      constructor
      · intro h x
        obtain ⟨i, hi⟩ := x.property
        have hx : x = eA i := Subtype.ext hi.symm
        rw [hx]
        simpa [e₀, eA, eB] using h i
      · intro h i
        simpa [e₀, eA, eB] using h (eA i))
  let c : ↥((Set.range A)ᶜ) ≃ ↥((Set.range B)ᶜ) := Fintype.equivOfCardEq (by
    change Fintype.card {x : X // x ∉ Set.range A} = Fintype.card {x : X // x ∉ Set.range B}
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, ha, hb])
  rw [Fintype.card_congr (e.trans (Equiv.Set.compl e₀)), Fintype.card_equiv c]
  change (Fintype.card {x : X // x ∉ Set.range A}).factorial = _
  rw [Fintype.card_subtype_compl, ha]

lemma uniform_assignment_probability (A B : I ↪ X) :
    (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  classical
  have hn : Fintype.card I ≤ Fintype.card X := Fintype.card_le_of_injective A A.injective
  have hcard : (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) =
      ((Fintype.card X - Fintype.card I).factorial : ℝ) := by
    exact_mod_cast card_assignment_completions A B
  have hsum : (∑ σ : Equiv.Perm X, if Assigns A B σ then
      (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ else 0) =
      (Fintype.card {σ : Equiv.Perm X // Assigns A B σ} : ℝ) *
        (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ := by
    simp [Fintype.card_subtype, Finset.sum_ite]
  rw [hsum, hcard, Fintype.card_perm,
    ← Nat.factorial_mul_descFactorial hn, Nat.cast_mul, mul_inv_rev]
  have hf : (((Fintype.card X - Fintype.card I).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (Fintype.card X - Fintype.card I))
  field_simp

end Assignments

attribute [local instance] Classical.propDecidable

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_AssignmentWeight
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.conditionalChoicesFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
section AssignmentWeights
attribute [local instance] Classical.propDecidable
variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

omit [Fintype I] in
lemma assignmentWeight_mono (p q : Equiv.Perm X → ℝ)
    (hpq : ∀ σ, p σ ≤ q σ) (A B : I ↪ X) :
    assignmentWeight p A B ≤ assignmentWeight q A B := by
  apply Finset.sum_le_sum
  intro σ _
  split_ifs
  · exact hpq σ
  · exact le_rfl

omit [Fintype I] in
lemma assignmentWeight_smul (p : Equiv.Perm X → ℝ) (c : ℝ) (A B : I ↪ X) :
    assignmentWeight (fun σ => c * p σ) A B = c * assignmentWeight p A B := by
  simp only [assignmentWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

lemma assignmentWeight_uniform (A B : I ↪ X) :
    assignmentWeight (fun _ => (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) A B =
      (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ :=
  uniform_assignment_probability A B

lemma assignmentWeight_comparison {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) :
    (1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ ≤
      assignmentWeight p A B ∧
    assignmentWeight p A B ≤
      2 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹ := by
  constructor
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono (fun _ => (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) p hl A B
  · simpa [assignmentWeight_smul, assignmentWeight_uniform] using
      assignmentWeight_mono p (fun _ => 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹) hu A B

lemma assignmentWeight_ratio_le {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) :
    assignmentWeight p A' B' / assignmentWeight p A B ≤
      4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A A.injective)
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (Fintype.card_le_of_injective A' A'.injective)
  have hden := (assignmentWeight_comparison hl hu A B).1
  have hnum := (assignmentWeight_comparison hl hu A' B').2
  have hdp : 0 < assignmentWeight p A B :=
    lt_of_lt_of_le (mul_pos (by norm_num) (inv_pos.mpr hi)) hden
  apply (div_le_iff₀ hdp).mpr
  calc
    _ ≤ 2 * (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)⁻¹ := hnum
    _ = (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
        (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) *
          ((1 / 2 : ℝ) * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ)⁻¹) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

end AssignmentWeights

attribute [local instance] Classical.propDecidable

lemma sum_lineHoles {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (j : Fin b) : ∑ y, lineHoles H j y = h := by
  classical
  have hh := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun k : Fin h => (fun i : {i : Fin b // i ≠ j} => H.position j.castSucc k i)))
  simpa only [Fintype.card_sigma, Fintype.card_fin, lineHoles] using hh

lemma pathEvent_iff_assigns {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (g : GridChoices bits) : pathEvent H g ↔
      ∀ (j : Fin b) (y : GridOutside bits j), Assigns (lineInput H j y) (lineOutput H j y) (g j y) := by
  constructor
  · intro hg j y k
    change g j y (H.position j.castSucc k.val j) = H.position j.succ k.val j
    have he := congrArg (fun x : GridSlot bits => x j) (hg j k.val)
    simpa only [gridLayer, Equiv.trans_apply, Equiv.piSplitAt_apply,
      Equiv.prodCongrLeft_apply, Equiv.piSplitAt_symm_apply, dite_true, eq_self,
      lineInput, lineOutput, Function.Embedding.coeFn_mk, k.property] using he
  · intro hg j k
    apply (Equiv.piSplitAt j (fun i => Slot (bits i))).injective
    simp only [gridLayer, Equiv.trans_apply, Equiv.apply_symm_apply,
      Equiv.piSplitAt_apply, Equiv.prodCongrLeft_apply]
    apply Prod.ext
    · exact hg j _ ⟨k, rfl⟩
    · funext i
      exact (H.changes_only_stage j k i.val i.property).symm

lemma finiteLaw_le_one {Ω G : Type*} [Fintype Ω] [Fintype G] [Nonempty Ω]
    (f : Ω → G) (g : G) : finiteLaw f g ≤ 1 := by
  calc
    _ ≤ ∑ x, finiteLaw f x := Finset.single_le_sum (fun x _ => finiteLaw_nonneg f x) (Finset.mem_univ _)
    _ = 1 := finiteLaw_sum f

lemma lineLaw_comparison (r d : ℕ) (hd : d ≤ 2 * r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) (g : Equiv.Perm (Slot d)) :
    (1 / 2 : ℝ) * uniformLaw (Equiv.Perm (Slot d)) g ≤ lineLaw d z g ∧
      lineLaw d z g ≤ 2 * uniformLaw (Equiv.Perm (Slot d)) g := by
  have hf1 : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  have hzp : z ≤ 1 / 2 := hzr.trans (by
    unfold linePerturbationRadius
    apply one_div_le_one_div_of_le (by norm_num)
    linarith)
  have hfd : (Fintype.card (Equiv.Perm (Slot d)) : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast (show Fintype.card (Equiv.Perm (Slot d)) ≤ (2 ^ (2 * r)).factorial from by
      simp only [Fintype.card_perm, Slot, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Nat.factorial_le (Nat.pow_le_pow_right (by norm_num) hd))
  have hup : 0 < uniformLaw (Equiv.Perm (Slot d)) g := by
    unfold uniformLaw
    have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (Slot d)) := by exact_mod_cast Fintype.card_pos
    positivity
  have hzU : z ≤ uniformLaw (Equiv.Perm (Slot d)) g := hzr.trans (by
    unfold linePerturbationRadius uniformLaw
    rw [one_div]
    apply inv_anti₀ (by exact_mod_cast Fintype.card_pos)
    linarith)
  have hB0 : 0 ≤ binaryLaw d g := finiteLaw_nonneg _ _
  have hB1 : binaryLaw d g ≤ 1 := finiteLaw_le_one _ _
  constructor
  · unfold lineLaw
    nlinarith
  · unfold lineLaw
    nlinarith [mul_le_mul_of_nonneg_left hB1 hz]

end BinaryCoordinateSweeps
end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Processes_LocalPathWeight
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma fallingCost_formula {m u : ℕ} (hm : 0 < m) (hu : u ≤ m) :
    fallingCost m u = (u : ℝ) * Real.log m - Real.log (m.descFactorial u : ℕ) := by
  have hmp : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdf : (m.descFactorial u : ℝ) ≠ 0 := by exact_mod_cast (Nat.descFactorial_pos.mpr hu).ne'
  rw [fallingCost, Real.log_div (pow_ne_zero _ hmp) hdf, Real.log_pow]

lemma assignmentWeight_eq_of_card_eq {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (p : Equiv.Perm X → ℝ) (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i)
    (hcard : Fintype.card I = Fintype.card J) : assignmentWeight p A' B' = assignmentWeight p A B := by
  have hsur : Function.Surjective f := by
    by_contra hn
    have hc := Fintype.card_lt_of_injective_not_surjective f f.injective hn
    omega
  have he (σ : Equiv.Perm X) : Assigns A' B' σ ↔ Assigns A B σ := by
    constructor
    · intro hσ i
      simpa only [hA, hB] using hσ (f i)
    · intro hσ j
      obtain ⟨i, rfl⟩ := hsur j
      simpa only [hA, hB] using hσ i
  simp only [assignmentWeight, he]

lemma assignmentWeight_log_ratio_le {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
    (hm : 0 < Fintype.card X) {p : Equiv.Perm X → ℝ}
    (hl : ∀ σ, (1 / 2 : ℝ) * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹ ≤ p σ)
    (hu : ∀ σ, p σ ≤ 2 * (Fintype.card (Equiv.Perm X) : ℝ)⁻¹)
    (A B : I ↪ X) (A' B' : J ↪ X) (f : I ↪ J)
    (hA : ∀ i, A' (f i) = A i) (hB : ∀ i, B' (f i) = B i) :
    Real.log (assignmentWeight p A' B' / assignmentWeight p A B) ≤
      fallingCost (Fintype.card X) (Fintype.card J) - fallingCost (Fintype.card X) (Fintype.card I) -
        ((Fintype.card J : ℝ) - Fintype.card I) * Real.log (Fintype.card X) +
          Real.log 4 * ((Fintype.card J : ℝ) - Fintype.card I) := by
  have hI := Fintype.card_le_of_injective A A.injective
  have hJ := Fintype.card_le_of_injective A' A'.injective
  have hi : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card I) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hI
  have hj : (0 : ℝ) < Nat.descFactorial (Fintype.card X) (Fintype.card J) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hJ
  have wi : 0 < assignmentWeight p A B := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A B).1
  have wj : 0 < assignmentWeight p A' B' := lt_of_lt_of_le (by positivity) (assignmentWeight_comparison hl hu A' B').1
  by_cases hc : Fintype.card I = Fintype.card J
  · rw [assignmentWeight_eq_of_card_eq p A B A' B' f hA hB hc, div_self wi.ne', Real.log_one, hc]
    simp
  · have hIJ := Fintype.card_le_of_injective f f.injective
    have hgap : (1 : ℝ) ≤ (Fintype.card J : ℝ) - Fintype.card I := by
      have hh : Fintype.card I + 1 ≤ Fintype.card J := by omega
      exact_mod_cast (show (1 : ℤ) ≤ (Fintype.card J : ℤ) - Fintype.card I from by omega)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    calc
      _ ≤ Real.log (4 * (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) /
          (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ)) :=
        Real.log_le_log (div_pos wj wi) (assignmentWeight_ratio_le hl hu A B A' B')
      _ = Real.log 4 + Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card I) : ℝ) -
          Real.log (Nat.descFactorial (Fintype.card X) (Fintype.card J) : ℝ) := by
        rw [Real.log_div (by positivity) hj.ne', Real.log_mul (by norm_num) hi.ne']
      _ ≤ _ := by
        rw [fallingCost_formula hm hI, fallingCost_formula hm hJ]
        nlinarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_Placement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma conditionalWeight_factor {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g else 0) =
      ∏ j, ∏ y, if Assigns (lineInput H j y) (lineOutput H j y) (g j y) then
        lineLaw (bits j) z (g j y) else 0 := by
  classical
  rw [pathEvent_iff_assigns]
  simp only [Fintype.prod_ite_zero]
  split_ifs <;> rfl

lemma sum_prod_grid {b : ℕ} (bits : Fin b → ℕ)
    (f : ∀ j : Fin b, GridOutside bits j → Equiv.Perm (Slot (bits j)) → ℝ) :
    (∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y)) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
  rw [← Fintype.prod_sum (fun (j : Fin b)
    (g : GridOutside bits j → Equiv.Perm (Slot (bits j))) => ∏ y, f j y (g y))]
  apply Finset.prod_congr rfl
  intro j _
  exact (Fintype.prod_sum (f j)).symm

lemma conditionalNormalizer_eq_prod {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (z : ℝ) : conditionalNormalizer H z = ∏ j, ∏ y, localPathWeight H z j y := by
  let f (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) : ℝ :=
    if Assigns (lineInput H j y) (lineOutput H j y) σ then lineLaw (bits j) z σ else 0
  have hL : conditionalNormalizer H z =
      ∑ g : GridChoices bits, ∏ j, ∏ y, f j y (g j y) := by
    unfold conditionalNormalizer
    apply Finset.sum_congr rfl
    intro g _
    rw [conditionalWeight_factor]
  have hR : (∏ j, ∏ y, localPathWeight H z j y) =
      ∏ j, ∏ y, ∑ σ, f j y σ := by
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro y _
    unfold localPathWeight assignmentWeight
    refine Finset.sum_congr ?_ ?_
    · ext σ
      simp only [Finset.mem_univ]
    intro σ _
    unfold f
    split_ifs <;> rfl
  rw [hL, hR]
  exact sum_prod_grid bits f

instance conditionalChoicesNonempty {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    Nonempty (ConditionalChoices H) := by
  obtain ⟨g, hg⟩ := pathEvent_nonempty H
  exact ⟨⟨g, hg⟩⟩

lemma conditionalChoiceWeight_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (g : ConditionalChoices H) :
    0 ≤ conditionalChoiceWeight H z g :=
  le_of_lt (div_pos (gridWeight_pos bits hz hz1 g.val) (conditionalNormalizer_pos H hz hz1))

lemma conditionalChoiceWeight_sum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∑ g : ConditionalChoices H, conditionalChoiceWeight H z g = 1 := by
  classical
  unfold conditionalChoiceWeight
  rw [← Finset.sum_div]
  have hs : (∑ g : ConditionalChoices H, gridWeight bits z g.val) =
      conditionalNormalizer H z := by
    unfold conditionalNormalizer
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hs, div_self (conditionalNormalizer_pos H hz hz1).ne']

section FiniteBijectionKernel
variable {Ω A B : Type*} [Fintype Ω] [Fintype A] [Fintype B]

omit [Fintype A] [Fintype B] in
lemma bijectionKernel_nonneg (w : Ω → ℝ) (e : Ω → A ≃ B)
    (hw : ∀ ω, 0 ≤ w ω) (x : A) (y : B) : 0 ≤ bijectionKernel w e x y := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs
  · exact hw ω
  · exact le_rfl

omit [Fintype A] in
lemma bijectionKernel_rowSum (w : Ω → ℝ) (e : Ω → A ≃ B) (x : A) :
    ∑ y, bijectionKernel w e x y = ∑ ω, w ω := by
  unfold bijectionKernel
  rw [Finset.sum_comm]
  simp

lemma bijectionKernel_colSum (w : Ω → ℝ) (e : Ω → A ≃ B) (y : B) :
    ∑ x, bijectionKernel w e x y = ∑ ω, w ω := by
  unfold bijectionKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [(e ω).sum_comp (fun x => if x = y then w ω else 0)]
  simp

end FiniteBijectionKernel

lemma placementProbability_eq_kernel {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    placementProbability H z x y =
      bijectionKernel (conditionalChoiceWeight H z) (placementBijection H k) x y := by
  unfold placementProbability bijectionKernel
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> rfl

lemma placementProbability_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    0 ≤ placementProbability H z x y := by
  rw [placementProbability_eq_kernel]
  exact bijectionKernel_nonneg _ _ (conditionalChoiceWeight_nonneg H hz hz1) x y

lemma placementProbability_rowSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (x : Placement H k 0) :
    ∑ y, placementProbability H z x y = 1 := by
  simp_rw [placementProbability_eq_kernel]
  rw [bijectionKernel_rowSum, conditionalChoiceWeight_sum H hz hz1]

lemma placementProbability_colSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (y : Placement H k (Fin.last b)) :
    ∑ x, placementProbability H z x y = 1 := by
  simp_rw [placementProbability_eq_kernel]
  rw [bijectionKernel_colSum, conditionalChoiceWeight_sum H hz hz1]

lemma card_placement {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    (k : ℕ) (t : Fin (b+1)) :
    Fintype.card (Placement H k t) = (gridSize bits - h).descFactorial k := by
  rw [Fintype.card_embedding_eq, card_freeSlot, Fintype.card_fin]

lemma placementKernel_nonneg {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (x y : Placement H k 0) :
    0 ≤ placementKernel H z x y := placementProbability_nonneg H hz hz1 _ _

lemma placementKernel_rowSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (x : Placement H k 0) :
    ∑ y, placementKernel H z x y = 1 := by
  unfold placementKernel
  rw [(placementIdentification H k).sum_comp]
  exact placementProbability_rowSum H hz hz1 x

lemma placementKernel_colSum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) {k : ℕ} (y : Placement H k 0) :
    ∑ x, placementKernel H z x y = 1 := placementProbability_colSum H hz hz1 _

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CoinductionTools
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G H V W : Type*} [Group G] [Group H]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  (φ : H →* G) (ρ : Representation ℂ G V) (σ : Representation ℂ H W)

variable [Fintype G] [Fintype H] [Module.Finite ℂ V] [Module.Finite ℂ W]

lemma multiplicity_symm (σ : Representation ℂ G W) :
    Module.finrank ℂ (IntertwiningMap ρ σ) = Module.finrank ℂ (IntertwiningMap σ ρ) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have h₁ := card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have h₂ := card_inv_mul_sum_char_mul_char_eq_finrank σ ρ
  have he : ∑ g : G, σ.character g * ρ.character g⁻¹ =
      ∑ g : G, ρ.character g * σ.character g⁻¹ := by
    rw [← Equiv.sum_comp (Equiv.inv G) (fun g => ρ.character g * σ.character g⁻¹)]
    simp only [Equiv.inv_apply,inv_inv,mul_comm]
  apply Nat.cast_injective (R := ℂ)
  exact h₁.symm.trans ((congrArg (fun z : ℂ => (Nat.card G : ℂ)⁻¹*z) he).trans h₂)

omit [Fintype G] [Fintype H] [Module.Finite ℂ W] in
lemma coindEvaluation_injective {I : Type*} (r : I → G)
    (hr : ∀ g : G, ∃ h : H, ∃ i : I, g = φ h * r i) :
    Function.Injective (coindEvaluation φ σ r) := by
  intro f a he
  apply Subtype.ext
  funext g
  obtain ⟨h,i,rfl⟩ := hr g
  rw [f.property,a.property]
  exact congrArg (σ h) (congrFun he i)

omit [Fintype G] [Fintype H] in
lemma coind_finrank_le {I : Type*} [Fintype I] (r : I → G)
    (hr : ∀ g : G, ∃ h : H, ∃ i : I, g = φ h * r i) :
    Module.finrank ℂ (coindV φ σ) ≤ Fintype.card I * Module.finrank ℂ W := by
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,smul_eq_mul] using
    (LinearMap.finrank_le_finrank_of_injective (coindEvaluation_injective φ σ r hr))

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation Equiv Equiv.Perm

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

variable {W : Type*} [AddCommMonoid W] [Module ℂ W] [Module.Finite ℂ W]
  (σ : Representation ℂ (Equiv.Perm A) W)

theorem placement_coind_finrank :
    Module.finrank ℂ (coindV (blockPerm e) σ) ≤
      Fintype.card (B ↪ X) * Module.finrank ℂ W :=
  coind_finrank_le (blockPerm e) σ (fun x => (placementSection e x)⁻¹)
    (placementSection_covers e)

theorem placement_coind_finrank_pow :
    Module.finrank ℂ (coindV (blockPerm e) σ) ≤
      (Fintype.card X)^(Fintype.card B) * Module.finrank ℂ W := by
  apply (placement_coind_finrank e σ).trans
  apply Nat.mul_le_mul_right
  simpa only [Fintype.card_fun] using
    Fintype.card_le_of_injective (fun x : B ↪ X => (x : B → X)) DFunLike.coe_injective

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CoindFibers
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep

section
open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [AddCommMonoid W] [Module ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

lemma coindFiberEquiv_action (a : G) (f : coindV φ σ) (i : I) :
    coindFiberEquiv φ σ r hc (coind φ σ a f) i =
      σ ((cosetEquiv φ r hc).symm (r i*a)).1
        (coindFiberEquiv φ σ r hc f ((cosetEquiv φ r hc).symm (r i*a)).2) := by
  change f.val (r i*a) = σ _ (f.val (r _))
  rw [← f.property]
  exact congrArg f.val ((cosetEquiv φ r hc).apply_symm_apply (r i*a)).symm

end

open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [Fintype I] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

omit [Fintype I] in
lemma coindHilbertRep_apply (a : G) (v : CoindHilbertSpace (I := I) (W := W)) (i : I) :
    coindHilbertRep φ σ r hc a v i =
      σ ((cosetEquiv φ r hc).symm (r i*a)).1
        (v (cosetIndexAction φ r hc a i)) := by
  obtain ⟨f,rfl⟩ := (coindHilbertEquiv φ σ r hc).surjective v
  change coindHilbertEquiv φ σ r hc
    (coind φ σ a ((coindHilbertEquiv φ σ r hc).symm
      (coindHilbertEquiv φ σ r hc f))) i = _
  rw [LinearEquiv.symm_apply_apply]
  exact coindFiberEquiv_action φ σ r hc a f i

lemma coindHilbert_unitary (hu : ∀ h v w, inner ℂ (σ h v) (σ h w) = inner ℂ v w)
    (a : G) (v w : CoindHilbertSpace (I := I) (W := W)) :
    inner ℂ (coindHilbertRep φ σ r hc a v) (coindHilbertRep φ σ r hc a w) = inner ℂ v w := by
  simp only [PiLp.inner_apply,coindHilbertRep_apply,hu]
  exact Equiv.sum_comp (cosetIndexAction φ r hc a) (fun i => inner ℂ (v i) (w i))

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W V' W' : Type*} [Group G]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  [AddCommMonoid V'] [Module ℂ V'] [AddCommMonoid W'] [Module ℂ W']
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}

lemma multiplicity_congr (e : ρ.Equiv ρ') (f : σ.Equiv σ') :
    Module.finrank ℂ (IntertwiningMap ρ σ) = Module.finrank ℂ (IntertwiningMap ρ' σ') :=
  (homCongr e f).finrank_eq

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_UnitaryTransport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

section Algebra
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

lemma irreducible_equiv (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : ρ.Equiv σ) [ρ.IsIrreducible] : σ.IsIrreducible := by
  apply (irreducible_iff_isSimpleModule_asModule σ).mpr
  exact IsSimpleModule.congr (LinearEquiv.ofBijective
    (IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) e.toLinearEquiv.bijective).symm

end Algebra

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFactor
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instDecidableEqElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.instMulActionGElemForallCellNatTabloid _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma nat_le_strictMono {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) (i : Fin n) :
    i.val ≤ f i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have hi' : i < n := by omega
    have hl := hf (show (⟨i, hi'⟩ : Fin n) < ⟨i+1, hi⟩ from by simp)
    have hp := ih hi'
    change i ≤ f ⟨i, hi'⟩ at hp
    change i + 1 ≤ f ⟨i+1, hi⟩
    omega

lemma sum_orderEmb (s : Finset ℕ) :
    ∑ i : Fin s.card, s.orderEmbOfFin rfl i = ∑ i ∈ s, i := by
  have h := Finset.sum_map (s := (Finset.univ : Finset (Fin s.card)))
    (s.orderEmbOfFin rfl).toEmbedding (fun i : ℕ => i)
  rw [s.map_orderEmbOfFin_univ rfl] at h
  exact h.symm

lemma range_sum_le (s : Finset ℕ) :
    ∑ i ∈ Finset.range s.card, i ≤ ∑ i ∈ s, i := by
  let e := s.orderEmbOfFin rfl
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => nat_le_strictMono e e.strictMono i)
  simpa only [← Fin.sum_univ_eq_sum_range, e, sum_orderEmb] using h

lemma eq_range_of_sum_eq (s : Finset ℕ)
    (h : ∑ i ∈ s, i = ∑ i ∈ Finset.range s.card, i) : s = Finset.range s.card := by
  let e := s.orderEmbOfFin rfl
  have he : ∀ i : Fin s.card, e i = i.val := by
    have hsum : ∑ i : Fin s.card, i.val = ∑ i : Fin s.card, e i := by
      dsimp only [e]
      rw [sum_orderEmb, Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
      exact h.symm
    have hh := (Finset.sum_eq_sum_iff_of_le
        (fun (i : Fin s.card) _ => nat_le_strictMono e e.strictMono i)).mp hsum
    exact fun i => (hh i (Finset.mem_univ i)).symm
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := (s.range_orderEmbOfFin rfl ▸ hi : i ∈ Set.range e)
    rw [← hj, he]
    exact Finset.mem_range.mpr j.isLt
  · intro hi
    let j : Fin s.card := ⟨i, Finset.mem_range.mp hi⟩
    rw [← show e j = i from he j]
    exact s.orderEmbOfFin_mem rfl j

lemma mem_columnCells {μ : YoungDiagram} {j : ℕ} {x : Cell μ} :
    x ∈ columnCells μ j ↔ col x = j := by simp [columnCells]

lemma row_injectiveOn_column (μ : YoungDiagram) (j : ℕ) :
    Set.InjOn (row (μ := μ)) (↑(columnCells μ j) : Set (Cell μ)) := by
  intro x hx y hy hxy
  apply Subtype.ext
  apply Prod.ext hxy
  exact (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm

lemma image_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).image row = Finset.range (μ.colLen j) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hc := x.property
    have hj := mem_columnCells.mp hx
    change x.val.2 = j at hj
    rw [← hj]
    exact YoungDiagram.mem_iff_lt_colLen.mp hc
  · intro hi
    refine ⟨⟨(i,j), YoungDiagram.mem_iff_lt_colLen.mpr hi⟩, ?_, rfl⟩
    exact mem_columnCells.mpr rfl

lemma card_columnCells (μ : YoungDiagram) (j : ℕ) :
    (columnCells μ j).card = μ.colLen j := by
  rw [← Finset.card_image_of_injOn (row_injectiveOn_column μ j), image_row_columnCells]
  exact Finset.card_range _

lemma sum_row_columnCells (μ : YoungDiagram) (j : ℕ) :
    ∑ x ∈ columnCells μ j, row x = ∑ i ∈ Finset.range (μ.colLen j), i := by
  rw [← image_row_columnCells μ j]
  exact (Finset.sum_image (f := fun i : ℕ => i) (row_injectiveOn_column μ j)).symm

lemma sum_columnCells_le (μ : YoungDiagram) (f : Cell μ → ℕ) (j : ℕ)
    (hf : Set.InjOn f (columnCells μ j)) :
    ∑ x ∈ columnCells μ j, row x ≤ ∑ x ∈ columnCells μ j, f x := by
  have h := range_sum_le ((columnCells μ j).image f)
  rw [Finset.card_image_of_injOn hf, card_columnCells, Finset.sum_image hf] at h
  rwa [sum_row_columnCells]

lemma column_image_of_total_sum (μ : YoungDiagram) (f : Cell μ → ℕ)
    (hf : ∀ j, Set.InjOn f (columnCells μ j))
    (hsum : ∑ x, f x = ∑ x : Cell μ, row x) (j : ℕ) :
    (columnCells μ j).image f = Finset.range (μ.colLen j) := by
  classical
  let J := (Finset.univ : Finset (Cell μ)).image col
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Cell μ)), col x ∈ J := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hfib (g : Cell μ → ℕ) :
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, g x = ∑ x, g x :=
    Finset.sum_fiberwise_of_maps_to hmaps g
  have heq : ∑ j ∈ J, ∑ x ∈ columnCells μ j, row x =
      ∑ j ∈ J, ∑ x ∈ columnCells μ j, f x := by rw [hfib, hfib, hsum]
  have hone := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ J) => sum_columnCells_le μ f j (hf j))).mp heq
  by_cases hj : j ∈ J
  · have hc : ((columnCells μ j).image f).card = μ.colLen j := by
      rw [Finset.card_image_of_injOn (hf j), card_columnCells]
    have h : ∑ i ∈ (columnCells μ j).image f, i =
        ∑ i ∈ Finset.range ((columnCells μ j).image f).card, i := by
      rw [hc, Finset.sum_image (hf j), ← sum_row_columnCells]
      exact (hone j hj).symm
    simpa only [hc] using eq_range_of_sum_eq _ h
  · have hc : columnCells μ j = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hj
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, mem_columnCells.mp hx⟩
    have hz : μ.colLen j = 0 := by rw [← card_columnCells, hc]; rfl
    simp [hc, hz]

lemma rearranged_row_mem (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) (x : Cell μ) :
    (row (π x), col x) ∈ μ := by
  have he := column_image_of_total_sum μ (fun x => row (π x)) hc
    (Equiv.sum_comp π row) (col x)
  have hm : row (π x) ∈ (columnCells μ (col x)).image (fun x => row (π x)) :=
    Finset.mem_image.mpr ⟨x, mem_columnCells.mpr rfl, rfl⟩
  rw [he, Finset.mem_range] at hm
  exact YoungDiagram.mem_iff_lt_colLen.mpr hm

lemma row_col_intersection (μ : YoungDiagram) :
    rowStabilizer μ ⊓ colStabilizer μ = ⊥ := by
  apply le_antisymm
  · intro π hπ
    change π = 1
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact Prod.ext (hπ.1 x) (hπ.2 x)
  · exact bot_le

theorem row_col_factorization (μ : YoungDiagram) (π : Equiv.Perm (Cell μ))
    (hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)) :
    ∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c := by
  let t : Cell μ → Cell μ := fun x =>
    ⟨(row (π x), col x), rearranged_row_mem μ π hc x⟩
  have ht : Function.Injective t := by
    intro x y hxy
    have hcol := congrArg (fun z : Cell μ => col z) hxy
    change col x = col y at hcol
    have hrow := congrArg (fun z : Cell μ => row z) hxy
    change row (π x) = row (π y) at hrow
    exact hc (col x) (mem_columnCells.mpr rfl) (mem_columnCells.mpr hcol.symm) hrow
  let c : Equiv.Perm (Cell μ) := Equiv.ofBijective t
    ⟨ht, (Finite.injective_iff_surjective).mp ht⟩
  have cc : c ∈ colStabilizer μ := by intro x; rfl
  have cr : ∀ x, row (c x) = row (π x) := by intro x; rfl
  refine ⟨π * c⁻¹, ?_, c, cc, ?_⟩
  · intro x
    change row (π (c⁻¹ x)) = row x
    rw [← cr]
    simp
  · simp

theorem row_col_alternative (μ : YoungDiagram) (π : Equiv.Perm (Cell μ)) :
    (∃ x y : Cell μ, x ≠ y ∧ col x = col y ∧ row (π x) = row (π y)) ∨
    (∃ r ∈ rowStabilizer μ, ∃ c ∈ colStabilizer μ, π = r * c) := by
  by_cases hc : ∀ j, Set.InjOn (fun x => row (π x)) (columnCells μ j)
  · exact Or.inr (row_col_factorization μ π hc)
  · left
    simp only [Set.InjOn] at hc
    push Not at hc
    obtain ⟨j, x, hx, y, hy, hrow, hne⟩ := hc
    exact ⟨x, y, hne, (mem_columnCells.mp hx).trans (mem_columnCells.mp hy).symm, hrow⟩

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungTabloid
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.instFintypeSubtypePermCellMemSubgroupC _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma tabloidOfPerm_row_mul (π : G μ) (r : rowStabilizer μ) :
    tabloidOfPerm μ (π * r.val) = tabloidOfPerm μ π := by
  apply (tabloidOfPerm_eq_iff μ _ _).mpr
  simp

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungAnti
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instFiniteDimensionalComplexSubtypeAsModuleGForallElemForallCellNatTabloidTabloidRepresentationMemSubmoduleMonoidAlgebraSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma signC_swap {x y : Cell μ} (h : x ≠ y) : signC μ (Equiv.swap x y) = -1 := by
  simp [signC_eq, Equiv.Perm.sign_swap h]

lemma columnAnti_apply (v : Tabloid μ → ℂ) :
    columnAnti μ v = ∑ c : C μ, signC μ c.val • tabloidRepresentation μ c.val v := by
  simp [columnAnti, LinearMap.sum_apply]

lemma columnAnti_rep (c : C μ) (v : Tabloid μ → ℂ) :
    columnAnti μ (tabloidRepresentation μ c.val v) = signC μ c.val • columnAnti μ v := by
  rw [columnAnti_apply, columnAnti_apply, Finset.smul_sum]
  have h := Equiv.sum_comp (Equiv.mulRight c)
    (fun d : C μ => signC μ c.val • (signC μ d.val • tabloidRepresentation μ d.val v))
  rw [← h]
  apply Finset.sum_congr rfl
  intro d hd
  change signC μ d.val • tabloidRepresentation μ d.val (tabloidRepresentation μ c.val v) =
    signC μ c.val • (signC μ (d * c).val • tabloidRepresentation μ (d * c).val v)
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, smul_smul]
  rw [show signC μ c.val * (signC μ d.val * signC μ c.val) = signC μ d.val from by
    calc
      _ = signC μ d.val * (signC μ c.val * signC μ c.val) := by ring
      _ = signC μ d.val := by rw [signC_sq, mul_one]]

lemma columnAnti_basis_column (c : C μ) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ c.val)) = signC μ c.val • polytabloid μ := by
  rw [← mul_one c.val, ← smul_tabloidOfPerm, ← rep_basis, columnAnti_rep]
  rfl

lemma col_fixes_base_iff (c : C μ) :
    c.val • tabloidOfPerm μ 1 = tabloidOfPerm μ 1 ↔ c = 1 := by
  rw [smul_tabloidOfPerm, mul_one, tabloidOfPerm_eq_iff]
  constructor
  · intro hc
    have hr : c.val ∈ rowStabilizer μ := by
      have h := (rowStabilizer μ).inv_mem hc
      simpa using h
    have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hr, c.property⟩
    rw [row_col_intersection] at hi
    exact Subtype.ext hi
  · intro hc
    subst c
    simp

lemma polytabloid_base : polytabloid μ (tabloidOfPerm μ 1) = 1 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ 1 = tabloidOfPerm μ c.val ↔ c = 1 := by
    simpa [smul_tabloidOfPerm, eq_comm] using (col_fixes_base_iff μ c)
  simp only [he]
  simp

lemma polytabloid_ne_zero : polytabloid μ ≠ 0 := by
  intro h
  have hh := congrFun h (tabloidOfPerm μ 1)
  rw [polytabloid_base] at hh
  exact one_ne_zero hh

lemma swap_mem_fiber {X Y : Type*} [DecidableEq X] (f : X → Y) {x y : X}
    (h : f x = f y) : Equiv.swap x y ∈ fiberStabilizer f := by
  intro z
  exact Equiv.apply_swap_eq_self h z

lemma swap_fixes_tabloid (t : Tabloid μ) {x y : Cell μ} (h : t.val x = t.val y) :
    (Equiv.swap x y : G μ) • t = t := by
  apply Subtype.ext
  funext z
  change t.val ((Equiv.swap x y)⁻¹ z) = t.val z
  simpa only [Equiv.swap_inv] using Equiv.apply_swap_eq_self h z

lemma columnAnti_basis_collision (π : G μ) {x y : Cell μ}
    (hne : x ≠ y) (hc : col x = col y) (hr : row (π⁻¹ x) = row (π⁻¹ y)) :
    columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) = 0 := by
  let c : C μ := ⟨Equiv.swap x y, swap_mem_fiber _ hc⟩
  have hf : c.val • tabloidOfPerm μ π = tabloidOfPerm μ π :=
    swap_fixes_tabloid μ _ hr
  have h := columnAnti_rep μ c (tabloidBasis μ (tabloidOfPerm μ π))
  rw [rep_basis, hf] at h
  have hs : signC μ c.val = -1 := signC_swap μ hne
  rw [hs, neg_one_smul] at h
  ext t
  have ht := congrFun h t
  simp only [Pi.neg_apply] at ht
  change columnAnti μ (tabloidBasis μ (tabloidOfPerm μ π)) t = 0
  linear_combination (1 / 2 : ℂ) * ht

lemma columnAnti_basis_span (t : Tabloid μ) :
    ∃ a : ℂ, columnAnti μ (tabloidBasis μ t) = a • polytabloid μ := by
  obtain ⟨π, rfl⟩ := tabloidOfPerm_surjective μ t
  rcases row_col_alternative μ π⁻¹ with ⟨x, y, hne, hc, hr⟩ | ⟨r, hr, c, hc, he⟩
  · exact ⟨0, by rw [columnAnti_basis_collision μ π hne hc hr, zero_smul]⟩
  · have hp : π = c⁻¹ * r⁻¹ := by simpa using congrArg Inv.inv he
    rw [hp, tabloidOfPerm_row_mul μ c⁻¹ ⟨r⁻¹, (rowStabilizer μ).inv_mem hr⟩]
    exact ⟨signC μ c⁻¹, columnAnti_basis_column μ ⟨c⁻¹, (colStabilizer μ).inv_mem hc⟩⟩

theorem columnAnti_rank_one (v : Tabloid μ → ℂ) :
    columnAnti μ v = (columnAnti μ v (tabloidOfPerm μ 1)) • polytabloid μ := by
  have hv : ∃ a : ℂ, columnAnti μ v = a • polytabloid μ := by
    choose a ha using columnAnti_basis_span μ
    refine ⟨∑ t, v t * a t, ?_⟩
    conv_lhs => rw [← sum_tabloidBasis μ v]
    rw [map_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [map_smul, ha, smul_smul]
  obtain ⟨a, ha⟩ := hv
  have he := congrFun ha (tabloidOfPerm μ 1)
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at he
  rw [he, ha]

lemma columnAnti_square (v : Tabloid μ → ℂ) :
    columnAnti μ (columnAnti μ v) = (Fintype.card (C μ) : ℂ) • columnAnti μ v := by
  rw [columnAnti_apply μ v]
  rw [map_sum]
  simp_rw [map_smul, columnAnti_rep, smul_smul, signC_sq, one_smul]
  rw [← columnAnti_apply]
  simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

lemma columnAnti_polytabloid :
    columnAnti μ (polytabloid μ) = (Fintype.card (C μ) : ℂ) • polytabloid μ :=
  columnAnti_square μ _

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungSpecht
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma antiModule_apply (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v = (tabloidRepresentation μ).asModuleEquiv.symm
      (columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v)) := rfl

lemma antiModule_rank_one (v : (tabloidRepresentation μ).asModule) :
    antiModule μ v =
      columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) • polyModule μ := by
  rw [antiModule_apply, columnAnti_rank_one, map_smul]
  simp only [Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one]
  rfl

lemma polyModule_ne_zero : polyModule μ ≠ 0 := by
  intro h
  apply polytabloid_ne_zero μ
  have he := congrArg (tabloidRepresentation μ).asModuleEquiv h
  simpa only [polyModule, LinearEquiv.apply_symm_apply, map_zero] using he

lemma Specht_ne_bot : Specht μ ≠ ⊥ := by
  intro h
  have hm := polyModule_mem_Specht μ
  rw [h] at hm
  exact polyModule_ne_zero μ hm

lemma antiModule_mem (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    (v : (tabloidRepresentation μ).asModule) (hv : v ∈ U) : antiModule μ v ∈ U := by
  rw [antiModule_apply, columnAnti_apply, map_sum]
  apply U.sum_mem
  intro c hc
  have h := U.smul_mem (MonoidAlgebra.single c.val (signC μ c.val)) hv
  have he : (tabloidRepresentation μ).asModuleEquiv.symm
      (signC μ c.val • tabloidRepresentation μ c.val ((tabloidRepresentation μ).asModuleEquiv v)) =
      MonoidAlgebra.single c.val (signC μ c.val) • v := by
    apply (tabloidRepresentation μ).asModuleEquiv.injective
    rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_single, LinearMap.smul_apply]
  rw [he]
  exact h

lemma scalar_polyModule_mem_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule)
    {a : ℂ} (ha : a ≠ 0) : a • polyModule μ ∈ U ↔ polyModule μ ∈ U := by
  exact (U.restrictScalars ℂ).smul_mem_iff ha

lemma Specht_le_iff (U : Submodule ℂ[G μ] (tabloidRepresentation μ).asModule) :
    Specht μ ≤ U ↔ polyModule μ ∈ U := by
  rw [Specht, Submodule.span_le, Set.singleton_subset_iff]
  rfl

theorem Specht_isAtom : IsAtom (Specht μ) := by
  refine ⟨Specht_ne_bot μ, ?_⟩
  intro U hU
  obtain ⟨V, hUV⟩ := exists_isCompl U
  have ht : polyModule μ ∈ U ⊔ V := by
    rw [hUV.sup_eq_top]
    trivial
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ht
  have hau := antiModule_mem μ U u hu
  have hav := antiModule_mem μ V v hv
  rw [antiModule_rank_one] at hau hav
  by_cases hc : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv u) (tabloidOfPerm μ 1) = 0
  · have he : columnAnti μ ((tabloidRepresentation μ).asModuleEquiv v) (tabloidOfPerm μ 1) =
          (Fintype.card (C μ) : ℂ) := by
      have hh := congrArg (fun w : (tabloidRepresentation μ).asModule =>
        columnAnti μ ((tabloidRepresentation μ).asModuleEquiv w) (tabloidOfPerm μ 1)) huv
      simp only [map_add, Pi.add_apply, hc, zero_add, polyModule,
        LinearEquiv.apply_symm_apply, columnAnti_polytabloid,
        Pi.smul_apply, polytabloid_base, smul_eq_mul, mul_one] at hh
      exact hh
    have hne : (Fintype.card (C μ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hSV : Specht μ ≤ V := (Specht_le_iff μ V).mpr
      ((scalar_polyModule_mem_iff μ V (he.trans_ne hne)).mp hav)
    apply le_antisymm _ bot_le
    calc U ≤ U ⊓ V := le_inf le_rfl (hU.le.trans hSV)
         _ = ⊥ := hUV.inf_eq_bot
  · have hSU : Specht μ ≤ U := (Specht_le_iff μ U).mpr
      ((scalar_polyModule_mem_iff μ U hc).mp hau)
    exact (hU.not_ge hSU).elim

instance Specht_isSimpleModule : IsSimpleModule ℂ[G μ] (Specht μ) :=
  isSimpleModule_iff_isAtom.mpr (Specht_isAtom μ)

end BinaryCoordinateSweeps.Young

end

open scoped MonoidAlgebra BigOperators

namespace BinaryCoordinateSweeps.Young

variable {A V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V]
  [Module A V] [Module ℂ V] [IsScalarTower ℂ A V]

variable (μ : YoungDiagram)

instance instIsIrreducibleGComplexSpechtSpaceSpechtRep : Representation.IsIrreducible (k := ℂ) (G := G μ) (V := SpechtSpace μ) (spechtRep μ) :=
  (Representation.isSimpleModule_iff_irreducible_ofModule (Specht μ)).mp inferInstance

lemma spechtInclude_poly : spechtInclude μ (spechtPoly μ) = polytabloid μ := by
  change (tabloidRepresentation μ).asModuleEquiv
    ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)
      ((restrictLinearEquiv (A := ℂ[G μ]) (V := Specht μ)).symm
        (⟨polyModule μ, polyModule_mem_Specht μ⟩ : Specht μ))).val) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (tabloidRepresentation μ).asModuleEquiv.apply_symm_apply _

lemma spechtPoly_ne_zero : spechtPoly μ ≠ 0 := by
  intro h
  have he := congrArg (spechtInclude μ) h
  rw [map_zero, spechtInclude_poly] at he
  exact polytabloid_ne_zero μ he

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungHilbert
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

variable (μ : YoungDiagram)

instance instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht : (hilbertSpecht μ).IsIrreducible :=
  letI : AddCommGroup (SpechtSpace μ) := Module.addCommMonoidToAddCommGroup ℂ
  Irrep.irreducible_equiv _ _ (Irrep.conjugateEquiv _ _)

lemma spechtHilbertEquiv_coeff (v : SpechtSpace μ) (t : Tabloid μ) :
    (spechtHilbertEquiv μ v).val t = spechtInclude μ v t := rfl

lemma hilbertSpecht_coeff (g : G μ) (v : SpechtHilbert μ) (t : Tabloid μ) :
    (hilbertSpecht μ g v).val t = v.val (g⁻¹ • t) := by
  obtain ⟨w,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  change (spechtHilbertEquiv μ (spechtRep μ g ((spechtHilbertEquiv μ).symm
      (spechtHilbertEquiv μ w)))).val t = _
  rw [LinearEquiv.symm_apply_apply,spechtHilbertEquiv_coeff,spechtInclude_rep]
  rfl

lemma hilbertSpecht_inner (g : G μ) (v w : SpechtHilbert μ) :
    inner ℂ (hilbertSpecht μ g v) (hilbertSpecht μ g w) = inner ℂ v w := by
  change inner ℂ (hilbertSpecht μ g v).val (hilbertSpecht μ g w).val = inner ℂ v.val w.val
  simp only [PiLp.inner_apply,RCLike.inner_apply,hilbertSpecht_coeff]
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹) (fun t => w.val t * star (v.val t))

lemma hilbertSpecht_unitary (g : G μ) (v : SpechtHilbert μ) :
    ‖hilbertSpecht μ g v‖ = ‖v‖ :=
  ((hilbertSpecht μ g).isometryOfInner (hilbertSpecht_inner μ g)).norm_map v

lemma hilbertSpecht_finrank : Module.finrank ℂ (SpechtHilbert μ) = Module.finrank ℂ (SpechtSpace μ) :=
  (spechtHilbertEquiv μ).finrank_eq.symm

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

namespace BinaryCoordinateSweeps.Signed
variable {n : ℕ}

lemma adjacent_swap_inversion (a b i j : Fin n) (hab : a.val + 1 = b.val) (hij : j < i) :
    Equiv.swap a b i ≤ Equiv.swap a b j ↔ i = b ∧ j = a := by
  have hn : a ≠ b := by intro h; subst b; omega
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp_all only [Fin.le_def, Fin.lt_def, Fin.ext_iff, and_true, and_false, iff_true, iff_false] <;> omega

lemma koszulSign_swap_adjacent (β : Fin n → Bool) (a b : Fin n) (hab : a.val+1=b.val) :
    koszulSign β (Equiv.swap a b) = if β a = true ∧ β b = true then -1 else 1 := by
  unfold koszulSign
  rw [Finset.prod_eq_single (⟨b,a⟩ : Σ _ : Fin n, Fin n)]
  · simp only [swap_apply_right, swap_apply_left]
    rw [ite_eq_left (show a ≤ b by omega)]
    simp only [and_comm]
  · rintro ⟨i,j⟩ hij hne
    have hi : ¬ Equiv.swap a b i ≤ Equiv.swap a b j := by
      rw [adjacent_swap_inversion a b i j hab (mem_finPairsLT.mp hij)]
      rintro ⟨rfl,rfl⟩; exact hne rfl
    simp [hi]
  · intro h
    exact False.elim (h (mem_finPairsLT.mpr (show a < b by omega)))

lemma mask_swap (β : Fin n → Bool) (a b : Fin n) (h : β a = β b) :
    β ∘ Equiv.swap a b = β := by
  funext i
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

lemma koszulSign_conjugate (β : Fin n → Bool) (g f : Equiv.Perm (Fin n))
    (hf : β ∘ f.symm = β) :
    koszulSign (β ∘ g.symm) (g*f*g⁻¹) = koszulSign β f := by
  have hc : (g*f*g⁻¹)*g = g*f := by group
  have h := congrArg (koszulSign β) hc
  rw [koszulSign_mul β (g*f*g⁻¹) g, koszulSign_mul β g f, hf] at h
  have he : koszulSign β g * koszulSign β f = koszulSign β f * koszulSign β g := mul_comm _ _
  rw [he] at h
  exact mul_right_cancel h

lemma exists_perm_pair (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : Equiv.Perm (Fin n), g a = c ∧ g b = d := by
  let h := Equiv.swap a c
  have hh : h b ≠ c := by
    intro hbc
    have ha : h a = c := by simp [h]
    exact hab (h.injective (ha.trans hbc.symm))
  refine ⟨Equiv.swap (h b) d * h, ?_, ?_⟩
  · change Equiv.swap (h b) d (h a) = c
    rw [show h a = c by simp [h]]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hh) hcd
  · simp

lemma koszulSign_swap (β : Fin n → Bool) (a b : Fin n) (hab : a ≠ b)
    (hβ : β a = β b) :
    koszulSign β (Equiv.swap a b) = if β a = true then -1 else 1 := by
  have hn : 2 ≤ n := by
    by_contra h
    have ha := a.isLt
    have hb := b.isLt
    apply hab
    apply Fin.ext
    omega
  let c : Fin n := ⟨0, by omega⟩
  let d : Fin n := ⟨1, by omega⟩
  have hcd : c ≠ d := by intro hh; have := congrArg Fin.val hh; dsimp [c,d] at this; omega
  obtain ⟨g,hga,hgb⟩ := exists_perm_pair a b c d hab hcd
  have hc := koszulSign_conjugate β g (Equiv.swap a b) (by simpa using mask_swap β a b hβ)
  have hconj : g * Equiv.swap a b * g⁻¹ = Equiv.swap c d := by
    have ht := Equiv.symm_trans_swap_trans a b g
    change g * Equiv.swap a b * g⁻¹ = Equiv.swap (g a) (g b) at ht
    simpa only [hga,hgb] using ht
  rw [hconj, koszulSign_swap_adjacent _ c d (by rfl)] at hc
  have hgca : g.symm c = a := by rw [← hga]; simp
  have hgdb : g.symm d = b := by rw [← hgb]; simp
  simpa only [Function.comp_apply, hgca, hgdb, ← hβ, and_self] using hc.symm

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungInducedMap
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Equiv Equiv.Perm

namespace BinaryCoordinateSweeps.Signed
variable {n : ℕ}

lemma mask_ofSubtype (β : Fin n → Bool) (b : Bool)
    (f : Equiv.Perm {i // β i = b}) : β ∘ (Equiv.Perm.ofSubtype f).symm = β := by
  funext i
  change β ((Equiv.Perm.ofSubtype f⁻¹) i) = β i
  by_cases h : β i = b
  · rw [Equiv.Perm.ofSubtype_apply_of_mem f⁻¹ h]
    exact (f⁻¹ ⟨i,h⟩).property.trans h.symm
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem f⁻¹ h]

lemma koszulSign_ofSubtype (β : Fin n → Bool) (b : Bool)
    (f : Equiv.Perm {i // β i = b}) :
    koszulSign β (Equiv.Perm.ofSubtype f) = if b = true then Equiv.Perm.sign f else 1 := by
  induction f using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f a c hac ih =>
    rw [map_mul, koszulSign_mul, mask_ofSubtype, ofSubtype_swap_eq,
      koszulSign_swap _ _ _ (fun h => hac (Subtype.ext h)) (a.property.trans c.property.symm),
      a.property, ih, map_mul, Equiv.Perm.sign_swap hac]
    split_ifs <;> simp

lemma mask_of_fixed_complement (β : Fin n → Bool) (b : Bool) (g : Equiv.Perm (Fin n))
    (hg : ∀ i, β i ≠ b → g i = i) : ∀ i, β (g i) = b ↔ β i = b := by
  intro i
  constructor
  · intro h
    by_contra hi
    rw [hg i hi] at h
    exact hi h
  · intro h
    by_contra hi
    have he := hg (g i) hi
    have eq := g.injective he
    rw [eq] at hi
    exact hi h

lemma mask_fixed_complement (β : Fin n → Bool) (b : Bool) (g : Equiv.Perm (Fin n))
    (hg : ∀ i, β i ≠ b → g i = i) : β ∘ g.symm = β := by
  let f : Equiv.Perm {i // β i = b} :=
    g.subtypePerm (mask_of_fixed_complement β b g hg)
  have he : Equiv.Perm.ofSubtype f = g := by
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro i hi
    by_contra h
    exact hi (hg i h)
  simpa only [he] using mask_ofSubtype β b f

lemma koszulSign_of_fixed_complement (β : Fin n → Bool) (b : Bool)
    (g : Equiv.Perm (Fin n)) (hg : ∀ i, β i ≠ b → g i = i) :
    koszulSign β g = if b = true then Equiv.Perm.sign g else 1 := by
  let f : Equiv.Perm {i // β i = b} :=
    g.subtypePerm (mask_of_fixed_complement β b g hg)
  have he : Equiv.Perm.ofSubtype f = g := by
    apply Equiv.Perm.ofSubtype_subtypePerm
    intro i hi
    by_contra h
    exact hi (hg i h)
  have hs := koszulSign_ofSubtype β b f
  rw [← Equiv.Perm.sign_ofSubtype f, he] at hs
  exact hs

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookWord
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Equiv Equiv.Perm

namespace BinaryCoordinateSweeps.Young

variable {μ : YoungDiagram} {p : ℕ}

lemma hookLabel_top (h : InHook μ p) (x : Cell μ) :
    (hookLabel h x).1 = false ↔ row x < p := by
  unfold hookLabel
  split_ifs <;> simp_all

lemma hookLabel_bottom (h : InHook μ p) (x : Cell μ) :
    (hookLabel h x).1 = true ↔ ¬row x < p := by
  unfold hookLabel
  split_ifs <;> simp_all

lemma hookLabel_eq_top (h : InHook μ p) (x y : Cell μ)
    (hx : row x < p) (he : hookLabel h y = hookLabel h x) : row y = row x := by
  have hy : row y < p := (hookLabel_top h y).mp
    ((congrArg Prod.fst he).trans ((hookLabel_top h x).mpr hx))
  have hh := congrArg (fun z : Bool × Fin p => z.2.val) he
  simpa only [hookLabel, dite_eq_left hx, dite_eq_left hy] using hh

lemma hookLabel_eq_bottom (h : InHook μ p) (x y : Cell μ)
    (hx : ¬row x < p) (he : hookLabel h y = hookLabel h x) : col y = col x := by
  have hy : ¬row y < p := (hookLabel_bottom h y).mp
    ((congrArg Prod.fst he).trans ((hookLabel_bottom h x).mpr hx))
  have hh := congrArg (fun z : Bool × Fin p => z.2.val) he
  simpa only [hookLabel, dite_eq_right hx, dite_eq_right hy] using hh

lemma hook_return_column_fixes (h : InHook μ p) (c : C μ) (r : rowStabilizer μ)
    (hr : ∀ x, hookLabel h ((c.val*r.val) x) = hookLabel h x)
    (x : Cell μ) (hx : row x < p) : c.val x = x := by
  have hrinv : row (r.val⁻¹ x) = row x := (r⁻¹).property x
  have hz : row (r.val⁻¹ x) < p := by rwa [hrinv]
  have hh := hr (r.val⁻¹ x)
  simp only [mul_apply, show r.val (r.val⁻¹ x) = x from r.val.apply_symm_apply x] at hh
  apply Subtype.ext
  apply Prod.ext
  · exact (hookLabel_eq_top h _ _ hz hh).trans ((r⁻¹).property x)
  · exact c.property x

lemma hook_return_row_fixes (h : InHook μ p) (c : C μ) (r : rowStabilizer μ)
    (hr : ∀ x, hookLabel h ((c.val*r.val) x) = hookLabel h x)
    (x : Cell μ) (hx : ¬row x < p) : r.val x = x := by
  apply Subtype.ext
  apply Prod.ext
  · exact r.property x
  · have hh := hookLabel_eq_bottom h x ((c.val*r.val) x) hx (hr x)
    change col (c.val (r.val x)) = col x at hh
    rw [c.property] at hh
    exact hh

variable {n : ℕ}

lemma hookWord_comp_eq (h : InHook μ p) (e : Cell μ ≃ Fin n) (g : G μ) :
    hookWord h e ∘ e.permCongr g = hookWord h e ↔
      ∀ x, hookLabel h (g x) = hookLabel h x := by
  constructor
  · intro hh x
    have he := congrFun hh (e x)
    simpa only [hookWord, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply] using he
  · intro hh
    funext i
    simpa only [hookWord, Function.comp_apply, Equiv.permCongr_apply,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply] using hh (e.symm i)

lemma hook_return_sign (h : InHook μ p) (e : Cell μ ≃ Fin n)
    (c : C μ) (r : rowStabilizer μ)
    (hr : hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e) :
    Signed.signC (Prod.fst ∘ hookWord h e) (e.permCongr (c.val*r.val))⁻¹ = signC μ c.val := by
  let β := Prod.fst ∘ hookWord h e
  have hh := (hookWord_comp_eq h e _).mp hr
  have hc : ∀ i, β i ≠ true → e.permCongr c.val i = i := by
    intro i hi
    have hx : row (e.symm i) < p := by
      apply (hookLabel_top h _).mp
      exact Bool.eq_false_of_not_eq_true hi
    have hf := hook_return_column_fixes h c r hh (e.symm i) hx
    simp only [Equiv.permCongr_apply, hf, Equiv.apply_symm_apply]
  have hrf : ∀ i, β i ≠ false → e.permCongr r.val i = i := by
    intro i hi
    have hx : ¬row (e.symm i) < p := by
      intro hx
      exact hi ((hookLabel_top h _).mpr hx)
    have hf := hook_return_row_fixes h c r hh (e.symm i) hx
    simp only [Equiv.permCongr_apply, hf, Equiv.apply_symm_apply]
  have hcm := Signed.mask_fixed_complement β true (e.permCongr c.val) hc
  have hrm := Signed.mask_fixed_complement β false (e.permCongr r.val) hrf
  have hcs := Signed.koszulSign_of_fixed_complement β true (e.permCongr c.val) hc
  have hrs := Signed.koszulSign_of_fixed_complement β false (e.permCongr r.val) hrf
  simp only [ite_true, Bool.false_eq_true, ite_false] at hcs hrs
  have hs : Signed.koszulSign β (e.permCongr (c.val*r.val)) = Equiv.Perm.sign c.val := by
    rw [Equiv.permCongr_mul, Signed.koszulSign_mul, hrm, hcs, hrs, mul_one,
      Equiv.Perm.sign_permCongr]
  have hm : β ∘ (e.permCongr (c.val*r.val)).symm = β := by
    change Prod.fst ∘ hookWord h e ∘ (e.permCongr (c.val*r.val)).symm = β
    have hi := congrArg (fun w => w ∘ (e.permCongr (c.val*r.val)).symm) hr
    have hi' : hookWord h e = hookWord h e ∘ (e.permCongr (c.val*r.val)).symm := by
      simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hi
    exact congrArg (fun w => Prod.fst ∘ w) hi'.symm
  have hinv := Signed.koszulSign_inv β (e.permCongr (c.val*r.val))
  rw [hm,hs] at hinv
  change ((Signed.koszulSign β _ : ℤ) : ℂ) = _
  rw [hinv]
  rfl

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Representation

namespace BinaryCoordinateSweeps.Young
variable {μ : YoungDiagram} {p n : ℕ}

lemma hookMap_poly (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    hookMap h e (spechtPoly μ) =
      ∑ c : C μ, ∑ r : rowStabilizer μ,
        signC μ c.val • hookRep e p (c.val*r.val) (Pi.single (hookWord h e) 1) := by
  change fromTabloid μ (hookRep e p) (hookRowVector h e)
    (spechtInclude μ (spechtPoly μ)) = _
  rw [spechtInclude_poly, polytabloid, columnAnti_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smul, fromTabloid_intertwines μ _ _ (hookRowVector_fixed h e),
    fromTabloid_basis, tabloidVector_eq μ _ _ (hookRowVector_fixed h e), map_one,
    Module.End.one_apply, hookRowVector, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_mul, Module.End.mul_apply]

lemma hook_term_coefficient (h : InHook μ p) (e : Cell μ ≃ Fin n)
    (c : C μ) (r : rowStabilizer μ) :
    (signC μ c.val • hookRep e p (c.val*r.val) (Pi.single (hookWord h e) 1)) (hookWord h e) =
      if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then (1 : ℂ) else 0 := by
  change signC μ c.val * (Signed.signC (Prod.fst ∘ hookWord h e)
    (e.permCongr (c.val*r.val))⁻¹ *
      (Pi.single (hookWord h e) (1 : ℂ) : (Fin n → Bool × Fin p) → ℂ)
        (hookWord h e ∘ e.permCongr (c.val*r.val))) = _
  by_cases hh : hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e
  · rw [ite_eq_left hh, hook_return_sign h e c r hh, hh, Pi.single_eq_same, mul_one, signC_sq]
  · rw [ite_eq_right hh, Pi.single_eq_of_ne hh, mul_zero, mul_zero]

lemma hookMap_poly_coefficient (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    hookMap h e (spechtPoly μ) (hookWord h e) =
      ∑ c : C μ, ∑ r : rowStabilizer μ,
        if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then (1 : ℂ) else 0 := by
  rw [hookMap_poly]
  simp only [Finset.sum_apply, hook_term_coefficient]

lemma hookMap_nonzero (h : InHook μ p) (e : Cell μ ≃ Fin n) : hookMap h e ≠ 0 := by
  intro hz
  have he := hookMap_poly_coefficient h e
  rw [hz] at he
  change (0 : ℂ) = _ at he
  have hre := congrArg Complex.re he
  simp only [Complex.zero_re, Complex.re_sum, apply_ite,
    Complex.one_re, Complex.zero_re] at hre
  have hs (c : C μ) (r : rowStabilizer μ) :
      (0 : ℝ) ≤ if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then 1 else 0 := by
    split_ifs <;> norm_num
  have hid : (1 : ℝ) ≤ ∑ r : rowStabilizer μ,
      if hookWord h e ∘ e.permCongr ((1 : C μ).val*r.val) = hookWord h e then 1 else 0 := by
    have hi := Finset.single_le_sum (s := Finset.univ) (f := fun r : rowStabilizer μ =>
      if hookWord h e ∘ e.permCongr ((1 : C μ).val*r.val) = hookWord h e then (1 : ℝ) else 0)
      (fun r _ => hs 1 r) (Finset.mem_univ (1 : rowStabilizer μ))
    have he1 : e.permCongr (1 : G μ) = (1 : Equiv.Perm (Fin n)) := by
      apply Equiv.ext
      intro i
      exact e.apply_symm_apply i
    simpa only [Subgroup.coe_one, one_mul, he1, Equiv.Perm.coe_one, Function.comp_id,
      ite_true] using hi
  have hle := Finset.single_le_sum (s := Finset.univ) (f := fun c : C μ =>
      ∑ r : rowStabilizer μ,
        if hookWord h e ∘ e.permCongr (c.val*r.val) = hookWord h e then (1 : ℝ) else 0)
    (fun c _ => Finset.sum_nonneg (fun r _ => hs c r)) (Finset.mem_univ (1 : C μ))
  linarith

theorem hookMap_injective (h : InHook μ p) (e : Cell μ ≃ Fin n) :
    Function.Injective (hookMap h e) :=
  (Representation.IsIrreducible.injective_or_eq_zero (k := ℂ) (G := G μ)
    (V := SpechtSpace μ) (W := (Fin n → Bool × Fin p) → ℂ) (hookMap h e)).resolve_right
      (hookMap_nonzero h e)

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookCut
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Equiv Equiv.Perm

variable (μ : YoungDiagram) (p : ℕ)

lemma signC_cutPerm (g : G (hookPart μ p) × G (southeast μ p)) :
    signC μ (cutPerm μ p g) = signC (hookPart μ p) g.1 * signC (southeast μ p) g.2 := by
  change (((sign ((cutEquiv μ p).permCongr (Equiv.sumCongr g.1 g.2))) : ℤ) : ℂ) = _
  rw [sign_permCongr,sign_sumCongr,Units.val_mul,Int.cast_mul]
  rfl

lemma glueTabloid_injective : Function.Injective (glueTabloid μ p) := by
  intro t u h
  apply Prod.ext
  · apply Subtype.ext
    funext x
    have hh := congrArg (fun v : Tabloid μ => v.val (hookIn μ p x)) h
    simpa only [glueTabloid_val,glueLabels_hook] using hh
  · apply Subtype.ext
    funext x
    have hh := congrArg (fun v : Tabloid μ => v.val (southeastIn μ p x)) h
    simpa only [glueTabloid_val,glueLabels_southeast,Nat.add_right_cancel_iff] using hh

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CutColumns
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

section
open Equiv Equiv.Perm

variable (μ : YoungDiagram) (p : ℕ)

lemma column_glue_in_range (c : C μ)
    (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p))
    (he : tabloidOfPerm μ c.val = glueTabloid μ p t) : c ∈ Set.range (cutColumns μ p) := by
  let q := (cutEquiv μ p).symm.permCongr c.val⁻¹
  have hinr : Set.MapsTo q (Set.range Sum.inr) (Set.range Sum.inr) := by
    rintro x ⟨y,rfl⟩
    have hh := congrArg (fun v : Tabloid μ => v.val (southeastIn μ p y)) he
    change row (c.val⁻¹ (southeastIn μ p y)) = glueLabels μ p t (southeastIn μ p y) at hh
    rw [glueLabels_southeast] at hh
    have hc := (C μ).inv_mem c.property (southeastIn μ p y)
    rcases hq : q (Sum.inr y) with a | b
    · have hcell : c.val⁻¹ (southeastIn μ p y) = hookIn μ p a := by
        have h := congrArg (cutEquiv μ p) hq
        simpa only [q,Equiv.permCongr_apply,Equiv.symm_symm,
          Equiv.apply_symm_apply,cutEquiv_inr,cutEquiv_inl] using h
      rw [hcell,row_hookIn] at hh
      rw [hcell,col_hookIn,col_southeastIn] at hc
      have ha := hookPart_inHook μ p a
      omega
    · exact ⟨b,rfl⟩
  have hq := mem_sumCongrHom_range_of_perm_mapsTo_inl
    ((perm_mapsTo_inl_iff_mapsTo_inr q).mpr hinr)
  obtain ⟨g,hg⟩ := hq
  have hinv : cutPerm μ p g = c.val⁻¹ := by
    change (cutEquiv μ p).permCongr (sumCongrHom _ _ g) = _
    rw [hg]
    exact (cutEquiv μ p).permCongr.apply_symm_apply _
  have hg' : cutPerm μ p g⁻¹ = c.val := by rw [map_inv,hinv,inv_inv]
  have hgcol := (cutPerm_mem_column_iff μ p g⁻¹).mp (hg' ▸ c.property)
  refine ⟨(⟨g⁻¹.1,hgcol.1⟩,⟨g⁻¹.2,hgcol.2⟩),?_⟩
  apply Subtype.ext
  exact hg'

end

variable (μ : YoungDiagram) (p : ℕ)

lemma polytabloid_coefficient (t : Tabloid μ) :
    polytabloid μ t = ∑ c : C μ, if t = tabloidOfPerm μ c.val then signC μ c.val else 0 := by
  rw [polytabloid,columnAnti_apply]
  simp_rw [rep_basis,smul_tabloidOfPerm,mul_one]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,tabloidBasis,Pi.single_apply]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

lemma cut_column_coefficient (a : C (hookPart μ p) × C (southeast μ p))
    (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    (if glueTabloid μ p t = tabloidOfPerm μ (cutColumns μ p a).val
      then signC μ (cutColumns μ p a).val else 0) =
    (if t.1 = tabloidOfPerm (hookPart μ p) a.1.val then signC (hookPart μ p) a.1.val else 0) *
    (if t.2 = tabloidOfPerm (southeast μ p) a.2.val then signC (southeast μ p) a.2.val else 0) := by
  change (if glueTabloid μ p t = tabloidOfPerm μ (cutPerm μ p (a.1.val,a.2.val))
    then signC μ (cutPerm μ p (a.1.val,a.2.val)) else 0) = _
  simp only [← glueTabloid_perm, (glueTabloid_injective μ p).eq_iff,Prod.ext_iff,signC_cutPerm]
  split_ifs <;> simp_all

theorem polytabloid_glue (t : Tabloid (hookPart μ p) × Tabloid (southeast μ p)) :
    polytabloid μ (glueTabloid μ p t) =
      polytabloid (hookPart μ p) t.1 * polytabloid (southeast μ p) t.2 := by
  rw [polytabloid_coefficient]
  let e := cutColumns μ p
  let f : C μ → ℂ := fun c =>
    if glueTabloid μ p t = tabloidOfPerm μ c.val then signC μ c.val else 0
  change ∑ c, f c = _
  have hs : ∑ c ∈ Finset.univ.image e, f c = ∑ c, f c := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    have hn : glueTabloid μ p t ≠ tabloidOfPerm μ c.val := by
      intro he
      obtain ⟨a,ha⟩ := column_glue_in_range μ p c t he.symm
      apply hc
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩
    exact ite_eq_right hn
  rw [← hs,Finset.sum_image e.injective.injOn]
  change (∑ a, if glueTabloid μ p t = tabloidOfPerm μ (cutColumns μ p a).val
    then signC μ (cutColumns μ p a).val else 0) = _
  simp_rw [cut_column_coefficient]
  rw [Fintype.sum_prod_type,polytabloid_coefficient,polytabloid_coefficient,Finset.sum_mul_sum]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) [ρ.IsIrreducible]

lemma span_orbit_eq_top (v : V) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun g : G => ρ g v)) = ⊤ := by
  let U : Subrepresentation ρ := {
    toSubmodule := Submodule.span ℂ (Set.range (fun g : G => ρ g v))
    apply_mem_toSubmodule := by
      intro g w hw
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h,rfl⟩ := hx
        rw [← Module.End.mul_apply,← map_mul]
        exact Submodule.subset_span ⟨g*h,rfl⟩
      | zero => simpa only [map_zero] using Submodule.zero_mem _
      | add x y hx hy hx' hy' => simpa only [map_add] using Submodule.add_mem _ hx' hy'
      | smul c x hx hx' => simpa only [map_smul] using Submodule.smul_mem _ c hx' }
  have hvm : v ∈ U := by
    change v ∈ Submodule.span ℂ (Set.range (fun g : G => ρ g v))
    apply Submodule.subset_span
    exact ⟨1,by simp⟩
  rcases eq_bot_or_eq_top U with h | h
  · have hem : v ∈ (⊥ : Subrepresentation ρ) := h ▸ hvm
    have hv0 : v = 0 := hem
    exact (hv hv0).elim
  · exact congrArg Subrepresentation.toSubmodule h

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CutTensor
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Young
lemma tensor_map_injective_complex {V W X Y : Type*}
    [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (f : V →ₗ[ℂ] X) (g : W →ₗ[ℂ] Y)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  let : AddCommGroup X := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  exact TensorProduct.map_injective_of_flat_flat f g hf hg

variable (μ : YoungDiagram) (p : ℕ)

lemma cutTensorInclude_injective : Function.Injective (cutTensorInclude μ p) := by
  let T := TensorProduct.map (spechtInclude (hookPart μ p)) (spechtInclude (southeast μ p))
  have hT : Function.Injective T := tensor_map_injective_complex
    (spechtInclude (hookPart μ p)) (spechtInclude (southeast μ p))
    (spechtInclude_injective (hookPart μ p)) (spechtInclude_injective (southeast μ p))
  let E := TensorProduct.piScalarRight ℂ ℂ (Tabloid (hookPart μ p) → ℂ) (Tabloid (southeast μ p))
  have hE (u : CutTensor μ p) (t : CutTabloids μ p) :
      E (T u) t.2 t.1 = cutTensorInclude μ p u t := by
    induction u using OAI.tensorInductionOn with
    | tmul v w =>
      change E (spechtInclude _ v ⊗ₜ[ℂ] spechtInclude _ w) t.2 t.1 = _
      simp only [cutTensorInclude_tmul,E,TensorProduct.piScalarRight_apply,
        TensorProduct.piScalarRightHom_tmul,Pi.smul_apply,smul_eq_mul]
      exact mul_comm _ _
    | add u v hu hv => simp only [map_add,Pi.add_apply,hu,hv]
  intro u v h
  apply hT
  apply E.injective
  ext s t
  exact (hE u (t,s)).trans ((congrFun h (t,s)).trans (hE v (t,s)).symm)

lemma cutRestriction_translate (g : G (hookPart μ p) × G (southeast μ p)) :
    cutRestriction μ p (spechtRep μ (cutPerm μ p g) (spechtPoly μ)) =
      cutTensorInclude μ p
        (spechtRep (hookPart μ p) g.1 (spechtPoly (hookPart μ p)) ⊗ₜ[ℂ]
         spechtRep (southeast μ p) g.2 (spechtPoly (southeast μ p))) := by
  ext t
  change spechtInclude μ (spechtRep μ (cutPerm μ p g) (spechtPoly μ))
    (glueTabloid μ p t) = _
  rw [spechtInclude_rep,tabloidRepresentation_apply,← map_inv,← glueTabloid_smul,
    spechtInclude_poly,polytabloid_glue,cutTensorInclude_tmul,
    spechtInclude_rep,spechtInclude_rep]
  rfl

lemma cut_tensor_orbit_mem_range (g : G (hookPart μ p)) (d : G (southeast μ p)) :
    cutTensorInclude μ p (spechtRep (hookPart μ p) g (spechtPoly (hookPart μ p)) ⊗ₜ[ℂ]
      spechtRep (southeast μ p) d (spechtPoly (southeast μ p))) ∈
      LinearMap.range (cutRestriction μ p) :=
  ⟨spechtRep μ (cutPerm μ p (g,d)) (spechtPoly μ),cutRestriction_translate μ p (g,d)⟩

private lemma spechtPoly_span_top (ν : YoungDiagram) :
    Submodule.span ℂ (Set.range (fun g : G ν => spechtRep ν g (spechtPoly ν))) = ⊤ :=
  Irrep.span_orbit_eq_top (spechtRep ν) (spechtPoly ν) (spechtPoly_ne_zero ν)

lemma cut_tensor_tmul_mem_range (v : SpechtSpace (hookPart μ p))
    (w : SpechtSpace (southeast μ p)) :
    cutTensorInclude μ p (v ⊗ₜ[ℂ] w) ∈ LinearMap.range (cutRestriction μ p) := by
  have hv : v ∈ Submodule.span ℂ (Set.range (fun g : G (hookPart μ p) =>
      spechtRep (hookPart μ p) g (spechtPoly (hookPart μ p)))) := by
    rw [spechtPoly_span_top]
    trivial
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    have hw : w ∈ Submodule.span ℂ (Set.range (fun d : G (southeast μ p) =>
        spechtRep (southeast μ p) d (spechtPoly (southeast μ p)))) := by
      rw [spechtPoly_span_top]
      trivial
    induction hw using Submodule.span_induction with
    | mem y hy => obtain ⟨d,rfl⟩ := hy; exact cut_tensor_orbit_mem_range μ p g d
    | zero => simp
    | add x y hx hy hx' hy' => simpa only [TensorProduct.tmul_add,map_add] using Submodule.add_mem _ hx' hy'
    | smul c x hx hx' => simpa only [TensorProduct.tmul_smul,map_smul] using Submodule.smul_mem _ c hx'
  | zero => simp
  | add x y hx hy hx' hy' => simpa only [TensorProduct.add_tmul,map_add] using Submodule.add_mem _ hx' hy'
  | smul c x hx hx' => simpa only [← TensorProduct.smul_tmul',map_smul] using Submodule.smul_mem _ c hx'

theorem cutTensor_range_le : LinearMap.range (cutTensorInclude μ p) ≤
    LinearMap.range (cutRestriction μ p) := by
  rintro _ ⟨u,rfl⟩
  induction u using OAI.tensorInductionOn with
  | tmul v w => exact cut_tensor_tmul_mem_range μ p v w
  | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W P : Type*} [Group G] [Fintype G]
  [AddCommMonoid V] [Module ℂ V] [AddCommMonoid W] [Module ℂ W]
  [AddCommMonoid P] [Module ℂ P]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G P)

lemma averageLinear_lift (l : P →ₗ[ℂ] V) (f : IntertwiningMap ρ σ)
    (g : IntertwiningMap τ σ) (hl : ∀ v, f (l v) = g v) (v : P) :
    f (averageLinear ρ τ l v) = g v := by
  rw [averageLinear_apply,map_smul,map_sum]
  simp only [hl,IntertwiningMap.isIntertwining,
    ← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (show (Fintype.card G : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr Fintype.card_ne_zero),one_smul]

theorem lift_intertwiner (f : IntertwiningMap ρ σ) (g : IntertwiningMap τ σ)
    (h : LinearMap.range g.toLinearMap ≤ LinearMap.range f.toLinearMap) :
    ∃ l : IntertwiningMap τ ρ, ∀ v, f (l v) = g v := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup P := Module.addCommMonoidToAddCommGroup ℂ
  let f0 := f.toLinearMap.rangeRestrict
  obtain ⟨r,hr⟩ := f0.exists_rightInverse_of_surjective f.toLinearMap.range_rangeRestrict
  let g0 : P →ₗ[ℂ] LinearMap.range f.toLinearMap :=
    g.toLinearMap.codRestrict _ (fun v => h ⟨v,rfl⟩)
  let l := r.comp g0
  have hl (v : P) : f (l v) = g v := by
    have hh := DFunLike.congr_fun hr (g0 v)
    exact congrArg Subtype.val hh
  exact ⟨averagedIntertwiner ρ τ l,averageLinear_lift ρ σ τ l f g hl⟩

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_CutBranching
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinaryCoordinateSweeps.Young

local instance instFiniteComplexSpechtSpace (ν : YoungDiagram) : Module.Finite ℂ (SpechtSpace ν) :=
  inferInstanceAs (FiniteDimensional ℂ (SpechtSpace ν))

local instance instIsTorsionFreeComplexSpechtSpace (ν : YoungDiagram) :
    @Module.IsTorsionFree ℂ (SpechtSpace ν) _
      (SpechtSpace.instAddCommGroup ν).toAddCommMonoid inferInstance :=
  DivisionSemiring.to_moduleIsTorsionFree

local instance instFiniteComplexIntertwiningMap_solutions {G V W : Type*} [Monoid G] [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Module.Finite ℂ (Representation.IntertwiningMap ρ σ) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup ℂ
  exact Module.Finite.of_injective (Representation.IntertwiningMap.toLinearMapl (ρ := ρ) (σ := σ))
    (Representation.IntertwiningMap.toLinearMap_injective ρ σ)

section

open scoped BigOperators Classical TensorProduct

open Representation

variable (μ : YoungDiagram) (p : ℕ)

theorem hook_removal_embedding :
    ∃ l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p)),
      Function.Injective l := by
  obtain ⟨l,hl⟩ := Irrep.lift_intertwiner _ _ _
    (cutRestrictionIntertwiner μ p) (cutTensorIntertwiner μ p) (cutTensor_range_le μ p)
  refine ⟨l,?_⟩
  intro v w h
  apply cutTensorInclude_injective μ p
  exact (hl v).symm.trans ((congrArg (cutRestrictionIntertwiner μ p) h).trans (hl w))

lemma cutSliceMap_injective
    (l : IntertwiningMap (cutSpechtRep μ p) ((spechtRep μ).comp (cutPerm μ p)))
    (hl : Function.Injective l) : Function.Injective (cutSliceMap μ p l) := by
  intro w z h
  have hh := DFunLike.congr_fun h (spechtPoly (hookPart μ p))
  change l (_ ⊗ₜ[ℂ] w) = l (_ ⊗ₜ[ℂ] z) at hh
  have he := congrArg (cutTensorInclude μ p) (hl hh)
  apply spechtInclude_injective (southeast μ p)
  ext t
  have ht := congrFun he (tabloidOfPerm (hookPart μ p) 1,t)
  simpa only [cutTensorInclude_tmul,spechtInclude_poly,polytabloid_base,one_mul] using ht

theorem hook_removal_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤
      Module.finrank ℂ (IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p)) := by
  obtain ⟨l,hl⟩ := hook_removal_embedding μ p
  exact LinearMap.finrank_le_finrank_of_injective (cutSliceMap_injective μ p l hl)

end

open scoped BigOperators Classical

open Representation

variable (μ : YoungDiagram) (p : ℕ)

lemma hookPerm_block : hookPerm μ p = Irrep.blockPerm (cutEquiv μ p) := rfl

theorem hook_induced_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤
      Module.finrank ℂ (IntertwiningMap (spechtRep μ) (hookInducedRep μ p)) := by
  have he := (Irrep.coindHomEquiv (hookPerm μ p) (spechtRep μ)
    (spechtRep (hookPart μ p))).finrank_eq
  have hs := Irrep.multiplicity_symm (spechtRep (hookPart μ p)) (hookRestriction μ p)
  change Module.finrank ℂ (IntertwiningMap (spechtRep (hookPart μ p)) (hookRestriction μ p)) =
    Module.finrank ℂ (IntertwiningMap (hookRestriction μ p) (spechtRep (hookPart μ p))) at hs
  exact (hook_removal_multiplicity μ p).trans (by rw [hs]; exact Nat.le_of_eq he)

lemma hook_induced_dimension :
    Module.finrank ℂ (SpechtSpace μ) ≤ Module.finrank ℂ (HookInducedSpace μ p) := by
  have hp : 0 < Module.finrank ℂ (SpechtSpace (southeast μ p)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨spechtPoly _,spechtPoly_ne_zero _⟩
  let : AddCommGroup (HookInducedSpace μ p) := Module.addCommMonoidToAddCommGroup ℂ
  have hi := lt_of_lt_of_le hp (hook_induced_multiplicity μ p)
  obtain ⟨f,hf⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hi
  exact LinearMap.finrank_le_finrank_of_injective
    ((IsIrreducible.injective_or_eq_zero f).resolve_right hf)

theorem hook_removal_dimension_upper :
    Module.finrank ℂ (SpechtSpace μ) ≤
      (Fintype.card (Cell μ))^(Fintype.card (Cell (southeast μ p))) *
        Module.finrank ℂ (SpechtSpace (hookPart μ p)) := by
  apply (hook_induced_dimension μ p).trans
  change Module.finrank ℂ (coindV (hookPerm μ p) _) ≤ _
  exact Irrep.placement_coind_finrank_pow (cutEquiv μ p) (spechtRep (hookPart μ p))

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookInducedMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G H I W : Type*} [Group G] [Group H]
  [Fintype I] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (φ : H →* G) (σ : Representation ℂ H W) (r : I → G)
  (hc : Function.Bijective (fun a : H × I => φ a.1 * r a.2))

omit [Fintype I] in
lemma hilbertBlock_coind (a : G) (i j : I) :
    hilbertBlock (coindHilbertRep φ σ r hc a) i j =
      if cosetIndexAction φ r hc a i = j then
        σ ((cosetEquiv φ r hc).symm (r i*a)).1 else 0 := by
  ext w
  change coindHilbertRep φ σ r hc a (fiberInclude j w) i = _
  rw [coindHilbertRep_apply,fiberInclude_apply]
  split_ifs <;> simp_all

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_PlacementBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation Equiv Equiv.Perm

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
  (e : A ⊕ B ≃ X)

omit [Fintype X] in
lemma placementCoset_index (a : Equiv.Perm X) (y : B ↪ X) :
    cosetIndexAction (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e) a y = y.trans a.symm.toEmbedding := by
  let c := (cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
    (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)
  have he : blockPerm e c.1 * (placementSection e c.2)⁻¹ = (placementSection e y)⁻¹*a :=
    (cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).apply_symm_apply _
  have hi := congrArg (fun g : Equiv.Perm X => g⁻¹) he
  ext b
  have hb := Equiv.congr_fun hi (basePlacement e b)
  simp only [mul_inv_rev,inv_inv,Equiv.Perm.mul_apply,← map_inv,placementSection_apply] at hb
  change placementSection e c.2 ((blockPerm e c.1⁻¹) (e (Sum.inr b))) = _ at hb
  rw [blockPerm_inr] at hb
  exact (placementSection_apply e c.2 b).symm.trans hb

omit [Fintype X] in
lemma placementCoset_subgroup (a : Equiv.Perm X) (y : B ↪ X) :
    blockPerm e ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).1 =
      (placementSection e y)⁻¹*a*placementSection e (y.trans a.symm.toEmbedding) := by
  have he := (cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
    (placement_cosets_bijective e)).apply_symm_apply ((placementSection e y)⁻¹*a)
  change blockPerm e _ * (placementSection e _)⁻¹ = _ at he
  have hi := placementCoset_index e a y
  change ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
    (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).2 = _ at hi
  rw [hi] at he
  exact (mul_inv_eq_iff_eq_mul.mp he)

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (σ : Representation ℂ (Equiv.Perm A) W)

omit [Fintype X] in
lemma placement_hilbertBlock (a : Equiv.Perm X) (x y : B ↪ X) :
    hilbertBlock (coindHilbertRep (blockPerm e) σ (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e) a) y x =
      if x.trans a.toEmbedding = y then
        σ ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
          (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).1 else 0 := by
  rw [hilbertBlock_coind,placementCoset_index]
  congr 1
  apply propext
  constructor
  · intro h
    ext b
    have hb := congrArg (fun x : B ↪ X => a (x b)) h
    exact hb.symm.trans (by simp)
  · intro h
    ext b
    have hb := congrArg (fun x : B ↪ X => a⁻¹ (x b)) h
    simpa using hb.symm

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_SumDite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps
lemma sum_dite_zero {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] (f : ∀ x, P x → M) :
    (∑ x, if h : P x then f x h else 0) = ∑ x : {x // P x}, f x.val x.property := by
  classical
  have he := (Equiv.Set.sumCompl {x | P x}).sum_comp
    (fun x => if h : P x then f x h else 0)
  rw [Fintype.sum_sum_type] at he
  rw [← he]
  simp only [Equiv.Set.sumCompl_apply_inl, Equiv.Set.sumCompl_apply_inr]
  have hp : (∑ x : {x // P x}, if h : P x.val then f x.val h else 0) =
      ∑ x : {x // P x}, f x.val x.property := by
    apply Finset.sum_congr rfl
    intro x _
    exact dite_eq_left x.property
  have hn : (∑ x : {x // ¬P x}, if h : P x.val then f x.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact dite_eq_right x.property
  exact (congrArg₂ (· + ·) hp hn).trans (add_zero _)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_PathExtension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

namespace PathExtension
variable {b h h' : ℕ} {bits : Fin b → ℕ}
  {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma lineInput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineInput H' j y (E.lineEmbedding j y i) = lineInput H j y i := by
  change H'.position j.castSucc (E.labels i.val) j = H.position j.castSucc i.val j
  rw [E.position_eq]

lemma lineOutput_eq (E : PathExtension H H') (j : Fin b) (y : GridOutside bits j)
    (i : LinePaths H j y) :
    lineOutput H' j y (E.lineEmbedding j y i) = lineOutput H j y i := by
  change H'.position j.succ (E.labels i.val) j = H.position j.succ i.val j
  rw [E.position_eq]

end PathExtension

lemma localPathWeight_pos_comparison {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) : 0 < localPathWeight H z j y := by
  unfold localPathWeight
  have hw := @assignmentWeight_comparison (Slot (bits j)) (LinePaths H j y) _ _
    (lineLaw (bits j) z) ?_ ?_ (lineInput H j y) (lineOutput H j y)
  · have hm : 0 < (Nat.descFactorial (Fintype.card (Slot (bits j)))
        (Fintype.card (LinePaths H j y)) : ℝ) := by
      exact_mod_cast Nat.descFactorial_pos.mpr
        (Fintype.card_le_of_injective (lineInput H j y) (lineInput H j y).injective)
    exact lt_of_lt_of_le (by positivity) hw.1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma lineExtension_log_bound {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (j : Fin b) (y : GridOutside bits j) :
    Real.log (localPathWeight H' z j y / localPathWeight H z j y) ≤
      fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
      ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
      Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y) := by
  have he := @assignmentWeight_log_ratio_le (Slot (bits j)) (LinePaths H j y)
    (LinePaths H' j y) _ _ _ Fintype.card_pos (lineLaw (bits j) z)
    ?_ ?_ (lineInput H j y) (lineOutput H j y) (lineInput H' j y) (lineOutput H' j y)
      (E.lineEmbedding j y) (E.lineInput_eq j y) (E.lineOutput_eq j y)
  · simpa only [localPathWeight, lineHoles, Slot, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool] using he
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).1
  · intro σ
    simpa only [uniformLaw, Fintype.card_perm] using
      (lineLaw_comparison r (bits j) (hd j) hz hzr σ).2

lemma log_gridSize {b : ℕ} (bits : Fin b → ℕ) :
    Real.log (gridSize bits : ℝ) = ∑ j, Real.log (2^bits j : ℕ) := by
  unfold gridSize
  rw [Nat.cast_prod, Real.log_prod]
  intro j _
  positivity

lemma sum_lineHoles_sub {b h h' : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (H' : PathFamily bits h') (j : Fin b) :
    ∑ y : GridOutside bits j, ((lineHoles H' j y : ℝ) - lineHoles H j y) = (h' : ℝ) - h := by
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, sum_lineHoles, sum_lineHoles]

lemma pathCost_eq_sum {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) :
    pathCost H = ∑ j, ∑ y, fallingCost (2^bits j) (lineHoles H j y) := rfl

theorem pathExtension_log_ratio {b h h' r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    Real.log (conditionalNormalizer H' z / conditionalNormalizer H z) ≤
      pathCost H' - pathCost H - ((h' : ℝ) - h) * Real.log (gridSize bits) +
        Real.log 4 * ((h' : ℝ) - h) * b := by
  have hposH := localPathWeight_pos_comparison H hd hz hzr
  have hposH' := localPathWeight_pos_comparison H' hd hz hzr
  rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
  rw [← Finset.prod_div_distrib]
  simp_rw [← Finset.prod_div_distrib]
  rw [Real.log_prod (fun j _ => Finset.prod_ne_zero_iff.mpr (fun y _ =>
    (div_pos (hposH' j y) (hposH j y)).ne'))]
  simp_rw [Real.log_prod (fun y _ => (div_pos (hposH' _ y) (hposH _ y)).ne')]
  calc
    _ ≤ ∑ j, ∑ y,
        (fallingCost (2^bits j) (lineHoles H' j y) - fallingCost (2^bits j) (lineHoles H j y) -
        ((lineHoles H' j y : ℝ) - lineHoles H j y) * Real.log (2^bits j : ℕ) +
        Real.log 4 * ((lineHoles H' j y : ℝ) - lineHoles H j y)) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun y _ => lineExtension_log_bound E hd hz hzr j y)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
      simp_rw [sum_lineHoles_sub]
      rw [pathCost_eq_sum, pathCost_eq_sum, log_gridSize]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring

lemma pathExtension_event_ratio {b h h' : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits h'} (E : PathExtension H H') (z : ℝ) :
    conditionalEventWeight H z (pathEvent H') =
      conditionalNormalizer H' z / conditionalNormalizer H z := by
  unfold conditionalEventWeight conditionalChoiceWeight
  have hdiv (g : ConditionalChoices H) :
      (if pathEvent H' g.val then gridWeight bits z g.val / conditionalNormalizer H z else 0) =
      (if pathEvent H' g.val then gridWeight bits z g.val else 0) / conditionalNormalizer H z := by
    split_ifs <;> simp only [zero_div]
  simp_rw [hdiv]
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter (pathEvent H)) (by simp)
    (fun g => if pathEvent H' g then gridWeight bits z g else 0)]
  rw [Finset.sum_filter]
  unfold conditionalNormalizer
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : pathEvent H' g
  · simp only [hg, E.pathEvent_mono hg, ite_true]
  · simp only [hg, ite_false, ite_self]

lemma gridSize_pos {b : ℕ} (bits : Fin b → ℕ) : 0 < gridSize bits := by
  unfold gridSize
  exact Finset.prod_pos (fun j _ => Nat.pow_pos (by norm_num))

theorem pathExtension_probability_bound {b h k r : ℕ} {bits : Fin b → ℕ}
    {H : PathFamily bits h} {H' : PathFamily bits (h+k)} (E : PathExtension H H')
    (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r) :
    conditionalEventWeight H z (pathEvent H') ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost H' - pathCost H + Real.log 4 * k * b) := by
  rw [pathExtension_event_ratio E]
  have hp : 0 < conditionalNormalizer H' z / conditionalNormalizer H z := by
    rw [conditionalNormalizer_eq_prod, conditionalNormalizer_eq_prod]
    apply div_pos <;> apply Finset.prod_pos <;> intro j _ <;>
      apply Finset.prod_pos <;> intro y _
    · exact localPathWeight_pos_comparison H' hd hz hzr j y
    · exact localPathWeight_pos_comparison H hd hz hzr j y
  have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  have he := pathExtension_log_ratio E hd hz hzr
  simp only [Nat.cast_add, add_sub_cancel_left] at he
  calc
    _ ≤ Real.exp (pathCost H' - pathCost H - (k : ℝ) * Real.log (gridSize bits) +
        Real.log 4 * k * b) := (Real.log_le_iff_le_exp hp).mp he
    _ = _ := by
      rw [Real.rpow_def_of_pos hs, ← Real.exp_add]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_ComplementBlocks
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X]

omit [Fintype B] [Fintype X] in
lemma complementMap_val (f : X ≃ Y) (x : B ↪ X) (y : B ↪ Y)
    (hf : x.trans f.toEmbedding=y) (u : PlacementComplement x) :
    (complementMap f x y hf u).val=f u.val := rfl

omit [Fintype B] [Fintype X] in
lemma placement_inverse_event (a : Equiv.Perm X) (x y : B ↪ X)
    (he : x.trans a.toEmbedding=y) : y.trans a.symm.toEmbedding=x := by
  ext b
  change a.symm (y b)=x b
  rw [← he]
  exact a.symm_apply_apply _

omit [Fintype A] [Fintype B] [Fintype X] in
lemma blockPerm_inl (e : A ⊕ B ≃ X) (a : Equiv.Perm A) (u : A) :
    blockPerm e a (e (Sum.inl u))=e (Sum.inl (a u)) := by
  change e (Equiv.sumCongr a (1:Equiv.Perm B) (e.symm (e (Sum.inl u))))=_
  rw [e.symm_apply_apply]
  rfl

omit [Fintype X] in
lemma placement_subgroup_complement (e : A ⊕ B ≃ X) (a : Equiv.Perm X)
    (x y : B ↪ X) (he : x.trans a.toEmbedding=y) :
    ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*a)).1 =
      ((placementComplementEquiv e x).trans (complementMap a x y he)).trans
        (placementComplementEquiv e y).symm := by
  have hh := placementCoset_subgroup e a y
  rw [placement_inverse_event a x y he] at hh
  ext u
  apply (placementComplementEquiv e y).injective
  apply Subtype.ext
  have hu := congrArg (placementSection e y) (Equiv.congr_fun hh (e (Sum.inl u)))
  simp only [blockPerm_inl,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,
    Equiv.apply_symm_apply] at hu
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  change placementSection e y (e (Sum.inl _)) = a (placementSection e x (e (Sum.inl u)))
  simpa only [Equiv.Perm.inv_def] using hu

end BinaryCoordinateSweeps.Irrep

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h h' : ℕ} {bits : Fin b → ℕ}
variable {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma PathExtension.choiceWeight (E : PathExtension H H') (z : ℝ)
    (hpos : conditionalNormalizer H' z ≠ 0) (g : ConditionalChoices H') :
    conditionalChoiceWeight H z (E.restrictChoice g) =
      (conditionalNormalizer H' z / conditionalNormalizer H z) *
        conditionalChoiceWeight H' z g := by
  unfold conditionalChoiceWeight PathExtension.restrictChoice
  simp only
  field_simp

lemma PathExtension.sum_restrict {V : Type*} [AddCommMonoid V]
    (E : PathExtension H H') (f : ConditionalChoices H' → V) :
    (∑g : ConditionalChoices H,
      if hg : pathEvent H' g.val then f ⟨g.val,hg⟩ else 0) =
      ∑g : ConditionalChoices H',f g := by
  have hL := sum_dite_zero (pathEvent H)
    (fun (g : GridChoices bits) (_ : pathEvent H g) =>
      if hg' : pathEvent H' g then f ⟨g,hg'⟩ else 0)
  have hR := sum_dite_zero (pathEvent H') (fun g hg => f ⟨g,hg⟩)
  refine Eq.trans ?_ (Eq.trans hL.symm (Eq.trans ?_ (Eq.trans hR ?_)))
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hg : pathEvent H' g
    · simp only [hg,E.pathEvent_mono hg,dite_eq_left]
    · simp [hg]
  · apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _
    rfl

lemma PathExtension.conditional_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : PathExtension H H') (z : ℝ) (hpos : conditionalNormalizer H' z ≠ 0)
    (f : ConditionalChoices H' → V) :
    (∑g : ConditionalChoices H,
      if hg : pathEvent H' g.val then conditionalChoiceWeight H z g • f ⟨g.val,hg⟩ else 0) =
      (conditionalNormalizer H' z / conditionalNormalizer H z) •
        ∑g : ConditionalChoices H', conditionalChoiceWeight H' z g • f g := by
  rw [Finset.smul_sum]
  simp_rw [← mul_smul]
  rw [← E.sum_restrict (fun g =>
    ((conditionalNormalizer H' z / conditionalNormalizer H z) *
      conditionalChoiceWeight H' z g) • f g)]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs with hg
  · rw [← E.choiceWeight z hpos ⟨g.val,hg⟩]
    rfl
  · rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_Trajectory
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma placementProbability_augmentation {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) =
      conditionalEventWeight H z (pathEvent (augmentByChoice H x g)) := by
  unfold placementProbability conditionalEventWeight
  apply Finset.sum_congr rfl
  intro g' _
  simp only [placementEvent_iff_augmentation]

theorem placement_probability_cost {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (g : ConditionalChoices H) :
    placementProbability H z x (placementBijection H k g x) ≤
      (gridSize bits : ℝ) ^ (-(k : ℝ)) *
        Real.exp (pathCost (augmentByChoice H x g) - pathCost H + Real.log 4 * k * b) := by
  rw [placementProbability_augmentation]
  exact pathExtension_probability_bound (augmentByChoice_extension H x g) hd hz hzr

lemma realizePlacement_spec {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) {k : ℕ}
    (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementBijection H k (realizePlacement H z x y hp) x = y :=
  Classical.choose_spec (placementProbability_pos_has_choice H z x y hp)

theorem placement_probability_cost_of_pos {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    {k : ℕ} (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hp : 0 < placementProbability H z x y) :
    placementProbability H z x y ≤ (gridSize bits : ℝ) ^ (-(k : ℝ)) *
      Real.exp (placementTransitionCost H z x y - pathCost H + Real.log 4 * k * b) := by
  have he := placement_probability_cost H hd hz hzr x (realizePlacement H z x y hp)
  unfold placementTransitionCost
  rw [dite_eq_left hp]
  rwa [realizePlacement_spec] at he

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Trajectories_TrajectoryComplement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g : ConditionalChoices H)

lemma augmented_gridSweep (g' : ConditionalChoices (augmentByChoice H x g))
    (w : FreeSlot (augmentByChoice H x g) 0) :
    (augmentationFreeEquiv H x g (Fin.last b)
      (remainingBijection (augmentByChoice H x g) g'.val g'.property w)).val =
      remainingBijection H g'.val
        ((augmentByChoice_extension H x g).pathEvent_mono g'.property)
        (augmentationFreeEquiv H x g 0 w).val := rfl

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_AugmentedComplement
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g₀ : ConditionalChoices H)

lemma augmentationOutputComplement_val (w : FreeSlot (augmentByChoice H x g₀) (Fin.last b)) :
    (augmentationOutputComplement H x g₀ w).val=
      (freeIdentification H).symm (augmentationFreeEquiv H x g₀ (Fin.last b) w).val := rfl

lemma augmentation_complement_square (g : ConditionalChoices (augmentByChoice H x g₀))
    (w : FreeSlot (augmentByChoice H x g₀) 0) :
    augmentationOutputComplement H x g₀
      (remainingBijection (augmentByChoice H x g₀) g.val g.property w) =
      complementMap (remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))
        x (augmentedOutputIndex H x g₀)
        (augmented_event H x g₀ g)
        (augmentationInputComplement H x g₀ w) := by
  apply Subtype.ext
  rw [augmentationOutputComplement_val,complementMap_val]
  exact congrArg (freeIdentification H).symm (augmented_gridSweep H x g₀ g w)

variable {A : Type*} [Fintype A] (e : A ⊕ Fin k ≃ FreeSlot H 0)

lemma augmented_subgroup_bijection (g : ConditionalChoices (augmentByChoice H x g₀)) :
    ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm
        ((placementSection e (augmentedOutputIndex H x g₀))⁻¹*
          remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))).1 =
      ((augmentedInputBasis H x g₀ e).trans
        (remainingBijection (augmentByChoice H x g₀) g.val g.property)).trans
          (augmentedOutputBasis H x g₀ e).symm := by
  rw [placement_subgroup_complement e
    (remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))
    x (augmentedOutputIndex H x g₀) (augmented_event H x g₀ g)]
  ext a
  apply (placementComplementEquiv e (augmentedOutputIndex H x g₀)).injective
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply,augmentedInputBasis,augmentedOutputBasis,
    Equiv.symm_trans_apply]
  exact (augmentation_complement_square H x g₀ g
    ((augmentationInputComplement H x g₀).symm (placementComplementEquiv e x a))).symm.trans
      (by rfl)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_SparseBounds_ConditionalCentered
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Sparse

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma conditionalGroupLaw_expectation {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (z : ℝ) (f : Equiv.Perm (FreeSlot H 0) → W) :
    (∑a, conditionalGroupLaw H z a • f a) =
      ∑g : ConditionalChoices H, conditionalChoiceWeight H z g • f (remainingPerm H g.val g.property) := by
  unfold conditionalGroupLaw
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [ite_smul,zero_smul]
  simp

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_AugmentedBlock
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (x : Placement H k 0) (g₀ : ConditionalChoices H)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

lemma augmented_subgroup_perm (g : ConditionalChoices (augmentByChoice H x g₀)) :
    ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm
        ((placementSection e (augmentedOutputIndex H x g₀))⁻¹*
          remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))).1 =
      augmentedFrame H x g₀ e * (augmentedInputBasis H x g₀ e).symm.permCongr
        (remainingPerm (augmentByChoice H x g₀) g.val g.property) := by
  rw [augmented_subgroup_bijection]
  ext a
  simp only [augmentedFrame,Equiv.Perm.mul_apply,Equiv.permCongr_apply,Equiv.trans_apply,
    Equiv.symm_symm,Equiv.apply_symm_apply,remainingPerm]

omit [FiniteDimensional ℂ W] in
lemma placementBlock_expectation (z : ℝ) (y : Placement H k 0) :
    hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) y x =
    ∑g : ConditionalChoices H, conditionalChoiceWeight H z g •
      (if x.trans (remainingPerm H g.val g.property).toEmbedding=y then
        σ ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
          (placement_cosets_bijective e)).symm ((placementSection e y)⁻¹*
            remainingPerm H g.val g.property)).1 else 0) := by
  have hs (r : ℝ) (T : W →ₗ[ℂ] W) : (r:ℂ) • T = r • T :=
    algebraMap_smul ℂ r T
  calc
    _ = ∑a, conditionalGroupLaw H z a •
        hilbertBlock (coindHilbertRep (blockPerm e) σ (fun x => (placementSection e x)⁻¹)
          (placement_cosets_bijective e) a) y x := by
      ext v
      simp only [groupAverage,hilbertBlock,LinearMap.comp_apply,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
      apply Finset.sum_congr rfl
      intro a _
      exact algebraMap_smul ℂ (conditionalGroupLaw H z a) _
    _ = _ := by
      rw [conditionalGroupLaw_expectation]
      apply Finset.sum_congr rfl
      intro g _
      rw [placement_hilbertBlock]
      split_ifs <;> rfl

omit [FiniteDimensional ℂ W] in
theorem augmented_block_average (z : ℝ)
    (hp : conditionalNormalizer (augmentByChoice H x g₀) z≠0) :
    hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) (augmentedOutputIndex H x g₀) x =
    (conditionalNormalizer (augmentByChoice H x g₀) z / conditionalNormalizer H z) •
      (σ (augmentedFrame H x g₀ e) *
        groupAverage (augmentedRepresentation H x g₀ e σ)
          (fun a => (conditionalGroupLaw (augmentByChoice H x g₀) z a:ℂ))) := by
  rw [placementBlock_expectation]
  have he := (augmentByChoice_extension H x g₀).conditional_sum z hp
    (fun g => σ ((cosetEquiv (blockPerm e) (fun x => (placementSection e x)⁻¹)
      (placement_cosets_bijective e)).symm ((placementSection e (augmentedOutputIndex H x g₀))⁻¹*
        remainingPerm H g.val ((augmentByChoice_extension H x g₀).pathEvent_mono g.property))).1)
  refine Eq.trans ?_ (Eq.trans he ?_)
  · apply Finset.sum_congr rfl
    intro g _
    by_cases hg : pathEvent (augmentByChoice H x g₀) g.val
    · rw [dite_eq_left hg,ite_eq_left ((augmentedOutputIndex_event H x g₀ g).mpr hg)]
    · rw [dite_eq_right hg,ite_eq_right (fun he => hg ((augmentedOutputIndex_event H x g₀ g).mp he)),smul_zero]
  · congr 1
    simp_rw [augmented_subgroup_perm,map_mul]
    rw [groupAverage]
    have hh := conditionalGroupLaw_expectation (augmentByChoice H x g₀) z
      (fun a => augmentedRepresentation H x g₀ e σ a)
    have hc : (∑a, (conditionalGroupLaw (augmentByChoice H x g₀) z a:ℂ) •
        augmentedRepresentation H x g₀ e σ a) =
        ∑g : ConditionalChoices (augmentByChoice H x g₀),
          conditionalChoiceWeight (augmentByChoice H x g₀) z g •
            augmentedRepresentation H x g₀ e σ (remainingPerm (augmentByChoice H x g₀) g.val g.property) := by
      refine Eq.trans ?_ hh
      apply Finset.sum_congr rfl
      intro a _
      exact algebraMap_smul ℂ (conditionalGroupLaw (augmentByChoice H x g₀) z a)
        (augmentedRepresentation H x g₀ e σ a)
    rw [hc,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_smul_comm]
    rfl

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma placementBijection_index (x : Placement H k 0) (g : ConditionalChoices H) :
    placementBijection H k g x = placementIdentification H k (augmentedOutputIndex H x g) := by
  apply Function.Embedding.ext
  intro i
  change remainingBijection H g.val g.property (x i) =
    freeIdentification H ((freeIdentification H).symm (remainingBijection H g.val g.property (x i)))
  exact (Equiv.apply_symm_apply _ _).symm

lemma placementKernel_ratio (z : ℝ) (x : Placement H k 0) (g : ConditionalChoices H) :
    placementKernel H z x (augmentedOutputIndex H x g) =
      conditionalNormalizer (augmentByChoice H x g) z / conditionalNormalizer H z := by
  unfold placementKernel
  rw [← placementBijection_index H x g,placementProbability_augmentation,
    pathExtension_event_ratio (augmentByChoice_extension H x g)]

lemma placementKernel_output_pos {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (x : Placement H k 0) (g : ConditionalChoices H) :
    0<placementKernel H z x (augmentedOutputIndex H x g) := by
  rw [placementKernel_ratio]
  exact div_pos (conditionalNormalizer_pos _ hz hz1) (conditionalNormalizer_pos _ hz hz1)

variable {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

omit [FiniteDimensional ℂ W] in
lemma placementBlock_zero {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (x y : Placement H k 0) (hp : placementKernel H z x y=0) :
    hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) y x = 0 := by
  rw [placementBlock_expectation]
  apply Finset.sum_eq_zero
  intro g _
  have hn : x.trans (remainingPerm H g.val g.property).toEmbedding ≠ y := by
    intro he
    have ht := placementKernel_output_pos H hz hz1 x g
    change 0<placementKernel H z x (x.trans (remainingPerm H g.val g.property).toEmbedding) at ht
    rw [he,hp] at ht
    exact (lt_irrefl 0 ht)
  rw [ite_eq_right hn,smul_zero]

lemma placementBlock_moment {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) (q : ℕ)
    (x : Placement H k 0) (g : ConditionalChoices H) :
    evenMoment q (hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) (augmentedOutputIndex H x g) x) =
    (placementKernel H z x (augmentedOutputIndex H x g))^(2*q) *
      evenMoment q (groupAverage (augmentedRepresentation H x g e σ)
        (fun a => (conditionalGroupLaw (augmentByChoice H x g) z a:ℂ))) := by
  rw [augmented_block_average H x g e σ z (conditionalNormalizer_pos _ hz hz1).ne',
    evenMoment_smul,evenMoment_unitary_left]
  · rw [placementKernel_ratio]
  · rw [unitary_rep_adjoint σ hσ,←map_mul,inv_mul_cancel,map_one]

lemma placementBlock_moment_root {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q)
    (x : Placement H k 0) (g : ConditionalChoices H) :
    evenMoment q (hilbertBlock (groupAverage (coindHilbertRep (blockPerm e) σ
      (fun x => (placementSection e x)⁻¹) (placement_cosets_bijective e))
      (fun a => (conditionalGroupLaw H z a:ℂ))) (augmentedOutputIndex H x g) x)^(((2*q:ℕ):ℝ)⁻¹) =
    placementKernel H z x (augmentedOutputIndex H x g) *
      evenMoment q (groupAverage (augmentedRepresentation H x g e σ)
        (fun a => (conditionalGroupLaw (augmentByChoice H x g) z a:ℂ)))^(((2*q:ℕ):ℝ)⁻¹) := by
  rw [placementBlock_moment H e σ hz hz1 hσ]
  have hp := (placementKernel_output_pos H hz hz1 x g).le
  rw [Real.mul_rpow (pow_nonneg hp _) (evenMoment_nonneg _ _),
    ← Real.rpow_natCast,← Real.rpow_mul hp]
  have hn : ((2*q:ℕ):ℝ)≠0 := by positivity
  rw [mul_inv_cancel₀ hn,Real.rpow_one]

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_BlockTrace
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace BinaryCoordinateSweeps.TraceHolder

section Expansion
variable {P R : Type*} [Fintype P] [DecidableEq P] [Semiring R]

omit [Fintype P] [DecidableEq P] in
lemma snoc_cons_succ {n : ℕ} (a : P) (x : Fin n → P) (b : P) (j : Fin (n+1)) :
    Fin.snoc (α := fun _ => P) (Fin.cons a x) b j.succ =
      Fin.snoc (α := fun _ => P) x b j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.cons_succ]

omit [Fintype P] [DecidableEq P] in
lemma pathProduct_cons {n : ℕ} (A : Fin (n+1) → Matrix P P R)
    (a : P) (x : Fin n → P) (b : P) :
    pathProduct A (Fin.cons a x) b =
      A 0 a (Fin.snoc (α := fun _ => P) x b 0) * pathProduct (fun j => A j.succ) x b := by
  simp only [pathProduct, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ,
    snoc_cons_succ]

lemma prod_apply_sum_path {n : ℕ} (A : Fin (n+1) → Matrix P P R) (a b : P) :
    (List.ofFn A).prod a b = ∑ x : Fin n → P, pathProduct A (Fin.cons a x) b := by
  induction n generalizing a with
  | zero => simp [pathProduct, Fin.snoc]
  | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
      simp_rw [ih]
      rw [← (Fin.consEquiv (fun _ : Fin (n+1) => P)).sum_comp, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      change A 0 a c * pathProduct (fun j => A j.succ) (Fin.cons c x) b =
        pathProduct A (Fin.cons a (Fin.cons c x)) b
      rw [pathProduct_cons A]
      congr 2

omit [Fintype P] [DecidableEq P] in
lemma snoc_cycle {n : ℕ} (x : Fin (n+1) → P) (j : Fin (n+1)) :
    Fin.snoc (α := fun _ => P) x (x 0) j.succ = x (finRotate (n+1) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    simp [finRotate_apply, Fin.coeSucc_eq_succ]

lemma trace_prod_eq_sum_cycles {n : ℕ} (A : Fin (n+1) → Matrix P P R) :
    Matrix.trace (List.ofFn A).prod =
      ∑ x : Fin (n+1) → P,
        (List.ofFn fun j => A j (x j) (x (finRotate (n+1) j))).prod := by
  change (∑ i : P, (List.ofFn A).prod i i) = _
  simp_rw [prod_apply_sum_path]
  calc
    _ = ∑ y : P × (Fin n → P), pathProduct A (Fin.cons y.1 y.2) y.1 := by
      exact (Fintype.sum_prod_type (fun y : P × (Fin n → P) =>
        pathProduct A (Fin.cons y.1 y.2) y.1)).symm
    _ = ∑ x : Fin (n+1) → P, pathProduct A x (x 0) := by
      simpa only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero] using
        (Fin.consEquiv (fun _ : Fin (n+1) => P)).sum_comp (fun x => pathProduct A x (x 0))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [pathProduct, snoc_cycle]
end Expansion

end BinaryCoordinateSweeps.TraceHolder

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_MatrixBounds_HilbertBlockTrace
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open TraceHolder

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
local notation "HW" => CoindHilbertSpace (I:=I) (W:=W)

omit [DecidableEq I] [FiniteDimensional ℂ W] in
lemma fiber_identity : (∑i : I, (fiberInclude i).comp (fiberProject i))=(1 : HW →ₗ[ℂ] HW) := by
  apply LinearMap.ext
  intro v
  simpa only [LinearMap.sum_apply,LinearMap.comp_apply, fiberProject, Module.End.one_apply,
    LinearEquiv.coe_coe, LinearMap.proj_apply, WithLp.coe_linearEquiv] using fiber_sum v

lemma fiber_adjoint (i : I) : (fiberInclude i : W →ₗ[ℂ] HW).adjoint=fiberProject i := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply,fiberInclude_apply,apply_ite,inner_zero_right]
  change _ = ∑j, if j=i then inner ℂ (x j) y else 0
  simp only [fiberProject,LinearMap.comp_apply,LinearMap.proj_apply,LinearEquiv.coe_coe,
    WithLp.coe_linearEquiv,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma hilbertBlock_adjoint (A : HW →ₗ[ℂ] HW) (i j : I) :
    hilbertBlock A.adjoint i j=(hilbertBlock A j i).adjoint := by
  unfold hilbertBlock
  rw [LinearMap.adjoint_comp,LinearMap.adjoint_comp,fiber_adjoint,
    ← fiber_adjoint (W:=W) j,LinearMap.adjoint_adjoint]
  rfl

omit [DecidableEq I] in
lemma trace_hilbertBlocks (A : HW →ₗ[ℂ] HW) :
    LinearMap.trace ℂ HW A = ∑i, LinearMap.trace ℂ W (hilbertBlock A i i) := by
  conv_lhs => rw [← mul_one A,← fiber_identity]
  rw [Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.trace ℂ HW ((A.comp (fiberInclude i)).comp (fiberProject i)) = _
  rw [LinearMap.trace_comp_comm']
  rfl

lemma trace_hilbertBlocks_prod {n : ℕ} (A : Fin (n+1) → HW →ₗ[ℂ] HW) :
    LinearMap.trace ℂ HW (List.ofFn A).prod =
      ∑x : Fin (n+1) → I, LinearMap.trace ℂ W
        (List.ofFn (fun j => hilbertBlock (A j) (x j) (x (finRotate (n+1) j)))).prod := by
  rw [trace_hilbertBlocks]
  rw [← map_sum]
  change LinearMap.trace ℂ W (Matrix.trace (hilbertBlocksHom (I:=I) (W:=W) (List.ofFn A).prod)) = _
  have hm := (hilbertBlocksHom (I:=I) (W:=W)).map_list_prod (List.ofFn A)
  rw [List.map_ofFn] at hm
  rw [hm,trace_prod_eq_sum_cycles,map_sum]
  rfl

theorem hilbert_block_trace_holder {q : ℕ} (hq : 0<q) (A : Fin (2*q) → HW →ₗ[ℂ] HW) :
    ‖LinearMap.trace ℂ HW (List.ofFn A).prod‖ ≤
      ∑x : Fin (2*q) → I, ∏j,
        evenMoment q (hilbertBlock (A j) (x j) (x (finRotate (2*q) j)))^(((2*q:ℕ):ℝ)⁻¹) := by
  have ht : LinearMap.trace ℂ HW (List.ofFn A).prod =
      ∑x : Fin (2*q) → I, LinearMap.trace ℂ W
        (List.ofFn (fun j => hilbertBlock (A j) (x j) (x (finRotate (2*q) j)))).prod := by
    generalize hm : 2*q=m at A ⊢
    cases m with
    | zero => omega
    | succ n => exact trace_hilbertBlocks_prod A
  rw [ht]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => linear_trace_holder hq _))

theorem evenMoment_blocks_le {q : ℕ} (hq : 0<q) (K : HW →ₗ[ℂ] HW) :
    evenMoment q K ≤ ∑x : Fin (2*q) → I, ∏j,
      (if j.val%2=0 then
        evenMoment q (hilbertBlock K (x (finRotate (2*q) j)) (x j))
      else evenMoment q (hilbertBlock K (x j) (x (finRotate (2*q) j))))^(((2*q:ℕ):ℝ)⁻¹) := by
  have ht := hilbert_block_trace_holder hq
    (fun j : Fin (2*q) => if j.val%2=0 then K.adjoint else K)
  rw [alternating_prod] at ht
  refine (Complex.re_le_norm _).trans (ht.trans_eq ?_)
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp only [hilbertBlock_adjoint,evenMoment_adjoint]

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_PlacementCycleMoment
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

lemma realizedOutputIndex (z : ℝ) (x y : Placement H k 0)
    (hp : 0<placementKernel H z x y) :
    augmentedOutputIndex H x (realizePlacement H z x (placementIdentification H k y) hp)=y := by
  apply (placementIdentification H k).injective
  rw [←placementBijection_index]
  exact realizePlacement_spec H z x (placementIdentification H k y) hp

lemma inducedPlacementBlock_root {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q)
    (x y : Placement H k 0) :
    evenMoment q (hilbertBlock (inducedPlacementAverage H e σ z) y x)^(((2*q:ℕ):ℝ)⁻¹) =
      placementKernel H z x y * (placementFiberMoment H e σ z q x y)^(((2*q:ℕ):ℝ)⁻¹) := by
  by_cases hp : 0<placementKernel H z x y
  · unfold placementFiberMoment
    rw [dite_eq_left hp]
    have he := placementBlock_moment_root H e σ hz hz1 hσ hq x
      (realizePlacement H z x (placementIdentification H k y) hp)
    rw [realizedOutputIndex H z x y hp] at he
    exact he
  · have he : placementKernel H z x y=0 :=
      le_antisymm (le_of_not_gt hp) (placementKernel_nonneg H hz hz1 x y)
    rw [he,zero_mul,placementBlock_zero H e σ hz hz1 x y he]
    have hq0 : q≠0 := hq.ne'
    simp [evenMoment,hq0]

theorem induced_placement_cycle_bound {z : ℝ} (hz : 0≤z) (hz1 : z<1)
    (hσ : ∀ g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q) :
    evenMoment q (inducedPlacementAverage H e σ z) ≤
      ∑x : Fin (2*q) → Placement H k 0,
        (∏j, placementEdge H z (decide (j.val%2≠0)) (x j) (x (finRotate (2*q) j))) *
        ∏j, (if j.val%2=0 then
          placementFiberMoment H e σ z q (x j) (x (finRotate (2*q) j))
        else placementFiberMoment H e σ z q (x (finRotate (2*q) j)) (x j))^(((2*q:ℕ):ℝ)⁻¹) := by
  refine (evenMoment_blocks_le hq (inducedPlacementAverage H e σ z)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro x _
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases he : j.val%2=0
  · simp only [placementEdge,decide_eq_true_eq,ne_eq,he,not_true_eq_false,ite_false,ite_true]
    exact inducedPlacementBlock_root H e σ hz hz1 hσ hq _ _
  · simp only [placementEdge,decide_eq_true_eq,ne_eq,he,not_false_eq_true,ite_true,ite_false]
    exact inducedPlacementBlock_root H e σ hz hz1 hσ hq _ _

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_WeightedCycle
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

lemma weighted_entry_bound (n : ℕ) {p C a : ℝ} (hp : 0 ≤ p)
    (hbound : 0 < p → p ≤ Real.exp (C + a)) :
    p * Real.exp (-C / (n+1 : ℝ)) ≤
      Real.exp (a / (n+1 : ℝ)) * p ^ ((n : ℝ) / (n+1 : ℝ)) := by
  rcases hp.eq_or_lt with hp | hp
  · subst p
    simp only [zero_mul]
    positivity
  have hn : (0 : ℝ) < n+1 := by positivity
  have hl : Real.log p ≤ C + a := (Real.log_le_iff_le_exp hp).mpr (hbound hp)
  have he : Real.log p + -C / (n+1 : ℝ) ≤
      a / (n+1 : ℝ) + Real.log p * ((n : ℝ) / (n+1 : ℝ)) := by
    apply (mul_le_mul_iff_left₀ hn).mp
    field_simp
    nlinarith [hl]
  calc
    _ = Real.exp (Real.log p + -C / (n+1 : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hp]
    _ ≤ Real.exp (a / (n+1 : ℝ) + Real.log p * ((n : ℝ) / (n+1 : ℝ))) :=
      Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add, Real.rpow_def_of_pos hp]

theorem weighted_cycle_le_card {A : Type*} [Fintype A] (n : ℕ)
    (p C : Fin (n+1) → A → A → ℝ) (a : ℝ)
    (hp : ∀ i x y, 0 ≤ p i x y)
    (hsum : ∀ i y, ∑ x, p i x y = 1)
    (hbound : ∀ i x y, 0 < p i x y → p i x y ≤ Real.exp (C i x y + a)) :
    (∑ x : Fin (n+1) → A,
      ∏ i, p i (x i) (x (finRotate (n+1) i)) *
        Real.exp (-C i (x i) (x (finRotate (n+1) i)) / (n+1 : ℝ))) ≤
      Real.exp a * (Fintype.card A : ℝ) := by
  have hconstant : (∏ _i : Fin (n+1), Real.exp (a / (n+1 : ℝ))) = Real.exp a := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  calc
    _ ≤ ∑ x : Fin (n+1) → A,
      ∏ i, Real.exp (a / (n+1 : ℝ)) *
        (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.prod_le_prod
      · intro i _; exact mul_nonneg (hp _ _ _) (Real.exp_pos _).le
      · intro i _; exact weighted_entry_bound n (hp _ _ _) (hbound _ _ _)
    _ = Real.exp a * (∑ x : Fin (n+1) → A,
      ∏ i, (p i (x i) (x (finRotate (n+1) i))) ^ ((n : ℝ) / (n+1 : ℝ))) := by
      simp_rw [Finset.prod_mul_distrib, hconstant]
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Cyclic.sum_cycle_rpow_le_card n p hp hsum)
      (Real.exp_pos a).le

lemma placementEdge_bound {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (reverse : Bool) {k : ℕ} (x y : Placement H k 0)
    (hp : 0 < placementEdge H z reverse x y) :
    placementEdge H z reverse x y ≤
      Real.exp (placementEdgeCost H z reverse x y +
        (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b)) := by
  have hsingle (x y : Placement H k 0) (hp : 0 < placementKernel H z x y) :
      placementKernel H z x y ≤ Real.exp (
        placementTransitionCost H z x (placementIdentification H k y) +
        (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b)) := by
    have hc := placement_probability_cost_of_pos H hd hz hzr x
      (placementIdentification H k y) hp
    have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
    rw [Real.rpow_def_of_pos hs, ← Real.exp_add] at hc
    convert hc using 1 <;> congr 1
    ring
  cases reverse with
  | false => exact hsingle x y hp
  | true => exact hsingle y x hp

lemma linePerturbationRadius_lt_one (r : ℕ) : linePerturbationRadius r < 1 := by
  have hf : (1 : ℝ) ≤ ((2 ^ (2 * r)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 ^ (2 * r))
  unfold linePerturbationRadius
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem placement_weighted_cycle_bound {b h r : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (hd : ∀ j, bits j ≤ 2*r) {z : ℝ}
    (hz : 0 ≤ z) (hzr : z ≤ linePerturbationRadius r)
    (k n : ℕ) (reverse : Fin (n+1) → Bool) :
    (∑ x : Fin (n+1) → Placement H k 0,
      ∏ i, placementEdge H z (reverse i) (x i) (x (finRotate (n+1) i)) *
        Real.exp (-placementEdgeCost H z (reverse i) (x i) (x (finRotate (n+1) i)) /
          (n+1 : ℝ))) ≤ Real.exp (-pathCost H + Real.log 4 * k * b) := by
  have hz1 := hzr.trans_lt (linePerturbationRadius_lt_one r)
  have hc := weighted_cycle_le_card (A := Placement H k 0) n
    (fun i => placementEdge H z (reverse i))
    (fun i => placementEdgeCost H z (reverse i))
    (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b)
    (by
      intro i x y
      unfold placementEdge
      split_ifs <;> exact placementKernel_nonneg H hz hz1 _ _)
    (by
      intro i y
      unfold placementEdge
      cases reverse i with
      | false => exact placementKernel_colSum H hz hz1 y
      | true => exact placementKernel_rowSum H hz hz1 y)
    (by intro i x y hp; exact placementEdge_bound H hd hz hzr (reverse i) x y hp)
  rw [card_placement] at hc
  apply hc.trans
  have hcard : ((gridSize bits - h).descFactorial k : ℝ) ≤ (gridSize bits : ℝ) ^ k := by
    exact_mod_cast (Nat.descFactorial_le_pow (gridSize bits - h) k).trans
      (Nat.pow_le_pow_left (Nat.sub_le (gridSize bits) h) k)
  have hs : (0 : ℝ) < gridSize bits := by exact_mod_cast gridSize_pos bits
  calc
    _ ≤ Real.exp (-(k : ℝ) * Real.log (gridSize bits) - pathCost H + Real.log 4 * k * b) *
          (gridSize bits : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hcard (Real.exp_pos _).le
    _ = _ := by
      have he : (gridSize bits : ℝ) ^ k =
          Real.exp ((k : ℝ) * Real.log (gridSize bits)) := by
        rw [Real.exp_nat_mul, Real.exp_log hs]
      rw [he, ← Real.exp_add]
      congr 1
      ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Conditional_CycleAugmentation
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  {A W : Type*} [Fintype A] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W] (e : A ⊕ Fin k ≃ FreeSlot H 0)
  (σ : Representation ℂ (Equiv.Perm A) W)

lemma placement_weighted_cycle_bound_pos (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r)
    {N : ℕ} (hN : 0<N) (reverse : Fin N → Bool) :
    (∑x : Fin N → Placement H k 0, ∏i,
      placementEdge H z (reverse i) (x i) (x (finRotate N i))*
      Real.exp (-placementEdgeCost H z (reverse i) (x i) (x (finRotate N i))/(N:ℝ))) ≤
      Real.exp (-pathCost H+Real.log 4*k*b) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  simpa only [Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one] using
    placement_weighted_cycle_bound H hd hz hzr k n reverse

omit [Fintype A] in
lemma placementFiberMoment_nonneg (z : ℝ) (q : ℕ) (x y : Placement H k 0) :
    0≤placementFiberMoment H e σ z q x y := by
  unfold placementFiberMoment
  split_ifs
  · exact evenMoment_nonneg _ _
  · rfl

theorem induced_placement_of_hook_bound (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r)
    (hσ : ∀g v, ‖σ g v‖=‖v‖) {q : ℕ} (hq : 0<q) (B : ℝ)
    (hf : ∀x y : Placement H k 0, 0<placementKernel H z x y →
      placementFiberMoment H e σ z q x y ≤
        Real.exp (B-placementTransitionCost H z x (placementIdentification H k y))) :
    evenMoment q (inducedPlacementAverage H e σ z) ≤
      Real.exp (B-pathCost H+Real.log 4*k*b) := by
  have hz1 := hzr.trans_lt (linePerturbationRadius_lt_one r)
  have hqR : (0:ℝ)<(2*q:ℕ) := by positivity
  have hf' (x y : Placement H k 0) :
      (placementFiberMoment H e σ z q x y)^(((2*q:ℕ):ℝ)⁻¹) ≤
        Real.exp (B/((2*q:ℕ):ℝ))*
          Real.exp (-placementTransitionCost H z x (placementIdentification H k y)/((2*q:ℕ):ℝ)) := by
    have hle : placementFiberMoment H e σ z q x y ≤
        Real.exp (B-placementTransitionCost H z x (placementIdentification H k y)) := by
      by_cases hp : 0<placementKernel H z x y
      · exact hf x y hp
      · simp only [placementFiberMoment,dite_eq_right hp]
        exact (Real.exp_pos _).le
    refine (Real.rpow_le_rpow (placementFiberMoment_nonneg H e σ z q x y) hle
      (inv_nonneg.mpr hqR.le)).trans_eq ?_
    rw [←Real.exp_mul,←Real.exp_add]
    congr 1
    ring
  have hconst : (∏_j : Fin (2*q), Real.exp (B/((2*q:ℕ):ℝ)))=Real.exp B := by
    rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.exp_nat_mul]
    congr 1
    field_simp
  let rev (j : Fin (2*q)) := decide (j.val%2≠0)
  have hedge (x : Fin (2*q) → Placement H k 0) (j : Fin (2*q)) :
      (if j.val%2=0 then placementFiberMoment H e σ z q (x j) (x (finRotate (2*q) j))
        else placementFiberMoment H e σ z q (x (finRotate (2*q) j)) (x j))^(((2*q:ℕ):ℝ)⁻¹) ≤
        Real.exp (B/((2*q:ℕ):ℝ))*
          Real.exp (-placementEdgeCost H z (rev j) (x j) (x (finRotate (2*q) j))/((2*q:ℕ):ℝ)) := by
    by_cases hj : j.val%2=0
    · simpa only [rev,placementEdgeCost,decide_eq_true_eq,ne_eq,hj,not_false_eq_true,not_true_eq_false,
        ite_true,ite_false] using hf' (x j) (x (finRotate (2*q) j))
    · simpa only [rev,placementEdgeCost,decide_eq_true_eq,ne_eq,hj,not_false_eq_true,not_true_eq_false,
        ite_true,ite_false] using hf' (x (finRotate (2*q) j)) (x j)
  have hs := induced_placement_cycle_bound H e σ hz hz1 hσ hq
  refine hs.trans ?_
  calc
    _ ≤ ∑x : Fin (2*q) → Placement H k 0,
      (∏j, placementEdge H z (rev j) (x j) (x (finRotate (2*q) j)))*
        ∏j, (Real.exp (B/((2*q:ℕ):ℝ))*
          Real.exp (-placementEdgeCost H z (rev j) (x j) (x (finRotate (2*q) j))/((2*q:ℕ):ℝ))) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left
      · apply Finset.prod_le_prod
        · intro j _
          apply Real.rpow_nonneg
          split_ifs <;> exact placementFiberMoment_nonneg H e σ z q _ _
        · intro j _; exact hedge x j
      · apply Finset.prod_nonneg
        intro j _
        unfold placementEdge
        split_ifs <;> exact placementKernel_nonneg H hz hz1 _ _
    _ = Real.exp B * (∑x : Fin (2*q) → Placement H k 0, ∏j,
      placementEdge H z (rev j) (x j) (x (finRotate (2*q) j))*
        Real.exp (-placementEdgeCost H z (rev j) (x j) (x (finRotate (2*q) j))/((2*q:ℕ):ℝ))) := by
      simp_rw [Finset.prod_mul_distrib,hconst]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ ≤ Real.exp B * Real.exp (-pathCost H+Real.log 4*k*b) :=
      mul_le_mul_of_nonneg_left (placement_weighted_cycle_bound_pos H hd hz hzr
        (by omega) rev) (Real.exp_pos B).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalRigidity
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma diagonal_rigidity_aux {X : Type*} [Fintype X] (A B : X → ℝ)
    (r c : Equiv.Perm X) (hr : ∀ x, A (r x) = A x)
    (hc : ∀ x, B (c x) = B x)
    (hd : ∀ x, A ((r*c) x) + B ((r*c) x) = A x + B x) :
    ∀ x, A (c x) = A x := by
  have hq (x : X) : B ((r*c) x) = A x + B x - A (c x) := by
    have he := hd x
    change A (r (c x)) + _ = _ at he
    rw [hr] at he
    linarith
  have hxc : ∑ x, A (c x) * B x = ∑ x, A x * B x := by
    simpa only [hc] using Equiv.sum_comp c (fun x => A x * B x)
  have hxx : ∑ x, (A (c x))^2 = ∑ x, (A x)^2 :=
    Equiv.sum_comp c (fun x => (A x)^2)
  have hprod : ∑ x, (A (c x) * A x + A (c x) * B x - (A (c x))^2) =
      ∑ x, A x * B x := by
    calc
      _ = ∑ x, A ((r*c) x) * B ((r*c) x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hq]
        change _ = A (r (c x)) * _
        rw [hr]
        ring
      _ = _ := Equiv.sum_comp (r*c) (fun x => A x * B x)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hxc] at hprod
  have hcross : ∑ x, A (c x) * A x = ∑ x, (A (c x))^2 := by linarith
  have hzero : ∑ x, (A (c x) - A x)^2 = 0 := by
    calc
      _ = (∑ x, (A (c x))^2) - 2 * (∑ x, A (c x)*A x) + ∑ x, (A x)^2 := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = 0 := by rw [hcross, hxx]; ring
  intro x
  have hx : (A (c x) - A x)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (A (c x) - A x))).mp hzero x
      (Finset.mem_univ x)
  nlinarith [sq_nonneg (A (c x) - A x)]

lemma diagonal_row_column (μ : YoungDiagram) (r : rowStabilizer μ) (c : C μ)
    (hd : r.val*c.val ∈ diagonalStabilizer μ) : r = 1 ∧ c = 1 := by
  have he := diagonal_rigidity_aux (fun x : Cell μ => (row x : ℝ))
    (fun x => (col x : ℝ)) r.val c.val
    (fun x => congrArg Nat.cast (r.property x)) (fun x => congrArg Nat.cast (c.property x))
    (fun x => by exact_mod_cast hd x)
  have hc : c.val ∈ rowStabilizer μ := fun x => by exact_mod_cast he x
  have hi : c.val ∈ rowStabilizer μ ⊓ colStabilizer μ := ⟨hc,c.property⟩
  rw [row_col_intersection] at hi
  have hc1 : c = 1 := Subtype.ext hi
  have hr1 : r = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Prod.ext (r.property x)
    have hh := hd x
    rw [hc1] at hh
    change row (r.val x) + col (r.val x) = row x + col x at hh
    rw [r.property] at hh
    exact Nat.add_left_cancel hh
  exact ⟨hr1,hc1⟩

lemma diagonal_column_row (μ : YoungDiagram) (c : C μ) (r : rowStabilizer μ)
    (hd : c.val*r.val ∈ diagonalStabilizer μ) : c = 1 ∧ r = 1 := by
  have hi := (diagonalStabilizer μ).inv_mem hd
  have he : (r⁻¹).val * (c⁻¹).val ∈ diagonalStabilizer μ := by simpa using hi
  obtain ⟨hr,hc⟩ := diagonal_row_column μ r⁻¹ c⁻¹ he
  exact ⟨inv_eq_one.mp hc, inv_eq_one.mp hr⟩

variable (μ : YoungDiagram)

lemma diagonal_tabloid_eq (g h : diagonalStabilizer μ) (c : C μ) :
    tabloidOfPerm μ (g.val*c.val) = tabloidOfPerm μ h.val ↔ g = h ∧ c = 1 := by
  constructor
  · intro he
    let r : rowStabilizer μ := ⟨(g.val*c.val)⁻¹*h.val,
      (tabloidOfPerm_eq_iff μ _ _).mp he⟩
    have hr : c.val*r.val = g.val⁻¹*h.val := by dsimp only [r]; group
    have hd : c.val*r.val ∈ diagonalStabilizer μ := by
      rw [hr]
      exact (diagonalStabilizer μ).mul_mem ((diagonalStabilizer μ).inv_mem g.property) h.property
    obtain ⟨hc,hr1⟩ := diagonal_column_row μ c r hd
    refine ⟨?_,hc⟩
    rw [hc,hr1] at hr
    have hg : g.val = h.val := inv_mul_eq_one.mp (by simpa using hr.symm)
    exact Subtype.ext hg
  · rintro ⟨rfl,rfl⟩
    simp

lemma diagonal_poly_coefficient (g h : diagonalStabilizer μ) :
    tabloidRepresentation μ g.val (polytabloid μ) (tabloidOfPerm μ h.val) =
      if g = h then (1 : ℂ) else 0 := by
  rw [polytabloid, columnAnti_apply]
  simp_rw [rep_basis, smul_tabloidOfPerm, mul_one]
  rw [map_sum]
  simp_rw [map_smul, rep_basis, smul_tabloidOfPerm]
  simp only [Finset.sum_apply, Pi.smul_apply, tabloidBasis, Pi.single_apply]
  have he (c : C μ) : tabloidOfPerm μ h.val = tabloidOfPerm μ (g.val*c.val) ↔
      g = h ∧ c = 1 := (eq_comm).trans (diagonal_tabloid_eq μ g h c)
  simp only [he]
  by_cases hgh : g = h
  · simp [hgh]
  · simp [hgh]

theorem diagonal_polytabloids_independent : LinearIndependent ℂ
    (fun g : diagonalStabilizer μ => spechtRep μ g.val (spechtPoly μ)) := by
  apply LinearIndependent.of_comp (f := spechtInclude μ)
  rw [Fintype.linearIndependent_iff]
  intro a ha g
  have he := congrFun ha (tabloidOfPerm μ g.val)
  simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, Pi.zero_apply] at he
  simp_rw [spechtInclude_rep, spechtInclude_poly, diagonal_poly_coefficient] at he
  simpa using he

theorem diagonal_card_le_dimension : Fintype.card (diagonalStabilizer μ) ≤
    Module.finrank ℂ (SpechtSpace μ) := by
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  exact (diagonal_polytabloids_independent μ).fintype_card_le_finrank

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype X] [Fintype Y] in
lemma fiberQuotientLabel_injective (f : X → Y) :
    Function.Injective (fiberQuotientLabel f) := by
  intro a b
  induction a using Quotient.inductionOn with | h g =>
    induction b using Quotient.inductionOn with | h h =>
      intro he
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      intro x
      have hh := congrFun he (h x)
      simpa [fiberQuotientLabel] using hh

theorem factorial_le_colorings_mul_stabilizer (f : X → Y) :
    (Fintype.card X).factorial ≤
      (Fintype.card Y)^(Fintype.card X) * Nat.card (fiberStabilizer f) := by
  have hi : Nat.card (Equiv.Perm X ⧸ fiberStabilizer f) ≤ Nat.card (X → Y) :=
    Nat.card_le_card_of_injective (fiberQuotientLabel f) (fiberQuotientLabel_injective f)
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (fiberStabilizer f)
  rw [Nat.card_eq_fintype_card, Fintype.card_perm] at he
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun] at hi
  simp only [Nat.card_eq_fintype_card] at he ⊢
  rw [he]
  exact Nat.mul_le_mul_right _ hi

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DiagonalDimension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram)

lemma factorial_le_diagonal_dimension (L : ℕ) (hL : ∀ x : Cell μ, diagonal μ x < L) :
    (Fintype.card (Cell μ)).factorial ≤ L^(Fintype.card (Cell μ)) *
      Module.finrank ℂ (SpechtSpace μ) := by
  let f : Cell μ → Fin L := fun x => ⟨diagonal μ x,hL x⟩
  have hf : fiberStabilizer f = diagonalStabilizer μ := by
    ext g
    constructor
    · intro hg x
      exact congrArg Fin.val (hg x)
    · intro hg x
      exact Fin.ext (hg x)
  have hb := factorial_le_colorings_mul_stabilizer f
  rw [Fintype.card_fin, hf, Nat.card_eq_fintype_card] at hb
  exact hb.trans (Nat.mul_le_mul_left _ (diagonal_card_le_dimension μ))

lemma specht_dimension_pos : 0 < Module.finrank ℂ (SpechtSpace μ) :=
  lt_of_lt_of_le (Fintype.card_pos) (diagonal_card_le_dimension μ)

theorem log_dimension_lower_of_diagonal_bound (L : ℕ) (hpos : 0 < L)
    (hk : 0 < Fintype.card (Cell μ)) (hL : ∀ x : Cell μ, diagonal μ x < L) :
    (Fintype.card (Cell μ) : ℝ) *
        (Real.log (Fintype.card (Cell μ)) - Real.log L - 1) ≤
      Real.log (Module.finrank ℂ (SpechtSpace μ)) := by
  let k := Fintype.card (Cell μ)
  let D := Module.finrank ℂ (SpechtSpace μ)
  have hD : (0 : ℝ) < D := by exact_mod_cast specht_dimension_pos μ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hpos
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hbound : (k.factorial : ℝ) ≤ (L : ℝ)^k * D := by
    exact_mod_cast factorial_le_diagonal_dimension μ L hL
  have hlog := Real.log_le_log hfac hbound
  rw [Real.log_mul (pow_ne_zero _ hLr.ne') hD.ne', Real.log_pow] at hlog
  have hst := Stirling.le_log_factorial_stirling (show k ≠ 0 from hk.ne')
  have hpi : 0 ≤ Real.log (2*Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hklog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  change (k : ℝ) * (Real.log k - Real.log L - 1) ≤ Real.log D
  nlinarith

lemma diagonal_lt_height_add_width (x : Cell μ) :
    diagonal μ x < μ.colLen 0 + μ.rowLen 0 := by
  have hr : row x < μ.colLen (col x) := YoungDiagram.mem_iff_lt_colLen.mp x.property
  have hc : col x < μ.rowLen (row x) := YoungDiagram.mem_iff_lt_rowLen.mp x.property
  have hr' := μ.colLen_anti 0 (col x) (Nat.zero_le _)
  have hc' := μ.rowLen_anti 0 (row x) (Nat.zero_le _)
  unfold diagonal
  omega

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_Representations_IrrepTransport
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators MonoidAlgebra Classical

namespace BinaryCoordinateSweeps.Irrep
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

lemma irreducible_comp_equiv (e : H ≃* G) (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    Representation.IsIrreducible (k := ℂ) (G := H) (V := V) (ρ.comp e.toMonoidHom) :=
  (subrepresentationCongr e ρ).isSimpleOrder_iff.mp inferInstance

end BinaryCoordinateSweeps.Irrep

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungFinite
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.hilbertInner _root_.OAI.BinaryCoordinateSweeps.Young.hilbertNormed _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreducibleGComplexSubtypeEuclideanSpaceElemForallCellNatTabloidMemSubmoduleSpechtHilbertHilbertSpecht _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

instance instIsIrreduciblePermFinComplexPartitionSpacePartitionRep {n : ℕ} (p : n.Partition) :
    Representation.IsIrreducible (k := ℂ) (G := Equiv.Perm (Fin n))
      (V := PartitionSpace p) (partitionRep p) :=
  Irrep.irreducible_comp_equiv _ _

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_YoungResolution
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.rowStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Representation

instance instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep {n : ℕ} (p : n.Partition) : (partitionHilbertRep p).IsIrreducible :=
  Irrep.irreducible_comp_equiv _ _

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical
open Equiv Equiv.Perm Finset

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GroupedLogBounds
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma irreducible_finrank_pos {G W : Type*} [Group G]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G W) [ρ.IsIrreducible] : 0<Module.finrank ℂ W := by
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  rw [← ρ.asModuleEquiv.finrank_eq]
  exact Module.finrank_pos

end BinaryCoordinateSweeps.Signed

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_FiniteLaws_SoutheastDimension
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable (μ : YoungDiagram) (p : ℕ)

lemma southeast_height_mul_le_card :
    (p+1)*(southeast μ p).colLen 0 ≤ Fintype.card (Cell μ) := by
  let f : Fin (p+1) × Fin ((southeast μ p).colLen 0) → Cell μ := fun a =>
    ⟨(a.2.val+p,a.1.val), μ.up_left_mem le_rfl
      (show a.1.val ≤ p from Nat.le_of_lt_succ a.1.isLt)
      (by simpa using (mem_southeast μ p _).mp (YoungDiagram.mem_iff_lt_colLen.mpr a.2.isLt))⟩
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg (fun x : Cell μ => x.val.1) h
    have h2 := congrArg (fun x : Cell μ => x.val.2) h
    apply Prod.ext (Fin.ext h2)
    apply Fin.ext
    change a.2.val+p = b.2.val+p at h1
    exact Nat.add_right_cancel h1
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma southeast_width_mul_le_card :
    (p+1)*(southeast μ p).rowLen 0 ≤ Fintype.card (Cell μ) := by
  let f : Fin (p+1) × Fin ((southeast μ p).rowLen 0) → Cell μ := fun a =>
    ⟨(a.1.val,a.2.val+p), μ.up_left_mem
      (show a.1.val ≤ p from Nat.le_of_lt_succ a.1.isLt) le_rfl
      (by simpa using (mem_southeast μ p _).mp (YoungDiagram.mem_iff_lt_rowLen.mpr a.2.isLt))⟩
  have hf : Function.Injective f := by
    intro a b h
    have h1 := congrArg (fun x : Cell μ => x.val.1) h
    have h2 := congrArg (fun x : Cell μ => x.val.2) h
    apply Prod.ext (Fin.ext h1)
    apply Fin.ext
    change a.2.val+p = b.2.val+p at h2
    exact Nat.add_right_cancel h2
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma southeast_diagonal_bound (x : Cell (southeast μ p)) :
    diagonal (southeast μ p) x < 2*(Fintype.card (Cell μ)/(p+1)) := by
  have hh : (southeast μ p).colLen 0 ≤ Fintype.card (Cell μ)/(p+1) := (Nat.le_div_iff_mul_le (show 0<p+1 by omega)).mpr
    (by simpa only [Nat.mul_comm] using southeast_height_mul_le_card μ p)
  have hw : (southeast μ p).rowLen 0 ≤ Fintype.card (Cell μ)/(p+1) := (Nat.le_div_iff_mul_le (show 0<p+1 by omega)).mpr
    (by simpa only [Nat.mul_comm] using southeast_width_mul_le_card μ p)
  have hd := diagonal_lt_height_add_width (southeast μ p) x
  omega

theorem southeast_log_dimension_lower (hk : 0 < Fintype.card (Cell (southeast μ p))) :
    (Fintype.card (Cell (southeast μ p)) : ℝ) *
      (Real.log (Fintype.card (Cell (southeast μ p))) -
        Real.log (2*(Fintype.card (Cell μ)/(p+1)) : ℕ) - 1) ≤
      Real.log (Module.finrank ℂ (SpechtSpace (southeast μ p))) := by
  have hn := Fintype.card_pos_iff.mp hk
  obtain ⟨x⟩ := hn
  have hpos : 0 < 2*(Fintype.card (Cell μ)/(p+1)) :=
    Nat.zero_lt_of_lt (southeast_diagonal_bound μ p x)
  exact log_dimension_lower_of_diagonal_bound (southeast μ p) _ hpos hk
    (southeast_diagonal_bound μ p)

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Signed

lemma hook_log_dimension_upper (μ : YoungDiagram) (p s : ℕ) (hs : 0<s)
    (hM : Fintype.card (Cell μ)≤ s) :
    Real.log (Module.finrank ℂ (SpechtSpace μ)) ≤
      Real.log (Module.finrank ℂ (SpechtSpace (hookPart μ p)))+
        Fintype.card (Cell (southeast μ p))*Real.log s := by
  have hD : (0:ℝ)<Module.finrank ℂ (SpechtSpace μ) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht μ)
  have hG : (0:ℝ)<Module.finrank ℂ (SpechtSpace (hookPart μ p)) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht (hookPart μ p))
  have hsp : (0:ℝ)<s := by exact_mod_cast hs
  have hb := (hook_removal_dimension_upper μ p).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM _))
  have hl := Real.log_le_log hD (show (Module.finrank ℂ (SpechtSpace μ):ℝ)≤
      (s:ℝ)^Fintype.card (Cell (southeast μ p))*Module.finrank ℂ (SpechtSpace (hookPart μ p)) by
    exact_mod_cast hb)
  rw [Real.log_mul (pow_pos hsp _).ne' hG.ne',Real.log_pow] at hl
  linarith

lemma southeast_dense_saving (μ : YoungDiagram) (s : ℕ) (hs : 0<s)
    (hM : Fintype.card (Cell μ)≤ s)
    (hk : (s:ℝ)^(199/200:ℝ)≤Fintype.card (Cell (southeast μ ⌊(s:ℝ)^(1/100:ℝ)⌋₊))) :
    (Fintype.card (Cell (southeast μ ⌊(s:ℝ)^(1/100:ℝ)⌋₊)):ℝ)*
      ((1/200:ℝ)*Real.log s-(Real.log 2+1)) ≤
      Real.log (Module.finrank ℂ (SpechtSpace (southeast μ ⌊(s:ℝ)^(1/100:ℝ)⌋₊))) := by
  let p := ⌊(s:ℝ)^(1/100:ℝ)⌋₊
  let k := Fintype.card (Cell (southeast μ p))
  let M := Fintype.card (Cell μ)
  let U := 2*(M/(p+1))
  have hsp : (0:ℝ)<s := by exact_mod_cast hs
  have hkR : (0:ℝ)<k := (Real.rpow_pos_of_pos hsp _).trans_le hk
  have hkN : 0<k := by exact_mod_cast hkR
  have hU : 0<U := by
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hkN
    exact Nat.zero_lt_of_lt (southeast_diagonal_bound μ p x)
  have hp : (s:ℝ)^(1/100:ℝ)≤(p:ℝ)+1 := (Nat.lt_floor_add_one _).le
  have hprod : (M/(p+1):ℕ)*(p+1)≤ s := (Nat.div_mul_le_self _ _).trans hM
  have hprodR : (M/(p+1):ℕ)*( (p:ℝ)+1)≤(s:ℝ) := by exact_mod_cast hprod
  have hquot : (M/(p+1):ℕ)≤(s:ℝ)^(99/100:ℝ) := by
    rw [show (99/100:ℝ)=1-1/100 by norm_num,Real.rpow_sub hsp,Real.rpow_one]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hsp _)).mpr
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans hprodR
  have hUR : (U:ℝ)≤2*(s:ℝ)^(99/100:ℝ) := by dsimp [U]; push_cast; linarith
  have hlU := Real.log_le_log (show (0:ℝ)<U by exact_mod_cast hU) hUR
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hsp _).ne',Real.log_rpow hsp] at hlU
  have hlk := Real.log_le_log (Real.rpow_pos_of_pos hsp _) hk
  rw [Real.log_rpow hsp] at hlk
  have hb := southeast_log_dimension_lower μ p hkN
  change (k:ℝ)*(Real.log k-Real.log U-1)≤_ at hb
  refine le_trans ?_ hb
  apply mul_le_mul_of_nonneg_left _ hkR.le
  linarith

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_HookHilbertOccurrence
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace BinaryCoordinateSweeps.Young
open Representation Irrep Signed

variable {N p : ℕ} (α : N.Partition) (h : InHook (diagram α) p)

variable (μ : YoungDiagram) (hμ : InHook μ p) (e : Cell μ ≃ Fin N)

lemma hookHilbertMapAt_injective : Function.Injective (hookHilbertMapAt μ hμ e) :=
  (coeffEquiv (Bool × Fin p) N).symm.injective.comp
    ((hookMap_injective hμ e).comp (spechtHilbertEquiv μ).symm.injective)

include hμ in
lemma hookHilbert_occursAt :
    0<Module.finrank ℂ (IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N)) := by
  have : Nontrivial (SpechtHilbert μ) := by
    exact Module.nontrivial_of_finrank_pos (irreducible_finrank_pos (hilbertSpecht μ))
  have hn : hookHilbertMapAt μ hμ e≠0 := by
    intro he
    obtain ⟨v,hv⟩ := exists_ne (0 : SpechtHilbert μ)
    apply hv
    apply hookHilbertMapAt_injective μ hμ e
    rw [he]
    rfl
  have : Nontrivial (IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (hilbertTensorRep (Prod.fst : Bool × Fin p → Bool) N)) := ⟨⟨_,_,hn⟩⟩
  exact Module.finrank_pos

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_GridDenseCost
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace BinaryCoordinateSweeps

lemma dense_error_eventually : ∀ᶠ s : ℝ in atTop,
    s ^ (9/10 : ℝ) + s ^ (199/200 : ℝ) * Real.log s ≤
      inductionGap s * s ^ (399/400 : ℝ) := by
  have ho := isLittleO_log_rpow_rpow_atTop (3/2 : ℝ) (by norm_num : (0 : ℝ) < 1/400)
  have he := ho.bound (by norm_num : (0 : ℝ) < 1/40)
  filter_upwards [he, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℝ)] with s hs hl h1
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one h1
  have hl0 : 0 < Real.log s := lt_of_lt_of_le zero_lt_one hl
  have ht : (Real.log s) ^ (3/2 : ℝ) ≤ (1/40 : ℝ) * s ^ (1/400 : ℝ) := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hl0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hs0.le _)] using hs
  have hl32 : Real.sqrt (Real.log s) * Real.log s = (Real.log s) ^ (3/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (Real.log s) ^ (1/2 : ℝ) * Real.log s =
          (Real.log s) ^ (1/2 : ℝ) * (Real.log s) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (Real.log s) ^ (3/2 : ℝ) := by rw [← Real.rpow_add hl0]; norm_num
  have hpow : s ^ (9/10 : ℝ) ≤ s ^ (199/200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have hpow0 : 0 ≤ s ^ (199/200 : ℝ) := Real.rpow_nonneg hs0.le _
  have hsq0 : 0 < Real.sqrt (Real.log s) := Real.sqrt_pos.mpr hl0
  unfold inductionGap
  rw [div_mul_eq_mul_div, one_mul]
  apply (le_div_iff₀ (by positivity : 0 < 20 * Real.sqrt (Real.log s))).mpr
  calc
    (s ^ (9/10 : ℝ) + s ^ (199/200 : ℝ) * Real.log s) *
        (20 * Real.sqrt (Real.log s)) ≤
        (2 * s ^ (199/200 : ℝ) * Real.log s) * (20 * Real.sqrt (Real.log s)) := by
      gcongr
      nlinarith
    _ = 40 * s ^ (199/200 : ℝ) * (Real.log s) ^ (3/2 : ℝ) := by
      rw [← hl32]
      ring
    _ ≤ 40 * s ^ (199/200 : ℝ) * ((1/40 : ℝ) * s ^ (1/400 : ℝ)) := by gcongr
    _ = s ^ (399/400 : ℝ) := by
      rw [show 40 * s ^ (199/200 : ℝ) * ((1/40 : ℝ) * s ^ (1/400 : ℝ)) =
        s ^ (199/200 : ℝ) * s ^ (1/400 : ℝ) by ring, ← Real.rpow_add hs0]
      norm_num

theorem dense_induction_absorption_eventually (C : ℝ) : ∀ᶠ s : ℕ in atTop,
    ∀ b h k F G J : ℝ, 0 ≤ h → 0 ≤ k → 0 ≤ J →
      Real.log 4 * b ≤ (1/1000 : ℝ) * Real.log s →
      F ≤ G + k * Real.log s →
      (s : ℝ) ^ (399/400 : ℝ) ≤ F →
      ((s : ℝ) ^ (199/200 : ℝ) ≤ k →
        k * ((1/200 : ℝ) * Real.log s - C) ≤ J) →
      -(cExponent s + inductionGap s) * G +
        (eExponent s - inductionGap s) * (h+k) * Real.log s +
        (s : ℝ) ^ (9/10 : ℝ) + Real.log 4 * k * b - J ≤
        -cExponent s * F + eExponent s * h * Real.log s := by
  have hlim : Tendsto (fun s : ℕ => (s : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hloglim := Real.tendsto_log_atTop.comp hlim
  filter_upwards [hlim.eventually dense_error_eventually,
      hloglim.eventually_ge_atTop (max 1 (1000*C))] with s herr hlarge
  have hl : 1 ≤ Real.log s := (le_max_left _ _).trans hlarge
  have hC : 1000*C ≤ Real.log s := (le_max_right _ _).trans hlarge
  have hl0 : 0 < Real.log s := by linarith
  have hg0 : 0 < inductionGap s := by unfold inductionGap; positivity
  have hc0 : 0 ≤ cExponent s + inductionGap s := by unfold cExponent c0; positivity
  intro b h k F G J hh hk hJ hb hdim hF hremoved
  have hce : cExponent s + inductionGap s + (eExponent s - inductionGap s) =
      (1/5000 : ℝ) := by unfold cExponent eExponent c0 e0; ring
  have hextra : (1/5000 : ℝ) * k * Real.log s + Real.log 4 * k * b - J ≤
      (s : ℝ) ^ (199/200 : ℝ) * Real.log s := by
    by_cases hbig : (s : ℝ) ^ (199/200 : ℝ) ≤ k
    · have hpay := hremoved hbig
      have hb' := mul_le_mul_of_nonneg_left hb hk
      have hcost : (1/5000 : ℝ) * k * Real.log s + Real.log 4 * k * b - J ≤ 0 := by
        have hcoef : (1/5000 : ℝ) * Real.log s + (1/1000 : ℝ) * Real.log s ≤
            (1/200 : ℝ) * Real.log s - C := by nlinarith
        have hcoef' := mul_le_mul_of_nonneg_left hcoef hk
        nlinarith
      exact hcost.trans (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg s) _) hl0.le)
    · have hk' : k ≤ (s : ℝ) ^ (199/200 : ℝ) := (lt_of_not_ge hbig).le
      have hb' := mul_le_mul_of_nonneg_left hb hk
      have hkl := mul_le_mul_of_nonneg_right hk' hl0.le
      have hkl0 := mul_nonneg hk hl0.le
      nlinarith
  have hce' := congrArg (fun t : ℝ => t * k * Real.log s) hce
  have hdim' := mul_le_mul_of_nonneg_left hdim hc0
  have hsave := mul_le_mul_of_nonneg_left hF hg0.le
  have hholes := mul_nonneg (mul_nonneg hg0.le hh) hl0.le
  nlinarith

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_GenericHookAux
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed Young

theorem specht_hook_auxiliary_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ μ : YoungDiagram, InHook μ t → ∀ e : Cell μ ≃ FreeSlot H 0, ∀z : ℝ,
    (∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-cExponent (gridSize (leftBits bits))*typeF a.val+
          eExponent (gridSize (leftBits bits))*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) →
    (∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-cExponent (gridSize (rightBits bits))*typeF a.val+
          eExponent (gridSize (rightBits bits))*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) →
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*Real.log (Module.finrank ℂ (SpechtSpace μ):ℝ)+
        (eExponent s-inductionGap s)*h*Real.log s-pathCost H+(s:ℝ)^(9/10:ℝ)) := by
  filter_upwards [occurring_auxiliary_eventually q hq] with s hs
  intro m n h bits H hsize hu hv hub hvb t ht hts μ hμ e z hR hC
  let eJ := e.trans (inputToJunction bits H)
  let ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) (SpechtHilbert μ) := (hilbertSpecht μ).comp eJ.symm.permCongrHom.toMonoidHom
  let : ρ.IsIrreducible := irreducible_comp_equiv eJ.symm.permCongrHom (hilbertSpecht μ)
  have hρ : ∀g v, ‖ρ g v‖=‖v‖ := fun g v => hilbertSpecht_unitary μ _ v
  have hb := hs m n h bits H hsize hu hv hub hvb t ht hts (SpechtHilbert μ) ρ hρ
    (hookHilbert_occursAt μ hμ eJ) z hR hC
  have he : ρ.comp (inputToJunction bits H).permCongrHom.toMonoidHom =
      (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change hilbertSpecht μ (eJ.symm.permCongr ((inputToJunction bits H).permCongr g)) =
      hilbertSpecht μ (e.symm.permCongr g)
    apply congrArg (hilbertSpecht μ)
    apply Equiv.ext
    intro a
    simp [eJ,Equiv.permCongr_apply]
  rw [he,hilbertSpecht_finrank] at hb
  exact hb

end BinaryCoordinateSweeps.GridSplit

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_YoungTheory_PhysicalHookInduced
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype _root_.OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexPartitionSpacePartitionRep _root_.OAI.BinaryCoordinateSweeps.Young.instIsIrreduciblePermFinComplexSubtypeEuclideanSpaceElemForallCellDiagramNatTabloidMemSubmodulePartitionHilbertPartitionHilbertRep _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
open Irrep Representation

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
  (μ : YoungDiagram) (p : ℕ) (e : Cell μ ≃ FreeSlot H 0)

lemma hookPlacement_restriction :
    ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom).comp
      (blockPerm (hookPlacementBasis H μ p e)) = (hilbertSpecht μ).comp (hookPerm μ p) := by
  apply MonoidHom.ext
  intro g
  change hilbertSpecht μ
    (e.symm.permCongr (blockPerm (hookPlacementBasis H μ p e) g)) =
    hilbertSpecht μ (hookPerm μ p g)
  apply congrArg (hilbertSpecht μ)
  rw [hookPerm_block]
  apply Equiv.ext
  intro a
  obtain ⟨a,rfl⟩ := (cutEquiv μ p).surjective a
  cases a with
  | inl a => simp [hookPlacementBasis,blockPerm,Equiv.permCongr_apply]
  | inr a => simp [hookPlacementBasis,blockPerm,Equiv.permCongr_apply]

lemma hook_hilbert_restriction_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤ Module.finrank ℂ
      (IntertwiningMap ((hilbertSpecht μ).comp (hookPerm μ p)) (hilbertSpecht (hookPart μ p))) := by
  let : Module.Finite ℂ (SpechtSpace μ) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace μ))
  let : Module.Finite ℂ (SpechtSpace (hookPart μ p)) :=
    inferInstanceAs (FiniteDimensional ℂ (SpechtSpace (hookPart μ p)))
  have hs := multiplicity_symm (spechtRep (hookPart μ p)) (hookRestriction μ p)
  have he := multiplicity_congr
    (repEquiv_comp (conjugateEquiv (spechtRep μ) (spechtHilbertEquiv μ)) (hookPerm μ p))
    (conjugateEquiv (spechtRep (hookPart μ p)) (spechtHilbertEquiv (hookPart μ p)))
  exact (hook_removal_multiplicity μ p).trans (Nat.le_of_eq (hs.trans he))

lemma hook_placement_multiplicity :
    Module.finrank ℂ (SpechtSpace (southeast μ p)) ≤ Module.finrank ℂ
      (IntertwiningMap ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (coindHilbertRep (blockPerm (hookPlacementBasis H μ p e)) (hilbertSpecht (hookPart μ p))
          (fun x => (placementSection (hookPlacementBasis H μ p e) x)⁻¹)
          (placement_cosets_bijective (hookPlacementBasis H μ p e)))) := by
  let ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (SpechtHilbert μ) :=
    (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom
  let f := hookPlacementBasis H μ p e
  let σ := hilbertSpecht (hookPart μ p)
  have hr := (coindHomEquiv (blockPerm f) ρ σ).finrank_eq
  have hd := multiplicity_congr (Representation.Equiv.refl ρ)
    (conjugateEquiv (coind (blockPerm f) σ)
      (coindHilbertEquiv (blockPerm f) σ (fun x => (placementSection f x)⁻¹)
        (placement_cosets_bijective f)))
  have he : ρ.comp (blockPerm f)=(hilbertSpecht μ).comp (hookPerm μ p) :=
    hookPlacement_restriction H μ p e
  rw [he] at hr
  exact (hook_hilbert_restriction_multiplicity μ p).trans (Nat.le_of_eq (hr.trans hd))

theorem conditional_hook_induced_moment_le (z : ℝ) (q : ℕ) :
    (Module.finrank ℂ (SpechtSpace (southeast μ p)):ℝ)*
      evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
        (fun a => (conditionalGroupLaw H z a:ℂ))) ≤
      evenMoment q (inducedPlacementAverage H (hookPlacementBasis H μ p e)
        (hilbertSpecht (hookPart μ p)) z) := by
  let ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (SpechtHilbert μ) :=
    (hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom
  let : ρ.IsIrreducible := irreducible_comp_equiv e.symm.permCongrHom (hilbertSpecht μ)
  let f := hookPlacementBasis H μ p e
  let σ := coindHilbertRep (blockPerm f) (hilbertSpecht (hookPart μ p))
    (fun x => (placementSection f x)⁻¹) (placement_cosets_bijective f)
  have hσ (a) (v) : ‖σ a v‖=‖v‖ :=
    ((σ a).isometryOfInner (coindHilbert_unitary _ _ _ _
      (hilbertSpecht_inner (hookPart μ p)) a)).norm_map v
  have hm := multiplicity_moment_le ρ σ (fun a => (conditionalGroupLaw H z a:ℂ))
    (fun a v => hilbertSpecht_unitary μ _ v) hσ q
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hook_placement_multiplicity H μ p e)
    (evenMoment_nonneg q _)).trans hm

end BinaryCoordinateSweeps.Young

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DenseAssembly
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Irrep Representation Young GridSplit Signed

lemma moment_divide_dimension {D T B : ℝ} (hD : 0<D) (h : D*T≤Real.exp B) :
    T≤Real.exp (B-Real.log D) := by
  have hh : T*D≤Real.exp B := by rwa [mul_comm]
  have he := (le_div_iff₀ hD).mpr hh
  rwa [←Real.exp_log hD,←Real.exp_sub] at he

lemma dense_of_auxiliary_hook {m n h r : ℕ} (s q t : ℕ) (hq : 0<q)
    (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
    (hd : ∀j, bits j≤2*r) (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0)
    (z : ℝ) (hz : 0≤z) (hzr : z≤linePerturbationRadius r)
    (hhook : ∀ h' : ℕ, ∀ HH : PathFamily bits h',
      ∀ ee : Cell (hookPart μ t) ≃ FreeSlot HH 0,
      evenMoment q (groupAverage ((hilbertSpecht (hookPart μ t)).comp
        ee.symm.permCongrHom.toMonoidHom) (fun a => (conditionalGroupLaw HH z a:ℂ)))≤
        Real.exp (-(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
          (eExponent s-inductionGap s)*h'*Real.log s-pathCost HH+(s:ℝ)^(9/10:ℝ))) :
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
        (eExponent s-inductionGap s)*(h+Fintype.card (Cell (southeast μ t)))*Real.log s+
        (s:ℝ)^(9/10:ℝ)-pathCost H+
        Real.log 4*Fintype.card (Cell (southeast μ t))*(m+n)-diagramF (southeast μ t)) := by
  let k := Fintype.card (Cell (southeast μ t))
  let f := hookPlacementBasis H μ t e
  let σ := hilbertSpecht (hookPart μ t)
  let B := -(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
    (eExponent s-inductionGap s)*(h+k)*Real.log s+(s:ℝ)^(9/10:ℝ)
  have hf (x y : Placement H k 0) (hp : 0<placementKernel H z x y) :
      placementFiberMoment H f σ z q x y ≤
        Real.exp (B-placementTransitionCost H z x (placementIdentification H k y)) := by
    let g := realizePlacement H z x (placementIdentification H k y) hp
    have hb := hhook (h+k) (augmentByChoice H x g) (augmentedInputBasis H x g f)
    unfold placementFiberMoment
    rw [dite_eq_left hp]
    change evenMoment q (groupAverage (augmentedRepresentation H x g f σ) _)≤_
    change evenMoment q (groupAverage ((hilbertSpecht (hookPart μ t)).comp
      (augmentedInputBasis H x g f).symm.permCongrHom.toMonoidHom) _)≤_ at hb ⊢
    refine hb.trans_eq ?_
    unfold placementTransitionCost
    rw [dite_eq_left (show 0<placementProbability H z x (placementIdentification H k y) from hp)]
    congr 1
    dsimp [B,diagramF]
    push_cast
    ring
  have hi := induced_placement_of_hook_bound H f σ hd hz hzr
    (hilbertSpecht_unitary (hookPart μ t)) hq B hf
  have hm := (conditional_hook_induced_moment_le H μ t e z q).trans hi
  have hD : (0:ℝ)<Module.finrank ℂ (SpechtSpace (southeast μ t)) := by
    rw [←hilbertSpecht_finrank]
    exact_mod_cast irreducible_finrank_pos (hilbertSpecht (southeast μ t))
  refine (moment_divide_dimension hD hm).trans_eq ?_
  congr 1
  dsimp [B,k,diagramF]
  push_cast
  ring

theorem dense_branch_operator_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h r : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    (∀j, bits j≤2*r) →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ μ : YoungDiagram, ∀ e : Cell μ ≃ FreeSlot H 0, ∀z : ℝ,
    0≤z → z≤linePerturbationRadius r →
    EnumeratedMomentBound q (leftBits bits) z → EnumeratedMomentBound q (rightBits bits) z →
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*diagramF (hookPart μ t)+
        (eExponent s-inductionGap s)*(h+Fintype.card (Cell (southeast μ t)))*Real.log s+
        (s:ℝ)^(9/10:ℝ)-pathCost H+
        Real.log 4*Fintype.card (Cell (southeast μ t))*(m+n)-diagramF (southeast μ t)) := by
  filter_upwards [specht_hook_auxiliary_eventually q hq] with s hs
  intro m n h r bits H hsize hu hv hub hvb hd t ht hts μ e z hz hzr hR hC
  apply dense_of_auxiliary_hook s q t (by omega) bits H hd μ e z hz hzr
  intro h' HH ee
  exact hs m n h' bits HH hsize hu hv hub hvb t ht hts
    (hookPart μ t) (hookPart_inHook μ t) ee z
    (fun y a => hR _ (rowFamily bits HH y) a.val)
    (fun x a => hC _ (columnFamily bits HH x) a.val)

end BinaryCoordinateSweeps

end

end OAI
end

section
-- module Solutions.OAIB3_Bsw.BinarySweep_GridBounds_DenseClosing
attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps
open Young Irrep Representation GridSplit Signed

lemma diagramF_nonneg (μ : YoungDiagram) : 0≤diagramF μ := by
  apply Real.log_nonneg
  have hpos := irreducible_finrank_pos (hilbertSpecht μ)
  rw [hilbertSpecht_finrank] at hpos
  exact_mod_cast Nat.one_le_of_lt hpos

theorem dense_induction_step_eventually_oai (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h r : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    (∀j, bits j≤2*r) → Real.log 4*(m+n)≤(1/1000:ℝ)*Real.log s →
    ∀ μ : YoungDiagram, ∀ e : Cell μ ≃ FreeSlot H 0,
    (s:ℝ)^(399/400:ℝ)≤diagramF μ → ∀z : ℝ,
    0≤z → z≤linePerturbationRadius r →
    EnumeratedMomentBound q (leftBits bits) z → EnumeratedMomentBound q (rightBits bits) z →
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-cExponent s*diagramF μ+eExponent s*h*Real.log s-pathCost H) := by
  filter_upwards [dense_branch_operator_eventually q hq,
    dense_induction_absorption_eventually (Real.log 2+1),eventually_ge_atTop (1:ℕ)] with s hop hab hs
  intro m n h r bits H hsize hu hv hub hvb hd haxes μ e hF z hz hzr hR hC
  have hs0 : 0<s := by omega
  have hs1 : (1:ℝ)≤ s := by exact_mod_cast hs
  let p := ⌊(s:ℝ)^(1/100:ℝ)⌋₊
  have hp : 0<p := Nat.floor_pos.mpr (Real.one_le_rpow hs1 (by norm_num))
  have hps : (p:ℝ)≤(s:ℝ)^(1/100:ℝ) := Nat.floor_le (by positivity)
  have hM : Fintype.card (Cell μ)≤ s := by
    rw [Fintype.card_congr e,card_freeSlot,hsize]
    omega
  have hdim := hook_log_dimension_upper μ p s hs0 hM
  have hc := hab (m+n) h (Fintype.card (Cell (southeast μ p)))
    (diagramF μ) (diagramF (hookPart μ p)) (diagramF (southeast μ p))
    (by positivity) (by positivity) (diagramF_nonneg _) haxes hdim hF
    (southeast_dense_saving μ s hs0 hM)
  have hm := hop m n h r bits H hsize hu hv hub hvb hd p hp hps μ e z hz hzr hR hC
  refine hm.trans (Real.exp_le_exp.mpr ?_)
  have he := sub_le_sub_right hc (pathCost H)
  convert he using 1; ring

end BinaryCoordinateSweeps

end

end OAI
end

theorem solution : type_of% @OAI.BinaryCoordinateSweeps.dense_induction_step_eventually_oai := @OAI.BinaryCoordinateSweeps.dense_induction_step_eventually_oai
